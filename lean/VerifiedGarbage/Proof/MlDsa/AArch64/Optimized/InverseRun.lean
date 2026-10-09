import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStage

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def runRegs : List VReg :=
  [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17,.v18,.v19,.v20,.v21,.v24,.v25,.v26,.v27]

theorem stageClobs_subset (i : Fin 7) : ∀ r∈stageClobs i.val, r∈runRegs := by
  exact (show ∀ i : Fin 7, ∀ r∈stageClobs i.val, r∈runRegs by decide +kernel) i

theorem roots_apart (i : Fin 8) (k : Fin 8) : (regs i.val)[k.val]∉[.v20,.v21] := by
  exact (show ∀ i k : Fin 8, (regs i.val)[k.val]∉[.v20,.v21] by decide +kernel) i k

/-- A root supplier packages either static-table loads or hoisted DUPs. Its
invariant includes the immutable root storage and the modulus vector. -/
structure RootPlan where
  load : Nat → List Instr
  value : Nat → Nat → Int
  invariant : State → Prop
  range : ∀ i : Fin 7, ∀ e<4, 0≤value i.val e ∧ value i.val e<8380417
  stable : ∀ i : Fin 7, ∀ {s t : State}, VChg (stageClobs i.val) s t → invariant s → invariant t
  load_ok : ∀ i : Fin 7, ∀ {s : State} {rest : List Instr} {Q : State → Prop}, invariant s →
    (∀ t, VChg [.v20,.v21] s t → invariant t →
      (∀ e<4, vword (t.v .v20) e=BitVec.ofInt 32 (value i.val e)) →
      (∀ e<4, vword (t.v .v21) e=BitVec.ofInt 32 (reciprocal (value i.val e))) →
      (∀ e<4, vword (t.v .v31) e=8380417#32) → WP isa (.block rest) t Q) →
    WP isa (.block (load i.val ++ rest)) s Q

def stageCode (i : Nat) : List Instr :=
  (stagePairs i).flatMap PairRegs.code ++ multiplyCode (stageProducts i)

def runCode (roots : Nat → List Instr) (i : Nat) : Nat → List Instr
  | 0 => []
  | n+1 => roots i ++ stageCode i ++ runCode roots (i+1) n

def runValues (z : Nat → Nat → Int) (i : Nat) : Nat → Vector (BitVec 128) 8 → Vector (BitVec 128) 8
  | 0,v => v
  | n+1,v => runValues z (i+1) n (stageValues i v (z i))

/-- All seven renamed arithmetic groups, before their surrounding loads and
stores. The theorem retains the exact representatives, not only residues. -/
theorem run_ok (plan : RootPlan) (i n : Nat) (hin : i+n≤7)
    {s : State} {rest : List Instr} {Q : State → Prop} {v : Vector (BitVec 128) 8}
    (hbank : Bank s (regs i) v) (hplan : plan.invariant s)
    (k : ∀ t, VChg runRegs s t → plan.invariant t →
      Bank t (regs (i+n)) (runValues plan.value i n v) → WP isa (.block rest) t Q) :
    WP isa (.block (runCode plan.load i n ++ rest)) s Q := by
  induction n generalizing i s v with
  | zero => exact k s (VChg.refl _ _) hplan hbank
  | succ n ih =>
    have hi : i<7 := by omega
    simp only [runCode,List.append_assoc]
    refine plan.load_ok ⟨i,hi⟩ hplan fun a ha hpa hz hb hq => ?_
    have hba : Bank a (regs i) v := by
      intro j
      rw [ha.get _ (roots_apart ⟨i,by omega⟩ j)]
      exact hbank j
    have hstage := stage_ok ⟨i,hi⟩ (rest := runCode plan.load (i+1) n ++ rest) (Q := Q)
      hba (plan.range ⟨i,hi⟩) hz hb hq
    refine hstage fun b hc hbb => ?_
    refine ih (i+1) (by omega) hbb (plan.stable ⟨i,hi⟩ hc hpa) fun t ht hpt hbt => ?_
    refine k t (VChg.mono ((ha.trans hc).trans ht) ?_) hpt ?_
    · intro r hr
      simp only [List.mem_append] at hr
      rcases hr with (hr | hr) | hr
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> decide
      · exact stageClobs_subset ⟨i,hi⟩ r hr
      · exact hr
    · simpa only [runValues,Nat.add_assoc,Nat.add_comm n 1] using hbt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
