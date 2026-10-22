module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.PAttempt
public import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: the search for p

`pPart_vp`: the candidates of the counters 0, 1, … from a seed, until one is
a probable prime (`fP` := 1, p at `sPBE` and its arrays), the witnesses run
out (`fP` := 0) or the `4 L` counters are done (`fP` := 2), as
`Spec.Dsa.primeFromSeed` searches them.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd wp_dp wp_movw wp_cmp op2_reg op2_imm dpVal eval_eq)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)

section
variable {G : GP} {X : State → Prop}

/-- The next counter: `fCounter` + 1, `fOffset` + `C`, and Z when the counter
reaches `32 pLen` (`4 L`). -/
theorem pAdvance_vp {d : Cfg} {j off C : Nat} (hC : C < 256) (hCt : fCounter ∈ d.LS)
    (hCv : d.V fCounter = BitVec.ofNat 32 j) (hOf : fOffset ∈ d.LS) (hOv : d.V fOffset = BitVec.ofNat 32 off)
    (hj : j + 1 < 2 ^ 16) :
    VP (St G d X) (VG.Impl.Rsa.Arm.Keys.seqs [
        .block [ld .r1 fCounter], .block [.dp .add .r1 .r1 (.imm 1)], .block (st .r1 fCounter),
        .block [ld .r2 fOffset], .block [.dp .add .r2 .r2 (.imm (BitVec.ofNat 32 C))],
        .block (st .r2 fOffset), .block [.movw .r2 (BitVec.ofNat 16 (32 * G.pLen)), .cmp .r1 (.reg .r2)]])
      (fun σ s => St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset (BitVec.ofNat 32 (off + C))) X σ s ∧
        isa.eval .eq s = some (decide (j + 1 = 32 * G.pLen))) := by
  have taint1 : ∀ σ₁ σ₂ (s₁ s₂ : State) (P : State → State → Prop) (v : BitVec 32), (P σ₁ s₁ ∧ s₁.gpr .r1 = v) →
      (P σ₂ s₂ ∧ s₂.gpr .r1 = v) → ∀ r ∈ [Reg.r1], s₁.gpr r = s₂.gpr r := fun _ _ _ _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
  -- The counter.
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 j)
    (ld_vp (c := fun _ => d) (fun σ s h => h.1) (by decide) (by decide) (fun σ s h => (h.1.slotV hCt).trans hCv)
      fun σ s t ⟨h, x⟩ u => ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => St G d X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (j + 1))
    (VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.dp .add .r1 .r1 (.imm 1)]), rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => taint1 σ₁ σ₂ s₁ s₂ _ _ h₁ h₂)
      fun σ s ⟨⟨h, x⟩, r1⟩ => wp_dp (op2_imm (encodable_lt (by decide : 1 < 256))) fun t u => WP.block_nil
        ⟨⟨h.of_rest (u.rest (ws := [.r1]) (by simp)) u.mem, x⟩, by
          rw [u.gpr, dpVal, r1]; exact (BitVec.ofNat_add _ _).symm⟩) ?_
  have d1O : fOffset ∈ (d.setV fCounter (BitVec.ofNat 32 (j + 1))).LS := List.mem_cons_of_mem _ hOf
  refine VP.seq (G := fun σ s => St G (d.setV fCounter (BitVec.ofNat 32 (j + 1))) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 (j + 1))
    (st_vp (c := fun _ => d) (fun σ s h => h.1.1) (by decide) (varOk_of (by decide))
      fun σ s t ⟨⟨h, x⟩, r1⟩ h' R => ⟨⟨r1 ▸ h', x⟩, by rw [R.gpr _ (by decide), r1]⟩) ?_
  -- The offset.
  refine VP.seq (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 32 (j + 1))) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 (j + 1)) ∧ s.gpr .r2 = BitVec.ofNat 32 off)
    (ld_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 32 (j + 1))) (fun σ s h => h.1.1) (by decide) (by decide)
      (fun σ s h => (h.1.1.slotV d1O).trans (by show upd d.V fCounter (BitVec.ofNat 32 (j + 1)) fOffset = _; rw [upd_ne _ _ (by decide)]; exact hOv))
      fun σ s t ⟨⟨h, x⟩, r1⟩ u => ⟨⟨⟨h.of_rest (u.rest (ws := [.r2]) (by simp)) u.mem, x⟩,
        by rw [u.other _ (by decide), r1]⟩, u.gpr⟩) ?_
  refine VP.seq (G := fun σ s => (St G (d.setV fCounter (BitVec.ofNat 32 (j + 1))) X σ s ∧
      s.gpr .r1 = BitVec.ofNat 32 (j + 1)) ∧ s.gpr .r2 = BitVec.ofNat 32 (off + C))
    (VP.taint [.r2] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r2])
      (.block [.dp .add .r2 .r2 (.imm (BitVec.ofNat 32 0))]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
      fun σ s ⟨⟨⟨h, x⟩, r1⟩, r2⟩ => wp_dp (op2_imm (encodable_lt hC)) fun t u => WP.block_nil
        ⟨⟨⟨h.of_rest (u.rest (ws := [.r2]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), r1]⟩, by
          rw [u.gpr, dpVal, r2]; exact (BitVec.ofNat_add _ _).symm⟩) ?_
  refine VP.seq (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
      (BitVec.ofNat 32 (off + C))) X σ s ∧ s.gpr .r1 = BitVec.ofNat 32 (j + 1))
    (st_vp (c := fun _ => d.setV fCounter (BitVec.ofNat 32 (j + 1))) (fun σ s h => h.1.1.1) (by decide)
      (varOk_of (by decide))
      fun σ s t ⟨⟨⟨h, x⟩, r1⟩, r2⟩ h' R => ⟨⟨r2 ▸ h', x⟩, by rw [R.gpr _ (by decide), r1]⟩) ?_
  -- The end of the counters.
  refine VP.taint [.r1] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1])
      (.block [.movw .r2 (BitVec.ofNat 16 1), .cmp .r1 (.reg .r2)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => taint1 σ₁ σ₂ s₁ s₂ _ _ h₁ h₂)
    fun σ s ⟨⟨h, x⟩, r1⟩ => wp_movw fun t u => wp_cmp (op2_reg _ _) fun t' f z => WP.block_nil ?_
  have l := h.lens
  have r2 : t.gpr .r2 = BitVec.ofNat 32 (32 * G.pLen) := by rw [u.gpr, setWidth_ofNat16 (by omega)]
  refine ⟨⟨h.of_rest ((u.rest (ws := [.r2]) (by simp)).trans (f.rest _)) (by rw [f.mem, u.mem]), x⟩, ?_⟩
  rw [eval_eq, z, u.other _ (by decide), r1, r2, beq_sub_zero]
  congr 1
  by_cases e : j + 1 = 32 * G.pLen
  · simp [e]
  · simp only [e, decide_false]
    refine beq_false_of_ne fun h' => e ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega

/-- The code after a candidate. -/
abbrev pTail (C : Nat) (L : Nat) : Prog isa :=
  .seq (.block (cmpF fP 4)) (.seq (.ite .eq (VG.Impl.Rsa.Arm.Keys.seqs [VG.Impl.Rsa.Arm.Keys.seqs [
      .block [ld .r1 fCounter], .block [.dp .add .r1 .r1 (.imm 1)], .block (st .r1 fCounter),
      .block [ld .r2 fOffset], .block [.dp .add .r2 .r2 (.imm (BitVec.ofNat 32 C))],
      .block (st .r2 fOffset), .block [.movw .r2 (BitVec.ofNat 16 (32 * L)), .cmp .r1 (.reg .r2)]],
    .ite .eq (.block (stImm fP 2)) (.block [])]) (.block [])) (.block (cmpF fP 4)))

/-- After a candidate that is not p: the next counter, or `fP` := 2 after the last. -/
theorem pCont_vp {d : Cfg} {j off C : Nat} (hC : C < 256) (hP : fP ∈ d.LS) (hPv : d.V fP = 4)
    (hCt : fCounter ∈ d.LS) (hCv : d.V fCounter = BitVec.ofNat 32 j) (hOf : fOffset ∈ d.LS)
    (hOv : d.V fOffset = BitVec.ofNat 32 off) (hj : j + 1 < 2 ^ 16) :
    VP (St G d X) (pTail C G.pLen)
      (fun σ s => if j + 1 = 32 * G.pLen then
          St G (((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset (BitVec.ofNat 32 (off + C))).setV fP
            (BitVec.ofNat 32 2)) X σ s ∧ isa.eval .eq s = some false
        else St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset (BitVec.ofNat 32 (off + C))) X σ s ∧
          isa.eval .eq s = some true) := by
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval .eq s = some true)
    (cmpF_vp (c := fun _ => d) (x := 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hP).trans hPv) fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e]; rfl⟩) ?_
  have hO2 : fOffset ∈ (d.setV fCounter (BitVec.ofNat 32 (j + 1))).LS := List.mem_cons_of_mem _ hOf
  by_cases e : j + 1 = 32 * G.pLen
  · refine VP.mono (G := fun σ s => St G (((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
        (BitVec.ofNat 32 (off + C))).setV fP (BitVec.ofNat 32 2)) X σ s ∧ isa.eval .eq s = some false) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_left_of_eq_true _ _ (eq_true e)]; exact h
    refine VP.seq (G := St G (((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
        (BitVec.ofNat 32 (off + C))).setV fP (BitVec.ofNat 32 2)) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (stImm_vp (c := fun _ => (d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
              (BitVec.ofNat 32 (off + C))) (fun σ s h => h.1.1.1) (by decide) (varOk_of (by decide))
              fun σ s t h h' _ => ⟨h', h.1.1.2⟩)
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := BitVec.ofNat 32 2) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp)).trans (by simp))
      fun σ s t ⟨h, x⟩ R m e' => ⟨⟨h.of_rest R m, x⟩, by rw [e']; rfl⟩
  · refine VP.mono (G := fun σ s => St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
        (BitVec.ofNat 32 (off + C))) X σ s ∧ isa.eval .eq s = some true) ?_
      (fun _ _ h => h) fun σ s h => by rw [ite_eq_right_of_eq_false _ _ (eq_false e)]; exact h
    refine VP.seq (G := St G ((d.setV fCounter (BitVec.ofNat 32 (j + 1))).setV fOffset
        (BitVec.ofNat 32 (off + C))) X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        rw [h₁.2, h₂.2]) (VP.seq ((pAdvance_vp hC hCt hCv hOf hOv hj).mono (fun σ s h => h.1.1) fun _ _ h => h)
          (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
            (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp [e] at z)
            (VP.block_nil fun σ s h => h.1.1)))
        (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z)) ?_
    exact cmpF_vp (x := 4) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV (by simp [hP])).trans (by
        show upd (upd d.V fCounter (BitVec.ofNat 32 (j + 1))) fOffset (BitVec.ofNat 32 (off + C)) fP = _; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hPv))
      fun σ s t ⟨h, x⟩ R m e' => ⟨⟨h.of_rest R m, x⟩, by rw [e']; rfl⟩

/-- After a candidate that ends the search (`fP` := 0 or 1). -/
theorem pExit_vp {d : Cfg} {v C : Nat} (hP : fP ∈ d.LS) (hPv : d.V fP = BitVec.ofNat 32 v) (hv : v < 4) :
    VP (St G d X) (pTail C G.pLen) (fun σ s => St G d X σ s ∧ isa.eval .eq s = some false) := by
  have ne : (BitVec.ofNat 32 v == BitVec.ofNat 32 4) = false := by
    refine beq_false_of_ne fun h' => ?_
    have := congrArg BitVec.toNat h'; simp only [BitVec.toNat_ofNat] at this; omega
  refine VP.seq (G := fun σ s => St G d X σ s ∧ isa.eval .eq s = some false)
    (cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 32 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
      (fun σ s h => (h.1.slotV hP).trans hPv) fun σ s t ⟨h, x⟩ R m e => ⟨⟨h.of_rest R m, x⟩, by rw [e, ne]⟩) ?_
  refine VP.seq (G := St G d X) (VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2])
    (VP.of_false fun σ s ⟨⟨_, e'⟩, z⟩ => by rw [e'] at z; simp at z) (VP.block_nil fun σ s h => h.1.1)) ?_
  exact cmpF_vp (c := fun _ => d) (x := BitVec.ofNat 32 v) (fun σ s h => h.1) (by decide) (by decide) (by decide)
    (fun σ s h => (h.1.slotV hP).trans hPv) fun σ s t h R m e => ⟨⟨h.1.of_rest R m, h.2⟩, by rw [e, ne]⟩

end

section
variable {Gh : Hash}

/-- Counter `j`'s candidate. -/
abbrev pCand (HO : HashOk Gh) (G : GP) (k j : Nat) : Nat :=
  pVal (Spec.Dsa.decodeBE (xBytes HO G k (1 + j * (cnt G + 1)))) (Spec.Dsa.decodeBE (qBytes G k))

/-- Whether counter `j`'s candidate is too short to test. -/
abbrev pShort (HO : HashOk Gh) (G : GP) (k j : Nat) : Prop := pCand HO G k j < 2 ^ (8 * G.pLen - 1)

/-- The witnesses read before counter `j`. -/
def pU (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat
  | 0 => u0
  | j + 1 => if pShort HO G k j then pU HO G k u0 j else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (_, r) => G.witLen - r.length
      | none => pU HO G k u0 j

/-- The search's iterations from counter `j`, with `m` counters after it. -/
def pCount (HO : HashOk Gh) (G : GP) (k u0 : Nat) : Nat → Nat → Nat
  | 0, j => j + 1
  | m + 1, j => if pShort HO G k j then pCount HO G k u0 m (j + 1) else
      match Spec.Dsa.probablePrime (pCand HO G k j) (G.witB.drop (pU HO G k u0 j)) with
      | some (false, _) => pCount HO G k u0 m (j + 1)
      | _ => j + 1

theorem pCount_gt (HO : HashOk Gh) (G : GP) (k u0 : Nat) : ∀ m j, j < pCount HO G k u0 m j
  | 0, j => by simp [pCount]
  | m + 1, j => by
    have := pCount_gt HO G k u0 m (j + 1)
    simp only [pCount]; split
    · omega
    · split <;> omega

/-- The search's frame words at counter `j`, with `u` witnesses read. -/
abbrev pBase (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Cfg :=
  { c with
    cl := [(G.qLen, padTail HO.md G.qLen), (pStart G 0, []), (sQ, qBytes G k)]
    live := []
    kls := [] }

abbrev pCfgJ (c : Cfg) (HO : HashOk Gh) (G : GP) (k j u : Nat) : Cfg :=
  ((((pBase c HO G k).setV fUsed (BitVec.ofNat 32 u)).setV fCounter (BitVec.ofNat 32 j)).setV fOffset
    (BitVec.ofNat 32 (1 + j * (cnt G + 1)))).setV fP 4

/-- The spec's search from counter `j`. -/
abbrev pSpec (HO : HashOk Gh) (G : GP) (k u0 j : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * G.pLen) (8 * G.qLen) (Spec.Dsa.decodeBE (qBytes G k)) (seedAt G k) j
    (G.witB.drop (pU HO G k u0 j))

/-- The arrays of p. -/
abbrev pAp (p q : Nat) : Nat → Nat := KU (KU (KU (KU (fun _ => 0) aOne 1) aPm1 (p - 1)) aE ((p - 1) / q)) aP p

/-- The stage after the search. -/
abbrev pFound (c : Cfg) (HO : HashOk Gh) (G : GP) (k p : Nat) : Cfg :=
  { c with
    cl := (sPBE, Spec.Rsa.i2osp p G.pLen) :: pRest HO.md G k
    A := pAp p (Spec.Dsa.decodeBE (qBytes G k))
    live := [aP, aE, aPm1, aOne]
    kls := [] }

abbrev pNone (c : Cfg) (HO : HashOk Gh) (G : GP) : Cfg :=
  { c with
    cl := [(G.qLen, padTail HO.md G.qLen)]
    live := []
    kls := [] }

def pFin (c : Cfg) (HO : HashOk Gh) (G : GP) (k : Nat) : Option (Option Nat × Spec.RsaKeyGen.Rand) → Cfg
  | some (some p, rest) => ((pFound c HO G k p).setV fUsed (BitVec.ofNat 32 (G.witLen - rest.length))).setV fP 1
  | some (none, r) => ((pNone c HO G).setV fUsed (BitVec.ofNat 32 (G.witLen - r.length))).setV fP 2
  | none => (pNone c HO G).setV fP 0

/-- The search with `r` iterations left of `N`. -/
abbrev pInv (c : Cfg) (HO : HashOk Gh) (G : GP) (k u0 N : Nat) (X : State → Prop) (r : Nat) (σ s : State) : Prop :=
  (r ≤ N ∧ N - r < 32 * G.pLen ∧ pCount HO G k u0 (32 * G.pLen - 1 - (N - r)) (N - r) = N ∧
    pSpec HO G k u0 (N - r) = pSpec HO G k u0 0 ∧ pU HO G k u0 (N - r) ≤ G.witLen) ∧
    St G (pCfgJ c HO G k (N - r) (pU HO G k u0 (N - r))) X σ s

/-- The words the search keeps apart from `c`'s. -/
abbrev PNot (c : Cfg) : Prop :=
  fUsed ∉ c.LS ∧ fCounter ∉ c.LS ∧ fOffset ∉ c.LS ∧ fP ∉ c.LS ∧ fRes ∉ c.LS ∧ fUsedOut ∉ c.LS ∧
    fUsedOut + 4 ∉ c.LS

theorem PNot.ne {c : Cfg} (h : PNot c) {o : Nat} (ho : o ∈ c.LS) :
    o ≠ fUsed ∧ o ≠ fCounter ∧ o ≠ fOffset ∧ o ≠ fP ∧ o ≠ fRes :=
  ⟨fun e => h.1 (e ▸ ho), fun e => h.2.1 (e ▸ ho), fun e => h.2.2.1 (e ▸ ho), fun e => h.2.2.2.1 (e ▸ ho),
    fun e => h.2.2.2.2.1 (e ▸ ho)⟩

/-- A stage's words agree with the search's at counter `j`. -/
theorem pCfgJ_V {c : Cfg} (hn : PNot c) {HO : HashOk Gh} {G : GP} {k j u : Nat} {LS : List Nat}
    {V : Nat → BitVec 32} (hLS : ∀ o ∈ c.LS, o ∈ LS) (h1 : fP ∈ LS) (h2 : fOffset ∈ LS) (h3 : fCounter ∈ LS)
    (h4 : fUsed ∈ LS) (vP : V fP = 4) (vO : V fOffset = BitVec.ofNat 32 (1 + j * (cnt G + 1)))
    (vC : V fCounter = BitVec.ofNat 32 j) (vU : V fUsed = BitVec.ofNat 32 u) (vc : ∀ o ∈ c.LS, V o = c.V o) :
    ∀ o ∈ (pCfgJ c HO G k j u).LS, o ∈ LS ∧ V o = (pCfgJ c HO G k j u).V o := by
  intro o ho
  change o ∈ fP :: fOffset :: fCounter :: fUsed :: c.LS at ho
  simp only [List.mem_cons] at ho
  rcases ho with rfl | rfl | rfl | rfl | ho
  · exact ⟨h1, by rw [vP]; simp [upd]⟩
  · exact ⟨h2, by rw [vO]; simp [upd, fOffset, fP]⟩
  · exact ⟨h3, by rw [vC]; simp [upd, fCounter, fOffset, fP]⟩
  · exact ⟨h4, by rw [vU]; simp [upd, fUsed, fCounter, fOffset, fP]⟩
  · obtain ⟨n1, n2, n3, n4, -⟩ := hn.ne ho
    exact ⟨hLS o ho, by rw [vc o ho]; simp [upd, n1, n2, n3, n4]⟩

end

end VG.Proof.Dsa.Arm.Gen
