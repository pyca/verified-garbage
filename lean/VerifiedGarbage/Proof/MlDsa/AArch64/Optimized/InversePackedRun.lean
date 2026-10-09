import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InversePackedBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

def packedRegs : List VReg := [.v0,.v1,.v2,.v3,.v4,.v5,.v6,.v7,.v16,.v17,.v18,.v19,.v20,.v21]
def packedOffset (g len : Nat) : Nat := (if len=1 then 0 else 128)+32*g

structure PackedRoots (s : State) (z : Nat → Nat → Nat → Int) : Prop where
  q : ∀ e<4, vword (s.v .v31) e=8380417#32
  range : ∀ g<4, ∀ len, len=1 ∨ len=2 → ∀ e<4, 0≤z g len e ∧ z g len e<8380417
  read : ∀ g<4, ∀ len, len=1 ∨ len=2 → ∀ b, b=0 ∨ b=16 →
    InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (packedOffset g len+b)) 16
  root : ∀ g<4, ∀ len, len=1 ∨ len=2 → ∀ e<4,
    vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 (packedOffset g len)) 16) e=BitVec.ofInt 32 (z g len e)
  recip : ∀ g<4, ∀ len, len=1 ∨ len=2 → ∀ e<4,
    vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 (packedOffset g len+16)) 16) e=BitVec.ofInt 32 (reciprocal (z g len e))

theorem PackedRoots.frame {s t : State} {z : Nat → Nat → Nat → Int}
    (h : PackedRoots s z) (hc : VChg packedRegs s t) : PackedRoots t z := by
  refine ⟨?_,h.range,?_,?_,?_⟩
  · intro e he
    rw [hc.get .v31 (by decide)]
    exact h.q e he
  · simpa only [hc.rd,hc.wr,hc.gpr] using h.read
  · simpa only [hc.mem,hc.gpr] using h.root
  · simpa only [hc.mem,hc.gpr] using h.recip

def packedGroupCode (g : Fin 4) (len : Nat) : List Instr :=
  [.ldrq .v20 .x1 (packedOffset g.val len),.ldrq .v21 .x1 (packedOffset g.val len+16)] ++
    VG.Impl.MlDsa.AArch64.Optimized.Inverse.packed (regs 0)[2*g.val] (regs 0)[2*g.val+1] len

theorem initial_apart : ∀ a : Fin 8, (regs 0)[a.val]∉[.v20,.v21] := by decide +kernel

theorem initial_small : ∀ a : Fin 8, (regs 0)[a.val]∉[.v16,.v17,.v18,.v19] := by decide +kernel

theorem initial_inj : Function.Injective (fun a : Fin 8 => (regs 0)[a.val]) := by
  exact (show ∀ a b : Fin 8, (regs 0)[a.val]=(regs 0)[b.val] → a=b by decide +kernel)

theorem initial_clobs : ∀ i j : Fin 8, packedClobs (regs 0) i j⊆packedRegs := by decide +kernel

theorem packedGroup_ok (g : Fin 4) (len : Nat) (hl : len=1 ∨ len=2)
    {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} {z : Nat → Nat → Nat → Int}
    (hb : Bank s (regs 0) v) (hr : PackedRoots s z)
    (k : ∀ t, VChg packedRegs s t → PackedRoots t z →
      Bank t (regs 0) (packedValues v ⟨2*g.val,by omega⟩ ⟨2*g.val+1,by omega⟩ len (z g.val len)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (packedGroupCode g len ++ rest)) s Q := by
  have ho : packedOffset g len%16=0 ∧ packedOffset g len+16<65536 := by
    rcases hl with rfl | rfl <;> simp [packedOffset] <;> omega
  let i : Fin 8 := ⟨2*g.val,by omega⟩
  let j : Fin 8 := ⟨2*g.val+1,by omega⟩
  simp only [packedGroupCode,List.append_assoc]
  refine rootLoads_ok _ ho.1 ho.2 ?_ (hr.read g.val g.isLt len hl 16 (Or.inr rfl)) fun s₁ hc₁ hz₁ hbr₁ => ?_
  · simpa only [Nat.add_zero] using hr.read g.val g.isLt len hl 0 (Or.inl rfl)
  · have hbank : Bank s₁ (regs 0) v := by
      intro a
      rw [hc₁.get _ (initial_apart a)]
      exact hb a
    refine packedBank_ok (regs 0) i j len (by intro h; have := congrArg Fin.val h; simp only [i,j] at this; omega)
      initial_inj initial_small hbank (hr.range g.val g.isLt len hl) ?_ ?_ ?_
      fun t hc₂ hbt => ?_
    · rw [hz₁]
      exact hr.root g.val g.isLt len hl
    · rw [hbr₁]
      exact hr.recip g.val g.isLt len hl
    · intro e he
      rw [hc₁.get .v31 (by decide)]
      exact hr.q e he
    · have hc : VChg packedRegs s t := VChg.mono (hc₁.trans hc₂) (by
        intro r hh
        rcases List.mem_append.mp hh with hh | hh
        · exact (show [.v20,.v21]⊆packedRegs by decide) hh
        · exact initial_clobs i j hh)
      exact k t hc (hr.frame hc) hbt

def packedSteps : List (Fin 4 × Nat) := [(0,1),(1,1),(2,1),(3,1),(0,2),(1,2),(2,2),(3,2)]

def packedCode (ps : List (Fin 4 × Nat)) : List Instr := ps.flatMap fun (g,len) => packedGroupCode g len

def packedRunValues (v : Vector (BitVec 128) 8) (z : Nat → Nat → Nat → Int) :
    List (Fin 4 × Nat) → Vector (BitVec 128) 8
  | [] => v
  | (g,len)::ps => packedRunValues
      (packedValues v ⟨2*g.val,by omega⟩ ⟨2*g.val+1,by omega⟩ len (z g.val len)) z ps

theorem packedRun_ok (ps : List (Fin 4 × Nat)) (hl : ∀ p∈ps, p.2=1 ∨ p.2=2)
    {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} {z : Nat → Nat → Nat → Int}
    (hb : Bank s (regs 0) v) (hr : PackedRoots s z)
    (k : ∀ t, VChg packedRegs s t → PackedRoots t z →
      Bank t (regs 0) (packedRunValues v z ps) → WP isa (.block rest) t Q) :
    WP isa (.block (packedCode ps ++ rest)) s Q := by
  induction ps generalizing s v with
  | nil => exact k s (VChg.refl _ _) hr hb
  | cons p ps ih =>
    simp only [packedCode,List.flatMap_cons,List.append_assoc]
    refine packedGroup_ok p.1 p.2 (hl p (by simp)) hb hr fun s₁ hc₁ hr₁ hb₁ => ?_
    refine ih (fun p hp => hl p (List.mem_cons_of_mem _ hp)) hb₁ hr₁ fun t hc₂ hr₂ hb₂ => ?_
    refine k t (VChg.mono (hc₁.trans hc₂) ?_) hr₂ hb₂
    intro r h
    simpa only [List.mem_append,or_self] using h

theorem packedSteps_valid : ∀ p∈packedSteps, p.2=1 ∨ p.2=2 := by
  simp only [packedSteps,List.mem_cons,List.not_mem_nil,or_false]
  intro p hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
