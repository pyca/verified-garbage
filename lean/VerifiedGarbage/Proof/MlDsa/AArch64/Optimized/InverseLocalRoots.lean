import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)

/-- Root vectors for the seven local groups, relative to the current table
cursor. Both readable ranges and exact field constants are explicit. -/
structure TableRoots (offset : Nat → Nat) (z : Nat → Nat → Int) (s : State) : Prop where
  q : ∀ e<4, vword (s.v .v31) e=8380417#32
  read : ∀ i : Fin 7, ∀ b, b=0 ∨ b=16 →
    InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (offset i.val+b)) 16
  root : ∀ i : Fin 7, ∀ e<4,
    vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 (offset i.val)) 16) e=BitVec.ofInt 32 (z i.val e)
  recip : ∀ i : Fin 7, ∀ e<4,
    vword (s.mem.read (s.gpr .x1+BitVec.ofNat 64 (offset i.val+16)) 16) e=
      BitVec.ofInt 32 (reciprocal (z i.val e))

theorem TableRoots.frame {offset : Nat → Nat} {z : Nat → Nat → Int} {s t : State}
    {clob : List VReg} (h : TableRoots offset z s) (hc : VChg clob s t) (hq : .v31∉clob) :
    TableRoots offset z t := by
  refine ⟨?_,?_,?_,?_⟩
  · intro e he
    rw [hc.get .v31 hq]
    exact h.q e he
  · simpa only [hc.rd,hc.wr,hc.gpr] using h.read
  · simpa only [hc.mem,hc.gpr] using h.root
  · simpa only [hc.mem,hc.gpr] using h.recip

theorem stage_q (i : Fin 7) : .v31∉stageClobs i.val := by
  exact (show ∀ i : Fin 7, .v31∉stageClobs i.val by decide +kernel) i

def tablePlan (offset : Nat → Nat) (z : Nat → Nat → Int)
    (ha : ∀ i : Fin 7, offset i.val%16=0)
    (hi : ∀ i : Fin 7, offset i.val+16<65536)
    (hz : ∀ i : Fin 7, ∀ e<4, 0≤z i.val e ∧ z i.val e<8380417) : RootPlan where
  load i := [.ldrq .v20 .x1 (offset i),.ldrq .v21 .x1 (offset i+16)]
  value := z
  invariant := TableRoots offset z
  range := hz
  stable i _ _ hc hs := hs.frame hc (stage_q i)
  load_ok i _ _ _ hs k := by
    refine rootLoads_ok (offset i.val) (ha i) (hi i) ?_ (hs.read i 16 (Or.inr rfl)) fun t ht hroot hrecip => ?_
    · simpa only [Nat.add_zero] using hs.read i 0 (Or.inl rfl)
    · have hp := hs.frame ht (by decide)
      refine k t ht hp ?_ ?_ hp.q
      · intro e he
        rw [hroot]
        exact hs.root i e he
      · intro e he
        rw [hrecip]
        exact hs.recip i e he

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
