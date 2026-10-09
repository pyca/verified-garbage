import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseHalfStore

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)

def canonicalValues (v : Vector (BitVec 128) 8) (q : BitVec 128) : Vector (BitVec 128) 8 :=
  Vector.ofFn fun j => canonicalVector v[j.val] q

def finalStoreCode : List Instr := halfCode 0 ++ halfCode 1

theorem halfWrite_both (v : Vector (BitVec 128) 8) (q : BitVec 128) (p : Addr) (m : Mem) :
    halfWrite 1 (halfValues 1 (halfValues 0 v q) q) p (halfWrite 0 (halfValues 0 v q) p m)=
      writeBank (canonicalValues v q) p 128 m := by rfl

theorem halfValues_both (v : Vector (BitVec 128) 8) (q : BitVec 128) :
    halfValues 1 (halfValues 0 v q) q=canonicalValues v q := by
  apply Vector.ext
  intro i hi
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem finalStore_ok {s : State} {rest : List Instr} {Q : State → Prop}
    {v : Vector (BitVec 128) 8} (hb : Bank s (regs 7) v)
    (hw : ∀ i : Fin 8, InRegions s.wr (s.gpr .x2+BitVec.ofNat 64 (128*i.val)) 16)
    (k : ∀ t, (∃ mid, VChg runRegs s mid ∧
        VMem mid t (writeBank (canonicalValues v (s.v .v31)) (s.gpr .x2) 128 s.mem)) →
      Bank t (regs 7) (canonicalValues v (s.v .v31)) → WP isa (.block rest) t Q) :
    WP isa (.block (finalStoreCode ++ rest)) s Q := by
  simp only [finalStoreCode,List.append_assoc]
  refine halfStore_ok 0 hb hw fun s₁ ⟨a,ha,hm₁⟩ hb₁ => ?_
  have hq : s₁.v .v31=s.v .v31 := by rw [hm₁.v,ha.get .v31 (by decide)]
  refine halfStore_ok 1 hb₁ ?_ fun t ⟨b,hb',hm₂⟩ hbt => ?_
  · intro i
    simpa only [hm₁.wr,hm₁.gpr,ha.wr,ha.gpr] using hw i
  · have hm₂' : VMem b t (writeBank (canonicalValues v (s.v .v31)) (s.gpr .x2) 128 s.mem) := by
      simpa only [hq,hm₁.gpr,ha.gpr,hm₁.mem,halfWrite_both] using hm₂
    refine k t (frame_store_trans ha hm₁ hb' hm₂') ?_
    simpa only [hq,halfValues_both] using hbt

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
