module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulPairs
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Framework.Block

/-! Input loads and the first two rows of streamed multiplication. -/

-- separate module: closes the first pair's input-memory interface
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)

def streamClob : List Reg := [.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,
  .x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26]

theorem firstPair_loaded {s : State} {pa pb : Addr}
    (ha : Ptr s .x1 pa 72) (hb : Ptr s .x2 pb 72) :
    WP isa (.block (row0Loads++pair0Code)) s fun t =>
      regsVal t pair0Out = wordsVal s.mem pa 0 2 * wordsVal s.mem pb 0 9 ∧
      regsVal t bRegs = wordsVal s.mem pb 0 9 ∧
      t.gpr .x2=0 ∧ Keeps streamClob s t := by
  rw [row0Loads,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loadsR_ok [.x3,.x4] ha (a:=0) (by decide) (by decide) (by decide) (by decide))
    fun u ⟨au,ku,_⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (loadsR_ok bRegs (hb.of_keeps ku (by decide))
    (a:=0) (by decide) (by decide) (by decide) (by decide)) fun v ⟨bv,kv,_⟩ => ?_
  have av : (v.gpr .x3).toNat+2^64*(v.gpr .x4).toNat=wordsVal s.mem pa 0 2 := by
    rw [kv.gpr _ (by decide),kv.gpr _ (by decide)]
    change regsVal u [.x3,.x4]=wordsVal s.mem pa 0 2 at au
    simpa only [regsVal,Nat.mul_zero,Nat.add_zero] using au
  have bv' : regsVal v bRegs=wordsVal s.mem pb 0 9 := by
    change regsVal v bRegs=wordsVal u.mem pb 0 9 at bv
    rw [bv,ku.mem]
  refine WP.mono (pair0_value v) fun t ⟨prod,z,kt⟩ => ?_
  have bt : regsVal t bRegs=regsVal v bRegs := regsVal_congr fun r hr =>
    kt.gpr r ((show ∀r∈bRegs,r∉(.x2::.x14::pair0Out) from by decide) r hr)
  exact ⟨by rw [prod,av,bv'],bt.trans bv',z,
    (ku.mono (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide)))⟩

end VG.Proof.Mont.AArch64.P521Field
