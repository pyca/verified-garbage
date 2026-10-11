import VerifiedGarbage.Proof.Bignum.X86_64.FoldedPublic
import VerifiedGarbage.Proof.Bignum.X86_64.PdExp

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

theorem input_preserved {B : Addr} {w : Nat} {m m' : Mem}
    (h : Frm B (pExpRanges w) m m') (hb : B.toNat + slot w 8 ≤ 2^64) :
    wv m' B (slot w aX) w = wv m B (slot w aX) w := by
  apply h.wv_eq
  · intro r hr
    simp only [pExpRanges,pBitRanges,bitRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [slot,hdrBytes,sI,sV,sBit,Precomputed.sStarted,sFn,aX,aAcc,aTmp,aY] <;> omega
  · have := slot_le (w := w) (show aX < 8 by decide); omega

end VG.Proof.Bignum.X86_64.FoldedPublic
