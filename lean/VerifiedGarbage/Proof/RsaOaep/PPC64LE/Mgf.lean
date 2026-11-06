module

public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfSteps
public import VerifiedGarbage.Proof.RsaOaep.Mask
public import VerifiedGarbage.Proof.Mgf1.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View

/-!
# RSA paddings on PPC64LE: MGF1

Untrusted: everything here is checked by Lean. Where `src` and `dst` lie
(`MFit`), the bytes of an exclusive-or (`xorAt_getD`) and those of `src`
from the view (`bytesAt_view`).
-/

@[expose] public section

namespace VG.Proof.RsaOaep.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaOaep.PPC64LE VG.WriteBytes
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_mov wp_nil eval_nonzero)
open VG.Proof.RsaPkcs1Sig (bytesAt_length)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.Mgf1 (ifp ifn)

/-- `src`, `srcLen`, `dst` and `dstLen`: in `EM`'s place, and apart. -/
structure MFit (src srcLen dst dstLen : Nat) : Prop where
  fs : src + srcLen ≤ 1024
  fd : dst + dstLen ≤ 1024
  sep : src + srcLen ≤ dst ∨ dst + dstLen ≤ src
  pos : 0 < dstLen

theorem xorAt_getD (m : Mem) (p q : Addr) {n i : Nat} (hi : i < n) :
    (xorAt m p q n).getD i 0 = m (p + BitVec.ofNat 64 i) ^^^ m (q + BitVec.ofNat 64 i) := by
  simp [xorAt, List.getD_eq_getElem?_getD, List.getElem?_range hi]

/-- The bytes of `src`, from the view. -/
theorem bytesAt_view (m : Mem) (S : Addr) (src n : Nat) :
    Spec.Rsa.bytesAt m (off S src) n = srcB (view m S) src n := by
  simp only [Spec.Rsa.bytesAt, srcB, view]
  exact List.map_congr_left fun i _ => by rw [off_add]

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

end

end VG.Proof.RsaOaep.PPC64LE
