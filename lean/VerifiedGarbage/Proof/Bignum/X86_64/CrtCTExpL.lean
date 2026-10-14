module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# RSA with the CRT on x86-64: the exponentiations are constant time

`CrtExpL.w4` (`crtExpLoop_ct`, whose hypotheses `EPre5` implies) and
`CrtExpL.w5` (`crtExpLoop5_ct`, with the AVX2 selection's `tabSelV_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64

theorem CrtExpL.w4_ct (M : Mont) : (CrtExpL.w4 M).CT :=
  ⟨two_map (fun a => a) (fun _ _ h => h.1) (expLoop_ct_P M CrtSel.sse CrtSel.sse_ct),
    two_map (fun a => a) (fun _ _ h => h.1) (expLoop_ct_Q M CrtSel.sse CrtSel.sse_ct)⟩

theorem CrtExpL.w5_ct (M : Mont) : (CrtExpL.w5 M).CT :=
  ⟨expLoop5_ct_P M CrtSel.avx tabSelV_ct, expLoop5_ct_Q M CrtSel.avx tabSelV_ct⟩

end VG.Proof.Bignum.X86_64
