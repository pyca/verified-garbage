module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSelV

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

theorem CrtExpL.w4S_ct (M : Mont) (Sq : MontS) : (CrtExpL.w4S M Sq).CT :=
  ⟨two_map (fun a => a) (fun _ _ h => h.1) (expLoopS_ct_P M Sq CrtSel.sse CrtSel.sse_ct),
    two_map (fun a => a) (fun _ _ h => h.1) (expLoopS_ct_Q M Sq CrtSel.sse CrtSel.sse_ct)⟩

theorem CrtExpL.w5S_ct (M : Mont) (Sq : MontS) : (CrtExpL.w5S M Sq).CT :=
  ⟨expLoop5S_ct_P M Sq CrtSel.avx tabSelV_ct, expLoop5S_ct_Q M Sq CrtSel.avx tabSelV_ct⟩

end VG.Proof.Bignum.X86_64
