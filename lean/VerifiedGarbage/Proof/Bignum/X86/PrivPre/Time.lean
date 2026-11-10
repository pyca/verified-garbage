module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
public import VerifiedGarbage.Impl.Bignum.X86.PrivPre
meta import VerifiedGarbage.Impl.Bignum.X86.PrivPre

/-! # The factors' values of an RSA private key on x86: constant time -/

@[expose] public section

namespace VG.Proof.Bignum.X86.PrivPre

open VG VG.X86 VG.Proof.Bignum.X86.CrtRt

theorem body_check : XCheck VG.Impl.Bignum.X86.PrivPre.primesBody := by dsimp only [XCheck]; taint_decide

end VG.Proof.Bignum.X86.PrivPre
