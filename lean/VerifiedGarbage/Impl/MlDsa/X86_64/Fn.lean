module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.Inst
public import VerifiedGarbage.Impl.MlDsa.X86_64.KeyGen.KeyGen
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify
public import VerifiedGarbage.Impl.MlDsa.X86_64.Message
public import VerifiedGarbage.Impl.MlDsa.X86_64.PkTr
public import VerifiedGarbage.Impl.MlDsa.X86_64.PreparedKey

/-! # ML-DSA on x86-64: the functions as emitted

Each function over an implementation of the polynomial arithmetic, then its
cleanup (`Impl.Scrub.X86_64.scrubAll v rb n`) at the level `v` of the
vector instructions of its code and the implementation's: every vector
register at that level and every caller-saved register but the `rb` bits of
the result cleared, and the `n` bytes of stack its frames and calls use
zeroed.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)

/-- `Spec.MlDsa.keyGenApi p`'s function as emitted, over the arithmetic `B`. -/
def keyGen (v : VecLevel) (B : Arith.Backend) (p : Spec.MlDsa.Params) : Prog isa :=
  scrubAll v 32 32 (KeyGen.keyGen (KeyGen.primsWith B) p)

/-- `vg_mldsa*_pk_tr` as emitted. -/
def pkTr (p : Spec.MlDsa.Params) : Prog isa := scrubAll .sse 0 32 (PkTr.pkTr p)

/-- `vg_mldsa*_sign` (`flag = 0`) or `vg_mldsa*_sign_prepared` (`flag = 1`) as
emitted, calling the signing over the functions `P` as `n`. -/
def signEntry (v : VecLevel) (n : String) (P : Sign.Prims) (p : Spec.MlDsa.Params) (flag : Nat) : Prog isa :=
  scrubAll v 32 40 (Sign.entry n (Sign.sign P p) flag)

/-- `vg_mldsa*_sign_message` or `vg_mldsa*_sign_message_prepared` as emitted. -/
def signMessage (v : VecLevel) (n : String) (P : Sign.Prims) (p : Spec.MlDsa.Params) (flag : Nat) : Prog isa :=
  scrubAll v 32 112 (Message.signMessage n (Sign.sign P p) p flag)

/-- `vg_mldsa*_verify` or `vg_mldsa*_verify_prepared` as emitted. -/
def verifyEntry (v : VecLevel) (n : String) (P : Verify.Prims) (p : Spec.MlDsa.Params) (flag : Nat) : Prog isa :=
  scrubAll v 32 40 (Verify.entry n (Verify.verify P p) flag)

/-- `vg_mldsa*_verify_message_cached` or `vg_mldsa*_verify_message_prepared` as emitted. -/
def verifyMessage (v : VecLevel) (n : String) (P : Verify.Prims) (p : Spec.MlDsa.Params) (flag : Nat) :
    Prog isa :=
  scrubAll v 32 112 (Message.verifyMessageCached n (Verify.verify P p) p flag)

/-- `vg_mldsa*_prepare_verifying_key` as emitted. -/
def preparePublic (v : VecLevel) (P : Verify.Prims) (p : Spec.MlDsa.Params) : Prog isa :=
  scrubAll v 0 32 (PreparedKey.preparePublic P p)

/-- `vg_mldsa*_prepare_signing_key` as emitted. -/
def prepareSecret (v : VecLevel) (P : Verify.Prims) (p : Spec.MlDsa.Params) : Prog isa :=
  scrubAll v 0 32 (PreparedKey.prepareSecret P p)

end VG.Impl.MlDsa.X86_64.Fn
