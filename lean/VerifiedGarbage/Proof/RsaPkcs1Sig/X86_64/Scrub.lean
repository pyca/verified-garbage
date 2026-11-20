module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignPrecomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.PrecomputedCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecPcCT
public import VerifiedGarbage.Proof.Rsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSASSA-PKCS1-v1_5 on x86-64, without secret residue

Each function as emitted (`Impl.RsaPkcs1Sig.X86_64.Fn`), over any
implementation of the private CRT operation (`CrtImpl`) or of the public
operation (`PublicImpl`), its whole stack wiped by its cleanup at the higher
of its own level and theirs. Its code is its code over a stub, with the
implementations' code where it calls them (`fill_calls`): the kernel
evaluates what the cleanup needs of the stub once, and each implementation
proves what it needs of its own code where it is defined (`CrtImpl.sideP`,
`PublicImpl.side`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.Proof.Rsa.X86_64

/-- The stack the implementations the signing function calls need: the CRT
operation's 8 bytes, the public operation's none. -/
def signStack : String → Nat := fun s => if s = "crt" then 8 else 0

/-- The signing function over stubs of the CRT and public operations. -/
def signStub : Prog isa :=
  Impl.RsaPkcs1Sig.X86_64.Sign.codeP "priv" (Impl.Rsa.X86_64.PrivChecked.codeP "crt" (.block []) "pub" (.block []))

/-- The level of the signing function's cleanup over `v`. -/
def signLevel (v : CrtImpl) : VecLevel := v.level.join v.pubOp.level

theorem sign_fill (v : CrtImpl) {k : Nat} (hc : calleeSide v.codeP k 8 = true)
    (hp : calleeSide v.pubOp.code k 0 = true) :
    Fill k signStack signStub
      (Impl.RsaPkcs1Sig.X86_64.Sign.codeP (Sgn.privNameP v) (Sgn.privCodeP v)) := by
  unfold signStub Sgn.privCodeP Sgn.pdName
  fill_calls

theorem sign_stub : stubSide signStub VecLevel.sse.level signStack 4456 [] = true := by lit_decide

/-- The signing function over `v` before its cleanup. -/
def signPlain (v : CrtImpl) : Unscrubbed Spec.RsaPkcs1Sig.signPrecomputedApi target where
  code := Impl.RsaPkcs1Sig.X86_64.Sign.codeP (Sgn.privNameP v) (Sgn.privCodeP v)
  verified := Sgn.signPrecomputed_verified v
  spSafe := Sgn.codeP_spSafe v

/-- `Spec.RsaPkcs1Sig.signPrecomputedApi`'s function as emitted over `v`
meets its contract in constant time and returns without secret residue. -/
theorem sign_scrubbed (v : CrtImpl) :
    VerifiedScrubbed target
      (Impl.RsaPkcs1Sig.X86_64.Fn.signPrecomputed (signLevel v) (Sgn.privNameP v) (Sgn.privCodeP v))
      (Spec.RsaPkcs1Sig.signPrecomputedApi.contract X86_64.abi 4456) 32 :=
  verifiedScrubbedAllFill (signPlain v) _ (Sgn.signPrecomputed_postOut _)
    (sign_fill v (calleeSide_mono (level_join_left _ _) (Nat.le_refl _) v.sideP)
      (calleeSide_mono (level_join_right _ _) (Nat.le_refl _) v.pubOp.side))
    (Nat.zero_le _) (Nat.le_refl _) (ha := sign_stub)

theorem sign_spSafe (v : CrtImpl) :
    (Impl.RsaPkcs1Sig.X86_64.Fn.signPrecomputed (signLevel v) (Sgn.privNameP v) (Sgn.privCodeP v)).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Sgn.codeP_spSafe v)

/-- The stack the public operation needs: none. -/
def pubStack : String → Nat := fun _ => 0

theorem verify_stub :
    stubSide (Impl.RsaPkcs1Sig.X86_64.Precomputed.code "pub" (.block [])) VecLevel.sse.level pubStack 2144 [] =
      true := by lit_decide

/-- `Spec.RsaPkcs1Sig.verifyPrecomputedApi`'s function as emitted over `v`
meets its contract in constant time and returns without secret residue. -/
theorem verify_scrubbed (v : PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Sig.X86_64.Fn.verifyPrecomputed v.level v.name v.code)
      (Spec.RsaPkcs1Sig.verifyPrecomputedApi.contract X86_64.abi 2144) 32 :=
  verifiedScrubbedAllFill (api := Spec.RsaPkcs1Sig.verifyPrecomputedApi)
    { code := Impl.RsaPkcs1Sig.X86_64.Precomputed.code v.name v.code
      verified := PcCT.code_verified v
      spSafe := PcCT.code_spSafe v } _ (Proof.Rsa.X86_64.Scrub.pkcs1VerifyOut _)
    (by have := v.side; unfold Impl.RsaPkcs1Sig.X86_64.Precomputed.code; fill_calls)
    (Nat.zero_le _) (Nat.le_refl _) (ha := verify_stub)

theorem verify_spSafe (v : PublicImpl) :
    (Impl.RsaPkcs1Sig.X86_64.Fn.verifyPrecomputed v.level v.name v.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (PcCT.code_spSafe v)

theorem recover_stub :
    stubSide (Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code "pub" (.block [])) VecLevel.sse.level pubStack 2144
      [] = true := by lit_decide

/-- `Spec.RsaPkcs1Sig.recoverPrecomputedApi`'s function as emitted over `v`
meets its contract in constant time and returns without secret residue. -/
theorem recover_scrubbed (v : PublicImpl) :
    VerifiedScrubbed target (Impl.RsaPkcs1Sig.X86_64.Fn.recoverPrecomputed v.level v.name v.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedApi.contract X86_64.abi 2144) 32 :=
  verifiedScrubbedAllFill (api := Spec.RsaPkcs1Sig.recoverPrecomputedApi)
    { code := Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code v.name v.code
      verified := RecPcCT.code_verified v
      spSafe := RecPcCT.code_spSafe v } _ (Proof.Rsa.X86_64.Scrub.pkcs1RecoverOut _)
    (by have := v.side; unfold Impl.RsaPkcs1Sig.X86_64.RecoverPrecomputed.code; fill_calls)
    (Nat.zero_le _) (Nat.le_refl _) (ha := recover_stub)

theorem recover_spSafe (v : PublicImpl) :
    (Impl.RsaPkcs1Sig.X86_64.Fn.recoverPrecomputed v.level v.name v.code).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (RecPcCT.code_spSafe v)

end VG.Proof.RsaPkcs1Sig.X86_64.Scrub
