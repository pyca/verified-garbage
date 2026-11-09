module

public import VerifiedGarbage.Impl.Dsa.Arm.Generate

/-! # Separate reusable public-key validation from DSA signature verification on ARMv7

`validate` is the domain checker's entry and public-width dispatch, with
the verifier's checks of the domain and public value (`PublicValidation.call`):
its arguments, `key, key_len, p_len, q_len, scratch, scratch_len`, are the
checker's, with the public value after the domain. `verify` is the verifier
with those checks replaced by rebuilding q−2: validation is a precondition on
the immutable key bytes, never a flag recovered from scratch.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.Prevalidated
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Impl.Dsa.Layout

def validateSized (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen)
    (.ite .eq (.block [.mov .r0 (.imm 0)]) (.seq (PublicValidation.call pLen qLen) (.block SignVerify.result)))

/-- `vg_dsa_validate_public_key(key, key_len, p_len, q_len, scratch,
scratch_len)`. -/
def validate : Prog isa := Core.sequence [
  .block Generate.checkEntry, Generate.dispatch validateSized Generate.widths, .block Entry.restore]

def compute (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.minus qLen .q 2 qMinusTwo,
  .seq (Validate.range qLen .q (.input .signature)) (Validate.range qLen .q .signatureS),
  Core.verify pLen qLen,
  Validate.equalValues qLen (.local u) (.input .signature)]

def body (pLen qLen : Nat) : Prog isa := .seq (compute pLen qLen) (.block SignVerify.result)

def sized (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen) (.ite .eq (Entry.failure false) (body pLen qLen))

/-- `vg_dsa_verify_prevalidated`, with `vg_dsa_verify`'s arguments. -/
def verify : Prog isa := Core.sequence [
  .block Entry.verifyEntry, Generate.dispatch sized Generate.widths, .block Entry.restore]

end VG.Impl.Dsa.Arm.Prevalidated
