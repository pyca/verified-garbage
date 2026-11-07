module

public import VerifiedGarbage.Impl.Dsa.Arm.Prevalidated

/-!
# Separate reusable private-key validation from DSA signing on ARMv7

`validate` is `vg_dsa_validate_private_key` (Spec/Dsa/PrevalidatedSign.lean):
the domain checker's entry, with the nonce field pointing at x, and its
public-width dispatch, with the signer's key checks (`Validate.signingKey`
and `Validate.privateKey`, whose nonce range check is then x's). `sign` is
`vg_dsa_sign_prevalidated`, one signing attempt of
`vg_dsa_sign_random_prevalidated`: the signer with those two checks, and
their two exponentiations, replaced by rebuilding q−2 and the nonce's range
check; the precondition that the exact key bytes validate makes the omitted
checks' mask true.
-/

@[expose] public section
namespace VG.Impl.Dsa.Arm.PrevalidatedSign
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Impl.Dsa.Layout

/-- `vg_dsa_validate_private_key(key, key_len, p_len, q_len, scratch,
scratch_len)`: the domain checker's arguments, with the nonce at x. -/
def validateEntry : List Instr :=
  Generate.checkEntry ++ [.ldr .r4 .r12 (Layout.field .x), .str .r4 .r12 (Layout.field .nonce)]

def validateSized (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen)
    (.ite .eq (.block [.mov .r0 (.imm 0)])
      (.seq (Validate.signingKey pLen qLen) (.seq (Validate.privateKey pLen qLen) (.block SignVerify.result))))

def validate : Prog isa := Core.sequence [
  .block validateEntry, Generate.dispatch validateSized Generate.widths, .block Entry.restore]

/-- Rebuild q−2 in this call's workspace and check the nonce's range;
validation is a precondition on the immutable key bytes, never a flag
recovered from scratch. -/
def compute (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.minus qLen .q 2 qMinusTwo,
  Validate.range qLen .q (.input .nonce),
  Core.sign pLen qLen,
  .seq (Validate.zero qLen (.local r) true) (Validate.zero qLen (.local s) true)]

def body (pLen qLen : Nat) : Prog isa :=
  .seq (compute pLen qLen)
    (.seq (SignVerify.writeScalar qLen r false) (.seq (SignVerify.writeScalar qLen s true) (.block SignVerify.result)))

def sized (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen) (.ite .eq (Entry.failure true) (body pLen qLen))

/-- The signer's public-width dispatch, with its failure for unsupported widths. -/
def dispatch : List (Nat × Nat) → Prog isa
  | [] => Entry.failure true
  | (pLen, qLen) :: rest =>
    .seq (Entry.widthMatch pLen qLen) (.ite .eq (sized pLen qLen) (dispatch rest))

/-- `vg_dsa_sign_prevalidated`, with `vg_dsa_sign`'s arguments. -/
def sign : Prog isa := Core.sequence [
  .block Entry.signEntry, dispatch Generate.widths, .block Entry.restore]

end VG.Impl.Dsa.Arm.PrevalidatedSign
