module

public import VerifiedGarbage.Impl.Dsa.X86.Generate

/-! # Separate reusable public-key validation from DSA signature verification on i686

`validate` is the domain checker's entry and public-width dispatch, with
the verifier's checks of the domain and public value: its arguments, `key,
key_len, p_len, q_len, scratch, scratch_len`, are the checker's, with the
public value after the domain. `verify` is the verifier with those checks
replaced by rebuilding q−2: validation is a precondition on the immutable
key bytes, never a flag recovered from scratch.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.Prevalidated
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.Layout

def validate : Prog isa := Generate.checkParametersWith (Generate.checkSizedWith Validate.publicKey)

def compute (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.minus qLen .q 2 qMinusTwo,
  .seq (Validate.range qLen .q (.input .signature)) (Validate.range qLen .q .signatureS),
  Core.verify pLen qLen,
  Validate.equalValues qLen (.local u) (.input .signature)]

def body (pLen qLen : Nat) : Prog isa :=
  .seq (compute pLen qLen) (.block SignVerify.result)

def sized (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen) (.ite .e (Entry.failure false) (body pLen qLen))

def verify : Prog isa := Core.sequence [
  .block Entry.verifyEntry,
  Generate.dispatch sized [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)],
  .block Entry.restore]

end VG.Impl.Dsa.X86.Prevalidated
