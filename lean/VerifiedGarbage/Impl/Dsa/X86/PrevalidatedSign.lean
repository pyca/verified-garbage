module

public import VerifiedGarbage.Impl.Dsa.X86.Generate

/-!
# Separate reusable private-key validation from DSA signing on i686

`validate` is `vg_dsa_validate_private_key` (Spec/Dsa/PrevalidatedSign.lean):
the domain checker's cdecl entry (`Generate.checkEntry`), with the nonce
field pointing at x, and its public-width dispatch, around the signer's key
checks (`Validate.publicKey` and `Validate.privateKey`, whose nonce range
check is then x's): every check signing makes of the key. `sign` is
`vg_dsa_sign_prevalidated`, the signer the randomized wrapper calls for a
validated key: the signer's program with those two checks, and their two
exponentiations, replaced by rebuilding q−2 and the nonce's range check;
the precondition that the exact key bytes validate makes the omitted checks'
mask true.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86.PrevalidatedSign
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Dsa.Layout

/-- Point the nonce field at x. -/
def nonceAtX : List Instr :=
  [.mov .eax (.mem (sc (Layout.field .x))), .store (sc (Layout.field .nonce)) .eax]

/-- `vg_dsa_validate_private_key(key, key_len, p_len, q_len, scratch,
scratch_len)`: the domain checker's arguments, with x after the public value. -/
def validateEntry : List Instr := Generate.checkEntry ++ nonceAtX

def validateCompute (pLen qLen : Nat) : Prog isa :=
  .seq (Validate.publicKey pLen qLen) (Validate.privateKey pLen qLen)

def validate : Prog isa := Core.sequence [
  .block validateEntry,
  Generate.dispatch (Generate.checkSizedWith validateCompute)
    [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)],
  .block Entry.restore]

/-- Rebuild q−2 and check the nonce's range; validation is a precondition on
the immutable key bytes, never a flag recovered from scratch. -/
def compute (pLen qLen : Nat) : Prog isa := Core.sequence [
  Validate.minus qLen .q 2 qMinusTwo,
  Validate.range qLen .q (.input .nonce),
  Core.sign pLen qLen,
  .seq (Validate.zero qLen (.local r) true) (Validate.zero qLen (.local s) true)]

def body (pLen qLen : Nat) : Prog isa :=
  .seq (compute pLen qLen)
    (.seq (SignVerify.writeScalar qLen r false)
      (.seq (SignVerify.writeScalar qLen s true) (.block SignVerify.result)))

def sized (pLen qLen : Nat) : Prog isa :=
  .seq (Shape.check pLen qLen) (.ite .e (Entry.failure true) (body pLen qLen))

/-- `vg_dsa_sign_prevalidated`: `vg_dsa_sign`'s arguments. -/
def sign : Prog isa := Core.sequence [
  .block Entry.signEntry,
  Generate.dispatch sized [(128, 20), (256, 28), (256, 32), (384, 32), (256, 20)],
  .block Entry.restore]

end VG.Impl.Dsa.X86.PrevalidatedSign
