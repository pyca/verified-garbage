module

public import VerifiedGarbage.Spec.Rc2.Contract

/-!
# RC2-CBC: the contracts of its internal functions

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.
-/

@[expose] public section

namespace VG.Proof.Rc2

open VG.Spec.Rc2

/-! ## CBC on blocks

The internal CBC functions' contracts are stated with `cbcBlocks`, on blocks as
vectors, returning the chaining value to continue from;
`Proof/Rc2/Stream.lean` proves it is CBC (`Spec.Cbc.encrypt`,
`Spec.Cbc.decrypt`), as `Spec.Rc2.update` states it. -/

def xorBlock (a b : Block) : Block :=
  Vector.ofFn fun i => a[i] ^^^ b[i]

/-- One block of CBC, returning `(output, next IV)`. Decryption retains the
original ciphertext as the next IV, including for an in-place caller. -/
def cbcStep (k : Schedule) (direction : Direction) (iv input : Block) : Block × Block :=
  match direction with
  | .encrypt => let out := encryptBlock k (xorBlock input iv); (out, out)
  | .decrypt => (xorBlock (decryptBlock k input) iv, input)

/-- CBC on complete blocks, including the final chaining value. On empty
input the output is empty and the IV is unchanged. -/
def cbcBlocks (k : Schedule) (direction : Direction) (iv : Block) :
    List Block → List Block × Block
  | [] => ([], iv)
  | b :: bs =>
    let (out, iv') := cbcStep k direction iv b
    let (rest, last) := cbcBlocks k direction iv' bs
    (out :: rest, last)

end VG.Proof.Rc2
