module

/-!
# IDEA key expansion: where each subkey bit comes from

Every bit of the encryption subkeys is a bit of the key (`Spec.Idea.expandKey`
rotates the key and takes 16-bit windows of it): `keyBit n b` is the bit of
the key, as a 128-bit number, at bit `b` of subkey `n`, and `keyLoc` where
that bit is in memory, as a bit of one of the key's two little-endian
quadwords. The implementations assemble the schedule from these positions,
a group of bits with the same source quadword and rotation at a time
(`expandGroups`). `invOp` says what each decryption subkey is
(`Spec.Idea.invertKey`): a copy, the negation or the inverse of which
encryption subkey.
-/

@[expose] public section

namespace VG.Impl.Idea

/-- The key bit (of `keyValue`, from the least significant) at bit `b` of
subkey `n`. -/
def keyBit (n b : Nat) : Nat := (16 * (7 - n % 8) + b + 128 - 25 * (n / 8) % 128) % 128

/-- Where key bit `i` is in memory: the quadword `j` (`[key + 8j]`) and the
bit `t` in it. -/
def keyLoc (i : Nat) : Nat × Nat :=
  let byte := 15 - i / 8
  (byte / 8, 8 * (byte % 8) + i % 8)

/-- The source (quadword, bit) of bit `p` of schedule quadword `q`. -/
def expandSrc (q p : Nat) : Nat × Nat := keyLoc (keyBit (4 * q + p / 16) (p % 16))

/-- The rotation right that moves source bit `t` to `p`. -/
def rot (t p : Nat) : Nat := (t + 64 - p) % 64

/-- The groups of bits of quadword `q` with the same source quadword and
rotation: `(j, rotation, mask)`, in order of first bit. -/
def expandGroups (q : Nat) : List (Nat × Nat × Nat) :=
  (List.range 64).foldl (fun gs p =>
    let (j, t) := expandSrc q p
    let r := rot t p
    if gs.any (fun g => g.1 = j ∧ g.2.1 = r) then
      gs.map fun g => if g.1 = j ∧ g.2.1 = r then (g.1, g.2.1, g.2.2 ||| 2 ^ p) else g
    else gs ++ [(j, r, 2 ^ p)]) []

inductive Op | copy | neg | inv
  deriving DecidableEq, Repr

/-- Decryption subkey `n`: the operation, and the encryption subkey it
applies to (`Spec.Idea.invertKey`). -/
def invOp (n : Nat) : Op × Nat :=
  let r := n / 6
  let e := 6 * (8 - r)
  let ends := r = 0 ∨ r = 8
  match n % 6 with
  | 0 => (.inv, e)
  | 1 => (.neg, if ends then e + 1 else e + 2)
  | 2 => (.neg, if ends then e + 2 else e + 1)
  | 3 => (.inv, e + 3)
  | 4 => (.copy, 6 * (7 - r) + 4)
  | _ => (.copy, 6 * (7 - r) + 5)

end VG.Impl.Idea
