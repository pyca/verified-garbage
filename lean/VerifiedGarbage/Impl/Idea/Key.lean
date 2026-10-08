/-!
# IDEA key expansion: where each subkey bit comes from

Every bit of the encryption subkeys is a bit of the key (`Spec.Idea.expandKey`
rotates the key and takes 16-bit windows of it): `keyBit n b` is the bit of
the key, as a 128-bit number, at bit `b` of subkey `n`, and `keyLoc` where
that bit is in memory, as a bit of one of the key's two little-endian
quadwords. The implementations assemble the schedule from these positions.
-/

namespace VG.Impl.Idea

/-- The key bit (of `keyValue`, from the least significant) at bit `b` of
subkey `n`. -/
def keyBit (n b : Nat) : Nat := (16 * (7 - n % 8) + b + 128 - 25 * (n / 8) % 128) % 128

/-- Where key bit `i` is in memory: the quadword `j` (`[key + 8j]`) and the
bit `t` in it. -/
def keyLoc (i : Nat) : Nat × Nat :=
  let byte := 15 - i / 8
  (byte / 8, 8 * (byte % 8) + i % 8)

end VG.Impl.Idea
