import VerifiedGarbage.Impl.Idea.Key

/-!
# IDEA key expansion on 32-bit words

As `Impl/Idea/Key.lean`, for targets with 32-bit registers: each 32-bit word
of the schedule (two subkeys) is a fixed bit permutation of the key's four
little-endian 32-bit words. `keyLoc32 i` is where key bit `i` is in memory,
and `expandGroups32 w` the groups of bits of schedule word `w` with the same
source word and rotation.
-/

namespace VG.Impl.Idea

/-- Where key bit `i` is in memory: the 32-bit word `j` (`[key + 4j]`) and
the bit `t` in it. -/
def keyLoc32 (i : Nat) : Nat × Nat :=
  let byte := 15 - i / 8
  (byte / 4, 8 * (byte % 4) + i % 8)

/-- The source (word, bit) of bit `p` of schedule word `w`. -/
def expandSrc32 (w p : Nat) : Nat × Nat := keyLoc32 (keyBit (2 * w + p / 16) (p % 16))

/-- The rotation right that moves source bit `t` to `p`. -/
def rot32 (t p : Nat) : Nat := (t + 32 - p) % 32

/-- The groups of bits of word `w` with the same source word and rotation:
`(j, rotation, mask)`, in order of first bit. -/
def expandGroups32 (w : Nat) : List (Nat × Nat × Nat) :=
  (List.range 32).foldl (fun gs p =>
    let (j, t) := expandSrc32 w p
    let r := rot32 t p
    if gs.any (fun g => g.1 = j ∧ g.2.1 = r) then
      gs.map fun g => if g.1 = j ∧ g.2.1 = r then (g.1, g.2.1, g.2.2 ||| 2 ^ p) else g
    else gs ++ [(j, r, 2 ^ p)]) []

end VG.Impl.Idea
