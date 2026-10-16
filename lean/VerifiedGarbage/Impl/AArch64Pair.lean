module

public import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Pairing adjacent loads and stores of AArch64 code

`pairUp` replaces two adjacent `ldr`s (or `str`s) of the 64-bit words at
`[n, #o]` and `[n, #o + 8]` by one `ldp` (or `stp`), where `ldp` encodes the
offset and the first load overwrites neither `n` nor the second's register.
The pair runs to the same state, faulting where the two did, and leaks the
same two addresses, so a block runs exactly as it did
(`Proof/Framework/AArch64/Pair.lean`, `execBlock_pairUp`), and so does code
whose blocks are paired (`pairCode`, which leaves the functions it calls as
they are).
-/

@[expose] public section

namespace VG.Impl.AArch64Pair

open VG VG.AArch64

/-- `i; j` as one `ldp` or `stp`, if they are adjacent 64-bit loads (or stores) that it can do. -/
def fuse : Instr → Instr → Option Instr
  | .ldr .x a n o, .ldr .x b n' o' =>
    if n' = n ∧ o' = o + 8 ∧ a ≠ b ∧ a ≠ n ∧ o % 8 = 0 ∧ o ≤ 504 then some (.ldp a b n o) else none
  | .str .x a n o, .str .x b n' o' =>
    if n' = n ∧ o' = o + 8 ∧ o % 8 = 0 ∧ o ≤ 504 then some (.stp a b n o) else none
  | _, _ => none

/-- The block `is` with each pair of adjacent instructions `fuse` makes one of made one, from the first. -/
def pairUp : List Instr → List Instr
  | [] => []
  | [i] => [i]
  | i :: r@(j :: rest) =>
    match fuse i j with
    | some p => p :: pairUp rest
    | none => i :: pairUp r

/-- `c` with its blocks paired (`pairUp`); the functions it calls are left as they are. -/
def pairCode : Prog isa → Prog isa
  | .block is => .block (pairUp is)
  | .seq a b => .seq (pairCode a) (pairCode b)
  | .ite c t e => .ite c (pairCode t) (pairCode e)
  | .loop b c => .loop (pairCode b) c
  | .call n b => .call n b
  | .frame i b j => .frame i (pairCode b) j

end VG.Impl.AArch64Pair
