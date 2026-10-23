module

public import VerifiedGarbage.Impl.Aes.AArch64.Aese

/-!
# AES-GCM key setup with the Armv8 Cryptographic Extension, without calls

`vg_aes_gcm_init` for CPUs with FEAT_AES (`key = x0`, `key_len = x1`,
`ctx = x2`), a leaf that uses no stack: the key schedule as
`vg_aes_expand_key_scratch_aes` computes it (`Impl.Aes.AArch64.Aese.word`,
word by word in 32-bit registers, each stored as soon as it is computed),
and with it the hash subkey `H = CIPH_K(0¹²⁸)`, in `v3`, one round as soon
as its round key is complete, written to `ctx + 240` at the end.

Round key `j` is gathered in `v2` once its last word is computed: the
words in pairs in `x14` and `x15` (`w[4j] | w[4j+1] << 32`, with `orr` of a
rotation by 32, the words' registers having their upper halves zero), the
first pair in both halves of `v2` by `dup` (which depends on nothing in
`v2`, so the round keys do not wait on each other), the second inserted in
the upper half. Then `v3` takes the
round with it: `aese` and `aesmc` for `j < Nr − 1`, `aese` for
`j = Nr − 1`, and `eor` (`AddRoundKey`) for `j = Nr`. The rounds are off
the expansion's critical path, which they only follow.

`v0` stays zero (the round key of `SubWord`'s `aese`), `v1` is
`SubWord`'s, and the words' registers are those of the expansion; only
caller-saved registers are written. Every branch is on `key_len`, and
every address depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.AesGcm.AArch64.InitAese

open VG.AArch64
open VG.Impl.Aes.AArch64.Aese (wreg word)

/-- After word `i` of an `Nk`-word key: once round key `i / 4` is complete,
the round key into `v2` (its words paired in `x14` and `x15`), and its round
of `H` (in `v3`). -/
def hstep (nk i : Nat) : List Instr :=
  if i % 4 = 3 then
    [.logicRor .orr .x .x14 (wreg nk (i - 3)) (wreg nk (i - 2)) 32,
     .logicRor .orr .x .x15 (wreg nk (i - 1)) (wreg nk i) 32,
     .vop (.dup .d2 .v2 .x14), .vop (.ins .d2 .v2 1 .x15)] ++
    (if i / 4 + 2 ≤ nk + 6 then [.vop (.aese .v3 .v2), .vop (.aesmc .v3 .v3)]
     else if i / 4 + 1 = nk + 6 then [.vop (.aese .v3 .v2)]
     else [.vop (.logic .eor .v3 .v3 .v2)])
  else []

/-- The schedule of an `Nk`-word key, with `H`. -/
def initN (nk : Nat) : List Instr :=
  (List.range (4 * (nk + 7))).flatMap fun i => word nk i ++ hstep nk i

def init : Prog isa :=
  .seq (.block [.vop (.movi0 .v0), .vop (.movi0 .v3), .subImm .x .x9 .x1 24,
      .subImm .x .x10 .x1 32])
    (.seq (.ite (.zero .x .x9) (.block (initN 6))
        (.ite (.zero .x .x10) (.block (initN 8)) (.block (initN 4))))
      (.block [.strq .v3 .x2 240]))

end VG.Impl.AesGcm.AArch64.InitAese
