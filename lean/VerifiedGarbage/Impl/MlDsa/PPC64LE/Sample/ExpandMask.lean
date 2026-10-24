module

public import VerifiedGarbage.Impl.MlDsa.PPC64LE.Sample.Common

/-!
# ML-DSA on PPC64LE: `vg_mldsa_expand_mask_poly`

`expandMask(seed = r3, gamma1 = r4, a = r5, scratch = r6)` (see
`Common.lean` for the layout), as on 32-bit ARM: it squeezes 640 bytes of
SHAKE256 of the 66 bytes of the seed (5 blocks, which also hold the 576
bytes that `γ₁ = 2¹⁷` needs), and unpacks the first `32c` of them, `c = 18`
or `20` (chosen by a branch on the public `γ₁`), as `BitUnpack` with
`(a, b) = (γ₁ - 1, γ₁)`: coefficient `i` is `γ₁` minus the `c`-bit field `i`,
modulo `q`.

The loop (`emLoop c`) goes through groups of fields that end on a byte: 4
fields in 9 bytes for `c = 18`, 2 in 5 bytes for `c = 20`, with `r3` at the
group's first byte, `r4` at its first coefficient, `r6` counting down and
`r7` = `q`. Field `k` of a group starts at bit `c k`, in byte `⌊c k / 8⌋` at
bit `c k mod 8 ≤ 6`, so the three bytes from there hold it (`emField`): they
are read, shifted into place, and the field is cut out by a pair of shifts.
There is no branch on the data, and the addresses depend only on the pointers
and `γ₁`: it is constant time.
-/

@[expose] public section

namespace VG.Impl.MlDsa.PPC64LE.Sample

open VG.PPC64LE

/-- The `c`-bit field at bit `sh` of the 3 bytes at `r3 + o`, as the
coefficient `γ₁` (in `r27`) minus it, modulo `q`, stored to `r4 + 4 k`. -/
def emField (c o sh k : Nat) : List Instr :=
  ([.lbz .r8 .r3 o, .lbz .r9 .r3 (o + 1), .lbz .r10 .r3 (o + 2), .lsl .r9 .r9 8, .lsl .r10 .r10 16,
    .add .r8 .r8 .r9, .add .r8 .r8 .r10] : List Instr) ++
    (if sh = 0 then [] else [.lsr .d .r8 .r8 sh]) ++
    ([.lsl .r8 .r8 (64 - c), .lsr .d .r8 .r8 (64 - c), .sub .r8 .r27 .r8] : List Instr) ++ addQNeg .r8 ++
    ([.store .w .r8 .r4 (4 * k)] : List Instr)

/-- A group of fields: 4 for `c = 18`, 2 for `c = 20`. -/
def emGroup (c : Nat) : List Instr :=
  if c = 18 then emField 18 0 0 0 ++ emField 18 2 2 1 ++ emField 18 4 4 2 ++ emField 18 6 6 3
  else emField 20 0 0 0 ++ emField 20 2 4 1

/-- The bytes, the coefficients and the number of the groups. -/
def emBytes (c : Nat) : Nat := if c = 18 then 9 else 5
def emCoeffs (c : Nat) : Nat := if c = 18 then 4 else 2
def emCount (c : Nat) : Nat := if c = 18 then 64 else 128

def emBody (c : Nat) : List Instr :=
  emGroup c ++ [.addi .r3 .r3 (emBytes c), .addi .r4 .r4 (4 * emCoeffs c), .subi .r6 .r6 1]

/-- The fields, from the XOF output at `scratch + 840` to `a`. -/
def emLoop (c : Nat) : Prog isa :=
  .seq (.block ([.addi .r3 .r31 840, VG.Impl.Sha3.PPC64LE.Stream.mov .r4 .r30, .li .r6 (emCount c)] ++ loadQ))
    (.loop (.block (emBody c)) (.nonzero .d .r6))

def expandMask : Prog isa :=
  .seq (.block (pro .r6 .r5 .r3 [.li .r28 66] [VG.Impl.Sha3.PPC64LE.Stream.mov .r27 .r4]))
    (.seq (sponge 136 640)
      (.seq (.seq (.block [.lis .r12 2, .sub .r12 .r27 .r12]) (.ite (.zero .d .r12) (emLoop 18) (emLoop 20)))
        (.block epi)))

end VG.Impl.MlDsa.PPC64LE.Sample
