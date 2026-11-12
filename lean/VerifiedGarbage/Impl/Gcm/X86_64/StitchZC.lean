module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZR
public import VerifiedGarbage.Impl.Aes.X86_64.VaesZH

/-!
# Prepared AVX-512 GCM encryption: each group hashed from registers

`StitchZ.body48` hashes the ciphertext it stored one iteration before,
loaded back from the output. `bigC` keeps each group's ciphertext instead:
once a group is stored, its four registers, byte-reversed, are copied to
`zmm7`, `zmm1`, `zmm12` and `zmm15` (`copies`, `creg`), and the next group
hashes them between its rounds (`gqC`), so that no load reads what a store
just wrote.

The registers the copies take are those of the reduction constant and of
the counters' increment: the constant is loaded from `scratch + 832`
before each reduction, as `StitchZ.fin48` does, and the increment, kept at
`scratch + 896` (`enter`), into `zmm11` before each group's counters
(`grpC`). A pair of copies is hashed with one register for its powers,
`zmm13`, loaded twice (`pairC`): the products of the first copy are left
in `zmm11` (or `zmm8`), `zmm9` and the copy itself, and added with the
second's.

As in `StitchZ.body48`, the products of up to three groups are added
before they are reduced: `body48C` (while at least 48 blocks follow the
group in the copies), then `body32C` or `body16C` for the two or one
groups left, each with the powers of its blocks, `H'⁴⁸`–`H'`
(`StitchZR.powP48`). `bigC` starts from one group encrypted and not yet
hashed, as `StitchZ.big` does, and leaves one, with the registers as it
found them (`leave`).
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.StitchZC
open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Aes.X86_64.VaesZ (ctrsZ)
open VG.Impl.Gcm.X86_64.StitchZ (tab fin48 adv xorDataZM)
open VG.Impl.Gcm.X86_64.StitchZR (powP48)

/-- The register of copy `k` of a group: its blocks `4k`–`4k + 3`,
byte-reversed. -/
def creg : Nat → XReg
  | 0 => .xmm7 | 1 => .xmm1 | 2 => .xmm12 | _ => .xmm15

/-- Where the counters' increment is kept. -/
def incAt : MemOp := at_ .r11 896

/-- The products of the copy in `a` with the powers in `zmm13`: the middle
one added to `zmm9`, the low one left in `zmm11` and the high one in `a`;
for the first pair (`first`), with `Y` added to the copy, the middle one
written to `zmm9` and the low one to `zmm8`. -/
def halfA (first : Bool) (a : XReg) : List Instr :=
  if first then
    [.zop (.zbin .vpxord a a .xmm2),
     .zop (.vpclmulqdq .xmm9 a .xmm13 0x01), .zop (.vpclmulqdq .xmm11 a .xmm13 0x10),
     .zop (.zbin .vpxord .xmm9 .xmm9 .xmm11),
     .zop (.vpclmulqdq .xmm8 a .xmm13 0x00), .zop (.vpclmulqdq a a .xmm13 0x11)]
  else
    [.zop (.vpclmulqdq .xmm11 a .xmm13 0x01), .zop (.vpclmulqdq .xmm2 a .xmm13 0x10),
     .zop (.vpternlogd .xmm9 .xmm11 .xmm2 0x96),
     .zop (.vpclmulqdq .xmm11 a .xmm13 0x00), .zop (.vpclmulqdq a a .xmm13 0x11)]

/-- The products of the copy in `b` with the powers in `zmm13`, added with
those `halfA` left of the copy in `a` to `zmm8`, `zmm9` and `zmm10`. -/
def halfB (first : Bool) (a b : XReg) : List Instr :=
  (if first then
    [.zop (.vpclmulqdq .xmm2 b .xmm13 0x00), .zop (.zbin .vpxord .xmm8 .xmm8 .xmm2),
     .zop (.vpclmulqdq .xmm10 b .xmm13 0x11), .zop (.zbin .vpxord .xmm10 .xmm10 a)]
  else
    [.zop (.vpclmulqdq .xmm2 b .xmm13 0x00), .zop (.vpternlogd .xmm8 .xmm11 .xmm2 0x96),
     .zop (.vpclmulqdq .xmm2 b .xmm13 0x11), .zop (.vpternlogd .xmm10 a .xmm2 0x96)]) ++
  ([.zop (.vpclmulqdq .xmm11 b .xmm13 0x01), .zop (.vpclmulqdq .xmm2 b .xmm13 0x10),
    .zop (.vpternlogd .xmm9 .xmm11 .xmm2 0x96)] : List Instr)

/-- Copies `ka` and `ka + 1` of group `g` of three, each with its powers
(at `scratch + tab g + 64 k`). -/
def pairC (ka g : Nat) (first : Bool) : List Instr :=
  ([.vmovdqu32Load .xmm13 (at_ .r11 (tab g + 64 * ka))] : List Instr) ++ halfA first (creg ka) ++
  ([.vmovdqu32Load .xmm13 (at_ .r11 (tab g + 64 * (ka + 1)))] : List Instr) ++
  halfB first (creg ka) (creg (ka + 1))

/-- The GHASH work after round `j` of a group, on the copies of the group
before, group `g` of three: its pairs after rounds 4 and 7, the first
writing the products if it is the first of those added (`first`), and the
reduction after round 9 if it is the last (`last`). -/
def gqC (first last : Bool) (g j : Nat) : List Instr :=
  if j = 4 then pairC 0 g first else if j = 7 then pairC 2 g false
  else if j = 9 ∧ last = true then fin48 else []

/-- The four registers of the group stored, byte-reversed, in the copies. -/
def copies : List Instr :=
  [.zop (.zbin .vpshufb .xmm7 .xmm3 .xmm0), .zop (.zbin .vpshufb .xmm1 .xmm4 .xmm0),
   .zop (.zbin .vpshufb .xmm12 .xmm5 .xmm0), .zop (.zbin .vpshufb .xmm15 .xmm6 .xmm0)]

/-- Sixteen blocks at `rdx + 64 j` encrypted, in place or from
`rdx + r8 + 64 j` (`ld`), with `g i` after round `i`, and copied. -/
def grpC (j : Nat) (g : Nat → List Instr) (ld : Bool) : Prog isa :=
  .seq (.block (.vmovdqu32Load .xmm11 incAt :: ctrsZ .xmm14 .xmm0 .xmm11 aregs))
    (.seq (Aes.X86_64.VaesZH.aes aregs g) (.block (xorDataZM false .xmm13 ld aregs j ++ copies)))

/-- Three groups encrypted (at `rdx + 256`), each after the first hashing
the one before it, and the first the group at `rdx`. -/
def body48C (ld : Bool) : Prog isa :=
  .seq (grpC 4 (gqC true false 0) ld) (.seq (grpC 8 (gqC false false 1) ld) (.seq (grpC 12 (gqC false true 2) ld)
    (.block [.alu .add .rdx (.imm 768), .alu .sub .r9 (.imm 48), .alu .cmp .r9 (.imm 64)])))

/-- `body48C` with two groups. -/
def body32C (ld : Bool) : Prog isa :=
  .seq (grpC 4 (gqC true false 1) ld) (.seq (grpC 8 (gqC false true 2) ld)
    (.block [.alu .add .rdx (.imm 512), .alu .sub .r9 (.imm 32)]))

/-- `body48C` with one group. -/
def body16C (ld : Bool) : Prog isa :=
  .seq (grpC 4 (gqC true true 2) ld) (.block adv)

/-- The increment kept, and the group at `rdx` loaded into the copies,
byte-reversed. -/
def enter : List Instr :=
  [.vmovdqu32Store incAt .xmm15,
   .vmovdqu32Load .xmm7 (at_ .rdx 0), .vmovdqu32Load .xmm1 (at_ .rdx 64),
   .vmovdqu32Load .xmm12 (at_ .rdx 128), .vmovdqu32Load .xmm15 (at_ .rdx 192),
   .zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0), .zop (.zbin .vpshufb .xmm1 .xmm1 .xmm0),
   .zop (.zbin .vpshufb .xmm12 .xmm12 .xmm0), .zop (.zbin .vpshufb .xmm15 .xmm15 .xmm0)]

/-- The reduction constant and the increment back in their registers. -/
def leave : List Instr := [.vmovdqu32Load .xmm1 (at_ .r11 832), .vmovdqu32Load .xmm15 incAt]

/-- From how many blocks on (`r9`) `bigC` takes the groups after the first. -/
def bigMinC : BitVec 32 := 48

/-- At least 48 blocks, the first group encrypted and the powers of 48
blocks stored: the groups after it, all but the last hashed. -/
def bigRestC (ld : Bool := false) : Prog isa :=
  .seq (.block (enter ++ ([.alu .cmp .r9 (.imm 64)] : List Instr)))
    (.seq (.ite .b (.block []) (.loop (body48C ld) .ae))
      (.seq (.block [.alu .cmp .r9 (.imm 48)])
        (.seq (.ite .b (.block []) (body32C ld))
          (.seq (.block [.alu .cmp .r9 (.imm 32)])
            (.seq (.ite .b (.block []) (body16C ld)) (.block leave))))))

/-- At least 48 blocks, the first group encrypted: the powers of 48 blocks,
then `bigRestC`. -/
def bigC (ld : Bool := false) : Prog isa := .seq (.block powP48) (bigRestC ld)

end VG.Impl.Gcm.X86_64.StitchZC
