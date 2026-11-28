module

public import VerifiedGarbage.Impl.SlhDsa.AArch64.Thash4

/-!
# SLH-DSA (SHAKE) on AArch64: the working space, and code to build code

Every function of the SHAKE parameter sets works in the caller's `scratch`
(64 KiB, `Spec.SlhDsa.scratchWords`), whose base it keeps in `x19`, laid out
at the offsets below for the security parameter `n` (16, 24 or 32 bytes), as
on x86-64 (`Impl/SlhDsa/X86_64/Layout.lean`), but placed for AArch64's
addressing: every offset an instruction carries is an immediate of its
form, so the bytes the code reads one at a time (the digest, the digits,
the message of a layer, `M′`'s header) are below 4096 (`ldrb`/`strb`), the
32-bit fields of the lanes below 16384 (`str w`), and every region is
16-byte aligned for `ldr q`/`str q`:

* `work`, from 0: `thash4`'s working space (`Impl/SlhDsa/AArch64/Thash4.lean`),
  1024 bytes; there is no table of round constants, as the two-way
  permutation reads its own;
* the frames of the internal functions, from `oVars`;
* the frame of the functions the Rust code calls, `oTop`, which no internal
  function changes (as x86-64's `oKgSave`);
* `SK.seed`, `SK.prf`, `PK.seed` and `PK.root`, from `oKeys`;
* the digest, the digits, the message of a layer, the FORS indices and the
  stream state of `H_msg` and `PRF_msg`;
* the lanes `A`, from `oA`: four of `strideA` bytes, each
  `PK.seed ‖ ADRS ‖ M` for an `F`, `H` or `PRF` (`M` of at most `2n` bytes,
  from `n + 32`);
* the lanes `B`, from `oB`: four of `strideB` bytes, each
  `PK.seed ‖ ADRS ‖ M` for a `T_ℓ` (`M` of `len·n` or `k·n` bytes);
* the nodes of a tree, from `oN`, `nodeSlots` of `n` bytes, the roots of
  FORS's subtrees, and the signature key generation computes and discards.

The address in a lane is at `n` (`adrsOff`): its layer address in bytes 0–3,
tree address 4–15, type 16–19, key pair address 20–23, chain address or tree
height 24–27, hash address or tree index 28–31, each big-endian.

The code keeps every public value it addresses memory with, or branches on,
in a register (its loop counters and pointers in callee-saved registers,
which its callees keep), never in memory, so that an analysis that treats
memory as secret can follow them; values in memory (the frames' parameters,
the digest, the digits, the indices) reach only data and masks. Temporaries
are `x9`–`x15` (the copies' `x14`, `x15` and `v16`), which no value outlives
a call in.
-/

@[expose] public section

namespace VG.Impl.SlhDsa.AArch64

open VG.AArch64
open VG.Impl.SlhDsa.AArch64.Thash4 (mov)

/-- The layout of the working space for the security parameter `n`. -/
structure Layout where
  n : Nat
  /-- `len` of WOTS⁺ (35, 51 or 67 for `lg_w = 4`). -/
  len : Nat

namespace Layout

variable (L : Layout)

/-- The frames, `frameLen` bytes each: `0`: `wotsLeaves4`, `1`: `xmssTree`
and `xmssPk`, `2`: `forsSign` and `forsPk`, `3`: `levels`. -/
def oVars : Nat := 1024
def frameLen : Nat := 128
/-- The frame of the functions the Rust code calls: the saved registers, and
`M′`'s two header bytes at `oHdr`. -/
def oTop : Nat := 1536
def oHdr : Nat := oTop + 96
/-- `SK.seed`, `SK.prf`, `PK.seed`, `PK.root`, `n` bytes each (as the private key). -/
def oKeys : Nat := 1664
def oSkSeed : Nat := oKeys
def oSkPrf : Nat := oKeys + 32
def oPkSeed : Nat := oKeys + 64
def oPkRoot : Nat := oKeys + 96
def oDigest : Nat := 1792
def oDigits : Nat := 1856
def oMsg : Nat := 1984
/-- The FORS indices, 8 bytes each. -/
def oFidx : Nat := 2048
/-- The Keccak state of the sponge (200 bytes), and its working space (560). -/
def oStream : Nat := 2368
def oA : Nat := 3136
def strideA : Nat := 128
def oB : Nat := 3648
def strideB : Nat := 2208
def oN : Nat := 12480
/-- Room for the 512 nodes of the largest tree, and 8 more that a last
group of four lanes may write past the nodes of a level. -/
def nodeSlots : Nat := 520
def oRoots : Nat := oN + 32 * nodeSlots
/-- A signature key generation computes and discards, `(len + h′)·n` bytes. -/
def oSigTmp : Nat := oRoots + 32 * 32
/-- The end of what the functions use. -/
def oEnd : Nat := oSigTmp + 2432

/-- Where the address of a lane starts. -/
def adrsOff : Nat := L.n
/-- Where the message of a lane starts. -/
def msgOff : Nat := L.n + 32

/-- Lane `k` of the lanes `A`, and of `B`. -/
def laneA (k : Nat) : Nat := oA + strideA * k
def laneB (k : Nat) : Nat := oB + strideB * k

/-- Frame `f`: the saved registers (slots 0 to 10), then the function's
variables in memory, 8 bytes each, from 88. -/
def oFrame (f : Nat) : Nat := oVars + frameLen * f
def oSave (f i : Nat) : Nat := oFrame f + 8 * i
def oVar (f i : Nat) : Nat := oFrame f + 88 + 8 * i

end Layout

/-! ## Code to build code -/

/-- Save the registers `rs` (callee-saved, or `x30`) in the slots `o`,
`o + 8`, … of `scratch` in `b`. -/
def saveRegsAt (o : Nat) (b : Reg) (rs : List Reg) : List Instr :=
  rs.zipIdx.map fun (r, i) => .str .x r b (o + 8 * i)

/-- Restore them from `scratch` in `x19` (`x19`, the base, last, if it is one
of them). -/
def restoreRegsAt (o : Nat) (rs : List Reg) : List Instr :=
  (rs.zipIdx.filter (·.1 != .x19)).map (fun (r, i) => .ldr .x r .x19 (o + 8 * i)) ++
    (rs.zipIdx.filter (·.1 == .x19)).map (fun (r, i) => .ldr .x r .x19 (o + 8 * i))

/-- Save `rs` in frame `f`, with `scratch` in `b`. -/
def saveRegs (f : Nat) (b : Reg) (rs : List Reg) : List Instr := saveRegsAt (Layout.oSave f 0) b rs

/-- Restore them from frame `f`. -/
def restoreRegs (f : Nat) (rs : List Reg) : List Instr := restoreRegsAt (Layout.oSave f 0) rs

/-- `d ← v` (below `2⁶⁴`): a `movz`, and a `movk` for each further nonzero
16 bits. -/
def movV (d : Reg) (v : Nat) : List Instr :=
  .movz .x d (BitVec.ofNat 16 v) 0 ::
    ((List.range 3).filterMap fun h =>
      if v / 2 ^ (16 * (h + 1)) % 65536 = 0 then none
      else some (.movk .x d (BitVec.ofNat 16 (v / 2 ^ (16 * (h + 1)))) (h + 1)))

/-- `d ← b + off` (for `d ≠ b` if `off ≥ 4096`). -/
def lea (d b : Reg) (off : Nat) : List Instr :=
  if off < 4096 then [.addImm .x d b off] else movV d off ++ [.add .x d b d]

/-- The 32-bit value `v` with its bytes reversed: what a big-endian field
holding `v` reads as little-endian. -/
def bswap32 (v : Nat) : Nat :=
  (v % 256) * 2 ^ 24 + (v / 256 % 256) * 2 ^ 16 + (v / 65536 % 256) * 256 + v / 2 ^ 24 % 256

/-- `w9 ← u` for `u < 2³²`: a `movz`, and a `movk` if both halves are nonzero. -/
def movW9 (u : Nat) : List Instr :=
  if u % 65536 = 0 then [.movz .w .x9 (BitVec.ofNat 16 (u / 65536)) 1]
  else if u / 65536 = 0 then [.movz .w .x9 (BitVec.ofNat 16 u) 0]
  else [.movz .w .x9 (BitVec.ofNat 16 u) 0, .movk .w .x9 (BitVec.ofNat 16 (u / 65536)) 1]

/-- The 32-bit field at `b + d` set to `v` (below `2³²`), big-endian, through `w9`. -/
def setField (b : Reg) (d v : Nat) : List Instr := movW9 (bswap32 v) ++ [.str .w .x9 b d]

/-- The 32-bit field at `b + d` set to the low 32 bits of `r`, big-endian, through `w9`. -/
def setFieldR (b : Reg) (d : Nat) (r : Reg) : List Instr := [.rev32 .x9 r, .str .w .x9 b d]

/-- Copy `w` 8-byte words from `[s + d₁]` to `[t + d₂]`: two at a time
through `v16` where both offsets are multiples of 16, else one at a time
through `x14`. -/
def copyWords (t : Reg) (d₂ : Nat) (s : Reg) (d₁ w : Nat) : List Instr :=
  go w 0
where
  go : Nat → Nat → List Instr
  | 0, _ => []
  | 1, i => [.ldr .x .x14 s (d₁ + 8 * i), .str .x .x14 t (d₂ + 8 * i)]
  | m + 2, i =>
    if (d₁ + 8 * i) % 16 = 0 ∧ (d₂ + 8 * i) % 16 = 0 then
      [.ldrq .v16 s (d₁ + 8 * i), .strq .v16 t (d₂ + 8 * i)] ++ go m (i + 2)
    else [.ldr .x .x14 s (d₁ + 8 * i), .str .x .x14 t (d₂ + 8 * i)] ++ go (m + 1) (i + 1)

/-- Zero `w` 8-byte words at `[t + d]` (`d` a multiple of 16): two at a time
with the zeroed `v16`, and a last one with the zeroed `x14`. -/
def zeroWords (t : Reg) (d w : Nat) : List Instr :=
  .vop (.movi0 .v16) :: (List.range (w / 2)).map (fun i => .strq .v16 t (d + 16 * i)) ++
    (if w % 2 = 1 then [.movz .x .x14 0 0, .str .x .x14 t (d + 16 * (w / 2))] else [])

/-- `r ← r·n` (`n` 16, 24 or 32), through `tmp`. -/
def mulN (n : Nat) (r tmp : Reg) : List Instr :=
  if n = 24 then [.lsl .x tmp r 3, .lsl .x r r 4, .add .x r r tmp]
  else [.lsl .x r r (if n = 16 then 4 else 5)]

/-- `r ← -((r - 1) ≫ 63)`, through `tmp`: all ones if `r` was 0, and zero if
it was positive and below `2⁶³`. -/
def maskZero (r tmp : Reg) : List Instr :=
  [.subImm .x r r 1, .lsr .x r r 63, .movz .x tmp 0 0, .sub .x r tmp r]

/-- The arguments of `thash4` on the lanes at `x19 + o`, of `stride` bytes,
for messages of `len` bytes, each output written over the message from
`msgOff` on, with `work` at `x19`. -/
def thashArgs (L : Layout) (o stride len : Nat) : List Instr :=
  lea .x0 .x19 o ++ [.movz .x .x1 (BitVec.ofNat 16 stride) 0, .movz .x .x2 (BitVec.ofNat 16 len) 0,
    .addImm .x .x3 .x0 L.msgOff, mov .x4 .x19]

/-- A call of the variant's `thash4`, named `name`, on those lanes. -/
def thashCall (L : Layout) (name : String) (t4 : Prog isa) (o stride len : Nat) : Prog isa :=
  .seq (.block (thashArgs L o stride len)) (.call name t4)

end VG.Impl.SlhDsa.AArch64
