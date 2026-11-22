module

public import VerifiedGarbage.Impl.Camellia.X86.AesNiWide
meta import VerifiedGarbage.Impl.Camellia.X86.AesNiWide
public import VerifiedGarbage.Proof.Camellia.X86.AesNiMaps
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiMaps
public import VerifiedGarbage.Proof.Framework.X86.SseEquiv
public import VerifiedGarbage.Proof.Camellia.Words
meta import VerifiedGarbage.Proof.Camellia.Words
meta import VerifiedGarbage.Proof.Framework.X86.SseEquiv
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Camellia's four blocks by the AES S-box: the parts one pair after the other

Each of the four parts of `Impl.Camellia.X86.AesNiWide.crypt` computes what
a program here does that takes the two pairs, and a pair's steps, one after
the other, with `Impl.Camellia.X86.AesNi`'s registers (`refIn`, `refGroup`,
`refLayer`, `refOut`): the same operations on the same operands, which
the kernel checks (`in_equiv` … `out_equiv`, by
`Proof/Framework/X86/SseEquiv.lean`).

And what the straight-line steps of those programs leave in the registers,
as expressions of the bytes they start with, each compared by the kernel
with the expression the proofs use (`Proof/Framework/X86/ByteMap.lean`),
which is `AesNiMaps.lean`'s of one block for each quadword: the constants
this code reads are that file's.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNiWide

open VG VG.X86 VG.X86.ByteMap VG.Impl.Camellia.X86.AesNiWide
open VG.Impl.Camellia.X86.AesNi (tbr kr m0 x ld stx)
open VG.Impl.Modes.X86 (sb)

/-! ## The parts, a pair at a time -/

/-- The byte map at `t` (`wT` or `wI`) of every byte of `v`, to `b`; `v`,
`a`, `c` and `d` are lost. -/
def conv (v a b c d : XReg) (t : Nat) : List Instr :=
  [x .movdqa a m0, x .pand a v, sh .psrld v 4, x .pand v m0,
   tb b t, x .pshufb b a, tb c wM4, x .pand a c, x .pand c v,
   tb d (t + 16), x .pshufb d v, x .pxor b d,
   tb d (t + 32), x .pshufb d a, x .pxor b d,
   tb d (t + 48), x .pshufb d c, x .pxor b d]

/-- `v ⊕=` the eight bytes at `off` of the group's keys, in both
quadwords; `t` is lost. -/
def keyq (v t : XReg) (off : Nat) : List Instr := [lq t off, x .punpcklqdq t t, x .pxor v t]

/-- The shuffles `is` of map `k`'s bytes (in `acc`) into `y`, through `o`
for all but the last. -/
def shufs (acc o y : XReg) (k : Nat) : List Nat → List Instr
  | [] => []
  | [i] => [tb .xmm6 (wS k i), x .pshufb acc .xmm6, x .pxor y acc]
  | i :: is => [x .movdqa o acc, tb .xmm6 (wS k i), x .pshufb o .xmm6, x .pxor y o] ++ shufs acc o y k is

/-- Map `k` of the S-boxes' bytes (their nibbles in `xmm3` and `xmm2`) to
`acc`, and its shuffles `is` into `y`. -/
def flavor (acc o y : XReg) (k : Nat) (is : List Nat) : List Instr :=
  [tb acc (wN k), x .pshufb acc .xmm3, tb .xmm6 (wN k + 16), x .pshufb .xmm6 .xmm2, x .pxor acc .xmm6] ++
    shufs acc o y k is

/-- Round `i` of a group: `y ⊕=` the round's map of the S-boxes of `xr`, in
each quadword, and `xr ⊕=` the keys' difference (the last round's is left
to the part after the group). -/
def round (xr y : XReg) (i : Nat) : List Instr :=
  [x .movdqa .xmm2 xr] ++ (if i < 5 then keyq xr .xmm5 (16 + 8 * i) else []) ++
  [x .aesenclast .xmm2 m0, x .movdqa .xmm3 m0, x .pand .xmm3 .xmm2, sh .psrld .xmm2 4, x .pand .xmm2 m0] ++
    flavor .xmm4 .xmm5 y 3 [0, 1] ++ flavor .xmm5 .xmm4 y 2 [0, 1] ++ flavor .xmm4 .xmm5 y 1 [0, 1] ++
    flavor .xmm5 .xmm4 y 0 [0, 1, 2, 3]

/-- The six rounds of a group. -/
def rounds6 : List Instr :=
  round .xmm0 .xmm1 0 ++ (round .xmm1 .xmm0 1 ++ (round .xmm0 .xmm1 2 ++ (round .xmm1 .xmm0 3 ++
    (round .xmm0 .xmm1 4 ++ round .xmm1 .xmm0 5))))

/-- The byte of the scratch buffer where pair `p`'s half `h` is. -/
def plc (p h : Nat) : Nat := 512 + 32 * p + 16 * h

/-- The byte of the scratch buffer where block `b` is. -/
def blk (b : Nat) : Nat := 576 + 16 * b

/-- The six rounds of a group on pair `p`. -/
def pairGroup (p : Nat) : List Instr :=
  [ld .xmm0 sb (plc p 0), ld .xmm1 sb (plc p 1)] ++ rounds6 ++ [stx sb (plc p 0) .xmm0, stx sb (plc p 1) .xmm1]

def refGroup : List Instr := pairGroup 0 ++ pairGroup 1

/-- The halves of pair `p`'s two blocks, each in the order of `BSW`: the
first halves in `xmm0`, the second in `xmm2`. -/
def splitX : List Instr :=
  [tb .xmm3 wBSW, x .pshufb .xmm0 .xmm3, x .pshufb .xmm1 .xmm3, x .movdqa .xmm2 .xmm0, x .punpckhqdq .xmm2 .xmm1,
   x .punpcklqdq .xmm0 .xmm1]

/-- The two blocks in `xmm0` and `xmm1` to their halves in the rounds' form
with the first keys: the first halves in `xmm3`, the second in `xmm1`. -/
def inX : List Instr :=
  splitX ++ conv .xmm0 .xmm1 .xmm3 .xmm4 .xmm5 wT ++ keyq .xmm3 .xmm6 0 ++
    conv .xmm2 .xmm0 .xmm1 .xmm4 .xmm5 wT ++ keyq .xmm1 .xmm5 8

/-- Pair `p`'s two blocks to its places. -/
def pairIn (p : Nat) : List Instr :=
  [ld .xmm0 sb (blk (2 * p)), ld .xmm1 sb (blk (2 * p + 1))] ++ inX ++
    [stx sb (plc p 0) .xmm3, stx sb (plc p 1) .xmm1]

def refIn : List Instr := pairIn 0 ++ pairIn 1

/-- `v ⊕= ((v ∧ e) rotated left by one in its 32 bits, moved up 32 bits) ⊕
((v ∧ e) moved down 32 bits)`, `e` the eight bytes at `off` of the keys in
both quadwords (`AesNi.step`, of two blocks). -/
def step (v t s u : XReg) (off : Nat) : List Instr :=
  [lq t off, x .punpcklqdq t t, x .pand t v, x .movdqa s t, x .movdqa u t, sh .pslld u 1, sh .psrld t 31,
   x .por u t, sh .psllq u 32, sh .psrlq s 32, x .pxor v u, x .pxor v s]

/-- The half in `xmm0` (the second first takes the last round's keys) out
of the rounds' form, to `xmm3`. -/
def halfIn (h : Nat) : List Instr :=
  (if h = 1 then keyq .xmm0 .xmm1 56 else []) ++ conv .xmm0 .xmm1 .xmm3 .xmm4 .xmm5 wI

/-- FL (`h = 0`) or FL⁻¹ (`h = 1`) of both quadwords of `xmm3`, with the
masks of the group at hand. -/
def halfMid (h : Nat) : List Instr :=
  step .xmm3 .xmm0 .xmm1 .xmm2 (64 + 8 * h) ++ keyq .xmm3 .xmm0 (96 + 8 * h) ++
    step .xmm3 .xmm0 .xmm1 .xmm2 (80 + 8 * h)

/-- The bytes of `xmm3` back to the rounds' form with the next group's
first keys, in `xmm1`. -/
def halfOut (h : Nat) : List Instr := conv .xmm3 .xmm0 .xmm1 .xmm2 .xmm4 wT ++ keyq .xmm1 .xmm5 (112 + 8 * h)

/-- The FL layer on the half at byte `o` of the scratch buffer, the first
(`h = 0`) or the second. -/
def halfLayer (o h : Nat) : List Instr :=
  [ld .xmm0 sb o] ++ halfIn h ++ halfMid h ++ halfOut h ++ [stx sb o .xmm1]

/-- The FL layer on pair `p`: FL of its first halves, FL⁻¹ of its second. -/
def pairLayer (p : Nat) : List Instr := halfLayer (plc p 0) 0 ++ halfLayer (plc p 1) 1

def refLayer : List Instr := pairLayer 0 ++ pairLayer 1

/-- The halves in `xmm0` and `xmm1` (the second without the last round's
keys) to the two blocks' bytes, in `xmm0` and `xmm2`, with the last keys. -/
def joinX : List Instr :=
  keyq .xmm1 .xmm2 56 ++ conv .xmm0 .xmm2 .xmm3 .xmm4 .xmm5 wI ++ conv .xmm1 .xmm0 .xmm2 .xmm4 .xmm5 wI ++
    [x .movdqa .xmm0 .xmm2, x .punpcklqdq .xmm0 .xmm3, x .punpckhqdq .xmm2 .xmm3,
     tb .xmm4 wBSW, x .pshufb .xmm0 .xmm4, x .pshufb .xmm2 .xmm4, ld .xmm5 kr 64, x .pxor .xmm0 .xmm5,
     x .pxor .xmm2 .xmm5]

/-- Pair `p`'s halves after the last round to its two blocks. -/
def pairOut (p : Nat) : List Instr :=
  [ld .xmm0 sb (plc p 0), ld .xmm1 sb (plc p 1)] ++ joinX ++
    [stx sb (blk (2 * p)) .xmm0, stx sb (blk (2 * p + 1)) .xmm2]

def refOut : List Instr := pairOut 0 ++ pairOut 1

/-- The parts' parameters: the table at `ebx`, the places and the blocks in
the scratch buffer, the keys of a group at `esi`. -/
def eparams : SseEquiv.Params :=
  { tb := tbr, name := tableName, mreg := sb, mlen := 640, kreg := kr, klen := 128, slo := 512, shi := 640 }

/-! ## What the steps compute -/

/-- The steps' parameters: the table at `ebx`, the keys of a group at `esi`
(a quadword is read as the first of two). -/
def wparams : ByteMap.Params := { tb := tbr, name := tableName, kreg := kr, klen := 136 }

open VG.Proof.Camellia.X86.AesNi (regs₀ var slot sets kOf isA kind bswq cterms maskOk tblAt)
open VG.Impl.Camellia.X86.AesNi (oN oT oI)

/-- A round's output byte in slot `q` of `y`, as the code leaves it: `y`'s
own, and for each byte of the S-boxes' output that P takes, in `q`'s
quadword, its map by the two look-ups (`AesNi.roundRef`, of a quadword). -/
def roundRef (xr y : XReg) (q : Nat) : BV :=
  let j := slot (q % 8)
  ⟨var y q, (sets j).flatMap (fun i =>
    let k := kOf (isA j) (kind i)
    [⟨[.look (tblAt (oN k)), .xorc 0x0f#8, .and 0x0f#8, .aes], var xr (8 * (q / 8) + slot i)⟩,
     ⟨[.look (tblAt (oN k + 16)), .hi4, .aes], var xr (8 * (q / 8) + slot i)⟩]), 0#8⟩

/-- Round `i` of a group leaves `xr` with its eight key bytes added in both
quadwords (but the last round's), `y` as `roundRef`, and the mask. -/
def roundOk (xr y : XReg) (i : Nat) : Bool :=
  match run wparams regs₀ (round xr y i) with
  | none => false
  | some ρ =>
    !(ρ.get xr).sh && !(ρ.get y).sh &&
    ((List.range 16).all fun q => (get (ρ.get y).bs q).same (roundRef xr y q)) &&
    ((List.range 16).all fun q => (get (ρ.get xr).bs q).same
      ⟨var xr q ^^^ (if i < 5 then 2 ^ (128 + 16 + 8 * i + q % 8) else 0), [], 0#8⟩) && maskOk ρ

theorem round_all : ([0, 2, 4].all fun i => roundOk .xmm0 .xmm1 i) = true ∧
    ([1, 3, 5].all fun i => roundOk .xmm1 .xmm0 i) = true := by
  constructor <;> lit_decide

/-- The byte of the block in `xmm0` or `xmm1` (the quadword's) that `BSW`
puts in slot `r` of the block's halves. -/
def blockVar (q r : Nat) : Nat := var (xreg (q / 8)) (bswq r)

def inOk : Bool :=
  match run wparams regs₀ inX with
  | none => false
  | some ρ => !(ρ.get .xmm3).sh && !(ρ.get .xmm1).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm3).bs q).same
      ⟨2 ^ (128 + q % 8), cterms oT q (blockVar q (q % 8)), 0#8⟩) &&
    ((List.range 16).all fun q => (get (ρ.get .xmm1).bs q).same
      ⟨2 ^ (128 + (8 + q % 8)), cterms oT q (blockVar q (q % 8 + 8)), 0#8⟩) && maskOk ρ

def halfInOk (h : Nat) : Bool :=
  match run wparams regs₀ (halfIn h) with
  | none => false
  | some ρ => !(ρ.get .xmm3).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm3).bs q).same
      ⟨0, cterms oI q (var .xmm0 q ^^^ (if h = 1 then 2 ^ (128 + (56 + q % 8)) else 0)), 0#8⟩) && maskOk ρ

def halfOutOk (h : Nat) : Bool :=
  match run wparams regs₀ (halfOut h) with
  | none => false
  | some ρ => !(ρ.get .xmm1).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm1).bs q).same
      ⟨2 ^ (128 + (112 + 8 * h + q % 8)), cterms oT q (var .xmm3 q), 0#8⟩) && maskOk ρ

/-- Byte `q` of block `L` of a pair, from its halves: the second half's
slot (with the last round's keys) for the block's first eight bytes. -/
def joinRef (L q : Nat) : BV :=
  let r := bswq q
  if r < 8 then ⟨2 ^ (128 + (64 + q)), cterms oI r (var .xmm1 (8 * L + r) ^^^ 2 ^ (128 + (56 + r))), 0#8⟩
  else ⟨2 ^ (128 + (64 + q)), cterms oI r (var .xmm0 (8 * L + (r - 8))), 0#8⟩

def joinOk : Bool :=
  match run wparams regs₀ joinX with
  | none => false
  | some ρ => !(ρ.get .xmm0).sh && !(ρ.get .xmm2).sh &&
    ((List.range 16).all fun q => (get (ρ.get .xmm0).bs q).same (joinRef 0 q)) &&
    ((List.range 16).all fun q => (get (ρ.get .xmm2).bs q).same (joinRef 1 q)) && maskOk ρ

theorem conv_all : inOk = true ∧ halfInOk 0 = true ∧ halfInOk 1 = true ∧ halfOutOk 0 = true ∧
    halfOutOk 1 = true ∧ joinOk = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> lit_decide

/-- The mask, from the table. -/
def m0Ok : Bool :=
  match run wparams Regs.init [tb m0 wM0] with
  | none => false
  | some ρ => maskOk ρ

theorem m0_ok : m0Ok = true := by lit_decide

/-! ## `prepare`'s copy -/

/-- The copy reads the schedule at `eax` and stores in the scratch buffer. -/
def cparams : ByteMap.Params := { tb := tbr, name := Impl.Camellia.X86.AesNi.tableName, kreg := .eax, klen := 272 }
def coparams : OParams := { oreg := sb, olen := 816 }

/-- The copy `c` stores, for each `u < n`, at byte `16 u` of the schedule's
copy the 16 bytes at `16 (src u)` of the schedule, their halves exchanged
when `sw u`, and nothing else. -/
def copyOk (c : List Instr) (n : Nat) (src : Nat → Nat) (sw : Nat → Bool) : Bool :=
  match runS cparams coparams (Regs.init, []) c with
  | none => false
  | some σ => outsIn σ.2 544 816 && (List.range n).all fun u =>
    decide (src u ≤ 16) && outOk σ.2 (544 + 16 * u) (fun q => .var (128 + (16 * src u + (if sw u then (q + 8) % 16 else q))))

theorem copy_all : copyOk copyEnc 17 (fun u => u) (fun _ => false) = true ∧
    copyOk (copyDec 3) 13 (fun u => 12 - u) (fun u => decide (0 < u ∧ u < 12)) = true ∧
    copyOk (copyDec 4) 17 (fun u => 16 - u) (fun u => decide (0 < u ∧ u < 16)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> lit_decide

/-- The words of the copy are the schedule's in decryption's order. -/
theorem perm_all :
    ((List.range 26).all fun k => 2 * (12 - k / 2) + (if decide (0 < k / 2 ∧ k / 2 < 12) = true then 1 - k % 2 else k % 2) ==
      Proof.Camellia.decPerm 3 k) = true ∧
    ((List.range 34).all fun k => 2 * (16 - k / 2) + (if decide (0 < k / 2 ∧ k / 2 < 16) = true then 1 - k % 2 else k % 2) ==
      Proof.Camellia.decPerm 4 k) = true := by
  constructor <;> decide

/-! ## The parts as they run -/

theorem in_equiv : SseEquiv.equiv eparams refIn wIn [(m0, m0)] = true := by lit_decide
theorem group_equiv : SseEquiv.equiv eparams refGroup wGroup [(m0, m0)] = true := by lit_decide
theorem layer_equiv : SseEquiv.equiv eparams refLayer wLayer [(m0, m0)] = true := by lit_decide
theorem out_equiv : SseEquiv.equiv eparams refOut wOut [(m0, m0)] = true := by lit_decide

end VG.Proof.Camellia.X86.AesNiWide
