module

public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Poly1305: PPC64LE implementation

The AArch64 implementation's algorithm (`Impl/Poly1305/AArch64.lean`), as in
poly1305-donna-32: the model has no carry bit, so the arithmetic is in radix
`2²⁶`: the accumulator `h` and the clamped `r` are five 26-bit limbs (`h = h0
+ 2²⁶ h1 + … + 2¹⁰⁴ h4`), their products are 64-bit `mulld`s, and carries are
shifts and masks.

The state (`r3`, 128 bytes, see `VG.Spec.Poly1305.Buffered`):

* `[0, 24)`: the accumulator `h = w0 + 2⁶⁴ w1 + 2¹²⁸ w2`, fully reduced
  (`h < p`) between calls, in three 64-bit words;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 72)`: the buffer: the message's last bytes that do not fill a block,
  padded in place in `finalize`;
* `[72, 108)`: the limbs `r0, …, r4` and `s1, …, s4` (`sj = 5 rj`) of the
  clamped `r`, as 32-bit words, computed on entry.

Registers: `r7`–`r11` hold the limbs of `h`, `r12` and `r14`–`r17` the sums
of products `d0, …, d4` (and other limbs in between), `r18`, `r19` and `r0`
are temporaries and `r20` holds the mask `2²⁶ - 1`. Each function takes a
working space (`blocks` in `r6`, `update` in `r7`, `finalize` in `r6`), where
it saves the nonvolatile `r14`–`r21` first; it keeps the working space's
address in `r21` and restores them from there last.

Each call converts `h` into limbs (`loadH`). A block `m` is absorbed as in
poly1305-donna-32: `h += m + pad · 2¹²⁸`, then `dk = Σ_{i+j=k} hi rj +
Σ_{i+j=k+5} hi sj` (as `2¹³⁰ ≡ 5` modulo `p = 2¹³⁰ - 5`), with the
coefficients loaded from the state, then the carries are propagated from
`d0` to `d4` and the carry out of `d4` is added, times 5, to `h0`. Between
blocks, `h1 < 2²⁷` and the other limbs are less than `2²⁶`.

Before `h` is stored, it is reduced fully (`reduce`): its limbs are
normalized (except that `h4` may be `2²⁶`), `g = h + 5` is computed with
carries, and `g - 2¹³⁰` is selected, with a mask and without a branch, if
`g ≥ 2¹³⁰`. The limbs are then packed into 64-bit words (`pack`).

The only branches are on the block count, the number of bytes buffered
(`count mod 16`) and the lengths, and every address is a pointer plus a
constant, or plus a count, so only the pointers, `count` and the lengths can
affect timing.
-/

@[expose] public section

namespace VG.Impl.Poly1305.PPC64LE

open VG.PPC64LE

/-- The limbs of `h`. -/
def H : List Reg := [.r7, .r8, .r9, .r10, .r11]
/-- The sums of products, and other limbs. -/
def D : List Reg := [.r12, .r14, .r15, .r16, .r17]

/-- `2²⁶ - 1` into `r20`. -/
def mask : List Instr := [.lis .r20 0x3ff, .ori .r20 .r20 0xffff]

/-- The 64-bit constant `c` into `d`. -/
def const64 (d : Reg) (c : BitVec 64) : List Instr :=
  [.lis d (c.extractLsb' 48 16), .ori d d (c.extractLsb' 32 16), .lsl d d 32,
    .oris d d (c.extractLsb' 16 16), .ori d d (c.extractLsb' 0 16)]

/-- The 128-bit number at `[n + off]` into `r18` (low word) and `r19`. -/
def load2 (n : Reg) (off : Nat) : List Instr := [.load .d .r18 n off, .load .d .r19 n (off + 8)]

/-- The five 26-bit limbs of the 128-bit `r18 + 2⁶⁴ r19` into `r12`, `r14`–`r17`
(the last less than `2²⁴`), using `r0`. -/
def split : List Instr := [
  .logic .and .r12 .r18 .r20,
  .lsr .d .r14 .r18 26, .logic .and .r14 .r14 .r20,
  .lsr .d .r15 .r18 52, .lsl .r0 .r19 12, .add .r15 .r15 .r0,
  .logic .and .r15 .r15 .r20,
  .lsr .d .r16 .r19 14, .logic .and .r16 .r16 .r20,
  .lsr .d .r17 .r19 40]

/-- The offsets of the limbs `rj` and `sj` in the state. -/
def rOff (j : Nat) : Nat := 72 + 4 * j
def sOff (j : Nat) : Nat := 88 + 4 * j

/-- `r` clamped, in `r18, r19`. -/
def clampR : List Instr :=
  const64 .r0 0x0ffffffc0fffffff ++ ([.logic .and .r18 .r18 .r0] : List Instr) ++
  const64 .r0 0x0ffffffc0ffffffc ++ ([.logic .and .r19 .r19 .r0] : List Instr)

/-- `sj = 5 rj` into `r7`–`r10`, from `rj` in `r14`–`r17`. -/
def times5 : List Instr :=
  [.lsl .r7 .r14 2, .add .r7 .r7 .r14, .lsl .r8 .r15 2, .add .r8 .r8 .r15,
    .lsl .r9 .r16 2, .add .r9 .r9 .r16, .lsl .r10 .r17 2, .add .r10 .r10 .r17]

/-- `r0, …, r4` (in `r12`, `r14`–`r17`) and `s1, …, s4` (in `r7`–`r10`) stored. -/
def storeCoefs : List Instr :=
  [.store .w .r12 .r3 (rOff 0), .store .w .r14 .r3 (rOff 1), .store .w .r15 .r3 (rOff 2),
    .store .w .r16 .r3 (rOff 3), .store .w .r17 .r3 (rOff 4),
    .store .w .r7 .r3 (sOff 1), .store .w .r8 .r3 (sOff 2), .store .w .r9 .r3 (sOff 3),
    .store .w .r10 .r3 (sOff 4)]

/-- The limbs of the clamped `r` and `sj = 5 rj`, stored in the state. -/
def coeffs : List Instr := load2 .r3 24 ++ clampR ++ split ++ times5 ++ storeCoefs

/-- The limbs of the stored `h = w0 + 2⁶⁴ w1 + 2¹²⁸ w2` into `r7`–`r11`: those of
`w0 + 2⁶⁴ w1`, with `2²⁴ w2` added to the last. -/
def moveH : List Instr :=
  [.load .d .r0 .r3 16, .lsl .r0 .r0 24, .addi .r7 .r12 0, .addi .r8 .r14 0,
    .addi .r9 .r15 0, .addi .r10 .r16 0, .add .r11 .r17 .r0]

def loadH : List Instr := load2 .r3 0 ++ split ++ moveH

/-! ## Saving and restoring the nonvolatile registers -/

/-- The nonvolatile registers used, in the order they are saved: `r21` keeps
the working space's address. -/
def saved (i : Nat) : Reg := [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21].getD i .r14

/-- Save them in the first 64 bytes of the working space at `w`, and keep its
address in `r21`. -/
def save (w : Reg) : List Instr :=
  (List.range 8).flatMap (fun i => [.store .d (saved i) w (8 * i)]) ++ [.addi .r21 w 0]

/-- Restore them, through `r21`, which is restored last. -/
def restore : List Instr :=
  (List.range 7).flatMap (fun i => [.load .d (saved i) .r21 (8 * i)]) ++ [.load .d .r21 .r21 56]

/-- Everything `blocks` and `finalize` do first. -/
def setup : List Instr := mask ++ coeffs ++ loadH

/-! ## Absorbing a block -/

/-- `hi += xi` for the limbs `xi` in `r12`, `r14`–`r17`. -/
def addLimbs : List Instr :=
  [.add .r7 .r7 .r12, .add .r8 .r8 .r14, .add .r9 .r9 .r15, .add .r10 .r10 .r16,
    .add .r11 .r11 .r17]

/-- `h += 2¹²⁸`. -/
def padBit : List Instr := [.lis .r0 0x100, .add .r11 .r11 .r0]

/-- `h += m` for the block `m` at `r4`, and `h += 2¹²⁸` if `pad`. -/
def addBlock (pad : Bool) : List Instr :=
  load2 .r4 0 ++ split ++ addLimbs ++ (if pad then padBit else [])

/-- The offset of the coefficient of `hi` in `dk`: `r(k-i)`, or `s(k+5-i)`. -/
def coef (k i : Nat) : Nat := if i ≤ k then rOff (k - i) else sOff (k + 5 - i)

/-- `d += h · c`, with the coefficient `c` loaded from `[r3 + off]` into `r18`,
and the product computed there. -/
def mac (d h : Reg) (off : Nat) : List Instr :=
  [.load .w .r18 .r3 off, .mul .r18 h .r18, .add d d .r18]

/-- `dk = Σ hi · coef k i`, into `D.getD k`. -/
def dsum (k : Nat) : List Instr :=
  ([.load .w .r18 .r3 (coef k 0), .mul (D.getD k .r12) .r7 .r18] : List Instr) ++
    (List.range 4).flatMap fun i => mac (D.getD k .r12) (H.getD (i + 1) .r7) (coef k (i + 1))

def products : List Instr := (List.range 5).flatMap dsum

/-- The carry out of `d` into `d'`, leaving the low 26 bits in `h`. -/
def carryStep (d h d' : Reg) : List Instr :=
  [.lsr .d .r18 d 26, .logic .and h d .r20, .add d' d' .r18]

/-- The carries from `d0` to `d4`, the carry out of `d4` added, times 5, to
`h0`, and the carry out of `h0` into `h1`. -/
def carry : List Instr :=
  carryStep .r12 .r7 .r14 ++ carryStep .r14 .r8 .r15 ++ carryStep .r15 .r9 .r16 ++
  carryStep .r16 .r10 .r17 ++
  ([.lsr .d .r18 .r17 26, .logic .and .r11 .r17 .r20, .lsl .r19 .r18 2,
    .add .r18 .r18 .r19, .add .r7 .r7 .r18] : List Instr) ++
  carryStep .r7 .r7 .r8

/-- Absorbing the block at `r4`, with `pad` for a whole block (the `0x01`
byte appended to it is `2¹²⁸`), without for a padded last block (whose
`0x01` byte is inside it). -/
def absorb (pad : Bool) : List Instr := addBlock pad ++ products ++ carry

/-! ## The final reduction -/

/-- The limbs `h1, h2, h3` normalized, carrying into `h4`. -/
def normalize : List Instr :=
  carryStep .r8 .r8 .r9 ++ carryStep .r9 .r9 .r10 ++ carryStep .r10 .r10 .r11

/-- `g = h + 5`, normalized, in `r12`, `r14`–`r17`, and the mask `⌊g / 2¹³⁰⌋ - 1`
in `r18`. -/
def plus5 : List Instr := [
  .addi .r12 .r7 5,
  .lsr .d .r18 .r12 26, .logic .and .r12 .r12 .r20, .add .r14 .r8 .r18,
  .lsr .d .r18 .r14 26, .logic .and .r14 .r14 .r20, .add .r15 .r9 .r18,
  .lsr .d .r18 .r15 26, .logic .and .r15 .r15 .r20, .add .r16 .r10 .r18,
  .lsr .d .r18 .r16 26, .logic .and .r16 .r16 .r20, .add .r17 .r11 .r18,
  .lsr .d .r18 .r17 26, .logic .and .r17 .r17 .r20, .subi .r18 .r18 1]

/-- `h := g ^ ((h ^ g) & mask)`: `h` if the mask is all ones, `g` if it is zero. -/
def selectLimb (h g : Reg) : List Instr :=
  [.logic .xor .r19 h g, .logic .and .r19 .r19 .r18, .logic .xor h g .r19]

def select : List Instr :=
  selectLimb .r7 .r12 ++ selectLimb .r8 .r14 ++ selectLimb .r9 .r15 ++ selectLimb .r10 .r16 ++
  selectLimb .r11 .r17

/-- `h` reduced fully. -/
def reduce : List Instr := normalize ++ plus5 ++ select

/-- The limbs of `h` packed into the 64-bit words `r18, r19, r0`. -/
def pack : List Instr := [
  .lsl .r12 .r8 26, .add .r18 .r7 .r12, .lsl .r12 .r9 52, .add .r18 .r18 .r12,
  .lsr .d .r19 .r9 12, .lsl .r12 .r10 14, .add .r19 .r19 .r12, .lsl .r12 .r11 40,
  .add .r19 .r19 .r12,
  .lsr .d .r0 .r11 24]

/-! ## `init(state = r3, key = r4)` -/

def init : Prog isa := .block [
  .load .d .r5 .r4 0, .load .d .r6 .r4 8, .load .d .r7 .r4 16, .load .d .r8 .r4 24,
  .store .d .r5 .r3 24, .store .d .r6 .r3 32, .store .d .r7 .r3 40, .store .d .r8 .r3 48,
  .li .r5 0, .store .d .r5 .r3 0, .store .d .r5 .r3 8, .store .d .r5 .r3 16]

/-! ## `blocks(state = r3, blocks = r4, n = r5, scratch = r6)` -/

def advance : List Instr := [.addi .r4 .r4 16, .subi .r5 .r5 1]

def body : Prog isa := .block (absorb true ++ advance)

/-- `h` stored. -/
def storeH : List Instr := [.store .d .r18 .r3 0, .store .d .r19 .r3 8, .store .d .r0 .r3 16]

def blocks : Prog isa :=
  .seq (.block (save .r6 ++ setup))
  (.seq (.ite (.zero .d .r5) (.block []) (.loop body (.nonzero .d .r5)))
    (.block (reduce ++ pack ++ storeH ++ restore)))

/-! ## `update(state = r3, count = r4, data = r5, len = r6, scratch = r7)`

With `r12` = the number of bytes in the buffer (`count mod 16`), `r5` = the
data not yet consumed and `r6` = its length: a non-empty buffer is filled
from the data (as far as it goes) and, once full, absorbed; then the whole
blocks of the data are absorbed, and the rest is copied into the buffer. -/

/-- Copies the `r14 > 0` bytes at `r4` to `[r15 + 56]` on, advancing `r4` and `r15`. -/
def copyBody : List Instr :=
  [.lbz .r16 .r4 0, .stb .r16 .r15 56, .addi .r4 .r4 1, .addi .r15 .r15 1,
    .subi .r14 .r14 1]

def copyIn : Prog isa := .loop (.block copyBody) (.nonzero .d .r14)

/-- The number of bytes to copy into the buffer, `n = min(16 - r12, r6)`, into
`r14` (if `r6 < 16`, `r6 < 16 - r12` is the sign of `r6 - (16 - r12)`); then
`r6 -= n`, the buffer's byte `r12` at `[r15 + 56]`, `r12 += n`, and the data into
`r4`. -/
def count : Prog isa :=
  .seq (.block [.li .r14 16, .sub .r14 .r14 .r12, .lsr .d .r15 .r6 4])
  (.seq (.ite (.zero .d .r15)
      (.seq (.block [.sub .r16 .r6 .r14, .lsr .d .r16 .r16 63])
        (.ite (.zero .d .r16) (.block []) (.block [.addi .r14 .r6 0])))
      (.block []))
    (.block [.sub .r6 .r6 .r14, .add .r15 .r3 .r12, .add .r12 .r12 .r14,
      .addi .r4 .r5 0]))

/-- Fills the buffer with `min(16 - r12, r6)` bytes of the data, and absorbs it
if that fills it. -/
def fill : Prog isa :=
  .seq count
  (.seq (.ite (.zero .d .r14) (.block []) copyIn)
  (.seq (.block [.addi .r5 .r4 0, .subi .r16 .r12 16])
    (.ite (.zero .d .r16) (.block (([.addi .r4 .r3 56] : List Instr) ++ absorb true)) (.block []))))

/-- Absorbs the whole blocks of the data, from `r4`, counting them in `r5`. -/
def whole : Prog isa :=
  .seq (.block [.addi .r4 .r5 0, .lsr .d .r5 .r6 4])
    (.ite (.zero .d .r5) (.block [])
      (.loop (.block (absorb true ++ ([.addi .r4 .r4 16, .subi .r6 .r6 16,
        .lsr .d .r5 .r6 4] : List Instr))) (.nonzero .d .r5)))

/-- Copies the rest of the data into the (empty) buffer. -/
def rest : Prog isa :=
  .ite (.zero .d .r6) (.block [])
    (.seq (.block [.addi .r14 .r6 0, .addi .r15 .r3 0]) copyIn)

def update : Prog isa :=
  .seq (.block (save .r7 ++ setup ++ ([.li .r12 15, .logic .and .r12 .r4 .r12] : List Instr)))
  (.seq (.ite (.zero .d .r12) (.block []) fill)
  (.seq whole
  (.seq rest
    (.block (reduce ++ pack ++ storeH ++ restore)))))

/-! ## `finalize(state = r3, count = r4, out = r5, scratch = r6)`

`out` is moved to `r6`, and `count mod 16`, the number of bytes in the
buffer, to `r5`. A non-empty buffer is padded in place with `0x01` and zeros
and absorbed without `pad`. Then `h` is reduced, `s` is added (as limbs, with
carries), and the low 128 bits of the sum are the tag. -/

/-- Zeros the buffer from `[r12 + 56]` on, for `r14 > 0` bytes. -/
def zeroBody : List Instr := [.stb .r15 .r12 56, .addi .r12 .r12 1, .subi .r14 .r14 1]

def lastBlock : Prog isa :=
  .seq (.block [.li .r15 0, .add .r12 .r3 .r5, .li .r14 16, .sub .r14 .r14 .r5])
  (.seq (.loop (.block zeroBody) (.nonzero .d .r14))
    (.block (([.li .r15 1, .add .r12 .r3 .r5, .stb .r15 .r12 56, .addi .r4 .r3 56] : List Instr) ++
      absorb false)))

/-- `h += s`, with the carries propagated up to `h4`. -/
def addS : List Instr := load2 .r3 40 ++ split ++ addLimbs ++ carryStep .r7 .r7 .r8 ++ normalize

/-- The tag stored. -/
def storeTag : List Instr := [.store .d .r18 .r6 0, .store .d .r19 .r6 8]

def finalize : Prog isa :=
  .seq (.block (save .r6 ++ ([.addi .r6 .r5 0, .li .r5 15, .logic .and .r5 .r4 .r5] : List Instr) ++
    setup))
  (.seq (.ite (.zero .d .r5) (.block []) lastBlock)
    (.block (reduce ++ addS ++ pack ++ storeTag ++ restore)))

end VG.Impl.Poly1305.PPC64LE
