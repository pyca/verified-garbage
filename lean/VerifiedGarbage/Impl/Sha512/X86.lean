import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.X86.Isa

/-!
# SHA-512 compression function: x86 (32-bit) implementation with SSE2

`vg_sha512_compress(state, blocks, n, scratch)`, cdecl: the arguments are at
`[esp + 4]`, `[esp + 8]`, `[esp + 12]` and `[esp + 16]`. SSE2 is this
target's baseline, so this is the only implementation.

* Each 64-bit word is the low quadword of an XMM register: a rotation is a
  logical shift each way (`psrlq`, `psllq`) and `pxor`, an addition is
  `paddq`, and the words in memory are loaded and stored with `movq`. The
  shifts of each `Σ` and `σ` are chained: the copy shifted right is shifted
  further right for the next term, and likewise left (`sig5`).
* The working variables `a … h` live in `scratch[0..64)`, renamed between
  the fully unrolled rounds (in round `t`, variable `k` is at `vOff t k`),
  but `a`, `e` and `b ⊕ c` are also in registers, in roles that two
  consecutive rounds swap (`xr`): a round computes the next `a`, `e` and
  `a ⊕ b` (the next round's `b ⊕ c`, for `Maj(a, b, c) = ((a ⊕ b) ∧ (b ⊕ c)) ⊕
  b`) into the three registers the next round reads them from, and stores
  its `a` and `e` into their slots last, so that every load of a round reads
  memory as the round found it. `xmm6` and `xmm7` are temporaries. `Kₜ` is
  made from two immediates with `movd` and `punpckldq` (the model has no
  constant pool).
* The 16-word message-schedule window is in `scratch[64..192)` (`wOff`):
  the block's sixteen words are made first, each from its big-endian bytes
  with `bswap` in general-purpose registers, and `Wₜ` for `t ≥ 16` replaces
  `Wₜ₋₁₆` just before round `t`. The saved `ebx`, `esi`, `edi`, `ebp` are in
  `scratch[192..208)`, the count of blocks left in `scratch[208..212)`.
* `esi` points to the scratch buffer and `edi` to the current block; the
  hash value's address is read from its argument slot when needed.
* The pointers, the block count and `esp` are public; no address and no
  branch depends on anything else.
-/

namespace VG.Impl.Sha512.X86

open VG.X86
open VG.Spec.Sha512 (K)

/-- The low half of a 64-bit word. -/
def lo (x : BitVec 64) : BitVec 32 := x.extractLsb' 0 32

/-- The high half of a 64-bit word. -/
def hi (x : BitVec 64) : BitVec 32 := x.extractLsb' 32 32

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- `[esi + d]` -/
def sc (d : Nat) : Src := .mem (at_ .esi d)

/-- The general-purpose temporary register, and register pairs (low, high)
for the 64-bit words of other x86 code. -/
def T : Reg := .eax
def Y0 : Reg := .ebx
def Y1 : Reg := .ebp
def Z0 : Reg := .ecx
def Z1 : Reg := .edx

/-! ## 64-bit words in register pairs

Shared with other x86 code that keeps 64-bit words as pairs of 32-bit
registers (BLAKE2b, Argon2). -/

/-- Load the word at `[esi + off]` into `l` (low half) and `h`. -/
def ld (l h : Reg) (off : Nat) : List Instr := [.mov l (sc off), .mov h (sc (off + 4))]

/-- Store `l` (low half) and `h` as the word at `[esi + off]`. -/
def st (l h : Reg) (off : Nat) : List Instr := [.store (at_ .esi off) l, .store (at_ .esi (off + 4)) h]

/-- `(dl, dh) := (dl, dh) + (l, h)` -/
def add64 (dl dh l h : Reg) : List Instr := [.alu .add dl (.reg l), .alu .adc dh (.reg h)]

/-- `(dl, dh) := (dl, dh) +` the word at `[esi + off]` -/
def add64m (dl dh : Reg) (off : Nat) : List Instr := [.alu .add dl (sc off), .alu .adc dh (sc (off + 4))]

/-! ## The scratch buffer -/

/-- The offset in the scratch buffer of `W[j mod 16]`. -/
def wOff (j : Nat) : Nat := 64 + 8 * (j % 16)

/-- The offset in the scratch buffer of working variable `k` (`a = 0, …, h = 7`)
at the start of round `t`. -/
def vOff (t k : Nat) : Nat := 8 * ((k + 8 - t % 8) % 8)

/-- Where the count of blocks left is. -/
def cntOff : Nat := 208

/-! ## SSE2 instructions -/

/-- `movq x, QWORD PTR [b + d]` -/
def ldq (x : XReg) (b : Reg) (d : Nat) : Instr := .movqLoad x (at_ b d)

/-- `movq QWORD PTR [b + d], x` -/
def stq (b : Reg) (d : Nat) (x : XReg) : Instr := .movqStore (at_ b d) x

def xb (op : XBinOp) (d r : XReg) : Instr := .xop (.bin op d r)

def xs (op : XShiftOp) (d : XReg) (n : BitVec 8) : Instr := .xop (.shift op d n)

/-- The temporaries. -/
def X : XReg := .xmm6
def Y : XReg := .xmm7

/-- The register in role `k` in round `t`: `a` (0), `e` (1) and `b ⊕ c` (2)
when the round starts, and the next `a` (3), `e` (4) and `a ⊕ b` (5) it
computes, which are roles 0, 1 and 2 in round `t + 1`. -/
def xr (t k : Nat) : XReg :=
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5].getD ((k + 3 * (t % 2)) % 6) .xmm0

/-- `acc := x >>> r₁ ⊕ x <<< l₁ ⊕ x >>> (r₁ + r₂) ⊕ x <<< (l₁ + l₂) ⊕ x >>> (r₁ + r₂ + r₃)`,
for `x` in `X`, leaving `x <<< (l₁ + l₂)` in `Y`. -/
def sig5 (acc : XReg) (r₁ l₁ r₂ l₂ r₃ : BitVec 8) : List Instr :=
  [xb .movdqa Y X, xs .psrlq X r₁, xs .psllq Y l₁, xb .movdqa acc X, xb .pxor acc Y,
   xs .psrlq X r₂, xb .pxor acc X, xs .psllq Y l₂, xb .pxor acc Y, xs .psrlq X r₃, xb .pxor acc X]

/-- `sig5` of the register `src`, and the sixth term `x <<< (l₁ + l₂ + l₃)`:
`Σ₀` or `Σ₁`. -/
def bigSig (acc src : XReg) (r₁ l₁ r₂ l₂ r₃ l₃ : BitVec 8) : List Instr :=
  xb .movdqa X src :: (sig5 acc r₁ l₁ r₂ l₂ r₃ ++ [xs .psllq Y l₃, xb .pxor acc Y])

/-! ## Rounds -/

/-- A round with the working variables `a`, `b`, `d`, `e`, `f`, `g`, `h` at
`[esi + a]`, …, the message word at `[esi + w]` and the constant `k`; `a`,
`e` and `b ⊕ c` in `A`, `E` and `BC`. It computes
`T₁ = h + Kₜ + Wₜ + Ch(e, f, g) + Σ₁(e)` in `T`, the next `e = d + T₁` in
`NE`, the next `a = T₁ + Σ₀(a) + Maj(a, b, c)` in `T` and `a ⊕ b` in `AB`,
and then stores `a` and `e` into their slots. -/
def roundW (a b d e f g h w : Nat) (k : BitVec 64) (A E BC T NE AB : XReg) : List Instr :=
  [ldq T .esi h, .mov .eax (.imm (lo k)), .xop (.movd X .eax), .mov .eax (.imm (hi k)),
   .xop (.movd Y .eax), xb .punpckldq X Y, xb .paddq T X, ldq X .esi w, xb .paddq T X,
   -- Ch(e, f, g) = ((f ⊕ g) ∧ e) ⊕ g
   ldq X .esi f, ldq Y .esi g, xb .pxor X Y, xb .pand X E, xb .pxor X Y, xb .paddq T X] ++
  -- Σ₁(e): right 14, 18, 41 and left 23, 46, 50
  bigSig NE E 14 23 4 23 23 4 ++
  [xb .paddq T NE, ldq NE .esi d, xb .paddq NE T] ++
  -- Σ₀(a): right 28, 34, 39 and left 25, 30, 36
  bigSig AB A 28 25 6 5 5 6 ++
  [xb .paddq T AB,
   -- Maj(a, b, c) = ((a ⊕ b) ∧ (b ⊕ c)) ⊕ b
   ldq X .esi b, xb .movdqa AB A, xb .pxor AB X, xb .pand BC AB, xb .pxor BC X,
   xb .paddq T BC, stq .esi a A, stq .esi e E]

/-- Round `t`. -/
def round (t : Nat) : List Instr :=
  roundW (vOff t 0) (vOff t 1) (vOff t 3) (vOff t 4) (vOff t 5) (vOff t 6) (vOff t 7) (wOff t) (K t)
    (xr t 0) (xr t 1) (xr t 2) (xr t 3) (xr t 4) (xr t 5)

/-- `Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆` for `t ≥ 16`, with `Wₜ₋ᵢ` at
`[esi + oᵢ]`, in place of `Wₜ₋₁₆`, with `T` and `NE` as temporaries. The
additions are in the order of the specification. -/
def scheduleW (o2 o7 o15 o16 : Nat) (T NE : XReg) : List Instr :=
  -- σ₁: right 6, 19, 61 and left 3, 45
  ldq X .esi o2 :: (sig5 T 6 3 13 42 42 ++ [ldq X .esi o7, xb .paddq T X] ++
  -- σ₀: right 1, 7, 8 and left 56, 63
  ldq X .esi o15 :: (sig5 NE 1 56 6 7 1 ++
  [xb .paddq T NE, ldq X .esi o16, xb .paddq T X, stq .esi o16 T]))

/-- `Wₜ` for `t ≥ 16`, before round `t`, in the registers round `t` computes into. -/
def schedule (t : Nat) : List Instr :=
  scheduleW (wOff (t + 14)) (wOff (t + 9)) (wOff (t + 1)) (wOff t) (xr t 3) (xr t 4)

/-- Round `t`, after computing `Wₜ` if `t ≥ 16`. -/
def step (t : Nat) : List Instr := if t < 16 then round t else schedule t ++ round t

/-- Rounds `0 … n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (step n))

/-! ## One block -/

/-- `Wₜ` for `t < 16`, from the block's bytes at `[edi + i]`, stored at `[esi + o]`. -/
def loadW (i o : Nat) : List Instr :=
  [.mov Z0 (.mem (at_ .edi (i + 4))), .mov Z1 (.mem (at_ .edi i)), .bswap Z0, .bswap Z1] ++ st Z0 Z1 o

/-- The block's sixteen words. -/
def loadWs : List Instr := (List.range 16).flatMap fun t => loadW (8 * t) (wOff t)

/-- Copy word `k` of the hash value at `ecx` to the working variables (`vOff 0 k = 8k`). -/
def loadH (k : Nat) : List Instr := [ldq X .ecx (8 * k), stq .esi (8 * k) X]

/-- `a`, `e` and `b ⊕ c` into their registers for round 0. -/
def enter : List Instr :=
  [ldq (xr 0 0) .esi 0, ldq (xr 0 1) .esi 32, ldq (xr 0 2) .esi 8, ldq X .esi 16, xb .pxor (xr 0 2) X]

/-- Store `a` and `e` after the last round (`80 % 8 = 0`: at `vOff 80 0 = 0`
and `vOff 80 4 = 32`). -/
def exit : List Instr := [stq .esi 0 (xr 80 0), stq .esi 32 (xr 80 1)]

/-- Add word `k` of the working variables (at `vOff 80 k = 8k`) into the hash
value at `ecx`, as `a + H₀` etc. -/
def addH (k : Nat) : List Instr :=
  [ldq X .esi (8 * k), ldq Y .ecx (8 * k), xb .paddq X Y, stq .ecx (8 * k) X]

def load : List Instr := .mov .ecx (.mem (at_ .esp 4)) :: (List.range 8).flatMap loadH

def update : List Instr := .mov .ecx (.mem (at_ .esp 4)) :: (List.range 8).flatMap addH

/-- Advance to the next block and decrement the count (setting ZF when it hits 0). -/
def advance : List Instr :=
  [.alu .add .edi (.imm 128), .mov T (sc cntOff), .alu .sub T (.imm 1), .store (at_ .esi cntOff) T]

/-- One block. -/
def body : Prog isa :=
  .seq (.block (load ++ loadWs ++ enter)) (.seq (rounds 80) (.block (exit ++ update ++ advance)))

/-- The callee-saved registers we use, and where they are saved. -/
def saved : List (Reg × Nat) := [(.ebx, 192), (.esi, 196), (.edi, 200), (.ebp, 204)]

/-- Save the callee-saved registers, load the arguments, and set ZF if there
are no blocks. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 16))] ++
  saved.map (fun (r, d) => .store (at_ .eax d) r) ++
  [.mov .esi (.reg .eax), .mov .edi (.mem (at_ .esp 8)), .mov .eax (.mem (at_ .esp 12)),
   .store (at_ .esi cntOff) .eax, .alu .test .eax (.reg .eax)]

/-- Restore the callee-saved registers (`esi`, the base, last). -/
def epilogue : List Instr :=
  [.mov .ebx (sc 192), .mov .edi (sc 200), .mov .ebp (sc 204), .mov .esi (sc 196)]

def compress : Prog isa :=
  .seq (.block prologue) (.seq (.ite .e (.block []) (.loop body .ne)) (.block epilogue))

end VG.Impl.Sha512.X86
