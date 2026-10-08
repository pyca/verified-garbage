import VerifiedGarbage.Impl.Seed.X86_64.G16
import VerifiedGarbage.Spec.Seed

/-!
# SEED ECB on x86-64

`vg_seed_ecb_{en,de}crypt(schedule = rdi, data = rsi, n = rdx, scratch = rcx)`.

Sixteen blocks at a time (fewer in the last batch), each round's three `G`s
computed for all of them at once by `g16`. The scratch buffer (moved to
`r9`, the base `g16` uses) holds `g16`'s slots and masks (`G16.lean`), the
blocks' state as four arrays of sixteen 32-bit words, one per word of the
block (`L0`, `L1`, `R0`, `R1`: `arrSlot 0 … arrSlot 3`), the intermediate
arrays `a`, `c` and `d` of the round function, and the callee-saved
registers.

* A batch copies its blocks' words, byte-swapped to the big-endian words of
  RFC 4269, into the arrays; lanes past the batch hold whatever they held,
  and their results are not stored.
* A round (`round`) computes, lane by lane, `a = R0 ⊕ K0` and
  `a ⊕ R1 ⊕ K1`; `c = G` of that; `c + a`; `d = G` of that; `d + c`;
  `e = G` of that; and `L0 ⊕ (e + d)` and `L1 ⊕ e`, which become the new
  `R0` and `R1` as the halves are exchanged (`swapHalves`): RFC 4269 §2's
  `T = R; R = L ⊕ F(Ki, R); L = T`. After sixteen rounds, the halves are
  exchanged once too often, so the copy out takes `R` first.
* Encryption steps through the round keys from the first, decryption from
  the last (`keyStart`, `keyStep`); the key pointer is moved back after the
  sixteen rounds.
* The key pointer (`rdi`), the data pointer (`rsi`), the blocks left (`rdx`)
  and the rounds left (`r8`) stay in registers that `g16` does not write.
  Every address and branch depends only on them, the scratch base and the
  copy loops' counters.
-/

namespace VG.Impl.Seed.X86_64

open VG.X86_64 VG.Impl.Aes.X86_64
open VG.Spec.Seed (Direction)

/-! ## Scratch slots -/

/-- The arrays of `a`, `c` and `d`. -/
def aSlot : Nat := 69
def cSlot : Nat := 77
def dSlot : Nat := 85
/-- The array of word `w` of the blocks: `L0`, `L1`, `R0`, `R1`. -/
def arrSlot (w : Nat) : Nat := 93 + 8 * w
def savedRegs : List (Reg × Nat) :=
  [(.rbx, 125), (.rbp, 126), (.r12, 127), (.r13, 128), (.r14, 129), (.r15, 130)]
/-- The scratch buffer's size, in slots. -/
def scratchSlots : Nat := 132

/-- Lane `b` of the array starting at slot `k`, at `base`. -/
def lane (base : Reg) (k b : Nat) : MemOp := { base, disp := ((8 * k + 4 * b : Nat) : Int) }

/-! ## A round -/

/-- `rax := L`-lane `b` … (each step on one lane, through `eax` and `ecx`). -/
def step1 (b : Nat) : List Instr :=
  [.mov32 .rax (.mem (lane .r9 (arrSlot 2) b)), .alu32 .xor .rax (.reg .r11),
   .store32 (lane .r9 aSlot b) .rax, .alu32 .xor .rax (.mem (lane .r9 (arrSlot 3) b)),
   .alu32 .xor .rax (.reg .r12), .store32 (lane .r9 (tSlot 0) b) .rax]

/-- `c := G(…)`, `T := c + a`. -/
def step2 (b : Nat) : List Instr :=
  [.mov32 .rax (.mem (lane .r9 (tSlot 0) b)), .store32 (lane .r9 cSlot b) .rax,
   .alu32 .add .rax (.mem (lane .r9 aSlot b)), .store32 (lane .r9 (tSlot 0) b) .rax]

/-- `d := G(…)`, `T := d + c`. -/
def step3 (b : Nat) : List Instr :=
  [.mov32 .rax (.mem (lane .r9 (tSlot 0) b)), .store32 (lane .r9 dSlot b) .rax,
   .alu32 .add .rax (.mem (lane .r9 cSlot b)), .store32 (lane .r9 (tSlot 0) b) .rax]

/-- `e := G(…)`, `L1 := L1 ⊕ e`, `L0 := L0 ⊕ (e + d)`. -/
def step4 (b : Nat) : List Instr :=
  [.mov32 .rax (.mem (lane .r9 (tSlot 0) b)), .mov32 .rcx (.mem (lane .r9 (arrSlot 1) b)),
   .alu32 .xor .rcx (.reg .rax), .store32 (lane .r9 (arrSlot 1) b) .rcx,
   .alu32 .add .rax (.mem (lane .r9 dSlot b)), .alu32 .xor .rax (.mem (lane .r9 (arrSlot 0) b)),
   .store32 (lane .r9 (arrSlot 0) b) .rax]

def lanes16 (f : Nat → List Instr) : List Instr := (List.range 16).flatMap f

/-- Exchange the halves `L` and `R`, a slot at a time. -/
def swapHalves : List Instr :=
  (List.range 16).flatMap fun k =>
    [movS .rax (arrSlot 0 + k), movS .rcx (arrSlot 2 + k), st (arrSlot 0 + k) .rcx,
     st (arrSlot 2 + k) .rax]

/-- The step of the key pointer from one round to the next. -/
def keyStep : Direction → Int
  | .encrypt => 8
  | .decrypt => -8

/-- Where the first round's key is, from the schedule. -/
def keyStart : Direction → Nat
  | .encrypt => 0
  | .decrypt => 120

/-- One round, with its key at `rdi`; advances `rdi` and counts down `r8`. -/
def round (d : Direction) : List Instr :=
  [.mov32 .r11 (.mem { base := .rdi, disp := 0 }), .mov32 .r12 (.mem { base := .rdi, disp := 4 })] ++
  lanes16 step1 ++ g16 ++ lanes16 step2 ++ g16 ++ lanes16 step3 ++ g16 ++ lanes16 step4 ++
  swapHalves ++
  [.alu .add .rdi (.imm (BitVec.ofInt 32 (keyStep d))), .alu .sub .r8 (.imm 1)]

/-- Sixteen rounds, then the key pointer back to the first round's key. -/
def rounds (d : Direction) : Prog isa :=
  .seq (.block [.mov .r8 (.imm 16)])
    (.seq (.loop (.block (round d)) .ne)
      (.block [.alu .sub .rdi (.imm (BitVec.ofInt 32 (16 * keyStep d)))]))

/-! ## Batches -/

/-- `rcx := min(rdx, 16)`, the blocks of this batch. -/
def batchSize : Prog isa :=
  .seq (.block [movR .rcx .rdx, .alu .cmp .rcx (.imm 16)])
    (.ite .b (.block []) (.block [.mov .rcx (.imm 16)]))

/-- Copy one block (at `r10`) into the arrays' lane at `rbx`, its words
byte-swapped; move on to the next. -/
def copyInBody : List Instr :=
  ((List.range 4).flatMap fun w =>
    [.mov32 .rax (.mem { base := .r10, disp := ((4 * w : Nat) : Int) }), .bswap32 .rax,
     .store32 (lane .rbx (arrSlot w) 0) .rax]) ++
  [.alu .add .r10 (.imm 16), .alu .add .rbx (.imm 4), .alu .sub .rcx (.imm 1)]

/-- Copy a lane out to one block, `R` first (see the rounds). -/
def copyOutBody : List Instr :=
  ((List.range 4).flatMap fun w =>
    [.mov32 .rax (.mem (lane .rbx (arrSlot ((w + 2) % 4)) 0)), .bswap32 .rax,
     .store32 { base := .r10, disp := ((4 * w : Nat) : Int) } .rax]) ++
  [.alu .add .r10 (.imm 16), .alu .add .rbx (.imm 4), .alu .sub .rcx (.imm 1)]

def copyStart : List Instr := [movR .r10 .rsi, movR .rbx .r9]

def copyIn : Prog isa := .seq batchSize (.seq (.block copyStart) (.loop (.block copyInBody) .ne))

/-- Copy out, then move the data pointer past the batch and count it. -/
def copyOut : Prog isa :=
  .seq batchSize (.seq (.block copyStart)
    (.seq (.loop (.block copyOutBody) .ne)
      (.seq batchSize (.block [movR .rsi .r10, .alu .sub .rdx (.reg .rcx)]))))

def batch (d : Direction) : Prog isa := .seq copyIn (.seq (rounds d) copyOut)

/-! ## The function -/

def setup (d : Direction) : List Instr :=
  [movR .r9 .rcx] ++ savedRegs.map (fun (r, k) => st k r) ++ setG16Masks ++
  [.alu .add .rdi (.imm (BitVec.ofNat 32 (keyStart d))), .alu .cmp .rdx (.imm 0)]

def restore : List Instr := savedRegs.map fun (r, k) => movS r k

def ecb (d : Direction) : Prog isa :=
  .seq (.block (setup d)) (.seq (.ite .e (.block []) (.loop (batch d) .ne)) (.block restore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.Seed.X86_64
