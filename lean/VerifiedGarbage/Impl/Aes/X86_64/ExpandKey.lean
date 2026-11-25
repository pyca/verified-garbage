module

public import VerifiedGarbage.Impl.Aes.X86_64.Linear

/-!
# The AES key expansion on x86-64

`vg_aes_expand_key_scratch(key = rdi, key_len = rsi, schedule = rdx,
scratch = rcx)` (FIPS 197 §5.2), a word at a time: `rdx` points at `w[i]`,
`rsi` is `4 Nk`, `r8` is `4 (i mod Nk)` and `rdi` the bytes of the schedule
left. `SUBWORD` needs four S-boxes, at the bits 0, 8, 16 and 24 of slices:
slice `j` is the word shifted right by `j`, the other bits are ignored.

The scratch buffer holds the S-box's spills (slots 0–47), the callee-saved
registers (48–53) and the round constant (54).
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64

open VG.X86_64

/-- The callee-saved registers the code uses, and their slots. -/
def savedRegs : List (Nat × Reg) :=
  [(48, .rbx), (49, .rbp), (50, .r12), (51, .r13), (52, .r14), (53, .r15)]

def saveRegs : List Instr := savedRegs.map fun p => st p.1 p.2
def restoreRegs : List Instr := savedRegs.map fun p => movS p.2 p.1

/-- The round constant's slot. -/
def rcSlot : Nat := 54

/-- Slice `j` of the word in `rax`. -/
def spread : List Instr :=
  (List.range 7).flatMap fun j => [movR (q (j + 1)) .rax, shrI (q (j + 1)) (j + 1)]

/-- The word of the slices' bits 0, 8, 16 and 24, in `rax`. -/
def gather : List Instr :=
  [.alu .and .rax (.imm 0x01010101)] ++ (List.range 7).flatMap fun j =>
    [.alu .and (q (j + 1)) (.imm 0x01010101), rolI (q (j + 1)) (j + 1), xorR .rax (q (j + 1))]

/-- `SUBWORD` of `eax`. -/
def subWord : List Instr := spread ++ sboxCode ++ gather

/-- `ROTWORD`, the round constant, and the next round constant. -/
def rotTail : List Instr :=
  [.shift32 .ror .rax 8, movS .r10 rcSlot, xorR .rax .r10,
   .shift .shl .r10 1, movR .r11 .r10, shrI .r11 8, .mov32 .r12 (.imm 0), .alu .sub .r12 (.reg .r11),
   .alu .and .r12 (.imm 0x11b), xorR .r10 .r12, st rcSlot .r10]

/-- `temp` of word `i`, in `eax`, from `w[i - 1]`. -/
def temp : Prog isa :=
  .seq (.block [.mov32 .rax (.mem { base := .rdx, disp := -4 }), .alu .test .r8 (.reg .r8)])
    (.ite .e (.block (subWord ++ rotTail))
      (.seq (.block [movR .r10 .rsi, .alu .add .r10 (.reg .r8), .alu .cmp .r10 (.imm 48)])
        (.ite .e (.block subWord) (.block []))))

/-- A word of the schedule. -/
def word : Prog isa :=
  .seq temp
    (.seq (.block [movR .r10 .rdx, .alu .sub .r10 (.reg .rsi), .alu32 .xor .rax (.mem (at_ .r10 0)),
        .store32 (at_ .rdx 0) .rax, .alu .add .rdx (.imm 4), .alu .add .r8 (.imm 4), .alu .cmp .r8 (.reg .rsi)])
      (.seq (.ite .e (.block [.mov32 .r8 (.imm 0)]) (.block [])) (.block [.alu .sub .rdi (.imm 4)])))

/-- A word of the key. -/
def keyCopy : List Instr :=
  [.mov32 .rax (.mem (at_ .rdi 0)), .store32 (at_ .rdx 0) .rax, .alu .add .rdi (.imm 4), .alu .add .rdx (.imm 4),
   .alu .sub .r8 (.imm 4)]

/-- `vg_aes_expand_key_scratch`. -/
def expandKey : Prog isa :=
  .seq (.block ([movR .r9 .rcx] ++ saveRegs ++ [movR .r8 .rsi]))
    (.seq (.loop (.block keyCopy) .ne)
      (.seq (.block [.mov32 .r10 (.imm 1), st rcSlot .r10, .mov32 .r8 (.imm 0), movR .rdi .rsi, .alu .add .rdi (.reg .rsi),
          .alu .add .rdi (.reg .rsi), .alu .add .rdi (.imm 112)])
        (.seq (.loop word .ne) (.block restoreRegs))))

end VG.Impl.Aes.X86_64
