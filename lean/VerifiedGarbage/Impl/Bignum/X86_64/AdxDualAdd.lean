import VerifiedGarbage.Impl.Bignum.X86_64.Adx

/-! Interleave two independent additions into the eight live columns. -/
namespace VG.Impl.Bignum.X86_64.AdxDualAdd
open VG.X86_64

def regs : List Reg := [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

def word (dst : Reg) (a b : Src) : List Instr := [.adcx dst a, .adox dst b]

def chain (a b : Nat → Src) : List Instr :=
  (regs.zipIdx).flatMap fun (r,k) => word r (a k) (b k)

/-- Capture both independent carries without losing either one. -/
def close : List Instr :=
  [.mov32 .rdx (.imm 0), .adcx .rax (.reg .rdx), .adox .rax (.reg .rdx)]

/-- Add an input block and the carry word held in `rdx`. -/
def addInput : List Instr :=
  [.alu32 .xor .rax (.reg .rax)] ++
  chain (fun k => .mem ({ base := .rsi, disp := (8 * k : Nat) }))
    (fun k => .reg (if k = 0 then .rdx else .rax)) ++ close

end VG.Impl.Bignum.X86_64.AdxDualAdd
