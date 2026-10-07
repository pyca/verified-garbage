import VerifiedGarbage.Impl.Weierstrass.X86_64.NafPrep

/-! Public width-five/width-seven recoding, skipping known zero digits. -/
namespace VG.Impl.Weierstrass.X86_64.FastNaf
open VG VG.X86_64 VG.Impl.Mont.X86_64

def shift (w : Nat) : List Instr :=
  [.shift .shr .r8 w,.mov .rax (.reg .r9),.shift .shl .rax (64-w),.alu .or .r8 (.reg .rax),
   .shift .shr .r9 w,.mov .rax (.reg .r10),.shift .shl .rax (64-w),.alu .or .r9 (.reg .rax),
   .shift .shr .r10 w,.mov .rax (.reg .r11),.shift .shl .rax (64-w),.alu .or .r10 (.reg .rax),
   .shift .shr .r11 w,.mov .rax (.reg .r12),.shift .shl .rax (64-w),.alu .or .r11 (.reg .rax),
   .shift .shr .r12 w]

def choose (w : Nat) : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm (BitVec.ofNat 32 (2^w-1))),
    .alu .cmp .rcx (.imm (BitVec.ofNat 32 (2^(w-1))))])
    (.ite .b (.block []) (.block [.alu .sub .rcx (.imm (BitVec.ofNat 32 (2^w)))]))

def advance (w : Nat) : List Instr := [.alu .add .rbx (.imm (BitVec.ofNat 32 w))]

def step (dst w : Nat) : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm 1),.alu .test .rcx (.reg .rcx)]) <|
  .seq (.ite .e (.block (shift 1++advance 1))
    (.seq (choose w) (.block (Naf.subtractDigit++[.store8 (tbl dst) .rcx]++shift w++advance w))))
    (.block [.alu .cmp .rbx (.imm 257)])

def prep (src dst w : Nat) : Prog isa :=
  .seq (.block (Naf.init src++setConst 33 dst 0)) (.loop (step dst w) .b)

end VG.Impl.Weierstrass.X86_64.FastNaf
