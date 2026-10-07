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

/-- The scalar's registers shifted right by `w` bits, through `rax`. -/
def shiftN (n w : Nat) : List Instr :=
  let rs := Naf.sregs n
  (rs.zip rs.tail).flatMap (fun (a, b) =>
    [.shift .shr a w,.mov .rax (.reg b),.shift .shl .rax (64-w),.alu .or a (.reg .rax)]) ++
  [.shift .shr (Naf.stop n) w]

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

/-- `step` for a scalar of `n` words: `64 n + 1` digits. -/
def stepN (n dst w : Nat) : Prog isa :=
  .seq (.block [.mov .rcx (.reg .r8),.alu .and .rcx (.imm 1),.alu .test .rcx (.reg .rcx)]) <|
  .seq (.ite .e (.block (shiftN n 1++advance 1))
    (.seq (choose w) (.block (Naf.subtractDigitN n++[.store8 (tbl dst) .rcx]++shiftN n w++advance w))))
    (.block [.alu .cmp .rbx (.imm (BitVec.ofNat 32 (64*n+1)))])

/-- The digits of a scalar of `n` words, into `8 n + 1` zeroed words at `dst`. -/
def prepN (n src dst w : Nat) : Prog isa :=
  .seq (.block (Naf.initN n src++setConst (8*n+1) dst 0)) (.loop (stepN n dst w) .b)

end VG.Impl.Weierstrass.X86_64.FastNaf
