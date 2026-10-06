import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8

/-! Register-resident triangular products within one eight-word block. -/
namespace VG.Impl.Bignum.X86_64.AdxTri8
open VG.X86_64
open AdxRotate8 (at_)

def word (k : Nat) (hi prev col : Reg) : List Instr :=
  [.mulx hi .rsi (.mem (at_ .rbp (8*k))),.adcx col (.reg .rsi),.adox col (.reg prev)]

def close (hi col : Reg) : List Instr := [.adcx col (.reg .rcx),.adox col (.reg hi)]

def chain (k : Nat) (hi other prev : Reg) : List Reg → List Instr
  | [] => []
  | [col] => close prev col
  | col::next::rest => word k hi prev col ++ chain (k+1) other hi hi (next::rest)

def rowCore (i : Nat) (rs : List Reg) : List Instr :=
  [.mov .rdx (.mem (at_ .rbp (8*i))),.alu32 .xor .rcx (.reg .rcx)] ++ chain (i+1) .rax .rbx .rcx rs

def headBases : List Instr :=
  [.mov .rsi (.mem (hdr (sArr Public.aAcc))),.mov .rcx (.mem (hdr (sFn 12))),
   .shift .shl .rcx 4,.alu .add .rsi (.reg .rcx)]

def storeHead (i : Nat) (lo hi : Reg) : Prog isa := .seq (.block headBases)
  (.seq (.block [.store (at_ .rsi (16+8*(2*i+1))) lo])
    (.block [.store (at_ .rsi (16+8*(2*i+2))) hi]))

def rowStep (i : Nat) (lo hi : Reg) (tail : List Reg) : Prog isa :=
  .seq (.block (rowCore i (lo::hi::tail)))
    (.seq (storeHead i lo hi) (.block [.mov32 lo (.imm 0)]))

def rotate (rs : List Reg) : List Reg := rs.drop 2 ++ rs.take 1

def rows : Nat → Nat → List Reg → Prog isa
  | 0, _, _ => .block []
  | n+1, i, rs => .seq (rowStep i rs[0]! rs[1]! (rs.drop 2)) (rows n (i+1) (rotate rs))

def columns : List Reg := [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

def clearColumns : List Instr := columns.map (fun r => .mov32 r (.imm 0))

def setup (a : Nat) : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))),.shift .shl .rax 3,
   .mov .rbp (.mem (hdr (sArr a))),.alu .add .rbp (.reg .rax)]

def block (a : Nat) : Prog isa :=
  .seq (.block (setup a)) (.seq (.block clearColumns) (rows 7 0 columns))

def nextBlock : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),
   .store (hdr (sFn 12)) .rax,.alu .cmp .rax (.mem (hdr sW))]

def blocks (a : Nat) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax])
    (.loop (.seq (block a) (.block nextBlock)) .ne)

end VG.Impl.Bignum.X86_64.AdxTri8
