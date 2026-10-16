module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8

/-! Register-resident triangular products within one eight-word block. -/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.AdxTri8
open VG.X86_64
open AdxRotate8 (at_)

def word (k : Nat) (hi prev col : Reg) : List Instr :=
  [.mulx hi .rsi (.mem (at_ .rbp (8*k))),.adcx col (.reg .rsi),.adox col (.reg prev)]

/-- The last column, which is zero: its carries and the high word. -/
def close (hi col : Reg) : List Instr := [.adcx col (.reg col),.adox col (.reg hi)]

def chain (k : Nat) (hi other prev : Reg) : List Reg → List Instr
  | [] => []
  | [col] => close prev col
  | col::next::rest => word k hi prev col ++ chain (k+1) other hi hi (next::rest)

/-- The last register of `col::rest`. -/
def last : Reg → List Reg → Reg
  | r, [] => r
  | _, r::rs => last r rs

/-- A row's first word, whose incoming high word is zero: the low product
added to `col`, no `adox`. -/
def wordF (k : Nat) (hi col : Reg) : List Instr :=
  [.mulx hi .rsi (.mem (at_ .rbp (8*k))),.adcx col (.reg .rsi)]

/-- A row over the columns `col::rest`: one `xor` zeroes its top column
`last col rest` and clears both flags, then its first word, then the rest of
the chain, from the first word's high word in `rbx`. -/
def rowCore (i : Nat) (col : Reg) (rest : List Reg) : List Instr :=
  ([.mov .rdx (.mem (at_ .rbp (8*i))),.alu32 .xor (last col rest) (.reg (last col rest))] : List Instr) ++
    (wordF (i+1) .rbx col ++ chain (i+2) .rax .rbx .rbx rest)

/-- `rcx :=` the block's output base, which it keeps through the rows. -/
def headBases : List Instr :=
  [.mov .rsi (.mem (hdr (sArr Public.aAcc))),.mov .rcx (.mem (hdr (sFn 12))),
   .shift .shl .rcx 4,.alu .add .rcx (.reg .rsi)]

def storeHead (i : Nat) (lo hi : Reg) : Prog isa :=
  .seq (.block [.store (at_ .rcx (16+8*(2*i+1))) lo])
    (.block [.store (at_ .rcx (16+8*(2*i+2))) hi])

/-- A row, its two low words stored; `lo` becomes the next row's top column,
which that row zeroes. -/
def rowStep (i : Nat) (lo hi : Reg) (tail : List Reg) : Prog isa :=
  .seq (.block (rowCore i lo (hi::tail))) (storeHead i lo hi)

def rotate (rs : List Reg) : List Reg := rs.drop 2 ++ rs.take 1

/-- A word of the first row, whose columns hold nothing yet: the low product
straight into `col`, then the high word before it added. -/
def word0 (k : Nat) (hi prev col : Reg) : List Instr :=
  [.mulx hi col (.mem (at_ .rbp (8*k))),.adcx col (.reg prev)]

/-- The first row's words from `k` on: the last column takes the last high
word and the carry. -/
def chain0 (k : Nat) (hi other prev : Reg) : List Reg → List Instr
  | [] => []
  | [col] => [.mov32 col (.imm 0),.adcx col (.reg prev)]
  | col::next::rest => word0 k hi prev col ++ chain0 (k+1) other hi hi (next::rest)

/-- The block's first row, which writes its columns rather than adding to
them, so that nothing clears them first. -/
def row0Core : List Reg → List Instr
  | [] => []
  | col::rest => ([.mov .rdx (.mem (at_ .rbp 0)),.alu32 .xor .rax (.reg .rax),
      .mulx .rbx col (.mem (at_ .rbp 8))] : List Instr) ++ chain0 2 .rax .rbx .rbx rest

def rowStep0 (lo hi : Reg) (tail : List Reg) : Prog isa :=
  .seq (.block (row0Core (lo::hi::tail))) (storeHead 0 lo hi)

def rows : Nat → Nat → List Reg → Prog isa
  | 0, _, _ => .block []
  | n+1, i, rs => .seq (rowStep i rs[0]! rs[1]! (rs.drop 2)) (rows n (i+1) (rotate rs))

def columns : List Reg := [.r8,.r9,.r10,.r11,.r12,.r13,.r14,.r15]

def setup (a : Nat) : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))),.shift .shl .rax 3,
   .mov .rbp (.mem (hdr (sArr a))),.alu .add .rbp (.reg .rax)]

/-- Zero the two words of the block's sixteen output words that no row writes,
its first and last: the rows then write the other fourteen, and nothing has to
clear the whole product buffer first. -/
def clearEnds : Prog isa := .seq (.block headBases)
  (.seq (.block [.mov32 .rax (.imm 0),.store (at_ .rcx 16) .rax]) (.block [.store (at_ .rcx 136) .rax]))

def block (a : Nat) : Prog isa :=
  .seq (.block (setup a)) (.seq clearEnds
    (.seq (rowStep0 .r8 .r9 [.r10,.r11,.r12,.r13,.r14,.r15]) (rows 6 1 (rotate columns))))

def nextBlock : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),
   .store (hdr (sFn 12)) .rax,.alu .cmp .rax (.mem (hdr sW))]

def blocks (a : Nat) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax])
    (.loop (.seq (block a) (.block nextBlock)) .ne)

end VG.Impl.Bignum.X86_64.AdxTri8
