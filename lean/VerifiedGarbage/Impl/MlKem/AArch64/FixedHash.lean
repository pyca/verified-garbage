module
public import VerifiedGarbage.Impl.MlKem.AArch64.Top

/-! Fixed-length word/byte absorb and single-block squeeze, matching the
measured ML-KEM specialization. Callers must establish encodable offsets,
word-multiple output lengths and total output at most the rate. -/
@[expose] public section
namespace VG.Impl.MlKem.AArch64.FixedHash
open VG.AArch64

def code (c : Impl.Sha3.AArch64.Callee) (sc : Reg) (st wk rate sfx : Nat) (ins outs : List Piece) : Prog isa := Id.run do
 let mut blocks : List (Prog isa) := [.block (zeroState sc st ++ [.str .x .x30 sc (wk+600)])]
 let perm := .seq (.block (ptrTo .x0 sc st ++ ptrTo .x1 sc wk)) (.call c.name c.code)
 let mut pos := 0
 let mut code : List Instr := []
 for p in ins do
  let mut i := 0
  for _ in List.range p.len do
   if i < p.len then
    if i%8 == 0 && pos%8 == 0 && p.len-i >= 8 then
     code := code ++ ptrTo .x2 p.base (p.off+i) ++
      [.ldr .x .x9 .x2 0,.ldr .x .x10 sc (st+pos),.logic .eor .x .x9 .x9 .x10,.str .x .x9 sc (st+pos)]
     i := i+8
     pos := pos+8
    else
     code := code ++ ptrTo .x2 p.base (p.off+i) ++
      [.ldrb .x9 .x2 0,.ldrb .x10 sc (st+pos),.logic .eor .x .x9 .x9 .x10,.strb .x9 sc (st+pos)]
     i := i+1
     pos := pos+1
    if pos == rate then
     blocks := blocks ++ [.block code,perm]
     code := []
     pos := 0
 code := code ++ [.ldrb .x9 sc (st+pos),.movz .x .x10 (BitVec.ofNat 16 sfx) 0,
  .logic .eor .x .x9 .x9 .x10,.strb .x9 sc (st+pos),
  .ldrb .x9 sc (st+rate-1),.movz .x .x10 128 0,.logic .eor .x .x9 .x9 .x10,.strb .x9 sc (st+rate-1)]
 blocks := blocks ++ [.block code,perm]
 code := []
 pos := 0
 for p in outs do
  for i in List.range (p.len/8) do
   code := code ++ [.ldr .x .x9 sc (st+pos)] ++ ptrTo .x2 p.base (p.off+8*i) ++ [.str .x .x9 .x2 0]
   pos := pos+8
 blocks := blocks ++ [.block (code ++ [.ldr .x .x30 sc (wk+600)])]
 return blocks.foldr (fun a b => .seq a b) (.block [])

end VG.Impl.MlKem.AArch64.FixedHash
