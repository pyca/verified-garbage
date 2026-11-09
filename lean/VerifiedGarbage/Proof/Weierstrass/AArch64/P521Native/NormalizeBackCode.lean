module

-- separate module: Three bundled source certificates and bounded WP regroupings cost 1.53s versus 0.38s importing their dependencies (local Lean trace); state-invariant edits reuse these checked source matches.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeBackWork
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Impl.Weierstrass.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block

/-! Literal source matching for the complete back-substitution instruction stream. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native


def normalizeBackRange (start : Nat) : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (normalizeBackRow (normalizePrefixSlot start) start) (normalizeBackRange (start-1) n)


def normalizeBackChunk0 : Prog isa := sequence [
  .block outerBlock046,callNormalMul,
  .block outerBlock047,callNormalMul,
  .block outerBlock048,callNormalSqr,
  .block outerBlock049,callNormalMul,
  .block outerBlock050,callNormalMul,
  .block outerBlock051,callNormalMul,
  .block outerBlock052,callNormalMul,
  .block outerBlock053,callNormalMul,
  .block outerBlock054,callNormalSqr,
  .block outerBlock055,callNormalMul,
  .block outerBlock056,callNormalMul,
  .block outerBlock057,callNormalMul,
  .block outerBlock058,callNormalMul,
  .block outerBlock059,callNormalMul,
  .block outerBlock060,callNormalSqr,
  .block outerBlock061,callNormalMul,
  .block outerBlock062,callNormalMul,
  .block outerBlock063,callNormalMul,
  .block outerBlock064,callNormalMul,
  .block outerBlock065,callNormalMul,
  .block outerBlock066,callNormalSqr,
  .block outerBlock067,callNormalMul,
  .block outerBlock068,callNormalMul,
  .block outerBlock069,callNormalMul,
  .block outerBlock070,callNormalMul,
  .block outerBlock071,callNormalMul,
  .block outerBlock072,callNormalSqr,
  .block outerBlock073,callNormalMul,
  .block outerBlock074,callNormalMul,
  .block outerBlock075,callNormalMul,
  .block (outerBlock076.take 19)]

private theorem normalize_back_chunk0_sources :
    (outerBlock046=
      VG.Impl.Weierstrass.AArch64.copy 9 1504 2152++normalizeCopy 9 (216*15+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 15)) ∧
    (outerBlock047=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock048=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock049=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*15) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock050=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*15)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock051=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*15+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock052=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*15+72)++normalizeCopy 9 (216*14+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 14)) ∧
    (outerBlock053=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock054=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock055=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*14) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock056=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*14)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock057=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*14+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock058=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*14+72)++normalizeCopy 9 (216*13+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 13)) ∧
    (outerBlock059=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock060=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock061=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*13) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock062=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*13)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock063=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*13+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock064=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*13+72)++normalizeCopy 9 (216*12+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 12)) ∧
    (outerBlock065=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock066=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock067=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*12) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock068=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*12)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock069=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*12+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock070=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*12+72)++normalizeCopy 9 (216*11+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 11)) ∧
    (outerBlock071=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock072=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock073=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*11) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock074=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*11)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock075=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*11+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock076.take 19=([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*11+72)) := by lit_decide

theorem normalize_back_chunk0_wp {s : State} {Q : State → Prop} :
    WP isa normalizeBackChunk0 s Q ↔ WP isa (.seq (.block (VG.Impl.Weierstrass.AArch64.copy 9 1504 2152)) (normalizeBackRange 15 5)) s Q := by
  rcases normalize_back_chunk0_sources with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30⟩
  simp only [normalizeBackChunk0,sequence,List.foldr_cons,List.foldr_nil,normalizeBackRange,
    normalizeBackRow,normalizeBackX,normalizeBackY,normalizeMulStep,normalizeSquareStep,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30]
  simp only [Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul]
  simp only [VG.WP.seq_iff (M:=isa),VG.WP.block_append_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)]

def normalizeBackChunk1 : Prog isa := sequence [
  .block (outerBlock076.drop 19),callNormalMul,
  .block outerBlock077,callNormalMul,
  .block outerBlock078,callNormalSqr,
  .block outerBlock079,callNormalMul,
  .block outerBlock080,callNormalMul,
  .block outerBlock081,callNormalMul,
  .block outerBlock082,callNormalMul,
  .block outerBlock083,callNormalMul,
  .block outerBlock084,callNormalSqr,
  .block outerBlock085,callNormalMul,
  .block outerBlock086,callNormalMul,
  .block outerBlock087,callNormalMul,
  .block outerBlock088,callNormalMul,
  .block outerBlock089,callNormalMul,
  .block outerBlock090,callNormalSqr,
  .block outerBlock091,callNormalMul,
  .block outerBlock092,callNormalMul,
  .block outerBlock093,callNormalMul,
  .block outerBlock094,callNormalMul,
  .block outerBlock095,callNormalMul,
  .block outerBlock096,callNormalSqr,
  .block outerBlock097,callNormalMul,
  .block outerBlock098,callNormalMul,
  .block outerBlock099,callNormalMul,
  .block outerBlock100,callNormalMul,
  .block outerBlock101,callNormalMul,
  .block outerBlock102,callNormalSqr,
  .block outerBlock103,callNormalMul,
  .block outerBlock104,callNormalMul,
  .block outerBlock105,callNormalMul,
  .block (outerBlock106.take 19)]

private theorem normalize_back_chunk1_sources :
    (outerBlock076.drop 19=normalizeCopy 9 (216*10+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 10)) ∧
    (outerBlock077=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock078=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock079=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*10) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock080=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*10)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock081=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*10+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock082=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*10+72)++normalizeCopy 9 (216*9+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 9)) ∧
    (outerBlock083=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock084=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock085=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*9) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock086=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*9)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock087=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*9+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock088=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*9+72)++normalizeCopy 9 (216*8+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 8)) ∧
    (outerBlock089=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock090=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock091=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*8) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock092=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*8)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock093=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*8+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock094=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*8+72)++normalizeCopy 9 (216*7+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 7)) ∧
    (outerBlock095=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock096=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock097=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*7) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock098=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*7)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock099=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*7+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock100=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*7+72)++normalizeCopy 9 (216*6+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 6)) ∧
    (outerBlock101=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock102=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock103=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*6) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock104=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*6)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock105=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*6+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock106.take 19=([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*6+72)) := by lit_decide

theorem normalize_back_chunk1_wp {s : State} {Q : State → Prop} :
    WP isa normalizeBackChunk1 s Q ↔ WP isa (normalizeBackRange 10 5) s Q := by
  rcases normalize_back_chunk1_sources with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30⟩
  simp only [normalizeBackChunk1,sequence,List.foldr_cons,List.foldr_nil,normalizeBackRange,
    normalizeBackRow,normalizeBackX,normalizeBackY,normalizeMulStep,normalizeSquareStep,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30]
  simp only [Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul]
  simp only [VG.WP.seq_iff (M:=isa),VG.WP.block_append_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)]

def normalizeBackChunk2 : Prog isa := sequence [
  .block (outerBlock106.drop 19),callNormalMul,
  .block outerBlock107,callNormalMul,
  .block outerBlock108,callNormalSqr,
  .block outerBlock109,callNormalMul,
  .block outerBlock110,callNormalMul,
  .block outerBlock111,callNormalMul,
  .block outerBlock112,callNormalMul,
  .block outerBlock113,callNormalMul,
  .block outerBlock114,callNormalSqr,
  .block outerBlock115,callNormalMul,
  .block outerBlock116,callNormalMul,
  .block outerBlock117,callNormalMul,
  .block outerBlock118,callNormalMul,
  .block outerBlock119,callNormalMul,
  .block outerBlock120,callNormalSqr,
  .block outerBlock121,callNormalMul,
  .block outerBlock122,callNormalMul,
  .block outerBlock123,callNormalMul,
  .block outerBlock124,callNormalMul,
  .block outerBlock125,callNormalMul,
  .block outerBlock126,callNormalSqr,
  .block outerBlock127,callNormalMul,
  .block outerBlock128,callNormalMul,
  .block outerBlock129,callNormalMul,
  .block outerBlock130,callNormalMul,
  .block outerBlock131,callNormalMul,
  .block outerBlock132,callNormalSqr,
  .block outerBlock133,callNormalMul,
  .block outerBlock134,callNormalMul,
  .block outerBlock135,callNormalMul,
  .block (outerBlock136.take 19)]

private theorem normalize_back_chunk2_sources :
    (outerBlock106.drop 19=normalizeCopy 9 (216*5+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 5)) ∧
    (outerBlock107=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock108=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock109=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*5) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock110=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*5)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock111=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*5+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock112=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*5+72)++normalizeCopy 9 (216*4+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 4)) ∧
    (outerBlock113=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock114=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock115=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*4) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock116=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*4)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock117=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*4+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock118=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*4+72)++normalizeCopy 9 (216*3+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 3)) ∧
    (outerBlock119=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock120=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock121=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*3) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock122=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*3)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock123=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*3+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock124=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*3+72)++normalizeCopy 9 (216*2+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 2)) ∧
    (outerBlock125=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock126=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock127=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*2) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock128=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*2)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock129=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*2+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock130=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*2+72)++normalizeCopy 9 (216*1+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 1)) ∧
    (outerBlock131=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1504 1504 1360) ∧
    (outerBlock132=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCallArgs 1432 1288 1288) ∧
    (outerBlock133=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*1) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock134=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*1)++normalizeCallArgs 1432 1432 1288) ∧
    (outerBlock135=
      ([.umov .x .x30 .v29 0] : List Instr)++normalizeCopy 9 (216*1+72) 1360++normalizeCallArgs 1360 1360 1432) ∧
    (outerBlock136.take 19=([.umov .x .x30 .v29 0] : List Instr)++normalizeStoreCopy 9 1360 (216*1+72)) := by lit_decide

theorem normalize_back_chunk2_wp {s : State} {Q : State → Prop} :
    WP isa normalizeBackChunk2 s Q ↔ WP isa (normalizeBackRange 5 5) s Q := by
  rcases normalize_back_chunk2_sources with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30⟩
  simp only [normalizeBackChunk2,sequence,List.foldr_cons,List.foldr_nil,normalizeBackRange,
    normalizeBackRow,normalizeBackX,normalizeBackY,normalizeMulStep,normalizeSquareStep,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30]
  simp only [Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul]
  simp only [VG.WP.seq_iff (M:=isa),VG.WP.block_append_iff (M:=isa),VG.WP.block_nil_iff (M:=isa)]

def normalizeBackMachine : Prog isa := .seq normalizeBackChunk0 (.seq normalizeBackChunk1 normalizeBackChunk2)

theorem normalize_back_machine_wp {s : State} {Q : State → Prop} :
    WP isa normalizeBackMachine s Q ↔
      WP isa (.seq (.block (VG.Impl.Weierstrass.AArch64.copy 9 1504 2152)) (normalizeBackWork 15)) s Q := by
  simp only [normalizeBackMachine,VG.WP.seq_iff (M:=isa),
    normalize_back_chunk0_wp,normalize_back_chunk1_wp,normalize_back_chunk2_wp,
    normalizeBackRange,normalizeBackWork,Nat.reduceAdd,Nat.reduceSub,
    VG.WP.block_nil_iff (M:=isa)]

end VG.Proof.Weierstrass.AArch64.P521Native
