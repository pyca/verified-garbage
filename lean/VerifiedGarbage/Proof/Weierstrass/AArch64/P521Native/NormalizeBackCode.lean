module

-- separate module: The ninety literal block identities and three bounded WP regroupings cost about 2.7 seconds; state-invariant edits should reuse this source replay.

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeBackWork
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
public import VerifiedGarbage.Impl.Weierstrass.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Block

/-! Literal source matching for the complete back-substitution instruction stream. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native

theorem normalize_back_source_046 : outerBlock046=
    VG.Impl.Weierstrass.AArch64.copy 9 1504 2152++normalizeCopy 9 (216*15+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 15) := by lit_decide

theorem normalize_back_source_047 : outerBlock047=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_048 : outerBlock048=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_049 : outerBlock049=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*15) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_050 : outerBlock050=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*15)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_051 : outerBlock051=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*15+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_052 : outerBlock052=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*15+72)++normalizeCopy 9 (216*14+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 14) := by lit_decide

theorem normalize_back_source_053 : outerBlock053=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_054 : outerBlock054=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_055 : outerBlock055=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*14) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_056 : outerBlock056=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*14)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_057 : outerBlock057=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*14+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_058 : outerBlock058=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*14+72)++normalizeCopy 9 (216*13+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 13) := by lit_decide

theorem normalize_back_source_059 : outerBlock059=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_060 : outerBlock060=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_061 : outerBlock061=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*13) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_062 : outerBlock062=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*13)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_063 : outerBlock063=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*13+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_064 : outerBlock064=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*13+72)++normalizeCopy 9 (216*12+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 12) := by lit_decide

theorem normalize_back_source_065 : outerBlock065=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_066 : outerBlock066=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_067 : outerBlock067=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*12) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_068 : outerBlock068=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*12)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_069 : outerBlock069=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*12+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_070 : outerBlock070=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*12+72)++normalizeCopy 9 (216*11+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 11) := by lit_decide

theorem normalize_back_source_071 : outerBlock071=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_072 : outerBlock072=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_073 : outerBlock073=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*11) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_074 : outerBlock074=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*11)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_075 : outerBlock075=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*11+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_076 : outerBlock076=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*11+72)++normalizeCopy 9 (216*10+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 10) := by lit_decide

theorem normalize_back_source_077 : outerBlock077=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_078 : outerBlock078=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_079 : outerBlock079=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*10) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_080 : outerBlock080=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*10)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_081 : outerBlock081=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*10+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_082 : outerBlock082=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*10+72)++normalizeCopy 9 (216*9+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 9) := by lit_decide

theorem normalize_back_source_083 : outerBlock083=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_084 : outerBlock084=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_085 : outerBlock085=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*9) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_086 : outerBlock086=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*9)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_087 : outerBlock087=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*9+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_088 : outerBlock088=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*9+72)++normalizeCopy 9 (216*8+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 8) := by lit_decide

theorem normalize_back_source_089 : outerBlock089=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_090 : outerBlock090=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_091 : outerBlock091=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*8) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_092 : outerBlock092=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*8)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_093 : outerBlock093=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*8+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_094 : outerBlock094=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*8+72)++normalizeCopy 9 (216*7+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 7) := by lit_decide

theorem normalize_back_source_095 : outerBlock095=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_096 : outerBlock096=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_097 : outerBlock097=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*7) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_098 : outerBlock098=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*7)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_099 : outerBlock099=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*7+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_100 : outerBlock100=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*7+72)++normalizeCopy 9 (216*6+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 6) := by lit_decide

theorem normalize_back_source_101 : outerBlock101=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_102 : outerBlock102=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_103 : outerBlock103=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*6) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_104 : outerBlock104=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*6)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_105 : outerBlock105=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*6+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_106 : outerBlock106=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*6+72)++normalizeCopy 9 (216*5+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 5) := by lit_decide

theorem normalize_back_source_107 : outerBlock107=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_108 : outerBlock108=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_109 : outerBlock109=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*5) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_110 : outerBlock110=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*5)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_111 : outerBlock111=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*5+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_112 : outerBlock112=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*5+72)++normalizeCopy 9 (216*4+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 4) := by lit_decide

theorem normalize_back_source_113 : outerBlock113=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_114 : outerBlock114=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_115 : outerBlock115=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*4) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_116 : outerBlock116=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*4)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_117 : outerBlock117=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*4+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_118 : outerBlock118=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*4+72)++normalizeCopy 9 (216*3+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 3) := by lit_decide

theorem normalize_back_source_119 : outerBlock119=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_120 : outerBlock120=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_121 : outerBlock121=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*3) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_122 : outerBlock122=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*3)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_123 : outerBlock123=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*3+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_124 : outerBlock124=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*3+72)++normalizeCopy 9 (216*2+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 2) := by lit_decide

theorem normalize_back_source_125 : outerBlock125=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_126 : outerBlock126=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_127 : outerBlock127=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*2) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_128 : outerBlock128=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*2)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_129 : outerBlock129=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*2+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_130 : outerBlock130=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*2+72)++normalizeCopy 9 (216*1+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 1) := by lit_decide

theorem normalize_back_source_131 : outerBlock131=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1504 1504 1360 := by lit_decide

theorem normalize_back_source_132 : outerBlock132=
    [.umov .x .x30 .v29 0]++normalizeCallArgs 1432 1288 1288 := by lit_decide

theorem normalize_back_source_133 : outerBlock133=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*1) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_134 : outerBlock134=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*1)++normalizeCallArgs 1432 1432 1288 := by lit_decide

theorem normalize_back_source_135 : outerBlock135=
    [.umov .x .x30 .v29 0]++normalizeCopy 9 (216*1+72) 1360++normalizeCallArgs 1360 1360 1432 := by lit_decide

theorem normalize_back_source_tail : outerBlock136.take 19=
    [.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 288 := by lit_decide


def normalizeBackRange (start : Nat) : Nat → Prog isa
  | 0 => .block []
  | n+1 => .seq (normalizeBackRow (normalizePrefixSlot start) start) (normalizeBackRange (start-1) n)

private theorem wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem normalize_back_source_end_0 : outerBlock076.take 19=[.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*11+72) := by lit_decide

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

theorem normalize_back_chunk0_wp {s : State} {Q : State → Prop} :
    WP isa normalizeBackChunk0 s Q ↔ WP isa (.seq (.block (VG.Impl.Weierstrass.AArch64.copy 9 1504 2152)) (normalizeBackRange 15 5)) s Q := by
  simp only [normalizeBackChunk0,sequence,List.foldr_cons,List.foldr_nil,normalizeBackRange,
    normalizeBackRow,normalizeBackX,normalizeBackY,normalizeMulStep,normalizeSquareStep,
    normalize_back_source_046,normalize_back_source_047,normalize_back_source_048,normalize_back_source_049,normalize_back_source_050,normalize_back_source_051,normalize_back_source_052,normalize_back_source_053,normalize_back_source_054,normalize_back_source_055,normalize_back_source_056,normalize_back_source_057,normalize_back_source_058,normalize_back_source_059,normalize_back_source_060,normalize_back_source_061,normalize_back_source_062,normalize_back_source_063,normalize_back_source_064,normalize_back_source_065,normalize_back_source_066,normalize_back_source_067,normalize_back_source_068,normalize_back_source_069,normalize_back_source_070,normalize_back_source_071,normalize_back_source_072,normalize_back_source_073,normalize_back_source_074,normalize_back_source_075,normalize_back_source_end_0]
  simp only [Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply wp_post_iff; intro t)

theorem normalize_back_source_head_1 : outerBlock076.drop 19=normalizeCopy 9 (216*10+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 10) := by lit_decide

theorem normalize_back_source_end_1 : outerBlock106.take 19=[.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*6+72) := by lit_decide

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

theorem normalize_back_chunk1_wp {s : State} {Q : State → Prop} :
    WP isa normalizeBackChunk1 s Q ↔ WP isa (normalizeBackRange 10 5) s Q := by
  simp only [normalizeBackChunk1,sequence,List.foldr_cons,List.foldr_nil,normalizeBackRange,
    normalizeBackRow,normalizeBackX,normalizeBackY,normalizeMulStep,normalizeSquareStep,
    normalize_back_source_head_1,normalize_back_source_077,normalize_back_source_078,normalize_back_source_079,normalize_back_source_080,normalize_back_source_081,normalize_back_source_082,normalize_back_source_083,normalize_back_source_084,normalize_back_source_085,normalize_back_source_086,normalize_back_source_087,normalize_back_source_088,normalize_back_source_089,normalize_back_source_090,normalize_back_source_091,normalize_back_source_092,normalize_back_source_093,normalize_back_source_094,normalize_back_source_095,normalize_back_source_096,normalize_back_source_097,normalize_back_source_098,normalize_back_source_099,normalize_back_source_100,normalize_back_source_101,normalize_back_source_102,normalize_back_source_103,normalize_back_source_104,normalize_back_source_105,normalize_back_source_end_1]
  simp only [Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply wp_post_iff; intro t)

theorem normalize_back_source_head_2 : outerBlock106.drop 19=normalizeCopy 9 (216*5+144) 1360++normalizeCallArgs 1288 1504 (normalizePrefixSlot 5) := by lit_decide

theorem normalize_back_source_end_2 : outerBlock136.take 19=[.umov .x .x30 .v29 0]++normalizeStoreCopy 9 1360 (216*1+72) := by lit_decide

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

theorem normalize_back_chunk2_wp {s : State} {Q : State → Prop} :
    WP isa normalizeBackChunk2 s Q ↔ WP isa (normalizeBackRange 5 5) s Q := by
  simp only [normalizeBackChunk2,sequence,List.foldr_cons,List.foldr_nil,normalizeBackRange,
    normalizeBackRow,normalizeBackX,normalizeBackY,normalizeMulStep,normalizeSquareStep,
    normalize_back_source_head_2,normalize_back_source_107,normalize_back_source_108,normalize_back_source_109,normalize_back_source_110,normalize_back_source_111,normalize_back_source_112,normalize_back_source_113,normalize_back_source_114,normalize_back_source_115,normalize_back_source_116,normalize_back_source_117,normalize_back_source_118,normalize_back_source_119,normalize_back_source_120,normalize_back_source_121,normalize_back_source_122,normalize_back_source_123,normalize_back_source_124,normalize_back_source_125,normalize_back_source_126,normalize_back_source_127,normalize_back_source_128,normalize_back_source_129,normalize_back_source_130,normalize_back_source_131,normalize_back_source_132,normalize_back_source_133,normalize_back_source_134,normalize_back_source_135,normalize_back_source_end_2]
  simp only [Nat.reduceAdd,Nat.reduceSub,Nat.reduceMul]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply wp_post_iff; intro t)

def normalizeBackMachine : Prog isa := .seq normalizeBackChunk0 (.seq normalizeBackChunk1 normalizeBackChunk2)

theorem normalize_back_machine_wp {s : State} {Q : State → Prop} :
    WP isa normalizeBackMachine s Q ↔
      WP isa (.seq (.block (VG.Impl.Weierstrass.AArch64.copy 9 1504 2152)) (normalizeBackWork 15)) s Q := by
  rw [normalizeBackMachine,WP.seq_iff,normalize_back_chunk0_wp]
  simp only [normalizeBackRange,normalizeBackWork]
  simp only [Nat.reduceAdd,Nat.reduceSub]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_nil_iff] |
    (rw [normalize_back_chunk1_wp]; simp only [normalizeBackRange,Nat.reduceSub]) |
    (rw [normalize_back_chunk2_wp]; simp only [normalizeBackRange,Nat.reduceSub]) |
    (apply wp_post_iff; intro t)

end VG.Proof.Weierstrass.AArch64.P521Native
