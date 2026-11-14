module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildDouble
public import VerifiedGarbage.Impl.Weierstrass.AArch64.P521Native.Code
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native
open VG.Impl.Mont.AArch64

def buildRestore : List Instr := [.umov .x .x30 .v29 0]

theorem build_double_source7 : outerBlock007.drop 55=normalizeCallArgs 1720 424 424 := by lit_decide

theorem build_double_source8 : outerBlock008=buildRestore++normalizeCallArgs 1792 3160 3160 := by lit_decide

theorem build_double_source9 : outerBlock009=buildRestore++
  (P521Linear.add 1864 2800 1720++(P521Linear.sub 1936 2800 1720++normalizeCallArgs 2008 1864 1936)) := by lit_decide

theorem build_double_source10 : outerBlock010=buildRestore++
  (P521Linear.add 1864 3160 424++normalizeCallArgs 1936 2008 2008) := by lit_decide

theorem build_double_source11 : outerBlock011=buildRestore++normalizeCallArgs 2080 2800 1792 := by lit_decide

theorem build_double_source12 : outerBlock012=buildRestore++normalizeCallArgs 1864 1864 1864 := by lit_decide

theorem build_double_source13 : outerBlock013=buildRestore++
  (P521Linear.cms 1936 12 2080 9 1936++(P521Linear.sub 1864 1864 1720++
    (P521Linear.sub 1432 1864 1792++normalizeCallArgs 1720 1792 1792))) := by lit_decide

theorem build_double_source14 : outerBlock014=buildRestore++normalizeCallArgs 2008 1936 2008 := by lit_decide

theorem build_double_source15 : outerBlock015.take 283=buildRestore++
  (P521Linear.cms 1288 4 2080 1 1936++P521Linear.cms 1360 3 2008 8 1720) := by lit_decide

def buildDoubleMachine : Prog isa := sequence [
 .block (outerBlock007.drop 55),callNormalSqr,.block outerBlock008,callNormalSqr,
 .block outerBlock009,callNormalMul,.block outerBlock010,callNormalSqr,
 .block outerBlock011,callNormalMul,.block outerBlock012,callNormalSqr,
 .block outerBlock013,callNormalSqr,.block outerBlock014,callNormalMul,.block (outerBlock015.take 283)]

private theorem wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem build_double_machine_wp {s : State} {Q : State → Prop} :
    WP isa buildDoubleMachine s Q ↔ WP isa (fieldProgram id buildDoubleOps) s Q := by
  simp only [buildDoubleMachine,sequence,List.foldr_cons,List.foldr_nil,
    buildDoubleOps,fieldProgram,fieldCode,id,show ¬(1864=1936) from by decide,show ¬(2800=1792) from by decide,
    show ¬(1936=2008) from by decide,ite_true,ite_false,
    normalizeMulStep,normalizeSquareStep,
    build_double_source7,build_double_source8,build_double_source9,build_double_source10,
    build_double_source11,build_double_source12,build_double_source13,build_double_source14,build_double_source15]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply wp_post_iff; intro t)

end VG.Proof.Weierstrass.AArch64.P521Native
