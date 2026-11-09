module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.BuildDoubleCode
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit

-- separate module: Closed instruction/source identities and the table mixed-add field schedule cost 0.62s plus 0.55s arithmetic replay versus 0.41s imports; retain this computational boundary separately from its semantic group adapter.

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG.Proof.Mont.AArch64.P521Field VG.Proof.Weierstrass

/-- The canonical field schedule used while filling entries 3 through 16. -/
def buildMixedOps : List PointOp := [
  .mul 1720 1648 1648 false,.mul 1792 2800 1720 false,.mul 1864 1648 1720 false,
  .mul 1864 3160 1864 false,.sub 1792 1792 1504,.sub 1864 1864 1576,
  .mul 1936 1792 1792 false,.mul 2008 1792 1936 false,.mul 1936 1504 1936 false,
  .mul 1288 1864 1864 false,.sub 1288 1288 2008,.add 2080 1936 1936,
  .sub 1288 1288 2080,.sub 1936 1936 1288,.mul 1936 1864 1936 false,
  .mul 2008 1576 2008 false,.sub 1360 1936 2008,.mul 1432 1648 1792 false]

theorem buildMixed_value {F : Type _} [Lean.Grind.CommRing F] (E : Nat → F) :
    (pointRun buildMixedOps E 1288,pointRun buildMixedOps E 1360,pointRun buildMixedOps E 1432)=
      maddJF (E 1504) (E 1576) (E 1648) (E 2800) (E 3160) := by
  simp only [pointRun,buildMixedOps,List.foldl,PointOp.run,Function.update_apply,maddJF,ite_true]
  rfl

theorem buildMixed_reads : fieldReads buildMixedOps [1504,1576,1648,2800,3160]=true := by decide

theorem buildMixed_slots : ∀op∈buildMixedOps,∀x∈op.out::op.ins,buildSlot x := by
  simp [buildMixedOps,PointOp.out,PointOp.ins,buildSlot]

theorem buildMixed_coeffs : ∀op∈buildMixedOps,fieldCoeffs op := by
  simp [buildMixedOps,fieldCoeffs]

end VG.Proof.Weierstrass.AArch64.P521Native

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64.P521Native
open VG.Impl.Mont.AArch64

theorem build_mixed_source16 : outerBlock016=normalizeCallArgs 1720 1648 1648 := by lit_decide

theorem build_mixed_source17 : outerBlock017=buildRestore++(normalizeCallArgs 1792 2800 1720) := by lit_decide

theorem build_mixed_source18 : outerBlock018=buildRestore++(normalizeCallArgs 1864 1648 1720) := by lit_decide

theorem build_mixed_source19 : outerBlock019=buildRestore++(normalizeCallArgs 1864 3160 1864) := by lit_decide

theorem build_mixed_source20 : outerBlock020=buildRestore++(P521Linear.sub 1792 1792 1504++(P521Linear.sub 1864 1864 1576++(normalizeCallArgs 1936 1792 1792))) := by lit_decide

theorem build_mixed_source21 : outerBlock021=buildRestore++(normalizeCallArgs 2008 1792 1936) := by lit_decide

theorem build_mixed_source22 : outerBlock022=buildRestore++(normalizeCallArgs 1936 1504 1936) := by lit_decide

theorem build_mixed_source23 : outerBlock023=buildRestore++(normalizeCallArgs 1288 1864 1864) := by lit_decide

theorem build_mixed_source24 : outerBlock024=buildRestore++(P521Linear.sub 1288 1288 2008++(P521Linear.add 2080 1936 1936++(P521Linear.sub 1288 1288 2080++(P521Linear.sub 1936 1936 1288++(normalizeCallArgs 1936 1864 1936))))) := by lit_decide

theorem build_mixed_source25 : outerBlock025=buildRestore++(normalizeCallArgs 2008 1576 2008) := by lit_decide

theorem build_mixed_source26 : outerBlock026=buildRestore++(P521Linear.sub 1360 1936 2008++(normalizeCallArgs 1432 1648 1792)) := by lit_decide

theorem build_mixed_source27 : outerBlock027.take 1=buildRestore := by lit_decide

def buildMixedMachine : Prog isa := sequence [
  .block outerBlock016,
  callNormalSqr,
  .block outerBlock017,
  callNormalMul,
  .block outerBlock018,
  callNormalMul,
  .block outerBlock019,
  callNormalMul,
  .block outerBlock020,
  callNormalSqr,
  .block outerBlock021,
  callNormalMul,
  .block outerBlock022,
  callNormalMul,
  .block outerBlock023,
  callNormalSqr,
  .block outerBlock024,
  callNormalMul,
  .block outerBlock025,
  callNormalMul,
  .block outerBlock026,
  callNormalMul,
  .block (outerBlock027.take 1)]

private theorem wp_post_iff {code : Prog isa} {s : State} {Q R : State → Prop}
    (h : ∀t,Q t ↔ R t) : WP isa code s Q ↔ WP isa code s R :=
  ⟨fun q => WP.mono q (fun t ht => (h t).mp ht),fun q => WP.mono q (fun t ht => (h t).mpr ht)⟩

theorem build_mixed_machine_wp {s : State} {Q : State → Prop} :
    WP isa buildMixedMachine s Q ↔ WP isa (fieldProgram id buildMixedOps) s Q := by
  simp only [buildMixedMachine,sequence,List.foldr_cons,List.foldr_nil,buildMixedOps,fieldProgram,fieldCode,id,
    show ¬(2800=1720) from by decide,show ¬(1648=1720) from by decide,show ¬(3160=1864) from by decide,show ¬(1792=1936) from by decide,show ¬(1504=1936) from by decide,show ¬(1864=1936) from by decide,show ¬(1576=2008) from by decide,show ¬(1648=1792) from by decide,ite_true,ite_false,
    normalizeMulStep,normalizeSquareStep,
    build_mixed_source16,build_mixed_source17,build_mixed_source18,build_mixed_source19,build_mixed_source20,build_mixed_source21,build_mixed_source22,build_mixed_source23,build_mixed_source24,build_mixed_source25,build_mixed_source26,build_mixed_source27]
  repeat' first | rfl | rw [VG.WP.seq_iff] | rw [VG.WP.block_append_iff] | rw [VG.WP.block_nil_iff] | (apply wp_post_iff; intro t)

end VG.Proof.Weierstrass.AArch64.P521Native
