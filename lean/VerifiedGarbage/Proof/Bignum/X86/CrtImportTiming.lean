module

public import VerifiedGarbage.Proof.Bignum.X86.CrtPair
public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Bignum.X86.CrtImportStep
import VerifiedGarbage.Proof.Bignum.X86.PublicLoadTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Import all private components with traces determined only by slice geometry -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.Crt VG.Impl.Mont.X86.Dynamic

theorem importStep_relCT (base : Addr) (bytes len k i dst : Nat) (args : Nat → BitVec 32)
    (hi : i ∈ componentArguments) (hd : dst < 20)
    (hk : Spec.Rsa.modulusWords len ≤ k) (hk' : k ≤ 2 * Spec.Rsa.modulusWords len) :
    RelCT isa (Pair base bytes len args)
      (importComponent k i (slot (Spec.Rsa.modulusWords len) dst)) (Pair base bytes len args) := by
  intro s t tr ur sf tf H E F
  have islot : i + 1 < 18 := by
    simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have Trace := (loadArgument_trace i (i + 1) k _ (args i) (args (i + 1)) _ _ _ _ _ _
    ⟨H.agree, (H.left.stack i (by omega)).readSrc, (H.right.stack i (by omega)).readSrc,
      (H.left.stack (i + 1) islot).readSrc, (H.right.stack (i + 1) islot).readSrc⟩ E F).1
  obtain ⟨_, _, Is, Ks⟩ := wp_result (importStep_ok H.left hi hd hk hk') E
  obtain ⟨_, _, It, Kt⟩ := wp_result (importStep_ok H.right hi hd hk hk') F
  exact ⟨Trace, Is, It, (Ks.1 _ (by decide)).trans (H.sp.trans (Kt.1 _ (by decide)).symm)⟩

theorem importComponents_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (Pair base bytes len args) (importComponents (Spec.Rsa.modulusWords len))
      (Pair base bytes len args) := by
  unfold importComponents
  refine VG.RelCT.seq (importStep_relCT base bytes len _ 2 9 args (by decide) (by decide) (by omega) (by omega)) ?_
  refine VG.RelCT.seq (importStep_relCT base bytes len _ 4 15 args (by decide) (by decide) (by omega) (by omega)) ?_
  refine VG.RelCT.seq (importStep_relCT base bytes len _ 6 10 args (by decide) (by decide) (by omega) (by omega)) ?_
  refine VG.RelCT.seq (importStep_relCT base bytes len _ 8 11 args (by decide) (by decide) (by omega) (by omega)) ?_
  refine VG.RelCT.seq (importStep_relCT base bytes len _ 10 12 args (by decide) (by decide) (by omega) (by omega)) ?_
  exact VG.RelCT.seq (importStep_relCT base bytes len _ 12 13 args (by decide) (by decide) (by omega) (by omega))
    (importStep_relCT base bytes len _ 14 14 args (by decide) (by decide) (by omega) (by omega))

end VG.Proof.Bignum.X86.Crt
