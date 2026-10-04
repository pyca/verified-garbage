import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorBackend
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Bulk
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident

/-!
# The scalar Keccak backend with its resident absorb

The scalar permutation (`VectorSlots`), whose sponge absorbs whole blocks
with the state in registers (`Scalar.Resident.bulk`) under the resident
absorber's guards (`Sha3.Vector.Resident.absorbWith`), falling back to the
ordinary streaming absorb for the rest.
-/

namespace VG.Proof.Sha3.AArch64.Scalar.ResidentBackend

open VG VG.AArch64

def callee : Impl.Sha3.AArch64.Callee :=
  { VectorSlots.callee with
    absorbOverride := some (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorbWith
      Impl.Sha3.AArch64.Scalar.Resident.bulk VectorSlots.callee) }

/-! ## Summaries for the constant-time checks

`callee` differs from `VectorSlots.callee` only in its absorb, so the
summaries of the permutation, `pad` and `squeeze` are `VectorSlots.VSums`'s
(what `sponge_taint_summaries VSums callee saving` would prove again), and
only the absorb's are proven here, over them. -/

taint_summary VSums.absorb23 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x23, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

taint_summary VSums.absorb24 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

taint_summary VSums.absorb28 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

taint_summary VSums.absorb27 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

taint_summary VSums.absorb24_26 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

/-- `sponge_taint_decide VSums`, with the summaries of the absorb above and
`VectorSlots.VSums`'s others, in the same order. -/
local macro "sponge_taint_decide_resident" : tactic => `(tactic|
  taint_decide_sum [
    VSums.absorb23, VSums.absorb24, VSums.absorb28, VSums.absorb27, VSums.absorb24_26,
    VectorSlots.VSums.pad28, VectorSlots.VSums.pad27, VectorSlots.VSums.pad26,
    VectorSlots.VSums.squeeze28, VectorSlots.VSums.squeeze27, VectorSlots.VSums.squeeze26,
    VectorSlots.VSums.perm28s, VectorSlots.VSums.perm27s, VectorSlots.VSums.perm26s,
    VectorSlots.VSums.permS, VectorSlots.VSums.perm28, VectorSlots.VSums.perm27,
    VectorSlots.VSums.perm26, VectorSlots.VSums.perm, MlKemSums.ntt, MlKemSums.nttInv,
    MlKemSums.mul, MlKemSums.add, MlKemSums.sub, MlKemSums.cbd2, MlKemSums.encode12,
    MlKemSums.decode12, MlKemSums.ce, MlKemSums.dd, MlKemSums.ce1024, MlKemSums.dd1024])

theorem bulk_depth : Impl.Sha3.AArch64.Scalar.Resident.bulk.aarch64Depth = 0 := by rfl

theorem absorb_correct (a : State) (hp : Proof.Sha3.absorbAArch64.pre a) :
    ∃ t q, Exec isa (Impl.Sha3.AArch64.Sha3.Vector.Resident.absorbWith
      Impl.Sha3.AArch64.Scalar.Resident.bulk VectorSlots.callee) a t q ∧
      abiPreserved a q ∧ Proof.Sha3.absorbAArch64.post a q :=
  Sha3.Vector.Resident.absorb_correct VectorSlots.backend _ Resident.functional a hp

#assert_standard_axioms absorb_correct

theorem absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem sampleFullTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem sampleFastTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeNWith callee 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaBoundedTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 544) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemKgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.kgAWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemKgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.kgCWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemEnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem.AArch64.enAWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemEnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.enCWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemDeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.deAWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemDeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.deCWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024KgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.kgAWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024KgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.kgCWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024EnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem1024.AArch64.enAWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024EnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.enCWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024DeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.deAWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024DeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.deCWith callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaSeedsTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith callee p) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide_resident

theorem mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide_resident

theorem mldsaSignDecodeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide_resident

def backend : Permutation where
  callee := callee
  features := []
  ok := VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_correct
  noFrames := VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_noFrames
  absorbOverrideOk := by
    intro code h
    cases h
    exact absorb_correct
  absorbOverrideDepth := by
    intro code h
    cases h
    exact Sha3.Vector.Resident.absorb_depth VectorSlots.backend _ bulk_depth
  absorbTaint := absorbTaint
  padTaint := padTaint
  squeezeTaint := squeezeTaint
  sampleFullTaint := sampleFullTaint
  sampleFastTaint := sampleFastTaint
  mldsaNttTaint := mldsaNttTaint
  mldsaBoundedTaint := mldsaBoundedTaint
  mldsaBallTaint := mldsaBallTaint
  mldsaMaskTaint := mldsaMaskTaint
  mlkemKgATaint := mlkemKgATaint
  mlkemKgCTaint := mlkemKgCTaint
  mlkemEnATaint := mlkemEnATaint
  mlkemEnCTaint := mlkemEnCTaint
  mlkemDeATaint := mlkemDeATaint
  mlkemDeCTaint := mlkemDeCTaint
  mlkem1024KgATaint := mlkem1024KgATaint
  mlkem1024KgCTaint := mlkem1024KgCTaint
  mlkem1024EnATaint := mlkem1024EnATaint
  mlkem1024EnCTaint := mlkem1024EnCTaint
  mlkem1024DeATaint := mlkem1024DeATaint
  mlkem1024DeCTaint := mlkem1024DeCTaint

  mldsaSeedsTaint := mldsaSeedsTaint
  mldsaTrHashTaint := mldsaTrHashTaint
  mldsaVerifyHashTaint := mldsaVerifyHashTaint

  mldsaSignDecodeTaint := mldsaSignDecodeTaint
  mldsaSignCommitTaint := mldsaSignCommitTaint

end VG.Proof.Sha3.AArch64.Scalar.ResidentBackend
