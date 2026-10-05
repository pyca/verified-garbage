import VerifiedGarbage.Proof.Sha3.AArch64.Call
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Unrolled
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Bulk
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Resident.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Resident

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorBackend`. -/
section

namespace VG.Proof.Sha3.AArch64.Scalar.VectorSlots

open VG VG.AArch64

def callee : Impl.Sha3.AArch64.Callee where
  name := "vg_keccak_f1600"
  code := Impl.Sha3.AArch64.Scalar.unrolledPermute
  suffix := ""
  absorbOverride := none

/- The rounds of the permutation, from nothing public. They write every
general-purpose register but no vector register other than the temporary
lanes `v24` and `v25`, so they keep public the vectors that hold the
callee-saved registers and the pointers (`Boundary.save`). Each summary of
the permutation below uses this one rather than analysing the rounds again. -/
taint_summary VSums.rounds : VectorTaint.taint (VectorTaint.ofRegs [])
  (.block Impl.Sha3.AArch64.Scalar.unrolledRounds)
  keeping ((AArch64.Taint.ofRegs [], RegSet.ofList
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v12, .v13, .v14, .v15,
      .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v26, .v27, .v28, .v29, .v30, .v31]) : VectorTaint.T)

sponge_taint_summaries VSums callee saving using VSums.rounds

theorem absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem sampleFullTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem sampleFastTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeNWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee 168 1008) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mldsaBoundedTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee 136 544) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee 136 272) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkemKgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.kgAWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkemKgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.kgCWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkemEnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem.AArch64.enAWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkemEnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.enCWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkemDeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.deAWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkemDeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.deCWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkem1024KgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.kgAWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkem1024KgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.kgCWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkem1024EnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem1024.AArch64.enAWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkem1024EnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.enCWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkem1024DeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.deAWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mlkem1024DeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.deCWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mldsaSeedsTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee p) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide VSums

theorem mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide VSums

theorem mldsaSignDecodeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true :=
  by sponge_taint_decide VSums

theorem mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide VSums

def backend : Permutation where
  callee := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.callee
  features := []
  ok := VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_correct
  noFrames := VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_noFrames
  absorbOverrideOk := by intro code h; cases h
  absorbOverrideDepth := by intro code h; cases h
  absorbTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.absorbTaint
  padTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.padTaint
  squeezeTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.squeezeTaint
  sampleFullTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.sampleFullTaint
  sampleFastTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.sampleFastTaint
  mldsaNttTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaNttTaint
  mldsaBoundedTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaBoundedTaint
  mldsaBallTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaBallTaint
  mldsaMaskTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaMaskTaint
  mlkemKgATaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkemKgATaint
  mlkemKgCTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkemKgCTaint
  mlkemEnATaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkemEnATaint
  mlkemEnCTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkemEnCTaint
  mlkemDeATaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkemDeATaint
  mlkemDeCTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkemDeCTaint
  mlkem1024KgATaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkem1024KgATaint
  mlkem1024KgCTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkem1024KgCTaint
  mlkem1024EnATaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkem1024EnATaint
  mlkem1024EnCTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkem1024EnCTaint
  mlkem1024DeATaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkem1024DeATaint
  mlkem1024DeCTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mlkem1024DeCTaint

  mldsaSeedsTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaSeedsTaint
  mldsaTrHashTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaTrHashTaint
  mldsaVerifyHashTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaVerifyHashTaint

  mldsaSignDecodeTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaSignDecodeTaint
  mldsaSignCommitTaint := VG.Proof.Sha3.AArch64.Scalar.VectorSlots.mldsaSignCommitTaint

end VG.Proof.Sha3.AArch64.Scalar.VectorSlots

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ResidentBackend`. -/
section

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
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

taint_summary VSums.absorb24 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

taint_summary VSums.absorb28 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27, .x28])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

taint_summary VSums.absorb27 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x25, .x26, .x27])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee))
  using VectorSlots.VSums.perm28s VectorSlots.VSums.perm27s VectorSlots.VSums.perm26s
    VectorSlots.VSums.permS VectorSlots.VSums.perm28 VectorSlots.VSums.perm27
    VectorSlots.VSums.perm26 VectorSlots.VSums.perm

taint_summary VSums.absorb24_26 : VectorTaint.taint
  (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x24, .x25, .x26])
  (.call ("vg_keccak_absorb_scratch" ++ callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee))
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

#assert_standard_axioms VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.absorb_correct

theorem absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem sampleFullTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem sampleFastTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeNWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee 168 1008) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaBoundedTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee 136 544) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee 136 272) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemKgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.kgAWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemKgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.kgCWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemEnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem.AArch64.enAWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemEnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.enCWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemDeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.deAWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkemDeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.deCWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024KgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.kgAWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024KgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.kgCWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024EnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem1024.AArch64.enAWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024EnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.enCWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024DeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.deAWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mlkem1024DeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.deCWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaSeedsTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee p) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide_resident

theorem mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide_resident

theorem mldsaSignDecodeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true :=
  by sponge_taint_decide_resident

theorem mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide_resident

def backend : Permutation where
  callee := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.callee
  features := []
  ok := VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_correct
  noFrames := VG.Proof.Sha3.AArch64.Scalar.unrolled_permute_noFrames
  absorbOverrideOk := by
    intro code h
    cases h
    exact VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.absorb_correct
  absorbOverrideDepth := by
    intro code h
    cases h
    exact Sha3.Vector.Resident.absorb_depth VectorSlots.backend _ VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.bulk_depth
  absorbTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.absorbTaint
  padTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.padTaint
  squeezeTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.squeezeTaint
  sampleFullTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.sampleFullTaint
  sampleFastTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.sampleFastTaint
  mldsaNttTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaNttTaint
  mldsaBoundedTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaBoundedTaint
  mldsaBallTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaBallTaint
  mldsaMaskTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaMaskTaint
  mlkemKgATaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkemKgATaint
  mlkemKgCTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkemKgCTaint
  mlkemEnATaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkemEnATaint
  mlkemEnCTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkemEnCTaint
  mlkemDeATaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkemDeATaint
  mlkemDeCTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkemDeCTaint
  mlkem1024KgATaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkem1024KgATaint
  mlkem1024KgCTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkem1024KgCTaint
  mlkem1024EnATaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkem1024EnATaint
  mlkem1024EnCTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkem1024EnCTaint
  mlkem1024DeATaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkem1024DeATaint
  mlkem1024DeCTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mlkem1024DeCTaint

  mldsaSeedsTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaSeedsTaint
  mldsaTrHashTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaTrHashTaint
  mldsaVerifyHashTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaVerifyHashTaint

  mldsaSignDecodeTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaSignDecodeTaint
  mldsaSignCommitTaint := VG.Proof.Sha3.AArch64.Scalar.ResidentBackend.mldsaSignCommitTaint

end VG.Proof.Sha3.AArch64.Scalar.ResidentBackend

end
