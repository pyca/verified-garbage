module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningInitialize
import VerifiedGarbage.Proof.Dsa.AArch64.Failure
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.DomainWidths
import Mathlib.Algebra.Group.Nat.Defs

/-! # Both signing branches return the packed byte specification -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def SigningPost (p : SigningInput) (original t : State) : Prop :=
  let result := Spec.Dsa.signBytes p.pLen p.qLen p.key p.nonce p.digest
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
  Spec.Rsa.bytesAt t.mem (original.gpr .x0) (2 * p.qLen) = result.getD (List.replicate (2 * p.qLen) 0) ∧
  (∀ x, usedBytes ≤ ofs p.base x → (∀ i < 2 * p.qLen, x ≠ original.gpr .x0 + BitVec.ofNat 64 i) →
    t.mem x = original.mem x) ∧ Keep coreRegs original t

theorem signingAccepted_ok (M : Mont) {p : SigningInput} {original s : State} (h : SigningPre p original)
    (hi : SigningInitialized p original h.pLength s) (ha : p.accepted = true) :
    WP isa (signBody M.mm) s (SigningPost p original) := by
  obtain ⟨pi, qi, hr, ho, hm, hf, hk⟩ := hi
  let L := (p.layout original h.pLength).withInverses pi qi
  obtain ⟨hsize, hpodd, hqodd⟩ := p.shapeFacts ha
  have hpf : L.modulus ≤ 256 ^ L.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.p
    rw [p.components.pLength] at hh
    exact Nat.le_of_lt hh
  have hqf : L.subgroup ≤ 256 ^ L.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.components.q
    rw [p.components.qLength] at hh
    exact Nat.le_of_lt hh
  have hqn := VG.Proof.Dsa.subgroup_scan_width hsize
  have hkey : Spec.Dsa.privateKeyBytes L.pLen L.qLen p.key = p.values.key L p.components.y := rfl
  refine WP.mono (signBody_spec M hr p.values ho hsize hpodd hqodd hpf hqf p.keyLength hkey hqn rfl hm
    (fun i hi => by rw [hk.wr]; exact h.writable i hi) h.separate)
    fun t ⟨hret, hout, hframe, hkeep⟩ => ?_
  exact ⟨hret, hout,
    fun x hx ho => (hframe x hx ho).trans (hf x hx), (hk.trans hkeep).mono (by decide)⟩

theorem signingRejected_ok {p : SigningInput} {original s : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength s) (ha : p.accepted = false) :
    WP isa SignVerify.signFailure s (SigningPost p original) := by
  have hparams : ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes p.pLen p.qLen p.key).params :=
    shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  have hnone := signBytes_invalid_shape (nonce := p.nonce) (digest := p.digest) hparams
  have hwidth : 1 ≤ p.qLen ∧ p.qLen ≤ 32 := by
    have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega
  refine WP.mono (signFailure_ok hs.scratch hs.x0 (by decide) rfl (by omega) (by omega)
    (hs.fields .out) (hs.fields .qLen)
    (fun i hi => by rw [hs.keep.wr]; exact h.writable i hi))
    fun t ⟨hout, hret, hframe, hk⟩ => ?_
  unfold SigningPost
  rw [hnone]
  refine ⟨?_, ?_,
    fun x hx ho => (hframe x ho).trans (hs.frame x hx), (hs.keep.trans hk).mono (by decide)⟩
  · exact hret
  · exact hout

end VG.Proof.Dsa.AArch64
