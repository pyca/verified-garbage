module

public import VerifiedGarbage.Proof.Dsa.AArch64.SigningInitialize
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Finish
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.DomainWidths
import Mathlib.Algebra.Group.Nat.Defs

/-! ### `Dsa.AArch64.Failure`, which only this module used -/

section

/-! # Encoding a DSA arithmetic result into its separate output buffer -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

open VG.Impl.Dsa.Layout

theorem signFailure_ok {s : State} {B : Addr} {Z k q : Nat} {op : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : pWorkspace ≤ Z) (hkq : k = 2 * q) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B Field.out.offset = op) (hK : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa SignVerify.signFailure s fun t => Spec.Rsa.bytesAt t.mem op k = List.replicate k 0 ∧
      t.gpr .x0 = 0 ∧ (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep coreRegs s t := by
  have hn := hs.nowrap
  unfold SignVerify.signFailure seqs
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 k ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [h0, Core.field, field_enc .out, field_enc .qLen, fieldAddress,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ), hO, hK]
    rw [BitVec.ofNat_add_ofNat, hkq, Nat.two_mul]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (N := k) (by omega_using [hk']) (by omega_using [hk1]) (BInv s₁ op)
    (fun j hj t hI _ => bStep_ok (by omega_using [hk']) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hj hI)
    ⟨Keep.refl _ _, h1, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ h2) fun t₂ hI => ?_)
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = 0 ∧ t.mem = t₂.mem) (by brun) (by decide) (by decide)
    (by decide +kernel)) fun t ⟨⟨hx, hm⟩, k₃⟩ => ⟨?_, hx, fun x hx' => ?_, ((k₁.trans hI.keep).trans k₃).mono
      (by decide)⟩
  · rw [bytesAt_eq, List.eq_replicate_iff]
    refine ⟨by simp, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hm]
    exact hI.bytes i (List.mem_range.mp hi)
  · rw [hm, hI.frame x hx', hm₁]

end VG.Proof.Dsa.AArch64

end

end

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
    have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (signFailure_ok hs.scratch hs.x0 (by decide) rfl (by omega_using [hwidth]) (by omega_using [hwidth])
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
