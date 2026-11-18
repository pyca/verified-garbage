module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSlices
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
public import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.EntryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ComputeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleCTState
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningInitialize
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
public import Mathlib.Algebra.Group.Nat.Defs
meta import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceBridge
meta import VerifiedGarbage.Proof.Dsa.AArch64.DomainShapeCT
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.AArch64.SigningInitialize
meta import VerifiedGarbage.Proof.Dsa.AArch64.ShapeCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
meta import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.DomainWidths
public import VerifiedGarbage.Proof.Dsa.AArch64.Finish
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
meta import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
meta import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
meta import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
meta import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify
meta import VerifiedGarbage.Proof.Dsa.AArch64.Finish
meta import VerifiedGarbage.Proof.Dsa.AArch64.Operands
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Dsa.AArch64.PrevalidatedSignCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.PrevalidatedSign`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SigningReturn`, which this module and modules that import it used -/

section

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

end

end

/-! # Functional correctness of an AArch64 DSA signing attempt for a validated private key

The program is the signer's, with the domain and key checks replaced by
rebuilding q−2 and the nonce's range check: the precondition that the exact
key bytes validate makes the omitted checks' mask true. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def prevalidatedSignAccepted (L : ExecutionLayout) (data : SignValues) (valid : Bool) : Bool :=
  !decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.s L), b = 0) &&
  (!decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.r L), b = 0) &&
  (decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup) && valid))

theorem prevalidatedSignCompute_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues)
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hx : OperandBytes s0 L.base usedBytes Core.privateScalar data.privateScalar)
    (hn : OperandBytes s0 L.base usedBytes Core.nonce data.nonce)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen)
    (hxl : data.privateScalar.length = L.qLen) (hnl : data.nonce.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (PrevalidatedSign.compute M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (prevalidatedSignAccepted L data valid) ∧
      Spec.Rsa.bytesAt s5.mem (off L.base r) L.qLen = Spec.Dsa.encodeBE L.qLen (data.r L) ∧
      Spec.Rsa.bytesAt s5.mem (off L.base s) L.qLen = Spec.Dsa.encodeBE L.qLen (data.s L) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega_using [hqu]
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega_using [hqu]
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega_using [hqu]
  unfold PrevalidatedSign.compute
  refine WP.seq (WP.mono (readyMinus_ok h0 .q 2 (by decide)
    (by change 2 ≤ L.subgroup; omega_using [hq]) qMinusTwo (by decide) hqm) fun s1 h1 => ?_)
  have hg1 := h1.external (by decide) hqm hg
  have hx1 := h1.external (by decide) hqm hx
  have hn1 := h1.external (by decide) hqm hn
  have hz1 := h1.external (by decide) hqm hz
  have hm1 := (h1.fields (by decide) hqm .mask).trans hm
  have hqm1 := h1.output (by decide) hqm
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.nonce (by trivial) hn1.active
    (by rw [hnl]; omega_using [hql]) (by simp only [hnl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm1) fun s2 h2 => ?_)
  have hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hx2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.privateScalar]) hx1
  have hn2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.nonce]) hn1
  have hz2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz1
  have hqm2 := h2.preserve h1.ready (Nat.le_refl _) (by decide) (by trivial) hqm1
  refine WP.seq (WP.mono (coreSign_ok M h2.ready hp hq hop hoq hpf hqf data hg2 hn2 hx2 hz2
    hgl hnl hxl hzl hqm2) fun s3 ⟨h3, hr3bytes, hs3bytes, hf3, hm3eq, hk3⟩ => ?_)
  have hm3 := hm3eq.trans h2.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] at hm3
  have hr3 := h3.encodedLocal .q r (data.r L) (by decide) hr hr3bytes
  have hs3 := h3.encodedLocal .q s (data.s L) (by decide) hs hs3bytes
  refine WP.seq (WP.mono (readyZero_ok h3 (Core.scalar r) (by change r < 2 ^ 16; decide) hr3
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) true hm3) fun s4 h4 => ?_)
  have hr4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hr3
  have hs4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hs3
  refine WP.mono (readyZero_ok h4.ready (Core.scalar s) (by change s < 2 ^ 16; decide) hs4
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) true h4.mask) fun s5 h5 => ?_
  have hr5 := h5.preserve h4.ready (Nat.le_refl _) (by decide) (by trivial) hr4
  have hs5 := h5.preserve h4.ready (Nat.le_refl _) (by decide) (by trivial) hs4
  refine ⟨h5.ready, ?_, ?_, ?_,
    ((((h1.scheduleFrame (by decide) hqm).trans h2.scheduleFrame).trans hf3).trans
      h4.scheduleFrame).trans h5.scheduleFrame,
    ((((h1.keep.trans h2.keep).trans hk3).trans h4.keep).trans h5.keep).mono (by decide)⟩
  · have hm5 := h5.mask
    simp only [↓reduceIte, ModulusSide.length] at hm5
    exact hm5
  · have hh := operand_bytesAt hr5
    rw [encodeBE_length] at hh
    exact hh
  · have hh := operand_bytesAt hs5
    rw [encodeBE_length] at hh
    exact hh

def prevalidatedSignBody (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (PrevalidatedSign.compute mul) signRelease

theorem prevalidatedSignBody_ok (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues) {yb qb : List Byte} (h : SigningOperands L data yb qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (prevalidatedSignBody M.mm) s0 fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (prevalidatedSignAccepted L data valid).toNat ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) =
        (if prevalidatedSignAccepted L data valid then Spec.Dsa.encodeBE L.qLen (data.r L) ++
          Spec.Dsa.encodeBE L.qLen (data.s L) else List.replicate (2 * L.qLen) 0) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  unfold prevalidatedSignBody
  refine WP.seq (WP.mono (prevalidatedSignCompute_ok M h0 hp hq hop hoq hpf hqf data h.generator
    h.privateScalar h.nonce h.digest h.generatorLength h.privateLength h.nonceLength h.digestBound hm)
    fun s1 ⟨h1, hm1, hr1, hs1, hf1, hk1⟩ => ?_)
  refine WP.mono (signRelease_ok h1 hm1 (fun i hi => by rw [hk1.wr]; exact hw i hi) hsep)
    fun t ⟨ha, hb, hf, hk⟩ => ?_
  refine ⟨ha, ?_, ?_, (hk1.trans hk).mono (by decide)⟩
  · rw [hr1, hs1] at hb
    exact hb
  · intro x hx ho
    exact (hf x ho).trans (hf1 x (Or.inr (by
      have hu : 128 ≤ usedBytes := by decide
      omega_using [hx, hu])))

/-- Validation of the packed key makes the signer's key checks true, so its
acceptance is the prevalidated program's. -/
theorem signAccepted_prevalidated (L : ExecutionLayout) (data : SignValues) {yb key : List Byte}
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hyl : yb.length = L.pLen)
    (hkl : key.length = 3 * L.pLen + 2 * L.qLen)
    (hk : Spec.Dsa.privateKeyBytes L.pLen L.qLen key = data.key L yb)
    (hv : Spec.Dsa.validatePrivateKeyBytes L.pLen L.qLen key = true) :
    signAccepted L data yb true = prevalidatedSignAccepted L data true := by
  have hv' : (decide (Spec.Dsa.parametersValid (data.key L yb).params) &&
      Spec.Dsa.keyValid (data.key L yb)) = true := by
    simpa only [Spec.Dsa.validatePrivateKeyBytes, L.lengths, decide_true, Bool.not_true,
      hkl, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk] using hv
  have hpa : privateAccepted L data yb true =
      decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup) := by
    rw [privateAccepted_spec L data yb hsize hop hoq hpf hyl]
    exact (congrArg (· && _) hv').trans (Bool.true_and _)
  simp only [signAccepted, prevalidatedSignAccepted, hpa, Bool.and_true]

theorem prevalidatedSignBody_spec (M : Mont) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (data : SignValues) {yb qb key digest : List Byte} {n : Nat}
    (h : SigningOperands L data yb qb s0)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hkl : key.length = 3 * L.pLen + 2 * L.qLen)
    (hk : Spec.Dsa.privateKeyBytes L.pLen L.qLen key = data.key L yb)
    (hqn : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n)
    (hv : Spec.Dsa.validatePrivateKeyBytes L.pLen L.qLen key = true)
    (hm : word s0.mem L.base Field.mask.offset = mask true)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (prevalidatedSignBody M.mm) s0 fun t =>
      let result := Spec.Dsa.signBytes L.pLen L.qLen key data.nonce digest
      t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) = result.getD (List.replicate (2 * L.qLen) 0) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have he := signBytes_compute L data yb key digest n hsize hop hoq hpf hqf h.publicLength hkl h.nonceLength hk hqn hz
  rw [signAccepted_prevalidated L data hsize hop hoq hpf h.publicLength hkl hk hv] at he
  refine WP.mono (prevalidatedSignBody_ok M h0 hp hq hop hoq hpf hqf data h hm hw hsep) fun t ht => ?_
  rw [he]
  cases hc : prevalidatedSignAccepted L data true <;> simpa only [hc, Bool.toNat_false, Bool.toNat_true,
    Bool.false_eq_true, ↓reduceIte, Spec.Dsa.signStatus, Option.isSome_none, Option.isSome_some,
    Option.getD_none, Option.getD_some] using ht

theorem prevalidatedSignAccepted_ok (M : Mont) {p : SigningInput} {original s : State}
    (h : SigningPre p original)
    (hi : SigningInitialized p original h.pLength s) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (prevalidatedSignBody M.mm) s (SigningPost p original) := by
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
  refine WP.mono (prevalidatedSignBody_spec M hr p.values ho hsize hpodd hqodd hpf hqf p.keyLength hkey
    hqn rfl hv hm (fun i hi => by rw [hk.wr]; exact h.writable i hi) h.separate)
    fun t ⟨hret, hout, hframe, hkeep⟩ => ?_
  exact ⟨hret, hout,
    fun x hx ho => (hframe x hx ho).trans (hf x hx), (hk.trans hkeep).mono (by decide)⟩

theorem prevalidatedSignSuccess_ok (M : Mont) {p : SigningInput} {original st : State}
    (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength st) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (seqs [SignVerify.workspaces, PrevalidatedSign.compute M.mm,
      SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result]) st
      (SigningPost p original) := by
  refine WP.seq (WP.mono (signingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := prevalidatedSignAccepted_ok M h ht ha hv
  unfold prevalidatedSignBody signRelease at hb
  exact hb

theorem prevalidatedSignMain_ok (M : Mont) {p : SigningInput} {s0 : State} (h : SigningPre p s0)
    (hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (PrevalidatedSign.sign M.mm) s0 (SigningPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (signingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => signingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    simp only [hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h)
      (fun _ => prevalidatedSignSuccess_ok M h hs ha hv)
    change some (s.gpr .x3 == (0#64)) = some false
    simp only [hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.SigningCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SigningReadyCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SigningPublic`, which this module and modules that import it used -/

section

/-! # Public observations used to relate two complete signing calls

The reference call supplies public lengths, addresses and domain bytes. The
relation does not equate private scalars, nonces, digests or scratch contents.
-/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure SigningCall where
  input : SigningInput
  original : State
  pre : SigningPre input original

abbrev SigningCall.layout (c : SigningCall) : ExecutionLayout := c.input.layout c.original c.pre.pLength

structure SigningAgrees (reference c : SigningCall) : Prop where
  layout : c.layout = reference.layout
  pBytes : c.input.components.p = reference.input.components.p
  qBytes : c.input.components.q = reference.input.components.q
  digestLength : c.input.digest.length = reference.input.digest.length
  stack : c.original.sp = reference.original.sp

def SigningStart (reference : SigningCall) (s : State) : Prop :=
  ∃ c : SigningCall, SigningAgrees reference c ∧ c.original = s

def SigningEntered (reference : SigningCall) (s : State) : Prop :=
  ∃ c : SigningCall, SigningAgrees reference c ∧
    SignEntryPost c.original c.input.base (BitVec.ofNat 64 c.input.qLen) c.input.digestPointer
      (BitVec.ofNat 64 c.input.digest.length) s

def SigningShaped (reference : SigningCall) (s : State) : Prop :=
  ∃ c : SigningCall, SigningAgrees reference c ∧ SigningShapePost c.input c.original c.pre.pLength s

def SigningReady (reference : SigningCall) (s : State) : Prop :=
  ∃ c : SigningCall, SigningAgrees reference c ∧ SigningInitialized c.input c.original c.pre.pLength s

def SigningCall.shape (c : SigningCall) : ShapePublic where
  base := c.layout.base
  extent := usedBytes
  pPointer := c.layout.fields .p
  qPointer := c.layout.fields .q
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  digestLen := c.input.digest.length
  extentBound := by decide
  pPositive := by rw [c.input.components.pLength]; have := c.layout.widths; change 0 < c.layout.pLen; omega_using [this]
  qPositive := by rw [c.input.components.qLength]; exact c.layout.widths.1
  pBound := by rw [c.input.components.pLength]; have := c.layout.widths; change c.layout.pLen < 2 ^ 64; omega_using [this]
  qBound := by rw [c.input.components.qLength]; have := c.layout.widths; change c.layout.qLen < 2 ^ 64; omega_using [this]
  digestBound := c.input.digestBound

theorem SigningAgrees.shape {reference c : SigningCall} (h : SigningAgrees reference c) :
    c.shape = reference.shape := by
  unfold SigningCall.shape
  congr 1
  · exact congrArg ExecutionLayout.base h.layout
  · exact congrArg (fun L => L.fields .p) h.layout
  · exact congrArg (fun L => L.fields .q) h.layout
  · exact h.pBytes
  · exact h.qBytes
  · exact h.digestLength

theorem SigningAgrees.accepted {reference c : SigningCall} (h : SigningAgrees reference c) :
    c.input.accepted = reference.input.accepted := by
  unfold SigningInput.accepted
  congr 1
  · exact h.pBytes
  · exact h.qBytes

theorem SigningEntered.context {reference : SigningCall} {s : State} (h : SigningEntered reference s) :
    ShapeContext reference.shape s := by
  obtain ⟨c, ha, he⟩ := h
  rw [← ha.shape]
  have hf : InScr c.input.base usedBytes c.original.mem s.mem := InScr.of_outside he.frame (by decide)
  have hkey := c.pre.keySource.congrK hf he.keep
  refine ⟨c.pre.scratch.congr he.keep.wr, he.base, he.p, he.q, ?_, ?_, he.digestLen,
    source_take hkey, ?_⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact he.pLen.trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact he.qLen
  · change Src s c.input.base usedBytes (c.original.gpr .x2 + c.original.gpr .x4) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.SigningShapeCT`, which only this module used -/

section

/-! # Constant time of signing argument capture and domain validation -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signingEntered_ct : RelCT isa (Two SigningStart) (.block SignVerify.signEntry) (Two SigningEntered) := by
  refine two_post (two_map (fun c : SigningCall => (c.layout.base, c.original.sp)) ?_ signEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    have hb : c.input.base = reference.layout.base := congrArg ExecutionLayout.base ha.layout
    refine ⟨ha.stack, ?_, ?_⟩
    · rw [← ha.stack, ← hb]
      exact c.pre.base
    · rw [← ha.stack]
      exact c.pre.stackRead 1 (by decide)
  · intro reference s ⟨c, ha, hs⟩
    subst s
    exact WP.mono (signEntry_ok c.pre.scratch rfl (by decide) c.pre.stackRead c.pre.stackSeparate
      c.pre.qLength c.pre.digestPointer c.pre.digestLength c.pre.base) fun t ht => ⟨c, ha, ht⟩

theorem signingShape_ct : RelCT isa (Two SigningStart)
    (.seq (.block SignVerify.signEntry) Checks.domainShape) (Two SigningShaped) := by
  refine two_post (RelCT.seq signingEntered_ct
    (two_map SigningCall.shape (fun _ _ h => h.context) domainShape_ct)) ?_
  intro reference s ⟨c, ha, hs⟩
  subst s
  exact WP.mono (signingShape_ok c.pre) fun t ht => ⟨c, ha, ht⟩

def SigningCall.initialization (c : SigningCall) (ha : c.input.accepted = true) : InitializationPublic where
  layout := c.layout
  pBytes := c.input.components.p
  qBytes := c.input.components.q
  pLength := c.input.components.pLength
  qLength := c.input.components.qLength
  pValue := rfl
  qValue := rfl
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2

theorem SigningShaped.initialization {reference : SigningCall} {s : State}
    (h : SigningShaped reference s) (ha : reference.input.accepted = true) :
    InitializationPre (reference.initialization ha) s := by
  obtain ⟨c, hag, hs⟩ := h
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hkey := c.pre.keySource.congrK hs.frame hs.keep
  have hps : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .x2 + c.original.gpr .x4) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])
  rw [hag.layout] at hf hr hscr hps hqs
  rw [hag.pBytes] at hps
  rw [hag.qBytes] at hqs
  exact ⟨hscr, hr, hf, hps, hqs⟩

abbrev AcceptedSigningCall := {c : SigningCall // c.input.accepted = true}

theorem signingWorkspaces_ct : RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
    SignVerify.workspaces (Two (fun c : AcceptedSigningCall => SigningReady c.val)) := by
  refine two_post ((two_map (fun c : AcceptedSigningCall => c.val.initialization c.property)
    (fun c _ h => h.initialization c.property) initialization_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
  intro reference s ⟨c, ha, hs⟩
  have hac : c.input.accepted = true := ha.accepted.trans reference.property
  exact WP.mono (signingInitialize_ok c.pre hs hac) fun t ht => ⟨c, ha, ht⟩

end VG.Proof.Dsa.AArch64

end

end


/-! # The public schedule after independent signing-workspace initialization -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def SigningCall.schedule (c : SigningCall) (ha : c.input.accepted = true) (pi qi : BitVec 64) : SchedulePublic where
  layout := c.layout.withInverses pi qi
  digestLen := c.input.prefixLength
  pGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).1
  qGreater := (VG.Proof.Dsa.supported_bounds (c.input.shapeFacts ha).1).2.1
  pOdd := (c.input.shapeFacts ha).2.1
  qOdd := (c.input.shapeFacts ha).2.2
  pFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.p
    rw [c.input.components.pLength] at h
    exact Nat.le_of_lt h
  qFits := by
    have h := VG.Proof.Dsa.decodeBE_lt c.input.components.q
    rw [c.input.components.qLength] at h
    exact Nat.le_of_lt h
  digestBound := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) c.input.digestBound

theorem SigningAgrees.prefixLength {reference c : SigningCall} (h : SigningAgrees reference c) :
    c.input.prefixLength = reference.input.prefixLength := by
  unfold SigningInput.prefixLength
  rw [h.digestLength, h.qBytes]

theorem SigningReady.body {reference : SigningCall} {s : State} (ha : reference.input.accepted = true)
    (h : SigningReady reference s) : ∃ pi qi, SigningBodyPre (reference.schedule ha pi qi) s := by
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, hk⟩ := h
  have hw : ∀ i < 2 * c.layout.qLen, InRegions s.wr (c.layout.fields .out + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hk.wr]
    exact c.pre.writable i hi
  have hsep : ∀ i < 2 * c.layout.qLen,
      usedBytes ≤ ofs c.layout.base (c.layout.fields .out + BitVec.ofNat 64 i) := c.pre.separate
  have hmask : word s.mem c.layout.base Field.mask.offset = mask true := hm
  change Ready (c.layout.withInverses pi qi) s at hr
  change SigningOperands (c.layout.withInverses pi qi) c.input.values c.input.components.y c.input.components.q s at ho
  rw [hag.layout] at hr ho hw hsep hmask
  refine ⟨pi, qi, hr, ⟨c.input.values, c.input.components.y, c.input.components.q, ho, ?_⟩,
    ⟨true, hmask⟩, hw, hsep⟩
  change (c.input.digest.take _).length = reference.input.prefixLength
  rw [List.length_take, Nat.min_comm]
  exact hag.prefixLength

theorem signingReady_related {s₁ s₂ : State}
    (h : Two (fun c : AcceptedSigningCall => SigningReady c.val) s₁ s₂) : Two SigningBodyPre s₁ s₂ := by
  obtain ⟨reference, h₁, h₂, hsp⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1 h₂.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂, hsp⟩

theorem signingSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey M.mm, Checks.privateKey M.mm,
        Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
        SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq signingWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.signingKey M.mm, Checks.privateKey M.mm,
    Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact (signBody_ct M).mono (fun _ _ h => signingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of the complete signing entry point -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem SigningShaped.branch {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    eval (.zero .x .x3) s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change some (s.gpr .x3 == (0#64)) = _
  rw [hs.branch, ha.accepted]

def SigningCall.failure (c : SigningCall) : FailurePublic := ⟨c.layout.base, c.layout.fields .out, c.layout.qLen⟩

theorem SigningShaped.failure {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    FailurePre reference.failure s := by
  obtain ⟨c, ha, hs⟩ := h
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hr : s.gpr .x0 = c.layout.base := hs.x0
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  rw [ha.layout] at hscr hr hf
  exact ⟨usedBytes, hscr, by decide, hr, hf .out, (hf .qLen).trans reference.layout.qLength⟩

theorem signingMain_ct (M : Mont) : RelCT isa (Two SigningStart) (SignVerify.sign M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq signingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map SigningCall.failure (fun _ _ h => h.failure) signFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (signingSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Constant time of an AArch64 DSA signing attempt for a validated private key -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem prevalidatedSignCompute_ct (M : Mont) : RelCT isa (Two (ScheduleState signComputeInputs))
    (PrevalidatedSign.compute M.mm) (Two (ScheduleState signComputeInputs)) := by
  have h1 := scheduleMinus_ct signComputeInputs signComputeInputs_stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega_using [this])
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  have h2 := scheduleRange_ct signComputeInputs signComputeInputs_stable .q Core.nonce
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.nonce])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h3 := coreSignSchedule_ct M signComputeInputs signComputeInputs_stable
    (by intro p a ha; simp [signComputeInputs, ha])
  have h4 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar r)
    (fun p => p.layout.qLen) true (by change r < 2 ^ 16; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this]) (by taint_decide)
  have h5 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar s)
    (fun p => p.layout.qLen) true (by change s < 2 ^ 16; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this]) (by taint_decide)
  unfold PrevalidatedSign.compute seqs
  refine RelCT.seq h1 (RelCT.seq (R := Two (ScheduleState signComputeInputs)) ?_
    (RelCT.seq h3 (RelCT.seq (R := Two (ScheduleState signComputeInputs)) ?_ ?_)))
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, (h.2.1 (Core.nonce, p.layout.qLen) (by simp [signComputeInputs, signInputs])).active⟩) h2
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q r (by decide) (scalar_space (by decide) p)⟩) h4
  · exact two_map (fun p => p) (fun p st h =>
      ⟨h, h.1.availableLocal .q s (by decide) (scalar_space (by decide) p)⟩) h5

theorem prevalidatedSignComputeRelease_ok (M : Mont) {p : SchedulePublic} {s : State}
    (h : SigningBodyPre p s) :
    WP isa (PrevalidatedSign.compute M.mm) s (ReleasePre p.release) := by
  obtain ⟨hr, ⟨data, yb, qb, ho, _⟩, ⟨valid, hm⟩, hw, hsep⟩ := h
  refine WP.mono (prevalidatedSignCompute_ok M hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits
    data ho.generator ho.privateScalar ho.nonce ho.digest ho.generatorLength ho.privateLength
    ho.nonceLength ho.digestBound hm) fun t ⟨ht, hm, _, _, _, hk⟩ => ?_
  exact ⟨ht.scratch, ht.parent.x0, ht.fields .out (by decide),
    (ht.fields .qLen (by decide)).trans p.layout.qLength, ⟨_, hm⟩,
    fun i hi => by rw [hk.wr]; exact hw i hi, hsep⟩

theorem prevalidatedSignBody_ct (M : Mont) :
    RelCT isa (Two SigningBodyPre) (prevalidatedSignBody M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => ReleasePre p.release)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule.1) (prevalidatedSignCompute_ct M)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => prevalidatedSignComputeRelease_ok M h
  · exact two_map SchedulePublic.release (fun _ _ h => h) signRelease_ct

theorem prevalidatedSignSuccess_ct (M : Mont) :
    RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
      (seqs [SignVerify.workspaces, PrevalidatedSign.compute M.mm,
        SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq signingWorkspaces_ct ?_
  exact (prevalidatedSignBody_ct M).mono (fun _ _ h => signingReady_related h) (fun _ _ h => h)

theorem prevalidatedSignMain_ct (M : Mont) :
    RelCT isa (Two SigningStart) (PrevalidatedSign.sign M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq signingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂, hsp⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map SigningCall.failure (fun _ _ h => h.failure) signFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (prevalidatedSignSuccess_ct M).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂, hsp⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval (.zero .x .x3) s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂, hsp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.SigningABIPre`, which this module and modules that import it used -/

section

/-! # The shared signing precondition supplies every machine-level resource -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem SigningABI.pre {s : State} (h : SigningABI s) : SigningPre h.input s := by
  have hs : Scr s (stackArg s 1) ((stackArg s 2).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 24⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · intro j hj
    exact stackWord_read (count := 3) hargs (by omega_using [hj]) (by decide)
  · intro i hi
    simpa only [Nat.mul_zero, off_zero, SigningABI.input] using Nat.le_trans h.used (stackWord_separate (count := 3) (j := 0) h.scratchArgs (by decide) (by decide) i hi)
  · exact (ofNat_toNat64 _).symm
  · change stackArg s 0 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (s.gpr .x7) (stackArg s 0).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x3).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .x6).isLt) h.nonceScratch) h.used
  · exact source_shrink (src_of_region (p := s.gpr .x7) (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt) h.digestScratch) h.used
  · intro i hi
    exact ⟨_, by rw [h.wr]; simp, contains_byte _ (by change i < 2 * (s.gpr .x6).toNat at hi; rw [h.outLength]; exact hi)
      (Nat.le_of_lt (s.gpr .x1).isLt)⟩
  · intro i hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _
      (by change i < 2 * (s.gpr .x6).toNat at hi; rw [h.outLength]; exact hi) (Nat.le_of_lt (s.gpr .x1).isLt)))

def SigningABI.call {s : State} (h : SigningABI s) : SigningCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.SigningVerified`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SigningAgreement`, which this module and modules that import it used -/

section

/-! # Only the signing ABI's declared public observations determine its schedule -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signingLayout_eq {p₁ p₂ : SigningInput} {s₁ s₂ : State}
    {hp₁ : s₁.gpr .x4 = BitVec.ofNat 64 p₁.pLen} {hp₂ : s₂.gpr .x4 = BitVec.ofNat 64 p₂.pLen}
    (hb : p₁.base = p₂.base) (hp : p₁.pLen = p₂.pLen) (hq : p₁.qLen = p₂.qLen)
    (hd : p₁.digestPointer = p₂.digestPointer) (hdl : p₁.digest.length = p₂.digest.length)
    (hpb : p₁.components.p = p₂.components.p) (hqb : p₁.components.q = p₂.components.q)
    (hdi : s₁.gpr .x0 = s₂.gpr .x0) (hdx : s₁.gpr .x2 = s₂.gpr .x2)
    (h8 : s₁.gpr .x4 = s₂.gpr .x4) (h9 : s₁.gpr .x5 = s₂.gpr .x5) :
    p₁.layout s₁ hp₁ = p₂.layout s₂ hp₂ := by
  have hac : p₁.accepted = p₂.accepted := by
    unfold SigningInput.accepted
    congr 1
  have hprefix : p₁.prefixLength = p₂.prefixLength := by
    unfold SigningInput.prefixLength
    rw [hdl, hqb]
  have hfields : signFieldValues s₁ (BitVec.ofNat 64 p₁.qLen) p₁.digestPointer
      (BitVec.ofNat 64 p₁.digest.length) (BitVec.ofNat 64 p₁.prefixLength) p₁.accepted =
      signFieldValues s₂ (BitVec.ofNat 64 p₂.qLen) p₂.digestPointer
      (BitVec.ofNat 64 p₂.digest.length) (BitVec.ofNat 64 p₂.prefixLength) p₂.accepted := by
    funext f
    cases f <;> simp only [signFieldValues, hq, hd, hdl, hprefix, hac, hdi, hdx, h8, h9]
  unfold SigningInput.layout
  congr 1
  · exact congrArg Spec.Dsa.decodeBE hpb
  · exact congrArg Spec.Dsa.decodeBE hqb

theorem signingAgreement {s₁ s₂ : State} (h₁ : SigningABI s₁) (h₂ : SigningABI s₂)
    (hdi : s₁.gpr .x0 = s₂.gpr .x0) (hdx : s₁.gpr .x2 = s₂.gpr .x2)
    (h8 : s₁.gpr .x4 = s₂.gpr .x4) (h9 : s₁.gpr .x5 = s₂.gpr .x5)
    (hsp : s₁.sp = s₂.sp)
    (a0 : s₁.gpr .x6 = s₂.gpr .x6) (a1 : s₁.gpr .x7 = s₂.gpr .x7)
    (a2 : stackArg s₁ 0 = stackArg s₂ 0) (a3 : stackArg s₁ 1 = stackArg s₂ 1)
    (hpub : h₁.input.key.take (3 * h₁.input.pLen + h₁.input.qLen) =
      h₂.input.key.take (3 * h₂.input.pLen + h₂.input.qLen)) : SigningAgrees h₂.call h₁.call := by
  have hp : h₁.input.pLen = h₂.input.pLen := congrArg BitVec.toNat h8
  have hq : h₁.input.qLen = h₂.input.qLen := congrArg BitVec.toNat a0
  have hdl : h₁.input.digest.length = h₂.input.digest.length := by
    change (Spec.Rsa.bytesAt _ _ _).length = (Spec.Rsa.bytesAt _ _ _).length
    rw [bytesAt_length, bytesAt_length, a2]
  rw [← hp, ← hq] at hpub
  have hpb : h₁.input.components.p = h₂.input.components.p := by
    have he := prefix_component_eq (offset := 0) (len := h₁.input.pLen) hpub (by omega_using [])
    simp only [List.drop_zero] at he
    change h₁.input.key.take h₁.input.pLen = h₂.input.key.take h₂.input.pLen
    rw [← hp]
    exact he
  have hqb : h₁.input.components.q = h₂.input.components.q := by
    have he := prefix_component_eq (offset := h₁.input.pLen) (len := h₁.input.qLen) hpub (by omega_using [])
    change (h₁.input.key.drop h₁.input.pLen).take h₁.input.qLen = (h₂.input.key.drop h₂.input.pLen).take h₂.input.qLen
    rw [← hp, ← hq]
    exact he
  exact ⟨signingLayout_eq a3 hp hq a1 hdl hpb hqb hdi hdx h8 h9, hpb, hqb, hdl, hsp⟩

theorem signingPublicRelated {s₁ s₂ : State} (h₁ : SigningABI s₁) (h₂ : SigningABI s₂)
    (h : (Spec.Dsa.signContract abi).pub s₁ s₂) : Two SigningStart s₁ s₂ := by
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, _, h8, h9, a0, a1, a2, a3, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  exact ⟨h₂.call, ⟨h₁.call, signingAgreement h₁ h₂ hdi hdx h8 h9 hsp a0 a1 a2 a3 hb, rfl⟩,
    ⟨h₂.call, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩, hsp⟩

theorem signingConstantTime (M : Mont) : ConstantTime isa (Spec.Dsa.signContract abi).pre
    (Spec.Dsa.signContract abi).pub (SignVerify.sign M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (signingMain_ct M _ _ _ _ _ _ (signingPublicRelated (signingABI_of h₁) (signingABI_of h₂) hp) e₁ e₂).1

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.SigningABIPost`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.SigningMain`, which only this module used -/

section

/-! # Functional correctness of the complete AArch64 DSA signing program -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signingSuccess_ok (M : Mont) {p : SigningInput} {original st : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey M.mm, Checks.privateKey M.mm,
      Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
      SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result]) st
      (SigningPost p original) := by
  refine WP.seq (WP.mono (signingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := signingAccepted_ok M h ht ha
  apply wpAppendSequences (a := [Checks.signingKey M.mm, Checks.privateKey M.mm,
    Core.sign M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem signingMain_ok (M : Mont) {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (SignVerify.sign M.mm) s0 (SigningPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (signingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => signingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    simp only [hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => signingSuccess_ok M h hs ha)
    change some (s.gpr .x3 == (0#64)) = some false
    simp only [hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.AArch64

end

end

/-! # Signing correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem signStatus_u32 (result : Option (List Byte)) :
    ((BitVec.ofNat 64 (Spec.Dsa.signStatus result)).setWidth 32).toNat = Spec.Dsa.signStatus result := by
  cases result <;> rfl

theorem signingSharedPost {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    (Spec.Dsa.signContract abi).post s t := by
  obtain ⟨hr, hout, _, _⟩ := hp
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
  rw [hr, signStatus_u32]
  refine ⟨rfl, ?_⟩
  rw [h.outLength]
  exact hout

theorem signingCorrect (M : Mont)
    (s : State) (h : (Spec.Dsa.signContract abi).pre s) :
    ∃ trace t, Exec isa (SignVerify.sign M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi).post s t := by
  have ha := signingABI_of h
  obtain ⟨trace, t, he, hp⟩ := signingMain_ok M ha.pre
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2.2, signingSharedPost ha hp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # DSA signing verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum.AArch64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def signingSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 40 | .x2 => 0x2000 | .x3 => 424
    | .x4 => 128 | .x5 => 0x4000 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10009 then 0x80 else if a = 0x10011 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩, ⟨0x10000, 24⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
    [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem signing_verified (M : Mont) :
    Verified target (SignVerify.sign M.mm) (Spec.Dsa.signContract abi) :=
  ⟨signingCorrect M, signingConstantTime M, signingSatisfiable⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # An AArch64 DSA signing attempt for a validated private key against its contract

`prevalidated_sign_verified` is the program's proof against
`signContractWith validatePrivateKeyBytes`. The randomized wrapper
(`vg_dsa_sign_random_prevalidated`) calls it. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64 VG.Proof.Bignum.AArch64

theorem prevalidatedSigningCorrect (M : Mont)
    (s : State) (h : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s) :
    ∃ trace t, Exec isa (PrevalidatedSign.sign M.mm) s trace t ∧ abiPreserved s t ∧
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).post s t := by
  obtain ⟨hs, hv⟩ := signWith_pre h
  have ha := signingABI_of hs
  obtain ⟨trace, t, he, hp⟩ := prevalidatedSignMain_ok M ha.pre hv
  exact ⟨trace, t, he, abiPreserved_of_keep hp.2.2.2, signWith_post (signingSharedPost ha hp)⟩

theorem prevalidatedSigningConstantTime (M : Mont) :
    ConstantTime isa (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pub (PrevalidatedSign.sign M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (prevalidatedSignMain_ct M _ _ _ _ _ _
    (signingPublicRelated (signingABI_of (signWith_pre h₁).1) (signingABI_of (signWith_pre h₂).1)
      (signWith_pub hp)) e₁ e₂).1

/-- `signingSatState` with `validPrivateKeyWitness` at `0x2000`. -/
def prevalidatedSignSatState : State where
  gpr := signingSatState.gpr
  sp := signingSatState.sp
  rd := signingSatState.rd
  wr := signingSatState.wr
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
    VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0 else signingSatState.mem a

theorem prevalidatedSignSatisfiable :
    ∃ s, (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s := by
  have hb : Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424 = VG.Proof.Dsa.validPrivateKeyWitness :=
    VG.Proof.Dsa.bytesAt_of_list (lo := 0x2000) (by decide +kernel) (by decide) fun a h1 h2 => by
      have h : 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 := ⟨h1, h2⟩
      simp only [prevalidatedSignSatState, h, and_self, ↓reduceIte]
  have ho : ∃ s, (Spec.Dsa.signContract abi).pre s ∧ s = prevalidatedSignSatState := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, dsaSignStackArgs]
      [prevalidatedSignSatState, signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSignSatState
  obtain ⟨s, h, rfl⟩ := ho
  refine ⟨_, signWith_of_pre h ?_⟩
  change Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424) = true
  rw [hb]
  exact VG.Proof.Dsa.validPrivateKeyWitness_valid

theorem prevalidated_sign_verified (M : Mont) :
    Verified target (PrevalidatedSign.sign M.mm) (signContractWith Spec.Dsa.validatePrivateKeyBytes abi) :=
  ⟨prevalidatedSigningCorrect M, prevalidatedSigningConstantTime M, prevalidatedSignSatisfiable⟩

end VG.Proof.Dsa.AArch64
