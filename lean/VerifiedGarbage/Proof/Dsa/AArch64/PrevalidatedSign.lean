module

public import VerifiedGarbage.Impl.Dsa.AArch64.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.AArch64.SigningReturn
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.AArch64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.AArch64.CheckEffects
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleState
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  have hr : r + L.qLen ≤ usedBytes := by unfold r usedBytes; omega
  have hs : s + L.qLen ≤ usedBytes := by unfold s usedBytes; omega
  unfold PrevalidatedSign.compute
  refine WP.seq (WP.mono (readyMinus_ok h0 .q 2 (by decide)
    (by change 2 ≤ L.subgroup; omega) qMinusTwo (by decide) hqm) fun s1 h1 => ?_)
  have hg1 := h1.external (by decide) hqm hg
  have hx1 := h1.external (by decide) hqm hx
  have hn1 := h1.external (by decide) hqm hn
  have hz1 := h1.external (by decide) hqm hz
  have hm1 := (h1.fields (by decide) hqm .mask).trans hm
  have hqm1 := h1.output (by decide) hqm
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.nonce (by trivial) hn1.active
    (by rw [hnl]; omega) (by simp only [hnl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
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
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) true hm3) fun s4 h4 => ?_)
  have hr4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hr3
  have hs4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hs3
  refine WP.mono (readyZero_ok h4.ready (Core.scalar s) (by change s < 2 ^ 16; decide) hs4
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) true h4.mask) fun s5 h5 => ?_
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
      omega)))

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
