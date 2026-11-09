module

public import VerifiedGarbage.Impl.Dsa.X86_64.Prevalidated
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingReturn
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.CheckEffects
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.X86_64.CallOperands
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Functional correctness of x86-64 DSA verification for a validated public key

The program is the verifier's, with the domain and public-value checks
replaced by rebuilding q−2: the precondition that the exact key bytes
validate makes those checks' mask true. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def prevalidatedAccepted (L : ExecutionLayout) (data : VerifyValues) (valid : Bool) : Bool :=
  decide (Spec.Dsa.encodeBE L.qLen (data.value L) = data.signatureR) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureS ∧ Spec.Dsa.decodeBE data.signatureS < L.subgroup) &&
  (decide (0 < Spec.Dsa.decodeBE data.signatureR ∧ Spec.Dsa.decodeBE data.signatureR < L.subgroup) &&
    valid))

theorem prevalidatedCompute_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues)
    (hg : OperandBytes s0 L.base usedBytes Core.generator data.generator)
    (hy : OperandBytes s0 L.base usedBytes Core.publicValue data.publicValue)
    (hr : OperandBytes s0 L.base usedBytes Core.signatureR data.signatureR)
    (hs : OperandBytes s0 L.base usedBytes Core.signatureS data.signatureS)
    (hz : OperandBytes s0 L.base usedBytes Core.digest data.digest)
    (hgl : data.generator.length = L.pLen) (hyl : data.publicValue.length = L.pLen)
    (hrl : data.signatureR.length = L.qLen) (hsl : data.signatureS.length = L.qLen)
    (hzl : data.digest.length < 2 ^ 64)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (Prevalidated.compute Sq.mm M.mm) s0 fun s5 =>
      Ready L s5 ∧ word s5.mem L.base Field.mask.offset = mask (prevalidatedAccepted L data valid) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem s5.mem ∧ Keep coreRegs s0 s5 := by
  obtain ⟨hql, hqu, _, _⟩ := L.widths
  have hu : u + L.qLen ≤ usedBytes := by unfold u usedBytes; omega
  have hqm : qMinusTwo + L.qLen ≤ usedBytes := by unfold qMinusTwo usedBytes; omega
  unfold Prevalidated.compute
  refine WP.seq (WP.mono (readyMinus_ok h0 .q 2 (by decide)
    (by change 2 ≤ L.subgroup; omega) qMinusTwo (by decide) hqm) fun s1 h1 => ?_)
  have hg1 := h1.external (by decide) hqm hg
  have hy1 := h1.external (by decide) hqm hy
  have hr1 := h1.external (by decide) hqm hr
  have hs1 := h1.external (by decide) hqm hs
  have hz1 := h1.external (by decide) hqm hz
  have hm1 := (h1.fields (by decide) hqm .mask).trans hm
  have hqm1 := h1.output (by decide) hqm
  refine WP.seq (WP.mono (readyRange_ok h1.ready .q Core.signatureR (by trivial) hr1.active
    (by rw [hrl]; omega) (by simp only [hrl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm1) fun s2 h2 => ?_)
  have hg2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg1
  have hy2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy1
  have hr2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr1
  have hs2 := h2.preserve h1.ready (by decide) (by decide) (by trivial) hs1
  have hz2 := h2.preserve h1.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz1
  have hqm2 := h2.preserve h1.ready (Nat.le_refl _) (by decide) (by trivial) hqm1
  refine WP.seq (WP.mono (readyRange_ok h2.ready .q Core.signatureS (by trivial) hs2.active
    (by rw [hsl]; omega) (by simp only [hsl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false h2.mask) fun s3 h3 => ?_)
  have hg3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.generator]) hg2
  have hy3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.publicValue]) hy2
  have hr3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.signatureR]) hr2
  have hs3 := h3.preserve h2.ready (by decide) (by decide) (by trivial) hs2
  have hz3 := h3.preserve h2.ready (by decide) (by decide) (by simp [stablePointer, Core.digest]) hz2
  have hqm3 := h3.preserve h2.ready (Nat.le_refl _) (by decide) (by trivial) hqm2
  refine WP.seq (WP.mono (coreVerify_ok M Sq h3.ready hp hq hop hoq hpf hqf data hg3 hy3 hr3 hs3 hz3
    hgl hyl hrl hsl hzl hqm3) fun s4 ⟨h4, hu4bytes, hf4, hm4eq, hk4⟩ => ?_)
  have hr4 := h3.ready.preserveExternal h4 hf4 hk4 (by decide) (by simp [stablePointer, Core.signatureR]) hr3
  have hm4 := hm4eq.trans h3.mask
  have hu4 := h4.encodedLocal .q u (data.value L) (by decide) hu hu4bytes
  refine WP.mono (readyEqual_ok h4 (Core.scalar u) Core.signatureR
    (by change u < 2 ^ 31; decide) (by trivial) hu4 hr4.active
    (by simp only [encodeBE_length, ModulusSide.length, hrl])
    (by simp only [encodeBE_length, ModulusSide.length]; omega)
    (by simp only [encodeBE_length, ModulusSide.length]; omega) false hm4) fun s5 h5 => ?_
  refine ⟨h5.ready, ?_, ((((h1.scheduleFrame (by decide) hqm).trans h2.scheduleFrame).trans
      h3.scheduleFrame).trans hf4).trans h5.scheduleFrame,
    ((((h1.keep.trans h2.keep).trans h3.keep).trans hk4).trans h5.keep).mono (by decide)⟩
  have hm5 := h5.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.length, ModulusSide.value] at hm5
  exact hm5

def prevalidatedBody (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (Prevalidated.compute sq mul) (.block SignVerify.result)

theorem prevalidatedBody_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : VerifyValues) {qb : List Byte} (h : VerificationOperands L data qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid) :
    WP isa (prevalidatedBody Sq.mm M.mm) s0 fun t =>
      t.gpr .rax = BitVec.ofNat 64 (prevalidatedAccepted L data valid).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  unfold prevalidatedBody
  refine WP.seq (WP.mono (prevalidatedCompute_ok M Sq h0 hp hq hop hoq hpf hqf data h.generator
    h.publicValue h.signatureR h.signatureS h.digest h.generatorLength h.publicLength
    h.rLength h.sLength h.digestBound hm)
    fun s1 ⟨h1, hm1, hf1, hk1⟩ => ?_)
  refine WP.mono (result_ok h1.scratch h1.parent.rdi (by decide) hm1)
    fun t ⟨ha, hsave, hmem, hk⟩ => ?_
  exact ⟨ha, fun i hi => (hsave i hi).trans (hf1.word (Or.inl (by omega)) (by omega)),
    by rw [hmem]; exact hf1, (hk1.trans hk).mono (by decide)⟩

theorem prevalidatedBody_spec (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (data : VerifyValues) {qb key signature digest : List Byte} {n : Nat}
    (h : VerificationOperands L data qb s0)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hkl : key.length = 3 * L.pLen + L.qLen) (hsl : signature.length = 2 * L.qLen)
    (hk : Spec.Dsa.publicKeyBytes L.pLen L.qLen key = data.key L)
    (hr : signature.take L.qLen = data.signatureR) (hs : signature.drop L.qLen = data.signatureS)
    (hqn : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n)
    (hv : Spec.Dsa.validatePublicKeyBytes L.pLen L.qLen key = true)
    (hm : word s0.mem L.base Field.mask.offset = mask true) :
    WP isa (prevalidatedBody Sq.mm M.mm) s0 fun t =>
      t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.verifyBytes L.pLen L.qLen key signature digest).toNat ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      Outside L.base 128 (usedBytes - 128) s0.mem t.mem ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hv' : publicAccepted L data.generator data.publicValue true = true := by
    rw [publicAccepted_spec L data.generator data.publicValue hsize hop hoq]
    simpa only [Spec.Dsa.validatePublicKeyBytes, L.lengths, decide_true, Bool.not_true,
      hkl, bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk,
      VerifyValues.key] using hv
  have he : verifyAccepted L data true = prevalidatedAccepted L data true := by
    simp only [verifyAccepted, prevalidatedAccepted, hv']
  rw [verifyBytes_compute L data key signature digest n hsize hop hoq hqf h.rLength hkl hsl hk hr hs hqn hz, he]
  exact prevalidatedBody_ok M Sq h0 hp hq hop hoq hpf hqf data h hm

theorem prevalidatedAccepted_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {original s : State}
    (h : VerifyingPre p original)
    (hi : VerifyingInitialized p original h.pLength h.qLength s) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (prevalidatedBody Sq.mm M.mm) s (VerifyingPost p original) := by
  obtain ⟨pi, qi, hr, ho, hm, hsave, hf, hk⟩ := hi
  let L := (p.layout original h.pLength h.qLength).withInverses pi qi
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
  have hkey : Spec.Dsa.publicKeyBytes L.pLen L.qLen p.key = p.values.key L := rfl
  refine WP.mono (prevalidatedBody_spec M Sq (L := L) hr p.values ho hsize hpodd hqodd hpf hqf
    p.keyLength p.signatureLength hkey rfl rfl hqn rfl hv hm)
    fun t ⟨hret, hsaved, hframe, hkeep⟩ => ?_
  exact ⟨hret, fun i hi => (hsaved i hi).trans (hsave i hi),
    hf.trans (InScr.of_outside hframe (by decide)), (hk.trans hkeep).mono (by decide)⟩

theorem prevalidatedMain_ok (M : Mont) (Sq : MontS) {p : VerifyingInput} {s0 : State} (h : VerifyingPre p s0)
    (hv : Spec.Dsa.validatePublicKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (Prevalidated.verify Sq.mm M.mm) s0 (VerifyingPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (verifyingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => verifyingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => ?_)
    · change eval .e s = some false
      simp only [eval, hs.branch, ha, Bool.not_true]
    · refine WP.seq (WP.mono (verifyingInitialize_ok h hs ha) fun t ht => ?_)
      exact prevalidatedAccepted_ok M Sq h ht ha hv

end VG.Proof.Dsa.X86_64
