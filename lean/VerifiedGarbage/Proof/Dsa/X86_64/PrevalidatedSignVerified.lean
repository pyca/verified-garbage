module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCall
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
import VerifiedGarbage.Proof.Dsa.X86_64.PrevalidatedVerified
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.PublicSlices
import VerifiedGarbage.Proof.Dsa.X86_64.ABIRegions
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
public import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Dsa.X86_64.BodyCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Dsa.SizeBounds
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInitialize
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.X86_64.SigningInitialize
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
meta import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
meta import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
meta import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
meta import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import Mathlib.Tactic.Finiteness.Attr
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.X86_64.PrevalidatedSignCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.PrevalidatedSign`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SigningReturn`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Failure`, which only this module used -/

section

/-! # Zeroing the signature and restoring registers on public domain rejection -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.WriteBytes (writeW8_apply)

theorem signFailure_ok {s : State} {B : Addr} {Z k q : Nat} {op : Addr} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hZ : pWorkspace ≤ Z) (hkq : k = 2 * q) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B Field.out.offset = op) (hK : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1)
    (hsep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)) :
    WP isa SignVerify.signFailure s fun t =>
      (List.range k).map (fun i => t.mem (op + BitVec.ofNat 64 i)) = Spec.Rsa.i2osp 0 k ∧
      t.gpr .rax = 0 ∧ (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
      (∀ x, (∀ j < k, x ≠ op + BitVec.ofNat 64 j) → t.mem x = s.mem x) ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have h256 : 256 ≤ Z := Nat.le_trans (by decide) hZ
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega_using [h256, hi])
  unfold SignVerify.signFailure seqs
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rax] (Q := fun t => t.gpr .rsi = op ∧
      t.gpr .rcx = BitVec.ofNat 64 k ∧ t.gpr .rax = 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, Core.field, hdi, fieldAddress,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ), hO, hK]
    rw [BitVec.ofNat_add_ofNat, hkq, Nat.two_mul]) rfl) fun s₁ ⟨⟨hsi, hcx, hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := k) (by omega_using [hk1]) (FailInv s₁ op k) ?_ (fun t h => h)
    ⟨Keep.refl _ _, by rw [hsi, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero], by rw [hcx, Nat.sub_zero],
      fun i hi => absurd hi (by omega_using []), fun x _ => rfl⟩) fun t₂ hI => ?_)
  · intro j _ hj t hI
    have hst : InRegions t.wr (op + BitVec.ofNat 64 j) 1 := by
      rw [hI.keep.2.2, k₁.2.2]; exact hout j hj
    have hax' : (t.gpr .rax).setWidth 8 = 0 := by rw [hI.keep.gpr (by decide), hax]; rfl
    refine WP.mono (WP.keep [.rsi, .rcx] (Q := fun t' =>
        t'.mem = t.mem.writeW (op + BitVec.ofNat 64 j) (0 : BitVec 8) ∧
        t'.gpr .rsi = op + BitVec.ofNat 64 (j + 1) ∧ t'.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧
        t'.zf = some (decide (j + 1 = k))) (by
      xrun [State.ea, at0, hI.rsi, hI.rcx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hst, hax',
        ofNat64_pred (show 1 ≤ k - j by omega_using [hj]) (by omega_using [hk']), BitVec.add_assoc, ofNat_add_one,
        ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega_using [hk'])]
      exact ⟨by rw [show k - j - 1 = k - (j + 1) by omega_using []], decide_eq_decide.mpr (by omega_using [hj])⟩) rfl)
      fun t' ⟨⟨hm, hsi', hcx', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hsi', hcx', ?_, ?_⟩
    · intro i hi
      rw [hm, writeW8_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_using [hk', hj, hi]) (by omega_using [hk', hj]) hij))]
        exact hI.bytes i (by omega_using [hi, hij])
    · intro x hx
      rw [hm, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_using [])))]
      exact hI.frame x fun i hi => hx i (by omega_using [hi])
  -- The saved registers.
  have hw₂ : ∀ i < 32, word t₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    apply Mem.readW_congr
    intro b hb
    rw [hI.frame _ (fun j hj => scr_ne_out hsep (d := 8 * i) (i := b) (by omega_using [h256, hi, hb]) (by omega_using [hn]) j (by omega_using [hj])), hm₁]
  have k12 := k₁.trans hI.keep
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k12.2.1, k12.2.2]; exact hl i hi
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hdi
  rw [exit_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ 0 (by decide), hl₂ 1 (by decide), hl₂ 2 (by decide),
      hl₂ 3 (by decide), hl₂ 4 (by decide), hl₂ 5 (by decide), hw₂ 0 (by decide), hw₂ 1 (by decide),
      hw₂ 2 (by decide), hw₂ 3 (by decide), hw₂ 4 (by decide), hw₂ 5 (by decide)]) rfl)
    fun t ⟨⟨h0, h1, h2, h3, h4, h5, hm⟩, k₃⟩ => ⟨?_, ?_, ?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [i2osp_zero]
    exact List.map_congr_left fun i hi => by rw [hm]; exact hI.bytes i (List.mem_range.mp hi)
  · rw [k₃.gpr (by decide), hI.keep.gpr (by decide), hax]
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro x hx
    rw [hm, hI.frame x hx, hm₁]


end VG.Proof.Dsa.X86_64

end

end


/-! # Both signing branches return the packed byte specification -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def SigningPost (p : SigningInput) (original t : State) : Prop :=
  let result := Spec.Dsa.signBytes p.pLen p.qLen p.key p.nonce p.digest
  t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
  Spec.Rsa.bytesAt t.mem (original.gpr .rdi) (2 * p.qLen) = result.getD (List.replicate (2 * p.qLen) 0) ∧
  (∀ i < 6, t.gpr (saved.getD i .rax) = original.gpr (saved.getD i .rax)) ∧
  (∀ x, usedBytes ≤ ofs p.base x → (∀ i < 2 * p.qLen, x ≠ original.gpr .rdi + BitVec.ofNat 64 i) →
    t.mem x = original.mem x) ∧ Keep coreRegs original t

theorem signingAccepted_ok (M : Mont) (Sq : MontS) {p : SigningInput} {original s : State} (h : SigningPre p original)
    (hi : SigningInitialized p original h.pLength s) (ha : p.accepted = true) :
    WP isa (signBody Sq.mm M.mm) s (SigningPost p original) := by
  obtain ⟨pi, qi, hr, ho, hm, hsave, hf, hk⟩ := hi
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
  refine WP.mono (signBody_spec M Sq hr p.values ho hsize hpodd hqodd hpf hqf p.keyLength hkey hqn rfl hm
    (fun i hi => by rw [hk.2.2]; exact h.writable i hi) h.separate)
    fun t ⟨hret, hout, hsaved, hframe, hkeep⟩ => ?_
  exact ⟨hret, hout, fun i hi => (hsaved i hi).trans (hsave i hi),
    fun x hx ho => (hframe x hx ho).trans (hf x hx), (hk.trans hkeep).mono (by decide)⟩

theorem signingRejected_ok {p : SigningInput} {original s : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength s) (ha : p.accepted = false) :
    WP isa SignVerify.signFailure s (SigningPost p original) := by
  have hparams : ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes p.pLen p.qLen p.key).params :=
    shapeAccepted_false ha (Spec.Dsa.decodeBE p.components.g)
  have hnone := signBytes_invalid_shape (nonce := p.nonce) (digest := p.digest) hparams
  have hwidth : 1 ≤ p.qLen ∧ p.qLen ≤ 32 := by
    have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this]
  refine WP.mono (signFailure_ok hs.scratch hs.rdi (by decide) rfl (by omega_using [hwidth]) (by omega_using [hwidth])
    (hs.fields .out) (hs.fields .qLen)
    (fun i hi => by rw [hs.keep.2.2]; exact h.writable i hi) h.separate)
    fun t ⟨hout, hret, hsave, hframe, hk⟩ => ?_
  unfold SigningPost
  rw [hnone]
  refine ⟨?_, ?_, fun i hi => (hsave i hi).trans (hs.saved i hi),
    fun x hx ho => (hframe x ho).trans (hs.frame x hx), (hs.keep.trans hk).mono (by decide)⟩
  · exact hret
  · rw [i2osp_zero'] at hout
    exact hout

end VG.Proof.Dsa.X86_64

end

end

/-! # Functional correctness of an x86-64 DSA signing attempt for a validated private key

The program is the signer's, with the domain and key checks replaced by
rebuilding q−2 and the nonce's range check: the precondition that the exact
key bytes validate makes the omitted checks' mask true. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def prevalidatedSignAccepted (L : ExecutionLayout) (data : SignValues) (valid : Bool) : Bool :=
  !decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.s L), b = 0) &&
  (!decide (∀ b ∈ Spec.Dsa.encodeBE L.qLen (data.r L), b = 0) &&
  (decide (0 < Spec.Dsa.decodeBE data.nonce ∧ Spec.Dsa.decodeBE data.nonce < L.subgroup) && valid))

theorem prevalidatedSignCompute_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
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
    WP isa (PrevalidatedSign.compute Sq.mm M.mm) s0 fun s5 =>
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
  refine WP.seq (WP.mono (coreSign_ok M Sq h2.ready hp hq hop hoq hpf hqf data hg2 hn2 hx2 hz2
    hgl hnl hxl hzl hqm2) fun s3 ⟨h3, hr3bytes, hs3bytes, hf3, hm3eq, hk3⟩ => ?_)
  have hm3 := hm3eq.trans h2.mask
  simp only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] at hm3
  have hr3 := h3.encodedLocal .q r (data.r L) (by decide) hr hr3bytes
  have hs3 := h3.encodedLocal .q s (data.s L) (by decide) hs hs3bytes
  refine WP.seq (WP.mono (readyZero_ok h3 (Core.scalar r) (by change r < 2 ^ 31; decide) hr3
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hql])
    (by simp only [encodeBE_length, ModulusSide.length]; omega_using [hqu]) true hm3) fun s4 h4 => ?_)
  have hr4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hr3
  have hs4 := h4.preserve h3 (Nat.le_refl _) (by decide) (by trivial) hs3
  refine WP.mono (readyZero_ok h4.ready (Core.scalar s) (by change s < 2 ^ 31; decide) hs4
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

def prevalidatedSignBody (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (PrevalidatedSign.compute sq mul) signRelease

theorem prevalidatedSignBody_ok (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup)
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (data : SignValues) {yb qb : List Byte} (h : SigningOperands L data yb qb s0)
    {valid : Bool} (hm : word s0.mem L.base Field.mask.offset = mask valid)
    (hw : ∀ i < 2 * L.qLen, InRegions s0.wr (L.fields .out + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < 2 * L.qLen, usedBytes ≤ ofs L.base (L.fields .out + BitVec.ofNat 64 i)) :
    WP isa (prevalidatedSignBody Sq.mm M.mm) s0 fun t =>
      t.gpr .rax = BitVec.ofNat 64 (prevalidatedSignAccepted L data valid).toNat ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) =
        (if prevalidatedSignAccepted L data valid then Spec.Dsa.encodeBE L.qLen (data.r L) ++
          Spec.Dsa.encodeBE L.qLen (data.s L) else List.replicate (2 * L.qLen) 0) ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  unfold prevalidatedSignBody
  refine WP.seq (WP.mono (prevalidatedSignCompute_ok M Sq h0 hp hq hop hoq hpf hqf data h.generator
    h.privateScalar h.nonce h.digest h.generatorLength h.privateLength h.nonceLength h.digestBound hm)
    fun s1 ⟨h1, hm1, hr1, hs1, hf1, hk1⟩ => ?_)
  refine WP.mono (signRelease_ok h1 hm1 (fun i hi => by rw [hk1.2.2]; exact hw i hi) hsep)
    fun t ⟨ha, hb, hsave, hf, hk⟩ => ?_
  refine ⟨ha, ?_, ?_, ?_, (hk1.trans hk).mono (by decide)⟩
  · rw [hr1, hs1] at hb
    exact hb
  · intro i hi
    exact (hsave i hi).trans (hf1.word (Or.inl (by omega_using [hi])) (by omega_using [hi]))
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

theorem prevalidatedSignBody_spec (M : Mont) (Sq : MontS) {L : ExecutionLayout} {s0 : State} (h0 : Ready L s0)
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
    WP isa (prevalidatedSignBody Sq.mm M.mm) s0 fun t =>
      let result := Spec.Dsa.signBytes L.pLen L.qLen key data.nonce digest
      t.gpr .rax = BitVec.ofNat 64 (Spec.Dsa.signStatus result) ∧
      Spec.Rsa.bytesAt t.mem (L.fields .out) (2 * L.qLen) = result.getD (List.replicate (2 * L.qLen) 0) ∧
      (∀ i < 6, t.gpr (saved.getD i .rax) = word s0.mem L.base (8 * i)) ∧
      (∀ x, usedBytes ≤ ofs L.base x → (∀ i < 2 * L.qLen, x ≠ L.fields .out + BitVec.ofNat 64 i) →
        t.mem x = s0.mem x) ∧ Keep coreRegs s0 t := by
  obtain ⟨hp, hq, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have he := signBytes_compute L data yb key digest n hsize hop hoq hpf hqf h.publicLength hkl h.nonceLength hk hqn hz
  rw [signAccepted_prevalidated L data hsize hop hoq hpf h.publicLength hkl hk hv] at he
  refine WP.mono (prevalidatedSignBody_ok M Sq h0 hp hq hop hoq hpf hqf data h hm hw hsep) fun t ht => ?_
  rw [he]
  cases hc : prevalidatedSignAccepted L data true <;> simpa only [hc, Bool.toNat_false, Bool.toNat_true,
    Bool.false_eq_true, ↓reduceIte, Spec.Dsa.signStatus, Option.isSome_none, Option.isSome_some,
    Option.getD_none, Option.getD_some] using ht

theorem prevalidatedSignAccepted_ok (M : Mont) (Sq : MontS) {p : SigningInput} {original s : State}
    (h : SigningPre p original)
    (hi : SigningInitialized p original h.pLength s) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (prevalidatedSignBody Sq.mm M.mm) s (SigningPost p original) := by
  obtain ⟨pi, qi, hr, ho, hm, hsave, hf, hk⟩ := hi
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
  refine WP.mono (prevalidatedSignBody_spec M Sq hr p.values ho hsize hpodd hqodd hpf hqf p.keyLength hkey
    hqn rfl hv hm (fun i hi => by rw [hk.2.2]; exact h.writable i hi) h.separate)
    fun t ⟨hret, hout, hsaved, hframe, hkeep⟩ => ?_
  exact ⟨hret, hout, fun i hi => (hsaved i hi).trans (hsave i hi),
    fun x hx ho => (hframe x hx ho).trans (hf x hx), (hk.trans hkeep).mono (by decide)⟩

theorem prevalidatedSignSuccess_ok (M : Mont) (Sq : MontS) {p : SigningInput} {original st : State}
    (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength st) (ha : p.accepted = true)
    (hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (seqs [SignVerify.workspaces, PrevalidatedSign.compute Sq.mm M.mm,
      SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result]) st
      (SigningPost p original) := by
  refine WP.seq (WP.mono (signingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := prevalidatedSignAccepted_ok M Sq h ht ha hv
  unfold prevalidatedSignBody signRelease at hb
  exact hb

theorem prevalidatedSignMain_ok (M : Mont) (Sq : MontS) {p : SigningInput} {s0 : State} (h : SigningPre p s0)
    (hv : Spec.Dsa.validatePrivateKeyBytes p.pLen p.qLen p.key = true) :
    WP isa (PrevalidatedSign.sign Sq.mm M.mm) s0 (SigningPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (signingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => signingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h)
      (fun _ => prevalidatedSignSuccess_ok M Sq h hs ha hv)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SigningCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SigningPublic`, which this module and modules that import it used -/

section

/-! # Public observations used to relate two complete signing calls

The reference call supplies public lengths, addresses and domain bytes. The
relation does not equate private scalars, nonces, digests or scratch contents.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  stack : c.original.gpr .rsp = reference.original.gpr .rsp

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
  refine ⟨c.pre.scratch.congr he.keep.2.2, he.base, he.p, he.q, ?_, ?_, he.digestLen,
    source_take hkey, ?_⟩
  · change word s.mem c.input.base Field.pLen.offset = BitVec.ofNat 64 c.input.components.p.length
    rw [c.input.components.pLength]
    exact he.pLen.trans c.pre.pLength
  · change word s.mem c.input.base Field.qLen.offset = BitVec.ofNat 64 c.input.components.q.length
    rw [c.input.components.qLength]
    exact he.qLen
  · change Src s c.input.base usedBytes (c.original.gpr .rdx + c.original.gpr .r8) c.input.components.q
    rw [c.pre.pLength]
    exact source_slice hkey (by rw [c.input.keyLength]; omega_using [])

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of the complete signing entry point -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/SigningShapeCT.lean`, which only this module imported.
section

/-! # Constant time of signing argument capture and domain validation -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingEntered_ct : RelCT isa (Two SigningStart) (.block SignVerify.signEntry) (Two SigningEntered) := by
  refine two_post (two_map (fun c : SigningCall => (c.layout.base, c.original.gpr .rsp)) ?_ signEntry_ct) ?_
  · intro reference s ⟨c, ha, hs⟩
    subst s
    have hb : c.input.base = reference.layout.base := congrArg ExecutionLayout.base ha.layout
    refine ⟨ha.stack, ?_, ?_⟩
    · rw [← ha.stack, ← hb]
      exact c.pre.base
    · rw [← ha.stack]
      exact c.pre.stackRead 4 (by decide) (by decide)
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
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hkey := c.pre.keySource.congrK hs.frame hs.keep
  have hps : Src s c.layout.base usedBytes (c.layout.fields .p) c.input.components.p := source_take hkey
  have hqs : Src s c.layout.base usedBytes (c.layout.fields .q) c.input.components.q := by
    change Src s c.input.base usedBytes (c.original.gpr .rdx + c.original.gpr .r8) c.input.components.q
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

end VG.Proof.Dsa.X86_64
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/SigningReadyCT.lean`, which only this module imported.
section

/-! # The public schedule after independent signing-workspace initialization -/

public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

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
  obtain ⟨c, hag, pi, qi, hr, ho, hm, _, _, hk⟩ := h
  have hw : ∀ i < 2 * c.layout.qLen, InRegions s.wr (c.layout.fields .out + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [hk.2.2]
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
  obtain ⟨reference, h₁, h₂⟩ := h
  obtain ⟨pi₁, qi₁, h₁⟩ := h₁.body reference.property
  obtain ⟨pi₂, qi₂, h₂⟩ := h₂.body reference.property
  obtain ⟨rfl, rfl⟩ := readyInverses_eq h₁.1 h₂.1
    (reference.val.input.shapeFacts reference.property).2.1
    (reference.val.input.shapeFacts reference.property).2.2
  exact ⟨_, h₁, h₂⟩

theorem signingSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
      (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
        Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
        SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq signingWorkspaces_ct ?_
  apply RelCT.seqs_append (a := [Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
    Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact (signBody_ct M Sq).mono (fun _ _ h => signingReady_related h) (fun _ _ h => h)

end VG.Proof.Dsa.X86_64
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem SigningShaped.branch {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    eval .e s = some (!reference.input.accepted) := by
  obtain ⟨c, ha, hs⟩ := h
  change s.zf = _
  rw [hs.branch, ha.accepted]

def SigningCall.failure (c : SigningCall) : FailurePublic := ⟨c.layout.base, c.layout.fields .out, c.layout.qLen⟩

theorem SigningShaped.failure {reference : SigningCall} {s : State} (h : SigningShaped reference s) :
    FailurePre reference.failure s := by
  obtain ⟨c, ha, hs⟩ := h
  have hscr : Scr s c.layout.base usedBytes := hs.scratch
  have hr : s.gpr .rdi = c.layout.base := hs.rdi
  have hf : ∀ f, word s.mem c.layout.base f.offset = c.layout.fields f := hs.fields
  rw [ha.layout] at hscr hr hf
  exact ⟨usedBytes, hscr, by decide, hr, hf .out, (hf .qLen).trans reference.layout.qLength⟩

theorem signingMain_ct (M : Mont) (Sq : MontS) : RelCT isa (Two SigningStart) (SignVerify.sign Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq signingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map SigningCall.failure (fun _ _ h => h.failure) signFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (signingSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # Constant time of an x86-64 DSA signing attempt for a validated private key -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem prevalidatedSignCompute_ct (M : Mont) (Sq : MontS) : RelCT isa (Two (ScheduleState signComputeInputs))
    (PrevalidatedSign.compute Sq.mm M.mm) (Two (ScheduleState signComputeInputs)) := by
  have h1 := scheduleMinus_ct signComputeInputs signComputeInputs_stable .q 2 qMinusTwo (by decide)
    (by intro p; have := p.qGreater; change 2 ≤ p.layout.subgroup; omega_using [this])
    (by decide) (by decide) (scalar_space (by decide)) (by taint_decide) (by taint_decide)
  have h2 := scheduleRange_ct signComputeInputs signComputeInputs_stable .q Core.nonce
    (fun p => p.layout.qLen) false (by trivial) (by simp [stablePointer, Core.nonce])
    (fun p => p.layout.widths.1) (fun _ => Nat.le_refl _) (by taint_decide)
  have h3 := coreSignSchedule_ct M Sq signComputeInputs signComputeInputs_stable
    (by intro p a ha; simp [signComputeInputs, ha])
  have h4 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar r)
    (fun p => p.layout.qLen) true (by change r < 2 ^ 31; decide) (by trivial) (by decide)
    (fun p => p.layout.widths.1) (by intro p; have := p.layout.widths; omega_using [this]) (by taint_decide)
  have h5 := scheduleZero_ct signComputeInputs signComputeInputs_stable (Core.scalar s)
    (fun p => p.layout.qLen) true (by change s < 2 ^ 31; decide) (by trivial) (by decide)
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

theorem prevalidatedSignComputeRelease_ok (M : Mont) (Sq : MontS) {p : SchedulePublic} {s : State}
    (h : SigningBodyPre p s) :
    WP isa (PrevalidatedSign.compute Sq.mm M.mm) s (ReleasePre p.release) := by
  obtain ⟨hr, ⟨data, yb, qb, ho, _⟩, ⟨valid, hm⟩, hw, hsep⟩ := h
  refine WP.mono (prevalidatedSignCompute_ok M Sq hr p.pGreater p.qGreater p.pOdd p.qOdd p.pFits p.qFits
    data ho.generator ho.privateScalar ho.nonce ho.digest ho.generatorLength ho.privateLength
    ho.nonceLength ho.digestBound hm) fun t ⟨ht, hm, _, _, _, hk⟩ => ?_
  exact ⟨ht.scratch, ht.parent.rdi, ht.fields .out (by decide),
    (ht.fields .qLen (by decide)).trans p.layout.qLength, ⟨_, hm⟩,
    fun i hi => by rw [hk.2.2]; exact hw i hi, hsep⟩

theorem prevalidatedSignBody_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two SigningBodyPre) (prevalidatedSignBody Sq.mm M.mm) (fun _ _ => True) := by
  refine RelCT.seq (R := Two (fun p : SchedulePublic => ReleasePre p.release)) ?_ ?_
  · refine two_post ((two_map (fun p => p) (fun _ _ h => h.schedule.1) (prevalidatedSignCompute_ct M Sq)).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) ?_
    exact fun _ _ h => prevalidatedSignComputeRelease_ok M Sq h
  · exact two_map SchedulePublic.release (fun _ _ h => h) signRelease_ct

theorem prevalidatedSignSuccess_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two (fun c : AcceptedSigningCall => SigningShaped c.val))
      (seqs [SignVerify.workspaces, PrevalidatedSign.compute Sq.mm M.mm,
        SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
      (fun _ _ => True) := by
  refine RelCT.seq signingWorkspaces_ct ?_
  exact (prevalidatedSignBody_ct M Sq).mono (fun _ _ h => signingReady_related h) (fun _ _ h => h)

theorem prevalidatedSignMain_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two SigningStart) (PrevalidatedSign.sign Sq.mm M.mm) (fun _ _ => True) := by
  apply RelCT.assoc
  refine RelCT.seq signingShape_ct (RelCT.ite ?_ ?_ ?_)
  · rintro s₁ s₂ ⟨reference, h₁, h₂⟩
    exact h₁.branch.trans h₂.branch.symm
  · exact ((two_map SigningCall.failure (fun _ _ h => h.failure) signFailure_ct).mono
      (fun _ _ h => h.1) (fun _ _ h => h))
  · refine (prevalidatedSignSuccess_ct M Sq).mono ?_ (fun _ _ h => h)
    rintro s₁ s₂ ⟨⟨reference, h₁, h₂⟩, hb⟩
    have ha : reference.input.accepted = true := by
      change eval .e s₁ = some false at hb
      rw [h₁.branch] at hb
      cases h : reference.input.accepted <;> simp_all
    exact ⟨⟨reference, ha⟩, h₁, h₂⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SigningABIPre`, which this module and modules that import it used -/

section

/-! # The shared signing precondition supplies every machine-level resource -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem SigningABI.pre {s : State} (h : SigningABI s) : SigningPre h.input s := by
  have hs : Scr s (stackArg s 3) ((stackArg s 4).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.scratchBound
  have hargs : (⟨stackArgAddr s 0, 40⟩ : Region) ∈ s.rd ++ s.wr := by rw [h.rd]; simp
  refine ⟨scratch_prefix hs h.used (by decide), ?_, ?_, ?_, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ofNat_toNat64 _).symm
  · intro j hj hb
    exact stackWord_read (count := 5) hargs hj (by omega_using [hb]) (by decide)
  · intro j hj hb i hi
    exact Nat.le_trans h.used (stackWord_separate (count := 5) h.scratchArgs hj (by omega_using [hb]) (by decide) i hi)
  · exact (ofNat_toNat64 _).symm
  · change stackArg s 2 = BitVec.ofNat 64 (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat).length
    rw [bytesAt_length, ofNat_toNat64]
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (s.gpr .rcx).isLt) h.keyScratch) h.used
  · exact source_shrink (src_of_region (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 0).isLt) h.nonceScratch) h.used
  · exact source_shrink (src_of_region (p := stackArg s 1) (by rw [h.rd]; simp) (Nat.le_of_lt (stackArg s 2).isLt) h.digestScratch) h.used
  · intro i hi
    exact ⟨_, by rw [h.wr]; simp, contains_byte _ (by change i < 2 * (stackArg s 0).toNat at hi; rw [h.outLength]; exact hi)
      (Nat.le_of_lt (s.gpr .rsi).isLt)⟩
  · intro i hi
    exact Nat.le_trans h.used (out_scr h.outScratch (contains_byte _
      (by change i < 2 * (stackArg s 0).toNat at hi; rw [h.outLength]; exact hi) (Nat.le_of_lt (s.gpr .rsi).isLt)))

def SigningABI.call {s : State} (h : SigningABI s) : SigningCall := ⟨h.input, s, h.pre⟩

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.Calls`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SigningVerified`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SigningAgreement`, which this module and modules that import it used -/

section

/-! # Only the signing ABI's declared public observations determine its schedule -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingLayout_eq {p₁ p₂ : SigningInput} {s₁ s₂ : State}
    {hp₁ : s₁.gpr .r8 = BitVec.ofNat 64 p₁.pLen} {hp₂ : s₂.gpr .r8 = BitVec.ofNat 64 p₂.pLen}
    (hb : p₁.base = p₂.base) (hp : p₁.pLen = p₂.pLen) (hq : p₁.qLen = p₂.qLen)
    (hd : p₁.digestPointer = p₂.digestPointer) (hdl : p₁.digest.length = p₂.digest.length)
    (hpb : p₁.components.p = p₂.components.p) (hqb : p₁.components.q = p₂.components.q)
    (hdi : s₁.gpr .rdi = s₂.gpr .rdi) (hdx : s₁.gpr .rdx = s₂.gpr .rdx)
    (h8 : s₁.gpr .r8 = s₂.gpr .r8) (h9 : s₁.gpr .r9 = s₂.gpr .r9) :
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
    (hdi : s₁.gpr .rdi = s₂.gpr .rdi) (hdx : s₁.gpr .rdx = s₂.gpr .rdx)
    (h8 : s₁.gpr .r8 = s₂.gpr .r8) (h9 : s₁.gpr .r9 = s₂.gpr .r9)
    (hsp : s₁.gpr .rsp = s₂.gpr .rsp)
    (a0 : stackArg s₁ 0 = stackArg s₂ 0) (a1 : stackArg s₁ 1 = stackArg s₂ 1)
    (a2 : stackArg s₁ 2 = stackArg s₂ 2) (a3 : stackArg s₁ 3 = stackArg s₂ 3)
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
  sig_pub [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, hdi, _, hdx, _, h8, h9, a0, a1, a2, a3, _⟩ := h
  have hpub := (List.append_inj' hl (List.length_singleton.trans List.length_singleton.symm)).1
  have hb := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hpub
  exact ⟨h₂.call, ⟨h₁.call, signingAgreement h₁ h₂ hdi hdx h8 h9 hsp a0 a1 a2 a3 hb, rfl⟩,
    ⟨h₂.call, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩

theorem signingConstantTime (M : Mont) (Sq : MontS) : ConstantTime isa (Spec.Dsa.signContract abi).pre
    (Spec.Dsa.signContract abi).pub (SignVerify.sign Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (signingMain_ct M Sq _ _ _ _ _ _ (signingPublicRelated (signingABI_of h₁) (signingABI_of h₂) hp) e₁ e₂).1

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SigningABIPost`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SigningMain`, which only this module used -/

section

/-! # Functional correctness of the complete x86-64 DSA signing program -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingSuccess_ok (M : Mont) (Sq : MontS) {p : SigningInput} {original st : State} (h : SigningPre p original)
    (hs : SigningShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
      Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
      SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result]) st
      (SigningPost p original) := by
  refine WP.seq (WP.mono (signingInitialize_ok h hs ha) fun t ht => ?_)
  have hb := signingAccepted_ok M Sq h ht ha
  apply wpAppendSequences (a := [Checks.signingKey Sq.mm M.mm, Checks.privateKey Sq.mm M.mm,
    Core.sign Sq.mm M.mm, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true])
    (b := [SignVerify.writeScalar r false, SignVerify.writeScalar s true, .block SignVerify.result])
    (by simp) (by simp)
  exact WP.seq_iff.mp hb

theorem signingMain_ok (M : Mont) (Sq : MontS) {p : SigningInput} {s0 : State} (h : SigningPre p s0) :
    WP isa (SignVerify.sign Sq.mm M.mm) s0 (SigningPost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (signingShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => signingRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change eval .e s = some true
    simp only [eval, hs.branch, ha, Bool.not_false]
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => signingSuccess_ok M Sq h hs ha)
    change eval .e s = some false
    simp only [eval, hs.branch, ha, Bool.not_true]

end VG.Proof.Dsa.X86_64

end

end

/-! # Signing correctness and ABI preservation against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem signingGprPreserved {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    gprPreserved s t := by
  obtain ⟨_, _, hsaved, hf, hk⟩ := hp
  refine ⟨?_, Mem.readW_congr fun i hi => ?_⟩
  · intro reg hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 0 (by decide)
    · exact hsaved 1 (by decide)
    · exact hk.gpr (by decide)
    · exact hsaved 2 (by decide)
    · exact hsaved 3 (by decide)
    · exact hsaved 4 (by decide)
    · exact hsaved 5 (by decide)
  · have hret := contains_byte (s.gpr .rsp) (i := i) (len := 8) hi (by decide)
    apply hf _ (Nat.le_trans h.used (out_scr h.retScratch hret))
    intro j hj he
    apply h.retOut _ hret
    rw [he]
    exact contains_byte _ (by change j < 2 * (stackArg s 0).toNat at hj; rw [h.outLength]; exact hj)
      (Nat.le_of_lt (s.gpr .rsi).isLt)

theorem signStatus_u32 (result : Option (List Byte)) :
    ((BitVec.ofNat 64 (Spec.Dsa.signStatus result)).setWidth 32).toNat = Spec.Dsa.signStatus result := by
  cases result <;> rfl

theorem signingSharedPost {s t : State} (h : SigningABI s) (hp : SigningPost h.input s t) :
    (Spec.Dsa.signContract abi).post s t := by
  obtain ⟨hr, hout, _, _, _⟩ := hp
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
  rw [hr, signStatus_u32]
  refine ⟨rfl, ?_⟩
  rw [h.outLength]
  exact hout

theorem signingCorrect (M : Mont) (Sq : MontS)
    (hmx : (SignVerify.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (Spec.Dsa.signContract abi).pre s) :
    ∃ trace t, Exec isa (SignVerify.sign Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (Spec.Dsa.signContract abi).post s t := by
  have ha := signingABI_of h
  obtain ⟨trace, t, he, hp⟩ := signingMain_ok M Sq ha.pre
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (signingGprPreserved ha hp), signingSharedPost ha hp⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # DSA signing verified against the shared contract -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64

/-- An ordinary 1024/160 call with disjoint buffers and an empty digest.
The all-zero key is allowed by the contract and is rejected by the program. -/
def signingSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 40 | .rdx => 0x2000 | .rcx => 424
    | .r8 => 128 | .r9 => 0x4000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 20 else if a = 0x10011 then 0x50
    else if a = 0x10021 then 0x80 else if a = 0x10029 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x4000, 20⟩, ⟨0x5000, 0⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x8000, 16384⟩]

theorem signingSatisfiable : ∃ s, (Spec.Dsa.signContract abi).pre s := by
  sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
    [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem signing_verified (M : Mont) (Sq : MontS)
    (hmx : (SignVerify.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (SignVerify.sign Sq.mm M.mm) (Spec.Dsa.signContract abi) :=
  ⟨signingCorrect M Sq hmx, signingConstantTime M Sq, signingSatisfiable⟩

end VG.Proof.Dsa.X86_64

end

end

/-! # DSA using RSA's callable Montgomery kernels

The shared contracts already parameterize stack use. Calls need eight bytes
for the return address; the arithmetic and leakage proofs apply to their
inlined bodies. Output buffers remain disjoint from that stack slot.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem signing_implies8 : (Spec.Dsa.signContract abi).Implies (Spec.Dsa.signContract abi 8) where
  pre := by
    intro s h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
    sig_split h
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
    sig_pre [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
      [signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using signingSatState

theorem signing_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (Spec.Dsa.signContract abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (Spec.Dsa.signContract abi).post s b) :
    (Spec.Dsa.signContract abi).post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have ha := signingABI_of hs
  have hm := Clear.miss_wr hc (by rw [ha.wr]; exact List.mem_cons_self)
    ha.outBound (Nat.le_refl _)
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at hp ⊢
  sig_post [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at hp ⊢
  simpa only [State.patch_gpr, patch_mem, bytesAt_overlay hm] using hp

theorem signing_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = SignVerify.sign Sq.mm M.mm)
    (hmx : (SignVerify.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Dsa.signContract abi 8) :=
  Verified.of_inline_sig hc (hin ▸ signingCorrect M Sq hmx) (hin ▸ signingConstantTime M Sq)
    signing_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    signing_patch

end VG.Proof.Dsa.X86_64

end

end

/-! # An x86-64 DSA signing attempt for a validated private key against its contract

`prevalidated_sign_verified` is the program's proof against
`signContractWith validatePrivateKeyBytes`, and
`prevalidated_sign_call_verified` that of the code that calls the
Montgomery kernels, whose return addresses take eight bytes of stack. The
randomized wrapper (`vg_dsa_sign_random_prevalidated`) calls it. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64

theorem prevalidatedSigningCorrect (M : Mont) (Sq : MontS)
    (hmx : (PrevalidatedSign.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s) :
    ∃ trace t, Exec isa (PrevalidatedSign.sign Sq.mm M.mm) s trace t ∧ abiPreserved s t ∧
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).post s t := by
  obtain ⟨hs, hv⟩ := signWith_pre h
  have ha := signingABI_of hs
  obtain ⟨trace, t, he, hp⟩ := prevalidatedSignMain_ok M Sq ha.pre hv
  exact ⟨trace, t, he, abiPreserved_of_exec hmx he (signingGprPreserved ha hp),
    signWith_post (signingSharedPost ha hp)⟩

theorem prevalidatedSigningConstantTime (M : Mont) (Sq : MontS) :
    ConstantTime isa (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre
      (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pub (PrevalidatedSign.sign Sq.mm M.mm) := by
  intro s₁ s₂ trace₁ trace₂ t₁ t₂ h₁ h₂ hp e₁ e₂
  exact (prevalidatedSignMain_ct M Sq _ _ _ _ _ _
    (signingPublicRelated (signingABI_of (signWith_pre h₁).1) (signingABI_of (signWith_pre h₂).1)
      (signWith_pub hp)) e₁ e₂).1

/-- `signingSatState` with `validPrivateKeyWitness` at `0x2000`. -/
def prevalidatedSignSatState : State where
  gpr := signingSatState.gpr
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
    validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0 else signingSatState.mem a
  rd := signingSatState.rd
  wr := signingSatState.wr

theorem prevalidatedSignSat_key :
    Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424 = validPrivateKeyWitness :=
  bytesAt_window (base := 0x2000) validPrivateKeyWitness_length (by decide) fun a h₁ h₂ => by
    simp only [prevalidatedSignSatState]
    exact ite_eq_left ⟨h₁, h₂⟩

theorem prevalidatedSignSat_valid : Spec.Dsa.validatePrivateKeyBytes 128 20
    (Spec.Rsa.bytesAt prevalidatedSignSatState.mem 0x2000 424) = true := by
  rw [prevalidatedSignSat_key]; exact validPrivateKeyWitness_valid

theorem prevalidatedSignSatisfiable :
    ∃ s, (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s := by
  have ho : ∃ s, (Spec.Dsa.signContract abi).pre s ∧ s = prevalidatedSignSatState := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five]
      [prevalidatedSignSatState, signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSignSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, signWith_of_pre h prevalidatedSignSat_valid⟩

theorem prevalidatedSignSatisfiable8 :
    ∃ s, (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 8).pre s := by
  have ho : ∃ s, (Spec.Dsa.signContract abi 8).pre s ∧ s = prevalidatedSignSatState := by
    sig_implies_sat [Spec.Dsa.signContract, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range,
      List.range.loop]
      [prevalidatedSignSatState, signingSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using prevalidatedSignSatState
  obtain ⟨s, h, rfl⟩ := ho
  exact ⟨_, signWith_of_pre h prevalidatedSignSat_valid⟩

theorem prevalidated_sign_verified (M : Mont) (Sq : MontS)
    (hmx : (PrevalidatedSign.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target (PrevalidatedSign.sign Sq.mm M.mm) (signContractWith Spec.Dsa.validatePrivateKeyBytes abi) :=
  ⟨prevalidatedSigningCorrect M Sq hmx, prevalidatedSigningConstantTime M Sq,
    prevalidatedSignSatisfiable⟩

theorem prevalidatedSign_implies8 : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).Implies
    (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 8) where
  pre := by
    intro s h
    sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
    sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop] at h
    sig_split h
    sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
    sig_pre [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range, List.range.loop]
    sig_and_intros
    sig_close
  post := by sig_implies_post [signContractWith, Spec.Dsa.signSig, abi, argRegs, stackArgs_five, List.range,
    List.range.loop]
  pub := by intro s t _ _ h; exact h
  sat := prevalidatedSignSatisfiable8

theorem prevalidatedSign_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64)
    (hs : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).pre s) (hc : Clear (hole (s.gpr .rsp)) s)
    (hp : (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).post s b) :
    (signContractWith Spec.Dsa.validatePrivateKeyBytes abi).post s (b.patch (hole (s.gpr .rsp)) hv u) :=
  signWith_post (signing_patch s b hv u (signWith_pre hs).1 hc (signWith_post' hp))

theorem prevalidated_sign_call_verified (M : Mont) (Sq : MontS) {c : Prog isa}
    (hc : c.InlineOk = true) (hin : c.inline = PrevalidatedSign.sign Sq.mm M.mm)
    (hmx : (PrevalidatedSign.sign Sq.mm M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (signContractWith Spec.Dsa.validatePrivateKeyBytes abi 8) :=
  Verified.of_inline_sig hc (hin ▸ prevalidatedSigningCorrect M Sq hmx) (hin ▸ prevalidatedSigningConstantTime M Sq)
    prevalidatedSign_implies8 (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h)
    prevalidatedSign_patch

end VG.Proof.Dsa.X86_64
