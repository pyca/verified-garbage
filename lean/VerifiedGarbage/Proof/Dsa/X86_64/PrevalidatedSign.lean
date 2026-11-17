module

public import VerifiedGarbage.Impl.Dsa.X86_64.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.CheckOperands
import VerifiedGarbage.Proof.Dsa.X86_64.Sequences
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleState
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Dsa.X86_64.SigningInitialize
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

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
