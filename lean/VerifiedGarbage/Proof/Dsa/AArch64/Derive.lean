module

public import VerifiedGarbage.Proof.Dsa.AArch64.DeriveEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Parameters

import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCopy
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveWrite
import VerifiedGarbage.Proof.Dsa.AArch64.CallOperands
import VerifiedGarbage.Proof.Dsa.AArch64.ScheduleOperands
import VerifiedGarbage.Proof.Dsa.AArch64.SourceSlices
import VerifiedGarbage.Proof.Dsa.AArch64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.AArch64.ABIRegions
import VerifiedGarbage.Proof.Dsa.AArch64.Result
import VerifiedGarbage.Proof.Dsa.AArch64.Sequences
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Tactic.Set
import VerifiedGarbage.Impl.Dsa.AArch64.Generate
import VerifiedGarbage.Proof.Dsa.AArch64.Finish
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
/-! # Functional correctness of AArch64 DSA key derivation -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/DeriveFailure.lean`, which only this module imported.
section

/-! # Zeroing a derived key after domain rejection -/

section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

open VG.Impl.Dsa.Layout

theorem deriveFailure_ok {s : State} {B : Addr} {Z k q : Nat} {op : Addr} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : pWorkspace ≤ Z) {p : Nat} (hkq : k = 3 * p + 2 * q) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hO : word s.mem B Field.out.offset = op) (hK : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q)
    (hP : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p)
    (hout : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa Generate.deriveFailure s fun t => Spec.Rsa.bytesAt t.mem op k = List.replicate k 0 ∧
      t.gpr .x0 = 0 ∧ (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧
      Keep coreRegs s t := by
  have hn := hs.nowrap
  unfold Generate.deriveFailure seqs
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => t.gpr .x1 = op + BitVec.ofNat 64 0 ∧
      t.gpr .x2 = BitVec.ofNat 64 k ∧ t.gpr .x3 = 0 ∧ t.mem = s.mem) (by
    brun [h0, Core.field, field_enc .out, field_enc .pLen, field_enc .qLen, fieldAddress,
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .out).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .pLen).2 hZ),
      hs.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds .qLen).2 hZ), hO, hP, hK]
    simp only [BitVec.ofNat_add_ofNat, hkq]
    congr 1
    omega) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h1, h2, h3, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (N := k) (by omega) (by omega) (BInv s₁ op)
    (fun j hj t hI _ => bStep_ok (by omega) h3 (fun i hi => by rw [k₁.wr]; exact hout i hi) hj hI)
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

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

/-- The scratch derivation uses: the signer's layout and the derived y. -/
abbrev deriveExtent : Nat := derivedY + 384

structure DeriveInput extends ParametersInput where
  x : List Byte
  xLength : x.length = qLen

namespace DeriveInput

variable (p : DeriveInput)

abbrev outLen : Nat := 3 * p.pLen + 2 * p.qLen

def layout (original : State) (hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen) : ExecutionLayout where
  base := p.base
  pLen := p.pLen
  qLen := p.qLen
  modulus := Spec.Dsa.decodeBE p.pb
  subgroup := Spec.Dsa.decodeBE p.qb
  pInverse := 0
  qInverse := 0
  fields := deriveFieldValues original (BitVec.ofNat 64 p.qLen) p.base p.accepted
  lengths := p.lengths
  pLength := hp
  qLength := rfl

/-- The derived public value. -/
abbrev y : Nat := Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.x) (Spec.Dsa.decodeBE p.pb)

abbrev yb : List Byte := Spec.Dsa.encodeBE p.pLen p.y

end DeriveInput

structure DerivePre (p : DeriveInput) (s : State) : Prop where
  scratch : Scr s p.base deriveExtent
  qLength : s.gpr .x6 = BitVec.ofNat 64 p.qLen
  base : s.gpr .x7 = p.base
  pLength : s.gpr .x4 = BitVec.ofNat 64 p.pLen
  paramsSource : Src s p.base deriveExtent (s.gpr .x2) p.params
  xSource : Src s p.base deriveExtent (s.gpr .x5) p.x
  outWrite : ∀ i < p.outLen, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 i) 1
  outSeparate : ∀ i < p.outLen, deriveExtent ≤ ofs p.base (s.gpr .x0 + BitVec.ofNat 64 i)
  paramsOut : ∀ i < 2 * p.pLen + p.qLen, ∀ j < p.outLen,
    s.gpr .x2 + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j
  xOut : ∀ i < p.qLen, ∀ j < p.outLen, s.gpr .x5 + BitVec.ofNat 64 i ≠ s.gpr .x0 + BitVec.ofNat 64 j

theorem DerivePre.sources {p : DeriveInput} {original s : State} (h : DerivePre p original)
    (hm : InScr p.base deriveExtent original.mem s.mem) (hk : Keep coreRegs original s) :
    Src s p.base deriveExtent (original.gpr .x2) p.pb ∧
    Src s p.base deriveExtent (original.gpr .x2 + original.gpr .x4) p.qb ∧
    Src s p.base deriveExtent (original.gpr .x2 + original.gpr .x4 + BitVec.ofNat 64 p.qLen) p.gb ∧
    Src s p.base deriveExtent (original.gpr .x5) p.x := by
  have hsrc := h.paramsSource.congrK hm hk
  refine ⟨source_take hsrc, ?_, ?_, h.xSource.congrK hm hk⟩
  · rw [h.pLength]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_arith)
  · rw [h.pLength, Offset.add_add]
    exact source_slice hsrc (by rw [p.paramsLength]; omega_arith)

structure DeriveShapePost (p : DeriveInput) (original : State)
    (hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen) (s : State) : Prop where
  scratch : Scr s p.base deriveExtent
  x0 : s.gpr .x0 = p.base
  fields : ∀ f, word s.mem p.base f.offset = (p.layout original hp).fields f
  branch : (s.gpr .x3 == (0#64)) = !p.accepted
  frame : InScr p.base deriveExtent original.mem s.mem
  keep : Keep coreRegs original s

theorem deriveShape_ok {p : DeriveInput} {s0 : State} (h : DerivePre p s0) :
    WP isa (.seq (.block Generate.deriveEntry) Checks.domainShape) s0
      (DeriveShapePost p s0 h.pLength) := by
  have hsu : Scr s0 p.base usedBytes := scratch_prefix h.scratch (by decide) (by decide)
  refine WP.seq (WP.mono (deriveEntry_ok hsu h.base)
    fun s1 he => ?_)
  rw [h.qLength] at he
  have hinside : InScr p.base deriveExtent s0.mem s1.mem := InScr.of_outside he.frame (by decide)
  obtain ⟨hps, hqs, _, _⟩ := h.sources hinside (he.keep.mono (by decide))
  have hp64 : p.pb.length < 2 ^ 64 := by
    rw [p.pbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  have hq64 : p.qb.length < 2 ^ 64 := by
    rw [p.qbLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  refine WP.mono (domainShape_ok (hsu.congr he.keep.wr) he.base (by decide)
    (he.fields .p (by decide) (by decide)) (he.fields .q (by decide) (by decide))
    ((he.fields .pLen (by decide) (by decide)).trans (by rw [p.pbLength]; exact h.pLength))
    ((he.fields .qLen (by decide) (by decide)).trans (by rw [p.qbLength]; rfl))
    (source_shrink hps (by decide)) (source_shrink hqs (by decide)) p.pPositive hp64 p.qPositive hq64
    rfl rfl (by decide) (he.fields .digestLen (by decide) (by decide)))
    fun s2 ⟨hprefix, hmask, hbranch, hf, hk⟩ => ?_
  have hall := he.keep.trans hk
  have hft : InScr p.base deriveExtent s1.mem s2.mem := by
    apply InScr.of_frm hf
    intro range hr
    simp only [shapeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  refine ⟨h.scratch.congr hall.wr, (hk.gpr .x0 (by decide)).trans he.base,
    he.shapeFields hf ?_ (by rw [hprefix]; rfl) hmask, hbranch,
    hinside.trans hft, hall.mono (by decide)⟩
  intro f h1 h2
  cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 | rfl

/-- The output and frame of a derivation. -/
def DerivePost (p : DeriveInput) (original t : State) : Prop :=
  let res := Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x
  t.gpr .x0 = BitVec.ofNat 64 (Spec.Dsa.signStatus res) ∧
  Spec.Rsa.bytesAt t.mem (original.gpr .x0) p.outLen = res.getD (List.replicate p.outLen 0) ∧
  (∀ x, deriveExtent ≤ ofs p.base x → (∀ j < p.outLen, x ≠ original.gpr .x0 + BitVec.ofNat 64 j) →
    t.mem x = original.mem x) ∧
  Keep coreRegs original t

theorem DeriveInput.derive_eq (p : DeriveInput) :
    Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x =
      if p.accepted && (decide (Spec.Dsa.powMod (Spec.Dsa.decodeBE p.gb) (Spec.Dsa.decodeBE p.qb)
          (Spec.Dsa.decodeBE p.pb) = 1) &&
        (decide ((Spec.Dsa.decodeBE p.pb - 1) % Spec.Dsa.decodeBE p.qb = 0) &&
        (decide (1 < p.y ∧ p.y < Spec.Dsa.decodeBE p.pb) &&
        (decide (1 < Spec.Dsa.decodeBE p.gb ∧ Spec.Dsa.decodeBE p.gb < Spec.Dsa.decodeBE p.pb) &&
        (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < Spec.Dsa.decodeBE p.qb) && true)))))
      then some (p.params ++ p.yb ++ p.x) else none := by
  rw [VG.Proof.Dsa.deriveKeyBytes_eq p.lengths p.paramsLength p.xLength, ParametersInput.accepted,
    shapeAccepted_spec]
  rfl

theorem bytesAt_zero_list (mem : Mem) (O : Addr) (n : Nat)
    (h : ∀ i < n, mem (O + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt mem O n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
  exact h i h1

theorem deriveRejected_ok {p : DeriveInput} {original s : State} (h : DerivePre p original)
    (hs : DeriveShapePost p original h.pLength s) (ha : p.accepted = false) :
    WP isa Generate.deriveFailure s (DerivePost p original) := by
  have hf := hs.fields
  have hq1 : 1 ≤ p.qLen := by have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_arith
  have hk31 : p.outLen < 2 ^ 31 := by
    have := p.lengths; unfold Spec.Dsa.lengthsValid at this; unfold DeriveInput.outLen; omega_arith
  refine WP.mono (deriveFailure_ok (k := p.outLen) (q := p.qLen) (p := p.pLen) hs.scratch hs.x0 (by decide) rfl
    (by unfold DeriveInput.outLen; omega_arith) hk31 (hf .out) (hf .qLen) (hf .pLen |>.trans h.pLength)
    (fun j hj => by rw [hs.keep.wr]; exact h.outWrite j hj))
    fun t ⟨hbytes, hret, hframe, hk⟩ => ?_
  have hres : Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x = none := by
    rw [p.derive_eq, ha, Bool.false_and]; rfl
  refine ⟨by rw [hret, hres]; rfl, ?_, ?_,
    (hs.keep.trans hk).mono (by decide)⟩
  · rw [hres, Option.getD_none]
    exact hbytes
  · intro x hx hout
    exact (hframe x hout).trans (hs.frame x hx)

theorem OperandBytes.frame {L : ExecutionLayout} {s t : State} (hs : Ready L s) (ht : Ready L t)
    (hf : Outside L.base 128 (deriveExtent - 128) s.mem t.mem) (hk : Keep coreRegs s t)
    {a : Operand} {bytes : List Byte} (ha : a.length ≠ .mask) (hp : stablePointer a.pointer)
    (hb : OperandBytes s L.base deriveExtent a bytes) : OperandBytes t L.base deriveExtent a bytes := by
  refine ⟨(ht.fields a.length ha).trans ((hs.fields a.length ha).symm.trans hb.length), ?_⟩
  rw [hs.pointer_eq ht a.pointer hp]
  exact hb.source.congrK (InScr.of_outside hf (by decide)) hk

theorem OperandBytes.shrink {s : State} {B : Addr} {Z n : Nat} {a : Operand} {bs : List Byte}
    (h : OperandBytes s B Z a bs) (hn : n ≤ Z) : OperandBytes s B n a bs :=
  ⟨h.length, source_shrink h.source hn⟩

/-- What derivation computes before writing the key: x's range, y = g^x
copied past the signer's layout, and the signer's checks with that y. -/
theorem deriveBody_ok (M : Mont) {L : ExecutionLayout} {s : State} (hr : Ready L s)
    (hs : Scr s L.base deriveExtent)
    (hp : 1 < L.modulus) (hq : 255 < L.subgroup) (hpo : L.modulus % 2 = 1) (hqo : L.subgroup % 2 = 1)
    (hpf : L.modulus ≤ 256 ^ L.pLen) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    {gb qb xb : List Byte}
    (hg : OperandBytes s L.base deriveExtent Core.generator gb)
    (hqb : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ qb)
    (hx : OperandBytes s L.base deriveExtent Core.privateScalar xb)
    (hgl : gb.length = L.pLen) (hql : qb.length = L.qLen) (hxl : xb.length = L.qLen)
    (hqv : Spec.Dsa.decodeBE qb = L.subgroup) (hy : L.fields .y = off L.base derivedY)
    (hm : word s.mem L.base Field.mask.offset = mask true) :
    let y := Spec.Dsa.powMod (Spec.Dsa.decodeBE gb) (Spec.Dsa.decodeBE xb) L.modulus
    WP isa (seqs [Checks.range qWorkspace Core.privateScalar,
        Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
        Generate.copyY, Checks.signingKey M.mm]) s fun t =>
      Ready L t ∧
      word t.mem L.base Field.mask.offset = mask (signingKeyAccepted L gb (Spec.Dsa.encodeBE L.pLen y)
        (decide (0 < Spec.Dsa.decodeBE xb ∧ Spec.Dsa.decodeBE xb < L.subgroup) && true)) ∧
      (∀ i (hi : i < L.pLen), t.mem (off L.base derivedY + BitVec.ofNat 64 i) =
        (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)) ∧
      Outside L.base 128 (deriveExtent - 128) s.mem t.mem ∧ Keep coreRegs s t := by
  intro y
  obtain ⟨hql1, hqu, hqp, hpu⟩ := L.widths
  have hp384 : 0 < L.pLen ∧ L.pLen ≤ 384 := by
    have hl := L.lengths; unfold Spec.Dsa.lengthsValid at hl; omega_using [hl]
  have hend : t2 + L.pLen ≤ usedBytes := by unfold t2 usedBytes; omega_using [hp384]
  unfold seqs
  -- 0 < x < q
  refine WP.seq (WP.mono (readyRange_ok hr .q Core.privateScalar (by trivial) (hx.shrink (by decide)).active
    (by rw [hxl]; omega_using [hql1]) (by simp only [hxl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    false hm) fun s1 h1 => ?_)
  have hf1 : Outside L.base 128 (deriveExtent - 128) s.mem s1.mem := h1.frame.mono (by decide) (by decide)
  have hg1 := hg.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.generator])
  have hq1 := hqb.frame hr h1.ready hf1 h1.keep (by decide) (by change Field.q ≠ .mask; decide)
  have hx1 := hx.frame hr h1.ready hf1 h1.keep (by decide) (by simp [stablePointer, Core.privateScalar])
  -- y = g^x mod p, at t2
  have step2 := readyPow_ok M h1.ready .p hp hpo Core.generator Core.privateScalar (by trivial) (by trivial)
    (hg1.shrink (by decide)).active (hx1.shrink (by decide)).active (by rw [hgl]; omega_using [hp384])
    (by simp only [hgl, ModulusSide.words, ModulusSide.length]; exact Nat.le_refl _)
    (by rw [hxl]; omega_using [hql1]) (by rw [hxl]; omega_using [hqu]) t2 (by decide) hend
  have step2' : WP isa (Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2)) s1
      (CallResult L .p t2 y s1) := by
    simpa only [Core.element, ModulusSide.offset, ModulusSide.lengthField, ModulusSide.value] using step2
  refine WP.seq (WP.mono step2' fun s2 h2 => ?_)
  have hf2 : Outside L.base 128 (deriveExtent - 128) s1.mem s2.mem :=
    (h2.scheduleFrame (by decide) hend).mono (by decide) (by decide)
  have hg2 := hg1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by simp [stablePointer, Core.generator])
  have hq2 := hq1.frame h1.ready h2.ready hf2 h2.keep (by decide) (by change Field.q ≠ .mask; decide)
  have hm2 := (h2.fields (by decide) hend .mask).trans h1.mask
  have hs2 : Scr s2 L.base deriveExtent := hs.congr (h1.keep.trans h2.keep).wr
  -- y, copied past the signer's layout
  refine WP.seq (WP.mono (copyY_ok h2.ready hs2) fun s3 ⟨h3, hy3, hf3o, hk3⟩ => ?_)
  have hf3 : Outside L.base 128 (deriveExtent - 128) s2.mem s3.mem :=
    hf3o.mono (by decide) (by unfold deriveExtent; omega_using [hp384])
  have hg3 := hg2.frame h2.ready h3 hf3 hk3 (by decide) (by simp [stablePointer, Core.generator])
  have hq3 := hq2.frame h2.ready h3 hf3 hk3 (by decide) (by change Field.q ≠ .mask; decide)
  have hm3 : word s3.mem L.base Field.mask.offset = mask (decide (0 < Spec.Dsa.decodeBE xb ∧
      Spec.Dsa.decodeBE xb < L.subgroup) && true) := by
    refine (hf3o.word (Or.inl (by decide)) (by decide)).trans ?_
    simpa only [Bool.false_eq_true, ↓reduceIte, ModulusSide.value] using hm2
  have hyb : ∀ i (hi : i < L.pLen), s3.mem (off L.base derivedY + BitVec.ofNat 64 i) =
      (Spec.Dsa.encodeBE L.pLen y)[i]'(by rw [VG.Proof.Dsa.encodeBE_length]; exact hi) := by
    intro i hi
    rw [hy3 i hi]
    have hb := congrArg (fun l => l[i]?) h2.bytes
    simp only [ModulusSide.length, Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range hi,
      Option.map_some] at hb
    rw [List.getElem?_eq_getElem (by rw [VG.Proof.Dsa.encodeBE_length]; exact hi)] at hb
    exact Option.some.inj hb
  have hys : OperandBytes s3 L.base usedBytes Core.publicValue (Spec.Dsa.encodeBE L.pLen y) := by
    refine ⟨(h3.fields .pLen (by decide)).trans (by rw [VG.Proof.Dsa.encodeBE_length]; exact L.pLength), ?_⟩
    simp only [Core.publicValue, pointerValue, h3.fields .y (by decide), hy]
    refine ⟨fun i hi => ?_, fun i hi => hyb i (by rwa [VG.Proof.Dsa.encodeBE_length] at hi), fun i hi => ?_⟩
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [off_add]
      exact scr_byte_rd (hs.congr (h1.keep.trans (h2.keep.trans hk3)).wr)
        (by unfold deriveExtent; omega_using [hi, hp384])
    · rw [VG.Proof.Dsa.encodeBE_length] at hi
      rw [ofs_off _ (by have := hs.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
      exact Nat.le_add_right _ _
  -- the signer's checks of the domain and y
  refine WP.mono (signingKey_ok M h3 hp hq hpo hqo hpf hqf (hg3.shrink (by decide)) hys (hq3.shrink (by decide))
    hgl (VG.Proof.Dsa.encodeBE_length _ _) hql hqv hm3) fun t ⟨ht, hmt, _, hft, hkt⟩ => ?_
  refine ⟨ht, hmt, fun i hi => (hft _ (Or.inr ?_)).trans (hyb i hi), ?_,
    (((h1.keep.trans h2.keep).trans hk3).trans hkt).mono (by decide)⟩
  · rw [ofs_off _ (by have := hs.nowrap; unfold deriveExtent at this; omega_using [this, hi, hp384])]
    exact Nat.le_trans (by decide) (Nat.le_add_right _ _)
  · exact ((hf1.trans hf2).trans hf3).trans (hft.mono (by decide) (by decide))

theorem bytesAt_key (mem : Mem) (O : Addr) (l₁ l₂ l₃ : List Byte)
    (h₁ : ∀ i (hi : i < l₁.length), mem (O + BitVec.ofNat 64 i) = l₁[i])
    (h₂ : ∀ i (hi : i < l₂.length), mem (O + BitVec.ofNat 64 (l₁.length + i)) = l₂[i])
    (h₃ : ∀ i (hi : i < l₃.length), mem (O + BitVec.ofNat 64 (l₁.length + l₂.length + i)) = l₃[i]) :
    Spec.Rsa.bytesAt mem O (l₁.length + l₂.length + l₃.length) = l₁ ++ l₂ ++ l₃ := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt, Nat.add_assoc])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at hi
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  by_cases a : i < l₁.length
  · rw [List.getElem_append_left (by simp only [List.length_append]; omega_arith), List.getElem_append_left a]
    exact h₁ i a
  by_cases b : i < l₁.length + l₂.length
  · rw [List.getElem_append_left (by simp only [List.length_append]; omega_arith),
      List.getElem_append_right (by omega_arith)]
    have := h₂ (i - l₁.length) (by omega_arith)
    rwa [show l₁.length + (i - l₁.length) = i by omega_arith] at this
  · rw [List.getElem_append_right (by simp only [List.length_append]; omega_arith)]
    have := h₃ (i - (l₁ ++ l₂).length) (by simp only [List.length_append]; omega_arith)
    simp only [List.length_append] at this ⊢
    rwa [show l₁.length + l₂.length + (i - (l₁.length + l₂.length)) = i by omega_arith] at this

structure DeriveOperands (L : ExecutionLayout) (p : DeriveInput) (s : State) : Prop where
  generator : OperandBytes s L.base deriveExtent Core.generator p.gb
  subgroup : OperandBytes s L.base deriveExtent ⟨.input .q, .qLen⟩ p.qb
  scalar : OperandBytes s L.base deriveExtent Core.privateScalar p.x

def DeriveInitialized (p : DeriveInput) (original : State)
    (hp : original.gpr .x4 = BitVec.ofNat 64 p.pLen) (s : State) : Prop :=
  ∃ pi qi,
    Ready ((p.layout original hp).withInverses pi qi) s ∧
    DeriveOperands ((p.layout original hp).withInverses pi qi) p s ∧
    word s.mem p.base Field.mask.offset = mask true ∧
    InScr p.base deriveExtent original.mem s.mem ∧ Keep coreRegs original s

theorem deriveInitialize_ok {p : DeriveInput} {original st : State} (h : DerivePre p original)
    (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa SignVerify.workspaces st (DeriveInitialized p original h.pLength) := by
  let L := p.layout original h.pLength
  obtain ⟨_, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hps, hqs, _, _⟩ := h.sources hs.frame hs.keep
  refine WP.mono (workspacesReady_ok (L := L) (scratch_prefix hs.scratch (by decide) (by decide)) hs.x0
    hs.fields (source_shrink hps (by decide)) (source_shrink hqs (by decide))
    p.pbLength p.qbLength rfl rfl hpo hqo) fun t ⟨pi, qi, hr, hf, hm, hk⟩ => ?_
  let L' := L.withInverses pi qi
  have hr' : Ready L' t := hr
  have hframe : InScr p.base deriveExtent original.mem t.mem :=
    hs.frame.trans (InScr.of_outside hf (by decide))
  have hkeep := hs.keep.trans hk
  obtain ⟨_, hqs', hgs', hxs'⟩ := h.sources hframe (hkeep.mono (by decide))
  have operand (f len : Field) (hf : f ≠ .mask) (hl : len ≠ .mask) {bs : List Byte}
      (hsrc : Src t L'.base deriveExtent (L'.fields f) bs) (hlen : L'.fields len = BitVec.ofNat 64 bs.length) :
      OperandBytes t L'.base deriveExtent ⟨.input f, len⟩ bs := by
    refine ⟨(hr'.fields len hl).trans hlen, ?_⟩
    simpa only [pointerValue, hr'.fields f hf] using hsrc
  refine ⟨pi, qi, hr', ⟨operand .g .pLen (by decide) (by decide) hgs' (by rw [p.gbLength]; exact h.pLength),
    operand .q .qLen (by decide) (by decide) hqs' (by rw [p.qbLength]; rfl),
    operand .x .qLen (by decide) (by decide) hxs' (by rw [p.xLength]; rfl)⟩,
    hm.trans ((hs.fields .mask).trans (congrArg mask ha)),
    hframe, hkeep.mono (by decide)⟩

theorem deriveSuccess_ok (M : Mont) {p : DeriveInput} {original st : State}
    (h : DerivePre p original) (hs : DeriveShapePost p original h.pLength st) (ha : p.accepted = true) :
    WP isa (seqs [SignVerify.workspaces, Checks.range qWorkspace Core.privateScalar,
      Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
      Generate.copyY, Checks.signingKey M.mm, Generate.writeKey, .block SignVerify.result]) st
      (DerivePost p original) := by
  obtain ⟨hsize, hpo, hqo⟩ := p.shapeFacts ha
  obtain ⟨hp1, hq255, _⟩ := VG.Proof.Dsa.supported_bounds hsize
  have hpf : Spec.Dsa.decodeBE p.pb ≤ 256 ^ p.pLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.pb; rw [p.pbLength] at hh; exact Nat.le_of_lt hh
  have hqf : Spec.Dsa.decodeBE p.qb ≤ 256 ^ p.qLen := by
    have hh := VG.Proof.Dsa.decodeBE_lt p.qb; rw [p.qbLength] at hh; exact Nat.le_of_lt hh
  have hl := p.lengths
  unfold Spec.Dsa.lengthsValid at hl
  refine WP.seq (WP.mono (deriveInitialize_ok h hs ha) fun u ⟨pi, qi, hr, ho, hm, hframe, hkeep⟩ => ?_)
  let L := (p.layout original h.pLength).withInverses pi qi
  have hsu : Scr u p.base deriveExtent := h.scratch.congr hkeep.wr
  apply wpAppendSequences (a := [Checks.range qWorkspace Core.privateScalar,
    Core.pow M.mm pWorkspace Core.generator Core.privateScalar (Core.element t2),
    Generate.copyY, Checks.signingKey M.mm]) (b := [Generate.writeKey, .block SignVerify.result])
    (by simp) (by simp)
  refine WP.mono (deriveBody_ok (L := L) M hr hsu hp1 hq255 hpo hqo hpf hqf ho.generator ho.subgroup ho.scalar
    p.gbLength p.qbLength p.xLength rfl rfl hm) fun v ⟨hv, hmv, hyv, hfv, hkv⟩ => ?_
  have hframe' : InScr p.base deriveExtent original.mem v.mem :=
    hframe.trans (InScr.of_outside hfv (by decide))
  have hkeep' : Keep coreRegs original v := (hkeep.trans hkv).mono (by decide)
  have hsv' : Scr v p.base deriveExtent := h.scratch.congr hkeep'.wr
  obtain ⟨_, _, _, hxs⟩ := h.sources hframe' hkeep'
  have hparams := h.paramsSource.congrK hframe' hkeep'
  set valid := signingKeyAccepted L p.gb p.yb
    (decide (0 < Spec.Dsa.decodeBE p.x ∧ Spec.Dsa.decodeBE p.x < L.subgroup) && true) with hvalid
  have hfields : KeyFields v p.base (original.gpr .x0) (original.gpr .x2) (off p.base derivedY)
      (original.gpr .x5) p.pLen p.qLen valid :=
    ⟨hv.fields .out (by decide), hv.fields .p (by decide), hv.fields .y (by decide),
      hv.fields .x (by decide), (hv.fields .pLen (by decide)).trans h.pLength,
      hv.fields .qLen (by decide), hmv⟩
  have hn := hsv'.nowrap
  have hp384 : p.pLen ≤ 384 := by omega_using [hl]
  have hpq : 0 < p.pLen ∧ 0 < p.qLen := by omega_using [hl]
  have hreg : v.rd = original.rd ∧ v.wr = original.wr := ⟨hkeep'.rd, hkeep'.wr⟩
  unfold seqs
  refine WP.seq (WP.mono (writeKey_ok hsv' hv.parent.x0 (by decide) hfields hpq.1 hpq.2 (by omega_using [hl])
    ⟨fun i hi => hparams.rd i (by rw [p.paramsLength]; exact hi), h.paramsOut⟩
    ⟨fun i hi => by
      rw [off_add]; exact scr_byte_rd hsv' (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hp384]),
     fun i hi j hj => scr_ne_out h.outSeparate (d := derivedY) (i := i)
      (by unfold deriveExtent derivedY usedBytes; omega_using [hi, hp384]) (by omega_using [hn]) j hj⟩
    ⟨fun i hi => hxs.rd i (by rw [p.xLength]; exact hi), h.xOut⟩
    (fun i hi => by rw [hreg.2]; exact h.outWrite i hi))
    fun w ⟨hw₁, hw₂, hw₃, hwf, hkw⟩ => ?_)
  have hwv : ∀ d, d + 8 ≤ deriveExtent → word w.mem p.base d = word v.mem p.base d := fun d hd =>
    Mem.readW_congr fun b hb => hwf _ (scr_ne_out h.outSeparate (d := d) (i := b) (by omega_using [hd, hb]) (by omega_using [hn]))
  refine WP.mono (result_ok (hsv'.congr hkw.wr) ((hkw.gpr .x0 (by decide)).trans hv.parent.x0) (by decide)
    ((hwv _ (by decide)).trans hmv)) fun t ⟨hret, hmem, hkt⟩ => ?_
  have hyfit : p.y < 256 ^ p.pLen :=
    Nat.lt_of_lt_of_le (VG.Proof.Dsa.powMod_lt _ _ (by omega_using [hp1])) hpf
  have hres : Spec.Dsa.deriveKeyBytes p.pLen p.qLen p.params p.x =
      if valid then some (p.params ++ p.yb ++ p.x) else none := by
    rw [p.derive_eq, ha, Bool.true_and, hvalid]
    unfold signingKeyAccepted
    rw [VG.Proof.Dsa.decodeBE_encodeBE hyfit]
    rfl
  have hlen : p.outLen = p.params.length + p.yb.length + p.x.length := by
    rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length, p.xLength]; unfold DeriveInput.outLen; omega_arith
  refine ⟨?_, ?_, ?_,
    ((hkeep'.trans hkw).trans hkt).mono (by decide)⟩
  · rw [hret]
    change BitVec.ofNat 64 valid.toNat = _
    rw [hres]
    cases valid <;> rfl
  · rw [hmem, hres]
    cases hvb : valid
    · apply bytesAt_zero_list
      intro i hi
      by_cases h1 : i < 2 * p.pLen + p.qLen
      · rw [hw₁ i h1, hvb]; rfl
      by_cases h2 : i < 3 * p.pLen + p.qLen
      · have := hw₂ (i - (2 * p.pLen + p.qLen)) (by omega_arith)
        rw [show 2 * p.pLen + p.qLen + (i - (2 * p.pLen + p.qLen)) = i by omega_arith, hvb] at this
        exact this
      · have := hw₃ (i - (3 * p.pLen + p.qLen)) (by unfold DeriveInput.outLen at hi; omega_arith)
        rw [show 3 * p.pLen + p.qLen + (i - (3 * p.pLen + p.qLen)) = i by omega_arith, hvb] at this
        exact this
    · simp only [↓reduceIte, Option.getD_some]
      rw [hlen]
      apply bytesAt_key
      · intro i hi
        rw [p.paramsLength] at hi
        rw [hw₁ i hi, hvb]
        simp only [↓reduceIte]
        exact hparams.val i (by rw [p.paramsLength]; exact hi)
      · intro i hi
        rw [VG.Proof.Dsa.encodeBE_length] at hi
        rw [p.paramsLength, hw₂ i hi, hvb]
        simp only [↓reduceIte]
        exact hyv i hi
      · intro i hi
        rw [p.xLength] at hi
        rw [p.paramsLength, VG.Proof.Dsa.encodeBE_length,
          show 2 * p.pLen + p.qLen + p.pLen = 3 * p.pLen + p.qLen by omega_arith, hw₃ i hi, hvb]
        simp only [↓reduceIte]
        exact hxs.val i (by rw [p.xLength]; exact hi)
  · intro x hx hout
    rw [hmem, hwf x hout]
    exact hframe' x hx

theorem deriveMain_ok (M : Mont) {p : DeriveInput} {s0 : State} (h : DerivePre p s0) :
    WP isa (Generate.deriveKey M.mm) s0 (DerivePost p s0) := by
  apply WP.assoc
  refine WP.seq (WP.mono (deriveShape_ok h) fun s hs => ?_)
  cases ha : p.accepted
  · refine WP.ite true ?_ (fun _ => deriveRejected_ok h hs ha) (fun h => Bool.noConfusion h)
    change some (s.gpr .x3 == (0#64)) = some true
    rw [hs.branch, ha]; rfl
  · refine WP.ite false ?_ (fun h => Bool.noConfusion h) (fun _ => deriveSuccess_ok M h hs ha)
    change some (s.gpr .x3 == (0#64)) = some false
    rw [hs.branch, ha]; rfl

end VG.Proof.Dsa.AArch64
