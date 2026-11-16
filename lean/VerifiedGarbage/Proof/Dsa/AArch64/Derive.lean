module

public import VerifiedGarbage.Proof.Dsa.AArch64.KeygenEntry
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.AArch64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.AArch64.KeyPointers
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
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
import VerifiedGarbage.Proof.Bignum.AArch64.PubFail
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Dsa.AArch64.DeriveEntry`, which only this module used -/

section

/-! # AAPCS64 argument capture for DSA key derivation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def deriveFieldValues (original : State) (qlen B : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .x2
  | .q => original.gpr .x2 + original.gpr .x4
  | .g => original.gpr .x2 + original.gpr .x4 + qlen
  | .y => B + BitVec.ofNat 64 derivedY
  | .x => original.gpr .x5
  | .signature => 0
  | .nonce => 0
  | .digest => 0
  | .out => original.gpr .x0
  | .pLen => original.gpr .x4
  | .qLen => qlen
  | .digestLen => 0
  | .digestPrefixLen => 0
  | .mask => mask valid

abbrev deriveFields := Generate.deriveFields

def deriveFieldMem (mem : Mem) (B out p pl ql : Addr) : Mem :=
  ((((((((mem.writeW (off B Field.signature.offset) (0#64)).writeW (off B Field.nonce.offset) (0#64)).writeW
    (off B Field.digest.offset) (0#64)).writeW (off B Field.digestLen.offset) (0#64)).writeW
    (off B Field.out.offset) out).writeW (off B Field.p.offset) p).writeW
    (off B Field.pLen.offset) pl).writeW (off B Field.qLen.offset) ql)

theorem deriveFields_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block deriveFields) s fun t =>
      t.mem = deriveFieldMem s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x6) ∧ Keep [.x12] s t := by
  refine WP.keep [.x12] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  unfold deriveFields Generate.deriveFields
  brun [SignVerify.initial, h11, fieldAddress,
    field_enc .signature, field_enc .nonce, field_enc .digest, field_enc .digestLen,
    field_enc .out, field_enc .p, field_enc .pLen, field_enc .qLen,
    hw .signature, hw .nonce, hw .digest, hw .digestLen, hw .out, hw .p, hw .pLen, hw .qLen]
  rfl

theorem deriveTail_ok {s : State} {B : Addr} {Z : Nat}
    (hs : Scr s B Z) (h11 : s.gpr .x11 = B) (hZ : pWorkspace ≤ Z) :
    WP isa (.block [SignVerify.initial .x5 .x, movi .x3 derivedY,
      .add .x .x3 .x11 .x3, SignVerify.initial .x3 .y]) s fun t =>
      t.mem = (s.mem.writeW (off B Field.x.offset) (s.gpr .x5)).writeW (off B Field.y.offset)
        (B + BitVec.ofNat 64 derivedY) ∧ Keep [.x3] s t := by
  refine WP.keep [.x3] ?_ rfl rfl rfl
  have hw (f : Field) := hs.st (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 hZ)
  brun [SignVerify.initial, h11, fieldAddress, field_enc .x, field_enc .y, hw .x, hw .y]
  rfl

theorem deriveMoveScratch_ok (s : State) :
    WP isa (.block [mov .x11 .x7]) s fun t =>
      t.gpr .x11 = s.gpr .x7 ∧ t.mem = s.mem ∧ Keep [.x11] s t := by
  refine WP.mono (WP.keep [.x11] (Q := fun t => t.gpr .x11 = s.gpr .x7 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hp, hm⟩, hk⟩ => ⟨hp, hm, hk⟩
  brun []

theorem deriveEntry_ok {s0 : State} {B : Addr} (hs : Scr s0 B usedBytes) (h7 : s0.gpr .x7 = B) :
    WP isa (.block Generate.deriveEntry) s0 (KeygenEntryPost s0 B (deriveFieldValues s0 (s0.gpr .x6) B true)) := by
  unfold Generate.deriveEntry
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (deriveMoveScratch_ok s0) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [h7] at h11
  rw [WP.block_append_iff]
  have hreg (reg : Reg) (hne : reg ≠ .x11) : s1.gpr reg = s0.gpr reg := hk1.gpr reg (by simpa using hne)
  refine WP.mono (deriveFields_ok (hs.congr hk1.wr) h11 (by decide)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .x0 (by decide), hreg .x2 (by decide), hreg .x4 (by decide), hreg .x6 (by decide)] at hmem3
  have hk123 := hk1.trans hk3
  have h113 : s3.gpr .x11 = B := (hk3.gpr .x11 (by decide)).trans h11
  have hw3 (f : Field) : word s3.mem B f.offset =
      word (deriveFieldMem s1.mem B (s0.gpr .x0) (s0.gpr .x2) (s0.gpr .x4) (s0.gpr .x6)) B f.offset := by rw [hmem3]
  rw [WP.block_append_iff]
  refine WP.mono (keyPointers_ok (p := s0.gpr .x2) (pl := s0.gpr .x4) (ql := s0.gpr .x6) (hs.congr hk123.wr) h113 (by decide)
    ((hw3 .p).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl))
    ((hw3 .pLen).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl))
    ((hw3 .qLen).trans (by simp only [deriveFieldMem, word_fieldWrite]; rfl)))
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hk1234 := hk123.trans hk4
  have h114 : s4.gpr .x11 = B := (hk4.gpr .x11 (by decide)).trans h113
  have h5 : s4.gpr .x5 = s0.gpr .x5 := hk1234.gpr .x5 (by decide)
  refine WP.mono (deriveTail_ok (hs.congr hk1234.wr) h114 (by decide)) fun t ⟨hmem5, hk5⟩ => ?_
  rw [h5] at hmem5
  refine ⟨(hk5.gpr .x0 (by decide)).trans hdi4, ?_, ?_,
    ((hk1234.trans hk5).mono (by decide))⟩
  · intro f h1 h2
    rw [hmem5, hmem4, hmem3]
    cases f <;> first | exact absurd rfl h1 | exact absurd rfl h2 |
      (simp only [deriveFieldMem, keyPointerMem, word_fieldWrite, reduceCtorEq, reduceIte, deriveFieldValues]; try rfl)
  · intro x hx
    have hx' : ofs B x < 256 ∨ pWorkspace ≤ ofs B x := by omega_using [hx]
    rw [hmem5, hmem4, hmem3]
    simp only [deriveFieldMem, keyPointerMem, field_write_frame _ B _ _ x hx']
    rw [hmem1]

end VG.Proof.Dsa.AArch64

end

end

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

end VG.Proof.Dsa.AArch64
