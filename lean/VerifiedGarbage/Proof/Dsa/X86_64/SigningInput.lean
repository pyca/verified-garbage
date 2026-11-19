module

public import VerifiedGarbage.Proof.Dsa.X86_64.CoreSign
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.Save
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToAdditive
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeFrame
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.X86_64.ShapeSpec`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.SourceSlices`, which the modules that import this one used -/

section

/-! # Memory-safe component and digest slices of external DSA inputs -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem source_slice {s : State} {B p : Addr} {Z offset len : Nat} {bs : List Byte}
    (h : Src s B Z p bs) (hl : offset + len ≤ bs.length) :
    Src s B Z (p + BitVec.ofNat 64 offset) ((bs.drop offset).take len) := by
  have hlen : ((bs.drop offset).take len).length = len := by
    simp only [List.length_take, List.length_drop]
    omega_using [hl]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    rw [Offset.add_add]
    exact h.rd _ (by omega_using [hl, hi])
  · intro i hi
    rw [Offset.add_add, h.val _ (by omega_using [hl, hlen, hi])]
    simp only [List.getElem_take, List.getElem_drop]
  · intro i hi
    rw [hlen] at hi
    rw [Offset.add_add]
    exact h.out _ (by omega_using [hl, hi])

theorem source_take {s : State} {B p : Addr} {Z n : Nat} {bs : List Byte}
    (h : Src s B Z p bs) : Src s B Z p (bs.take n) := by
  have hlen : (bs.take n).length ≤ bs.length := by simp only [List.length_take]; omega_using []
  exact ⟨fun i hi => h.rd i (by omega_using [hlen, hi]),
    fun i hi => (h.val i (by omega_using [hlen, hi])).trans List.getElem_take.symm,
    fun i hi => h.out i (by omega_using [hlen, hi])⟩

structure PackedComponents (pLen qLen : Nat) where
  p : List Byte
  q : List Byte
  g : List Byte
  y : List Byte
  x : List Byte
  pLength : p.length = pLen
  qLength : q.length = qLen
  gLength : g.length = pLen
  yLength : y.length = pLen

/-- Slice lengths are independent of leading-zero encodings. -/
theorem component_length {bs : List Byte} {offset len : Nat} (h : offset + len ≤ bs.length) :
    ((bs.drop offset).take len).length = len := by
  simp only [List.length_take, List.length_drop]
  omega_using [h]

def packedComponents (pLen qLen : Nat) (key : List Byte) (hlen : 3 * pLen + qLen ≤ key.length) :
    PackedComponents pLen qLen where
  p := key.take pLen
  q := (key.drop pLen).take qLen
  g := (key.drop (pLen + qLen)).take pLen
  y := (key.drop (2 * pLen + qLen)).take pLen
  x := (key.drop (3 * pLen + qLen)).take qLen
  pLength := by simp only [List.length_take]; omega_using [hlen]
  qLength := component_length (by omega_using [hlen])
  gLength := component_length (by omega_using [hlen])
  yLength := component_length (by omega_using [hlen])

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.DomainShape`, which only this module used -/

section

/-! # Functional correctness of the public DSA domain-shape check -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

def shapeValid (p q : List Byte) (pLast qLast : Byte) : Bool :=
  decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) &&
    (decide (Spec.Dsa.supportedSizes (8 * (VG.Proof.Dsa.significant p).1)
      (8 * (VG.Proof.Dsa.significant q).1)) &&
      (decide (128 ≤ (VG.Proof.Dsa.significant q).2.toNat) &&
        decide (128 ≤ (VG.Proof.Dsa.significant p).2.toNat)))

theorem shapeValid_spec (p q : List Byte) (pLast qLast : Byte) :
    shapeValid p q pLast qLast = decide (
      Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
        (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ∧
      pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) := by
  unfold shapeValid
  rw [← Bool.decide_and, ← Bool.decide_and, ← Bool.decide_and]
  apply decide_eq_decide.mpr
  rw [VG.Proof.Dsa.supported_scans]
  constructor
  · rintro ⟨⟨hp, hq⟩, hs, htq, htp⟩
    exact ⟨⟨htp, htq, hs⟩, hp, hq⟩
  · rintro ⟨⟨htp, htq, hs⟩, hp, hq⟩
    exact ⟨⟨hp, hq⟩, hs, htq, htp⟩

theorem domainShape_ok {s : State} {B pp qp : Addr} {Z n : Nat} {p q : List Byte}
    {pLast qLast : Byte}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hp1 : 0 < p.length) (hp64 : p.length < 2 ^ 64) (hq1 : 0 < q.length) (hq64 : q.length < 2 ^ 64)
    (hplast : p[p.length - 1] = pLast) (hqlast : q[q.length - 1] = qLast)
    (hn : n < 2 ^ 64) (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n) :
    WP isa Checks.domainShape s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n (VG.Proof.Dsa.significant q).1) ∧
      word t.mem B Field.mask.offset = mask (shapeValid p q pLast qLast) ∧
      t.zf = some (!(shapeValid p q pLast qLast)) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t := by
  have h : WP isa (.seq shapeSizes (.block shapeTail)) s (fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n (VG.Proof.Dsa.significant q).1) ∧
      word t.mem B Field.mask.offset = mask (shapeValid p q pLast qLast) ∧
      t.zf = some (!(shapeValid p q pLast qLast)) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t) := by
    refine WP.seq (WP.mono (shapeSizes_ok hs hdi hZ hpp hqp hpl hql hps hqs hp1 hp64 hq1 hq64)
      fun u ⟨hua, hum, huw, hfu, hku⟩ => ?_)
    have hudi := (hku.gpr (show Reg.rdi ∉ mmRegs by decide)).trans hdi
    refine WP.mono (shapeTail_ok (hs.congr hku.2.2) hudi hZ
      ((shape_field hfu .p (by decide) (by decide)).trans hpp)
      ((shape_field hfu .q (by decide) (by decide)).trans hqp)
      ((shape_field hfu .pLen (by decide) (by decide)).trans hpl)
      ((shape_field hfu .qLen (by decide) (by decide)).trans hql)
      (shape_source hfu hku (Nat.le_trans (by decide) hZ) hps)
      (shape_source hfu hku (Nat.le_trans (by decide) hZ) hqs)
      hp1 hp64 hq1 hq64 hplast hqlast hn
      (Nat.lt_of_le_of_lt (VG.Proof.Dsa.significant_fits q) hq64)
      ((shape_field hfu .digestLen (by decide) (by decide)).trans hd) huw hua hum)
      fun t ⟨htw, htm, htz, hft, hkt⟩ => ?_
    exact ⟨htw, htm, htz, hfu.trans hft, (hku.trans hkt).mono (by decide)⟩
  unfold Checks.domainShape seqs
  refine WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ?_)
  refine WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ?_)
  refine WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ?_)
  refine WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ?_)
  refine WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => ?_)
  simpa only [seqs, widthChoice, shapeTail, oddCheck, oddCombine, shapeFinish,
    List.append_assoc, List.cons_append, List.nil_append] using h

end VG.Proof.Dsa.X86_64

end

end


/-! # Public shape acceptance and early rejection in the DSA specification -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG

theorem decodeBE_last_parity (bs : List Byte) (hn : 0 < bs.length) :
    Spec.Dsa.decodeBE bs % 2 = (bs[bs.length - 1]'(by omega_using [hn])).toNat % 2 := by
  have hne : bs ≠ [] := by intro h; simp only [h, List.length_nil, Nat.lt_irrefl] at hn
  have he := VG.Proof.Dsa.decodeBE_last_mod_two bs.dropLast (bs.getLast hne)
  rw [List.dropLast_concat_getLast hne, List.getLast_eq_getElem] at he
  exact he

def shapeAccepted (p q : List Byte) (hp : 0 < p.length) (hq : 0 < q.length) : Bool :=
  shapeValid p q (p[p.length - 1]'(by omega_using [hp])) (q[q.length - 1]'(by omega_using [hq]))

theorem shapeAccepted_spec (p q : List Byte) (hp : 0 < p.length) (hq : 0 < q.length) :
    shapeAccepted p q hp hq = decide (
      Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
        (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ∧
      Spec.Dsa.decodeBE p % 2 = 1 ∧ Spec.Dsa.decodeBE q % 2 = 1) := by
  unfold shapeAccepted
  rw [shapeValid_spec, ← decodeBE_last_parity p hp, ← decodeBE_last_parity q hq]

theorem shapeAccepted_false {p q : List Byte} {hp : 0 < p.length} {hq : 0 < q.length}
    (h : shapeAccepted p q hp hq = false) (g : Nat) :
    ¬ Spec.Dsa.parametersValid ⟨Spec.Dsa.decodeBE p, Spec.Dsa.decodeBE q, g⟩ := by
  rw [shapeAccepted_spec] at h
  intro hv
  have ht : decide (Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (Spec.Dsa.decodeBE p))
      (Spec.Dsa.bitLength (Spec.Dsa.decodeBE q)) ∧
      Spec.Dsa.decodeBE p % 2 = 1 ∧ Spec.Dsa.decodeBE q % 2 = 1) = true :=
    decide_eq_true ⟨hv.1, hv.2.1, hv.2.2.1⟩
  rw [h] at ht
  cases ht

theorem signBytes_invalid_shape {pLen qLen : Nat} {key nonce digest : List Byte}
    (h : ¬ Spec.Dsa.parametersValid (Spec.Dsa.privateKeyBytes pLen qLen key).params) :
    Spec.Dsa.signBytes pLen qLen key nonce digest = none := by
  unfold Spec.Dsa.signBytes
  split
  · rfl
  · simp only [h, decide_false, Bool.not_false, ↓reduceIte]

theorem verifyBytes_invalid_shape {pLen qLen : Nat} {key signature digest : List Byte}
    (h : ¬ Spec.Dsa.parametersValid (Spec.Dsa.publicKeyBytes pLen qLen key).params) :
    Spec.Dsa.verifyBytes pLen qLen key signature digest = false := by
  unfold Spec.Dsa.verifyBytes
  split
  · rfl
  · simp only [h, decide_false, Bool.false_and]

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.InitializedFields`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.VerifyEntry`, which this module and modules that import it used -/

section

/-! # Complete System V entry for DSA verification -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure VerifyEntryPost (original : State) (B digest digestLen : Addr) (t : State) : Prop where
  base : t.gpr .rdi = B
  p : word t.mem B Field.p.offset = original.gpr .rdi
  pLen : word t.mem B Field.pLen.offset = original.gpr .rdx
  qLen : word t.mem B Field.qLen.offset = original.gpr .rcx
  signature : word t.mem B Field.signature.offset = original.gpr .r8
  digest : word t.mem B Field.digest.offset = digest
  digestLen : word t.mem B Field.digestLen.offset = digestLen
  q : word t.mem B Field.q.offset = original.gpr .rdi + original.gpr .rdx
  g : word t.mem B Field.g.offset = original.gpr .rdi + original.gpr .rdx + original.gpr .rcx
  y : word t.mem B Field.y.offset = original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx
  x : word t.mem B Field.x.offset = original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx + original.gpr .rdx
  unused : word t.mem B Field.out.offset = 0 ∧ word t.mem B Field.nonce.offset = 0
  saved : ∀ i < 6, word t.mem B (8 * i) = original.gpr (saved.getD i .rax)
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.rax, .rdi, .r11] original t

theorem verifyEntry_ok {s0 : State} {B sp digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (hsp : s0.gpr .rsp = sp) (hZ : pWorkspace ≤ Z)
    (hr : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (s0.rd ++ s0.wr) (off sp (8 * j)) 8)
    (hsep : ∀ j, 1 ≤ j → j ≤ 3 → ∀ i < 8, Z ≤ ofs B (off sp (8 * j) + BitVec.ofNat 64 i))
    (hd : word s0.mem sp 8 = digest) (hdl : word s0.mem sp 16 = digestLen) (hb : word s0.mem sp 24 = B) :
    WP isa (.block SignVerify.verifyEntry) s0 (VerifyEntryPost s0 B digest digestLen) := by
  change WP isa (.block (([.mov .r11 (.mem (Crt.stk 3))] : List Instr) ++ SignVerify.save ++ verifyFields ++ SignVerify.keyPointers)) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (entryScratch_ok 3 hsp (hr 3 (by decide) (by decide)) hb) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (Nat.le_trans (by decide) hZ)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  have hr2 : ∀ j, 1 ≤ j → j ≤ 2 → InRegions (s2.rd ++ s2.wr) (off sp (8 * j)) 8 := by
    intro j hj1 hj2
    rw [hk12.2.1, hk12.2.2]
    exact hr j hj1 (by omega_using [hj2])
  have hstack (j : Nat) (hj1 : 1 ≤ j) (hj2 : j ≤ 2) : word s2.mem sp (8 * j) = word s0.mem sp (8 * j) := by
    rw [entry_stack_frame hf2 (Nat.le_trans (by decide) hZ) (hsep j hj1 (by omega_using [hj2])), hmem1]
  rw [WP.block_append_iff]
  refine WP.mono (verifyFields_ok (hs.congr hk12.2.2) ((hk2.gpr (by decide)).trans h11)
    ((hreg .rsp (by decide)).trans hsp) hZ hr2 (fun j h1 h2 => hsep j h1 (by omega_using [h2]))
    ((hstack 1 (by decide) (by decide)).trans hd) ((hstack 2 (by decide) (by decide)).trans hdl))
    fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .rcx (by decide), hreg .r8 (by decide)] at hmem3
  have hfields := verifyFieldMem_fields s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx) (s0.gpr .r8) digest digestLen
  rw [← hmem3] at hfields
  have hunused := verifyFieldMem_unused s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx) (s0.gpr .r8) digest digestLen
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s2.mem s3.mem := by rw [hmem3]; exact verifyFieldMem_frame _ _ _ _ _ _ _ _
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans ((hk2.gpr (by decide)).trans h11)
  refine WP.mono (keyPointers_ok (hs.congr hk123.2.2) h113 hZ hfields.1 hfields.2.1 hfields.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .rcx)
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .p (by decide)).trans hfields.1, (hsame .pLen (by decide)).trans hfields.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.1, (hsame .signature (by decide)).trans hfields.2.2.2.1,
    (hsame .digest (by decide)).trans hfields.2.2.2.2.1, (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2,
    hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2, ?_, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact ⟨(hsame .out (by decide)).trans hunused.1, (hsame .nonce (by decide)).trans hunused.2⟩
  · intro i hi
    exact ((hf4.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (entry_saved_frame hf3 hi)).trans
      ((hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
  · have hwide2 : Outside B 0 pWorkspace s0.mem s2.mem := by
      rw [← hmem1]
      exact hf2.mono (Nat.le_refl _) (by decide)
    exact (hwide2.trans (hf3.mono (by decide) (by decide))).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.X86_64

end

end

/-! ### `Dsa.X86_64.SignEntry`, which only this module used -/

section

/-! # Complete System V entry for a DSA signing attempt -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure SignEntryPost (original : State) (B qlen digest digestLen : Addr) (t : State) : Prop where
  base : t.gpr .rdi = B
  out : word t.mem B Field.out.offset = original.gpr .rdi
  p : word t.mem B Field.p.offset = original.gpr .rdx
  pLen : word t.mem B Field.pLen.offset = original.gpr .r8
  nonce : word t.mem B Field.nonce.offset = original.gpr .r9
  qLen : word t.mem B Field.qLen.offset = qlen
  digest : word t.mem B Field.digest.offset = digest
  digestLen : word t.mem B Field.digestLen.offset = digestLen
  q : word t.mem B Field.q.offset = original.gpr .rdx + original.gpr .r8
  g : word t.mem B Field.g.offset = original.gpr .rdx + original.gpr .r8 + qlen
  y : word t.mem B Field.y.offset = original.gpr .rdx + original.gpr .r8 + qlen + original.gpr .r8
  x : word t.mem B Field.x.offset = original.gpr .rdx + original.gpr .r8 + qlen + original.gpr .r8 + original.gpr .r8
  unused : word t.mem B Field.signature.offset = 0
  saved : ∀ i < 6, word t.mem B (8 * i) = original.gpr (saved.getD i .rax)
  frame : Outside B 0 pWorkspace original.mem t.mem
  keep : Keep [.rax, .rdi, .r11] original t

theorem signEntry_ok {s0 : State} {B sp qlen digest digestLen : Addr} {Z : Nat}
    (hs : Scr s0 B Z) (hsp : s0.gpr .rsp = sp) (hZ : pWorkspace ≤ Z)
    (hr : ∀ j, 1 ≤ j → j ≤ 4 → InRegions (s0.rd ++ s0.wr) (off sp (8 * j)) 8)
    (hsep : ∀ j, 1 ≤ j → j ≤ 4 → ∀ i < 8, Z ≤ ofs B (off sp (8 * j) + BitVec.ofNat 64 i))
    (hq : word s0.mem sp 8 = qlen) (hd : word s0.mem sp 16 = digest)
    (hdl : word s0.mem sp 24 = digestLen) (hb : word s0.mem sp 32 = B) :
    WP isa (.block SignVerify.signEntry) s0 (SignEntryPost s0 B qlen digest digestLen) := by
  change WP isa (.block (([.mov .r11 (.mem (Crt.stk 4))] : List Instr) ++ SignVerify.save ++ signFields ++ SignVerify.keyPointers)) s0 _
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (entryScratch_ok 4 hsp (hr 4 (by decide) (by decide)) hb) fun s1 ⟨h11, hmem1, hk1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (hs.congr hk1.2.2) h11 (Nat.le_trans (by decide) hZ)) fun s2 ⟨hsaved, hf2, hk2⟩ => ?_
  have hk12 := hk1.trans hk2
  have hreg (reg : Reg) (hne : reg ≠ .r11) : s2.gpr reg = s0.gpr reg := hk12.gpr (by simpa using hne)
  have hr2 : ∀ j, 1 ≤ j → j ≤ 3 → InRegions (s2.rd ++ s2.wr) (off sp (8 * j)) 8 := by
    intro j hj1 hj3
    rw [hk12.2.1, hk12.2.2]
    exact hr j hj1 (by omega_using [hj3])
  have hstack (j : Nat) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) : word s2.mem sp (8 * j) = word s0.mem sp (8 * j) := by
    rw [entry_stack_frame hf2 (Nat.le_trans (by decide) hZ) (hsep j hj1 (by omega_using [hj3])), hmem1]
  rw [WP.block_append_iff]
  refine WP.mono (signFields_ok (hs.congr hk12.2.2) ((hk2.gpr (by decide)).trans h11)
    ((hreg .rsp (by decide)).trans hsp) hZ hr2 (fun j h1 h3 => hsep j h1 (by omega_using [h3]))
    ((hstack 1 (by decide) (by decide)).trans hq) ((hstack 2 (by decide) (by decide)).trans hd)
    ((hstack 3 (by decide) (by decide)).trans hdl)) fun s3 ⟨hmem3, hk3⟩ => ?_
  rw [hreg .rdi (by decide), hreg .rdx (by decide), hreg .r8 (by decide), hreg .r9 (by decide)] at hmem3
  have hfields := signFieldMem_fields s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .r8) (s0.gpr .r9) qlen digest digestLen
  rw [← hmem3] at hfields
  have hunused := signFieldMem_unused s2.mem B (s0.gpr .rdi) (s0.gpr .rdx) (s0.gpr .r8) (s0.gpr .r9) qlen digest digestLen
  rw [← hmem3] at hunused
  have hf3 : Outside B 256 (pWorkspace - 256) s2.mem s3.mem := by rw [hmem3]; exact signFieldMem_frame _ _ _ _ _ _ _ _ _
  have hk123 := hk12.trans hk3
  have h113 : s3.gpr .r11 = B := (hk3.gpr (by decide)).trans ((hk2.gpr (by decide)).trans h11)
  refine WP.mono (keyPointers_ok (hs.congr hk123.2.2) h113 hZ hfields.2.1 hfields.2.2.1 hfields.2.2.2.2.1)
    fun s4 ⟨hmem4, hdi4, hk4⟩ => ?_
  have hptr := keyPointerMem_fields s3.mem B (s0.gpr .rdx) (s0.gpr .r8) qlen
  rw [← hmem4] at hptr
  have hf4 : Outside B 264 32 s3.mem s4.mem := by rw [hmem4]; exact keyPointerMem_frame _ _ _ _ _
  have hsame (f : Field) (hsep : f.offset + 8 ≤ 264 ∨ 296 ≤ f.offset) :
      word s4.mem B f.offset = word s3.mem B f.offset :=
    hf4.word hsep (Nat.le_trans (VG.Proof.Dsa.field_bounds f).2 (by decide))
  refine ⟨hdi4, (hsame .out (by decide)).trans hfields.1, (hsame .p (by decide)).trans hfields.2.1,
    (hsame .pLen (by decide)).trans hfields.2.2.1, (hsame .nonce (by decide)).trans hfields.2.2.2.1,
    (hsame .qLen (by decide)).trans hfields.2.2.2.2.1, (hsame .digest (by decide)).trans hfields.2.2.2.2.2.1,
    (hsame .digestLen (by decide)).trans hfields.2.2.2.2.2.2, hptr.1, hptr.2.1, hptr.2.2.1, hptr.2.2.2,
    ?_, ?_, ?_, (hk123.trans hk4).mono (by decide)⟩
  · exact (hsame .signature (by decide)).trans hunused
  · intro i hi
    exact ((hf4.word (Or.inl (by omega_using [hi])) (by omega_using [hi])).trans (entry_saved_frame hf3 hi)).trans
      ((hsaved i hi).trans (hk1.gpr (by simpa using saved_ne_r11 hi)))
  · have hwide2 : Outside B 0 pWorkspace s0.mem s2.mem := by
      rw [← hmem1]
      exact hf2.mono (Nat.le_refl _) (by decide)
    exact (hwide2.trans (hf3.mono (by decide) (by decide))).trans (hf4.mono (by decide) (by decide))

end VG.Proof.Dsa.X86_64

end

end


/-! # Every saved argument has a defined value after the public shape check -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Dsa.Layout
open VG.Proof.Bignum VG.Proof.Bignum.X86_64

def signFieldValues (original : State) (qlen digest digestLen prefixLen : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .rdx
  | .q => original.gpr .rdx + original.gpr .r8
  | .g => original.gpr .rdx + original.gpr .r8 + qlen
  | .y => original.gpr .rdx + original.gpr .r8 + qlen + original.gpr .r8
  | .x => original.gpr .rdx + original.gpr .r8 + qlen + original.gpr .r8 + original.gpr .r8
  | .signature => 0
  | .nonce => original.gpr .r9
  | .digest => digest
  | .out => original.gpr .rdi
  | .pLen => original.gpr .r8
  | .qLen => qlen
  | .digestLen => digestLen
  | .digestPrefixLen => prefixLen
  | .mask => mask valid

def verifyFieldValues (original : State) (digest digestLen prefixLen : Addr) (valid : Bool) : Field → Addr
  | .p => original.gpr .rdi
  | .q => original.gpr .rdi + original.gpr .rdx
  | .g => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx
  | .y => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx
  | .x => original.gpr .rdi + original.gpr .rdx + original.gpr .rcx + original.gpr .rdx + original.gpr .rdx
  | .signature => original.gpr .r8
  | .nonce => 0
  | .digest => digest
  | .out => 0
  | .pLen => original.gpr .rdx
  | .qLen => original.gpr .rcx
  | .digestLen => digestLen
  | .digestPrefixLen => prefixLen
  | .mask => mask valid

theorem SignEntryPost.shapeFields {original s t : State} {B qlen digest digestLen prefixLen : Addr} {valid : Bool}
    (h : SignEntryPost original B qlen digest digestLen s)
    (hf : Frm B shapeRanges s.mem t.mem)
    (hp : word t.mem B Field.digestPrefixLen.offset = prefixLen)
    (hm : word t.mem B Field.mask.offset = mask valid) :
    ∀ f, word t.mem B f.offset = signFieldValues original qlen digest digestLen prefixLen valid f := by
  intro f
  cases f
  case digestPrefixLen => exact hp
  case mask => exact hm
  case p =>
    exact (shape_field hf .p (by decide) (by decide)).trans h.p
  case q =>
    exact (shape_field hf .q (by decide) (by decide)).trans h.q
  case g =>
    exact (shape_field hf .g (by decide) (by decide)).trans h.g
  case y =>
    exact (shape_field hf .y (by decide) (by decide)).trans h.y
  case x =>
    exact (shape_field hf .x (by decide) (by decide)).trans h.x
  case signature =>
    exact (shape_field hf .signature (by decide) (by decide)).trans h.unused
  case nonce =>
    exact (shape_field hf .nonce (by decide) (by decide)).trans h.nonce
  case digest =>
    exact (shape_field hf .digest (by decide) (by decide)).trans h.digest
  case out =>
    exact (shape_field hf .out (by decide) (by decide)).trans h.out
  case pLen =>
    exact (shape_field hf .pLen (by decide) (by decide)).trans h.pLen
  case qLen =>
    exact (shape_field hf .qLen (by decide) (by decide)).trans h.qLen
  case digestLen =>
    exact (shape_field hf .digestLen (by decide) (by decide)).trans h.digestLen

theorem VerifyEntryPost.shapeFields {original s t : State} {B digest digestLen prefixLen : Addr} {valid : Bool}
    (h : VerifyEntryPost original B digest digestLen s)
    (hf : Frm B shapeRanges s.mem t.mem)
    (hp : word t.mem B Field.digestPrefixLen.offset = prefixLen)
    (hm : word t.mem B Field.mask.offset = mask valid) :
    ∀ f, word t.mem B f.offset = verifyFieldValues original digest digestLen prefixLen valid f := by
  intro f
  cases f
  case digestPrefixLen => exact hp
  case mask => exact hm
  case p =>
    exact (shape_field hf .p (by decide) (by decide)).trans h.p
  case q =>
    exact (shape_field hf .q (by decide) (by decide)).trans h.q
  case g =>
    exact (shape_field hf .g (by decide) (by decide)).trans h.g
  case y =>
    exact (shape_field hf .y (by decide) (by decide)).trans h.y
  case x =>
    exact (shape_field hf .x (by decide) (by decide)).trans h.x
  case signature =>
    exact (shape_field hf .signature (by decide) (by decide)).trans h.signature
  case nonce =>
    exact (shape_field hf .nonce (by decide) (by decide)).trans h.unused.2
  case digest =>
    exact (shape_field hf .digest (by decide) (by decide)).trans h.digest
  case out =>
    exact (shape_field hf .out (by decide) (by decide)).trans h.unused.1
  case pLen =>
    exact (shape_field hf .pLen (by decide) (by decide)).trans h.pLen
  case qLen =>
    exact (shape_field hf .qLen (by decide) (by decide)).trans h.qLen
  case digestLen =>
    exact (shape_field hf .digestLen (by decide) (by decide)).trans h.digestLen

end VG.Proof.Dsa.X86_64

end

end

/-! # External input layout for the complete DSA signing program -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure SigningInput where
  base : Addr
  digestPointer : Addr
  pLen : Nat
  qLen : Nat
  key : List Byte
  nonce : List Byte
  digest : List Byte
  lengths : Spec.Dsa.lengthsValid pLen qLen
  keyLength : key.length = 3 * pLen + 2 * qLen
  nonceLength : nonce.length = qLen
  digestBound : digest.length < 2 ^ 64

def SigningInput.components (p : SigningInput) : PackedComponents p.pLen p.qLen :=
  packedComponents p.pLen p.qLen p.key (by rw [p.keyLength]; omega_using [])

abbrev SigningInput.prefixLength (p : SigningInput) : Nat :=
  min p.digest.length (VG.Proof.Dsa.significant p.components.q).1

abbrev SigningInput.accepted (p : SigningInput) : Bool :=
  shapeAccepted p.components.p p.components.q
    (by rw [p.components.pLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this])
    (by rw [p.components.qLength]; have := p.lengths; unfold Spec.Dsa.lengthsValid at this; omega_using [this])

def SigningInput.values (p : SigningInput) : SignValues :=
  ⟨p.components.g, p.nonce, p.components.x, p.digest.take (VG.Proof.Dsa.significant p.components.q).1⟩

structure SigningPre (p : SigningInput) (s : State) : Prop where
  scratch : Scr s p.base usedBytes
  pLength : s.gpr .r8 = BitVec.ofNat 64 p.pLen
  stackRead : ∀ j, 1 ≤ j → j ≤ 4 → InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) (8 * j)) 8
  stackSeparate : ∀ j, 1 ≤ j → j ≤ 4 → ∀ i < 8,
    usedBytes ≤ ofs p.base (off (s.gpr .rsp) (8 * j) + BitVec.ofNat 64 i)
  qLength : word s.mem (s.gpr .rsp) 8 = BitVec.ofNat 64 p.qLen
  digestPointer : word s.mem (s.gpr .rsp) 16 = p.digestPointer
  digestLength : word s.mem (s.gpr .rsp) 24 = BitVec.ofNat 64 p.digest.length
  base : word s.mem (s.gpr .rsp) 32 = p.base
  keySource : Src s p.base usedBytes (s.gpr .rdx) p.key
  nonceSource : Src s p.base usedBytes (s.gpr .r9) p.nonce
  digestSource : Src s p.base usedBytes p.digestPointer p.digest
  writable : ∀ i < 2 * p.qLen, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 i) 1
  separate : ∀ i < 2 * p.qLen, usedBytes ≤ ofs p.base (s.gpr .rdi + BitVec.ofNat 64 i)

def SigningInput.layout (p : SigningInput) (original : State) (hp : original.gpr .r8 = BitVec.ofNat 64 p.pLen) : ExecutionLayout where
  base := p.base
  pLen := p.pLen
  qLen := p.qLen
  modulus := Spec.Dsa.decodeBE p.components.p
  subgroup := Spec.Dsa.decodeBE p.components.q
  pInverse := 0
  qInverse := 0
  fields := signFieldValues original (BitVec.ofNat 64 p.qLen) p.digestPointer
    (BitVec.ofNat 64 p.digest.length) (BitVec.ofNat 64 p.prefixLength) p.accepted
  lengths := p.lengths
  pLength := hp
  qLength := rfl

end VG.Proof.Dsa.X86_64
