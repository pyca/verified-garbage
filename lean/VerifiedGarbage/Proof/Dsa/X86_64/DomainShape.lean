module
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeFrame
public import VerifiedGarbage.Proof.Dsa.DomainShape

import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizes
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import Mathlib.Tactic.Set

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
