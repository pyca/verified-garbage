module

public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeFrame
public import VerifiedGarbage.Proof.Dsa.DomainShape

import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeSizes
import VerifiedGarbage.Proof.Dsa.AArch64.ShapeTail
/-! # Public shape acceptance and early rejection in the DSA specification -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/DomainShape.lean`, which only this module imported.
section

/-! # Functional correctness of the public DSA domain-shape check -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

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
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
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
      (t.gpr .x3 == (0#64)) = !(shapeValid p q pLast qLast) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t := by
  have h : WP isa (.seq shapeSizes (.block shapeTail)) s (fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n (VG.Proof.Dsa.significant q).1) ∧
      word t.mem B Field.mask.offset = mask (shapeValid p q pLast qLast) ∧
      (t.gpr .x3 == (0#64)) = !(shapeValid p q pLast qLast) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t) := by
    refine WP.seq (WP.mono (shapeSizes_ok hs hdi hZ hpp hqp hpl hql hps hqs hp1 hp64 hq1 hq64)
      fun u ⟨hua, hum, huw, hfu, hku⟩ => ?_)
    have hudi := (hku.gpr .x0 (show Reg.x0 ∉ mmRegs by decide)).trans hdi
    refine WP.mono (shapeTail_ok (hs.congr hku.wr) hudi hZ
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
  exact h

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG

theorem decodeBE_last_parity (bs : List Byte) (hn : 0 < bs.length) :
    Spec.Dsa.decodeBE bs % 2 = (bs[bs.length - 1]'(by omega)).toNat % 2 := by
  have hne : bs ≠ [] := by intro h; simp only [h, List.length_nil, Nat.lt_irrefl] at hn
  have he := VG.Proof.Dsa.decodeBE_last_mod_two bs.dropLast (bs.getLast hne)
  rw [List.dropLast_concat_getLast hne, List.getLast_eq_getElem] at he
  exact he

def shapeAccepted (p q : List Byte) (hp : 0 < p.length) (hq : 0 < q.length) : Bool :=
  shapeValid p q (p[p.length - 1]'(by omega)) (q[q.length - 1]'(by omega))

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

end VG.Proof.Dsa.AArch64
