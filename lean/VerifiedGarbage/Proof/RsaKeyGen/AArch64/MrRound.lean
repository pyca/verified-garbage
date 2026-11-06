module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWit
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrExp
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTab
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail
import VerifiedGarbage.Proof.RsaKeyGen.Slots
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrLoop
public import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Bignum.Math

/-!
# A candidate on AArch64: one round of Miller–Rabin

A round takes one witness `b` from the next `8 w` octets (`wtOf`,
`passOf`): what it changes (`preRanges`, `roundRanges`), and `MrCtx` with a
new witness (`MrCtx.setB`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY sCnt sK)

/-- The octets of `rand` from `a`. -/
theorem Src.seg {s : State} {B : Addr} {Z : Nat} {rp : Addr} {r : List Byte} (h : Src s B Z rp r) {a n : Nat}
    (ha : a + n ≤ r.length) : Src s B Z (rp + BitVec.ofNat 64 a) (VG.Proof.RsaKeyGen.seg r a n) := by
  have hl : (VG.Proof.RsaKeyGen.seg r a n).length = n := by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [ha]
  have he : ∀ i, rp + BitVec.ofNat 64 a + BitVec.ofNat 64 i = rp + BitVec.ofNat 64 (a + i) := fun i => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [he]; exact h.rd (a + i) (by omega_using [ha, hl, hi])
  · rw [he, h.val (a + i) (by omega_using [ha, hl, hi])]
    simp only [VG.Proof.RsaKeyGen.seg, List.getElem_take, List.getElem_drop]
  · rw [he]; exact h.out (a + i) (by omega_using [ha, hl, hi])

/-- What the start of a round changes. -/
def preRanges (w : Nat) : List (Nat × Nat) :=
  witRanges w ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (slot w aB, 8 * (w + 2))] ++ tabRanges w

/-- What a round changes. -/
def roundRanges (w : Nat) : List (Nat × Nat) :=
  preRanges w ++ expRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

/-- Disjointness of a range from each of a list of literal ranges of a round. -/
tactic_template "rd_disj" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, roundRanges, preRanges,
    witRanges, expRanges, winRanges, tabRanges, List.cons_append, List.nil_append, slot, hdrBytes, aN, aX, aAcc,
    aTmp, aR2, aY, aXm, aB, aR1, aRm1, aT0, aE, kG, kFlag, kPlen, kV, kT0, sCnt, kBits, kT2, kWords, kT1, kUsed, kU,
    kI, kElen, kUni, kP, kStat, kChecks, kE, kRand, kLen, sK, kRandLen, kOut, kUsedP, sFn, sMinv]
  and_intros <;> omega_arith))

/-- The ranges of a list of literal ranges are `KMut`. -/
tactic_template "kmut" : tactic => `(tactic| first | hdr_disj | (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  and_intros <;> first | exact KMut.ofSlot _ _ _ | exact KMut.hdr (by decide)))

/-- `MrCtx` with a new witness. -/
theorem MrCtx.setB {s t : State} {B : Addr} {Z w c bm bm' : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, KMut r)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (dN : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN)
    (d1 : ∀ r ∈ rs, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1)
    (dm : ∀ r ∈ rs, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1)
    (hb : wv t.mem B (slot w aB) w = bm') : MrCtx t B Z w c bm' := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have e : ∀ {j : Nat}, j < 16 → slot w j + 8 * w ≤ Z := fun hj => by
    have := slot_lt (w := w) hj; omega_using [hZ, this]
  have e1 := e (show aR1 < 16 by decide)
  have em := e (show aRm1 < 16 by decide)
  have eN := e (show aN < 16 by decide)
  have hw1 := hc.ws.w1
  refine ⟨hc.ws.congr' hf hm k hr, ?_, ?_, hb, ?_, ?_⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by have := dN r hr; omega_using [hw1, this]) (by omega_using [hn, eN, hw1]),
      hf.word_eq (d := 8 * sMinv) dI (by simp only [sMinv] at *; have := hc.ws.h256; omega_using [])]
    exact hc.inv
  · rw [hf.wv_eq dN (by omega_using [hn, eN])]; exact hc.n
  · rw [hf.wv_eq d1 (by omega_using [hn, e1])]; exact hc.r1
  · rw [hf.wv_eq dm (by omega_using [hn, em])]; exact hc.rm1

/-- A round changes nothing from `aE` on. -/
theorem roundRanges_lt (w : Nat) : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  simp only [roundRanges, preRanges, witRanges, expRanges, winRanges, tabRanges, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [slot, hdrBytes, aX, aAcc, aTmp, aY, aXm, aB, aT0, aE, kG, kFlag, kPlen, kV, kT0, sCnt, kBits, kT2,
      kWords, kT1, kUsed, kU, kI, kElen, kUni, kP, kStat, sFn] <;> omega

/-- The witness of a round, and whether it passes. -/
abbrev wtOf (c w used : Nat) (r : List Byte) : Nat × Bool :=
  Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))

abbrev passOf (c w used : Nat) (r : List Byte) : Bool :=
  Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (wtOf c w used r).1

end VG.Proof.RsaKeyGen.AArch64
