module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Ffdh.WordPred
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-!
# `vg_ffdh_check_domain` on AArch64: its own pieces

`p − 1` into the outer workspace's array `aX` (`Pa.pMinus1`), and the checks
of q's range in the inner workspace (`In.qrange`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave zeroArr copyArr)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem Outer.good {t : State} {B : Addr} {Z w : Nat} (h : Outer t B Z w) :
    Good t B Z w (word t.mem B (8 * sMinv)) ∧ slot w 8 ≤ Z :=
  ⟨⟨h.scr, h.x0, ⟨h.hw, rfl, h.harr⟩⟩, by have := h.room; unfold inner at this; omega_arith⟩

/-- `p − 1`'s first step: the outer array `aX` cleared. -/
theorem Pa.zeroX {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) :
    WP isa (zeroArr aX) t (Pa D mi) := by
  have hO := h.outer
  have hb := h.1
  have ew := hb.ew
  have := hb.k2
  obtain ⟨hg, hZ⟩ := hO.good
  have hsX := slot_le (w := D.w) (show aX < 8 by decide)
  have hX0 := hdr_lt_slot D.w aX (show 31 < 32 by decide)
  exact WP.mono (zeroArr_ok hg hZ (by omega_arith) (show aX < 8 by decide)) fun t₁ ⟨_, ho₁, k₁⟩ =>
    h.outside (o := slot D.w aX) (n := 8 * (D.w + 2)) (by omega_arith) (by unfold inner; omega_arith) ho₁ k₁.rd k₁.wr
      ((k₁.gpr .x0 (by decide)).trans h.2.2.2.2.2.2)

/-- `p − 1`'s second step: the load's registers, and the load. -/
theorem Pa.ldX {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) :
    WP isa (.block [ldh .x1 sDom, ldh .x2 sK, ldh .x8 (sArr aX)]) t fun u => (u.gpr .x1 = D.dp ∧
      u.gpr .x2 = BitVec.ofNat 64 D.k ∧ u.gpr .x8 = off D.B (slot D.w aX)) ∧
      WP isa loadBE u fun v => v.gpr .x0 = D.B ∧ v.gpr .x8 = off D.B (slot D.w aX) := by
  have hO := h.outer
  have hb := h.1
  have hn := hb.scr.nowrap
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  have hsX := slot_le (w := D.w) (show aX < 8 by decide)
  have hroom := hb.room
  have hiZ : inner D.w + slot D.w 8 ≤ D.Z := by unfold tabBytes32 at hroom; omega_arith
  refine WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun u => u.gpr .x1 = D.dp ∧
      u.gpr .x2 = BitVec.ofNat 64 D.k ∧ u.gpr .x8 = off D.B (slot D.w aX) ∧ u.mem = t.mem)
    (by brun [hO.x0, hdr_enc (show sDom < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (sArr_lt (show aX < 8 by decide)), hO.ld (show sDom < 32 by decide), hO.ld (show sK < 32 by decide),
      hO.ld (sArr_lt (show aX < 8 by decide)), h.2.2.2.2.1.get (i := sDom) (v := D.dp) (by simp),
      h.2.2.2.2.1.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp), hO.harr aX (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun u ⟨⟨h1, h2, h8, hm⟩, k⟩ => ⟨⟨h1, h2, h8⟩, ?_⟩
  have hsrc : Src u D.B D.Z D.dp (D.dom.take D.k) := (hb.dom.take D.k).congrK (by rw [hm]; exact InScr.refl _ _ _) k
  exact WP.mono (loadBE_ok (bs := D.dom.take D.k) (hb.scr.congr k.wr) h1 h2 h8 hb.plen
    (by omega_arith) (by omega_arith) rfl (by omega_arith) (fun i hi => hsrc.rd i (by rw [hb.plen]; exact hi))
    (fun i hi => hsrc.val i _) (fun i hi => Or.inr (by have := hsrc.out i (by rw [hb.plen]; exact hi); omega_arith)))
    fun v ⟨_, _, k'⟩ => ⟨(k'.gpr .x0 (by decide)).trans ((k.gpr .x0 (by decide)).trans hO.x0),
      (k'.gpr .x8 (by decide)).trans h8⟩

/-- `p − 1` into the outer array `aX`. -/
theorem Pa.pMinus1 {D : FD} {mi : BitVec 64} {t : State} (h : Pa D mi t) :
    WP isa (seqs CheckDomain.pMinus1) t fun u => Pa D mi u ∧
      wv u.mem D.B (slot D.w aX) D.w = D.P - 1 ∧ (∀ i < 32, word u.mem D.B (8 * i) = word t.mem D.B (8 * i)) ∧
      KX t u := by
  have hO := h.outer
  have hb := h.1
  have hs := h.2.2.2.2.1
  have hn := hb.scr.nowrap
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  obtain ⟨hg, hZ⟩ := hO.good
  have hsX := slot_le (w := D.w) (show aX < 8 by decide)
  have hX0 := hdr_lt_slot D.w aX (show 31 < 32 by decide)
  have hroom := hb.room
  have hiZ : inner D.w + slot D.w 8 ≤ D.Z := by unfold tabBytes32 at hroom; omega_arith
  unfold CheckDomain.pMinus1
  simp only [seqs]
  -- Zeros.
  refine WP.seq (WP.mono (zeroArr_ok hg hZ (by omega_arith) (show aX < 8 by decide)) fun t₁ ⟨_, ho₁, k₁⟩ => ?_)
  have h₁ := h.outside (o := slot D.w aX) (n := 8 * (D.w + 2)) (by omega_arith) (by unfold inner; omega_arith) ho₁ k₁.rd k₁.wr
    ((k₁.gpr .x0 (by decide)).trans h.2.2.2.2.2.2)
  have hO₁ := h₁.outer
  have hW₁ : ∀ i < 32, word t₁.mem D.B (8 * i) = word t.mem D.B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by omega_arith)) (by omega_arith)
  -- The load's registers.
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun u => u.gpr .x1 = D.dp ∧
      u.gpr .x2 = BitVec.ofNat 64 D.k ∧ u.gpr .x8 = off D.B (slot D.w aX) ∧ u.mem = t₁.mem)
    (by brun [hO₁.x0, hdr_enc (show sDom < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (sArr_lt (show aX < 8 by decide)), hO₁.ld (show sDom < 32 by decide), hO₁.ld (show sK < 32 by decide),
      hO₁.ld (sArr_lt (show aX < 8 by decide)), h₁.2.2.2.2.1.get (i := sDom) (v := D.dp) (by simp),
      h₁.2.2.2.2.1.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp), hO₁.harr aX (by decide)])
    (by decide) (by decide) (by decide +kernel)) fun t₂ ⟨⟨h1₂, h2₂, h8₂, hm₂⟩, k₂⟩ => ?_)
  have hsrc : Src t₂ D.B D.Z D.dp (D.dom.take D.k) := (hb.dom.take D.k).congrK
    (by rw [hm₂]; exact (InScr.of_outside ho₁ (by omega_arith))) (k₁.trans k₂)
  -- p.
  refine WP.seq (WP.mono (loadBE_ok (bs := D.dom.take D.k) (hb.scr.congr (k₁.trans k₂).wr) h1₂ h2₂ h8₂ hb.plen
    (by omega_arith) (by omega_arith) rfl (by omega_arith) (fun i hi => hsrc.rd i (by rw [hb.plen]; exact hi))
    (fun i hi => hsrc.val i _) (fun i hi => Or.inr (by have := hsrc.out i (by rw [hb.plen]; exact hi); omega_arith)))
    fun t₃ ⟨hP₃, ho₃, k₃⟩ => ?_)
  have h8₃ : t₃.gpr .x8 = off D.B (slot D.w aX) := (k₃.gpr .x8 (by decide)).trans h8₂
  have ho₃' : Outside D.B (slot D.w aX) (8 * (D.w + 2)) t₂.mem t₃.mem := ho₃.mono (by omega_arith) (by omega_arith)
  have h₃ := h₁.outside (o := slot D.w aX) (n := 8 * (D.w + 2)) (by omega_arith) (by unfold inner; omega_arith)
    (by rw [hm₂] at ho₃'; exact ho₃') (k₂.trans k₃).rd (k₂.trans k₃).wr
    ((k₃.gpr .x0 (by decide)).trans ((k₂.gpr .x0 (by decide)).trans hO₁.x0))
  have hO₃ := h₃.outer
  have hodd : wv t₃.mem D.B (slot D.w aX) D.w % 2 = 1 := by
    rw [hP₃]; exact (valid_facts h.2.2.2.2.2.1 hb.k1).1
  -- Less one.
  refine WP.mono (WP.keep [.x3, .x8] (Q := fun u => u.mem = t₃.mem.writeW (off D.B (slot D.w aX))
      (word t₃.mem D.B (slot D.w aX) - 1))
    (by brun [h8₃, hO₃.scr.ld (show slot D.w aX + 8 ≤ D.Z by omega_arith),
      hO₃.scr.st (show slot D.w aX + 8 ≤ D.Z by omega_arith)]; rfl)
    (by decide) (by decide) (by decide +kernel)) fun u ⟨hm, k⟩ => ?_
  have o := writeW_outside t₃.mem D.B (d := slot D.w aX) (word t₃.mem D.B (slot D.w aX) - 1) (by omega_arith)
  rw [← hm] at o
  refine ⟨h₃.outside (by omega_arith) (by unfold inner; omega_arith) (o.mono (by omega_arith) (by omega_arith)) k.rd k.wr
    ((k.gpr .x0 (by decide)).trans hO₃.x0), by rw [hm, wv_dec _ _ (by omega_arith) hodd (by omega_arith), hP₃], fun i hi => ?_,
    (((k₁.trans k₂).trans k₃).trans k).mono (by decide)⟩
  rw [o.word (Or.inl (by omega_arith)) (by omega_arith), ho₃.word (Or.inl (by omega_arith)) (by omega_arith), hm₂, hW₁ i hi]

theorem bit_and (p q : Prop) [Decidable p] [Decidable q] : bit p &&& bit q = bit (p ∧ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem stepR_F (w : Nat) : StepR w (8 * sF, 8) := by
  have := hdr_lt_slot w 0 (show sF < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  have := slot_le (w := w) (show aN < 8 by decide)
  have := hdr_lt_slot w aN (show sF < 32 by decide)
  have := hdr_lt_slot w aOne (show sF < 32 by decide)
  have := hdr_lt_slot w 8 (show sF < 32 by decide)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [sF, sFn] at * <;> omega_arith

/-- `x9` into the header slot `sF`. -/
theorem stFlag_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx) :
    WP isa (.block [sth .x9 sF]) t fun u => u.mem = t.mem.writeW (off G (8 * sF)) (t.gpr .x9) ∧ Keep [] t u := by
  have h8 := hdr_lt_slot w 8 (show sF < 32 by decide)
  exact WP.keep [] (Q := fun u => u.mem = t.mem.writeW (off G (8 * sF)) (t.gpr .x9))
    (by brun [hg.x0, hdr_enc (show sF < 32 by decide), hg.scr.st (show 8 * sF + 8 ≤ Zx by omega_arith)]) rfl rfl rfl

/-- `andF`. -/
theorem andFlag_ok {t : State} {G : Addr} {Zx w : Nat} {mi : BitVec 64} (hg : Good t G Zx w mi) (hZ : slot w 8 ≤ Zx) :
    WP isa (.block andF) t fun u => (u.gpr .x9 = t.gpr .x9 &&& word t.mem G (8 * sF) ∧
      u.mem = t.mem.writeW (off G (8 * sF)) (t.gpr .x9 &&& word t.mem G (8 * sF))) ∧ Keep [.x3, .x9] t u := by
  have h8 := hdr_lt_slot w 8 (show sF < 32 by decide)
  refine WP.keep [.x3, .x9] ?_ (by decide) (by decide) (by decide +kernel)
  unfold andF
  brun [hg.x0, hdr_enc (show sF < 32 by decide), hg.scr.ld (show 8 * sF + 8 ≤ Zx by omega_arith),
    hg.scr.st (show 8 * sF + 8 ≤ Zx by omega_arith)]

/-- `x9` into the inner header's `sF`. -/
theorem In.stFlag {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    WP isa (.block [sth .x9 sF]) t fun u => In D mi u ∧ u.gpr .x9 = t.gpr .x9 ∧
      word u.mem (off D.B (inner D.w)) (8 * sF) = t.gpr .x9 ∧
      Outside (off D.B (inner D.w)) (8 * sF) 8 t.mem u.mem ∧ KX t u := by
  have hg := h.2.1.good
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot D.w 8 (show sF < 32 by decide)
  refine WP.mono (stFlag_ok hg (Nat.le_refl _)) fun u ⟨hm, k⟩ => ?_
  have o := writeW_outside t.mem (off D.B (inner D.w)) (d := 8 * sF) (t.gpr .x9) (by omega_arith)
  rw [← hm] at o
  exact ⟨h.step (rs := [(8 * sF, 8)]) (Frm.of_outside o (by simp)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact stepR_F _) k.rd k.wr (k.gpr .x0 (by decide)), k.gpr .x9 (by decide),
    by rw [hm]; exact word_writeW_self _ _ _ _, o, k.mono (by decide)⟩

/-- `andF`, in the inner workspace. -/
theorem In.andFlag {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    WP isa (.block andF) t fun u => In D mi u ∧
      u.gpr .x9 = t.gpr .x9 &&& word t.mem (off D.B (inner D.w)) (8 * sF) ∧
      word u.mem (off D.B (inner D.w)) (8 * sF) = u.gpr .x9 ∧ Outside (off D.B (inner D.w)) (8 * sF) 8 t.mem u.mem ∧
      KX t u := by
  have hg := h.2.1.good
  have hn := hg.scr.nowrap
  have h8 := hdr_lt_slot D.w 8 (show sF < 32 by decide)
  refine WP.mono (andFlag_ok hg (Nat.le_refl _)) fun u ⟨⟨h9, hm⟩, k⟩ => ?_
  have o := writeW_outside t.mem (off D.B (inner D.w)) (d := 8 * sF)
    (t.gpr .x9 &&& word t.mem (off D.B (inner D.w)) (8 * sF)) (by omega_arith)
  rw [← hm] at o
  exact ⟨h.step (rs := [(8 * sF, 8)]) (Frm.of_outside o (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact stepR_F _) k.rd k.wr (k.gpr .x0 (by decide)), h9,
    by rw [hm, h9]; exact word_writeW_self _ _ _ _, o, k.mono (by decide)⟩

/-- q's range: odd, above 1, and below `p − 1`. -/
theorem In.qrange {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) {Q : Nat}
    (hQ : wv t.mem (off D.B (inner D.w)) (slot D.w aXm) D.w = Q) :
    WP isa (seqs (isOdd aXm ++ ([.block [sth .x9 sF]] : List (Prog isa)) ++ gt1 aXm ++ ([.block andF] : List (Prog isa)) ++ ltP aXm ++ ([.block andF] : List (Prog isa)))) t
      fun u => (In D mi u ∧ u.gpr .x9 = bit (Q % 2 = 1 ∧ 1 < Q ∧ 2 * (Q / 2) + 1 < D.P)) ∧ KX t u := by
  have hb := h.1
  have ew := hb.ew
  have := hb.k1
  have := hb.k2
  have hg := h.2.1.good
  have hv := h.2.2.1
  simp only [List.append_assoc, List.singleton_append]
  refine wp_seqs_append (by simp [isOdd]) (by simp) (WP.mono (isOdd_ok hg (Nat.le_refl _) (show 1 ≤ D.w by omega_arith)
    (show aXm < 8 by decide)) fun t₁ ⟨h9₁, hm₁, k₁⟩ => ?_)
  have h₁ := h.keep hm₁ k₁ (by decide)
  refine wp_seqs_cons (by simp [gt1, ltArr, cmpArr]) (WP.mono h₁.stFlag fun t₂ ⟨h₂, h9₂, hF₂, ho₂, k₂⟩ => ?_)
  refine wp_seqs_append (by simp [gt1, ltArr, cmpArr]) (by simp) (WP.mono (ltArr_ok h₂.2.1.good (Nat.le_refl _)
    (show 1 ≤ D.w by omega_arith) (show D.w < 2 ^ 31 by omega_arith) (show aOne < 8 by decide) (show aXm < 8 by decide))
    fun t₃ ⟨h9₃, hm₃, k₃⟩ => ?_)
  have h₃ := h₂.keep hm₃ k₃ (by decide)
  refine wp_seqs_cons (by simp [ltP, copyArr]) (WP.mono h₃.andFlag fun t₄ ⟨h₄, h9₄, hF₄, ho₄, k₄⟩ => ?_)
  refine wp_seqs_append (by simp [ltP, copyArr]) (by simp) (WP.mono (ltP_ok h₄.2.1.good (Nat.le_refl _)
    (show 1 ≤ D.w by omega_arith) (show D.w < 2 ^ 31 by omega_arith) (show aXm < 8 by decide) (by decide))
    fun t₅ ⟨h9₅, ho₅, k₅⟩ => ?_)
  have hT0 := hdr_lt_slot D.w aTmp (show 31 < 32 by decide)
  have h₅ := h₄.step (rs := [(slot D.w aTmp, 8 * D.w)]) (Frm.of_outside ho₅ (by simp)) (fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_le (w := D.w) (show aTmp < 8 by decide)
    have s1 := slot_sep (w := D.w) (show aTmp ≠ aN by decide)
    have s2 := slot_sep (w := D.w) (show aTmp ≠ aOne by decide)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> omega_arith) k₅.rd k₅.wr (k₅.gpr .x0 (by decide))
  refine WP.mono h₅.andFlag fun u ⟨hu, h9, _, _, k₆⟩ => ⟨⟨hu, ?_⟩,
    keep_trans (keep_trans (keep_trans (keep_trans (k₁.mono (by decide)) k₂) (k₃.mono (by decide))) k₄)
      (keep_trans (k₅.mono (by decide)) k₆)⟩
  -- The values the checks read.
  have hG := h.2.1.good.scr.nowrap
  have sXm := slot_le (w := D.w) (show aXm < 8 by decide)
  have hXm0 := hdr_lt_slot D.w aXm (show sF < 32 by decide)
  have hT := hdr_lt_slot D.w aTmp (show sF < 32 by decide)
  have sTX := slot_sep (w := D.w) (show aTmp ≠ aXm by decide)
  have hQ₂ : wv t₂.mem (off D.B (inner D.w)) (slot D.w aXm) D.w = Q := by
    rw [ho₂.wv (Or.inr (by omega_arith)) (by omega_arith), hm₁, hQ]
  have hQ₄ : wv t₄.mem (off D.B (inner D.w)) (slot D.w aXm) D.w = Q := by
    rw [ho₄.wv (Or.inr (by omega_arith)) (by omega_arith), hm₃, hQ₂]
  have hF₅ : word t₅.mem (off D.B (inner D.w)) (8 * sF) = t₄.gpr .x9 := by
    rw [ho₅.word (Or.inl (by omega_arith)) (by omega_arith), hF₄]
  rw [h9, h9₅, hF₅, h9₄, hm₃, hF₂, h9₃, h9₁, hQ, hQ₂, hQ₄, h₂.2.2.1.one, h₄.2.2.1.n, bit_and, bit_and]
  by_cases a : Q % 2 = 1 <;> by_cases b : 1 < Q <;> by_cases c : 2 * (Q / 2) + 1 < D.P <;> simp [bit, a, b, c]

end VG.Proof.Ffdh.AArch64
