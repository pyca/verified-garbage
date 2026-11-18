module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.R2wFast
public import VerifiedGarbage.Proof.Bignum.CrtHdr
public import VerifiedGarbage.Proof.Bignum.CrtKey
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtUnit
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks

/-! ### `Bignum.X86_64.CrtChk`, which this module and modules that import it used -/

section

/-!
# RSA with the CRT on x86-64: the checks

`checks`: the mask of `c < n`, `p q = n` and `qInv < p` into the modulus'
`sMask` and the primes' `sMaskX`, the primes replaced by 3 where it is
clear, and their `-X⁻¹` and the number 1 (`checks_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The checks after `p q = n`'s (`s₁` after `p q`, `s₂` after its mask):
`qInv < p`, and the primes' fixes. -/
theorem checksTail_ok {s s₁ s₂ : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {op oq wp wq N P Q QI : Nat}
    {m0 : Bool} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hop : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wq 8 + wsTab wq ≤ Z) (hwp : 2 ≤ wp) (hwp' : wp ≤ w) (hwq : 2 ≤ wq)
    (hwq' : wq ≤ w) (hsP : word s.mem B (8 * sWsP) = off B op) (hsQ : word s.mem B (8 * sWsQ) = off B oq)
    (hwsP : WsAt s.mem B op wp mp) (hwsQ : WsAt s.mem B oq wq mq)
    (hP : wv s.mem (off B op) (slot wp Public.aN) wp = P) (hQ : wv s.mem (off B oq) (slot wq Public.aN) wq = Q)
    (hQI : wv s.mem (off B op) (slot wp aChunk) wp = QI) (hodd : N % 2 = 1)
    (ho₁ : Outside B (slot w Public.aAcc) (8 * (2 * w + 2)) s.mem s₁.mem)
    (ho₂ : Outside B (8 * Public.sMask) 8 s₁.mem s₂.mem)
    (hM₂ : word s₂.mem B (8 * Public.sMask) = mask (m0 && decide (P * Q = N))) (k₁₂ : Keep mmRegs s s₂) :
    WP isa (seqs checksP) s₂ (ChecksPost s B Z w minv op oq wp wq N P Q QI m0) := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hP8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_arith
  obtain hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega_arith
  obtain hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  obtain hacc := accs_le w
  obtain hA0 := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  obtain hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aAcc hi; omega_arith)) (by omega_arith)
  obtain hab₁ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega_arith)) hd'
  obtain hb₂ : ∀ d, d + 8 ≤ 8 * Public.sMask ∨ 8 * Public.sMask + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
      word s₂.mem B d = word s₁.mem B d := fun d hd hd' => ho₂.word hd hd'
  obtain hab₂ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₂.mem B d = word s.mem B d := fun d hd hd' => by
    rw [hb₂ d (Or.inr (by unfold Public.sMask sFn; omega_arith)) hd', hab₁ d hd hd']
  obtain hpw₂ : ∀ i < 32, word s₂.mem (off B op) (8 * i) = word s.mem (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hab₂ _ (by omega_arith) (by omega_arith)
  obtain hpv₂ : ∀ d k, d + 8 * k ≤ slot wp 8 → wv s₂.mem (off B op) d k = wv s.mem (off B op) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hab₂ _ (by omega_arith) (by omega_arith)
  obtain hsP₂ : word s₂.mem B (8 * sWsP) = off B op := by
    rw [hb₂ _ (Or.inr (by unfold sWsP Public.sMask sFn; omega_arith)) (by unfold sWsP sFn; omega_arith), hb₁ _ (by decide)]
    exact hsP
  obtain hsQ₂ : word s₂.mem B (8 * sWsQ) = off B oq := by
    rw [hb₂ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega_arith)) (by unfold sWsQ sFn; omega_arith), hb₁ _ (by decide)]
    exact hsQ
  obtain hs₂ := hs.congr k₁₂.2.2
  obtain hdi₂ : s₂.gpr .rdi = B := (k₁₂.gpr (by decide)).trans hg.rdi
  unfold checksP
  simp only [List.append_assoc]
  -- Into `p`'s workspace: `qInv < p`.
  refine wp_seqs_append (by simp) (by simp [qinvCheck]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B op ∧ t.mem = s₂.mem)
    (by xrun [enterP, State.ea, hdr, hdi₂, hdrOff, hs₂.ld (d := 8 * sWsP) (by unfold sWsP sFn; omega_arith), hsP₂]) rfl)
    fun s₃ ⟨⟨hdi₃, hm₃⟩, k₃⟩ => ?_
  obtain hs₃ := hs₂.congr k₃.2.2
  obtain hwsP₃ : WsAt s₃.mem B op wp mp := by rw [hm₃]; exact hwsP.of_words fun i hi => hpw₂ i (by omega_arith)
  refine wp_seqs_append (by simp [qinvCheck]) (by simp [primeFix]) ?_
  refine WP.mono (qinvCheck_ok hs₃ hdi₃ hwsP₃.hdr (by omega_arith) (by unfold Public.sMask sFn; omega_arith) (by omega_arith)
    (by omega_arith) hwsP₃.link) fun s₄ ⟨hM₄, ho₄, k₄⟩ => ?_
  rw [hm₃, hpv₂ _ _ (by have := slot_le (w := wp) (show aChunk < 8 by decide); omega_arith),
    hpv₂ _ _ (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega_arith), hP, hQI, hM₂, mask_and] at hM₄
  obtain hb₄ : ∀ d, d + 8 ≤ 8 * Public.sMask ∨ 8 * Public.sMask + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
      word s₄.mem B d = word s₂.mem B d := fun d hd hd' => by rw [ho₄.word hd hd', hm₃]
  obtain hab₄ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₄.mem B d = word s.mem B d := fun d hd hd' => by
    rw [hb₄ d (Or.inr (by unfold Public.sMask sFn; omega_arith)) hd', hab₂ d hd hd']
  obtain hH₄ : Hdr s₄.mem B w minv := by
    have : ∀ i < 16, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
      rw [hb₄ _ (Or.inl (by unfold Public.sMask sFn; omega_arith)) (by omega_arith),
        hb₂ _ (Or.inl (by unfold Public.sMask sFn; omega_arith)) (by omega_arith), hb₁ _ (by omega_arith)]
    exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (this _ (by unfold sArr; omega_arith)).trans (hg.hdr.harr j hj)⟩
  obtain hwsP₄ : WsAt s₄.mem B op wp mp := hwsP.of_words fun i hi => by
    rw [word_off, word_off]; exact hab₄ _ (by omega_arith) (by omega_arith)
  obtain kk4 := (k₁₂.trans k₃).trans k₄
  obtain hcP₄ := SubCtx.mk' (hs.congr kk4.2.2) hH₄ hwsP₄ ((k₄.gpr (by decide)).trans hdi₃) hlo (by have := tabBytes_le_wsTab wp; omega_arith)
  obtain hoddP : keyMask m0 N P Q QI = true → P % 2 = 1 := fun h => by
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq] at h
    exact odd_of_mul_odd h.1.2 hodd
  obtain hoddQ : keyMask m0 N P Q QI = true → Q % 2 = 1 := fun h => by
    simp only [keyMask, Bool.and_eq_true, decide_eq_true_eq] at h
    exact odd_of_mul_odd (by rw [Nat.mul_comm]; exact h.1.2) hodd
  -- `p := M ? p : 3`.
  refine wp_seqs_append (by simp [primeFix]) (by simp) ?_
  refine WP.mono (primeFix_ok hcP₄ hwp hwp' (by omega_arith) hM₄
    (by rw [wv_off, (show wv s₄.mem B (op + slot wp Public.aN) wp = wv s.mem B (op + slot wp Public.aN) wp from
      wv_congr fun i hi => hab₄ _ (by omega_arith) (by
        have := slot_le (w := wp) (show Public.aN < 8 by decide); omega_arith)), ← wv_off]; exact hP) hoddP)
    fun s₅ ⟨mp', hcP₅, hP₅, hiP₅, hoP₅, hmP₅, f₅, k₅⟩ => ?_
  obtain hpr : ∀ r ∈ [(slot wp Public.aN, 8 * (wp + 2)), (slot wp Public.aOne, 8 * (wp + 2)), (8 * sMaskX, 8),
      (8 * sMinv, 8)], r.1 + r.2 ≤ slot wp 8 := by
    have := slot_le (w := wp) (show Public.aN < 8 by decide)
    have := slot_le (w := wp) (show Public.aOne < 8 by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega_arith
  obtain ho64 : op < 2 ^ 64 := by omega_arith
  obtain hb₅ : ∀ d, d + 8 ≤ op → word s₅.mem B d = word s₄.mem B d := fun d hd =>
    f₅.word_below hpr (by omega_arith) ho64 hd
  obtain hq₅ : ∀ d, oq ≤ d → d + 8 ≤ 2 ^ 64 → word s₅.mem B d = word s₄.mem B d := fun d hd hd' =>
    (f₅.rebase ho64 fun r hr => by have := hpr r hr; omega_arith).word_eq (fun r hr => Or.inr (by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hpr r₀ hr₀; simp only; omega_arith)) hd'
  obtain hl₅ : InRegions (s₅.rd ++ s₅.wr) (off (off B op) (8 * sLink)) 8 :=
    hcP₅.good.scr.ld (by unfold sLink sFn; omega_arith)
  obtain hsQ₅ : word s₅.mem B (8 * sWsQ) = off B oq := by
    rw [hb₅ _ (by unfold sWsQ sFn; omega_arith), hb₄ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega_arith))
      (by unfold sWsQ sFn; omega_arith)]; exact hsQ₂
  -- Into `q`'s workspace.
  refine wp_seqs_append (by simp) (by simp [primeFix]) ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = off B oq ∧ t.mem = s₅.mem)
    (by xrun [leave, enterQ, State.ea, hdr, hcP₅.rdi, hdrOff, hl₅, hcP₅.link,
      hcP₅.scr.ld (d := 8 * sWsQ) (by unfold sWsQ sFn; omega_arith), hsQ₅]) rfl)
    fun s₆ ⟨⟨hdi₆, hm₆⟩, k₆⟩ => ?_
  obtain hH₆ : Hdr s₆.mem B w minv := by
    rw [hm₆]
    exact ⟨(hb₅ _ (by unfold sW; omega_arith)).trans hH₄.hw, (hb₅ _ (by unfold sMinv; omega_arith)).trans hH₄.hminv,
      fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_arith); omega_arith)).trans
        (hH₄.harr j hj)⟩
  obtain hwsQ₆ : WsAt s₆.mem B oq wq mq := by
    rw [hm₆]
    exact hwsQ.of_words fun i hi => by
      rw [word_off, word_off, hq₅ _ (by omega_arith) (by omega_arith), hab₄ _ (by omega_arith) (by omega_arith)]
  obtain kk6 := (kk4.trans k₅).trans k₆
  obtain hcQ₆ := SubCtx.mk' (hs.congr kk6.2.2) hH₆ hwsQ₆ hdi₆ (by omega_arith) (by have := tabBytes_le_wsTab wq; omega_using [hoq, this])
  obtain hM₆ : word s₆.mem B (8 * Public.sMask) = mask (keyMask m0 N P Q QI) := by
    rw [hm₆, hb₅ _ (by unfold Public.sMask sFn; omega_arith)]; exact hM₄
  refine wp_seqs_append (by simp [primeFix]) (by simp) ?_
  refine WP.mono (primeFix_ok hcQ₆ hwq hwq' (by omega_arith) hM₆
    (by rw [hm₆, wv_off, wv_congr fun i hi => hq₅ _ (by omega_arith) (by
        have := slot_le (w := wq) (show Public.aN < 8 by decide); omega_arith),
      wv_congr fun i hi => hab₄ _ (by omega_arith) (by have := slot_le (w := wq) (show Public.aN < 8 by decide); omega_arith),
      ← wv_off]; exact hQ) hoddQ)
    fun s₇ ⟨mq', hcQ₇, hQ₇, hiQ₇, hoQ₇, _, f₇, k₇⟩ => ?_
  obtain hqr : ∀ r ∈ [(slot wq Public.aN, 8 * (wq + 2)), (slot wq Public.aOne, 8 * (wq + 2)), (8 * sMaskX, 8),
      (8 * sMinv, 8)], r.1 + r.2 ≤ slot wq 8 := by
    have := slot_le (w := wq) (show Public.aN < 8 by decide)
    have := slot_le (w := wq) (show Public.aOne < 8 by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega_arith
  obtain hoq64 : oq < 2 ^ 64 := by omega_arith
  obtain hb₇ : ∀ d, d + 8 ≤ oq → word s₇.mem B d = word s₆.mem B d := fun d hd =>
    f₇.word_below hqr (by omega_arith) hoq64 hd
  obtain hl₇ : InRegions (s₇.rd ++ s₇.wr) (off (off B oq) (8 * sLink)) 8 :=
    hcQ₇.good.scr.ld (by unfold sLink sFn; omega_arith)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = s₇.mem)
    (by xrun [leave, State.ea, hdr, hcQ₇.rdi, hdrOff, hl₇, hcQ₇.link]) rfl) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  obtain kall := (kk6.trans k₇).trans k'
  obtain hbt : ∀ d, d + 8 ≤ op → word t.mem B d = word s₄.mem B d := fun d hd => by
    rw [hm, hb₇ d (by omega_arith), hm₆, hb₅ d hd]
  obtain hpt : ∀ d, op ≤ d → d + 8 ≤ oq → word t.mem B d = word s₅.mem B d := fun d hd hd' => by
    rw [hm, hb₇ d hd', hm₆]
  obtain hpt' : ∀ i < 32, word t.mem (off B op) (8 * i) = word s₅.mem (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hpt _ (by omega_arith) (by omega_arith)
  obtain hptv : ∀ d k, d + 8 * k ≤ slot wp 8 → wv t.mem (off B op) d k = wv s₅.mem (off B op) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpt _ (by omega_arith) (by omega_arith)
  refine ⟨⟨hs.congr kall.2.2, hdi, ⟨(hbt _ (by unfold sW; omega_arith)).trans hH₄.hw,
      (hbt _ (by unfold sMinv; omega_arith)).trans hH₄.hminv,
      fun j hj => (hbt _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_arith); omega_arith)).trans
        (hH₄.harr j hj)⟩⟩,
    by rw [hbt _ (by unfold Public.sMask sFn; omega_arith)]; exact hM₄,
    by rw [hbt _ (by unfold sWsP sFn; omega_arith), hb₄ _ (Or.inr (by unfold sWsP Public.sMask sFn; omega_arith))
      (by unfold sWsP sFn; omega_arith)]; exact hsP₂,
    by rw [hbt _ (by unfold sWsQ sFn; omega_arith), hb₄ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega_arith))
      (by unfold sWsQ sFn; omega_arith)]; exact hsQ₂,
    ⟨mp', hcP₅.ws.of_words fun i hi => hpt' i (by omega_arith), ⟨?_, ?_, ?_⟩,
      by rw [hpt' _ (by decide)]; exact hmP₅⟩,
    ⟨mq', by rw [hm]; exact hcQ₇.ws, ⟨by rw [hm]; exact hQ₇, by rw [hm]; exact hiQ₇, by rw [hm]; exact hoQ₇⟩⟩,
    ?_, ⟨fun r hr => ?_, kall.2⟩⟩
  · rw [hptv _ _ (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega_arith)]; exact hP₅
  · rw [word_off, hpt _ (by omega_arith) (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega_arith), ← word_off]
    exact hiP₅
  · rw [hptv _ _ (by have := slot_le (w := wp) (show Public.aOne < 8 by decide); omega_arith)]; exact hoP₅
  · have mem1 : (slot w Public.aAcc, 8 * (2 * w + 2)) ∈ [(slot w Public.aAcc, 8 * (2 * w + 2)),
        (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)] := by simp
    obtain mem2 : (8 * Public.sMask, 8) ∈ [(slot w Public.aAcc, 8 * (2 * w + 2)),
        (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)] := by simp
    obtain g1 := Frm.of_outside ho₁ mem1
    obtain g2 := Frm.of_outside ho₂ mem2
    obtain g4 := Frm.of_outside ho₄ mem2
    obtain g5 := (f₅.rebase ho64 fun r hr => by have := hpr r hr; omega_arith).widen (rs' := [(slot w Public.aAcc,
        8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)]) fun r hr => by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hpr r₀ hr₀
      exact ⟨(op, slot wp 8), by simp, by simp only; omega_arith, by simp only; omega_arith⟩
    obtain g7 := (f₇.rebase hoq64 fun r hr => by have := hqr r hr; omega_arith).widen (rs' := [(slot w Public.aAcc,
        8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)]) fun r hr => by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hqr r₀ hr₀
      exact ⟨(oq, slot wq 8), by simp, by simp only; omega_arith, by simp only; omega_arith⟩
    rw [hm₃] at g4
    rw [hm₆] at g7
    rw [hm]
    exact (((g1.trans g2).trans g4).trans g5).trans g7
  · by_cases h : r = .rdi
    · subst h; rw [hdi, hg.rdi]
    · exact kall.1 r (by revert hr h; cases r <;> decide)


/-- The checks: the mask `M` of `c < n` (`m0`), `p q = n` and `qInv < p`;
`p := M ? p : 3`, `q := M ? q : 3`, their `-X⁻¹` and 1. -/
theorem checks_ok {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {op oq wp wq N P Q QI : Nat}
    {m0 : Bool} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hop : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wq 8 + wsTab wq ≤ Z) (hwp : 2 ≤ wp) (hwp' : wp ≤ w) (hwq : 2 ≤ wq)
    (hwq' : wq ≤ w) (hsP : word s.mem B (8 * sWsP) = off B op) (hsQ : word s.mem B (8 * sWsQ) = off B oq)
    (hwsP : WsAt s.mem B op wp mp) (hwsQ : WsAt s.mem B oq wq mq)
    (hN : wv s.mem B (slot w Public.aN) w = N) (hM : word s.mem B (8 * Public.sMask) = mask m0)
    (hP : wv s.mem (off B op) (slot wp Public.aN) wp = P) (hQ : wv s.mem (off B oq) (slot wq Public.aN) wq = Q)
    (hQI : wv s.mem (off B op) (slot wp aChunk) wp = QI) (hodd : N % 2 = 1) :
    WP isa (seqs checks) s (ChecksPost s B Z w minv op oq wp wq N P Q QI m0) := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hP8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_arith
  obtain hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega_arith
  obtain hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  obtain hacc := accs_le w
  obtain hA0 := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  unfold checks
  simp only [List.append_assoc]
  -- `p q`.
  refine wp_seqs_append (by simp [pqProduct, zeroAccs]) (by simp) ?_
  refine WP.mono (pqProduct_ok hg (by omega_arith) hsP hsQ hwsP.hdr.hw hwsQ.hdr.hw
    (by rw [hwsP.hdr.harr _ (by decide), off_off]) (by rw [hwsQ.hdr.harr _ (by decide), off_off]) hlo hop hoq
    (by omega_arith) hwp' (by omega_arith) hwq') fun s₁ ⟨hpq₁, ho₁, k₁⟩ => ?_
  obtain hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aAcc hi; omega_arith)) (by omega_arith)
  obtain hab₁ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega_arith)) hd'
  obtain hg₁ : Good s₁ B Z w minv := ⟨hs.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi,
    ⟨(hb₁ _ (by decide)).trans hg.hdr.hw, (hb₁ _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (hb₁ _ (by unfold sArr; omega_arith)).trans (hg.hdr.harr j hj)⟩⟩
  obtain hN₁ : wv s₁.mem B (slot w Public.aN) w = N := by
    have := slot_le (w := w) (show Public.aN < 8 by decide)
    have : slot w Public.aN + 8 * w ≤ slot w Public.aAcc := by unfold slot Public.aN Public.aAcc; omega_arith
    rw [ho₁.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact hN
  rw [← wv_off, ← wv_off, hP, hQ] at hpq₁
  -- `p q = n`.
  refine wp_seqs_append (by simp [eqCheck]) (by simp) ?_
  refine WP.mono (eqCheck_ok hg₁ (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨hM₂, ho₂, k₂⟩ => ?_
  rw [hpq₁, hN₁, hb₁ _ (by decide), hM, mask_and] at hM₂
  exact checksTail_ok hg hw hw28 hlo hop hoq hwp hwp' hwq hwq' hsP hsQ hwsP hwsQ hP hQ hQI hodd ho₁ ho₂ hM₂
    ((k₁.trans k₂).mono (by decide))

/-- `checksP`, the checks but `p q = n`'s, given `p q = n`: as `checks_ok`. -/
theorem checksP_ok {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {op oq wp wq N P Q QI : Nat}
    {m0 : Bool} (hg : Good s B Z w minv) (hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hop : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wq 8 + wsTab wq ≤ Z) (hwp : 2 ≤ wp) (hwp' : wp ≤ w) (hwq : 2 ≤ wq)
    (hwq' : wq ≤ w) (hsP : word s.mem B (8 * sWsP) = off B op) (hsQ : word s.mem B (8 * sWsQ) = off B oq)
    (hwsP : WsAt s.mem B op wp mp) (hwsQ : WsAt s.mem B oq wq mq)
    (hM : word s.mem B (8 * Public.sMask) = mask m0)
    (hP : wv s.mem (off B op) (slot wp Public.aN) wp = P) (hQ : wv s.mem (off B oq) (slot wq Public.aN) wq = Q)
    (hQI : wv s.mem (off B op) (slot wp aChunk) wp = QI) (hodd : N % 2 = 1) (hpq : P * Q = N) :
    WP isa (seqs checksP) s (ChecksPost s B Z w minv op oq wp wq N P Q QI m0) := by
  exact checksTail_ok (s₁ := s) hg hw hw28 hlo hop hoq hwp hwp' hwq hwq' hsP hsQ hwsP hwsQ hP hQ hQI hodd
    (Outside.refl _ _ _ _) (Outside.refl _ _ _ _) (by rw [hM, hpq]; simp) (Keep.refl _ _)

end VG.Proof.Bignum.X86_64

end

end

/-!
# RSA with the CRT on x86-64: up to the checks

From the header `entry` leaves, for a valid modulus: the modulus' setup (as
`vg_rsa_public`'s, then `c R mod n`), the primes' workspaces and the checks
(`front_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- What `main` starts from: the working space at `B` (its base in `rdi`)
holding all three workspaces, the header `entry` leaves, and the byte
strings outside the working space. -/
structure CrtPre (s : State) (B : Addr) (Z k : Nat) (op np ip pp qp dpp dqp qip : Addr) (pl ql : Nat)
    (nb xb pb qb dpb dqb qib : List Byte) : Prop where
  scr : Scr s B Z
  rdi : s.gpr .rdi = B
  z : offQ ((k + 7) / 8) pl + slot (wsWords ql) 8 + wsTab (wsWords ql) ≤ Z
  zk : 128 * k ≤ Z
  k1 : 64 ≤ k
  k2 : k ≤ 1024
  hO : word s.mem B (8 * Public.sOut) = op
  hN : word s.mem B (8 * Public.sN) = np
  hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k
  hIn : word s.mem B (8 * Public.sIn) = ip
  hP : word s.mem B (8 * sP) = pp
  hPl : word s.mem B (8 * sPlen) = BitVec.ofNat 64 pl
  hQ : word s.mem B (8 * sQ) = qp
  hQl : word s.mem B (8 * sQlen) = BitVec.ofNat 64 ql
  hDp : word s.mem B (8 * sDp) = dpp
  hDq : word s.mem B (8 * sDq) = dqp
  hQi : word s.mem B (8 * sQinv) = qip
  n : Src s B Z np nb
  x : Src s B Z ip xb
  p : Src s B Z pp pb
  q : Src s B Z qp qb
  dp : Src s B Z dpp dpb
  dq : Src s B Z dqp dqb
  qi : Src s B Z qip qib
  nl : nb.length = k
  xl : xb.length = k
  pbl : pb.length = pl
  qbl : qb.length = ql
  dpl : dpb.length = pl
  dql : dqb.length = ql
  qil : qib.length = pl
  pl1 : 1 ≤ pl
  pl2 : pl < k
  ql1 : 1 ≤ ql
  ql2 : ql < k
  out : ∀ j < k, InRegions s.wr (op + BitVec.ofNat 64 j) 1
  outSep : ∀ j < k, Z ≤ ofs B (op + BitVec.ofNat 64 j)

/-- After the checks: the three workspaces, the modulus' values, the mask
`M` and the primes `M ? p : 3`, `M ? q : 3`. -/
structure CrtReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q : Nat)
    (M : Bool) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : word t.mem B (8 * Public.sMask) = mask M
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  pxv : XVals t B (offP w) (wsWords pl) mp (if M then P else 3)
  pmask : word t.mem (off B (offP w)) (8 * sMaskX) = mask M
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  qxv : XVals t B (offQ w pl) (wsWords ql) mq (if M then Q else 3)
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

theorem nSetup_eq (M : Mont) : nSetup M.mm =
    (loadSteps ++ restSteps) ++ ([R2Words.choice M.mm] ++ [M.mm Public.aXm Public.aX Public.aR2]) := rfl

/-- After `n`'s setup: its values, `c R mod n` and the mask of `c < n`. -/
structure NReady (s t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N C : Nat) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : word t.mem B (8 * Public.sMask) = mask (decide (C < N))
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

/-- What a step computing `R² mod n` into `aR2` leaves, from the state `t`
of `n`'s setup: what `R2w.choice_ok` gives. -/
def R2Post (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N : Nat) (t' : State) : Prop :=
  Good t' B Z w minv ∧ wv t'.mem B (slot w Public.aR2) w < N ∧
    wv t'.mem B (slot w Public.aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
    Frm B (r2Ranges w) t.mem t'.mem ∧ Keep mmRegs t t'

/-- `n`'s setup, for a valid modulus, with `R² mod n` from the step `r2`,
which leaves `R2Post` from the state the setup before it leaves (`hr2`). -/
theorem nPartWith_ok (M : Mont) (r2 : Prog isa) {s : State} {B : Addr} {Z k : Nat}
    {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat} {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr2 : ∀ t₁ minv, SetupOut t₁ B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) →
      InScr B Z s.mem t₁.mem → Keep mmRegs s t₁ →
      WP isa r2 t₁ (R2Post t₁ B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb))) :
    WP isa (seqs ((loadSteps ++ restSteps) ++ ([r2] ++ [M.mm Public.aXm Public.aX Public.aR2]))) s fun t => ∃ minv,
      NReady s t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  have hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_arith
  have hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => (h' r hr).trans hZ
  -- The modulus, the input, `-n⁻¹`, 1 and the mask of `c < n`.
  refine wp_seqs_append (by simp [loadSteps]) (by simp)
    (WP.mono (setup_ok h.scr h.rdi hZ (by omega_arith) (by omega_arith) h.hK h.hN h.hIn h.n h.x h.nl h.xl hodd)
      fun t₁ ⟨minv, so, f₁, k₁⟩ => ?_)
  -- `R² mod n`.
  refine wp_seqs_append (by simp) (by simp)
    (WP.mono (hr2 t₁ minv so (InScr.of_frm f₁ (hZs (setupRanges_le _))) k₁)
      fun t₂ ⟨hg₂, hlt₂, hr₂, f₂, k₂⟩ => ?_)
  have hX₂ : wv t₂.mem B (slot ((k + 7) / 8) Public.aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.x
  have hN₂ : wv t₂.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.n
  have hI₂ : ((word t₂.mem B (slot ((k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₂.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact so.inv
  have hO₂ : wv t₂.mem B (slot ((k + 7) / 8) Public.aOne) ((k + 7) / 8) = 1 := by
    rw [f₂.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact so.one
  -- `c R mod n`.
  simp only [seqs]
  refine WP.mono (mmN_ok M hg₂ hZ (by omega_arith) (by omega_arith) (o := Public.aXm) (a := Public.aX) (b := Public.aR2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hN₂ hI₂ hlt₂)
    fun t₃ ⟨hg₃, hN₃, hI₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_
  have hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) (Spec.Rsa.os2ip nb) := VG.Proof.Bignum.coprime_pow2 hodd _
  have hxm₃ : wv t₃.mem B (slot ((k + 7) / 8) Public.aXm) ((k + 7) / 8) % Spec.Rsa.os2ip nb =
      Spec.Rsa.os2ip xb * 2 ^ (64 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₃, hX₂, Nat.mul_mod, hr₂, ← Nat.mul_mod, Nat.mul_assoc]
  have g₃ : Frm B [(slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))] t₂.mem t₃.mem :=
    Frm.of_arrays ha₃ fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp
  have kg₃ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))], KeepsHdr r ∧ r.1 + r.2 ≤ slot ((k + 7) / 8) 8 := by
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) Public.aTmp (show 31 < 32 by decide)
    have := hdr_lt_slot ((k + 7) / 8) Public.aXm (show 31 < 32 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aAcc < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aTmp < 8 by decide)
    have := slot_le (w := (k + 7) / 8) (show Public.aXm < 8 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl) <;> exact ⟨keepsHdr_ge (by simp only; omega_arith), by simp only; omega_arith⟩
  have e2 : word t₂.mem B (8 * Public.sMask) = word t₁.mem B (8 * Public.sMask) :=
    f₂.word_eq (r2Ranges_hdr _ (by decide) (by decide)) (by unfold Public.sMask sFn; omega_arith)
  exact ⟨minv, hg₃,
    ⟨hN₃, hI₃, by rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact hr₂,
      by rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact hlt₂,
      by rw [ha₃.wv_of_not_mem (by decide) (by decide) hn']; exact hO₂⟩, hxm₃,
    by rw [ha₃.hslot (by decide), e2]; exact so.mask,
    ((HFix.of_frm f₁ (keepsHdr_setupRanges _)).trans (HFix.of_frm f₂ (keepsHdr_r2Ranges _))).trans
      (HFix.of_frm g₃ fun r hr => (kg₃ r hr).1),
    ((InScr.of_frm f₁ (hZs (setupRanges_le _))).trans (InScr.of_frm f₂ (hZs (r2Ranges_le _)))).trans
      (InScr.of_frm g₃ (hZs fun r hr => (kg₃ r hr).2)),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `n`'s setup, for a valid modulus. -/
theorem nPart_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm)) s fun t => ∃ minv,
      NReady s t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, -, hlo⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  rw [nSetup_eq]
  exact nPartWith_ok M _ h hv fun t₁ minv so _ _ =>
    R2w.choice_ok M so.good hZ (by omega_arith) (by omega_arith) so.n so.inv so.r12 so.r10 hodd hlo

/-- After the primes' workspaces: `n`'s values as before, the workspaces,
`p`, `q` and `qInv`. -/
structure PReady (s t : State) (B : Addr) (Z w pl ql : Nat) (minv mp mq : BitVec 64) (N C P Q QI : Nat) : Prop
    where
  n : NReady s t B Z w minv N C
  wsP : word t.mem B (8 * sWsP) = off B (offP w)
  wsQ : word t.mem B (8 * sWsQ) = off B (offQ w pl)
  pws : WsAt t.mem B (offP w) (wsWords pl) mp
  qws : WsAt t.mem B (offQ w pl) (wsWords ql) mq
  pv : wv t.mem (off B (offP w)) (slot (wsWords pl) Public.aN) (wsWords pl) = P
  qiv : wv t.mem (off B (offP w)) (slot (wsWords pl) aChunk) (wsWords pl) = QI
  qv : wv t.mem (off B (offQ w pl)) (slot (wsWords ql) Public.aN) (wsWords ql) = Q

/-- The primes' workspaces, from `n`'s setup. -/
theorem setupPart_ok {s t₃ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hr : NReady s t₃ B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)) :
    WP isa (seqs primesSetup) t₃ fun t => ∃ mp mq, PReady s t B Z ((k + 7) / 8) pl ql minv mp mq
      (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib) := by
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_arith
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hh₃ : ∀ i < 32, hFixed i = true → word t₃.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  refine WP.mono (primesSetup_ok hr.good (by omega_arith) (by omega_arith) hZq
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hPl) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQl)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hP) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQ)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQi) (h.p.congrK hr.iscr hr.keep) (h.q.congrK hr.iscr hr.keep)
    (h.qi.congrK hr.iscr hr.keep) h.pbl h.qbl h.qil h.pl1 (by have := h.pl2; omega_arith) h.ql1 (by have := h.ql2; omega_arith))
    fun t₄ ⟨hg₄, hsP₄, hsQ₄, ⟨mp, hwp₄⟩, ⟨mq, hwq₄⟩, hp₄, hc₄, hq₄, f₄, k₄⟩ => ?_
  have kf₄ : ∀ r ∈ [(8 * sWsP, 8), (8 * sWsQ, 8), (offP ((k + 7) / 8), slot (wsWords pl) 8 + wsTab (wsWords pl) + slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z ∧ (slot ((k + 7) / 8) 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 31) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsP, sFn]; omega_arith,
        Or.inr (by simp only [sWsP, sFn]; omega_arith)⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsQ, sFn]; omega_arith,
        Or.inr (by simp only [sWsQ, sFn]; omega_arith)⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega_arith), by simp only [offP]; unfold offQ at hZq; omega_arith,
        Or.inl (by simp only [offP]; omega_arith)⟩
  have hnv₄ : ∀ j < 8, wv t₄.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₃.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj =>
    f₄.wv_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) hj
      have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) hj; omega_using [hn, hZ, this])
  have hnw₄ : word t₄.mem B (slot ((k + 7) / 8) Public.aN) = word t₃.mem B (slot ((k + 7) / 8) Public.aN) :=
    f₄.word_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
      have := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide); omega_using [hn, hZ, this])
  have hM₄ : word t₄.mem B (8 * Public.sMask) = word t₃.mem B (8 * Public.sMask) := by
    refine f₄.word_eq (fun r hr => ?_) (by unfold Public.sMask sFn; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl (by simp only [Public.sMask, sWsP, sFn]; omega_arith)
    · exact Or.inl (by simp only [Public.sMask, sWsQ, sFn]; omega_arith)
    · exact Or.inl (by simp only [offP, Public.sMask, sFn]; omega_arith)
  refine ⟨mp, mq, ⟨hg₄, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩, hsP₄, hsQ₄, hwp₄, hwq₄, hp₄, hc₄, hq₄⟩
  · rw [hnv₄ _ (by decide)]; exact hr.nv.n
  · rw [hnw₄]; exact hr.nv.inv
  · rw [hnv₄ _ (by decide)]; exact hr.nv.r2
  · rw [hnv₄ _ (by decide)]; exact hr.nv.r2lt
  · rw [hnv₄ _ (by decide)]; exact hr.nv.one
  · rw [hnv₄ _ (by decide)]; exact hr.xm
  · rw [hM₄]; exact hr.msk
  · exact hr.hfix.trans (HFix.of_frm f₄ fun r hr => (kf₄ r hr).1)
  · exact hr.iscr.trans (InScr.of_frm f₄ fun r hr => (kf₄ r hr).2.1)
  · exact (hr.keep.trans k₄).mono (by decide)

/-- Checks `c` that give what `checks` gives (`hc`), from the primes'
workspaces. -/
theorem checksPartWith_ok {c : List (Prog isa)} {s t₄ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hc : WP isa (seqs c) t₄ (ChecksPost t₄ B Z ((k + 7) / 8) minv (slot ((k + 7) / 8) 8) (offQ ((k + 7) / 8) pl)
      (wsWords pl) (wsWords ql) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)
      (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)))) :
    WP isa (seqs c) t₄ fun t => ∃ mp' mq',
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  have hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_arith
  have hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_arith
  have hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_arith
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_arith
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_arith
  refine WP.mono hc
    fun t ⟨hg, hMt, hsPt, hsQt, ⟨mp', hwpt, hxpt, hmpt⟩, ⟨mq', hwqt, hxqt⟩, f₅, k₅⟩ => ?_
  have kf₅ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * (2 * ((k + 7) / 8) + 2)), (8 * Public.sMask, 8),
      (offP ((k + 7) / 8), slot (wsWords pl) 8), (offQ ((k + 7) / 8) pl, slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z := by
    have := accs_le ((k + 7) / 8)
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact ⟨keepsHdr_ge (by simp only; omega_arith), by simp only; omega_arith⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [Public.sMask, sFn]; omega_arith⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega_arith), by simp only [offP]; unfold offQ at hZq; omega_arith⟩
    · exact ⟨keepsHdr_ge (by simp only [offQ]; omega_arith), by simp only; omega_arith⟩
  have hnv₅ : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₄.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj h1 h2 => by
    have := slot_le (w := (k + 7) / 8) hj
    have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
    have := accs_le ((k + 7) / 8)
    have : slot ((k + 7) / 8) j + 8 * ((k + 7) / 8) ≤ slot ((k + 7) / 8) Public.aAcc ∨
        slot ((k + 7) / 8) Public.aAcc + 8 * (2 * ((k + 7) / 8) + 2) ≤ slot ((k + 7) / 8) j := by
      unfold slot Public.aAcc
      rw [show Public.aAcc = 2 from rfl] at h1
      rw [show Public.aTmp = 3 from rfl] at h2
      rcases (show j < 2 ∨ 4 ≤ j by omega_arith) with hj' | hj'
      · left; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show j + 1 ≤ 2 by omega_arith)
        rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
      · right; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show 4 ≤ j by omega_arith); omega_arith
    refine f₅.wv_eq (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simp only; omega_arith
    · exact Or.inr (by simp only [Public.sMask, sFn]; omega_arith)
    · exact Or.inl (by simp only; omega_arith)
    · exact Or.inl (by simp only [offQ]; omega_arith)
  refine ⟨mp', mq', hg, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hMt, hsPt, hsQt, hwpt, hxpt, hmpt, hwqt, hxqt, ?_, ?_,
    (hr.n.keep.trans k₅).mono (by decide)⟩
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.n
  · have := accs_le ((k + 7) / 8)
    have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
    have hN0 := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
    rw [f₅.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have : slot ((k + 7) / 8) Public.aN + 8 ≤ slot ((k + 7) / 8) Public.aAcc := by
        unfold slot Public.aN Public.aAcc; omega_arith
      rcases hr with rfl | rfl | rfl | rfl
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inr (by simp only [Public.sMask, sFn]; omega_arith)
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inl (by simp only [offQ]; omega_arith)) (by omega_arith)]
    exact hr.n.nv.inv
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.r2
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.r2lt
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.one
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.xm
  · exact hr.n.hfix.trans (HFix.of_frm f₅ fun r hr => (kf₅ r hr).1)
  · exact hr.n.iscr.trans (InScr.of_frm f₅ fun r hr => (kf₅ r hr).2)

/-- The checks, from the primes' workspaces. -/
theorem checksPart_ok {s t₄ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :
    WP isa (seqs checks) t₄ fun t => ∃ mp' mq',
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_arith
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_arith
  exact checksPartWith_ok h hv hr (checks_ok hr.n.good (by omega_arith) (by omega_arith) (le_refl _) (by unfold offQ; omega_arith)
    (by unfold offQ at hZq ⊢; omega_arith) hwp2 (wsWords_le (by have := h.pl2; omega_arith) (by omega_arith)) hwq2
    (wsWords_le (by have := h.ql2; omega_arith) (by omega_arith)) hr.wsP hr.wsQ hr.pws hr.qws hr.n.nv.n hr.n.msk hr.pv hr.qv
    hr.qiv hodd)

/-- `checksP`, from the primes' workspaces, for `p q = n`: as `checksPart_ok`. -/
theorem checksPartP_ok {s t₄ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib))
    (hpq : Spec.Rsa.os2ip pb * Spec.Rsa.os2ip qb = Spec.Rsa.os2ip nb) :
    WP isa (seqs checksP) t₄ fun t => ∃ mp' mq',
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_arith
  have hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_arith
  exact checksPartWith_ok h hv hr (checksP_ok hr.n.good (by omega_arith) (by omega_arith) (le_refl _) (by unfold offQ; omega_arith)
    (by unfold offQ at hZq ⊢; omega_arith) hwp2 (wsWords_le (by have := h.pl2; omega_arith) (by omega_arith)) hwq2
    (wsWords_le (by have := h.ql2; omega_arith) (by omega_arith)) hr.wsP hr.wsQ hr.pws hr.qws hr.n.msk hr.pv hr.qv
    hr.qiv hodd hpq)

/-- Up to the checks, for a valid modulus. -/
theorem front_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm ++ primesSetup ++ checks)) s fun t => ∃ minv mp mq,
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  wp_seqs_append (by simp [nSetup]) (by simp [checks]) (wp_seqs_append (by simp [nSetup])
    (by simp [primesSetup]) (WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ =>
      WP.mono (setupPart_ok h hr) fun _ ⟨_, _, hr'⟩ =>
        WP.mono (checksPart_ok h hv hr') fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))

end VG.Proof.Bignum.X86_64
