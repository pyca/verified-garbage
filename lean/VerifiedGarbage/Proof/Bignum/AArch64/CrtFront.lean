module

public import VerifiedGarbage.Proof.Bignum.CrtHdr
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtUnit
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Bignum.CrtKey
import VerifiedGarbage.Proof.Bignum.AArch64.CrtFix
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSetup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtRedc
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks

/-! ### `Bignum.AArch64.CrtChk`, which this module and modules that import it used -/

section

/-!
# RSA with the CRT on AArch64: the checks

`checks`: the mask of `c < n`, `p q = n` and `qInv < p` into the modulus'
`sMask` and the primes' `sMaskX`, the primes replaced by 3 where it is
clear, and their `-X⁻¹` and the number 1 (`checks_ok`); `checksGiven`, all
but `p q = n`, for a mask that implies it (`checksGiven_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- The checks but `p q = n` (`checksGiven`), for a mask `m1` that implies
it: the mask of `m1` and `qInv < p`; `p := M ? p : 3`, `q := M ? q : 3`,
their `-X⁻¹` and 1. -/
theorem checksGiven_ok {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {op oq wp wq N P Q QI : Nat}
    {m1 : Bool} (hg : Good s B Z w minv) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hop : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wq 8 + wsTab wq ≤ Z) (hwp : 2 ≤ wp) (hwp' : wp ≤ w) (hwq : 2 ≤ wq)
    (hwq' : wq ≤ w) (hsP : word s.mem B (8 * sWsP) = off B op) (hsQ : word s.mem B (8 * sWsQ) = off B oq)
    (hwsP : WsAt s.mem B op wp mp) (hwsQ : WsAt s.mem B oq wq mq) (hM : word s.mem B (8 * Public.sMask) = mask m1)
    (hP : wv s.mem (off B op) (slot wp Public.aN) wp = P) (hQ : wv s.mem (off B oq) (slot wq Public.aN) wq = Q)
    (hQI : wv s.mem (off B op) (slot wp aChunk) wp = QI) (hodd : N % 2 = 1) (hpq : m1 = true → P * Q = N) :
    WP isa (seqs checksGiven) s fun t => Good t B Z w minv ∧
      word t.mem B (8 * Public.sMask) = mask (m1 && decide (QI < P)) ∧
      word t.mem B (8 * sWsP) = off B op ∧ word t.mem B (8 * sWsQ) = off B oq ∧
      (∃ mp', WsAt t.mem B op wp mp' ∧ XVals t B op wp mp' (if m1 && decide (QI < P) then P else 3) ∧
        word t.mem (off B op) (8 * sMaskX) = mask (m1 && decide (QI < P))) ∧
      (∃ mq', WsAt t.mem B oq wq mq' ∧ XVals t B oq wq mq' (if m1 && decide (QI < P) then Q else 3)) ∧
      Frm B [(slot w Public.aAcc, 8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)]
        s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain hP8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_using []
  obtain hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega_using []
  obtain hacc := accs_le w
  obtain hA0 := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  unfold checksGiven
  simp only [List.append_assoc]
  -- Into `p`'s workspace: `qInv < p`.
  refine wp_seqs_append (by decide) (by decide) ?_
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off B op ∧ t.mem = s.mem)
    (by brun [enterP, hg.x0, hdr_enc (show sWsP < 32 by decide), hs.ld (show 8 * sWsP + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show sWsP < 32 by decide); omega_using [hlo, hop, hoq,
          this]), hsP]) (by decide) (by decide) (by decide +kernel))
    fun s₃ ⟨⟨hdi₃, hm₃⟩, k₃⟩ => ?_
  obtain hs₃ := hs.congr k₃.wr
  obtain hwsP₃ : WsAt s₃.mem B op wp mp := by rw [hm₃]; exact hwsP
  refine wp_seqs_append (by decide) (by decide) ?_
  refine WP.mono (qinvCheck_ok hs₃ hdi₃ hwsP₃.hdr (by omega_using [hop, hoq])
      (by unfold Public.sMask sFn; omega_using [hlo, hacc, hA0]) (by omega_using [hwp])
    (by omega_using [hw28, hwp']) hwsP₃.link) fun s₄ ⟨hM₄, ho₄, k₄⟩ => ?_
  rw [hm₃, hP, hQI, hM, mask_and] at hM₄
  obtain hb₄ : ∀ d, d + 8 ≤ 8 * Public.sMask ∨ 8 * Public.sMask + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
      word s₄.mem B d = word s.mem B d := fun d hd hd' => by rw [ho₄.word hd hd', hm₃]
  obtain hab₄ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₄.mem B d = word s.mem B d := fun d hd hd' =>
    hb₄ d (Or.inr (by unfold Public.sMask sFn; omega_using [hacc, hA0, hd])) hd'
  obtain hH₄ : Hdr s₄.mem B w minv := by
    have : ∀ i < 16, word s₄.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
      rw [hb₄ _ (Or.inl (by unfold Public.sMask sFn; omega_using [hi])) (by omega_using [hi])]
    exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (this _ (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj)⟩
  obtain hwsP₄ : WsAt s₄.mem B op wp mp := hwsP.of_words fun i hi => by
    rw [word_off, word_off]; exact hab₄ _ (by omega_using [hlo]) (by omega_using [hop, hoq, hn, hQ8, hi])
  obtain kk4 := k₃.trans k₄
  obtain hcP₄ := SubCtx.mk' (hs.congr kk4.wr) hH₄ hwsP₄ ((k₄.gpr .x0 (by decide)).trans hdi₃) hlo (by have := tabBytes_le_wsTab wp; omega_using [hop, hoq, this])
  obtain hoddP : (m1 && decide (QI < P)) = true → P % 2 = 1 := fun h => by
    simp only [Bool.and_eq_true] at h
    exact odd_of_mul_odd (hpq h.1) hodd
  obtain hoddQ : (m1 && decide (QI < P)) = true → Q % 2 = 1 := fun h => by
    simp only [Bool.and_eq_true] at h
    exact odd_of_mul_odd (by rw [Nat.mul_comm]; exact hpq h.1) hodd
  -- `p := M ? p : 3`.
  refine wp_seqs_append (by decide) (by decide) ?_
  refine WP.mono (primeFix_ok hcP₄ hwp hwp' (by omega_using [hw28]) hM₄
    (by rw [wv_off, (show wv s₄.mem B (op + slot wp Public.aN) wp = wv s.mem B (op + slot wp Public.aN) wp from
      wv_congr fun i hi => hab₄ _ (by omega_using [hlo]) (by
        have := slot_le (w := wp) (show Public.aN < 8 by decide); omega_using [hop, hoq, hn, hi, this])), ← wv_off]; exact hP) hoddP)
    fun s₅ ⟨mp', hcP₅, hP₅, hiP₅, hoP₅, hmP₅, f₅, k₅⟩ => ?_
  obtain hpr : ∀ r ∈ [(slot wp Public.aN, 8 * (wp + 2)), (slot wp Public.aOne, 8 * (wp + 2)), (8 * sMaskX, 8),
      (8 * sMinv, 8)], r.1 + r.2 ≤ slot wp 8 := by
    have := slot_le (w := wp) (show Public.aN < 8 by decide)
    have := slot_le (w := wp) (show Public.aOne < 8 by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega_arith
  obtain ho64 : op < 2 ^ 64 := by omega_using [hop, hoq, hn, hQ8]
  obtain hb₅ : ∀ d, d + 8 ≤ op → word s₅.mem B d = word s₄.mem B d := fun d hd =>
    f₅.word_below hpr (by omega_using [hop, hoq, hn]) ho64 hd
  obtain hq₅ : ∀ d, oq ≤ d → d + 8 ≤ 2 ^ 64 → word s₅.mem B d = word s₄.mem B d := fun d hd hd' =>
    (f₅.rebase ho64 fun r hr => by have := hpr r hr; omega_using [hop, hd, hd', this]).word_eq (fun r hr => Or.inr (by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
      have := hpr r₀ hr₀; simp only; omega_using [hop, hd, this])) hd'
  obtain hsQ₅ : word s₅.mem B (8 * sWsQ) = off B oq := by
    rw [hb₅ _ (by unfold sWsQ sFn; omega_arith), hb₄ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega_using []))
      (by unfold sWsQ sFn; omega_using [])]; exact hsQ
  -- Into `q`'s workspace.
  refine wp_seqs_append (by decide) (by decide) ?_
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = off B oq ∧ t.mem = s₅.mem)
    (by brun [leave, enterQ, hcP₅.x0, hdr_enc (show sLink < 32 by decide), hdr_enc (show sWsQ < 32 by decide),
      hcP₅.ld' (show sLink < 32 by decide), hcP₅.link', hcP₅.ldn (show sWsQ < 32 by decide), hsQ₅])
    (by decide) (by decide) (by decide +kernel))
    fun s₆ ⟨⟨hdi₆, hm₆⟩, k₆⟩ => ?_
  obtain hH₆ : Hdr s₆.mem B w minv := by
    rw [hm₆]
    exact ⟨(hb₅ _ (by unfold sW; omega_using [hlo, hacc, hA0])).trans hH₄.hw, (hb₅ _ (by unfold sMinv; omega_arith)).trans hH₄.hminv,
      fun j hj => (hb₅ _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_using [hj]); omega_using [hlo, this])).trans
        (hH₄.harr j hj)⟩
  obtain hwsQ₆ : WsAt s₆.mem B oq wq mq := by
    rw [hm₆]
    exact hwsQ.of_words fun i hi => by
      rw [word_off, word_off, hq₅ _ (by omega_using []) (by omega_using [hoq, hn, hQ8, hi]),
          hab₄ _ (by omega_using [hlo, hop]) (by omega_using [hoq, hn, hQ8, hi])]
  obtain kk6 := (kk4.trans k₅).trans k₆
  obtain hcQ₆ := SubCtx.mk' (hs.congr kk6.wr) hH₆ hwsQ₆ hdi₆ (by omega_using [hlo, hop]) (by have := tabBytes_le_wsTab wq; omega_using [hoq, this])
  obtain hM₆ : word s₆.mem B (8 * Public.sMask) = mask ((m1 && decide (QI < P))) := by
    rw [hm₆, hb₅ _ (by unfold Public.sMask sFn; omega_using [hlo, hacc, hA0])]; exact hM₄
  refine wp_seqs_append (by decide) (by decide) ?_
  refine WP.mono (primeFix_ok hcQ₆ hwq hwq' (by omega_using [hw28]) hM₆
    (by rw [hm₆, wv_off, wv_congr fun i hi => hq₅ _ (by omega_using []) (by
        have := slot_le (w := wq) (show Public.aN < 8 by decide); omega_using [hoq, hn, hi, this]),
      wv_congr fun i hi => hab₄ _ (by omega_using [hlo, hop])
          (by have := slot_le (w := wq) (show Public.aN < 8 by decide); omega_using [hoq, hn, hi, this]),
      ← wv_off]; exact hQ) hoddQ)
    fun s₇ ⟨mq', hcQ₇, hQ₇, hiQ₇, hoQ₇, _, f₇, k₇⟩ => ?_
  obtain hqr : ∀ r ∈ [(slot wq Public.aN, 8 * (wq + 2)), (slot wq Public.aOne, 8 * (wq + 2)), (8 * sMaskX, 8),
      (8 * sMinv, 8)], r.1 + r.2 ≤ slot wq 8 := by
    have := slot_le (w := wq) (show Public.aN < 8 by decide)
    have := slot_le (w := wq) (show Public.aOne < 8 by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [sMaskX, sMinv, sFn] <;> omega_arith
  obtain hoq64 : oq < 2 ^ 64 := by omega_using [hoq, hn, hQ8]
  obtain hb₇ : ∀ d, d + 8 ≤ oq → word s₇.mem B d = word s₆.mem B d := fun d hd =>
    f₇.word_below hqr (by omega_using [hoq, hn]) hoq64 hd
  refine WP.mono (WP.keep [.x0] (Q := fun t => t.gpr .x0 = B ∧ t.mem = s₇.mem)
    (by brun [leave, hcQ₇.x0, hdr_enc (show sLink < 32 by decide), hcQ₇.ld' (show sLink < 32 by decide), hcQ₇.link'])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨hdi, hm⟩, k'⟩ => ?_
  obtain kall := (kk6.trans k₇).trans k'
  obtain hbt : ∀ d, d + 8 ≤ op → word t.mem B d = word s₄.mem B d := fun d hd => by
    rw [hm, hb₇ d (by omega_using [hop, hd]), hm₆, hb₅ d hd]
  obtain hpt : ∀ d, op ≤ d → d + 8 ≤ oq → word t.mem B d = word s₅.mem B d := fun d hd hd' => by
    rw [hm, hb₇ d hd', hm₆]
  obtain hpt' : ∀ i < 32, word t.mem (off B op) (8 * i) = word s₅.mem (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hpt _ (by omega_using []) (by omega_using [hop, hP8, hi])
  obtain hptv : ∀ d k, d + 8 * k ≤ slot wp 8 → wv t.mem (off B op) d k = wv s₅.mem (off B op) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hpt _ (by omega_using []) (by omega_using [hop, hd, hi])
  refine ⟨⟨hs.congr kall.wr, hdi, ⟨(hbt _ (by unfold sW; omega_using [hlo, hacc, hA0])).trans hH₄.hw,
      (hbt _ (by unfold sMinv; omega_arith)).trans hH₄.hminv,
      fun j hj => (hbt _ (by have := hdr_lt_slot w 8 (show sArr j < 32 by unfold sArr; omega_using [hj]); omega_using [hlo, this])).trans
        (hH₄.harr j hj)⟩⟩,
    by rw [hbt _ (by unfold Public.sMask sFn; omega_arith)]; exact hM₄,
    by rw [hbt _ (by unfold sWsP sFn; omega_using [hlo, hacc, hA0]), hb₄ _ (Or.inr (by unfold sWsP Public.sMask sFn; omega_using []))
      (by unfold sWsP sFn; omega_using [])]; exact hsP,
    by rw [hbt _ (by unfold sWsQ sFn; omega_using [hlo, hacc, hA0]), hb₄ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega_using []))
      (by unfold sWsQ sFn; omega_using [])]; exact hsQ,
    ⟨mp', hcP₅.ws.of_words fun i hi => hpt' i (by omega_using [hi]), ⟨?_, ?_, ?_⟩,
      by rw [hpt' _ (by decide)]; exact hmP₅⟩,
    ⟨mq', by rw [hm]; exact hcQ₇.ws, ⟨by rw [hm]; exact hQ₇, by rw [hm]; exact hiQ₇, by rw [hm]; exact hoQ₇⟩⟩,
    ?_, ⟨fun r hr => ?_, kall.rd, kall.wr, kall.sp, kall.vcs⟩⟩
  · rw [hptv _ _ (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega_using [this])]; exact hP₅
  · rw [word_off, hpt _ (by omega_arith) (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega_arith), ← word_off]
    exact hiP₅
  · rw [hptv _ _ (by have := slot_le (w := wp) (show Public.aOne < 8 by decide); omega_arith)]; exact hoP₅
  · have mem2 : (8 * Public.sMask, 8) ∈ [(slot w Public.aAcc, 8 * (2 * w + 2)),
        (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)] := by simp
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
    exact (g4.trans g5).trans g7
  · by_cases h : r = .x0
    · subst h; rw [hdi, hg.x0]
    · exact kall.gpr r (by revert hr h; cases r <;> decide)


/-- The checks: the mask `M` of `c < n` (`m0`), `p q = n` and `qInv < p`;
`p := M ? p : 3`, `q := M ? q : 3`, their `-X⁻¹` and 1. -/
theorem checks_ok {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {op oq wp wq N P Q QI : Nat}
    {m0 : Bool} (hg : Good s B Z w minv) (_hw : 8 ≤ w) (hw28 : w < 2 ^ 28) (hlo : slot w 8 ≤ op)
    (hop : op + slot wp 8 + wsTab wp ≤ oq) (hoq : oq + slot wq 8 + wsTab wq ≤ Z) (hwp : 2 ≤ wp) (hwp' : wp ≤ w) (hwq : 2 ≤ wq)
    (hwq' : wq ≤ w) (hsP : word s.mem B (8 * sWsP) = off B op) (hsQ : word s.mem B (8 * sWsQ) = off B oq)
    (hwsP : WsAt s.mem B op wp mp) (hwsQ : WsAt s.mem B oq wq mq)
    (hN : wv s.mem B (slot w Public.aN) w = N) (hM : word s.mem B (8 * Public.sMask) = mask m0)
    (hP : wv s.mem (off B op) (slot wp Public.aN) wp = P) (hQ : wv s.mem (off B oq) (slot wq Public.aN) wq = Q)
    (hQI : wv s.mem (off B op) (slot wp aChunk) wp = QI) (hodd : N % 2 = 1) :
    WP isa (seqs checks) s fun t => Good t B Z w minv ∧
      word t.mem B (8 * Public.sMask) = mask (keyMask m0 N P Q QI) ∧
      word t.mem B (8 * sWsP) = off B op ∧ word t.mem B (8 * sWsQ) = off B oq ∧
      (∃ mp', WsAt t.mem B op wp mp' ∧ XVals t B op wp mp' (if keyMask m0 N P Q QI then P else 3) ∧
        word t.mem (off B op) (8 * sMaskX) = mask (keyMask m0 N P Q QI)) ∧
      (∃ mq', WsAt t.mem B oq wq mq' ∧ XVals t B oq wq mq' (if keyMask m0 N P Q QI then Q else 3)) ∧
      Frm B [(slot w Public.aAcc, 8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)]
        s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  obtain hP8 : 256 ≤ slot wp 8 := by unfold slot hdrBytes; omega_using []
  obtain hQ8 : 256 ≤ slot wq 8 := by unfold slot hdrBytes; omega_using []
  obtain hz : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega_using [hlo, hop, hoq, hn]
  obtain hacc := accs_le w
  obtain hA0 := hdr_lt_slot w Public.aAcc (show 31 < 32 by decide)
  unfold checks
  simp only [List.append_assoc]
  -- `p q`.
  refine wp_seqs_append (by decide) (by decide) ?_
  refine WP.mono (pqProduct_ok hg (by omega_using [hw28]) hsP hsQ (by rw [← word_off]; exact hwsP.hdr.hw)
    (by rw [← word_off]; exact hwsQ.hdr.hw) (by rw [← word_off, hwsP.hdr.harr _ (by decide), off_off])
    (by rw [← word_off, hwsQ.hdr.harr _ (by decide), off_off]) hlo hop hoq
    (by omega_using [hwp]) hwp' (by omega_using [hwq]) hwq') fun s₁ ⟨hpq₁, ho₁, k₁⟩ => ?_
  obtain hb₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    ho₁.word (Or.inl (by have := hdr_lt_slot w Public.aAcc hi; omega_using [this])) (by omega_using [hi])
  obtain hab₁ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₁.mem B d = word s.mem B d := fun d hd hd' =>
    ho₁.word (Or.inr (by omega_using [hacc, hd])) hd'
  obtain hg₁ : Good s₁ B Z w minv := ⟨hs.congr k₁.wr, (k₁.gpr .x0 (by decide)).trans hg.x0,
    ⟨(hb₁ _ (by decide)).trans hg.hdr.hw, (hb₁ _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (hb₁ _ (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj)⟩⟩
  obtain hN₁ : wv s₁.mem B (slot w Public.aN) w = N := by
    have := slot_le (w := w) (show Public.aN < 8 by decide)
    have : slot w Public.aN + 8 * w ≤ slot w Public.aAcc := by unfold slot Public.aN Public.aAcc; omega_using []
    rw [ho₁.wv (Or.inl (by omega_using [this])) (by omega_arith)]; exact hN
  rw [← wv_off, ← wv_off, hP, hQ] at hpq₁
  -- `p q = n`.
  refine wp_seqs_append (by decide) (by simp [checksGiven]) ?_
  refine WP.mono (eqCheck_ok hg₁ (by omega_using [hlo, hop, hoq]) (by omega_using [hwq, hwq']) (by omega_using [hw28]))
      fun s₂ ⟨hM₂, ho₂, k₂⟩ => ?_
  rw [hpq₁, hN₁, hb₁ _ (by decide), hM, mask_and] at hM₂
  obtain hb₂ : ∀ d, d + 8 ≤ 8 * Public.sMask ∨ 8 * Public.sMask + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
      word s₂.mem B d = word s₁.mem B d := fun d hd hd' => ho₂.word hd hd'
  obtain hab₂ : ∀ d, slot w 8 ≤ d → d + 8 ≤ 2 ^ 64 → word s₂.mem B d = word s.mem B d := fun d hd hd' => by
    rw [hb₂ d (Or.inr (by unfold Public.sMask sFn; omega_using [hacc, hA0, hd])) hd', hab₁ d hd hd']
  obtain hpw₂ : ∀ i < 32, word s₂.mem (off B op) (8 * i) = word s.mem (off B op) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hab₂ _ (by omega_using [hlo]) (by omega_using [hop, hoq, hn, hQ8, hi])
  obtain hqw₂ : ∀ i < 32, word s₂.mem (off B oq) (8 * i) = word s.mem (off B oq) (8 * i) := fun i hi => by
    rw [word_off, word_off]; exact hab₂ _ (by omega_using [hlo, hop]) (by omega_using [hoq, hn, hQ8, hi])
  obtain hpv₂ : ∀ d k, d + 8 * k ≤ slot wp 8 → wv s₂.mem (off B op) d k = wv s.mem (off B op) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hab₂ _ (by omega_using [hlo]) (by omega_using [hop, hoq, hn, hd, hi])
  obtain hqv₂ : ∀ d k, d + 8 * k ≤ slot wq 8 → wv s₂.mem (off B oq) d k = wv s.mem (off B oq) d k := fun d k hd => by
    rw [wv_off, wv_off]; exact wv_congr fun i hi => hab₂ _ (by omega_using [hlo, hop]) (by omega_using [hoq, hn, hd, hi])
  obtain hsP₂ : word s₂.mem B (8 * sWsP) = off B op := by
    rw [hb₂ _ (Or.inr (by unfold sWsP Public.sMask sFn; omega_using [])) (by unfold sWsP sFn; omega_using []), hb₁ _ (by decide)]
    exact hsP
  obtain hsQ₂ : word s₂.mem B (8 * sWsQ) = off B oq := by
    rw [hb₂ _ (Or.inr (by unfold sWsQ Public.sMask sFn; omega_using [])) (by unfold sWsQ sFn; omega_using []), hb₁ _ (by decide)]
    exact hsQ
  obtain hs₂ := hs.congr (k₁.trans k₂).wr
  obtain hdi₂ : s₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans hg.x0
  obtain hH₂ : Hdr s₂.mem B w minv := by
    have : ∀ i < 16, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
      rw [hb₂ _ (Or.inl (by unfold Public.sMask sFn; omega_using [hi])) (by omega_using [hi]), hb₁ _ (by omega_using [hi])]
    exact ⟨(this _ (by decide)).trans hg.hdr.hw, (this _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (this _ (by unfold sArr; omega_using [hj])).trans (hg.hdr.harr j hj)⟩
  obtain mem1 : (slot w Public.aAcc, 8 * (2 * w + 2)) ∈ [(slot w Public.aAcc, 8 * (2 * w + 2)),
      (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)] := by simp
  obtain mem2 : (8 * Public.sMask, 8) ∈ [(slot w Public.aAcc, 8 * (2 * w + 2)),
      (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)] := by simp
  obtain g12 := (Frm.of_outside ho₁ mem1).trans (Frm.of_outside ho₂ mem2)
  -- The rest.
  refine WP.mono (checksGiven_ok ⟨hs₂, hdi₂, hH₂⟩ hw28 hlo hop hoq hwp hwp' hwq hwq' hsP₂ hsQ₂
    (hwsP.of_words fun i hi => hpw₂ i (by omega_using [hi])) (hwsQ.of_words fun i hi => hqw₂ i (by omega_using [hi])) hM₂
    (by rw [hpv₂ _ _ (by have := slot_le (w := wp) (show Public.aN < 8 by decide); omega_using [this])]; exact hP)
    (by rw [hqv₂ _ _ (by have := slot_le (w := wq) (show Public.aN < 8 by decide); omega_using [this])]; exact hQ)
    (by rw [hpv₂ _ _ (by have := slot_le (w := wp) (show aChunk < 8 by decide); omega_using [this])]; exact hQI)
    hodd fun h => by simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2)
    fun t ⟨h1, h2, h3, h4, h5, h6, f, k⟩ => ⟨h1, h2, h3, h4, h5, h6, g12.trans f, ((k₁.trans k₂).trans k).mono (by decide)⟩

/-- A stage of the key checks `chk` meets `checks_ok`'s statement for a key
with `G N P Q`. -/
structure ChecksOk (chk : List (Prog isa)) (G : Nat → Nat → Nat → Prop) : Prop where
  ne : chk ≠ []
  ok : ∀ {s : State} {B : Addr} {Z w : Nat} {minv mp mq : BitVec 64} {op oq wp wq N P Q QI : Nat} {m0 : Bool},
    Good s B Z w minv → 8 ≤ w → w < 2 ^ 28 → slot w 8 ≤ op → op + slot wp 8 + wsTab wp ≤ oq →
    oq + slot wq 8 + wsTab wq ≤ Z → 2 ≤ wp → wp ≤ w → 2 ≤ wq → wq ≤ w →
    word s.mem B (8 * sWsP) = off B op → word s.mem B (8 * sWsQ) = off B oq →
    WsAt s.mem B op wp mp → WsAt s.mem B oq wq mq → wv s.mem B (slot w Public.aN) w = N →
    word s.mem B (8 * Public.sMask) = mask m0 → wv s.mem (off B op) (slot wp Public.aN) wp = P →
    wv s.mem (off B oq) (slot wq Public.aN) wq = Q → wv s.mem (off B op) (slot wp aChunk) wp = QI →
    N % 2 = 1 → G N P Q →
    WP isa (seqs chk) s fun t => Good t B Z w minv ∧
      word t.mem B (8 * Public.sMask) = mask (keyMask m0 N P Q QI) ∧
      word t.mem B (8 * sWsP) = off B op ∧ word t.mem B (8 * sWsQ) = off B oq ∧
      (∃ mp', WsAt t.mem B op wp mp' ∧ XVals t B op wp mp' (if keyMask m0 N P Q QI then P else 3) ∧
        word t.mem (off B op) (8 * sMaskX) = mask (keyMask m0 N P Q QI)) ∧
      (∃ mq', WsAt t.mem B oq wq mq' ∧ XVals t B oq wq mq' (if keyMask m0 N P Q QI then Q else 3)) ∧
      Frm B [(slot w Public.aAcc, 8 * (2 * w + 2)), (8 * Public.sMask, 8), (op, slot wp 8), (oq, slot wq 8)]
        s.mem t.mem ∧ Keep mmRegs s t

/-- `checks`, for any key. -/
theorem checks_okG : ChecksOk checks fun _ _ _ => True where
  ne := by simp [checks, checksGiven]
  ok hg hw hw28 hlo hop hoq hwp hwp' hwq hwq' hsP hsQ hwsP hwsQ hN hM hP hQ hQI hodd _ :=
    checks_ok hg hw hw28 hlo hop hoq hwp hwp' hwq hwq' hsP hsQ hwsP hwsQ hN hM hP hQ hQI hodd

/-- `checksGiven`, for a key whose factors' product is the modulus. -/
theorem checksGiven_okG : ChecksOk checksGiven fun N P Q => P * Q = N where
  ne := by simp [checksGiven]
  ok {_ _ _ _ _ _ _ _ _ _ _ N P Q QI m0} hg _ hw28 hlo hop hoq hwp hwp' hwq hwq' hsP hsQ hwsP hwsQ _ hM hP hQ hQI
      hodd hG := by
    obtain e : (m0 && decide (QI < P)) = keyMask m0 N P Q QI := by simp [keyMask, hG]
    rw [← e]
    exact checksGiven_ok hg hw28 hlo hop hoq hwp hwp' hwq hwq' hsP hsQ hwsP hwsQ hM hP hQ hQI hodd fun _ => hG

end VG.Proof.Bignum.AArch64

end

end

/-!
# RSA with the CRT on AArch64: up to the checks

From the header `entry` leaves, for a valid modulus: the modulus' setup (as
`vg_rsa_public`'s, then `c R mod n`), the primes' workspaces and the checks
(`front_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- `nSetup` after `pcLoad`: the input `c` into `X`, the mask of `c < n`
and the number 1. -/
def nInput : List (Prog isa) := [
  .block [ldh .x1 Public.sIn, ldh .x2 Public.sK, ldh .x8 (sArr Public.aX)],
  loadBE,
  .block [ldh .x12 sW, ldh .x16 (sArr Public.aX), ldh .x17 (sArr Public.aN), movi .x7 0, mov .x14 .x12,
    .subs .x .x3 .x7 .x7],
  cmpLoop,
  .block (borrowMask ++ [sth .x15 Public.sMask, ldh .x12 sW, movi .x9 1, movi .x13 0]),
  setWord Public.aOne]

theorem nHead_eq (M : Mont) : nHead M.mm = pcLoad ++ (nInput ++ r2StepsPub M.mm) := rfl

theorem nSetup_eq (M : Mont) : nSetup M.mm =
    pcLoad ++ (nInput ++ (r2StepsPub M.mm ++ [M.mm Public.aXm Public.aX Public.aR2])) := rfl

/-- `nInput`: `c` into `X`, the mask of `c < n` into `sMask`, and 1. -/
theorem nInput_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {ip : Addr} {xb : List Byte} {N : Nat}
    (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 64 ≤ k) (hk2 : k ≤ 1024)
    (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) (hIn : word s.mem B (8 * Public.sIn) = ip)
    (hx : Src s B Z ip xb) (hxl : xb.length = k)
    (hN : wv s.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = N) :
    WP isa (seqs nInput) s fun t => Good t B Z ((k + 7) / 8) minv ∧
      wv t.mem B (slot ((k + 7) / 8) Public.aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb ∧
      wv t.mem B (slot ((k + 7) / 8) Public.aOne) ((k + 7) / 8) = 1 ∧
      word t.mem B (8 * Public.sMask) = mask (decide (Spec.Rsa.os2ip xb < N)) ∧
      Frm B [(slot ((k + 7) / 8) Public.aX, 8 * ((k + 7) / 8 + 2)), (8 * Public.sMask, 8),
        (slot ((k + 7) / 8) Public.aOne, 8 * ((k + 7) / 8 + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain lX := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide)
  obtain lN := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
  obtain lO := slot_le (w := (k + 7) / 8) (show Public.aOne < 8 by decide)
  obtain sXN := slot_sep (w := (k + 7) / 8) (show Public.aX ≠ Public.aN by decide)
  obtain sXO := slot_sep (w := (k + 7) / 8) (show Public.aX ≠ Public.aOne by decide)
  obtain hX0 := hdr_lt_slot ((k + 7) / 8) Public.aX (show 31 < 32 by decide)
  obtain hO0 := hdr_lt_slot ((k + 7) / 8) Public.aOne (show 31 < 32 by decide)
  have eM : Public.sMask = 22 := rfl
  have eW : sW = 6 := rfl
  have eMi : sMinv = 7 := rfl
  simp only [nInput, seqs]
  -- `c` into `X`.
  refine WP.seq (WP.mono (WP.keep [.x1, .x2, .x8] (Q := fun t => t.gpr .x1 = ip ∧ t.gpr .x2 = BitVec.ofNat 64 k ∧
      t.gpr .x8 = off B (slot ((k + 7) / 8) Public.aX) ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show Public.sIn < 32 by decide), hdr_enc (show Public.sK < 32 by decide),
      hdr_enc (sArr_lt (show Public.aX < 8 by decide)), hg.ld hZ (show Public.sIn < 32 by decide),
      hg.ld hZ (show Public.sK < 32 by decide), hg.ld hZ (sArr_lt (show Public.aX < 8 by decide)), hIn, hK,
      hg.hdr.harr Public.aX (by decide)]) (by decide) (by decide) (by decide +kernel))
    fun s₁ ⟨⟨h1, h2, h8', hm₁⟩, k₁⟩ => ?_)
  obtain hs₁ := hs.congr k₁.wr
  refine WP.seq (WP.mono (loadArr_ok hs₁ (show Public.aX < 8 by decide) hZ
    (hx.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hxl (by omega_using [hk1]) (by omega_using [hk2]) h1 h2 h8')
    fun s₂ ⟨hX₂, ha₂, k₂⟩ => ?_)
  obtain hs₂ := hs₁.congr k₂.wr
  obtain h0₂ : s₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans hg.x0
  obtain hH₂ : Hdr s₂.mem B ((k + 7) / 8) minv :=
    ⟨by rw [ha₂.hslot (by decide), hm₁]; exact hg.hdr.hw, by rw [ha₂.hslot (by decide), hm₁]; exact hg.hdr.hminv,
      fun j hj => by rw [ha₂.hslot (sArr_lt hj), hm₁]; exact hg.hdr.harr j hj⟩
  obtain hN₂ : wv s₂.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = N := by
    rw [ha₂.wv_of_not_mem (by decide) (by decide) (by omega_using [hZ, hn]), hm₁]; exact hN
  -- `c < n`.
  refine WP.seq (WP.mono (WP.keep [.x3, .x7, .x12, .x14, .x16, .x17] (Q := fun t =>
      t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .x16 = off B (slot ((k + 7) / 8) Public.aX) ∧
      t.gpr .x17 = off B (slot ((k + 7) / 8) Public.aN) ∧ t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.c = true ∧ t.mem = s₂.mem)
    (by brun [h0₂, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show Public.aX < 8 by decide)),
      hdr_enc (sArr_lt (show Public.aN < 8 by decide)), hs₂.ld (show 8 * sW + 8 ≤ Z by
        have := hdr_lt_slot ((k + 7) / 8) 8 (show sW < 32 by decide); omega_using [hZ, this]),
      hs₂.ld (show 8 * sArr Public.aX + 8 ≤ Z by
        have := hdr_lt_slot ((k + 7) / 8) 8 (sArr_lt (show Public.aX < 8 by decide)); omega_using [hZ, this]),
      hs₂.ld (show 8 * sArr Public.aN + 8 ≤ Z by
        have := hdr_lt_slot ((k + 7) / 8) 8 (sArr_lt (show Public.aN < 8 by decide)); omega_using [hZ, this]),
      hH₂.hw, hH₂.harr Public.aX (by decide), hH₂.harr Public.aN (by decide)])
    (by decide) (by decide) (by decide +kernel))
    fun s₃ ⟨⟨h12, h16, h17, h7, h14, hc, hm₃⟩, k₃⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hs₂.congr k₃.wr) h16 h17 h14 hc (by omega_using [hk1]) (by omega_using [hk2]) (by omega_using [hZ, lX]) (by omega_using [hZ, lN]))
    fun s₄ ⟨hc₄, hm₄, k₄⟩ => ?_)
  rw [hm₃, hX₂, hN₂] at hc₄
  obtain k24 := k₃.trans k₄
  obtain h0₄ : s₄.gpr .x0 = B := (k24.gpr .x0 (by decide)).trans h0₂
  obtain h7₄ : s₄.gpr .x7 = 0 := (k₄.gpr .x7 (by decide)).trans h7
  obtain hs₄ := hs₂.congr k24.wr
  obtain hm₂₄ : s₄.mem = s₂.mem := hm₄.trans hm₃
  obtain hW' : ∀ v : BitVec 64, word (s₄.mem.writeW (off B (8 * Public.sMask)) v) B (8 * sW) =
      BitVec.ofNat 64 ((k + 7) / 8) := fun v => by
    rw [(writeW_outside s₄.mem B v (by omega_using [eM])).word (by rw [eM]; unfold sW; omega_using []) (by omega_using [eW]), hm₂₄]
    exact hH₂.hw
  -- The mask, and the operands of `setWord`.
  refine WP.seq (WP.mono (WP.keep [.x4, .x9, .x12, .x13, .x15] (Q := fun t =>
      t.mem = s₄.mem.writeW (off B (8 * Public.sMask)) (mask (!s₄.c)) ∧
      t.gpr .x12 = BitVec.ofNat 64 ((k + 7) / 8) ∧ (t.gpr .x9).toNat = 1 ∧ t.gpr .x13 = BitVec.ofNat 64 0)
    (by brun [borrowMask, h0₄, h7₄, hdr_enc (show Public.sMask < 32 by decide), hdr_enc (show sW < 32 by decide),
      hs₄.st (show 8 * Public.sMask + 8 ≤ Z by rw [eM]; omega_using [hZ, lO, hO0]),
      hs₄.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot ((k + 7) / 8) 8 (show sW < 32 by decide); omega_using [hZ, this]), hW']; cases s₄.c <;> rfl)
    (by decide) (by decide) (by decide +kernel))
    fun s₅ ⟨⟨hm₅, h12₅, h9₅, h13₅⟩, k₅⟩ => ?_)
  obtain hwo₅ : Outside B (8 * Public.sMask) 8 s₄.mem s₅.mem := by
    rw [hm₅]; exact writeW_outside _ B _ (by omega_using [eM])
  obtain hH₅ : Hdr s₅.mem B ((k + 7) / 8) minv := by
    have : ∀ i < 16, word s₅.mem B (8 * i) = word s₂.mem B (8 * i) := fun i hi => by
      rw [hwo₅.word (by rw [eM]; omega_using [hi]) (by omega_using [hi]), hm₂₄]
    exact ⟨(this _ (by decide)).trans hH₂.hw, (this _ (by decide)).trans hH₂.hminv,
      fun j hj => (this _ (by unfold sArr; omega_using [hj])).trans (hH₂.harr j hj)⟩
  obtain k25 := k24.trans k₅
  obtain hs₅ := hs₂.congr k25.wr
  refine WP.mono (setWord_ok hs₅ ((k₅.gpr .x0 (by decide)).trans h0₄) hH₅ hZ h12₅ (by omega_using [hk2]) (o := Public.aOne)
    (by decide) (i := 0) (by omega_using [hk1]) h13₅) fun t ⟨hone, ho, k₆⟩ => ?_
  have hO : Outside B (slot ((k + 7) / 8) Public.aOne) (8 * ((k + 7) / 8 + 2)) s₅.mem t.mem := ho
  refine ⟨⟨hs.congr ((k₁.trans k₂).trans (k25.trans k₆)).wr,
      (k₆.gpr .x0 (by decide)).trans ((k₅.gpr .x0 (by decide)).trans h0₄), ?_⟩, ?_, ?_, ?_, ?_,
    (((k₁.trans k₂).trans (k25.trans k₆))).mono (by decide)⟩
  · exact ⟨by rw [hO.word (by omega_using [hO0, eW]) (by omega_using [eW])]; exact hH₅.hw,
      by rw [hO.word (by omega_using [hO0, eMi]) (by omega_using [eMi])]; exact hH₅.hminv,
      fun j hj => by
        have := sArr_lt hj
        rw [hO.word (d := 8 * sArr j) (by have := hdr_lt_slot ((k + 7) / 8) Public.aOne (sArr_lt hj); omega_arith)
          (by omega_using [this])]; exact hH₅.harr j hj⟩
  · rw [hO.wv (by omega_using [sXO]) (by omega_using [hZ, hn, lX]), hwo₅.wv (by omega_using [hX0, eM]) (by omega_using [hZ, hn, lX]), hm₂₄]; exact hX₂
  · rw [hone, h9₅]
  · rw [hO.word (by omega_using [hO0, eM]) (by omega_using [eM]), hm₅, word_writeW_self, hc₄, Bool.not_not]
  · have g2 : Frm B [(slot ((k + 7) / 8) Public.aX, 8 * ((k + 7) / 8 + 2)), (8 * Public.sMask, 8),
        (slot ((k + 7) / 8) Public.aOne, 8 * ((k + 7) / 8 + 2))] s.mem s₂.mem := by
      rw [← hm₁]; exact Frm.of_arrays1 ha₂ (by simp)
    rw [← hm₂₄] at g2
    exact (g2.trans (Frm.of_outside hwo₅ (by simp))).trans (Frm.of_outside hO (by simp))

/-- What `main` starts from: the working space at `B` (its base in `x0`)
holding all three workspaces, the header `entry` leaves, and the byte
strings outside the working space. -/
structure CrtPre (s : State) (B : Addr) (Z k : Nat) (op np ip pp qp dpp dqp qip : Addr) (pl ql : Nat)
    (nb xb pb qb dpb dqb qib : List Byte) : Prop where
  scr : Scr s B Z
  x0 : s.gpr .x0 = B
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

/-- After `n`'s setup: its values, `c R mod n` and the mask of `c < n`. -/
structure NReady (s t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N C : Nat) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  xm : wv t.mem B (slot w Public.aXm) w % N = C * 2 ^ (64 * w) % N
  msk : word t.mem B (8 * Public.sMask) = mask (decide (C < N))
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

/-- After `nHead`: `n`'s values, the input `c` in `X`, and the mask of
`c < n`. -/
structure NHead (s t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N C : Nat) : Prop where
  good : Good t B Z w minv
  nv : NVals t B w minv N
  x : wv t.mem B (slot w Public.aX) w = C
  msk : word t.mem B (8 * Public.sMask) = mask (decide (C < N))
  hfix : HFix B s.mem t.mem
  iscr : InScr B Z s.mem t.mem
  keep : Keep mmRegs s t

/-- `nHead`, for a valid modulus. -/
theorem nHead_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nHead M.mm)) s fun t => ∃ minv,
      NHead s t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, hN1, hlo⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  obtain hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_using [hZq]
  obtain hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hn, hZ]
  obtain hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => Nat.le_trans (h' r hr) hZ
  obtain lN := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
  obtain lX := slot_le (w := (k + 7) / 8) (show Public.aX < 8 by decide)
  obtain lO := slot_le (w := (k + 7) / 8) (show Public.aOne < 8 by decide)
  obtain sNX := slot_sep (w := (k + 7) / 8) (show Public.aN ≠ Public.aX by decide)
  obtain sNO := slot_sep (w := (k + 7) / 8) (show Public.aN ≠ Public.aOne by decide)
  obtain hN0 := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
  rw [nHead_eq]
  -- The modulus and `-n⁻¹`.
  refine wp_seqs_append (by simp [pcLoad, pcLoadWith]) (by simp [nInput])
    (WP.mono (pcLoad_ok h.scr h.x0 hZ (by omega_using [hk1]) (by omega_using [hk2]) h.hK h.hN h.n h.nl hodd)
      fun t₁ ⟨minv, hg₁, hn₁, hi₁, f₁, k₁⟩ => ?_)
  obtain f₁' : Frm B (setupRanges ((k + 7) / 8)) s.mem t₁.mem :=
    f₁.mono (by simp [pcLoadRanges, setupRanges, loadRanges])
  obtain hh₁ := HFix.of_frm f₁' (keepsHdr_setupRanges _)
  -- The input, the mask of `c < n` and 1.
  refine wp_seqs_append (by simp [nInput]) (by simp [r2StepsPub])
    (WP.mono (nInput_ok hg₁ hZ hk1 hk2 (by rw [hh₁ _ (by decide) (by decide)]; exact h.hK)
      (by rw [hh₁ _ (by decide) (by decide)]; exact h.hIn)
      (h.x.congrK (InScr.of_frm f₁' (hZs (setupRanges_le _))) k₁) h.xl hn₁)
      fun t₂ ⟨hg₂, hX₂, hO₂, hM₂, f₂, k₂⟩ => ?_)
  obtain hN₂ : wv t₂.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [f₂.wv_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Public.sMask, sFn] <;> omega_using [sNX, hN0, sNO]) (by omega_using [hn', lN])]; exact hn₁
  obtain hI₂ : ((word t₂.mem B (slot ((k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₂.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Public.sMask, sFn] <;> omega_using [sNX, hN0, sNO]) (by omega_using [hn', lN])]; exact hi₁
  obtain f₂' : Frm B (setupRanges ((k + 7) / 8)) t₁.mem t₂.mem := f₂.mono (by simp [setupRanges, loadRanges])
  -- `R² mod n`.
  refine WP.mono (r2Pub_ok M hg₂ hZ (by omega_using [hk1]) (by omega_using [hk2]) hN₂ hI₂ hodd hlo)
    fun t₃ ⟨hg₃, hlt₃, hr₃, f₃, k₃⟩ => ?_
  obtain hX₃ : wv t₃.mem B (slot ((k + 7) / 8) Public.aX) ((k + 7) / 8) = Spec.Rsa.os2ip xb := by
    rw [f₃.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hX₂
  obtain hN₃ : wv t₃.mem B (slot ((k + 7) / 8) Public.aN) ((k + 7) / 8) = Spec.Rsa.os2ip nb := by
    rw [f₃.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hN₂
  obtain hI₃ : ((word t₃.mem B (slot ((k + 7) / 8) Public.aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [f₃.r2_word hn' (by decide) (by decide) (by decide) (by decide)]; exact hI₂
  obtain hO₃ : wv t₃.mem B (slot ((k + 7) / 8) Public.aOne) ((k + 7) / 8) = 1 := by
    rw [f₃.r2_wv hn' (by decide) (by decide) (by decide) (by decide)]; exact hO₂
  obtain e3 : word t₃.mem B (8 * Public.sMask) = word t₂.mem B (8 * Public.sMask) :=
    f₃.word_eq (r2Ranges_hdr _ (by decide) (by decide)) (by unfold Public.sMask sFn; omega_using [])
  exact ⟨minv, hg₃, ⟨hN₃, hI₃, hr₃, hlt₃, hO₃⟩, hX₃, by rw [e3]; exact hM₂,
    (hh₁.trans (HFix.of_frm f₂' (keepsHdr_setupRanges _))).trans (HFix.of_frm f₃ (keepsHdr_r2Ranges _)),
    ((InScr.of_frm f₁' (hZs (setupRanges_le _))).trans (InScr.of_frm f₂' (hZs (setupRanges_le _)))).trans
      (InScr.of_frm f₃ (hZs (r2Ranges_le _))),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `n`'s setup, for a valid modulus. -/
theorem nPart_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) :
    WP isa (seqs (nSetup M.mm)) s fun t => ∃ minv,
      NReady s t B Z ((k + 7) / 8) minv (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  obtain hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_using [hZq]
  obtain hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_using [hn, hZ]
  obtain hZs : ∀ {rs : List (Nat × Nat)}, (∀ r ∈ rs, r.1 + r.2 ≤ slot ((k + 7) / 8) 8) → ∀ r ∈ rs, r.1 + r.2 ≤ Z :=
    fun h' r hr => Nat.le_trans (h' r hr) hZ
  refine wp_seqs_append (by simp [nHead]) (by simp) (WP.mono (nHead_ok M h hv) fun t₃ ⟨minv, hh⟩ => ?_)
  -- `c R mod n`.
  simp only [seqs]
  refine WP.mono (crtMmN_ok M hh.good hZ (by omega_using [hk1]) (by omega_using [hk2]) (o := Public.aXm) (a := Public.aX) (b := Public.aR2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hh.nv.n hh.nv.inv hh.nv.r2lt)
    fun t₄ ⟨hg₄, hN₄, hI₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_
  obtain hR : Nat.Coprime (2 ^ (64 * ((k + 7) / 8))) (Spec.Rsa.os2ip nb) := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain hxm₄ : wv t₄.mem B (slot ((k + 7) / 8) Public.aXm) ((k + 7) / 8) % Spec.Rsa.os2ip nb =
      Spec.Rsa.os2ip xb * 2 ^ (64 * ((k + 7) / 8)) % Spec.Rsa.os2ip nb := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hh.x, Nat.mul_mod, hh.nv.r2, ← Nat.mul_mod, Nat.mul_assoc]
  obtain g₄ : Frm B [(slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aTmp, 8 * ((k + 7) / 8 + 2)),
      (slot ((k + 7) / 8) Public.aXm, 8 * ((k + 7) / 8 + 2))] t₃.mem t₄.mem :=
    Frm.of_arrays ha₄ fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> simp
  obtain kg₄ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * ((k + 7) / 8 + 2)),
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
  exact ⟨minv, hg₄,
    ⟨hN₄, hI₄, by rw [ha₄.wv_of_not_mem (by decide) (by decide) hn']; exact hh.nv.r2,
      by rw [ha₄.wv_of_not_mem (by decide) (by decide) hn']; exact hh.nv.r2lt,
      by rw [ha₄.wv_of_not_mem (by decide) (by decide) hn']; exact hh.nv.one⟩, hxm₄,
    by rw [ha₄.hslot (by decide)]; exact hh.msk,
    hh.hfix.trans (HFix.of_frm g₄ fun r hr => (kg₄ r hr).1),
    hh.iscr.trans (InScr.of_frm g₄ (hZs fun r hr => (kg₄ r hr).2)),
    (hh.keep.trans k₄).mono (by decide)⟩

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
  obtain hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  obtain hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_using []
  obtain hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_using [hZq]
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have hh₃ : ∀ i < 32, hFixed i = true → word t₃.mem B (8 * i) = word s.mem B (8 * i) := hr.hfix
  refine WP.mono (primesSetup_ok hr.good (by omega_using [hk1]) (by omega_using [hk2]) hZq
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hPl) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQl)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hP) (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQ)
    (by rw [hh₃ _ (by decide) (by decide)]; exact h.hQi) (h.p.congrK hr.iscr hr.keep) (h.q.congrK hr.iscr hr.keep)
    (h.qi.congrK hr.iscr hr.keep) h.pbl h.qbl h.qil h.pl1 (by have := h.pl2; omega_using [this]) h.ql1 (by have := h.ql2; omega_using [this]))
    fun t₄ ⟨hg₄, hsP₄, hsQ₄, ⟨mp, hwp₄⟩, ⟨mq, hwq₄⟩, hp₄, hc₄, hq₄, f₄, k₄⟩ => ?_
  obtain kf₄ : ∀ r ∈ [(8 * sWsP, 8), (8 * sWsQ, 8), (offP ((k + 7) / 8), slot (wsWords pl) 8 + wsTab (wsWords pl) + slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z ∧ (slot ((k + 7) / 8) 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * 31) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsP, sFn]; omega_using [hZ, h8],
        Or.inr (by simp only [sWsP, sFn]; omega_using [])⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [sWsQ, sFn]; omega_using [hZ, h8],
        Or.inr (by simp only [sWsQ, sFn]; omega_using [])⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega_using [h8]), by simp only [offP]; unfold offQ at hZq; omega_using [hZq],
        Or.inl (by simp only [offP]; omega_using [])⟩
  obtain hnv₄ : ∀ j < 8, wv t₄.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₃.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj =>
    f₄.wv_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) hj
      have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) hj; omega_using [hn, hZ, this])
  obtain hnw₄ : word t₄.mem B (slot ((k + 7) / 8) Public.aN) = word t₃.mem B (slot ((k + 7) / 8) Public.aN) :=
    f₄.word_eq (fun r hr => by
      have := kf₄ r hr
      have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide)
      have := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
      omega) (by have := slot_le (w := (k + 7) / 8) (show Public.aN < 8 by decide); omega_using [hn, hZ, this])
  obtain hM₄ : word t₄.mem B (8 * Public.sMask) = word t₃.mem B (8 * Public.sMask) := by
    refine f₄.word_eq (fun r hr => ?_) (by unfold Public.sMask sFn; omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl (by simp only [Public.sMask, sWsP, sFn]; omega_using [])
    · exact Or.inl (by simp only [Public.sMask, sWsQ, sFn]; omega_using [])
    · exact Or.inl (by simp only [offP, Public.sMask, sFn]; omega_using [h8])
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

/-- The checks, from the primes' workspaces. -/
theorem checksPart_ok {s t₄ : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte} {minv mp mq : BitVec 64}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true)
    (hr : PReady s t₄ B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
      (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksOk C G)
    (hG : G (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)) :
    WP isa (seqs C) t₄ fun t => ∃ mp' mq',
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp' mq' (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) := by
  obtain ⟨hodd, -, -⟩ := valid_facts hv h.k1
  have hk1 := h.k1
  have hk2 := h.k2
  have hZq := h.z
  have hn := h.scr.nowrap
  obtain hP8 : 256 ≤ slot (wsWords pl) 8 := by unfold slot hdrBytes; omega_using []
  obtain hQ8 : 256 ≤ slot (wsWords ql) 8 := by unfold slot hdrBytes; omega_using []
  obtain hZ : slot ((k + 7) / 8) 8 ≤ Z := by unfold offQ at hZq; omega_using [hZq]
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  obtain hwp2 : 2 ≤ wsWords pl := by unfold wsWords; omega_using []
  obtain hwq2 : 2 ≤ wsWords ql := by unfold wsWords; omega_using []
  refine WP.mono (hC.ok hr.n.good (by omega_using [hk1]) (by omega_using [hk2]) (Nat.le_refl _) (by unfold offQ; omega_using [])
    (by unfold offQ at hZq ⊢; omega_using [hZq]) hwp2 (wsWords_le (by have := h.pl2; omega_using [this]) (by omega_using [hk1])) hwq2
    (wsWords_le (by have := h.ql2; omega_using [this]) (by omega_using [hk1])) hr.wsP hr.wsQ hr.pws hr.qws hr.n.nv.n hr.n.msk hr.pv hr.qv
    hr.qiv hodd hG)
    fun t ⟨hg, hMt, hsPt, hsQt, ⟨mp', hwpt, hxpt, hmpt⟩, ⟨mq', hwqt, hxqt⟩, f₅, k₅⟩ => ?_
  obtain kf₅ : ∀ r ∈ [(slot ((k + 7) / 8) Public.aAcc, 8 * (2 * ((k + 7) / 8) + 2)), (8 * Public.sMask, 8),
      (offP ((k + 7) / 8), slot (wsWords pl) 8), (offQ ((k + 7) / 8) pl, slot (wsWords ql) 8)],
      KeepsHdr r ∧ r.1 + r.2 ≤ Z := by
    have := accs_le ((k + 7) / 8)
    have := hdr_lt_slot ((k + 7) / 8) Public.aAcc (show 31 < 32 by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl)
    · exact ⟨keepsHdr_ge (by simp only; omega_arith), by simp only; omega_arith⟩
    · exact ⟨keepsHdr_slot (by decide) (by decide), by simp only [Public.sMask, sFn]; omega_arith⟩
    · exact ⟨keepsHdr_ge (by simp only [offP]; omega_arith), by simp only [offP]; unfold offQ at hZq; omega_using [hZq]⟩
    · exact ⟨keepsHdr_ge (by simp only [offQ]; omega_arith), by simp only; omega_using [hZq]⟩
  obtain hnv₅ : ∀ j < 8, j ≠ Public.aAcc → j ≠ Public.aTmp → wv t.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) =
      wv t₄.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) := fun j hj h1 h2 => by
    have := slot_le (w := (k + 7) / 8) hj
    have := hdr_lt_slot ((k + 7) / 8) j (show 31 < 32 by decide)
    have := accs_le ((k + 7) / 8)
    have : slot ((k + 7) / 8) j + 8 * ((k + 7) / 8) ≤ slot ((k + 7) / 8) Public.aAcc ∨
        slot ((k + 7) / 8) Public.aAcc + 8 * (2 * ((k + 7) / 8) + 2) ≤ slot ((k + 7) / 8) j := by
      unfold slot Public.aAcc
      rw [show Public.aAcc = 2 from rfl] at h1
      rw [show Public.aTmp = 3 from rfl] at h2
      rcases (show j < 2 ∨ 4 ≤ j by omega_using [h1, h2]) with hj' | hj'
      · left; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show j + 1 ≤ 2 by omega_using [hj'])
        rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
      · right; have := Nat.mul_le_mul_right (8 * ((k + 7) / 8 + 2)) (show 4 ≤ j by omega_using [hj']); omega_arith
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
    obtain hN0 := hdr_lt_slot ((k + 7) / 8) Public.aN (show 31 < 32 by decide)
    rw [f₅.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have : slot ((k + 7) / 8) Public.aN + 8 ≤ slot ((k + 7) / 8) Public.aAcc := by
        unfold slot Public.aN Public.aAcc; omega_using []
      rcases hr with rfl | rfl | rfl | rfl
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inr (by simp only [Public.sMask, sFn]; omega_using [hN0])
      · exact Or.inl (by simp only; omega_arith)
      · exact Or.inl (by simp only [offQ]; omega_arith)) (by omega_arith)]
    exact hr.n.nv.inv
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.r2
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.r2lt
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.nv.one
  · rw [hnv₅ _ (by decide) (by decide) (by decide)]; exact hr.n.xm
  · exact hr.n.hfix.trans (HFix.of_frm f₅ fun r hr => (kf₅ r hr).1)
  · exact hr.n.iscr.trans (InScr.of_frm f₅ fun r hr => (kf₅ r hr).2)

/-- Up to the checks, for a valid modulus. -/
theorem front_ok (M : Mont) {s : State} {B : Addr} {Z k : Nat} {op np ip pp qp dpp dqp qip : Addr} {pl ql : Nat}
    {nb xb pb qb dpb dqb qib : List Byte}
    (h : CrtPre s B Z k op np ip pp qp dpp dqp qip pl ql nb xb pb qb dpb dqb qib)
    (hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nb) k = true) {C : List (Prog isa)} {G : Nat → Nat → Nat → Prop} (hC : ChecksOk C G)
    (hG : G (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)) :
    WP isa (seqs (nSetup M.mm ++ primesSetup ++ C)) s fun t => ∃ minv mp mq,
      CrtReady s t B Z ((k + 7) / 8) pl ql minv mp mq (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip xb)
        (Spec.Rsa.os2ip pb) (Spec.Rsa.os2ip qb)
        (keyMask (decide (Spec.Rsa.os2ip xb < Spec.Rsa.os2ip nb)) (Spec.Rsa.os2ip nb) (Spec.Rsa.os2ip pb)
          (Spec.Rsa.os2ip qb) (Spec.Rsa.os2ip qib)) :=
  wp_seqs_append (by simp [nSetup]) hC.ne (wp_seqs_append (by simp [nSetup])
    (by simp [primesSetup]) (WP.mono (nPart_ok M h hv) fun _ ⟨minv, hr⟩ =>
      WP.mono (setupPart_ok h hr) fun _ ⟨_, _, hr'⟩ =>
        WP.mono (checksPart_ok h hv hr' hC hG) fun _ ⟨mp', mq', hr''⟩ => ⟨minv, mp', mq', hr''⟩))

end VG.Proof.Bignum.AArch64
