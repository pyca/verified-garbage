module
public import VerifiedGarbage.Impl.Ffdh.AArch64.ParameterCandidate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs

import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# An FFDH parameter candidate on AArch64: drawing a witness

The pieces of `draw` before the round: the test of the tape's octets left
(`roomHead_ok`), the next `sK` octets into `aX` (`drawLoad_ok`, as RSA's
`witLoad_ok` for any length), its top word cut (`drawCut_ok`, `wv_cut`), and
the mask of `2 ≤ x ≤ N − 2` (`drawRange_ok`, from RSA's `witLow_ok` and
`witCmp_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The test of the tape's octets left: `x5 = 0` iff fewer than `len`. -/
theorem roomHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {r : List Byte} {used len : Nat}
    (hlen' : len < 2 ^ 32) (hrl : r.length < 2 ^ 64) (hul : used ≤ r.length)
    (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 len)
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) :
    WP isa (.block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag)) s fun t =>
      isa.eval (.zero .x .x5) t = some (decide (r.length < used + len)) ∧ t.mem = s.mem ∧
        Keep [.x3, .x4, .x5, .x7] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have e1 : BitVec.ofNat 64 r.length - BitVec.ofNat 64 used = BitVec.ofNat 64 (r.length - used) :=
    ofNat_sub_ofNat' hul hrl
  have r1 : s.mem.readW (B + BitVec.ofNat 64 (8 * kRandLen)) 64 = BitVec.ofNat 64 r.length := hrlen
  have r2 : s.mem.readW (B + BitVec.ofNat 64 (8 * kUsed)) 64 = BitVec.ofNat 64 used := hus
  have r3 : s.mem.readW (B + BitVec.ofNat 64 (8 * kLen)) 64 = BitVec.ofNat 64 len := hlen
  refine (WP.block_append_iff (M := isa)
    (l₁ := ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] : List Instr))).mpr ?_
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (r.length - used) ∧
      t.gpr .x4 = BitVec.ofNat 64 len ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kRandLen < 32 by decide), hdr_enc (show kUsed < 32 by decide),
      hdr_enc (show kLen < 32 by decide), h.scr.ld (d := 8 * kRandLen) (by simp only [kRandLen, sFn]; omega_arith),
      h.scr.ld (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega_arith),
      h.scr.ld (d := 8 * kLen) (by simp only [kLen, sK, sFn]; omega_arith), r1, r2, r3, e1])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h3, h4, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (geFlag_ok s₁) fun t ⟨⟨h5, hm⟩, k⟩ => ⟨?_, hm.trans hm₁, (k₁.trans k).mono (by decide)⟩
  rw [eval_zero, h5, h3, h4, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show r.length - used < 2 ^ 64 by omega_arith)]
  rcases Nat.lt_or_ge r.length (used + len) with hl | hl
  · rw [decide_eq_false (show ¬(len ≤ r.length - used) by omega_arith), decide_eq_true hl]; rfl
  · rw [decide_eq_true (show len ≤ r.length - used by omega_arith), decide_eq_false (show ¬(r.length < used + len) by omega_arith)]
    rfl

/-- The witness's octets into `aX`, `len` of them. -/
theorem drawLoad_ok {s : State} {B : Addr} {Z w len : Nat} (h : Ws s B Z w) {rp : Addr} {u : Nat}
    {bs : List Byte} (hR : word s.mem B (8 * kRand) = rp) (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * w)
    (hsrc : Src s B Z (rp + BitVec.ofNat 64 u) bs) (hbl : bs.length = len) :
    WP isa (seqs [zeroA aX, .block (ws ++ base aX .x8 ++ [ldh .x1 kRand, ldh .x3 kUsed, .add .x .x1 .x1 .x3,
        ldh .x2 kLen, .add .x .x3 .x3 .x2, sth .x3 kUsed]), loadBE]) s fun t =>
      wv t.mem B (slot w aX) w = Spec.Rsa.os2ip bs ∧ word t.mem B (8 * kUsed) = BitVec.ofNat 64 (u + len) ∧
      Frm B [(slot w aX, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem ∧ Ws t B Z w ∧ Keep mmRegs s t := by
  have hn := h.scr.nowrap
  have sj := h.sl (show aX < 16 by decide)
  have hw2 := h.w2
  have hw1 := h.w1
  have hUs : 8 * kUsed + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  simp only [seqs]
  refine WP.seq (WP.mono (zeroA_ok h (show aX < 16 by decide)) fun s₁ ⟨hz₁, o₁, _, _, _, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr (Frm.of_outside o₁ (List.mem_singleton_self _)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Mut.ofSlot w aX _) k₁ (by decide)
  have hh : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    o₁.word (Or.inl (by have := hdr_lt_slot w aX hi; omega_using [this])) (by omega_using [hi])
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono h₁.ws_ok fun s₂ ⟨⟨h12, h11, m₂, _⟩, k₂⟩ =>
    WP.mono (base_ok aX .x8 ((k₂.gpr .x0 (by decide)).trans h₁.x0) h11) fun s₃ ⟨⟨h8, m₃, _⟩, k₃⟩ =>
      WP.mono (WP.keep [.x1, .x3, .x2] (Q := fun t => t.gpr .x1 = rp + BitVec.ofNat 64 u ∧
        t.gpr .x2 = BitVec.ofNat 64 len ∧
        t.mem = s₃.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (u + len))) (by
          have h0₃ : s₃.gpr .x0 = B := ((k₂.trans k₃).gpr .x0 (by decide)).trans h₁.x0
          have hs₃ := h₁.scr.congr (k₂.trans k₃).wr
          have hl₃ : ∀ i < 32, InRegions (s₃.rd ++ s₃.wr) (off B (8 * i)) 8 := fun i hi =>
            hs₃.ld (by have := h.h256; omega_using [hi, this])
          brun [h0₃, hdr_enc (show kRand < 32 by decide), hdr_enc (show kUsed < 32 by decide),
            hdr_enc (show kLen < 32 by decide), m₃, m₂, hl₃ kRand (by decide), hl₃ kUsed (by decide),
            hl₃ kLen (by decide), hs₃.st (d := 8 * kUsed) (by omega_using [sj, hUs]), hh kRand (by decide),
            hh kUsed (by decide), hh kLen (by decide), hR, hU, hK, BitVec.ofNat_add])
        (by decide) (by decide) (by decide +kernel))
      fun s₄ ⟨⟨h1, h2, m₄⟩, k₄⟩ => ?_)))
  have k14 := ((k₁.trans k₂).trans k₃).trans k₄
  have hs₄ := h.scr.congr k14.wr
  have hm₃ : s₃.mem = s₁.mem := m₃.trans m₂
  have oU : Outside B (8 * kUsed) 8 s₁.mem s₄.mem := by rw [m₄, hm₃]; exact writeW_outside _ _ _ (by omega_using [hn, sj, hUs])
  have hsrc₄ : Src s₄ B Z (rp + BitVec.ofNat 64 u) bs := hsrc.congrK (fun x hx => by
    rw [oU x (Or.inr (by omega_using [sj, hUs, hx])), o₁ x (Or.inr (by omega_using [sj, hx]))]) k14
  refine WP.mono (loadBE_ok (w := (len + 7) / 8) hs₄ h1 h2 ((k₄.gpr .x8 (by decide)).trans h8) hbl hl1
    (by omega_using [hlw, hw2]) rfl (by omega_using [sj, hlw]) (fun i hi => hsrc₄.rd i (by omega_using [hbl, hi]))
        (fun i hi => hsrc₄.val i (by omega_using [hbl, hi]))
    (fun i hi => Or.inr (by have := hsrc₄.out i (by omega_using [hbl, hi]); omega_using [sj, this, hlw])))
    fun t ⟨hv, o, k₅⟩ => ?_
  have F : Frm B [(slot w aX, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem :=
    ((Frm.of_outside o₁ (by simp)).trans (Frm.of_outside oU (by simp))).trans
      (Frm.of_outside (o.mono (o' := slot w aX) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [hlw])) (by simp))
  refine ⟨?_, ?_, F, h.congr' F (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact KMut.ofSlot w _ _
      · exact KMut.hdr (by simp [kUsed, sFn, sW, sStride, sArr])) (k14.trans k₅) (by decide),
    (k14.trans k₅).mono (by decide)⟩
  · -- The words above the loaded ones are still zero.
    have hz' : ∀ q < w + 2, word s₁.mem B (slot w aX + 8 * q) = 0 := (wv_eq_zero_iff _ _ _ _).mp hz₁
    have e := wv_add t.mem B (slot w aX) ((len + 7) / 8) (w - (len + 7) / 8)
    rw [show (len + 7) / 8 + (w - (len + 7) / 8) = w by omega_arith] at e
    rw [e, hv, wv_zero (n := w - (len + 7) / 8) fun q hq => by
        rw [o.word (by omega_arith) (by omega_arith), Nat.add_assoc, ← Nat.mul_add,
          oU.word (by omega_arith) (by omega_arith)]; exact hz' _ (by omega_arith)]
    simp
  · rw [o.word (Or.inl (by omega_using [hUs])) (by omega_using [hn, sj, hUs]), m₄, word_writeW_self]


/-- The cut: `aX`'s top word and'ed with `fTop = 2^k − 1`. -/
theorem drawCut_ok {s : State} {B : Addr} {Z w k : Nat} (h : Ws s B Z w) (hk : k ≤ 64)
    (hT : word s.mem B (8 * fTop) = BitVec.ofNat 64 (2 ^ k - 1)) :
    WP isa (.block (ws ++ base aX .x16 ++ ([.lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8,
      ldh .x4 fTop, ld .x3 .x5, .logic .and .x .x3 .x3 .x4, st .x3 .x5] : List Instr))) s fun t =>
      wv t.mem B (slot w aX) w = wv s.mem B (slot w aX) w % 2 ^ (64 * (w - 1) + k) ∧
      Frm B [(slot w aX, 8 * (w + 2))] s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have sX := h.sl (show aX < 16 by decide)
  have hTs : 8 * fTop + 8 ≤ slot w aX := hdr_lt_slot w aX (by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aX .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have h0₂ : s₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  generalize ht : word s.mem B (slot w aX + 8 * (w - 1)) = top
  refine WP.mono (WP.keep [.x3, .x4, .x5] (Q := fun t => t.mem =
      s.mem.writeW (off B (slot w aX + 8 * (w - 1))) (top &&& BitVec.ofNat 64 (2 ^ k - 1))) (by
    brun [hm₂, h16, e12, h0₂, ht, hT, top_addr B (d := slot w aX) (w := w) (by omega_arith) (by omega_arith),
      hs₂.ld (d := slot w aX + 8 * (w - 1)) (by omega_arith), hs₂.st (d := slot w aX + 8 * (w - 1)) (by omega_arith),
      hdr_enc (show fTop < 32 by decide), hs₂.ld (d := 8 * fTop) (by omega_arith)])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ⟨?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [hm]
    refine VG.Proof.Ffdh.ParameterCandidate.wv_cut (by omega_arith) hk ?_ ?_
    · rw [word_writeW_self, ht]
    · intro j hj
      rw [(writeW_outside _ _ _ (by omega_arith)).word (by omega_arith) (by omega_arith)]
  · intro x hx
    rw [hm, writeW_outside _ B _ (by omega_arith) x (by have := hx (slot w aX, 8 * (w + 2)) (by simp); omega_arith)]

/-- The range: `x9 := ` the mask of `2 ≤ x` and `(x | 1) < N`. -/
theorem drawRange_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {X : Nat}
    (hX : wv s.mem B (slot w aX) w = X) :
    WP isa (seqs [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) s fun t =>
      t.gpr .x9 = mask (decide (2 ≤ X) && decide (X + (1 - X % 2) < wv s.mem B (slot w aN) w)) ∧
        t.mem = s.mem ∧ Keep mmRegs s t := by
  have e : ([.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
      countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16],
      .block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]),
      cmpLoop,
      .block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]] : List (Prog isa)) =
      [.block (ws ++ base aX .x16 ++ [ld .x5 .x16, .lsr .x .x5 .x5 1, next .x16, .subImm .x .x14 .x12 1]),
        countLoop .x14 [ld .x3 .x16, .logic .orr .x .x5 .x5 .x3, next .x16]] ++
      ([.block ([movi .x7 0, .subImm .x .x8 .x7 1, movi .x4 1, .subs .x .x3 .x5 .x4, .csel .x .x9 .x8 .x7] ++ ws ++
        base aX .x16 ++ base aN .x17 ++ [ld .x3 .x16, .logic .orr .x .x3 .x3 .x4, ld .x4 .x17, .subs .x .x3 .x3 .x4,
        next .x16, next .x17, .subImm .x .x14 .x12 1]), cmpLoop] ++
      [.block [.csel .x .x15 .x7 .x8, .logic .and .x .x9 .x9 .x15]]) := rfl
  rw [e]
  refine wp_seqs_append (by simp) (by simp) (WP.mono (witLow_ok h) fun s₁ ⟨hl₁, hm₁, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr' (rs := []) (by rw [hm₁]; exact Frm.refl _ _ _) (by simp) k₁ (by decide)
  refine wp_seqs_append (by simp) (by simp) (WP.mono (witCmp_ok h₁ (X := X) (by rw [hm₁]; exact hX)
    (by rw [hX] at hl₁; exact hl₁)) fun s₂ ⟨h9₂, hc₂, h7₂, h8₂, _, _, hm₂, k₂⟩ => ?_)
  rw [seqs_one]
  refine WP.mono (WP.keep [.x15, .x9] (Q := fun t => t.gpr .x9 =
      mask (decide (2 ≤ X) && decide (X + (1 - X % 2) < wv s.mem B (slot w aN) w)) ∧ t.mem = s₂.mem) (by
    brun [h9₂, hc₂, h7₂, h8₂]
    rw [hm₁]
    cases decide (2 ≤ X) <;> cases decide (X + (1 - X % 2) < wv s.mem B (slot w aN) w) <;> rfl)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h9, hm⟩, k₃⟩ =>
    ⟨h9, by rw [hm, hm₂, hm₁], ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- For an odd `N`: `(x | 1) < N` iff `x < N − 1`. -/
theorem or1_lt_iff {X N : Nat} (hN : N % 2 = 1) : X + (1 - X % 2) < N ↔ X < N - 1 := by omega_arith

end VG.Proof.Ffdh.AArch64.ParameterCandidate
