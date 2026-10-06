import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.AArch64.R2
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Rsa.AArch64.Div

/-!
# A candidate on AArch64: too close to `p`

`subA o a b`: `[o] := [a] − [b]` and its borrow (`subA_ok`). `closeCheck`
loads `p` into `aX`, puts `c − p` in `aAcc` and `p − c` in `aTmp`, selects
the latter under the mask of the former's borrow: `|c − p|`; then compares
the bound `2^(64 w − 100)` (`aY`, by `setWord`) with it, and leaves the mask
of `|c − p| ≤ 2^(64 w − 100)`, or 0 without `p`, in `x15`
(`closeCheck_ok`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aY)

theorem subs_self_c (x : BitVec 64) :
    decide (2 ^ 64 ≤ x.toNat + (~~~x).toNat + true.toNat) = true := by
  rw [BitVec.toNat_not, show true.toNat = 1 from rfl]; have := x.isLt; exact decide_eq_true (by omega)

/-- The middle of `subA`'s head: `x7 := 0`, `x15` all ones, `x14 := w` and the
carry set. -/
theorem subAMid_ok (s : State) {w : Nat} (h12 : s.gpr .x12 = BitVec.ofNat 64 w) :
    WP isa (.block [movi .x7 0, .subImm .x .x15 .x7 1, mov .x14 .x12, .subs .x .x3 .x7 .x7]) s fun t =>
      (t.gpr .x7 = 0 ∧ t.gpr .x15 = mask true ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s.mem) ∧
        Keep [.x7, .x15, .x14, .x3] s t := by
  refine WP.keep [.x7, .x15, .x14, .x3] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h12, subs_self_c]

/-- `subA o a b`: `[o] := [a] − [b]` over `w` words, the carry flag clear on
a borrow, and `x7 = 0`. -/
theorem subA_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {o a b : Nat} (ho : o < 16) (ha : a < 16)
    (hb : b < 16) (hoa : o = a ∨ o ≠ a) (hob : o ≠ b) :
    WP isa (seqs (subA o a b)) s fun t =>
      wv t.mem B (slot w o) w + wv s.mem B (slot w b) w = wv s.mem B (slot w a) w + 2 ^ (64 * w) * (!t.c).toNat ∧
      Outside B (slot w o) (8 * w) s.mem t.mem ∧ t.gpr .x7 = 0 ∧ t.gpr .x12 = BitVec.ofNat 64 w ∧
      t.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) ∧
      Keep [.x11, .x12, .x7, .x15, .x14, .x3, .x16, .x17, .x8, .x4] s t := by
  have hn := h.scr.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have so := h.sl ho
  have sa := h.sl ha
  have sb := h.sl hb
  unfold subA
  simp only [seqs, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ =>
    WP.block_append_iff.mpr (WP.mono (subAMid_ok s₁ h12) fun s₂ ⟨⟨h7, h15, h14, hc, m₂⟩, k₂⟩ => ?_)))
  have h0₂ : s₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans h.x0
  have h11₂ : s₂.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2)) := (k₂.gpr .x11 (by decide)).trans h11
  have h12₂ : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  refine WP.block_append_iff.mpr (WP.mono (base_ok a .x16 h0₂ h11₂) fun s₃ ⟨⟨h16, m₃, c₃⟩, k₃⟩ =>
    WP.block_append_iff.mpr (WP.mono (base_ok b .x17 ((k₃.gpr .x0 (by decide)).trans h0₂)
      ((k₃.gpr .x11 (by decide)).trans h11₂)) fun s₄ ⟨⟨h17, m₄, c₄⟩, k₄⟩ =>
    WP.mono (base_ok o .x8 (((k₃.trans k₄).gpr .x0 (by decide)).trans h0₂)
      (((k₃.trans k₄).gpr .x11 (by decide)).trans h11₂)) fun s₅ ⟨⟨h8, m₅, c₅⟩, k₅⟩ => ?_))
  have k35 := (k₃.trans k₄).trans k₅
  have k15 := ((k₁.trans k₂).trans k35)
  refine WP.mono (subM_ok (N := w) (c := true) (h.scr.congr k15.wr) (((k₄.trans k₅).gpr .x16 (by decide)).trans h16)
    ((k₅.gpr .x17 (by decide)).trans h17) h8 ((k35.gpr .x14 (by decide)).trans h14)
    ((k35.gpr .x15 (by decide)).trans h15)
    (by rw [c₅, c₄, c₃]; exact hc) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by rcases hoa with rfl | hne
        · exact .inl rfl
        · exact .inr ((slot_sep (w := w) (Ne.symm hne)).elim (fun h => .inl (by omega)) (fun h => .inr (by omega))))
    ((slot_sep (w := w) (Ne.symm hob)).elim (fun h => .inl (by omega)) (fun h => .inr (by omega))))
    fun t ⟨hv, o', k₆⟩ => ?_
  have hm : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  rw [hm] at hv o'
  simp only [ite_true] at hv
  have k36 := k35.trans k₆
  exact ⟨by omega, o', (k36.gpr .x7 (by decide)).trans h7, (k36.gpr .x12 (by decide)).trans h12₂,
    (k36.gpr .x11 (by decide)).trans h11₂, (k15.trans k₆).mono (by simp)⟩

/-- What `closeCheck` changes. -/
def closeRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aX, 8 * (w + 2)), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
    (8 * kT0, 8)]

theorem closeRanges_mut (w : Nat) : ∀ r ∈ closeRanges w, KMut r := by
  simp only [closeRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl)
  · exact KMut.ofSlot w _ _
  · exact KMut.ofSlot w _ _
  · exact KMut.ofSlot w _ _
  · exact KMut.ofSlot w _ _
  · exact KMut.hdr (by simp [kT0, Public.sCnt, sFn, sArr, sStride])

/-- The borrow's mask, kept in `kT0`. -/
theorem closeMask_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (h7 : s.gpr .x7 = 0) :
    WP isa (.block (borrowMask ++ [sth .x15 kT0])) s fun t =>
      (t.gpr .x15 = mask (!s.c) ∧ t.mem = s.mem.writeW (off B (8 * kT0)) (mask (!s.c))) ∧ Keep [.x4, .x15] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  refine WP.keep [.x4, .x15] ?_ (by decide) (by decide) (by decide +kernel)
  brun [borrowMask, h7, csel_mask_not, h.x0, hdr_enc (show kT0 < 32 by decide), hs.st (d := 8 * kT0) (by
    simp only [kT0, Public.sCnt, sFn]; omega)]

/-- The selection's head: `x15` the mask in `kT0`, `x14 := w`, `x16` at `aTmp`
and `x17` at `aAcc`. -/
theorem closeSelHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {b : Bool}
    (hT : word s.mem B (8 * kT0) = mask b) :
    WP isa (.block (ws ++ [ldh .x15 kT0, mov .x14 .x12] ++ base aTmp .x16 ++ base aAcc .x17)) s fun t =>
      (t.gpr .x15 = mask b ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.gpr .x16 = off B (slot w aTmp) ∧
        t.gpr .x17 = off B (slot w aAcc) ∧ t.mem = s.mem) ∧ Keep [.x11, .x12, .x15, .x14, .x16, .x17] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_)
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x15, .x14] (Q := fun t => t.gpr .x15 = mask b ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.mem = s₁.mem) (by
    brun [h0₁, h12, m₁, hdr_enc (show kT0 < 32 by decide), (hs.congr k₁.wr).ld (d := 8 * kT0) (by
      simp only [kT0, Public.sCnt, sFn]; omega), hT]) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h15, h14, m₂⟩, k₂⟩ => ?_)
  refine WP.mono (base2_ok aTmp aAcc .x16 .x17 ((k₂.gpr .x0 (by decide)).trans h0₁)
    ((k₂.gpr .x11 (by decide)).trans h11)) fun t ⟨⟨h16, h17, m₃, _⟩, k₃⟩ => ?_
  exact ⟨⟨(k₃.gpr .x15 (by decide)).trans h15, (k₃.gpr .x14 (by decide)).trans h14, h16, h17,
    by rw [m₃, m₂, m₁]⟩, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

/-- The comparison's head: `x7 := 0`, `x14 := w`, the carry set, `x16` at
`aY` and `x17` at `aAcc`. -/
theorem closeCmpHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base aY .x16 ++ base aAcc .x17)) s
      fun t => (t.gpr .x7 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.gpr .x16 = off B (slot w aY) ∧
        t.gpr .x17 = off B (slot w aAcc) ∧ t.mem = s.mem) ∧ Keep [.x11, .x12, .x7, .x14, .x3, .x16, .x17] s t := by
  simp only [List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_)
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.x7, .x14, .x3] (Q := fun t => t.gpr .x7 = 0 ∧
      t.gpr .x14 = BitVec.ofNat 64 w ∧ t.c = true ∧ t.mem = s₁.mem) (by
    brun [h12, subs_self_c]) (by decide) (by decide) (by decide +kernel))
    fun s₂ ⟨⟨h7, h14, hc, m₂⟩, k₂⟩ => ?_)
  refine WP.mono (base2_ok aY aAcc .x16 .x17 ((k₂.gpr .x0 (by decide)).trans h0₁)
    ((k₂.gpr .x11 (by decide)).trans h11)) fun t ⟨⟨h16, h17, m₃, c₃⟩, k₃⟩ => ?_
  exact ⟨⟨(k₃.gpr .x7 (by decide)).trans h7, (k₃.gpr .x14 (by decide)).trans h14, c₃.trans hc, h16, h17,
    by rw [m₃, m₂, m₁]⟩, ((k₁.trans k₂).trans k₃).mono (by simp)⟩

theorem movz_2p28 : BitVec.setWidth 64 (4096#16) <<< (16 * 1) = BitVec.ofNat 64 (2 ^ 28) := by decide

/-- The bound's head: `x12 := w`, `x9 := 2^28`, `x13 := w − 2`. -/
theorem closeBound_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) :
    WP isa (.block [ldh .x12 sW, .movz .x .x9 0x1000 1, .subImm .x .x13 .x12 2]) s fun t =>
      (t.gpr .x12 = BitVec.ofNat 64 w ∧ t.gpr .x9 = BitVec.ofNat 64 (2 ^ 28) ∧
        t.gpr .x13 = BitVec.ofNat 64 (w - 2) ∧ t.mem = s.mem) ∧ Keep [.x12, .x9, .x13] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw1 := h.w1
  refine WP.keep [.x12, .x9, .x13] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h.x0, hdr_enc (show sW < 32 by decide), hs.ld (d := 8 * sW) (by unfold sW; omega), h.hw,
    exec_movz_x' (show 1 < 4 by decide), movz_2p28]
  exact BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; have := h.w2; omega)

theorem closeCheck_eq : closeCheck = [.block [ldh .x3 kPlen, movi .x15 0],
    .ite (.zero .x .x3) (.block []) (seqs (loadA aX kP kPlen ++ (subA aAcc aN aX ++
      (([.block (borrowMask ++ ([sth .x15 kT0] : List Instr))] : List (Prog isa)) ++ (subA aTmp aX aN ++
      ([.block (ws ++ [ldh .x15 kT0, mov .x14 .x12] ++ base aTmp .x16 ++ base aAcc .x17), VG.Impl.Rsa.AArch64.Crt.selLoop,
        .block [ldh .x12 sW, .movz .x .x9 0x1000 1, .subImm .x .x13 .x12 2], setWord aY,
        .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base aY .x16 ++ base aAcc .x17),
        cmpLoop, .block carryMask] : List (Prog isa)))))))] := by
  simp only [closeCheck, List.append_assoc, List.cons_append, List.nil_append]

theorem otherPrime_ne {pB : List Byte} (h : pB.length ≠ 0) :
    Spec.RsaKeyGen.otherPrime pB = some (Spec.Rsa.os2ip pB) := by
  unfold Spec.RsaKeyGen.otherPrime; rw [ite_eq_right_iff.mpr (fun e => absurd (by rw [e]; rfl) h)]

theorem tooClose_some {L c p : Nat} :
    Spec.RsaKeyGen.tooClose L (some p) c = decide (Spec.RsaKeyGen.absDiff c p ≤ 2 ^ (L - 100)) := rfl

/-- `closeCheck`: the mask of the candidate in `aN` being too close to `p`
in `x15`. -/
theorem closeCheck_ok {s : State} {B : Addr} {Z w : Nat} {pP : Addr} {pB : List Byte} (h : Ws s B Z w)
    (hw4 : 4 ≤ w) (hP : word s.mem B (8 * kP) = pP) (hPl : word s.mem B (8 * kPlen) = BitVec.ofNat 64 pB.length)
    (hpl : pB.length = 0 ∨ pB.length = 8 * w) (psrc : Src s B Z pP pB) :
    WP isa (seqs closeCheck) s fun t =>
      t.gpr .x15 = mask (Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime pB)
        (wv s.mem B (slot w aN) w)) ∧
      Ws t B Z w ∧ Frm B (closeRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have sX := h.sl (show aX < 16 by decide)
  have sA := h.sl (show aAcc < 16 by decide)
  have sT := h.sl (show aTmp < 16 by decide)
  have sY := h.sl (show aY < 16 by decide)
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  rw [closeCheck_eq]
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3, .x15] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 pB.length ∧
      t.gpr .x15 = 0 ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kPlen < 32 by decide), hl kPlen (by decide), hPl])
    (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h3, h15, m₁⟩, k₁⟩ => ?_)
  have h₁ : Ws s₁ B Z w := h.congr' (rs := []) (fun x _ => by rw [m₁]) (by simp) k₁ (by decide)
  have hpl64 : pB.length < 2 ^ 64 := by omega
  refine WP.ite (decide (pB.length = 0)) (by rw [eval_zero, h3, ofNat64_beq_zero hpl64]) (fun hb => ?_) (fun hb => ?_)
  · -- No `p`.
    have hp0 : pB = [] := List.eq_nil_of_length_eq_zero (of_decide_eq_true hb)
    refine WP.block_nil ⟨?_, h₁, fun x _ => by rw [m₁], k₁.mono (by decide)⟩
    rw [h15, hp0]; simp [Spec.RsaKeyGen.otherPrime, Spec.RsaKeyGen.tooClose, mask_false]
  -- `p` of `8 w` octets.
  have hp8 : pB.length = 8 * w := by
    rcases hpl with hp | hp
    · simp [hp] at hb
    · exact hp
  have hlen8 : 1 ≤ pB.length ∧ pB.length ≤ 8 * w := by omega
  -- The slots, as numbers.
  have eN : slot w aN = 256 := by simp [slot, hdrBytes, aN]
  have eX : slot w aX = 256 + 8 * (w + 2) := by simp [slot, hdrBytes, aX]
  have eA : slot w aAcc = 256 + 16 * (w + 2) := by simp [slot, hdrBytes, aAcc]; omega
  have eT : slot w aTmp = 256 + 24 * (w + 2) := by simp [slot, hdrBytes, aTmp]; omega
  have eY : slot w aY = 256 + 48 * (w + 2) := by simp [slot, hdrBytes, aY]; omega
  have eK : 8 * kT0 = 8 * 26 := rfl
  generalize hc : wv s.mem B (slot w aN) w = c
  refine wp_seqs_append (by simp [loadA]) (by simp) ?_
  refine WP.mono (loadA_ok h₁ (j := aX) (sPtr := kP) (sLen := kPlen) (by decide) (by decide) (by decide)
    (by rw [m₁]; exact hP) (by rw [m₁, hPl, hp8]) (psrc.congrK (fun x _ => by rw [m₁]) k₁) hp8 (by omega)
    (by omega)) fun s₂ ⟨hv₂, o₂, _, _, k₂⟩ => ?_
  rw [m₁] at o₂
  have f₂ : Frm B (closeRanges w) s.mem s₂.mem := Frm.of_outside o₂ (by simp [closeRanges])
  have h₂ : Ws s₂ B Z w := h.congr' f₂ (closeRanges_mut w) (k₁.trans k₂) (by decide)
  refine wp_seqs_append (by simp [subA]) (by simp) ?_
  refine WP.mono (subA_ok h₂ (o := aAcc) (a := aN) (b := aX) (by decide) (by decide) (by decide)
    (.inr (by decide)) (by decide)) fun s₃ ⟨hv₃, o₃, h7₃, _, _, k₃⟩ => ?_
  have f₃ : Frm B (closeRanges w) s.mem s₃.mem :=
    f₂.trans (Frm.of_outside (o₃.mono (o' := slot w aAcc) (n' := 8 * (w + 2)) (le_refl _) (by omega)) (by simp [closeRanges]))
  have h₃ : Ws s₃ B Z w := h.congr' f₃ (closeRanges_mut w) ((k₁.trans k₂).trans k₃) (by decide)
  have cN₂ : wv s₂.mem B (slot w aN) w = c := by rw [← hc, o₂.wv (by omega) (by omega)]
  rw [cN₂] at hv₃
  generalize hb : (!s₃.c) = b at hv₃
  refine wp_seqs_append (by simp) (by simp [subA]) ?_
  refine WP.mono (closeMask_ok h₃ h7₃) fun s₄ ⟨⟨_, hm₄⟩, k₄⟩ => ?_
  rw [hb] at hm₄
  have o₄ : Outside B (8 * kT0) 8 s₃.mem s₄.mem := by rw [hm₄]; exact writeW_outside _ _ _ (by omega)
  have f₄ : Frm B (closeRanges w) s.mem s₄.mem := f₃.trans (Frm.of_outside o₄ (by simp [closeRanges]))
  have h₄ : Ws s₄ B Z w := h.congr' f₄ (closeRanges_mut w) (((k₁.trans k₂).trans k₃).trans k₄) (by decide)
  have hT₄ : word s₄.mem B (8 * kT0) = mask b := by rw [hm₄]; exact word_writeW_self _ _ _ _
  refine wp_seqs_append (by simp [subA]) (by simp) ?_
  refine WP.mono (subA_ok h₄ (o := aTmp) (a := aX) (b := aN) (by decide) (by decide) (by decide)
    (.inr (by decide)) (by decide)) fun s₅ ⟨hv₅, o₅, _, _, _, k₅⟩ => ?_
  have f₅ : Frm B (closeRanges w) s.mem s₅.mem :=
    f₄.trans (Frm.of_outside (o₅.mono (o' := slot w aTmp) (n' := 8 * (w + 2)) (le_refl _) (by omega)) (by simp [closeRanges]))
  have h₅ : Ws s₅ B Z w := h.congr' f₅ (closeRanges_mut w) ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅)
    (by decide)
  have cN₄ : wv s₄.mem B (slot w aN) w = c := by
    rw [o₄.wv (by omega) (by omega), o₃.wv (by omega) (by omega), cN₂]
  have cX₄ : wv s₄.mem B (slot w aX) w = Spec.Rsa.os2ip pB := by
    rw [o₄.wv (by omega) (by omega), o₃.wv (by omega) (by omega), hv₂]
  rw [cN₄, cX₄] at hv₅
  have cA₅ : wv s₅.mem B (slot w aAcc) w = wv s₃.mem B (slot w aAcc) w := by
    rw [o₅.wv (by omega) (by omega), o₄.wv (by omega) (by omega)]
  have hT₅ : word s₅.mem B (8 * kT0) = mask b := by rw [o₅.word (by omega) (by omega), hT₄]
  simp only [seqs]
  refine WP.seq (WP.mono (closeSelHead_ok h₅ hT₅) fun s₆ ⟨⟨h15₆, h14₆, h16₆, h17₆, m₆⟩, k₆⟩ => ?_)
  have hs₆ := h₅.scr.congr k₆.wr
  refine WP.seq (WP.mono (VG.Proof.Bignum.AArch64.selLoop_ok hs₆ h16₆ h17₆ h14₆ h15₆ (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun s₇ ⟨hv₇, o₇, k₇⟩ => ?_)
  rw [m₆, cA₅] at hv₇
  rw [m₆] at o₇
  have f₇ : Frm B (closeRanges w) s.mem s₇.mem :=
    f₅.trans (Frm.of_outside (o₇.mono (o' := slot w aAcc) (n' := 8 * (w + 2)) (le_refl _) (by omega)) (by simp [closeRanges]))
  have k17 := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k₇
  have h₇ : Ws s₇ B Z w := h.congr' f₇ (closeRanges_mut w) k17 (by decide)
  refine WP.seq (WP.mono (closeBound_ok h₇) fun s₈ ⟨⟨h12₈, h9₈, h13₈, m₈⟩, k₈⟩ => ?_)
  have h₈ : Ws s₈ B Z w := h₇.congr' (rs := []) (fun x _ => by rw [m₈]) (by simp) k₈ (by decide)
  refine WP.seq (WP.mono (setWord_ok h₈.scr h₈.x0 h₈.good.1.hdr h₈.good.2 h12₈ (by omega) (o := aY) (by decide)
    (i := w - 2) (by omega) h13₈) fun s₉ ⟨hv₉, o₉, k₉⟩ => ?_)
  rw [h9₈] at hv₉
  rw [m₈] at o₉
  have f₉ : Frm B (closeRanges w) s.mem s₉.mem := f₇.trans (Frm.of_outside o₉ (by simp [closeRanges]))
  have k19 := (k17.trans k₈).trans k₉
  have h₉ : Ws s₉ B Z w := h.congr' f₉ (closeRanges_mut w) k19 (by decide)
  refine WP.seq (WP.mono (closeCmpHead_ok h₉) fun s₁₀ ⟨⟨h7₁₀, h14₁₀, hc₁₀, h16₁₀, h17₁₀, m₁₀⟩, k₁₀⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (h₉.scr.congr k₁₀.wr) h16₁₀ h17₁₀ h14₁₀ hc₁₀ (by omega) (by omega) (by omega)
    (by omega)) fun s₁₁ ⟨hc₁₁, m₁₁, k₁₁⟩ => ?_)
  refine WP.mono (carryMask_ok s₁₁ ((k₁₁.gpr .x7 (by decide)).trans h7₁₀)) fun t ⟨⟨h15, mt, _⟩, k₁₂⟩ => ?_
  have k1t := ((k19.trans k₁₀).trans k₁₁).trans k₁₂
  have hmt : t.mem = s₉.mem := by rw [mt, m₁₁, m₁₀]
  refine ⟨?_, h.congr' (by rw [hmt]; exact f₉) (closeRanges_mut w) k1t (by decide), by rw [hmt]; exact f₉,
    k1t.mono (by decide)⟩
  -- The value.
  rw [h15, hc₁₁, m₁₀]
  have hY : wv s₉.mem B (slot w aY) w = 2 ^ (64 * w - 100) := by
    rw [hv₉, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), ← Nat.pow_add]; congr 1; omega
  have hA : wv s₉.mem B (slot w aAcc) w = Spec.RsaKeyGen.absDiff c (Spec.Rsa.os2ip pB) := by
    rw [o₉.wv (by omega) (by omega), hv₇]
    have l1 := wv_lt s₃.mem B (slot w aAcc) w
    have l2 := wv_lt s₅.mem B (slot w aTmp) w
    have l3 : c < 2 ^ (64 * w) := hc ▸ wv_lt _ _ _ _
    have l4 : Spec.Rsa.os2ip pB < 2 ^ (64 * w) := cX₄ ▸ wv_lt _ _ _ _
    generalize (!s₅.c) = b5 at hv₅
    unfold Spec.RsaKeyGen.absDiff
    cases b <;> cases b5 <;> simp only [Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
      Nat.add_zero, Bool.false_eq_true, ↓reduceIte] at hv₃ hv₅ ⊢ <;> split <;> omega
  rw [hY, hA, otherPrime_ne (by omega), tooClose_some]
  congr 1
  rw [← decide_not]; exact decide_eq_decide.mpr Nat.not_lt


end VG.Proof.RsaKeyGen.AArch64
