import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Front
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Rsa.AArch64.CvHead

/-!
# A candidate on AArch64: the candidate

`Keys.head` sets up the working space for `w = out_len / 8` (`kHead_ok`);
`loadC` then loads the first `out_len` octets of `rand` into `aN`, sets its
two top bits and its low bit (`wv_candidate`), and `used := out_len`
(`loadC_ok`).
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN)

/-- `Keys.head`, for a length `k` of at least 32: `w`, the arrays' bases,
the stride, and the mask all ones (`cvHead_ok`, whose moduli are longer). -/
theorem kHead_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hk1 : 32 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z) (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block VG.Impl.Rsa.AArch64.Keys.head) s fun t =>
      Ws t B Z (wk k) ∧ word t.mem B (8 * Public.sMask) = mask true ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Public.sMask, 8)] s.mem t.mem ∧
      Keep [.x3, .x4, .x7, .x12] s t := by
  have hn := hs.nowrap
  have hZ16 : slot (wk k) 16 ≤ Z := by simp only [slot, hdrBytes, wk]; omega
  have h8 := hdr_lt_slot (wk k) 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have hl8 : slot (wk k) 8 ≤ slot (wk k) 16 := by unfold slot; omega
  unfold VG.Impl.Rsa.AArch64.Keys.head
  rw [WP.block_append_iff]
  refine WP.mono (head_ok hs h0 (by simp only [slot, hdrBytes]; omega) (by omega) hK) fun t₁ ⟨h12, hW₁, hb₁, hf₁, k₁⟩ => ?_
  have hs₁ := hs.congr k₁.wr
  have h0₁ : t₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h0
  refine WP.mono (WP.keep [.x3, .x4, .x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = (t₁.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (wk k + 2)))).writeW (off B (8 * Public.sMask)) (mask true)) (by
    brun [h0₁, h12, hdr_enc (show sStride < 32 by decide), hdr_enc (show Public.sMask < 32 by decide),
      hs₁.st (d := 8 * sStride) (by omega), hs₁.st (d := 8 * Public.sMask) (by omega),
      ofNat_add_ofNat, shl_ofNat (show ((k + 7) / 8 + 2) * 2 ^ 3 < 2 ^ 64 by omega)]
    rw [show ((k + 7) / 8 + 2) * 2 ^ 3 = 8 * (wk k + 2) by simp only [wk]; omega]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨_, hm⟩, k₂⟩ => ?_
  have o1 := writeW_outside t₁.mem B (BitVec.ofNat 64 (8 * (wk k + 2))) (d := 8 * sStride) (by omega)
  have o2 := writeW_outside (t₁.mem.writeW (off B (8 * sStride)) (BitVec.ofNat 64 (8 * (wk k + 2)))) B (mask true)
    (d := 8 * Public.sMask) (by omega)
  have hw : ∀ i < 32, i ≠ sStride → i ≠ Public.sMask → word t.mem B (8 * i) = word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => by rw [hm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  refine ⟨⟨hs₁.congr k₂.wr, (k₂.gpr .x0 (by decide)).trans h0₁, ?_, ?_, fun j hj => ?_, hZ16, show 2 ≤ (k + 7) / 8 by omega,
    show (k + 7) / 8 < 2 ^ 24 by omega⟩, by rw [hm, word_writeW_self], ?_, (k₁.trans k₂).mono (by simp)⟩
  · rw [hw sW (by decide) (by decide) (by decide)]; exact hW₁
  · rw [hm, o2.word (by omega) (by omega), word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega) (by unfold sArr sStride sFn; omega)
      (by unfold sArr Public.sMask sFn; omega)]
    exact hb₁ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    have d := hx (8 * Public.sMask, 8) (by simp)
    dsimp only at a b c d
    rw [hm, o2 x d, o1 x c, hf₁ x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> with_reducible assumption)]

/-- The top word of an array at `x16`: `x16 + 8 w − 8`. -/
theorem top_addr (B : Addr) {d w : Nat} (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    off B d + BitVec.ofNat 64 w <<< 3 - BitVec.ofNat 64 8 = off B (d + 8 * (w - 1)) := by
  rw [shl_ofNat (show w * 2 ^ 3 < 2 ^ 64 by omega), off_add, show d + w * 2 ^ 3 = d + 8 * (w - 1) + 8 by omega,
    ← off_add, BitVec.add_sub_cancel]

theorem movz_top : BitVec.setWidth 64 (49152#16) <<< (16 * 3) = BitVec.ofNat 64 (3 * 2 ^ 62) := by decide

/-- The candidate's bits, and `used := out_len`. -/
theorem candBits_ok {s : State} {B : Addr} {Z w k : Nat} (h : Ws s B Z w)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 k) :
    WP isa (.block (ws ++ base aN .x16 ++ [ld .x3 .x16, movi .x4 1, .logic .orr .x .x3 .x3 .x4, st .x3 .x16,
      .lsl .x .x5 .x12 3, .add .x .x5 .x16 .x5, .subImm .x .x5 .x5 8, ld .x3 .x5, .movz .x .x4 0xC000 3,
      .logic .orr .x .x3 .x3 .x4, st .x3 .x5, ldh .x3 kLen, sth .x3 kUsed])) s fun t =>
      wv t.mem B (slot w aN) w = Spec.RsaKeyGen.candidate (64 * w) (wv s.mem B (slot w aN) w) ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 k ∧
      Frm B [(slot w aN, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem ∧
      Keep [.x11, .x12, .x16, .x3, .x4, .x5] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have hw1 := h.w1
  have hw2 := h.w2
  have sN := h.sl (show aN < 16 by decide)
  have hU : 8 * kUsed + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hK' : 8 * kLen + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono h.ws_ok fun s₁ ⟨⟨h12, h11, m₁, _⟩, k₁⟩ => ?_
  refine WP.mono (base_ok aN .x16 ((k₁.gpr .x0 (by decide)).trans h.x0) h11) fun s₂ ⟨⟨h16, m₂, _⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have h0₂ : s₂.gpr .x0 = B := (k12.gpr .x0 (by decide)).trans h.x0
  have e12 : s₂.gpr .x12 = BitVec.ofNat 64 w := (k₂.gpr .x12 (by decide)).trans h12
  have hm₂ : s₂.mem = s.mem := m₂.trans m₁
  generalize ht : word s.mem B (slot w aN + 8 * (w - 1)) = top
  generalize hb : word s.mem B (slot w aN) = bot
  have hb₁ : word (s.mem.writeW (off B (slot w aN)) (bot ||| 1)) B (slot w aN + 8 * (w - 1)) = top := by
    rw [← ht]; exact (writeW_outside _ _ _ (by omega)).word (by omega) (by omega)
  have hK₂ : ((s.mem.writeW (off B (slot w aN)) (bot ||| 1)).writeW (off B (slot w aN + 8 * (w - 1)))
      (top ||| BitVec.ofNat 64 (3 * 2 ^ 62))).readW (off B (8 * kLen)) 64 = BitVec.ofNat 64 k := by
    rw [← hK]
    exact ((writeW_outside _ _ _ (by omega)).word (by omega) (by omega)).trans
      ((writeW_outside _ _ _ (by omega)).word (by omega) (by omega))
  have one16 : (1#16).setWidth 64 = (1 : BitVec 64) := rfl
  refine WP.mono (WP.keep [.x3, .x4, .x5] (Q := fun t => t.mem =
      ((s.mem.writeW (off B (slot w aN)) (bot ||| 1)).writeW (off B (slot w aN + 8 * (w - 1)))
        (top ||| BitVec.ofNat 64 (3 * 2 ^ 62))).writeW (off B (8 * kUsed)) (BitVec.ofNat 64 k)) (by
    brun [hm₂, h16, e12, h0₂, exec_movz_x' (show 3 < 4 by decide), movz_top, one16, hb,
      top_addr B (d := slot w aN) (w := w) (by omega) (by omega),
      hs₂.ld (d := slot w aN) (by omega), hs₂.st (d := slot w aN) (by omega),
      hs₂.ld (d := slot w aN + 8 * (w - 1)) (by omega), hs₂.st (d := slot w aN + 8 * (w - 1)) (by omega), hb₁,
      hdr_enc (show kLen < 32 by decide), hdr_enc (show kUsed < 32 by decide), hs₂.ld (d := 8 * kLen) (by omega),
      hs₂.st (d := 8 * kUsed) (by omega)]
    exact hK₂ ▸ rfl)
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₃⟩ => ⟨?_, ?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [hm, (writeW_outside _ _ _ (by omega)).wv (Or.inr hU) (by omega)]
    refine VG.Proof.RsaKeyGen.wv_candidate hw1 ?_ ?_ ?_
    · rw [(writeW_outside _ _ _ (by omega)).word (by omega) (by omega), word_writeW_self, hb]
    · rw [word_writeW_self, ht]
    · intro j h0 hj
      rw [(writeW_outside _ _ _ (by omega)).word (by omega) (by omega),
        (writeW_outside _ _ _ (by omega)).word (by omega) (by omega)]
  · rw [hm]; exact word_writeW_self _ _ _ _
  · intro x hx
    rw [hm, writeW_outside _ B _ (by omega) x (hx (8 * kUsed, 8) (by simp)),
      writeW_outside _ B _ (by omega) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega),
      writeW_outside _ B _ (by omega) x (by have := hx (slot w aN, 8 * (w + 2)) (by simp); omega)]

/-- What `loadC` changes. -/
def loadCRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Public.sMask, 8), (slot w aN, 8 * (w + 2)), (8 * kUsed, 8)]

/-- `loadC`: the working space for `w` words, the candidate from the first
`8 w` octets of `rand`, and `used := 8 w`. -/
theorem loadC_ok {s : State} {B : Addr} {Z w : Nat} {rp : Addr} {bs : List Byte} (hs : Scr s B Z)
    (h0 : s.gpr .x0 = B) (hw4 : 4 ≤ w) (hw : w ≤ 128) (hZ : 1024 * w ≤ Z)
    (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)) (hR : word s.mem B (8 * kRand) = rp)
    (hsrc : Src s B Z rp bs) (hbl : bs.length = 8 * w) :
    WP isa (seqs loadC) s fun t =>
      Ws t B Z w ∧ word t.mem B (8 * Public.sMask) = mask true ∧
      wv t.mem B (slot w aN) w = Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip bs) ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (8 * w) ∧
      Frm B (loadCRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have ew : wk (8 * w) = w := by simp only [wk]; omega
  unfold loadC
  rw [List.append_assoc]
  refine wp_seqs_append (by simp) (by simp [loadA]) ?_
  rw [seqs_one]
  refine WP.mono (kHead_ok hs h0 (by omega) (by omega) (by omega) hK) fun s₁ ⟨h₁, hM₁, f₁, k₁⟩ => ?_
  rw [ew] at h₁
  have hs₁ := h₁.scr
  have hK₁ : word s₁.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w) := by
    rw [f₁.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, kLen,
      Public.sK, sW, sArr, sStride, Public.sMask, sFn]; omega) (by simp only [kLen, Public.sK, sFn]; omega)]; exact hK
  have hR₁ : word s₁.mem B (8 * kRand) = rp := by
    rw [f₁.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, kRand,
      sW, sArr, sStride, Public.sMask, sFn]; omega) (by simp only [kRand, sFn]; omega)]; exact hR
  have i₁ : InScr B Z s.mem s₁.mem := InScr.of_frm f₁ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, sW, sArr, sStride,
      Public.sMask, sFn]; omega)
  refine wp_seqs_append (by simp [loadA]) (by simp) ?_
  refine WP.mono (loadA_ok h₁ (j := aN) (sPtr := kRand) (sLen := kLen) (by decide) (by decide) (by decide) hR₁ hK₁
    (hsrc.congrK i₁ k₁) hbl (by omega) (by omega)) fun s₂ ⟨hv₂, o₂, _, _, k₂⟩ => ?_
  have f₂ : Frm B [(slot w aN, 8 * (w + 2))] s₁.mem s₂.mem := Frm.of_outside o₂ (by simp)
  have h₂ : Ws s₂ B Z w := h₁.congrA (js := [aN]) (fun x hx => o₂ x (hx aN (by simp))) k₂ (by decide)
  have hK₂ : word s₂.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w) := by
    rw [o₂.word (by simp only [kLen, Public.sK, sFn, slot, hdrBytes, aN]; omega) (by simp only [kLen, Public.sK, sFn]; omega)]
    exact hK₁
  have hM₂ : word s₂.mem B (8 * Public.sMask) = mask true := by
    rw [o₂.word (by simp only [Public.sMask, sFn, slot, hdrBytes, aN]; omega) (by simp only [Public.sMask, sFn]; omega)]
    exact hM₁
  rw [seqs_one]
  refine WP.mono (candBits_ok h₂ hK₂) fun t ⟨hv, hu, f₃, k₃⟩ => ?_
  have hM : word t.mem B (8 * Public.sMask) = mask true := by
    rw [f₃.word_eq (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Public.sMask, sFn, slot, hdrBytes, aN, kUsed]; omega) (by simp only [Public.sMask, sFn]; omega)]; exact hM₂
  refine ⟨h₂.congr' f₃ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact KMut.ofSlot w _ _
      · exact KMut.hdr (by decide)) k₃ (by decide), hM, by rw [hv, hv₂], hu, ?_,
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  exact (f₁.mono (by simp [loadCRanges])).trans ((f₂.mono (by simp [loadCRanges])).trans (f₃.mono (by simp [loadCRanges])))

end VG.Proof.RsaKeyGen.AArch64
