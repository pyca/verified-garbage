import VerifiedGarbage.Proof.Rsa.X86_64.RpProd
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad

/-!
# `vg_rsa_recover_primes` on x86-64: whether `d e - 1` is even and positive

`skipBlk` takes the mask of `M = d e` even and clears `M`'s low bit (`m =
M - 1` for an odd `M`); the loop of `orBody` tests `m = 0`, and `skipTest`
sets `ZF` to neither (`skip_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Recover
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- A word's low bit, as a word. -/
theorem and_one (x : BitVec 64) : x &&& 1 = BitVec.ofNat 64 (x.toNat % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x.toNat % 2 < 2 ^ 64 by omega)]

/-- The mask of an even word, from its low bit. -/
theorem low_sub_one (x : BitVec 64) : (x &&& 1) - 1 = mask (decide (x.toNat % 2 = 0)) := by
  rw [and_one]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

/-- A word minus its low bit. -/
theorem sub_low (x : BitVec 64) : (x - (x &&& 1)).toNat = x.toNat - x.toNat % 2 := by
  rw [and_one, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

/-- `Bw = w + ⌈e_len / 8⌉` into `rax` (`bw`). -/
theorem bw_val (w el : Nat) (hel : el < 2 ^ 32) :
    (BitVec.ofNat 64 el + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 + BitVec.ofNat 64 w =
      BitVec.ofNat 64 (w + (el + 7) / 8) := by
  rw [shr3_w el hel, BitVec.ofNat_add_ofNat, Nat.add_comm]

/-- `skipBlk`. -/
theorem skipBlk_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (hel' : el < 2 ^ 32) :
    WP isa (.block skipBlk) s fun t =>
      t.gpr .rbx = off B (slot w aM) ∧ t.gpr .rbp = 0 ∧ t.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
      t.gpr .rdi = B ∧
      t.mem = (s.mem.writeW (off B (slot w aM)) (word s.mem B (slot w aM) - (word s.mem B (slot w aM) &&& 1))).writeW
        (off B (8 * sC2)) (mask (decide ((word s.mem B (slot w aM)).toNat % 2 = 0))) ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx, .rbp] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sM := h.sl (j := aM) (by decide)
  have hM0 := hdr_lt_slot w aM (show sC2 < 32 by decide)
  unfold skipBlk
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono h.ws_ok fun t₁ ⟨_, h9, m₁, k₁⟩ => WP.block_append_iff.mpr ?_
  refine WP.mono (base_ok aM (r := .rbx) (by decide) ((k₁.gpr (by decide)).trans h.rdi) h9)
    fun t₂ ⟨hbx, m₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := h.scr.congr k12.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans h.rdi
  have hl : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => hs₂.ld (by omega)
  have hW : word t₂.mem B (8 * sW) = BitVec.ofNat 64 w := by rw [m₂, m₁]; exact h.hw
  have hE : word t₂.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el := by rw [m₂, m₁]; exact hel
  refine WP.mono (WP.keep [.rax, .rdx, .rcx, .r12, .rbp] (Q := fun t => t.gpr .rbp = 0 ∧
    t.gpr .r12 = BitVec.ofNat 64 (w + (el + 7) / 8) ∧
    t.mem = (t₂.mem.writeW (off B (slot w aM)) (word t₂.mem B (slot w aM) - (word t₂.mem B (slot w aM) &&& 1))).writeW
        (off B (8 * sC2)) (mask (decide ((word t₂.mem B (slot w aM)).toNat % 2 = 0)))) (by
      xrun [State.ea, hdr, at0, hdi₂, hdrOff, hbx, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs₂.ld (d := slot w aM) (by omega), hs₂.st (d := slot w aM) (by omega), hl _ (show sW < 32 by decide),
        hl _ (show Impl.Bignum.X86_64.Public.sElen < 32 by decide), hW, hE, bw_val w el hel',
        hs₂.st (d := 8 * sC2) (by omega)]
      rw [low_sub_one]) rfl)
    fun t ⟨⟨hbp, h12, mt⟩, k₃⟩ => ⟨(k₃.gpr (by decide)).trans hbx, hbp, h12, (k₃.gpr (by decide)).trans hdi₂,
      by rw [mt, m₂, m₁], (k12.trans k₃).mono (by decide)⟩

/-- The loop of `orBody`: `rbp = 0` iff the `N` words at `rbx` are. -/
theorem orLoop_ok {s : State} {B : Addr} {Z N e : Nat} (hs : Scr s B Z) (hbx : s.gpr .rbx = off B e)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 N) (hbp : s.gpr .rbp = 0) (hN1 : 1 ≤ N) (hN : N < 2 ^ 31)
    (he : e + 8 * N ≤ Z) :
    WP isa (wordLoop 0 orBody) s fun t =>
      (t.gpr .rbp = 0 ↔ wv s.mem B e N = 0) ∧ t.mem = s.mem ∧ Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      OrInv s B Z (fun j => True ∧ ∀ i < j, word s.mem B (e + 8 * i) = 0) 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s.gpr .rbp), hbp]
      exact ⟨fun _ => ⟨trivial, fun i hi => absurd hi (Nat.not_lt_zero _)⟩, fun _ => rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := N) (by omega) hN _ h0
    (fun j _ hj t hI => orStep_ok hbx h12 (by omega) he hj hI)) fun t hI => ?_
  refine ⟨?_, hI.mem, hI.keep⟩
  rw [hI.val, wv_eq_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

/-- `skipTest`: `ZF` set iff `m = 0` or `M` is even. -/
theorem skipTest_ok {s : State} {B : Addr} {Z : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : 8 * 32 ≤ Z)
    {z : Prop} [Decidable z] (hz : s.gpr .rbp = 0 ↔ z) {c : Bool} (hm : word s.mem B (8 * sC2) = mask c) :
    WP isa (.block skipTest) s fun t =>
      t.zf = some (decide (¬ z ∧ c = false)) ∧ t.mem = s.mem ∧ Keep [.rax, .rbp] s t := by
  have hn := hs.nowrap
  have e : decide (s.gpr .rbp = 0) = decide z := by
    by_cases hz' : z
    · rw [decide_eq_true hz', decide_eq_true (hz.mpr hz')]
    · rw [decide_eq_false hz', decide_eq_false (fun h => hz' (hz.mp h))]
  unfold skipTest
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.zf = some (decide (¬ z ∧ c = false)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k⟩
  xrun [State.ea, hdr, hdi, hdrOff, hs.ld (d := 8 * sC2) (by simp only [sC2, sFn]; omega), hm, decide_lt_one', e]
  rw [show (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide z))) = mask (decide z) from rfl, BitVec.and_self]
  by_cases hz' : z <;> cases c <;> simp [hz'] <;> decide

/-- `M` with its low bit cleared: `M - M mod 2`. -/
theorem clearLow_wv (m : Mem) (B : Addr) {e n : Nat} (hn : 1 ≤ n) (hen : B.toNat + e + 8 * n ≤ 2 ^ 64) :
    wv (m.writeW (off B e) (word m B e - (word m B e &&& 1))) B e n = wv m B e n - wv m B e n % 2 := by
  have o := writeW_outside m B (word m B e - (word m B e &&& 1)) (d := e) (by omega)
  rw [wv_low hn, wv_low (m := m) hn, word_writeW_self, sub_low, o.wv (Or.inr (by omega)) (by omega)]
  have := (word m B e).isLt
  omega

/-- The test of `skip`: `ZF` clear iff `M` is odd and above 1; then `M`'s
array holds `m = M - 1`. -/
theorem skip_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {el : Nat}
    (hel : word s.mem B (8 * Impl.Bignum.X86_64.Public.sElen) = BitVec.ofNat 64 el) (he1 : 1 ≤ el)
    (he2 : el ≤ 8 * w)
    (hM : wv s.mem B (slot w aM) (2 * (w + 2)) < 2 ^ (64 * (w + (el + 7) / 8))) :
    WP isa (seqs [.block skipBlk, wordLoop 0 orBody, .block skipTest]) s fun t =>
      t.zf = some (decide (wv s.mem B (slot w aM) (2 * (w + 2)) % 2 = 1 ∧ 2 ≤ wv s.mem B (slot w aM) (2 * (w + 2)))) ∧
      wv t.mem B (slot w aM) (2 * (w + 2)) =
        wv s.mem B (slot w aM) (2 * (w + 2)) - wv s.mem B (slot w aM) (2 * (w + 2)) % 2 ∧
      Frm B [(slot w aM, 8), (8 * sC2, 8)] s.mem t.mem ∧ t.gpr .rdi = B ∧
      Keep [.r12, .r9, .rbx, .rax, .rdx, .rcx, .rbp, .r14] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have sM := slot_lt (w := w) (show aM + 1 < 16 by decide)
  have hZ := h.hZ
  have eM1 : slot w (aM + 1) = slot w aM + 8 * (w + 2) := by simp only [slot, hdrBytes, aM]; omega
  have hM0 := hdr_lt_slot w aM (show sC2 < 32 by decide)
  have hw1 := h.w1
  have hw2 := h.w2
  have sMM : slot w aM + 16 * (w + 2) ≤ Z := by rw [eM1] at sM; omega
  simp only [seqs]
  refine WP.seq (WP.mono (skipBlk_ok h hel (by omega)) fun s₁ ⟨hbx, hbp, h12, hdi, m₁, k₁⟩ => ?_)
  have hs₁ := h.scr.congr k₁.2.2
  -- `m` in `M`'s arrays, and `M`'s parity in `sC2`.
  have o₂ := writeW_outside (s.mem.writeW (off B (slot w aM)) (word s.mem B (slot w aM) -
    (word s.mem B (slot w aM) &&& 1))) B (mask (decide ((word s.mem B (slot w aM)).toNat % 2 = 0))) (d := 8 * sC2)
    (by omega)
  have hm : wv s₁.mem B (slot w aM) (2 * (w + 2)) =
      wv s.mem B (slot w aM) (2 * (w + 2)) - wv s.mem B (slot w aM) (2 * (w + 2)) % 2 := by
    rw [m₁, o₂.wv (Or.inr (by omega)) (by omega), clearLow_wv _ _ (by omega) (by omega)]
  have hpar : (word s.mem B (slot w aM)).toNat % 2 = wv s.mem B (slot w aM) (2 * (w + 2)) % 2 := by
    rw [wv_low (show 1 ≤ 2 * (w + 2) by omega)]; omega
  have hc : word s₁.mem B (8 * sC2) = mask (decide (wv s.mem B (slot w aM) (2 * (w + 2)) % 2 = 0)) := by
    rw [m₁, word_writeW_self, hpar]
  -- `m = 0`.
  refine WP.seq (WP.mono (orLoop_ok hs₁ hbx h12 hbp (by omega) (by have := h.w2; omega)
    (by omega)) fun s₂ ⟨hz, m₂, k₂⟩ => ?_)
  have hlt : wv s₁.mem B (slot w aM) (2 * (w + 2)) < 2 ^ (64 * (w + (el + 7) / 8)) := by rw [hm]; omega
  rw [wv_low_of_lt (by omega) hlt, hm] at hz
  refine WP.mono (skipTest_ok (hs₁.congr k₂.2.2) ((k₂.gpr (by decide)).trans hdi) h256 hz
    (c := decide (wv s.mem B (slot w aM) (2 * (w + 2)) % 2 = 0)) (by rw [m₂]; exact hc)) fun t ⟨hzf, mt, k₃⟩ => ⟨?_, by rw [mt, m₂, hm], ?_,
      (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans hdi), ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [hzf]
    congr 1
    simp only [decide_eq_decide, decide_eq_false_iff_not]
    omega
  · intro x hx
    have a := hx (slot w aM, 8) (by simp)
    have b := hx (8 * sC2, 8) (by simp)
    dsimp only at a b
    rw [mt, m₂, m₁, o₂ x b, writeW_outside s.mem B _ (d := slot w aM) (by omega) x a]

end VG.Proof.Rsa.X86_64
