import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcStep
import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareWideRow

/-! A complete row of Montgomery reduction, retaining its pending carry. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem wv_mod_word (m : Mem) (B : Addr) (e : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m B e w % 2 ^ 64 = (word m B e).toNat := by
  rw [show w = (w - 1) + 1 by omega, wv_low]
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero,
    Nat.mod_eq_of_lt (word m B e).isLt]

/-- A number split just before and just after its word `w`. -/
theorem wv_at_word (m : Mem) (B : Addr) (e w n : Nat) (hw : w < n) :
    wv m B e n = wv m B e w + 2 ^ (64 * w) *
      ((word m B (e + 8 * w)).toNat + 2 ^ 64 * wv m B (e + 8 * w + 8) (n - (w + 1))) := by
  have hn : n = w + ((n - (w + 1)) + 1) := by omega
  have h := wv_add m B e w ((n - (w + 1)) + 1)
  rw [← hn, wv_low] at h
  exact h

/-- The multiply-add cancels its low word. -/
theorem redc_low {s t : State} {B : Addr} {e eN w C : Nat} {minv : BitVec 64} (hw : 1 ≤ w)
    (hinv : ((word s.mem B eN).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hv : wv t.mem B e w + 2 ^ (64 * w) * C = wv s.mem B e w +
      (redcU (word s.mem B e) minv).toNat * wv s.mem B eN w) : word t.mem B e = 0 := by
  have hR : 2 ^ (64 * w) % 2 ^ 64 = 0 := by
    rw [show 64 * w = 64 + 64 * (w - 1) by omega, Nat.pow_add]
    simp only [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  apply BitVec.eq_of_toNat_eq
  change (word t.mem B e).toNat = 0
  rw [← wv_mod_word _ _ _ hw]
  calc
    wv t.mem B e w % 2 ^ 64 = (wv t.mem B e w + 2 ^ (64 * w) * C) % 2 ^ 64 := by
      simp only [Nat.add_mod, Nat.mul_mod, hR, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
    _ = (wv s.mem B e w + (redcU (word s.mem B e) minv).toNat * wv s.mem B eN w) % 2 ^ 64 := congrArg (· % 2 ^ 64) hv
    _ = ((word s.mem B e).toNat + (redcU (word s.mem B e) minv).toNat * (word s.mem B eN).toNat) % 2 ^ 64 := by
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, wv_mod_word _ _ _ hw,
        Nat.mod_eq_of_lt (word s.mem B e).isLt, Nat.mod_eq_of_lt (word s.mem B eN).isLt]
    _ = 0 := by
      rw [Nat.add_comm]
      exact mont_low _ _ _ hinv

/-- One row shifts away the canceled word; the high carry remains separate
until the last row. -/
theorem redcRow_ok {s : State} {B : Addr} {Z e w n : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (h8 : s.gpr .r8 = off B e)
    (h9 : s.gpr .r9 = off B (slot w aN)) (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (hwn : w < n) (he : hdrBytes ≤ e)
    (heZ : e + 8 * n ≤ Z) (hsep : slot w aN + 8 * w ≤ e)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0) :
    WP isa AdxSquare.redcRow s fun t => ∃ u < 2 ^ 64,
      2 ^ 64 * (wv t.mem B (e + 8) (n - 1) + 2 ^ (64 * w) * (t.gpr .r10).toNat) =
        wv s.mem B e n + 2 ^ (64 * w) * (s.gpr .r10).toNat + u * wv s.mem B (slot w aN) w ∧
      ((s.gpr .r10).toNat ≤ 1 → (t.gpr .r10).toNat ≤ 1) ∧
      Outside B e (8 * (w + 1)) s.mem t.mem ∧ t.gpr .r8 = off B (e + 8) ∧
      t.zf = some (decide (e + 8 = slot w aTmp)) ∧
      Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s t := by
  have hn := hs.nowrap
  have hN := slot_le (w := w) (show aN < 8 by decide)
  unfold AdxSquare.redcRow
  refine WP.seq (WP.mono (redcHead_ok hs hdi hH h8 (by omega) hZ) fun s₁ ⟨hdx, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (AdxSquareWide.row_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h8)
    ((k₁.gpr (by decide)).trans h9) ((k₁.gpr (by decide)).trans hbp) (by omega) (by omega)
    (by omega) (by omega) (by omega)) fun s₂ ⟨hv, ho, h14, k₂⟩ => ?_)
  rw [hm₁, hdx] at hv
  rw [hm₁] at ho
  have k12 := k₁.trans k₂
  have hlow := redc_low (by omega) hinv hv
  have top : word s₂.mem B (e + 8 * w) = word s.mem B (e + 8 * w) := ho.word (by omega) (by omega)
  have c10 : s₂.gpr .r10 = s.gpr .r10 := k12.gpr (by decide)
  refine WP.seq (WP.mono (redcTail_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans h8)
    h14 (by omega)) fun s₃ ⟨lo, hm₃, ht, hc, h8₃, k₃⟩ => ?_)
  rw [top, c10] at ht
  rw [c10] at hc
  have out₃ : Outside B (e + 8 * w) 8 s₂.mem s₃.mem := by
    rw [hm₃]; exact writeW_outside _ _ _ (by omega)
  have allout : Outside B e (8 * (w + 1)) s.mem s₃.mem :=
    (ho.mono (o' := e) (n' := 8 * (w + 1)) (Nat.le_refl _) (by omega)).trans
      (out₃.mono (o' := e) (n' := 8 * (w + 1)) (by omega) (by omega))
  have low₃ : word s₃.mem B e = 0 := (out₃.word (by omega) (by omega)).trans hlow
  have pre₃ : wv s₃.mem B e w = wv s₂.mem B e w := out₃.wv (by omega) (by omega)
  have top₃ : word s₃.mem B (e + 8 * w) = lo := by rw [hm₃, word_writeW_self]
  have high₃ : wv s₃.mem B (e + 8 * w + 8) (n - (w + 1)) =
      wv s.mem B (e + 8 * w + 8) (n - (w + 1)) := allout.wv (by omega) (by omega)
  have eq : wv s₃.mem B e n + 2 ^ (64 * w) * 2 ^ 64 * (s₃.gpr .r10).toNat =
      wv s.mem B e n + 2 ^ (64 * w) * (s.gpr .r10).toNat +
        (redcU (word s.mem B e) minv).toNat * wv s.mem B (slot w aN) w := by
    rw [wv_at_word _ _ _ _ _ hwn, wv_at_word s.mem _ _ _ _ hwn, pre₃, top₃, high₃]
    grind
  have shifted : wv s₃.mem B e n = 2 ^ 64 * wv s₃.mem B (e + 8) (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, wv_low, low₃]
    simp
  rw [shifted] at eq
  have k123 := k12.trans k₃
  refine WP.mono (VG.Proof.Bignum.X86_64.rowEnd_ok (hs.congr k123.2.2)
    ((k123.gpr (by decide)).trans hdi) (hH.of_outside allout he) hZ h8₃ (by omega))
    fun t ⟨hz, hm, h8', kt⟩ => ?_
  refine ⟨(redcU (word s.mem B e) minv).toNat, (redcU (word s.mem B e) minv).isLt, ?_, ?_, ?_, h8', hz, (k123.trans kt).mono (by simp)⟩
  · rw [hm, kt.gpr (by decide)]
    grind
  · rw [kt.gpr (by decide)]; exact hc
  · rw [hm]; exact allout

end VG.Proof.Bignum.X86_64.AdxSquare
