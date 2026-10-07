import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Tile

/-! The outer tiles implement Montgomery reduction for any valid inverse. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

structure RedcInv (s₀ : State) (B : Addr) (Z w i : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  rcx : s.gpr .rcx = off B (slot w aAcc + 16 + 64 * i)
  keep : Keep mmRegs s₀ s
  out : Outside B (slot w aAcc) (16 * w + 32) s₀.mem s.mem
  val : ((word s₀.mem B (slot w aN)).toNat * mi.toNat + 1) % 2 ^ 64 = 0 →
    ∃ q < 2 ^ (512 * i),
      2 ^ (512 * i) * (wv s.mem B (slot w aAcc + 16 + 64 * i) (2 * w - 8 * i) +
        2 ^ (64 * w) * (word s.mem B (slot w aAcc + 16 + 64 * i - 16)).toNat) =
      wv s₀.mem B (slot w aAcc + 16) (2 * w) + q * wv s₀.mem B (slot w aN) w

theorem digit512_bound {q P u : Nat} (hq : q < P) (hu : u < 2 ^ 512) : q + P * u < P * 2 ^ 512 := by
  have hb := radix_bound hq hu
  exact hb

theorem tileStep_ok {s₀ s : State} {B : Addr} {Z w n i : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : w = 8 * n) (hi : i < n) (h : RedcInv s₀ B Z w i mi s) :
    WP isa AdxRotate8.tile s fun t => t.zf = some (decide (i + 1 = n)) ∧ RedcInv s₀ B Z w (i + 1) mi t := by
  have hn := h.scr.nowrap
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hTs := slot_le (w := w) (show aTmp < 8 by decide)
  have hsN : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hhh : hdrBytes + 16 ≤ slot w aAcc + 16 + 64 * i := by unfold slot; omega
  refine WP.mono (tile_ok (L := 2 * w - 8 * i) h.scr h.rdi h.hdr hZ
    (show w = 8 * ((n - 1) + 1) by omega) h.rcx hhh (by omega) (by omega) (by omega))
    fun t ⟨vt, ct, zt, ot, kt⟩ => ?_
  have mn : wv s.mem B (slot w aN) w = wv s₀.mem B (slot w aN) w := h.out.wv (by omega) (by omega)
  have mn0 : word s.mem B (slot w aN) = word s₀.mem B (slot w aN) := h.out.word (by omega) (by omega)
  refine ⟨?_, ⟨h.scr.congr kt.2.2, h.hdr.of_outside ot (by omega),
    (kt.gpr (by decide)).trans h.rdi, ?_, (h.keep.trans kt).mono (by decide),
    h.out.trans (ot.mono (by omega) (by omega)), ?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [ct]
    exact congrArg (off B) (by omega)
  · intro hinv
    obtain ⟨q, hq, eq⟩ := h.val hinv
    obtain ⟨u, hu, eu⟩ := vt (by rw [mn0]; exact hinv)
    rw [mn, show slot w aAcc + 16 + 64 * i + 64 = slot w aAcc + 16 + 64 * (i + 1) by omega,
      show 2 * w - 8 * i - 8 = 2 * w - 8 * (i + 1) by omega,
      show slot w aAcc + 16 + 64 * i + 48 = slot w aAcc + 16 + 64 * (i + 1) - 16 by omega] at eu
    refine ⟨q + 2 ^ (512 * i) * u, ?_, ?_⟩
    · rw [show 512 * (i + 1) = 512 * i + 512 by omega, Nat.pow_add]
      exact digit512_bound hq hu
    · rw [show 512 * (i + 1) = 512 * i + 512 by omega, Nat.pow_add]
      have hv := extend_tiles (P := 2 ^ (512 * i)) (R := 2 ^ 512)
        (X := wv s.mem B (slot w aAcc + 16 + 64 * i) (2 * w - 8 * i) +
          2 ^ (64 * w) * (word s.mem B (slot w aAcc + 16 + 64 * i - 16)).toNat)
        (Y := wv t.mem B (slot w aAcc + 16 + 64 * (i + 1)) (2 * w - 8 * (i + 1)) +
          2 ^ (64 * w) * (word t.mem B (slot w aAcc + 16 + 64 * (i + 1) - 16)).toNat)
        (T := wv s₀.mem B (slot w aAcc + 16) (2 * w))
        (q := q) (u := u) (N := wv s₀.mem B (slot w aN) w) eq eu
      exact hv
end VG.Proof.Bignum.X86_64.AdxRotate8
