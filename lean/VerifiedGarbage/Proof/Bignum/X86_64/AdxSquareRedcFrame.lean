import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareRedcStep

/-! The reduction row's memory and public-control behavior, even when the
header's inverse does not match the modulus. -/

namespace VG.Proof.Bignum.X86_64.AdxSquare

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem redcRow_frame {s : State} {B : Addr} {Z e w : Nat} {minv : BitVec 64}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv)
    (hZ : slot w 8 ≤ Z) (h8 : s.gpr .r8 = off B e)
    (h9 : s.gpr .r9 = off B (slot w aN)) (hbp : s.gpr .rbp = BitVec.ofNat 64 w)
    (hw1 : 2 ≤ w) (hw : w < 2 ^ 31) (he : hdrBytes ≤ e)
    (heZ : e + 8 * (w + 1) ≤ Z) (hsep : slot w aN + 8 * w ≤ e) :
    WP isa AdxSquare.redcRow s fun t =>
      Outside B e (8 * (w + 1)) s.mem t.mem ∧ t.gpr .r8 = off B (e + 8) ∧
      t.zf = some (decide (e + 8 = slot w aTmp)) ∧
      Keep [.rdx, .rax, .rsi, .r11, .r12, .r13, .r15, .rcx, .r14, .rbx, .r10, .r8] s t := by
  have hn := hs.nowrap
  have hN := slot_le (w := w) (show aN < 8 by decide)
  unfold AdxSquare.redcRow
  refine WP.seq (WP.mono (redcHead_ok hs hdi hH h8 (by omega) hZ) fun s₁ ⟨_, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (macRow_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h8)
    ((k₁.gpr (by decide)).trans h9) ((k₁.gpr (by decide)).trans hbp) (by omega)
    (by omega) (by omega) (by omega)) fun s₂ ⟨_, ho, h14, k₂⟩ => ?_)
  rw [hm₁] at ho
  have k12 := k₁.trans k₂
  refine WP.seq (WP.mono (redcTail_ok (hs.congr k12.2.2) ((k12.gpr (by decide)).trans h8)
    h14 (by omega)) fun s₃ ⟨lo, hm₃, _, _, h8₃, k₃⟩ => ?_)
  have out₃ : Outside B (e + 8 * w) 8 s₂.mem s₃.mem := by
    rw [hm₃]; exact writeW_outside _ _ _ (by omega)
  have allout : Outside B e (8 * (w + 1)) s.mem s₃.mem :=
    (ho.mono (o' := e) (n' := 8 * (w + 1)) (Nat.le_refl _) (by omega)).trans
      (out₃.mono (o' := e) (n' := 8 * (w + 1)) (by omega) (by omega))
  have k123 := k12.trans k₃
  refine WP.mono (VG.Proof.Bignum.X86_64.rowEnd_ok (hs.congr k123.2.2)
    ((k123.gpr (by decide)).trans hdi) (hH.of_outside allout he) hZ h8₃ (by omega))
    fun t ⟨hz, hm, h8', kt⟩ => ⟨?_, h8', hz, (k123.trans kt).mono (by simp)⟩
  rw [hm]; exact allout

end VG.Proof.Bignum.X86_64.AdxSquare
