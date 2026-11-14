module

public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Update
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Start
public import VerifiedGarbage.Proof.Weierstrass.X86.InvLoop
import VerifiedGarbage.Proof.Weierstrass.X86.InvHalf
import VerifiedGarbage.Proof.Weierstrass.X86.InvRead
import VerifiedGarbage.Proof.Divstep.Word32
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Monoid
import VerifiedGarbage.Proof.Rsa.X86.GcdBatch.Count
import VerifiedGarbage.Proof.Divstep.Batch

/-! # A batch at a run-time width

`words_ok`: `start_ok`, then thirty word divsteps in the header's window.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.InvBatchRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Impl.Rsa.X86.InvBatchRt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Rsa.X86.KeyRt VG.Proof.Weierstrass
open VG.Proof.Weierstrass.X86.Inv (wordClob wordState atWord)
open VG.Impl.Weierstrass.X86 (decCounter testCounter)

variable {L : Lay} {B : Addr} {Z len N : Nat}

theorem low_cong {m : Mem} {base : Addr} {d n : Nat} {x : Int}
    (h : (val32 m base d (n + 1) : Int) % 2 ^ (32 * (n + 1)) = x % 2 ^ (32 * (n + 1))) :
    ((m.readW (off base d) 32).toNat : Int) % 2 ^ 32 = x % 2 ^ 32 := by
  have D : (2 : Int) ^ 32 ∣ 2 ^ (32 * (n + 1)) := pow_dvd_pow 2 (by omega_using [])
  have E : (w32 m base d : Int) % 2 ^ 32 = (val32 m base d (n + 1) : Int) % 2 ^ 32 := by
    rw [val32]; push_cast; exact (Int.add_mul_emod_self_left _ _ _).symm
  rw [E, ← Int.emod_emod_of_dvd _ D, h, Int.emod_emod_of_dvd _ D]

/-- The window's thirty word divsteps (`GcdBatch.words_ok`). -/
theorem words_ok {s : State} (h : Bx L s B Z len N) {d f g : Int}
    (hd : s.mem.readW (off B win) 32 = BitVec.ofInt 32 d)
    (hf : (val32 s.mem B (rv (kw len) (a 4)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      f % 2 ^ (32 * (nw len + 1)))
    (hg : (val32 s.mem B (rv (kw len) (a 5)) (nw len + 1) : Int) % 2 ^ (32 * (nw len + 1)) =
      g % 2 ^ (32 * (nw len + 1)))
    (hdb : |d| + 64 < 2 ^ 30) (hfo : f % 2 = 1) :
    WP isa (.seq (.block (start L)) (VG.Impl.Weierstrass.X86.Inv.wordSteps win 30)) s fun z =>
      Bx L z B Z len N ∧ MatrixAt B (Divstep.msteps 30 (Divstep.MSt.init d f g)) z ∧
      Keeps wordClob s z ∧ Outside B win 28 s.mem z.mem := by
  have hn := h.nowrap
  have hZ := h.halfZ
  have e16 : win = 16 := rfl
  have e96 : halfSlot = 96 := rfl
  refine WP.seq (WP.mono (start_ok h) fun s₁ ⟨H₁, V₁, K₁, O₁⟩ => ?_)
  have rel : (wordState s₁.mem B win).rel (Divstep.MSt.init d f g) 32 := by
    rw [V₁]
    exact ⟨hd, rfl, rfl, rfl, rfl, low_cong hf, low_cong hg⟩
  have matrix := Divstep.W32.wsteps_rel (by decide) rel hdb hfo 30 (by decide)
  refine WP.mono (VG.Proof.Weierstrass.X86.Inv.wordSteps_ok H₁.ws.ws.workspace (t := win) (by omega_using [hZ, e16, e96])
    (by decide) (by decide)) fun z ⟨V₂, K₂, O₂⟩ => ⟨H₁.keepLow K₂ (by decide) (by decide) O₂ (by decide), ?_,
      (K₁.mono (by decide)).trans K₂, ?_⟩
  · rw [← V₂] at matrix
    obtain ⟨D, U, V, Q, R, _, _⟩ := matrix
    exact ⟨D, U, V, Q, R⟩
  · intro x hx
    rw [O₂ x hx, O₁ x (by omega_using [hx])]

end VG.Proof.Rsa.X86.InvBatchRt
