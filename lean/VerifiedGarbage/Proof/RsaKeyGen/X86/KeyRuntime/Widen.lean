module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Copy
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import VerifiedGarbage.Proof.Framework.Omega

/-! # Widening between banks reuses the shared clear and copy operations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem widenTo_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    (target w : Width) (out src : Loc) (width : w.words n ≤ target.words n)
    (fit : out.offset n + 4 * (target.words n + 2) ≤ Z) (sourceBound : src.offset n + 4 * w.words n ≤ Z)
    (separate : src.offset n + 4 * w.words n ≤ out.offset n ∨
      out.offset n + 4 * (target.words n + 2) ≤ src.offset n) :
    WP isa (widenTo target w out src) s fun t => Ws t B Z n N ∧
      Outside B (out.offset n) (4 * (target.words n + 2)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (target.words n + 2) = val32 s.mem B (src.offset n) (w.words n) ∧
      val32 t.mem B (out.offset n) (target.words n) = val32 s.mem B (src.offset n) (w.words n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  unfold widenTo
  refine WP.seq (WP.mono (zero_ok h target out fit) fun u ⟨hu, Ou, zero, Ku⟩ => ?_)
  change Outside B (out.offset n) (4 * (target.words n + 2)) s.mem u.mem at Ou
  change val32 u.mem B (out.offset n) (target.words n + 2) = 0 at zero
  have source : val32 u.mem B (src.offset n) (w.words n) =
      val32 s.mem B (src.offset n) (w.words n) := Ou.val32 separate (by omega)
  have high : val32 u.mem B (out.offset n + 4 * w.words n) (target.words n + 2 - w.words n) = 0 :=
    VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (by change _ ≤ target.words n + 2; omega)
  refine WP.mono (copy_loc_ok hu w out src (by omega) sourceBound (by omega))
    fun t ⟨ht, Ot, copied, Kt⟩ => ?_
  have highT : val32 t.mem B (out.offset n + 4 * w.words n) (target.words n + 2 - w.words n) = 0 := by
    rw [Ot.val32 (Or.inr (Nat.le_refl _)) (by omega), high]
  have full : val32 t.mem B (out.offset n) (target.words n + 2) = val32 s.mem B (src.offset n) (w.words n) := by
    have append := val32_append t.mem B (out.offset n) (w.words n) (target.words n + 2 - w.words n)
    rw [show w.words n + (target.words n + 2 - w.words n) = target.words n + 2 by omega,
      highT, Nat.mul_zero, Nat.add_zero, copied, source] at append
    exact append
  have bound : val32 t.mem B (out.offset n) (target.words n + 2) < 2 ^ (32 * target.words n) := by
    rw [full]
    exact Nat.lt_of_lt_of_le (val32_lt s.mem B (src.offset n) (w.words n))
      (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨ht, Ou.trans (Ot.mono (Nat.le_refl _) (by omega)), full,
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega : target.words n ≤ target.words n + 2) bound).trans full,
    (Ku.mono (by decide)).trans Kt⟩


theorem widen_ok {s : State} {B : Addr} {Z n N : Nat} (h : Ws s B Z n N)
    (w : Width) (out src : Loc) (width : w.words n ≤ n)
    (fit : out.offset n + 4 * (n + 2) ≤ Z) (sourceBound : src.offset n + 4 * w.words n ≤ Z)
    (separate : src.offset n + 4 * w.words n ≤ out.offset n ∨
      out.offset n + 4 * (n + 2) ≤ src.offset n) :
    WP isa (widen w out src) s fun t => Ws t B Z n N ∧
      Outside B (out.offset n) (4 * (n + 2)) s.mem t.mem ∧
      val32 t.mem B (out.offset n) (n + 2) = val32 s.mem B (src.offset n) (w.words n) ∧
      val32 t.mem B (out.offset n) n = val32 s.mem B (src.offset n) (w.words n) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t :=
  widenTo_ok h .modulus w out src width fit sourceBound separate

end VG.Proof.RsaKeyGen.X86.KeyRuntime
