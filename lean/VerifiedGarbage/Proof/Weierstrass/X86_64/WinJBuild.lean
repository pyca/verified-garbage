module
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinQuad

/-!
# Windows in Jacobian coordinates on x86-64: the slots

The field programs of the Jacobian window method are on slots that are apart
(`WinLay.rcbApart_winJ`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- The slots the Jacobian window method's field programs use are apart:
the doublings between `R` and `D`, and `fromJ` from `R` into `D` (`z` the
slots of zero). -/
theorem _root_.VG.Proof.Weierstrass.WinLay.rcbApart_winJ {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    RcbApart K.S K.R K.R K.D ∧ RcbApart K.S K.D K.D K.R ∧
      RcbApart K.S K.R ⟨K.zero, K.zero, K.zero⟩ K.D :=
  ⟨hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 13, 14, 15]) (lr := [16, 17, 0, 1, 2, 0, 1, 2]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 0, 1, 2]) (lr := [16, 17, 13, 14, 15, 13, 14, 15]) rfl rfl,
    hL.rcbApart_codes (lw := [7, 8, 9, 10, 11, 12, 13, 14, 15]) (lr := [16, 17, 0, 1, 2, 18, 18, 18]) rfl rfl⟩

/-- The slots of a point, written. -/
theorem pt_other {K : WinCfg} {p : Pt} (h : p = K.R ∨ p = K.E ∨ p = K.D) :
    ∀ x ∈ [p.x, p.y, p.z], x ∈ winOther K := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases h with rfl | rfl | rfl <;> rcases hx with rfl | rfl | rfl <;> win_mem

end VG.Proof.Weierstrass.X86_64
