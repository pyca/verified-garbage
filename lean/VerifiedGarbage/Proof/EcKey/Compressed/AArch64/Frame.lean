module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Pow
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps

/-! # Frames for the converter's scratch slots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Ecdsa.AArch64
open VG.Impl.Ecdsa.AArch64

theorem unch_same {base : Addr} {W : List (Nat × Nat)} {a b c : Mem}
    (h₁ : Unch base W a b) (h₂ : Unch base W b c) : Unch base W a c :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem slot_frame {c : Cfg} {base : Addr} {a b : Mem} {i len : Nat} {slots : List Nat}
    (hi : i ∈ slots) (hlen : len ≤ 8 * c.n) (h : Outside base (c.sl i) len a b) :
    Unch base (slW c slots) a b :=
  (h.mono (o' := c.sl i) (n' := 8 * c.n) (Nat.le_refl _) (by omega)).unch.mono fun w hw => by
    obtain rfl := List.mem_singleton.mp hw
    exact List.mem_map_of_mem hi

theorem slots_widen {c : Cfg} {base : Addr} {a b : Mem} {slots slots' : List Nat}
    (h : Unch base (slW c slots) a b) (hsub : ∀ i ∈ slots, i ∈ slots') :
    Unch base (slW c slots') a b := h.mono fun w hw => by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact List.mem_map_of_mem (hsub i hi)

 theorem x0_not_powClob (n : Nat) : VG.AArch64.Reg.x0 ∉ VG.Proof.Weierstrass.AArch64.powClob n := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · cases h
  · exact (by decide : VG.AArch64.Reg.x0 ∉ VG.Proof.Mont.AArch64.clobAll)
      (VG.Proof.Mont.AArch64.mem_clobAll h)

 theorem x20_not_powClob (n : Nat) : VG.AArch64.Reg.x20 ∉ VG.Proof.Weierstrass.AArch64.powClob n := by
  intro h
  rcases List.mem_cons.mp h with h | h
  · cases h
  · exact (by decide : VG.AArch64.Reg.x20 ∉ VG.Proof.Mont.AArch64.clobAll)
      (VG.Proof.Mont.AArch64.mem_clobAll h)

 theorem mulPP_eq_op {c : Cfg} (o a b : Nat) (h : a ≠ b) :
    VG.Impl.Weierstrass.AArch64.opProg c.MP' (.mul o a b) = c.mulPP o a b := by
  unfold VG.Impl.Weierstrass.AArch64.opProg VG.Impl.Ecdsa.AArch64.Cfg.mulPP
  cases hh : VG.Impl.Weierstrass.AArch64.Mont.callOf c.MP' with
  | none => simp [VG.Impl.Weierstrass.AArch64.opCode, h]
  | some fm => obtain ⟨f, m⟩ := fm; simp [h, MP'_n]

end VG.Proof.EcKey.Compressed.AArch64
