module

public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Weierstrass.Arm.Pow
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps

/-! # Frames for the converter's scratch slots -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Ecdsa.Arm
open VG.Impl.Ecdsa.Arm

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

theorem slotsWk_widen {c : Cfg} {base : Addr} {a b : Mem} {slots slots' : List Nat}
    (h : Unch base (slWk c slots) a b) (hsub : ∀ i ∈ slots, i ∈ slots') :
    Unch base (slWk c slots') a b := h.mono fun w hw => by
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_map_of_mem (hsub i hi))
  · exact List.mem_append_right _ hw

end VG.Proof.EcKey.Compressed.Arm
