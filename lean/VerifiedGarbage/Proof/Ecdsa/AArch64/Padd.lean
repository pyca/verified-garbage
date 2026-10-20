module

import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
public import VerifiedGarbage.Proof.Weierstrass.AArch64.AddCall
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout

/-!
# ECDSA on AArch64: what the complete additions' calls need

`c.padd` (`Cfg.pointOps`) makes the complete additions of the comb, the
window method and verification's sum calls of `vg_<curve>_proj_add`, which
reads `b` at `EM`'s slot. Any slots laid out together with `EM`'s give what
`addP_ok` needs (`addOk_of`), from the curve's facts (`BaseCfgOk.padd`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass

variable {c : Cfg}

theorem _root_.VG.Proof.Mont.Lay.congr {M : Mod} {size : Nat} {Sl Sl' : Nat → Prop} (h : Lay M size Sl)
    (e : ∀ x, Sl' x ↔ Sl x) : Lay M size Sl' := by
  have : Sl' = Sl := funext fun x => propext (e x)
  rw [this]; exact h

/-- Numbered slots and `EM`'s, laid out together. -/
theorem lay_map_em (hc : BaseCfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l ++ [EM], i < 45 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size fun x => x ∈ l.map c.sl ∨ x = c.sl EM :=
  (lay_map hc hmo htmp hMn hl).congr fun x => by
    simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton]

/-- The complete additions' function reads `b` at `EM`'s slot. -/
theorem padd_bAt {name : String} {bAt : Nat} (h : c.padd = some (name, bAt)) : bAt = c.sl EM := by
  unfold Cfg.padd at h
  cases hp : c.pointOps with
  | none => rw [hp] at h; cases h
  | some C => rw [hp] at h; cases h; rfl

/-- The complete additions' calls, on slots `Sl` laid out with `EM`'s. -/
theorem addOk_of (hc : BaseCfgOk c) {Sl : Nat → Prop}
    (hL : Lay c.MP' size fun x => Sl x ∨ x = c.sl EM) :
    AddOk c.MP' size Sl c.rcbSlots (c.pt RX RY RZ) (c.pt TX TY TZ) (c.pt DX DY DZ) c.padd := by
  unfold Cfg.padd
  cases h : c.pointOps with
  | none => trivial
  | some C =>
    have P := hc.padd (by rw [h]; exact Option.some_ne_none _)
    refine ⟨hL, sl_mod8 c EM, map_sl_disj (c := c) hc.n0 (l₁ := [EM])
        (l₂ := [T0, T1, T2, T3, T4, T5, DX, DY, DZ, AP, BM, RX, RY, RZ, TX, TY, TZ]) (by decide) (by decide)
        (by decide) (c.sl EM) (List.mem_singleton_self _), P.n4, P.pres, fun i hi => ?_, P.nf⟩
    have := List.all_eq_true.mp P.vec i hi
    exact Option.isNone_iff_eq_none.mp this

end VG.Proof.Ecdsa.AArch64
