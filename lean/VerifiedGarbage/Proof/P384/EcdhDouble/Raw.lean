module

public import VerifiedGarbage.Proof.P384.Ops
public import VerifiedGarbage.Impl.P384.EcdhDouble
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
public import VerifiedGarbage.Proof.Weierstrass.JacMul

/-!
# P-384's raw doubling

`raw_ok`: the raw doubling (`Impl/P384/EcdhDouble.lean`) from `p` into `o`
does what `winN_ok` (`Proof/Weierstrass/AArch64/WindowQuad.lean`) says of the
window's doubling by calls, but changes the registers `clobX`.
-/

@[expose] public section

namespace VG.Proof.P384.EcdhDouble
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX ProgKeepX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

theorem raw_eq (p o : Pt) : raw p o = (ofN (dblJChoiceN false) K.S p p o).flatMap Impl.P384.Ops.op := by
  rw [raw, ← dblJChoice_eq false]; rfl

theorem K_M : K.M = Impl.P384.Ops.M := rfl

/-- The raw doubling from `p` into `o`. -/
theorem raw_ok {C : Curve} (hC : C.p = p384) {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt}
    (hAp : RcbApart K.S p p o) (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winSlots K)
    (hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ rcbR K.S p p, x ∈ V) :
    WP isa (.block (raw p o)) s fun s' => KeepRegs clobX s s' ∧
      Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
      (E' o.x, E' o.y, E' o.z) = (runOps (dblJChoiceN false) (fun y => E (rcbσ K.S p p o y)) 6,
        runOps (dblJChoiceN false) (fun y => E (rcbσ K.S p p o y)) 7,
        runOps (dblJChoiceN false) (fun y => E (rcbσ K.S p p o y)) 8) := by
  have hN := dblJChoiceN_ok false
  have hR : readsOk (ofN (dblJChoiceN false) K.S p p o) V = true := readsOk_mono (ofN_readsOk hN K.S p p o) hV
  rw [raw_eq]
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun s' ⟨hk, hI'⟩ => ⟨⟨hk.gpr, hk.rd, hk.wr, hk.sp⟩, ?_, _, hI'.sub fun x hx => ?_,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out hN op hop),
      congrArg₂ Prod.mk (ofN_run hN hAp E 6) (congrArg₂ Prod.mk (ofN_run hN hAp E 7) (ofN_run hN hAp E 8))⟩
  · refine (hk.mono fun w hw => ?_).unch.mono fun w hw => ?_
    · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
      exact ofN_out hN op hop
    · simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
      rcases hw with ⟨y, hy, rfl⟩ | rfl
      · exact Or.inl ⟨y, hW y hy, rfl⟩
      · exact Or.inr rfl
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx

end VG.Proof.P384.EcdhDouble
