module

public import VerifiedGarbage.Impl.P384.EcdhMadd
import VerifiedGarbage.Proof.P384.Ops
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad

/-!
# P-384's inline mixed addition

`madd_ok`: the inline mixed addition (`Impl/P384/EcdhMadd.lean`) does what
the window's must (`MaddSpec`), as `ofN_ok` shows of the field program's: its
operations are `fprog_ok`'s, on the slots the field program uses.
-/

@[expose] public section

-- Powers of two up to `2^384` are evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.P384.EcdhMadd
open VG VG.AArch64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64 VG.Impl.P384.EcdhDouble
open VG.Impl.P384.EcdhMadd
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.P384.Ops (clobX ProgKeepX)
open VG.Proof.Weierstrass.AArch64.Mont (p384)
open Spec.Weierstrass

/-- The inline mixed addition, as the window's. -/
theorem madd_ok {C : Curve} (hC : C.p = p384) {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) : MaddSpec K C base size (.block madd) := by
  intro E s hI
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  have w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  have hAp := hL.rcbApart_D (Or.inr rfl)
  rw [madd, maddJ_eq]
  refine WP.mono (Ops.fprog_ok hC hL.lay hA.al hp _ hI (fun op hop x hx => w1.1 x (ofN_slots op hop x hx))
    (readsOk_mono (ofN_readsOk maddJN_ok _ _ _ _) fun x hx => hx)) fun s' ⟨k, I⟩ => ?_
  have hw : ∀ w ∈ (ofN maddJN K.S K.R K.E K.D).map FOp.out, w ∈ rcbW K.S K.D := fun w hw => by
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out maddJN_ok op hop
  refine ⟨⟨fun r hr => k.gpr r fun h => hr (by
      have : ∀ r ∈ clobX, r ∈ clob K.M.n ++ winSaved K.M.n := by decide
      exact this r h), k.rd, k.wr, k.sp⟩,
    (ProgKeepX.mono k hw).unch.mono fun w hw => ?_, _, I.sub fun x hx => ?_,
    fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out maddJN_ok op hop),
    (congrArg₂ Prod.mk (ofN_run maddJN_ok hAp E 6)
      (congrArg₂ Prod.mk (ofN_run maddJN_ok hAp E 7) (ofN_run maddJN_ok hAp E 8))).trans (maddJN_run _)⟩
  · simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact Or.inl ⟨y, w1.2.1 y hy, rfl⟩
    · exact Or.inr rfl
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem maddJN_ok hx)
    · exact Or.inl hx

/-- P-384's inline mixed addition, as the window's. -/
theorem maddOk {C : Curve} (hC : C.p = p384) (hL : WinLay K 8192) (hA : WinA K)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (base : Addr) : MaddOk K C base 8192 (some (.block madd)) := by
  intro m hm
  cases hm
  exact madd_ok hC hL hA hp

end VG.Proof.P384.EcdhMadd
