import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeInvariant
import VerifiedGarbage.Impl.Weierstrass.AArch64.Naf
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout
import VerifiedGarbage.Proof.Weierstrass.Window5

/-! Invariants retained by the public five-bit Jacobian loop. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- The eight odd entries and cached double are initialized; E is a scratch lookup destination. -/
def nafLive (K : WinCfg) : List Nat :=
  winRo K ++ [K.R.x,K.R.y,K.R.z,K.D.x,K.D.y,K.D.z] ++ jacTreeSlots K 9

structure NafStable (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (β : Nat → BitVec 8) (s : State) : Prop where
  zero : wordsVal s.mem base K.zero K.M.n = 0
  table : ∀ a, 1 ≤ a → a ≤ 8 →
    InvJ C (tmv C K.M.n base s (Jacobian.tablePt K a).x)
      (tmv C K.M.n base s (Jacobian.tablePt K a).y)
      (tmv C K.M.n base s (Jacobian.tablePt K a).z) (mul (2*a-1) P)
  bits : ∀ t<257, s.mem (off base (K.bits+t))=β t

/-- The signed scalar bytes, zero slot, and eight odd-multiple table entries are stable
through an iteration's work-slot writes. -/
theorem NafStable.keep {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {P : Point C} {β : Nat → BitVec 8} {s t : State} (hL : JacWinLay K size) (hJ : K.J=52)
    (hn : base.toNat+size ≤ 2^64) (h : NafStable K C base P β s)
    (hU : Unch base (jacLoopWrites K) s.mem t.mem) : NafStable K C base P β t := by
  have old := hL.toWinLay hJ
  refine ⟨?_,fun a ha h16 => ?_,fun i hi => ?_⟩
  · rw [hU.wordsVal (fun w hw => ?_) (by have := old.lay.le K.zero (by win_mem); omega),h.zero]
    apply old.ro_w (x := K.zero) (by simp [winRo]) w
    simp only [jacLoopWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨y,hy,rfl⟩ | rfl
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨y,winOther_ws K y hy,rfl⟩)
    · exact List.mem_append_right _ (by simp)
  · have hv (x : Nat) (hx : x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z]) :
        tmv C K.M.n base t x = tmv C K.M.n base s x := by
      unfold tmv; rw [hL.table_words hU hn ha (by omega) hx]
    rw [hv _ (by simp),hv _ (by simp),hv _ (by simp)]
    exact h.table a ha h16
  · rw [hU.byte (fun w hw => ?_) (by have := hL.bits; omega),h.bits i hi]
    simp only [jacLoopWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨y,hy,rfl⟩ | rfl
    · have ht := hL.bits_w y (List.mem_append_left _ hy)
      dsimp only; rw [hL.n]; omega
    · have ht := hL.bits_tmp
      dsimp only; rw [hL.n]; omega

/-- The loop's initialized fields, fixed data, and current multiple. -/
structure NafCore (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (β : Nat → BitVec 8) (e : Nat) (s : State) : Prop where
  field : Inv K.M base size C.p (· ∈ jacWinSlots K) (nafLive K) (tmv C K.M.n base s) s
  stable : NafStable K C base P β s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul e P)

theorem nafLive_R (K : WinCfg) : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ nafLive K := by
  intro x hx
  simp only [nafLive,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem nafLive_read (K : WinCfg) : ∀ x ∈ rcbR K.S K.R K.D, x ∈ nafLive K := by
  intro x hx
  simp only [nafLive,winRo,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

/-- Any arithmetic result with the loop frame reconstructs the invariant. -/
theorem NafCore.next {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {P : Point C} {β : Nat → BitVec 8} {e e' : Nat} {s t : State} (hL : JacWinLay K size) (hJ : K.J=52)
    (h : NafCore K C base size P β e s) {E : Nat → Fe C}
    (hk : ProgKeep K.M base (winOther K) s t)
    (hi : Inv K.M base size C.p (· ∈ jacWinSlots K) (nafLive K) E t)
    (hp : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul e' P)) :
    NafCore K C base size P β e' t :=
  ⟨hi.to_tmv,h.stable.keep hL hJ h.field.scr.nowrap hk.unch,
    hi.point_tmv (nafLive_R K) hp⟩

end VG.Proof.Weierstrass.AArch64
