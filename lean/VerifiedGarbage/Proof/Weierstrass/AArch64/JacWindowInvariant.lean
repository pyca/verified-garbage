import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLayout
import VerifiedGarbage.Proof.Weierstrass.Window5

/-! Invariants retained by the public five-bit Jacobian loop. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

def jacLive (K : WinCfg) : List Nat := winRo K ++
  [K.R.x,K.R.y,K.R.z,K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z] ++ jacTblSlots K

def jacLoopWrites (K : WinCfg) : List (Nat × Nat) :=
  (winOther K).map (·,8*K.M.n) ++ [(K.M.tmp,8*K.M.n)]

structure JacStable (K : WinCfg) (C : Curve) (base : Addr) (P : Point C) (k : Nat) (s : State) : Prop where
  zero : wordsVal s.mem base K.zero K.M.n = 0
  table : ∀ a, 1 ≤ a → a ≤ 16 →
    InvJ C (tmv C K.M.n base s (Jacobian.tablePt K a).x)
      (tmv C K.M.n base s (Jacobian.tablePt K a).y)
      (tmv C K.M.n base s (Jacobian.tablePt K a).z) (mul a P)
  bits : ∀ t<260, s.mem (off base (K.bits+t))=if k.testBit t then 1 else 0

/-- Unmodified table slots retain all their field words. -/
theorem JacWinLay.table_words {K : WinCfg} {size : Nat} (hL : JacWinLay K size)
    {base : Addr} {m m' : Mem} (hU : Unch base (jacLoopWrites K) m m')
    (hn : base.toNat+size ≤ 2^64) {a : Nat} (ha : 1 ≤ a) (h16 : a ≤ 16)
    {x : Nat} (hx : x ∈ [(Jacobian.tablePt K a).x,(Jacobian.tablePt K a).y,(Jacobian.tablePt K a).z]) :
    wordsVal m' base x K.M.n = wordsVal m base x K.M.n := by
  have hs := jacTblPt_mem K ha h16 x hx
  have hb := hL.lay.le x hs
  apply hU.wordsVal _ (by omega)
  intro w hw
  simp only [jacLoopWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
  rcases hw with ⟨y,hy,rfl⟩ | rfl
  · have ht := hL.tbl y (List.mem_append_right _ hy)
    simp only [Jacobian.tablePt,List.mem_cons,List.not_mem_nil,or_false] at hx
    rw [hL.n]
    rcases hx with rfl | rfl | rfl <;> dsimp only <;> omega
  · exact hL.lay.tmp x hs

/-- The scalar bits, zero slot, and all sixteen table entries are stable
through an iteration's work-slot writes. -/
theorem JacStable.keep {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {P : Point C} {k : Nat} {s t : State} (hL : JacWinLay K size) (hJ : K.J=52)
    (hn : base.toNat+size ≤ 2^64) (h : JacStable K C base P k s)
    (hU : Unch base (jacLoopWrites K) s.mem t.mem) : JacStable K C base P k t := by
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
      unfold tmv; rw [hL.table_words hU hn ha h16 hx]
    rw [hv _ (by simp),hv _ (by simp),hv _ (by simp)]
    exact h.table a ha h16
  · rw [hU.byte (fun w hw => ?_) (by have := hL.bits; omega),h.bits i hi]
    simp only [jacLoopWrites,List.mem_append,List.mem_map,List.mem_singleton] at hw
    rcases hw with ⟨y,hy,rfl⟩ | rfl
    · have ht := hL.bits_w y (List.mem_append_left _ hy)
      dsimp only; rw [hL.n]; omega
    · have ht := hL.bits_tmp
      dsimp only; rw [hL.n]; omega

/-- An initialized environment can always be represented by the current
memory function, avoiding artificial relationships between temporary environments. -/
theorem Inv.to_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (h : Inv M base size C.p Sl V E s) : Inv M base size C.p Sl V (tmv C M.n base s) s :=
  ⟨h.scr,h.mod,h.sl,h.lt,fun _ _ => rfl⟩

theorem Inv.point_tmv {M : Mod} {base : Addr} {size : Nat} {C : Curve}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (h : Inv M base size C.p Sl V E s) {p : Pt} {P : Point C}
    (hp : ∀ x ∈ [p.x,p.y,p.z], x ∈ V) (hJ : InvJ C (E p.x) (E p.y) (E p.z) P) :
    InvJ C (tmv C M.n base s p.x) (tmv C M.n base s p.y) (tmv C M.n base s p.z) P := by
  unfold tmv
  rw [h.val _ (hp _ (by simp)),h.val _ (hp _ (by simp)),h.val _ (hp _ (by simp))]
  exact hJ

/-- The loop's initialized fields, fixed data, and current multiple. -/
structure JacCore (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (P : Point C) (k e : Nat) (s : State) : Prop where
  field : Inv K.M base size C.p (· ∈ jacWinSlots K) (jacLive K) (tmv C K.M.n base s) s
  stable : JacStable K C base P k s
  point : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y)
    (tmv C K.M.n base s K.R.z) (mul e P)

theorem jacLive_R (K : WinCfg) : ∀ x ∈ [K.R.x,K.R.y,K.R.z], x ∈ jacLive K := by
  intro x hx
  simp only [jacLive,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

theorem jacLive_read (K : WinCfg) : ∀ x ∈ rcbR K.S K.R K.D, x ∈ jacLive K := by
  intro x hx
  simp only [jacLive,winRo,rcbR,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
  grind

/-- Any arithmetic result with the loop frame reconstructs the invariant. -/
theorem JacCore.next {K : WinCfg} {C : Curve} {base : Addr} {size : Nat}
    {P : Point C} {k e e' : Nat} {s t : State} (hL : JacWinLay K size) (hJ : K.J=52)
    (h : JacCore K C base size P k e s) {E : Nat → Fe C}
    (hk : ProgKeep K.M base (winOther K) s t)
    (hi : Inv K.M base size C.p (· ∈ jacWinSlots K) (jacLive K) E t)
    (hp : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul e' P)) :
    JacCore K C base size P k e' t :=
  ⟨hi.to_tmv,h.stable.keep hL hJ h.field.scr.nowrap hk.unch,
    hi.point_tmv (jacLive_R K) hp⟩

end VG.Proof.Weierstrass.AArch64
