module

public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
public import VerifiedGarbage.Proof.Weierstrass.OddWin

import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacDbls
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacBuild
import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch

/-!
# The odd window method on x86-64: what holds between its steps

As `WinJacState.lean`, for the table of odd multiples: entries `1 … M` hold
`[2m - 1]P` (`JTblOkO`); what the method reads at the start, the table of
bits that of `oq J k` (`JacWinFixedO`); and between doublings, the frame,
the table and `R` (`RStO`, `dblsO_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- Entries `1 … M` of the table hold `[2m - 1]P`. -/
def JTblOkO (K : JacWinCfg) (C : Curve) (base : Addr) (P : Point C) (M : Nat) (s : State) : Prop :=
  ∀ m, 1 ≤ m → m ≤ M → JPt C K.M.n base s (entS K m) (mul (2 * m - 1) P)

variable {K : JacWinCfg} {size : Nat} {C : Curve}

theorem JTblOkO.unch (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat}
    {s s' : State} (hT : JTblOkO K C base P M s) {W : List (Nat × Nat)} (hU : Unch base W s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) (hM : M ≤ 16)
    (hW : ∀ w ∈ W, ∀ i < 5 * M, jg K i + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ jg K i) :
    JTblOkO K C base P M s' := fun m h1 hm =>
  (hT m h1 hm).congr fun c hc => jgWord_unch hL hU hn (by omega) fun w hw => hW w hw _ (by omega)

/-- A program's writes keep entries `1 … M` if the loop may write them. -/
theorem JTblOkO.loopW (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat} {s s' : State}
    (hT : JTblOkO K C base P M s) (hU : Unch base (jwLoopW K) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hM : M ≤ 16) : JTblOkO K C base P M s' :=
  hT.unch hL hU hn hM fun w hw i hi => loopW_apart hL (by omega) w hw

/-- Storing entry `M + 1` keeps entries `1 … M`. -/
theorem JTblOkO.store (hL : JacWinLay K size) {base : Addr} {P : Point C} {M : Nat} {s s' : State}
    (hT : JTblOkO K C base P M s)
    (hO : Outside base (jg K (5 * M)) (40 * K.M.n) s.mem s'.mem) (hn : base.toNat + size ≤ 2 ^ 64)
    (hM : M ≤ 15) : JTblOkO K C base P M s' :=
  hT.unch hL (outside_grid5 hO) hn (by omega) fun w hw i hi => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hw
    refine jg_sep K ?_; omega

/-- What the odd method reads and never writes, at the start: zero, `P`, and
the table of the bits of `oq J k = (k + 32^J - 1) / 2`. -/
structure JacWinFixedO (K : JacWinCfg) (C : Curve) (base : Addr) (s₀ : State) (P : Point C) (k : Nat) :
    Prop extends JacWinPt K C base s₀ P where
  bits : ∀ t < 5 * K.J, s₀.mem (off base (K.bits + t)) =
    if (OddWin.oq K.J k).testBit t then 1 else 0

/-- `P ≠ O`: its `Z` is one. -/
theorem JacWinFixedO.ne_infinity (hC : Law C) {base : Addr} {s₀ : State} {P : Point C} {k : Nat}
    (hF : JacWinFixedO K C base s₀ P k) : P ≠ .infinity := by
  intro h
  have := hF.pt
  rw [h, hF.pz] at this
  exact hC.one_ne_zero this.2.2

/-- What holds between doublings: the frame, the odd table, and `R` a
Jacobian triple of `Q`. -/
structure RStO (K : JacWinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ : State)
    (Q : Point C) (s : State) : Prop where
  fr : JFrame K C base size s₀ s
  tbl : JTblOkO K C base P 16 s
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) Q

theorem RStO.rbxKeeps (hL : JacWinLay K size) {base : Addr} {P Q : Point C} {s₀ s s' : State}
    (h : RStO K C base size P s₀ Q s) (hk : Keeps [.rbx] s s') : RStO K C base size P s₀ Q s' := by
  have m : s'.mem = s.mem := hk.2.1
  have e : ∀ x, tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [m]
  refine ⟨h.fr.next hL (h.fr.scr.of_keeps hk (by decide)) ((Keeps.regs hk).mono (sub_powClob (by decide)))
    (W := []) (by rw [m]; exact Unch.refl _ _ _) (by simp), fun j h1 hj => (h.tbl j h1 hj).congr
    fun c _ => by rw [m], fun x hx => by rw [m]; exact h.lt x hx, by rw [e, e, e]; exact h.rep⟩

/-- What the loop's doublings write: the other slots and the temporary area,
not the grid. -/
def jwOthW (K : JacWinCfg) : List (Nat × Nat) := (jwOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

theorem jwOthW_loopW (K : JacWinCfg) : ∀ w ∈ jwOthW K, w ∈ jwLoopW K := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw; exact other_loopW hx
  · rw [List.mem_singleton.mp hw]; exact tmp_loopW

/-- One doubling of `R`. -/
theorem dblRO_ok (hL : JacWinLay K size) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    {base : Addr} {P Q : Point C} (hQ : onCurve C Q = true) {s₀ s : State}
    (h : RStO K C base size P s₀ Q s) :
    WP isa (dbl K.R).inline s fun t => RStO K C base size P s₀ (Spec.Weierstrass.add Q Q) t ∧
      t.gpr .rbx = s.gpr .rbx ∧ Unch base (jwOthW K) s.mem t.mem := by
  have hs := h.fr.scr
  have hn := hs.nowrap
  have hRo : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ jwOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> jw_mem
  have I0 : Inv K.M base size C.p (· ∈ jwSlots K) [K.R.x, K.R.y, K.R.z] (tmv C K.M.n base s) s :=
    ⟨hs, h.fr.mod, fun x hx => other_mem (hRo x hx), h.lt, fun _ _ => rfl⟩
  have hsl : ∀ x ∈ rcbW K.S K.R, x ∈ jwSlots K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
  refine WP.mono (hD hL.lay hL.rcbW_R hsl I0 hQ h.rep) fun t ⟨k, E, I, J⟩ => ?_
  have hRw : ∀ x ∈ rcbW K.S K.R, x ∈ jwOther K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> jw_mem
  have U' : Unch base (jwOthW K) s.mem t.mem := (ProgKeep.unch k).mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hRw x hx))
    · exact List.mem_append_right _ hw
  have U : Unch base (jwLoopW K) s.mem t.mem := U'.mono (jwOthW_loopW K)
  refine ⟨⟨h.fr.next hL (k.scr hs) k.regs U (jwLoopW_sub K), h.tbl.loopW hL U hn (by decide),
    fun x hx => I.lt x hx, ?_⟩, k.gpr _ (rbx_not_clob _), U'⟩
  have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base t x = E x := fun x hx => I.val x hx
  rw [e _ (by simp), e _ (by simp), e _ (by simp)]
  exact J

/-- `R = 32 R`, `rbx` the window index `j < 4096` before and after. -/
theorem dblsO_ok (hL : JacWinLay K size) (hC : Law C) {dbl : Pt → Prog isa} (hD : DblOk K.M K.S C dbl)
    {base : Addr} {P Q : Point C} (hQ : onCurve C Q = true) {s₀ s : State} {e j : Nat} (hj : j < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 j) (h : RStO K C base size P s₀ (mul e Q) s) :
    WP isa (K.dbls dbl).inline s fun t => RStO K C base size P s₀ (mul (32 * e) Q) t ∧
      t.gpr .rbx = BitVec.ofNat 64 j ∧ Unch base (jwOthW K) s.mem t.mem := by
  rw [JacWinCfg.dbls]
  simp only [Code.inline]
  refine WP.seq (WP.mono (addRbx_ok s (c := 5 * 4096) (by decide) hb) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  refine aeLoop_ok (n := 5) (Inv := fun i t => RStO K C base size P s₀ (mul (2 ^ (5 - i) * e) Q) t ∧
      t.gpr .rbx = BitVec.ofNat 64 (j + 4096 * i) ∧ Unch base (jwOthW K) s.mem t.mem)
    (fun i t h1 h5 ⟨R, b, U⟩ => ?_) (fun t ⟨R, b, U⟩ => ⟨by simpa using R, by simpa using b, U⟩) (by decide)
    ⟨by simpa using h.rbxKeeps hL k₁, by rw [b₁], by rw [m₁]; exact Unch.refl _ _ _⟩
  rw [JacWinCfg.dblStep]
  refine WP.seq (WP.mono (dblRO_ok hL hD (hC.onCurve_mul hQ _) R) fun t₁ ⟨R₁, b₁', U₁⟩ => ?_)
  refine WP.mono (dblCount_ok t₁ hj h1 h5 (by rw [b₁', b])) fun t₂ ⟨b₂, c₂, k₂⟩ =>
    ⟨⟨?_, b₂, by rw [k₂.2.1]; exact (U.trans U₁).mono fun w hw => (List.mem_append.mp hw).elim id id⟩, c₂⟩
  have := R₁.rbxKeeps hL k₂
  rwa [hC.add_mul_mul hQ, show 2 ^ (5 - i) * e + 2 ^ (5 - i) * e = 2 ^ (5 - (i - 1)) * e by
    rw [show 5 - (i - 1) = 5 - i + 1 by omega, Nat.pow_succ]; grind] at this

end VG.Proof.Weierstrass.X86_64
