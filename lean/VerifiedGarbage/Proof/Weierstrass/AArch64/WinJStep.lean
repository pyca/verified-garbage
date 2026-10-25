module

import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJNorm
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CopyKeep
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.FprogJ
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
public import VerifiedGarbage.Impl.Weierstrass.AArch64.WindowJ
import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
import VerifiedGarbage.Proof.Weierstrass.WindowJ
public import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Proof.Framework.AArch64.Call
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Fprog
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowBase
public import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Weierstrass.WindowJA
import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJBuild

/-!
# Windows in Jacobian coordinates on AArch64: an iteration

The loop's state with the table affine (`WinStR`), `R = 16 R` in place in
Jacobian coordinates (`quadJ_ok`: two pairs of doublings between `R` and
`D`), and the mixed addition of the affine entry `E` into `D` with the
selection of `E`, `R` or `D` (`sumJ_ok`), for an iteration but the last
(`winStepJ_ok`): as on x86-64 (`Proof/Weierstrass/X86_64/WinJStep.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)
open Spec.Weierstrass

/-- `x ∈ l₂` from `h : x ∈ l₁`, for literal lists with `l₁`'s elements in `l₂`: not by
`omega` on the disjunctions, which splits cases exponentially. -/
macro "sub_mem " h:term : tactic => `(tactic| plain_simp_names (
                   refine (show (_ : List _) ⊆ _ from ?_) $h
                   simp only [List.cons_subset, List.nil_subset, List.mem_cons, eq_self_iff_true, true_or,
                     or_true, and_true, and_self]))

/-! ## The loop's state, with the table by any representation -/

/-- The table survives what the loop writes. -/
theorem TblOkR.unch {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {P : Point C} {s s' : State}
    (hT : TblOkR K C base Rp P 8 s) (hU : Unch base (loopW K) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : TblOkR K C base Rp P 8 s' := by
  intro j h1 h8
  have T := hT j h1 h8
  have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    have hs := (tblPt_slots K h1 h8 x hx).1
    exact hU.wordsVal (tbl_apart_loopW hL h1 h8 hx) (by have := hL.lay.le _ hs; omega_using [hn, this])
  refine ⟨fun x hx => by rw [e x hx]; exact T.1 x hx, ?_⟩
  have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
  exact T.2

/-- `WinSt`, with the table's entries represented by `Rp`. -/
structure WinStR (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (Rp : Fe C → Fe C → Fe C → Point C → Prop) (P : Point C) (s₀ s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (combClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkA K.M size C.p s.mem base
  tbl : TblOkR K C base Rp P 8 s

/-- The state after a change of `loopW` only. -/
theorem WinStR.next {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {P : Point C} {s₀ s s' : State}
    (h : WinStR K C base size Rp P s₀ s) (hs' : Scr s' base size)
    (hk : KeepRegs (combClob K.M.n) s s') (hU : Unch base (loopW K) s.mem s'.mem) :
    WinStR K C base size Rp P s₀ s' :=
  ⟨hs', h.keep.trans hk, (h.unch.trans hU).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact loopW_sub K w hw,
    h.mod.unch hU (fun w hw => winW_mo hL h.mod w (loopW_sub K w hw)) h.scr.nowrap,
    h.tbl.unch hL hU h.scr.nowrap⟩

theorem WinStR.ro_tmv {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {P : Point C} {s₀ s : State}
    (h : WinStR K C base size Rp P s₀ s) (hF : WinFixed K C base s₀ P k) :
    tmv C K.M.n base s K.S.a = Fin.ofNat C.p C.a ∧ tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b ∧
      (∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p) ∧ wordsVal s.mem base K.zero K.M.n = 0 := by
  have hn := h.scr.nowrap
  refine ⟨?_, ?_, fun x hx => ?_, ?_⟩
  · rw [hL.ro_tmv h.unch hn (by simp [winRo])]; exact hF.a
  · rw [hL.ro_tmv h.unch hn (by simp [winRo])]; exact hF.b
  · rw [hL.ro_val h.unch hn hx]; exact hF.ro_lt x hx
  · rw [hL.ro_val h.unch hn (by simp [winRo])]; exact hF.zero

/-- A state of the loop with the table in projective coordinates. -/
theorem WinSt.toR {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} {P : Point C} {s₀ s : State}
    (h : WinSt K C base size P s₀ s) : WinStR K C base size (Rep C) P s₀ s :=
  ⟨h.scr, h.keep, h.unch, h.mod, h.tbl⟩

/-! ## Four doublings in place -/

/-- The slots the doublings keep in the environment: `R` and the constants. -/
def dblVR (K : WinCfg) : List Nat := [K.R.x, K.R.y, K.R.z, K.S.a, K.S.b3, K.zero]

/-- What a window's doubling from `p` into `o` must do, the slots `V`
holding their values: change only the registers `combClob` and the loop's
slots, and leave `o` holding `2p` by the numbered doubling. -/
def DblSpec (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (prog : Prog isa) (p o : Pt)
    (V : List Nat) : Prop :=
  ∀ (E : Nat → Fe C) (s : State), Inv K.M base size C.p (· ∈ winSlots K) V E s →
    WP isa prog s fun s' => KeepRegs (clob K.M.n ++ winSaved K.M.n) s s' ∧ Unch base (loopW K) s.mem s'.mem ∧
      ∃ E' : Nat → Fe C, Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (E' o.x, E' o.y, E' o.z) = (runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 6,
        runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 7,
        runOps (dblJChoiceN (K.M.n == 4)) (fun y => E (rcbσ K.S p p o y)) 8)

/-- The doublings a window is given (`WinCfg.dblRD`, `dblDR`) do what the
field programs do. -/
def DblsOk (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (dd : Option (Prog isa × Prog isa)) : Prop :=
  ∀ d, dd = some d → DblSpec K C base size d.1 K.R K.D (dblVR K) ∧
    DblSpec K C base size d.2 K.D K.R ([K.D.x, K.D.y, K.D.z] ++ dblVR K)

theorem DblsOk.none {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} : DblsOk K C base size none :=
  fun _ h => by cases h

/-- What a window's mixed addition must do, `R` and `E` holding their values:
change only the registers `combClob` and the loop's slots, and leave `D`
holding `R + E` by the mixed addition. -/
def MaddSpec (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (prog : Prog isa) : Prop :=
  ∀ (E : Nat → Fe C) (s : State), Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) E s →
    WP isa prog s fun s' => KeepRegs (clob K.M.n ++ winSaved K.M.n) s s' ∧ Unch base (loopW K) s.mem s'.mem ∧
      ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.R K.E) E' s' ∧
      (∀ x, x ∉ rcbW K.S K.D → E' x = E x) ∧
      (E' K.D.x, E' K.D.y, E' K.D.z) = maddJF (E K.R.x) (E K.R.y) (E K.R.z) (E K.E.x) (E K.E.y)

/-- The mixed addition a window is given (`WinCfg.maddRD`) does what the
field program does. -/
def MaddOk (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (ma : Option (Prog isa)) : Prop :=
  ∀ m, ma = some m → MaddSpec K C base size m

theorem MaddOk.none {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} : MaddOk K C base size none :=
  fun _ h => by cases h

/-- The field program's doubling from `p` into `o`, on the window's slots. -/
theorem dblN_spec {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {p o : Pt} (hAp : RcbApart K.S p p o)
    (hw : (∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winSlots K) ∧ (∀ x ∈ rcbW K.S o, x ∈ winOther K) ∧
      ∀ x ∈ rcbW K.S o ++ rcbR K.S p p, x ∈ winRo K ++ winOther K) {V : List Nat}
    (hV : ∀ x ∈ rcbR K.S p p, x ∈ V) :
    DblSpec K C base size (fprogB K.M (WinCfg.double K p o)) p o V := by
  intro E s hI
  simp only [WinCfg.double, dblJChoice_eq]
  exact WP.mono (winN_ok hL hA hp (dblJChoiceN_ok (K.M.n == 4)) hAp hw.1 hw.2.1 hw.2.2 hI hV)
    fun s' ⟨k, U, E', I, _, v⟩ => ⟨k.mono fun _ h => List.mem_append_left _ h, U, E', I, v⟩

/-- Two doublings, `R` to `D` and back, and one less to count. -/
theorem dblPair_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State}
    {dd : Option (Prog isa × Prog isa)} (hD : DblsOk K C base size dd)
    (hS : WinStR K C base size Rp P s₀ s) {j c e : Nat}
    (hj : j < 2 ^ 32) (hc : 1 ≤ c) (hc2 : c ≤ 2)
    (hx : s.gpr .x19 = BitVec.ofNat 64 (j + 2 ^ 32 * c)) {E : Nat → Fe C}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) E s)
    (hJ : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul e P)) :
    WP isa (WinCfg.jacPair K dd) s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .x19 = BitVec.ofNat 64 (j + 2 ^ 32 * (c - 1)) ∧
      s'.gpr .x2 = BitVec.ofNat 64 (c - 1) ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) E' s' ∧
      InvJ C (E' K.R.x) (E' K.R.y) (E' K.R.z) (mul (4 * e) P) := by
  obtain ⟨aRD, aDR, -⟩ := hL.rcbApart_winJ
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  have w2 := winJ_sl oD (sl _ oR) (sl _ oR)
  have w3 := winJ_sl oR (sl _ oD) (sl _ oD)
  have hQ := fun (a : Nat) => hC.onCurve_mul hP a
  have hRD : DblSpec K C base size (WinCfg.dblRD K dd) K.R K.D (dblVR K) := by
    cases dd with
    | some d => exact (hD d rfl).1
    | none =>
      exact dblN_spec hL hA hp aRD w2
        (by intro x hx; simp only [rcbR, dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
            rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true])
  have hDR : DblSpec K C base size (WinCfg.dblDR K dd) K.D K.R ([K.D.x, K.D.y, K.D.z] ++ dblVR K) := by
    cases dd with
    | some d => exact (hD d rfl).2
    | none =>
      exact dblN_spec hL hA hp aDR w3
        (by intro x hx; simp only [rcbR, dblVR, List.cons_append, List.nil_append, List.mem_cons,
              List.not_mem_nil, or_false] at hx ⊢
            rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true])
  rw [WinCfg.jacPair]
  refine WP.seq (WP.mono (hRD E s hI) fun s₂ ⟨k₂, U₂, E₂, I₂, v₂⟩ => ?_)
  have S₂ := hS.next hL I₂.scr (k₂.mono fun _ h => winSaved_combClob h) U₂
  have J₂ := InvJ.dbl' hC hM3 (hQ e) hJ (v₂.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP] at J₂
  refine WP.seq (WP.mono (hDR E₂ s₂ I₂) fun s₃ ⟨k₃, U₃, E₃, I₃, v₃⟩ => ?_)
  have S₃ := S₂.next hL I₃.scr (k₃.mono fun _ h => winSaved_combClob h) U₃
  have J₃ := InvJ.dbl' hC hM3 (hQ _) J₂ (v₃.trans (dblJChoiceN_run (K.M.n == 4) _))
  rw [hC.double hP, show 2 * (2 * e) = 4 * e by omega_using []] at J₃
  have x₃ : s₃.gpr .x19 = BitVec.ofNat 64 (j + 2 ^ 32 * ((c - 1) + 1)) := by
    have n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
      (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
    rw [k₃.gpr _ n19, k₂.gpr _ n19, hx, Nat.sub_add_cancel hc]
  refine WP.mono (dblCnt_ok s₃ hj (by omega_using [hc2, hc]) x₃) fun s₄ ⟨x₄, y₄, k₄⟩ => ?_
  have hs₄ := S₃.scr.of_keeps k₄ (by decide)
  have cc : ∀ r ∈ [Reg.x2, .x19], r ∈ combClob K.M.n := by
    intro r hr
    simp only [combClob, clob, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  refine ⟨S₃.next hL hs₄ ((Keeps.regs k₄).mono cc) (by rw [k₄.mem]; exact Unch.refl _ _ _), x₄, y₄,
    E₃, (I₃.of_mem hs₄ k₄.mem).sub ?_, J₃⟩
  intro x hx
  simp only [dblVR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx ⊢
  rcases hx with h | h | h | h | h | h <;> simp only [h, true_or, or_true]

/-- `R = 16 R` in Jacobian coordinates, in place: from `(X : Y : Z)` standing
for `[e]P` (or with `Z = 0`) to a triple standing for `[16 e]P`. -/
theorem quadJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State}
    {dd : Option (Prog isa × Prog isa)} (hD : DblsOk K C base size dd)
    (hF : WinFixed K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s) {j : Nat} (hj : j < 2 ^ 32)
    (hx : s.gpr .x19 = BitVec.ofNat 64 j) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quadJ K dd) s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have V0 : ∀ x ∈ dblVR K, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hlt _ (by simp)⟩
    all_goals exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  have cc : ∀ r ∈ [Reg.x2, .x19], r ∈ combClob K.M.n := by
    intro r hr
    simp only [combClob, clob, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  rw [WinCfg.quadJ]
  refine WP.seq (WP.mono (dblSet_ok s hx) fun s₂ ⟨x₂, k₂⟩ => ?_)
  have hs₂ := hS.scr.of_keeps k₂ (by decide)
  have S₂ := hS.next hL hs₂ ((Keeps.regs k₂).mono cc) (by rw [k₂.mem]; exact Unch.refl _ _ _)
  refine WP.mono (WP.loop (M := isa) (fun c t => 1 ≤ c ∧ c ≤ 2 ∧ WinStR K C base size Rp P s₀ t ∧
      t.gpr .x19 = BitVec.ofNat 64 (j + 2 ^ 32 * c) ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) E' t ∧
      InvJ C (E' K.R.x) (E' K.R.y) (E' K.R.z) (mul (4 ^ (2 - c) * e) P))
    (Q := fun t => WinStR K C base size Rp P s₀ t ∧ t.gpr .x19 = BitVec.ofNat 64 j ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) (dblVR K) E' t ∧
      InvJ C (E' K.R.x) (E' K.R.y) (E' K.R.z) (mul (16 * e) P))
    (fun c t ⟨hc, hc2, St, xt, Et, It, Jt⟩ => ?_) 2 s₂
    ⟨by decide, Nat.le_refl _, S₂, x₂, tmv C K.M.n base s, (I₀.of_mem hs₂ k₂.mem), by simpa using hR⟩)
    fun s₅ ⟨S₅, x₅, E₅, I₅, J₅⟩ => ?_
  · refine WP.mono (dblPair_ok hL hA hp hC hM3 hP hD St hj hc hc2 xt It Jt)
      fun t' ⟨St', xt', yt', E', It', Jt'⟩ => ?_
    have ev : isa.eval (.nonzero .x .x2) t' = some (decide (c - 1 ≠ 0)) := by
      show some (t'.read .x .x2 != 0) = _
      rw [read_x, yt']
      rcases (by omega_using [hc, hc2] : c = 1 ∨ c = 2) with rfl | rfl <;> rfl
    rcases (by omega_using [hc, hc2] : c = 1 ∨ c = 2) with rfl | rfl
    · refine Or.inl ⟨ev, St', by simpa using xt', E', It', ?_⟩
      rw [show 16 * e = 4 * (4 ^ (2 - 1) * e) by simp only [Nat.reduceSub, Nat.reducePow]; omega_using []]
      exact Jt'
    · refine Or.inr ⟨ev, 1, by decide, Nat.le_refl _, by decide, St', xt', E', It', by simpa using Jt'⟩
  · have hRV : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ dblVR K := by
      intro x hx; simp only [dblVR, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h <;> simp [h]
    refine ⟨S₅, by rw [x₅, hx], fun x hx => I₅.lt x (hRV x hx), ?_⟩
    show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp)), I₅.val _ (hRV _ (by simp))]
    exact J₅

/-! ## The Jacobian sum, selected -/

/-- `R`, `E` and `D`: in the working space and apart, as the selection after
the sum needs. -/
theorem winRED_lay {K : WinCfg} {size : Nat} (hL : WinLay K size) :
    (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], x + 8 * K.M.n ≤ size) ∧
    ((K.D.x + 8 * K.M.n ≤ K.D.y ∨ K.D.y + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.x + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.x) ∧
      (K.D.y + 8 * K.M.n ≤ K.D.z ∨ K.D.z + 8 * K.M.n ≤ K.D.y)) ∧
    ((K.R.x + 8 * K.M.n ≤ K.R.y ∨ K.R.y + 8 * K.M.n ≤ K.R.x) ∧
      (K.R.x + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.x) ∧
      (K.R.y + 8 * K.M.n ≤ K.R.z ∨ K.R.z + 8 * K.M.n ≤ K.R.y)) ∧
    (∀ d ∈ [K.D.x, K.D.y, K.D.z], ∀ e ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      d + 8 * K.M.n ≤ e ∨ e + 8 * K.M.n ≤ d) ∧
    (∀ d ∈ [K.R.x, K.R.y, K.R.z], ∀ e ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ e ∨ e + 8 * K.M.n ≤ d) := by
  -- The nine slots by index, apart by `Nodup` of a sublist (not by rewriting `Nodup` per pair).
  let L : List Nat := [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z]
  have sub : L.Sublist (winOther K) := by
    simp only [L, winOther, rcbW, List.cons_append, List.nil_append]
    repeat first | exact List.nil_sublist _ | apply List.Sublist.cons_cons | apply List.Sublist.cons
  have nd := sub.nodup hL.nodup
  have hw : ∀ x ∈ L, x ∈ winWs K := fun x hx => winOther_ws K x (sub.subset hx)
  have A : ∀ i j (hi : i < 9) (hj : j < 9), i ≠ j → L[i] + 8 * K.M.n ≤ L[j] ∨ L[j] + 8 * K.M.n ≤ L[i] :=
    fun i j hi hj h => hL.apart₂ (hw _ (List.getElem_mem _)) (hw _ (List.getElem_mem _))
      (fun e => h ((nd.getElem_inj (hi := hi) (hj := hj)).mp e))
  refine ⟨fun x hx => hL.lay.le _ (winWs_slots K _ (hw _ hx)),
    ⟨A 6 7 (by decide) (by decide) (by decide), A 6 8 (by decide) (by decide) (by decide),
      A 7 8 (by decide) (by decide) (by decide)⟩,
    ⟨A 0 1 (by decide) (by decide) (by decide), A 0 2 (by decide) (by decide) (by decide),
      A 1 2 (by decide) (by decide) (by decide)⟩, ?_, ?_⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨A 6 0 (by decide) (by decide) (by decide), A 6 1 (by decide) (by decide) (by decide),
        A 6 2 (by decide) (by decide) (by decide), A 6 3 (by decide) (by decide) (by decide),
        A 6 4 (by decide) (by decide) (by decide), A 6 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 7 0 (by decide) (by decide) (by decide), A 7 1 (by decide) (by decide) (by decide),
        A 7 2 (by decide) (by decide) (by decide), A 7 3 (by decide) (by decide) (by decide),
        A 7 4 (by decide) (by decide) (by decide), A 7 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 8 0 (by decide) (by decide) (by decide), A 8 1 (by decide) (by decide) (by decide),
        A 8 2 (by decide) (by decide) (by decide), A 8 3 (by decide) (by decide) (by decide),
        A 8 4 (by decide) (by decide) (by decide), A 8 5 (by decide) (by decide) (by decide)⟩⟩
  · simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨A 0 3 (by decide) (by decide) (by decide), A 0 4 (by decide) (by decide) (by decide),
        A 0 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 1 3 (by decide) (by decide) (by decide), A 1 4 (by decide) (by decide) (by decide),
        A 1 5 (by decide) (by decide) (by decide)⟩,
      ⟨A 2 3 (by decide) (by decide) (by decide), A 2 4 (by decide) (by decide) (by decide),
        A 2 5 (by decide) (by decide) (by decide)⟩⟩

/-- The value `selSum` leaves in a coordinate of `R`: `E`'s where `R` is
`O` (`Z = 0`), else `R`'s where `E` is `O`, else `D`'s. -/
def selValJ (m : Mem) (base : Addr) (K : WinCfg) (r e d : Nat) : Nat :=
  if wordsVal m base K.R.z K.M.n = 0 then wordsVal m base e K.M.n
  else if wordsVal m base K.E.z K.M.n = 0 then wordsVal m base r K.M.n else wordsVal m base d K.M.n

/-- `D = R` where `E` is `O`, then `R = E` where `R` is `O`, else `D`. -/
theorem selSum_ok {K : WinCfg} {size : Nat} (hL : WinLay K size) (hA : WinA K) {s : State}
    {base : Addr} (hs : Scr s base size) :
    WP isa (.block (WinCfg.selSum K)) s fun s' =>
      wordsVal s'.mem base K.R.x K.M.n = selValJ s.mem base K K.R.x K.E.x K.D.x ∧
      wordsVal s'.mem base K.R.y K.M.n = selValJ s.mem base K K.R.y K.E.y K.D.y ∧
      wordsVal s'.mem base K.R.z K.M.n = selValJ s.mem base K K.R.z K.E.z K.D.z ∧
      KeepRegs [.x1, .x2, .x3, .x7, .x16] s s' ∧ Unch base (loopW K) s.mem s'.mem := by
  have hn := hs.nowrap
  obtain ⟨le, aD, aR, dRE, rE⟩ := winRED_lay hL
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have al : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], x % 8 = 0 :=
    fun x hx => hA.sl x (winOther_mem (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_in))
  have hin : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      x + 8 * K.M.n ≤ size ∧ x % 8 = 0 := fun x hx => ⟨le x hx, al x hx⟩
  rw [WinCfg.selSum]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs hL.n0 (le K.E.z (by simp)) (al K.E.z (by simp))) fun s₁ ⟨c₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.mem
  rw [WP.block_append_iff]
  refine WP.mono (selPtKeep_ok hs₁ (decide (wordsVal s.mem base K.E.z K.M.n ≠ 0))
    (by rw [c₁]; simp only [mask, decide_eq_true_eq]) (o := K.D) (a := K.R)
    (fun d hd => hin d (by sub_mem hd)) aD
    (fun d hd e he => dRE d hd e (by sub_mem he))) fun s₂ ⟨d2x, d2y, d2z, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [m₁] at d2x d2y d2z O₂
  have UD : Unch base [(K.D.x, 8 * K.M.n), (K.D.y, 8 * K.M.n), (K.D.z, 8 * K.M.n)] s.mem s₂.mem :=
    fun x hx => O₂ x (hx _ (List.mem_cons_self ..)) (hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have keepD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      wordsVal s₂.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    refine UD.wordsVal (fun w hw => ?_) (by have := le x (by sub_mem hx); omega_using [hn, this])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> dsimp only <;> exact (dRE _ (by simp) x hx).symm
  rw [WP.block_append_iff]
  refine WP.mono (nzMask_ok hs₂ hL.n0 (le K.R.z (by simp)) (al K.R.z (by simp))) fun s₃ ⟨c₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have m₃ : s₃.mem = s₂.mem := k₃.mem
  refine WP.mono (selPt_ok hs₃ (decide (wordsVal s₂.mem base K.R.z K.M.n ≠ 0))
    (by rw [c₃]; simp only [mask, decide_eq_true_eq]) (o := K.R) (a := K.E) (b := K.D)
    (fun d hd => hin d (by sub_mem hd)) aR (fun d hd e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl
      · exact rE d hd _ (by simp)
      · exact rE d hd _ (by simp)
      · exact rE d hd _ (by simp)
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm
      · exact (dRE _ (by simp) d (by sub_mem hd)).symm))
    fun s₄ ⟨r4x, r4y, r4z, k₄, O₄⟩ => ?_
  rw [m₃] at r4x r4y r4z O₄
  have UR : Unch base [(K.R.x, 8 * K.M.n), (K.R.y, 8 * K.M.n), (K.R.z, 8 * K.M.n)] s₂.mem s₄.mem :=
    fun x hx => O₄ x (hx _ (List.mem_cons_self ..)) (hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      (hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
  have inL : ∀ {P : Pt}, (∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) →
      ∀ w ∈ [(P.x, 8 * K.M.n), (P.y, 8 * K.M.n), (P.z, 8 * K.M.n)], w ∈ loopW K := by
    intro P hP w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
    · exact Or.inl ⟨_, hP _ (by simp), rfl⟩
  have rz := keepD K.R.z (by simp)
  have ez : wordsVal s.mem base K.E.z K.M.n = wordsVal s.mem base K.E.z K.M.n := rfl
  refine ⟨?_, ?_, ?_, ?_, (UD.trans UR).mono fun w hw => ?_⟩
  · rw [r4x, d2x, rz, keepD K.E.x (by simp), selValJ]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;>
      by_cases h2 : wordsVal s.mem base K.E.z K.M.n = 0 <;> simp [h1, h2]
  · rw [r4y, d2y, rz, keepD K.E.y (by simp), selValJ]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;>
      by_cases h2 : wordsVal s.mem base K.E.z K.M.n = 0 <;> simp [h1, h2]
  · rw [r4z, d2z, rz, keepD K.E.z (by simp), selValJ]
    by_cases h1 : wordsVal s.mem base K.R.z K.M.n = 0 <;>
      by_cases h2 : wordsVal s.mem base K.E.z K.M.n = 0 <;> simp [h1, h2]
  · exact ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans
      (((Keeps.regs k₃).mono (by decide)).trans (k₄.mono (by decide))))
  · rcases List.mem_append.mp hw with h | h
    · exact inL oD w h
    · exact inL oR w h

theorem toM_iteJ {m R : Nat} [NeZero m] (p : Prop) [Decidable p] (a b : Nat) :
    toM m R (if p then a else b) = if p then toM m R a else toM m R b := by
  split <;> rfl

/-- `selValJ` in the field. -/
theorem toM_selValJ {C : Curve} {K : WinCfg} {m : Mem} {base : Addr} (hp : UnitMod C.p (2 ^ (64 * K.M.n)))
    {r e d : Nat} {Z1 Z2 a b c : Fe C}
    (hz1 : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base K.R.z K.M.n) = Z1)
    (hl1 : wordsVal m base K.R.z K.M.n < C.p)
    (hz2 : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base K.E.z K.M.n) = Z2)
    (hl2 : wordsVal m base K.E.z K.M.n < C.p)
    (ha : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base r K.M.n) = a)
    (hb : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base e K.M.n) = b)
    (hc : toM C.p (2 ^ (64 * K.M.n)) (wordsVal m base d K.M.n) = c) :
    toM C.p (2 ^ (64 * K.M.n)) (selValJ m base K r e d) = if Z1 = 0 then b else if Z2 = 0 then a else c := by
  have i1 : wordsVal m base K.R.z K.M.n = 0 ↔ Z1 = 0 := by rw [← hz1]; exact (toM_eq_zero_iff hp hl1).symm
  have i2 : wordsVal m base K.E.z K.M.n = 0 ↔ Z2 = 0 := by rw [← hz2]; exact (toM_eq_zero_iff hp hl2).symm
  unfold selValJ
  rw [toM_iteJ, toM_iteJ, ha, hb, hc]
  simp only [i1, i2]

/-- `R = R + E` for `R` in Jacobian coordinates and `E` affine (or `O`), by
the mixed addition into `D`, with `R = E` where `R` is `O` and `R` kept where
`E` is `O`: for `R` and `E` standing for points not equal unless one is `O`. -/
theorem sumJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop} {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinStR K C base size Rp P s₀ s) {QR QE : Point C} (hQR : onCurve C QR = true)
    (hQE : onCurve C QE = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) QR)
    (hE : RepA C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) QE)
    (hsep : QR ≠ .infinity → QE ≠ .infinity → QR ≠ QE) {ma : Option (Prog isa)}
    (hM : MaddOk K C base size ma) :
    WP isa (WinCfg.sumJ K ma) s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .x19 = s.gpr .x19 ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      InvJ C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add QR QE) := by
  obtain ⟨-, -, ro_lt, -⟩ := hS.ro_tmv hL hF
  have oR := pt_other (K := K) (p := K.R) (Or.inl rfl)
  have oE := pt_other (K := K) (p := K.E) (Or.inr (Or.inl rfl))
  have oD := pt_other (K := K) (p := K.D) (Or.inr (Or.inr rfl))
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    List.mem_append_right (winRo K) (h x hx)
  have w1 := winJ_sl oD (sl _ oR) (sl _ oE)
  have V0 : ∀ x ∈ rcbR K.S K.R K.E, x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_in, ro_lt _ (by simp [winRo])⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oR _ (by simp)), hltR _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
    · exact ⟨winOther_mem (oE _ (by simp)), hltE _ (by simp)⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  have hM' : MaddSpec K C base size (WinCfg.maddRD K ma) := by
    cases ma with
    | some m => exact hM m rfl
    | none =>
      intro E s hI
      rw [WinCfg.maddRD, maddJ_eq]
      exact WP.mono (winN_ok hL hA hp maddJN_ok (hL.rcbApart_D (Or.inr rfl)) w1.1 w1.2.1 w1.2.2 hI
        (fun x hx => hx)) fun s' ⟨k, U, E', I, o, v⟩ =>
        ⟨k.mono fun _ h => List.mem_append_left _ h, U, E', I, o, v.trans (maddJN_run _)⟩
  rw [WinCfg.sumJ]
  refine WP.seq (WP.mono (hM' _ s I₀) fun s₁ ⟨k₁, U₁, E₁, I₁, o₁, v₁⟩ => ?_)
  have S₁ := hS.next hL I₁.scr (k₁.mono fun _ h => winSaved_combClob h) U₁
  obtain ⟨-, -, -, hRo, -, -, -, hEo, -, -⟩ := hL.other_ne
  have nD : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z], x ∉ rcbW K.S K.D := by
    intro x hx h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have h1 : ∀ y ∈ [K.R.x, K.R.y, K.R.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hRo y hy (List.mem_append_right _ h)
    have h2 : ∀ y ∈ [K.E.x, K.E.y, K.E.z], y ∉ rcbW K.S K.D := fun y hy h =>
      hEo y hy (List.mem_cons_of_mem _ h)
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h1 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
    · exact h2 _ (by simp) h
  have inV : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      x ∈ [K.D.x, K.D.y, K.D.z] ++ rcbR K.S K.R K.E := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append] at hx ⊢
    rcases hx with h | h | h | h | h | h | h | h | h <;> simp [h]
  have v₁' : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z],
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base x K.M.n) = tmv C K.M.n base s x := fun x hx => by
    rw [I₁.val x (inV x (by sub_mem hx)), o₁ x (nD x hx)]
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z],
      wordsVal s₁.mem base x K.M.n < C.p := fun x hx => I₁.lt x (inV x hx)
  have vD : (toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.x K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.y K.M.n),
      toM C.p (2 ^ (64 * K.M.n)) (wordsVal s₁.mem base K.D.z K.M.n)) =
      maddJF (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) := by
    refine Eq.trans ?_ v₁
    rw [I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp)), I₁.val _ (inV _ (by simp))]
  have jx := congrArg Prod.fst vD
  have jy := congrArg (fun t => t.2.1) vD
  have jz := congrArg (fun t => t.2.2) vD
  dsimp only at jx jy jz
  refine WP.mono (selSum_ok hL hA I₁.scr) fun s₂ ⟨r2x, r2y, r2z, k₂, U₂⟩ => ?_
  have c : ∀ r ∈ [Reg.x1, .x2, .x3, .x7, .x16], r ∈ combClob K.M.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [combClob, clob]
  have S₂ := S₁.next hL (I₁.scr.of_keepRegs k₂ (by decide)) (k₂.mono c) U₂
  have tz1 := v₁' K.R.z (by simp)
  have tz2 := v₁' K.E.z (by simp)
  have l1 := lt₁ K.R.z (by simp)
  have l2 := lt₁ K.E.z (by simp)
  have n19 : Reg.x19 ∉ clob K.M.n ++ winSaved K.M.n := fun h =>
    (List.mem_append.mp h).elim (x19_not_clob _) (not_mem_winSaved (by decide))
  refine ⟨S₂, by rw [k₂.gpr _ (by decide), k₁.gpr _ n19], fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [r2x, selValJ]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2y, selValJ]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
    · rw [r2z, selValJ]; split
      · exact lt₁ _ (by simp)
      · split <;> exact lt₁ _ (by simp)
  · show InvJ C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [r2x, r2y, r2z, toM_selValJ hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jx,
      toM_selValJ hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jy,
      toM_selValJ hp tz1 l1 tz2 l2 (v₁' _ (by simp)) (v₁' _ (by simp)) jz]
    exact InvJ.sumSelM hC hM3 hQR hQE hR hE hsep


/-! ## An iteration but the last -/

/-- `x4 = x19 - 1`. -/
theorem subX4_ok (s : State) {j : Nat} (hx : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.subImm .x .x4 .x19 1]) s fun t =>
      t.gpr .x4 = BitVec.ofNat 64 j - BitVec.ofNat 64 1 ∧ Keeps [.x4] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, Size.bits,
    show 1 < 4096 by decide, ite_true, RegUpd.gpr_write, BitVec.setWidth_eq,
    hx, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The Jacobian loop's invariant at `x19 = j`: `R` stands for `[winE k J j]P`
in Jacobian coordinates, the table affine. -/
structure WinInvJ (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinStR K C base size (RepA C) P s₀ s
  x19 : s.gpr .x19 = BitVec.ofNat 64 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : InvJ C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

/-- What the entry's selection writes is in `loopW`. -/
theorem entryW_loopW (K : WinCfg) : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n),
    (K.neg, 8 * K.M.n), (K.M.tmp, 8 * K.M.n)], w ∈ loopW K := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
  · exact Or.inr rfl

/-- `R` is apart from what the entry's selection writes. -/
theorem R_apart_entry {K : WinCfg} {size : Nat} (hL : WinLay K size) {x : Nat}
    (hx : x ∈ [K.R.x, K.R.y, K.R.z]) :
    ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  obtain ⟨-, -, -, hRo, -⟩ := hL.other_ne
  have hxw : x ∈ winWs K := winOther_ws K x (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have hne : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ≠ y := fun y hy e => hRo x hx (by
    rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> simp)
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
  · exact hL.lay.tmp x (winWs_slots K x hxw)

/-- An iteration but the last, `x19 = j ≥ 2` to `j - 1`: adds digit `j - 1`;
then `x4 = j - 2`. -/
theorem winStepJ_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hA : WinA K) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C)
    (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true) (hP0 : P ≠ .infinity)
    (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {j : Nat} (hj : 2 ≤ j) (hjn : j ≤ K.J)
    (hb : 16 * winE k K.J j + 8 < C.n) {s : State} (hI : WinInvJ K C base size k P s₀ s j)
    {dd : Option (Prog isa × Prog isa)} (hD : DblsOk K C base size dd) {ma : Option (Prog isa)}
    (hM : MaddOk K C base size ma) {sl : Option (List Instr)} (hS : SelOk K size (WinCfg.selOf K sl)) :
    WP isa (WinCfg.stepJ K dd ma sl) s fun s' =>
      WinInvJ K C base size k P s₀ s' (j - 1) ∧
        s'.gpr .x4 = BitVec.ofNat 64 (j - 1) - BitVec.ofNat 64 1 := by
  have hJ := hL.J
  rw [WinCfg.stepJ]
  refine WP.seq (WP.mono (decCounter_ok s (by omega_using [hj]) (by omega_using [hjn, hJ]) hI.x19)
    fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hS₁ := hI.st.next hL (hI.st.scr.of_keeps k₁ (by decide))
    ((Keeps.regs k₁).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [combClob]))
    (by rw [k₁.mem]; exact Unch.refl _ _ _)
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.mem]; exact hI.lt
  have rep₁ : InvJ C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J j) P) := by
    have e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.mem]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadJ_ok hL hA hp hC hM3 hP hD hF hS₁ (j := j - 1) (by omega_using [hjn, hJ]) b₁ lt₁ rep₁)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  have hx₅ : s₅.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [x₅, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_using [ht, this]) (by have := S₅.scr.nowrap; omega)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntryR_ok hL hA (RepA.infinity hC) RepA.negY (P := P) hpn hone_lt hone
    S₅.scr S₅.mod (i := j - 1) (by omega_using [hjn, hJ]) hx₅ hbits₅ hz₅ S₅.tbl hS) fun s₇ E₇ => ?_)
  have hn := S₅.scr.nowrap
  have S₇ := S₅.next hL E₇.scr E₇.keep (E₇.unch.mono (entryW_loopW K))
  have eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n :=
    fun x hx => E₇.unch.wordsVal (R_apart_entry hL hx) (by
      have := hL.lay.le x (winOther_mem (pt_other (K := K) (p := K.R) (Or.inl rfl) x hx)); omega_using [hn, this])
  have lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  have rep₇ : InvJ C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J j) P) := by
    have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [eR x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact r₅
  have hsep := win_sep hC hO hP hP0 (k := k) (J := K.J) (j := j - 1)
    (by rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)]; exact hb)
  rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)] at hsep
  refine WP.seq (WP.mono (sumJ_ok hL hA hp hC hM3 hF S₇ (hC.onCurve_mul hP _)
    (onCurve_winPt hC hP k (j - 1)) lt₇ E₇.lt rep₇ E₇.rep (fun h1 _ => (hsep h1).1) hM)
    fun s₈ ⟨S₈, x₈, l₈, r₈⟩ => ?_)
  have hadd := win_add hC hP (k := k) (J := K.J) (j := j - 1) hk8 (by omega_using [hjn, hJ])
  rw [Nat.sub_add_cancel (by omega_using [hj] : 1 ≤ j)] at hadd
  rw [hadd] at r₈
  have hx₇ : s₇.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [E₇.x19, hx₅]
  have hx₈ : s₈.gpr .x19 = BitVec.ofNat 64 (j - 1) := by rw [x₈, hx₇]
  refine WP.mono (subX4_ok s₈ hx₈) fun s₉ ⟨z₉, k₉⟩ => ⟨?_, z₉⟩
  refine ⟨S₈.next hL (S₈.scr.of_keeps k₉ (by decide))
      ((Keeps.regs k₉).mono (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        simp [combClob, clob]))
      (by rw [k₉.mem]; exact Unch.refl _ _ _), by rw [k₉.gpr _ (by decide), hx₈],
    by rw [k₉.mem]; exact l₈, ?_⟩
  have e : ∀ x, tmv C K.M.n base s₉ x = tmv C K.M.n base s₈ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₉.mem]
  rw [e, e, e]; exact r₈

end VG.Proof.Weierstrass.AArch64
