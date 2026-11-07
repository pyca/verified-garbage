module

-- separate module: the window method for any `a`, which only the verification of the curves whose `a` is not `-3` (the Brainpool curves') uses, kept out of the window proofs every curve imports
public import VerifiedGarbage.Impl.Weierstrass.X86_64.WindowGeneral
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinQuad
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
public import VerifiedGarbage.Proof.Weierstrass.JacDblAF
import VerifiedGarbage.Proof.Weierstrass.X86_64.Window
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinEntry
import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd

/-!
# The window method for any `a` on x86-64

`WinCfg.windowA` (`Impl/Weierstrass/X86_64/WindowGeneral.lean`) is
`WinCfg.window` with the complete addition for any `a` (`rcb`) in place of
`rcb3`, and the Jacobian doubling for any `a` (`dblJGen`, whose operations
compute `dblAF`: `dblJGenN_run`) in place of `dblJX`/`dblJMul`. Its proof is
`window_ok`'s (`WinLoop.lean`), with the lemmas it rests on that see the
formulas copied here:

* `WinFixedA` is `WinFixed` but with `3 b R mod p` in `S.b3` (`rcb` reads
  `3b`, `rcb3` `b`);
* the additions (`winAddA_ok`, `sumStepA_ok`, `buildStepA_ok`) end in
  `Law.add` in place of `Law.add3`;
* the doublings (`jacA_ok`) in `InvJ.dblA'`, whose `a` is the slot `S.a`,
  which the loop's environment holds (`WinStR.ro_tmvA`).

Everything else the window reads or writes (the recoding, the selection of
entries, their negation, `Y = 1` where `Z = 0`) is `window`'s, with its lemmas.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- What a program reads is in `V`. -/
local macro "rcb_sub" : tactic => `(tactic| plain_simp_names (
                   intro x hx
                   simp only [rcbR, WinCfg.zeroPt, List.cons_append, List.nil_append, List.mem_cons,
                     List.not_mem_nil, or_false] at hx ⊢
                   rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))

/-- `dblJGen` on numbered slots: `a` at 9, `p` at 11–13, `o` at 6–8. -/
def dblJGenN : List FOp := WinCfg.dblJGen ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

theorem dblJGenN_ok : NumOk dblJGenN := ⟨by decide, by decide, by decide⟩

theorem dblJGen_eq (S : RcbSlots) (p o : Pt) : WinCfg.dblJGen S p o = ofN dblJGenN S p p o := rfl

/-- `dblJGen`'s operations compute `dblAF` of the slot `9`'s `a`. -/
theorem dblJGenN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblJGenN e 6, runOps dblJGenN e 7, runOps dblJGenN e 8) = dblAF (e 9) (e 11) (e 12) (e 13) := by
  dsimp only [dblJGenN, WinCfg.dblJGen, runOps, List.foldl, FOp.run, Function.update]
  simp only [dblAF, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

/-- `WinFixed`, but with `3 b R mod p` in `S.b3`, as the complete addition for
any `a` reads it. -/
structure WinFixedA (K : WinCfg) (C : Curve) (base : Addr) (s₀ : State) (P : Point C) (k : Nat) :
    Prop where
  a : tmv C K.M.n base s₀ K.S.a = Fin.ofNat C.p C.a
  b : tmv C K.M.n base s₀ K.S.b3 = Fin.ofNat C.p (3 * C.b)
  ro_lt : ∀ x ∈ winRo K, wordsVal s₀.mem base x K.M.n < C.p
  zero : wordsVal s₀.mem base K.zero K.M.n = 0
  pt : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y) (tmv C K.M.n base s₀ K.P.z) P
  bits : ∀ t < 4 * K.J, s₀.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0

/-- `R = R + E` by the complete addition for any `a` into `D`, then copied: `winAdd_ok`. -/
theorem winAddA_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base)
    (hlt : ∀ x ∈ rcbR K.S K.R K.E, wordsVal s.mem base x K.M.n < C.p) :
    WP isa (Code.seq (fprogB K.M (rcb K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))).inline s
      (SumPostW K C base size (VG.Proof.Weierstrass.rcbAdd (tmv C K.M.n base s K.S.a)
        (tmv C K.M.n base s K.S.b3)
        (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
        (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z)) s) := by
  have hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.E, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winOther_mem (List.mem_append_right _ hx)
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  have hI : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.R K.E) (tmv C K.M.n base s) s :=
    ⟨hs, hM, fun x hx => hO x (List.mem_append_right _ hx), hlt, fun _ _ => rfl⟩
  refine winCopy_ok (V := rcbR K.S K.R K.E) hL hs (WP.mono (rcb_ok hL.lay hp (hL.rcbApart_D (Or.inr rfl)) hO hI (fun x hx => hx))
    fun s' ⟨k, I, v, _⟩ => ⟨k, I.sub fun x hx => ?_, v⟩)
  rcases List.mem_append.mp hx with h | h
  · refine List.mem_append_left _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp [rcbW]
  · exact List.mem_append_right _ h

theorem WinStR.ro_tmvA {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s₀ s : State} (h : WinStR K C base size Rp P s₀ s) (hF : WinFixedA K C base s₀ P k) :
    tmv C K.M.n base s K.S.a = Fin.ofNat C.p C.a ∧ tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p (3 * C.b) ∧
      (∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p) ∧ wordsVal s.mem base K.zero K.M.n = 0 := by
  have hn := h.scr.nowrap
  refine ⟨?_, ?_, fun x hx => ?_, ?_⟩
  · rw [winRo_tmv hL h.unch hn (by simp [winRo])]; exact hF.a
  · rw [winRo_tmv hL h.unch hn (by simp [winRo])]; exact hF.b
  · rw [winRo_val hL h.unch hn hx]; exact hF.ro_lt x hx
  · rw [winRo_val hL h.unch hn (by simp [winRo])]; exact hF.zero

/-- `R = R + E`, for `R` representing `PR` and `E` `PQ`. -/
theorem sumStepA_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {s₀ s : State} (hF : WinFixedA K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s)
    {PR PQ : Point C} (hPR : onCurve C PR = true) (hPQ : onCurve C PQ = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltq : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) PR)
    (hQ : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) PQ) :
    WP isa (Code.seq (fprogB K.M (rcb K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add PR PQ) := by
  obtain ⟨ta, tb, ro_lt, -⟩ := hS.ro_tmvA hL hF
  have hlt : ∀ x ∈ rcbR K.S K.R K.E, wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · exact hltR _ (by simp)
    · exact hltR _ (by simp)
    · exact hltR _ (by simp)
    · exact hltq _ (by simp)
    · exact hltq _ (by simp)
    · exact hltq _ (by simp)
  refine WP.mono (winAddA_ok hL hp hS.scr hS.mod hlt) fun s' S => ?_
  have hV := S.val
  rw [ta, tb] at hV
  exact ⟨hS.next hL S.scr (S.keep.mono clob_powClob) S.unch, S.keep.gpr _ (rbx_not_clob _), S.lt,
    hC.add hPR hPQ hR hQ hV.symm⟩

/-- An entry of the table: `D = E + P` (`[m + 1]P`), `E = D`, and `D` into
entry `m + 1`. -/
theorem buildStepA_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    (hP : onCurve C P = true) {s₀ : State} (hF : WinFixedA K C base s₀ P k) {m : Nat} (h1 : 1 ≤ m)
    (h7 : m ≤ 7) {s : State} (hI : BuildInvE K C base size P s₀ m s) :
    WP isa (WinCfg.buildStepA K).inline s fun s' =>
      BuildInvE K C base size P s₀ (m + 1) s' ∧ s'.zf = some (decide (8 - (m + 1) = 0)) := by
  have hn := hI.inv.scr.nowrap
  rw [WinCfg.buildStepA]
  refine WP.seq (WP.mono (decRbx_ok s (j := 8 - m) (by omega_using [h1, h7]) (by omega_using [h1, h7]) hI.rbx) fun s₁ ⟨x₁, k₁⟩ => ?_)
  have hs₁ := hI.inv.scr.of_keeps k₁ (by decide)
  have m₁ : s₁.mem = s.mem := k₁.2.1
  have ta : tmv C K.M.n base s₁ K.S.a = Fin.ofNat C.p C.a := by
    show toM _ _ _ = _; rw [m₁, winRo_val hL hI.inv.unch hn (by simp [winRo])]; exact hF.a
  have tb : tmv C K.M.n base s₁ K.S.b3 = Fin.ofNat C.p (3 * C.b) := by
    show toM _ _ _ = _; rw [m₁, winRo_val hL hI.inv.unch hn (by simp [winRo])]; exact hF.b
  have ro_lt : ∀ x ∈ winRo K, wordsVal s₁.mem base x K.M.n < C.p := fun x hx => by
    rw [m₁, winRo_val hL hI.inv.unch hn hx]; exact hF.ro_lt x hx
  have tP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], tmv C K.M.n base s₁ x = tmv C K.M.n base s₀ x := by
    intro x hx; show toM _ _ _ = toM _ _ _; rw [m₁, winRo_val hL hI.inv.unch hn (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> simp [winRo])]
  have hO : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P, x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact winOther_mem (List.mem_append_right _ hx)
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  have hlt : ∀ x ∈ rcbR K.S K.E K.P, wordsVal s₁.mem base x K.M.n < C.p := by
    intro x hx
    simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · rw [m₁]; exact hI.lt _ (by simp)
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
    · exact ro_lt _ (by simp [winRo])
  have hI₁ : Inv K.M base size C.p (· ∈ winSlots K) (rcbR K.S K.E K.P) (tmv C K.M.n base s₁) s₁ :=
    ⟨hs₁, by rw [m₁]; exact hI.inv.mod, fun x hx => hO x (List.mem_append_right _ hx), hlt,
      fun _ _ => rfl⟩
  have W := rcb_ok hL.lay hp hL.rcbApart_EP hO hI₁ (fun x hx => hx)
  refine WP.seq ((WP.mono W fun s₂ ⟨k₂, I₂, v₂, _⟩ => ?_))
  -- `D` is `[m + 1]P`.
  have hox : K.D.x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P := by simp [rcbW]
  have hoy : K.D.y ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P := by simp [rcbW]
  have hoz : K.D.z ∈ rcbW K.S K.D ++ rcbR K.S K.E K.P := by simp [rcbW]
  have dlt : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₂.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact I₂.lt _ hox
    · exact I₂.lt _ hoy
    · exact I₂.lt _ hoz
  have dRep : Rep C (tmv C K.M.n base s₂ K.D.x) (tmv C K.M.n base s₂ K.D.y) (tmv C K.M.n base s₂ K.D.z)
      (mul (m + 1) P) := by
    have hS : (tmv C K.M.n base s₂ K.D.x, tmv C K.M.n base s₂ K.D.y, tmv C K.M.n base s₂ K.D.z) =
        VG.Proof.Weierstrass.rcbAdd (tmv C K.M.n base s₁ K.S.a) (tmv C K.M.n base s₁ K.S.b3)
          (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
          (tmv C K.M.n base s₁ K.P.x) (tmv C K.M.n base s₁ K.P.y) (tmv C K.M.n base s₁ K.P.z) := by
      rw [← v₂]
      show (toM _ _ _, toM _ _ _, toM _ _ _) = _
      rw [I₂.val _ hox, I₂.val _ hoy, I₂.val _ hoz]
    rw [ta, tb, tP K.P.x (by simp), tP K.P.y (by simp), tP K.P.z (by simp)] at hS
    have hE : Rep C (tmv C K.M.n base s₁ K.E.x) (tmv C K.M.n base s₁ K.E.y) (tmv C K.M.n base s₁ K.E.z)
        (mul m P) := by
      show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _; rw [m₁]; exact hI.rep
    have hPr : Rep C (tmv C K.M.n base s₀ K.P.x) (tmv C K.M.n base s₀ K.P.y)
        (tmv C K.M.n base s₀ K.P.z) (mul 1 P) := by rw [mul_one_pt]; exact hF.pt
    have hR := hC.add (hC.onCurve_mul hP m) (hC.onCurve_mul hP 1) hE hPr hS.symm
    rw [hC.add_mul_mul hP] at hR
    exact hR
  have hs₂ := k₂.scr hs₁
  have U₂ := k₂.unch
  -- `E = D`.
  have eO : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.D.x, K.D.y, K.D.z], y ∈ winOther K := by
    intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> win_mem
  obtain ⟨-, -, -, -, exy, exz, eyz, hED, -, -⟩ := hL.other_ne
  have hEd : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∉ [K.D.x, K.D.y, K.D.z] := by
    intro x hx hd
    refine hED x hx (List.mem_cons_of_mem _ ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp [rcbW]
  refine WP.seq (WP.mono (copyPt_ok hs₂ (o := K.E) (a := K.D) (n := K.M.n)
    (fun x hx => hL.lay.le x (winOther_mem (eO x hx)))
    (fun x hx y hy hxy => hL.apart₂ (winOther_ws K x (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx)))
      (winOther_ws K y (eO y hy)) hxy) hEd ⟨exy, exz, eyz⟩) fun s₃ ⟨e1, e2, e3, k₃, U₃⟩ => ?_)
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have x₃ : s₃.gpr .rbx = BitVec.ofNat 64 (7 - m) := by
    rw [k₃.gpr _ (by decide), k₂.gpr _ (rbx_not_clob _), x₁]; congr 1; omega_using [h1, h7]
  -- `D` into entry `m + 1`.
  refine WP.seq (WP.mono (storeEntry_ok hL (i := 7 - m) 6 (by omega_using [h1, h7]) (Nat.le_refl _) hs₃ x₃)
    fun s₄ ⟨f1, f2, f3, k₄, U₄⟩ => ?_)
  rw [show 8 - (7 - m) = m + 1 by omega_using [h1, h7]] at f1 f2 f3 U₄
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have x₄ : s₄.gpr .rbx = BitVec.ofNat 64 (7 - m) := by rw [k₄.gpr _ (by decide), x₃]
  refine WP.mono (testRbx_ok s₄ (j := 7 - m) (by omega_using [h1, h7]) x₄) fun s₅ ⟨z₅, k₅⟩ => ?_
  have m₅ : s₅.mem = s₄.mem := k₅.2.1
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega_using [this, hn]
  have sT := tblPt_slots K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7])
  -- `D` is kept by the copy into `E`, and `E` by the store.
  have dE : ∀ x ∈ [K.D.x, K.D.y, K.D.z], wordsVal s₃.mem base x K.M.n = wordsVal s₂.mem base x K.M.n := by
    intro x hx
    refine U₃.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (List.mem_append_right [K.E.x, K.E.y, K.E.z] hx))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxE : ∀ y ∈ [K.E.x, K.E.y, K.E.z], x ≠ y := fun y hy hxy => hEd y hy (hxy ▸ hx)
    rcases hw with rfl | rfl | rfl <;> dsimp only <;>
      exact hL.apart₂ (winOther_ws K x (eO x (List.mem_append_right [K.E.x, K.E.y, K.E.z] hx)))
        (winOther_ws K _ (eO _ (by simp))) (hxE _ (by simp))
  have tE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s₄.mem base x K.M.n = wordsVal s₃.mem base x K.M.n := by
    intro x hx
    refine U₄.wordsVal (fun w hw => ?_) (b64 x (winOther_mem (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx))))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hxo : x ∈ winRo K ++ winOther K := List.mem_append_right _ (eO x (List.mem_append_left [K.D.x, K.D.y, K.D.z] hx))
    rcases hw with rfl | rfl | rfl <;> dsimp only
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).x ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).y ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
    · obtain ⟨i, hi, e, -, -⟩ := tblPt_mem K (m := m + 1) (by omega_using [h1, h7]) (by omega_using [h1, h7]) _ (by simp : (K.tblPt (m + 1)).z ∈ _)
      rw [e]; exact hL.tbl_apart hxo hi
  have vEx : wordsVal s₅.mem base K.E.x K.M.n = wordsVal s₂.mem base K.D.x K.M.n := by
    rw [m₅, tE _ (by simp), e1]
  have vEy : wordsVal s₅.mem base K.E.y K.M.n = wordsVal s₂.mem base K.D.y K.M.n := by
    rw [m₅, tE _ (by simp), e2]
  have vEz : wordsVal s₅.mem base K.E.z K.M.n = wordsVal s₂.mem base K.D.z K.M.n := by
    rw [m₅, tE _ (by simp), e3]
  have vTx : wordsVal s₅.mem base (K.tblPt (m + 1)).x K.M.n = wordsVal s₂.mem base K.D.x K.M.n := by
    rw [m₅, f1, dE _ (by simp)]
  have vTy : wordsVal s₅.mem base (K.tblPt (m + 1)).y K.M.n = wordsVal s₂.mem base K.D.y K.M.n := by
    rw [m₅, f2, dE _ (by simp)]
  have vTz : wordsVal s₅.mem base (K.tblPt (m + 1)).z K.M.n = wordsVal s₂.mem base K.D.z K.M.n := by
    rw [m₅, f3, dE _ (by simp)]
  -- What the step writes: the addition's slots and temporary area, `E` and the entry.
  have UU := U₂.trans (U₃.trans U₄)
  have L2 : ∀ w ∈ (rcbW K.S K.D).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)],
      w = (K.M.tmp, 8 * K.M.n) ∨ ∃ y ∈ winOther K, w = (y, 8 * K.M.n) := by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact Or.inr ⟨y, List.mem_append_right _ hy, rfl⟩
    · exact Or.inl (List.mem_singleton.mp h)
  have L3 : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)],
      ∃ y ∈ winOther K, w = (y, 8 * K.M.n) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, by win_mem, rfl⟩
    · exact ⟨_, by win_mem, rfl⟩
    · exact ⟨_, by win_mem, rfl⟩
  have L4 : ∀ w ∈ [((K.tblPt (m + 1)).x, 8 * K.M.n), ((K.tblPt (m + 1)).y, 8 * K.M.n),
      ((K.tblPt (m + 1)).z, 8 * K.M.n)], ∃ y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y,
        (K.tblPt (m + 1)).z], w = (y, 8 * K.M.n) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨_, by simp, rfl⟩
    · exact ⟨_, by simp, rfl⟩
  have split : ∀ {Q : Nat × Nat → Prop}, (w : Nat × Nat) →
      w ∈ (rcbW K.S K.D).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)] ++
        ([(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] ++
          [((K.tblPt (m + 1)).x, 8 * K.M.n), ((K.tblPt (m + 1)).y, 8 * K.M.n),
            ((K.tblPt (m + 1)).z, 8 * K.M.n)]) →
      Q (K.M.tmp, 8 * K.M.n) → (∀ y ∈ winOther K, Q (y, 8 * K.M.n)) →
      (∀ y ∈ [(K.tblPt (m + 1)).x, (K.tblPt (m + 1)).y, (K.tblPt (m + 1)).z], Q (y, 8 * K.M.n)) → Q w := by
    intro Q w hw qt qo qT
    rcases List.mem_append.mp hw with h | h
    · rcases L2 w h with rfl | ⟨y, hy, rfl⟩
      · exact qt
      · exact qo y hy
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨y, hy, rfl⟩ := L3 w h; exact qo y hy
      · obtain ⟨y, hy, rfl⟩ := L4 w h; exact qT y hy
  have U : Unch base (winW K) s.mem s₅.mem := by
    rw [← m₁, m₅]
    refine UU.mono fun w hw => split w hw (by simp [winW])
      (fun y hy => by simp only [winW, List.mem_append, List.mem_map]; exact Or.inl ⟨y, winOther_ws K y hy, rfl⟩)
      (fun y hy => by simp only [winW, List.mem_append, List.mem_map]; exact Or.inl ⟨y, (sT y hy).2, rfl⟩)
  have keep : KeepRegs (powClob K.M.n) s s₅ := by
    have c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp at hr; subst hr; simp [powClob, clob]
    exact (((Keeps.regs k₁).mono fun r hr => by simp at hr; simp [hr, powClob]).trans
      ((⟨fun r hr => k₂.gpr r fun h => hr (List.mem_cons_of_mem _ h), k₂.rd, k₂.wr⟩ :
        KeepRegs (powClob K.M.n) s₁ s₂).trans ((k₃.mono c1).trans ((k₄.mono c1).trans
          ((Keeps.regs k₅).mono fun r hr => by simp at hr)))))
  refine ⟨⟨⟨hs₄.of_keeps k₅ (by decide), hI.inv.keep.trans keep,
    (hI.inv.unch.trans U).mono fun w hw => by rcases List.mem_append.mp hw with h | h <;> exact h,
    hI.inv.mod.unch U (winW_mo hL hI.inv.mod) hn, fun j hj1 hjm => ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rcases Nat.lt_or_ge j (m + 1) with hj | hj
    · -- An entry built before keeps its numbers.
      have Tj := hI.inv.tbl j hj1 (by omega_using [h1, h7, hj1, hjm, hj])
      have sj := tblPt_slots K (m := j) hj1 (by omega_using [h1, h7, hj1, hjm, hj])
      have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
          wordsVal s₅.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
        intro x hx
        rw [← m₁, m₅]
        obtain ⟨i, hi, hxi, -, -⟩ := tblPt_mem K hj1 (by omega_using [h1, h7, hj1, hjm, hj]) x hx
        refine UU.wordsVal (fun w hw => split (Q := fun w =>
            x + 8 * K.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x) w hw
          (by rw [hxi]; exact hL.lay.tmp _ (by
            simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)))
          (fun y hy => by rw [hxi]; exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm)
          (fun y hy => tbl_apart_entry (K := K) hj1 (by omega_using [h1, h7, hj1, hjm, hj]) (by omega_using [h1, h7, hj1, hjm, hj]) (by omega_using [h1, h7, hj1, hjm, hj]) (by omega_using [h1, h7, hj1, hjm, hj]) x hx
            y hy)) (b64 _ (sj _ hx).1)
      refine ⟨fun x hx => by rw [e x hx]; exact Tj.1 x hx, ?_⟩
      have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
          tmv C K.M.n base s₅ x = tmv C K.M.n base s x := fun x hx => by
        show toM _ _ _ = toM _ _ _; rw [e x hx]
      rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
      exact Tj.2
    · obtain rfl : j = m + 1 := by omega_using [hjm, hj]
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [vTx]; exact dlt _ (by simp)
        · rw [vTy]; exact dlt _ (by simp)
        · rw [vTz]; exact dlt _ (by simp)
      · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [vTx, vTy, vTz]; exact dRep
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [vEx]; exact dlt _ (by simp)
    · rw [vEy]; exact dlt _ (by simp)
    · rw [vEz]; exact dlt _ (by simp)
  · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
    rw [vEx, vEy, vEz]; exact dRep
  · rw [k₅.1 _ (by decide), x₄]; congr 1; omega_using [h1, h7]
  · rw [z₅]; congr 1; simp only [decide_eq_decide]; omega_using [h1, h7]

/-- The table `[1 … 8]P`. -/
theorem buildA_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    (hP : onCurve C P = true) {s : State} (hs : Scr s base size) (hM : ModOkW K.M size C.p s.mem base)
    (hF : WinFixedA K C base s P k) :
    WP isa (WinCfg.buildA K).inline s (BuildInv K C base size P s 8) := by
  have hn := hs.nowrap
  have s1 := tblPt_slots K (m := 1) (Nat.le_refl _) (by omega_arith)
  have pRo : ∀ x ∈ [K.P.x, K.P.y, K.P.z], x ∈ winRo K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [winRo]
  have eO : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have b64 : ∀ x ∈ winSlots K, x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := hL.lay.le x hx; omega_arith
  -- `[1]P = P`.
  have tP : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z], ∀ y ∈ [K.P.x, K.P.y, K.P.z],
      x + 8 * K.M.n ≤ y ∨ y + 8 * K.M.n ≤ x := by
    intro x hx y hy
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega_arith) x hx
    exact (hL.tbl_apart (List.mem_append_left _ (pRo y hy)) hi).symm
  have ne1 : (K.tblPt 1).x ≠ (K.tblPt 1).y ∧ (K.tblPt 1).x ≠ (K.tblPt 1).z ∧
      (K.tblPt 1).y ≠ (K.tblPt 1).z := by
    rw [tblPt_x, tblPt_y, tblPt_z]
    exact ⟨hL.tbl_ne₂ (by omega_arith), hL.tbl_ne₂ (by omega_arith), hL.tbl_ne₂ (by omega_arith)⟩
  have slP : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z] ++
      [K.P.x, K.P.y, K.P.z] by simpa using hx) with h | h
    · exact (s1 x h).1
    · exact winRo_slots K x (pRo x h)
  rw [WinCfg.buildA]
  simp only [Code.inline]
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyPt_ok hs (o := K.tblPt 1) (a := K.P) (n := K.M.n)
    (fun x hx => hL.lay.le x (slP x hx))
    (fun x hx y hy hxy => by
      rcases List.mem_append.mp (show y ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z] ++
        [K.P.x, K.P.y, K.P.z] by simpa using hy) with h | h
      · exact hL.apart₂ (s1 x hx).2 (s1 y h).2 hxy
      · exact tP x hx y h)
    (fun x hx h => by have := tP x hx x h; have := hL.n0; omega_arith) ne1) fun s₁ ⟨a1, a2, a3, k₁, U₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  -- `E = P`.
  obtain ⟨-, -, -, -, exy, exz, eyz, -⟩ := hL.other_ne
  have eP : ∀ x ∈ [K.E.x, K.E.y, K.E.z], ∀ y ∈ [K.P.x, K.P.y, K.P.z], x ≠ y := fun x hx y hy h =>
    hL.ro y (pRo y hy) (h ▸ eO x hx)
  have slE : ∀ x ∈ [K.E.x, K.E.y, K.E.z, K.P.x, K.P.y, K.P.z], x ∈ winSlots K := by
    intro x hx
    rcases List.mem_append.mp (show x ∈ [K.E.x, K.E.y, K.E.z] ++ [K.P.x, K.P.y, K.P.z] from hx) with h | h
    · exact winOther_mem (eO x h)
    · exact winRo_slots K x (pRo x h)
  rw [WP.block_append_iff]
  refine WP.mono (copyPt_ok hs₁ (o := K.E) (a := K.P) (n := K.M.n)
    (fun x hx => hL.lay.le x (slE x hx))
    (fun x hx y hy hxy => hL.lay.apart x y (slE x (List.mem_append_left [K.P.x, K.P.y, K.P.z] hx)) (slE y hy) hxy)
    (fun x hx h => eP x hx x h rfl) ⟨exy, exz, eyz⟩) fun s₂ ⟨c1, c2, c3, k₂, U₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (mov32Rbx_ok s₂ (j := 7) (by decide)) fun s₃ ⟨x₃, k₃⟩ => ?_
  -- The invariant for `[1]P`.
  have U : Unch base (winW K) s.mem s₃.mem := by
    rw [k₃.2.1]
    refine (U₁.trans U₂).mono fun w hw => ?_
    rcases List.mem_append.mp hw with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [winW, List.mem_append, List.mem_map]
      rcases h with rfl | rfl | rfl
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
      · exact Or.inl ⟨_, (s1 _ (by simp)).2, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [winW, List.mem_append, List.mem_map]
      rcases h with rfl | rfl | rfl
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
      · exact Or.inl ⟨_, winOther_ws K _ (eO _ (by simp)), rfl⟩
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  -- `[1]P` is kept by the copy into `E`.
  have kT : ∀ x ∈ [(K.tblPt 1).x, (K.tblPt 1).y, (K.tblPt 1).z],
      wordsVal s₃.mem base x K.M.n = wordsVal s₁.mem base x K.M.n := by
    intro x hx
    rw [m₃]
    refine U₂.wordsVal (fun w hw => ?_) (b64 x (s1 x hx).1)
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K (m := 1) (Nat.le_refl _) (by omega_arith) x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact (hL.tbl_apart (x := K.E.x) (List.mem_append_right _ (by win_mem)) hi).symm
    · exact (hL.tbl_apart (x := K.E.y) (List.mem_append_right _ (by win_mem)) hi).symm
    · exact (hL.tbl_apart (x := K.E.z) (List.mem_append_right _ (by win_mem)) hi).symm
  have kP : ∀ x ∈ [K.P.x, K.P.y, K.P.z], wordsVal s₁.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    refine U₁.wordsVal (fun w hw => ?_) (b64 x (winRo_slots K x (pRo x hx)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;>
      exact (tP _ (by simp) x hx).symm
  have c1' : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by intro r hr; simp at hr; subst hr; simp [powClob, clob]
  have I₁ : BuildInvE K C base size P s 1 s₃ := by
    refine ⟨⟨hs₂.of_keeps k₃ (by decide), ((k₁.mono c1').trans (k₂.mono c1')).trans
      ((Keeps.regs k₃).mono fun r hr => by simp at hr; simp [hr, powClob]), U, hM.unch U (winW_mo hL hM) hn,
      fun j hj1 hj => ?_⟩, fun x hx => ?_, ?_, by rw [x₃]⟩
    · obtain rfl : j = 1 := by omega_arith
      refine ⟨fun x hx => ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · rw [kT _ (by simp), a1]; exact hF.ro_lt _ (by simp [winRo])
        · rw [kT _ (by simp), a2]; exact hF.ro_lt _ (by simp [winRo])
        · rw [kT _ (by simp), a3]; exact hF.ro_lt _ (by simp [winRo])
      · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
        rw [kT _ (by simp), kT _ (by simp), kT _ (by simp), a1, a2, a3, mul_one_pt]
        exact hF.pt
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [m₃]
      rcases hx with rfl | rfl | rfl
      · rw [c1, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
      · rw [c2, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
      · rw [c3, kP _ (by simp)]; exact hF.ro_lt _ (by simp [winRo])
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [m₃, c1, c2, c3, kP _ (by simp), kP _ (by simp), kP _ (by simp), mul_one_pt]
      exact hF.pt
  exact countLoop_ok (Inv := fun j t => BuildInvE K C base size P s (8 - j) t) (n := 7)
    (fun j t h1 h2 hi => WP.mono (buildStepA_ok hL hp hC hP hF (m := 8 - j) (by omega_arith) (by omega_arith) hi)
      fun u ⟨I, z⟩ => ⟨by rw [show 8 - (j - 1) = 8 - j + 1 by omega_arith]; exact I,
        by rw [z]; congr 1; simp only [decide_eq_decide]; omega_arith⟩)
    (fun t hi => hi.inv) (by decide) I₁

/-- `R = 16 R` in Jacobian coordinates, but `Y`: the triple `(X : Y : Z)` stands for
`[16 e]P` (or `Z = 0`), `R` is `(XZ : Y : Z³)` and `E.z` is `Z`. -/
theorem jacA_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    (hP : onCurve C P = true) {s₀ s : State} (hF : WinFixedA K C base s₀ P k)
    (hS : WinSt K C base size P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.jacA K).inline s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      ∃ X Y Z : Fe C, InvJ C X Y Z (mul (16 * e) P) ∧ tmv C K.M.n base s' K.R.x = X * Z ∧
        tmv C K.M.n base s' K.R.y = Y ∧ tmv C K.M.n base s' K.R.z = Z * Z * Z ∧
        tmv C K.M.n base s' K.E.z = Z := by
  obtain ⟨-, -, ro_lt, hz⟩ := hS.ro_tmvA hL hF
  obtain ⟨a1, a2, a3, a4⟩ := hL.rcbApart_jac
  have oR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have oE : ∀ x ∈ [K.E.x, K.E.y, K.E.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have oD : ∀ x ∈ [K.D.x, K.D.y, K.D.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have sZ : ∀ x ∈ [(WinCfg.zeroPt K).x, (WinCfg.zeroPt K).y, (WinCfg.zeroPt K).z], x ∈ winSlots K := by
    intro x hx
    simp only [WinCfg.zeroPt, List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    subst hx; win_mem
  have sl := fun (P : Pt) (h : ∀ x ∈ [P.x, P.y, P.z], x ∈ winOther K) x (hx : x ∈ [P.x, P.y, P.z]) =>
    winOther_mem (h x hx)
  have w1 := winJ_sl oE (sl _ oR) sZ
  have w2 := winJ_sl oD (sl _ oE) (sl _ oE)
  have w3 := winJ_sl oE (sl _ oD) (sl _ oD)
  have w4 := winJ_sl oR (sl _ oE) sZ
  have V0 : ∀ x ∈ [K.S.a, K.S.b3, K.zero, K.R.x, K.R.y, K.R.z],
      x ∈ winSlots K ∧ wordsVal s.mem base x K.M.n < C.p := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | h | h | h
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    · exact ⟨by win_mem, ro_lt _ (by simp [winRo])⟩
    all_goals exact ⟨winOther_mem (oR _ (by simp [h])), hlt _ (by simp [h])⟩
  have I₀ : Inv K.M base size C.p (· ∈ winSlots K) [K.S.a, K.S.b3, K.zero, K.R.x, K.R.y, K.R.z]
      (tmv C K.M.n base s) s :=
    ⟨hS.scr, hS.mod, fun x hx => (V0 x hx).1, fun x hx => (V0 x hx).2, fun _ _ => rfl⟩
  have hQ := fun (a : Nat) => hC.onCurve_mul hP a
  simp only [WinCfg.jacA, toJ_eq, fromJ_eq]
  -- Into Jacobian coordinates, in `E`.
  refine WP.seq (WP.mono (winN_ok hL hp toJN_ok a1 w1.1 w1.2 I₀ (by rcb_sub))
    fun s₁ ⟨k₁, U₁, E₁, I₁, _, v₁⟩ => ?_)
  have S₁ := hS.next hL I₁.scr (k₁.mono clob_powClob) U₁
  have J₁ : InvJ C (E₁ K.E.x) (E₁ K.E.y) (E₁ K.E.z) (mul e P) :=
    InvJ.of_toJ (z := tmv C K.M.n base s K.zero) hC hR (show toM _ _ _ = 0 by rw [hz]; exact toM_zero _ _)
      (v₁.trans (toJN_run _))
  -- Two iterations of the same pair of doublings.
  let V := [K.E.x, K.E.y, K.E.z, K.S.a, K.S.b3, K.zero]
  have I₁' : Inv K.M base size C.p (· ∈ winSlots K) V E₁ s₁ :=
    I₁.sub (by intro x hx; simp only [V, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
               rcases hx with h | h | h | h | h | h <;> simp [h])
  refine WP.seq (WP.mono (quadStart_ok s₁ ((k₁.gpr _ (rbx_not_clob _)).trans hb))
    fun s₂ ⟨b₂, kc₂⟩ => ?_)
  let LI := fun j st => WinSt K C base size P s₀ st ∧
    st.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) ∧ ∃ E : Nat → Fe C,
    Inv K.M base size C.p (· ∈ winSlots K) V E st ∧
    InvJ C (E K.E.x) (E K.E.y) (E K.E.z) (mul (4 ^ (2 - j) * e) P)
  have start : LI 2 s₂ := ⟨S₁.rbxKeeps hL kc₂, b₂, E₁, I₁'.rbxKeeps kc₂, by simpa using J₁⟩
  have body : ∀ j st, 1 ≤ j → j ≤ 2 → LI j st →
      WP isa (WinCfg.jacPairA K).inline st fun st' => LI (j - 1) st' ∧ st'.cf = some (decide (j - 1 = 0)) := by
    intro j st hj hj' ⟨S, b, E, I, J⟩
    simp only [WinCfg.jacPairA, dblJGen_eq]
    have hA : E K.S.a = Fin.ofNat C.p C.a :=
      (I.val K.S.a (by simp [V])).symm.trans (S.ro_tmvA hL hF).1
    refine WP.seq (WP.mono (winN_ok hL hp dblJGenN_ok a2 w2.1 w2.2 I (by
      dsimp [V]; rcb_sub)) fun st₁ ⟨k₁', U₁', E₁', I₁', _, v₁'⟩ => ?_)
    have S₁' := S.next hL I₁'.scr (k₁'.mono clob_powClob) U₁'
    have hA₁ : E₁' K.S.a = Fin.ofNat C.p C.a :=
      (I₁'.val K.S.a (by simp [V])).symm.trans (S₁'.ro_tmvA hL hF).1
    have J₁' := InvJ.dblA' hC (hQ _) J hA (v₁'.trans (dblJGenN_run _))
    rw [hC.double hP] at J₁'
    refine WP.seq (WP.mono (winN_ok hL hp dblJGenN_ok a3 w3.1 w3.2 I₁' (by
      dsimp [V]; rcb_sub)) fun st₂ ⟨k₂', U₂', E₂', I₂', _, v₂'⟩ => ?_)
    have S₂' := S₁'.next hL I₂'.scr (k₂'.mono clob_powClob) U₂'
    have J₂' := InvJ.dblA' hC (hQ _) J₁' hA₁ (v₂'.trans (dblJGenN_run _))
    rw [hC.double hP] at J₂'
    have ar : 2 * (2 * (4 ^ (2 - j) * e)) = 4 ^ (2 - (j - 1)) * e := by
      have hj12 : j = 1 ∨ j = 2 := by omega_arith
      rcases hj12 with rfl | rfl <;> simp <;> omega_arith
    rw [ar] at J₂'
    have b' : st₂.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j) := by
      rw [k₂'.gpr _ (rbx_not_clob _), k₁'.gpr _ (rbx_not_clob _), b]
    refine WP.mono (quadCount_ok st₂ hi hj hj' b') fun st₃ ⟨b₃, c₃, kc₃⟩ => ?_
    have I₂'' : Inv K.M base size C.p (· ∈ winSlots K) V E₂' st₂ :=
      I₂'.sub (by
        intro x hx
        simp only [V, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with h | h | h | h | h | h <;> simp [h])
    exact ⟨⟨S₂'.rbxKeeps hL kc₃, b₃, E₂', I₂''.rbxKeeps kc₃, J₂'⟩, c₃⟩
  refine WP.seq (WP.mono (quadLoop_ok body (fun _ h => h) start)
    fun s₅ ⟨S₅, b₅, E₅, I₅, J₅⟩ => ?_)
  have rb₅ : s₅.gpr .rbx = s.gpr .rbx := by simpa only [Nat.mul_zero, Nat.add_zero, hb] using b₅
  have J₅ : InvJ C (E₅ K.E.x) (E₅ K.E.y) (E₅ K.E.z) (mul (16 * e) P) := by simpa using J₅
  -- Back to projective coordinates, in `R`.
  refine WP.mono (winN_ok hL hp fromJN_ok a4 w4.1 w4.2 I₅ (by dsimp [V]; rcb_sub))
    fun s₆ ⟨k₆, U₆, E₆, I₆, o₆, v₆⟩ => ?_
  have S₆ := S₅.next hL I₆.scr (k₆.mono clob_powClob) U₆
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmvA hL hF
  have z₅ : E₅ K.zero = 0 := by
    rw [← I₅.val _ (by simp [V]), hz₅]; exact toM_zero _ _
  have r₆ : (E₆ K.R.x, E₆ K.R.y, E₆ K.R.z) = (E₅ K.E.x * E₅ K.E.z, E₅ K.E.y + E₅ K.zero,
      E₅ K.E.z * E₅ K.E.z * E₅ K.E.z) := v₆.trans (fromJN_run _)
  simp only [z₅, Prod.mk.injEq] at r₆
  have ez : E₆ K.E.z = E₅ K.E.z := o₆ _ (a4.apart _ (by simp [rcbR]))
  refine ⟨S₆, by
      rw [k₆.gpr _ (rbx_not_clob _), rb₅],
    fun x hx => I₆.lt x (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with
      h | h | h | h <;> simp [V, h]),
    E₅ K.E.x, E₅ K.E.y, E₅ K.E.z, J₅, ?_, ?_, ?_, ?_⟩
  · exact (I₆.val _ (by simp)).trans r₆.1
  · exact (I₆.val _ (by simp)).trans (r₆.2.1.trans (by grind))
  · exact (I₆.val _ (by simp)).trans r₆.2.2
  · exact (I₆.val _ (by simp [V])).trans ez

/-- `R = 16 R`: `[e]P` to `[16 e]P`. -/
theorem quadA_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ s : State} (hF : WinFixedA K C base s₀ P k)
    (hS : WinSt K C base size P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quadA K).inline s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  rw [WinCfg.quadA]
  refine WP.seq (WP.mono (jacA_ok hL hp hC hP hF hS hi hb hlt hR)
    fun s₁ ⟨S₁, x₁, l₁, X, Y, Z, hJ, ex, ey, ez, eE⟩ => ?_)
  have hn := S₁.scr.nowrap
  refine WP.mono (ySel_ok hL S₁.scr (Nat.lt_trans hone_lt hpn)) fun s₂ ⟨v₂, k₂, U₂⟩ => ?_
  have hRy : K.R.y ∈ winOther K := by win_mem
  have c₂ : ∀ r ∈ [Reg.rax, .rdx, .r8], r ∈ powClob K.M.n := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simp [powClob, clob]
    · simp [powClob, clob]
    · exact List.mem_cons_of_mem _ (r8_mem_clob _)
  have S₂ := S₁.next hL (S₁.scr.of_keepRegs k₂ (by decide)) (k₂.mono c₂)
    (U₂.mono fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact List.mem_append_left _ (List.mem_map_of_mem hRy))
  obtain ⟨rxy, -, ryz, -⟩ := hL.other_ne
  have hws : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winWs K := fun x hx => winOther_ws K x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem)
  have eR : ∀ x ∈ [K.R.x, K.R.z], x ≠ K.R.y →
      wordsVal s₂.mem base x K.M.n = wordsVal s₁.mem base x K.M.n := by
    intro x hx hne
    have hxw : x ∈ winWs K := hws x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h <;> simp [h])
    refine U₂.wordsVal (fun w hw => ?_) (by have := hL.lay.le x (winWs_slots K x hxw); omega_arith)
    rw [List.mem_singleton.mp hw]
    exact hL.apart₂ hxw (hws _ (by simp)) hne
  have ex₂ := eR K.R.x (by simp) rxy
  have ez₂ := eR K.R.z (by simp) (Ne.symm ryz)
  have tm : ∀ {x}, wordsVal s₂.mem base x K.M.n = wordsVal s₁.mem base x K.M.n →
      tmv C K.M.n base s₂ x = tmv C K.M.n base s₁ x := fun h => by
    show toM _ _ _ = toM _ _ _; rw [h]
  have hZ : (wordsVal s₁.mem base K.E.z K.M.n = 0) ↔ Z = 0 := by
    rw [← toM_eq_zero_iff hp (l₁ _ (by simp)), ← eE]
  have ey₂ : tmv C K.M.n base s₂ K.R.y = if Z = 0 then 1 else Y := by
    by_cases h : wordsVal s₁.mem base K.E.z K.M.n = 0
    · have e₂ : wordsVal s₂.mem base K.R.y K.M.n = K.one := by rw [v₂]; simp only [h, ↓reduceIte]
      show toM _ _ _ = _
      rw [e₂, hone]; simp only [hZ.mp h, ↓reduceIte]
    · have e₂ : wordsVal s₂.mem base K.R.y K.M.n = wordsVal s₁.mem base K.R.y K.M.n := by
        rw [v₂]; simp only [h, ↓reduceIte]
      rw [tm e₂, ey]
      exact (ite_eq_right_iff.mpr fun h' => absurd (hZ.mpr h') h).symm
  refine ⟨S₂, (k₂.gpr _ (by decide)).trans x₁, fun x hx => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex₂]; exact l₁ _ (by simp)
    · rw [v₂]; split
      · exact hone_lt
      · exact l₁ _ (by simp)
    · rw [ez₂]; exact l₁ _ (by simp)
  · rw [tm ex₂, ey₂, tm ez₂, ex, ez]
    exact InvJ.out hC hJ

/-- An iteration. -/
theorem winStepA_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixedA K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : WinInv K C base size k P s₀ s j) :
    WP isa (WinCfg.stepA K).inline s fun s' =>
      WinInv K C base size k P s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have hJ := hL.J
  rw [WinCfg.stepA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s hj (by omega) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  have hS₁ : WinSt K C base size P s₀ s₁ := hI.st.next hL (hI.st.scr.of_keeps k₁ (by decide))
    ((Keeps.regs k₁).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob]))
    (by rw [k₁.2.1]; exact Unch.refl _ _ _)
  have lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.2.1]; exact hI.lt
  have rep₁ : Rep C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J j) P) := by
    have e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.2.1]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quadA_ok hL hp hC hP hpn hone_lt hone hF hS₁ (by omega) b₁ lt₁ rep₁)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  have hx₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₅, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmvA hL hF
  have hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega) (by have := S₅.scr.nowrap; omega)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntry_ok hL hX hC (P := P) hpn hone_lt hone S₅.scr S₅.mod
    (i := j - 1) (by omega) hx₅ hbits₅ hz₅ S₅.tbl) fun s₆ h₆ => WP.seq (WP.mono h₆ fun s₇ E₇ => ?_))
  have hn := S₅.scr.nowrap
  have hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
      (K.M.tmp, 8 * K.M.n)], w ∈ loopW K := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
    · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
    · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
    · exact Or.inl ⟨_, winE_mem _ (by simp), rfl⟩
    · exact Or.inr rfl
  have S₇ := S₅.next hL E₇.scr (E₇.keep.mono clob_powClob) (E₇.unch.mono hEW)
  -- `R` is apart from what the entry writes.
  obtain ⟨-, -, -, hRo, -⟩ := hL.other_ne
  have eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n := by
    intro x hx
    have hxw : x ∈ winWs K := winOther_ws K x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> win_mem)
    refine E₇.unch.wordsVal (fun w hw => ?_) (by
      have := hL.lay.le x (winWs_slots K x hxw); omega)
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
  have lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  have rep₇ : Rep C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J j) P) := by
    have e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [eR x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact r₅
  refine WP.seq (WP.mono (sumStepA_ok hL hp hC hF S₇ (hC.onCurve_mul hP _)
    (onCurve_winPt hC hP k (j - 1)) lt₇ E₇.lt rep₇ E₇.rep) fun s₈ ⟨S₈, x₈, l₈, r₈⟩ => ?_)
  have hadd := win_add hC hP (k := k) (J := K.J) (j := j - 1) hk8 (by omega)
  rw [Nat.sub_add_cancel hj] at hadd
  rw [hadd] at r₈
  have hx₇ : s₇.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [E₇.keep.gpr _ (rbx_not_clob _), hx₅]
  have hx₈ : s₈.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₈, hx₇]
  refine WP.mono (testRbx_ok s₈ (by omega) hx₈) fun s₉ ⟨z₉, k₉⟩ => ⟨?_, z₉⟩
  have S₉ := S₈.next hL (S₈.scr.of_keeps k₉ (by decide)) ((Keeps.regs k₉).mono (by simp))
    (by rw [k₉.2.1]; exact Unch.refl _ _ _)
  refine ⟨S₉, by rw [k₉.1 _ (by simp), hx₈], by rw [k₉.2.1]; exact l₈, ?_⟩
  have e : ∀ x, tmv C K.M.n base s₉ x = tmv C K.M.n base s₈ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₉.2.1]
  rw [e, e, e]; exact r₈

/-- `[k - 8 Σ_{i<J} 16^i]P` into `R`, for `8 Σ_{i<J} 16^i ≤ k < 16^J` whose bits
are the table at `K.bits`; only `powClob` and `winW` change. -/
theorem windowA_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hF : WinFixedA K C base s P k) (hk : k < 16 ^ K.J)
    (hk8 : 8 * geom K.J ≤ k) :
    WP isa (WinCfg.windowA K).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (winW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (k - 8 * geom K.J) P) := by
  have hn := hs.nowrap
  have hJ := hL.J
  rw [WinCfg.windowA]
  simp only [Code.inline]
  refine WP.seq (WP.mono (buildA_ok hL hp hC hP hs hM hF) fun s₁ B => ?_)
  have S₁ : WinSt K C base size P s s₁ :=
    ⟨B.scr, B.keep, B.unch, B.mod, B.tbl⟩
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  have wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  have le : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (wR x hx))
  have ap := fun {x y} (hx : x ∈ [K.R.x, K.R.y, K.R.z]) (hy : y ∈ [K.R.x, K.R.y, K.R.z]) (h : x ≠ y) =>
    hL.apart₂ (winOther_ws K x (wR x hx)) (winOther_ws K y (wR y hy)) h
  have axy := ap (x := K.R.x) (y := K.R.y) (by simp) (by simp) rxy
  have axz := ap (x := K.R.x) (y := K.R.z) (by simp) (by simp) rxz
  have ayz := ap (x := K.R.y) (y := K.R.z) (by simp) (by simp) ryz
  have hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  refine WP.seq ?_
  rw [WinCfg.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  have W1 := setConst_ok S₁.scr (n := K.M.n) (o := K.R.x) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W1 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := S₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  have W2 := setConst_ok hs₂ (n := K.M.n) (o := K.R.y) (x := K.one) (le _ (by simp))
    (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  have W3 := setConst_ok hs₃ (n := K.M.n) (o := K.R.z) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W3 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (mov32Rbx_ok s₄ (j := K.J) (by omega)) fun s₅ ⟨b₅, k₅⟩ => ?_
  have hU : Unch base (loopW K) s₁.mem s₅.mem := by
    rw [k₅.2.1]
    refine (O₂.unch.trans (O₃.unch.trans O₄.unch)).mono fun w hw => ?_
    simp only [List.mem_append, List.mem_singleton] at hw
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton]
    refine Or.inl ⟨w.1, ?_, ?_⟩
    · rcases hw with rfl | rfl | rfl
      · exact wR _ (by simp)
      · exact wR _ (by simp)
      · exact wR _ (by simp)
    · rcases hw with rfl | rfl | rfl <;> rfl
  have c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
  have S₅ : WinSt K C base size P s s₅ := S₁.next hL (hs₄.of_keeps k₅ (by decide))
    ((((k₂.mono c1).trans (k₃.mono c1)).trans (k₄.mono c1)).trans
      ((Keeps.regs k₅).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
                                simp [powClob]))) hU
  have b64 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega
  have vx : wordsVal s₅.mem base K.R.x K.M.n = 0 := by
    rw [k₅.2.1, O₄.wordsVal axz (b64 _ (by simp)), O₃.wordsVal axy (b64 _ (by simp)), e₂]
  have vy : wordsVal s₅.mem base K.R.y K.M.n = K.one := by
    rw [k₅.2.1, O₄.wordsVal ayz (b64 _ (by simp)), e₃]
  have vz : wordsVal s₅.mem base K.R.z K.M.n = 0 := by rw [k₅.2.1, e₄]
  have I₅ : WinInv K C base size k P s s₅ K.J := by
    refine ⟨S₅, b₅, fun x hx => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · rw [vx]; exact hp0
      · rw [vy]; exact hone_lt
      · rw [vz]; exact hp0
    · show Rep C (toM _ _ _) (toM _ _ _) (toM _ _ _) _
      rw [vx, vy, vz, toM_zero, hone, winE_top hk, mul_zero_pt']
      exact rep_infinity' hC
  exact countLoop_ok (Inv := fun j s' => WinInv K C base size k P s s' j) (n := K.J)
    (fun j s' h1 h2 hi => winStepA_ok hL hX hp hC hP hpn hone_lt hone hF hk8 h1 h2 hi)
    (fun s' hi => ⟨hi.st.keep, hi.st.unch, hi.st.mod, hi.lt, by rw [← winE_zero]; exact hi.rep⟩)
    hJ.1 I₅


end VG.Proof.Weierstrass.X86_64
