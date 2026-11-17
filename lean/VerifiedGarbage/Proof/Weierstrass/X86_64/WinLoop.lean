module

import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinEntry
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Flags
public import VerifiedGarbage.Proof.Weierstrass.JacMul
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.X25519.X86_64.Adx.MulProd
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Weierstrass.X86_64.WinQuad`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86_64.QuadCounter`, which this module and modules that import it used -/

section

/-!
# A public counter for pairs of window doublings

The low 12 bits of `rbx` retain the window index; the next bits count the
two pairs. Subtracting 4096 consumes one pair. Comparing with 4096 sets
carry exactly when the inner count reaches zero, leaving the index intact.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

/-- Add the two-pair count to the window index. -/
theorem quadStart_ok (s : State) {i : Nat} (hb : s.gpr .rbx = BitVec.ofNat 64 i) :
    WP isa (.block [.alu .add .rbx (.imm 8192)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 4096 * 2) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left', hb]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e : (8192 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8192 := by decide
    rw [e, ← BitVec.ofNat_add]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- Consume one pair, setting carry when only the window index remains. -/
theorem quadCount_ok (s : State) {i j : Nat} (hi : i < 4096) (hj : 1 ≤ j) (hj' : j ≤ 2)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (i + 4096 * j)) :
    WP isa (.block [.alu .sub .rbx (.imm 4096), .alu .cmp .rbx (.imm 4096)]) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 (i + 4096 * (j - 1)) ∧
      s'.cf = some (decide (j - 1 = 0)) ∧ Keeps [.rbx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left', hb]
  have e : (4096 : BitVec 32).signExtend 64 = BitVec.ofNat 64 4096 := by decide
  have sub : BitVec.ofNat 64 (i + 4096 * j) - (4096 : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (i + 4096 * (j - 1)) := by
    rw [e]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_using [hj]
  refine ⟨sub, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [sub]
    rw [e]
    congr 1
    simp only [BitVec.toNat_ofNat]
    apply propext
    omega_using [hi, hj']
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- Run two pairs, branching while the public inner count remains nonzero. -/
theorem quadLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop}
    (hstep : ∀ j s, 1 ≤ j → j ≤ 2 → Inv j s →
      WP isa body s fun s' => Inv (j - 1) s' ∧ s'.cf = some (decide (j - 1 = 0)))
    (hQ : ∀ s, Inv 0 s → Q s) {s : State} (hs : Inv 2 s) :
    WP isa (.loop body .ae) s Q := by
  refine WP.loop (M := isa) (fun j s => 1 ≤ j ∧ j ≤ 2 ∧ Inv j s) (fun j s ⟨h1, h2, hi⟩ => ?_) 2 s
    ⟨by decide, by decide, hs⟩
  refine WP.mono (hstep j s h1 h2 hi) fun s' ⟨hi', hc⟩ => ?_
  by_cases hj : j - 1 = 0
  · refine Or.inl ⟨?_, hQ s' (by rw [hj] at hi'; exact hi')⟩
    show s'.cf.map (!·) = some false
    rw [hc, hj]; rfl
  · refine Or.inr ⟨?_, j - 1, by omega_using [h1], by omega_using [hj], by omega_using [h2], hi'⟩
    show s'.cf.map (!·) = some true
    rw [hc]; simp [hj]

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# The window method on x86-64: the loop's frame and 

As on AArch64: what holds through the loop (`WinSt`, the table surviving what
the loop writes), the addition of the entry (`sumStep_ok`), and `R = 16 R`
(`quad_ok`): four doublings in Jacobian coordinates (`jac_ok`), and
`Y = 1` where the result is `O` (`ySel_ok`: the mask of `E.z = 0`,
`winZeroMask_ok`, selecting Montgomery's one word by word, `ySelWord_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-! ## The doubling's operations, numbered (`dblJX`, as `dblJSN`) -/

def dblJXN : List FOp := WinCfg.dblJX ⟨9, 10, 0, 1, 2, 3, 4, 5⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩

def dblJXChoiceN (direct : Bool) : List FOp := if direct then dblJMulN else dblJXN

theorem dblJXChoiceN_ok (direct : Bool) : NumOk (dblJXChoiceN direct) := by
  cases direct <;> exact ⟨by decide, by decide, by decide⟩

theorem dblJXChoice_eq (direct : Bool) (S : RcbSlots) (p o : Pt) :
    (if direct then dblJMul S p o else WinCfg.dblJX S p o) = ofN (dblJXChoiceN direct) S p p o := by
  cases direct <;> rfl

theorem dblJXN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    (runOps dblJXN e 6, runOps dblJXN e 7, runOps dblJXN e 8) =
      dblJF (e 11) (e 12) (e 13) := by
  dsimp only [dblJXN, WinCfg.dblJX, runOps, List.foldl, FOp.run, Function.update]
  simp only [dblJF, Prod.mk.injEq]
  constructor
  · grind
  constructor <;> grind

theorem dblJXChoiceN_run {F : Type _} [Lean.Grind.CommRing F] (direct : Bool) (e : Nat → F) :
    (runOps (dblJXChoiceN direct) e 6, runOps (dblJXChoiceN direct) e 7,
      runOps (dblJXChoiceN direct) e 8) = dblJF (e 11) (e 12) (e 13) := by
  cases direct
  · exact dblJXN_run e
  · exact dblJMulN_run e

/-! ## The loop -/

/-- What the loop writes: the slots but the table's, and the temporary area. -/
def loopW (K : WinCfg) : List (Nat × Nat) := (winOther K).map (·, 8 * K.M.n) ++ [(K.M.tmp, 8 * K.M.n)]

theorem loopW_sub (K : WinCfg) : ∀ w ∈ loopW K, w ∈ winW K := by
  intro w hw
  simp only [loopW, winW, winWs, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact Or.inl ⟨y, Or.inl hy, rfl⟩
  · exact Or.inr rfl

/-- The table survives what the loop writes. -/
theorem TblOkR.unch {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s s' : State} (hT : TblOkR K C base Rp P 8 s) (hU : Unch base (loopW K) s.mem s'.mem)
    (hn : base.toNat + size ≤ 2 ^ 64) : TblOkR K C base Rp P 8 s' := by
  intro j h1 h8
  have T := hT j h1 h8
  have e : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      wordsVal s'.mem base x K.M.n = wordsVal s.mem base x K.M.n := by
    intro x hx
    obtain ⟨i, hi, rfl, -, -⟩ := tblPt_mem K h1 h8 x hx
    have hs : K.tbl + 8 * K.M.n * i ∈ winSlots K := by
      simp only [winSlots, List.mem_append]; exact Or.inr (winTbl_mem K hi)
    refine hU.wordsVal (fun w hw => ?_) (by have := hL.lay.le _ hs; omega_arith)
    simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · exact (hL.tbl_apart (List.mem_append_right _ hy) hi).symm
    · exact hL.lay.tmp _ hs
  refine ⟨fun x hx => by rw [e x hx]; exact T.1 x hx, ?_⟩
  have ex : ∀ x ∈ [(K.tblPt j).x, (K.tblPt j).y, (K.tblPt j).z],
      tmv C K.M.n base s' x = tmv C K.M.n base s x := fun x hx => by
    show toM _ _ _ = toM _ _ _; rw [e x hx]
  rw [ex _ (by simp), ex _ (by simp), ex _ (by simp)]
  exact T.2

/-- What holds throughout the loop, from `s₀` (the state before the table). -/
structure WinStR (K : WinCfg) (C : Curve) (base : Addr) (size : Nat)
    (Rp : Fe C → Fe C → Fe C → Point C → Prop) (P : Point C) (s₀ s : State) : Prop where
  scr : Scr s base size
  keep : KeepRegs (powClob K.M.n) s₀ s
  unch : Unch base (winW K) s₀.mem s.mem
  mod : ModOkW K.M size C.p s.mem base
  tbl : TblOkR K C base Rp P 8 s

/-- `WinStR` with the table in projective coordinates. -/
abbrev WinSt (K : WinCfg) (C : Curve) (base : Addr) (size : Nat) (P : Point C) (s₀ s : State) : Prop :=
  WinStR K C base size (Rep C) P s₀ s

/-- The state after a change of `loopW` only. -/
theorem WinStR.next {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s₀ s s' : State} (h : WinStR K C base size Rp P s₀ s) (hs' : Scr s' base size)
    (hk : KeepRegs (powClob K.M.n) s s') (hU : Unch base (loopW K) s.mem s'.mem) :
    WinStR K C base size Rp P s₀ s' :=
  ⟨hs', h.keep.trans hk, (h.unch.trans hU).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact loopW_sub K w hw,
    h.mod.unch hU (fun w hw => winW_mo hL h.mod w (loopW_sub K w hw)) h.scr.nowrap,
    TblOkR.unch hL h.tbl hU h.scr.nowrap⟩

theorem WinStR.ro_tmv {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s₀ s : State} (h : WinStR K C base size Rp P s₀ s) (hF : WinFixed K C base s₀ P k) :
    tmv C K.M.n base s K.S.a = Fin.ofNat C.p C.a ∧ tmv C K.M.n base s K.S.b3 = Fin.ofNat C.p C.b ∧
      (∀ x ∈ winRo K, wordsVal s.mem base x K.M.n < C.p) ∧ wordsVal s.mem base K.zero K.M.n = 0 := by
  have hn := h.scr.nowrap
  refine ⟨?_, ?_, fun x hx => ?_, ?_⟩
  · rw [winRo_tmv hL h.unch hn (by simp [winRo])]; exact hF.a
  · rw [winRo_tmv hL h.unch hn (by simp [winRo])]; exact hF.b
  · rw [winRo_val hL h.unch hn hx]; exact hF.ro_lt x hx
  · rw [winRo_val hL h.unch hn (by simp [winRo])]; exact hF.zero

/-- `R = R + E`, for `R` representing `PR` and `E` `PQ`. -/
theorem sumStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {s₀ s : State} (hF : WinFixed K C base s₀ P k) (hS : WinStR K C base size Rp P s₀ s)
    {PR PQ : Point C} (hPR : onCurve C PR = true) (hPQ : onCurve C PQ = true)
    (hltR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hltq : ∀ x ∈ [K.E.x, K.E.y, K.E.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z) PR)
    (hQ : Rep C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) PQ) :
    WP isa (Code.seq (fprogB K.M (rcb3 K.S K.R K.E K.D)) (.block (copyPt K.M.n K.R K.D))).inline s fun s' =>
      WinStR K C base size Rp P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (Spec.Weierstrass.add PR PQ) := by
  obtain ⟨-, tb, ro_lt, -⟩ := hS.ro_tmv hL hF
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
  refine WP.mono (winAdd_ok hL hp hS.scr hS.mod hlt) fun s' S => ?_
  have hV := S.val
  rw [tb] at hV
  exact ⟨hS.next hL S.scr (S.keep.mono clob_powClob) S.unch, S.keep.gpr _ (rbx_not_clob _), S.lt,
    hC.add3 hM3 hPR hPQ hR hQ hV.symm⟩

/-- The loop's invariant at `rbx = j`: `R` represents `[winE k J j]P`. -/
structure WinInv (K : WinCfg) (C : Curve) (base : Addr) (size k : Nat) (P : Point C) (s₀ s : State)
    (j : Nat) : Prop where
  st : WinSt K C base size P s₀ s
  rbx : s.gpr .rbx = BitVec.ofNat 64 j
  lt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p
  rep : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
    (mul (winE k K.J j) P)

/-! ## Four doublings in Jacobian coordinates -/

/-- A field program on numbered slots, writing slots of `winOther`: the loop's frame. -/
theorem winN_ok {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) {N : List FOp} (hN : NumOk N) {p q o : Pt}
    (hAp : RcbApart K.S p q o) (hSl : ∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winSlots K)
    (hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K) {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ winSlots K) V E s) (hV : ∀ x ∈ rcbR K.S p q, x ∈ V) :
    WP isa (fprogB K.M (ofN N K.S p q o)).inline s fun s' => KeepRegs (clob K.M.n) s s' ∧
      Unch base (loopW K) s.mem s'.mem ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p (· ∈ winSlots K) ([o.x, o.y, o.z] ++ V) E' s' ∧
      (∀ x, x ∉ rcbW K.S o → E' x = E x) ∧
      (E' o.x, E' o.y, E' o.z) = (runOps N (fun y => E (rcbσ K.S p q o y)) 6,
        runOps N (fun y => E (rcbσ K.S p q o y)) 7, runOps N (fun y => E (rcbσ K.S p q o y)) 8) := by
  refine (WP.mono (ofN_ok hL.lay hp hN hAp hSl hI hV)
    fun s' ⟨k, I, v⟩ => ⟨⟨k.gpr, k.rd, k.wr⟩, k.unch.mono fun w hw => ?_, _, I,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out hN op hop), v⟩)
  simp only [loopW, List.mem_append, List.mem_map, List.mem_singleton] at hw ⊢
  rcases hw with ⟨y, hy, rfl⟩ | rfl
  · exact Or.inl ⟨y, hW y hy, rfl⟩
  · exact Or.inr rfl

/-- The slots of a numbered program from `p` and `q` into `o`, a point written. -/
theorem winJ_sl {K : WinCfg} {o p q : Pt} (ho : ∀ x ∈ [o.x, o.y, o.z], x ∈ winOther K)
    (hp : ∀ x ∈ [p.x, p.y, p.z], x ∈ winSlots K) (hq : ∀ x ∈ [q.x, q.y, q.z], x ∈ winSlots K) :
    (∀ x ∈ rcbW K.S o ++ rcbR K.S p q, x ∈ winSlots K) ∧ ∀ x ∈ rcbW K.S o, x ∈ winOther K := by
  have hW : ∀ x ∈ rcbW K.S o, x ∈ winOther K := by
    intro x hx
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h <;> subst h
    · win_mem
    · win_mem
    · win_mem
    · win_mem
    · win_mem
    · win_mem
    · exact ho _ (by simp)
    · exact ho _ (by simp)
    · exact ho _ (by simp)
  refine ⟨fun x hx => ?_, hW⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact winOther_mem (hW x hx)
  · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h <;> subst h
    · win_mem
    · win_mem
    · exact hp _ (by simp)
    · exact hp _ (by simp)
    · exact hp _ (by simp)
    · exact hq _ (by simp)
    · exact hq _ (by simp)
    · exact hq _ (by simp)

/-- What a program reads is in `V`. -/
local macro "rcb_sub" : tactic => `(tactic| plain_simp_names (
                   intro x hx
                   simp only [rcbR, WinCfg.zeroPt, List.cons_append, List.nil_append, List.mem_cons,
                     List.not_mem_nil, or_false] at hx ⊢
                   rcases hx with h | h | h | h | h | h | h | h <;> simp only [h, true_or, or_true]))

/-- Changing only the public loop counter preserves the field environment. -/
theorem Inv.rbxKeeps {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop}
    {V : List Nat} {E : Nat → Fin m} {s s' : State} (h : Inv M base size m Sl V E s)
    (hk : Keeps [.rbx] s s') : Inv M base size m Sl V E s' :=
  ⟨h.scr.of_keeps hk (by decide), by rw [hk.2.1]; exact h.mod, h.sl,
    by rw [hk.2.1]; exact h.lt, by rw [hk.2.1]; exact h.val⟩

/-- The public counter is among the registers the window loop may change. -/
theorem WinStR.rbxKeeps {K : WinCfg} {C : Curve} {base : Addr} {size : Nat} (hL : WinLay K size)
    {Rp : Fe C → Fe C → Fe C → Point C → Prop}
    {P : Point C} {s₀ s s' : State} (h : WinStR K C base size Rp P s₀ s)
    (hk : Keeps [.rbx] s s') : WinStR K C base size Rp P s₀ s' :=
  h.next hL (h.scr.of_keeps hk (by decide)) ((Keeps.regs hk).mono (by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob]))
    (by rw [hk.2.1]; exact Unch.refl _ _ _)

/-- `R = 16 R` in Jacobian coordinates, but `Y`: the triple `(X : Y : Z)` stands for
`[16 e]P` (or `Z = 0`), `R` is `(XZ : Y : Z³)` and `E.z` is `Z`. -/
theorem jac_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinSt K C base size P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.jac K).inline s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z, K.E.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      ∃ X Y Z : Fe C, InvJ C X Y Z (mul (16 * e) P) ∧ tmv C K.M.n base s' K.R.x = X * Z ∧
        tmv C K.M.n base s' K.R.y = Y ∧ tmv C K.M.n base s' K.R.z = Z * Z * Z ∧
        tmv C K.M.n base s' K.E.z = Z := by
  obtain ⟨-, -, ro_lt, hz⟩ := hS.ro_tmv hL hF
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
  simp only [WinCfg.jac, toJ_eq, fromJ_eq]
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
      WP isa (WinCfg.jacPair K).inline st fun st' => LI (j - 1) st' ∧ st'.cf = some (decide (j - 1 = 0)) := by
    intro j st hj hj' ⟨S, b, E, I, J⟩
    simp only [WinCfg.jacPair, WinCfg.double, dblJXChoice_eq]
    refine WP.seq (WP.mono (winN_ok hL hp (dblJXChoiceN_ok (K.M.n ≤ 6 : Bool)) a2 w2.1 w2.2 I (by
      dsimp [V]; rcb_sub)) fun st₁ ⟨k₁', U₁', E₁', I₁', _, v₁'⟩ => ?_)
    have S₁' := S.next hL I₁'.scr (k₁'.mono clob_powClob) U₁'
    have J₁' := InvJ.dbl' hC hM3 (hQ _) J (v₁'.trans (dblJXChoiceN_run (K.M.n ≤ 6 : Bool) _))
    rw [hC.double hP] at J₁'
    refine WP.seq (WP.mono (winN_ok hL hp (dblJXChoiceN_ok (K.M.n ≤ 6 : Bool)) a3 w3.1 w3.2 I₁' (by
      dsimp [V]; rcb_sub)) fun st₂ ⟨k₂', U₂', E₂', I₂', _, v₂'⟩ => ?_)
    have S₂' := S₁'.next hL I₂'.scr (k₂'.mono clob_powClob) U₂'
    have J₂' := InvJ.dbl' hC hM3 (hQ _) J₁' (v₂'.trans (dblJXChoiceN_run (K.M.n ≤ 6 : Bool) _))
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
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
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

/-! ## `Y = 1` where `Z = 0` -/

/-- `rdx = -CF`. -/
theorem zmSbb_ok (s : State) {b : Bool} (hb : s.cf = some b) :
    WP isa (.block [.alu .sbb .rdx (.reg .rdx)]) s fun s' =>
      s'.gpr .rdx = (if b then BitVec.allOnes 64 else 0) ∧ Keeps [.rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.map_some, hb, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨by cases b <;> simp, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `cmp rdx, 1` sets `CF` iff `rdx = 0`. -/
theorem zmCmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 1)]) s fun s' =>
      s'.cf = some (decide (s.gpr .rdx = 0)) ∧ Keeps [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r _ => by simp only [RegUpd.gpr_arithFlags], rfl, rfl, rfl⟩
  have : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
  rw [this]
  congr 1
  simp only [Nat.lt_one_iff]
  exact propext ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩

/-- The mask `rdx` of `[E.z] = 0`. -/
theorem winZeroMask_ok (K : WinCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 0 < K.M.n) (ha : K.E.z + 8 * K.M.n ≤ size) :
    WP isa (.block (WinCfg.zeroMask K)) s fun s' =>
      s'.gpr .rdx = mask (wordsVal s.mem base K.E.z K.M.n = 0) ∧ Keeps [.rdx] s s' := by
  rw [WinCfg.zeroMask, List.append_assoc, WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov .rdx (.mem (sc K.E.z))]) s (fun s₁ =>
      s₁.gpr .rdx = word s.mem base K.E.z ∧ Keeps [.rdx] s s₁) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs (d := K.E.z) (by omega_arith),
      Option.map_some, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ors_ok hs₁ (a := K.E.z) (K.M.n - 1) (by omega_arith)) fun s₂ ⟨e₂, k₂⟩ => ?_
  rw [e₁, k₁.2.1] at e₂
  have hz : s₂.gpr .rdx = 0 ↔ wordsVal s.mem base K.E.z K.M.n = 0 := by
    rw [e₂, wordsVal_eq_zero_iff]
    constructor
    · intro ⟨h₀, h⟩ j hj
      rcases j with _ | j
      · simpa using h₀
      · exact h j (by omega_arith)
    · intro h
      exact ⟨by simpa using h 0 hn, fun j hj => h (j + 1) (by omega_arith)⟩
  rw [show ([.alu .cmp .rdx (.imm 1), .alu .sbb .rdx (.reg .rdx)] : List Instr) =
    [.alu .cmp .rdx (.imm 1)] ++ [.alu .sbb .rdx (.reg .rdx)] from rfl, WP.block_append_iff]
  refine WP.mono (zmCmp_ok s₂) fun s₃ ⟨c₃, k₃⟩ => ?_
  refine WP.mono (zmSbb_ok s₃ c₃) fun s₄ ⟨e₄, k₄⟩ =>
    ⟨?_, ((k₁.trans k₂).trans (k₃.mono (fun _ h => absurd h List.not_mem_nil))).trans k₄⟩
  rw [e₄]
  simp only [mask, decide_eq_true_eq, hz]

theorem sel_mask (a b : BitVec 64) (p : Prop) [Decidable p] :
    a ^^^ ((b ^^^ a) &&& mask p) = if p then b else a := by
  by_cases h : p
  · simp only [mask, h, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [mask, h]

/-- Word `w` of `R.y`: Montgomery's one where `rdx` is the mask of `p`. -/
theorem ySelWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    (p : Prop) [Decidable p] (hdx : s.gpr .rdx = mask p) {w : Nat} (ho : K.R.y + 8 * w + 8 ≤ size) :
    WP isa (.block (WinCfg.ySelWord K w)) s fun t =>
      t.mem = s.mem.writeW (off base (K.R.y + 8 * w))
        (if p then wordOf K.one w else word s.mem base (K.R.y + 8 * w)) ∧
      KeepRegs [.rax, .r8] s t := by
  have hn := hs.nowrap
  apply WP.of_runBlock
  simp only [WinCfg.ySelWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, ea_sc, hdx, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.mem_arithFlags, reduceCtorEq, ite_true, ite_false, hs.rdi,
    ld_sc hs (d := K.R.y + 8 * w) (by omega_arith), st_sc hs (d := K.R.y + 8 * w) (by omega_arith),
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [sel_mask], ⟨fun r hr => ?_, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

/-- The first `k` words of `R.y`. -/
theorem ySelWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (K : WinCfg)
    (p : Prop) [Decidable p] (hdx : s.gpr .rdx = mask p) :
    ∀ k, K.R.y + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (WinCfg.ySelWord K))) s fun t =>
      (∀ w < k, word t.mem base (K.R.y + 8 * w) =
        if p then wordOf K.one w else word s.mem base (K.R.y + 8 * w)) ∧
      KeepRegs [.rax, .r8] s t ∧ Outside base K.R.y (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ySelWords_ok hs K p hdx k (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (ySelWord_ok hs₁ K p ((k₁.gpr _ (by decide)).trans hdx) (w := k) (by omega_arith))
      fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (K.R.y + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega_arith) (by omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₂, word_writeW_self, O₁.word (by omega_arith) (by omega_arith)]

/-- `R.y` = Montgomery's one where `E.z` is zero. -/
theorem ySel_ok {K : WinCfg} {base : Addr} {size : Nat} (hL : WinLay K size)
    {s : State} (hs : Scr s base size) (h1 : K.one < 2 ^ (64 * K.M.n)) :
    WP isa (.block (WinCfg.ySel K)) s fun t =>
      wordsVal t.mem base K.R.y K.M.n = (if wordsVal s.mem base K.E.z K.M.n = 0 then K.one
        else wordsVal s.mem base K.R.y K.M.n) ∧
      KeepRegs [.rax, .rdx, .r8] s t ∧
      Unch base [(K.R.y, 8 * K.M.n)] s.mem t.mem := by
  have hn := hs.nowrap
  have hy : K.R.y ∈ winSlots K := by win_mem
  have hz : K.E.z ∈ winSlots K := by win_mem
  rw [WinCfg.ySel, WP.block_append_iff]
  refine WP.mono (winZeroMask_ok K hs hL.n0 (hL.lay.le _ hz)) fun s₁ ⟨m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (ySelWords_ok hs₁ K _ m₁ K.M.n (hL.lay.le _ hy))
    fun t ⟨e, kt, O⟩ => ⟨?_, ?_, ?_⟩
  · by_cases hz0 : wordsVal s.mem base K.E.z K.M.n = 0
    · simp only [hz0, ↓reduceIte]
      exact wordsVal_of_shifts _ _ _ _ _ h1 fun j hj => by simp only [e j hj, hz0, ↓reduceIte]; rfl
    · simp only [hz0, ↓reduceIte]
      rw [← k₁.2.1]
      exact wordsVal_congr₂ _ _ _ fun j hj => by simp only [e j hj, hz0, ↓reduceIte]
  · exact ((Keeps.regs k₁).mono (by decide)).trans (kt.mono (by decide))
  · rw [← k₁.2.1]; exact O.unch.mono (by simp)

/-- `R = 16 R`: `[e]P` to `[16 e]P`. -/
theorem quad_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ s : State} (hF : WinFixed K C base s₀ P k)
    (hS : WinSt K C base size P s₀ s) {i : Nat} (hi : i < 4096)
    (hb : s.gpr .rbx = BitVec.ofNat 64 i) {e : Nat}
    (hlt : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s.mem base x K.M.n < C.p)
    (hR : Rep C (tmv C K.M.n base s K.R.x) (tmv C K.M.n base s K.R.y) (tmv C K.M.n base s K.R.z)
      (mul e P)) :
    WP isa (WinCfg.quad K).inline s fun s' =>
      WinSt K C base size P s₀ s' ∧ s'.gpr .rbx = s.gpr .rbx ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (16 * e) P) := by
  rw [WinCfg.quad]
  refine WP.seq (WP.mono (jac_ok hL hp hC hM3 hP hF hS hi hb hlt hR)
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

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# The window method on x86-64

As on AArch64 (`Proof/Weierstrass/AArch64/Window.lean`): the table `[1 … 8]P`
(`build_ok`), then, from `R = O`, iterations (`winStep_ok`) that multiply `R`
by 16 (`quad_ok`) and add the entry of the digit (`winEntry_ok`), so that `R`,
which represented `[winE k J (j+1)]P`, represents `[winE k J j]P` (`win_add`).
After all `J` digits `R` represents `[k - 8 Σ_{i<J} 16^i]P` (`window_ok`), for
`k < 16^J` whose bits are the table at `K.bits`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open Spec.Weierstrass

/-- An iteration. -/
theorem winStep_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s₀ : State} (hF : WinFixed K C base s₀ P k)
    (hk8 : 8 * geom K.J ≤ k) {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ K.J)
    (hI : WinInv K C base size k P s₀ s j) :
    WP isa (WinCfg.step K).inline s fun s' =>
      WinInv K C base size k P s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have hJ := hL.J
  rw [WinCfg.step]
  simp only [Code.inline]
  refine WP.seq (WP.mono (decRbx_ok s hj (by omega_using [hjn, hJ]) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_)
  obtain hS₁ : WinSt K C base size P s₀ s₁ := hI.st.next hL (hI.st.scr.of_keeps k₁ (by decide))
    ((Keeps.regs k₁).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob]))
    (by rw [k₁.2.1]; exact Unch.refl _ _ _)
  obtain lt₁ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₁.mem base x K.M.n < C.p := by
    rw [k₁.2.1]; exact hI.lt
  obtain rep₁ : Rep C (tmv C K.M.n base s₁ K.R.x) (tmv C K.M.n base s₁ K.R.y)
      (tmv C K.M.n base s₁ K.R.z) (mul (winE k K.J j) P) := by
    obtain e : ∀ x, tmv C K.M.n base s₁ x = tmv C K.M.n base s x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [k₁.2.1]
    rw [e, e, e]; exact hI.rep
  refine WP.seq (WP.mono (quad_ok hL hp hC hM3 hP hpn hone_lt hone hF hS₁ (by omega_using [hjn, hJ]) b₁ lt₁ rep₁)
    fun s₅ ⟨S₅, x₅, l₅, r₅⟩ => ?_)
  obtain hx₅ : s₅.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₅, b₁]
  obtain ⟨-, -, -, hz₅⟩ := S₅.ro_tmv hL hF
  obtain hbits₅ : ∀ t < 4 * K.J, s₅.mem (off base (K.bits + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      have := hL.bits
      rw [S₅.unch.byte (fun w hw => by have := hL.bits_w w hw; omega_using [ht, this]) (by have := S₅.scr.nowrap; omega_arith)]
      exact hF.bits t ht
  refine WP.seq (WP.mono (winEntry_ok hL hX hC (P := P) hpn hone_lt hone S₅.scr S₅.mod
    (i := j - 1) (by omega_using [hj, hjn]) hx₅ hbits₅ hz₅ S₅.tbl) fun s₆ h₆ => WP.seq (WP.mono h₆ fun s₇ E₇ => ?_))
  have hn := S₅.scr.nowrap
  obtain hEW : ∀ w ∈ [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n), (K.neg, 8 * K.M.n),
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
  obtain S₇ := S₅.next hL E₇.scr (E₇.keep.mono clob_powClob) (E₇.unch.mono hEW)
  -- `R` is apart from what the entry writes.
  obtain ⟨-, -, -, hRo, -⟩ := hL.other_ne
  obtain eR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n = wordsVal s₅.mem base x K.M.n := by
    intro x hx
    obtain hxw : x ∈ winWs K := winOther_ws K x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> win_mem)
    refine E₇.unch.wordsVal (fun w hw => ?_) (by
      have := hL.lay.le x (winWs_slots K x hxw); omega_using [hn, this])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain hne : ∀ y ∈ [K.E.x, K.E.y, K.E.z, K.neg], x ≠ y := fun y hy e => hRo x hx (by
      rw [e]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> simp)
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
    · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
    · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
    · exact hL.apart₂ hxw (winOther_ws K _ (winE_mem _ (by simp))) (hne _ (by simp))
    · exact hL.lay.tmp x (winWs_slots K x hxw)
  obtain lt₇ : ∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s₇.mem base x K.M.n < C.p := fun x hx => by
    rw [eR x hx]; exact l₅ x hx
  obtain rep₇ : Rep C (tmv C K.M.n base s₇ K.R.x) (tmv C K.M.n base s₇ K.R.y)
      (tmv C K.M.n base s₇ K.R.z) (mul (16 * winE k K.J j) P) := by
    obtain e : ∀ x ∈ [K.R.x, K.R.y, K.R.z], tmv C K.M.n base s₇ x = tmv C K.M.n base s₅ x := fun x hx => by
      show toM _ _ _ = toM _ _ _; rw [eR x hx]
    rw [e _ (by simp), e _ (by simp), e _ (by simp)]; exact r₅
  refine WP.seq (WP.mono (sumStep_ok hL hp hC hM3 hF S₇ (hC.onCurve_mul hP _)
    (onCurve_winPt hC hP k (j - 1)) lt₇ E₇.lt rep₇ E₇.rep) fun s₈ ⟨S₈, x₈, l₈, r₈⟩ => ?_)
  obtain hadd := win_add hC hP (k := k) (J := K.J) (j := j - 1) hk8 (by omega_using [hj, hjn])
  rw [Nat.sub_add_cancel hj] at hadd
  rw [hadd] at r₈
  obtain hx₇ : s₇.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [E₇.keep.gpr _ (rbx_not_clob _), hx₅]
  obtain hx₈ : s₈.gpr .rbx = BitVec.ofNat 64 (j - 1) := by rw [x₈, hx₇]
  refine WP.mono (testRbx_ok s₈ (by omega_using [hjn, hJ]) hx₈) fun s₉ ⟨z₉, k₉⟩ => ⟨?_, z₉⟩
  obtain S₉ := S₈.next hL (S₈.scr.of_keeps k₉ (by decide)) ((Keeps.regs k₉).mono (by simp))
    (by rw [k₉.2.1]; exact Unch.refl _ _ _)
  refine ⟨S₉, by rw [k₉.1 _ (by simp), hx₈], by rw [k₉.2.1]; exact l₈, ?_⟩
  obtain e : ∀ x, tmv C K.M.n base s₉ x = tmv C K.M.n base s₈ x := fun x => by
    show toM _ _ _ = toM _ _ _; rw [k₉.2.1]
  rw [e, e, e]; exact r₈

/-- `[k - 8 Σ_{i<J} 16^i]P` into `R`, for `8 Σ_{i<J} 16^i ≤ k < 16^J` whose bits
are the table at `K.bits`; only `powClob` and `winW` change. -/
theorem window_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat} (hL : WinLay K size)
    (hX : WinX K size) (hp : UnitMod C.p (2 ^ (64 * K.M.n))) (hC : Law C) (hM3 : AM3 C) {P : Point C}
    (hP : onCurve C P = true) (hpn : C.p < 2 ^ (64 * K.M.n)) (hone_lt : K.one < C.p)
    (hone : toM C.p (2 ^ (64 * K.M.n)) K.one = 1) {s : State} (hs : Scr s base size)
    (hM : ModOkW K.M size C.p s.mem base) (hF : WinFixed K C base s P k) (hk : k < 16 ^ K.J)
    (hk8 : 8 * geom K.J ≤ k) :
    WP isa (WinCfg.window K).inline s fun s' => KeepRegs (powClob K.M.n) s s' ∧
      Unch base (winW K) s.mem s'.mem ∧ ModOkW K.M size C.p s'.mem base ∧
      (∀ x ∈ [K.R.x, K.R.y, K.R.z], wordsVal s'.mem base x K.M.n < C.p) ∧
      Rep C (tmv C K.M.n base s' K.R.x) (tmv C K.M.n base s' K.R.y) (tmv C K.M.n base s' K.R.z)
        (mul (k - 8 * geom K.J) P) := by
  have hn := hs.nowrap
  have hJ := hL.J
  rw [WinCfg.window]
  simp only [Code.inline]
  refine WP.seq (WP.mono (build_ok hL hp hC hM3 hP hs hM hF) fun s₁ B => ?_)
  obtain S₁ : WinSt K C base size P s s₁ :=
    ⟨B.scr, B.keep, B.unch, B.mod, B.tbl⟩
  obtain ⟨rxy, rxz, ryz, -⟩ := hL.other_ne
  obtain wR : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x ∈ winOther K := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> win_mem
  obtain le : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ size := fun x hx =>
    hL.lay.le x (winOther_mem (wR x hx))
  obtain ap := fun {x y} (hx : x ∈ [K.R.x, K.R.y, K.R.z]) (hy : y ∈ [K.R.x, K.R.y, K.R.z]) (h : x ≠ y) =>
    hL.apart₂ (winOther_ws K x (wR x hx)) (winOther_ws K y (wR y hy)) h
  obtain axy := ap (x := K.R.x) (y := K.R.y) (by simp) (by simp) rxy
  obtain axz := ap (x := K.R.x) (y := K.R.z) (by simp) (by simp) rxz
  obtain ayz := ap (x := K.R.y) (y := K.R.z) (by simp) (by simp) ryz
  obtain hp0 : 0 < C.p := Nat.lt_of_le_of_lt (Nat.zero_le _) hone_lt
  refine WP.seq ?_
  rw [WinCfg.init, List.append_assoc, List.append_assoc, WP.block_append_iff]
  obtain W1 := setConst_ok S₁.scr (n := K.M.n) (o := K.R.x) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W1 fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := S₁.scr.of_keepRegs k₂ (by decide)
  rw [WP.block_append_iff]
  obtain W2 := setConst_ok hs₂ (n := K.M.n) (o := K.R.y) (x := K.one) (le _ (by simp))
    (Nat.lt_trans hone_lt hpn)
  refine WP.mono W2 fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [WP.block_append_iff]
  obtain W3 := setConst_ok hs₃ (n := K.M.n) (o := K.R.z) (x := 0) (le _ (by simp)) (Nat.two_pow_pos _)
  refine WP.mono W3 fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (mov32Rbx_ok s₄ (j := K.J) (by omega_using [hJ])) fun s₅ ⟨b₅, k₅⟩ => ?_
  obtain hU : Unch base (loopW K) s₁.mem s₅.mem := by
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
  obtain c1 : ∀ r ∈ [Reg.rax], r ∈ powClob K.M.n := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp [powClob, clob]
  obtain S₅ : WinSt K C base size P s s₅ := S₁.next hL (hs₄.of_keeps k₅ (by decide))
    ((((k₂.mono c1).trans (k₃.mono c1)).trans (k₄.mono c1)).trans
      ((Keeps.regs k₅).mono (by intro r hr; simp only [List.mem_singleton] at hr; subst hr
                                simp [powClob]))) hU
  obtain b64 : ∀ x ∈ [K.R.x, K.R.y, K.R.z], x + 8 * K.M.n ≤ 2 ^ 64 := fun x hx => by
    have := le x hx; omega_using [hn, this]
  obtain vx : wordsVal s₅.mem base K.R.x K.M.n = 0 := by
    rw [k₅.2.1, O₄.wordsVal axz (b64 _ (by simp)), O₃.wordsVal axy (b64 _ (by simp)), e₂]
  obtain vy : wordsVal s₅.mem base K.R.y K.M.n = K.one := by
    rw [k₅.2.1, O₄.wordsVal ayz (b64 _ (by simp)), e₃]
  obtain vz : wordsVal s₅.mem base K.R.z K.M.n = 0 := by rw [k₅.2.1, e₄]
  obtain I₅ : WinInv K C base size k P s s₅ K.J := by
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
    (fun j s' h1 h2 hi => winStep_ok hL hX hp hC hM3 hP hpn hone_lt hone hF hk8 h1 h2 hi)
    (fun s' hi => ⟨hi.st.keep, hi.st.unch, hi.st.mod, hi.lt, by rw [← winE_zero]; exact hi.rep⟩)
    hJ.1 I₅

end VG.Proof.Weierstrass.X86_64
