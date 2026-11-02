module

public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
public import VerifiedGarbage.Proof.Rsa.RecoverDet
public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.X86.Rd.Ops
import VerifiedGarbage.Proof.Rsa.X86.Rd.Count
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvFusedFlags
import VerifiedGarbage.Proof.Rsa.X86.RvSubWrap
public import VerifiedGarbage.Proof.Rsa.RecoverSubtract
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The halvings of Appendix C.2 on i686

`RecoverDetRt.twos`: `u = n - 1` halved while even, `x` (narrow) halved
and `x'` (wide) doubled while both are: `32 w` steps of
`RecoverDet.twoStep` modulo `2^(32 W)`.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.RecoverDet (twoStep)
open VG.Proof.Rsa (b2n b2n_le)

section
variable {g : Geo} {s0 : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

theorem mod2_b2n (n : Nat) : n % 2 = b2n (decide (n % 2 = 1)) := by
  unfold b2n; by_cases h : n % 2 = 1 <;> simp [h]; omega

/-- `[j]` halved where the header word `sl` is one. -/
theorem halfIf_ok {j sl : Nat} {u : State} (h : KS g s0 A live AW liveW V ls u)
    (hj : j ∈ live) (hT : aTmp ∉ live) (hjT : j ≠ aTmp) (hsl : sl ∈ ls) (bit : V sl ≤ 1)
    (hlW : ∀ i ∈ liveW, j / 2 ≠ i ∧ aTmp / 2 ≠ i) :
    WP isa (halfIf j sl) u fun v =>
      KS g s0 (upd A j (if V sl = 0 then A j else A j / 2)) live AW liveW V ls v := by
  unfold halfIf
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := aTmp) (a := j) (by decide) hj (Ne.symm hjT)
    (fun i hi => (hlW i hi).2)) fun u1 ⟨h1, _, _⟩ => ?_)
  refine WP.seq (wp_movS rfl fun u2 U _ => WP.block_nil ?_)
  have h2 := h1.of_rest U.keeps (by decide) U.mem
  refine WP.seq (WP.mono (h2.half_w (j := aTmp) (by simp) (by rw [U.gpr]; rfl) (fun i hi => (hlW i hi).2))
    fun u3 ⟨h3, _⟩ => ?_)
  refine WP.mono (h3.sel_w (o := j) (a := j) (b := aTmp) (sl := sl) (h.live_lt j hj) (by simp [hj]) (by simp)
    hsl bit (.inr hjT) (fun i hi => (hlW i hi).1)) fun v ⟨hv, _⟩ => ?_
  refine hv.mono (fun i hi => ⟨by simp [hi], ?_⟩) (fun i hi => ⟨hi, rfl⟩) (fun d hd => ⟨hd, rfl⟩)
  have iT : i ≠ aTmp := fun e => hT (e ▸ hi)
  by_cases ij : i = j
  · subst ij; simp [upd, hjT]
  · simp [upd, ij, iT]

/-- The arrays the halvings name, apart from the arrays tracked around them. -/
structure TwoIdx (live liveW ls : List Nat) : Prop where
  u_live : aU ∈ live
  x_live : aX2 ∈ live
  x3_live : wX3 ∈ liveW
  tmp_not : aTmp ∉ live
  t_not : wT ∉ liveW
  live_apart : ∀ j ∈ live, j / 2 ≠ wT ∧ j / 2 ≠ wX3
  liveW_apart : ∀ j ∈ liveW, aU / 2 ≠ j ∧ aX2 / 2 ≠ j ∧ aTmp / 2 ≠ j
  slots_not : ∀ d ∈ [sU, sX, sBoth, sEven], d ∉ ls
  sK_in : sK ∈ ls

/-- The halvings after `i` steps: `(u, x, x')`. -/
def TwoS (g : Geo) (s0 : State) (A : Nat → Nat) (live : List Nat) (AW : Nat → Nat) (liveW : List Nat)
    (V : Nat → Nat) (ls : List Nat) (K i : Nat) (st : Nat × Nat × Nat) (u : State) : Prop :=
  KS g s0 (upd (upd A aU st.1) aX2 st.2.1) live (upd AW wX3 st.2.2) liveW (upd V sK (K - i)) ls u

theorem twosBody_ok {K i : Nat} {st : Nat × Nat × Nat} {u : State}
    (I : TwoIdx live liveW ls) (hi : i < K) (hK : K < 2 ^ 32)
    (h : TwoS g s0 A live AW liveW V ls K i st u) :
    WP isa twosBody u fun v =>
      TwoS g s0 A live AW liveW V ls K (i + 1) (twoStep (32 * g.W) st) v ∧
      v.zf = some (decide (K - i - 1 = 0)) := by
  obtain ⟨U0, X2, X3⟩ := st
  unfold TwoS at h
  simp only at h
  have vU : upd (upd A aU U0) aX2 X2 aU = U0 := by simp [upd, aU, aX2]
  have vX : upd (upd A aU U0) aX2 X2 aX2 = X2 := by simp [upd]
  unfold twosBody twosFlags
  simp only [seqs]
  refine WP.seq (WP.seq (WP.mono (h.bitOf_w (j := aU) (sl := sU) I.u_live (by decide)) fun u1 ⟨h1, _⟩ => ?_))
  rw [vU, mod2_b2n U0] at h1
  refine WP.seq (WP.mono (h1.bitOf_w (j := aX2) (sl := sX) I.x_live (by decide)) fun u2 ⟨h2, _⟩ => ?_)
  rw [vX, mod2_b2n X2] at h2
  refine WP.seq (WP.mono (h2.flagOr_ok (d := sBoth) (a := sU) (b := sX) (x := decide (U0 % 2 = 1)) (y := decide (X2 % 2 = 1)) (by decide) (by simp) (by simp)
    (by simp [upd, sU, sX]) (by simp [upd])) fun u3 h3 => ?_)
  refine WP.seq (WP.mono (h3.flagNot_ok (d := sBoth) (a := sBoth) (x := decide (U0 % 2 = 1) || decide (X2 % 2 = 1)) (by decide) (by simp) (by simp [upd]))
    fun u4 h4 => ?_)
  refine WP.mono (h4.flagNot_ok (d := sEven) (a := sU) (x := decide (U0 % 2 = 1)) (by decide) (by simp)
    (by simp [upd, sU, sBoth, sX])) fun u5 h5 => ?_
  have dn := I.slots_not
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at dn
  -- The flags, as two booleans.
  generalize hE : (!decide (U0 % 2 = 1)) = bE at h5
  generalize hB : (!(decide (U0 % 2 = 1) || decide (X2 % 2 = 1))) = bB at h5
  have h5' : KS g s0 (upd (upd A aU U0) aX2 X2) live (upd AW wX3 X3) liveW
      (upd (upd (upd V sK (K - i)) sBoth (b2n bB)) sEven (b2n bE)) (sEven :: sBoth :: ls) u5 := by
    refine h5.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨by simp only [List.mem_cons] at hd ⊢; rcases hd with h | h | h <;> simp [h], ?_⟩)
    simp only [List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · simp [upd]
    · simp [upd, sBoth, sEven]
    · have : d ≠ sU := fun e => dn.1 (e ▸ hd)
      have : d ≠ sX := fun e => dn.2.1 (e ▸ hd)
      have : d ≠ sBoth := fun e => dn.2.2.1 (e ▸ hd)
      have : d ≠ sEven := fun e => dn.2.2.2 (e ▸ hd)
      simp [upd, *]
  have vE : upd (upd (upd V sK (K - i)) sBoth (b2n bB)) sEven (b2n bE) sEven = b2n bE := by simp [upd]
  have vB : upd (upd (upd V sK (K - i)) sBoth (b2n bB)) sEven (b2n bE) sBoth = b2n bB := by
    simp [upd, sBoth, sEven]
  have vK : upd (upd (upd V sK (K - i)) sBoth (b2n bB)) sEven (b2n bE) sK = K - i := by
    simp [upd, sBoth, sEven, sK]
  have hlW : ∀ i ∈ liveW, aU / 2 ≠ i ∧ aTmp / 2 ≠ i := fun i hi => ⟨(I.liveW_apart i hi).1, (I.liveW_apart i hi).2.2⟩
  have hlW2 : ∀ i ∈ liveW, aX2 / 2 ≠ i ∧ aTmp / 2 ≠ i := fun i hi => ⟨(I.liveW_apart i hi).2.1, (I.liveW_apart i hi).2.2⟩
  refine WP.seq (WP.mono (halfIf_ok h5' I.u_live I.tmp_not (by decide) (by simp) (by rw [vE]; exact b2n_le _) hlW)
    fun u6 h6 => ?_)
  rw [vE, vU] at h6
  refine WP.seq (WP.mono (halfIf_ok h6 I.x_live I.tmp_not (by decide) (by simp) (by rw [vB]; exact b2n_le _) hlW2)
    fun u7 h7 => ?_)
  rw [vB, show upd (upd (upd A aU U0) aX2 X2) aU (if b2n bE = 0 then U0 else U0 / 2) aX2 = X2 by
    simp [upd, aU, aX2]] at h7
  refine WP.seq (WP.mono (h7.add_W (o := wT) (a := wX3) (b := wX3) (by decide) I.x3_live I.x3_live
    (fun j hj => (I.live_apart j hj).1)) fun u8 ⟨h8, _⟩ => ?_)
  refine WP.seq (WP.mono (h8.sel_W (o := wX3) (a := wX3) (b := wT) (sl := sBoth) (by decide) (by simp [I.x3_live]) (by simp)
    (by simp) (by rw [vB]; exact b2n_le _) (.inr (by decide)) (fun j hj => (I.live_apart j hj).2)) fun u9 ⟨h9, _⟩ => ?_)
  rw [vB] at h9
  refine WP.mono (h9.countNext_ok (by simp [I.sK_in]) (by rw [vK]; omega) (by rw [vK]; omega))
    fun v ⟨hv, zv⟩ => ⟨?_, by rw [zv, vK]⟩
  -- The step's values.
  have step : twoStep (32 * g.W) (U0, X2, X3) = (if b2n bE = 0 then U0 else U0 / 2,
      if b2n bB = 0 then X2 else X2 / 2, if b2n bB = 0 then X3 else (X3 + X3) % 2 ^ (32 * g.W)) := by
    subst hE hB
    unfold twoStep
    rcases Nat.mod_two_eq_zero_or_one U0 with hu | hu <;> rcases Nat.mod_two_eq_zero_or_one X2 with hx | hx <;>
      simp [hu, hx, b2n, Nat.two_mul]
  unfold TwoS
  rw [step]
  simp only
  refine hv.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨by simp [hj], ?_⟩) (fun d hd => ⟨by simp [hd], ?_⟩)
  · by_cases ju : j = aU
    · subst ju; simp [upd, aX2]
    · by_cases jx : j = aX2
      · subst jx; simp [upd]
      · simp [upd, ju, jx]
  · have jT : j ≠ wT := fun e => I.t_not (e ▸ hj)
    by_cases jx : j = wX3
    · subst jx; simp [upd, wX3, wT]
    · simp [upd, jx, jT]
  · have : d ≠ sU := fun e => dn.1 (e ▸ hd)
    have : d ≠ sX := fun e => dn.2.1 (e ▸ hd)
    have : d ≠ sBoth := fun e => dn.2.2.1 (e ▸ hd)
    have : d ≠ sEven := fun e => dn.2.2.2 (e ▸ hd)
    by_cases dk : d = sK
    · subst dk; simp [upd, sBoth, sEven, sK]; omega
    · simp [upd, *]

theorem twosLoop_ok {u : State} {st : Nat × Nat × Nat}
    (I : TwoIdx live liveW ls) (h : TwoS g s0 A live AW liveW V ls (32 * g.w) 0 st u) :
    WP isa (.loop twosBody .ne) u
      (TwoS g s0 A live AW liveW V ls (32 * g.w) (32 * g.w) ((twoStep (32 * g.W))^[32 * g.w] st)) := by
  have up := h.upper
  refine countLoop (P := fun i v => TwoS g s0 A live AW liveW V ls (32 * g.w) i ((twoStep (32 * g.W))^[i] st) v)
    (by change 0 < 32 * (2 * g.n + 2); omega) h fun i v hi hv => ?_
  refine WP.mono (twosBody_ok I hi (by change 32 * (2 * g.n + 2) < _; omega) hv) fun w ⟨hw, zw⟩ => ⟨?_, zw⟩
  rw [Function.iterate_succ_apply']
  exact hw

end

open VG.Proof.Rsa (sub32)

/-- The halvings' set-up: `u = n - 1`, `x` and `x'` copied and the count set, from `n` (`aN`), `x`
(`aX2`, the low half of `wX`, whose wide value `x'` is `wX`'s), and zero (`aZ0`). -/
theorem twosHead_ok {g : Geo} {s0 u : State} {A AW V : Nat → Nat} {n x X : Nat}
    (h : KS g s0 A [aZ0, aX2, aN] AW [wX] V [sOkDE] u)
    (z : A aZ0 = 0) (hn : A aN = n) (hx : A aX2 = x) (hX : AW wX = X) :
    WP isa (.seq twosInit (.block countN)) u
      (TwoS g s0 (upd (upd A aU 0) aX2 0) [aU, aX2, aN] (upd AW wX3 0) [wX3] V [sK, sOkDE] (32 * g.w) 0
        (sub32 g.w n 1, x, X)) := by
  have hn' : A 32 = n := hn
  have hx' : A 20 = x := hx
  unfold twosInit
  simp only [seqs]
  refine WP.seq (WP.seq (WP.mono (h.copy_w (o := aOneN) (a := aZ0) (by decide) (by simp) (by decide) (by decide))
    fun u1 ⟨h1, _, _⟩ => ?_))
  refine WP.seq (WP.mono (h1.setOne_w (j := aOneN) (by simp) (by decide)) fun u2 ⟨h2, _⟩ => ?_)
  refine WP.seq (WP.mono (h2.subWrap (o := aU) (a := aN) (b := aOneN) (by decide) (by simp) (by simp) (by decide)
    (by decide) (by decide)) fun u3 ⟨h3, _⟩ => ?_)
  refine WP.mono (h3.copy_W (o := wX3) (a := wX) (by decide) (by simp) (by decide) (by decide)) fun u4 ⟨h4, _⟩ => ?_
  refine WP.mono (h4.countN_ok) fun u5 h5 => ?_
  have one : upd (upd A aOneN (A aZ0)) aOneN (1 + 2 ^ 32 * (upd A aOneN (A aZ0) aOneN / 2 ^ 32)) aOneN = 1 := by
    simp [upd, z]
  unfold TwoS
  refine h5.mono (fun j hj => ⟨by simp at hj ⊢; omega, ?_⟩) (fun j hj => ⟨by simp at hj ⊢; omega, ?_⟩)
    (fun d hd => ⟨by simpa using hd, ?_⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp [upd, hn', z, aU, aOneN, aN, VG.Impl.Rsa.X86.Recover.aN, aX2]
    · simp [upd, hx', aU, aOneN, aX2]
    · simp [upd, hn', aU, aOneN, aX2, aN, VG.Impl.Rsa.X86.Recover.aN]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    subst hj; simp [upd, hX]
  · simp [upd]

/-- The arrays and header words the halvings track, as `TwoIdx` needs them. -/
theorem twosIdx : TwoIdx [aU, aX2, aN] [wX3] [sK, sOkDE] :=
  ⟨by simp, by simp, by simp, by decide, by decide, by decide, by decide, by decide, by simp⟩

/-- The halvings from `n` (`aN`), `x` (`aX2`, the low half of `wX`, whose wide value `x'` is
`wX`'s), and zero (`aZ0`). -/
theorem twos_ok {g : Geo} {s0 u : State} {A AW V : Nat → Nat} {n x X : Nat}
    (h : KS g s0 A [aZ0, aX2, aN] AW [wX] V [sOkDE] u)
    (z : A aZ0 = 0) (hn : A aN = n) (hx : A aX2 = x) (hX : AW wX = X) :
    WP isa twos u fun v => ∃ A' AW' V',
      KS g s0 A' [aU, aX2, aN] AW' [wX3] V' [sK, sOkDE] v ∧
      A' aU = ((twoStep (32 * g.W))^[32 * g.w] (sub32 g.w n 1, x, X)).1 ∧
      A' aX2 = ((twoStep (32 * g.W))^[32 * g.w] (sub32 g.w n 1, x, X)).2.1 ∧
      AW' wX3 = ((twoStep (32 * g.W))^[32 * g.w] (sub32 g.w n 1, x, X)).2.2 ∧
      A' aN = n ∧ V' sOkDE = V sOkDE := by
  have hn' : A 32 = n := hn
  unfold twos
  simp only [seqs]
  refine WP.assoc (WP.seq (WP.mono (twosHead_ok h z hn hx hX) fun v hv =>
    WP.mono (twosLoop_ok twosIdx hv) fun w hw => ?_))
  unfold TwoS at hw
  refine ⟨_, _, _, hw, by simp [upd, aU, aX2], by simp [upd], by simp [upd], by simp [upd, aU, aX2, aN,
    VG.Impl.Rsa.X86.Recover.aN, hn'], by simp [upd, sK, sOkDE]⟩

end VG.Proof.Rsa.X86.Recover
