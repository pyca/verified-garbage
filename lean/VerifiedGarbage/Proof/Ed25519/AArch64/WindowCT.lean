module

import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual
public import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
public import VerifiedGarbage.Proof.Ed25519.AArch64.Nibbles
public import VerifiedGarbage.Proof.Ed25519.AArch64.WindowLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ed25519.Window
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RecoverCTBlocks
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointEqual
meta import VerifiedGarbage.Proof.Ed25519.AArch64.CTSupport
meta import VerifiedGarbage.Proof.Ed25519.AArch64.Nibbles
meta import VerifiedGarbage.Proof.Ed25519.AArch64.WindowLoop
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ed25519.Window
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
meta import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulCounter
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Merged from `Proof.Ed25519.AArch64.PointEqualCT`. -/

@[expose] public section

section
/-! Point comparison branches only on the two public projective points. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def EqualCTPre (base : Addr) (p q : Spec.Ed25519.Point) (s : State) : Prop :=
  Scr s base ∧ point (env s.mem base) 0 1 2 3 = p ∧ point (env s.mem base) 4 5 6 7 = q

theorem equalFirst_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
      Keep base s t ∧
      eval (.zero .x .x8) t = some (decide (env s.mem base 0 * env s.mem base 6 = env s.mem base 4 * env s.mem base 2)) ∧
      env t.mem base 10 = env s.mem base 1 * env s.mem base 6 ∧
      env t.mem base 11 = env s.mem base 5 * env s.mem base 2 := by
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok pointEqualOps hs) fun a ⟨ka, va⟩ => ?_
  refine WP.mono (fieldEqual_ok (ka.scr hs) 8 9) fun t ⟨tz, kt, te⟩ => ?_
  refine ⟨ka.trans kt, ?_, ?_, ?_⟩
  · change some (t.gpr .x8 == 0) = _
    rw [tz, va, (equalOps_eval _).1, (equalOps_eval _).2.1]
  · rw [te 10 (by decide), va, (equalOps_eval _).2.2.1]
  · rw [te 11 (by decide), va, (equalOps_eval _).2.2.2]

theorem returnFlag_ct (b : Bool) :
    CT (fun _ _ => True) (.block [.movz .w .x8 (if b then 1 else 0) 0]) (fun _ _ => True) := by
  cases b
  · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)
  · apply CT.taint (Taint.ofRegs []) _ (by taint_decide)
    exact fun _ _ _ => agree_ofRegs (by simp)

theorem equalSecond_ct (base : Addr) (u v : Spec.X25519.Fe) :
    CT (fun s t => (Scr s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Scr t base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.seq (.block (fieldEqual 10 11)) (.ite (.zero .x .x8) (.block [.movz .w .x8 1 0]) recoverInvalid))
      (fun _ _ => True) := by
  have ht : CT (fun s t => (Scr s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) ∧
      (Scr t base ∧ env t.mem base 10 = u ∧ env t.mem base 11 = v))
      (.block (fieldEqual 10 11)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : Scr s base ∧ env s.mem base 10 = u ∧ env s.mem base 11 = v) :
      WP isa (.block (fieldEqual 10 11)) s fun t => eval (.zero .x .x8) t = some (decide (u = v)) := by
    refine WP.mono (fieldEqual_ok h.1 10 11) fun t k => ?_
    change some (t.gpr .x8 == 0) = _
    rw [k.1, h.2.1, h.2.2]
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.trans h.2.2.symm
  · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

theorem pointEqual_ct (base : Addr) (p q : Spec.Ed25519.Point) :
    CT (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      Impl.Ed25519.AArch64.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => EqualCTPre base p q s ∧ EqualCTPre base p q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) := by
    apply CT.taint (Taint.ofRegs [.x0]) _ (by taint_decide)
    exact fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0
  have hw (s : State) (h : EqualCTPre base p q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some (decide (p.X * q.Z = q.X * p.Z)) ∧
          env t.mem base 10 = p.Y * q.Z ∧ env t.mem base 11 = q.Y * p.Z := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.scr h.1, ?_, ?_, ?_⟩
    · rw [tz, ← h.2.1, ← h.2.2]; rfl
    · rw [tu, ← h.2.1, ← h.2.2]; rfl
    · rw [tv, ← h.2.1, ← h.2.2]; rfl
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  rw [Impl.Ed25519.AArch64.pointEqual]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · exact (equalSecond_ct base (p.Y * q.Z) (q.Y * p.Z)).mono
      (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
end

/-!
# Verification's windows: what their traces depend on

The windows branch on the digits of the scalars and address the tables by
them, so their traces depend on the scalars: both runs must use the same ones
(in verification, the public inputs are the same in both runs). The nibbles are
split out of the inputs through pointers in the scratch, and the digits read
from them through a counter there, the same in both runs by correctness;
everything else is public by the taint analysis. The skipped nibbles of `k`
are its leading zeros, the same in both runs. The final
comparison branches on whether two points of the group are equal, which only
depends on the points represented.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards

/-- Chains two programs, from runs that satisfy the same predicate. -/
theorem seq_same {P F : State → Prop} {c₁ c₂ : Prog isa}
    (h₁ : CT (fun x y => P x ∧ P y) c₁ (fun _ _ => True)) (w : ∀ x, P x → WP isa c₁ x F)
    (h₂ : CT (fun x y => F x ∧ F y) c₂ (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) (.seq c₁ c₂) (fun _ _ => True) :=
  CT.seq ((CT.wp h₁ fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) h₂

theorem agree_x0 {x y : State} (h : x.gpr .x0 = y.gpr .x0) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs [.x0], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst r; exact h

/-- Code the taint analysis proves constant time with `x0` alone public. -/
theorem x0_ct {base : Addr} {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → x.gpr .x0 = base)
    (h : CT (fun x y => x.gpr .x0 = y.gpr .x0) c (fun _ _ => True)) :
    CT (fun x y => P x ∧ P y) c (fun _ _ => True) :=
  h.mono (fun x y hh => (hP x hh.1).trans (hP y hh.2).symm) (fun _ _ h => h)

theorem agree2 {x y : State} {a b : Reg} (h : x.gpr a = y.gpr a ∧ x.gpr b = y.gpr b) :
    ∀ r ∈ VG.AArch64.Taint.ofRegs [a, b], x.gpr r = y.gpr r :=
  agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2

/-! ## Digits -/

/-- A digit's code: its counter by correctness, the rest by the taint analysis. -/
theorem digit_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {o : Nat}
    (hrest : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x8 = y.gpr .x8)
      (.block [.add .x .x8 .x0 .x8, .ldrb .x19 .x8 o]) (fun _ _ => True)) :
    CT (fun x y => (WinCtx base K S A x ∧ x.mem.readW (off base 56) 64 = C) ∧
      (WinCtx base K S A y ∧ y.mem.readW (off base 56) 64 = C))
      (.block (digitAt o)) (fun _ _ => True) := by
  have hpre : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block [ld .x8 56]) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)
  have w (x : State) (h : WinCtx base K S A x ∧ x.mem.readW (off base 56) 64 = C) :
      WP isa (.block [ld .x8 56]) x fun t => t.gpr .x0 = base ∧ t.gpr .x8 = C :=
    WP.mono (loadPointer_ok h.1.scratch .x8 56 (by decide) (by decide)) fun t ⟨tp, kt⟩ =>
      ⟨(kt.gpr _ (by decide)).trans h.1.scratch.x0, tp.trans h.2⟩
  rw [digitAt, show ([ld .x8 56, .add .x .x8 .x0 .x8, .ldrb .x19 .x8 o] : List Instr) =
    [ld .x8 56] ++ [.add .x .x8 .x0 .x8, .ldrb .x19 .x8 o] from rfl]
  refine blockAppend_ct ((CT.wp (x0_ct (fun x h => h.1.scratch.x0) hpre)
    fun x y h => ⟨w x h.1, w y h.2⟩).mono (fun _ _ h => h) ?_) hrest
  intro x y ⟨_, hx, hy⟩
  exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩

theorem digitRest_ct (o : Nat) (ho : o = 768 ∨ o = 896) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x8 = y.gpr .x8)
      (.block [.add .x .x8 .x0 .x8, .ldrb .x19 .x8 o]) (fun _ _ => True) := by
  rcases ho with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x0, .x8]) (fun _ _ h => agree2 h) (by taint_decide)

/-- What a digit's code reads, in both runs. -/
abbrev DigitCT (base : Addr) (K S : Nat) (A : EPoint dZ) (C : Addr) (digit : List Instr) : Prop :=
  CT (fun x y => (WinCtx base K S A x ∧ x.mem.readW (off base 56) 64 = C) ∧
    (WinCtx base K S A y ∧ y.mem.readW (off base 56) 64 = C)) (.block digit) (fun _ _ => True)

theorem digitK_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} :
    DigitCT base K S A C (digitAt 768) :=
  digit_ct (digitRest_ct _ (.inl rfl))

theorem digitS_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} :
    DigitCT base K S A C (digitAt 896) :=
  digit_ct (digitRest_ct _ (.inr rfl))

/-! ## Windows -/

/-- A window's start, in one run: its digit is `v`, and the counter `C`. -/
structure WinPre (base : Addr) (K S : Nat) (A : EPoint dZ) (C : Addr) (digit : List Instr) (v : Nat)
    (s : State) : Prop where
  ctx : WinCtx base K S A s
  d : env s.mem base 16 = Spec.Ed25519.d
  value : ∃ a, RepP (point (env s.mem base) 0 1 2 3) a
  counter : s.mem.readW (off base 56) 64 = C
  digit : DigitSpec base s digit v
  bound : v < 16

theorem addDigit_ct (o : Nat) (add : List Instr) (h : o = 5376 ∧ add = pointAddCachedP ∨
    o = 5376 ∧ add = pointAddCached ∨ o = 2048 ∧ add = pointAddCachedP) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)
  · exact CT.taint (Taint.ofRegs [.x0, .x19]) (fun _ _ h => agree2 h) (by taint_decide)

/-- A digit and its addition: the branch is on the digit, the same in both runs. -/
theorem digitAdd_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {digit add : List Instr}
    {v o : Nat} (hdig : DigitCT base K S A C digit)
    (hadd : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr o ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    CT (fun x y => WinPre base K S A C digit v x ∧ WinPre base K S A C digit v y)
      (.seq (.block digit) (addDigit o add)) (fun _ _ => True) := by
  have hw (x : State) (h : WinPre base K S A C digit v x) : WP isa (.block digit) x fun u =>
      u.gpr .x0 = base ∧ u.gpr .x19 = BitVec.ofNat 64 v :=
    WP.mono (h.digit x (WinKeep.refl _ _)) fun u ⟨uv, ku⟩ =>
      ⟨(ku.gpr _ (by decide)).trans h.ctx.scratch.x0, uv⟩
  refine CT.seq ((CT.wp (hdig.mono (fun _ _ h => ⟨⟨h.1.ctx, h.1.counter⟩,
    ⟨h.2.ctx, h.2.counter⟩⟩) (fun _ _ h => h)) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono
      (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  rw [addDigit]
  refine CT.ite (fun x y h => ?_) ?_ (VG.RelCT.block_nil fun _ _ h => ⟨h.1, trivial⟩)
  · simp only [eval, read_x, h.1.2, h.2.2]
  · exact hadd.mono (fun x y h => ⟨h.1.1.1.trans h.1.2.1.symm, h.1.1.2.trans h.1.2.2.symm⟩)
      (fun _ _ h => h)

theorem doubleWindow_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) doubleWindow (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem windowWith_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {digit add : List Instr}
    {v : Nat} (hdig : DigitCT base K S A C digit)
    (hadd : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x19 = y.gpr .x19)
      (.block (([.subImm .x .x19 .x19 1] : List Instr) ++ tableAddr 5376 ++ pointFromTableQ ++ add))
      (fun _ _ => True)) :
    CT (fun x y => WinPre base K S A C digit v x ∧ WinPre base K S A C digit v y)
      (windowWith digit add) (fun _ _ => True) := by
  have hw (x : State) (h : WinPre base K S A C digit v x) :
      WP isa doubleWindow x (WinPre base K S A C digit v) := by
    obtain ⟨a, ha⟩ := h.value
    refine WP.mono (doubleWindow_ok h.ctx.scratch ha) fun b ⟨br, bh, bk⟩ => ?_
    have kb := WinKeep.of_double bk
    exact ⟨h.ctx.of_keep kb, (bh 16 (by decide)).trans h.d, ⟨_, br.proj⟩, kb.counter.trans h.counter,
      h.digit.of_keep kb, h.bound⟩
  rw [windowWith]
  exact seq_same (x0_ct (fun x h => h.ctx.scratch.x0) doubleWindow_ct) hw (digitAdd_ct hdig hadd)

theorem windowA_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {digit : List Instr} {v : Nat}
    (hdig : DigitCT base K S A C digit) :
    CT (fun x y => WinPre base K S A C digit v x ∧ WinPre base K S A C digit v y)
      (windowA digit) (fun _ _ => True) :=
  windowWith_ct hdig (addDigit_ct _ _ (.inl ⟨rfl, rfl⟩))

/-- After a window of `k`, the next digit's start. -/
theorem windowWith_next {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr}
    {digit next add : List Instr} {full : Bool} (hadd : AddSpec add cache full) {v w : Nat} {x : State}
    (h : WinPre base K S A C digit v x ∧ DigitSpec base x next w ∧ w < 16) :
    WP isa (windowWith digit add) x (WinPre base K S A C next w) := by
  obtain ⟨a, ha⟩ := h.1.value
  refine WP.mono (windowWith_ok h.1.ctx h.1.d ha hadd h.1.bound h.1.digit) fun b ⟨br, bd, kb⟩ => ?_
  exact ⟨h.1.ctx.of_keep kb, bd, ⟨_, br.proj⟩, kb.counter.trans h.1.counter, h.2.1.of_keep kb, h.2.2⟩

theorem windowAB_ct {base : Addr} {K S : Nat} {A : EPoint dZ} {C : Addr} {digitA digitB : List Instr}
    {vA vB : Nat} (hA : DigitCT base K S A C digitA) (hB : DigitCT base K S A C digitB) :
    CT (fun x y => (WinPre base K S A C digitA vA x ∧ DigitSpec base x digitB vB ∧ vB < 16) ∧
      (WinPre base K S A C digitA vA y ∧ DigitSpec base y digitB vB ∧ vB < 16))
      (windowAB digitA digitB) (fun _ _ => True) := by
  rw [windowAB]
  exact seq_same ((windowWith_ct hA (addDigit_ct _ _ (.inr (.inl ⟨rfl, rfl⟩)))).mono
    (fun _ _ h => ⟨h.1.1, h.2.1⟩) (fun _ _ h => h))
    (fun x h => windowWith_next pointAddCached_spec h)
    (digitAdd_ct hB (addDigit_ct _ _ (.inr (.inr ⟨rfl, rfl⟩))))

/-! ## Nibbles -/

theorem batchBegin_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block batchBegin) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem batchTest_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block batchTest) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem aboveLow_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block aboveLow) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

/-- After `batchBegin`: the counter is `i`. -/
theorem nibBegin_ok {s₀ x : State} {base : Addr} {A : EPoint dZ} {K S i : Nat}
    (h : WinLoop s₀ base A K S (i + 1) x) :
    WP isa (.block batchBegin) x fun a => WinCtx base K S A a ∧ env a.mem base 16 = Spec.Ed25519.d ∧
      (∃ v, RepP (point (env a.mem base) 0 1 2 3) v) ∧
      a.mem.readW (off base 56) 64 = BitVec.ofNat 64 i := by
  refine WP.mono (batchBegin_ok h.ctx.scratch i h.counter) fun a ⟨_, av, ag, ar, aw, asp, am⟩ => ?_
  have ka : ByteKeep base x a := ByteKeep.of_counter ag ar aw asp am
  exact ⟨h.ctx.of_byte ka, by rw [header_env am]; exact h.d, ⟨_, by rw [header_env am]; exact h.value⟩, av⟩

theorem nibStepA_ct {base : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 128) :
    CT (fun x y => (∃ s₀, WinLoop s₀ base A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base A K S (i + 1) y)) nibStepA (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let v := K / 16 ^ i % 16
  have w1 (x : State) (h : ∃ s₀, WinLoop s₀ base A K S (i + 1) x) :
      WP isa (.block batchBegin) x (WinPre base K S A C (digitAt 768) v) := by
    obtain ⟨s₀, h⟩ := h
    exact WP.mono (nibBegin_ok h) fun a ⟨actx, ad, av, ac⟩ =>
      ⟨actx, ad, av, ac, digitK actx hi ac, Nat.mod_lt _ (by decide)⟩
  have w2 (x : State) (h : WinPre base K S A C (digitAt 768) v x) :
      WP isa (windowA (digitAt 768)) x fun c => c.gpr .x0 = base := by
    obtain ⟨a, ha⟩ := h.value
    exact WP.mono (windowA_ok h.ctx h.d ha h.bound h.digit) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.ctx.scratch).x0
  rw [nibStepA]
  refine seq_same (x0_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.x0) batchBegin_ct)
    w1 ?_
  exact seq_same (windowA_ct digitK_ct) w2 (x0_ct (fun _ h => h) aboveLow_ct)

theorem nibStepAB_ct {base : Addr} {A : EPoint dZ} {K S i : Nat} (hi : i < 64) :
    CT (fun x y => (∃ s₀, WinLoop s₀ base A K S (i + 1) x) ∧
      (∃ s₀, WinLoop s₀ base A K S (i + 1) y)) nibStepAB (fun _ _ => True) := by
  let C := BitVec.ofNat 64 i
  let kv := K / 16 ^ i % 16
  let sv := S / 16 ^ i % 16
  have w1 (x : State) (h : ∃ s₀, WinLoop s₀ base A K S (i + 1) x) :
      WP isa (.block batchBegin) x fun a =>
        WinPre base K S A C (digitAt 768) kv a ∧ DigitSpec base a (digitAt 896) sv ∧ sv < 16 := by
    obtain ⟨s₀, h⟩ := h
    exact WP.mono (nibBegin_ok h) fun a ⟨actx, ad, av, ac⟩ =>
      ⟨⟨actx, ad, av, ac, digitK actx (by omega) ac, Nat.mod_lt _ (by decide)⟩, digitS actx hi ac,
        Nat.mod_lt _ (by decide)⟩
  have w2 (x : State) (h : WinPre base K S A C (digitAt 768) kv x ∧
      DigitSpec base x (digitAt 896) sv ∧ sv < 16) :
      WP isa (windowAB (digitAt 768) (digitAt 896)) x fun c => c.gpr .x0 = base := by
    obtain ⟨a, ha⟩ := h.1.value
    exact WP.mono (windowAB_ok h.1.ctx h.1.d ha h.1.bound h.2.2 h.1.digit h.2.1) fun _ ⟨_, _, kc⟩ =>
      (kc.scratch h.1.ctx.scratch).x0
  rw [nibStepAB]
  refine seq_same (x0_ct (fun x h => by obtain ⟨_, h⟩ := h; exact h.ctx.scratch.x0) batchBegin_ct)
    w1 ?_
  exact seq_same (windowAB_ct digitK_ct digitS_ct) w2 (x0_ct (fun _ h => h) batchTest_ct)

/-! ## Loops -/

/-- A run of the loops: from a state satisfying `R₀`, with `c` nibbles left. -/
def LoopRun (R₀ : State → Prop) (base : Addr) (A : EPoint dZ) (K S c : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ WinLoop s₀ base A K S c x

theorem loopA_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S : Nat} (n : Nat)
    (hn0 : 0 < n) (hn : n ≤ 64) :
    CT (fun x y => LoopRun R₀ base A K S (64 + n) x ∧ LoopRun R₀ base A K S (64 + n) y)
      (.loop nibStepA (.nonzero .x .x19))
      (fun x y => LoopRun R₀ base A K S 64 x ∧ LoopRun R₀ base A K S 64 y) := by
  refine (CT.loop (fun n x y => (LoopRun R₀ base A K S (64 + n) x ∧
    LoopRun R₀ base A K S (64 + n) y) ∧ 0 < n ∧ n ≤ 64) ?_ n).mono
      (fun _ _ h => ⟨h, hn0, hn⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 64
  · have hw (x : State) (h : LoopRun R₀ base A K S (64 + (j + 1)) x) :
        WP isa nibStepA x fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
          LoopRun R₀ base A K S (64 + j) u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepA_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (CT.wp ((nibStepA_ct (i := 64 + j) (by omega)).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [xz, decide_eq_true hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [xz, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact CT.of_false fun _ _ h => hj (by omega)

theorem windowsA_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S c : Nat}
    (hc64 : 64 ≤ c) (hc128 : c ≤ 128) :
    CT (fun x y => LoopRun R₀ base A K S c x ∧ LoopRun R₀ base A K S c y) windowsA
      (fun x y => LoopRun R₀ base A K S 64 x ∧ LoopRun R₀ base A K S 64 y) := by
  have hw (x : State) (h : LoopRun R₀ base A K S c x) : WP isa (.block aboveLow) x fun u =>
      eval (.nonzero .x .x19) u = some (decide (c ≠ 64)) ∧ LoopRun R₀ base A K S c u := by
    obtain ⟨s₀, r₀, h⟩ := h
    exact WP.mono (aboveLow_ok h.ctx.scratch c hc128 h.counter) fun u ⟨uz, ku⟩ =>
      ⟨uz, s₀, r₀, h.of_keeps ku (by decide)⟩
  rw [windowsA]
  refine CT.seq ((CT.wp (x0_ct (fun x h => by obtain ⟨_, _, h⟩ := h; exact h.ctx.scratch.x0)
    aboveLow_ct) fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine CT.ite (fun x y h => h.1.1.trans h.2.1.symm) ?_ ?_
  · obtain ⟨n, rfl⟩ : ∃ n, c = 64 + n := ⟨c - 64, by omega⟩
    by_cases hn : n = 0
    · subst hn
      exact CT.of_false fun x y h => by
        have := h.2; rw [h.1.1.1] at this; cases this
    · exact (loopA_ct n (by omega) (by omega)).mono (fun _ _ h => ⟨h.1.1.2, h.1.2.2⟩)
        (fun _ _ h => h)
  · refine VG.RelCT.block_nil fun x y h => ⟨h.1, ?_⟩
    have hc : c = 64 := by
      by_contra hne
      have := h.2.2; rw [h.2.1.1.1, decide_eq_true hne] at this; cases this
    subst hc
    exact ⟨h.2.1.1.2, h.2.1.2.2⟩

theorem loopB_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S : Nat} :
    CT (fun x y => LoopRun R₀ base A K S 64 x ∧ LoopRun R₀ base A K S 64 y)
      (.loop nibStepAB (.nonzero .x .x19))
      (fun x y => LoopRun R₀ base A K S 0 x ∧ LoopRun R₀ base A K S 0 y) := by
  refine (CT.loop (fun n x y => (LoopRun R₀ base A K S n x ∧
    LoopRun R₀ base A K S n y) ∧ 0 < n ∧ n ≤ 64) ?_ 64).mono
      (fun _ _ h => ⟨h, by decide, by decide⟩) (fun _ _ h => h)
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => Nat.lt_irrefl 0 h.2.1
  by_cases hj : j < 64
  · have hw (x : State) (h : LoopRun R₀ base A K S (j + 1) x) :
        WP isa nibStepAB x fun u => eval (.nonzero .x .x19) u = some (decide (j ≠ 0)) ∧
          LoopRun R₀ base A K S j u := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (stepB_ok hj h) fun u ⟨uz, hu⟩ => ⟨uz, s₀, r₀, hu⟩
    refine (CT.wp ((nibStepAB_ct (i := j) hj).mono
      (fun x y h => ⟨by obtain ⟨s₀, _, hx⟩ := h.1.1; exact ⟨s₀, hx⟩,
        by obtain ⟨s₀, _, hy⟩ := h.1.2; exact ⟨s₀, hy⟩⟩) (fun _ _ h => h))
      fun x y h => ⟨hw x h.1.1, hw y h.1.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, hx⟩, ⟨yz, hy⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have : j = 0 := by
        by_contra hne
        rw [xz, decide_eq_true hne] at he
        cases he
      subst this
      exact ⟨hx, hy⟩
    · have : j ≠ 0 := by
        intro hz
        rw [xz, hz] at he
        cases he
      exact ⟨j, by omega, ⟨hx, hy⟩, by omega, by omega⟩
  · exact CT.of_false fun _ _ h => hj (by omega)

/-! ## Skipping the leading zero nibbles of `k` -/

/-- A run of the skipping: from a state satisfying `R₀`, with `64 + n` nibbles left. -/
def SkipRun (R₀ : State → Prop) (base : Addr) (A : EPoint dZ) (K S n : Nat) (x : State) : Prop :=
  ∃ s₀, R₀ s₀ ∧ SkipInv s₀ base A K S n x

/-- The counter, less one. -/
def skipPrefix : List Instr := [ld .x8 56, .subImm .x .x8 .x8 1]

theorem skipPrefix_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block skipPrefix) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem skipRest_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x8 = y.gpr .x8)
    (.block [.add .x .x2 .x0 .x8, .ldrb .x19 .x2 768]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0, .x8]) (fun _ _ h => agree2 h) (by taint_decide)

theorem skipPrefix_ok {s : State} {base : Addr} (hs : Scr s base) (j : Nat)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block skipPrefix) s fun t => t.gpr .x0 = base ∧ t.gpr .x8 = BitVec.ofNat 64 j := by
  rw [skipPrefix, show ([ld .x8 56, .subImm .x .x8 .x8 1] : List Instr) =
    [ld .x8 56] ++ [.subImm .x .x8 .x8 1] from rfl, WP.block_append_iff]
  refine WP.mono (loadPointer_ok hs .x8 56 (by decide) (by decide)) fun a ⟨av, ka⟩ => ?_
  refine WP.mono (subOne_ok a .x8 j (av.trans hc)) fun t ⟨tv, kt⟩ => ?_
  exact ⟨(kt.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hs.x0), tv⟩

theorem movzZero_ct : CT (fun _ _ => True) (.block [.movz .w .x19 0 0]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs []) (fun _ _ _ => agree_ofRegs (by simp)) (by taint_decide)

theorem skipStore_ct : CT (fun x y => x.gpr .x0 = y.gpr .x0)
    (.block [st .x8 56, .subImm .x .x19 .x8 64]) (fun _ _ => True) :=
  CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

theorem skipBody_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S j : Nat} :
    CT (fun x y => SkipRun R₀ base A K S (j + 1) x ∧ SkipRun R₀ base A K S (j + 1) y)
      skipBody (fun _ _ => True) := by
  let P := SkipRun R₀ base A K S (j + 1)
  have hx0 (x : State) (h : P x) : x.gpr .x0 = base := by
    obtain ⟨_, _, h, _⟩ := h; exact h.ctx.scratch.x0
  have hpre (x : State) (h : P x) : WP isa (.block skipPrefix) x fun t =>
      t.gpr .x0 = base ∧ t.gpr .x8 = BitVec.ofNat 64 (64 + j) := by
    obtain ⟨_, _, h, _⟩ := h
    exact skipPrefix_ok h.ctx.scratch (64 + j) (by rw [h.counter]; rfl)
  have hload : CT (fun x y => P x ∧ P y) (.block skipLoad) (fun _ _ => True) := by
    rw [show skipLoad = skipPrefix ++ [.add .x .x2 .x0 .x8, .ldrb .x19 .x2 768] from rfl]
    refine blockAppend_ct ((CT.wp (x0_ct hx0 skipPrefix_ct) fun x y h => ⟨hpre x h.1, hpre y h.2⟩).mono
      (fun _ _ h => h) ?_) skipRest_ct
    intro x y ⟨_, hx, hy⟩
    exact ⟨hx.1.trans hy.1.symm, hx.2.trans hy.2.symm⟩
  have hw (x : State) (h : P x) : WP isa (.block skipLoad) x fun u => u.gpr .x0 = base ∧
      u.gpr .x19 = BitVec.ofNat 64 (K / 16 ^ (64 + j) % 16) := by
    obtain ⟨_, _, hl, _, _, hn⟩ := h
    refine WP.mono (skipLoad_ok hl.ctx.scratch (64 + j) (by omega) (by rw [hl.counter]; rfl))
      fun u ⟨_, uv, ku⟩ => ⟨(ku.gpr _ (by decide)).trans hl.ctx.scratch.x0,
        by rw [uv, hl.ctx.kNib _ (by omega)]⟩
  rw [skipBody]
  refine CT.seq ((CT.wp hload fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h)
    (fun _ _ h => h.2)) ?_
  refine CT.ite (fun x y h => by simp only [eval, read_x, h.1.2, h.2.2]) ?_ ?_
  · exact movzZero_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact skipStore_ct.mono (fun _ _ h => h.1.1.1.trans h.1.2.1.symm) (fun _ _ h => h)

theorem skipZero_ct {R₀ : State → Prop} {base : Addr} {A : EPoint dZ} {K S : Nat} :
    CT (fun x y => SkipRun R₀ base A K S 64 x ∧ SkipRun R₀ base A K S 64 y) skipZero
      (fun x y => ∃ c, 64 ≤ c ∧ c ≤ 128 ∧ LoopRun R₀ base A K S c x ∧
        LoopRun R₀ base A K S c y) := by
  rw [skipZero]
  refine CT.loop (fun n x y => SkipRun R₀ base A K S n x ∧ SkipRun R₀ base A K S n y)
    ?_ 64
  intro n
  rcases n with _ | j
  · exact CT.of_false fun _ _ h => by obtain ⟨_, _, _, _, h, _⟩ := h.1; exact Nat.lt_irrefl 0 h
  by_cases hj : j < 64
  · have hw (x : State) (h : SkipRun R₀ base A K S (j + 1) x) : WP isa skipBody x fun u =>
        eval (.nonzero .x .x19) u = some (skipOn K j) ∧
        (skipOn K j = false → LoopRun R₀ base A K S (skipEnd K j) u) ∧
        (skipOn K j = true → SkipRun R₀ base A K S j u) := by
      obtain ⟨s₀, r₀, h⟩ := h
      exact WP.mono (skipBody_ok h) fun u ⟨uz, uf, ut⟩ =>
        ⟨uz, fun hf => ⟨s₀, r₀, uf hf⟩, fun ht => ⟨s₀, r₀, ut ht⟩⟩
    refine (CT.wp skipBody_ct fun x y h => ⟨hw x h.1, hw y h.2⟩).mono (fun _ _ h => h) ?_
    intro x y ⟨_, ⟨xz, xf, xt⟩, ⟨yz, yf, yt⟩⟩
    refine ⟨xz.trans yz.symm, fun he => ?_, fun he => ?_⟩
    · have hs : skipOn K j = false := Option.some.inj (xz.symm.trans he)
      exact ⟨skipEnd K j, (skipEnd_range K j hj).1, (skipEnd_range K j hj).2, xf hs, yf hs⟩
    · have hs : skipOn K j = true := Option.some.inj (xz.symm.trans he)
      exact ⟨j, by omega, xt hs, yt hs⟩
  · exact CT.of_false fun _ _ h => by obtain ⟨_, _, _, _, _, h⟩ := h.1; exact hj (by omega)

/-! ## The nibbles -/

/-- What the nibbles' code needs, in one run. -/
structure NibPre (base sig challenge : Addr) (s : State) : Prop where
  scratch : Scr s base
  kHeader : s.mem.readW (off base 7952) 64 = challenge
  sHeader : s.mem.readW (off base 7944) 64 = sig
  kRead : ∀ d, d + 16 ≤ 64 → InRegions (s.rd ++ s.wr) (off challenge d) 16
  sRead : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 16
  kFar : ∀ i < 64, 8192 ≤ ofs base (off challenge i)
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)

/-- After `k`'s nibbles, what `S`'s need. -/
structure SNibPre (base sig : Addr) (s : State) : Prop where
  scratch : Scr s base
  sHeader : s.mem.readW (off base 7944) 64 = sig
  sRead : ∀ d, d + 16 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 16
  sFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)
  mask : s.v .v7 = mask15

/-- A block's trace, with what each run reaches. -/
theorem stage_ct {P F : State → Prop} {xs : List Instr}
    (h : CT (fun x y => P x ∧ P y) (.block xs) (fun _ _ => True))
    (w : ∀ x, P x → WP isa (.block xs) x F) :
    CT (fun x y => P x ∧ P y) (.block xs) (fun x y => F x ∧ F y) :=
  (CT.wp h fun x y hh => ⟨w x hh.1, w y hh.2⟩).mono (fun _ _ h => h) (fun _ _ h => h.2)

theorem ldPtr_ct (d : Nat) (hd : d = 7952 ∨ d = 7944) :
    CT (fun x y => x.gpr .x0 = y.gpr .x0) (.block [ld .x2 d]) (fun _ _ => True) := by
  rcases hd with rfl | rfl
  all_goals exact CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => agree_x0 h) (by taint_decide)

/-- The nibbles' trace: the scalars' pointers by correctness, the rest by the taint analysis. -/
theorem nibbles_ct {base sig challenge : Addr} :
    CT (fun x y => NibPre base sig challenge x ∧ NibPre base sig challenge y) (.block nibbles)
      (fun _ _ => True) := by
  have c1 := stage_ct (P := NibPre base sig challenge)
    (F := fun x => NibPre base sig challenge x ∧ x.gpr .x2 = challenge)
    (x0_ct (fun x h => h.scratch.x0) (ldPtr_ct 7952 (.inl rfl))) fun x h =>
      WP.mono (loadPointer_ok h.scratch .x2 7952 (by decide) (by decide)) fun t ⟨tp, kt⟩ =>
        ⟨⟨h.scratch.of_keeps kt (by decide), by rw [kt.mem]; exact h.kHeader,
          by rw [kt.mem]; exact h.sHeader, by rw [kt.rd, kt.wr]; exact h.kRead,
          by rw [kt.rd, kt.wr]; exact h.sRead, h.kFar, h.sFar⟩, tp.trans h.kHeader⟩
  have c2 := stage_ct (P := fun x => NibPre base sig challenge x ∧ x.gpr .x2 = challenge)
    (F := SNibPre base sig)
    ((CT.taint (Taint.ofRegs [.x0, .x2]) (fun _ _ h => agree2 h) (by taint_decide) :
      CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x2 = y.gpr .x2) (.block kNibblesAt)
        (fun _ _ => True)).mono
      (fun x y h => ⟨h.1.1.scratch.x0.trans h.2.1.scratch.x0.symm, h.1.2.trans h.2.2.symm⟩)
      (fun _ _ h => h)) fun x h =>
      WP.mono (kNibblesAt_ok h.1.scratch h.2 h.1.kRead h.1.kFar) fun t ⟨_, tm, tg, tr, tw, _, t7⟩ =>
        ⟨⟨by rw [tg _ (by decide)]; exact h.1.scratch.x0, by rw [tw]; exact h.1.scratch.wr,
          h.1.scratch.nowrap⟩, (tm.word (d := 7944) (Or.inr (by decide)) (by decide)).trans h.1.sHeader,
          by rw [tr, tw]; exact h.1.sRead, h.1.sFar, t7⟩
  have c3 := stage_ct (P := SNibPre base sig) (F := fun x => SNibPre base sig x ∧ x.gpr .x2 = sig)
    (x0_ct (fun x h => h.scratch.x0) (ldPtr_ct 7944 (.inr rfl))) fun x h =>
      WP.mono (loadPointerV_ok h.scratch .x2 7944 (by decide) (by decide)) fun t ⟨tp, kt, tv⟩ =>
        ⟨⟨h.scratch.of_keeps kt (by decide), by rw [kt.mem]; exact h.sHeader,
          by rw [kt.rd, kt.wr]; exact h.sRead, h.sFar, by rw [tv]; exact h.mask⟩, tp.trans h.sHeader⟩
  have c4 : CT (fun x y => (SNibPre base sig x ∧ x.gpr .x2 = sig) ∧ (SNibPre base sig y ∧ y.gpr .x2 = sig))
      (.block (nibBlocks 32 896 2)) (fun _ _ => True) :=
    (CT.taint (Taint.ofRegs [.x0, .x2]) (fun _ _ h => agree2 h) (by taint_decide) :
      CT (fun x y => x.gpr .x0 = y.gpr .x0 ∧ x.gpr .x2 = y.gpr .x2) (.block (nibBlocks 32 896 2))
        (fun _ _ => True)).mono
      (fun x y h => ⟨h.1.1.scratch.x0.trans h.2.1.scratch.x0.symm, h.1.2.trans h.2.2.symm⟩)
      (fun _ _ h => h)
  rw [nibbles, kNibbles, sNibbles, List.append_assoc]
  exact blockAppend_ct c1 (blockAppend_ct c2 (blockAppend_ct c3 c4))

/-! ## The comparison -/

/-- Two points representing `P` and `Q` in slots 0–3 and 4–7. -/
def EqRepPre (base : Addr) (P Q : EPoint dZ) (s : State) : Prop :=
  Scr s base ∧ RepP (point (env s.mem base) 0 1 2 3) P ∧ RepP (point (env s.mem base) 4 5 6 7) Q

theorem pointEqualRep_ct (base : Addr) (P Q : EPoint dZ) :
    CT (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      Impl.Ed25519.AArch64.pointEqual (fun _ _ => True) := by
  have ht : CT (fun s t => EqRepPre base P Q s ∧ EqRepPre base P Q t)
      (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0) (by taint_decide)
  have hw (s : State) (h : EqRepPre base P Q s) :
      WP isa (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) s fun t =>
        Scr t base ∧ eval (.zero .x .x8) t = some (decide (P.x = Q.x)) ∧
          (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y) := by
    refine WP.mono (equalFirst_ok h.1) fun t ⟨kt, tz, tu, tv⟩ => ?_
    refine ⟨kt.scr h.1, ?_, ?_⟩
    · rw [tz]
      exact congrArg some (decide_eq_decide.mpr (repP_cross_x h.2.1 h.2.2))
    · rw [tu, tv]
      exact repP_cross_y h.2.1 h.2.2
  have hp := CT.wp ht (fun s t h => ⟨hw s h.1, hw t h.2⟩)
  have ht2 : CT (fun s t => (Scr s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) ∧
      (Scr t base ∧ (env t.mem base 10 = env t.mem base 11 ↔ P.y = Q.y)))
      (.block (fieldEqual 10 11)) (fun _ _ => True) :=
    CT.taint (Taint.ofRegs [.x0]) (fun _ _ h => x0_agree h.1.1.x0 h.2.1.x0) (by taint_decide)
  have hw2 (s : State) (h : Scr s base ∧ (env s.mem base 10 = env s.mem base 11 ↔ P.y = Q.y)) :
      WP isa (.block (fieldEqual 10 11)) s fun t => eval (.zero .x .x8) t = some (decide (P.y = Q.y)) :=
    WP.mono (fieldEqual_ok h.1 10 11) fun t k => by
      change some (t.gpr .x8 == 0) = _
      rw [k.1]; exact congrArg some (decide_eq_decide.mpr h.2)
  have hp2 := CT.wp ht2 (fun s t h => ⟨hw2 s h.1, hw2 t h.2⟩)
  rw [Impl.Ed25519.AArch64.pointEqual]
  refine CT.seq hp (CT.ite ?_ ?_ ?_)
  · exact fun _ _ h => h.2.1.2.1.trans h.2.2.2.1.symm
  · refine CT.seq (hp2.mono (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.2⟩⟩)
      (fun _ _ h => h)) (CT.ite ?_ ?_ ?_)
    · exact fun _ _ h => h.2.1.trans h.2.2.symm
    · exact (returnFlag_ct true).mono (fun _ _ _ => trivial) (fun _ _ h => h)
    · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.AArch64
