import VerifiedGarbage.Proof.X448.AArch64.Fast.StepOps
import VerifiedGarbage.Proof.X448.AArch64.Weak.Inv
import VerifiedGarbage.Proof.X448.AArch64.Weak.Counters
import VerifiedGarbage.Proof.Curve448.AArch64.Swap

/-!
# X448 on AArch64: chains of field operations

Untrusted: everything here is checked by Lean. What a chain of products,
copies and repeated squarings with the faster field operations computes
(`ISpec`, `opsI`, `sqnI`), and the conditional swap (`cswapE`), apart from
the ladder's proofs, so that other chains (Ed448's square root) do not import
the ladder's AdvSIMD arithmetic.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot mask)
open VG.Proof.X448.AArch64.Weak (Index Env setCounter_ok decCounter_ok opMul opCopy opSqn opMul_update
  FieldOp applyOps invEnv opSwap)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

structure IKeep (base : Addr) (s t : State) : Prop where
  regs : Keeps (.x19 :: fclob) s t
  mem : Outside2 base 64 2816 ACC 1152 s.mem t.mem

theorem IKeep.trans {base : Addr} {s t u : State} (h : IKeep base s t) (h' : IKeep base t u) :
    IKeep base s u := ⟨h.regs.trans h'.regs, h.mem.trans h'.mem⟩

theorem IKeep.scr {base : Addr} {s t : State} (h : IKeep base s t) (hs : Scr s base) : Scr t base :=
  hs.of_keeps h.regs (by decide)

theorem FKeep.ikeep {base : Addr} {s t : State} (h : FKeep base s t) : IKeep base s t :=
  ⟨h.regs.mono (fun _ hr => List.mem_cons_of_mem _ hr), h.mem⟩

theorem counter_keep {base : Addr} {s t : State} (hg : ∀ r, r ≠ .x19 → t.gpr r = s.gpr r)
    (hm : t.mem = s.mem) (hr : t.rd = s.rd) (hw : t.wr = s.wr) : IKeep base s t :=
  ⟨⟨fun r h => hg r (fun he => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
    hm ▸ Outside2.refl _ _ _ _ _ _⟩

def ISpec (base : Addr) (code : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Scr s base → BEnv s.mem base → WP isa code s fun t =>
    IKeep base s t ∧ BEnv t.mem base ∧ EV t.mem base = f (EV s.mem base)

theorem ISpec.seq {base : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : ISpec base c₁ f) (h₂ : ISpec base c₂ g) :
    ISpec base (.seq c₁ c₂) (fun e => g (f e)) := fun s hs hb =>
  WP.seq (WP.mono (h₁ s hs hb) fun t ⟨tk, tb, te⟩ =>
    WP.mono (h₂ t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.trans uk, ub, by rw [ue, te]⟩)

/-- The inversion's operations: products and copies. -/
def fimpl : FieldOp → Impl.X448.AArch64.Fast.Op
  | .mul o a b => .mul (slot o.val) (slot a.val) (slot b.val)
  | .copy o a => .copy (slot o.val) (slot a.val)
  | _ => .copy 0 0

def MulCopy : FieldOp → Prop
  | .mul o a b => a = b ∨ o ≠ b
  | .copy .. => True
  | _ => False

theorem opsI (base : Addr) (xs : List FieldOp) (hx : ∀ x ∈ xs, MulCopy x) :
    ISpec base (Impl.X448.AArch64.Fast.ops (xs.map fimpl)) (applyOps xs) := by
  induction xs with
  | nil => exact fun s _ hb => WP.block_nil ⟨⟨Keeps.refl _ _, Outside2.refl _ _ _ _ _ _⟩, hb, rfl⟩
  | cons x xs ih =>
    intro s hs hb
    have ih' := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    refine WP.seq ?_
    cases x with
    | mul o a b =>
      refine WP.mono (fmulE hs hb o a b (hx _ List.mem_cons_self)) fun t ⟨tk, tb, _, _, te⟩ =>
        WP.mono (ih' t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.ikeep.trans uk, ub, ?_⟩
      rw [ue, te]; rfl
    | copy o a =>
      refine WP.mono (copyE hs hb o a) fun t ⟨tk, tb, _, _, te⟩ =>
        WP.mono (ih' t (tk.scr hs) tb) fun u ⟨uk, ub, ue⟩ => ⟨tk.ikeep.trans uk, ub, ?_⟩
      rw [ue, te]; rfl
    | _ => exact absurd (hx _ List.mem_cons_self) (by simp [MulCopy])

theorem sqnI (base : Addr) (o : Index) {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 16) :
    ISpec base (Impl.X448.AArch64.Fast.sqn (slot o.val) n) (opSqn o n) := by
  intro s hs hb
  rw [Impl.X448.AArch64.Fast.sqn, WP.seq_iff]
  refine WP.mono (setCounter_ok s n hn') fun t ⟨tc, tg, tm, tr, tw⟩ => ?_
  have kt : IKeep base s t := counter_keep tg tm tr tw
  let inv := fun m (u : State) => 1 ≤ m ∧ m ≤ n ∧ IKeep base s u ∧ BEnv u.mem base ∧
    u.gpr .x19 = BitVec.ofNat 64 m ∧
    EV u.mem base = Function.update (EV s.mem base) o (Proof.X448.sqn (EV s.mem base o) (n - m))
  refine WP.loop (M := isa) inv ?_ n t ?_
  · intro m u ⟨hm, hm', ku, bu, cu, eu⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [WP.block_append_iff]
    have hsq : Impl.Curve448.AArch64.Fast.sqr (slot o.val) (slot o.val) =
        Impl.X448.AArch64.Fast.fmul (slot o.val) (slot o.val) (slot o.val) := by
      simp only [Impl.X448.AArch64.Fast.fmul, ite_true]
    rw [hsq]
    refine WP.mono (fmulE (ku.scr hs) bu o o o (Or.inl rfl)) fun v ⟨kv, bv, _, _, ev⟩ => ?_
    have cv : v.gpr .x19 = BitVec.ofNat 64 (m + 1) := (kv.regs.1 _ (by decide)).trans cu
    refine WP.mono (decCounter_ok (by omega) cv) fun w ⟨cw, wg, wm, wr, ww, wz⟩ => ?_
    have kw : IKeep base s w := ku.trans (kv.ikeep.trans (counter_keep wg wm wr ww))
    have bw : BEnv w.mem base := wm ▸ bv
    have ew : EV w.mem base = Function.update (EV s.mem base) o (Proof.X448.sqn (EV s.mem base o) (n - m)) := by
      rw [wm, ev, eu]
      simp only [VG.Proof.X448.AArch64.opMul, Function.update_self, Function.update_idem]
      rw [← Proof.X448.sqn]
      rw [show (n - (m + 1)).succ = n - m by omega]
    simp only [eval, State.read, BitVec.setWidth_eq, bne, wz]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, kw, bw, ew⟩
    · refine Or.inr ⟨?_, m, by omega, hm, by omega, kw, bw, cw, ew⟩
      rw [decide_eq_false (by omega : ¬m = 0)]; rfl
  · refine ⟨hn, by omega, kt, tm ▸ hb, tc, ?_⟩
    rw [tm, Nat.sub_self, Proof.X448.sqn, Function.update_eq_self]

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (x y : Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot x.val) (slot y.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ t.gpr .x6 = s.gpr .x6 ∧
      (∀ j < 8, limbs t.mem base (slot x.val) j = if sw then limbs s.mem base (slot y.val) j
        else limbs s.mem base (slot x.val) j) ∧
      (∀ j < 8, limbs t.mem base (slot y.val) j = if sw then limbs s.mem base (slot x.val) j
        else limbs s.mem base (slot y.val) j) ∧
      Same base [x, y] s.mem t.mem ∧ EV t.mem base = opSwap x y sw (EV s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.cswap_ok hs (VG.Proof.X448.AArch64.Weak.slot_bound x)
    (VG.Proof.X448.AArch64.Weak.slot_bound y) (VG.Proof.X448.AArch64.Weak.slot_aligned x)
    (VG.Proof.X448.AArch64.Weak.slot_aligned y) (VG.Proof.X448.AArch64.Weak.slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have sm : Same base [x, y] s.mem t.mem := by
    intro i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    have ex := VG.Proof.X448.AArch64.Weak.slot_sep hi.1
    have ey := VG.Proof.X448.AArch64.Weak.slot_sep hi.2
    have hi' := VG.Proof.X448.AArch64.Weak.slot_bound i
    change (word t.mem base (slot i.val + 8 * j)).toNat = _
    rw [tm.word (by omega) (by omega) (by change slot i.val + 128 ≤ 3584 at hi'; omega)]
  have fx : EV t.mem base x = if sw then EV s.mem base y else EV s.mem base x := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.Wide.valN_congr <;> exact tx
  have fy : EV t.mem base y = if sw then EV s.mem base x else EV s.mem base y := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.Wide.valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, fun i => ?_, tk.1 _ (by decide), tx, ty, sm, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega
  · by_cases hix : i = x
    · subst i; intro j hj; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; intro j hj; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · exact sm.bnd (by simp [hix, hiy]) (hb i)
  · funext i
    by_cases hiy : i = y
    · subst i; rw [opSwap, Function.update_self]; exact fy
    · rw [opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact sm.env (by simp [hix, hiy])

end VG.Proof.X448.AArch64.Fast
