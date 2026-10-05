import VerifiedGarbage.Impl.ChaCha20.AArch64.Neon4
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64

theorem vword_rev32h_rol16 (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (VRevOp.rev32h.eval x) e = (vword x e).rotateLeft 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, VRevOp.eval,
    BitVec.getLsbD_rotateLeft]
  rw [show 32 * e + i = 8 * (4 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (by omega)]
  simp only [vbyte, BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true, Bool.true_and]
  simp only [Nat.reduceMod]
  split
  · simp only [show 32 - 16 + i < 32 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  · simp only [show i - 16 < 32 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)

theorem rol8_index (i : Fin 16) :
    (vbyte VG.Impl.ChaCha20.AArch64.Neon4.rol8Table i).toNat =
      4 * (i.val / 4) + (i.val + 3) % 4 :=
  (show ∀ i : Fin 16, (vbyte VG.Impl.ChaCha20.AArch64.Neon4.rol8Table i).toNat =
      4 * (i.val / 4) + (i.val + 3) % 4 by decide +kernel) i

theorem vword_tbl_rol8 (x : BitVec 128) {e : Nat} (he : e < 4) :
    vword (ofVBytes fun j =>
      let idx := (vbyte VG.Impl.ChaCha20.AArch64.Neon4.rol8Table j).toNat
      if idx < 16 then vbyte x idx else 0) e = (vword x e).rotateLeft 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    BitVec.getLsbD_rotateLeft]
  rw [show 32 * e + i = 8 * (4 * e + i / 8) + i % 8 by omega,
    getLsbD_ofVBytes _ (by omega) (by omega)]
  rw [VG.Proof.ChaCha20.AArch64.Neon4.rol8_index ⟨4 * e + i / 8, by omega⟩]
  have hidx : 4 * ((4 * e + i / 8) / 4) + (4 * e + i / 8 + 3) % 4 < 16 := by omega
  simp only [hidx, ite_true, vbyte, BitVec.getLsbD_extractLsb',
    show i % 8 < 8 by omega, decide_true, Bool.true_and, Nat.reduceMod]
  split
  · simp only [show 32 - 8 + i < 32 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)
  · simp only [show i - 8 < 32 by omega, decide_true, Bool.true_and]
    exact congrArg x.getLsbD (by omega)

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

theorem vreg_inj (a b : Fin 16) : VG.Impl.ChaCha20.AArch64.Neon4.vreg a = VG.Impl.ChaCha20.AArch64.Neon4.vreg b ↔ a = b :=
  (show ∀ a b : Fin 16, VG.Impl.ChaCha20.AArch64.Neon4.vreg a = VG.Impl.ChaCha20.AArch64.Neon4.vreg b ↔ a = b by decide) a b

theorem vreg_ne (a : Fin 16) : VG.Impl.ChaCha20.AArch64.Neon4.vreg a ≠ .v31 :=
  (show ∀ a : Fin 16, VG.Impl.ChaCha20.AArch64.Neon4.vreg a ≠ .v31 by decide) a

theorem vreg_ne30 (a : Fin 16) : VG.Impl.ChaCha20.AArch64.Neon4.vreg a ≠ .v30 :=
  (show ∀ a : Fin 16, VG.Impl.ChaCha20.AArch64.Neon4.vreg a ≠ .v30 by decide) a

def Holds (vs : Nat → CState) (s : State) : Prop :=
  ∀ k : Fin 16, ∀ j, j < 4 → vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j = (vs j)[k]

structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Same.trans {s₀ s₁ s₂ : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.Same s₀ s₁) (h' : VG.Proof.ChaCha20.AArch64.Neon4.Same s₁ s₂) : VG.Proof.ChaCha20.AArch64.Neon4.Same s₀ s₂ :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

structure RoundSame (s s' : State) : Prop extends VG.Proof.ChaCha20.AArch64.Neon4.Same s s' where
  v30 : s'.v .v30 = s.v .v30

theorem RoundSame.trans {s₀ s₁ s₂ : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.RoundSame s₀ s₁) (h' : VG.Proof.ChaCha20.AArch64.Neon4.RoundSame s₁ s₂) :
    VG.Proof.ChaCha20.AArch64.Neon4.RoundSame s₀ s₂ := ⟨h.toSame.trans h'.toSame, h'.v30.trans h.v30⟩

def step (v : CState) : VG.Impl.ChaCha20.AArch64.Neon4.Op → CState
  | .add d a b => v.set d (v[a] + v[b])
  | .xorRol d a b n => v.set d ((v[a] ^^^ v[b]).rotateLeft n)

theorem get_set (v : CState) (d k : Fin 16) (x : Word) :
    (v.set d x)[k] = if k = d then x else v[k] := by
  simp only [Vector.getElem_set, Fin.getElem_fin, Fin.ext_iff, eq_comm]

theorem op_ok (op : VG.Impl.ChaCha20.AArch64.Neon4.Op) {vs : Nat → CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = rol8Table) :
    WP isa (.block op.code) s fun s' => VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => VG.Proof.ChaCha20.AArch64.Neon4.step (vs j) op) s' ∧ VG.Proof.ChaCha20.AArch64.Neon4.RoundSame s s' := by
  cases op with
  | add d a b =>
    apply WP.of_runBlock
    simp only [Op.code, runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp only [↓reduceIte, RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne30 d)]⟩⟩
    simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Neon4.step, VG.Proof.ChaCha20.AArch64.Neon4.get_set, VG.Proof.ChaCha20.AArch64.Neon4.vreg_inj]
    split
    · rw [vword_map2 _ _ _ hj, h a j hj, h b j hj]
    · exact h k j hj
  | xorRol d a b n =>
    by_cases h16 : n.val = 16
    · apply WP.of_runBlock
      simp only [Op.code, h16, ite_true, List.cons_append, List.nil_append,
        runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV]
      refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp only [reduceCtorEq, ↓reduceIte, RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne30 d)]⟩⟩
      simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne, ite_false, VG.Proof.ChaCha20.AArch64.Neon4.step, VG.Proof.ChaCha20.AArch64.Neon4.get_set, VG.Proof.ChaCha20.AArch64.Neon4.vreg_inj]
      split
      · rw [VG.Proof.ChaCha20.AArch64.Neon4.vword_rev32h_rol16 _ hj, Neon.vword_xor, h a j hj, h b j hj, h16]
      · exact h k j hj
    by_cases h8 : n.val = 8
    · apply WP.of_runBlock
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceEqDiff, Op.code, h8, List.cons_append, List.nil_append,
        runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV]
      refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
        by simp only [reduceCtorEq, ↓reduceIte, RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne30 d)]⟩⟩
      simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne, ite_false, VG.Proof.ChaCha20.AArch64.Neon4.step, VG.Proof.ChaCha20.AArch64.Neon4.get_set, VG.Proof.ChaCha20.AArch64.Neon4.vreg_inj]
      split
      · rw [ht, VG.Proof.ChaCha20.AArch64.Neon4.vword_tbl_rol8 _ hj, Neon.vword_xor, h a j hj, h b j hj, h8]
      · exact h k j hj
    have hn : n.val < 32 := n.isLt
    have hsh : VShiftOp.ushr.ok VArr.s4.esize (32 - n.val) = true := by
      simp only [VShiftOp.ok, VArr.esize, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hsl : VShiftOp.sli.ok VArr.s4.esize n.val = true := by
      simp only [VShiftOp.ok, VArr.esize, decide_eq_true_eq]; exact hn
    apply WP.of_runBlock
    simp only [Op.code, h16, h8, ite_false, List.cons_append, List.nil_append,
      runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      hsh, hsl, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
      RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne, Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne d), ite_false]
    refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp only [reduceCtorEq, ↓reduceIte, RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne30 d)]⟩⟩
    simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne, ite_false, VG.Proof.ChaCha20.AArch64.Neon4.step, VG.Proof.ChaCha20.AArch64.Neon4.get_set, VG.Proof.ChaCha20.AArch64.Neon4.vreg_inj]
    split
    · rw [vword_map2 _ _ _ hj, vword_map2 _ _ _ hj]
      simp only [VShiftOp.eval, Neon.shr_mask _ n hn, Neon.vword_xor,
        h a j hj, h b j hj, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn, BitVec.or_comm]
    · exact h k j hj

theorem ops_ok : ∀ (ops : List VG.Impl.ChaCha20.AArch64.Neon4.Op) {vs : Nat → CState} {s : State}, VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s → s.v .v30 = rol8Table →
    WP isa (.block (ops.flatMap Op.code)) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => ops.foldl VG.Proof.ChaCha20.AArch64.Neon4.step (vs j)) s' ∧ VG.Proof.ChaCha20.AArch64.Neon4.RoundSame s s'
  | [], _, _, h, _ => WP.block_nil ⟨h, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  | op :: ops, _, _, h, ht => by
    exact WP.block_append ((VG.Proof.ChaCha20.AArch64.Neon4.op_ok op h ht).mono fun _ ⟨h', hs⟩ =>
      (VG.Proof.ChaCha20.AArch64.Neon4.ops_ok ops h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

/-- A term in the words `var k` of a state. -/
inductive E
  | var (k : Nat) | add (a b : VG.Proof.ChaCha20.AArch64.Neon4.E) | xor (a b : VG.Proof.ChaCha20.AArch64.Neon4.E) | rol (a : VG.Proof.ChaCha20.AArch64.Neon4.E) (n : Nat)
  deriving DecidableEq

def E.eval (v : CState) : VG.Proof.ChaCha20.AArch64.Neon4.E → Word
  | .var k => if h : k < 16 then v[k] else 0
  | .add a b => a.eval v + b.eval v
  | .xor a b => a.eval v ^^^ b.eval v
  | .rol a n => (a.eval v).rotateLeft n

/-- A state of terms. -/
abbrev ES := Nat → VG.Proof.ChaCha20.AArch64.Neon4.E

def ES.set (f : VG.Proof.ChaCha20.AArch64.Neon4.ES) (i : Nat) (x : VG.Proof.ChaCha20.AArch64.Neon4.E) : VG.Proof.ChaCha20.AArch64.Neon4.ES := fun k => if k = i then x else f k

/-- The scheduled operations on symbolic words. -/
def stepE (f : VG.Proof.ChaCha20.AArch64.Neon4.ES) : VG.Impl.ChaCha20.AArch64.Neon4.Op → VG.Proof.ChaCha20.AArch64.Neon4.ES
  | .add d a b => f.set d (.add (f a) (f b))
  | .xorRol d a b n => f.set d (.rol (.xor (f a) (f b)) n)

/-- `qround` on terms. -/
def qroundE (f : VG.Proof.ChaCha20.AArch64.Neon4.ES) (x y z w : Fin 16) : VG.Proof.ChaCha20.AArch64.Neon4.ES :=
  let a := E.add (f x) (f y); let d := E.rol (.xor (f w) a) 16
  let c := E.add (f z) d; let b := E.rol (.xor (f y) c) 12
  let a := E.add a b; let d := E.rol (.xor d a) 8
  let c := E.add c d; let b := E.rol (.xor b c) 7
  (((f.set x a).set y b).set z c).set w d

/-- The terms `f` evaluate to `v`, in the words of `v₀`. -/
def Rel (v₀ : CState) (f : VG.Proof.ChaCha20.AArch64.Neon4.ES) (v : CState) : Prop := ∀ k (hk : k < 16), (f k).eval v₀ = v[k]

theorem Rel.set {v₀ : CState} {f : VG.Proof.ChaCha20.AArch64.Neon4.ES} {v : CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ f v) {i : Nat} (hi : i < 16) {x : VG.Proof.ChaCha20.AArch64.Neon4.E}
    {y : Word} (hx : x.eval v₀ = y) : VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ (f.set i x) (v.set i y hi) := by
  intro k hk
  simp only [ES.set, Vector.getElem_set]
  by_cases e : k = i
  · subst e; simp [hx]
  · simp only [e, ite_false, Ne.symm e]; exact h k hk

theorem Rel.step {v₀ : CState} {f : VG.Proof.ChaCha20.AArch64.Neon4.ES} {v : CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ f v) (i : VG.Impl.ChaCha20.AArch64.Neon4.Op) :
    VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ (VG.Proof.ChaCha20.AArch64.Neon4.stepE f i) (VG.Proof.ChaCha20.AArch64.Neon4.step v i) := by
  cases i with
  | add d a b => exact h.set d.isLt (by simp only [E.eval, h _ a.isLt, h _ b.isLt, Fin.getElem_fin])
  | xorRol d a b n => exact h.set d.isLt (by simp only [E.eval, h _ a.isLt, h _ b.isLt, Fin.getElem_fin])

theorem Rel.foldl {v₀ : CState} {f : VG.Proof.ChaCha20.AArch64.Neon4.ES} {v : CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ f v) :
    ∀ is : List VG.Impl.ChaCha20.AArch64.Neon4.Op, VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ (is.foldl VG.Proof.ChaCha20.AArch64.Neon4.stepE f) (is.foldl Neon4.step v)
  | [] => h
  | i :: is => (h.step i).foldl is

theorem Rel.qround {v₀ : CState} {f : VG.Proof.ChaCha20.AArch64.Neon4.ES} {v : CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ f v) (x y z w : Fin 16) :
    VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ (VG.Proof.ChaCha20.AArch64.Neon4.qroundE f x y z w) (VG.Spec.ChaCha20.qround v x y z w) := by
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.qroundE]
  refine (((h.set x.2 ?_).set y.2 ?_).set z.2 ?_).set w.2 ?_ <;>
    simp only [E.eval, h _ x.2, h _ y.2, h _ z.2, h _ w.2, Fin.getElem_fin]

/-- The words of a state, as terms. -/
def vars : VG.Proof.ChaCha20.AArch64.Neon4.ES := .var

theorem rel_vars (v : CState) : VG.Proof.ChaCha20.AArch64.Neon4.Rel v VG.Proof.ChaCha20.AArch64.Neon4.vars v := fun k hk => by simp [VG.Proof.ChaCha20.AArch64.Neon4.vars, E.eval, hk]

theorem Rel.eq {v₀ : CState} {f : VG.Proof.ChaCha20.AArch64.Neon4.ES} {v v' : CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ f v) (h' : VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ f v') : v = v' :=
  Vector.ext fun k hk => (h k hk).symm.trans (h' k hk)

/-- Two states of terms agree on the words of a state. -/
def ES.eq16 (f g : VG.Proof.ChaCha20.AArch64.Neon4.ES) : Bool := (List.range 16).all fun k => f k == g k

theorem Rel.of_eq16 {v₀ : CState} {f g : VG.Proof.ChaCha20.AArch64.Neon4.ES} {v : CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ f v) (e : ES.eq16 f g = true) :
    VG.Proof.ChaCha20.AArch64.Neon4.Rel v₀ g v := by
  intro k hk
  simp only [ES.eq16, List.all_eq_true, List.mem_range, beq_iff_eq] at e
  rw [← e k hk]; exact h k hk

theorem cols_eq (v : CState) :
    (quarters cols).foldl VG.Proof.ChaCha20.AArch64.Neon4.step v =
      VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround v 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15 := by
  have e : ES.eq16 ((quarters cols).foldl VG.Proof.ChaCha20.AArch64.Neon4.stepE VG.Proof.ChaCha20.AArch64.Neon4.vars)
      (VG.Proof.ChaCha20.AArch64.Neon4.qroundE (VG.Proof.ChaCha20.AArch64.Neon4.qroundE (VG.Proof.ChaCha20.AArch64.Neon4.qroundE (VG.Proof.ChaCha20.AArch64.Neon4.qroundE VG.Proof.ChaCha20.AArch64.Neon4.vars 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15) = true := by
    decide +kernel
  exact (((VG.Proof.ChaCha20.AArch64.Neon4.rel_vars v).foldl _).of_eq16 e).eq
    ((((VG.Proof.ChaCha20.AArch64.Neon4.rel_vars v).qround 0 4 8 12).qround 1 5 9 13 |>.qround 2 6 10 14).qround 3 7 11 15)

theorem diags_eq (v : CState) :
    (quarters diags).foldl VG.Proof.ChaCha20.AArch64.Neon4.step v =
      VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround (VG.Spec.ChaCha20.qround v 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14 := by
  have e : ES.eq16 ((quarters diags).foldl VG.Proof.ChaCha20.AArch64.Neon4.stepE VG.Proof.ChaCha20.AArch64.Neon4.vars)
      (VG.Proof.ChaCha20.AArch64.Neon4.qroundE (VG.Proof.ChaCha20.AArch64.Neon4.qroundE (VG.Proof.ChaCha20.AArch64.Neon4.qroundE (VG.Proof.ChaCha20.AArch64.Neon4.qroundE VG.Proof.ChaCha20.AArch64.Neon4.vars 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14) = true := by
    decide +kernel
  exact (((VG.Proof.ChaCha20.AArch64.Neon4.rel_vars v).foldl _).of_eq16 e).eq
    ((((VG.Proof.ChaCha20.AArch64.Neon4.rel_vars v).qround 0 5 10 15).qround 1 6 11 12 |>.qround 2 7 8 13).qround 3 4 9 14)

theorem innerBlock_eq (v : CState) : (quarters cols ++ quarters diags).foldl VG.Proof.ChaCha20.AArch64.Neon4.step v = innerBlock v := by
  rw [List.foldl_append, VG.Proof.ChaCha20.AArch64.Neon4.cols_eq, VG.Proof.ChaCha20.AArch64.Neon4.diags_eq]; rfl


theorem doubleRound_ok {vs : Nat → CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = rol8Table) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Neon4.doubleRound) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => innerBlock (vs j)) s' ∧ VG.Proof.ChaCha20.AArch64.Neon4.RoundSame s s' := by
  have e : (fun j => (quarters cols ++ quarters diags).foldl VG.Proof.ChaCha20.AArch64.Neon4.step (vs j)) =
      fun j => innerBlock (vs j) := funext fun j => VG.Proof.ChaCha20.AArch64.Neon4.innerBlock_eq (vs j)
  exact (VG.Proof.ChaCha20.AArch64.Neon4.ops_ok _ h ht).mono fun _ ⟨h', hs⟩ => ⟨e ▸ h', hs⟩

theorem rounds_ok {vs : Nat → CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s) (ht : s.v .v30 = rol8Table) :
    ∀ n, WP isa (VG.Impl.ChaCha20.AArch64.Neon4.rounds n) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock n (vs j)) s' ∧ VG.Proof.ChaCha20.AArch64.Neon4.RoundSame s s'
  | 0 => WP.block_nil ⟨h, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  | n + 1 => WP.seq ((VG.Proof.ChaCha20.AArch64.Neon4.rounds_ok h ht n).mono fun _ ⟨h', hs⟩ =>
      (VG.Proof.ChaCha20.AArch64.Neon4.doubleRound_ok h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (Word stateAt)

theorem vword_dup (w : Word) {j : Nat} (hj : j < 4) : vword (ofVWords w w w w) j = w := by
  rw [vword_ofVWords _ _ _ _ hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem vword_insert (v : BitVec 128) (w : Word) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    vword (setLane v 32 i w) j = if j = i then w else vword v j := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
    BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hb, decide_true, Bool.true_and]
  by_cases h : j = i
  · subst h
    simp (disch := omega) [Nat.add_sub_cancel_left, decide_eq_true, decide_eq_false]
  · by_cases hlt : j < i
    · simp (disch := omega) [h, decide_eq_true]
    · simp (disch := omega) [h, decide_eq_true, decide_eq_false,
        BitVec.getLsbD_of_ge]

structure LoadSame (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem LoadSame.refl (s : State) : VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem LoadSame.trans {s₀ s₁ s₂ : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s₀ s₁) (h' : VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s₁ s₂) :
    VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s₀ s₂ := ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr),
      h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

def input (s : State) (k : Fin 16) (j : Nat) : Word :=
  let w := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 32
  if k = 12 then w + BitVec.ofNat 32 j else w

theorem input_same {s s' : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s') (k : Fin 16) (j : Nat) :
    VG.Proof.ChaCha20.AArch64.Neon4.input s' k j = VG.Proof.ChaCha20.AArch64.Neon4.input s k j := by rw [VG.Proof.ChaCha20.AArch64.Neon4.input, h.mem, h.gpr _ (by decide)]; rfl

theorem inputWordInto_ok (s : State) (k : Fin 16) (d : VReg)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (inputWordInto k d)) s fun s' =>
      (∀ j, j < 4 → vword (s'.v d) j = VG.Proof.ChaCha20.AArch64.Neon4.input s k j) ∧
      (∀ r, r ≠ d → s'.v r = s.v r) ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s' := by
  have ha : 4 * k.val % 4 = 0 ∧ 4 * k.val < 4096 * 4 := by omega
  unfold inputWordInto
  split
  · rename_i hk
    subst k
    apply WP.of_runBlock
    simp (config := {decide := true}) only [List.cons_append, List.nil_append,
      runBlock_cons, runBlock_nil, exec, addr, Size.bytes, ite_true,
      State.load, hin, Option.bind_some, Option.map_some, isa, runStep_some,
      Option.some.injEq, exists_eq_left', VOp.eval, State.read,
      RegUpd.gpr_write, RegUpd.gpr_setV, RegUpd.v_write, RegUpd.v_setV,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    refine ⟨fun j hj => ?_, fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [VG.Proof.ChaCha20.AArch64.Neon4.vword_insert _ _ (i := 3) (by decide) hj,
        VG.Proof.ChaCha20.AArch64.Neon4.vword_insert _ _ (i := 2) (by decide) hj,
        VG.Proof.ChaCha20.AArch64.Neon4.vword_insert _ _ (i := 1) (by decide) hj, VG.Proof.ChaCha20.AArch64.Neon4.vword_dup _ hj, VG.Proof.ChaCha20.AArch64.Neon4.input,
        ite_true, Mem.readW, BitVec.setWidth_eq]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
        simp (config := {decide := true}) [Size.bits, BitVec.add_assoc]
    · simp only [hr, ite_false]
    · simp only [RegUpd.gpr_setV, RegUpd.gpr_write, hr, ite_false]
  · rename_i hk
    apply WP.of_runBlock
    simp only [List.append_nil, runBlock_cons, runBlock_nil, exec, addr, Size.bytes,
      ha, and_self, ite_true, State.load, hin, Option.bind_some, Option.map_some,
      isa, runStep_some, Option.some.injEq, exists_eq_left', VOp.eval,
      RegUpd.gpr_write_self, BitVec.setWidth_eq]
    refine ⟨fun j hj => ?_, fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · rw [RegUpd.v_setV_self, VG.Proof.ChaCha20.AArch64.Neon4.vword_dup _ hj]
      simp only [VG.Proof.ChaCha20.AArch64.Neon4.input, hk, ite_false, Mem.readW,
        BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
    · exact RegUpd.v_setV_of_ne _ _ hr
    · exact RegUpd.gpr_write_of_ne _ _ _ hr


theorem inputWord_ok (s : State) (k : Fin 16)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (inputWord k)) s fun s' =>
      (∀ j, j < 4 → vword (s'.v .v31) j = VG.Proof.ChaCha20.AArch64.Neon4.input s k j) ∧
      (∀ r, r ≠ .v31 → s'.v r = s.v r) ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s' :=
  VG.Proof.ChaCha20.AArch64.Neon4.inputWordInto_ok s k .v31 hin

structure Loaded (s₀ : State) (ks : List (Fin 16)) (s : State) : Prop where
  words : ∀ k ∈ ks, ∀ j, j < 4 → vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j = VG.Proof.ChaCha20.AArch64.Neon4.input s₀ k j
  same : VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s₀ s

theorem setupWord_ok {s₀ s : State} {ks : List (Fin 16)} (h : VG.Proof.ChaCha20.AArch64.Neon4.Loaded s₀ ks s) (k : Fin 16)
    (hin : ∀ k : Fin 16, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (setupWord k)) s (VG.Proof.ChaCha20.AArch64.Neon4.Loaded s₀ (k :: ks)) := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [h.same.rd, h.same.wr, h.same.gpr _ (by decide)]; exact hin k
  refine (VG.Proof.ChaCha20.AArch64.Neon4.inputWordInto_ok s k (VG.Impl.ChaCha20.AArch64.Neon4.vreg k) hi).mono fun s' ⟨hw, hv, hs⟩ => ?_
  refine ⟨fun l hl j hj => ?_, h.same.trans hs⟩
  by_cases e : l = k
  · subst e; rw [hw j hj, VG.Proof.ChaCha20.AArch64.Neon4.input_same h.same]
  · rw [hv _ (fun he => e ((VG.Proof.ChaCha20.AArch64.Neon4.vreg_inj l k).mp he))]
    exact h.words l ((List.mem_cons.mp hl).resolve_left e) j hj

theorem setupList_ok (ks : List (Fin 16)) {s₀ s : State} {done : List (Fin 16)}
    (h : VG.Proof.ChaCha20.AArch64.Neon4.Loaded s₀ done s)
    (hin : ∀ k : Fin 16, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (ks.flatMap setupWord)) s fun s' =>
      (∀ k ∈ ks ++ done, ∀ j, j < 4 → vword (s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j = VG.Proof.ChaCha20.AArch64.Neon4.input s₀ k j) ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s₀ s' := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨h.words, h.same⟩
  | cons k ks ih =>
    refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Neon4.setupWord_ok h k hin).mono fun _ h' => ?_)
    exact (ih h').mono fun _ ⟨hw, hs⟩ => ⟨fun l hl j hj => hw l (by simpa [List.mem_append,
      List.mem_cons, or_assoc, or_left_comm, or_comm] using hl) j hj, hs⟩

theorem setupTable_ok (s : State) :
    WP isa (.block setupTable) s fun s' =>
      s'.v .v30 = rol8Table ∧ (∀ r, r ≠ .v30 → s'.v r = s.v r) ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s' := by
  apply WP.of_runBlock
  simp only [setupTable, runBlock_cons, runBlock_nil, isa,
    runStep_some, exec, State.read, Size.bits, BitVec.setWidth_eq, VOp.eval,
    RegUpd.gpr_write, RegUpd.v_write, RegUpd.v_setV,
    Option.map_some, Option.some.injEq, exists_eq_left', ↓reduceIte, Nat.reduceMul, Nat.reduceLT]
  refine ⟨?_, fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · trivial
  · simp only [hr, ite_false]
  · simp only [RegUpd.gpr_write, RegUpd.gpr_setV, hr, ite_false]

theorem setup_ok (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Neon4.setup) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => ctr (stateAt s.mem (s.gpr .x0)) j) s' ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s' ∧
      s'.v .v30 = rol8Table := by
  rw [VG.Impl.ChaCha20.AArch64.Neon4.setup]
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Neon4.setupList_ok (List.finRange 16) (done := [])
    ⟨(fun _ h => by cases h), LoadSame.refl s⟩ hin).mono fun a ⟨hw, hs⟩ => ?_)
  refine (VG.Proof.ChaCha20.AArch64.Neon4.setupTable_ok a).mono fun b ⟨ht, hk, hab⟩ => ⟨?_, hs.trans hab, ht⟩
  intro k j hj
  rw [hk (VG.Impl.ChaCha20.AArch64.Neon4.vreg k) (VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne30 k), hw k (by simp) j hj]
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.input, ctr, Vector.getElem_set, stateAt, Vector.getElem_ofFn, Fin.getElem_fin]
  by_cases hk : k = 12
  · subst k; rfl
  · have hk' : k.val ≠ 12 := fun e => hk (Fin.ext e)
    simp only [hk, Ne.symm hk', ite_false]

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

/-- ZIP's word arrangement, without widening and narrowing its lanes. -/
theorem zip1_s4 (x y : BitVec 128) :
    VPermOp.eval .zip1 .s4 x y = ofVWords (vword x 0) (vword y 0) (vword x 1) (vword y 1) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.range_succ, List.getD]

theorem zip2_s4 (x y : BitVec 128) :
    VPermOp.eval .zip2 .s4 x y = ofVWords (vword x 2) (vword y 2) (vword x 3) (vword y 3) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.range_succ, List.getD]

theorem zip1_d2 (x y : BitVec 128) :
    VPermOp.eval .zip1 .d2 x y = ofVWords (vword x 0) (vword x 1) (vword y 0) (vword y 1) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.range_succ, List.getD]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords, ofVWords, vdword, vword, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  simp only [Nat.reduceMul, Nat.zero_add]
  by_cases h : i < 64
  · by_cases h' : i < 32
    · simp (disch := omega) only [ite_eq_left, decide_eq_true, Bool.true_and]
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega
  · by_cases h' : i < 96
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega
    · simp (disch := omega) only [ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega

theorem zip2_d2 (x y : BitVec 128) :
    VPermOp.eval .zip2 .d2 x y = ofVWords (vword x 2) (vword x 3) (vword y 2) (vword y 3) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes, List.range_succ, List.getD]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofVDwords, ofVWords, vdword, vword, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb']
  simp only [Nat.reduceMul]
  by_cases h : i < 64
  · by_cases h' : i < 32
    · simp (disch := omega) only [ite_eq_left, decide_eq_true, Bool.true_and]
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega
  · by_cases h' : i < 96
    · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega
    · simp (disch := omega) only [ite_eq_right, decide_eq_true, Bool.true_and]
      congr 1 <;> omega

theorem rowWord_inj (r i j : Fin 4) : rowWord r i = rowWord r j ↔ i = j := by
  simp only [rowWord, Fin.ext_iff]; omega

theorem vreg_scratch (k : Fin 16) :
    VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v24 ∧ VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v25 ∧ VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v26 ∧ VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v27 :=
  (show ∀ k : Fin 16, VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v24 ∧ VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v25 ∧ VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v26 ∧ VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v27
    by decide) k

def transposed (s : State) (r j : Fin 4) : BitVec 128 :=
  ofVWords (vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0))) j) (vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 1))) j)
    (vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 2))) j) (vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 3))) j)

structure TPrep (s₀ : State) (r : Fin 4) (s : State) : Prop where
  t24 : s.v .v24 = VPermOp.eval .zip1 .s4 (s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0))) (s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 1)))
  t25 : s.v .v25 = VPermOp.eval .zip2 .s4 (s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0))) (s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 1)))
  t26 : s.v .v26 = VPermOp.eval .zip1 .s4 (s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 2))) (s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 3)))
  t27 : s.v .v27 = VPermOp.eval .zip2 .s4 (s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 2))) (s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 3)))
  keep : ∀ k : Fin 16, s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k) = s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)
  same : VG.Proof.ChaCha20.AArch64.Neon4.Same s₀ s

theorem transposePrep_ok (s : State) (r : Fin 4) :
    WP isa (.block (transposePrep (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0)) (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 1))
      (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 2)) (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 3)))) s (VG.Proof.ChaCha20.AArch64.Neon4.TPrep s r) := by
  have hn0 := fun k => (VG.Proof.ChaCha20.AArch64.Neon4.vreg_scratch k).1
  have hn1 := fun k => (VG.Proof.ChaCha20.AArch64.Neon4.vreg_scratch k).2.1
  have hn2 := fun k => (VG.Proof.ChaCha20.AArch64.Neon4.vreg_scratch k).2.2.1
  have hn3 := fun k => (VG.Proof.ChaCha20.AArch64.Neon4.vreg_scratch k).2.2.2
  apply WP.of_runBlock
  simp only [↓reduceIte, transposePrep, runBlock_cons, runBlock_nil,
    exec, VOp.eval, isa, runStep_some, Option.map_some, Option.some.injEq,
    exists_eq_left', RegUpd.v_setV, hn0, hn1, hn2]
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.v_setV]; rfl
  · simp only [RegUpd.v_setV]; rfl
  · simp only [RegUpd.v_setV]; rfl
  · exact RegUpd.v_setV_self _ _ _
  · intro k; simp only [RegUpd.v_setV, hn0, hn1, hn2, hn3, ite_false]

theorem transposeEnd_ok {s₀ s : State} {r : Fin 4} (h : VG.Proof.ChaCha20.AArch64.Neon4.TPrep s₀ r s) :
    WP isa (.block (transposeEnd (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0)) (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 1))
      (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 2)) (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 3)))) s fun s' =>
      (∀ j : Fin 4, s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r j)) = VG.Proof.ChaCha20.AArch64.Neon4.transposed s₀ r j) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k) = s₀.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) ∧ VG.Proof.ChaCha20.AArch64.Neon4.Same s₀ s' := by
  have hn0 := fun k => Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_scratch k).1
  have hn1 := fun k => Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_scratch k).2.1
  have hn2 := fun k => Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_scratch k).2.2.1
  have hn3 := fun k => Ne.symm (VG.Proof.ChaCha20.AArch64.Neon4.vreg_scratch k).2.2.2
  apply WP.of_runBlock
  simp only [transposeEnd, runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV,
    hn0, hn1, hn2, hn3, ite_false, h.t24, h.t25, h.t26, h.t27]
  refine ⟨?_, ?_, h.same.gpr, h.same.mem, h.same.rd, h.same.wr, h.same.sp⟩
  · intro j
    rcases j with ⟨j, hj⟩
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.ChaCha20.AArch64.Neon4.vreg_inj, VG.Proof.ChaCha20.AArch64.Neon4.rowWord_inj] <;>
      simp (config := {decide := true}) only [Fin.ext_iff,
        ite_true, ite_false, VG.Proof.ChaCha20.AArch64.Neon4.zip1_s4, VG.Proof.ChaCha20.AArch64.Neon4.zip2_s4, VG.Proof.ChaCha20.AArch64.Neon4.zip1_d2, VG.Proof.ChaCha20.AArch64.Neon4.zip2_d2,
        vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3, VG.Proof.ChaCha20.AArch64.Neon4.transposed]
  · intro k hk
    have hne (j : Fin 4) : k ≠ rowWord r j := by
      intro e; subst k; simp only [rowWord] at hk; omega
    simp only [VG.Proof.ChaCha20.AArch64.Neon4.vreg_inj, hne, ite_false, h.keep]

theorem transpose_ok (s : State) (r : Fin 4) :
    WP isa (.block (transpose (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 0)) (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 1))
      (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 2)) (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r 3)))) s fun s' =>
      (∀ j : Fin 4, s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r j)) = VG.Proof.ChaCha20.AArch64.Neon4.transposed s r j) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k) = s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) ∧ VG.Proof.ChaCha20.AArch64.Neon4.Same s s' :=
  WP.block_append ((VG.Proof.ChaCha20.AArch64.Neon4.transposePrep_ok s r).mono fun _ h => VG.Proof.ChaCha20.AArch64.Neon4.transposeEnd_ok h)

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

theorem addWord_ok (s : State) (k : Fin 16)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (addWord k)) s fun s' =>
      (∀ j, j < 4 → vword (s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j = vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j + VG.Proof.ChaCha20.AArch64.Neon4.input s k j) ∧
      (∀ l : Fin 16, l ≠ k → s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg l) = s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg l)) ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s' := by
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Neon4.inputWord_ok s k hin).mono fun s' ⟨hw, hv, hs⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, hs.gpr, hs.mem, hs.rd, hs.wr, hs.sp⟩
  · intro j hj
    rw [RegUpd.v_setV_self, vword_map2 _ _ _ hj, hv _ (VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne k), hw j hj]
  · intro l hl
    rw [RegUpd.v_setV, ite_eq_right (fun e => hl ((VG.Proof.ChaCha20.AArch64.Neon4.vreg_inj l k).mp e)), hv _ (VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne l)]

theorem feedList_ok (ks : List (Fin 16)) (hn : ks.Nodup) (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (ks.flatMap addWord)) s fun s' =>
      (∀ k : Fin 16, ∀ j, j < 4 → vword (s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j =
        if k ∈ ks then vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j + VG.Proof.ChaCha20.AArch64.Neon4.input s k j else vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j) ∧
      VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s' := by
  induction ks generalizing s with
  | nil => exact WP.block_nil ⟨fun _ _ _ => rfl, LoadSame.refl s⟩
  | cons k ks ih =>
    obtain ⟨hk, hn⟩ := List.nodup_cons.mp hn
    apply WP.block_append
    refine (VG.Proof.ChaCha20.AArch64.Neon4.addWord_ok s k (hin k)).mono fun s' ⟨hw, hv, hs⟩ => ?_
    have hi : ∀ l : Fin 16, InRegions (s'.rd ++ s'.wr) (s'.gpr .x0 + BitVec.ofNat 64 (4 * l)) 4 := by
      intro l; rw [hs.rd, hs.wr, hs.gpr _ (by decide)]; exact hin l
    refine (ih hn s' hi).mono fun s'' ⟨ht, hsame⟩ => ⟨?_, hs.trans hsame⟩
    intro l j hj
    rw [ht l j hj, VG.Proof.ChaCha20.AArch64.Neon4.input_same hs]
    by_cases e : l = k
    · subst l; simp only [hk, ite_false, hw j hj, List.mem_cons_self, ite_true]
    · rw [hv l e]
      simp only [List.mem_cons, e, false_or]

theorem feed_ok {s : State} {vs : Nat → CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block ((List.finRange 16).flatMap addWord)) s fun s' =>
      (∀ k : Fin 16, ∀ j, j < 4 → vword (s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) j = (vs j)[k] + VG.Proof.ChaCha20.AArch64.Neon4.input s k j) ∧
      VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s s' := by
  refine (VG.Proof.ChaCha20.AArch64.Neon4.feedList_ok _ (List.nodup_finRange 16) s hin).mono fun s' ⟨hw, hs⟩ => ⟨?_, hs⟩
  intro k j hj
  rw [hw k j hj, ite_eq_left (List.mem_finRange k), h k j hj]

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Store`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

structure StoreSame (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  v : ∀ k : Fin 16, s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k) = s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem StoreSame.trans {s₀ s₁ s₂ : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.StoreSame s₀ s₁) (h' : VG.Proof.ChaCha20.AArch64.Neon4.StoreSame s₁ s₂) :
    VG.Proof.ChaCha20.AArch64.Neon4.StoreSame s₀ s₂ := ⟨h'.gpr.trans h.gpr, fun k => (h'.v k).trans (h.v k),
      h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem xorRow_ok (s : State) (r j : Fin 4)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (VG.Impl.ChaCha20.AArch64.Neon4.xorRow r j)) s fun s' =>
      s'.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16
        (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 ^^^
          s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r j))) ∧ VG.Proof.ChaCha20.AArch64.Neon4.StoreSame s s' := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 :=
    by obtain ⟨q, hq, hc⟩ := hout; exact ⟨q, List.mem_append_right _ hq, hc⟩
  have ha : (64 * j.val + 16 * r.val) % 16 = 0 ∧ 64 * j.val + 16 * r.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp only [VG.Impl.ChaCha20.AArch64.Neon4.xorRow, runBlock_cons, runBlock_nil, exec, addr, ha, and_self, ite_true, State.load, hin,
    Option.bind_some, Option.map_some, isa, runStep_some, RegUpd.gpr_setV, RegUpd.v_setV,
    VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne, ite_false, VOp.eval, State.store,
    RegUpd.wr_setV, hout, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl⟩
  intro k; simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Neon4.vreg_ne, ite_false]

/-- A byte of a 16-byte vector load. -/
theorem byte_read16 (m : Mem) (p : Addr) {i : Nat} (hi : i < 16) :
    (m.read p 16).extractLsb' (8 * i) 8 = m (p + BitVec.ofNat 64 i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  rw [getLsbD_read m 16 p _ (by omega), show (8 * i + b) / 8 = i by omega,
    show (8 * i + b) % 8 = b by omega]

theorem xor_write_byte (m : Mem) (p : Addr) (v : BitVec 128) {i : Nat} (hi : i < 16) :
    (m.write p 16 (m.read p 16 ^^^ v)) (p + BitVec.ofNat 64 i) =
      m (p + BitVec.ofNat 64 i) ^^^ v.extractLsb' (8 * i) 8 := by
  simp only [Mem.write, Mem.sub_ofNat_toNat p (by omega : i < 2 ^ 64), hi, ite_true,
    BitVec.extractLsb'_xor, VG.Proof.ChaCha20.AArch64.Neon4.byte_read16 m p hi]

theorem xor_write_apply (m : Mem) (p : Addr) (v : BitVec 128) (x : Addr) :
    (m.write p 16 (m.read p 16 ^^^ v)) x =
      if (x - p).toNat < 16 then m x ^^^ v.extractLsb' (8 * (x - p).toNat) 8 else m x := by
  by_cases h : (x - p).toNat < 16
  · simp only [Mem.write, h, ite_true, BitVec.extractLsb'_xor, VG.Proof.ChaCha20.AArch64.Neon4.byte_read16 m p h]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm p (x - p), BitVec.sub_add_cancel]
  · rw [ite_eq_right h]; exact Mem.write_apply h

/-- A sequence of distinct, aligned vector stores, tracked by their 16-byte slot. -/
def Data (m₀ m : Mem) (p : Addr) (out : Nat → BitVec 128) (done : List Nat) : Prop :=
  ∀ x, m x = if (x - p).toNat / 16 ∈ done ∧ (x - p).toNat < 256
    then m₀ x ^^^ (out ((x - p).toNat / 16)).extractLsb' (8 * ((x - p).toNat % 16)) 8
    else m₀ x

theorem Data.nil (m : Mem) (p : Addr) (out : Nat → BitVec 128) : VG.Proof.ChaCha20.AArch64.Neon4.Data m m p out [] := by
  intro x; simp only [List.not_mem_nil, false_and, ite_false]

theorem Data.store {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ m p out done) {n : Nat} (hn : n < 16) (hfresh : n ∉ done) :
    VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ (m.write (p + BitVec.ofNat 64 (16 * n)) 16
      (m.read (p + BitVec.ofNat 64 (16 * n)) 16 ^^^ out n)) p out (n :: done) := by
  intro x
  rw [VG.Proof.ChaCha20.AArch64.Neon4.xor_write_apply]
  simp only [Offset.lt_iff x p (by omega : 16 * n + 16 ≤ 2 ^ 64)]
  rw [h x]
  have hx := (x - p).isLt
  by_cases he : (x - p).toNat / 16 = n ∧ (x - p).toNat < 256
  · obtain ⟨he, hb⟩ := he
    have hd : 16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16 := by omega
    have hs : (x - (p + BitVec.ofNat 64 (16 * n))).toNat = (x - p).toNat % 16 := by
      rw [Offset.toNat_sub_add x p (by omega)]
      have hh : 2 ^ 64 - 16 * n + (x - p).toNat = 2 ^ 64 + (x - p).toNat % 16 := by omega
      rw [hh, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp only [hd, and_self, ite_true, he, hfresh, false_and, ite_false, hs,
      List.mem_cons_self, hb]
  · have hd : ¬(16 * n ≤ (x - p).toNat ∧ (x - p).toNat < 16 * n + 16) := by omega
    rw [ite_eq_right hd]
    by_cases hb : (x - p).toNat < 256
    · have hn' : (x - p).toNat / 16 ≠ n := by omega
      simp only [List.mem_cons, hn', false_or]
    · simp only [hb, and_false, ite_false]

def slot (r j : Fin 4) : Nat := 4 * j.val + r.val

theorem slot_lt (r j : Fin 4) : VG.Proof.ChaCha20.AArch64.Neon4.slot r j < 16 := by unfold VG.Proof.ChaCha20.AArch64.Neon4.slot; omega

theorem slot_inj (r i j : Fin 4) : VG.Proof.ChaCha20.AArch64.Neon4.slot r i = VG.Proof.ChaCha20.AArch64.Neon4.slot r j ↔ i = j := by
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.slot, Fin.ext_iff]; omega

theorem xorList_ok (r : Fin 4) (js : List (Fin 4)) (hn : js.Nodup)
    {m₀ : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat} {s : State}
    (hd : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s.mem p out done) (hp : s.gpr .x1 = p)
    (hv : ∀ j : Fin 4, s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r j)) = out (VG.Proof.ChaCha20.AArch64.Neon4.slot r j))
    (hfresh : ∀ j ∈ js, VG.Proof.ChaCha20.AArch64.Neon4.slot r j ∉ done)
    (hout : ∀ j ∈ js, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (js.flatMap (VG.Impl.ChaCha20.AArch64.Neon4.xorRow r))) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s'.mem p out (js.map (VG.Proof.ChaCha20.AArch64.Neon4.slot r) ++ done) ∧ VG.Proof.ChaCha20.AArch64.Neon4.StoreSame s s' := by
  induction js generalizing s done with
  | nil => exact WP.block_nil ⟨hd, rfl, fun _ => rfl, rfl, rfl, rfl⟩
  | cons j js ih =>
    have ho : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
      rw [hp]; exact hout j (List.mem_cons_self ..)
    apply WP.block_append
    refine (VG.Proof.ChaCha20.AArch64.Neon4.xorRow_ok s r j ho).mono fun s' ⟨hm, hs⟩ => ?_
    have hd' : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s'.mem p out (VG.Proof.ChaCha20.AArch64.Neon4.slot r j :: done) := by
      rw [hm, hp, hv j, show 64 * j.val + 16 * r.val = 16 * VG.Proof.ChaCha20.AArch64.Neon4.slot r j by unfold VG.Proof.ChaCha20.AArch64.Neon4.slot; omega]
      exact hd.store (VG.Proof.ChaCha20.AArch64.Neon4.slot_lt r j) (hfresh j (List.mem_cons_self ..))
    have hp' : s'.gpr .x1 = p := by rw [hs.gpr, hp]
    have hv' : ∀ i : Fin 4, s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r i)) = out (VG.Proof.ChaCha20.AArch64.Neon4.slot r i) := by
      intro i; rw [hs.v, hv]
    have hfresh' : ∀ i ∈ js, VG.Proof.ChaCha20.AArch64.Neon4.slot r i ∉ VG.Proof.ChaCha20.AArch64.Neon4.slot r j :: done := by
      intro i hi
      simp only [List.mem_cons, VG.Proof.ChaCha20.AArch64.Neon4.slot_inj, not_or]
      exact ⟨fun e => (List.nodup_cons.mp hn).1 (e ▸ hi),
        hfresh i (List.mem_cons_of_mem _ hi)⟩
    have hout' : ∀ i ∈ js, InRegions s'.wr (p + BitVec.ofNat 64 (64 * i + 16 * r)) 16 := by
      intro i hi; rw [hs.wr]; exact hout i (List.mem_cons_of_mem _ hi)
    refine (ih (List.nodup_cons.mp hn).2 hd' hp' hv' hfresh' hout').mono fun s'' ⟨hd'', ht⟩ =>
      ⟨?_, hs.trans ht⟩
    intro x
    simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Data, List.map_cons, List.mem_append, List.mem_cons, or_assoc,
      or_left_comm] using hd'' x

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4

/-- One 16-byte row of the final four ChaCha blocks. -/
def output (vs : Nat → CState) (n : Nat) : BitVec 128 :=
  ofVWords ((vs (n / 4))[4 * (n % 4)]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 1]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 2]'(by omega))
    ((vs (n / 4))[4 * (n % 4) + 3]'(by omega))

theorem output_slot (vs : Nat → CState) (r j : Fin 4) :
    VG.Proof.ChaCha20.AArch64.Neon4.output vs (VG.Proof.ChaCha20.AArch64.Neon4.slot r j) = ofVWords ((vs j)[rowWord r 0]) ((vs j)[rowWord r 1])
      ((vs j)[rowWord r 2]) ((vs j)[rowWord r 3]) := by
  have hd : VG.Proof.ChaCha20.AArch64.Neon4.slot r j / 4 = j.val := by unfold VG.Proof.ChaCha20.AArch64.Neon4.slot; omega
  have hm : VG.Proof.ChaCha20.AArch64.Neon4.slot r j % 4 = r.val := by unfold VG.Proof.ChaCha20.AArch64.Neon4.slot; omega
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.output, hd, hm, rowWord, Fin.getElem_fin]; rfl

structure Keep (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.trans {s₀ s₁ s₂ : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.Keep s₀ s₁) (h' : VG.Proof.ChaCha20.AArch64.Neon4.Keep s₁ s₂) : VG.Proof.ChaCha20.AArch64.Neon4.Keep s₀ s₂ :=
  ⟨h'.gpr.trans h.gpr, h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

def rowSlots (r : Fin 4) : List Nat := (List.finRange 4).map (VG.Proof.ChaCha20.AArch64.Neon4.slot r)

theorem finishRowFor_ok (js : List (Fin 4)) (hj : js.Nodup) {s : State} {m₀ : Mem} {p : Addr} {vs : Nat → CState} {done : List Nat}
    (r : Fin 4) (hd : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) done) (hp : s.gpr .x1 = p)
    (hv : ∀ i j : Fin 4, vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ j ∈ js, VG.Proof.ChaCha20.AArch64.Neon4.slot r j ∉ done)
    (hout : ∀ j ∈ js, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (finishRowFor js r)) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s'.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) (js.map (VG.Proof.ChaCha20.AArch64.Neon4.slot r) ++ done) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k) = s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) ∧ VG.Proof.ChaCha20.AArch64.Neon4.Keep s s' := by
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Neon4.transpose_ok s r).mono fun t ⟨ht, ho, hs⟩ => ?_
  have hd' : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ t.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) done := hs.mem ▸ hd
  have hp' : t.gpr .x1 = p := by rw [hs.gpr, hp]
  have hv' : ∀ j : Fin 4, t.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r j)) = VG.Proof.ChaCha20.AArch64.Neon4.output vs (VG.Proof.ChaCha20.AArch64.Neon4.slot r j) := by
    intro j; rw [ht j, VG.Proof.ChaCha20.AArch64.Neon4.transposed, VG.Proof.ChaCha20.AArch64.Neon4.output_slot, hv 0 j, hv 1 j, hv 2 j, hv 3 j]
  have hout' : ∀ j ∈ js, InRegions t.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro j hjs; rw [hs.wr]; exact hout j hjs
  refine (VG.Proof.ChaCha20.AArch64.Neon4.xorList_ok r js hj hd' hp' hv'
    hfresh hout').mono fun u ⟨hu, hk⟩ => ⟨hu, ?_, ?_⟩
  · intro k hkr; rw [hk.v, ho k hkr]
  · exact ⟨hk.gpr.trans hs.gpr, hk.rd.trans hs.rd, hk.wr.trans hs.wr, hk.sp.trans hs.sp⟩

theorem slot_ne {r t : Fin 4} (hne : r ≠ t) (i j : Fin 4) : VG.Proof.ChaCha20.AArch64.Neon4.slot r i ≠ VG.Proof.ChaCha20.AArch64.Neon4.slot t j := by
  intro e; apply hne; apply Fin.ext; unfold VG.Proof.ChaCha20.AArch64.Neon4.slot at e; omega

theorem finishRowsFor_ok (js : List (Fin 4)) (hj : js.Nodup) (rs : List (Fin 4)) (hn : rs.Nodup)
    {s : State} {m₀ : Mem} {p : Addr} {vs : Nat → CState} {done : List Nat}
    (hd : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) done) (hp : s.gpr .x1 = p)
    (hv : ∀ r ∈ rs, ∀ i j : Fin 4, vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ r ∈ rs, ∀ j ∈ js, VG.Proof.ChaCha20.AArch64.Neon4.slot r j ∉ done)
    (hout : ∀ r : Fin 4, ∀ j ∈ js, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (rs.flatMap (finishRowFor js))) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s'.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) (rs.flatMap (fun r => js.map (VG.Proof.ChaCha20.AArch64.Neon4.slot r)) ++ done) ∧ VG.Proof.ChaCha20.AArch64.Neon4.Keep s s' := by
  induction rs generalizing s done with
  | nil => exact WP.block_nil ⟨hd, rfl, rfl, rfl, rfl⟩
  | cons r rs ih =>
    have hr := (List.nodup_cons.mp hn).1
    apply WP.block_append
    refine (VG.Proof.ChaCha20.AArch64.Neon4.finishRowFor_ok js hj r hd hp (hv r (List.mem_cons_self ..))
      (hfresh r (List.mem_cons_self ..)) (hout r)).mono fun t ⟨ht, hvkeep, hs⟩ => ?_
    have hp' : t.gpr .x1 = p := by rw [hs.gpr, hp]
    have hv' : ∀ q ∈ rs, ∀ i j : Fin 4,
        vword (t.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord q i))) j = (vs j)[rowWord q i] := by
      intro q hq i j
      have hqr : (rowWord q i).val / 4 ≠ r.val := by
        have hqr : q ≠ r := fun e => hr (e ▸ hq)
        simp only [rowWord] at *; omega
      rw [hvkeep _ hqr]; exact hv q (List.mem_cons_of_mem _ hq) i j
    have hfresh' : ∀ q ∈ rs, ∀ j ∈ js, VG.Proof.ChaCha20.AArch64.Neon4.slot q j ∉ js.map (VG.Proof.ChaCha20.AArch64.Neon4.slot r) ++ done := by
      intro q hq j hjs
      simp only [List.mem_append, not_or]
      refine ⟨?_, hfresh q (List.mem_cons_of_mem _ hq) j hjs⟩
      intro hm
      obtain ⟨i, _, he⟩ := List.mem_map.mp hm
      exact VG.Proof.ChaCha20.AArch64.Neon4.slot_ne (fun (e : q = r) => hr (e ▸ hq)) j i he.symm
    have hout' : ∀ q : Fin 4, ∀ j ∈ js, InRegions t.wr (p + BitVec.ofNat 64 (64 * j + 16 * q)) 16 := by
      intro q j hjs; rw [hs.wr]; exact hout q j hjs
    refine (ih (List.nodup_cons.mp hn).2 ht hp' hv' hfresh' hout').mono fun u ⟨hu, hk⟩ =>
      ⟨?_, hs.trans hk⟩
    intro x
    simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Data, List.flatMap_cons, List.mem_append, or_assoc, or_left_comm] using hu x

theorem finishRow_ok {s : State} {m₀ : Mem} {p : Addr} {vs : Nat → CState} {done : List Nat}
    (r : Fin 4) (hd : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) done) (hp : s.gpr .x1 = p)
    (hv : ∀ i j : Fin 4, vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ j : Fin 4, VG.Proof.ChaCha20.AArch64.Neon4.slot r j ∉ done)
    (hout : ∀ j : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (finishRow r)) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s'.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) (VG.Proof.ChaCha20.AArch64.Neon4.rowSlots r ++ done) ∧
      (∀ k : Fin 16, k.val / 4 ≠ r.val → s'.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k) = s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg k)) ∧ VG.Proof.ChaCha20.AArch64.Neon4.Keep s s' := by
  exact VG.Proof.ChaCha20.AArch64.Neon4.finishRowFor_ok (List.finRange 4) (List.nodup_finRange 4) r hd hp hv
    (fun j _ => hfresh j) (fun j _ => hout j)

theorem finishRows_ok (rs : List (Fin 4)) (hn : rs.Nodup)
    {s : State} {m₀ : Mem} {p : Addr} {vs : Nat → CState} {done : List Nat}
    (hd : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) done) (hp : s.gpr .x1 = p)
    (hv : ∀ r ∈ rs, ∀ i j : Fin 4, vword (s.v (VG.Impl.ChaCha20.AArch64.Neon4.vreg (rowWord r i))) j = (vs j)[rowWord r i])
    (hfresh : ∀ r ∈ rs, ∀ j : Fin 4, VG.Proof.ChaCha20.AArch64.Neon4.slot r j ∉ done)
    (hout : ∀ r j : Fin 4, InRegions s.wr (p + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block (rs.flatMap finishRow)) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ s'.mem p (VG.Proof.ChaCha20.AArch64.Neon4.output vs) (rs.flatMap VG.Proof.ChaCha20.AArch64.Neon4.rowSlots ++ done) ∧ VG.Proof.ChaCha20.AArch64.Neon4.Keep s s' := by
  exact VG.Proof.ChaCha20.AArch64.Neon4.finishRowsFor_ok (List.finRange 4) (List.nodup_finRange 4) rs hn hd hp hv
    (fun r hr j _ => hfresh r hr j) (fun r j _ => hout r j)

theorem all_slots (n : Fin 16) : n.val ∈ (List.finRange 4).flatMap VG.Proof.ChaCha20.AArch64.Neon4.rowSlots :=
  (show ∀ n : Fin 16, n.val ∈ (List.finRange 4).flatMap VG.Proof.ChaCha20.AArch64.Neon4.rowSlots by decide) n

theorem output_word (vs : Nat → CState) (n : Nat) {e : Nat} (he : e < 4) :
    vword (VG.Proof.ChaCha20.AArch64.Neon4.output vs n) e = (vs (n / 4))[4 * (n % 4) + e]'(by omega) := by
  rw [VG.Proof.ChaCha20.AArch64.Neon4.output, vword_ofVWords _ _ _ _ he]
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem byte_vword (v : BitVec 128) {i : Nat} (_hi : i < 16) :
    v.extractLsb' (8 * i) 8 = (vword v (i / 4)).extractLsb' (8 * (i % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [vword, BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    show 8 * (i % 4) + b < 32 by omega]
  exact congrArg v.getLsbD (by omega)

theorem output_byte (vs : Nat → CState) {k : Nat} (_hk : k < 256) :
    (VG.Proof.ChaCha20.AArch64.Neon4.output vs (k / 16)).extractLsb' (8 * (k % 16)) 8 =
      (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0 := by
  rw [VG.Proof.ChaCha20.AArch64.Neon4.byte_vword _ (by omega), VG.Proof.ChaCha20.AArch64.Neon4.output_word _ _ (by omega),
    VG.Proof.ChaCha20.serialize_getD _ (by omega)]
  simp only [show k / 16 / 4 = k / 64 by omega,
    show 4 * (k / 16 % 4) + k % 16 / 4 = k % 64 / 4 by omega,
    show k % 16 % 4 = k % 64 % 4 by omega]

theorem Data.frame {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : VG.Proof.ChaCha20.AArch64.Neon4.Data m₀ m p out done) : Frame [⟨p, 256⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 256 := by
    have hh := hx ⟨p, 256⟩ (List.mem_cons_self ..)
    simp only [Region.Contains] at hh
    omega
  rw [h x, ite_eq_right (fun h => hn h.2)]

theorem finishBlocks_ok {s : State} {vs : Nat → CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s)
    (hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap finishRow)) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1, 256⟩] s.mem s'.mem ∧ VG.Proof.ChaCha20.AArch64.Neon4.Keep s s' := by
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishRows_ok (List.finRange 4) (List.nodup_finRange 4)
    (Data.nil s.mem (s.gpr .x1) (VG.Proof.ChaCha20.AArch64.Neon4.output vs)) rfl (fun r _ i j => h (rowWord r i) j j.isLt)
    (fun _ _ _ => List.not_mem_nil) hout).mono fun s' ⟨hd, hs⟩ => ⟨?_, hd.frame, hs⟩
  intro k hk
  rw [hd _, Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64),
    ite_eq_left ⟨List.mem_append_left _ (VG.Proof.ChaCha20.AArch64.Neon4.all_slots ⟨k / 16, by omega⟩), hk⟩,
    VG.Proof.ChaCha20.AArch64.Neon4.output_byte vs hk]

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.RoundLoop`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (innerBlock)

theorem roundCounterInit_ok (s : State) :
    WP isa (.block [.movz .x .x4 10 0]) s fun u =>
      u.gpr .x4 = 10 ∧ u.v = s.v ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s u := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, runBlock_cons, runBlock_nil, exec,
    Size.bits, isa, runStep_some, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.gpr_write_self .., rfl,
    ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl⟩⟩

theorem roundCounterDec_ok (s : State) {n : Nat} (hn : 0 < n ∧ n ≤ 10)
    (hc : s.gpr .x4 = BitVec.ofNat 64 n) :
    WP isa (.block [.subImm .x .x4 .x4 1]) s fun u =>
      u.gpr .x4 = BitVec.ofNat 64 (n - 1) ∧ u.v = s.v ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s u := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runBlock_nil, exec,
    State.read, Size.bits, isa, runStep_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl, rfl⟩⟩
  rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc]
  exact Offset.ofNat_sub_ofNat (by omega)

theorem roundLoop_ok {vs : Nat → CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s)
    (ht : s.v .v30 = rol8Table) :
    WP isa roundLoop s fun u =>
      VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock 10 (vs j)) u ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s u := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.roundCounterInit_ok s).mono fun a ⟨ha, hav, hsa⟩ => ?_
  let Inv : Nat → State → Prop := fun n u =>
    0 < n ∧ n ≤ 10 ∧ u.gpr .x4 = BitVec.ofNat 64 n ∧
    VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock (10 - n) (vs j)) u ∧
    u.v .v30 = rol8Table ∧ VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s u
  refine WP.loop (M := isa) Inv ?_ 10 a ?_
  · intro n u ⟨hn, hle, hc, hu, hut, hsu⟩
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Neon4.doubleRound_ok hu hut).mono fun b ⟨hb, hub⟩ => ?_
    have hcb : b.gpr .x4 = BitVec.ofNat 64 n := by rw [hub.gpr]; exact hc
    refine (VG.Proof.ChaCha20.AArch64.Neon4.roundCounterDec_ok b ⟨hn, hle⟩ hcb).mono fun c ⟨hcc, hcv, hbc⟩ => ?_
    have hsc : VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s c := (hsu.trans
      ⟨fun r _ => congrFun hub.gpr r, hub.mem, hub.rd, hub.wr, hub.sp⟩).trans hbc
    have hcH : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => Nat.repeat innerBlock (10 - (n - 1)) (vs j)) c := by
      have he : 10 - (n - 1) = (10 - n) + 1 := by omega
      rw [he]
      simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Holds, hcv, Nat.repeat] using hb
    have hct : c.v .v30 = rol8Table := by rw [hcv, hub.v30, hut]
    have heval := Xor.eval_nonzero_ofNat c .x4 (by omega : n - 1 < 2 ^ 64) hcc
    by_cases hz : n = 1
    · left
      refine ⟨?_, ?_, hsc⟩
      · simpa only [hz, Nat.sub_self, ne_eq, not_true_eq_false, decide_false] using heval
      · simpa only [hz, Nat.sub_self, Nat.sub_zero] using hcH
    · right
      refine ⟨?_, n - 1, by omega, by omega, by omega, hcc, hcH, hct, hsc⟩
      simpa only [decide_eq_true (by omega : n - 1 ≠ 0)] using heval
  · refine ⟨by decide, by decide, ha, ?_, ?_, hsa⟩
    · simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Holds, hav, Nat.sub_self, Nat.repeat] using h
    · rw [hav, ht]

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (stateAt serialize block)

theorem input_eq (s : State) (k : Fin 16) (j : Nat) :
    VG.Proof.ChaCha20.AArch64.Neon4.input s k j = (ctr (stateAt s.mem (s.gpr .x0)) j)[k] := by
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.input, ctr, Vector.getElem_set, stateAt, Vector.getElem_ofFn, Fin.getElem_fin]
  by_cases hk : k = 12
  · subst k; rfl
  · have hk' : k.val ≠ 12 := fun e => hk (Fin.ext e)
    simp only [hk, Ne.symm hk', ite_false]

structure ChunkKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem chunk_ok (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa VG.Impl.ChaCha20.AArch64.Neon4.chunk s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (serialize (VG.Spec.ChaCha20.block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1, 256⟩] s.mem s'.mem ∧ VG.Proof.ChaCha20.AArch64.Neon4.ChunkKeep s s' := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.setup_ok s hin).mono fun a ⟨ha, hsa, hta⟩ => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.roundLoop_ok ha hta).mono fun b ⟨hb, hab⟩ => ?_
  have hsb : VG.Proof.ChaCha20.AArch64.Neon4.LoadSame s b := hsa.trans hab
  have hi : ∀ k : Fin 16, InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hsb.rd, hsb.wr, hsb.gpr _ (by decide)]; exact hin k
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Neon4.feed_ok hb hi).mono fun c ⟨hc, hbc⟩ => ?_
  have hsc := hsb.trans hbc
  have hc' : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => VG.Spec.ChaCha20.block (ctr (stateAt s.mem (s.gpr .x0)) j)) c := by
    intro k j hj
    simp only [VG.Spec.ChaCha20.block]
    rw [hc k j hj, VG.Proof.ChaCha20.AArch64.Neon4.input_same hsb, VG.Proof.ChaCha20.AArch64.Neon4.input_eq]
    simp only [Fin.getElem_fin, Vector.getElem_zipWith]
  have ho : ∀ r j : Fin 4, InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [hsc.wr, hsc.gpr _ (by decide)]; exact hout r j
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishBlocks_ok hc' ho).mono fun d ⟨hd, hf, hs⟩ => ⟨?_, ?_, ?_⟩
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4), hsc.mem] using hd
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4), hsc.mem] using hf
  · exact ⟨fun r hr => by rw [hs.gpr]; exact hsc.gpr r hr,
      hs.rd.trans hsc.rd, hs.wr.trans hsc.wr, hs.sp.trans hsc.sp⟩

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Lit`. -/
section

namespace VG

/- Cache the kernel-checked four-block stream code for all caller audits. -/
materialize_code Impl.ChaCha20.AArch64.Neon4.xor

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)

/-- Before four-block chunk t. x0/x3 and all but the two scratch registers
are retained, except the advancing data pointer and remaining length. -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (256 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256 * t)
  x3 : s.gpr .x3 = bp s₀
  le : 256 * t ≤ L s₀
  keep : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (4 * t)
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 256 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem shr8 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> 8 = BitVec.ofNat 64 (n / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem ctr_add (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.getElem_set_self, Vector.set_set, BitVec.ofNat_add, BitVec.add_assoc]

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 256 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (VG.Spec.ChaCha20.block (ctr (ctr S (4 * t)) ((k - 256 * t) / 64)))).getD
        ((k - 256 * t) % 64) 0 := by
  rw [keystream_getD _ hk, VG.Proof.ChaCha20.AArch64.Neon4.ctr_add, show 4 * t + (k - 256 * t) / 64 = k / 64 by omega,
    show (k - 256 * t) % 64 = k % 64 by omega]

theorem next_ok (s : State) (hlen : 256 ≤ (s.gpr .x2).toNat)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Neon4.next) s fun s' =>
      s'.gpr .x1 = s.gpr .x1 + 256 ∧
      s'.gpr .x2 = s.gpr .x2 - 256 ∧
      s'.gpr .x5 = BitVec.ofNat 64 (((s.gpr .x2).toNat - 256) / 256) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) 4 ∧
      Frame [⟨s.gpr .x0, 64⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, VG.Impl.ChaCha20.AArch64.Neon4.next, runBlock_cons, runBlock_nil, exec,
    addr, Size.bytes, Size.bits, State.load, hin, State.read, RegUpd.gpr_write, RegUpd.wr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.sp_write,
    Option.bind_some, Option.map_some, isa, runStep_some, BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq, State.store, hout, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, trivial⟩
  · have he : s.gpr .x2 - BitVec.ofNat 64 256 = BitVec.ofNat 64 ((s.gpr .x2).toNat - 256) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have h := (s.gpr .x2).isLt; omega
    rw [he, VG.Proof.ChaCha20.AArch64.Neon4.shr8 (by have h := (s.gpr .x2).isLt; omega)]
  · intro r h1 h2 h4 h5
    simp only [h1, h2, h4, h5, ite_false]
  · have hv : (stateAt s.mem (s.gpr .x0))[12] = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
      simp only [stateAt, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]
    have ht := Xor.stateAt_writeW_counter s.mem (s.gpr .x0)
      (s.mem.read (s.gpr .x0 + BitVec.ofNat 64 48) 4 + BitVec.ofNat 32 4)
    simp only [Mem.writeW, BitVec.setWidth_eq] at ht
    unfold ctr
    rw [hv]
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))

abbrev win (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (256 * t), 256⟩

theorem win_sub {s₀ : State} {t : Nat} (h : 256 * t + 256 ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Neon4.win s₀ t) (dR s₀) := Offset.sub_base _ h

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have h := Xor.L_lt s₀; omega)

theorem chunkData {s₀ s u : State} {t : Nat} (h : VG.Proof.ChaCha20.AArch64.Neon4.LInv s₀ t s)
    (hge : 256 * t + 256 ≤ L s₀)
    (hu : ∀ k < 256, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
      s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (VG.Spec.ChaCha20.block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0)
    (hf : Frame [⟨s.gpr .x1, 256⟩] s.mem u.mem) :
    ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 256 * (t + 1) then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
  intro k hk
  have hL := Xor.L_lt s₀
  by_cases hin : 256 * t ≤ k ∧ k < 256 * t + 256
  · have he : s.gpr .x1 + BitVec.ofNat 64 (k - 256 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.x1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
    have hh := hu (k - 256 * t) (by omega)
    rw [he, h.data k hk, ite_eq_right (by omega), h.x0, h.cnt, ← VG.Proof.ChaCha20.AArch64.Neon4.ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega)]; exact hh
  · have hx : ¬ (VG.Proof.ChaCha20.AArch64.Neon4.win s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
      simp only [Region.Contains, Nat.add_one_le_iff]
      rw [Offset.lt_iff _ _ (by omega), Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64)]
      exact hin
    have hh := hf (dp s₀ + BitVec.ofNat 64 k) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; rw [h.x1]; exact hx)
    rw [hh, h.data k hk]
    by_cases hold : k < 256 * t
    · rw [ite_eq_left hold, ite_eq_left (by omega)]
    · rw [ite_eq_right hold, ite_eq_right (by omega)]

theorem body_ok {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 256 * t + 256 ≤ L s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.LInv s₀ t s) :
    WP isa VG.Impl.ChaCha20.AArch64.Neon4.body s fun s' => VG.Proof.ChaCha20.AArch64.Neon4.LInv s₀ (t + 1) s' ∧
      s'.gpr .x5 = BitVec.ofNat 64 ((L s₀ - 256 * (t + 1)) / 256) := by
  have hL := Xor.L_lt s₀
  have hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [h.rd, h.wr, hp.rd, hp.wr, h.x0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [h.wr, hp.wr, h.x1, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.chunk_ok s hin hout).mono fun u ⟨hu, hf, hs⟩ => ?_
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (4 * t) := by
    rw [← h.cnt]
    apply Xor.stateAt_frame hf
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [h.x1]; exact hp.st_d.sub_right (VG.Proof.ChaCha20.AArch64.Neon4.win_sub hge)
  have hdata := VG.Proof.ChaCha20.AArch64.Neon4.chunkData h hge hu hf
  have hx0 : u.gpr .x0 = st s₀ := (hs.gpr _ (by decide)).trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (256 * t) := (hs.gpr _ (by decide)).trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256 * t) := (hs.gpr _ (by decide)).trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := (hs.gpr _ (by decide)).trans h.x3
  have hw : u.wr = [stR s₀, dR s₀, bR s₀] := hs.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hs.rd, h.rd, hp.rd, hw, hx0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw, hx0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 256 * t := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine (VG.Proof.ChaCha20.AArch64.Neon4.next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1, hv2, hv5, hkeep, hctr, hframe, hrd, hwr, hsp⟩ => ?_
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (256 * (t + 1)) := by
    rw [hv1, hx1, BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (256 * t) + BitVec.ofNat 64 256 = _
    rw [← BitVec.ofNat_add, show 256 * t + 256 = 256 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 256 * (t + 1)) := by
    rw [hv2, hx2]
    change BitVec.ofNat 64 (L s₀ - 256 * t) - BitVec.ofNat 64 256 = _
    rw [Offset.ofNat_sub_ofNat (by omega), show L s₀ - 256 * t - 256 = L s₀ - 256 * (t + 1) by omega]
  refine ⟨⟨?_, hptr, hrem, ?_, by omega, ?_, hrd.trans (hs.rd.trans h.rd),
    hwr.trans (hs.wr.trans h.wr), hsp.trans (hs.sp.trans h.sp), ?_, ?_, ?_⟩, ?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide), hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide), hx3]
  · intro r h1 h2 h4 h5
    rw [hkeep r h1 h2 h4 h5, hs.gpr r h4]; exact h.keep r h1 h2 h4 h5
  · rw [hx0, hcnt, VG.Proof.ChaCha20.AArch64.Neon4.ctr_add, show 4 * t + 4 = 4 * (t + 1) by omega] at hctr
    exact hctr
  · intro k hk
    rw [hframe _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact fun hn => hp.st_d _ hn (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)), hdata k hk]
  · have hf' : Frame [stR s₀, dR s₀] s.mem u.mem := hf.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      refine ⟨dR s₀, by simp, ?_⟩; rw [h.x1]; exact VG.Proof.ChaCha20.AArch64.Neon4.win_sub hge)
    have hn' : Frame [stR s₀, dR s₀] u.mem v.mem := hframe.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact List.mem_cons_self ..)
    exact (h.frame.trans hf').trans hn'
  · rw [hv5, hlen, show L s₀ - 256 * t - 256 = L s₀ - 256 * (t + 1) by omega]

theorem init_ok (s : State) :
    WP isa (.block [.lsr .x .x5 .x2 8]) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Neon4.LInv s 0 s' ∧ s'.gpr .x5 = BitVec.ofNat 64 (L s / 256) := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runBlock_nil, exec, State.read,
    Size.bits, Option.some.injEq, isa, runStep_some, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, by omega, ?_, rfl, rfl, rfl, ?_, ?_, Frame.refl _ _⟩, ?_⟩
  · exact RegUpd.gpr_write_of_ne _ _ _ (by decide)
  · simp only [RegUpd.gpr_write, show Reg.x1 ≠ .x5 by decide, ite_false]
    simp [dp]
  · simp only [RegUpd.gpr_write, show Reg.x2 ≠ .x5 by decide, ite_false, Nat.mul_zero, Nat.sub_zero]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s.gpr .x2)).symm
  · exact RegUpd.gpr_write_of_ne _ _ _ (by decide)
  · intro r _ _ _ h5; exact RegUpd.gpr_write_of_ne _ _ _ h5
  · exact (VG.Proof.ChaCha20.ctr_zero _).symm
  · intro k _; simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]; rfl
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    have he : s.gpr .x2 = BitVec.ofNat 64 (L s) := by
      simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s.gpr .x2)).symm
    rw [he, BitVec.setWidth_eq, VG.Proof.ChaCha20.AArch64.Neon4.shr8 (Xor.L_lt s)]

theorem zero_chunks {s : State} {n : Nat} (hn : n < 2 ^ 64)
    (h : s.gpr .x5 = BitVec.ofNat 64 (n / 256)) :
    isa.eval (.zero .x .x5) s = some (decide (n < 256)) := by
  rw [show isa.eval (.zero .x .x5) s = some (s.gpr .x5 == 0) from Xor.eval_zero s .x5,
    h, Xor.ofNat_beq_zero (by omega)]
  congr 2
  apply propext; omega

theorem bulk_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.LInv s₀ 0 s)
    (hx5 : s.gpr .x5 = BitVec.ofNat 64 (L s₀ / 256)) :
    WP isa (.ite (.zero .x .x5) (.block []) (.loop VG.Impl.ChaCha20.AArch64.Neon4.body (.nonzero .x .x5))) s fun s' =>
      ∃ t, L s₀ - 256 * t < 256 ∧ VG.Proof.ChaCha20.AArch64.Neon4.LInv s₀ t s' := by
  have hL := Xor.L_lt s₀
  apply WP.ite (decide (L s₀ < 256)) (VG.Proof.ChaCha20.AArch64.Neon4.zero_chunks hL hx5)
  · intro hb
    have hb' : L s₀ < 256 := of_decide_eq_true hb
    exact WP.block_nil ⟨0, by simpa using hb', h⟩
  · intro hb
    have hge : 256 ≤ L s₀ := by have := of_decide_eq_false hb; omega
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = L s₀ - 256 * t ∧ 256 ≤ n ∧ VG.Proof.ChaCha20.AArch64.Neon4.LInv s₀ t s
    refine WP.loop (M := isa) Inv ?_ (L s₀) s ⟨0, by omega, hge, h⟩
    intro n s ⟨t, hn, hge, hi⟩
    refine (VG.Proof.ChaCha20.AArch64.Neon4.body_ok hp (by omega) hi).mono fun u ⟨hu, h5⟩ => ?_
    have hc := Xor.eval_nonzero_ofNat u .x5
      (by omega : (L s₀ - 256 * (t + 1)) / 256 < 2 ^ 64) h5
    by_cases he : L s₀ - 256 * (t + 1) < 256
    · left
      refine ⟨?_, t + 1, he, hu⟩
      simpa only [Nat.div_eq_of_lt he, ne_eq, not_true_eq_false, decide_false] using hc
    · right
      refine ⟨?_, L s₀ - 256 * (t + 1), by omega, t + 1, rfl, by omega, hu⟩
      have hne : (L s₀ - 256 * (t + 1)) / 256 ≠ 0 := by omega
      simpa only [decide_eq_true hne] using hc

end VG.Proof.ChaCha20.AArch64.Neon4

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

abbrev tailR (s₀ : State) (t : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (256 * t), L s₀ - 256 * t⟩

theorem tail_sub {s₀ : State} {t : Nat} (ht : 256 * t ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Neon4.tailR s₀ t) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {t k : Nat} (hk : k < 256 * t) (ht : 256 * t ≤ L s₀) :
    ¬ (VG.Proof.ChaCha20.AArch64.Neon4.tailR s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := Xor.L_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

theorem tail_ok {s₀ : State} (hp : XPre s₀) {t : Nat} {s : State} (h : VG.Proof.ChaCha20.AArch64.Neon4.LInv s₀ t s) :
    WP isa Impl.ChaCha20.AArch64.Xor.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 := by
  have hL := Xor.L_lt s₀
  have hle := h.le
  have hn : (BitVec.ofNat 64 (L s₀ - 256 * t)).toNat = L s₀ - 256 * t :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let wr := [stR s₀, VG.Proof.ChaCha20.AArch64.Neon4.tailR s₀ t, bR s₀]
  have hs : xorAArch64.pre (s.withRegions [] wr) := by
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      h.x0, h.x1, h.x2, h.x3, hn]
    have ts := VG.Proof.ChaCha20.AArch64.Neon4.tail_sub h.le
    exact ⟨trivial, rfl, hp.st_d.sub_right ts, hp.st_b, hp.d_b.sub_left ts, by
      have := hp.nowrap
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega⟩
  have hc : Covers wr s.wr := by
    rw [h.wr, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s₀, by simp, 256 * t, rfl, by dsimp; omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, by simp⟩
  have hw : WP isa Impl.ChaCha20.AArch64.Xor.xor (s.withRegions [] wr) fun u =>
      abiPreserved (s.withRegions [] wr) u ∧ xorAArch64.post (s.withRegions [] wr) u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 :=
    Xor.xor_x1 BlockImpl.scalar _ hs
  refine WP.narrow hw ?_ hc ?_ BlockImpl.scalar.xorNoFrames
  · rw [h.rd, hp.rd]; exact hc
  · intro u _ _ hsp hf ⟨ha, hpost, h0, h1⟩
    simp only [State.withRegions_gpr, State.withRegions_sp, abiPreserved] at ha
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_mem,
      h.x0, h.x1, h.x2, hn, h.cnt] at hpost
    refine ⟨⟨?_, hsp.trans h.sp⟩, ?_, h0.trans h.x0, h1.trans h.x3⟩
    · intro r hr
      rw [ha.1 r hr]
      apply h.keep r <;> intro he <;> subst r <;> simp [preserved] at hr
    · refine bytesAt_xor (length_keystream _ _) fun k hk => ?_
      have hk2 : k < L s₀ := hk
      have ns : ¬ (stR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.st_d _ hh (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)
      have nb : ¬ (bR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.d_b _ (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk) hh
      by_cases hk' : k < 256 * t
      · rw [hf _ (by
          intro r hr; simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ns
          · exact VG.Proof.ChaCha20.AArch64.Neon4.not_tail hk' h.le
          · exact nb), h.data k hk, ite_eq_left hk']
      · have ea : dp s₀ + BitVec.ofNat 64 (256 * t) + BitVec.ofNat 64 (k - 256 * t) =
            dp s₀ + BitVec.ofNat 64 k := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
        have x := VG.Proof.ChaCha20.AArch64.Neon4.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 256 * t) (by omega)
        rw [ea, h.data k hk, ite_eq_right hk', keystream_getD _ (by omega)] at x
        rw [x, VG.Proof.ChaCha20.AArch64.Neon4.ks_shift _ hk (t := t) (by omega)]

theorem correct (s : State) (hp : xorAArch64.pre s) :
    WP isa Impl.ChaCha20.AArch64.Neon4.xor s fun s' =>
      abiPreserved s s' ∧ xorAArch64.post s s' ∧
      s'.gpr .x0 = s.gpr .x0 ∧ s'.gpr .x1 = s.gpr .x3 := by
  apply WP.withPreservedV (hc := by lit_decide)
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.init_ok s).mono fun u ⟨hi, h5⟩ => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Neon4.bulk_ok (XPre.of s hp) hi h5).mono fun v ⟨t, _, hv⟩ => ?_
  exact VG.Proof.ChaCha20.AArch64.Neon4.tail_ok (XPre.of s hp) hv

theorem xor_correct (s : State) (hs : xorAArch64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.AArch64.Neon4.xor s t s' ∧ abiPreserved s s' ∧
      xorAArch64.post s s' :=
  (VG.Proof.ChaCha20.AArch64.Neon4.correct s hs).imp fun _ ⟨s', he, ha, hp, _⟩ => ⟨s', he, ha, hp⟩

theorem xor_noFrames : Impl.ChaCha20.AArch64.Neon4.xor.noFrames = true := by lit_decide

theorem xor_ct : ConstantTime isa xorAArch64.pre xorAArch64.pub
    Impl.ChaCha20.AArch64.Neon4.xor := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ hp => Xor.agree₀ hp) (by taint_decide)

theorem xor_verified :
    Verified AArch64.target Impl.ChaCha20.AArch64.Neon4.xor (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct VG.Proof.ChaCha20.AArch64.Neon4.xor_correct VG.Proof.ChaCha20.AArch64.Neon4.xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, AArch64.abi, AArch64.argRegs,
      xorAArch64] [Xor.sat] using Xor.sat)

end VG.Proof.ChaCha20.AArch64.Neon4

end
