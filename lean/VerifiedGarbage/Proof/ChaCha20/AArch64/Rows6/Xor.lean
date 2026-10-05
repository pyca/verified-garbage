import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.ChaCha20.AArch64.XorVariant
import VerifiedGarbage.Proof.ChaCha20.AArch64.Small.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Ops`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (Word)
abbrev Rows := Vector Word 24

theorem vreg_inj (a b : Fin 24) : vreg a = vreg b ↔ a = b :=
  (show ∀ a b : Fin 24, vreg a = vreg b ↔ a = b by decide) a b

theorem vreg_ne (a : Fin 24) : vreg a ≠ .v31 :=
  (show ∀ a : Fin 24, vreg a ≠ .v31 by decide) a

theorem vreg_ne30 (a : Fin 24) : vreg a ≠ .v30 :=
  (show ∀ a : Fin 24, vreg a ≠ .v30 by decide) a

def Holds (vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows) (s : State) : Prop :=
  ∀ k : Fin 24, ∀ j, j < 4 → vword (s.v (vreg k)) j = (vs j)[k]

structure Same (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Same.trans {s₀ s₁ s₂ : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.Same s₀ s₁) (h' : VG.Proof.ChaCha20.AArch64.Rows6.Same s₁ s₂) : VG.Proof.ChaCha20.AArch64.Rows6.Same s₀ s₂ :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

structure RoundSame (s s' : State) : Prop extends VG.Proof.ChaCha20.AArch64.Rows6.Same s s' where
  v30 : s'.v .v30 = s.v .v30

theorem RoundSame.trans {s₀ s₁ s₂ : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s₀ s₁) (h' : VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s₁ s₂) :
    VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s₀ s₂ := ⟨h.toSame.trans h'.toSame, h'.v30.trans h.v30⟩

def step (vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows) : VG.Impl.ChaCha20.AArch64.Rows6.Op → Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows
  | .add d a b => fun j => (vs j).set d ((vs j)[a] + (vs j)[b])
  | .xorRol d a b n => fun j => (vs j).set d (((vs j)[a] ^^^ (vs j)[b]).rotateLeft n)
  | .permute d n => fun j => (vs j).set d ((vs ((j + n.val) % 4))[d])

theorem get_set (v : VG.Proof.ChaCha20.AArch64.Rows6.Rows) (d k : Fin 24) (x : Word) :
    (v.set d x)[k] = if k = d then x else v[k] := by
  simp only [Vector.getElem_set, Fin.getElem_fin, Fin.ext_iff, eq_comm]

theorem op_ok (op : VG.Impl.ChaCha20.AArch64.Rows6.Op) {vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows} {s : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.Holds vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (.block op.code) s fun s' => VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.step vs op) s' ∧ VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s s' := by
  cases op with
  | add d a b =>
    apply WP.of_runBlock
    simp only [Op.code, runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne30 d), ite_false]⟩⟩
    simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj]
    split
    · rw [vword_map2 _ _ _ hj, h a j hj, h b j hj]
    · exact h k j hj
  | xorRol d a b n =>
    by_cases h16 : n.val = 16
    · apply WP.of_runBlock
      simp only [Op.code, h16, ite_true, List.cons_append, List.nil_append,
        runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV]
      refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne30 d), ite_false]⟩⟩
      simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne, ite_false, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj]
      split
      · rw [VG.Proof.ChaCha20.AArch64.Neon4.vword_rev32h_rol16 _ hj, VG.Proof.ChaCha20.AArch64.Neon.vword_xor, h a j hj, h b j hj, h16]
      · exact h k j hj
    by_cases h8 : n.val = 8
    · apply WP.of_runBlock
      simp (config := {decide := true}) only [Op.code, h8, ite_true, ite_false, List.cons_append, List.nil_append,
        runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
        Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.v_setV]
      refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
        by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne30 d), ite_false]⟩⟩
      simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne, ite_false, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj]
      split
      · rw [ht, VG.Proof.ChaCha20.AArch64.Neon4.vword_tbl_rol8 _ hj, VG.Proof.ChaCha20.AArch64.Neon.vword_xor, h a j hj, h b j hj, h8]
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
      RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne, Ne.symm (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne d), ite_false]
    refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, by simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne30 d), ite_false]⟩⟩
    simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne, ite_false, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj]
    split
    · rw [vword_map2 _ _ _ hj, vword_map2 _ _ _ hj]
      simp only [VShiftOp.eval, VG.Proof.ChaCha20.AArch64.Neon.shr_mask _ n hn, VG.Proof.ChaCha20.AArch64.Neon.vword_xor,
        h a j hj, h b j hj, BitVec.rotateLeft_def, Nat.mod_eq_of_lt hn, BitVec.or_comm]
    · exact h k j hj

  | permute d n =>
    have hn : 4 * n.val < 16 := by omega
    apply WP.of_runBlock
    simp only [Op.code, runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some,
      hn, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun k j hj => ?_, ⟨⟨rfl,rfl,rfl,rfl,rfl⟩, by
      simp (config := {decide := true}) only [RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne30 d), ite_false]⟩⟩
    simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj]
    split
    · rw [VG.Proof.ChaCha20.AArch64.Neon.vword_ext _ n.val j n.isLt hj,
        h d ((j + n.val) % 4) (Nat.mod_lt _ (by decide))]
    · exact h k j hj

theorem ops_ok : ∀ (ops : List VG.Impl.ChaCha20.AArch64.Rows6.Op) {vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows} {s : State}, VG.Proof.ChaCha20.AArch64.Rows6.Holds vs s →
    s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table →
    WP isa (.block (ops.flatMap Op.code)) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Rows6.Holds (ops.foldl VG.Proof.ChaCha20.AArch64.Rows6.step vs) s' ∧ VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s s'
  | [], _, _, h, _ => WP.block_nil ⟨h, ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl⟩⟩
  | op :: ops, _, _, h, ht => by
    exact WP.block_append ((VG.Proof.ChaCha20.AArch64.Rows6.op_ok op h ht).mono fun _ ⟨h', hs⟩ =>
      (VG.Proof.ChaCha20.AArch64.Rows6.ops_ok ops h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

theorem ror_sub (x : BitVec 32) {n : Nat} (h0 : 0 < n) (hn : n < 32) :
    x.rotateRight (32 - n) = x.rotateLeft n := by
  rw [BitVec.rotateRight_def, BitVec.rotateLeft_def, Nat.mod_eq_of_lt (show 32 - n < 32 by omega),
    Nat.mod_eq_of_lt hn, show 32 - (32 - n) = n by omega, BitVec.or_comm]

/-- `op_ok` for the code with SVE2: an XAR in place of an `xorRol` whose
destination is its first source. -/
theorem op_ok_for (sve : Bool) (op : VG.Impl.ChaCha20.AArch64.Rows6.Op) {vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows} {s : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.Holds vs s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (.block (op.codeFor sve)) s fun s' => VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.step vs op) s' ∧ VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s s' := by
  cases sve with
  | false => exact VG.Proof.ChaCha20.AArch64.Rows6.op_ok op h ht
  | true =>
    cases op with
    | add d a b =>
      rw [show Op.codeFor true (.add d a b) = (Op.add d a b).code from rfl]; exact VG.Proof.ChaCha20.AArch64.Rows6.op_ok _ h ht
    | permute d n =>
      rw [show Op.codeFor true (.permute d n) = (Op.permute d n).code from rfl]; exact VG.Proof.ChaCha20.AArch64.Rows6.op_ok _ h ht
    | xorRol d a b n =>
      by_cases hda : d = a ∧ 0 < n.val
      · obtain ⟨rfl, h0⟩ := hda
        have hn : n.val < 32 := n.isLt
        have hr : 1 ≤ 32 - n.val ∧ 32 - n.val ≤ 32 := ⟨by omega, by omega⟩
        rw [show Op.codeFor true (.xorRol d d b n) = [.vop (.xarS (vreg d) (vreg b) (32 - n.val))]
          from ite_eq_left ⟨rfl, h0⟩]
        apply WP.of_runBlock
        simp only [runBlock_cons, runBlock_nil, exec, VOp.eval, isa, runStep_some, hr, and_self,
          ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
        refine ⟨fun k j hj => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩,
          by simp only [↓reduceIte, RegUpd.v_setV, Ne.symm (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne30 d)]⟩⟩
        simp only [RegUpd.v_setV, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj]
        split
        · rw [vword_map2 _ _ _ hj, h d j hj, h b j hj, VG.Proof.ChaCha20.AArch64.Rows6.ror_sub _ h0 hn]
        · exact h k j hj
      · rw [show Op.codeFor true (.xorRol d a b n) = (Op.xorRol d a b n).code from ite_eq_right hda]
        exact VG.Proof.ChaCha20.AArch64.Rows6.op_ok _ h ht

theorem ops_ok_for (sve : Bool) : ∀ (ops : List VG.Impl.ChaCha20.AArch64.Rows6.Op) {vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows} {s : State}, VG.Proof.ChaCha20.AArch64.Rows6.Holds vs s →
    s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table →
    WP isa (.block (ops.flatMap (Op.codeFor sve))) s fun s' =>
      VG.Proof.ChaCha20.AArch64.Rows6.Holds (ops.foldl VG.Proof.ChaCha20.AArch64.Rows6.step vs) s' ∧ VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s s'
  | [], _, _, h, _ => WP.block_nil ⟨h, ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl⟩⟩
  | op :: ops, _, _, h, ht => by
    exact WP.block_append ((VG.Proof.ChaCha20.AArch64.Rows6.op_ok_for sve op h ht).mono fun _ ⟨h', hs⟩ =>
      (VG.Proof.ChaCha20.AArch64.Rows6.ops_ok_for sve ops h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Rounds`. -/
section

/-! The row permutations and six-block schedule implement ChaCha's double round. -/
namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (Word innerBlock qround)
namespace Symbolic
abbrev E := VG.Proof.ChaCha20.AArch64.Neon4.E
abbrev ES := VG.Proof.ChaCha20.AArch64.Neon4.ES
open VG.Proof.ChaCha20.AArch64.Neon4 (qroundE)

def eval (env : Nat → Word) : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.E → Word
  | .var k => env k
  | .add a b => VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval env a + VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval env b
  | .xor a b => VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval env a ^^^ VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval env b
  | .rol a n => (VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval env a).rotateLeft n

abbrev ER := Nat → Nat → VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.E

def stepE (f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ER) : VG.Impl.ChaCha20.AArch64.Rows6.Op → VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ER
  | .add d a b => fun j k => if k = d.val then .add (f j a) (f j b) else f j k
  | .xorRol d a b n => fun j k =>
      if k = d.val then .rol (.xor (f j a) (f j b)) n else f j k
  | .permute d n => fun j k => if k = d.val then f ((j + n.val) % 4) d else f j k

def Rel (env : Nat → Word) (f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ER) (vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows) : Prop :=
  ∀ k : Fin 24, ∀ j, j < 4 → VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval env (f j k) = (vs j)[k]

theorem Rel.step {env : Nat → Word} {f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ER} {vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows} (h : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.Rel env f vs) (op : VG.Impl.ChaCha20.AArch64.Rows6.Op) :
    VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.Rel env (VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.stepE f op) (VG.Proof.ChaCha20.AArch64.Rows6.step vs op) := by
  intro k j hj
  cases op with
  | add d a b =>
    simp only [VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.stepE, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, Fin.ext_iff]
    split
    · simp only [VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval, h a j hj, h b j hj]
    · exact h k j hj
  | xorRol d a b n =>
    simp only [VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.stepE, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, Fin.ext_iff]
    split
    · simp only [VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval, h a j hj, h b j hj]
    · exact h k j hj
  | permute d n =>
    simp only [VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.stepE, VG.Proof.ChaCha20.AArch64.Rows6.step, VG.Proof.ChaCha20.AArch64.Rows6.get_set, Fin.ext_iff]
    split
    · exact h d _ (Nat.mod_lt _ (by decide))
    · exact h k j hj

theorem Rel.foldl {env : Nat → Word} {f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ER} {vs : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows} (h : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.Rel env f vs) :
    ∀ ops : List VG.Impl.ChaCha20.AArch64.Rows6.Op, VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.Rel env (ops.foldl VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.stepE f) (ops.foldl VG.Proof.ChaCha20.AArch64.Rows6.step vs)
  | [] => h
  | op :: ops => (h.step op).foldl ops

def roundE (f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ES) : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ES :=
  qroundE (qroundE (qroundE (qroundE
    (qroundE (qroundE (qroundE (qroundE f 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15)
    0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14

def vars : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ER := fun j k => .var (16 * (k / 4) + 4 * (k % 4) + j)
def target : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ER := fun j k => VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.roundE (fun w => .var (16 * (k / 4) + w)) (4 * (k % 4) + j)

def equal (f g : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ER) : Bool := (List.finRange 24).all fun k =>
  (List.finRange 4).all fun j => f j k == g j k

theorem schedule_equal : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.equal (roundOps.foldl VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.stepE VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.vars) VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.target = true := by decide +kernel

def LocalRel (env : Nat → Word) (f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ES) (v : CState) : Prop :=
  ∀ k (hk : k < 16), VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval env (f k) = v[k]

theorem LocalRel.set {env : Nat → Word} {f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ES} {v : CState} (h : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.LocalRel env f v)
    {i : Nat} (hi : i < 16) {x : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.E} {y : Word} (hx : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval env x = y) :
    VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.LocalRel env (VG.Proof.ChaCha20.AArch64.Neon4.ES.set f i x) (v.set i y hi) := by
  intro k hk
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.ES.set, Vector.getElem_set]
  by_cases e : k = i
  · subst e; simp [hx]
  · simp only [e, ite_false, Ne.symm e]; exact h k hk

theorem LocalRel.qround {env : Nat → Word} {f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ES} {v : CState} (h : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.LocalRel env f v)
    (x y z w : Fin 16) : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.LocalRel env (qroundE f x y z w) (VG.Spec.ChaCha20.qround v x y z w) := by
  simp only [qroundE]
  refine (((h.set x.isLt ?_).set y.isLt ?_).set z.isLt ?_).set w.isLt ?_ <;>
    simp only [VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.eval, h _ x.isLt, h _ y.isLt, h _ z.isLt, h _ w.isLt, Fin.getElem_fin]

theorem LocalRel.round {env : Nat → Word} {f : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.ES} {v : CState} (h : VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.LocalRel env f v) :
    VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.LocalRel env (VG.Proof.ChaCha20.AArch64.Rows6.Symbolic.roundE f) (innerBlock v) :=
  (((((((h.qround 0 4 8 12).qround 1 5 9 13).qround 2 6 10 14).qround 3 7 11 15)
    |>.qround 0 5 10 15).qround 1 6 11 12).qround 2 7 8 13).qround 3 4 9 14
end Symbolic

def pack (blocks : Nat → CState) : Nat → VG.Proof.ChaCha20.AArch64.Rows6.Rows := fun j => Vector.ofFn fun k : Fin 24 =>
  (blocks (k.val / 4))[4 * (k.val % 4) + j % 4]'(by omega)

theorem pack_get (blocks : Nat → CState) (j : Nat) (k : Fin 24) :
    (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks j)[k] = (blocks (k.val / 4))[4 * (k.val % 4) + j % 4]'(by omega) := by
  simp only [VG.Proof.ChaCha20.AArch64.Rows6.pack, Fin.getElem_fin, Vector.getElem_ofFn]

def env (blocks : Nat → CState) (k : Nat) : Word :=
  (blocks (k / 16))[k % 16]'(Nat.mod_lt _ (by decide))

theorem env_block (blocks : Nat → CState) (b w : Nat) (hw : w < 16) :
    VG.Proof.ChaCha20.AArch64.Rows6.env blocks (16 * b + w) = (blocks b)[w]'hw := by
  have hd : (16 * b + w) / 16 = b := by omega
  have hm : (16 * b + w) % 16 = w := by omega
  simp only [VG.Proof.ChaCha20.AArch64.Rows6.env, hd, hm]

theorem vars_rel (blocks : Nat → CState) : Symbolic.Rel (VG.Proof.ChaCha20.AArch64.Rows6.env blocks) Symbolic.vars (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) := by
  intro k j hj
  simp only [Symbolic.vars, Symbolic.eval, VG.Proof.ChaCha20.AArch64.Rows6.pack_get]
  rw [show 16 * (k.val / 4) + 4 * (k.val % 4) + j =
    16 * (k.val / 4) + (4 * (k.val % 4) + j) by omega,
    VG.Proof.ChaCha20.AArch64.Rows6.env_block blocks _ _ (by omega)]
  simp only [Nat.mod_eq_of_lt hj]

theorem target_rel (blocks : Nat → CState) :
    Symbolic.Rel (VG.Proof.ChaCha20.AArch64.Rows6.env blocks) Symbolic.target (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun b => innerBlock (blocks b))) := by
  intro k j hj
  have h : Symbolic.LocalRel (VG.Proof.ChaCha20.AArch64.Rows6.env blocks) (fun w => .var (16 * (k.val / 4) + w))
      (blocks (k.val / 4)) := fun w hw => VG.Proof.ChaCha20.AArch64.Rows6.env_block blocks _ w hw
  have hr := h.round (4 * (k.val % 4) + j) (by omega)
  simp only [Symbolic.target, VG.Proof.ChaCha20.AArch64.Rows6.pack_get, Nat.mod_eq_of_lt hj]
  exact hr

theorem round_eq (blocks : Nat → CState) (k : Fin 24) (j : Nat) (hj : j < 4) :
    (roundOps.foldl VG.Proof.ChaCha20.AArch64.Rows6.step (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) j)[k] = (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun b => innerBlock (blocks b)) j)[k] := by
  have h := ((VG.Proof.ChaCha20.AArch64.Rows6.vars_rel blocks).foldl VG.Impl.ChaCha20.AArch64.Rows6.roundOps) k j hj
  have he := Symbolic.schedule_equal
  simp only [Symbolic.equal, List.all_eq_true, List.mem_finRange, beq_iff_eq] at he
  rw [he k (by simp) ⟨j,hj⟩ (by simp)] at h
  exact h.symm.trans (VG.Proof.ChaCha20.AArch64.Rows6.target_rel blocks k j hj)

theorem doubleRound_ok {blocks : Nat → CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (.block doubleRound) s fun u =>
      VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun b => innerBlock (blocks b))) u ∧ VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s u := by
  refine (VG.Proof.ChaCha20.AArch64.Rows6.ops_ok VG.Impl.ChaCha20.AArch64.Rows6.roundOps h ht).mono fun u ⟨hu,hs⟩ => ⟨?_,hs⟩
  intro k j hj
  exact (hu k j hj).trans (VG.Proof.ChaCha20.AArch64.Rows6.round_eq blocks k j hj)
theorem rounds_ok {blocks : Nat → CState} {s : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    ∀ n, WP isa (VG.Impl.ChaCha20.AArch64.Rows6.rounds n) s fun u =>
      VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun b => Nat.repeat innerBlock n (blocks b))) u ∧ VG.Proof.ChaCha20.AArch64.Rows6.RoundSame s u
  | 0 => WP.block_nil ⟨h, ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl⟩⟩
  | n + 1 => WP.seq ((VG.Proof.ChaCha20.AArch64.Rows6.rounds_ok h ht n).mono fun _ ⟨h',hs⟩ =>
      (VG.Proof.ChaCha20.AArch64.Rows6.doubleRound_ok h' (hs.v30.trans ht)).mono fun _ ⟨h'',hs'⟩ => ⟨h'',hs.trans hs'⟩)

end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Setup`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (Word stateAt)
abbrev LoadSame := VG.Proof.ChaCha20.AArch64.Neon4.LoadSame

/-- A loaded vector's lane, including the per-block counter offset. -/
def input (s : State) (k : Fin 24) (j : Nat) : Word :=
  let w := s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4) + 4 * j)) 32
  if k.val % 4 = 3 ∧ j = 0 then w + BitVec.ofNat 32 (k.val / 4) else w

theorem input_same {s s' : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s s') (k : Fin 24) (j : Nat) :
    VG.Proof.ChaCha20.AArch64.Rows6.input s' k j = VG.Proof.ChaCha20.AArch64.Rows6.input s k j := by rw [VG.Proof.ChaCha20.AArch64.Rows6.input, h.mem, h.gpr _ (by decide)]; rfl

theorem vword_read16 (m : Mem) (a : Addr) (j : Nat) (hj : j < 4) :
    vword (m.read a 16) j = m.readW (a + BitVec.ofNat 64 (4 * j)) 32 := by
  rw [read16, vword_ofVWords _ _ _ _ hj]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem inputRowInto_ok (s : State) (k : Fin 24) (d : VReg)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block (inputRowInto k d)) s fun u =>
      (∀ j, j < 4 → vword (u.v d) j = VG.Proof.ChaCha20.AArch64.Rows6.input s k j) ∧
      (∀ r, r ≠ d → u.v r = s.v r) ∧ VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s u := by
  have ha : 16 * (k.val % 4) % 16 = 0 ∧ 16 * (k.val % 4) < 4096 * 16 := by omega
  change InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4 at hctr
  have hb : k.val / 4 < 4096 := by omega
  unfold inputRowInto
  split
  · rename_i hk
    apply WP.of_runBlock
    simp (config := {decide := true}) only [List.cons_append, List.nil_append, runBlock_cons, exec, addr,
      ha, ite_true, State.load, State.setV, hin, Option.bind_some, Option.map_some,
      isa, runStep_some]
    simp (config := {decide := true}) only [hctr, ite_true, Option.map_some, runStep_some,
      runBlock_cons, runBlock_nil, exec, hb, VOp.eval, State.read, Size.bits,
      State.write, State.setV, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun j hj => ?_, fun r hr => ?_, fun r hr => ?_,rfl,rfl,rfl,rfl⟩
    · rw [VG.Proof.ChaCha20.AArch64.Neon4.vword_insert _ _ (i := 0) (by decide) hj]
      simp only [VG.Proof.ChaCha20.AArch64.Rows6.input, hk, Nat.reduceMul, true_and]
      by_cases hj0 : j = 0
      · subst j; simp only [ite_true, Nat.mul_zero, Nat.add_zero]
        rfl
      · simp only [hj0, ite_false]
        rw [VG.Proof.ChaCha20.AArch64.Rows6.vword_read16 _ _ j hj, BitVec.add_assoc, ← BitVec.ofNat_add]
    · simp only [hr, ite_false]
    · simp only [hr, ite_false]
  · rename_i hk
    apply WP.of_runBlock
    simp only [List.append_nil, runBlock_cons, runBlock_nil, exec, addr,
      ha, and_self, ite_true, State.load, State.setV, hin, Option.bind_some, Option.map_some,
      isa, runStep_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun j hj => ?_,fun r hr => ?_,fun r hr => ?_,rfl,rfl,rfl,rfl⟩
    · rw [VG.Proof.ChaCha20.AArch64.Rows6.vword_read16 _ _ j hj, BitVec.add_assoc, ← BitVec.ofNat_add]
      simp only [VG.Proof.ChaCha20.AArch64.Rows6.input, hk, false_and, ite_false]
    · exact RegUpd.v_setV_of_ne _ _ hr
    · rfl
structure Loaded (s₀ : State) (ks : List (Fin 24)) (s : State) : Prop where
  words : ∀ k ∈ ks, ∀ j, j < 4 → vword (s.v (vreg k)) j = VG.Proof.ChaCha20.AArch64.Rows6.input s₀ k j
  same : VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s₀ s

theorem setupRow_ok {s₀ s : State} {ks : List (Fin 24)} (h : VG.Proof.ChaCha20.AArch64.Rows6.Loaded s₀ ks s) (k : Fin 24)
    (hin : ∀ k : Fin 24, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + 48) 4) :
    WP isa (.block (setupRow k)) s (VG.Proof.ChaCha20.AArch64.Rows6.Loaded s₀ (k :: ks)) := by
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hin k
  have hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4 := by
    rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hctr
  refine (VG.Proof.ChaCha20.AArch64.Rows6.inputRowInto_ok s k (vreg k) hi hc).mono fun u ⟨hw,hv,hs⟩ => ?_
  refine ⟨fun l hl j hj => ?_, h.same.trans hs⟩
  by_cases e : l = k
  · subst e; rw [hw j hj,VG.Proof.ChaCha20.AArch64.Rows6.input_same h.same]
  · rw [hv _ (fun he => e ((VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj l k).mp he))]
    exact h.words l ((List.mem_cons.mp hl).resolve_left e) j hj

theorem setupList_ok (ks : List (Fin 24)) {s₀ s : State} {done : List (Fin 24)}
    (h : VG.Proof.ChaCha20.AArch64.Rows6.Loaded s₀ done s)
    (hin : ∀ k : Fin 24, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + 48) 4) :
    WP isa (.block (ks.flatMap setupRow)) s fun u =>
      (∀ k ∈ ks ++ done, ∀ j, j < 4 → vword (u.v (vreg k)) j = VG.Proof.ChaCha20.AArch64.Rows6.input s₀ k j) ∧ VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s₀ u := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨h.words,h.same⟩
  | cons k ks ih =>
    refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Rows6.setupRow_ok h k hin hctr).mono fun _ h' => ?_)
    exact (ih h').mono fun _ ⟨hw,hs⟩ => ⟨fun l hl j hj => hw l (by simpa [List.mem_append,
      List.mem_cons,or_assoc,or_left_comm,or_comm] using hl) j hj,hs⟩

theorem setup_words (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Rows6.setup) s fun u =>
      (∀ k : Fin 24, ∀ j, j < 4 → vword (u.v (vreg k)) j = VG.Proof.ChaCha20.AArch64.Rows6.input s k j) ∧
      VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s u ∧ u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  rw [VG.Impl.ChaCha20.AArch64.Rows6.setup]
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Rows6.setupList_ok (List.finRange 24) (done := [])
    ⟨(fun _ h => by cases h),VG.Proof.ChaCha20.AArch64.Neon4.LoadSame.refl s⟩ hin hctr).mono fun a ⟨hw,hs⟩ => ?_)
  refine (VG.Proof.ChaCha20.AArch64.Neon4.setupTable_ok a).mono fun u ⟨ht,hv,has⟩ => ⟨?_,hs.trans has,ht⟩
  intro k j hj
  rw [hv (vreg k) (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne30 k), hw k (by simp) j hj]

theorem input_ctr (s : State) (k : Fin 24) (j : Nat) (hj : j < 4) :
    VG.Proof.ChaCha20.AArch64.Rows6.input s k j = (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun b => ctr (stateAt s.mem (s.gpr .x0)) b) j)[k] := by
  rw [VG.Proof.ChaCha20.AArch64.Rows6.pack_get]
  simp only [Nat.mod_eq_of_lt hj, ctr, Vector.getElem_set, stateAt, Vector.getElem_ofFn]
  have he : (12 = 4 * (k.val % 4) + j) ↔ (k.val % 4 = 3 ∧ j = 0) := by omega
  have hoff : 16 * (k.val % 4) + 4 * j = 4 * (4 * (k.val % 4) + j) := by omega
  simp only [VG.Proof.ChaCha20.AArch64.Rows6.input, he, hoff]
  split
  · rename_i h
    rcases h with ⟨hrow,hj0⟩
    simp only [hrow,hj0]
  · rfl

theorem setup_ok (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Rows6.setup) s fun u =>
      VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun b => ctr (stateAt s.mem (s.gpr .x0)) b)) u ∧
      VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s u ∧ u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  refine (VG.Proof.ChaCha20.AArch64.Rows6.setup_words s hin hctr).mono fun u ⟨hu,hs,ht⟩ => ⟨?_,hs,ht⟩
  intro k j hj
  exact (hu k j hj).trans (VG.Proof.ChaCha20.AArch64.Rows6.input_ctr s k j hj)

end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Add`. -/
section

/-! Feed the original input into the six row-oriented round results. -/
namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (Word)

theorem addRow_ok (s : State) (k : Fin 24)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block (addRow k)) s fun u =>
      (∀ j, j < 4 → vword (u.v (vreg k)) j = vword (s.v (vreg k)) j + VG.Proof.ChaCha20.AArch64.Rows6.input s k j) ∧
      (∀ r, r ≠ vreg k → r ≠ .v31 → u.v r = s.v r) ∧ VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s u := by
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Rows6.inputRowInto_ok s k .v31 hin hctr).mono fun a ⟨hw,hv,hs⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons,runBlock_nil,exec,VOp.eval,isa,runStep_some,
    Option.map_some,Option.some.injEq,exists_eq_left']
  refine ⟨fun j hj => ?_,fun r hr h31 => ?_,?_,hs.mem,hs.rd,hs.wr,hs.sp⟩
  · rw [RegUpd.v_setV_self,vword_map2 _ _ _ hj,hv _ (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne k),hw j hj]
  · rw [RegUpd.v_setV_of_ne _ _ hr,hv r h31]
  · intro r hr
    exact hs.gpr r hr

structure Added (s₀ : State) (done : List (Fin 24)) (s : State) : Prop where
  words : ∀ k : Fin 24, ∀ j, j < 4 → vword (s.v (vreg k)) j =
    vword (s₀.v (vreg k)) j + if k ∈ done then VG.Proof.ChaCha20.AArch64.Rows6.input s₀ k j else 0
  same : VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s₀ s

theorem addList_ok (ks : List (Fin 24)) (hn : ks.Nodup) {s₀ s : State} {done : List (Fin 24)}
    (h : VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ done s) (hf : ∀ k ∈ ks, k ∉ done)
    (hin : ∀ k : Fin 24, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + 48) 4) :
    WP isa (.block (ks.flatMap addRow)) s (VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ (ks ++ done)) := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil h
  | cons k ks ih =>
    have hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
      rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hin k
    have hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4 := by
      rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hctr
    apply WP.block_append
    refine (VG.Proof.ChaCha20.AArch64.Rows6.addRow_ok s k hi hc).mono fun a ⟨hw,hv,hs⟩ => ?_
    have h' : VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ (k :: done) a := by
      refine ⟨fun l j hj => ?_,h.same.trans hs⟩
      by_cases he : l = k
      · subst l
        rw [hw j hj,h.words k j hj,VG.Proof.ChaCha20.AArch64.Rows6.input_same h.same]
        simp [hf k (List.mem_cons_self ..)]
      · rw [hv _ (fun e => he ((VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj l k).mp e)) (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne l),h.words l j hj]
        simp only [List.mem_cons,he,false_or]
    have hf' : ∀ l ∈ ks, l ∉ k :: done := by
      intro l hl
      simp only [List.mem_cons,not_or]
      exact ⟨fun he => (List.nodup_cons.mp hn).1 (he ▸ hl),hf l (List.mem_cons_of_mem _ hl)⟩
    refine (ih (List.nodup_cons.mp hn).2 h' hf').mono fun u hu => ?_
    refine ⟨fun l j hj => ?_,hu.same⟩
    simpa only [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hu.words l j hj

end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6

/-- Add a common state row without rereading it for each block. -/
theorem cachedAdd_ok {s₀ s : State} {done : List (Fin 24)} (h : VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ done s)
    (k : Fin 24) (hk : k ∉ done)
    (hc : ∀ j, j < 4 → vword (s.v .v31) j = VG.Proof.ChaCha20.AArch64.Rows6.input s₀ k j) :
    WP isa (.block [.vop (.add .s4 (vreg k) (vreg k) .v31)]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ (k :: done) u ∧ u.v .v31 = s.v .v31 := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runBlock_nil,exec,VOp.eval,isa,runStep_some,
    Option.map_some,Option.some.injEq,exists_eq_left']
  refine ⟨⟨fun l j hj => ?_,⟨h.same.gpr,h.same.mem,h.same.rd,h.same.wr,h.same.sp⟩⟩,?_⟩
  · by_cases he : l = k
    · subst l
      rw [RegUpd.v_setV_self,vword_map2 _ _ _ hj,h.words k j hj,hc j hj]
      simp only [hk,ite_false,List.mem_cons_self,ite_true]
      exact congrArg (fun x => x + VG.Proof.ChaCha20.AArch64.Rows6.input s₀ k j) (BitVec.add_zero _)
    · rw [RegUpd.v_setV_of_ne _ _ (fun e => he ((VG.Proof.ChaCha20.AArch64.Rows6.vreg_inj l k).mp e)),h.words l j hj]
      simp only [List.mem_cons,he,false_or]
  · exact RegUpd.v_setV_of_ne _ _ (Ne.symm (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne k))

theorem cachedAdds_ok (ks : List (Fin 24)) (hn : ks.Nodup) {s₀ s : State}
    {done : List (Fin 24)} (h : VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ done s) (hf : ∀ k ∈ ks, k ∉ done)
    (hc : ∀ k ∈ ks, ∀ j, j < 4 → vword (s.v .v31) j = VG.Proof.ChaCha20.AArch64.Rows6.input s₀ k j) :
    WP isa (.block (ks.map fun k => Instr.vop (.add .s4 (vreg k) (vreg k) .v31))) s
      (VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ (ks ++ done)) := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil h
  | cons k ks ih =>
    change WP isa (.block (([Instr.vop (.add .s4 (vreg k) (vreg k) .v31)] : List Instr) ++
      ks.map fun k => Instr.vop (.add .s4 (vreg k) (vreg k) .v31))) s _
    apply WP.block_append
    refine (VG.Proof.ChaCha20.AArch64.Rows6.cachedAdd_ok h k (hf _ (List.mem_cons_self ..))
      (hc _ (List.mem_cons_self ..))).mono
      fun a ⟨ha,hcache⟩ => ?_
    refine (ih (List.nodup_cons.mp hn).2 ha (fun l hl => ?_)
      (fun l hl j hj => by rw [hcache]; exact hc l (List.mem_cons_of_mem _ hl) j hj)).mono
      fun u hu => ?_
    · simp only [List.mem_cons,not_or]
      exact ⟨fun he => (List.nodup_cons.mp hn).1 (he ▸ hl),hf l (List.mem_cons_of_mem _ hl)⟩
    · refine ⟨fun l j hj => ?_,hu.same⟩
      simpa only [List.mem_append,List.mem_cons,or_assoc,or_left_comm] using hu.words l j hj

def rowKeys (r : Fin 4) : List (Fin 24) := (List.finRange 6).map (fun b => row b r)

theorem rowKeys_nodup (r : Fin 4) : (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys r).Nodup := by
  exact (by decide +kernel : ∀ r : Fin 4, (rowKeys r).Nodup) r

theorem rowKeys_mod (r : Fin 4) (k : Fin 24) (hk : k ∈ VG.Proof.ChaCha20.AArch64.Rows6.rowKeys r) : k.val % 4 = r.val := by
  exact (by decide +kernel : ∀ r : Fin 4, ∀ k : Fin 24, k ∈ rowKeys r → k.val % 4 = r.val) r k hk

theorem cachedFeedRow_ok (r : Fin 3) {s₀ s : State} {done : List (Fin 24)}
    (h : VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ done s) (hf : ∀ k ∈ VG.Proof.ChaCha20.AArch64.Rows6.rowKeys ⟨r.val, by omega⟩, k ∉ done)
    (hin : ∀ k : Fin 24, InRegions (s₀.rd ++ s₀.wr)
      (s₀.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + 48) 4) :
    WP isa (.block (cachedFeedRow r)) s (VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys ⟨r.val, by omega⟩ ++ done)) := by
  let k : Fin 24 := ⟨r.val, by omega⟩
  have hm : k.val % 4 = r.val := Nat.mod_eq_of_lt (by change r.val < 4; omega)
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hin k
  have hc : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4 := by
    rw [h.same.rd,h.same.wr,h.same.gpr _ (by decide)]; exact hctr
  have he : cachedFeedRow r = inputRowInto k .v31 ++
      ((VG.Proof.ChaCha20.AArch64.Rows6.rowKeys ⟨r.val, by omega⟩).map fun l => Instr.vop (.add .s4 (vreg l) (vreg l) .v31)) := by
    simp only [cachedFeedRow,inputRowInto,hm,show ¬r.val = 3 by omega,ite_false,
      List.append_nil,VG.Proof.ChaCha20.AArch64.Rows6.rowKeys,List.map_map]
    rfl
  rw [he]
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Rows6.inputRowInto_ok s k .v31 hi hc).mono fun a ⟨hw,hv,hs⟩ => ?_
  have ha : VG.Proof.ChaCha20.AArch64.Rows6.Added s₀ done a := ⟨fun l j hj => by rw [hv _ (VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne l)]; exact h.words l j hj,
    h.same.trans hs⟩
  refine VG.Proof.ChaCha20.AArch64.Rows6.cachedAdds_ok _ (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys_nodup _) ha hf ?_
  intro l hl j hj
  rw [hw j hj,VG.Proof.ChaCha20.AArch64.Rows6.input_same h.same]
  simp only [VG.Proof.ChaCha20.AArch64.Rows6.input,hm,VG.Proof.ChaCha20.AArch64.Rows6.rowKeys_mod _ l hl,show ¬(r.val = 3 ∧ j = 0) by omega,ite_false]

theorem feedForward_ok (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4) :
    WP isa (.block feedForward) s fun u =>
      (∀ k : Fin 24, ∀ j, j < 4 → vword (u.v (vreg k)) j =
        vword (s.v (vreg k)) j + VG.Proof.ChaCha20.AArch64.Rows6.input s k j) ∧ VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s u := by
  have h : VG.Proof.ChaCha20.AArch64.Rows6.Added s [] s := ⟨fun _ _ _ => by simp,
    VG.Proof.ChaCha20.AArch64.Neon4.LoadSame.refl s⟩
  unfold feedForward
  rw [List.append_assoc,List.append_assoc]
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Rows6.cachedFeedRow_ok 0 h (fun _ _ h => by cases h) hin hctr).mono fun a ha => ?_
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Rows6.cachedFeedRow_ok 1 ha (by decide +kernel) hin hctr).mono fun b hb => ?_
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Rows6.cachedFeedRow_ok 2 hb (by decide +kernel) hin hctr).mono fun c hc => ?_
  change WP isa (.block ((VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 3).flatMap addRow)) c _
  refine (VG.Proof.ChaCha20.AArch64.Rows6.addList_ok (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 3) (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys_nodup 3) hc (by decide +kernel) hin hctr).mono
    fun u hu => ⟨?_,hu.same⟩
  intro k j hj
  have hall : k ∈ VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 3 ++ (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 2 ++ (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 1 ++ (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 0 ++ []))) := by
    exact (by decide +kernel : ∀ k : Fin 24,
      k ∈ rowKeys 3 ++ (rowKeys 2 ++ (rowKeys 1 ++ (rowKeys 0 ++ [])))) k
  have hw := hu.words k j hj
  change vword (u.v (vreg k)) j = vword (s.v (vreg k)) j +
    if k ∈ VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 3 ++ (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 2 ++ (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 1 ++ (VG.Proof.ChaCha20.AArch64.Rows6.rowKeys 0 ++ []))) then VG.Proof.ChaCha20.AArch64.Rows6.input s k j else 0 at hw
  simpa only [hall,ite_true] using hw

end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Store`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Neon4 (xor_write_apply)

structure StoreSame (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  v : ∀ k : Fin 24, s'.v (vreg k) = s.v (vreg k)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem StoreSame.trans {s₀ s₁ s₂ : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.StoreSame s₀ s₁) (h' : VG.Proof.ChaCha20.AArch64.Rows6.StoreSame s₁ s₂) :
    VG.Proof.ChaCha20.AArch64.Rows6.StoreSame s₀ s₂ := ⟨h'.gpr.trans h.gpr, fun k => (h'.v k).trans (h.v k),
      h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem xorRow_ok (s : State) (k : Fin 24)
    (hout : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block (xorRow k)) s fun u =>
      u.mem = s.mem.write (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16
        (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 ^^^ s.v (vreg k)) ∧ VG.Proof.ChaCha20.AArch64.Rows6.StoreSame s u := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    obtain ⟨q,hq,hc⟩ := hout; exact ⟨q,List.mem_append_right _ hq,hc⟩
  have ha : 16 * k.val % 16 = 0 ∧ 16 * k.val < 4096 * 16 := by omega
  apply WP.of_runBlock
  simp only [xorRow,runBlock_cons,runBlock_nil,exec,addr,ha,and_self,ite_true,State.load,hin,
    Option.bind_some,Option.map_some,isa,runStep_some,RegUpd.gpr_setV,RegUpd.v_setV,
    VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne,ite_false,VOp.eval,State.store,RegUpd.wr_setV,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl⟩
  intro l
  simp only [RegUpd.v_setV,VG.Proof.ChaCha20.AArch64.Rows6.vreg_ne,ite_false]

/-- A sequence of distinct, aligned vector stores, tracked by their 16-byte slot. -/
def Data (m₀ m : Mem) (p : Addr) (out : Nat → BitVec 128) (done : List Nat) : Prop :=
  ∀ x, m x = if (x - p).toNat / 16 ∈ done ∧ (x - p).toNat < 384
    then m₀ x ^^^ (out ((x - p).toNat / 16)).extractLsb' (8 * ((x - p).toNat % 16)) 8
    else m₀ x

theorem Data.nil (m : Mem) (p : Addr) (out : Nat → BitVec 128) : VG.Proof.ChaCha20.AArch64.Rows6.Data m m p out [] := by
  intro x; simp only [List.not_mem_nil, false_and, ite_false]

theorem Data.store {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : VG.Proof.ChaCha20.AArch64.Rows6.Data m₀ m p out done) {n : Nat} (hn : n < 24) (hfresh : n ∉ done) :
    VG.Proof.ChaCha20.AArch64.Rows6.Data m₀ (m.write (p + BitVec.ofNat 64 (16 * n)) 16
      (m.read (p + BitVec.ofNat 64 (16 * n)) 16 ^^^ out n)) p out (n :: done) := by
  intro x
  rw [xor_write_apply]
  simp only [Offset.lt_iff x p (by omega : 16 * n + 16 ≤ 2 ^ 64)]
  rw [h x]
  have hx := (x - p).isLt
  by_cases he : (x - p).toNat / 16 = n ∧ (x - p).toNat < 384
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
    by_cases hb : (x - p).toNat < 384
    · have hn' : (x - p).toNat / 16 ≠ n := by omega
      simp only [List.mem_cons, hn', false_or]
    · simp only [hb, and_false, ite_false]

theorem xorList_ok (ks : List (Fin 24)) (hn : ks.Nodup)
    {m₀ : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat} {s : State}
    (hd : VG.Proof.ChaCha20.AArch64.Rows6.Data m₀ s.mem p out done) (hp : s.gpr .x1 = p)
    (hv : ∀ k : Fin 24, s.v (vreg k) = out k.val)
    (hfresh : ∀ k ∈ ks, k.val ∉ done)
    (hout : ∀ k ∈ ks, InRegions s.wr (p + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block (ks.flatMap xorRow)) s fun u =>
      VG.Proof.ChaCha20.AArch64.Rows6.Data m₀ u.mem p out (ks.map Fin.val ++ done) ∧ VG.Proof.ChaCha20.AArch64.Rows6.StoreSame s u := by
  induction ks generalizing s done with
  | nil => exact WP.block_nil ⟨hd,rfl,fun _ => rfl,rfl,rfl,rfl⟩
  | cons k ks ih =>
    have ho : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
      rw [hp]; exact hout k (List.mem_cons_self ..)
    apply WP.block_append
    refine (VG.Proof.ChaCha20.AArch64.Rows6.xorRow_ok s k ho).mono fun a ⟨hm,hs⟩ => ?_
    have hd' : VG.Proof.ChaCha20.AArch64.Rows6.Data m₀ a.mem p out (k.val :: done) := by
      rw [hm,hp,hv k]; exact hd.store k.isLt (hfresh k (List.mem_cons_self ..))
    have hp' : a.gpr .x1 = p := by rw [hs.gpr,hp]
    have hv' : ∀ l : Fin 24, a.v (vreg l) = out l.val := by intro l; rw [hs.v,hv]
    have hf' : ∀ l ∈ ks, l.val ∉ k.val :: done := by
      intro l hl
      simp only [List.mem_cons,not_or]
      exact ⟨fun e => (List.nodup_cons.mp hn).1 ((Fin.ext e) ▸ hl),
        hfresh l (List.mem_cons_of_mem _ hl)⟩
    have ho' : ∀ l ∈ ks, InRegions a.wr (p + BitVec.ofNat 64 (16 * l.val)) 16 := by
      intro l hl; rw [hs.wr]; exact hout l (List.mem_cons_of_mem _ hl)
    refine (ih (List.nodup_cons.mp hn).2 hd' hp' hv' hf' ho').mono fun u ⟨hu,hau⟩ => ⟨?_,hs.trans hau⟩
    intro x
    simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Data,List.map_cons,List.cons_append,List.mem_append,List.mem_cons,or_assoc,
      or_left_comm] using hu x
end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Finish`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Neon4 (output output_word byte_vword)

theorem output_byte (vs : Nat → CState) (k : Nat) :
    (output vs (k / 16)).extractLsb' (8 * (k % 16)) 8 =
      (VG.Spec.ChaCha20.serialize (vs (k / 64))).getD (k % 64) 0 := by
  rw [byte_vword _ (by omega),output_word _ _ (by omega),
    VG.Proof.ChaCha20.serialize_getD _ (by omega)]
  simp only [show k / 16 / 4 = k / 64 by omega,
    show 4 * (k / 16 % 4) + k % 16 / 4 = k % 64 / 4 by omega,
    show k % 16 % 4 = k % 64 % 4 by omega]

theorem Data.frame {m₀ m : Mem} {p : Addr} {out : Nat → BitVec 128} {done : List Nat}
    (h : VG.Proof.ChaCha20.AArch64.Rows6.Data m₀ m p out done) : Frame [⟨p,384⟩] m₀ m := by
  intro x hx
  have hn : ¬ (x - p).toNat < 384 := by
    have hh := hx ⟨p,384⟩ (List.mem_cons_self ..)
    simp only [Region.Contains] at hh
    omega
  rw [h x,ite_eq_right (fun h => hn h.2)]

theorem finishBlocks_ok {s : State} {blocks : Nat → CState} (h : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s)
    (hout : ∀ k : Fin 24, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa (.block ((List.finRange 24).flatMap xorRow)) s fun u =>
      (∀ k < 384, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (VG.Spec.ChaCha20.serialize (blocks (k / 64))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1,384⟩] s.mem u.mem ∧ VG.Proof.ChaCha20.AArch64.Rows6.StoreSame s u := by
  have hv : ∀ k : Fin 24, s.v (vreg k) = output blocks k.val := by
    intro k
    apply vec_ext
    intro j hj
    rw [h k j hj,VG.Proof.ChaCha20.AArch64.Rows6.pack_get,output_word _ _ hj]
    simp only [Nat.mod_eq_of_lt hj]
  refine (VG.Proof.ChaCha20.AArch64.Rows6.xorList_ok (List.finRange 24) (List.nodup_finRange 24)
    (Data.nil s.mem (s.gpr .x1) (output blocks)) rfl hv
    (fun _ _ => List.not_mem_nil) (fun k _ => hout k)).mono fun u ⟨hu,hs⟩ => ⟨?_,hu.frame,hs⟩
  intro k hk
  have hm : k / 16 ∈ (List.finRange 24).map Fin.val ++ [] := by
    apply List.mem_append_left
    exact List.mem_map_of_mem (f := Fin.val) (List.mem_finRange (⟨k / 16,by omega⟩ : Fin 24))
  rw [hu _,Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64),ite_eq_left ⟨hm,hk⟩,VG.Proof.ChaCha20.AArch64.Rows6.output_byte]
end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Chunk`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (stateAt serialize block)
abbrev ChunkKeep := VG.Proof.ChaCha20.AArch64.Neon4.ChunkKeep

theorem chunk_ok (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4)
    (hout : ∀ k : Fin 24, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa VG.Impl.ChaCha20.AArch64.Rows6.chunk s fun u =>
      (∀ k < 384, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (serialize (VG.Spec.ChaCha20.block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1,384⟩] s.mem u.mem ∧ VG.Proof.ChaCha20.AArch64.Rows6.ChunkKeep s u := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Rows6.setup_ok s hin hctr).mono fun a ⟨ha,hsa,hta⟩ => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Rows6.rounds_ok ha hta 10).mono fun b ⟨hb,hab⟩ => ?_
  have hsb : VG.Proof.ChaCha20.AArch64.Rows6.LoadSame s b := hsa.trans
    ⟨fun r _ => congrFun hab.gpr r,hab.mem,hab.rd,hab.wr,hab.sp⟩
  have hi : ∀ k : Fin 24, InRegions (b.rd ++ b.wr)
      (b.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    intro k; rw [hsb.rd,hsb.wr,hsb.gpr _ (by decide)]; exact hin k
  have hc : InRegions (b.rd ++ b.wr) (b.gpr .x0 + 48) 4 := by
    rw [hsb.rd,hsb.wr,hsb.gpr _ (by decide)]; exact hctr
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Rows6.feedForward_ok b hi hc).mono fun c ⟨hfeed,hbc⟩ => ?_
  have hsc := hsb.trans hbc
  have hblocks : VG.Proof.ChaCha20.AArch64.Rows6.Holds (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => VG.Spec.ChaCha20.block (ctr (stateAt s.mem (s.gpr .x0)) j))) c := by
    intro k j hj
    rw [hfeed k j hj,hb k j hj,VG.Proof.ChaCha20.AArch64.Rows6.input_same hsb,VG.Proof.ChaCha20.AArch64.Rows6.input_ctr s k j hj]
    simp only [VG.Proof.ChaCha20.AArch64.Rows6.pack_get,VG.Spec.ChaCha20.block,Vector.getElem_zipWith]
  have ho : ∀ k : Fin 24, InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k; rw [hsc.wr,hsc.gpr _ (by decide)]; exact hout k
  refine (VG.Proof.ChaCha20.AArch64.Rows6.finishBlocks_ok hblocks ho).mono fun u ⟨hu,hf,hs⟩ => ⟨?_,?_,?_⟩
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4),hsc.mem] using hu
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4),hsc.mem] using hf
  · exact ⟨fun r hr => by rw [hs.gpr]; exact hsc.gpr r hr,
      hs.rd.trans hsc.rd,hs.wr.trans hsc.wr,hs.sp.trans hsc.sp⟩
end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Lit`. -/
section

namespace VG
materialize_code Impl.ChaCha20.AArch64.Rows6.xor
end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Loop`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20 (ctr keystream_getD)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream serialize block)

theorem less6 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n >>> 6) - BitVec.ofNat 64 6) >>> 63 =
      BitVec.ofNat 64 (if n < 384 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  have hd : n / 2 ^ 6 < 2 ^ 58 := by omega
  by_cases h : n < 384
  · rw [ite_eq_left h]
    have hb : n / 2 ^ 6 < 6 := by omega
    omega
  · rw [ite_eq_right h]
    have hb : 6 ≤ n / 2 ^ 6 := by omega
    omega

theorem check_ok (s : State) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Rows6.check) s fun u =>
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat < 384 then 1 else 0) ∧
      (∀ r, r ≠ .x5 → u.gpr r = s.gpr r) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, VG.Impl.ChaCha20.AArch64.Rows6.check, runBlock_cons, runBlock_nil, exec,
    State.read, Size.bits, isa, runStep_some, RegUpd.gpr_write,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨?_,fun r hr => by simp only [hr,ite_false],rfl,rfl,rfl,rfl,rfl⟩
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using VG.Proof.ChaCha20.AArch64.Rows6.less6 (s.gpr .x2).toNat (s.gpr .x2).isLt


/-- Before six-block chunk t. x0/x3 and all but the two scratch registers
are retained, except the advancing data pointer and remaining length. -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  x0 : s.gpr .x0 = st s₀
  x1 : s.gpr .x1 = dp s₀ + BitVec.ofNat 64 (384 * t)
  x2 : s.gpr .x2 = BitVec.ofNat 64 (L s₀ - 384 * t)
  x3 : s.gpr .x3 = bp s₀
  le : 384 * t ≤ L s₀
  keep : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : stateAt s.mem (st s₀) = ctr (S0 s₀) (6 * t)
  data : ∀ k < L s₀, s.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 384 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem ctr_add (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.getElem_set_self, Vector.set_set, BitVec.ofNat_add, BitVec.add_assoc]

theorem ks_shift (S : CState) {len t k : Nat} (hk : k < len) (ht : 384 * t ≤ k) :
    (keystream S len).getD k 0 =
      (serialize (VG.Spec.ChaCha20.block (ctr (ctr S (6 * t)) ((k - 384 * t) / 64)))).getD
        ((k - 384 * t) % 64) 0 := by
  rw [keystream_getD _ hk, VG.Proof.ChaCha20.AArch64.Rows6.ctr_add, show 6 * t + (k - 384 * t) / 64 = k / 64 by omega,
    show (k - 384 * t) % 64 = k % 64 by omega]

 theorem next_ok (s : State) (hlen : 384 ≤ (s.gpr .x2).toNat)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4)
    (hout : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 48) 4) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Rows6.next) s fun u =>
      u.gpr .x1 = s.gpr .x1 + 384 ∧ u.gpr .x2 = s.gpr .x2 - 384 ∧
      u.gpr .x5 = BitVec.ofNat 64 (if (s.gpr .x2).toNat - 384 < 384 then 1 else 0) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → u.gpr r = s.gpr r) ∧
      stateAt u.mem (s.gpr .x0) = ctr (stateAt s.mem (s.gpr .x0)) 6 ∧
      Frame [⟨s.gpr .x0,64⟩] s.mem u.mem ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul, Nat.reduceMod, and_self, VG.Impl.ChaCha20.AArch64.Rows6.next,VG.Impl.ChaCha20.AArch64.Rows6.check,
    List.cons_append,List.nil_append,runBlock_cons,runBlock_nil,exec,
    addr,Size.bytes,Size.bits,State.load,hin,State.read,RegUpd.gpr_write,
    RegUpd.wr_write,RegUpd.mem_write,RegUpd.rd_write,RegUpd.sp_write,
    Option.bind_some,Option.map_some,isa,runStep_some,BitVec.setWidth_setWidth_of_le,
    BitVec.setWidth_eq,State.store,hout,Option.some.injEq,exists_eq_left']
  refine ⟨rfl,rfl,?_,?_,?_,?_,trivial⟩
  · have he : s.gpr .x2 - BitVec.ofNat 64 384 = BitVec.ofNat 64 ((s.gpr .x2).toNat - 384) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub,BitVec.toNat_ofNat]
      have h := (s.gpr .x2).isLt; omega
    rw [he,VG.Proof.ChaCha20.AArch64.Rows6.less6 _ (by have h := (s.gpr .x2).isLt; omega)]
  · intro r h1 h2 h4 h5; simp only [h1,h2,h4,h5,ite_false]
  · have ht := VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr s.mem (s.gpr .x0) 6
    simp only [Mem.writeW,Mem.readW,BitVec.setWidth_eq] at ht
    exact ht
  · exact (Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 48 + 4 ≤ 64) (by decide))

abbrev win (s₀ : State) (t : Nat) : Region := ⟨dp s₀ + BitVec.ofNat 64 (384 * t), 384⟩

theorem win_sub {s₀ : State} {t : Nat} (h : 384 * t + 384 ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Rows6.win s₀ t) (dR s₀) := Offset.sub_base _ h

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have h := Xor.L_lt s₀; omega)

theorem chunkData {s₀ s u : State} {t : Nat} (h : VG.Proof.ChaCha20.AArch64.Rows6.LInv s₀ t s)
    (hge : 384 * t + 384 ≤ L s₀)
    (hu : ∀ k < 384, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
      s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (VG.Spec.ChaCha20.block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0)
    (hf : Frame [⟨s.gpr .x1, 384⟩] s.mem u.mem) :
    ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 384 * (t + 1) then D0 s₀ k ^^^ (KS s₀).getD k 0 else D0 s₀ k := by
  intro k hk
  have hL := Xor.L_lt s₀
  by_cases hin : 384 * t ≤ k ∧ k < 384 * t + 384
  · have he : s.gpr .x1 + BitVec.ofNat 64 (k - 384 * t) = dp s₀ + BitVec.ofNat 64 k := by
      rw [h.x1, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hin.1]
    have hh := hu (k - 384 * t) (by omega)
    rw [he, h.data k hk, ite_eq_right (by omega), h.x0, h.cnt, ← VG.Proof.ChaCha20.AArch64.Rows6.ks_shift (S0 s₀) hk hin.1] at hh
    rw [ite_eq_left (by omega)]; exact hh
  · have hx : ¬ (VG.Proof.ChaCha20.AArch64.Rows6.win s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
      simp only [Region.Contains, Nat.add_one_le_iff]
      rw [Offset.lt_iff _ _ (by omega), Mem.sub_ofNat_toNat _ (by omega : k < 2 ^ 64)]
      exact hin
    have hh := hf (dp s₀ + BitVec.ofNat 64 k) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r; rw [h.x1]; exact hx)
    rw [hh, h.data k hk]
    by_cases hold : k < 384 * t
    · rw [ite_eq_left hold, ite_eq_left (by omega)]
    · rw [ite_eq_right hold, ite_eq_right (by omega)]

theorem body_ok {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 384 * t + 384 ≤ L s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.LInv s₀ t s) :
    WP isa VG.Impl.ChaCha20.AArch64.Rows6.body s fun s' => VG.Proof.ChaCha20.AArch64.Rows6.LInv s₀ (t + 1) s' ∧
      s'.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 384 * (t + 1) < 384 then 1 else 0) := by
  have hL := Xor.L_lt s₀
  have hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    intro k; rw [h.rd,h.wr,hp.rd,hp.wr,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  have hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [h.rd,h.wr,hp.rd,hp.wr,h.x0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hout : ∀ k : Fin 24, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k; rw [h.wr,hp.wr,h.x1,BitVec.add_assoc,← BitVec.ofNat_add]
    exact ⟨dR s₀,by simp,Offset.contains_base _ (by omega) (by omega)⟩
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Rows6.chunk_ok s hin hctr hout).mono fun u ⟨hu, hf, hs⟩ => ?_
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (6 * t) := by
    rw [← h.cnt]
    apply Xor.stateAt_frame hf
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    rw [h.x1]; exact hp.st_d.sub_right (VG.Proof.ChaCha20.AArch64.Rows6.win_sub hge)
  have hdata := VG.Proof.ChaCha20.AArch64.Rows6.chunkData h hge hu hf
  have hx0 : u.gpr .x0 = st s₀ := (hs.gpr _ (by decide)).trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (384 * t) := (hs.gpr _ (by decide)).trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 384 * t) := (hs.gpr _ (by decide)).trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := (hs.gpr _ (by decide)).trans h.x3
  have hw : u.wr = [stR s₀, dR s₀, bR s₀] := hs.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hs.rd, h.rd, hp.rd, hw, hx0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw, hx0]
    exact ⟨stR s₀, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 384 * t := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine (VG.Proof.ChaCha20.AArch64.Rows6.next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1, hv2, hv5, hkeep, hctr, hframe, hrd, hwr, hsp⟩ => ?_
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (384 * (t + 1)) := by
    rw [hv1, hx1, BitVec.add_assoc]
    congr 1
    change BitVec.ofNat 64 (384 * t) + BitVec.ofNat 64 384 = _
    rw [← BitVec.ofNat_add, show 384 * t + 384 = 384 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 384 * (t + 1)) := by
    rw [hv2, hx2]
    change BitVec.ofNat 64 (L s₀ - 384 * t) - BitVec.ofNat 64 384 = _
    rw [Offset.ofNat_sub_ofNat (by omega), show L s₀ - 384 * t - 384 = L s₀ - 384 * (t + 1) by omega]
  refine ⟨⟨?_, hptr, hrem, ?_, by omega, ?_, hrd.trans (hs.rd.trans h.rd),
    hwr.trans (hs.wr.trans h.wr), hsp.trans (hs.sp.trans h.sp), ?_, ?_, ?_⟩, ?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide), hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide), hx3]
  · intro r h1 h2 h4 h5
    rw [hkeep r h1 h2 h4 h5, hs.gpr r h4]; exact h.keep r h1 h2 h4 h5
  · rw [hx0, hcnt, VG.Proof.ChaCha20.AArch64.Rows6.ctr_add, show 6 * t + 6 = 6 * (t + 1) by omega] at hctr
    exact hctr
  · intro k hk
    rw [hframe _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact fun hn => hp.st_d _ hn (VG.Proof.ChaCha20.AArch64.Rows6.data_in hk)), hdata k hk]
  · have hf' : Frame [stR s₀, dR s₀] s.mem u.mem := hf.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      refine ⟨dR s₀, by simp, ?_⟩; rw [h.x1]; exact VG.Proof.ChaCha20.AArch64.Rows6.win_sub hge)
    have hn' : Frame [stR s₀, dR s₀] u.mem v.mem := hframe.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact List.mem_cons_self ..)
    exact (h.frame.trans hf').trans hn'
  · rw [hv5, hlen, show L s₀ - 384 * t - 384 = L s₀ - 384 * (t + 1) by omega]

theorem init_ok (s : State) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Rows6.check) s fun u => VG.Proof.ChaCha20.AArch64.Rows6.LInv s 0 u ∧
      u.gpr .x5 = BitVec.ofNat 64 (if L s < 384 then 1 else 0) := by
  refine (VG.Proof.ChaCha20.AArch64.Rows6.check_ok s).mono fun u ⟨h5,hg,hm,hr,hw,hv,hsp⟩ => ⟨?_,h5⟩
  refine ⟨hg _ (by decide),?_,?_,hg _ (by decide),by omega,?_,hr,hw,hsp,?_,?_,?_⟩
  · rw [hg _ (by decide)]; simp [dp]
  · rw [hg _ (by decide)]; simp [L]
  · intro r _ _ _ h5; exact hg r h5
  · rw [hm]; exact (VG.Proof.ChaCha20.ctr_zero _).symm
  · intro k _; rw [hm]; simp only [Nat.mul_zero,Nat.not_lt_zero,ite_false]
  · rw [hm]; exact Frame.refl _ _

theorem bulk_ok {s₀ : State} (hp : XPre s₀) {s : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.LInv s₀ 0 s)
    (hx5 : s.gpr .x5 = BitVec.ofNat 64 (if L s₀ < 384 then 1 else 0)) :
    WP isa (.ite (.nonzero .x .x5) (.block []) (.loop VG.Impl.ChaCha20.AArch64.Rows6.body (.zero .x .x5))) s fun u =>
      ∃ t, L s₀ - 384 * t < 384 ∧ VG.Proof.ChaCha20.AArch64.Rows6.LInv s₀ t u := by
  have hL := Xor.L_lt s₀
  have he := Xor.eval_nonzero_ofNat s .x5 (by split <;> omega) hx5
  have he' : isa.eval (.nonzero .x .x5) s = some (decide (L s₀ < 384)) := by
    by_cases hl : L s₀ < 384 <;> simpa [hl] using he
  apply WP.ite (decide (L s₀ < 384)) he'
  · intro hb
    have hb' := of_decide_eq_true hb
    exact WP.block_nil ⟨0,by simpa using hb',h⟩
  · intro hb
    have hge : 384 ≤ L s₀ := by have := of_decide_eq_false hb; omega
    let Inv : Nat → State → Prop := fun n s =>
      ∃ t, n = L s₀ - 384 * t ∧ 384 ≤ n ∧ VG.Proof.ChaCha20.AArch64.Rows6.LInv s₀ t s
    refine WP.loop (M := isa) Inv ?_ (L s₀) s ⟨0,by omega,hge,h⟩
    intro n s ⟨t,hn,hge,hi⟩
    refine (VG.Proof.ChaCha20.AArch64.Rows6.body_ok hp (by omega) hi).mono fun u ⟨hu,h5⟩ => ?_
    have hc : isa.eval (.zero .x .x5) u =
        some (decide ((if L s₀ - 384 * (t + 1) < 384 then 1 else 0) = 0)) := by
      change VG.AArch64.eval (.zero .x .x5) u = _
      rw [Xor.eval_zero u .x5,h5,Xor.ofNat_beq_zero (by split <;> omega)]
    by_cases hl : L s₀ - 384 * (t + 1) < 384
    · left
      refine ⟨?_,t + 1,hl,hu⟩
      simpa [hl] using hc
    · right
      refine ⟨?_,L s₀ - 384 * (t + 1),by omega,t + 1,rfl,by omega,hu⟩
      simpa [hl] using hc

end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Tail`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6

open VG VG.AArch64
open VG.Proof.ChaCha20 (ctr length_keystream keystream_getD bytesAt_xor xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Spec.ChaCha20 (stateAt keystream bytesAt)

abbrev tailR (s₀ : State) (t : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (384 * t), L s₀ - 384 * t⟩

theorem tail_sub {s₀ : State} {t : Nat} (ht : 384 * t ≤ L s₀) :
    Region.Sub (VG.Proof.ChaCha20.AArch64.Rows6.tailR s₀ t) (dR s₀) := Offset.sub_base _ (by omega)

theorem not_tail {s₀ : State} {t k : Nat} (hk : k < 384 * t) (ht : 384 * t ≤ L s₀) :
    ¬ (VG.Proof.ChaCha20.AArch64.Rows6.tailR s₀ t).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
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

theorem tail_ok {s₀ : State} (hp : XPre s₀) {t : Nat} {s : State} (h : VG.Proof.ChaCha20.AArch64.Rows6.LInv s₀ t s) :
    WP isa Impl.ChaCha20.AArch64.Small.xor s fun s' =>
      GprAbi s₀ s' ∧ xorAArch64.post s₀ s' ∧
      s'.gpr .x0 = s₀.gpr .x0 ∧ s'.gpr .x1 = s₀.gpr .x3 := by
  have hL := Xor.L_lt s₀
  have hle := h.le
  have hn : (BitVec.ofNat 64 (L s₀ - 384 * t)).toNat = L s₀ - 384 * t :=
    by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let wr := [stR s₀, VG.Proof.ChaCha20.AArch64.Rows6.tailR s₀ t, bR s₀]
  have hs : xorAArch64.pre (s.withRegions [] wr) := by
    simp only [xorAArch64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      h.x0, h.x1, h.x2, h.x3, hn]
    have ts := VG.Proof.ChaCha20.AArch64.Rows6.tail_sub h.le
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
    · exact ⟨dR s₀, by simp, 384 * t, rfl, by dsimp; omega⟩
    · exact ⟨bR s₀, by simp, 0, by simp, by simp⟩
  have hw : WP isa Impl.ChaCha20.AArch64.Small.xor (s.withRegions [] wr) fun u =>
      abiPreserved (s.withRegions [] wr) u ∧ xorAArch64.post (s.withRegions [] wr) u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 :=
    VG.Proof.ChaCha20.AArch64.Small.correct _ hs
  refine WP.narrow hw ?_ hc ?_ VG.Proof.ChaCha20.AArch64.Small.xor_noFrames
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
        fun hh => hp.st_d _ hh (VG.Proof.ChaCha20.AArch64.Rows6.data_in hk)
      have nb : ¬ (bR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.d_b _ (VG.Proof.ChaCha20.AArch64.Rows6.data_in hk) hh
      by_cases hk' : k < 384 * t
      · rw [hf _ (by
          intro r hr; simp only [wr, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact ns
          · exact VG.Proof.ChaCha20.AArch64.Rows6.not_tail hk' h.le
          · exact nb), h.data k hk, ite_eq_left hk']
      · have ea : dp s₀ + BitVec.ofNat 64 (384 * t) + BitVec.ofNat 64 (k - 384 * t) =
            dp s₀ + BitVec.ofNat 64 k := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
        have x := VG.Proof.ChaCha20.AArch64.Rows6.bytes_of_bytesAt (length_keystream _ _) hpost (k := k - 384 * t) (by omega)
        rw [ea, h.data k hk, ite_eq_right hk', keystream_getD _ (by omega)] at x
        rw [x, VG.Proof.ChaCha20.AArch64.Rows6.ks_shift _ hk (t := t) (by omega)]

theorem raw_correct (s : State) (hp : xorAArch64.pre s) :
    WP isa Impl.ChaCha20.AArch64.Rows6.raw s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧ u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Rows6.init_ok s).mono fun u ⟨hi,h5⟩ => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Rows6.bulk_ok (XPre.of s hp) hi h5).mono fun v ⟨t,_,hv⟩ => ?_
  exact VG.Proof.ChaCha20.AArch64.Rows6.tail_ok (XPre.of s hp) hv

end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)

theorem read_write_self (m : Mem) (p : Addr) (v : BitVec 128) :
    (m.write p 16 v).read p 16 = v := by
  have h := Mem.readW_writeW_self m p 16 v (by decide)
  simpa only [Mem.readW,Mem.writeW,BitVec.setWidth_eq] using h

theorem save_ok (s : State) (hp : XPre s) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Rows6.save) s fun u =>
      u.gpr = s.gpr ∧ u.v = s.v ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame [bR s] s.mem u.mem ∧
      u.mem.read (bp s + BitVec.ofNat 64 256) 16 = s.v .v8 ∧
      u.mem.read (bp s + BitVec.ofNat 64 272) 16 = s.v .v9 := by
  have ho (d : Nat) (hd : d + 16 ≤ 320) : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [hp.wr]
    exact ⟨bR s,by simp,Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp only [↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Impl.ChaCha20.AArch64.Rows6.save,runBlock_cons,runBlock_nil,exec,addr,
    State.store,ho 256 (by decide),ho 272 (by decide),
    Option.bind_some,Option.some.injEq,exists_eq_left',isa,runStep_some]
  refine ⟨trivial,trivial,trivial,trivial,trivial,?_,?_,?_⟩
  · exact ((Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 256 + 16 ≤ 320) (by decide))).write
      (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide : 272 + 16 ≤ 320) (by decide))
  · rw [Mem.read_write_sep (Offset.sep (bp s) (d := 256) (n := 16) (e := 272) (k := 16)
      (by decide) (by decide) (by decide)) (by decide),VG.Proof.ChaCha20.AArch64.Rows6.read_write_self]
  · exact VG.Proof.ChaCha20.AArch64.Rows6.read_write_self _ _ _

theorem restore_ok {s : State} (v8 v9 : BitVec 128)
    (hi0 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 256) 16)
    (hi1 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 272) 16)
    (hm0 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 256) 16 = v8)
    (hm1 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 272) 16 = v9) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Rows6.restore) s fun u =>
      u.v .v8 = v8 ∧ u.v .v9 = v9 ∧ u.gpr = s.gpr ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.ChaCha20.AArch64.Rows6.restore,runBlock_cons,runBlock_nil,exec,addr,
    ite_true,State.load,hi0,hi1,State.setV,hm0,hm1,Option.bind_some,Option.map_some,
    Option.some.injEq,exists_eq_left',isa,runStep_some]
  trivial
end VG.Proof.ChaCha20.AArch64.Rows6

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Xor`. -/
section

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20 (xorAArch64)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)
open VG.Spec.ChaCha20 (stateAt bytesAt)

/-- The six other callee-saved vectors are never destinations. -/
def keepsOtherV (i : Instr) : Bool :=
  match vdstOf i with
  | some .v10 | some .v11 | some .v12 | some .v13 | some .v14 | some .v15 => false
  | _ => true

theorem keepsOtherV_ne {i : Instr} (hi : VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV i = true) {r : VReg}
    (hr : r ∈ preservedV) (h8 : r ≠ .v8) (h9 : r ≠ .v9) : vdstOf i ≠ some r := by
  intro he
  unfold VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV at hi
  rw [he] at hi
  cases r <;> simp_all [preservedV]

theorem post_save {s a u : State} (hp : XPre s) (hg : a.gpr = s.gpr)
    (hf : Frame [bR s] s.mem a.mem) (hpost : xorAArch64.post a u) :
    xorAArch64.post s u := by
  have hs : stateAt a.mem (st s) = stateAt s.mem (st s) :=
    Xor.stateAt_frame hf (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hp.st_b)
  have hd : bytesAt a.mem (dp s) (L s) = bytesAt s.mem (dp s) (L s) := by
    unfold bytesAt
    apply List.map_congr_left
    intro k hk
    have hk' := List.mem_range.mp hk
    exact hf.bytes (R := dR s) (by intro r hr; have he := List.mem_singleton.mp hr; subst r; exact hp.d_b)
      (by have := Xor.L_lt s; dsimp; omega) hk'
  simpa only [xorAArch64,hg,hs,hd] using hpost

theorem correct_aux (s : State) (hs : xorAArch64.pre s) :
    WP isa VG.Impl.ChaCha20.AArch64.Rows6.xor s fun u =>
      GprAbi s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 ∧
      (u.v .v8).extractLsb' 0 64 = (s.v .v8).extractLsb' 0 64 ∧
      (u.v .v9).extractLsb' 0 64 = (s.v .v9).extractLsb' 0 64 := by
  let hp := XPre.of s hs
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Rows6.save_ok s hp).mono fun a ⟨hag,hav,har,haw,has,haf,ha8,ha9⟩ => ?_
  have hpre : xorAArch64.pre a := by simpa only [xorAArch64,hag,har,haw] using hs
  let hap := XPre.of a hpre
  apply WP.seq
  have hb : WP isa VG.Impl.ChaCha20.AArch64.Rows6.bulk a fun v => ∃ t, VG.Proof.ChaCha20.AArch64.Rows6.LInv a t v := by
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Rows6.init_ok a).mono fun b ⟨hi,h5⟩ => ?_
    exact (VG.Proof.ChaCha20.AArch64.Rows6.bulk_ok hap hi h5).mono fun v ⟨t,_,hv⟩ => ⟨t,hv⟩
  refine hb.mono fun v ⟨t,hv⟩ => ?_
  apply WP.seq
  have hdis : ∀ r ∈ [stR a,dR a], (bR a).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact hap.st_b.symm
    · exact hap.d_b.symm
  have read_saved (d : Nat) (hd : d + 16 ≤ 320) :
      v.mem.read (v.gpr .x3 + BitVec.ofNat 64 d) 16 =
        a.mem.read (bp s + BitVec.ofNat 64 d) 16 := by
    rw [hv.x3,hv.frame.read (Offset.contains_base _ hd (by omega)) hdis (by decide)]
    rw [show bp a = bp s by simp only [bp,hag]]
  have hin (d : Nat) (hd : d + 16 ≤ 320) :
      InRegions (v.rd ++ v.wr) (v.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [hv.rd,hv.wr,hap.rd,hap.wr,hv.x3]
    exact ⟨bR a,by simp,Offset.contains_base _ hd (by omega)⟩
  refine (VG.Proof.ChaCha20.AArch64.Rows6.restore_ok (s.v .v8) (s.v .v9) (hin 256 (by decide)) (hin 272 (by decide))
    ((read_saved 256 (by decide)).trans ha8) ((read_saved 272 (by decide)).trans ha9)).mono
    fun w ⟨hw8,hw9,hg,hm,hr,hw,hsp⟩ => ?_
  have hwi : VG.Proof.ChaCha20.AArch64.Rows6.LInv a t w := by
    exact ⟨by rw [hg]; exact hv.x0,by rw [hg]; exact hv.x1,
      by rw [hg]; exact hv.x2,by rw [hg]; exact hv.x3,hv.le,
      by intro r h1 h2 h4 h5; rw [hg]; exact hv.keep r h1 h2 h4 h5,
      hr.trans hv.rd,hw.trans hv.wr,hsp.trans hv.sp,
      by rw [hm]; exact hv.cnt,by rw [hm]; exact hv.data,by rw [hm]; exact hv.frame⟩
  refine (WP.preservedV (VG.Proof.ChaCha20.AArch64.Rows6.tail_ok hap hwi) (hc := by lit_decide)).mono ?_
  intro u ⟨⟨ha,hpost,h0,h1⟩,hvec⟩
  refine ⟨⟨?_,ha.2.trans has⟩,VG.Proof.ChaCha20.AArch64.Rows6.post_save hp hag haf hpost,?_,?_,?_,?_⟩
  · intro r hr; rw [ha.1 r hr,hag]
  · exact h0.trans (congrFun hag .x0)
  · exact h1.trans (congrFun hag .x3)
  · rw [hvec .v8 (by decide),hw8]
  · rw [hvec .v9 (by decide),hw9]

theorem correct (s : State) (hs : xorAArch64.pre s) :
    WP isa VG.Impl.ChaCha20.AArch64.Rows6.xor s fun u => abiPreserved s u ∧ xorAArch64.post s u ∧
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x3 := by
  obtain ⟨t,u,he,ha,hp,h0,h1,h8,h9⟩ := VG.Proof.ChaCha20.AArch64.Rows6.correct_aux s hs
  refine ⟨t,u,he,⟨ha.1,ha.2,?_⟩,hp,h0,h1⟩
  intro r hr
  by_cases he8 : r = .v8
  · subst r; exact h8
  by_cases he9 : r = .v9
  · subst r; exact h9
  have hc : xor.allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true := by lit_decide
  rw [Exec.vec (fun i hi => VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV_ne (List.all_eq_true.mp
    ((Code.allInstrs_eq VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV VG.Impl.ChaCha20.AArch64.Rows6.xor) ▸ hc) i hi) hr he8 he9) he]

theorem xor_correct (s : State) (hs : xorAArch64.pre s) :
    ∃ t u, Exec isa VG.Impl.ChaCha20.AArch64.Rows6.xor s t u ∧ abiPreserved s u ∧ xorAArch64.post s u :=
  (VG.Proof.ChaCha20.AArch64.Rows6.correct s hs).imp fun _ ⟨u,he,ha,hp,_⟩ => ⟨u,he,ha,hp⟩

theorem xor_noFrames : xor.noFrames = true := by lit_decide

theorem xor_ct : ConstantTime isa xorAArch64.pre xorAArch64.pub VG.Impl.ChaCha20.AArch64.Rows6.xor := by
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3])
    (fun _ _ _ _ hp => Xor.agree₀ hp) (by taint_decide)

theorem xor_verified : Verified AArch64.target VG.Impl.ChaCha20.AArch64.Rows6.xor
    (Spec.ChaCha20.xorContract AArch64.abi) :=
  Verified.of_correct VG.Proof.ChaCha20.AArch64.Rows6.xor_correct VG.Proof.ChaCha20.AArch64.Rows6.xor_ct
    (by sig_implies [Spec.ChaCha20.xorContract,Spec.ChaCha20.xorSig,AArch64.abi,AArch64.argRegs,
      xorAArch64] [Xor.sat] using Xor.sat)

end VG.Proof.ChaCha20.AArch64.Rows6

end
