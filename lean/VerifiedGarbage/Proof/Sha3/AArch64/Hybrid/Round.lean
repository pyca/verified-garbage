module

public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.MemLower
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lower
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Control
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.TCB.AArch64.Isa
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Sha3.AArch64.Scalar.MemCoreExec`, which only this module used -/

section

/-!
# The scalar round with its temporary lanes in memory, run

`lowerMem off` (`Impl/Sha3/AArch64/Scalar/MemLower.lean`) realizes each
abstract operation with the temporary lanes in the words at `[sp, #off]`
and `[sp, #off + 8]`: the round computes `χ ∘ π ∘ ρ ∘ θ` on
the lanes in general registers (`mem_core_ok`), writes only those two
words of memory, and leaves every vector register as it was.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

theorem exec_strSp {s : VG.AArch64.State} {t : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.sp + BitVec.ofNat 64 off) 8) :
    exec (.strSp t off) s =
      some { s with mem := s.mem.writeW (s.sp + BitVec.ofNat 64 off) (s.gpr t) } := by
  simp only [exec, ho, and_self, ite_true, State.store, h, Mem.writeW]
  rfl

/-- The abstract file's registers in the registers, and its two temporary
lanes in the words at `sp + off` and `sp + off + 8`. -/
structure MemFileRel (off : Nat) (f : File) (s : VG.AArch64.State) : Prop where
  regs : ∀ r, s.gpr r = f.regs r
  slots : ∀ k < 2, s.mem.readW (s.sp + BitVec.ofNat 64 (off + 8 * k)) 64 = f.slots k

/-- The two words are writable, at an offset `ldr`/`str` encode. -/
structure SlotsOk (off : Nat) (s : VG.AArch64.State) : Prop where
  align : off % 8 = 0
  small : off + 8 < 32768
  wr : ∀ k < 2, InRegions s.wr (s.sp + BitVec.ofNat 64 (off + 8 * k)) 8

private theorem write_gpr (s : VG.AArch64.State) (d r : Reg) (v : BitVec 64) :
    (s.write .x d v).gpr r = if r = d then v else s.gpr r := by
  simp only [RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq]

/-- Every operation realizes its abstract one, writing at most the two words. -/
theorem mem_step_ok {off : Nat} (op : ScalarOp) (hg : Good op) (f : File) (s : VG.AArch64.State)
    (hr : MemFileRel off f s) (ho : SlotsOk off s) :
    ∃ s', runBlock isa (lowerMem off op) s = some s' ∧ MemFileRel off (step f op) s' ∧
      Frame [⟨s.sp, off + 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.v = s.v := by
  have ha := ho.align
  have hsm := ho.small
  cases op with
  | spill k a =>
    have hk := hg.1
    have hoff : (off + 8 * k) % 8 = 0 ∧ off + 8 * k < 32768 := ⟨by omega_using [ha], by omega_using [hsm, hk]⟩
    refine ⟨{ s with mem := s.mem.writeW (s.sp + BitVec.ofNat 64 (off + 8 * k)) (s.gpr a) }, ?_,
      ⟨hr.regs, fun j hj => ?_⟩, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [lowerMem, runBlock_cons, exec_strSp hoff (ho.wr k hk), runStep_some, runBlock_nil]
    · change (s.mem.writeW _ _).readW _ 64 = _
      simp only [step]
      by_cases he : j = k
      · subst j
        rw [Mem.readW_writeW_self64, ite_eq_left rfl, hr.regs]
      · rw [ite_eq_right he, Mem.readW_writeW_sep (w' := 64)
          (Offset.sep _ (by omega_using [he]) (by omega_using [hsm, hj]) (by omega_using [hsm, hk])) (by decide)]
        exact hr.slots j hj
    · exact (Frame.refl _ _).writeW (r := ⟨s.sp, off + 16⟩) (by simp) _
        (Offset.contains_base _ (by omega_using [hk]) (by omega_using [hsm, hk]))
  | reload d k =>
    have hk := hg.1
    have hoff : (off + 8 * k) % 8 = 0 ∧ off + 8 * k < 32768 := ⟨by omega_using [ha], by omega_using [hsm, hk]⟩
    have hin : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (off + 8 * k)) 8 := by
      obtain ⟨r, hr', hc⟩ := ho.wr k hk
      exact ⟨r, List.mem_append_right _ hr', hc⟩
    refine ⟨s.write .x d (s.mem.readW (s.sp + BitVec.ofNat 64 (off + 8 * k)) 64), ?_,
      ⟨fun r => ?_, hr.slots⟩, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
    · simp only [lowerMem, runBlock_cons, exec_ldrSp hoff hin, runStep_some, runBlock_nil]
    · simp only [step, File.write, write_gpr, hr.slots k hk]
      split <;> simp only [hr.regs]
  | _ =>
    obtain ⟨s', hs, hregs, hm, hrd, hwr, hsp, hv⟩ :=
      reg_lower_ok _ hg (by intro k r h; cases h) (by intro r k h; cases h) f s hr.regs
    refine ⟨s', hs, ⟨hregs, fun k hk => ?_⟩, ?_, hrd, hwr, hsp, hv⟩
    · rw [hm, hsp]; exact hr.slots k hk
    · rw [hm]; exact Frame.refl _ _

private theorem block_append' (xs ys : List Instr) (s : VG.AArch64.State) :
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    change (isa.exec x s).bind (fun s' => runBlock isa (xs ++ ys) s') =
      ((isa.exec x s).bind (runBlock isa xs)).bind (runBlock isa ys)
    rw [Option.bind_assoc]
    exact congrArg (Option.bind (isa.exec x s)) (funext fun s' => ih s')

theorem mem_list_ok {off : Nat} (ops : List ScalarOp) (hg : ∀ op ∈ ops, Good op)
    (f : File) (s : VG.AArch64.State) (hr : MemFileRel off f s) (ho : SlotsOk off s) :
    ∃ s', runBlock isa (ops.flatMap (lowerMem off)) s = some s' ∧ MemFileRel off (run ops f) s' ∧
      Frame [⟨s.sp, off + 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.v = s.v := by
  induction ops generalizing f s with
  | nil => exact ⟨s, rfl, hr, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | cons op ops ih =>
    obtain ⟨s₁, hs₁, hr₁, hf₁, hrd₁, hwr₁, hsp₁, hv₁⟩ :=
      mem_step_ok op (hg op (List.mem_cons_self ..)) f s hr ho
    have ho₁ : SlotsOk off s₁ := ⟨ho.align, ho.small, fun k hk => by rw [hwr₁, hsp₁]; exact ho.wr k hk⟩
    obtain ⟨s₂, hs₂, hr₂, hf₂, hrd₂, hwr₂, hsp₂, hv₂⟩ :=
      ih (fun op ho => hg op (List.mem_cons_of_mem _ ho)) (step f op) s₁ hr₁ ho₁
    refine ⟨s₂, ?_, hr₂, hf₁.trans (by rw [← hsp₁]; exact hf₂), hrd₂.trans hrd₁, hwr₂.trans hwr₁,
      hsp₂.trans hsp₁, hv₂.trans hv₁⟩
    simp only [List.flatMap_cons, block_append', hs₁, Option.bind_some, hs₂]

/-- The memory-slot core has the lane semantics of the round through chi. -/
theorem mem_core_ok {off : Nat} (A : Spec.Sha3.State) (s : VG.AArch64.State)
    (hl : ∀ i : Nat, (hi : i < 25) → s.gpr (laneReg i) = A[i]) (ho : SlotsOk off s) :
    ∃ s', runBlock isa (memCoreInstrs off) s = some s' ∧
      (∀ i : Nat, (hi : i < 25) → s'.gpr (laneReg i) =
        (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))[i]) ∧
      Frame [⟨s.sp, off + 16⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.v = s.v := by
  let f : File := ⟨s.gpr, fun k => s.mem.readW (s.sp + BitVec.ofNat 64 (off + 8 * k)) 64⟩
  have hr : MemFileRel off f s := ⟨fun _ => rfl, fun _ _ => rfl⟩
  have hmath := core_math A f hl
  obtain ⟨s', hs, hr', hf, hrd, hwr, hsp, hv⟩ := mem_list_ok coreOps core_good f s hr ho
  exact ⟨s', hs, fun i hi => (hr'.regs (laneReg i)).trans (hmath i hi), hf, hrd, hwr, hsp, hv⟩

end VG.Proof.Sha3.AArch64.Scalar

end

end

/-! ### `Sha3.AArch64.Hybrid.Comm`, which only this module used -/

section

/-!
# AArch64: vector-only and scalar-only instructions commute

The instructions of a two-state SHA-3 round read and write only vector
registers (`vecOnly`); those of a scalar Keccak round read and write only
general registers and memory, through the stack pointer for its spills
(`scalarOnly`). Any two such instructions commute (`comm`), so any
interleaving of the two rounds runs as one round and then the other
(`indeps`, with `VG.Interleave.run_merge`).
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Hybrid
open VG VG.AArch64

/-- The vector operations that read and write only vector registers. -/
def vopVecOnly : VOp → Bool
  | .logic .. | .eor3 .. | .bcax .. | .rax1 .. | .xar .. => true
  | _ => false

def vecOnly : Instr → Bool
  | .vop op => vopVecOnly op
  | _ => false

/-- The scalar instructions of the class: general registers, flags left
alone, memory only at the stack pointer. -/
def scalarOnly : Instr → Bool
  | .logic .. | .logicRor .. | .bicRor .. | .ror .. | .addImm .. | .movz .. | .movk ..
  | .ldrSp .. | .strSp .. => true
  | _ => false

theorem VOp.eval_congr {op : VOp} (h : vopVecOnly op = true) {s t : State} (hv : s.v = t.v) :
    op.eval s = op.eval t := by
  cases op <;> simp only [vopVecOnly, reduceCtorEq] at h <;> simp only [reduceVOpEval, hv]

theorem exec_setV {y : Instr} (h : scalarOnly y = true) (s : State) (d : VReg) (x : BitVec 128) :
    exec y (s.setV d x) = (exec y s).map (·.setV d x) := by
  cases y <;> simp only [scalarOnly, reduceCtorEq] at h
  case ldrSp t off =>
    simp only [reduceExec, State.load]
    by_cases ho : off % 8 = 0 ∧ off < 32768
    · by_cases hi : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8
      · simp only [ho, hi, and_self, ite_true, Option.map_some, State.setV, State.write]
      · simp [ho, hi, State.setV]
    · simp only [ho, ite_false, Option.map_none]
  case strSp t off =>
    simp only [reduceExec, State.store]
    by_cases ho : off % 8 = 0 ∧ off < 32768
    · by_cases hi : InRegions s.wr (s.sp + BitVec.ofNat 64 off) 8
      · simp only [ho, hi, and_self, ite_true, Option.map_some, State.setV, State.read]
      · simp [ho, hi, State.setV]
    · simp only [ho, ite_false, Option.map_none]
  all_goals
    simp only [reduceExec]
    first
    | (split <;> simp only [Option.map_some, Option.map_none, State.setV, State.write, State.read])
    | simp only [Option.map_some, State.setV, State.write, State.read]

theorem exec_v {y : Instr} (h : scalarOnly y = true) {s s' : State} (e : exec y s = some s') :
    s'.v = s.v := by
  cases y <;> simp only [scalarOnly, reduceCtorEq] at h <;>
    simp only [reduceExec, State.load, State.store] at e <;> (try split_ifs at e) <;>
    (try simp only [Option.some.injEq, Option.map_some] at e) <;> (try cases e) <;> (try subst e) <;> rfl

private theorem exec_vop (op : VOp) (s : State) :
    exec (.vop op) s = (op.eval s).map fun p => s.setV p.1 p.2 := rfl

theorem comm {x y : Instr} (hx : vecOnly x = true) (hy : scalarOnly y = true) :
    VG.Interleave.CommuteOn isa (fun _ => True) x y := by
  intro s _
  cases x <;> simp only [vecOnly, reduceCtorEq] at hx
  rename_i op
  show (exec (.vop op) s).bind (exec y) = (exec y s).bind (exec (.vop op))
  rw [exec_vop]
  cases hy' : exec y s with
  | none =>
    cases he : op.eval s with
    | none => rfl
    | some p => simp only [Option.map_some, Option.bind_some, exec_setV hy, hy', Option.map_none,
        Option.bind_none]
  | some s' =>
    simp only [Option.bind_some, exec_vop, VOp.eval_congr hx (exec_v hy hy')]
    cases he : op.eval s with
    | none => rfl
    | some p => simp only [Option.map_some, Option.bind_some, exec_setV hy, hy']

/-- A block of vector-only instructions and one of scalar-only ones are independent. -/
theorem indeps {a b : List Instr} (ha : a.all vecOnly = true) (hb : b.all scalarOnly = true) :
    VG.Interleave.Indeps isa (fun _ => True) a b :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial, fun x hx y hy =>
    comm (List.all_eq_true.mp ha x hx) (List.all_eq_true.mp hb y hy)⟩

end VG.Proof.Sha3.AArch64.Hybrid

end

end


/-!
# A round of Keccak-f[1600] on three states

`Hybrid.round off r` (`Impl/Sha3/AArch64/Hybrid/Round.lean`) runs round `r`
on the two states in the vector registers (`Neon.Hw.Pairs`) and on the
state in the general registers (`Scalar.laneReg`), writing no memory but the
scalar round's two temporary words at `[sp, #off]`: the woven cores run as
the vector core and then the scalar one (`Hybrid.indeps`), and iota follows
for all three from the constant in `x26`.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Hybrid
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Neon.Hw
open VG.Proof.Sha3.AArch64.Neon (Pairs vreg_inj pair_xor)
open VG.Proof.Sha3.AArch64.Sha3.Vector (chiWord)
open VG.Proof.MlKem.AArch64 (wp_vop)

abbrev laneReg := VG.Impl.Sha3.AArch64.Scalar.laneReg

theorem vecCore_vecOnly : Impl.Sha3.AArch64.Hybrid.vecCore.all vecOnly = true := by decide

theorem memCore_scalarOnly (off : Nat) :
    (Impl.Sha3.AArch64.Scalar.memCoreInstrs off).all scalarOnly = true := by
  unfold Impl.Sha3.AArch64.Scalar.memCoreInstrs
  rw [List.all_flatMap]
  refine List.all_eq_true.mpr fun op _ => ?_
  cases op <;> rfl

/-- Round `r` on the three states. -/
theorem round_ok {off r : Nat} (hr : r < 24) {s : State} {A B C : Spec.Sha3.State}
    (hp : Pairs s A B) (hl : ∀ i (hi : i < 25), s.gpr (laneReg i) = C[i])
    (ho : Scalar.SlotsOk off s) :
    WP isa (.block (Impl.Sha3.AArch64.Hybrid.round off r)) s fun t =>
      Pairs t (Spec.Sha3.rnd A r) (Spec.Sha3.rnd B r) ∧
      (∀ i (hi : i < 25), t.gpr (laneReg i) = (Spec.Sha3.rnd C r)[i]) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨s.sp, off + 16⟩] s.mem t.mem := by
  unfold Impl.Sha3.AArch64.Hybrid.round
  rw [List.append_assoc, WP.block_append_iff]
  refine VG.Interleave.WP.weave (P := fun _ => True)
    (indeps vecCore_vecOnly (memCore_scalarOnly off)) trivial ?_
  refine WP.mono (core2_ok hp) fun t ⟨hk, hc⟩ => ?_
  have ho' : Scalar.SlotsOk off t := ⟨ho.align, ho.small, fun k hk' => by
    rw [hk.wr, hk.sp]; exact ho.wr k hk'⟩
  obtain ⟨u, hu, hlu, hf, hrd, hwr, hsp, hv⟩ :=
    Scalar.mem_core_ok C t (fun i hi => by rw [hk.gpr]; exact hl i hi) ho'
  refine WP.of_runBlock ⟨u, hu, ?_⟩
  rw [WP.block_append_iff]
  refine (Scalar.Control.constant_ok (Spec.Sha3.RC r) u).mono fun w ⟨hkw, hw⟩ => ?_
  rw [Sha3.Vector.constantLow_RC r hr] at hw
  unfold Impl.Sha3.AArch64.Hybrid.iota
  refine WP.cons rfl ?_
  refine wp_vop (d := .v26) rfl fun s1 h1 => wp_vop (d := .v0) rfl fun t2 h2 =>
    WP.block_nil_iff.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The vector states: CPairs after the cores, kept by the scalar code.
    have hcw : CPairs w A B := by
      intro i hi; rw [hkw.vec, hv]; exact hc i hi
    have hrc : (w.write .x .x0 (w.read .x .x0 ^^^ w.read .x .x26)).gpr .x26 = Spec.Sha3.RC r := by
      simp only [RegUpd.gpr_write, State.read, Size.bits, BitVec.setWidth_eq, reduceCtorEq,
        ite_false, hw]
    intro i hi
    rw [← Proof.Sha3.outState_eq A r, ← Proof.Sha3.outState_eq B r, out_word A _ hi, out_word B _ hi]
    by_cases h0 : i = 0
    · subst i
      change t2.v .v0 = ofVDwords (chiWord A 0 ^^^ _) (chiWord B 0 ^^^ _)
      rw [h2.v, h1.get .v0, h1.v, hrc]
      change (w.write .x .x0 _).v .v0 ^^^ ofVDwords (Spec.Sha3.RC r) (Spec.Sha3.RC r) = _
      rw [RegUpd.v_write, show w.v .v0 = _ from hcw 0 (by decide), pair_xor]
    · rw [ite_eq_right h0, ite_eq_right h0, h2.get (vreg i) (by
        change ¬ vreg i = vreg 0
        rw [vreg_inj i (by omega_using [hi]) 0 (by decide)]; exact h0), h1.get (vreg i)
        ((show ∀ i < 25, vreg i ≠ .v26 by decide) i hi), RegUpd.v_write]
      exact hcw i hi
  · -- The scalar state: chi's lanes, then iota on lane 0.
    intro i hi
    have h26 := Scalar.scratch_not_lane .x26 (by simp) i hi
    have h0 : w.gpr .x0 = (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta C))))[0] :=
      (hkw.gpr .x0 (by decide)).trans (hlu 0 (by decide))
    rw [h2.gpr, h1.gpr]
    simp only [RegUpd.gpr_write, State.read, Size.bits, BitVec.setWidth_eq]
    by_cases hz : i = 0
    · subst i
      simp only [Impl.Sha3.AArch64.Scalar.laneReg, ite_true, h0, hw, Spec.Sha3.rnd, Spec.Sha3.iota,
        Vector.getElem_set_self]
    · have hr0 : laneReg i ≠ .x0 := by
        intro he; exact hz ((Scalar.laneReg_zero i hi).mp he)
      simp only [hr0, ite_false, hkw.gpr _ h26, hlu i hi, Spec.Sha3.rnd, Spec.Sha3.iota,
        Vector.getElem_set, Ne.symm hz]
  · rw [h2.sp, h1.sp]; exact (hkw.sp.trans hsp).trans hk.sp
  · rw [h2.rd, h1.rd]; exact (hkw.rd.trans hrd).trans hk.rd
  · rw [h2.wr, h1.wr]; exact (hkw.wr.trans hwr).trans hk.wr
  · rw [h2.mem, h1.mem]
    change Frame _ s.mem w.mem
    rw [hkw.mem, ← hk.mem, ← hk.sp]
    exact hf

/-- Rounds `rs` on the three states. -/
theorem rounds_list_ok {off : Nat} (rs : List Nat) (hrs : ∀ r ∈ rs, r < 24) {s : State}
    {A B C : Spec.Sha3.State} (hp : Pairs s A B) (hl : ∀ i (hi : i < 25), s.gpr (laneReg i) = C[i])
    (ho : Scalar.SlotsOk off s) :
    WP isa (.block (rs.flatMap (Impl.Sha3.AArch64.Hybrid.round off))) s fun t =>
      Pairs t (rs.foldl Spec.Sha3.rnd A) (rs.foldl Spec.Sha3.rnd B) ∧
      (∀ i (hi : i < 25), t.gpr (laneReg i) = (rs.foldl Spec.Sha3.rnd C)[i]) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨s.sp, off + 16⟩] s.mem t.mem := by
  induction rs generalizing A B C s with
  | nil => exact wp_nil ⟨hp, hl, rfl, rfl, rfl, Frame.refl _ _⟩
  | cons r rs ih =>
    rw [List.flatMap_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons, WP.block_append_iff]
    refine (round_ok (hrs r (by simp)) hp hl ho).mono fun t ⟨hpt, hlt, hsp, hrd, hwr, hf⟩ => ?_
    have ho' : Scalar.SlotsOk off t := ⟨ho.align, ho.small, fun k hk => by
      rw [hwr, hsp]; exact ho.wr k hk⟩
    refine (ih (fun q hq => hrs q (by simp only [List.mem_cons]; exact Or.inr hq)) hpt hlt ho').mono
      fun u ⟨hpu, hlu, hsp', hrd', hwr', hf'⟩ => ⟨hpu, hlu, hsp'.trans hsp, hrd'.trans hrd,
        hwr'.trans hwr, hf.trans (by rw [← hsp]; exact hf')⟩

/-- The 24 rounds: Keccak-f[1600] on each of the three states. -/
theorem rounds_ok {off : Nat} {s : State} {A B C : Spec.Sha3.State} (hp : Pairs s A B)
    (hl : ∀ i (hi : i < 25), s.gpr (laneReg i) = C[i]) (ho : Scalar.SlotsOk off s) :
    WP isa (.block (Impl.Sha3.AArch64.Hybrid.rounds off)) s fun t =>
      Pairs t ((List.range 24).foldl Spec.Sha3.rnd A) ((List.range 24).foldl Spec.Sha3.rnd B) ∧
      (∀ i (hi : i < 25), t.gpr (laneReg i) = ((List.range 24).foldl Spec.Sha3.rnd C)[i]) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ Frame [⟨s.sp, off + 16⟩] s.mem t.mem :=
  rounds_list_ok (List.range 24) (fun _ h => List.mem_range.mp h) hp hl ho

end VG.Proof.Sha3.AArch64.Hybrid
