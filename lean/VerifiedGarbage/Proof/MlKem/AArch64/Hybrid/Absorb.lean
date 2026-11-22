module

public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Pad
public import VerifiedGarbage.Impl.MlKem.AArch64.Hybrid
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Proof.Sha3.X2Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Permute
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.RegSet
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Lit
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
meta import VerifiedGarbage.Proof.Sha3.X2Contract
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Permute
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.RegSet
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.BoundaryCommon
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Permute
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Lit
meta import VerifiedGarbage.TCB.Axioms
public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.MemLower
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.TCB.AArch64.Isa
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
meta import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRound
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.MemLower
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Block
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.ScheduleFacts
meta import VerifiedGarbage.Proof.Framework.Interleave
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.Framework.AArch64.Reduce
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Parity
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Sha3.AArch64.Hybrid.X3`, which this module and modules that import it used -/

section

/-! ### `Sha3.AArch64.Hybrid.Round`, which only this module used -/

section

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

end

end

/-!
# `vg_keccak_f1600_x3_sha3` on AArch64

Untrusted: everything here is checked by Lean. The function
(`Impl/Sha3/AArch64/Hybrid/X3.lean`) opens a frame of 128 bytes at
`S = sp - 128`, saves the callee-saved registers and the three pointers in
its slots (`slots_ok`, `SlotsAt`) and `q8`–`q15` in `scratch`
(`scr_save_ok`), loads the two interleaved states into `v0`–`v24` and the
third into the general registers, runs the 24 rounds (`rounds_ok`), and
then, from the pointers it reloads from the frame, stores the states
(`b2_ok`, `b3_ok`) and restores the registers (`b4_ok`); the frame's
slots keep what they hold through the rounds and the stores (`SlotsAt.frame`). `verified`: its
contract (`Proof/Sha3/X2Contract.lean`).

The taint analysis does not track the frame, so the constant-time proof
(`ct`) checks the code in pieces: the saves, loads and rounds from the three
public pointers, and each piece after a reload of a pointer from the frame
from that pointer, which the correctness proofs show is the same public value
in both runs. The code is checked only here, so it has no literal.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Hybrid.X3

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Proof.Sha3.AArch64.Sha3.Vector (exec_strq exec_ldrq read_write16 vreg_inj)
open VG.Proof.Sha3.AArch64.Neon (Pairs PairAt pairR wordAddr pair_contains)
open VG.Proof.Sha3.AArch64.Neon.X2 (scr_contains Saved pairAt_stateX2 stateX2_of_pairAt)
open VG.Proof.Sha3.AArch64.Scalar (exec_strSp)
open VG.Proof.Sha3.AArch64.Scalar.Boundary (laneReg_ne_x30 laneReg_inj store_words_ok)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint ct_of RelCT.block_split)
open VG.Spec.Sha3 (stateAt keccakF)
open VG.Proof.Sha3 (stateX2At)

abbrev X3code := VG.Impl.Sha3.AArch64.Hybrid.X3.vector

/-- The working space. -/
abbrev scrR (q : Addr) : Region := Neon.X2.scrR q

abbrev Lanes := Scalar.Boundary.Lanes

/-! ## The frame's slots -/

/-- The registers the frame's slots `[S + 16 + 8 j]` hold: the callee-saved
registers, then the three pointers. -/
def slotReg (j : Nat) : Reg :=
  [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30, .x0, .x1, .x2].getD j .x19

theorem savedReg_slot : ∀ i < 11, Impl.Sha3.AArch64.Hybrid.X3.savedReg i = slotReg i := by decide

theorem savedReg_inj : ∀ i < 11, ∀ j < 11,
    Impl.Sha3.AArch64.Hybrid.X3.savedReg i = Impl.Sha3.AArch64.Hybrid.X3.savedReg j ↔ i = j := by
  decide

theorem preserved_saved : ∀ r ∈ preserved, ∃ i < 11, r = Impl.Sha3.AArch64.Hybrid.X3.savedReg i := by
  decide

/-- The slots. -/
def slotR (S : Addr) : Region := ⟨S + BitVec.ofNat 64 16, 112⟩

/-- The slots of the frame at `S` hold the registers of `s₀`. -/
def SlotsAt (S : Addr) (s₀ : State) (m : Mem) : Prop :=
  ∀ j < 14, m.readW (S + BitVec.ofNat 64 (16 + 8 * j)) 64 = s₀.gpr (slotReg j)

theorem SlotsAt.frame {S : Addr} {s₀ : State} {m m' : Mem} {rs : List Region} (h : SlotsAt S s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (slotR S).Disjoint r) : SlotsAt S s₀ m' := by
  intro j hj
  rw [hf.readW (r := slotR S) (Offset.contains S (by omega_using []) (by omega_using [hj]) (by omega_using [])) hd (by decide)]
  exact h j hj

theorem Saved.frame {s₀ : State} {q : Addr} {m m' : Mem} {rs : List Region} (h : Saved s₀ q m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (scrR q).Disjoint r) : Saved s₀ q m' := by
  intro i hi
  rw [hf.read (scr_contains q hi) hd (by decide)]
  exact h i hi

theorem pairAt_frame {p : Addr} {A B : Spec.Sha3.State} {m m' : Mem} {rs : List Region}
    (h : PairAt m p A B) (hf : Frame rs m m') (hd : ∀ r ∈ rs, (pairR p).Disjoint r) :
    PairAt m' p A B := fun i hi => by
  rw [hf.read (pair_contains p hi) hd (by decide)]; exact h i hi

/-- The third state's region. -/
def stR (q : Addr) : Region := ⟨q, 200⟩

theorem stateAt_frame {q : Addr} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (stR q).Disjoint r) : stateAt m' q = stateAt m q := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (r := stR q) (Offset.contains_base q (by omega_using [hi]) (by omega_using [hi])) hd (by decide)

/-- `str x<slotReg j>, [sp, #16 + 8 j]` for each slot. -/
theorem slots_ok {u : State} (hw : ∀ j < 14, InRegions u.wr (u.sp + BitVec.ofNat 64 (16 + 8 * j)) 8) :
    WP isa (.block ((List.range 14).map fun j => Instr.strSp (slotReg j) (16 + 8 * j))) u fun u' =>
      u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      Frame [slotR u.sp] u.mem u'.mem ∧ SlotsAt u.sp u u'.mem := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k x => x.gpr = u.gpr ∧ x.v = u.v ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
      Frame [slotR u.sp] u.mem x.mem ∧
      ∀ j < k, x.mem.readW (u.sp + BitVec.ofNat 64 (16 + 8 * j)) 64 = u.gpr (slotReg j))
    (fun k x hk ⟨hg, hv, hr, hwr, hsp, hf, hvals⟩ => ?_) 14 (Nat.le_refl _) u
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  refine WP.cons (exec_strSp ⟨by omega_using [], by omega_using [hk]⟩ (by rw [hwr, hsp]; exact hw k hk))
    (WP.block_nil ⟨hg, hv, hr, hwr, hsp, ?_, fun j hj => ?_⟩)
  · change Frame _ _ (x.mem.writeW _ _)
    rw [hsp]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains u.sp (by omega_using []) (by omega_using [hk]) (by omega_using []))
  · change (x.mem.writeW _ _).readW _ 64 = _
    rw [hsp, hg]
    by_cases he : j = k
    · subst j; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [he]) (by omega_using [hk, hj]) (by omega_using [hk])) (by decide)]
      exact hvals j (by omega_using [hj, he])

/-- `q8`–`q15` saved at `x2`. -/
theorem scr_save_ok {u : State} {q : Addr} (hq : u.gpr .x2 = q)
    (hw : ∀ i < 8, InRegions u.wr (q + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 8).map fun i => Instr.strq (vreg (8 + i)) .x2 (16 * i))) u fun u' =>
      u'.gpr = u.gpr ∧ u'.v = u.v ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      Frame [scrR q] u.mem u'.mem ∧ Saved u q u'.mem := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k x => x.gpr = u.gpr ∧ x.v = u.v ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
      Frame [scrR q] u.mem x.mem ∧
      ∀ i < k, x.mem.read (q + BitVec.ofNat 64 (16*i)) 16 = u.v (vreg (8+i)))
    (fun k x hk ⟨hg, hv, hr, hwr, hsp, hf, hvals⟩ => ?_) 8 (Nat.le_refl _) u
    ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  refine WP.cons (exec_strq ⟨by omega_using [], by omega_using [hk]⟩ (by rw [hwr, hg, hq]; exact hw k hk))
    (WP.block_nil_iff.mpr ⟨hg, hv, hr, hwr, hsp, ?_, fun i hi => ?_⟩)
  · change Frame _ _ (x.mem.write _ 16 _)
    rw [hg, hq]
    exact hf.write (List.mem_singleton_self _) _ (scr_contains q hk)
  · change (x.mem.write _ 16 _).read _ 16 = _
    rw [hg, hq, hv]
    by_cases he : i = k
    · subst i
      exact read_write16 _ _ _
    · rw [Mem.read_write_sep (Offset.sep _ (by omega_using [he]) (by omega_using [hk, hi]) (by omega_using [hk])) (by decide)]
      exact hvals i (by omega_using [hi, he])

/-- The third state's lanes into the general registers, from `x1`. -/
theorem lanes_ok (u : State)
    (hin : ∀ i < 25, InRegions (u.rd ++ u.wr) (u.gpr .x1 + BitVec.ofNat 64 (8*i)) 8) :
    WP isa (.block (([.addImm .x .x30 .x1 0] : List Instr) ++
        (List.range 25).map fun i => .ldr .x (laneReg i) .x30 (8*i))) u fun u' =>
      u'.mem = u.mem ∧ u'.v = u.v ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      Lanes u' (stateAt u.mem (u.gpr .x1)) := by
  refine WP.cons (exec_addImm_x (by decide)) ?_
  have hb : (u.write .x .x30 (u.read .x .x1 + BitVec.ofNat _ 0)).gpr .x30 = u.gpr .x1 := by
    simp only [RegUpd.gpr_write_self, State.read, Size.bits, BitVec.setWidth_eq,
      show BitVec.ofNat 64 0 = 0 by rfl]
    exact BitVec.add_zero _
  rw [List.map_eq_flatMap]
  refine (wp_range_flatMap (M := isa)
    (fun k x => x.mem = u.mem ∧ x.v = u.v ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
      x.gpr .x30 = u.gpr .x1 ∧
      ∀ j < k, x.gpr (laneReg j) = u.mem.readW (u.gpr .x1 + BitVec.ofNat 64 (8*j)) 64)
    (fun k x hk ⟨hm, hv, hr, hwr, hsp, h30, hl⟩ => ?_) 25 (Nat.le_refl _) (u.write .x .x30 (u.read .x .x1 + BitVec.ofNat _ 0))
    ⟨rfl, rfl, rfl, rfl, rfl, hb, fun _ h => absurd h (by omega_using [])⟩).mono
    fun x ⟨hm, hv, hr, hwr, hsp, _, hl⟩ => ⟨hm, hv, hr, hwr, hsp, fun i hi => ?_⟩
  · refine WP.cons (exec_ldr_x ⟨by omega_using [], by omega_using [hk]⟩ (by rw [hr, hwr, h30]; exact hin k hk))
      (WP.block_nil ⟨hm, hv, hr, hwr, hsp, ?_, fun j hj => ?_⟩)
    · rw [RegUpd.gpr_write_of_ne _ _ _ (Ne.symm (laneReg_ne_x30 k hk)), h30]
    · by_cases he : j = k
      · subst j
        simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, hm, h30]
      · rw [RegUpd.gpr_write_of_ne _ _ _ (fun h => he ((laneReg_inj j (by omega_using [hk, hj]) k hk).mp h))]
        exact hl j (by omega_using [hj, he])
  · simpa only [stateAt, Vector.getElem_ofFn] using hl i hi

/-- `q8`–`q15` back from `x2`. -/
theorem scr_restore_ok {s₀ u : State} {q : Addr} (hq : u.gpr .x2 = q) (hs : Saved s₀ q u.mem)
    (hin : ∀ i < 8, InRegions (u.rd ++ u.wr) (q + BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 8).map fun i => Instr.ldrq (vreg (8 + i)) .x2 (16 * i))) u fun u' =>
      u'.gpr = u.gpr ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      ∀ r ∈ preservedV, (u'.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64 := by
  have hh : WP isa (.block ((List.range 8).map fun i => Instr.ldrq (vreg (8 + i)) .x2 (16 * i))) u
      fun u' => u'.gpr = u.gpr ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
        ∀ i < 8, u'.v (vreg (8+i)) = s₀.v (vreg (8+i)) := by
    rw [List.map_eq_flatMap]
    refine wp_range_flatMap (M := isa)
      (fun k x => x.gpr = u.gpr ∧ x.mem = u.mem ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
        ∀ i < k, x.v (vreg (8+i)) = s₀.v (vreg (8+i)))
      (fun k x hk ⟨hg, hm, hr, hwr, hsp, hvals⟩ => ?_) 8 (Nat.le_refl _) u
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega_using [])⟩
    refine WP.cons (exec_ldrq ⟨by omega_using [], by omega_using [hk]⟩ ?_) (WP.block_nil ?_)
    · rw [hr, hwr, hg, hq]; exact hin k hk
    refine ⟨by rw [RegUpd.gpr_setV, hg], by rw [RegUpd.mem_setV, hm], by rw [RegUpd.rd_setV, hr],
      by rw [RegUpd.wr_setV, hwr], by rw [RegUpd.sp_setV, hsp], fun i hi => ?_⟩
    rw [RegUpd.v_setV]
    simp only [vreg_inj (8+i) (by omega_using [hk, hi]) (8+k) (by omega_using [hk]), Nat.add_left_cancel_iff]
    by_cases he : i = k
    · subst i
      simp only [ite_true, hm, hg, hq]
      exact hs k hk
    · rw [ite_eq_right (by omega_using [he])]
      exact hvals i (by omega_using [hi, he])
  refine hh.mono fun u' ⟨hg, hm, hr, hwr, hsp, hv⟩ => ⟨hg, hm, hr, hwr, hsp, fun r hr' => ?_⟩
  have hv' : ∀ r ∈ preservedV, ∃ i : Fin 8, r = vreg (8+i.val) := by decide
  obtain ⟨i, rfl⟩ := hv' r hr'
  exact congrArg (fun v : BitVec 128 => v.extractLsb' 0 64) (hv i.val i.isLt)

/-- The callee-saved registers back from the frame. -/
theorem regs_restore_ok {s₀ u : State}
    (hs : ∀ i < 11, u.mem.readW (u.sp + BitVec.ofNat 64 (16 + 8 * i)) 64 =
      s₀.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i))
    (hin : ∀ i < 11, InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (16 + 8 * i)) 8) :
    WP isa (.block ((List.range 11).map fun i =>
        Instr.ldrSp (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) (16 + 8 * i))) u fun u' =>
      u'.v = u.v ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧
      ∀ i < 11, u'.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) =
        s₀.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k x => x.v = u.v ∧ x.mem = u.mem ∧ x.rd = u.rd ∧ x.wr = u.wr ∧ x.sp = u.sp ∧
      ∀ i < k, x.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) =
        s₀.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i))
    (fun k x hk ⟨hv, hm, hr, hwr, hsp, hvals⟩ => ?_) 11 (Nat.le_refl _) u
    ⟨rfl, rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega_using [])⟩
  refine WP.cons (exec_ldrSp ⟨by omega_using [], by omega_using [hk]⟩ (by rw [hr, hwr, hsp]; exact hin k hk))
    (WP.block_nil ⟨hv, hm, hr, hwr, hsp, fun i hi => ?_⟩)
  by_cases he : i = k
  · subst i
    simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, hm, hsp]
    exact hs k hk
  · rw [RegUpd.gpr_write_of_ne _ _ _ (fun h => he ((savedReg_inj i (by omega_using [hk, hi]) k hk).mp h))]
    exact hvals i (by omega_using [hi, he])

/-! ## The layout -/

/-- The frame. -/
def frR (sp : Addr) : Region := ⟨sp - BitVec.ofNat 64 128, 128⟩

/-- The frame's base. -/
abbrev Sb (s : State) : Addr := s.sp - BitVec.ofNat 64 128

/-- What the contract gives. -/
structure Lay (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [pairR (s.gpr .x0), stR (s.gpr .x1), scrR (s.gpr .x2)]
  d01 : (pairR (s.gpr .x0)).Disjoint (stR (s.gpr .x1))
  d02 : (pairR (s.gpr .x0)).Disjoint (scrR (s.gpr .x2))
  d12 : (stR (s.gpr .x1)).Disjoint (scrR (s.gpr .x2))
  sp : 128 ≤ s.sp.toNat
  f0 : (frR s.sp).Disjoint (pairR (s.gpr .x0))
  f1 : (frR s.sp).Disjoint (stR (s.gpr .x1))
  f2 : (frR s.sp).Disjoint (scrR (s.gpr .x2))

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem inP {i : Nat} (hi : i < 25) : InRegions s.wr (wordAddr (s.gpr .x0) i) 16 :=
  ⟨_, by rw [h.wr]; simp, pair_contains _ hi⟩

theorem inQ {i : Nat} (hi : i < 25) : InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (8 * i)) 8 :=
  ⟨stR (s.gpr .x1), by rw [h.wr]; simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem inR {i : Nat} (hi : i < 8) : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (16 * i)) 16 :=
  ⟨scrR (s.gpr .x2), by rw [h.wr]; simp, scr_contains _ hi⟩

theorem sP : (slotR (Sb s)).Disjoint (pairR (s.gpr .x0)) := h.f0.sub_left (Offset.sub_base _ (by decide))
theorem sQ : (slotR (Sb s)).Disjoint (stR (s.gpr .x1)) := h.f1.sub_left (Offset.sub_base _ (by decide))
theorem sR : (slotR (Sb s)).Disjoint (scrR (s.gpr .x2)) := h.f2.sub_left (Offset.sub_base _ (by decide))

end Lay

theorem inF {s : State} {d n : Nat} (hd : d + n ≤ 128) :
    InRegions (frR s.sp :: s.wr) (Sb s + BitVec.ofNat 64 d) n :=
  ⟨frR s.sp, List.mem_cons_self .., Offset.contains_base _ hd (by omega_using [hd])⟩

theorem inW {s u : State} (hw : u.wr = frR s.sp :: s.wr) {a : Addr} {n : Nat} (h : InRegions s.wr a n) :
    InRegions u.wr a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, by rw [hw]; exact List.mem_cons_of_mem _ hr, hc⟩

theorem inW0 {r : Region} {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    InRegions (r :: rs) a n := by
  obtain ⟨r', hr, hc⟩ := h
  exact ⟨r', List.mem_cons_of_mem _ hr, hc⟩

theorem inRW {rd rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) : InRegions (rd ++ rs) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem slot_val {S : Addr} {s₀ : State} {m : Mem} (h : SlotsAt S s₀ m) (j : Nat) (hj : j < 14) {off : Nat}
    (ho : 16 + 8 * j = off) : m.readW (S + BitVec.ofNat 64 off) 64 = s₀.gpr (slotReg j) :=
  ho ▸ h j hj

/-! ## The phases -/

/-- After the saves, the loads and the rounds. -/
structure Mid (s u : State) : Prop where
  sp : u.sp = Sb s
  rd : u.rd = s.rd
  wr : u.wr = frR s.sp :: s.wr
  pairs : Pairs u (keccakF (stateX2At s.mem (s.gpr .x0) 0)) (keccakF (stateX2At s.mem (s.gpr .x0) 1))
  lanes : Lanes u (keccakF (stateAt s.mem (s.gpr .x1)))
  slots : SlotsAt (Sb s) s u.mem
  saved : Saved s (s.gpr .x2) u.mem

theorem save_eq : Impl.Sha3.AArch64.Hybrid.X3.save =
    (List.range 14).map (fun j => Instr.strSp (slotReg j) (16 + 8 * j)) ++
      (List.range 8).map (fun i => Instr.strq (vreg (8 + i)) .x2 (16 * i)) := by
  rfl

theorem front_ok {s : State} (h : Lay s) :
    WP isa (.block (Impl.Sha3.AArch64.Hybrid.X3.save ++ Impl.Sha3.AArch64.Hybrid.X3.load ++
      Impl.Sha3.AArch64.Hybrid.rounds 0)) (allocated 128 s) (Mid s) := by
  rw [show Impl.Sha3.AArch64.Hybrid.X3.save ++ Impl.Sha3.AArch64.Hybrid.X3.load ++
      Impl.Sha3.AArch64.Hybrid.rounds 0 =
      (List.range 14).map (fun j => Instr.strSp (slotReg j) (16 + 8 * j)) ++
      ((List.range 8).map (fun i => Instr.strq (vreg (8 + i)) .x2 (16 * i)) ++
      (Impl.Sha3.AArch64.Neon.Pair.load .x0 ++
      ((([.addImm .x .x30 .x1 0] : List Instr) ++
        (List.range 25).map fun i => .ldr .x (laneReg i) .x30 (8*i)) ++
      Impl.Sha3.AArch64.Hybrid.rounds 0))) from by
    rw [save_eq]; simp only [Impl.Sha3.AArch64.Hybrid.X3.load, List.append_assoc]]
  rw [WP.block_append_iff]
  refine (slots_ok (u := allocated 128 s) (fun j hj => inF (by omega_using [hj]))).mono
    fun u₁ ⟨g₁, v₁, r₁, w₁, sp₁, f₁, sl₁⟩ => ?_
  rw [WP.block_append_iff]
  refine (scr_save_ok (q := s.gpr .x2) (by rw [g₁]; rfl) (fun i hi => by rw [w₁]; exact inW0 (h.inR hi))).mono
    fun u₂ ⟨g₂, v₂, r₂, w₂, sp₂, f₂, sv₂⟩ => ?_
  have f₁' : Frame [slotR (Sb s)] s.mem u₁.mem := f₁
  have sl₂ : SlotsAt (Sb s) s u₂.mem := SlotsAt.frame sl₁ f₂ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sR
  have sv₂' : Saved s (s.gpr .x2) u₂.mem := fun i hi => (sv₂ i hi).trans (by rw [v₁]; rfl)
  have wr₂ : u₂.wr = frR s.sp :: s.wr := by rw [w₂, w₁]; rfl
  have hpair : PairAt u₂.mem (s.gpr .x0) (stateX2At s.mem (s.gpr .x0) 0) (stateX2At s.mem (s.gpr .x0) 1) :=
    pairAt_frame (pairAt_frame (pairAt_stateX2 s.mem _) f₁' fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.sP.symm) f₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d02
  rw [WP.block_append_iff]
  refine (Neon.load_ok (r := .x0) (by rw [g₂, g₁]; rfl) hpair
    (fun i hi => inRW (inW wr₂ (h.inP hi)))).mono fun u₃ ⟨c₃, ps₃⟩ => ?_
  rw [WP.block_append_iff]
  have hq₃ : u₃.gpr .x1 = s.gpr .x1 := by rw [c₃.gpr, g₂, g₁]; rfl
  refine (lanes_ok u₃ (fun i hi => by rw [hq₃, c₃.rd, c₃.wr]; exact inRW (inW wr₂ (h.inQ hi)))).mono
    fun u₄ ⟨m₄, v₄, r₄, w₄, sp₄, ln₄⟩ => ?_
  have hst : stateAt u₃.mem (u₃.gpr .x1) = stateAt s.mem (s.gpr .x1) := by
    rw [hq₃, c₃.mem, stateAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d12),
      stateAt_frame f₁' (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.sQ.symm)]
  rw [hst] at ln₄
  have sp₄' : u₄.sp = Sb s := by rw [sp₄, c₃.sp, sp₂, sp₁]; rfl
  have wr₄ : u₄.wr = frR s.sp :: s.wr := by rw [w₄, c₃.wr, wr₂]
  have ps₄ : Pairs u₄ (stateX2At s.mem (s.gpr .x0) 0) (stateX2At s.mem (s.gpr .x0) 1) :=
    fun i hi => by rw [v₄]; exact ps₃ i hi
  refine (rounds_ok (off := 0) ps₄ ln₄ ⟨by decide, by decide, fun k hk => by
    rw [wr₄, sp₄']; exact inF (by omega_using [hk])⟩).mono fun t ⟨pt, lt, spt, rdt, wrt, ft⟩ => ?_
  rw [sp₄'] at ft
  have m₄' : u₄.mem = u₂.mem := by rw [m₄, c₃.mem]
  exact ⟨by rw [spt, sp₄'], by rw [rdt, r₄, c₃.rd, r₂, r₁]; rfl, by rw [wrt, wr₄], pt, lt,
    SlotsAt.frame (m₄' ▸ sl₂) ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base _ (by decide) (by decide),
    Saved.frame (m₄' ▸ sv₂') ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h.f2.symm.sub_right (Region.sub_prefix (by decide))⟩
/-- The state's pointer back in `x30`. -/
theorem b1_ok {s u : State} (m : Mid s u) :
    WP isa (.block [.ldrSp .x30 112]) u fun u' => Mid s u' ∧ u'.gpr .x30 = s.gpr .x1 := by
  refine WP.cons (exec_ldrSp ⟨by decide, by decide⟩ (by rw [m.sp, m.wr]; exact inRW (inF (d := _) (n := 8) (by decide))))
    (WP.block_nil ⟨⟨m.sp, m.rd, m.wr, m.pairs, fun i hi => ?_, m.slots, m.saved⟩, ?_⟩)
  · rw [RegUpd.gpr_write_of_ne _ _ _ (laneReg_ne_x30 i hi)]; exact m.lanes i hi
  · simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, m.sp]
    exact slot_val m.slots 12 (by decide) rfl

/-- After the store of the third state. -/
structure Mid2 (s u : State) : Prop where
  sp : u.sp = Sb s
  rd : u.rd = s.rd
  wr : u.wr = frR s.sp :: s.wr
  pairs : Pairs u (keccakF (stateX2At s.mem (s.gpr .x0) 0)) (keccakF (stateX2At s.mem (s.gpr .x0) 1))
  slots : SlotsAt (Sb s) s u.mem
  saved : Saved s (s.gpr .x2) u.mem
  st : stateAt u.mem (s.gpr .x1) = keccakF (stateAt s.mem (s.gpr .x1))

/-- The third state stored, and the states' pointer back in `x0`. -/
theorem b2_ok {s u : State} (h : Lay s) (m : Mid s u) (h30 : u.gpr .x30 = s.gpr .x1) :
    WP isa (.block ((List.range 25).map (fun i => Instr.str .x (laneReg i) .x30 (8 * i)) ++
      ([.ldrSp .x0 104] : List Instr))) u fun u' => Mid2 s u' ∧ u'.gpr .x0 = s.gpr .x0 := by
  rw [WP.block_append_iff]
  refine (store_words_ok u _ m.lanes (fun i hi => by rw [h30, m.wr]; exact inW0 (h.inQ hi))).mono
    fun x hx => ?_
  have fx : Frame [stR (s.gpr .x1)] u.mem x.mem := by rw [← h30]; exact hx.frame
  have sl : SlotsAt (Sb s) s x.mem := SlotsAt.frame m.slots fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sQ
  have sv : Saved s (s.gpr .x2) x.mem := Saved.frame m.saved fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.d12.symm
  have spx : x.sp = Sb s := by rw [hx.keep.sp, m.sp]
  have wrx : x.wr = frR s.sp :: s.wr := by rw [hx.keep.wr, m.wr]
  refine WP.cons (exec_ldrSp ⟨by decide, by decide⟩ (by rw [spx, wrx]; exact inRW (inF (d := _) (n := 8) (by decide))))
    (WP.block_nil ⟨⟨spx, by rw [RegUpd.rd_write, hx.keep.rd, m.rd], wrx,
      fun i hi => by rw [RegUpd.v_write, hx.vec]; exact m.pairs i hi, sl, sv, ?_⟩, ?_⟩)
  · apply Vector.ext
    intro i hi
    simpa only [stateAt, Vector.getElem_ofFn, h30, RegUpd.mem_write] using hx.vals i hi hi
  · simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, spx]
    exact slot_val sl 11 (by decide) rfl

/-- After the store of the interleaved states. -/
structure Mid3 (s u : State) : Prop where
  sp : u.sp = Sb s
  rd : u.rd = s.rd
  wr : u.wr = frR s.sp :: s.wr
  slots : SlotsAt (Sb s) s u.mem
  saved : Saved s (s.gpr .x2) u.mem
  st : stateAt u.mem (s.gpr .x1) = keccakF (stateAt s.mem (s.gpr .x1))
  pa : PairAt u.mem (s.gpr .x0) (keccakF (stateX2At s.mem (s.gpr .x0) 0))
    (keccakF (stateX2At s.mem (s.gpr .x0) 1))

/-- The interleaved states stored, and the working space's pointer back in `x2`. -/
theorem b3_ok {s u : State} (h : Lay s) (m : Mid2 s u) (h0 : u.gpr .x0 = s.gpr .x0) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.store .x0 ++ ([.ldrSp .x2 120] : List Instr))) u
      fun u' => Mid3 s u' ∧ u'.gpr .x2 = s.gpr .x2 := by
  rw [WP.block_append_iff]
  refine (Neon.store_ok h0 m.pairs (fun i hi => by rw [m.wr]; exact inW0 (h.inP hi))).mono
    fun x ⟨vx, pax, fx⟩ => ?_
  have sl : SlotsAt (Sb s) s x.mem := SlotsAt.frame m.slots fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sP
  have sv : Saved s (s.gpr .x2) x.mem := Saved.frame m.saved fx fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.d02.symm
  have spx : x.sp = Sb s := by rw [vx.sp, m.sp]
  have wrx : x.wr = frR s.sp :: s.wr := by rw [vx.wr, m.wr]
  refine WP.cons (exec_ldrSp ⟨by decide, by decide⟩ (by rw [spx, wrx]; exact inRW (inF (d := _) (n := 8) (by decide))))
    (WP.block_nil ⟨⟨spx, by rw [RegUpd.rd_write, vx.rd, m.rd], wrx, sl, sv, ?_, pax⟩, ?_⟩)
  · rw [RegUpd.mem_write, stateAt_frame fx (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.d01.symm)]
    exact m.st
  · simp only [RegUpd.gpr_write_self, Size.bits, BitVec.setWidth_eq, spx]
    exact slot_val sl 13 (by decide) rfl

/-- `q8`–`q15` and the callee-saved registers restored. -/
theorem b4_ok {s u : State} (h : Lay s) (m : Mid3 s u) (h2 : u.gpr .x2 = s.gpr .x2) :
    WP isa (.block ((List.range 8).map (fun i => Instr.ldrq (vreg (8 + i)) .x2 (16 * i)) ++
      (List.range 11).map (fun i =>
        Instr.ldrSp (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) (16 + 8 * i)))) u fun t =>
      t.sp = Sb s ∧ t.mem = u.mem ∧
      (∀ i < 11, t.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) =
        s.gpr (Impl.Sha3.AArch64.Hybrid.X3.savedReg i)) ∧
      ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  rw [WP.block_append_iff]
  refine (scr_restore_ok h2 m.saved (fun i hi => by rw [m.wr]; exact inRW (inW0 (h.inR hi)))).mono
    fun x ⟨_, mx, rx, wx, spx, vx⟩ => ?_
  refine (regs_restore_ok (s₀ := s) (fun i hi => ?_) (fun i hi => ?_)).mono
    fun t ⟨vt, mt, _, _, spt, gt⟩ => ⟨by rw [spt, spx, m.sp], by rw [mt, mx], gt,
      fun r hr => by rw [vt]; exact vx r hr⟩
  · rw [mx, spx, m.sp, savedReg_slot i hi]; exact m.slots i (by omega_using [hi])
  · rw [rx, wx, spx, m.wr, m.sp]; exact inRW (inF (by omega_using [hi]))

theorem body_eq : Impl.Sha3.AArch64.Hybrid.X3.body =
    (Impl.Sha3.AArch64.Hybrid.X3.save ++ Impl.Sha3.AArch64.Hybrid.X3.load ++
      Impl.Sha3.AArch64.Hybrid.rounds 0) ++
    (([.ldrSp .x30 112] : List Instr) ++
    (((List.range 25).map (fun i => Instr.str .x (laneReg i) .x30 (8 * i)) ++
      ([.ldrSp .x0 104] : List Instr)) ++
    ((Impl.Sha3.AArch64.Neon.Pair.store .x0 ++ ([.ldrSp .x2 120] : List Instr)) ++
    ((List.range 8).map (fun i => Instr.ldrq (vreg (8 + i)) .x2 (16 * i)) ++
      (List.range 11).map (fun i =>
        Instr.ldrSp (Impl.Sha3.AArch64.Hybrid.X3.savedReg i) (16 + 8 * i)))))) := by
  simp only [Impl.Sha3.AArch64.Hybrid.X3.body, Impl.Sha3.AArch64.Hybrid.X3.store,
    Impl.Sha3.AArch64.Hybrid.X3.restore, List.append_assoc]

/-! ## The contract -/

/-- The contract on the states at `x0` and `x1`, the working space at `x2` and
the 128 bytes of stack below `sp`. -/
def K : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [pairR (s.gpr .x0), stR (s.gpr .x1), scrR (s.gpr .x2)] ∧
    (pairR (s.gpr .x0)).Disjoint (stR (s.gpr .x1)) ∧ (pairR (s.gpr .x0)).Disjoint (scrR (s.gpr .x2)) ∧
    (stR (s.gpr .x1)).Disjoint (scrR (s.gpr .x2)) ∧ 128 ≤ s.sp.toNat ∧
    (frR s.sp).Disjoint (pairR (s.gpr .x0)) ∧ (frR s.sp).Disjoint (stR (s.gpr .x1)) ∧
    (frR s.sp).Disjoint (scrR (s.gpr .x2))
  post s s' := stateX2At s'.mem (s.gpr .x0) 0 = keccakF (stateX2At s.mem (s.gpr .x0) 0) ∧
    stateX2At s'.mem (s.gpr .x0) 1 = keccakF (stateX2At s.mem (s.gpr .x0) 1) ∧
    stateAt s'.mem (s.gpr .x1) = keccakF (stateAt s.mem (s.gpr .x1))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

theorem lay {s : State} (h : K.pre s) : Lay s :=
  let ⟨a, b, c, d, e, f, g, i, j⟩ := h
  ⟨a, b, c, d, e, f, g, i, j⟩

/-- The body, in the frame. -/
theorem body_ok {s : State} (h : Lay s) :
    WP isa (.block Impl.Sha3.AArch64.Hybrid.X3.body) (allocated 128 s) fun t =>
      ∀ m u, Frame [⟨s.sp - BitVec.ofNat 64 128, 128⟩] t.mem m →
        abiPreserved s { freed 128 t with mem := m, unknowns := u } ∧
          K.post s { freed 128 t with mem := m, unknowns := u } := by
  rw [body_eq, WP.block_append_iff]
  refine (front_ok h).mono fun u m => ?_
  rw [WP.block_append_iff]
  refine (b1_ok m).mono fun u₁ ⟨m₁, h30⟩ => ?_
  rw [WP.block_append_iff]
  refine (b2_ok h m₁ h30).mono fun u₂ ⟨m₂, h0⟩ => ?_
  rw [WP.block_append_iff]
  refine (b3_ok h m₂ h0).mono fun u₃ ⟨m₃, h2⟩ => ?_
  refine (b4_ok h m₃ h2).mono fun t ⟨spt, mt, gt, vt⟩ mm u f => ⟨⟨fun r hr => ?_, ?_, vt⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := preserved_saved r hr
    exact gt i hi
  · show t.sp + BitVec.ofNat 64 128 = s.sp
    rw [spt]
    exact BitVec.sub_add_cancel _ _
  · obtain ⟨e0, e1⟩ := stateX2_of_pairAt m₃.pa
    -- The states lie apart from the frame, whose bytes the `free` loses.
    have hf : Frame [frR s.sp] t.mem mm := f
    have hd {R : Region} (hR : (frR s.sp).Disjoint R) : ∀ r ∈ [frR s.sp], R.Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hR.symm
    show stateX2At mm _ 0 = _ ∧ stateX2At mm _ 1 = _ ∧ stateAt mm _ = _
    rw [Neon.X2.stateX2At_frame hf (hd h.f0) (by decide), Neon.X2.stateX2At_frame hf (hd h.f0) (by decide),
      stateAt_frame hf (hd h.f1), mt]
    exact ⟨e0, e1, m₃.st⟩

theorem vector_correct (s : State) (hs : K.pre s) :
    ∃ tr t, Exec isa X3code s tr t ∧ abiPreserved s t ∧ K.post s t :=
  WP.alloc ⟨by decide, by decide, by decide⟩ (lay hs).sp (body_ok (lay hs))

theorem allocated_gpr (n : Nat) (s : State) : (allocated n s).gpr = s.gpr := rfl

theorem vector_ct : ConstantTime isa K.pre K.pub X3code := by
  refine ct_of fun σ₁ σ₂ p₁ p₂ ⟨q0, q1, q2, qsp⟩ => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  have hS : Sb σ₁ = Sb σ₂ := by simp only [Sb, qsp]
  refine (RelCT.alloc (P := Eq2 σ₁ σ₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocated 128 σ₁) (allocated 128 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  rw [body_eq]
  -- The saves, the loads and the rounds, from the three pointers.
  refine RelCT.block_split (rel_seq
    (rel_taint (c := (Code.block (Impl.Sha3.AArch64.Hybrid.X3.save ++
      Impl.Sha3.AArch64.Hybrid.X3.load ++ Impl.Sha3.AArch64.Hybrid.rounds 0) : Prog isa))
      (σ₁ := allocated 128 σ₁) (σ₂ := allocated 128 σ₂) [.x0, .x1, .x2]
      (by show σ₁.sp - _ = σ₂.sp - _; rw [qsp])
      (by agree_tac [allocated_gpr, q0, q1, q2]) ⟨_, by taint_decide⟩)
    (front_ok h₁) (front_ok h₂) fun u₁ u₂ m₁ m₂ => ?_)
  -- The state's pointer, from the frame.
  refine RelCT.block_split (rel_seq (rel_taint [] (by rw [m₁.sp, m₂.sp, hS]) (by agree_tac [])
    ⟨_, by taint_decide⟩) (b1_ok m₁) (b1_ok m₂) fun x₁ x₂ ⟨n₁, a₁⟩ ⟨n₂, a₂⟩ => ?_)
  -- The third state's store, from it.
  refine RelCT.block_split (rel_seq (rel_taint [.x30] (by rw [n₁.sp, n₂.sp, hS])
    (by agree_tac [a₁, a₂, q1]) ⟨_, by taint_decide⟩) (b2_ok h₁ n₁ a₁) (b2_ok h₂ n₂ a₂)
    fun y₁ y₂ ⟨k₁, c₁⟩ ⟨k₂, c₂⟩ => ?_)
  -- The interleaved states' store.
  refine RelCT.block_split (rel_seq (rel_taint [.x0] (by rw [k₁.sp, k₂.sp, hS])
    (by agree_tac [c₁, c₂, q0]) ⟨_, by taint_decide⟩) (b3_ok h₁ k₁ c₁) (b3_ok h₂ k₂ c₂)
    fun z₁ z₂ ⟨l₁, d₁⟩ ⟨l₂, d₂⟩ => ?_)
  -- The restores.
  exact rel_taint [.x2] (by rw [l₁.sp, l₂.sp, hS]) (by agree_tac [d₁, d₂, q2]) ⟨_, by taint_decide⟩

/-! ## Without a CPU feature: the scalar rounds on each state in turn -/

section Scalar
open VG.Impl.Sha3.AArch64.Hybrid.X3 (loadThird storeThird scalar code)
open VG.Impl.Sha3.AArch64.Scalar (laneReg)
open VG.Impl.Sha3.AArch64.Neon.X2 (loadLanes storeLanes)
open VG.Proof.Sha3.AArch64.Neon.X2 (scalarFirst_ok scalarNext_ok storeLanes_ok stateX2At_frame)

/-- The lanes of the state at `q` (the pointer kept in `v31`), to their registers. -/
theorem loadThird_ok (s₀ : State) {q : Addr} (hptr : vdword (s₀.v .v31) 0 = q)
    (hin : ∀ i < 25, InRegions (s₀.rd ++ s₀.wr) (q + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block loadThird) s₀ fun s' => Scalar.Boundary.Keep s₀ s' ∧ s'.mem = s₀.mem ∧
      s'.v = s₀.v ∧ Lanes s' (stateAt s₀.mem q) := by
  change (s₀.v .v31).extractLsb' (64*0) 64 = q at hptr
  unfold loadThird
  rw [List.singleton_append]
  refine WP.cons rfl ?_
  rw [List.map_eq_flatMap]
  refine (wp_range_flatMap (M := isa)
    (fun j s => Scalar.Boundary.Keep s₀ s ∧ s.mem = s₀.mem ∧ s.v = s₀.v ∧ s.gpr .x30 = q ∧
      ∀ i < j, s.gpr (laneReg i) = s₀.mem.readW (q + BitVec.ofNat 64 (8 * i)) 64)
    (fun i s hi ⟨hkeep,hm,hv,hx,hl⟩ => ?_) 25 (Nat.le_refl _)
    (s₀.write .x .x30 ((s₀.v .v31).extractLsb' (64*0) 64))
    ⟨⟨rfl,rfl,rfl⟩,rfl,rfl,
      by simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,vdword] using hptr,
      fun _ h => absurd h (by omega_using [])⟩).mono
    fun s ⟨hkeep,hm,hv,_,hl⟩ => ⟨hkeep,hm,hv,fun i hi => by
      simpa only [stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.laneAddr] using hl i hi⟩
  refine WP.cons (exec_ldr_x ⟨by omega_using [],by omega_using [hi]⟩ ?_) (WP.block_nil ?_)
  · rw [hkeep.rd,hkeep.wr,hx]
    exact hin i hi
  · refine ⟨⟨hkeep.rd,hkeep.wr,hkeep.sp⟩,hm,hv,?_,fun j hj => ?_⟩
    · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
        Ne.symm (laneReg_ne_x30 i hi),ite_false,hx]
    · simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,
        laneReg_inj j (by omega_using [hi, hj]) i hi]
      split
      · rename_i he; subst j
        rw [hm,hx]
      · exact hl j (by omega_arith)

/-- The lanes, from their registers to the state at `q` (the pointer kept in `v31`). -/
theorem storeThird_ok (s₀ : State) {q : Addr} (A : Spec.Sha3.State) (hA : Lanes s₀ A)
    (hptr : vdword (s₀.v .v31) 0 = q)
    (hin : ∀ i < 25, InRegions s₀.wr (q + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block storeThird) s₀ fun s' => Scalar.Boundary.Keep s₀ s' ∧ s'.v = s₀.v ∧
      Frame [stR q] s₀.mem s'.mem ∧ stateAt s'.mem q = A := by
  change (s₀.v .v31).extractLsb' (64*0) 64 = q at hptr
  unfold storeThird
  refine WP.cons rfl ?_
  refine (store_words_ok _ A ?_ ?_).mono fun s hs => ?_
  · intro i hi
    simpa only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,laneReg_ne_x30 i hi,ite_false]
      using hA i hi
  · intro i hi
    simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,RegUpd.wr_write,hptr] using hin i hi
  · have hb : (s₀.write .x .x30 ((s₀.v .v31).extractLsb' (64*0) 64)).gpr .x30 = q := by
      simpa only [RegUpd.gpr_write_self,Size.bits,BitVec.setWidth_eq,vdword] using hptr
    refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.vec,?_,?_⟩
    · simpa only [hb,RegUpd.mem_write,stR] using hs.frame
    · apply Vector.ext
      intro i hi
      simpa only [stateAt,Vector.getElem_ofFn,VG.Proof.Sha3.laneAddr,hb] using hs.vals i hi hi

/-- `vg_keccak_f1600_x3`, from the states at `p` (`x0`) and `st` (`x1`): it writes only them. -/
theorem scalar_ok {s : State} {p st : Addr} (hp : s.gpr .x0 = p) (hst : s.gpr .x1 = st)
    (hd : (pairR p).Disjoint (stR st))
    (hwp : ∀ i < 25, ∀ k < 2, InRegions s.wr (p + BitVec.ofNat 64 (16 * i + 8 * k)) 8)
    (hws : ∀ i < 25, InRegions s.wr (st + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa scalar s fun t => abiPreserved s t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [pairR p, stR st] s.mem t.mem ∧
      stateX2At t.mem p 0 = keccakF (stateX2At s.mem p 0) ∧
      stateX2At t.mem p 1 = keccakF (stateX2At s.mem p 1) ∧
      stateAt t.mem st = keccakF (stateAt s.mem st) := by
  have hall : ∀ {a : Addr} {n : Nat}, InRegions s.wr a n → InRegions (s.rd ++ s.wr) a n :=
    fun ⟨r,hr,hc⟩ => ⟨r,List.mem_append.mpr (.inr hr),hc⟩
  have dps : ∀ r ∈ [pairR p], (stR st).Disjoint r := by simpa using hd.symm
  have dsp : ∀ r ∈ [stR st], (pairR p).Disjoint r := by simpa using hd
  unfold scalar
  rw [WP.seq_iff]
  refine (scalarFirst_ok hp fun i hi => hall (hwp i hi 0 (by decide))).mono fun s₂ ⟨c₂,m₂⟩ => ?_
  refine WP.seq (WP.mono (Scalar.Lazy.core_state_keep s _ s₂ c₂) fun s₃ ⟨c₃,r₃⟩ => ?_)
  have m₃ : s₃.mem = s.mem := r₃.mem.trans m₂
  rw [WP.seq_iff]
  refine (scalarNext_ok hp c₃ (fun i hi => hwp i hi 0 (by decide))
    fun i hi => hall (hwp i hi 1 (by decide))).mono fun s₅ ⟨c₅,f₅,a₅⟩ => ?_
  rw [m₃] at c₅ f₅
  refine WP.seq (WP.mono (Scalar.Lazy.core_state_keep s _ s₅ c₅) fun s₆ ⟨c₆,r₆⟩ => ?_)
  rw [WP.seq_iff,WP.block_append_iff]
  refine (storeLanes_ok (k := 1) (by decide) s₆ (p := p) _ c₆.lanes (c₆.ptrs.1.trans hp)
    (fun i hi => by rw [c₆.keep.wr]; exact hwp i hi 1 (by decide))).mono
    fun s₇ ⟨k₇,v₇,_,f₇,a₇,b₇⟩ => ?_
  have b₇' : stateX2At s₇.mem p 0 = keccakF (stateX2At s.mem p 0) := by rw [← a₅,← r₆.mem]; exact b₇
  have fp : Frame [pairR p] s.mem s₇.mem := f₅.trans (by rw [← r₆.mem]; exact f₇)
  have e₇ : stateAt s₇.mem st = stateAt s.mem st := stateAt_frame fp dps
  refine (loadThird_ok s₇ (q := st) (by rw [v₇]; exact c₆.ptrs.2.trans hst) (fun i hi => by
    rw [k₇.rd,k₇.wr,c₆.keep.rd,c₆.keep.wr]; exact hall (hws i hi))).mono
    fun s₈ ⟨k₈,m₈,v₈,l₈⟩ => ?_
  have c₈ : Scalar.Boundary.CoreState s (stateAt s.mem st) s₈ :=
    ⟨⟨k₈.rd.trans (k₇.rd.trans c₆.keep.rd),k₈.wr.trans (k₇.wr.trans c₆.keep.wr),
        k₈.sp.trans (k₇.sp.trans c₆.keep.sp)⟩,
      by simpa only [Scalar.Boundary.Ptrs,v₈,v₇] using c₆.ptrs,
      fun i hi => by rw [v₈,v₇]; exact c₆.saved i hi,fun r hr => by rw [v₈,v₇]; exact c₆.vec r hr,
      by rw [← e₇]; exact l₈⟩
  refine WP.seq (WP.mono (Scalar.Lazy.core_state_keep s _ s₈ c₈) fun s₉ ⟨c₉,r₉⟩ => ?_)
  have m₉ : s₉.mem = s₇.mem := r₉.mem.trans m₈
  rw [WP.block_append_iff]
  refine (storeThird_ok s₉ (q := st) _ c₉.lanes (c₉.ptrs.2.trans hst)
    (fun i hi => by rw [c₉.keep.wr]; exact hws i hi)).mono fun s₁₀ ⟨k₁₀,v₁₀,f₁₀,a₁₀⟩ => ?_
  rw [m₉] at f₁₀
  refine (Scalar.Boundary.restore_ok s s₁₀ (fun i hi => by rw [v₁₀]; exact c₉.saved i hi)).mono
    fun t ⟨k₁₁,m₁₁,v₁₁,g₁₁⟩ => ⟨⟨g₁₁,k₁₁.sp.trans (k₁₀.sp.trans c₉.keep.sp),fun r hr => by
      rw [v₁₁,v₁₀,c₉.vec r hr]⟩,k₁₁.rd.trans (k₁₀.rd.trans c₉.keep.rd),
      k₁₁.wr.trans (k₁₀.wr.trans c₉.keep.wr),?_,?_,?_,by rw [m₁₁]; exact a₁₀⟩
  · rw [m₁₁]
    exact (fp.mono fun r hr => by simp only [List.mem_singleton] at hr; subst r; simp).trans
      (f₁₀.mono fun r hr => by simp only [List.mem_singleton] at hr; subst r; simp)
  · rw [m₁₁,stateX2At_frame f₁₀ dsp (by decide)]
    exact b₇'
  · rw [m₁₁,stateX2At_frame f₁₀ dsp (by decide)]
    exact a₇

theorem code_true : code true = X3code := rfl
theorem code_false : code false = scalar := rfl

theorem correct (sha3 : Bool) (s : State) (hs : K.pre s) :
    ∃ tr t, Exec isa (code sha3) s tr t ∧ abiPreserved s t ∧ K.post s t := by
  cases sha3
  · rw [code_false]
    obtain ⟨_,hw,hd,_⟩ := hs
    obtain ⟨tr,t,he,habi,_,_,_,h0,h1,h2⟩ := scalar_ok (s := s) rfl rfl hd
      (fun i hi k hk => ⟨_,by rw [hw]; simp,Neon.X2.lane_contains _ hi hk⟩)
      (fun i hi => ⟨stR (s.gpr .x1),by rw [hw]; simp,
        Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    exact ⟨tr,t,he,habi,h0,h1,h2⟩
  · rw [code_true]
    exact vector_correct s hs

theorem ct (sha3 : Bool) : ConstantTime isa K.pre K.pub (code sha3) := by
  cases sha3
  · -- Unfolded as far as the rounds, whose code has a literal (`.block Scalar.Lazy.permutationCore`)
    -- that `taint_decide` finds only where the goal names it.
    refine VectorTaint.constantTime (AArch64.Taint.ofRegs [.x0,.x1,.x2]) ?_ (by
      unfold Impl.Sha3.AArch64.Hybrid.X3.code Impl.Sha3.AArch64.Hybrid.X3.scalar
      taint_decide)
    intro s₁ s₂ _ _ ⟨h0,h1,h2,hsp⟩
    refine ⟨hsp,fun r hr => ?_⟩
    simp only [AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · rw [code_true]
    exact vector_ct

end Scalar

end VG.Proof.Sha3.AArch64.Hybrid.X3

end

end

/-!
# A rate-136 sponge of a message, one block before each `x3` call

`hstate E b d`: the third state before block `b` of `pad(E)` (rate 136,
suffix `d`: SHA3-256's `0x06` for `H(ek)`, SHAKE256's `0x1f` for `J(z ‖ c)`)
is absorbed: the sponge of the first `b` blocks of `E`, and, once every block
is absorbed, `absorb 136 (pad 136 d E)`, the state the hash is squeezed
from. `absorbBlock_ok`: the code XORing block `b` of the message `S`
(`Hybrid.HSrc`) into the state, followed by the permutation (of the `x3`
call), takes `hstate E b d` to `hstate E (b + 1) d`.
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.Sha3 (stateAt bytesAt keccakF absorb pad)
open VG.Proof.Sha3 (Rep xorAt xorByte)
open VG.Proof.Sha3.AArch64.Hybrid.X3 (stR)

/-! ## The sponge -/

/-- The third state before block `b` of `pad(E)` (suffix `d`) is absorbed. -/
def hstate (E : List Byte) (b : Nat) (d : Byte := BitVec.ofNat 8 6) : Spec.Sha3.State :=
  if 136 * b ≤ E.length then Rep 136 (E.take (136 * b)) else absorb 136 (pad 136 d E)

/-- The suffix of the message `S`. -/
abbrev dB (S : Impl.MlKem.AArch64.Hybrid.HSrc) : Byte := BitVec.ofNat 8 S.sfx

theorem hstate_zero (E : List Byte) {d : Byte} : hstate E 0 d = Spec.Sha3.zero := by
  simp only [hstate, Nat.mul_zero, Nat.zero_le, ite_true, List.take_zero, Proof.Sha3.rep_nil]

theorem hstate_done {E : List Byte} {b : Nat} {d : Byte} (h : E.length < 136 * b) :
    hstate E b d = absorb 136 (pad 136 d E) := by
  simp only [hstate, ite_eq_right (show ¬136 * b ≤ E.length by omega_using [h])]

theorem xorAt_nil (A : Spec.Sha3.State) (j : Nat) : xorAt A j [] = A := rfl

theorem xorAt_append (A : Spec.Sha3.State) (j : Nat) (bs : List Byte) :
    ∀ cs, xorAt A j (bs ++ cs) = xorAt (xorAt A j bs) (j + bs.length) cs := by
  refine Proof.Sha3.snoc_induction ?_ ?_
  · rw [List.append_nil]; exact (xorAt_nil _ _).symm
  · intro cs c ih
    rw [← List.append_assoc, Proof.Sha3.xorAt_snoc, ih, Proof.Sha3.xorAt_snoc, List.length_append,
      Nat.add_assoc]

/-- A whole block. -/
theorem hstate_full {E : List Byte} {b : Nat} {d : Byte} (h : 136 * b + 136 ≤ E.length) :
    keccakF (xorAt (hstate E b d) 0 ((E.drop (136 * b)).take 136)) = hstate E (b + 1) d := by
  have hl : (E.take (136 * b)).length = 136 * b := List.length_take_of_le (by omega_using [h])
  have hbs : ((E.drop (136 * b)).take 136).length = 136 := by
    rw [List.length_take, List.length_drop]; omega_using [h]
  have ra := Proof.Sha3.rep_append (rate := 136) (by decide) (by decide) (E.take (136 * b))
    ((E.drop (136 * b)).take 136) (by omega_using [hbs]) (by rw [hl, hbs]; omega_using [])
  rw [hl, hbs, show 136 * b % 136 = 0 by omega_using [], ite_eq_left (by decide)] at ra
  have ht : E.take (136 * (b + 1)) = E.take (136 * b) ++ (E.drop (136 * b)).take 136 := by
    rw [show 136 * (b + 1) = 136 * b + 136 by omega_using [], List.take_add]
  simp only [hstate, ite_eq_left (show 136 * b ≤ E.length by omega_using [h]),
    ite_eq_left (show 136 * (b + 1) ≤ E.length by omega_using [h]), ht, ra]

/-- The last, partial block, and the padding. -/
theorem hstate_last {E : List Byte} {b : Nat} {d : Byte} (hlo : 136 * b < E.length)
    (hhi : E.length < 136 * b + 136) :
    keccakF (xorByte (xorByte (xorAt (hstate E b d) 0 (E.drop (136 * b))) (E.length - 136 * b)
      d) 135 128) = hstate E (b + 1) d := by
  have hl : (E.take (136 * b)).length = 136 * b := List.length_take_of_le (by omega_using [hlo])
  have hbs : (E.drop (136 * b)).length = E.length - 136 * b := List.length_drop
  have ra := Proof.Sha3.rep_append (rate := 136) (by decide) (by decide) (E.take (136 * b))
    (E.drop (136 * b)) (by omega_using [hlo, hbs]) (by rw [hl, hbs]; omega_using [hhi])
  rw [hl, hbs, show 136 * b % 136 = 0 by omega_using [], ite_eq_right (show ¬0 + (E.length - 136 * b) = 136 by omega_using [hhi]),
    List.take_append_drop] at ra
  rw [hstate_done (show E.length < 136 * (b + 1) by omega_using [hhi]),
    Proof.Sha3.absorb_pad (by decide) (by decide), show E.length % 136 = E.length - 136 * b by omega_using [hlo, hhi]]
  simp only [hstate, ite_eq_left (show 136 * b ≤ E.length by omega_using [hlo]), ← ra]

/-! ## The code -/

theorem inRW {rd rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) : InRegions (rd ++ rs) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem covers_in {X : List Region} {p : Addr} {len : Nat} (hc : Covers [⟨p, len⟩] X) {off n : Nat}
    (h : off + n ≤ len) (hl : len < 2 ^ 64) : InRegions X (p + BitVec.ofNat 64 off) n :=
  hc _ _ ⟨_, List.mem_singleton_self _, contains_off h hl⟩

/-- One word of the message XORed into the state. -/
theorem absorbWord_ok {s : State} {r : Reg} {eo off : Nat} (heo : eo % 8 = 0 ∧ eo < 4096 * 8)
    (hoff : off % 8 = 0 ∧ off < 4096 * 8)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 eo) 8)
    (hw : InRegions s.wr (s.gpr .x28 + BitVec.ofNat 64 off) 8) :
    WP isa (.block ([.ldr .x .x9 r eo, .ldr .x .x10 .x28 off, .logic .eor .x .x9 .x9 .x10,
      .str .x .x9 .x28 off] : List Instr)) s fun t =>
      Keep [.x9, .x10] s t ∧
        t.mem = s.mem.writeW (s.gpr .x28 + BitVec.ofNat 64 off)
          (s.mem.readW (s.gpr r + BitVec.ofNat 64 eo) 64 ^^^
            s.mem.readW (s.gpr .x28 + BitVec.ofNat 64 off) 64) := by
  refine wp_ldrx (a := s.gpr r + BitVec.ofNat 64 eo) heo rfl hr fun a ha ea => ?_
  refine wp_ldrx (a := s.gpr .x28 + BitVec.ofNat 64 off) hoff (by rw [ha.get .x28])
    (by rw [ha.rd, ha.wr]; exact inRW hw) fun b hb eb => ?_
  refine wp_eor fun c hc ec => ?_
  have hh := (ha.trans hb).trans hc
  refine wp_strx hoff (by rw [hh.get .x28]) (by rw [hh.wr]; exact hw) fun t ht => wp_nil ?_
  refine ⟨(hh.keep.trans ht.keep).mono (by simp), ?_⟩
  rw [ht.mem, ec, hb.get .x9, ea, eb, hc.mem, hb.mem, ha.mem]

/-- The `n` words at `e + eo` (`e` in `r`) XORed into the state at `st`. -/
theorem absorbWords_ok {s : State} {r : Reg} {e st : Addr} {eo n : Nat} (hr9 : r ∉ [.x9, .x10])
    (he : s.gpr r = e)
    (hs : s.gpr .x28 = st) (hn : n ≤ 25) (heo : eo % 8 = 0) (hlim : eo + 8 * n ≤ 32768)
    (hr : ∀ w < n, InRegions (s.rd ++ s.wr) (e + BitVec.ofNat 64 (eo + 8 * w)) 8)
    (hw : Covers [stR st] s.wr) (hd : (stR st).Disjoint ⟨e + BitVec.ofNat 64 eo, 8 * n⟩) :
    WP isa (.block (Impl.MlKem.AArch64.Hybrid.absorbWords r eo n)) s fun t =>
      Keep [.x9, .x10] s t ∧ Frame [stR st] s.mem t.mem ∧
      stateAt t.mem st = xorAt (stateAt s.mem st) 0 (bytesAt s.mem (e + BitVec.ofNat 64 eo) (8 * n)) := by
  unfold Impl.MlKem.AArch64.Hybrid.absorbWords
  refine wp_range_flatMap (M := isa) (N := n)
    (fun w t => Keep [.x9, .x10] s t ∧ Frame [stR st] s.mem t.mem ∧
      stateAt t.mem st = xorAt (stateAt s.mem st) 0 (bytesAt s.mem (e + BitVec.ofNat 64 eo) (8 * w)))
    (fun w t hw' ⟨kt, ft, st'⟩ => ?_) n (Nat.le_refl _) s
    ⟨Keep.refl _ _, Frame.refl _ _, by simp only [Nat.mul_zero]; rfl⟩
  have t25 : t.gpr r = e := (kt.gpr r hr9).trans he
  have t28 : t.gpr .x28 = st := (kt.get .x28).trans hs
  have cst : (stR st).Contains (st + BitVec.ofNat 64 (8 * w)) 8 :=
    Offset.contains_base st (by omega_using [hn, hw']) (by omega_using [hn, hw'])
  refine WP.mono (absorbWord_ok (eo := eo + 8 * w) (off := 8 * w) ⟨by omega_using [heo], by omega_using [hlim, hw']⟩ ⟨by omega_using [], by omega_using [hn, hw']⟩
    (by rw [kt.rd, kt.wr, t25]; exact hr w hw')
    (by rw [kt.wr, t28]; exact hw _ _ ⟨stR st, List.mem_singleton_self _, cst⟩)) fun u ⟨ku, mu⟩ => ?_
  rw [t25, t28] at mu
  have sub : Region.Sub ⟨e + BitVec.ofNat 64 eo + BitVec.ofNat 64 (8 * w), 8⟩ ⟨e + BitVec.ofNat 64 eo, 8 * n⟩ :=
    Offset.sub_base _ (by omega_using [hw'])
  have bw : bytesAt t.mem (e + BitVec.ofNat 64 (eo + 8 * w)) 8 =
      bytesAt s.mem (e + BitVec.ofNat 64 eo + BitVec.ofNat 64 (8 * w)) 8 := by
    rw [← ptr_add]
    exact VG.Proof.MlKem.bytesAt_frame ft (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hd.sub_right sub).symm) (by decide)
  refine ⟨(kt.trans ku).mono (by simp), ?_, ?_⟩
  · rw [mu]
    exact ft.writeW (List.mem_singleton_self _) _ cst
  · rw [mu, FixedHash.absorbWord_state _ _ _ (by omega_using [hn, hw']), st', bw, show 8 * (w + 1) = 8 * w + 8 by omega_using [],
      VG.Proof.MlKem.bytesAt_add, xorAt_append, VG.Proof.MlKem.bytesAt_length, Nat.zero_add]

theorem padCode_eq (pos sfx : Nat) :
    Impl.MlKem.AArch64.Hybrid.xorByte pos sfx ++ Impl.MlKem.AArch64.Hybrid.xorByte 135 128 =
      FixedHash.padCode .x28 0 136 pos sfx := by
  simp only [FixedHash.padCode, FixedHash.xorByteCode, Impl.MlKem.AArch64.Hybrid.xorByte, Nat.zero_add]

/-- What the code needs of the message `S`: its register is kept by the
calls around it, and its words are within reach of `ldr`. -/
structure SrcOk (S : Impl.MlKem.AArch64.Hybrid.HSrc) : Prop where
  reg : S.r = .x25 ∨ S.r = .x26 ∨ S.r = .x28
  h8 : S.len % 8 = 0
  b8 : S.base % 8 = 0
  lim : S.base + S.len ≤ 32768

theorem SrcOk.keep {S : Impl.MlKem.AArch64.Hybrid.HSrc} (h : SrcOk S) {rs : List Reg} {s t : State}
    (k : Keep rs s t) (h25 : .x25 ∉ rs) (h28 : .x28 ∉ rs) (h26 : .x26 ∉ rs := by decide) :
    t.gpr S.r = s.gpr S.r := by
  rcases h.reg with e | e | e <;> rw [e]
  · exact k.gpr _ h25
  · exact k.gpr _ h26
  · exact k.gpr _ h28

theorem SrcOk.not9 {S : Impl.MlKem.AArch64.Hybrid.HSrc} (h : SrcOk S) : S.r ∉ [.x9, .x10] := by
  rcases h.reg with e | e | e <;> rw [e] <;> decide

/-- Block `b` of `pad(E)` XORed into the state: once permuted, the next state. -/
theorem absorbBlock_ok (S : Impl.MlKem.AArch64.Hybrid.HSrc) {s : State} {e st : Addr} {E : List Byte}
    {b : Nat} (hS : SrcOk S)
    (he : s.gpr S.r + BitVec.ofNat 64 S.base = e) (hs : s.gpr .x28 = st) (hb : 136 * b < S.len)
    (hE : bytesAt s.mem e S.len = E) (hst : stateAt s.mem st = hstate E b (dB S))
    (hr : Covers [⟨e, S.len⟩] (s.rd ++ s.wr))
    (hw : Covers [stR st] s.wr) (hd : (stR st).Disjoint ⟨e, S.len⟩) :
    WP isa (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock S b)) s fun t =>
      Keep [.x9, .x10] s t ∧ Frame [stR st] s.mem t.mem ∧
      keccakF (stateAt t.mem st) = hstate E (b + 1) (dB S) := by
  have h8 := hS.h8
  have hb8 := hS.b8
  have hlim := hS.lim
  have hlen : E.length = S.len := by rw [← hE]; exact VG.Proof.MlKem.bytesAt_length _ _ _
  have rd : ∀ {o n : Nat}, o + n ≤ S.len → InRegions (s.rd ++ s.wr) (e + BitVec.ofNat 64 o) n :=
    fun h => covers_in hr h (by omega_using [hlim])
  -- the words at `S.r + S.base + o` are those at `e + o`
  have pa : ∀ o : Nat, s.gpr S.r + BitVec.ofNat 64 (S.base + o) = e + BitVec.ofNat 64 o := fun o => by
    rw [← ptr_add, he]
  unfold Impl.MlKem.AArch64.Hybrid.absorbBlock
  split
  · rename_i hfull
    refine WP.mono (absorbWords_ok (e := s.gpr S.r) (eo := S.base + 136 * b) hS.not9 rfl hs (by decide)
      (by omega_using [hb8]) (by omega_using [hlim, hfull])
      (fun w hw' => by rw [Nat.add_assoc, pa]; exact rd (by omega_using [hfull, hw'])) hw
      (by rw [pa]; exact hd.sub_right (Offset.sub_base e (by omega_using [hfull])))) fun t ⟨kt, ft, mt⟩ => ⟨kt, ft, ?_⟩
    rw [mt, hst, pa, show 8 * 17 = 136 from rfl, ← VG.Proof.MlKem.bytesAt_slice _ _ hfull, hE]
    exact hstate_full (by omega_using [hlen, hfull])
  · rename_i hpart
    have hnw : 8 * ((S.len - 136 * b) / 8) = S.len - 136 * b := by omega_using [h8]
    rw [List.append_assoc, WP.block_append_iff, padCode_eq]
    refine WP.mono (absorbWords_ok (e := s.gpr S.r) (eo := S.base + 136 * b) hS.not9 rfl hs (by omega_using [hpart])
      (by omega_using [hb8]) (by omega_using [hb, hlim])
      (fun w hw' => by rw [Nat.add_assoc, pa]; exact rd (by omega_using [hw'])) hw
      (by rw [pa]; exact hd.sub_right (Offset.sub_base e (by omega_using [hb])))) fun t ⟨kt, ft, mt⟩ => ?_
    have t28 : t.gpr .x28 = st := (kt.get .x28).trans hs
    refine WP.mono (FixedHash.pad_ok (s := t) (sc := .x28) (st := 0) (rate := 136)
      (pos := S.len - 136 * b) (sfx := S.sfx) (by decide) (by decide) (by decide) (by decide)
      (by omega_using [hpart]) (by decide)
      (by rw [kt.wr, t28, ptr_zero]; exact hw)) fun u ⟨ku, fu, mu⟩ => ?_
    rw [t28, ptr_zero] at fu mu
    refine ⟨(kt.trans ku).mono (by simp), ft.trans fu, ?_⟩
    rw [mu, mt, hst, pa, hnw, ← VG.Proof.MlKem.bytesAt_drop _ _ (by omega_using [hb]), hE]
    have hh := hstate_last (E := E) (b := b) (d := dB S) (by omega_using [hb, hlen]) (by omega_using [hlen, hpart])
    rw [hlen] at hh
    exact hh

end VG.Proof.MlKem.AArch64.Hybrid
