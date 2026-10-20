module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.MemLower
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lower
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive

/-!
# The scalar round with its temporary lanes in memory, run

`lowerMem off` (`Impl/Sha3/AArch64/Scalar/MemLower.lean`) realizes each
abstract operation with the temporary lanes in the words at `[sp, #off]`
and `[sp, #off + 8]`: the round computes what `vectorCoreInstrs` does on
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
    have hoff : (off + 8 * k) % 8 = 0 ∧ off + 8 * k < 32768 := ⟨by omega, by omega⟩
    refine ⟨{ s with mem := s.mem.writeW (s.sp + BitVec.ofNat 64 (off + 8 * k)) (s.gpr a) }, ?_,
      ⟨hr.regs, fun j hj => ?_⟩, ?_, rfl, rfl, rfl, rfl⟩
    · simp only [lowerMem, runBlock_cons, exec_strSp hoff (ho.wr k hk), runStep_some, runBlock_nil]
    · change (s.mem.writeW _ _).readW _ 64 = _
      simp only [step]
      by_cases he : j = k
      · subst j
        rw [Mem.readW_writeW_self64, ite_eq_left rfl, hr.regs]
      · rw [ite_eq_right he, Mem.readW_writeW_sep (w' := 64)
          (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact hr.slots j hj
    · exact (Frame.refl _ _).writeW (r := ⟨s.sp, off + 16⟩) (by simp) _
        (Offset.contains_base _ (by omega) (by omega))
  | reload d k =>
    have hk := hg.1
    have hoff : (off + 8 * k) % 8 = 0 ∧ off + 8 * k < 32768 := ⟨by omega, by omega⟩
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
