module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Math
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lazy.Constant
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.VectorCoreExec
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Constant
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
public import VerifiedGarbage.Proof.Framework.Semantics

@[expose] public section
namespace VG.Proof.Sha3.AArch64.Scalar.Lazy
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Impl.Sha3.AArch64.Scalar.Lazy
open VG.Proof.Sha3.AArch64.Scalar

def machineFile (s : State) : File :=
  ⟨s.gpr, fun k => vdword (s.v (slotV k)) 0⟩

structure Keep (s t : State) : Prop where
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  vec : ∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → t.v v = s.v v

/-- A complete machine-code round realizes the checked rotated lane layout. -/
theorem round_ok (r : Fin 24) (A : Spec.Sha3.State) (s : State)
    (h : LayoutHolds (plan r).input (logicalState A) (machineFile s)) :
    WP isa (.block (round r)) s fun t =>
      LayoutHolds (plan r).finish (logicalState (Spec.Sha3.rnd A r.val)) (machineFile t) ∧
      Keep s t := by
  let f := machineFile s
  have hrel : VectorFileRel f s := ⟨fun _ => rfl, fun _ _ => rfl⟩
  have hp := plans_shape r
  obtain ⟨t, ht, hrt, hm, hrd, hwr, hsp, hv⟩ :=
    vector_list_ok (plan r).core hp.2.2.2.2.1 f s hrel
  unfold round
  rw [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨t, ht, ?_⟩
  rw [WP.block_append_iff]
  refine (Constant.constant_ok (plan r).constantReg r.val t).mono fun u ⟨hk, hu⟩ => ?_
  rw [VG.Proof.Sha3.AArch64.Sha3.Vector.constantLow_RC r.val r.isLt] at hu
  let f1 := (run (plan r).core f).write (plan r).constantReg (Spec.Sha3.RC r.val)
  have hru : VectorFileRel f1 u := by
    constructor
    · intro q
      by_cases hq : q = (plan r).constantReg
      · subst q
        simpa only [f1, File.write, ite_true] using hu
      · simp only [f1, File.write, ite_eq_right hq]
        exact (hk.gpr q hq).trans (hrt.regs q)
    · intro k hkb
      rw [hk.vec]
      exact hrt.slots k hkb
  obtain ⟨v, hvexec, hrv, hvm, hvrd, hvwr, hvsp, hvvec⟩ :=
    vector_step_ok (plan r).iota hp.2.2.2.2.2 f1 u hru
  refine WP.of_runBlock ⟨v, hvexec, ?_⟩
  refine ⟨?_, ⟨hvm.trans (hk.mem.trans hm), hvrd.trans (hk.rd.trans hrd),
    hvwr.trans (hk.wr.trans hwr), hvsp.trans (hk.sp.trans hsp), ?_⟩⟩
  · exact layout_of_regs _ _ _ _ (abstractRound_state r A f h) hrv.regs
  · intro w h24 h25 h28 h29
    exact (hvvec w h24 h25 h28 h29).trans
      ((congrFun hk.vec w).trans (hv w h24 h25 h28 h29))

end VG.Proof.Sha3.AArch64.Scalar.Lazy
