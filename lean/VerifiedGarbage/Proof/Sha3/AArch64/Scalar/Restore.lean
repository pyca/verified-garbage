module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.BoundaryCommon
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar.Boundary
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Scalar.Boundary

structure RestoreInv (orig start : State) (k : Nat) (s : State) : Prop where
  keep : Keep start s
  mem : s.mem = start.mem
  vec : s.v = start.v
  vals : ∀ i < k, s.gpr (savedReg i) = orig.gpr (savedReg i)

theorem restore_ok (orig start : State) (hsave : SavedVector orig start) :
    WP isa (.block restore) start fun s => Keep start s ∧ s.mem = start.mem ∧ s.v = start.v ∧
      ∀ r ∈ preserved, s.gpr r = orig.gpr r := by
  unfold restore
  rw [show (List.range 11).map (fun i => Instr.umov .x (savedReg i) (savedVec i) 0) =
    (List.range 11).flatMap (fun i => [Instr.umov .x (savedReg i) (savedVec i) 0]) by rfl]
  refine (wp_range_flatMap (M := isa) (RestoreInv orig start) (fun i s hi hs => ?_)
    11 (Nat.le_refl _) start ⟨Keep.refl _,rfl,rfl,fun _ h => by omega⟩).mono
    fun s hs => ⟨hs.keep,hs.mem,hs.vec,fun r hr => ?_⟩
  · refine WP.cons (exec_umov_low s (savedReg i) (savedVec i)) (wp_nil ?_)
    refine ⟨⟨hs.keep.rd,hs.keep.wr,hs.keep.sp⟩,hs.mem,hs.vec,fun j hj => ?_⟩
    simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,savedReg_inj j (by omega) i hi]
    split
    · rename_i h; subst j
      rw [hs.vec]
      exact hsave i hi
    · exact hs.vals j (by omega)
  · have hall : ∀ r ∈ preserved, ∃ i : Fin 11, r = savedReg i.val := by decide
    obtain ⟨i,rfl⟩ := hall r hr
    exact hs.vals i.val i.isLt
end VG.Proof.Sha3.AArch64.Scalar.Boundary
