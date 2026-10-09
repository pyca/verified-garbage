import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Loads

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg VMem)
open VG.Impl.MlDsa.AArch64.Optimized.Paired

def extraSlots (off : Nat) : List (VReg × Nat) :=
  saved.zipIdx.map fun (r,i) => (r,off+16*i)

theorem save_code : save=(extraSlots 2048).map (fun p => Instr.strq p.1 .x0 p.2) := rfl
theorem restore_code : restoreCode=(extraSlots 1920).map (fun p => Instr.ldrq p.1 .x2 p.2) := rfl

theorem save_ok {s : State}
    (hr : ∀p∈extraSlots 2048,InRegions s.wr (s.gpr .x0+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VMem s t (writeSlice (extraSlots 2048) (s.gpr .x0) s.v s.mem) →
      WP isa (.block rest) t Q) : WP isa (.block (save++rest)) s Q := by
  rw [save_code]
  exact store_many_ok _ _ (by decide) hr k

theorem restore_ok {s : State}
    (hr : ∀p∈extraSlots 1920,InRegions (s.rd++s.wr) (s.gpr .x2+BitVec.ofNat 64 p.2) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀t,VChg saved s t →
      (∀p∈extraSlots 1920,t.v p.1=s.mem.read (s.gpr .x2+BitVec.ofNat 64 p.2) 16) →
      WP isa (.block rest) t Q) : WP isa (.block (restoreCode++rest)) s Q := by
  rw [restore_code]
  exact load_many_ok _ _ (by decide) (by decide) hr k

end VG.Proof.MlDsa.AArch64.Optimized.Paired
