module

public import VerifiedGarbage.Impl.Rsa.Arm.PrivChecked
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.Arm.PcEntryCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Stack-addressed argument blocks have public traces -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm

theorem stackAddressBlock_ct (code : List Instr)
    (leak : ∀ i ∈ code, ∀ s t : State, s.sp = t.sp → addrs i s = addrs i t) :
    RelCT isa (fun s t => s.sp = t.sp) (.block code) (fun s t => s.sp = t.sp) := by
  induction code with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons i rest ih =>
    have first : RelCT isa (fun s t => s.sp = t.sp) (.block [i]) (fun s t => s.sp = t.sp) := by
      apply single_ct (fun s t h => leak i (by simp) s t h)
      intro s t u v h e1 e2
      exact (exec_sp e1).trans (h.trans (exec_sp e2).symm)
    exact RelCT.block_append (first.seq (ih (fun j hj => leak j (by simp [hj]))))

theorem cmpArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block cmpArgs) (fun s t => s.sp = t.sp) := by
  apply stackAddressBlock_ct
  intro i hi s t sp
  simp only [cmpArgs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [addrs, sp]
end VG.Proof.Rsa.Arm
