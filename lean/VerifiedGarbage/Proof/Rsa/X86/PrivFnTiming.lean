module

public import VerifiedGarbage.Proof.Rsa.X86.PrivFnInput
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Rsa.X86.PrivBodyTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivNoSp
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.RandomFinish

/-! # Stack allocation and saved-register restoration reveal only public addresses -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked
open VG.Proof.Dsa.X86 (allocated)

theorem restore_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block restore)
    (VG.X86.Taint.Agree (τr [.esp])) := VG.Proof.Dsa.X86.checkedBlockInvariant rfl rfl

theorem allocation_state {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) :
    a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem privateAllocation_relCT (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun a b => ∃ s t, PrivFnInput g bs1 s ∧ PrivFnInput g bs2 t ∧
      a = pushed savedRegisters s ∧ b = pushed savedRegisters t)
      (.frame (.alloc VG.Impl.Rsa.X86.PrivChecked.frameBytes)
        (body v.name v.code v.pcName v.pc v.pdName v.pd) (.free VG.Impl.Rsa.X86.PrivChecked.frameBytes))
      (fun a b => a.gpr .esp = b.gpr .esp) := by
  intro a b ta tb a' b' hp ea eb'
  obtain ⟨s, t, hs, ht, rfl, rfl⟩ := hp
  have sp : (pushed savedRegisters s).gpr .esp = (pushed savedRegisters t).gpr .esp := by
    rw [hs.savedSp, ht.savedSp]
  have post : a'.gpr .esp = b'.gpr .esp := by
    rw [Exec.gpr (privateAllocation_noSp v) ea, Exec.gpr (privateAllocation_noSp v) eb', sp]
  cases ea with
  | frame pa ba _ =>
    cases eb' with
    | frame pb bb _ =>
      have ha := allocation_state pa
      have hb := allocation_state pb
      subst ha hb
      have eq := (privateBody_relCT v nb eb) _ _ _ _ _ _ ⟨⟨hs.context⟩, ⟨ht.context⟩⟩ ba bb
      refine ⟨?_, post⟩
      rw [eq.1]
      rfl

theorem privateFn_relCT (v : CrtImpl) {g : PrivGeometry} {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => PrivFnInput g bs1 s ∧ PrivFnInput g bs2 t)
      (privCode v) (fun _ _ => True) := by
  unfold privCode code
  refine RelCT.frame (R := fun _ _ => True) ?_ ?_
  · intro s t h
    have eq := h.1.savedSp.trans h.2.savedSp.symm
    rw [pushed_esp, pushed_esp] at eq
    have same := congrArg (fun x => x + BitVec.ofNat 32 (4 * savedRegisters.length)) eq
    simpa only [BitVec.sub_add_cancel] using same
  · refine VG.RelCT.seq ((privateAllocation_relCT v (g := g) nb eb).mono ?_ (fun _ _ h => h))
      (restore_relCT.mono (fun _ _ h => sp_agree h) (fun _ _ _ => trivial))
    rintro a b ⟨s, t, h, rfl, rfl⟩
    exact ⟨s, t, h.1, h.2, rfl, rfl⟩
end VG.Proof.Rsa.X86.PrivChecked
