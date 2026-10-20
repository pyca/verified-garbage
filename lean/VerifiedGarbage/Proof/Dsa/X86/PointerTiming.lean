module

public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Dsa.X86.BytesTiming
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Public operand addresses feed constant-time component loading -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem pointer_check (p : Pointer) :
    (taint.checkBlock (workspaceTaint false) (Core.pointer p)).isSome = true := by
  cases p with
  | input f =>
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change (taint.checkBlock (workspaceTaint false) [.mov .esi (.mem (sc 0))]).isSome = true
    rfl
  | «local» offset =>
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change (taint.checkBlock (workspaceTaint false) [.mov .esi (.reg .edi), .alu .add .esi (.imm 0)]).isSome = true
    rfl
  | signatureS =>
    rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint false) = true from rfl)]
    change (taint.checkBlock (workspaceTaint false) [.mov .esi (.mem (sc 0)), .alu .add .esi (.mem (sc 0))]).isSome = true
    rfl

theorem pointer_relCT (p : Pointer) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ pointerValue base s p = pointerValue base t p)
      (.block (Core.pointer p)) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  intro s t tr ur sf tf ⟨S, T, P⟩ E F
  have G : s.gpr .edi = t.gpr .edi := by
    apply BitVec.eq_of_toNat_eq
    exact S.edi_toNat.trans T.edi_toNat.symm
  have Agree : VG.X86.Taint.Agree (workspaceTaint false) s t := by
    apply agree_regs (rs := [.edi])
    intro reg hreg
    obtain rfl := List.mem_singleton.mp hreg
    exact G
  obtain ⟨last, Check⟩ := Option.isSome_iff_exists.mp (pointer_check p)
  have Check' : VG.Taint.check taint (workspaceTaint false) (.block (Core.pointer p)) (.block []) = some last := Check
  have Trace := (VG.Taint.check_sound Check' Agree E F).1
  obtain ⟨_, u, Eu, Pu, Ku, _⟩ := pointer_ok S hz p
  obtain ⟨_, v, Fv, Pv, Kv, _⟩ := pointer_ok T hz p
  obtain ⟨_, rfl⟩ := Exec.det E Eu
  obtain ⟨_, rfl⟩ := Exec.det F Fv
  refine ⟨Trace, ?_⟩
  apply agree_regs (rs := [.edi, .esi])
  intro reg hreg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
  rcases hreg with rfl | rfl
  · rw [Ku.1 _ (by decide), Kv.1 _ (by decide)]; exact G
  · exact Pu.trans (P.trans Pv.symm)

theorem coreLoad_relCT (n len out : Nat) (p : Pointer) (base : Addr) (size : Nat) (hz : Layout.saved ≤ size) :
    RelCT isa (fun s t => Scr s base size ∧ Scr t base size ∧ pointerValue base s p = pointerValue base t p)
      (Core.load n len out p) (VG.X86.Taint.Agree (workspaceTaint true)) :=
  RelCT.seq (pointer_relCT p base size hz) (loadComponent_relCT len n out)

end VG.Proof.Dsa.X86
