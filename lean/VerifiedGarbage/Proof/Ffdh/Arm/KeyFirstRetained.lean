module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.KeyFirst
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.OutputSlice
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.TCB.Arm.Isa

/-! The first masked scalar byte preserves domain, entropy, and saved pointers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyFirst_retained (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : ArgumentMemory p slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (h20 : 20 ∈ slots) (h68 : 68 ∈ slots)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 p.scalarLead) (dest : s.gpr .r0 = p.scalarStart) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.first) s fun t =>
      ArgumentMemory p slots t ∧ Octets p.base p.entropy p.len rb t ∧
      t.mem (State.addr p.scalarStart) = rb.getD p.scalarLead 0 &&& p.scalarMask.setWidth 8 ∧
      t.gpr .r0 = p.privateValue + BitVec.ofNat 32 (p.scalarLead + 1) ∧
      t.gpr .r1 = p.entropy + BitVec.ofNat 32 (p.scalarLead + 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (p.scalarWidth - 1) ∧
      Frame [⟨State.addr p.scalarStart, 1⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  have lead := p.scalarLeadBound
  have addr : State.addr p.scalarStart = off (State.addr p.privateValue) p.scalarLead :=
    VG.Arm.addr_add (by have := output.fits; omega)
  have sub : (⟨State.addr p.scalarStart, 1⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ := by
    rw [addr]
    exact Offset.sub_base _ (by omega)
  have destBuf := output.slice (d := p.scalarLead) (n := 1) (by decide) (by omega)
  have read : InRegions (s.rd ++ s.wr) (State.addr (p.entropy + BitVec.ofNat 32 p.scalarLead)) 1 := by
    rw [VG.Arm.addr_add (by have := entropy.fits; omega)]
    exact CallLay.inRegions_sub entropy.readable (by omega) (by have := entropy.fits; omega)
  refine WP.mono (keyFirst_ok s h h20 h68 source dest read destBuf.writable
    ((stackSep.sub_right sub).sub_left (Offset.sub_base _ (by decide)))) ?_
  rintro t ⟨⟨mem, dstT, srcT, countT⟩, rest⟩
  have frame : Frame [⟨State.addr p.scalarStart, 1⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have context := h.after_output frame rest (domainSep.sub_right sub) (stackSep.sub_right sub) saved
  have entropyT := entropy.after_frame frame rest (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    simpa only [size] using entropySep.sub_right sub)
  refine ⟨context, entropyT, ?_, ?_, ?_, ?_, frame, rest⟩
  · have byte := entropy.byte p.scalarLead (by omega)
    rw [mem, VG.WriteBytes.writeW8_apply]
    rw [VG.Arm.addr_add (a := p.entropy) (k := p.scalarLead) (by have := entropy.fits; omega)]
    simp only [ite_true, off] at *
    rw [byte]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : p.scalarLead < rb.length), Option.getD_some]
  · rw [dstT, Inputs.scalarStart, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · rw [srcT, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · rw [countT]
    exact Offset.ofNat_sub_ofNat (by have := p.scalarWidthBounds; omega : 1 ≤ p.scalarWidth)

end VG.Proof.Ffdh.Arm
