module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.SampleFirst
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.OutputSlice
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.TCB.Arm.Isa

/-! The first masked scalar byte preserves domain, entropy, and saved pointers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem sampleFirst_retained (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (h : SampleMemory p l slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 l.lead) (dest : s.gpr .r0 = l.start) :
    WP isa (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.first) s fun t =>
      SampleMemory p l slots t ∧ Octets p.base p.entropy p.len rb t ∧
      t.mem (State.addr l.start) = rb.getD l.lead 0 &&& l.mask.setWidth 8 ∧
      t.gpr .r0 = p.privateValue + BitVec.ofNat 32 (l.lead + 1) ∧
      t.gpr .r1 = p.entropy + BitVec.ofNat 32 (l.lead + 1) ∧
      t.gpr .lr = BitVec.ofNat 32 (l.width - 1) ∧
      Frame [⟨State.addr l.start, 1⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .r3, .lr] s t := by
  have lead := l.lead_lt
  have addr : State.addr l.start = off (State.addr p.privateValue) l.lead :=
    VG.Arm.addr_add (by have := output.fits; omega)
  have sub : (⟨State.addr l.start, 1⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ := by
    rw [addr]
    exact Offset.sub_base _ (by omega)
  have destBuf := output.slice (d := l.lead) (n := 1) (by decide) (by omega)
  have read : InRegions (s.rd ++ s.wr) (State.addr (p.entropy + BitVec.ofNat 32 l.lead)) 1 := by
    rw [VG.Arm.addr_add (by have := entropy.fits; omega)]
    exact CallLay.inRegions_sub entropy.readable (by omega) (by have := entropy.fits; omega)
  refine WP.mono (sampleFirst_ok s h source dest read destBuf.writable
    ((stackSep.sub_right sub).sub_left (Offset.sub_base _ (by decide)))) ?_
  rintro t ⟨⟨mem, dstT, srcT, countT⟩, rest⟩
  have frame : Frame [⟨State.addr l.start, 1⟩] s.mem t.mem := by
    rw [mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have context := h.after_output frame rest (domainSep.sub_right sub) (stackSep.sub_right sub) saved
  have entropyT := entropy.after_frame frame rest (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    simpa only [size] using entropySep.sub_right sub)
  refine ⟨context, entropyT, ?_, ?_, ?_, ?_, frame, rest⟩
  · have byte := entropy.byte l.lead (by omega)
    rw [mem, VG.WriteBytes.writeW8_apply]
    rw [VG.Arm.addr_add (a := p.entropy) (k := l.lead) (by have := entropy.fits; omega)]
    simp only [ite_true, off] at *
    rw [byte]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : l.lead < rb.length), Option.getD_some]
  · rw [dstT, ScalarLayout.start, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · rw [srcT, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  · rw [countT]
    exact Offset.ofNat_sub_ofNat (by have := l.width_bounds; omega : 1 ≤ l.width)

end VG.Proof.Ffdh.Arm
