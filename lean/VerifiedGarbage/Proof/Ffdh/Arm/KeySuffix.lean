module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroOptional
import VerifiedGarbage.Proof.Ffdh.Arm.CopyOptional
import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.OutputSlice
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Impl.Bignum.Arm.CopyBytes

/-! Copy the scalar suffix after its first significant byte, including the
single-byte-bound case where the suffix is empty. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def scalarSuffix (p : Inputs) : Region :=
  ⟨off (State.addr p.privateValue) (p.scalarLead + 1), p.k - (p.scalarLead + 1)⟩

theorem keySuffix_ok (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : ArgumentMemory p slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy + BitVec.ofNat 32 (p.scalarLead + 1))
    (dest : s.gpr .r0 = p.privateValue + BitVec.ofNat 32 (p.scalarLead + 1))
    (count : s.gpr .lr = BitVec.ofNat 32 (p.k - (p.scalarLead + 1))) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr VG.Impl.Bignum.Arm.copyBytes) s fun t =>
      ArgumentMemory p slots t ∧ Octets p.base p.entropy p.len rb t ∧
      Spec.Rsa.bytesAt t.mem (scalarSuffix p).base (scalarSuffix p).len = rb.drop (p.scalarLead + 1) ∧
      Frame [scalarSuffix p] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have lead := p.scalarLeadBound
  by_cases empty : p.k - (p.scalarLead + 1) = 0
  · rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero, WP.seq_iff]
    refine WP.mono (zeroCount_ok s) ?_
    rintro t ⟨⟨zeroT, mem⟩, rest⟩
    refine WP.ite true (by change some t.z = some true; rw [zeroT, count, empty]; rfl) ?_ (by intro hf; cases hf)
    intro _
    apply WP.block_nil
    have frame : Frame [⟨State.addr p.privateValue, p.k⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
    have context := h.after_output frame rest domainSep stackSep saved
    have entropyT := entropy.after_frame frame rest (by simpa [size] using entropySep)
    refine ⟨context, entropyT, ?_, ?_, rest.mono (by simp)⟩
    · simp only [scalarSuffix, empty, Spec.Rsa.bytesAt, List.range_zero, List.map_nil]
      exact (List.drop_eq_nil_iff.mpr (by omega)).symm
    · rw [mem]; exact Frame.refl _ _
  · have positive : 0 < p.k - (p.scalarLead + 1) := by omega
    have out := output.slice positive (by omega : (p.scalarLead + 1) + (p.k - (p.scalarLead + 1)) ≤ p.k)
    have inp := entropy.slice positive (by omega : (p.scalarLead + 1) + (p.k - (p.scalarLead + 1)) ≤ rb.length)
    have inpSize : ((rb.drop (p.scalarLead + 1)).take (p.k - (p.scalarLead + 1))).length = p.k - (p.scalarLead + 1) := by
      simp only [List.length_take, List.length_drop, size, Nat.min_self]
    have inpAddr := VG.Arm.addr_add (a := p.entropy) (k := p.scalarLead + 1) (by have := entropy.fits; omega)
    have outAddr := VG.Arm.addr_add (a := p.privateValue) (k := p.scalarLead + 1) (by have := output.fits; omega)
    have inpSub : (⟨State.addr (p.entropy + BitVec.ofNat 32 (p.scalarLead + 1)), p.k - (p.scalarLead + 1)⟩ : Region).Sub
        ⟨State.addr p.entropy, p.k⟩ := by rw [inpAddr]; exact Offset.sub_base _ (by omega)
    have outSub : (⟨State.addr (p.privateValue + BitVec.ofNat 32 (p.scalarLead + 1)), p.k - (p.scalarLead + 1)⟩ : Region).Sub
        ⟨State.addr p.privateValue, p.k⟩ := by rw [outAddr]; exact Offset.sub_base _ (by omega)
    refine WP.mono (copyOptional_ok s (by have := p.maxLength; omega) (by simpa only [inpSize] using inp.fits) out.fits
      (by simpa only [inpSize] using inp.readable) out.writable ((entropySep.sub_left inpSub).sub_right outSub)
      source dest count) ?_
    rintro t ⟨bytes, frame, rest⟩
    have context := h.after_output frame rest (domainSep.sub_right outSub) (stackSep.sub_right outSub) saved
    have entropyT := entropy.after_frame frame rest (by simpa [size] using entropySep.sub_right outSub)
    refine ⟨context, entropyT, ?_, ?_, rest⟩
    · rw [outAddr, inpAddr] at bytes
      rw [← VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p.entropy) (by omega : (p.scalarLead + 1) + (p.k - (p.scalarLead + 1)) ≤ rb.length), entropy.bytes] at bytes
      rw [List.take_of_length_le (by simp only [List.length_drop, size]; omega)] at bytes
      exact bytes
    · simpa only [scalarSuffix, outAddr] using frame

end VG.Proof.Ffdh.Arm
