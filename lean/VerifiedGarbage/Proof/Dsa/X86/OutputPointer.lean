module

public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Selecting either scalar in the packed signature output -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem outputPointer_ok {s : State} {base : Addr} {size qLen : Nat}
    (hs : Scr s base size) (hz : Layout.saved ≤ size) (second : Bool) :
    WP isa (.block (SignVerify.outputPointer qLen second)) s fun t =>
      t.gpr .esi = pointerValue base s (.input .out) + (if second then BitVec.ofNat 32 qLen else 0) ∧
      Keeps [.esi] s t ∧ t.mem = s.mem := by
  unfold SignVerify.outputPointer
  refine WP.block_append (WP.mono (pointer_ok hs hz (.input .out)) fun u ⟨P, K, O⟩ => ?_)
  cases second
  · exact WP.block_nil ⟨by simpa using P, K, O⟩
  · refine wp_addS rfl fun t ut _ => WP.block_nil ⟨?_, K.trans ut.keeps, ut.mem.trans O⟩
    simp only [ut.gpr, P, ite_true]

end VG.Proof.Dsa.X86
