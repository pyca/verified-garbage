module

public import VerifiedGarbage.Impl.Dsa.X86.SignVerify
public import VerifiedGarbage.Proof.Dsa.X86.Checks
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Returning the accumulated acceptance mask as a Boolean status -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem result_ok {base : Addr} {size : Nat} {s : State} (hs : Scr s base size)
    (hz : Layout.saved ≤ size) (accepted : Prop) [Decidable accepted]
    (hm : flagW base (Layout.field .mask) s = mask32 accepted) :
    WP isa (.block SignVerify.result) s fun t =>
      t.gpr .eax = (if accepted then 1 else 0) ∧ Keeps [.eax] s t ∧ t.mem = s.mem := by
  have hb : Layout.field .mask + 4 ≤ size := by
    have H : 8256 ≤ size := hz
    change 8248 ≤ size
    omega
  unfold SignVerify.result
  refine wp_movS (readSrc_sc hs hb) fun u su _ => ?_
  refine wp_logicS (.inl rfl) rfl fun t ut => WP.block_nil ⟨?_, su.keeps.trans ut.keeps, ut.mem.trans su.mem⟩
  rw [ut.gpr, su.gpr]
  change flagW base (Layout.field .mask) s &&& 1 = _
  rw [hm]
  by_cases h : accepted <;> simp [mask32, h]

end VG.Proof.Dsa.X86
