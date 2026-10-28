module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext

/-! # The array reduction starts with remainder zero -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem zeroRemainder_ok (s : State) :
    WP isa (.block zeroRemainder) s fun t =>
      t.gpr .ecx = 0#32 ∧ t.gpr .ebx = 0#32 ∧ t.mem = s.mem ∧ Keeps [.ecx, .ebx] s t := by
  unfold zeroRemainder
  refine wp_movS rfl fun a A _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨by rw [T.other .ecx (by decide), A.gpr]; rfl, by rw [T.gpr]; rfl,
    T.mem.trans A.mem, (A.keeps.mono (by decide)).widen T.keeps⟩

end VG.Proof.RsaKeyGen.X86.Mod64
