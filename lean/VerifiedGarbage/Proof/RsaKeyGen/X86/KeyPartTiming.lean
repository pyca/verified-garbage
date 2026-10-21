module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCrtTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalTiming

/-! # The complete post-retry arithmetic has a fixed native schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key

theorem keyPart_public (n : Nat) : KeyPublic (keyPart n) := by
  unfold keyPart
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact qinvPart_public _
  · exact crtPart_public _
  · exact nPart_public _
  · exact finalMask_public _
  · exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem retry_public : KeyPublic retry :=
  ⟨.block [], zeroTaint true, rfl, rfl⟩

end VG.Proof.RsaKeyGen.X86.Key
