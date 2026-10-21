module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDTrivial
import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Retry clears the export mask and returns the specified status two -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem retry_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa retry s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kOk, kStatus] s.mem t.mem ∧
      slot t.mem B kOk = 0 ∧ slot t.mem B kStatus = 2 ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.sc kOk) .eax] ++
    [.mov .eax (.imm 2), .store (VG.Impl.Mont.X86.sc kStatus) .eax])) s _
  refine WP.block_append (WP.mono (dZero_ok h) fun u ⟨hu, Ou, mask, Ku⟩ => ?_)
  refine wp_movS rfl fun v V _ => ?_
  refine WP.mono (store_slot (hu.rest V.keeps) (by decide) .eax)
    fun t ⟨ht, Ot, status, Kt⟩ => ?_
  rw [V.mem] at Ot
  rw [V.gpr] at status
  refine ⟨ht, Ou.join Ot (js := []) (ds := [kOk, kStatus]), ?_, status,
    Ku.trans (V.keeps.trans (Kt.mono (by decide)))⟩
  exact (Ot.slot (by decide) (by decide)).trans mask

end VG.Proof.RsaKeyGen.X86.Key
