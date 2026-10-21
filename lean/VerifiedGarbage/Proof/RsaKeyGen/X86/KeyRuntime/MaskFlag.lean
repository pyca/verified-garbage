module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar

/-! # Combine a checked bit with the persistent RSA validity mask -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (kOk kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem withFlag_ok {s : State} {B : Addr} {Z n value : Nat} {c : Prog isa} {rs : List Reg}
    (bit : slot s.mem B kOk ≤ 1) (valueBit : value ≤ 1)
    (correct : WP isa c s fun u => Ws u B Z n 32 ∧ Keep B n [] [kFlag] s.mem u.mem ∧
      slot u.mem B kFlag = value ∧ Keeps rs s u) (eax : .eax ∈ rs := by decide) :
    WP isa (withFlag c) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if slot s.mem B kOk = 1 ∧ value = 1 then 1 else 0) ∧ Keeps rs s t := by
  unfold withFlag
  refine WP.seq (WP.mono correct fun u ⟨hu, Ou, flag, Ku⟩ => ?_)
  have maskU : slot u.mem B kOk = slot s.mem B kOk := Ou.slot (by decide) (by decide)
  refine WP.mono (andS_ok hu (by decide) (by decide) (by decide)
    (by rw [maskU]; exact bit) (by rw [flag]; exact valueBit)) fun t ⟨ht, Ot, mask, Kt⟩ => ?_
  exact ⟨ht, Ou.join Ot (js := []) (ds := [kFlag, kOk]), by rw [mask, maskU, flag], Ku.trans (Kt.mono (by simpa using eax))⟩


end VG.Proof.RsaKeyGen.X86.KeyRuntime
