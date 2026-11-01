module
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.TCB.AArch64.Target

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLoop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Verified eight-coefficient ByteDecode12 -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Codec16 (dec)

theorem dec_correct (s : State) (hs : decode12AArch64.pre s) :
    ∃ t s', Exec isa dec s t s' ∧ abiPreserved s s' ∧ decode12AArch64.post s s' := by
  obtain ⟨h1,h2,h3⟩ := hs
  obtain ⟨t,s',he,hi⟩ := dec_loop_ok (s0:=s) ⟨h1,h2,h3⟩
  exact ⟨t,s',he,abi_of rfl (by decide +kernel) he,
    (show CoeffsUpTo s'.mem (Decode12.fP s) 256 _ _ from hi.out).polyIs fun _ _ => rfl⟩

theorem dec_ct : ConstantTime isa decode12AArch64.pre decode12AArch64.pub dec :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ ⟨h0,h1,hsp⟩ => agree_of hsp (by simp [h0,h1])) (by taint_decide)

theorem dec_verified : Verified AArch64.target dec (Proof.MlKem.decode12Contract AArch64.abi) :=
  Verified.of_correct dec_correct dec_ct (by
    mlkem_implies [Proof.MlKem.decode12Contract,Proof.MlKem.decode12Sig,decode12AArch64,AArch64.abi,
      AArch64.argRegs] [Decode12.sat] using Decode12.sat)

end VG.Proof.MlKem.AArch64.Codec16
