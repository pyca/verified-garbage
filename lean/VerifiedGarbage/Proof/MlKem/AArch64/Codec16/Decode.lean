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

end VG.Proof.MlKem.AArch64.Codec16
