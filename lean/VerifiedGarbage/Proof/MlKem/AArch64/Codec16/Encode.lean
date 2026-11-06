module
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncBase
public import VerifiedGarbage.TCB.AArch64.Target

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncLoop
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
meta import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncBase
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncLoop
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Verified eight-coefficient ByteEncode12 -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Codec16 (enc)

theorem enc_correct (s : State) (hs : encode12AArch64.pre s) :
    ∃ t s', Exec isa enc s t s' ∧ abiPreserved s s' ∧ encode12AArch64.post s s' := by
  obtain ⟨h1,h2,h3,h4⟩ := hs
  obtain ⟨t,s',he,hi⟩ := enc_loop_ok (s0:=s) ⟨h1,h2,h3,h4⟩
  exact ⟨t,s',he,abi_of rfl (by decide +kernel) he,
    (show BytesUpTo s'.mem (Encode12.oP s) 384 384 _ _ from hi.out).eq
      (encode12_length _) fun _ _ => rfl⟩

end VG.Proof.MlKem.AArch64.Codec16
