module

public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Loop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Loop
import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.Rc4.AArch64.Group
import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.Rc4.Stream
import VerifiedGarbage.Proof.Rc4.Table
meta import VerifiedGarbage.Proof.Blowfish.AArch64.Lanes
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
meta import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lane
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Table
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.Rc4.AArch64.Group
meta import VerifiedGarbage.Proof.Rc4.AArch64.Rotate
meta import VerifiedGarbage.Proof.Rc4.AArch64.Rows
meta import VerifiedGarbage.Proof.Rc4.Stream
meta import VerifiedGarbage.Proof.Rc4.Table

/-! # Verified vector CBD2 using the existing public contract -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (code)

theorem correct (s : State) (hs : cbd2AArch64.pre s) :
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ cbd2AArch64.post s s' := by
  obtain ⟨h1,h2,h3⟩ := hs
  obtain ⟨t,s',he,hi⟩ := loop_ok (s0 := s) ⟨h1,h2,h3⟩
  exact ⟨t,s',he,abi_of rfl (by decide +kernel) he,
    (show CoeffsUpTo s'.mem (Cbd2.fP s) 256 _ _ from hi.out).polyIs fun _ _ => rfl⟩

theorem ct : ConstantTime isa cbd2AArch64.pre cbd2AArch64.pub code :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1])
    (fun _ _ _ _ ⟨h0,h1,hsp⟩ => agree_of hsp (by simp [h0,h1])) (by taint_decide)

theorem verified : Verified AArch64.target code (Spec.MlKem.cbd2Contract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.cbd2Contract,Spec.MlKem.cbd2Sig,cbd2AArch64,AArch64.abi,
      AArch64.argRegs] [Cbd2.sat] using Cbd2.sat)

end VG.Proof.MlKem.AArch64.Cbd16
