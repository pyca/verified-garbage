module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Halving
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CountEven
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingNext
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Half
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Ops
public import VerifiedGarbage.Proof.Rsa.RecoverMath

/-! Values retained while computing a candidate's power of two. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

structure HalvingState (L : Lay) (base : Addr) (bytes len count value twos remaining : Nat) (s : State) : Prop where
  workspace : RtWs L s base bytes len count
  value : num s.mem base (kw len) 0 = value
  twos : slot s.mem base 20 = twos
  remaining : slot s.mem base 56 = remaining

structure HalvingTemp (L : Lay) (base : Addr) (bytes len count r tc rem : Nat) (s : State) : Prop
    extends HalvingState L base bytes len count r tc rem s where
  temp : num s.mem base (kw len) 1 = r / 2

end VG.Proof.Dsa.X86.Generation
