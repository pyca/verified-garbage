module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext

/-! Track p and p-1 divisibility through the shared public prime table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

def pairAny (value count : Nat) : Bool :=
  (List.range count).any fun i => (value % VG.Impl.RsaKeyGen.tabEntry i == 0 ||
    (VG.Impl.RsaKeyGen.tabEntry i-1+value) % VG.Impl.RsaKeyGen.tabEntry i == 0)

theorem pairAny_succ (value count : Nat) :
    pairAny value (count + 1) = (pairAny value count || (value % VG.Impl.RsaKeyGen.tabEntry count == 0 ||
      (VG.Impl.RsaKeyGen.tabEntry count-1+value) % VG.Impl.RsaKeyGen.tabEntry count == 0)) := by
  rw [pairAny, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  rfl

def pairNext (n value i : Nat) : Nat := if pairAny value i then trialCount n else i+1

structure PairInv (s0 : State) (dst base : BitVec 32) (n value i : Nat) (s : State) : Prop where
  context : SieveContext dst base n s
  index : i ≤ (trialCount n)
  cursor : s.gpr .r10 = base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34 + 4 * i)
  count : s.gpr .r11 = BitVec.ofNat 32 ((trialCount n) - i)
  bad : s.mem.readW (State.addr (s.sp + 64#32)) 32 = if pairAny value i then 1 else 0
  candidate : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) = value
  changed : Frame [sieveLocal s0.sp] s0.mem s.mem
  rest : Rest sieveRegs s0 s

end VG.Proof.Ffdh.Arm.ParameterCandidate
