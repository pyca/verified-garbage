module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext

/-! The public sieve loop records precisely which RSA primes have been tried. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (arrAt)

def sieveAny (value count : Nat) : Bool :=
  (List.range count).any fun i => value % VG.Impl.RsaKeyGen.tabEntry i == 0

theorem sieveAny_succ (value count : Nat) :
    sieveAny value (count + 1) = (sieveAny value count || value % VG.Impl.RsaKeyGen.tabEntry count == 0) := by
  rw [sieveAny, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  rfl

structure SieveInv (s0 : State) (dst base : BitVec 32) (n value i : Nat) (s : State) : Prop where
  context : SieveContext dst base n s
  index : i ≤ 53
  cursor : s.gpr .r10 = base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34 + 4 * i)
  count : s.gpr .r11 = BitVec.ofNat 32 (53 - i)
  bad : s.mem.readW (State.addr (s.sp + 64#32)) 32 = if sieveAny value i then 1 else 0
  candidate : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) = value
  changed : Frame [sieveLocal s0.sp] s0.mem s.mem
  rest : Rest sieveRegs s0 s

end VG.Proof.Ffdh.Arm.ParameterCandidate
