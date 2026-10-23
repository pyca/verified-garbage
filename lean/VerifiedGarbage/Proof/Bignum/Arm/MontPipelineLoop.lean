module

public import VerifiedGarbage.Proof.Bignum.Arm.MontState
public import VerifiedGarbage.Proof.Bignum.Arm.RoundCT
public import VerifiedGarbage.Impl.Bignum.Arm.MontPipeline

/-! # What the pipeline needs of its loop of rounds

The Montgomery pipeline uses its rounds only through their loop: from a
cleared accumulator it reaches the complete invariant (`LoopLaw`), on a
public schedule (`LoopCTLaw`). Single rounds (`RoundLaw.loop`) and rounds
of two rows (`PairLaw.loop`) both supply them. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.MontPipeline
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

def LoopLaw (round : Prog isa) : Prop :=
  ∀ (s : State) {base : BitVec 32} {size tmp a b mod acc n : Nat} {inv : BitVec 32},
    RoundCtx s base size tmp a b mod acc n → n % 2 = 0 →
    RoundMeta s.mem base tmp a b mod acc n 0 inv →
    s.gpr .r0 = base + BitVec.ofNat 32 tmp →
    val32 s.mem (State.addr base) acc (n + 2) = 0 →
    val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n →
    (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0 →
    WP isa (VG.Impl.Bignum.Arm.MontPipeline.rounds round) s (MontInv s base tmp a b mod acc n n inv)

def LoopCTLaw (round : Prog isa) : Prop :=
  ∀ {base : BitVec 32} {size tmp a b mod acc n : Nat}, n % 2 = 0 →
    RelCT isa (fun s t => RoundReady base size tmp a b mod acc n 0 s ∧
      RoundReady base size tmp a b mod acc n 0 t) (VG.Impl.Bignum.Arm.MontPipeline.rounds round)
      (fun _ _ => True)

end VG.Proof.Bignum.Arm.MontPipeline
