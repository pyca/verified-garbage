module

public import VerifiedGarbage.Impl.Bignum.Arm.CopyWords
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Bignum.Arm.SelectStep
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! A word copy writes the source once, without evaluating a selection mask. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm

theorem copyWord_ok (s : State) (o a : Addr)
    (ho : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = o)
    (ha : State.addr (s.gpr .r10 + BitVec.ofNat 32 0) = a)
    (wo : InRegions s.wr o 4) (ra : InRegions (s.rd ++ s.wr) a 4) :
    WP isa copyWord s fun t =>
      t.mem = s.mem.writeW o (s.mem.readW a 32) ∧ Rest selectClobbers s t := by
  unfold copyWord
  refine wp_ldr (a := a) (by decide) ha ra fun u load => ?_
  refine wp_str (a := o) (by decide) (by rw [load.other .r0 (by decide)]; exact ho)
    (by rw [load.wr]; exact wo) fun t store => WP.block_nil ?_
  refine ⟨?_, (load.rest (by simp [selectClobbers])).trans (store.rest _)⟩
  rw [store.mem,load.mem,load.gpr]

end VG.Proof.Bignum.Arm
