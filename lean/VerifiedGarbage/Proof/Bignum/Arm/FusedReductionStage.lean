module

public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.FusedReductionBody
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.Block

/-! The Montgomery reduction and radix division share one downward-write pass. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem fusedStage_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n)
    (hdr : RoundMeta s.mem base tmp a b mod acc n i inv)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 (acc+4*n))
    (inverse : (val32 s.mem (State.addr base) mod n*inv.toNat+1)%2^32=0)
    (capacity : val32 s.mem (State.addr base) acc (n+2)+
      (inv*s.mem.readW (off (State.addr base) acc) 32).toNat*val32 s.mem (State.addr base) mod n<
        2^(32*(n+2))) :
    WP isa fusedReductionStage s fun t =>
      2^32*val32 t.mem (State.addr base) acc (n+1)=val32 s.mem (State.addr base) acc (n+2)+
        (inv*s.mem.readW (off (State.addr base) acc) 32).toNat*val32 s.mem (State.addr base) mod n ∧
      RoundMeta t.mem base tmp a b mod acc n i inv ∧
      t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
      Outside (State.addr base) acc (4*(n+1)) s.mem t.mem ∧ Rest roundClobbers s t := by
  have count := ctx.count
  have fits := ctx.tmpFits
  have layout := ctx.layout
  have accFit := ctx.accFits
  rw [fusedReductionStage,WP.seq_iff]
  refine WP.mono (reductionArgs_ok s (acc:=acc) (mod:=mod) (n:=n) inv ctx.workspace
    (by omega) (by omega) ptr ?_ ?_ ?_ ?_) ?_
  · simpa only [show acc+4*n+16=tmp by omega] using hdr.count
  · simpa only [show acc+4*n+24=tmp+8 by omega] using hdr.mPtr
  · simpa only [show acc+4*n+28=tmp+12 by omega] using hdr.inverse
  · simpa only [show acc+4*n+44=tmp+28 by omega] using hdr.accPtr
  · rintro u ⟨scalar,p0,p12,cnt,carry,memU,restU⟩
    have modLow : val32 s.mem (State.addr base) mod n%2^32=w32 s.mem (State.addr base) mod := by
      simpa only [show n-1+1=n by omega] using val32_mod_low s.mem (State.addr base) mod (n-1)
    have lowInverse : (w32 s.mem (State.addr base) mod*inv.toNat+1)%2^32=0 := by
      simpa only [Nat.add_mod,Nat.mul_mod,modLow,Nat.mod_mod] using inverse
    have cancel : ((u.gpr .r1).toNat*w32 u.mem (State.addr base) mod+
        w32 u.mem (State.addr base) acc)%2^32=0 := by
      rw [memU,scalar,BitVec.toNat_mul]
      simpa only [w32,Nat.mul_comm] using
        mont_low (w32 s.mem (State.addr base) acc) inv.toNat (w32 s.mem (State.addr base) mod) lowInverse
    refine WP.mono (FusedReduction.code_ok u (ctx.workspace.congr restU.wr) (by omega)
      accFit ctx.mFits ctx.accM p0 p12 cnt carry cancel ?_) ?_
    · simpa only [memU,scalar] using capacity
    · rintro t ⟨value,pointer,outside,rest⟩
      rw [memU,scalar] at value
      rw [memU] at outside
      exact ⟨value,hdr.of_outside outside (by omega) (by have := ctx.workspace.nowrap;omega),
        pointer,outside,(restU.mono (by decide)).trans rest⟩

end VG.Proof.Bignum.Arm
