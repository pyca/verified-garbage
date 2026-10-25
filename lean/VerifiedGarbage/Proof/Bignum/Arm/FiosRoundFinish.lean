module

public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Exact fused-row division feeds the existing canonical Montgomery round finish. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

theorem finishRound_ok (s v : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n)
    (hdr : RoundMeta s.mem base tmp a b mod acc n i inv) (hi : i < n)
    (hT : val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (quotient : ∃ q < 2^32, 2^32 * val32 v.mem (State.addr base) acc (n+1) =
      val32 s.mem (State.addr base) acc (n+2) +
        w32 s.mem (State.addr base) (a+4*i) * val32 s.mem (State.addr base) b n +
          q * val32 s.mem (State.addr base) mod n)
    (ptrV : v.gpr .r0 = base + BitVec.ofNat 32 (acc + 4*(n+1)))
    (outsideV : Outside (State.addr base) acc (4*(n+1)) s.mem v.mem)
    (keepV : Rest roundClobbers s v) :
    WP isa (.block roundFinish) v fun t => RoundPost s t base tmp a b mod acc n i inv := by
  have nowrap := ctx.workspace.nowrap
  have fits := ctx.tmpFits
  have layout := ctx.layout
  have hdrV := hdr.of_outside outsideV (by omega) (by omega)
  refine WP.mono (roundFinish_ok (tmp:=tmp) (top:=acc+4*(n+1)) v
    (ctx.workspace.congr keepV.wr) (by omega) (by omega) ptrV) ?_
  rintro t ⟨memT,ptrT,zero,keepT⟩
  have mt : t.mem = finishMem v.mem (State.addr base) (acc+4*(n+1)) tmp := memT
  have nowrap' : (State.addr base).toNat + size ≤ 2^32 := by
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
  obtain ⟨result,frame⟩ := finish_value (mem:=v.mem) (acc:=acc) (n:=n) (tmp:=tmp)
    nowrap' (by omega) rfl (by omega)
  rw [←mt] at result frame
  obtain ⟨q,hq,quotient⟩ := quotient
  have value : 2^32 * val32 t.mem (State.addr base) acc (n+2) =
      val32 s.mem (State.addr base) acc (n+2) +
        w32 s.mem (State.addr base) (a+4*i) * val32 s.mem (State.addr base) b n +
          q * val32 s.mem (State.addr base) mod n := by rw [result,quotient]
  have ha := (s.mem.readW (off (State.addr base) (a+4*i)) 32).isLt
  refine ⟨?_,ptrT,⟨q,hq,value⟩,round_lt value hT ha hB hq,?_,?_,?_⟩
  · rw [mt]
    exact finish_meta nowrap fits (by omega) hdrV hi
  · have enlarged : Outside (State.addr base) acc (4*(n+2)) s.mem v.mem :=
      outsideV.mono (Nat.le_refl _) (by omega)
    exact (Outs.of_outside enlarged (by simp)).trans frame
  · rw [zero,hdrV.remaining]
    change (BitVec.ofNat 32 (n-i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n-i-1=0 ↔ i+1=n by omega]
  · exact keepV.trans (keepT.mono (by decide))

end VG.Proof.Bignum.Arm.Fios
