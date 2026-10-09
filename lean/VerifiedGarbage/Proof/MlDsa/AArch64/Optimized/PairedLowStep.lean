import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowModel
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedCheckStep

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep laneVector laneVector_word)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

theorem lowPairStep_ok {g : Nat} (hg : IsG g) {r q : VReg} {off : Nat}
    (hr : r∉lowReserved) (hq : q∉lowReserved) (hrq : r≠q)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off+128<65536)
    (rd0 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (rd1 : InRegions (s.rd++s.wr) (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wh0 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (wh1 : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 (off+128)) 16)
    (wl0 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (wl1 : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 (off+128)) 16)
    (hmod : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v,StepKeep (lowPairClobs r q) s v →
      dataAt v=lowPairStep g (s.v r) (s.v q)
        (s.gpr .x15+BitVec.ofNat 64 off) (s.gpr .x15+BitVec.ofNat 64 (off+128))
        (s.gpr .x16+BitVec.ofNat 64 off) (s.gpr .x16+BitVec.ofNat 64 (off+128))
        (lowConstantsAt s) (dataAt s) → WP isa (.block rest) v Q) :
    WP isa (.block (lowPairBlocks g r q off++rest)) s Q := by
  refine lowPair_ok hg hr hq hrq ho rd0 rd1 wh0 wh1 wl0 wl1 hmod hc h11 h12 h13 h14
    fun v ha hb la lb hv hm hha hhb hla hlb hf => k v hv ?_
  have vecEq (v : BitVec 128) (f : Nat → BitVec 32)
      (h : ∀e<4,vword v e=f e) : v=laneVector f := by
    apply vec_ext
    intro e he
    rw [laneVector_word _ he]
    exact h e he
  have eha := vecEq ha _ hha
  have ehb := vecEq hb _ hhb
  have ela := vecEq la _ hla
  have elb := vecEq lb _ hlb
  rw [eha,ehb,ela,elb] at hm
  rw [ela,elb] at hf
  apply checkData_ext
  · simpa only [lowPairWrites,lowPairStep,lowInputValues,lowInputWord,lowConstantsAt,dataAt] using hm
  · apply vec_ext
    intro e he
    simpa only [lowPairStep,lowInputValues,lowInputWord,lowConstantsAt,dataAt,laneVector_word _ he] using hf e he
  · have rn : r≠.v14 := by intro he; exact hr (by simp [he,lowReserved])
    have qn : q≠.v14 := by intro he; exact hq (by simp [he,lowReserved])
    exact hv.vec .v14 (by simp [lowPairClobs,Ne.symm rn,Ne.symm qn])
end VG.Proof.MlDsa.AArch64.Optimized.Paired
