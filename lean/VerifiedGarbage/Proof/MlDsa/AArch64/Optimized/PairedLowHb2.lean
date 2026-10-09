import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowBlocks

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Proof.MlDsa.Round VG.Proof.MlDsa.AArch64.Round VG.Impl.MlDsa.AArch64.Round

theorem lowWrap_raw (g : Nat) (a : BitVec 32) :
    lowWrapWord g (HighPack.raw g a)=lowHighWord g a := by
  unfold lowWrapWord lowHighWord HighPack.highWord
  split <;> rfl

def lowHbTwo (g : Nat) (r q : VReg) : List Instr := lowHfTwo g .v24 r ++ lowWrapTwo g q

theorem lowHbTwo_ok {g : Nat} (hg : IsG g) {r q : VReg}
    (hr26 : r≠.v26) (hq25 : q≠.v25) (hq26 : q≠.v26) (hq28 : q≠.v28)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (h11 : ∀e<4,vword (s.v .v11) e=BitVec.ofNat 32 127)
    (h12 : ∀e<4,vword (s.v .v12) e=BitVec.ofNat 32 (hbMul g))
    (h13 : ∀e<4,vword (s.v .v13) e=BitVec.ofNat 32 (hbAdd g))
    (h14 : ∀e<4,vword (s.v .v14) e=BitVec.ofNat 32 (if g==261888 then 15 else dMod g))
    (k : ∀v,VChg [.v25,q,.v26,.v28] s v →
      (∀e<4,vword (v.v .v26) e=lowHighWord g (vword (s.v .v24) e)) →
      (∀e<4,vword (v.v .v28) e=lowHighWord g (vword (s.v r) e)) →
      WP isa (.block rest) v Q) :
    WP isa (.block (lowHbTwo g r q++rest)) s Q := by
  unfold lowHbTwo
  rw [List.append_assoc]
  refine lowHfTwo_ok hg hr26 h11 h12 h13 fun u hu ha hb => ?_
  refine lowWrapTwo_ok hq25 hq26 hq28
    (by intro e he; rw [hu.get .v14 (by decide)]; exact h14 e he)
    fun v hv hva hvb => k v ((hu.trans hv).mono (by simp)) ?_ ?_
  · intro e he; rw [hva e he,ha e he,lowWrap_raw]
  · intro e he; rw [hvb e he,hb e he,lowWrap_raw]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
