import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskSeedNonce
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskAt

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def pairSeedWrites (j : Nat) : List (Ptr × Nat) :=
  [(sc (oMP+66*j),32),(sc (oMP+66*j+32),32),(sc (oMP+66*j+64),2)]

def pairSeedChk (p : Params) (r j : Nat) : Bool :=
  inB (sgB p) (sc oMS) 32 && inB (sgW p) (sc (oMP+66*j)) 32 &&
  sepB (sgR p) (sgW p) (sc oMS) 32 (sc (oMP+66*j)) 32 &&
  icmChk p [(sc (oMP+66*j),32)] r &&
  inB (sgB p) (sc (oMS+32)) 32 && inB (sgW p) (sc (oMP+66*j+32)) 32 &&
  sepB (sgR p) (sgW p) (sc (oMS+32)) 32 (sc (oMP+66*j+32)) 32 &&
  icmChk p [(sc (oMP+66*j+32),32)] r &&
  keepB (sgR p) (sgW p) [(sc (oMP+66*j+32),32)] (sc (oMP+66*j)) 32 &&
  inB (sgB p) (sc oKAP) 8 && inB (sgW p) (sc (oMP+66*j+64)) 2 &&
  icmChk p [(sc (oMP+66*j+64),2)] r &&
  keepB (sgR p) (sgW p) [(sc (oMP+66*j+64),2)] (sc (oMP+66*j)) 64 &&
  decide (p.ℓ*813+r+j<2^16) && decide (r+j<4096) && decide (j<2)

/-- Two word-oriented copies and two nonce stores prepare exactly the
standard 66-byte seed, preserving the earlier masks and signing state. -/
theorem maskPairSeed_ok {p : Params} {D : Nat} {σ s : State} {t r j : Nat}
    (hc : pairSeedChk p r j=true) (h : ICm p D σ t r s) :
    WP isa (maskPairSeed r j) s fun u => ICm p D σ t r u ∧
      PPostB D s u (pairSeedWrites j) ∧
      bytesAt u.mem (pa u (sc (oMP+66*j))) 66=
        rppOf p σ++integerToBytes (p.ℓ*t+(r+j)) 2 := by
  simp only [pairSeedChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cr0,cw0,cs0,ci0,cr1,cw1,cs1,ci1,ck1,ck,cwn,cin,ckn,hx,hr,hj⟩ := hc
  unfold maskPairSeed
  refine WP.seq (WP.mono (maskSeedHalf_ok h.l.st.lay (by decide) (by decide) cr0 cw0 cs0)
    fun a ⟨ha,_,hb0⟩ => ?_)
  have hA := h.step ha ci0
  have b0 : bytesAt a.mem (pa a (sc (oMP+66*j))) 32=(rppOf p σ).take 32 := by
    rw [ha.pa (by simp [keptRegs]),hb0,← VG.Proof.MlKem.bytesAt_take _ _ (by decide : 32≤64),h.l.k.rpp]
  refine WP.seq (WP.mono (maskSeedHalf_ok hA.l.st.lay (by decide) (by decide) cr1 cw1 cs1)
    fun b ⟨hb,_,hb1⟩ => ?_)
  have hB := hA.step hb ci1
  have b1 : bytesAt b.mem (pa b (sc (oMP+66*j+32))) 32=(rppOf p σ).drop 32 := by
    rw [hb.pa (by simp [keptRegs]),hb1,← pa_sc_add]
    change bytesAt a.mem (pa a (sc oMS)+BitVec.ofNat 64 32) (64-32)=_
    rw [← VG.Proof.MlKem.bytesAt_drop _ _ (by decide : 32≤64),hA.l.k.rpp]
  have b64 : bytesAt b.mem (pa b (sc (oMP+66*j))) 64=rppOf p σ := by
    rw [show 64=32+32 from rfl,VG.Proof.MlKem.bytesAt_add,pa_sc_add,
      hA.l.st.lay.keepBytes hb ck1,b0,b1,List.take_append_drop]
  have hx' : p.ℓ*t+(r+j)<2^16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t≤813 by have := h.l.t_lt; omega)
    omega
  refine WP.mono (maskPairNonce_okB hB.l.st.lay hj hr hx' ck cwn hB.l.kap)
    fun u ⟨hu,_,hbn⟩ => ?_
  have hab := PPostB.trans ha hb (ws := [(sc (oMP+66*j),32),(sc (oMP+66*j+32),32)])
    (by simp [sc,keptRegs]) (by simp) (by simp)
  refine ⟨hB.step hu cin,?_,?_⟩
  · exact PPostB.trans hab hu (ws := pairSeedWrites j)
      (by simp [sc,keptRegs]) (by simp [pairSeedWrites]) (by simp [pairSeedWrites])
  · rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2,hB.l.st.lay.keepBytes hu ckn,b64,
      pa_sc_add,hu.pa (by simp [keptRegs]),hbn]

end VG.Proof.MlDsa.AArch64.Sign
