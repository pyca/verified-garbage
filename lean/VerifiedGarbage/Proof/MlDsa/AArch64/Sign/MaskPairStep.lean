import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskAt

/-! ## From `MaskSeedWords.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlKem.AArch64 (Keep Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem maskSeedHalf_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s)
    {src dst : Nat} (hs : src%8=0) (hsb : src+32≤32768) (hsrc : inB (rbs++wbs) (sc src) 32 = true)
    (hdst : inB wbs (sc dst) 32 = true)
    (hsep : sepB rbs wbs (sc src) 32 (sc dst) 32 = true) :
    WP isa (.block (maskSeedHalf src dst)) s fun t =>
      PPostB S s t [(sc dst,32)] ∧ Keep [.x9,.x10] s t ∧
        bytesAt t.mem (pa s (sc dst)) 32 = bytesAt s.mem (pa s (sc src)) 32 := by
  unfold maskSeedHalf
  refine lea_ok (by decide) _ fun s1 h1 e1 => ?_
  have eD : s1.gpr .x10 = pa s (sc dst) := e1
  have hin : Covers [⟨s.gpr .x28+BitVec.ofNat 64 src,32⟩] (s1.rd++s1.wr) := by
    rw [h1.rd,h1.wr]
    change Covers [⟨pa s (sc src),32⟩] (s.rd++s.wr)
    exact L.cR hsrc
  have hout : Covers [⟨pa s (sc dst)+BitVec.ofNat 64 0,32⟩] s1.wr := by
    rw [h1.wr,VG.Proof.MlKem.AArch64.ptr_zero]
    exact L.cW hdst
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.copy_ok (S := s.gpr .x28)
    (D := pa s (sc dst)) (sb := .x28) (db := .x10) (so := src) (dO := 0) (by decide) (by decide) ⟨hs,hsb⟩ (by decide)
    (by
      rw [VG.Proof.MlKem.AArch64.ptr_zero]
      change (⟨pa s (sc src),32⟩ : Region).Disjoint ⟨pa s (sc dst),32⟩
      exact L.disj hsep)
    (h1.get .x28) eD hin hout) fun t ⟨h2,hf,hb⟩ => ?_
  rw [VG.Proof.MlKem.AArch64.ptr_zero] at hf hb
  have ht : Keep [.x9,.x10] s t := (h1.keep.trans h2).mono (by simp)
  refine ⟨postB_of_keep ht (by decide) ?_,ht,?_⟩
  · rw [← h1.mem]; exact hf
  · rw [hb,h1.mem]

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `MaskSeedNonce.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlKem.AArch64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem maskPairNonce_run (r j : Nat) (hr : r+j < 4096) (hj : j<2) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (pa s (sc oKAP)) 8) (h2 : InRegions s.wr (pa s (sc (oMP+66*j+64))) 1)
    (h3 : InRegions s.wr (pa s (sc (oMP+66*j+65))) 1) :
    WP isa (.block (maskPairNonce r j)) s fun s' =>
      s'.mem = (s.mem.writeW (pa s (sc (oMP+66*j+64)))
        ((s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 (r+j)).setWidth 8)).writeW
        (pa s (sc (oMP+66*j+65))) (((s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 (r+j)) >>> 8).setWidth 8) ∧
        Keep [.x9] s s' := by
  refine wp_ldrx (a := pa s (sc oKAP)) (by decide) rfl h1 fun s₁ h₁ e₁ => wp_addImm hr fun s₂ h₂ e₂ =>
    wp_strb (a := pa s (sc (oMP+66*j+64))) (by dsimp only [oMP]; omega) (by rw [h₂.get .x28, h₁.get .x28]) (by rw [h₂.wr, h₁.wr]; exact h2)
      fun s₃ h₃ => wp_lsr (by decide) fun s₄ h₄ e₄ =>
        wp_strb (a := pa s (sc (oMP+66*j+65))) (by dsimp only [oMP]; omega) (by rw [h₄.get .x28, show s₃.gpr .x28 = s₂.gpr .x28 by
          rw [h₃.gpr], h₂.get .x28, h₁.get .x28]) (by rw [h₄.wr, h₃.wr, h₂.wr, h₁.wr]; exact h3)
          fun s₅ h₅ => wp_nil ⟨?_, ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).mono
            (by simp)⟩
  rw [h₅.mem, e₄, h₄.mem, h₃.mem, show s₃.gpr .x9 = s₂.gpr .x9 by rw [h₃.gpr], e₂, e₁, h₂.mem, h₁.mem]

theorem maskPairNonce_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r j x : Nat} (hj : j<2)
    (hr : r+j < 4096) (hx : x + (r+j) < 2 ^ 16) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : inB wbs (sc (oMP+66*j+64)) 2 = true) (hk : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (maskPairNonce r j)) s fun s' => PPostB D s s' [(sc (oMP+66*j+64), 2)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s (sc (oMP+66*j+64))) 2 = integerToBytes (x + (r+j)) 2 := by
  have e65 : pa s (sc (oMP+66*j+65)) = pa s (sc (oMP+66*j+64)) + 1 := (pa_sc_add s (oMP+66*j+64) 1).symm
  have w2 := L.inW h2
  have c0 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+64))) 1 := by
    have := Offset.contains_base (pa s (sc (oMP+66*j+64))) (d := 0) (n := 1) (k := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMP+66*j+64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (maskPairNonce_run r j hr hj s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨pa s (sc (oMP+66*j+64)), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  refine ⟨postB_of_keep k (by decide) hf, k.get .x24, ?_⟩
  rw [hm, e65, bytes2_write, hk, ofNat64_add, kappa_bytes hx]

theorem maskPairNonce_post {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r j : Nat} (hj : j<2)
    (hr : r+j < 4096) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true) (h2 : inB wbs (sc (oMP+66*j+64)) 2 = true) :
    WP isa (.block (maskPairNonce r j)) s fun s' => ∃ W, PostB D s s' W := by
  have e65 : pa s (sc (oMP+66*j+65)) = pa s (sc (oMP+66*j+64)) + 1 := (pa_sc_add s (oMP+66*j+64) 1).symm
  have w2 := L.inW h2
  have c0 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+64))) 1 := by
    have := Offset.contains_base (pa s (sc (oMP+66*j+64))) (d := 0) (n := 1) (k := 2) (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMP+66*j+64)), 2⟩ : Region).Contains (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact Offset.contains_base _ (d := 1) (by omega) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMP+66*j+64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMP+66*j+65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega) (by decide)
  refine WP.mono (maskPairNonce_run r j hr hj s (L.inR h1) i0 i1) fun s' ⟨hm, k⟩ => ⟨_, (postB_of_keep k (by decide)
    (W := [⟨pa s (sc (oMP+66*j+64)), 2⟩]) ?_)⟩
  rw [hm]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `MaskPairSeed.lean` -/

section

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

end

/-! ## From `MaskPairFinish.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa

def maskFinishChk (p : Params) (n r : Nat) : Bool :=
  let y := pS (yBase p+r)
  let yh := pS (yhBase p+r)
  copyChk (sgR p) (sgW p) yh y 1024 &&
  icmChk p [(yh,1024)] r && famChk (sgR p) (sgW p) [(yh,1024)] (yBase p) n &&
  ipChkS (sgR p) (sgW p) yh && icmChk p [(yh,1024),(sc oPS,1024)] r &&
  famChk (sgR p) (sgW p) [(yh,1024),(sc oPS,1024)] (yBase p) n

/-- Copy and transform one already sampled mask, keeping both canonical
outputs of the paired sampler available for the rejection checks. -/
theorem maskFinish_ok {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {p : Params} {σ s : State} {t n r : Nat} (hr : r<n)
    (hc : maskFinishChk p n r=true) (h : ICm p D σ t r s)
    (hy : Fam s (yBase p) n (Yv p σ (p.ℓ*t))) :
    WP isa (maskFinish P p r) s fun u => ICm p D σ t (r+1) u ∧
      Fam u (yBase p) n (Yv p σ (p.ℓ*t)) := by
  simp only [maskFinishChk,Bool.and_eq_true,and_assoc] at hc
  obtain ⟨cc,c1,fy1,ci,c2,fy2⟩ := hc
  unfold maskFinish
  refine WP.seq (WP.mono (copy_ok h.l.st.lay cc) fun a ⟨ha,_,hb⟩ => ?_)
  have hA := h.step ha c1
  have hya := Fam.keep h.l.st.lay ha fy1 hy
  have hpoly : Pl a (yhBase p+r) (Yv p σ (p.ℓ*t) r) := by
    show PolyIs _ _ _
    rw [ha.pa (pS_bases _)]
    exact polyIs_of_bytes hb (hy r hr)
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt hA.l.st.lay ci hpoly.1)
    fun u ⟨hu,_,hqu⟩ => ?_
  have hU := hA.step hu c2
  have hyu := Fam.keep hA.l.st.lay hu fy2 hya
  refine ⟨⟨hU.l,fun i hi => hyu i (by omega),Fam.snoc hU.yh ?_⟩,hyu⟩
  show PolyIs _ _ _
  rw [hu.pa (pS_bases _),hpoly.2] at *
  exact hqu

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `MaskPairStep.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def maskPairStepChk (p : Params) (r : Nat) : Bool :=
  pairSeedChk p r 0 && pairSeedChk p r 1 &&
  keepB (sgR p) (sgW p) (pairSeedWrites 1) (sc oMP) 66 &&
  maskPairChk (sgR p) (sgW p) (sc oMP) (yP p r) (yP p (r+1)) (sc (oR4 p)) &&
  icmChk p [(yP p r,1024),(yP p (r+1),1024),(sc (oR4 p),8192)] r &&
  maskFinishChk p (r+2) r && maskFinishChk p (r+2) (r+1) &&
  decide (p.γ₁=2^17 ∨ p.γ₁=2^19)

/-- Paired expansion advances the same canonical and transformed mask
invariants by two, with the original per-polynomial seeds. -/
theorem maskPairR_ok {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {nm : String} {cd : Prog isa} (C : CalleeOk D cd (expandMaskPairContract AArch64.abi D))
    {p : Params} {σ s : State} {t r : Nat} (hc : maskPairStepChk p r=true)
    (h : ICm p D σ t r s) :
    WP isa (maskPairR P p nm cd r) s (ICm p D σ t (r+2)) := by
  simp only [maskPairStepChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cs0,cs1,ck,cm,ci,cf0,cf1,hg⟩ := hc
  unfold maskPairR
  refine WP.seq (WP.mono (maskPairSeed_ok cs0 h) fun a ⟨hA,_,ha⟩ => ?_)
  refine WP.seq (WP.mono (maskPairSeed_ok cs1 hA) fun b ⟨hB,hb,hseed1⟩ => ?_)
  have hseed0 : bytesAt b.mem (pa b (sc oMP)) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+r) 2 := by
    have hkeep := hA.l.st.lay.keepBytes hb ck
    simp only [Nat.mul_zero,Nat.add_zero] at ha
    rw [hkeep]
    exact ha
  have hseed1' : bytesAt b.mem (pa b (sc oMP)+66) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+(r+1)) 2 := by
    change bytesAt b.mem (pa b (sc (oMP+66))) 66=_ at hseed1
    rw [← pa_sc_add] at hseed1
    exact hseed1
  refine WP.seq (WP.mono (maskPairAt_ok hB.l.st.lay.s64 C hB.l.st.lay cm hg)
    fun c ⟨hcP,_,hy0,hy1⟩ => ?_)
  rw [hseed0] at hy0
  rw [hseed1'] at hy1
  have hC := hB.step hcP ci
  have hy : Fam c (yBase p) (r+2) (Yv p σ (p.ℓ*t)) := by
    refine Fam.snoc (Fam.snoc hC.y ?_) ?_
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy0
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy1
  refine WP.seq (WP.mono (maskFinish_ok hP (by omega) cf0 hC hy) fun d ⟨hD,hyD⟩ => ?_)
  exact WP.mono (maskFinish_ok hP (by omega) cf1 hD hyD) fun _ hu => hu.1

end VG.Proof.MlDsa.AArch64.Sign

end
