import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.BallLoop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSecondCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallLoop
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallInitial

/-! ## From `BallMath.lean` -/

section

/-! Splitting the sampler byte stream does not change its deterministic fold. -/
namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.Spec.MlDsa VG.Proof.MlDsa.Sample
open VG.Proof.Sha3 (length_squeezeFrom squeezeFrom_getElem)

theorem signs_append {X : List Byte} (hX : 8≤X.length) (Y : List Byte) :
    signs (X++Y)=signs X := by
  simp only [signs,List.take_append_of_le_length hX]

theorem fold_append_bytes (τ : Nat) {X : List Byte} (hX : 8≤X.length) (Y : List Byte) :
    ballFold τ (X++Y)=bFold τ (signs X) (ballFold τ X) Y := by
  simp only [ballFold,signs_append hX,List.drop_append_of_le_length hX,bFold_append]

theorem fold_append_done {τ : Nat} {X : List Byte} (hX : 8≤X.length)
    (hf : (ballFold τ X).2=256) (Y : List Byte) : ballFold τ (X++Y)=ballFold τ X := by
  rw [fold_append_bytes τ hX,bFold_full hf]

/-- The second call resumes exactly the suffix of the272-byte SHAKE stream. -/
theorem squeeze_split (S : Spec.Sha3.State) :
    Spec.Sha3.squeezeFrom 136 S 0 272 =
      Spec.Sha3.squeezeFrom 136 S 0 136 ++ Spec.Sha3.squeezeFrom 136 S 136 136 := by
  apply List.ext_getElem
  · simp only [List.length_append,length_squeezeFrom (rate := 136) (by decide) (by decide)]
  · intro i hi hi'
    rw [squeezeFrom_getElem (by decide) (by decide) S (by
      rw [length_squeezeFrom (rate := 136) (by decide) (by decide)] at hi; exact hi)]
    by_cases h : i<136
    · rw [List.getElem_append_left (by rw [length_squeezeFrom (rate := 136) (by decide) (by decide)]; exact h),
        squeezeFrom_getElem (by decide) (by decide) S h]
    · rw [List.getElem_append_right (by rw [length_squeezeFrom (rate := 136) (by decide) (by decide)]; omega)]
      simp only [length_squeezeFrom (rate := 136) (by decide) (by decide)]
      rw [squeezeFrom_getElem (by decide) (by decide) S (by
          rw [length_squeezeFrom (rate := 136) (by decide) (by decide)] at hi; omega)]
      rw [show 136+(i-136)=0+i from by omega]
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallSecond.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (bytesAt stateAt)

structure SecondPost (P : Sp) (σ : State) (τ : Nat) (h : Array Bool) (c : Spec.MlDsa.IPoly)
    (i : Nat) (w : BitVec 64) (Y : List Byte) (s : State) : Prop where
  env : Env P σ s
  parser : Parser P.a (bFold τ h (c,i) Y).1 (bFold τ h (c,i) Y).2
    (w >>> ((bFold τ h (c,i) Y).2-i)) s

theorem second_ok (v : Proof.Sha3.AArch64.Permutation) {P : Sp} {σ s : State}
    {τ i : Nat} {h : Array Bool} {c : Spec.MlDsa.IPoly} {w : BitVec 64} {Y : List Byte}
    (hp : SpOk P σ) (he : Env P σ s) (hparser : Parser P.a c i w s) (hi : i≤256)
    (hY : Y.length=136) (hpos : (s.gpr .x0).toNat≤136)
    (hn : Spec.Sha3.squeezeFrom 136 (stateAt s.mem P.scr) (s.gpr .x0).toNat 136=Y)
    (hsign : ∀ j,i≤j → j<256 → (w >>> (j-i)).getLsbD 0=h.getD (j+τ-256) false) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee) s (SecondPost P σ τ h c i w Y) := by
  unfold Impl.MlDsa.AArch64.Optimized.Ball.second
  refine WP.seq (WP.block_append (M := isa) (l₁ := ([.str .x .x9 .x25 1800,.str .x .x10 .x25 1808,.str .x .x11 .x25 1816] : List VG.AArch64.Instr))
    (l₂ := args) (WP.mono (save_ok (s := s) (p := P.scr) he.x25 (fun d hd => inScr hp he.wr (by
      rcases mem3 hd with rfl | rfl | rfl <;> omega))) fun t ⟨kt,ft,sv⟩ => ?_))
  have et := env_saved hp he kt ft
  have ct : VG.Proof.MlDsa.AArch64.Sample.Ball.CStored t.mem P.a c := stored_frame hparser.stored ft (by
    intro r hr; rcases mem3 hr with rfl|rfl|rfl <;> exact a_scr' hp (by decide))
  have st : stateAt t.mem P.scr=stateAt s.mem P.scr := state_frame ft (by
    intro r hr
    have sep (d : Nat) (hd : 200≤d) (hd2 : d+8≤2048) :
        Region.Disjoint ⟨P.scr,200⟩ ⟨P.at' d,8⟩ := by
      simpa only [at_zero] using (disj_scr (P := P) (a := 0) (n := 200) (b := d) (m := 8) (.inl hd) (by decide) hd2)
    rcases mem3 hr with rfl|rfl|rfl <;> exact sep _ (by decide) (by decide))
  refine WP.mono (args_ok et.x25) fun u ⟨ku,ua⟩ => ?_
  have eu := et.keep ku.keep ku.mem
  refine WP.seq (WP.mono (resume_call_ok v (c := c) (Y := Y) (w9 := s.gpr .x9) (w10 := s.gpr .x10) (w11 := s.gpr .x11) hp eu ua
    (by rw [kt.get .x0]; exact hpos)
    (by rw [ku.mem,st,kt.get .x0]; exact hn)
    (by exact ⟨by rw [ku.mem]; exact sv.r9,by rw [ku.mem]; exact sv.r10,by rw [ku.mem]; exact sv.r11⟩) (by simpa only [ku.mem] using ct)) fun t₂ ⟨et₂,sv₂,ct₂,ot₂⟩ => ?_)
  refine WP.seq (WP.mono (restore_ok et₂.x25 sv₂ (fun d hd => inScrRd hp et₂.rd et₂.wr (by
    rcases mem3 hd with rfl | rfl | rfl <;> omega))) fun t₃ ⟨kr,rr⟩ => ?_)
  have er := et₂.keep kr.keep kr.mem
  have pr : Parser P.a c i w t₃ := ⟨er.x26,rr.x9.trans hparser.x9,
    by rw [rr.x10,hparser.x10],by rw [rr.x11,hparser.x11],rr.x12,rr.x15,by rw [kr.mem]; exact ct₂⟩
  refine WP.mono (chunk_ok (τ := τ) (h := h) (L := Y) (b := P.at' 840)
    (by rw [hY]; decide) (by rw [hY]; decide) hi pr rr.x2 (by rw [hY]; exact rr.x5)
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj => inA hp er.wr hj)
    (by rw [hY]; exact (a_scr' hp (by decide)).symm) hsign) fun z hz => ?_
  · rw [kr.mem,← ot₂,MlKem.bytesAt_getD _ _ (by rw [hY] at hj; exact hj)]
  · rw [at_add]; exact inScrRd hp er.rd er.wr (by rw [hY] at hj; omega)
  · refine ⟨er.keepA hp hz.keep hz.frame,?_⟩
    simpa only [Fold,List.take_length] using hz.parser
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallCorrect.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf W)

 theorem whole_bytes (σ : State) : Sample.Ball.X σ=firstBytes σ++tailBytes σ := by
  change Spec.MlDsa.H _ 272=Spec.MlDsa.H _ 136++_
  rw [H_eq,H_eq]
  exact squeeze_split _

 theorem branch_ok (v : Proof.Sha3.AArch64.Permutation) {σ s : State}
    (hp : sbK.pre σ) (h : Initial σ s) :
    WP isa (.ite (.zero .x .x11) (.block []) (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee))
      s (Sample.Ball.LP σ) := by
  have ht : tauOf σ≤64 := by have := (Sample.Ball.params hp).2.2; omega
  have hl : (firstBytes σ).length=136 := H_length _ _
  have hi : (ballFold (tauOf σ) (firstBytes σ)).2≤256 := bFold_le (by simp only [Spec.MlDsa.n]; omega) _
  have hg : 256-tauOf σ≤(ballFold (tauOf σ) (firstBytes σ)).2 := by
    simpa only [ballFold,Spec.MlDsa.n] using (bFold_ge (τ := tauOf σ) (h := signs (firstBytes σ)) (Vector.replicate 256 0,256-tauOf σ) ((firstBytes σ).drop 8))
  by_cases hd : (ballFold (tauOf σ) (firstBytes σ)).2=256
  · refine WP.ite true (by rw [eval_zero,eq_zero_iff,h.parser.x11,hd]; rfl) (fun _ => wp_nil ?_) (fun hh => nomatch hh)
    have heq : ballFold (tauOf σ) (Sample.Ball.X σ)=ballFold (tauOf σ) (firstBytes σ) := by
      rw [whole_bytes]; exact fold_append_done (by rw [hl]; decide) hd _
    refine ⟨h.env,?_,?_⟩
    · rw [heq]; exact h.parser.x10
    · rw [heq]; exact h.parser.stored
  · refine WP.ite (M := isa) false (by rw [eval_zero,eq_zero_iff,h.parser.x11]; simp only [decide_eq_false_iff_not, Option.some.injEq]; omega) (fun hh => nomatch hh) (fun _ => ?_)
    refine WP.mono (second_ok v (τ := tauOf σ) (h := signs (firstBytes σ)) (Sample.Ball.spOk hp) h.env h.parser hi
      (Proof.Sha3.length_squeezeFrom (by decide) (by decide) _ _ _)
      h.pos h.next (fun j hj hjn => ?_)) fun u hu => ?_
    · rw [← BitVec.shiftRight_add]
      rw [show (ballFold (tauOf σ) (firstBytes σ)).2-(256-tauOf σ)+
        (j-(ballFold (tauOf σ) (firstBytes σ)).2)=j-(256-tauOf σ) from by omega]
      exact Sample.Ball.sign_bit (by omega) (by omega) hjn ht
    · have heq : ballFold (tauOf σ) (Sample.Ball.X σ)=
          bFold (tauOf σ) (signs (firstBytes σ)) (ballFold (tauOf σ) (firstBytes σ)) (tailBytes σ) := by
        rw [whole_bytes,fold_append_bytes _ (by rw [hl]; decide)]
      exact ⟨hu.env,heq.symm ▸ hu.parser.x10,heq.symm ▸ hu.parser.stored⟩

 theorem correctWith (v : Proof.Sha3.AArch64.Permutation) (σ : State) (hp : sbK.pre σ) :
    WP isa (Impl.MlDsa.AArch64.Optimized.Ball.codeWith v.callee) σ
      (fun u => abiPreserved σ u ∧ sbK.post σ u) := by
  refine WP.seq (WP.mono (Sample.Ball.pro_ok hp) fun _ h0 =>
    WP.seq (WP.mono (spongeResume_ok (Sample.Ball.spOk hp) v (rate := 136) (outlen := 136)
      (by decide) (by decide) h0) fun s h1 => ?_))
  have hc := WP.mono (initial_ok hp h1) fun t ht =>
    WP.seq (WP.mono (branch_ok v hp ht) fun u hu => Sample.Ball.end_ok hp hu)
  exact WP.assoc (WP.seq hc)
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end
