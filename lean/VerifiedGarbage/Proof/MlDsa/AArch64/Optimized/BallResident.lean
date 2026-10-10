import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSecondCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChunkTiming
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallInitialTiming
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.ResidentBackend
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BallDispatch

/-! ## From `BallSecondPrefix.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (bytesAt stateAt)

def secondPrefix (c : Impl.Sha3.AArch64.Callee) : Prog isa :=
  .seq (.block (([.str .x .x9 .x25 1800,.str .x .x10 .x25 1808,.str .x .x11 .x25 1816] : List VG.AArch64.Instr) ++ args))
    (.seq (.call ("vg_keccak_squeeze_scratch"++c.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith c)) (.block restore))

structure PrefixPost (P : Sp) (σ : State) (c : Spec.MlDsa.IPoly) (i : Nat) (w : BitVec 64) (Y : List Byte) (s : State) : Prop where
  env : Env P σ s
  ready : ChunkReady P.a (P.at' 840) c i w Y s

theorem secondPrefix_ok (v : Proof.Sha3.AArch64.Permutation) {P : Sp} {σ s : State}
    {i : Nat} {c : Spec.MlDsa.IPoly} {w : BitVec 64} {Y : List Byte}
    (hp : SpOk P σ) (he : Env P σ s) (hparser : Parser P.a c i w s)
    (hY : Y.length=136) (hpos : (s.gpr .x0).toNat≤136)
    (hn : Spec.Sha3.squeezeFrom 136 (stateAt s.mem P.scr) (s.gpr .x0).toNat 136=Y)
    : WP isa (secondPrefix v.callee) s (PrefixPost P σ c i w Y) := by
  unfold secondPrefix
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
  refine WP.mono (restore_ok et₂.x25 sv₂ (fun d hd => inScrRd hp et₂.rd et₂.wr (by
    rcases mem3 hd with rfl | rfl | rfl <;> omega))) fun t₃ ⟨kr,rr⟩ => ?_
  have er := et₂.keep kr.keep kr.mem
  have pr : Parser P.a c i w t₃ := ⟨er.x26,rr.x9.trans hparser.x9,
    by rw [rr.x10,hparser.x10],by rw [rr.x11,hparser.x11],rr.x12,rr.x15,by rw [kr.mem]; exact ct₂⟩
  refine ⟨er,pr,rr.x2,?_,?_,?_,?_⟩
  · rw [hY]; exact rr.x5
  · intro j hj
    rw [kr.mem,← ot₂,MlKem.bytesAt_getD _ _ (by rw [hY] at hj; exact hj)]
  · rw [regions hp er]
    refine Covers.of_sub fun r hr => ?_
    rcases mem2 hr with rfl|rfl
    · exact ⟨P.scrR,by simp,840,rfl,by change 840+Y.length≤2048; rw [hY]; decide⟩
    · exact ⟨polyR P.a,by simp,0,(ptr_zero _).symm,by simp⟩
  · rw [er.wr,hp.wr]
    exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨polyR P.a,by simp,0,(ptr_zero _).symm,by simp⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallSecondChecks.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3

def PrefixTiming (c : Impl.Sha3.AArch64.Callee) : Prop :=
  RelCT isa (VectorTaint.Agree (VectorTaint.ofRegs [.x0,.x25])) (secondPrefix c) (fun _ _ => True)

 theorem sha3_prefixTiming : PrefixTiming callee := by
  have hh : ∃hint, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x25]) (secondPrefix callee) hint).isSome=true := by sponge_taint_decide Sha3Sums
  obtain ⟨hint,hh⟩ := hh
  exact RelCT.taint (A := VectorTaint.taint) _ (fun _ _ h => h) hh
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallSecondTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (stateAt)

structure SecondReady (P : Sp) (σ : State) (c : Spec.MlDsa.IPoly) (i : Nat)
    (w : BitVec 64) (Y : List Byte) (s : State) : Prop where
  env : Env P σ s
  parser : Parser P.a c i w s
  pos : (s.gpr .x0).toNat≤136
  next : Spec.Sha3.squeezeFrom 136 (stateAt s.mem P.scr) (s.gpr .x0).toNat 136=Y

 theorem second_relCT (v : Proof.Sha3.AArch64.Permutation) (hc : PrefixTiming v.callee)
    {P : Sp} {σ₁ σ₂ : State} {τ i : Nat} {h : Array Bool} {c : Spec.MlDsa.IPoly}
    {w : BitVec 64} {Y : List Byte} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂)
    (hi : i≤256) (hY : Y.length=136)
    (hsign : ∀j,i≤j → j<256 → (w >>> (j-i)).getLsbD 0=h.getD (j+τ-256) false) :
    RelCT isa (fun s t => SecondReady P σ₁ c i w Y s ∧ SecondReady P σ₂ c i w Y t ∧
      s.sp=t.sp ∧ s.gpr .x0=t.gpr .x0)
      (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee) (fun _ _ => True) := by
  intro s t ts tt u z ⟨hs,ht,hsp,h0⟩ es et
  cases es with | seq eb es =>
   cases es with | seq ec es =>
    cases es with | seq er el =>
     cases et with | seq fb et =>
      cases et with | seq fc et =>
       cases et with | seq fr fl =>
        have ep := Exec.seq eb (Exec.seq ec er)
        have fp := Exec.seq fb (Exec.seq fc fr)
        have hp := hc _ _ _ _ _ _ (by
          refine ⟨agree_of hsp (fun r hr => ?_),fun r hr => by simp [VectorTaint.ofRegs,RegSet.mem_ofList] at hr⟩
          rcases mem2 hr with rfl|rfl
          · exact h0
          · exact hs.env.x25.trans ht.env.x25.symm) ep fp
        obtain ⟨_,_,eq₁,h₁⟩ := secondPrefix_ok v hp₁ hs.env hs.parser hY hs.pos hs.next
        obtain ⟨_,_,eq₂,h₂⟩ := secondPrefix_ok v hp₂ ht.env ht.parser hY ht.pos ht.next
        obtain ⟨_,rfl⟩ := Exec.det ep eq₁
        obtain ⟨_,rfl⟩ := Exec.det fp eq₂
        have he := chunk_relCT (τ := τ) (h := h) (by rw [hY]; decide) (by rw [hY]; decide) hi
          (by rw [hY]; exact (a_scr' hp₁ (by decide)).symm) hsign _ _ _ _ _ _
          ⟨h₁.ready,h₂.ready,by rw [h₁.env.sp,h₂.env.sp,← hs.env.sp,← ht.env.sp]; exact hsp⟩ el fl
        refine ⟨?_,trivial⟩
        have hh := congr (congrArg (fun xs ys : List Leak => xs ++ ys) hp.1) he.1
        simpa only [List.append_assoc] using hh
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallBranchTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf pub_eq W)

 theorem branch_timing (v : Proof.Sha3.AArch64.Permutation) (hc : PrefixTiming v.callee) :
    RelCT isa (CursorPair Initial)
      (.ite (.zero .x .x11) (.block []) (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee))
      (fun _ _ => True) := by
  refine RelCT.ite (fun s t hh => ?_) ?_ ?_
  · obtain ⟨σ₁,σ₂,_,_,hq,h₁,h₂,_⟩ := hh
    rw [eval_zero,eval_zero,eq_zero_iff,eq_zero_iff,h₁.parser.x11,h₂.parser.x11,tau_eq hq,first_eq hq]
  · exact RelCT.taint (A := taint) (Taint.ofRegs []) (fun s t hh => by
      obtain ⟨⟨σ₁,σ₂,_,_,hq,h₁,h₂,_⟩,_⟩ := hh
      exact agree_of (by rw [h₁.env.sp,h₂.env.sp,hq.2.2.2.2.2.1]) (by simp)) (by taint_decide)
  · intro s t ts tt u z ⟨⟨σ₁,σ₂,p₁,p₂,hq,h₁,h₂,h0⟩,_⟩ es et
    have ht : tauOf σ₁≤64 := by have := (Sample.Ball.params p₁).2.2; omega
    have hg : 256-tauOf σ₁≤(ballFold (tauOf σ₁) (firstBytes σ₁)).2 := by
      simpa only [ballFold,Spec.MlDsa.n] using (bFold_ge (τ := tauOf σ₁) (h := signs (firstBytes σ₁)) (Vector.replicate 256 0,256-tauOf σ₁) ((firstBytes σ₁).drop 8))
    have hs₂ : SpOk (spOf σ₁) σ₂ := by rw [pub_eq hq]; exact Sample.Ball.spOk p₂
    have e₂ : Env (spOf σ₁) σ₂ t := by rw [pub_eq hq]; exact h₂.env
    have pp₂ := h₂.parser
    rw [← pub_eq hq,← tau_eq hq,← first_eq hq] at pp₂
    have nx₂ := h₂.next
    rw [← pub_eq hq,← tail_eq hq] at nx₂
    exact second_relCT v hc (τ := tauOf σ₁) (h := signs (firstBytes σ₁))
      (i := (ballFold (tauOf σ₁) (firstBytes σ₁)).2)
      (c := (ballFold (tauOf σ₁) (firstBytes σ₁)).1)
      (w := W (firstBytes σ₁) >>> ((ballFold (tauOf σ₁) (firstBytes σ₁)).2-(256-tauOf σ₁)))
      (Y := tailBytes σ₁)
      (Sample.Ball.spOk p₁) hs₂ (bFold_le (by simp only [Spec.MlDsa.n]; omega) _)
      (Proof.Sha3.length_squeezeFrom (by decide) (by decide) _ _ _)
      (fun j hj hjn => by
        rw [← BitVec.shiftRight_add]
        rw [show (ballFold (tauOf σ₁) (firstBytes σ₁)).2-(256-tauOf σ₁)+
          (j-(ballFold (tauOf σ₁) (firstBytes σ₁)).2)=j-(256-tauOf σ₁) from by omega]
        exact Sample.Ball.sign_bit (by omega) (by omega) hjn ht)
      s t ts tt u z
      ⟨⟨h₁.env,h₁.parser,h₁.pos,h₁.next⟩,⟨e₂,pp₂,h₂.pos,nx₂⟩,
        by rw [h₁.env.sp,h₂.env.sp,hq.2.2.2.2.2.1],h0⟩ es et

 theorem branch_step (v : Proof.Sha3.AArch64.Permutation) (hc : PrefixTiming v.callee) :
    RelCT isa (CursorPair Initial)
      (.ite (.zero .x .x11) (.block []) (Impl.MlDsa.AArch64.Optimized.Ball.second v.callee))
      (Rel2 sbK.pre sbK.pub Sample.Ball.LP) := by
  intro s t ts tt u z hh es et
  have he := branch_timing v hc _ _ _ _ _ _ hh es et
  obtain ⟨σ₁,σ₂,p₁,p₂,hq,h₁,h₂,_⟩ := hh
  obtain ⟨_,_,e₁,f₁⟩ := branch_ok v p₁ h₁
  obtain ⟨_,_,e₂,f₂⟩ := branch_ok v p₂ h₂
  obtain ⟨_,rfl⟩ := Exec.det es e₁
  obtain ⟨_,rfl⟩ := Exec.det et e₂
  exact ⟨he.1,σ₁,σ₂,p₁,p₂,hq,f₁,f₂⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf pub_eq)

 theorem ctWith (v : Proof.Sha3.AArch64.Permutation) (hs : SpongeCursor v.callee)
    (hp : PrefixTiming v.callee) :
    ConstantTime isa sbK.pre sbK.pub (Impl.MlDsa.AArch64.Optimized.Ball.codeWith v.callee) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono (Q := fun _ _ => True)
    (P := Rel2 sbK.pre sbK.pub fun σ s => s=σ)
    ?_ (fun s₁ s₂ h => ⟨s₁,s₂,h.1,h.2.1,h.2.2,rfl,rfl⟩) fun _ _ _ => trivial)
  refine RelCT.seq (relTaintStep (J' := fun σ => J0 (spOf σ) σ) [.x0,.x1,.x3,.x4]
    (fun σ s hp h => by subst h; exact Sample.Ball.pro_ok hp)
    (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => by
      subst h₁ h₂
      refine ⟨hq.2.2.2.2.2.1,fun r hr => ?_⟩
      rcases mem4 hr with rfl|rfl|rfl|rfl
      exacts [hq.1,hq.2.1,hq.2.2.2.1,hq.2.2.2.2.1]) (by taint_decide)) ?_
  refine RelCT.seq (sponge_step v hs) ?_
  refine RelCT.assoc (RelCT.seq initial_step ?_)
  refine RelCT.seq (branch_step v hp) ?_
  exact relTaint [.x25] (fun σ₁ σ₂ s₁ s₂ _ _ hq h₁ h₂ => ⟨by rw [h₁.env.sp,h₂.env.sp,hq.2.2.2.2.2.1],
    fun r hr => by rw [List.mem_singleton.mp hr,h₁.env.x25,h₂.env.x25,pub_eq hq]⟩) (by taint_decide)

 theorem sha3_ct : ConstantTime isa sbK.pre sbK.pub
    (Impl.MlDsa.AArch64.Optimized.Ball.codeWith Proof.Sha3.AArch64.Sha3.callee) :=
  ctWith Proof.Sha3.AArch64.Sha3.backend sha3_spongeCursor sha3_prefixTiming
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallVerified.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (H)
open VG.Spec.Sha3 (bytesAt)

theorem sampleInBall_verifiedWith (v : Proof.Sha3.AArch64.Permutation) (hc : SpongeCursor v.callee) (ht : PrefixTiming v.callee) : Verified AArch64.target (Impl.MlDsa.AArch64.Optimized.Ball.codeWith v.callee)
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  Verified.of_correct (correctWith v) (ctWith v hc ht)
    { pre := by sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK,
        AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi,
          AArch64.argRegs]
        dsimp only [sbK] at h
        obtain ⟨hr, hp⟩ := h
        by_cases hf : (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256
        · rw [ifT hf] at hr
          obtain ⟨hred, hpoly⟩ := hp hf
          exact ⟨fun _ => hred, .inl ⟨hr, { Spec.MlDsa.minBounds with ball := 272 }, by
            show Option.map _ (Spec.MlDsa.sampleInBall _ 272 _) = _
            rw [sampleInBall_some _ (by decide) hf, hpoly]; rfl⟩⟩
        · rw [ifF hf] at hr
          exact ⟨fun h1 => absurd (hr.symm.trans h1) (by decide),
            .inr ⟨hr, by
              show Option.map _ (Spec.MlDsa.sampleInBall _ Spec.MlDsa.minBounds.ball _) = none
              rw [sampleInBall_none (B := 272) _ (by decide) (by decide) hf]; rfl⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi,
          AArch64.argRegs] at h
        obtain ⟨hsp, hb, hx0, hx1, hx2, hx3, hx4⟩ := h
        exact ⟨hx0, hx1, hx2, hx3, hx4, hsp, VG.Proof.MlKem.map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK,
        AArch64.abi, AArch64.argRegs] [sbSat] using sbSat }

/-- The optimized sampler has the unchanged public SampleInBall contract. -/
theorem sampleInBall_verified : Verified AArch64.target
    (Impl.MlDsa.AArch64.Optimized.Ball.codeWith Proof.Sha3.AArch64.Sha3.callee)
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  sampleInBall_verifiedWith Proof.Sha3.AArch64.Sha3.backend sha3_spongeCursor sha3_prefixTiming
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallResident.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3.ResidentBackend

taint_summary residentFirstSponge : VectorTaint.taint SpongePublic
  (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 136)
  using RSums.absorb RSums.pad RSums.squeeze

theorem resident_spongeCursor : SpongeCursor callee := by
  obtain ⟨hint,τ,hcheck,hpost,_⟩ := residentFirstSponge SpongePublic (by decide)
  have hlo : VectorTaint.taint.le (VectorTaint.ofRegs [.x0]) τ=true :=
    Taint.Mono.le_R (A := VectorTaint.taint) (by decide) hpost
  intro s t ts tt u v hp hs ht
  obtain ⟨he,ha⟩ := Taint.check_sound hcheck hp hs ht
  have hh := VectorTaint.taint.le_sound hlo ha
  exact ⟨he,hh.1.2 .x0 (by decide)⟩

theorem resident_prefixTiming : PrefixTiming callee := by
  have hh : ∃hint,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x25]) (secondPrefix callee) hint).isSome=true := by sponge_taint_decide RSums
  obtain ⟨hint,hh⟩ := hh
  exact RelCT.taint (A := VectorTaint.taint) _ (fun _ _ h => h) hh

theorem resident_verified : Verified AArch64.target
    (Impl.MlDsa.AArch64.Optimized.Ball.codeWith Impl.MlDsa.AArch64.Optimized.Ball.residentCallee)
    (Spec.MlDsa.sampleInBallContract AArch64.abi 16) :=
  sampleInBall_verifiedWith backend resident_spongeCursor resident_prefixTiming
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end
