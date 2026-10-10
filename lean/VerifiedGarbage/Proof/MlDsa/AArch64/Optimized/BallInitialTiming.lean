import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.Ball
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallFirst
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallChunkTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallInitial

/-! ## From `BallChecks.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Sha3

taint_summary firstSponge : VectorTaint.taint (VectorTaint.ofRegs [.x25,.x26,.x27,.x3,.x4])
  (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 136)
  using Sha3Sums.absorb Sha3Sums.pad Sha3Sums.squeeze

end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallFirstTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample

structure FirstReady (a b : Addr) (τ : Nat) (X : List Byte) (s : State) : Prop where
  x25 : s.gpr .x25+840=b
  x26 : s.gpr .x26=a
  x27 : (s.gpr .x27).toNat=τ
  buf : ∀j<136,s.mem (b+BitVec.ofNat 64 j)=X.getD j 0
  zero : ∀j<256,Spec.MlDsa.coeffAt s.mem a j=0
  reads : Covers [⟨b,136⟩,polyR a] (s.rd++s.wr)
  writes : Covers [polyR a] s.wr

 theorem first_relCT {a b : Addr} {τ : Nat} {X : List Byte} (hX : X.length=136) (hτ : τ≤64)
    (hsep : (⟨b,136⟩ : Region).Disjoint (polyR a)) :
    RelCT isa (fun s t => FirstReady a b τ X s ∧ FirstReady a b τ X t ∧ s.sp=t.sp)
      Impl.MlDsa.AArch64.Optimized.Ball.first (fun _ _ => True) := by
  let rd : List Region := [⟨b,136⟩]
  let wr : List Region := [polyR a]
  have run (s : State) (hs : FirstReady a b τ X s) :
      ∃tr u,Exec isa Impl.MlDsa.AArch64.Optimized.Ball.first (s.withRegions rd wr) tr u := by
    obtain ⟨tr,u,he,_⟩ := first_ok (τ := τ) (s := s.withRegions rd wr) hX hs.x25 hs.x26 hs.x27 hτ
      (in_rd (in_regions (List.mem_singleton_self _) (by simp [Region.Contains])))
      (fun j hj => in_rd (in_regions (List.mem_singleton_self _) (Offset.contains_base _ (by omega) (by omega))))
      hs.buf (fun j hj => in_regions (List.mem_singleton_self _) (coeff_contains _ hj)) hsep hs.zero
    exact ⟨tr,u,he⟩
  refine RelCT.narrow rd wr
    (fun s t ht => ⟨⟨ht.1.reads,ht.1.writes⟩,⟨ht.2.1.reads,ht.2.1.writes⟩⟩)
    (fun s t ht => ⟨run s ht.1,run t ht.2.1⟩)
    (RelCT.taint (A := memTaint) (Taint.ofRegs [.x25,.x26,.x27]) ?_ (by taint_decide))
  intro s t hp
  obtain ⟨s₀,t₀,⟨hs,ht,hsp⟩,rfl,rfl⟩ := hp
  refine ⟨agree_of hsp (fun r hr => ?_),rfl,rfl,fun x hx => ?_⟩
  · rcases mem3 hr with rfl|rfl|rfl
    · change s₀.gpr .x25=t₀.gpr .x25
      have hh := congrArg (fun z : BitVec 64 => z-840) (hs.x25.trans ht.x25.symm)
      simpa only [BitVec.add_sub_cancel] using hh
    · exact hs.x26.trans ht.x26.symm
    · exact BitVec.eq_of_toNat_eq (hs.x27.trans ht.x27.symm)
  · obtain ⟨r,hr,hx⟩ := hx
    rcases mem2 hr with rfl|rfl
    · obtain ⟨j,hj,rfl⟩ := Proof.MlKem.AArch64.Sample.at_off hx
      exact (hs.buf j hj).trans (ht.buf j hj).symm
    · exact (Proof.MlKem.AArch64.Sample.byte_zero hs.zero hx).trans
        (Proof.MlKem.AArch64.Sample.byte_zero ht.zero hx).symm
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallCursor.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64

abbrev SpongePublic : VectorTaint.T := VectorTaint.ofRegs [.x25,.x26,.x27,.x3,.x4]

/-- The public cursor returned by the first block is retained for a possible
second squeeze. This is a relational fact proved by the existing taint checker. -/
def SpongeCursor (c : Impl.Sha3.AArch64.Callee) : Prop :=
  RelCT isa (VectorTaint.Agree SpongePublic) (Impl.MlDsa.AArch64.Sample.spongeWith c 136 136)
    (fun s t => s.gpr .x0=t.gpr .x0)

 theorem sha3_spongeCursor : SpongeCursor Proof.Sha3.AArch64.Sha3.callee := by
  obtain ⟨hint,τ,hcheck,hpost,_⟩ := firstSponge SpongePublic (by decide)
  have hlo : VectorTaint.taint.le (VectorTaint.ofRegs [.x0]) τ=true :=
    Taint.Mono.le_R (A := VectorTaint.taint) (by decide) hpost
  intro s t ts tt u v hp hs ht
  obtain ⟨he,ha⟩ := Taint.check_sound hcheck hp hs ht
  have hh := VectorTaint.taint.le_sound hlo ha
  exact ⟨he,hh.1.2 .x0 (by decide)⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallZeroReady.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf)

theorem zero_ready {σ s : State} (hp : sbK.pre σ) (h : Resume 136 136 (spOf σ) σ s) :
    WP isa Impl.MlDsa.AArch64.Optimized.Ball.zeroWide s fun u =>
      Keep [] s u ∧ FirstReady (spOf σ).a ((spOf σ).at' 840) (tauOf σ) (firstBytes σ) u := by
  have ps := Sample.Ball.spOk hp
  refine WP.mono (zeroWide_coeffs h.first.env.x26 (fun i hi => ?_)) fun t ⟨kt,ft,hz⟩ => ?_
  · rw [h.first.env.wr,ps.wr]
    exact in_regions (List.mem_cons_self ..) (Offset.contains_base _ (by omega) (by omega))
  have et := h.first.env.keepA ps kt ft
  have ot : bytesAt t.mem ((spOf σ).at' 840) 136=firstBytes σ := by
    rw [MlKem.bytesAt_frame ft (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (a_scr' ps (by decide)).symm) (by decide),h.first.out]
    exact (H_eq _ _).symm
  refine ⟨kt,by rw [et.x25]; rfl,et.x26,?_,?_,hz,?_,?_⟩
  · rw [et.x27]; simp [tauOf]; omega
  · intro j hj
    rw [← ot,MlKem.bytesAt_getD _ _ hj]
  · rw [regions ps et]
    refine Covers.of_sub fun r hr => ?_
    rcases mem2 hr with rfl|rfl
    · exact ⟨(spOf σ).scrR,by simp,840,rfl,by simp⟩
    · exact ⟨polyR (spOf σ).a,by simp,0,(ptr_zero _).symm,by simp⟩
  · rw [et.wr,ps.wr]
    exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨polyR (spOf σ).a,by simp,0,(ptr_zero _).symm,by simp⟩
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end

/-! ## From `BallInitialTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (spOf pub_eq)

def CursorPair (J : State → State → Prop) (s t : State) : Prop :=
  ∃σ₁ σ₂,sbK.pre σ₁ ∧ sbK.pre σ₂ ∧ sbK.pub σ₁ σ₂ ∧ J σ₁ s ∧ J σ₂ t ∧ s.gpr .x0=t.gpr .x0

 theorem tau_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : tauOf σ₁=tauOf σ₂ := congrArg BitVec.toNat hq.2.2.1
 theorem first_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : firstBytes σ₁=firstBytes σ₂ := by
  simp only [firstBytes,Sp.msg]
  rw [hq.2.2.2.2.2.2]
 theorem tail_eq {σ₁ σ₂ : State} (hq : sbK.pub σ₁ σ₂) : tailBytes σ₁=tailBytes σ₂ := by
  simp only [tailBytes,Sp.msg]
  rw [hq.2.2.2.2.2.2]

 theorem sponge_step (v : Proof.Sha3.AArch64.Permutation) (hc : SpongeCursor v.callee) :
    RelCT isa (Rel2 sbK.pre sbK.pub (fun σ => J0 (spOf σ) σ))
      (Impl.MlDsa.AArch64.Sample.spongeWith v.callee 136 136)
      (CursorPair fun σ => Resume 136 136 (spOf σ) σ) := by
  intro s t ts tt u z ⟨σ₁,σ₂,p₁,p₂,hq,h₁,h₂⟩ es et
  have hh := hc _ _ _ _ _ _ (by
    refine ⟨agree_of (by rw [h₁.env.sp,h₂.env.sp,hq.2.2.2.2.2.1]) (fun r hr => ?_),fun r hr => by simp [SpongePublic,VectorTaint.ofRegs,RegSet.mem_ofList] at hr⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · rw [h₁.env.x25,h₂.env.x25,pub_eq hq]
    · rw [h₁.env.x26,h₂.env.x26,pub_eq hq]
    · rw [h₁.env.x27,h₂.env.x27,pub_eq hq]
    · rw [h₁.x3,h₂.x3,pub_eq hq]
    · exact toNat_inj h₁.x4 (by rw [h₂.x4,pub_eq hq])) es et
  obtain ⟨_,_,e₁,f₁⟩ := spongeResume_ok (Sample.Ball.spOk p₁) v (rate := 136) (outlen := 136) (by decide) (by decide) h₁
  obtain ⟨_,_,e₂,f₂⟩ := spongeResume_ok (Sample.Ball.spOk p₂) v (rate := 136) (outlen := 136) (by decide) (by decide) h₂
  obtain ⟨_,rfl⟩ := Exec.det es e₁
  obtain ⟨_,rfl⟩ := Exec.det et e₂
  exact ⟨hh.1,σ₁,σ₂,p₁,p₂,hq,f₁,f₂,hh.2⟩

 theorem initial_step :
    RelCT isa (CursorPair fun σ => Resume 136 136 (spOf σ) σ)
      (.seq Impl.MlDsa.AArch64.Optimized.Ball.zeroWide Impl.MlDsa.AArch64.Optimized.Ball.first)
      (CursorPair Initial) := by
  intro s t ts tt u z ⟨σ₁,σ₂,p₁,p₂,hq,h₁,h₂,h0⟩ es et
  have hsp : s.sp=t.sp := by rw [h₁.first.env.sp,h₂.first.env.sp,hq.2.2.2.2.2.1]
  have full₁ := initial_full_ok p₁ h₁
  have full₂ := initial_full_ok p₂ h₂
  obtain ⟨_,_,e₁,f₁⟩ := full₁
  obtain ⟨_,_,e₂,f₂⟩ := full₂
  obtain ⟨_,rfl⟩ := Exec.det es e₁
  obtain ⟨_,rfl⟩ := Exec.det et e₂
  refine ⟨?_,σ₁,σ₂,p₁,p₂,hq,f₁.1,f₂.1,by rw [f₁.2,f₂.2,h0]⟩
  cases es with | seq ez₁ ef₁ =>
   cases et with | seq ez₂ ef₂ =>
    have hz := RelCT.taint (A := VectorTaint.taint) (VectorTaint.ofRegs [.x26])
      (P := fun a b => a.sp=b.sp ∧ a.gpr .x26=b.gpr .x26)
      (fun _ _ hh => ⟨agree_of hh.1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hh.2),fun r hr => by simp [VectorTaint.ofRegs,RegSet.mem_ofList] at hr⟩)
      (c := Impl.MlDsa.AArch64.Optimized.Ball.zeroWide) (by taint_decide)
      _ _ _ _ _ _ ⟨hsp,by rw [h₁.first.env.x26,h₂.first.env.x26,pub_eq hq]⟩ ez₁ ez₂
    obtain ⟨_,_,ze₁,k₁,r₁⟩ := zero_ready p₁ h₁
    obtain ⟨_,_,ze₂,k₂,r₂⟩ := zero_ready p₂ h₂
    obtain ⟨_,rfl⟩ := Exec.det ez₁ ze₁
    obtain ⟨_,rfl⟩ := Exec.det ez₂ ze₂
    have rr₂ := r₂
    rw [← pub_eq hq,← tau_eq hq,← first_eq hq] at rr₂
    have hf := first_relCT (H_length _ _) (by have := (Sample.Ball.params p₁).2.2; omega)
      (a_scr' (Sample.Ball.spOk p₁) (by decide)).symm _ _ _ _ _ _
      ⟨r₁,rr₂,by rw [k₁.sp,k₂.sp]; exact hsp⟩ ef₁ ef₂
    exact congr (congrArg (fun xs ys : List Leak => xs ++ ys) hz.1) hf.1
end VG.Proof.MlDsa.AArch64.Optimized.Ball

end
