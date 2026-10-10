import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretSeeds
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp

/-! ## From `OptimizedSecretCall.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.Optimized

theorem boundedReady {S : Nat} {p : Params} (hF : PFacts p) {s : State}
    (L : Lay S kgR (kgW p) s) {r : Nat} (hr : r+4≤p.ℓ+p.k+1) :
    BoundedFour.CallReady (sc 1408) (sP p r) (sc (oR4 p)) s := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hs : inB (kgR++kgW p) (sc 1408) 264=true := by layd
  have ho : inB (kgR++kgW p) (sP p r) 4096=true := by layd
  have hw : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by layd
  have hwo : inB (kgW p) (sP p r) 4096=true := by layd
  have hww : inB (kgW p) (sc (oR4 p)) 8192=true := by layd
  have hso : sepB kgR (kgW p) (sc 1408) 264 (sP p r) 4096=true := by layd
  have hsw : sepB kgR (kgW p) (sc 1408) 264 (sc (oR4 p)) 8192=true := by layd
  have how : sepB kgR (kgW p) (sP p r) 4096 (sc (oR4 p)) 8192=true := by layd
  exact ⟨L.nwp hs,L.nwp ho,L.nwp hw,L.disj hso,L.disj hsw,L.disj how,
    Covers.cons (L.cR hs) (Covers.cons (L.cR ho) (L.cR hw)),Covers.cons (L.cW hwo) (L.cW hww)⟩

theorem boundedAt_layout {S : Nat} {p : Params} (hF : PFacts p) {s : State}
    (L : Lay S kgR (kgW p) s) {r : Nat} (hr : r+4≤p.ℓ+p.k+1)
    (c : Impl.Sha3.AArch64.Callee) :
    WP isa (callAt (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.boundedFourSymbol c p.η)
      (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler c.pairedSha3 true p.η)
      (BoundedFour.samplerArgs (sc 1408) (sP p r) (sc (oR4 p)))) s fun t=>
      PPostB S s t [(sP p r,4096),(sc (oR4 p),8192)] ∧ t.gpr .x24=s.gpr .x24 ∧
      (∀i<4,Reduced t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) ∧
      (∀i<4,BoundedOutput p.η t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) ∧
      Outcome (fun b=>(rejBoundedFour p.η b.rejBounded s.mem (pa s (sc 1408))).map (List.map toRq))
        ((t.gpr .x0).setWidth 32)
        ((List.range 4).map fun i=>polyAt t.mem (pa s (sP p r)+BitVec.ofNat 64 (1024*i))) := by
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hs : inB (kgR++kgW p) (sc 1408) 264=true := by layd
  have ho : inB (kgR++kgW p) (sP p r) 4096=true := by layd
  have hw : inB (kgR++kgW p) (sc (oR4 p)) 8192=true := by layd
  have hη : p.η=2∨p.η=4 := by rcases hF.eta with h|h; exact Or.inl h.1; exact Or.inr h.1
  refine WP.mono (BoundedFour.samplerAt_ok L.s64 c.pairedSha3 hη
    (ptr_ok (L.ptrBs hs)) (ptr_ok (L.ptrBs ho)) (ptr_ok (L.ptrBs hw)) (boundedReady hF L hr))
    fun t ⟨hp,hred,hsmall,hout⟩=>?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hred,hsmall,hout⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedSecretMath.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.Spec.MlDsa

theorem mapM_some_map_iff {α β : Type} (f : α→Option β) (g : α→β) :
    ∀l : List α,l.mapM f=some (l.map g) ↔ ∀x∈l,f x=some (g x)
  | [] => by simp
  | x::xs => by
    rw [List.mapM_cons,List.map_cons]
    cases hx : f x with
    | none => simp [hx]
    | some y =>
      simp only [Option.bind_eq_bind,Option.bind_some]
      cases ht : xs.mapM f with
      | none =>
        change (none : Option (List β))=some _ ↔ _
        simp only [reduceCtorEq,false_iff]
        intro h
        have he := (mapM_some_map_iff f g xs).mpr (fun z hz=>h z (by simp [hz]))
        rw [ht] at he
        cases he
      | some ys =>
        change some (y::ys)=some (g x::xs.map g) ↔ _
        rw [Option.some.injEq,List.cons.injEq]
        constructor
        · rintro ⟨hy,he⟩ z hz
          subst y
          rcases List.mem_cons.mp hz with rfl|hz
          · exact hx
          · exact (mapM_some_map_iff f g xs).mp (ht.trans (congrArg some he)) z hz
        · intro h
          have hy := h x (by simp)
          rw [hx] at hy
          have ht' := (mapM_some_map_iff f g xs).mpr (fun z hz=>h z (by simp [hz]))
          exact ⟨Option.some.inj hy,Option.some.inj (ht.symm.trans ht')⟩

theorem mapM_map_result {α β γ : Type} (f : α→Option β) (g : β→γ) (l : List α) :
    (l.mapM f).map (List.map g)=l.mapM (fun x=>(f x).map g) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.mapM_cons,List.mapM_cons]
    cases f x <;> simp only [Option.bind_eq_bind,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some]
    case some a =>
      rw [←ih]
      cases l.mapM f <;> rfl

theorem mapM_none_iff {α β : Type} (f : α→Option β) :
    ∀l : List α,l.mapM f=none ↔ ∃x∈l,f x=none
  | [] => by simp
  | x::xs => by
    rw [List.mapM_cons]
    cases hx : f x with
    | none => simp [hx]
    | some y =>
      simp only [Option.bind_eq_bind,Option.bind_some]
      cases ht : xs.mapM f with
      | none =>
        constructor
        · intro _
          obtain ⟨z,hz,he⟩:=(mapM_none_iff f xs).mp ht
          exact ⟨z,by simp [hz],he⟩
        · intro _; rfl
      | some ys =>
        change some (y::ys)=none ↔ _
        simp only [reduceCtorEq,false_iff]
        rintro ⟨z,hz,he⟩
        rcases List.mem_cons.mp hz with rfl|hz
        · rw [hx] at he; cases he
        · have hn:=(mapM_none_iff f xs).mpr ⟨z,hz,he⟩
          rw [ht] at hn; cases hn

theorem boundedFour_some_iff (η B : Nat) (m : Mem) (seed : Addr) (f : Nat→Poly) :
    (rejBoundedFour η B m seed).map (List.map toRq)=some ((List.range 4).map f) ↔
      ∀i<4,(rejBoundedPoly η B (Spec.Sha3.bytesAt m (seed+BitVec.ofNat 64 (66*i)) 66)).map toRq=
        some (f i) := by
  unfold rejBoundedFour
  rw [mapM_map_result,mapM_some_map_iff]
  simp only [List.mem_range]

theorem boundedFour_none_iff (η B : Nat) (m : Mem) (seed : Addr) :
    (rejBoundedFour η B m seed).map (List.map toRq)=none ↔
      ∃i<4,rejBoundedPoly η B (Spec.Sha3.bytesAt m (seed+BitVec.ofNat 64 (66*i)) 66)=none := by
  rw [Option.map_eq_none_iff]
  unfold rejBoundedFour
  rw [mapM_none_iff]
  simp only [List.mem_range]

/-- Ignoring a duplicated fourth lane retains exactly the three requested
samplers, including their failure result. -/
theorem mapM_duplicate_tail {α : Type} (a b c : Option α) :
    (([a,b,c,a].mapM id).map (List.take 3))=[a,b,c].mapM id := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mapM_duplicate_none {α : Type} (a b c : Option α) :
    [a,b,c,a].mapM id=none ↔ [a,b,c].mapM id=none := by
  cases a <;> cases b <;> cases c <;> simp

/-- Duplicating a stream cannot introduce a failure or make failure depend on
an additional secret stream. The successful output keeps the first three. -/
theorem outcome_duplicate_tail {α : Type} {f g h : Bounds→Option α} {r : BitVec 32} {out : List α}
    (ho : Outcome (fun B=>[f B,g B,h B,f B].mapM id) r out) :
    Outcome (fun B=>[f B,g B,h B].mapM id) r (out.take 3) := by
  rcases ho with ⟨hr,B,hB⟩|⟨hr,hB⟩
  · refine Or.inl ⟨hr,B,?_⟩
    dsimp only at hB ⊢
    rw [←mapM_duplicate_tail,hB]
    rfl
  · exact Or.inr ⟨hr,(mapM_duplicate_none _ _ _).mp hB⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedSecretGood.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.KeyGen (Small seedS bmax)

theorem small_toRq_inj {η : Nat} (hη : η≤4) {a b : IPoly}
    (ha : Small η a) (hb : Small η b) (he : toRq a=toRq b) : a=b := by
  have ea:=VG.Proof.MlDsa.KeyGen.modPm_toRq (f := a) (fun c hc=>by have:=ha c hc; omega)
  have eb:=VG.Proof.MlDsa.KeyGen.modPm_toRq (f := b) (fun c hc=>by have:=hb c hc; omega)
  rw [←ea,←eb,he]

def secretUpdate (r n : Nat) (old fresh : Nat→IPoly) (i : Nat) : IPoly :=
 if r≤i ∧ i<r+n then fresh (i-r) else old i

def GroupOutcome (p : Params) (σ : State) (r n : Nat) (fresh : Nat→IPoly) (ret : BitVec 32) : Prop :=
 (ret=1 ∧ ∃B : Bounds,∀i<n,rejBoundedPoly p.η B.rejBounded (seedS (rho'Of p σ) (r+i))=some (fresh i)) ∨
 (ret=0 ∧ ∃i<n,rejBoundedPoly p.η minBounds.rejBounded (seedS (rho'Of p σ) (r+i))=none)

theorem good_group {p : Params} {σ : State} {r n : Nat} (hr : r+n≤p.ℓ+p.k)
    {A : Nat→Poly} {old fresh : Nat→IPoly} {v : BitVec 64} {ret : BitVec 32}
    (hg : Good p σ (p.k*p.ℓ) r A old v) (ho : GroupOutcome p σ r n fresh ret) :
    Good p σ (p.k*p.ℓ) (r+n) A (secretUpdate r n old fresh)
      (if v=1 ∧ ret=1 then 1 else 0) := by
  rcases ho with ⟨hret,B,hB⟩|⟨hret,i,hi,hfail⟩
  · rcases hg with ⟨hv,C,hA,hS⟩|⟨hv,hfail⟩
    · refine Or.inl ⟨by rw [ite_eq_left ⟨hv,hret⟩],bmax C B,?_,?_⟩
      · intro j hj
        exact VG.Proof.MlDsa.KeyGen.rejNTTPoly_mono
          (VG.Proof.MlDsa.KeyGen.Bounds.le_max_left C B).rejNTT (hA j hj)
      · intro j hj
        unfold secretUpdate
        by_cases h : r≤j
        · rw [ite_eq_left ⟨h,hj⟩]
          have he : r+(j-r)=j := by omega
          have hh:=VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono
            (VG.Proof.MlDsa.KeyGen.Bounds.le_max_right C B).rejBounded (hB (j-r) (by omega))
          simpa only [he] using hh
        · rw [ite_eq_right (fun hh=>h hh.1)]
          exact VG.Proof.MlDsa.KeyGen.rejBoundedPoly_mono
            (VG.Proof.MlDsa.KeyGen.Bounds.le_max_left C B).rejBounded (hS j (by omega))
    · exact Or.inr ⟨by rw [ite_eq_right (by simp [hv])],hfail⟩
  · exact Or.inr ⟨by rw [ite_eq_right (by simp [hret])],
      VG.Proof.MlDsa.KeyGen.keyGenInternal_none_S (by omega) hfail⟩


/-- The fourth tail lane repeats lane zero; ordinary groups use all four. -/
def secretLane (n i : Nat) : Nat := if i<n then i else 0

theorem secretLane_lt {n i : Nat} (hn : n=3∨n=4) : secretLane n i<n := by
  unfold secretLane
  split <;> omega

theorem groupOutcome_of_four {p : Params} (hη : p.η≤4) {σ : State}
    {r n : Nat} (hn : n=3∨n=4) {m : Mem} {seed : Addr} {out : Nat→Poly}
    {fresh : Nat→IPoly} {ret : BitVec 32}
    (hseed : ∀i<4,Spec.Sha3.bytesAt m (seed+BitVec.ofNat 64 (66*i)) 66=
      seedS (rho'Of p σ) (r+secretLane n i))
    (hsmall : ∀i<n,Small p.η (fresh i)) (hpoly : ∀i<n,toRq (fresh i)=out i)
    (ho : Outcome (fun B=>(rejBoundedFour p.η B.rejBounded m seed).map (List.map toRq))
      ret ((List.range 4).map out)) : GroupOutcome p σ r n fresh ret := by
  rcases ho with ⟨hret,B,hB⟩|⟨hret,hB⟩
  · refine Or.inl ⟨hret,B,fun i hi=>?_⟩
    have hh:=(boundedFour_some_iff p.η B.rejBounded m seed out).mp hB i (by omega)
    rw [hseed i (by omega),secretLane,ite_eq_left hi] at hh
    obtain ⟨x,hx,he⟩:=Option.map_eq_some_iff.mp hh
    have ex : x=fresh i := small_toRq_inj hη
      (VG.Proof.MlDsa.KeyGen.rejBoundedPoly_range hx) (hsmall i hi) (he.trans (hpoly i hi).symm)
    simpa only [ex] using hx
  · obtain ⟨i,hi,hfail⟩:=(boundedFour_none_iff p.η minBounds.rejBounded m seed).mp hB
    rw [hseed i hi] at hfail
    exact Or.inr ⟨hret,secretLane n i,secretLane_lt hn,hfail⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedSecretGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.KeyGen (Small)
open VG.Proof.MlDsa.AArch64.Optimized

/-- This form covers both four fresh lanes and the three-lane duplicated tail. -/
def groupCode (c : Impl.Sha3.AArch64.Callee) (p : Params) (r n : Nat) : Prog isa :=
 .seq (.block (secretSeedsCode (fun i=>r+secretLane n i))) <|
 .seq (callAt (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.boundedFourSymbol c p.η)
   (VG.Impl.MlDsa.AArch64.Optimized.BoundedFour.sampler c.pairedSha3 true p.η)
   (BoundedFour.samplerArgs (sc 1408) (sP p r) (sc (oR4 p)))) (.block and24)

theorem secretPoly_add (s : State) (p : Params) (r i : Nat) :
    pa s (sP p r)+BitVec.ofNat 64 (1024*i)=pa s (sP p (r+i)) := by
  rw [sc_add]
  congr 2
  unfold oP
  omega

theorem group_ok (c : Impl.Sha3.AArch64.Callee) {p : Params} (hF : PFacts p)
    {S : Nat} {σ : State} (hp : kgPre p S σ) {r n : Nat} (hn : n=3∨n=4)
    (hr : r+n≤p.ℓ+p.k) {s : State} (h : KSamp p σ (p.k*p.ℓ) r s) :
    WP isa (groupCode c p r n) s (KSamp p σ (p.k*p.ℓ) (r+n)) := by
  classical
  have hkl:=hF.kl; have hl:=hF.l; have hk:=hF.k; have hsc:=scr_eq p
  have hη : p.η≤4 := by rcases hF.eta with h|h <;> omega
  unfold groupCode
  refine WP.seq (WP.mono (secretSeeds_ok hF hp (by omega)
    (fun i hi=>by have:=secretLane_lt (i := i) hn; omega) h) fun s1 h1=>?_)
  have L1:=h1.ks.k1.kc.lay hF hp
  refine WP.seq (WP.mono (boundedAt_layout hF L1 (by omega) c) fun s2 ⟨hP2,h24,hred,hsmall,hout⟩=>?_)
  have h2:=h1.ks.keep hF hp hP2 (by unfold k1Chk kcChk; lay)
    (fun k hk=>by lay) (fun k hk=>by lay) h24
  have L2:=h2.k1.kc.lay hF hp
  let fresh : Nat→IPoly := fun i=>if hi : i<n then
    (hsmall i (by omega)).choose else Vector.replicate 256 0
  have freshSpec : ∀i<n,toRq (fresh i)=polyAt s2.mem (pa s1 (sP p r)+BitVec.ofNat 64 (1024*i)) ∧
      Small p.η (fresh i) := by
    intro i hi
    dsimp only [fresh]
    rw [dite_eq_left hi]
    exact ⟨(hsmall i (by omega)).choose_spec.1.symm,(hsmall i (by omega)).choose_spec.2⟩
  have ho : GroupOutcome p σ r n fresh ((s2.gpr .x0).setWidth 32) :=
    groupOutcome_of_four hη hn (fun i hi=>by rw [sc_add]; exact h1.done i hi)
      (fun i hi=>(freshSpec i hi).2) (fun i hi=>(freshSpec i hi).1) hout
  refine WP.mono (and24_ok s2) fun t ⟨ht,hval⟩=>?_
  have hP3 : PPostB S s2 t [] := postB_of_keep ht.keep (by decide)
    (by rw [ht.mem]; exact Frame.refl _ _)
  obtain ⟨A,old,hA,hS,hG⟩:=h2.ex
  refine ⟨h2.k1.step hF hp hP3 (by unfold k1Chk kcChk; layd),A,secretUpdate r n old fresh,
    fun i hi=>L2.keepPoly hP3 (by layd) (hA i hi),fun i hi=>?_,?_⟩
  · unfold secretUpdate
    by_cases hir : r≤i
    · rw [ite_eq_left ⟨hir,hi⟩]
      have hei : r+(i-r)=i := by omega
      have hp' := freshSpec (i-r) (by omega)
      refine ⟨⟨?_,?_⟩,hp'.2⟩
      · rw [ht.mem,sc_pa hP3,sc_pa hP2]
        simpa only [secretPoly_add,hei] using hred (i-r) (by omega)
      · rw [ht.mem,sc_pa hP3,sc_pa hP2]
        simpa only [secretPoly_add,hei] using hp'.1.symm
    · rw [ite_eq_right (fun hh=>hir hh.1)]
      exact ⟨L2.keepPoly hP3 (by lay) (hS i (by omega)).1,(hS i (by omega)).2⟩
  · rw [hval,VG.Proof.MlDsa.KeyGen.and01 (good_01 hG)
      (VG.Proof.MlDsa.KeyGen.outcome_01 hout)]
    exact good_group hr hG ho

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end
