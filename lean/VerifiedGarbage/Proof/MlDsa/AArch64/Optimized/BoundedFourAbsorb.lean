import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (oSave)
open VG.Impl.MlDsa.AArch64.Optimized.BoundedFour (absorbPair)
open ResidentRej (seedP scr at' scrR stateP)
open ResidentMask (absorbBody_ok seedState_eq)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (zeros_ok pair_sub)

def absorbArgs (p : Nat) : List Instr :=
 [.addImm .x .x2 .x19 (400*p),.addImm .x .x3 .x20 (132*p),.addImm .x .x4 .x3 66]

theorem absorbPair_eq (p : Nat) : absorbPair p=absorbArgs p++Impl.MlDsa.AArch64.Optimized.ResidentMask.absorbBody := rfl

theorem absorbArgs_ok {p : Nat} (hp : p<2) {s : State} :
    WP isa (.block (absorbArgs p)) s fun t=>Proof.MlKem.AArch64.Only [.x2,.x3,.x4] s t ∧
      t.gpr .x2=s.gpr .x19+BitVec.ofNat 64 (400*p) ∧
      t.gpr .x3=s.gpr .x20+BitVec.ofNat 64 (132*p) ∧
      t.gpr .x4=s.gpr .x20+BitVec.ofNat 64 (132*p+66) := by
  unfold absorbArgs
  refine Proof.MlKem.AArch64.wp_addImm (by omega) fun a ha h2=>
    Proof.MlKem.AArch64.wp_addImm (by omega) fun b hb h3=>
    Proof.MlKem.AArch64.wp_addImm (by decide) fun t ht h4=>Proof.MlKem.AArch64.wp_nil ?_
  refine ⟨((ha.trans hb).trans ht).mono (by decide),?_,?_,?_⟩
  · rw [ht.get .x2,hb.get .x2,h2]
  · rw [ht.get .x3,h3,ha.get .x20]
  · rw [h4,h3,ha.get .x20,BitVec.add_assoc,←BitVec.ofNat_add]

private theorem seed_sub {σ : State} {k : Nat} (hk : k<4) :
    Region.Sub (ResidentMask.seedR (seedP σ+BitVec.ofNat 64 (66*k)))
      (samplerSeeds σ) := Offset.sub_base (seedP σ) (by omega)

private theorem seed_eq {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s)
    {k : Nat} (hk : k<4) :
    Spec.Sha3.bytesAt s.mem (seedP σ+BitVec.ofNat 64 (66*k)) 66=Spec.Sha3.bytesAt σ.mem (seedP σ+BitVec.ofNat 64 (66*k)) 66 := by
  refine Proof.MlKem.bytesAt_frame he.frame ?_ (by decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.seed_output.sub_left (seed_sub hk)
  · exact hp.seed_work.sub_left (seed_sub hk)

theorem zeroAll_ok {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.zeroStates) s fun t => SamplerEnv σ t ∧
      ∀i<50,t.mem.read (wordAddr (scr σ) i) 16=0 := by
  refine WP.mono (zeros_ok he.x19 (fun i hi => sampler_in_work hp he.wr (by omega))) fun t ⟨ht,hf,hz⟩ => ?_
  exact ⟨he.lowStep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide))
    ht.rd ht.wr ht.sp (fun r _ => ht.gpr r (by simp)),hz⟩

theorem absorbPair_ok {σ s : State} (hp : SamplerPre σ) (he : SamplerEnv σ s) {p : Nat} (hstream : 2*p+1<4)
    (hz : ∀ i < 25,s.mem.read (wordAddr (stateP σ p) i) 16 = 0) :
    WP isa (.block (absorbPair p)) s fun t => SamplerEnv σ t ∧
      PairAt t.mem (stateP σ p) (samplerA σ (2*p)) (samplerA σ (2*p+1)) ∧
      Frame [pairR (stateP σ p)] s.mem t.mem := by
  have hpn : p<2 := by omega
  rw [absorbPair_eq,WP.block_append_iff]
  refine WP.mono (absorbArgs_ok hpn) fun s1 ⟨h1,e2,e3,e4⟩ => ?_
  have he1 : SamplerEnv σ s1 := he.lowStep (rs := []) (by rw [h1.mem]; exact Frame.refl _ _)
    (by simp) h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  let a := seedP σ+BitVec.ofNat 64 (66*(2*p))
  let b := seedP σ+BitVec.ofNat 64 (66*(2*p+1))
  have e2' : s1.gpr .x2 = stateP σ p := by rw [e2,he.x19]; rfl
  have e3' : s1.gpr .x3 = a := by rw [e3,he.x20,show 132*p = 66*(2*p) by omega]
  have e4' : s1.gpr .x4 = b := by rw [e4,he.x20,show 132*p+66 = 66*(2*p+1) by omega]
  have seed_in (k : Nat) (hk : k < 4) (d n : Nat) (hd : d+n ≤ 66) :
      InRegions (s1.rd++s1.wr) ((seedP σ+BitVec.ofNat 64 (66*k))+BitVec.ofNat 64 d) n := by
    rw [Offset.add_add]
    exact sampler_in_seed hp he1.rd (by omega)
  have hws : ∀ j < 25,InRegions s1.wr (wordAddr (stateP σ p) j) 16 := by
    intro j hj
    change InRegions s1.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*j)) 16
    rw [Offset.add_add]
    exact sampler_in_work hp he1.wr (by omega)
  have hps : Region.Sub (pairR (stateP σ p)) (scrR σ) :=
    Offset.sub_base (scr σ) (by omega)
  refine WP.mono (absorbBody_ok e2' e3' e4'
    (fun j hj => seed_in (2*p) (by omega) (8*j) 8 (by omega))
    (fun j hj => seed_in (2*p+1) (by omega) (8*j) 8 (by omega))
    (seed_in (2*p) (by omega) 64 1 (by decide)) (seed_in (2*p) (by omega) 65 1 (by decide))
    (seed_in (2*p+1) (by omega) 64 1 (by decide)) (seed_in (2*p+1) (by omega) 65 1 (by decide))
    hws ((hp.seed_work.sub_left (seed_sub (by omega))).sub_right hps)
    ((hp.seed_work.sub_left (seed_sub (by omega))).sub_right hps)
    (by intro i hi; rw [h1.mem]; exact hz i hi)) fun t ⟨h2,hf2,hp2⟩ => ?_
  refine ⟨he1.lowStep hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact pair_sub hpn)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_⟩
  · rw [seedState_eq,seedState_eq,seed_eq hp he1 (by omega : 2*p < 4),seed_eq hp he1 (by omega : 2*p+1 < 4)] at hp2
    simpa only [samplerA,samplerSeedAt,seedState_eq] using hp2
  · rw [← h1.mem]; exact hf2
end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
