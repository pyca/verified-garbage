import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPro
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejFour
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejTwo

/-! ## From `ResidentRejAbsorb.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (absorbPair oSave)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (absorbArgs_ok absorbBody_ok seedState_eq zeros_ok pair_sub)

private theorem seed_sub {v : Nat} {σ : State} {k : Nat} (hk : k<v) :
    Region.Sub (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR (seedP σ+BitVec.ofNat 64 (34*k)))
      (seedsR v σ) := Offset.sub_base (seedP σ) (by omega)

private theorem seed_eq {v : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s)
    {k : Nat} (hk : k<v) :
    Spec.Sha3.bytesAt s.mem (seedP σ+BitVec.ofNat 64 (34*k)) 34=B σ k := by
  refine Proof.MlKem.bytesAt_frame he.frame ?_ (by decide)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.seed_a.sub_left (seed_sub hk)
  · exact hp.seed_scr.sub_left (seed_sub hk)

theorem zeroAll_ok {v : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s) :
    WP isa (.block Impl.MlDsa.AArch64.Sample.Rej4.zeroStates) s fun t => Env v σ t ∧
      ∀i<50,t.mem.read (wordAddr (scr σ) i) 16=0 := by
  refine WP.mono (zeros_ok he.x19 (fun i hi => in_scr hp he.wr (by omega))) fun t ⟨ht,hf,hz⟩ => ?_
  exact ⟨he.lowStep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide))
    ht.rd ht.wr ht.sp (fun r _ => ht.gpr r (by simp)),hz⟩

theorem absorbPair_ok {v : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s) {p : Nat} (hstream : 2*p+1<v)
    (hz : ∀ i < 25,s.mem.read (wordAddr (stateP σ p) i) 16 = 0) :
    WP isa (.block (absorbPair p)) s fun t => Env v σ t ∧
      PairAt t.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)) ∧
      Frame [pairR (stateP σ p)] s.mem t.mem := by
  have hpn : p<2 := by have:=hp.streams; omega
  unfold absorbPair
  rw [WP.block_append_iff]
  refine WP.mono (absorbArgs_ok hpn) fun s1 ⟨h1,e2,e3,e4⟩ => ?_
  have he1 : Env v σ s1 := he.lowStep (rs := []) (by rw [h1.mem]; exact Frame.refl _ _)
    (by simp) h1.rd h1.wr h1.sp (fun r hr => h1.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide))
  let a := seedP σ+BitVec.ofNat 64 (34*(2*p))
  let b := seedP σ+BitVec.ofNat 64 (34*(2*p+1))
  have e2' : s1.gpr .x2 = stateP σ p := by rw [e2,he.x19]; rfl
  have e3' : s1.gpr .x3 = a := by rw [e3,he.x20,show 68*p = 34*(2*p) by omega]
  have e4' : s1.gpr .x4 = b := by rw [e4,he.x20,show 68*p+34 = 34*(2*p+1) by omega]
  have seed_in (k : Nat) (hk : k < v) (d n : Nat) (hd : d+n ≤ 34) :
      InRegions (s1.rd++s1.wr) ((seedP σ+BitVec.ofNat 64 (34*k))+BitVec.ofNat 64 d) n := by
    rw [Offset.add_add]
    exact in_seed hp he1.rd (by omega)
  have hws : ∀ j < 25,InRegions s1.wr (wordAddr (stateP σ p) j) 16 := by
    intro j hj
    change InRegions s1.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*j)) 16
    rw [Offset.add_add]
    exact in_scr hp he1.wr (by omega)
  have hps : Region.Sub (pairR (stateP σ p)) (scrR σ) :=
    Offset.sub_base (scr σ) (by omega)
  refine WP.mono (absorbBody_ok e2' e3' e4'
    (fun j hj => seed_in (2*p) (by omega) (8*j) 8 (by omega))
    (fun j hj => seed_in (2*p+1) (by omega) (8*j) 8 (by omega))
    (seed_in (2*p) (by omega) 32 1 (by decide)) (seed_in (2*p) (by omega) 33 1 (by decide))
    (seed_in (2*p+1) (by omega) 32 1 (by decide)) (seed_in (2*p+1) (by omega) 33 1 (by decide))
    hws ((hp.seed_scr.sub_left (seed_sub (by omega))).sub_right hps)
    ((hp.seed_scr.sub_left (seed_sub (by omega))).sub_right hps)
    (by intro i hi; rw [h1.mem]; exact hz i hi)) fun t ⟨h2,hf2,hp2⟩ => ?_
  refine ⟨he1.lowStep hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact pair_sub hpn)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_⟩
  · rw [seedState_eq,seedState_eq,seed_eq hp he1 (by omega : 2*p < v),seed_eq hp he1 (by omega : 2*p+1 < v)] at hp2
    exact hp2
  · rw [← h1.mem]; exact hf2
end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejCounts.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_movz)
open VG.Proof.Sha3.AArch64 (Mupd wp_str)
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej (counts)

def countR (s : State) : Region := ⟨at' s counts,32⟩
def initCountsCode (v : Nat) : List Instr := [.movz .x .x4 256 0]++
  (List.range v).map fun k => .str .x .x4 .x19 (counts+8*k)

theorem countsStore_ok (v : Nat) (hv : v≤4) {s : State} {p : Addr}
    (h19 : s.gpr .x19=p) (h4 : s.gpr .x4=256)
    (hw : ∀i<v,InRegions s.wr (p+BitVec.ofNat 64 (counts+8*i)) 8) :
    WP isa (.block ((List.range v).map fun k => .str .x .x4 .x19 (counts+8*k))) s fun t =>
      Mupd s t t.mem ∧ Frame [⟨p+BitVec.ofNat 64 counts,32⟩] s.mem t.mem ∧
      ∀i<v,t.mem.readW (p+BitVec.ofNat 64 (counts+8*i)) 64=256 := by
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Mupd s t t.mem ∧ Frame [⟨p+BitVec.ofNat 64 counts,32⟩] s.mem t.mem ∧
      ∀i<k,t.mem.readW (p+BitVec.ofNat 64 (counts+8*i)) 64=256)
    (fun k t hk ⟨ht,hf,hs⟩ => ?_) v (Nat.le_refl _) s
    ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_str (a := p+BitVec.ofNat 64 (counts+8*k))
    (by unfold counts; constructor <;> omega) (by rw [ht.gpr,h19])
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨hu.gpr.trans ht.gpr,rfl,hu.rd.trans ht.rd,hu.wr.trans ht.wr,
      hu.sp.trans ht.sp,hu.vec.trans ht.vec⟩
  · rw [hu.mem]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains p (d := counts+8*k) (e := counts) (n := 8) (k := 32)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hu.mem,ht.gpr,h4]
    by_cases he : i=k
    · subst i; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep
        (Offset.sep p (d := counts+8*i) (e := counts+8*k) (n := 8) (k := 8)
          (by omega) (by unfold counts; omega) (by unfold counts; omega)) (by decide)]
      exact hs i (by omega)

theorem initCounts_ok {v : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s) :
    WP isa (.block (initCountsCode v)) s fun t => Env v σ t ∧
      Frame [countR σ] s.mem t.mem ∧ ∀i<v,t.mem.readW (countP σ i) 64=256 := by
  rw [initCountsCode,List.cons_append,List.nil_append]
  refine wp_movz fun a ha ea => ?_
  have h4 : a.gpr .x4=256 := by rw [ea]; rfl
  refine WP.mono (countsStore_ok v (by have:=hp.streams; omega)
    (by rw [ha.get .x19]; exact he.x19) h4
    (fun i hi => in_scr hp (ha.wr.trans he.wr) (by have:=hp.streams; unfold counts; omega)))
    fun t ⟨ht,hf,hs⟩ => ?_
  have hframe : Frame [countR σ] s.mem t.mem := by rw [←ha.mem]; exact hf
  refine ⟨he.lowStep hframe (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.sub_base (scr σ) (by decide))
    (ht.rd.trans ha.rd) (ht.wr.trans ha.wr) (ht.sp.trans ha.sp)
    (fun r hr => by rw [ht.gpr,ha.get r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)]),hframe,hs⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
