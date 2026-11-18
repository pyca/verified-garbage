module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.ProArgs
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Zero
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.AbsorbArgs
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Absorb
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.SeedFrame

/-! ### `MlDsa.AArch64.Optimized.ResidentRejCounts`, which the modules that import this one used -/

section

/-! ## From `ResidentRejAbsorb.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (absorbPair oSave)
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (absorbArgs_ok absorbBody_ok seedState_eq zeros_ok pair_sub)

private theorem seed_sub {v : Nat} {σ : State} {k : Nat} (hk : k<v) :
    Region.Sub (VG.Proof.MlDsa.AArch64.Sample.Rej4.seedR (seedP σ+BitVec.ofNat 64 (34*k)))
      (seedsR v σ) := Offset.sub_base (seedP σ) (by omega_using [hk])

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
  refine WP.mono (zeros_ok he.x19 (fun i hi => in_scr hp he.wr (by omega_using [hi]))) fun t ⟨ht,hf,hz⟩ => ?_
  exact ⟨he.lowStep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide))
    ht.rd ht.wr ht.sp (fun r _ => ht.gpr r (by simp)),hz⟩

theorem absorbPair_ok {v : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s) {p : Nat} (hstream : 2*p+1<v)
    (hz : ∀ i < 25,s.mem.read (wordAddr (stateP σ p) i) 16 = 0) :
    WP isa (.block (absorbPair p)) s fun t => Env v σ t ∧
      PairAt t.mem (stateP σ p) (A0 σ (2*p)) (A0 σ (2*p+1)) ∧
      Frame [pairR (stateP σ p)] s.mem t.mem := by
  have hpn : p<2 := by have:=hp.streams; omega_using [hstream, this]
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
  have e3' : s1.gpr .x3 = a := by rw [e3,he.x20,show 68*p = 34*(2*p) by omega_using []]
  have e4' : s1.gpr .x4 = b := by rw [e4,he.x20,show 68*p+34 = 34*(2*p+1) by omega_using []]
  have seed_in (k : Nat) (hk : k < v) (d n : Nat) (hd : d+n ≤ 34) :
      InRegions (s1.rd++s1.wr) ((seedP σ+BitVec.ofNat 64 (34*k))+BitVec.ofNat 64 d) n := by
    rw [Offset.add_add]
    exact in_seed hp he1.rd (by omega_using [hk, hd])
  have hws : ∀ j < 25,InRegions s1.wr (wordAddr (stateP σ p) j) 16 := by
    intro j hj
    change InRegions s1.wr ((scr σ+BitVec.ofNat 64 (400*p))+BitVec.ofNat 64 (16*j)) 16
    rw [Offset.add_add]
    exact in_scr hp he1.wr (by omega_using [hpn, hj])
  have hps : Region.Sub (pairR (stateP σ p)) (scrR σ) :=
    Offset.sub_base (scr σ) (by omega_using [hpn])
  refine WP.mono (absorbBody_ok e2' e3' e4'
    (fun j hj => seed_in (2*p) (by omega_using [hstream]) (8*j) 8 (by omega_using [hj]))
    (fun j hj => seed_in (2*p+1) (by omega_using [hstream]) (8*j) 8 (by omega_using [hj]))
    (seed_in (2*p) (by omega_using [hstream]) 32 1 (by decide)) (seed_in (2*p) (by omega_using [hstream]) 33 1 (by decide))
    (seed_in (2*p+1) (by omega_using [hstream]) 32 1 (by decide)) (seed_in (2*p+1) (by omega_using [hstream]) 33 1 (by decide))
    hws ((hp.seed_scr.sub_left (seed_sub (by omega_using [hstream]))).sub_right hps)
    ((hp.seed_scr.sub_left (seed_sub (by omega_using [hstream]))).sub_right hps)
    (by intro i hi; rw [h1.mem]; exact hz i hi)) fun t ⟨h2,hf2,hp2⟩ => ?_
  refine ⟨he1.lowStep hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact pair_sub hpn)
    h2.rd h2.wr h2.sp (fun r hr => h2.gpr r (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide)),?_,?_⟩
  · rw [seedState_eq,seedState_eq,seed_eq hp he1 (by omega_using [hstream] : 2*p < v),seed_eq hp he1 (by omega_using [hstream] : 2*p+1 < v)] at hp2
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
    (by unfold counts; constructor <;> omega_arith) (by rw [ht.gpr,h19])
    (by rw [ht.wr]; exact hw k hk) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨hu.gpr.trans ht.gpr,rfl,hu.rd.trans ht.rd,hu.wr.trans ht.wr,
      hu.sp.trans ht.sp,hu.vec.trans ht.vec⟩
  · rw [hu.mem]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains p (d := counts+8*k) (e := counts) (n := 8) (k := 32)
        (by omega_using []) (by omega_using [hv, hk]) (by decide))
  · intro i hi
    rw [hu.mem,ht.gpr,h4]
    by_cases he : i=k
    · subst i; rw [Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep
        (Offset.sep p (d := counts+8*i) (e := counts+8*k) (n := 8) (k := 8)
          (by omega_using [he]) (by unfold counts; omega_using [hv, hk, hi]) (by unfold counts; omega_using [hv, hk])) (by decide)]
      exact hs i (by omega_using [hi, he])

theorem initCounts_ok {v : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s) :
    WP isa (.block (initCountsCode v)) s fun t => Env v σ t ∧
      Frame [countR σ] s.mem t.mem ∧ ∀i<v,t.mem.readW (countP σ i) 64=256 := by
  rw [initCountsCode,List.cons_append,List.nil_append]
  refine wp_movz fun a ha ea => ?_
  have h4 : a.gpr .x4=256 := by rw [ea]; rfl
  refine WP.mono (countsStore_ok v (by have:=hp.streams; omega_using [this])
    (by rw [ha.get .x19]; exact he.x19) h4
    (fun i hi => in_scr hp (ha.wr.trans he.wr) (by have:=hp.streams; unfold counts; omega_using [hi, this])))
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

end

end

/-! ## From `ResidentRejSaveG.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64 (wp_str Mupd)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (saveG oSave saved)

theorem saveG_with {σ : State}
    (hwork : ∀d n,d+n≤8192→InRegions σ.wr (at' σ d) n) :
    WP isa (.block saveG) σ fun t => Mupd σ t t.mem ∧ Frame [saveR σ] σ.mem t.mem ∧
      ∀ i < 10,t.mem.readW (at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!) := by
  unfold saveG
  rw [List.map_eq_flatMap]
  refine wp_range_flatMap (M := isa)
    (fun k t => Mupd σ t t.mem ∧ Frame [saveR σ] σ.mem t.mem ∧
      ∀ i < k,t.mem.readW (at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!))
    (fun k t hk ⟨ht,hf,hvals⟩ => ?_) 10 (Nat.le_refl _) σ
    ⟨⟨rfl,rfl,rfl,rfl,rfl,rfl⟩,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine wp_str (a := at' σ (oSave+8*k)) ⟨by dsimp only [oSave]; omega_using [],by dsimp only [oSave]; omega_using [hk]⟩
    (by rw [ht.gpr]; rfl) (by rw [ht.wr]; exact hwork _ _ (by dsimp only [oSave]; omega_using [hk])) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨hu.gpr.trans ht.gpr,rfl,hu.rd.trans ht.rd,hu.wr.trans ht.wr,
      hu.sp.trans ht.sp,hu.vec.trans ht.vec⟩
  · rw [hu.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains (scr σ) (d := oSave+8*k) (e := oSave) (n := 8) (k := 144) (by omega_using []) (by omega_using [hk]) (by decide))
  · intro i hi
    rw [hu.mem,ht.gpr]
    by_cases he : i = k
    · subst i; rw [Mem.readW_writeW_self64]
    · have hs : Mem.Sep (at' σ (oSave+8*i)) 8 (at' σ (oSave+8*k)) 8 :=
        Offset.sep (scr σ) (d := oSave+8*i) (e := oSave+8*k) (n := 8) (k := 8) (by omega_using [he]) (by dsimp only [oSave]; omega_using [hk, hi]) (by dsimp only [oSave]; omega_using [hk])
      rw [Mem.readW_writeW_sep hs (by decide)]
      exact hvals i (by omega_using [hi, he])
end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSaveV.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64 (Upd wp_str WP.cons)
open VG.Impl.Sha3.AArch64.Sha3.Vector (vreg)
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (saveV oSave)

theorem saveV_with {σ s : State}
    (hwork : ∀d n,d+n≤8192→InRegions σ.wr (at' σ d) n) (hw : s.wr = σ.wr) (hs : s.gpr .x2 = scr σ) :
    WP isa (.block saveV) s fun t => RegKeep [.x8] s t ∧ t.v = s.v ∧
      Frame [vSaveR σ] s.mem t.mem ∧ ∀ i < 8,
        t.mem.readW (at' σ (oSave+80+8*i)) 64 = vdword (s.v (vreg (8+i))) 0 := by
  unfold saveV
  refine wp_range_flatMap (M := isa)
    (fun k t => RegKeep [.x8] s t ∧ t.v = s.v ∧ Frame [vSaveR σ] s.mem t.mem ∧ ∀ i < k,
      t.mem.readW (at' σ (oSave+80+8*i)) 64 = vdword (s.v (vreg (8+i))) 0)
    (fun k t hk ⟨ht,hv,hf,hvals⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨RegKeep.refl _ _,rfl,Frame.refl _ _,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.saveV_step hk ((ht.gpr .x2 (by decide)).trans hs)
    (by rw [ht.wr,hw]; exact hwork _ _ (by dsimp only [oSave]; omega_using [hk]))) fun u ⟨hu,hvu,hm⟩ => ?_
  change u.mem = t.mem.writeW (at' σ (oSave+80+8*k)) (vdword (t.v (vreg (8+k))) 0) at hm
  refine ⟨(ht.trans hu).mono (by simp),hvu.trans hv,?_,?_⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains (scr σ) (d := oSave+80+8*k) (e := oSave+80) (n := 8) (k := 64)
        (by omega_using []) (by omega_using [hk]) (by decide))
  · intro i hi
    rw [hm,hv]
    by_cases he : i = k
    · subst i; rw [Mem.readW_writeW_self64]
    · have hs : Mem.Sep (at' σ (oSave+80+8*i)) 8 (at' σ (oSave+80+8*k)) 8 :=
        Offset.sep (scr σ) (d := oSave+80+8*i) (e := oSave+80+8*k) (n := 8) (k := 8)
          (by omega_using [he]) (by dsimp only [oSave]; omega_using [hk, hi]) (by dsimp only [oSave]; omega_using [hk])
      rw [Mem.readW_writeW_sep hs (by decide)]
      exact hvals i (by omega_using [hi, he])
end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejPro.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Impl.MlDsa.AArch64.Sample.Rej4 (pro oSave)

theorem pro_with (v : Nat) {σ : State}
    (hwork : ∀d n,d+n≤8192→InRegions σ.wr (at' σ d) n) : WP isa (.block pro) σ (Env v σ) := by
  unfold pro
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (saveG_with hwork) fun s1 ⟨h1,hf1,hg1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveV_with hwork h1.wr (by rw [h1.gpr]; rfl)) fun s2 ⟨h2,hv2,hf2,hvsave⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.AArch64.Sample.Rej4.proArgs_ok s2) fun t ⟨h3,e19,e20,e21⟩ => ?_
  refine ⟨h3.rd.trans (h2.rd.trans h1.rd),h3.wr.trans (h2.wr.trans h1.wr),
    h3.sp.trans (h2.sp.trans h1.sp),?_,?_,?_,?_,?_,?_,?_⟩
  · rw [e19,h2.gpr .x2 (by decide),h1.gpr]; rfl
  · rw [e20,h2.gpr .x0 (by decide),h1.gpr]; rfl
  · rw [e21,h2.gpr .x1 (by decide),h1.gpr]; rfl
  · rw [h3.get .x30,h2.gpr .x30 (by decide),h1.gpr]
  · intro i hi
    rw [h3.mem]
    have hd : (⟨at' σ (oSave+8*i),8⟩ : Region).Disjoint (vSaveR σ) :=
      Offset.disjoint (scr σ) (d := oSave+8*i) (n := 8) (e := oSave+80) (k := 64)
        (by omega_using [hi]) (by dsimp only [oSave]; omega_using [hi]) (by decide)
    rw [hf2.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)]
    exact hg1 i hi
  · intro i hi
    rw [h3.mem,hvsave i hi,h1.vec]
  · rw [h3.mem]
    exact (hf1.sub (fun r hr => by rw [List.mem_singleton.mp hr]; exact
      ⟨scrR σ,by simp,Offset.sub_base (scr σ) (d := oSave) (n := 144) (k := 8192) (by decide)⟩)).trans
      (hf2.sub (fun r hr => by rw [List.mem_singleton.mp hr]; exact
        ⟨scrR σ,by simp,Offset.sub_base (scr σ) (d := oSave+80) (n := 64) (k := 8192) (by decide)⟩))
theorem pro_ok {v : Nat} {σ : State} (hp : Pre v σ) : WP isa (.block pro) σ (Env v σ) :=
  pro_with v (fun _ _ h=>in_scr hp rfl h)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end
