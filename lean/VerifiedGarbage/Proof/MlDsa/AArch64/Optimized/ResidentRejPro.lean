import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejState

/-! ## From `ResidentRejSaveG.lean` -/

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
  refine wp_str (a := at' σ (oSave+8*k)) ⟨by dsimp only [oSave]; omega,by dsimp only [oSave]; omega⟩
    (by rw [ht.gpr]; rfl) (by rw [ht.wr]; exact hwork _ _ (by dsimp only [oSave]; omega)) fun u hu => WP.block_nil_iff.mpr ⟨?_,?_,?_⟩
  · exact ⟨hu.gpr.trans ht.gpr,rfl,hu.rd.trans ht.rd,hu.wr.trans ht.wr,
      hu.sp.trans ht.sp,hu.vec.trans ht.vec⟩
  · rw [hu.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains (scr σ) (d := oSave+8*k) (e := oSave) (n := 8) (k := 144) (by omega) (by omega) (by decide))
  · intro i hi
    rw [hu.mem,ht.gpr]
    by_cases he : i = k
    · subst i; rw [Mem.readW_writeW_self64]
    · have hs : Mem.Sep (at' σ (oSave+8*i)) 8 (at' σ (oSave+8*k)) 8 :=
        Offset.sep (scr σ) (d := oSave+8*i) (e := oSave+8*k) (n := 8) (k := 8) (by omega) (by dsimp only [oSave]; omega) (by dsimp only [oSave]; omega)
      rw [Mem.readW_writeW_sep hs (by decide)]
      exact hvals i (by omega)
theorem saveG_ok {v : Nat} {σ : State} (hp : Pre v σ) :
    WP isa (.block saveG) σ fun t => Mupd σ t t.mem ∧ Frame [saveR σ] σ.mem t.mem ∧
      ∀ i < 10,t.mem.readW (at' σ (oSave+8*i)) 64 = σ.gpr (saved[i]!) :=
  saveG_with (fun _ _ h=>in_scr hp rfl h)

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
    (by rw [ht.wr,hw]; exact hwork _ _ (by dsimp only [oSave]; omega))) fun u ⟨hu,hvu,hm⟩ => ?_
  change u.mem = t.mem.writeW (at' σ (oSave+80+8*k)) (vdword (t.v (vreg (8+k))) 0) at hm
  refine ⟨(ht.trans hu).mono (by simp),hvu.trans hv,?_,?_⟩
  · rw [hm]
    exact hf.writeW (List.mem_singleton_self _) _
      (Offset.contains (scr σ) (d := oSave+80+8*k) (e := oSave+80) (n := 8) (k := 64)
        (by omega) (by omega) (by decide))
  · intro i hi
    rw [hm,hv]
    by_cases he : i = k
    · subst i; rw [Mem.readW_writeW_self64]
    · have hs : Mem.Sep (at' σ (oSave+80+8*i)) 8 (at' σ (oSave+80+8*k)) 8 :=
        Offset.sep (scr σ) (d := oSave+80+8*i) (e := oSave+80+8*k) (n := 8) (k := 8)
          (by omega) (by dsimp only [oSave]; omega) (by dsimp only [oSave]; omega)
      rw [Mem.readW_writeW_sep hs (by decide)]
      exact hvals i (by omega)
theorem saveV_ok {v : Nat} {σ s : State} (hp : Pre v σ) (hw : s.wr = σ.wr) (hs : s.gpr .x2 = scr σ) :
    WP isa (.block saveV) s fun t => RegKeep [.x8] s t ∧ t.v = s.v ∧
      Frame [vSaveR σ] s.mem t.mem ∧ ∀ i < 8,
        t.mem.readW (at' σ (oSave+80+8*i)) 64 = vdword (s.v (vreg (8+i))) 0 :=
  saveV_with (fun _ _ h=>in_scr hp rfl h) hw hs

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
        (by omega) (by dsimp only [oSave]; omega) (by decide)
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
