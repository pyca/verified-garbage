module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps

/-! # Constant-time encapsulation with paired matrix sampling -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Kem
variable {P : KemLay} {keccak : Sha3.AArch64.Permutation}

theorem matrix_table_of_kb {L : Layout} {s t : State} (hp : Pre P L s) (kb : KB P L s t) (tb : Tables t) :
    MatrixTable P L s t := by
  have scratch : Covers [⟨kA s L.sc,P.scl⟩] t.wr := by
    have hh := cov_w hp kb (b:=L.sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩ (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  exact ⟨tb.shuffle,tb.shuffleRead,apart_of_covers tb.shuffleApart scratch⟩

theorem encaps_prefix {s : State} (hp : Pre P (Encaps.enL P) s) (tables : Tables s)
    (depth : (P.enAWith keccak.callee).aarch64Depth≤1) :
    WP isa (P.enAWith keccak.callee) s
      (fun t=>BInv P (Encaps.enL P) s t.mem (Encaps.rhoE P s) 0 t ∧ MatrixTable P (Encaps.enL P) s t) := by
  refine WP.mono (WP.tablesDepth (Encaps.a_ok hp) tables depth) fun t ⟨ha,tb⟩=>?_
  exact ⟨BInv.zero ha.kb ha.x24 ha.rho,matrix_table_of_kb hp ha.kb tb⟩

theorem encaps_ct (hw : P.Wf)
    (depth : (P.enAWith keccak.callee).aarch64Depth≤1)
    (ha : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4]) (P.enAWith keccak.callee) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Optimized.enRest keccak.callee P) h).isSome=true) :
    ConstantTime isa (entryContract (encapsAArch64 P)).pre (entryContract (encapsAArch64 P)).pub
      (Impl.MlKem.AArch64.Optimized.encapsWith keccak.callee P) := by
  intro s u tr ur t v hs hu hpub et eu
  have ps := kem_unstrip (Encaps.pre_of hw hs.1)
  have pu := kem_unstrip (Encaps.pre_of hw hu.1)
  have rs : ∀r∈[Reg.x0,.x1,.x2,.x3,.x4],s.gpr r=u.gpr r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact hpub.1.1
    · exact hpub.1.2.1
    · exact hpub.1.2.2.1
    · exact hpub.1.2.2.2.1
    · exact hpub.1.2.2.2.2.1
  have ptr : ∀i<4,kA s ((Encaps.enL P).slot i)=kA u ((Encaps.enL P).slot i) := by
    intro i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3) with rfl|rfl|rfl|rfl <;> exact rs _ (by simp [Encaps.enL,argReg])
  have sp : s.sp=u.sp := hpub.1.2.2.2.2.2.1
  have rho : Encaps.rhoE P s=Encaps.rhoE P u := map_toNat_inj hpub.1.2.2.2.2.2.2
  have sym := entry_symbols hpub
  have wa := encaps_prefix ps (entry_tables hs) depth
  have wb := encaps_prefix pu (entry_tables hu) depth
  rw [←rho] at wb
  have ac := VectorTaint.relRegs [.x0,.x1,.x2,.x3,.x4]
    (P:=fun a b=>a=s ∧ b=u) (fun a b ⟨ha,hb⟩=>by subst a; subst b; exact ⟨sp,rs⟩) ha.choose_spec
  exact (kem_relCT ps pu ptr sp sym.1 sym.2 wa wb ac hc _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.Optimized
