module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenUsing
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.KeyGen
variable {P : KemLay}
theorem keyGen_using_relCT {P : KemLay} {hash : FixedHash.HashFn} {σ τ : State}
    (hp : KeyGen.Pre P σ) (hq : KeyGen.Pre P τ)
    (ptr : ∀i,KeyGen.kA σ i=KeyGen.kA τ i) (sp : σ.sp=τ.sp)
    (rho : KeyGen.rhoK P σ=KeyGen.rhoK P τ)
    (shuffle : σ.syms "VG_MLKEM_REJ_SHUFFLE"=τ.syms "VG_MLKEM_REJ_SHUFFLE")
    (symbols : ∀name∈restSymbols,σ.syms name=τ.syms name)
    (wa : WP isa (FixedHashCallers.kgAUsing hash P) σ (fun s=>KeyGen.AfterA P σ s ∧ KeyGen.MatrixTable P σ s))
    (wb : WP isa (FixedHashCallers.kgAUsing hash P) τ (fun s=>KeyGen.AfterA P τ s ∧ KeyGen.MatrixTable P τ s))
    (ha : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (FixedHashCallers.kgAUsing hash P) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (FixedHashCallers.kgRestUsing hash P) h).isSome=true) :
    RelCT isa (fun s u=>s=σ ∧ u=τ) (FixedHashCallers.keyGenUsing hash P) (fun _ _=>True) := by
  intro s u tr ur t v h et eu
  rcases h with ⟨hs,hu⟩; subst s; subst u
  obtain ⟨sA,ta,tb,rfl,ea,eb⟩ := Paired.seq_parts et
  obtain ⟨uA,ua,ub,rfl,fa,fb⟩ := Paired.seq_parts eu
  have aeq := (VectorTaint.relRegs [.x0,.x1,.x2,.x3]
    (P:=fun s u=>s=σ ∧ u=τ) (fun s u ⟨hs,hu⟩=>by
      subst s; subst u
      refine ⟨sp,?_⟩
      intro r hr
      rcases mem4 hr with rfl|rfl|rfl|rfl
      · exact ptr 0
      · exact ptr 1
      · exact ptr 2
      · exact ptr 3) ha.choose_spec _ _ _ _ _ _ ⟨rfl,rfl⟩ ea fa).1
  have hs := Paired.exec_post wa ea
  have hu := Paired.exec_post wb fa
  have as := hs.1
  have au := hu.1
  obtain ⟨sB,tc,td,rfl,ec,ed⟩ := Paired.seq_parts eb
  obtain ⟨uB,uc,ud,rfl,fc,fd⟩ := Paired.seq_parts fb
  have bm := KeyGen.paired_matrix_relCT hp hq (ptr 3) sp rho _ _ _ _ _ _
    ⟨KeyGen.BInv.zero as,KeyGen.BInv.zero au,hs.2,hu.2,
      by rw [Exec.syms ea,Exec.syms fa]; exact shuffle⟩ ec fc
  have beq := bm.1
  have bs := bm.2.1
  have bu := bm.2.2.1
  have ceq := symbol_taint [.x25,.x26,.x27,.x28]
    (by rw [bs.kb.sp,bu.kb.sp,sp]) (fun r hr=>by
      rcases mem4 hr with rfl|rfl|rfl|rfl
      · rw [bs.kb.x25,bu.kb.x25,ptr 0]
      · rw [bs.kb.x26,bu.kb.x26,ptr 1]
      · rw [bs.kb.x27,bu.kb.x27,ptr 2]
      · rw [bs.kb.x28,bu.kb.x28,ptr 3])
    (fun name hn=>by rw [Exec.syms ec,Exec.syms fc,Exec.syms ea,Exec.syms fa]; exact symbols name hn) hc ed fd
  exact ⟨by rw [aeq,beq,ceq],trivial⟩
theorem keyGen_using_prefix (hash : FixedHash.HashFn)
 (hG : FixedHash.HashCorrect hash .x28 KG.ST KG.WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) {s : State} (hp : KeyGen.Pre P s) (tables : Tables s)
    (depth : (FixedHashCallers.kgAUsing hash P).aarch64Depth≤1) :
    WP isa (FixedHashCallers.kgAUsing hash P) s (fun t=>AfterA P s t ∧ MatrixTable P s t) := by
  refine WP.mono (WP.tablesDepth (a_using_ok hash hG hp) tables depth) fun t ⟨ha,tb⟩=>?_
  have scratch : Covers [⟨kA s 3,P.scl⟩] t.wr := by
    simpa only [R,ptr_zero] using cov_w hp ha.kb (b:=3) (o:=0) (l:=P.scl) (by decide) (by kl)
  exact ⟨ha,tb.shuffle,tb.shuffleRead,apart_of_covers tb.shuffleApart scratch⟩
theorem keyGen_using_ct (hash : FixedHash.HashFn)
 (hG : FixedHash.HashCorrect hash .x28 KG.ST KG.WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) (hw : P.Wf)
    (depth : (FixedHashCallers.kgAUsing hash P).aarch64Depth≤1)
    (ha : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (FixedHashCallers.kgAUsing hash P) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (FixedHashCallers.kgRestUsing hash P) h).isSome=true) :
    ConstantTime isa (entryContract (keyGenAArch64 P)).pre (entryContract (keyGenAArch64 P)).pub
      (FixedHashCallers.keyGenUsing hash P) := by
  intro s u tr ur t v hs hu hpub et eu
  have ps := entry_keygen hw hs
  have pu := entry_keygen hw hu
  have ptr : ∀i,kA s i=kA u i
    | 0=>hpub.1.1
    | 1=>hpub.1.2.1
    | 2=>hpub.1.2.2.1
    | _+3=>hpub.1.2.2.2.1
  have sp : s.sp=u.sp := hpub.1.2.2.2.2.1
  have rho : rhoK P s=rhoK P u := by
    have hh := map_toNat_inj hpub.1.2.2.2.2.2
    unfold rhoK dB
    rw [ptr_zero,ptr_zero]
    exact hh
  have sym := entry_symbols hpub
  exact (keyGen_using_relCT ps.1 pu.1 ptr sp rho sym.1 sym.2
    (keyGen_using_prefix hash hG ps.1 ps.2 depth) (keyGen_using_prefix hash hG pu.1 pu.2 depth) ha hc
    _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.Optimized
