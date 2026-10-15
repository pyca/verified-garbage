module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.EncapsTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecryptStart
public import VerifiedGarbage.Proof.MlKem.AArch64.Decaps

/-! # Constant-time decapsulation with fused decryption and paired sampling -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Kem
variable {P : KemLay} {keccak : Sha3.AArch64.Permutation}

theorem decaps_prefix {s : State} (hp : Pre P (Decaps.deL P) s) (calls : Calls P) (tables : Tables s)
    (depth : (Impl.MlKem.AArch64.Optimized.deStart keccak.callee P).aarch64Depth≤1) :
    WP isa (Impl.MlKem.AArch64.Optimized.deStart keccak.callee P) s
      (fun t=>BInv P (Decaps.deL P) s t.mem (Decaps.rhoD P s) 0 t ∧ MatrixTable P (Decaps.deL P) s t) := by
  have scratch : Covers [⟨kA s (Decaps.deL P).sc,P.scl⟩] s.wr := by
    have hh := cov_w₀ hp (b:=(Decaps.deL P).sc) (o:=0) (l:=P.scl) ⟨hp.scw,hp.scb⟩ (by rw [hp.scl]; omega)
    simpa only [R,ptr_zero] using hh
  refine WP.mono (WP.tablesDepth (Decaps.start_ok hp calls tables.transforms tables.gamma tables.gammaRead
    (apart_of_covers tables.gammaApart scratch)) tables depth) fun t ⟨ha,tb⟩=>?_
  exact ⟨BInv.zero ha.kb ha.x24 ha.rho,matrix_table_of_kb hp ha.kb tb⟩

theorem decaps_ct (hw : P.Wf) (calls : Calls P)
    (depth : (Impl.MlKem.AArch64.Optimized.deStart keccak.callee P).aarch64Depth≤1)
    (ha : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (Impl.MlKem.AArch64.Optimized.deStart keccak.callee P) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Optimized.deRest keccak.callee P) h).isSome=true) :
    ConstantTime isa (entryContract (decapsAArch64 P)).pre (entryContract (decapsAArch64 P)).pub
      (Impl.MlKem.AArch64.Optimized.decapsWith keccak.callee P) := by
  intro s u tr ur t v hs hu hpub et eu
  have ps := kem_unstrip (Decaps.pre_of hw hs.1)
  have pu := kem_unstrip (Decaps.pre_of hw hu.1)
  have rs : ∀r∈[Reg.x0,.x1,.x2,.x3],s.gpr r=u.gpr r := by
    intro r hr
    rcases mem4 hr with rfl|rfl|rfl|rfl
    · exact hpub.1.1
    · exact hpub.1.2.1
    · exact hpub.1.2.2.1
    · exact hpub.1.2.2.2.1
  have ptr : ∀i<4,kA s ((Decaps.deL P).slot i)=kA u ((Decaps.deL P).slot i) := by
    intro i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3) with rfl|rfl|rfl|rfl <;> exact rs _ (by simp [Decaps.deL,argReg])
  have sp : s.sp=u.sp := hpub.1.2.2.2.2.1
  have rho : Decaps.rhoD P s=Decaps.rhoD P u := map_toNat_inj hpub.1.2.2.2.2.2
  have sym := entry_symbols hpub
  have wa := decaps_prefix ps calls (entry_tables hs) depth
  have wb := decaps_prefix pu calls (entry_tables hu) depth
  rw [←rho] at wb
  have ac : RelCT isa (fun a b=>a=s ∧ b=u) (Impl.MlKem.AArch64.Optimized.deStart keccak.callee P) (fun _ _=>True) := by
    intro a b atr btr a' b' h ea eb
    rcases h with ⟨hsa,hub⟩; subst a; subst b
    exact ⟨symbol_taint [.x0,.x1,.x2,.x3] sp rs sym.2 ha ea eb,trivial⟩
  exact (kem_relCT ps pu ptr sp sym.1 sym.2 wa wb ac hc _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.Optimized
