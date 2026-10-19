module
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.DecapsTiming
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Kem
variable {P : KemLay}
theorem decaps_using_ct {w16 : Bool} {start rest : Prog isa} (hw : P.Wf)
    (prelude : ∀{s : State},Pre P (Decaps.deL P) s → Tables s →
      WP isa start s (fun t=>BInvW w16 P (Decaps.deL P) s t.mem (Decaps.rhoD P s) 0 t ∧
        MatrixTable P (Decaps.deL P) s t))
    (ha : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (start) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (rest) h).isSome=true) :
    ConstantTime isa (entryContract (decapsAArch64 P)).pre (entryContract (decapsAArch64 P)).pub
      (.seq start (.seq (Paired.matrix P false w16) rest)) := by
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
  have wa := prelude ps (entry_tables hs)
  have wb := prelude pu (entry_tables hu)
  rw [←rho] at wb
  have ac : RelCT isa (fun a b=>a=s ∧ b=u) (start) (fun _ _=>True) := by
    intro a b atr btr a' b' h ea eb
    rcases h with ⟨hsa,hub⟩; subst a; subst b
    exact ⟨symbol_taint [.x0,.x1,.x2,.x3] sp rs sym.2 ha ea eb,trivial⟩
  exact (kem_relCT ps pu ptr sp sym.1 sym.2 wa wb ac hc _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.Optimized
