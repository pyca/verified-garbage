module

public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Top

/-! # The 16-bit hashing encapsulation is constant time

`encapsHW_ct`: as `Hybrid.encapsH_ct`, for `Kem16.encaps`: the first phase
and the rest by the taint analyses, the matrix sampled with 16 bits by
`matrixH_relCT`. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Encaps (enL ekE rhoE)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {P : KemLay}

/-- **The 16-bit hashing encapsulation is constant time.** -/
theorem encapsHW_ct (hash : FixedHash.HashFn) (prf : Nat→Nat→Prog isa) (hw : P.Wf) (ho : HashOk P)
    (habs : ∀ blk, 136 * blk < P.ekLen → ∃ h, (taint.check (Taint.ofRegs [.x25, .x28])
      (.block (Impl.MlKem.AArch64.Hybrid.absorbBlock P blk)) h).isSome = true)
    (ha : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3,.x4])
      (Impl.MlKem.AArch64.Hybrid.startH P) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.seq (Impl.MlKem.AArch64.Hybrid.tailH hash) (Impl.MlKem.AArch64.Kem16.enRest prf P)) h).isSome=true) :
    ConstantTime isa (entryContractS (encapsAArch64S P)).pre (entryContractS (encapsAArch64S P)).pub
      (Impl.MlKem.AArch64.Kem16.encaps hash prf P) := by
  intro s u tr ur t v hs hu hpub et eu
  have ss := preS hs.1
  have su := preS hu.1
  have ps := kem_unstrip (Encaps.pre_of hw ss.1)
  have pu := kem_unstrip (Encaps.pre_of hw su.1)
  have rs : ∀r∈[Reg.x0,.x1,.x2,.x3,.x4],s.gpr r=u.gpr r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl
    · exact hpub.1.1
    · exact hpub.1.2.1
    · exact hpub.1.2.2.1
    · exact hpub.1.2.2.2.1
    · exact hpub.1.2.2.2.2.1
  have ptr : ∀i<4,kA s ((enL P).slot i)=kA u ((enL P).slot i) := by
    intro i hi
    rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3) with rfl|rfl|rfl|rfl <;> exact rs _ (by simp [enL,argReg])
  have sp : s.sp=u.sp := hpub.1.2.2.2.2.2.1
  have rho : rhoE P s=rhoE P u := map_toNat_inj hpub.1.2.2.2.2.2.2
  have sym := entryS_symbols hpub
  have sm : Same P s u := ⟨ptr 3 (by decide), ptr 0 (by decide), sp⟩
  have ts := entryS_tables hs
  have tu := entryS_tables hu
  have wa := prefixH (w16 := true) ps ts.1 ts.2
  have wb := prefixH (w16 := true) pu tu.1 tu.2
  rw [←rho] at wb
  have ac := VectorTaint.relRegs [.x0,.x1,.x2,.x3,.x4]
    (P:=fun a b=>a=s ∧ b=u) (fun a b ⟨ha,hb⟩=>by subst a; subst b; exact ⟨sp,rs⟩) ha.choose_spec
  exact (kemH_relCT ps pu ⟨ss.2.sp, ss.2.args⟩ ⟨su.2.sp, su.2.args⟩ sm ptr ho habs
    sym.1 sym.2 wa wb ac hc _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.Hybrid
