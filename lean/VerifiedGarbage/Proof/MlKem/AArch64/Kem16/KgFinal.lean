module
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgRows
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgOps
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTable
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Contracts
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgRows
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.ContractSat
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenMatrixTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.PairTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.RejectTiming
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgOps
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.TCB.Axioms

/-! # The 16-bit `vg_mlkem768_keygen` and `vg_mlkem1024_keygen`

For `Kem16.keyGen`: constant time (`keyGenW_ct`), with the taint analysis of
the code after the matrix decided on each parameter set, and the contract
(`keyGenW768_final`, `keyGenW1024_final`). -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.KeyGen
variable {P : KemLay}

theorem keyGenW_relCT {P : KemLay} {hash : FixedHash.HashFn} {σ τ : State}
    (hp : KeyGen.Pre P σ) (hq : KeyGen.Pre P τ)
    (ptr : ∀i,KeyGen.kA σ i=KeyGen.kA τ i) (sp : σ.sp=τ.sp)
    (rho : KeyGen.rhoK P σ=KeyGen.rhoK P τ)
    (shuffle : σ.syms "VG_MLKEM_REJ_SHUFFLE"=τ.syms "VG_MLKEM_REJ_SHUFFLE")
    (symbols : ∀name∈restSymbols,σ.syms name=τ.syms name)
    (wa : WP isa (FixedHashCallers.kgAUsing hash P) σ (fun s=>KeyGen.AfterA P σ s ∧ KeyGen.MatrixTable P σ s))
    (wb : WP isa (FixedHashCallers.kgAUsing hash P) τ (fun s=>KeyGen.AfterA P τ s ∧ KeyGen.MatrixTable P τ s))
    (ha : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (FixedHashCallers.kgAUsing hash P) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgRest hash P) h).isSome=true) :
    RelCT isa (fun s u=>s=σ ∧ u=τ) (Kem16.keyGen hash P) (fun _ _=>True) := by
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
    ⟨KeyGen.binvW_zero (w16 := true) as,KeyGen.binvW_zero (w16 := true) au,hs.2,hu.2,
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
theorem keyGenW_ct (hash : FixedHash.HashFn)
 (hG : FixedHash.HashCorrect hash .x28 KG.ST KG.WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) (hw : P.Wf)
    (depth : (FixedHashCallers.kgAUsing hash P).aarch64Depth≤1)
    (ha : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (FixedHashCallers.kgAUsing hash P) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgRest hash P) h).isSome=true) :
    ConstantTime isa (entryContract (keyGenAArch64 P)).pre (entryContract (keyGenAArch64 P)).pub
      (Kem16.keyGen hash P) := by
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
  exact (keyGenW_relCT ps.1 pu.1 ptr sp rho sym.1 sym.2
    (keyGen_using_prefix hash hG ps.1 ps.2 depth) (keyGen_using_prefix hash hG pu.1 pu.2 depth) ha hc
    _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.Optimized

namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem
open VG.Proof.MlKem.AArch64.Optimized

theorem kgMatrixW768_depth : (Paired.matrix lay768 true true).aarch64Depth≤1 := by decide
theorem kgMatrixW1024_depth : (Paired.matrix Impl.MlKem1024.AArch64.lay1024 true true).aarch64Depth≤1 := by decide

theorem kgRestW768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgRest (fixedHash c) lay768) h).isSome=true := by
  taint_decide_generic c := hole using hS
theorem kgRestW1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Kem16.kgRest (fixedHash c) Impl.MlKem1024.AArch64.lay1024) h).isSome=true := by
  taint_decide_generic c := hole using hS

theorem keyGenW768_final (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Kem16.keyGen (fixedHash v.callee) lay768) keyGen768Contract := by
  refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (keyGenAArch64 lay768)) ?_
    (keyGenW_ct (fixedHash v.callee) (kgG768_correct v) VG.Proof.MlKem.AArch64.KeyGen.wf768 (kgA768_depth v)
      (kgA768_taint v.callee v.callerSums) (kgRestW768_taint v.callee (symSums v))) ?_
  · intro s h
    exact KeyGen.using_correctW (fixedHash v.callee) (kgH768_correct v) (kgG768_correct v)
      (entry_keygen VG.Proof.MlKem.AArch64.KeyGen.wf768 h).1 Noise.room768 (entry_tables h) (kgA768_depth v)
      kgMatrixW768_depth
  · exact ⟨fun _ h=>keyGen768_entry h,fun _ _ h hp=>keyGen768_post h hp,
      fun _ _ hs ht hp=>keyGen768_pub hs ht hp,keyGen768_sat⟩

theorem keyGenW1024_final (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Kem16.keyGen (fixedHash v.callee) Impl.MlKem1024.AArch64.lay1024) keyGen1024Contract := by
  refine Verified.of_correct (T:=AArch64.target) (k:=entryContract (keyGenAArch64 Impl.MlKem1024.AArch64.lay1024)) ?_
    (keyGenW_ct (fixedHash v.callee) (kgG1024_correct v) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 (kgA1024_depth v)
      (kgA1024_taint v.callee v.callerSums) (kgRestW1024_taint v.callee (symSums v))) ?_
  · intro s h
    exact KeyGen.using_correctW (fixedHash v.callee) (kgH1024_correct v) (kgG1024_correct v)
      (entry_keygen VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 h).1 Noise.room1024 (entry_tables h) (kgA1024_depth v)
      kgMatrixW1024_depth
  · exact ⟨fun _ h=>keyGen1024_entry h,fun _ _ h hp=>keyGen1024_post h hp,
      fun _ _ hs ht hp=>keyGen1024_pub hs ht hp,keyGen1024_sat⟩

end VG.Proof.MlKem.AArch64.FixedHash
