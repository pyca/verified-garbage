module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TopTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TableApart
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Tables

/-! # Constant-time key generation under the emitted read-only table contract -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem.AArch64.KeyGen
variable {P : KemLay} {keccak : Sha3.AArch64.Permutation}

theorem keyGen_prefix {s : State} (hp : KeyGen.Pre P s) (tables : Tables s)
    (depth : (P.kgAWith keccak.callee).aarch64Depth≤1) :
    WP isa (P.kgAWith keccak.callee) s (fun t=>AfterA P s t ∧ MatrixTable P s t) := by
  refine WP.mono (WP.tablesDepth (a_ok hp) tables depth) fun t ⟨ha,tb⟩=>?_
  have scratch : Covers [⟨kA s 3,P.scl⟩] t.wr := by
    simpa only [R,ptr_zero] using cov_w hp ha.kb (b:=3) (o:=0) (l:=P.scl) (by decide) (by kl)
  exact ⟨ha,tb.shuffle,tb.shuffleRead,apart_of_covers tb.shuffleApart scratch⟩

theorem entry_symbols {base : Contract isa} {s u : State} (h : (entryContract base).pub s u) :
    (s.syms "VG_MLKEM_REJ_SHUFFLE"=u.syms "VG_MLKEM_REJ_SHUFFLE") ∧
    ∀name∈restSymbols,s.syms name=u.syms name := by
  refine ⟨h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inl rfl),?_⟩
  intro name hn
  simp only [restSymbols,List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inl rfl))
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
  · exact h.2 _ (by simp only [constants,List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))

theorem keyGen_ct (hw : P.Wf)
    (depth : (P.kgAWith keccak.callee).aarch64Depth≤1)
    (ha : ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3]) (P.kgAWith keccak.callee) h).isSome=true)
    (hc : ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Optimized.kgRest keccak.callee P) h).isSome=true) :
    ConstantTime isa (entryContract (keyGenAArch64 P)).pre (entryContract (keyGenAArch64 P)).pub
      (Impl.MlKem.AArch64.Optimized.keyGenWith keccak.callee P) := by
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
  exact (keyGen_relCT ps.1 pu.1 ptr sp rho sym.1 sym.2
    (keyGen_prefix ps.1 ps.2 depth) (keyGen_prefix pu.1 pu.2 depth) ha hc
    _ _ _ _ _ _ ⟨rfl,rfl⟩ et eu).1

end VG.Proof.MlKem.AArch64.Optimized
