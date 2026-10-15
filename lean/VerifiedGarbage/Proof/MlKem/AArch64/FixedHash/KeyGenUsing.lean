module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenEnd
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenPrefix
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenCorrect
@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Optimized
variable {P : KemLay}
theorem finish_using_ok (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} (h : EncodeInv P s₀ mB s.mem v 0 s)
    (ht : RowTable P s₀ s)
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) 2 0 (384*P.k))) :
    WP isa (seqs (((List.range P.k).map fun j => kgEnc (sOff P j) .x27 (384*j)) ++
      ((List.range P.k).map (Impl.MlKem.AArch64.Optimized.kgRow P)) ++ [FixedHashCallers.kgEndUsing hash P]))
      s (Done P s₀ mB v) := by
  apply WPs.seqs (by simp)
  rw [List.append_assoc]
  apply WPs.append
  have he := WPs.seqs (map_range_ne_nil hp.wf.facts.1 _) (encode_ok hp hr h)
  have he' := WP.mono_syms he (fun t he hs =>
    show EncodeInv P s₀ mB s.mem v P.k t ∧ RowTable P s₀ t from
      ⟨he,ht.encode_frame hs h.c.kb he.c.kb he.frame ha⟩)
  -- The encode loop's abstract list carries symbol preservation as well.
  have hseq : WPs ((List.range P.k).map fun j => kgEnc (sOff P j) .x27 (384*j)) s
      (fun t => EncodeInv P s₀ mB s.mem v P.k t ∧ RowTable P s₀ t) := by
    have hkeep : ∀ cs s Q, WP isa (seqs cs) s Q → cs≠[] → WPs cs s Q := by
      intro cs
      induction cs with
      | nil => intro s Q _ hn; exact False.elim (hn rfl)
      | cons c cs ih =>
        intro s Q hw hn
        cases cs with
        | nil => exact WP.mono hw (fun _ h => h)
        | cons d ds =>
          exact WP.mono (WP.seq_iff.mp hw) fun _ h => ih _ _ h (List.cons_ne_nil _ _)
    exact hkeep _ _ _ he' (map_range_ne_nil hp.wf.facts.1 _)
  exact WPs.mono hseq fun t ⟨he,ht'⟩ => WPs.append
    (WPs.mono (rows_ok hp hr ⟨he.tl,he.errors,ht'⟩) fun u hu => WPs.single (end_using_ok hash hH hp hu.1))

theorem rest_using_ok (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    (htr : Optimized.TransformTables s)
    (h : BInv P s₀ (P.k*P.k) s) (ht : RowTable P s₀ s)
    (hd : ∀r∈Noise.allWrites P true (kA s₀ 3), (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) 2 0 (384*P.k))) :
    WP isa (FixedHashCallers.kgRestUsing hash P) s (Done P s₀ s.mem (s.gpr .x24)) := by
  have c : CInv P s₀ s.mem (s.gpr .x24) s := ⟨h.kb,h.rho,h.sig,rfl,fun e he => ⟨h.red e he,rfl⟩⟩
  refine WP.seq (WP.mono_syms (readonly_noise_encode hp hr htr c) fun t ⟨kt,et⟩ hs => ?_)
  have tt : RowTable P s₀ t := by
    refine ⟨?_,?_,?_⟩
    · rw [hs]
      intro j hj
      rw [←ht.table j hj]
      exact kt.frame.readW (r := ⟨s.syms "VG_MLKEM_GAMMA",512⟩)
        (contains_off (by omega) (by decide)) hd (by decide)
    · simpa only [hs,kt.rd,kt.wr] using ht.read
    · simpa only [hs] using ht.apart
  exact finish_using_ok hash hH hp hr et tt (by simpa only [hs] using ha)

theorem using_correct (hash : FixedHash.HashFn)
 (hH : FixedHash.HashCorrect hash .x28 ST WK 136 6
  [⟨.x26,0,P.ekLen⟩] [⟨.x27,768*P.k+32,32⟩]) (hG : FixedHash.HashCorrect hash .x28 ST WK 72 6
  [⟨.x25,0,32⟩,⟨.x28,BK,1⟩] [⟨.x28,SB,32⟩,⟨.x28,SG,32⟩]) {s₀ : State} (hp : Pre P s₀) (hr : Noise.Room P) (tables : Tables s₀)
    (depthA : (FixedHashCallers.kgAUsing hash P).aarch64Depth≤1)
    (depthB : (Impl.MlKem.AArch64.Paired.matrix P true).aarch64Depth≤1) :
    WP isa (FixedHashCallers.keyGenUsing hash P) s₀ fun t=>
      abiPreserved s₀ t ∧ (keyGenAArch64 P).post s₀ t := by
  refine WP.seq (WP.mono (WP.tablesDepth (a_using_ok hash hG hp) tables depthA) fun sA ⟨hA,ta⟩=>?_)
  have scratchA : Covers [⟨kA s₀ 3,P.scl⟩] sA.wr := by
    simpa only [R,ptr_zero] using (cov_w hp hA.kb (b:=3) (o:=0) (l:=P.scl) (by decide) (by kl))
  have mt : MatrixTable P s₀ sA :=
    ⟨ta.shuffle,ta.shuffleRead,apart_of_covers ta.shuffleApart scratchA⟩
  refine WP.seq (WP.mono (WP.tablesDepth (paired_matrix_ok hp (BInv.zero hA) mt) ta depthB)
    fun sB ⟨⟨hB,_⟩,tb⟩=>?_)
  have hw := hp.wf
  refine WP.mono (rest_using_ok hash hH hp hr tb.transforms hB
    (readonly_rows hp hB.kb tb.gamma tb.gammaRead tb.gammaApart)
    (readonly_noise hp hr hB.kb tb.gammaApart)
    (apart_of_covers tb.gammaApart (cov_w hp hB.kb (b:=2) (o:=0) (l:=384*P.k) (by decide) (by kl))))
    fun t ht=>⟨ht.abi,post_of hB ht⟩

end VG.Proof.MlKem.AArch64.KeyGen
