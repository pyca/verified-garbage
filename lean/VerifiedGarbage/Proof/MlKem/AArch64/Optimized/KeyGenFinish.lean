module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenEncode

/-! # Key generation after paired noise sampling -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem RowTable.encode_frame {s₀ s t : State}
    (h : RowTable P s₀ s) (hs : t.syms=s.syms) (hk : KB P s₀ s) (hk' : KB P s₀ t)
    (hf : Frame [R (kA s₀) 2 0 (384*P.k)] s.mem t.mem)
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) 2 0 (384*P.k))) :
    RowTable P s₀ t := by
  refine ⟨?_,?_,?_⟩
  · rw [hs]
    intro j hj
    rw [←h.table j hj]
    exact hf.readW (r := ⟨s.syms "VG_MLKEM_GAMMA",512⟩)
      (contains_off (by omega) (by decide)) (fun r hr => by rw [List.mem_singleton.mp hr]; exact ha) (by decide)
  · simpa only [hs,hk'.rd,hk'.wr,←hk.rd,←hk.wr] using h.read
  · simpa only [hs] using h.apart

theorem finish_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    {mB : Mem} {v : BitVec 64} (h : EncodeInv P s₀ mB s.mem v 0 s)
    (ht : RowTable P s₀ s)
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) 2 0 (384*P.k))) :
    WP isa (seqs (((List.range P.k).map fun j => kgEnc (sOff P j) .x27 (384*j)) ++
      ((List.range P.k).map (Impl.MlKem.AArch64.Optimized.kgRow P)) ++ [P.kgEndWith keccak.callee]))
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
    (WPs.mono (rows_ok hp hr ⟨he.tl,he.errors,ht'⟩) fun u hu => WPs.single (end_ok hp hu.1))

end VG.Proof.MlKem.AArch64.KeyGen
