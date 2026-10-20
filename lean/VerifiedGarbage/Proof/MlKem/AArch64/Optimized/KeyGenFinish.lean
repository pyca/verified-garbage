module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenTables

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

end VG.Proof.MlKem.AArch64.KeyGen
