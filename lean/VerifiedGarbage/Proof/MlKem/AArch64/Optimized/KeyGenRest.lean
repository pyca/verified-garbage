module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.KeyGenReadonlyNoise
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Complete key-generation composition after matrix sampling -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
variable {P : KemLay}
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem rest_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P)
    (htr : Optimized.TransformTables s)
    (h : BInv P s₀ (P.k*P.k) s) (ht : RowTable P s₀ s)
    (hd : ∀r∈Noise.allWrites P true (kA s₀ 3), (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r)
    (ha : (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint (R (kA s₀) 2 0 (384*P.k))) :
    WP isa (Impl.MlKem.AArch64.Optimized.kgRest keccak.callee P) s (Done P s₀ s.mem (s.gpr .x24)) := by
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
  exact finish_ok hp hr et tt (by simpa only [hs] using ha)

end VG.Proof.MlKem.AArch64.KeyGen
