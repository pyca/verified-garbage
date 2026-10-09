import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallSave

namespace VG.Proof.MlDsa.AArch64.Optimized.Ball
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample
open VG.Proof.MlDsa.AArch64.Sample.Ball (CStored)
open VG.Proof.MlKem.AArch64

/-- Frame transport for a polynomial, including its representation. -/
theorem stored_frame {rs : List Region} {s u : State} {a : Addr} {c : Spec.MlDsa.IPoly}
    (hc : CStored s.mem a c) (hf : Frame rs s.mem u.mem)
    (hd : ∀ r∈rs,(polyR a).Disjoint r) : CStored u.mem a c := by
  intro k hk
  change u.mem.readW (coeffAddr a k) 32=_
  rw [hf.readW (coeff_contains a hk) hd (by decide)]
  exact hc k hk

/-- Retain the precise Keccak state through disjoint parser writes. -/
theorem state_frame {rs : List Region} {s u : State} {p : Addr}
    (hf : Frame rs s.mem u.mem) (hd : ∀ r∈rs,(⟨p,200⟩ : Region).Disjoint r) :
    Spec.Sha3.stateAt u.mem p=Spec.Sha3.stateAt s.mem p := by
  apply Vector.ext
  intro k hk
  simp only [Spec.Sha3.stateAt,Vector.getElem_ofFn]
  exact hf.readW (r := ⟨p,200⟩) (Offset.contains_base p (by omega) (by omega)) hd (by decide)

theorem env_saved {P : Sp} {σ s u : State} (hp : SpOk P σ) (he : Env P σ s)
    (hk : Keep [] s u) (hf : Frame (parserSaves P.scr) s.mem u.mem) : Env P σ u :=
  he.call hp ⟨fun r _ _ => hk.get r (by simp),hk.sp,hk.rd,hk.wr,hf,hk.vcs⟩ (by
    intro r hr
    rcases mem3 hr with rfl|rfl|rfl
    · exact .inl ⟨1800,8,rfl,by decide⟩
    · exact .inl ⟨1808,8,rfl,by decide⟩
    · exact .inl ⟨1816,8,rfl,by decide⟩)
end VG.Proof.MlDsa.AArch64.Optimized.Ball
