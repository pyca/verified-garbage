import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDotValue
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRoundCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)

section
variable {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {σ : State} (hp : kgPre p S' σ)
  {i : Nat} (hi : i < p.k)
include hP hF hp hi

theorem addS2_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.addAt P (tP p) (sP p (p.ℓ + i))) s fun s' =>
      PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => tK p A S i) A S s' := by
  dsimp only [tIs] at ht
  have L := h.kc.lay hF hp
  have hS := h.s2 i hi
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.addAt
  refine WP.mono (accAt_ok (op := add) hP.s64 hP.add L (add_chk hF hi) ht.1 hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (chk_t hF hi), ?_⟩
  rw [tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.tK, ← hS.2, ← ht.2]
  exact hb

/-- `Power2Round` of `t`. -/
theorem p2r_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => tK p A S i) A S s) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P (tP p) (t1P p) (t0P p)) s fun s' =>
      PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ NatPolyIs s'.mem (pa s' (t1P p)) (t1K p A S i) ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) := by
  dsimp only [tIs] at ht
  have L := h.kc.lay hF hp
  refine WP.mono (p2rAt_ok hP.s64 hP.power2Round L (p2r_chk hF hi) ht.1) fun s' ⟨hP', x', h1, h0⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (chk_p2r hF hi), ?_, ?_⟩
  · rw [hP'.pa (p := t1P p) (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.t1K, ← ht.2]; exact h1
  · rw [hP'.pa (p := t0P p) (show Reg.x28 ∈ keptRegs by decide), ← ht.2]; exact h0

/-- `t₁[i]` to `pk`. -/
theorem sbp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s) (h1 : NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i))
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) s fun s' =>
      PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
      bytesAt s'.mem (pa s' (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  refine WP.mono (sbpAt_ok hP.s64 hP.simpleBitPack L (sbp_chk hF hi) sbpOk_t1 (t1_bound h1))
    fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (chk_sbp hF hi), L.keepPoly hP' (by lay [hF.pk]) h0, ?_⟩
  rw [hP'.pa (show Reg.x26 ∈ keptRegs by decide), hb, h1]

/-- `t₀[i]` to `sk`. -/
theorem bp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s)
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2))
    (h1 : bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) s
      (PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  refine WP.mono (bpAt_ok hP.s64 hP.bitPack L (bp_chk hF hi) bpOk_t0 h0.1 (range_t0 h0))
    fun s' ⟨hP', x', hb⟩ => ?_
  have hk' := h.keep hF hp hP' x' (chk_bp hF hi)
  refine ⟨hk'.kc, hk'.x24, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨by
      have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
      rw [L.keepBytes hP' (by lay [hF.pk, hF.sk])]; exact h1, ?_⟩
    rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), hb, h0.2, modPm_t0]
    rfl

end


/-- One complete measured row, retaining lazy secret transforms and emitting
exactly the reference public and private key encodings. -/
theorem row_ok {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params}
    (hF : PFacts p) {σ s : State} (hp : kgPre p S' σ) {i : Nat} (hi : i<p.k)
    {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    (h : PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i s)
    (roots : Sign.StaticRoots S' s)
    (hd : 16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S') :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i) s fun t =>
      PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ (i+1) t ∧ Sign.StaticRoots S' t := by
  apply roots.phase hd hP.s64
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.row
  apply WP.seq
  refine WP.mono (dotRow_value hF hp hi h roots) fun a ⟨ha,_,hv⟩ => ?_
  apply WP.seq
  refine WP.mono (addS2_ok hP hF hp hi ha hv) fun b ⟨hb,hv⟩ => ?_
  apply WP.seq
  refine WP.mono (p2r_ok hP hF hp hi hb hv) fun c ⟨hc,h1,h0⟩ => ?_
  apply WP.seq
  refine WP.mono (sbp_ok hP hF hp hi hc h1 h0) fun d ⟨hd,h0,h1⟩ => ?_
  exact bp_ok hP hF hp hi hd h0 h1

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
