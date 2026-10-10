import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedDot
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRestState
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRoundCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution

/-! ## From `OptimizedDot.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.Inverse

abbrev dotWrites (p : Params) (_i : Nat) : List (Ptr × Nat) := [(tP p,1024),(sc oSS,1024)]

def optimizedDotChk (p : Params) (i : Nat) : Bool :=
  let o := tP p; let a := aP (p.ℓ*i); let b := sP p 0; let z := sc oSS
  inB (kgR++kgW p) o 1024 && inB (kgR++kgW p) a (1024*p.ℓ) &&
  inB (kgR++kgW p) b (1024*p.ℓ) && inB (kgR++kgW p) z 1024 &&
  inB (kgW p) o 1024 && inB (kgW p) z 1024 &&
  sepB (kgR) (kgW p) o 1024 a (1024*p.ℓ) &&
  sepB (kgR) (kgW p) o 1024 b (1024*p.ℓ) &&
  sepB (kgR) (kgW p) o 1024 z 1024 &&
  sepB (kgR) (kgW p) a (1024*p.ℓ) z 1024 &&
  sepB (kgR) (kgW p) b (1024*p.ℓ) z 1024 && kcChk p (dotWrites p i)

theorem optimizedDotChk_ok {p : Params} (hp : PFacts p) : ∀i<p.k,optimizedDotChk p i=true := by
  rcases hp.mem with rfl | rfl | rfl <;> decide

theorem optimizedDotReady {p : Params} (hp : PFacts p) {S : Nat} {σ s : State} {i : Nat}
    (hc : optimizedDotChk p i=true) (hpre : kgPre p S σ) (hs : KC p σ s) (roots : Sign.StaticRoots S s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) :
    DotCallReady p.ℓ (tP p) (aP (p.ℓ*i)) (sP p 0) (sc oSS) s := by
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,oa⟩,ob⟩,oz⟩,az⟩,bz⟩,_⟩ := hc
  have L := hs.lay hp hpre
  refine ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.nwp rz,roots.inverse.held,roots.inverse.fit,?_,
    L.disj oa,L.disj ob,L.disj oz,L.disj az,L.disj bz,ha,hb,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact roots.inverse.apart_write (L.inW wo)
    · exact roots.inverse.apart_write (L.inW wz)
  · exact Covers.cons (L.cR ra) (Covers.cons (L.cR rb)
      (Covers.cons roots.inverse.readable (Covers.cons (L.cR ro) (L.cR rz))))
  · exact Covers.cons (L.cW wo) (L.cW wz)

/-- Fused row arithmetic preserves all polynomial families outside its two
write slots. The returned frame can be applied directly to Fam/PosFam. -/
theorem optimizedDot_ok {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hp : PFacts p) (hc : optimizedDotChk p i=true) (hpre : kgPre p S σ) (hs : KC p σ s) (roots : Sign.StaticRoots S s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) s fun t =>
      KC p σ t ∧ Sign.StaticRoots S t ∧ t.gpr .x24=s.gpr .x24 ∧ PPostB S s t (dotWrites p i) ∧
      PolyIs t.mem (pa t (tP p)) (nttInv (dotNTT
        (fun j => polyAt s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
        (fun j => polyAt s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ)) := by
  have ready := optimizedDotReady hp hc hpre hs roots ha hb
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,_⟩,_⟩,_⟩,_⟩,_⟩,st⟩ := hc
  have hn : p.ℓ=4 ∨ p.ℓ=5 ∨ p.ℓ=7 := by rcases hp.mem with rfl | rfl | rfl <;> decide
  have L := hs.lay hp hpre
  refine WP.mono_syms (dotAt_ok L.s64 hn (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) (ptr_ok (L.ptrBs rz)) ready) fun t ⟨hP,hv⟩ hy => ?_
  have hpB : PPostB S s t (dotWrites p i) := hP.b
  refine ⟨hs.step hp hpre hpB st,roots.step_layout L hpB hy ?_,hP.cs .x24 (by decide) (by decide),hpB,?_⟩
  · intro w hw
    simp only [dotWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact wo
    · exact wz
  · rw [hpB.pa (L.ptrBs ro)]; exact hv


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedDotValue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.KeyGen (dotK)

private theorem poly_addr (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j))) =
      pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

/-- The fused inverse consumes the lazy secret transforms directly. Its
canonical row is the same field sum as the scalar reference key generator. -/
theorem dotRow_value {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {i : Nat}
    (hi : i<p.k) (h : PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i s)
    (roots : Sign.StaticRoots S' s) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) s fun t =>
      PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i t ∧ Sign.StaticRoots S' t ∧
      PolyIs t.mem (pa t (tP p)) (nttInv (dotK p A S i p.ℓ)) := by
  have hA j (hj : j<p.ℓ) : PolyIs s.mem
      (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)) (A (p.ℓ*i+j)) := by
    have hv := h.aS _ (idx_lt hi hj)
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*i+j)))) _ at hv
    rw [poly_addr] at hv
    exact hv
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem
      (pa s (sP p 0)+BitVec.ofNat 64 (1024*j)) (ntt (toRq (S j))) := by
    have hv := h.s1 j hj
    simp only [ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+j)))) _ at hv
    rw [poly_addr] at hv
    simpa only [sP,Nat.add_zero] using hv
  refine WP.mono (optimizedDot_ok hF (optimizedDotChk_ok hF i hi) hp h.kc roots
    (fun j hj => (PosPolyIs.of_canonical (hA j hj)).bound)
    (fun j hj => (hB j hj).bound)) fun t ⟨_,rt,h24,hP,hv⟩ => ?_
  have hc : KRChk p (p.ℓ+p.k) p.ℓ i (dotWrites p i) := by
    have hk := hF.k; have hl := hF.l; have hs := hF.scr
    exact KRChk.append (ws₁ := [_])
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [SV, oP]; omega) (.inr (Nat.le_refl _))
        (by rw [hs]; simp only [oP]; omega))
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [SV, oSS]; omega)
        (.inl (by simp only [oSS, oP]; omega)) (by rw [hs]; simp only [oSS]; omega))
  refine ⟨h.keep hF hp hP h24 hc,rt,?_⟩
  have he : dotNTT
      (fun j => polyAt s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
      (fun j => polyAt s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ = dotK p A S i p.ℓ := by
    unfold dotNTT dotK
    apply congrArg (List.foldl add zero)
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    dsimp only
    rw [(hA j hj).2,(hB j hj).value]
  simpa only [he] using hv

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

/-! ## From `OptimizedRow.lean` -/

section

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
  refine ⟨h.keep hF hp hP' x' (chk_sbp hF hi), L.keepPoly hP' (by layd) h0, ?_⟩
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
      rw [L.keepBytes hP' (by layd)]; exact h1, ?_⟩
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

end
