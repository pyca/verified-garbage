import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRowPieces
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedTimingBase

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG.Impl.MlDsa.AArch64.Call (Arg)
open VG.Proof.MlDsa.KeyGen (dotK)

private theorem slot_add (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j))) =
      pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem dotRow_ready {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {i : Nat} (hi : i<p.k)
    (h : KRx p (p.ℓ+p.k) p.ℓ i σ s) (roots : Sign.StaticRoots S' s) :
    DotCallReady p.ℓ (tP p) (aP (p.ℓ*i)) (sP p 0) (VG.Impl.MlDsa.AArch64.Call.sc oSS) s := by
  obtain ⟨A,T,R,h⟩ := h
  refine optimizedDotReady hF (optimizedDotChk_ok hF i hi) hp h.kc roots ?_ ?_
  · intro j hj
    have hv := h.aS _ (idx_lt hi hj)
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*i+j)))) _ at hv
    rw [slot_add] at hv
    exact (PosPolyIs.of_canonical hv).bound
  · intro j hj
    have hv := h.s1 j hj
    simp only [ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+j)))) _ at hv
    rw [slot_add] at hv
    have hv' : PosPolyIs s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j)) (ntt (toRq (T j))) := by
      simpa only [sP,Nat.add_zero] using hv
    exact hv'.bound

theorem dotRow_tr {p : Params} (hF : PFacts p) {S' : Nat} {i : Nat} (hi : i<p.k) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) fun _ _=>True := by
  have hn : p.ℓ=4∨p.ℓ=5∨p.ℓ=7 := by rcases hF.mem with rfl|rfl|rfl <;> decide
  apply dotAt_tr (S:=S') hn
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
  rintro x y ⟨⟨σ,τ,hσ,hτ,pub,⟨hx,rx⟩,⟨hy,ry⟩⟩,et⟩
  obtain ⟨A,T,R,hx'⟩ := hx
  obtain ⟨B,U,V,hy'⟩ := hy
  have ht := kc_two hF hσ hτ pub hx'.kc hy'.kc
  exact ⟨dotRow_ready hF hσ hi ⟨A,T,R,hx'⟩ rx,
    dotRow_ready hF hτ hi ⟨B,U,V,hy'⟩ ry,
    ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),
    ht.same.2,et.2⟩

theorem dotRow_relCT {p : Params} (hF : PFacts p) {S' : Nat} {i : Nat} (hi : i<p.k) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i)
      (RootPair p S' (RowI p i (tIs p fun A T=>nttInv (dotK p A T i p.ℓ)))) := by
  apply rootPair_progress (ht:=dotRow_tr hF hi)
  rintro σ s hp ⟨A,T,R,h⟩ roots
  exact WP.mono (dotRow_value hF hp hi h roots) fun t ⟨ht,rt,hv⟩=>⟨⟨A,T,R,ht,hv⟩,rt⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
