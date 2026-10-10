import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedDotTiming

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (wRow)
open VG.Proof.MlDsa.Arith.Montgomery
theorem product_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (_hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (_hw : W p σ A' r s)
    (ht : PosPolyIs s.mem (pa s (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)) :
    MontProduct.Ready (tm2P p) (cP p) (tmP p) s := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : PosPolyIs s.mem (pa s (cP p)) (ntt c0) := hs.c
  have ro : inB (vR p++vW p) (tm2P p) 1024=true := by vlayd
  have ra : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have rb : inB (vR p++vW p) (tmP p) 1024=true := by vlayd
  have wo : inB (vW p) (tm2P p) 1024=true := by vlayd
  have ready : MontProduct.Ready (tm2P p) (cP p) (tmP p) s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.disj (by vlayd),L.disj (by vlayd),hc.bound,ht.bound,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  exact ready

theorem inverse_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (_hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (scale montgomeryRInv (Diff p σ A' c0 r))) :
    Inverse.InverseSingleReady (wP p) s := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have wr : inB (vW p) (wP p) 1024=true := by vlayd
  have held : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED") := by
    intro j hj
    have eq (xs : List (BitVec 64)) (j : Nat) (hj : j<xs.length) : xs.getD j 0=xs[j]! := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some,getElem!_pos xs j hj]
    exact (hs.roots.inverse.held j hj).trans (eq _ _ (by rw [InverseTable.expandedWords_length];exact hj))
  have ready : Inverse.InverseSingleReady (wP p) s :=
    ⟨held,hs.roots.inverse.apart_write (L.inW wr),hw.1,
      Covers.cons hs.roots.inverse.readable (L.cR rd),L.cW wr⟩
  exact ready

theorem hintPack_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r)) :
    UseHintPack.CallReady (rowP p r) (hP p r) (wP p) p.γ₂ s := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hrow : w1Len p*r+w1Len p≤p.k*w1Len p := by
    rw [←Nat.mul_succ,Nat.mul_comm p.k];exact Nat.mul_le_mul_left _ hr
  have hkw:=hF.w1
  have ro : inB (vR p++vW p) (rowP p r) (w1Len p)=true := by
    rcases hF.wl with he|he <;> vlay [he]
  have ra : inB (vR p++vW p) (hP p r) 1024=true := by vlayd
  have rb : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have wo : inB (vW p) (rowP p r) (w1Len p)=true := by
    rcases hF.wl with he|he <;> vlay [he]
  have plen : UseHintPack.packLen p.γ₂=w1Len p := rfl
  have ready : UseHintPack.CallReady (rowP p r) (hP p r) (wP p) p.γ₂ s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,
      L.disj (by rw [plen];rcases hF.wl with he|he <;> vlay [he]),
      L.disj (by rw [plen];rcases hF.wl with he|he <;> vlay [he]),
      Round.isG_of_mem hF.g2.1,hw.1,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  exact ready

end VG.Proof.MlDsa.AArch64.Verify.Optimized
