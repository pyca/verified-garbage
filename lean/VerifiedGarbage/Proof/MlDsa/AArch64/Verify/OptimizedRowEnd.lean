import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSingleCallTiming

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Arith.Montgomery

abbrev Diff (p : Params) (σ : State) (A' : Nat→Nat→Poly) (c0 : Poly) (r : Nat) : Poly :=
  sub (rDot p σ A' r) (multiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))

theorem subtract_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PolyIs s.mem (pa s (tm2P p))
      (montgomeryMultiplyNTT (ntt c0) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.subtract p) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧
      PolyIs t.mem (pa t (wP p)) (scale montgomeryRInv (Diff p σ A' c0 r)) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : accChk (vR p) (vW p) (wP p) (tm2P p)=true := by unfold accChk;vlay
  have C : CalleeOk S (Impl.MlDsa.AArch64.Optimized.AddSub.code true) (subContract abi S) :=
    CalleeOk.of_verified L.s64 AddSub.sub_verified (Nat.zero_le _) (by change 0≤S;omega)
  refine WP.mono_syms (accAt_ok L.s64 C L hc hw.1 ht.1) fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;vlay) h24,?_⟩
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  rw [hw.2,ht.2] at hv
  rw [Diff,scale_sub]
  exact hv

theorem inverse_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (scale montgomeryRInv (Diff p σ A' c0 r))) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.inverse (wP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧
      PolyIs t.mem (pa t (wP p)) (Proof.MlDsa.Verify.wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r) := by
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
  refine WP.mono_syms (Inverse.inverseSingleAt_ok L.s64 (ptr_ok (L.ptrBs rd)) ready)
    fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(wP p,1024)] := hp'.b
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wr)
    (hp'.cs .x24 (by decide) (by decide)),?_⟩
  rw [hb.pa (L.ptrBs rd)]
  rw [hw.2,inv_cancel] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized
