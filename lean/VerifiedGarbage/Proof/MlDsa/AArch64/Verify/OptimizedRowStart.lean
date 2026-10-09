import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedDot
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedNtt

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized

abbrev W (p : Params) (σ : State) (A' : Nat→Nat→Poly) (r : Nat) (s : State) : Prop :=
  PolyIs s.mem (pa s (wP p)) ((rDot p σ A' r).map (·*montgomeryRInv))

theorem unpack_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A' : Nat→Nat→Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s) :
    WP isa (unpackT1At P (.x25,32+320*r) (tmP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧ PolyIs t.mem (pa t (tmP p)) (rU p σ r) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr;have hpk:=hF.pk
  have hc : rwChk (vR p) (vW p) (.x25,32+320*r) 320 (tmP p) 1024=true := by unfold rwChk;vlay
  refine WP.mono_syms (t1At_ok hP.s64 hP.unpackT1 L hc) fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;vlay) h24,
    L.keepPoly hb (by vlay) hw,?_⟩
  rw [hs.vc.pkSlice (by rw [hF.pk];omega)] at hv
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  exact hv

theorem nttT_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) (hw : W p σ A' r s)
    (ht : PolyIs s.mem (pa s (tmP p)) (rU p σ r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.forward (tmP p)) s fun t=>
      SC p S σ h A' c0 q p.ℓ true r t ∧ W p σ A' r t ∧
      PosPolyIs t.mem (pa t (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r) := by
  have L:=hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (tmP p) 1024=true := by vlay
  have wr : inB (vW p) (tmP p) 1024=true := by vlay
  refine WP.mono_syms (Sign.positiveNttAt_layout L rd wr
    ⟨hs.roots.nttTableAt (L.inW wr),hs.roots.forward.readable⟩ ht.1)
    fun t ⟨hb,h24,hv⟩ hy=>?_
  refine ⟨hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wr) h24,
    L.keepPoly hb (by vlay) hw,?_⟩
  rw [hb.pa (show Reg.x28∈keptRegs by decide)]
  rw [ht.2] at hv
  exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized
