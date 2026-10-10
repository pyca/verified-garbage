import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.UseHintPackCallTiming

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (wRow w1Row)

theorem hintPack_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s)
    (hw : PolyIs s.mem (pa s (wP p)) (wRow p (vPk p σ) (vSig p σ) A' (ntt c0) r)) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.hintPack p r) s (SC p S σ h A' c0 q p.ℓ true (r+1)) := by
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
  refine WP.mono_syms (UseHintPack.at_ok L.s64 (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) ready) fun t ⟨hp',hv⟩ hy=>?_
  have hb : PPostB S s t [(rowP p r,w1Len p)] := hp'.b
  have ht := hs.keep hF hp hb (by scchks hF (Nat.le_of_lt hr)) hy
    (fun w hm=>by obtain rfl:=List.mem_singleton.mp hm;exact wo)
    (hp'.cs .x24 (by decide) (by decide))
  refine ⟨ht.vc,ht.roots,ht.hh,ht.hint,ht.nok,ht.gd,ht.a,ht.z,ht.c,fun j hj=>?_,ht.x24⟩
  rcases (by omega : j<r∨j=r) with hj'|rfl
  · exact ht.rows j hj'
  · rw [hb.pa (L.ptrBs ro)]
    rw [hintRow_pa p s j,Proof.MlDsa.Verify.hintAt_row hs.hint hr,hw.2] at hv
    exact hv

end VG.Proof.MlDsa.AArch64.Verify.Optimized
