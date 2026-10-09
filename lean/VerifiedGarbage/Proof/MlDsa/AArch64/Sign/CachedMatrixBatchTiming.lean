import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixBatch

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Sign

theorem seeds2 {p : Params} {D : Nat} {σ s : State} {e : Nat} (h : AS p D σ e 2 s) :
    bytesAt s.mem (pa s (sc oRS4)) 68=seedE p σ (e+0)++seedE p σ (e+1) := by
  have h0 := aseeds2_eq h (show 0<2 by decide)
  have h1 := aseeds2_eq h (show 1<2 by decide)
  unfold seed4 at h0 h1
  rw [show 68=34+34 from rfl,VG.Proof.MlKem.bytesAt_add]
  simp only [Nat.mul_zero,Nat.mul_one,VG.Proof.MlKem.AArch64.ptr_zero] at h0 h1
  rw [h0,h1]

theorem twoBatch_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {e : Nat} (hc : twoChk p e = true) :
    RelCT isa (RR p D (AS p D · e 2) fun x y => x.gpr .x24 = y.gpr .x24)
      (.seq (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args (sc oRS4) (pS (aBase p+e)) (sc (oR4 p)))) (.block and24))
      (RA p D (e+2)) := by
  have hc' := hc
  simp only [twoChk,Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨cr,_⟩,_⟩,_⟩,_⟩ := hc'
  refine stepRR (F := fun _ _ => True) (fun _ _ _ h => WP.mono (twoBatch_ok hP hc h) fun _ ht => ⟨ht,trivial⟩) ?_
    (fun _ _ _ _ _ _ _ h => h)
  have calltr : RelCT isa (RR p D (AS p D · e 2) fun x y => x.gpr .x24 = y.gpr .x24)
      (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args (sc oRS4) (pS (aBase p+e)) (sc (oR4 p))))
      (fun x y => LRel D (sgR p) (sgW p) x y ∧ x.gpr .x24 = y.gpr .x24 ∧ (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32) := by
    refine postDepQ (fun x y t1 t2 x' y' h e1 e2 =>
      rej2At_trRet hP.s64 (h.lrel fun _ _ h => h.ia.st).ok cr ?_ x y t1 t2 x' y' h e1 e2)
      (F := fun s t => PPostB D s t [(pS (aBase p+e),2048),(sc (oR4 p),8192)] ∧ t.gpr .x24 = s.gpr .x24)
      ?_ ?_
    · intro x y h
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨L.lx,L.ly,?_,L.same⟩
      obtain ⟨⟨σ1,σ2,_,_,pub,h1,h2⟩,_⟩ := h
      rw [seeds2 h1,seeds2 h2]
      simp only [seedE,pub_rho pub]
    · intro x y h
      obtain ⟨⟨σ1,σ2,_,_,_,h1,h2⟩,_⟩ := h
      exact ⟨WP.mono (rej2Call_ok hP.s64 h1.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩),
        WP.mono (rej2Call_ok hP.s64 h2.ia.st.lay cr) (fun _ ht => ⟨ht.1,ht.2.1⟩)⟩
    · intro x y x' y' h hx hy hr
      have L := h.lrel fun _ _ h => h.ia.st
      refine ⟨⟨L.lx.post hx.1,L.ly.post hy.1,fun r hr => ?_,?_,L.ok⟩,by rw [hx.2,hy.2,h.2],hr⟩
      · rw [hx.1.bs r (bases_kept r hr),hy.1.bs r (bases_kept r hr)]; exact L.regs r hr
      · rw [hx.1.sp,hy.1.sp]; exact L.sp
  refine RelCT.seq calltr (RelCT.postDep (lrel_tr (fun _ _ h => h.1) (by taint_decide))
    (F := fun s t => t.gpr .x24 = BitVec.setWidth 64 ((s.gpr .x24).setWidth 32 &&& (s.gpr .x0).setWidth 32))
    (fun x y _ => ⟨WP.mono (and24_ok x) (fun _ h => h.2),WP.mono (and24_ok y) (fun _ h => h.2)⟩)
    fun x y x' y' h hx hy => by rw [hx,hy,h.2.1,h.2.2])


end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
