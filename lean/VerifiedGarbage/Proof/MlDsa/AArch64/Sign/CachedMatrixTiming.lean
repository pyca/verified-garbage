import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixBatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedMatrixRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedSignTiming

/-! ## From `CachedMatrixCallTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej
open VG.Spec.Sha3 (bytesAt)

theorem two_ret {S : Nat} (hS : S<2^64) : RetPub (rejNTT2Contract abi S) Two.code := by
  intro x y tx ty x' y' ⟨hx,hy,hpub⟩ ex ey
  have px := pre_two (pre_stack (Nat.zero_le S) hS hx)
  have py := pre_two (pre_stack (Nat.zero_le S) hS hy)
  have pub : Pub 2 x y := by
    sig_pub [rejNTT2Contract,rejNTT2Sig,abi,argRegs] at hpub
    obtain ⟨hsp,hb,h0,h1,h2⟩ := hpub
    exact ⟨h0,h1,h2,hsp,VG.Proof.MlKem.map_toNat_inj hb⟩
  refine ⟨two_ct _ _ _ _ _ _ px py pub ex ey,?_⟩
  obtain ⟨_,u,eu,hu⟩ := two_ok px
  obtain ⟨_,v,ev,hv⟩ := two_ok py
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  have he : (∀k<2,(prefixRow x k 1008).length=256) ↔ ∀k<2,(prefixRow y k 1008).length=256 := by
    constructor
    · intro h k hk; rw [←pub.prefix hk]; exact h k hk
    · intro h k hk; rw [pub.prefix hk]; exact h k hk
  rw [hu.status,hv.status]
  by_cases h : ∀k<2,(prefixRow x k 1008).length=256
  · simp only [ite_eq_left h,ite_eq_left (he.mp h)]
  · simp only [ite_eq_right h,ite_eq_right (fun hy=>h (he.mpr hy))]

theorem rej2At_trRet {S : Nat} (hS : S<2^64)
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {seed a ss : Ptr} (hc : rej2Chk rbs wbs seed a ss = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧
      bytesAt x.mem (pa x seed) 68 = bytesAt y.mem (pa y seed) 68 ∧ SameB x y) :
    RelCT isa Q (callAt "vg_mldsa_rej_ntt_poly2_sha3" Two.code (rej2Args seed a ss))
      fun s₁ s₂ => (s₁.gpr .x0).setWidth 32 = (s₂.gpr .x0).setWidth 32 := by
  have hc' := hc
  simp only [rej2Chk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : seed.1 ∈ bases ∧ a.1 ∈ bases ∧ ss.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_trRet (callee hS) (two_ret hS) (rej2_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, hsd, e⟩ := hQ x y hp
  refine ⟨_, _, rej2_pre Lx hc h1, ?_, ?_, (rej2_cov Lx hc).1, (rej2_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact rej2_pre Ly hc h2
  · sig_pub [rejNTT2Contract, rejNTT2Sig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2,
      Args.mem h1, Args.mem h2]
    simp only [Arg.val]
    exact ⟨e.2, by rw [hsd], e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (rej2_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end

/-! ## From `CachedMatrixBatchTiming.lean` -/

section

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

end

/-! ## From `CachedMatrixTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedMatrix
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call
open VG.Proof.MlDsa.Sign

theorem tail_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) :
    RelCT isa (RA mlDsa65 D 28) (Impl.MlDsa.AArch64.Sign.CachedMatrix.tail mlDsa65)
      (RA mlDsa65 D 30) := by
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.tail
  rw [show 4*(mlDsa65.k*mlDsa65.ℓ/4)=28 by decide]
  refine RelCT.seq (RelCT.mono (seqR_tr
    (Q:=fun j=>RR mlDsa65 D (AS mlDsa65 D · 28 j) fun x y=>x.gpr .x24=y.gpr .x24) 2 0
    (fun j _ hj=>slot4_tr (by omega)
      (slotChk_ok mlDsa65 (by simp) 28 (by decide) j (by omega)))) ?_ (fun _ _ h=>by simpa using h))
    (twoBatch_tr hP (show twoChk mlDsa65 28=true by decide))
  exact fun x y h=>h.mono (fun _ _ h=>⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩) (fun h=>h)

theorem expandA65_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) (hc : aChk mlDsa65 = true) :
    RelCT isa (RR mlDsa65 D (fun σ s => St mlDsa65 D σ s ∧ s.gpr .x24 = 1) fun _ _ => True)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P mlDsa65) (RA mlDsa65 D (mlDsa65.k * mlDsa65.ℓ)) := by
  have hp : mlDsa65 ∈ [mlDsa44,mlDsa65,mlDsa87] := by simp
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
  rw [ite_eq_left (by decide)]
  refine RelCT.seq (R := RA mlDsa65 D 0) (stepRR (F := fun s s' => s'.gpr .x24 = s.gpr .x24) (J := fun σ s => IA mlDsa65 D σ 0 s)
    (E' := fun x y => x.gpr .x24 = y.gpr .x24)
    (fun σ s _ h => ?_) (lrel_tr (fun x y h => h.lrel fun _ _ h => h.1) (by taint_decide))
    fun x y x' y' h fx fy _ => ?_) ?_
  · refine WP.mono (copyP_ok h.1.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ⟨?_, hcs1.get .x24⟩
    have S1 := h.1.step hP1 hst
    have e15 : s1.gpr .x24 = 1 := by rw [hcs1.get .x24, h.2]
    exact ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← h.1.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
      .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
      fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  · obtain ⟨⟨σ₁, σ₂, _, _, _, ⟨_, h₁⟩, ⟨_, h₂⟩⟩, _⟩ := h
    rw [fx, fy, h₁, h₂]
  · have hB : RelCT isa (RA mlDsa65 D 0) (seqR (sample4 P mlDsa65) 0 7) (RA mlDsa65 D 28) := by
      simpa only [Nat.zero_add,Nat.mul_zero] using
        (seqR_tr (Q:=fun g=>RA mlDsa65 D (4*g)) 7 0 (fun g _ hg=>
          sample4_tr hP (batchChk_ok mlDsa65 hp g (by change g<7; omega))
            (fun j hj=>slotChk_ok mlDsa65 hp (4*g) (by change 4*g<30; omega) j hj)))
    exact RelCT.seq hB (tail_tr hP)

theorem expandA_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params}
    (hp : Ok3 p) (hc : aChk p=true) :
    RelCT isa (RR p D (fun σ s=>St p D σ s ∧ s.gpr .x24=1) fun _ _=>True)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) (RA p D (p.k*p.ℓ)) := by
  rcases hp with rfl|rfl|rfl
  · exact Sign.expandA_tr hP (.inl rfl) hc
  · exact expandA65_tr hP hc
  · exact Sign.expandA_tr hP (.inr (.inr rfl)) hc

theorem positiveExpand_tr {P : Prims} {p : Params} {D : Nat} (hP : PrimsOk P D) (hp : Ok3 p) :
    RelCT isa (RR p D (fun σ s=>RootedSt p D σ s ∧ s.gpr .x24=1) RootSymbolsEq)
      (Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA P p) (PositiveRA p D) := by
  have ha := aChk_ok hp
  intro x y tx ty x' y' h ex ey
  have old : RR p D (fun σ s=>St p D σ s ∧ s.gpr .x24=1) (fun _ _=>True) x y := h.mono (fun _ _ h=>⟨h.1.1,h.2⟩) (fun _=>trivial)
  obtain ⟨tr,out⟩ := expandA_tr hP hp ha _ _ _ _ _ _ old ex ey
  obtain ⟨⟨σ,τ,_,_,_,hx,hy⟩,re⟩ := h
  obtain ⟨_,u,eu,_,ru⟩ := rooted_expandA_ok hP hp ha hx.1 hx.2
  obtain ⟨_,v,ev,_,rv⟩ := rooted_expandA_ok hP hp ha hy.1 hy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨tr,out,ru,rv,by
    simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using re⟩


end VG.Proof.MlDsa.AArch64.Sign.CachedMatrix

end
