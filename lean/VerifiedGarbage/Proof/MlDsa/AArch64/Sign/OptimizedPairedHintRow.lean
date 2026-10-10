import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedHintCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintRow
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintState
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedHints

/-! ## From `OptimizedPairedHintLayout.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedHintReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) (roots : PairedRoots S s) {c secret y high work : Ptr} {gamma : Nat}
    (hc : inB (rbs++wbs) c 1024=true) (hs : inB (rbs++wbs) secret 2048=true)
    (hh : inB (rbs++wbs) high 2048=true)
    (hy : inB (rbs++wbs) y 2048=true) (hw : inB (rbs++wbs) work 2176=true)
    (hwy : inB wbs y 2048=true) (hww : inB wbs work 2176=true)
    (hcy : sepB rbs wbs c 1024 y 2048=true) (hcw : sepB rbs wbs c 1024 work 2176=true)
    (hsy : sepB rbs wbs secret 2048 y 2048=true) (hsw : sepB rbs wbs secret 2048 work 2176=true)
    (hyw : sepB rbs wbs y 2048 work 2176=true)
    (hyh : sepB rbs wbs y 2048 high 2048=true) (hhw : sepB rbs wbs high 2048 work 2176=true)
    (hprod : pairedProductsReduced s.mem (pa s c) (pa s secret))
    (hdata : ∀j<2,ResponseDecomposed s.mem (pairPolyPtr (pa s y) j) (pairPolyPtr (pa s high) j) gamma)
    (hg : gamma∈gamma2s) :
    Paired.PairedHintReady c secret y high work gamma s := by
  refine ⟨L.nwp hc,L.nwp hs,L.nwp hy,L.nwp hh,L.nwp hw,roots.held,roots.fit,?_,L.disj hcy,L.disj hcw,
    L.disj hsy,L.disj hsw,L.disj hyw,L.disj hyh,L.disj hhw,hprod,hg,hdata,?_,?_⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact roots.apart_write (L.inW hwy)
    · exact roots.apart_write (L.inW hww)
  · exact Covers.cons (L.cR hc) (Covers.cons (L.cR hs)
      (Covers.cons (L.cR hh) (Covers.cons roots.readable (Covers.cons (L.cR hy) (L.cR hw)))))
  · exact Covers.cons (L.cW hwy) (L.cW hww)

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedHintField.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr callAt)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedHintPoly_field {m : Mem} {c secret low high : Addr} {gamma j : Nat} {f ch sk : Poly}
    (hg : gamma∈gamma2s) (hc : PosPolyIs m c ch) (hs : PosPolyIs m (pairPolyPtr secret j) sk)
    (hl : SignedPolyIs m (pairPolyPtr low j) (f.map fun r=>ofInt (lowBits gamma r)) (-(gamma:Int)) gamma)
    (hh : NatPolyIs m (pairPolyPtr high j) (f.map fun r=>(highBits gamma r).toNat)) :
    pairedHintPoly m c secret low high gamma j=
      Vector.zipWith (fun ci fi=>makeHint gamma (-ci) (fi+ci)) (nttInv (multiplyNTT ch sk)) f := by
  have hg' := VG.Proof.MlDsa.AArch64.Round.isG_of_mem hg
  apply Vector.ext
  intro i hi
  simp only [pairedHintPoly,Vector.getElem_ofFn,Vector.getElem_zipWith,pairedProduct,hc.value,hs.value]
  rw [Response.responseHintBase_parts hg' (Response.hintLow_exact hg' hl i hi) (Response.hintHigh_exact hh i hi)]
  simp only [getElem!_pos f i hi,getElem!_pos (nttInv (multiplyNTT ch sk)) i hi]

theorem pairedHintAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {c secret low high work : Ptr} {g : Nat} {f sk : Nat → Poly} {ch : Poly}
    (hc : inB (rbs++wbs) c 1024=true) (hs : inB (rbs++wbs) secret 2048=true)
    (hl : inB (rbs++wbs) low 2048=true) (hh : inB (rbs++wbs) high 2048=true)
    (hw : inB (rbs++wbs) work 2176=true) (h : Paired.PairedHintReady c secret low high work g s)
    (hch : PosPolyIs s.mem (pa s c) ch)
    (hsk : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s secret) j) (sk j))
    (hlo : ∀j<2,SignedPolyIs s.mem (pairPolyPtr (pa s low) j)
      ((f j).map fun r=>ofInt (lowBits g r)) (-(g:Int)) g)
    (hhi : ∀j<2,NatPolyIs s.mem (pairPolyPtr (pa s high) j) ((f j).map fun r=>(highBits g r).toNat)) :
    WP isa (callAt "vg_mldsa_fused_pair_h" (VG.Impl.MlDsa.AArch64.Optimized.Paired.selected .h)
      (Paired.pairedHintArgs c secret low high work g)) s fun t =>
      let hints := (List.range 2).map fun j => Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci))
        (nttInv (multiplyNTT ch (sk j))) (f j)
      PPostB S s t [(low,2048),(work,2176)] ∧ t.gpr .x24=s.gpr .x24 ∧
      HintIs t.mem (pa s low) 2 hints ∧
      t.gpr .x0=BitVec.ofNat 64 (hintOnes hints+
        if normRq ((List.range 2).map fun j => nttInv (multiplyNTT ch (sk j)))<g then 4294967296 else 0) := by
  refine WP.mono (Paired.pairedHintAt_ok L.s64 (ptr_ok (L.ptrBs hc)) (ptr_ok (L.ptrBs hs))
    (ptr_ok (L.ptrBs hl)) (ptr_ok (L.ptrBs hh)) (ptr_ok (L.ptrBs hw)) h) fun t ⟨hp,hout,hret⟩ => ?_
  have he : ((List.range 2).map fun j=>pairedHintPoly s.mem (pa s c) (pa s secret) (pa s low) (pa s high) g j)=
      (List.range 2).map (fun j=>Vector.zipWith (fun ci fi=>makeHint g (-ci) (fi+ci)) (nttInv (multiplyNTT ch (sk j))) (f j)) := by
    apply List.map_congr_left
    intro j hj
    exact pairedHintPoly_field h.gammaOk hch (hsk j (List.mem_range.mp hj)) (hlo j (List.mem_range.mp hj)) (hhi j (List.mem_range.mp hj))
  have ep : ((List.range 2).map fun j=>pairedProduct s.mem (pa s c) (pa s secret) j)=
      (List.range 2).map (fun j=>nttInv (multiplyNTT ch (sk j))) := by
    apply List.map_congr_left
    intro j hj
    simp only [pairedProduct,hch.value,(hsk j (List.mem_range.mp hj)).value]
  rw [he] at hout hret
  rw [ep] at hret
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hout,hret⟩

theorem hintIs_pair {m : Mem} {a : Addr} {f : Nat → Vector Bool n}
    (h : HintIs m a 2 ((List.range 2).map f)) {j : Nat} (hj : j<2) :
    HintIs m (pairPolyPtr a j) 1 [f j] := by
  refine ⟨rfl,?_⟩
  intro i hi k hk
  have ei : i=0 := by omega
  subst i
  have he := h.2 j hj k hk
  simp only [Nat.mul_zero,Nat.zero_add,List.getD_cons_zero] at *
  rw [VG.Proof.MlDsa.Sign.getD_range f hj (Vector.replicate n false)] at he
  have addr : pairPolyPtr a j+BitVec.ofNat 64 (4*k)=a+BitVec.ofNat 64 (4*(256*j+k)) := by
    simp only [pairPolyPtr,BitVec.add_assoc,←BitVec.ofNat_add]
    congr 2
    omega
  simpa only [coeffAt,addr] using he

theorem hintOnes_pair (f : Nat → Vector Bool n) :
    hintOnes ((List.range 2).map f)=hintOnes [f 0]+hintOnes [f 1] := by
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,List.nil_append]
  simp only [hintOnes,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedHintRow.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

def pairedHintWrites (i : Nat) : List (Ptr × Nat) := [(hP i,2048),(t1P,2176)]

def pairedHintRowChk (p : Params) (i : Nat) : Bool :=
  inB (sgB p) cP 1024 && inB (sgB p) (t0P p i) 2048 && inB (sgB p) (hP i) 2048 &&
  inB (sgB p) (wP p i) 2048 && inB (sgB p) t1P 2176 &&
  inB (sgW p) (hP i) 2048 && inB (sgW p) t1P 2176 &&
  sepB (sgR p) (sgW p) cP 1024 (hP i) 2048 && sepB (sgR p) (sgW p) cP 1024 t1P 2176 &&
  sepB (sgR p) (sgW p) (t0P p i) 2048 (hP i) 2048 && sepB (sgR p) (sgW p) (t0P p i) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (hP i) 2048 t1P 2176 &&
  sepB (sgR p) (sgW p) (hP i) 2048 (wP p i) 2048 && sepB (sgR p) (sgW p) (wP p i) 2048 t1P 2176 &&
  decide (p.γ₂∈gamma2s)

theorem pairedHintRowChk_ok {p : Params} (hp : Ok3 p) : ∀i<p.k,i+1<p.k → pairedHintRowChk p i=true := by
  rcases hp with rfl|rfl|rfl <;> decide

theorem pairedHint_inputs {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hi : i+1<p.k) (h : PositiveIH p S σ t i s) :
    (∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (t0P p i)) j) (T0v p σ (i+j))) ∧
    (∀j<2,SignedPolyIs s.mem (pairPolyPtr (pa s (hP i)) j)
      ((W'v p σ (p.ℓ*t) (i+j)).map fun r=>ofInt (lowBits p.γ₂ r)) (-(p.γ₂:Int)) p.γ₂) ∧
    (∀j<2,NatPolyIs s.mem (pairPolyPtr (pa s (wP p i)) j)
      ((W'v p σ (p.ℓ*t) (i+j)).map fun r=>(highBits p.γ₂ r).toNat)) := by
  refine ⟨?_,?_,?_⟩
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.1.b.l.k.d.t0 (i+j) (by omega)
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc,R0v,W'v,VG.Proof.MlDsa.Sign.r0F] using h.1.low j (by omega)
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc,WHighv] using h.1.high (i+j) (by omega)

theorem pairedHint_ready {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIH p S σ t i s) :
    Paired.PairedHintReady cP (t0P p i) (hP i) (wP p i) t1P p.γ₂ s := by
  have checks := pairedHintRowChk_ok hp i (by omega) hi
  simp only [pairedHintRowChk,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hl⟩,hh⟩,hw⟩,hwl⟩,hww⟩,hcl⟩,hcw⟩,hsl⟩,hsw⟩,hlw⟩,hlh⟩,hhw⟩,hg⟩ := checks
  obtain ⟨hsk,hlo,hhi⟩ := pairedHint_inputs hi h
  refine pairedHintReady_layout h.1.b.l.st.lay roots hc hs hh hl hw hwl hww hcl hcw hsl hsw hlw hlh hhw
    ⟨h.1.b.c.bound,fun j hj => (hsk j hj).bound⟩ (fun j hj=>?_) hg
  have hg' := VG.Proof.MlDsa.AArch64.Round.isG_of_mem hg
  exact Response.responseDecomposed_parts hg' _ (Response.hintLow_exact hg' (hlo j hj)) (Response.hintHigh_exact (hhi j hj))

theorem pairedHintRow_ok {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIH p S σ t i s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.hintPairRow p i) s fun a =>
      PPostB S s a (pairedHintWrites i) ∧ a.gpr .x24=s.gpr .x24 ∧
      HintIs a.mem (pa s (hP i)) 2 ((List.range 2).map fun j=>Hv p σ (p.ℓ*t) (i+j)) ∧
      a.gpr .x0=BitVec.ofNat 64 (hintOnes ((List.range 2).map fun j=>Hv p σ (p.ℓ*t) (i+j))+
        if normRq ((List.range 2).map fun j=>CT0v p σ (p.ℓ*t) (i+j))<p.γ₂ then 4294967296 else 0) := by
  have checks := pairedHintRowChk_ok hp i (by omega) hi
  simp only [pairedHintRowChk,Bool.and_eq_true,decide_eq_true_eq] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hl⟩,hh⟩,hw⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩ := checks
  obtain ⟨hsk,hlo,hhi⟩ := pairedHint_inputs hi h
  refine WP.mono (pairedHintAt_field_layout h.1.b.l.st.lay hc hs hl hh hw
    (pairedHint_ready hp hi roots h) h.1.b.c hsk hlo hhi) fun a ⟨ha,h24,hints,ret⟩ => ?_
  change HintIs a.mem _ 2 ((List.range 2).map fun j=>Vector.zipWith _ (CT0v p σ (p.ℓ*t) (i+j)) (W'v p σ (p.ℓ*t) (i+j))) at hints
  change a.gpr .x0=BitVec.ofNat 64 (hintOnes ((List.range 2).map fun j=>Vector.zipWith _
    (CT0v p σ (p.ℓ*t) (i+j)) (W'v p σ (p.ℓ*t) (i+j)))+_) at ret
  simp only [hintRow_value] at hints ret
  exact ⟨ha,h24,hints,ret⟩

end VG.Proof.MlDsa.AArch64.Sign

end
