import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHintLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedHintRow
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ

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
