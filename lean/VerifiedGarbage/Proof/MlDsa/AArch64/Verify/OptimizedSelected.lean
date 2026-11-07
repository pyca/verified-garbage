module

public import VerifiedGarbage.Proof.MlDsa.AArch64.PreparedKey.VerifyKeyRow

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Spec.MlDsa.CachedVerify

import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inst
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Final
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Optimized
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedState
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedHintPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowEnd
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowProduct
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedDot
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedTimingBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSingleCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowReady
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MontDotCallTiming
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Lay
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSat
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashMu
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.HashCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifySat
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MatrixMask
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCallTwo
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp4
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesFourTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesTwo
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedSamples
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedSamplesBall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Hash
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

/-- The final phase preserves public table addresses even though its semantic
postcondition no longer needs table contents. -/
theorem finish_rootPair {S : Nat} (h16 : 16≤S) (hS : S<2^64) {p : Params} (hF : VFacts p) :
    RelCT isa (RootPair p S (SCx p S p.ℓ true p.k))
      (.seq (shake256With keccak.callee (hIns p) [⟨.x28,oCT,p.ctildeLen⟩])
        (cmpAnd (sc oCT) (.x27,0) p.ctildeLen))
      (RootPair p S (VFin p)) := by
  have h := finish_vpiece (keccak:=keccak) h16 hS hF
  exact rootPair_progress h.ok (RelCT.mono h.tr (fun _ _ h=>h.1) (fun _ _ _=>trivial))

end VG.Proof.MlDsa.AArch64.Verify.Optimized

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedNttTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Verify.Optimized
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Call (Ptr)

theorem forward_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State}
    (hp : vPre p S σ) {a : Ptr} (hc : VC p σ s) (roots : Sign.StaticRoots S s)
    (hr : inB (vR p++vW p) a 1024=true) (hw : inB (vW p) a 1024=true)
    (red : Reduced s.mem (pa s a)) : NttCallReady a s := by
  have L := hc.lay hF hp
  exact ⟨L.nwp hr,roots.nttTableAt (L.inW hw),red,
    Covers.cons roots.forward.readable (L.cR hr),L.cW hw⟩

theorem nttZ_tr {p : Params} (hF : VFacts p) {S i : Nat} (hi : i<p.ℓ) :
    RelCT isa (RootPair p S (SCx p S i false 0)) (forward (zP p i))
      (RootPair p S (SCx p S (i+1) false 0)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs⟩=>
    WP.mono (nttZ_ok hF hp hi hs) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  unfold forward
  apply positiveNttAt_tr (S := S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx⟩,⟨h',A',c',q',hy⟩⟩,et⟩ := hh
  have H := vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hr : inB (vR p++vW p) (zP p i) 1024=true := by vlayd
  have hw : inB (vW p) (zP p i) 1024=true := by vlayd
  have red {σ s : State} {h A c q} (hs : SC p S σ h A c q i false 0 s) :
      Reduced s.mem (pa s (zP p i)) := by
    have hz:=hs.z i hi
    simp only [Stored,decide_eq_false_iff_not.mpr (Nat.lt_irrefl i),Bool.false_eq_true,↓reduceIte] at hz
    exact hz.1
  exact ⟨forward_ready hF hσ hx.vc hx.roots hr hw (red hx),
    forward_ready hF hτ hy.vc hy.roots hr hw (red hy),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩

theorem nttC_tr {p : Params} (hF : VFacts p) {S : Nat} :
    RelCT isa (RootPair p S (SCx p S p.ℓ false 0)) (forward (cP p))
      (RootPair p S (SCx p S p.ℓ true 0)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs⟩=>
    WP.mono (nttC_ok hF hp hs) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  unfold forward
  apply positiveNttAt_tr (S := S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx⟩,⟨h',A',c',q',hy⟩⟩,et⟩ := hh
  have H := vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hr : inB (vR p++vW p) (cP p) 1024=true := by vlayd
  have hw : inB (vW p) (cP p) 1024=true := by vlayd
  exact ⟨forward_ready hF hσ hx.vc hx.roots hr hw hx.c.1,
    forward_ready hF hτ hy.vc hy.roots hr hw hy.c.1,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRowState.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized VG.Proof.MlDsa.Arith.Montgomery

abbrev RowData (p : Params) (σ : State) (A : Nat→Nat→Poly) (c : Poly) (r stage : Nat) (s : State) : Prop :=
  match stage with
  | 0 => W p σ A r s
  | 1 => W p σ A r s ∧ PolyIs s.mem (pa s (tmP p)) (rU p σ r)
  | 2 => W p σ A r s ∧ PosPolyIs s.mem (pa s (tmP p)) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r)
  | 3 => W p σ A r s ∧ PolyIs s.mem (pa s (tm2P p))
      (montgomeryMultiplyNTT (ntt c) (Proof.MlDsa.Verify.t1Hat (vPk p σ) r))
  | 4 => PolyIs s.mem (pa s (wP p)) (scale montgomeryRInv (Diff p σ A c r))
  | _ => PolyIs s.mem (pa s (wP p)) (Proof.MlDsa.Verify.wRow p (vPk p σ) (vSig p σ) A (ntt c) r)

abbrev RowI (p : Params) (S r stage : Nat) (σ s : State) : Prop :=
  ∃h A c q,SC p S σ h A c q p.ℓ true r s ∧ RowData p σ A c r stage s

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedPiece.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call

structure Piece (p : Params) (S : Nat) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, vPre p S σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (RootPair p S I) c fun _ _ => True

theorem Piece.of_vpiece {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (h : VPiece p S I J c) : Piece p S I J c :=
  ⟨h.ok, h.tr.mono (fun _ _ h=>h.1) (fun _ _ h=>h)⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedSamplesTwoTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem vseeds2 {p : Params} {σ : State} {e : Nat} {s : State} (h : VS p σ e 2 s) :
    bytesAt s.mem (pa s (sc oSA4)) 68=seedOf p σ e++seedOf p σ (e+1) := by
  rw [show 68=34+34 from rfl,Proof.MlKem.bytesAt_add]
  have h0 := vseed2_eq h (k := 0) (by decide)
  have h1 := vseed2_eq h (k := 1) (by decide)
  simp only [Proof.MlDsa.seed4,Nat.mul_zero,Nat.add_zero,Nat.mul_one,
    VG.Proof.MlKem.AArch64.ptr_zero] at h0 h1
  rw [h0,h1]

theorem vcall2_piece {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Proof.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : VFacts p)
    {e : Nat} (he : e+2 ≤ p.k*p.ℓ) : VPiece p S (VS p · (e) 2) (VA p · (e+2))
      (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p)))) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => vcall2_ok hS C hF hp he h,
    vrel_of (Q := fun x y => VTwo p S x y ∧ bytesAt x.mem (pa x (sc oSA4)) 68 = bytesAt y.mem (pa y (sc oSA4)) 68) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨vc_two hF hp hp' hq h.va.vz.vc h'.va.vz.vc,by
        rw [vseeds2 h,vseeds2 h']; simp only [seedOf,(vPub_eq hq).2.1]⟩)⟩
  have hc : rej2Chk (vR p) (vW p) (sc oSA4) (aP (e)) (sc (oR4 p)) = true := by unfold rej2Chk; vlayd
  have ok := fun x (L : Lay S (vR p) (vW p) x) => WP.mono (rej2At_ok hS C L (nm := nm) hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  have tail : RelCT isa (VTwo p S) (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512)) fun _ _ => True := by
    refine RelCT.seq (VTwo.step (fun _ _ h => h) (block_nomem_tr fun i hi _ => by
      simp only [and24,List.mem_singleton] at hi; subst hi; rfl) ?_)
      (taintRel [.x28] (fun _ _ h => VTwo.x28 h) (matrixMask_taint (e) (by omega) 512 (by simp)))
    have f := fun z => WP.mono (and24_ok z) fun z' ⟨o,_⟩ =>
      (⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩ : ∃ W,PostB S z z' W)
    exact fun x y _ => ⟨f x,f y⟩
  exact RelCT.seq (VTwo.step (fun _ _ h => h.1)
    (rej2At_tr (nm := nm) C (vOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) tail

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedSamples.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params)

private theorem twoCallee {S : Nat} (hS : S<2^64) :
    CalleeOk S VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code
      (VG.Proof.MlDsa.rejNTT2Contract abi S) :=
  CalleeOk.of_verified hS VG.Proof.MlDsa.AArch64.Optimized.ResidentRej.two_verified
    (Nat.zero_le _) (by
      have hd : VG.Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code.aarch64Depth=0 := by decide +kernel
      simp only [hd,Nat.mul_zero]; exact Nat.zero_le _)

theorem tail2_vpiece {S : Nat} (hS : S<2^64) {p : Params} (hF : VFacts p)
    (hmod : p.k*p.ℓ%4=2) :
    VPiece p S (VA p · (4*(p.k*p.ℓ/4))) (VA p · (4*(p.k*p.ℓ/4)+2))
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2 p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.tail2
  refine VPiece.seq (VPiece.mono
    (VPiece.seqR (I := fun j σ s=>VS p σ (4*(p.k*p.ℓ/4)) j s) 2 0
      (fun j _ hj=>vslot2_piece hF (by omega) (by omega)))
    (fun _ _ _ h=>⟨h,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩)
    (fun _ _ _ h=>by simpa using h)) (vcall2_piece hS (twoCallee hS) hF (by omega))

theorem expAll_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (VA p · 0) (VA p · (p.k*p.ℓ))
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll P p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expAll
  have hB : VPiece p S (VA p · 0) (VA p · (4*(p.k*p.ℓ/4)))
      (seqR (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.expA4 P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero] using
      (VPiece.seqR (I := fun g σ s=>VA p σ (4*g) s) (p.k*p.ℓ/4) 0
        (fun g _ hg=>expA4_vpiece hP hF (by omega)))
  split
  · rename_i he
    refine VPiece.mono (VPiece.seq hB (tail2_vpiece hP.s64 hF he))
      (fun _ _ _ h=>h) (fun _ _ _ h=>?_)
    have eq : 4*(p.k*p.ℓ/4)+2=p.k*p.ℓ := by omega
    simpa only [eq] using h
  · refine VPiece.mono (VPiece.seq hB
      (VPiece.seqR (I := fun e σ s=>VA p σ e s) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
        (fun e _ he=>expA_vpiece hP hF (by omega)))) (fun _ _ _ h=>h) (fun _ _ _ h=>?_)
    have eq : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4=p.k*p.ℓ := by omega
    simpa only [eq] using h

theorem samples_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (fun σ s=>Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) (VB p)
      (VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) := by
  unfold VG.Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples
  exact (copyRho_vpiece hF).seq ((expAll_vpiece hP hF).seq
    ((ballCall_vpiece hP hF).seq (ballTail_vpiece hF)))

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedSamplesRoots.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots)
open VG.Proof.MlDsa.AArch64.Verify.Optimized (RootPair rootPair_progress)

/-- A bounded phase retains the immutable transform roots without making
any sampled coefficients or SHAKE states public. -/
theorem rooted_piece {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (h : VPiece p S I J c) (hd : 16*c.aarch64Depth≤S) (hS : S<2^64) :
    VPiece p S (fun σ s=>I σ s ∧ StaticRoots S s) (fun σ s=>J σ s ∧ StaticRoots S s) c := by
  refine ⟨fun σ s hp hs=>hs.2.phase hd hS (h.ok σ s hp hs.1),?_⟩
  exact RelCT.mono h.tr
    (fun _ _ ⟨σ,τ,hσ,hτ,pub,ix,iy⟩=>⟨σ,τ,hσ,hτ,pub,ix.1,iy.1⟩)
    (fun _ _ _=>trivial)

/-- Sampling preserves both root tables while retaining the existing exact
success/failure and rejection-transcript semantics. -/
theorem samples_rooted_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S)
    {p : Params} (hF : VFacts p) :
    VPiece p S
      (fun σ s=>(Z0 p p.ℓ σ s ∧ normOk p σ p.ℓ) ∧ StaticRoots S s)
      (fun σ s=>VB p σ s ∧ StaticRoots S s)
      (Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples P p) :=
  rooted_piece (samples_vpiece hP hF) (samples_depth hP p) hP.s64

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSamples
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedVectors.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen

theorem vb_sc {p : Params} {S : Nat} {σ s : State} (h : VB p σ s) (ht : Sign.StaticRoots S s) :
    SCx p S 0 false 0 σ s := by
  obtain ⟨hh,A,c,q,hs⟩:=Verify.vb_sc h
  refine ⟨hh,A,c,q,hs.vc,ht,hs.hh,hs.hint,hs.nok,hs.gd,hs.a,?_,hs.c,hs.rows,hs.x24⟩
  intro i hi
  simpa only [Stored,Nat.not_lt_zero,decide_false,Bool.false_eq_true,↓reduceIte] using hs.z i hi

theorem nttZ_vector_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    (hs : SCx p S 0 false 0 σ s) :
    WP isa (seqR (fun i=>Impl.MlDsa.AArch64.Verify.Optimized.forward (zP p i)) 0 p.ℓ) s
      (SCx p S p.ℓ false 0 σ) := by
  simpa only [Nat.zero_add] using seqR_ok (I:=fun i=>SCx p S i false 0 σ) p.ℓ 0
    (fun i _ hi s ⟨h,A,c,q,hs⟩=>WP.mono (nttZ_ok hF hp (by omega) hs)
      fun t ht=>⟨h,A,c,q,ht⟩) s hs

theorem nttZ_vector_tr {p : Params} (hF : VFacts p) {S : Nat} :
    RelCT isa (RootPair p S (SCx p S 0 false 0))
      (seqR (fun i=>Impl.MlDsa.AArch64.Verify.Optimized.forward (zP p i)) 0 p.ℓ)
      (RootPair p S (SCx p S p.ℓ false 0)) := by
  simpa only [Nat.zero_add] using seqR_tr (Q:=fun i=>RootPair p S (SCx p S i false 0)) p.ℓ 0 fun i _ hi=>nttZ_tr hF (by omega)

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/InverseSingleCallTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem inverseSingleAt_tr {S : Nat} {nm : String} {f : Ptr}
    (hf : (Arg.ptr f).Ok) {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → InverseSingleReady f x ∧ InverseSingleReady f y ∧
      pa x f=pa y f ∧ x.sp=y.sp ∧
      x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED") :
    RelCT isa Q (callAt nm staticCode (inverseSingleArgs f)) fun _ _=>True := by
  refine callAtSyms_tr (inverseSingle_callee S) (inverseSingleArgs_ok hf) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2=>?_
  obtain ⟨rx,ry,ef,esp,et⟩ := hQ x y hp
  refine ⟨[tableRegion (x.syms "VG_MLDSA_INV_FOLDED")],[outputRegion (pa x f)],
    inverseSingle_pre rx h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ef,et]; exact inverseSingle_pre ry h2 hy2
  · change x1.callEntry.gpr .x0=y1.callEntry.gpr .x0 ∧ x1.sp=y1.sp ∧
      x1.syms "VG_MLDSA_INV_FOLDED"=y1.syms "VG_MLDSA_INV_FOLDED"
    rw [show x1.callEntry.gpr .x0=x1.gpr .x0 from rfl,show y1.callEntry.gpr .x0=y1.gpr .x0 from rfl,Args.r0 h1,Args.r0 h2,
      Args.sp h1,Args.sp h2,hy1,hy2]
    exact ⟨ef,esp,et⟩
  · rw [ef,et]; exact ry.readable
  · rw [ef]; exact ry.writable
end VG.Proof.MlDsa.AArch64.Optimized.Inverse
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRowArithmeticTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized

theorem product_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 2)) (Impl.MlDsa.AArch64.Verify.Optimized.product p)
      (RootPair p S (RowI p S r 3)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (product_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.product
  apply MontProduct.at_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide)) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx,tx⟩,⟨h',A',c',q',hy,wy,ty⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨product_ready hF hσ hr hx wx tx,product_ready hF hτ hr hy wy ty,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.pa (show Reg.x28∈bases from by decide),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2⟩

theorem subtract_tr {p : Params} (hF : VFacts p) {S r : Nat} (hS : S<2^64) (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 3)) (Impl.MlDsa.AArch64.Verify.Optimized.subtract p)
      (RootPair p S (RowI p S r 4)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (subtract_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hc : accChk (vR p) (vW p) (wP p) (tm2P p)=true := by unfold accChk;vlay
  have C : CalleeOk S (Impl.MlDsa.AArch64.Optimized.AddSub.code true) (subContract abi S) :=
    CalleeOk.of_verified hS AddSub.sub_verified (Nat.zero_le _) (by change 0≤S;omega)
  apply accAt_tr (op:=sub) C (vOk p) hc
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx,tx⟩,⟨h',A',c',q',hy,wy,ty⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨H.lx,H.ly,⟨wx.1,tx.1⟩,⟨wy.1,ty.1⟩,H.same⟩

theorem inverse_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 4)) (Impl.MlDsa.AArch64.Verify.Optimized.inverse (wP p))
      (RootPair p S (RowI p S r 5)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw⟩=>
    WP.mono (inverse_ok hF hp hr hs hw) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.inverse
  apply Inverse.inverseSingleAt_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx⟩,⟨h',A',c',q',hy,wy⟩⟩,et⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨inverse_ready hF hσ hr hx wx,inverse_ready hF hτ hr hy wy,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.2⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedDotTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.Verify (zHat dotAcc foldl_dot)

private theorem poly_addr (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j)))=
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem dot_ready {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    {h : List (Vector Bool n)} {A' : Nat→Nat→Poly} {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) :
    MontDot.Ready p.ℓ (wP p) (aP (p.ℓ*r)) (zP p 0) s := by
  have L := hs.vc.lay hF hp
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have hrow : p.ℓ*r+p.ℓ≤p.k*p.ℓ := by
    have hm:=Nat.mul_le_mul_left p.ℓ (show r+1≤p.k by omega)
    rw [Nat.mul_succ,Nat.mul_comm p.ℓ p.k] at hm
    exact hm
  have hn : p.ℓ=4∨p.ℓ=5∨p.ℓ=7 := by rcases hF.mem with rfl|rfl|rfl <;> decide
  have ro : inB (vR p++vW p) (wP p) 1024=true := by vlayd
  have ra : inB (vR p++vW p) (aP (p.ℓ*r)) (1024*p.ℓ)=true := by vlayd
  have rb : inB (vR p++vW p) (zP p 0) (1024*p.ℓ)=true := by vlayd
  have wo : inB (vW p) (wP p) 1024=true := by vlayd
  have hA j (hj : j<p.ℓ) : PolyIs s.mem (pa s (aP (p.ℓ*r))+BitVec.ofNat 64 (1024*j)) (A' r j) := by
    have hv:=hs.a r hr j hj
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*r+j)))) _ at hv
    rwa [poly_addr] at hv
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem (pa s (zP p 0)+BitVec.ofNat 64 (1024*j)) (zHat p (vSig p σ) j) := by
    have hv:=hs.z j hj
    simp only [Stored,decide_eq_true_eq.mpr hj,↓reduceIte,ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+(1+p.k+j))))) _ at hv
    have he : p.k*p.ℓ+(1+p.k+j)=(p.k*p.ℓ+(1+p.k))+j := by omega
    rw [he,poly_addr] at hv
    simpa only [zP,vP,Nat.add_zero] using hv
  have ready : MontDot.Ready p.ℓ (wP p) (aP (p.ℓ*r)) (zP p 0) s :=
    ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.disj (by vlayd),L.disj (by vlayd),
      fun j hj=>(PosPolyIs.of_canonical (hA j hj)).bound,fun j hj=>(hB j hj).bound,
      Covers.cons (L.cR ra) (Covers.cons (L.cR rb) (L.cR ro)),L.cW wo⟩
  exact ready

theorem dot_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (SCx p S p.ℓ true r))
      (Impl.MlDsa.AArch64.Verify.Optimized.dot p r)
      (RootPair p S fun σ s=>∃h A c q,SC p S σ h A c q p.ℓ true r s ∧ W p σ A r s) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs⟩=>
    WP.mono (dot_ok hF hp hr hs) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  have hn : p.ℓ=4∨p.ℓ=5∨p.ℓ=7 := by rcases hF.mem with rfl|rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Verify.Optimized.dot
  apply MontDot.at_tr (S:=S) hn (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide)) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx⟩,⟨h',A',c',q',hy⟩⟩,_⟩ := hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨dot_ready hF hσ hr hx,dot_ready hF hτ hr hy,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.pa (show Reg.x28∈bases from by decide),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRowStartTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized

theorem unpack_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 0)) (unpackT1At P (.x25,32+320*r) (tmP p))
      (RootPair p S (RowI p S r 1)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw⟩=>
    WP.mono (unpack_ok hP hF hp hr hs hw) fun _ ht=>⟨h,A,c,q,ht⟩) ?_
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr;have hpk:=hF.pk
  have hc : rwChk (vR p) (vW p) (.x25,32+320*r) 320 (tmP p) 1024=true := by unfold rwChk;vlay
  apply t1At_tr hP.unpackT1 (vOk p) hc
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,_⟩,⟨h',A',c',q',hy,_⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨H.lx,H.ly,H.same⟩

theorem nttT_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 1)) (Impl.MlDsa.AArch64.Verify.Optimized.forward (tmP p))
      (RootPair p S (RowI p S r 2)) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw,ht⟩=>
    WP.mono (nttT_ok hF hp hr hs hw ht) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.forward
  apply positiveNttAt_tr (S:=S) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,_,tx⟩,⟨h',A',c',q',hy,_,ty⟩⟩,et⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  have hk:=hF.k;have hl:=hF.l;have hkl:=hF.kl;have hsc:=hF.scr
  have rd : inB (vR p++vW p) (tmP p) 1024=true := by vlayd
  have wr : inB (vW p) (tmP p) 1024=true := by vlayd
  exact ⟨forward_ready hF hσ hx.vc hx.roots rd wr tx.1,
    forward_ready hF hτ hy.vc hy.roots rd wr ty.1,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2,et.1⟩
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedRowTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Optimized

theorem hintPack_tr {p : Params} (hF : VFacts p) {S r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (RowI p S r 5)) (Impl.MlDsa.AArch64.Verify.Optimized.hintPack p r)
      (RootPair p S (SCx p S p.ℓ true (r+1))) := by
  refine rootPair_progress (fun σ s hp ⟨h,A,c,q,hs,hw⟩=>
    WP.mono (hintPack_ok hF hp hr hs hw) fun _ hv=>⟨h,A,c,q,hv⟩) ?_
  unfold Impl.MlDsa.AArch64.Verify.Optimized.hintPack
  apply UseHintPack.at_tr (S:=S) (Round.isG_of_mem hF.g2.1)
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide)) (ptr_ok (show Reg.x28∈keptRegs from by decide))
  intro x y hh
  obtain ⟨⟨σ,τ,hσ,hτ,pub,⟨h,A,c,q,hx,wx⟩,⟨h',A',c',q',hy,wy⟩⟩,_⟩:=hh
  have H:=vc_two hF hσ hτ pub hx.vc hy.vc
  exact ⟨hintPack_ready hF hσ hr hx wx,hintPack_ready hF hτ hr hy wy,
    H.same.pa (show Reg.x28∈bases from by decide),H.same.pa (show Reg.x28∈bases from by decide),
    H.same.pa (show Reg.x28∈bases from by decide),H.same.2⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedBody.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Message
open VG.Proof.MlDsa.KeyGen (ifn)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem hint_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) :
    16*(hint P p).aarch64Depth≤S := by
  have hh : DLe (S/16) P.hintUnpack := ⟨by have:=hP.hintUnpack.fd;omega⟩
  have hd : DLe (S/16) (hint P p) := by unfold hint;dle_tac
  have := hd.le;omega

theorem zOne_depth {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params) (i : Nat) :
    16*(zOne P p i).aarch64Depth≤S := by
  have hb : DLe (S/16) P.bitUnpack := ⟨by have:=hP.bitUnpack.fd;omega⟩
  have hn : DLe (S/16) P.normLt := ⟨by have:=hP.normLt.fd;omega⟩
  have hd : DLe (S/16) (zOne P p i) := by unfold zOne;dle_tac
  have := hd.le;omega

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

/-! # Shared prepared-key verification proof composition -/
namespace VG.Proof.MlDsa.AArch64.PreparedKey
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen VG.Proof.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.Optimized

def CachedVRel (p : Params) (S : Nat) (I : State → State → Prop) (x y : State) : Prop :=
  Verify.Optimized.RootPair p S
    (fun σ s => I σ s ∧ (s.gpr .x22 ≠ 0 → PublicCache p S σ s)) x y ∧
    SameIn [.x21, .x22] x y

theorem cached_v_progress {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
      WP isa code s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t))
    (ht : RelCT isa (CachedVRel p S I) code fun _ _ => True) :
    RelCT isa (CachedVRel p S I) code (CachedVRel p S J) := by
  intro x y tx ty u v h ex ey
  have trace := (ht _ _ _ _ _ _ h ex ey).1
  obtain ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩ := h
  obtain ⟨_, u', eu, hu⟩ := hw σ x ps hx.1 hx.2
  obtain ⟨_, v', ev, hv⟩ := hw τ y pt hy.1 hy.2
  obtain ⟨_, rfl⟩ := Exec.det ex eu
  obtain ⟨_, rfl⟩ := Exec.det ey ev
  refine ⟨trace, ⟨⟨σ, τ, ps, pt, pub, hu, hv⟩, ?_⟩, ?_⟩
  · simpa only [VG.Proof.MlDsa.AArch64.Sign.RootSymbolsEq,
      VG.AArch64.Exec.syms ex, VG.AArch64.Exec.syms ey] using roots
  · refine ⟨fun r hr => ?_, by rw [(hj _ _ hu.1).sp, (hj _ _ hv.1).sp,
      ← (hi _ _ hx.1).sp, ← (hi _ _ hy.1).sp, hm.2]⟩
    have hk : r ∈ VG.Proof.MlDsa.AArch64.KeyGen.untouched := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [(hj _ _ hu.1).cs r hk, (hj _ _ hv.1).cs r hk,
      ← (hi _ _ hx.1).cs r hk, ← (hi _ _ hy.1).cs r hk, hm.1 r hr]

theorem cached_v_lift {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → WP isa code s (J σ))
    (ht : RelCT isa (Verify.Optimized.RootPair p S I) code fun _ _ => True)
    (hd : 16 * code.aarch64Depth ≤ S) (hS : S < 2 ^ 64) :
    RelCT isa (CachedVRel p S I) code (CachedVRel p S J) := by
  apply cached_v_progress hi hj
  · intro σ s hp hs hc
    exact WP.optionalCache (hw σ s hp hs) hc hd hS
      (fun t ht => ((hj _ _ ht).cs .x21 (by decide)).trans ((hi _ _ hs).cs .x21 (by decide)).symm)
      (fun t ht => ((hj _ _ ht).cs .x22 (by decide)).trans ((hi _ _ hs).cs .x22 (by decide)).symm)
  · refine RelCT.mono ht ?_ (fun _ _ h => h)
    rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, _⟩
    exact ⟨⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩, roots⟩

theorem optimized_row_top {p : Params} {S r stage : Nat} {σ s : State}
    (h : Verify.Optimized.RowI p S r stage σ s) : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s := by
  obtain ⟨_, _, _, _, h, _⟩ := h
  exact h.vc.top

theorem keyRow_optimized_tr {c : Impl.Sha3.AArch64.Callee} (hpaired : c.pairedSha3 = true)
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r < p.k)
    (hd : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow c P p r).aarch64Depth ≤ S) :
    RelCT isa (CachedVRel p S (Verify.Optimized.RowI p S r 0))
      (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow c P p r)
      (CachedVRel p S (Verify.Optimized.RowI p S r 2)) := by
  refine cached_v_progress (fun _ _ h => optimized_row_top h) (fun _ _ h => optimized_row_top h) ?_ ?_
  · intro σ s hp hs cache
    obtain ⟨h, A, c0, q, state, hw⟩ := hs
    have main := WP.mono (keyRow_optimized hpaired hP hF hp hr state hw cache)
      fun t ht => (show Verify.Optimized.RowI p S r 2 σ t from ⟨h, A, c0, q, ht⟩)
    exact WP.optionalCache main cache hd hP.s64
      (fun t ht => ((optimized_row_top ht).cs .x21 (by decide)).trans (state.vc.top.cs .x21 (by decide)).symm)
      (fun t ht => ((optimized_row_top ht).cs .x22 (by decide)).trans (state.vc.top.cs .x22 (by decide)).symm)
  · unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
    refine RelCT.ite ?_ ?_ ?_
    · intro x y h
      change some (x.gpr .x22 != 0) = some (y.gpr .x22 != 0)
      rw [h.2.1 .x22 (by simp)]
    · apply RelCT.mono (copy_cache_tr _ _) ?_ (fun _ _ _ => trivial)
      rintro x y ⟨⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, _⟩, hm⟩, _⟩
      obtain ⟨_, _, _, _, ix, _⟩ := hx.1
      obtain ⟨_, _, _, _, iy, _⟩ := hy.1
      have layout := vc_two hF ps pt pub ix.vc iy.vc
      refine ⟨fun r hr => ?_, layout.same.2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hm.1 .x21 (by simp)
      · exact layout.same.1 .x28 (by decide)
    · have old := RelCT.seq (Verify.Optimized.unpack_tr hP hF hr) (Verify.Optimized.nttT_tr hF hr)
      apply RelCT.mono (by simpa [Impl.MlDsa.AArch64.PreparedKey.Verify.forward, hpaired] using old) ?_
        (fun _ _ _ => trivial)
      rintro x y ⟨⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, _⟩, _⟩
      exact ⟨⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩, roots⟩

theorem optimized_sc_top {p : Params} {S j r : Nat} {cn : Bool} {σ s : State}
    (h : Verify.Optimized.SCx p S j cn r σ s) : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s := by
  obtain ⟨_, _, _, _, h⟩ := h
  exact h.vc.top

theorem row_optimized_tr {c : Impl.Sha3.AArch64.Callee} (hpaired : c.pairedSha3 = true)
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r < p.k)
    (hdot : 16 * (Impl.MlDsa.AArch64.Verify.Optimized.dot p r).aarch64Depth ≤ S)
    (hkey : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow c P p r).aarch64Depth ≤ S)
    (hrow : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r).aarch64Depth ≤ S) :
    RelCT isa (CachedVRel p S (Verify.Optimized.SCx p S p.ℓ true r))
      (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r)
      (CachedVRel p S (Verify.Optimized.SCx p S p.ℓ true (r + 1))) := by
  refine cached_v_progress (fun _ _ h => optimized_sc_top h) (fun _ _ h => optimized_sc_top h) ?_ ?_
  · intro σ s hp hs cache
    obtain ⟨h, A, c0, q, state⟩ := hs
    exact WP.mono (row_optimized hpaired hP hF hp hr hdot hrow state cache)
      fun t ht => ⟨⟨h, A, c0, q, ht.1⟩, ht.2⟩
  · simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.row, hpaired, ↓reduceIte]
    refine RelCT.seq (R := CachedVRel p S (Verify.Optimized.RowI p S r 0))
      (cached_v_lift (fun _ _ h => optimized_sc_top h) (fun _ _ h => optimized_row_top h)
        (fun σ s hp ⟨h, A, c0, q, state⟩ => WP.mono (Verify.Optimized.dot_ok hF hp hr state)
          fun _ ht => ⟨h, A, c0, q, ht⟩)
        (RelCT.mono (Verify.Optimized.dot_tr hF hr) (fun _ _ h => h) (fun _ _ _ => trivial))
        hdot hP.s64) ?_
    refine RelCT.seq (keyRow_optimized_tr hpaired hP hF hr hkey) ?_
    refine RelCT.mono (RelCT.seq (Verify.Optimized.product_tr hF hr)
      (RelCT.seq (Verify.Optimized.subtract_tr hF hP.s64 hr)
        (RelCT.seq (Verify.Optimized.inverse_tr hF hr) (Verify.Optimized.hintPack_tr hF hr))))
      ?_ (fun _ _ _ => trivial)
    rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, _⟩
    exact ⟨⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩, roots⟩

def CachedScalarRel (p : Params) (S : Nat) (I : State → State → Prop) (x y : State) : Prop :=
  VR p S (fun σ s => I σ s ∧ (s.gpr .x22 ≠ 0 → PublicCache p S σ s)) x y ∧
    SameIn [.x21, .x22] x y

theorem cached_scalar_progress {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
      WP isa code s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t))
    (ht : RelCT isa (CachedScalarRel p S I) code fun _ _ => True) :
    RelCT isa (CachedScalarRel p S I) code (CachedScalarRel p S J) := by
  intro x y tx ty u v h ex ey
  have trace := (ht _ _ _ _ _ _ h ex ey).1
  obtain ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, hm⟩ := h
  obtain ⟨_, u', eu, hu⟩ := hw σ x ps hx.1 hx.2
  obtain ⟨_, v', ev, hv⟩ := hw τ y pt hy.1 hy.2
  obtain ⟨_, rfl⟩ := Exec.det ex eu
  obtain ⟨_, rfl⟩ := Exec.det ey ev
  refine ⟨trace, ⟨σ, τ, ps, pt, pub, hu, hv⟩, ?_⟩
  refine ⟨fun r hr => ?_, by rw [(hj _ _ hu.1).sp, (hj _ _ hv.1).sp,
    ← (hi _ _ hx.1).sp, ← (hi _ _ hy.1).sp, hm.2]⟩
  have hk : r ∈ VG.Proof.MlDsa.AArch64.KeyGen.untouched := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  rw [(hj _ _ hu.1).cs r hk, (hj _ _ hv.1).cs r hk,
    ← (hi _ _ hx.1).cs r hk, ← (hi _ _ hy.1).cs r hk, hm.1 r hr]

theorem cached_scalar_lift {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → WP isa code s (J σ))
    (ht : RelCT isa (VR p S I) code fun _ _ => True)
    (hd : 16 * code.aarch64Depth ≤ S) (hS : S < 2 ^ 64) :
    RelCT isa (CachedScalarRel p S I) code (CachedScalarRel p S J) := by
  apply cached_scalar_progress hi hj
  · intro σ s hp hs hc
    exact WP.optionalCache (hw σ s hp hs) hc hd hS
      (fun t ht => ((hj _ _ ht).cs .x21 (by decide)).trans ((hi _ _ hs).cs .x21 (by decide)).symm)
      (fun t ht => ((hj _ _ ht).cs .x22 (by decide)).trans ((hi _ _ hs).cs .x22 (by decide)).symm)
  · refine RelCT.mono ht ?_ (fun _ _ h => h)
    rintro x y ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, _⟩
    exact ⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩

theorem scalar_row_top {p : Params} {r : Nat} {F : State → List (Vector Bool n) →
    (Nat → Nat → Poly) → Poly → State → Prop} {σ s : State}
    (h : Verify.RowI p r F σ s) : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s := by
  obtain ⟨_, _, _, _, h, _⟩ := h
  exact h.vc.top

theorem scalar_sc_top {p : Params} {j r : Nat} {cn : Bool} {σ s : State}
    (h : Verify.SCx p j cn r σ s) : VG.Proof.MlDsa.AArch64.KeyGen.Top σ s := by
  obtain ⟨_, _, _, _, h⟩ := h
  exact h.vc.top

theorem keyRow_scalar_tr {c : Impl.Sha3.AArch64.Callee} (hpaired : c.pairedSha3 = false)
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r < p.k)
    (hd : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow c P p r).aarch64Depth ≤ S) :
    RelCT isa (CachedScalarRel p S (Verify.RowI p r (Verify.F1 p r p.ℓ)))
      (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow c P p r)
      (CachedScalarRel p S (Verify.RowI p r (Verify.F4 p r))) := by
  refine cached_scalar_progress (fun _ _ h => scalar_row_top h) (fun _ _ h => scalar_row_top h) ?_ ?_
  · intro σ s hp hs cache
    exact WP.optionalCache (keyRow_scalar hpaired hP hF hp hr hs cache) cache hd hP.s64
      (fun t ht => ((scalar_row_top ht).cs .x21 (by decide)).trans ((scalar_row_top hs).cs .x21 (by decide)).symm)
      (fun t ht => ((scalar_row_top ht).cs .x22 (by decide)).trans ((scalar_row_top hs).cs .x22 (by decide)).symm)
  · unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
    refine RelCT.ite ?_ ?_ ?_
    · intro x y h
      change some (x.gpr .x22 != 0) = some (y.gpr .x22 != 0)
      rw [h.2.1 .x22 (by simp)]
    · apply RelCT.mono (copy_cache_tr _ _) ?_ (fun _ _ _ => trivial)
      rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, hm⟩, _⟩
      obtain ⟨_, _, _, _, ix, _⟩ := hx.1
      obtain ⟨_, _, _, _, iy, _⟩ := hy.1
      have layout := vc_two hF ps pt pub ix.vc iy.vc
      refine ⟨fun r hr => ?_, layout.same.2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hm.1 .x21 (by simp)
      · exact layout.same.1 .x28 (by decide)
    · have old := ((Verify.t1_vpiece hP hF hr).seq (Verify.nttT_vpiece hP hF hr)).tr
      apply RelCT.mono (by simpa [Impl.MlDsa.AArch64.PreparedKey.Verify.forward, hpaired] using old) ?_
        (fun _ _ _ => trivial)
      rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, _⟩, _⟩
      exact ⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩

theorem row_scalar_tr {c : Impl.Sha3.AArch64.Callee} (hpaired : c.pairedSha3 = false)
    {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r < p.k)
    (hdot : 16 * (Impl.MlDsa.AArch64.Verify.dot P p r).aarch64Depth ≤ S)
    (hkey : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow c P p r).aarch64Depth ≤ S)
    (hrow : 16 * (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r).aarch64Depth ≤ S) :
    RelCT isa (CachedScalarRel p S (Verify.SCx p p.ℓ true r))
      (Impl.MlDsa.AArch64.PreparedKey.Verify.row c P p r)
      (CachedScalarRel p S (Verify.SCx p p.ℓ true (r + 1))) := by
  refine cached_scalar_progress (fun _ _ h => scalar_sc_top h) (fun _ _ h => scalar_sc_top h) ?_ ?_
  · intro σ s hp hs cache
    exact row_scalar hpaired hP hF hp hr hdot hrow hs cache
  · simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.row, hpaired, Bool.false_eq_true, ↓reduceIte]
    refine RelCT.seq (R := CachedScalarRel p S (Verify.RowI p r (Verify.F1 p r p.ℓ)))
      (cached_scalar_lift (fun _ _ h => scalar_sc_top h) (fun _ _ h => scalar_row_top h)
        (Verify.dot_vpiece hP hF hr).ok (Verify.dot_vpiece hP hF hr).tr hdot hP.s64) ?_
    refine RelCT.seq (keyRow_scalar_tr hpaired hP hF hr hkey) ?_
    have tail := ((Verify.mulT_vpiece hP hF hr).seq ((Verify.sub_vpiece hP hF hr).seq
      ((Verify.inv_vpiece hP hF hr).seq ((Verify.uh_vpiece hP hF hr).seq
        (Verify.sbpR_vpiece hP hF hr))))).tr
    apply RelCT.mono tail ?_ (fun _ _ _ => trivial)
    rintro x y ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, _⟩
    exact ⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩

theorem forward_dle (v : Proof.Sha3.AArch64.Permutation) {P : Prims}
    (hP : PrimsOk P 16) (p : Params) (a : Impl.MlDsa.AArch64.Call.Ptr) :
    Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.forward v.callee P p a) := by
  have hn := Message.DLe.of_fd hP.ntt.fd
  have hp := Message.DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.positiveNtt_callee 16).fd
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.forward
  split <;> dle_tac

theorem keyRow_dle (v : Proof.Sha3.AArch64.Permutation) {P : Prims}
    (hP : PrimsOk P 16) (p : Params) (r : Nat) :
    Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow v.callee P p r) := by
  have hc : Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.copy (tmP p) (.x21, 1024 * r) 1024) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.copy
    split <;> dle_tac
  have hu := Message.DLe.of_fd hP.unpackT1.fd
  have hf := forward_dle v hP p (tmP p)
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.keyRow
  dle_tac

theorem row_dle (v : Proof.Sha3.AArch64.Permutation) {P : Prims}
    (hP : PrimsOk P 16) (p : Params) (r : Nat) :
    Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.row v.callee P p r) := by
  have hk := keyRow_dle v hP p r
  have hm := Message.DLe.of_fd hP.mul.fd
  have hma := Message.DLe.of_fd hP.mulAdd.fd
  have hsub := Message.DLe.of_fd hP.sub.fd
  have hi := Message.DLe.of_fd hP.invNtt.fd
  have hh := Message.DLe.of_fd hP.useHint.fd
  have hb := Message.DLe.of_fd hP.simpleBitPack.fd
  have hinv := Message.DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.Inverse.inverseSingle_callee 16).fd
  have hdot : Message.DLe 1 (Impl.MlDsa.AArch64.Optimized.MontDot.dot p.ℓ) := by
    unfold Impl.MlDsa.AArch64.Optimized.MontDot.dot
    dle_tac
  have hprod : Message.DLe 1 Impl.MlDsa.AArch64.Optimized.MontProduct.code := by
    unfold Impl.MlDsa.AArch64.Optimized.MontProduct.code
    dle_tac
  have hminus : Message.DLe 1 (Impl.MlDsa.AArch64.Optimized.AddSub.code true) := by
    unfold Impl.MlDsa.AArch64.Optimized.AddSub.code
    dle_tac
  have hpack : Message.DLe 1 Impl.MlDsa.AArch64.Optimized.UseHintPack.prog := by
    unfold Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
      Impl.MlDsa.AArch64.Round.zext Impl.MlDsa.AArch64.Round.onGamma
      Impl.MlDsa.AArch64.Optimized.UseHintPack.code
    dle_tac
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.row
  split <;> dle_tac

structure CachePiece (p : Params) (S : Nat) (I J : State → State → Prop) (code : Prog isa) : Prop where
  ok : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
    WP isa code s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t)
  tr : RelCT isa (CachedVRel p S I) code (CachedVRel p S J)

theorem CachePiece.seq {p : Params} {S : Nat} {I J K : State → State → Prop} {a b : Prog isa}
    (ha : CachePiece p S I J a) (hb : CachePiece p S J K b) : CachePiece p S I K (.seq a b) :=
  ⟨fun σ s hp hs hc => WP.seq (WP.mono (ha.ok σ s hp hs hc)
    fun t ht => hb.ok σ t hp ht.1 ht.2), RelCT.seq ha.tr hb.tr⟩

theorem CachePiece.of_old {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → WP isa code s (J σ))
    (ht : RelCT isa (Verify.Optimized.RootPair p S I) code fun _ _ => True)
    (hd : 16 * code.aarch64Depth ≤ S) (hS : S < 2 ^ 64) : CachePiece p S I J code :=
  ⟨fun σ s hp hs hc => WP.optionalCache (hw σ s hp hs) hc hd hS
    (fun t ht => ((hj _ _ ht).cs .x21 (by decide)).trans ((hi _ _ hs).cs .x21 (by decide)).symm)
    (fun t ht => ((hj _ _ ht).cs .x22 (by decide)).trans ((hi _ _ hs).cs .x22 (by decide)).symm),
    cached_v_lift hi hj hw ht hd hS⟩

theorem CachePiece.mono {p : Params} {S : Nat} {I J I' J' : State → State → Prop} {code : Prog isa}
    (h : CachePiece p S I J code)
    (hi : ∀ σ s, I' σ s → I σ s) (hj : ∀ σ s, J σ s → J' σ s) : CachePiece p S I' J' code := by
  refine ⟨fun σ s hp hs hc => WP.mono (h.ok σ s hp (hi σ s hs) hc)
    (fun t ht => ⟨hj σ t ht.1, ht.2⟩), RelCT.mono h.tr ?_ ?_⟩
  · rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩
    exact ⟨⟨⟨σ, τ, ps, pt, pub, ⟨hi _ _ hx.1, hx.2⟩, ⟨hi _ _ hy.1, hy.2⟩⟩, roots⟩, hm⟩
  · rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩
    exact ⟨⟨⟨σ, τ, ps, pt, pub, ⟨hj _ _ hx.1, hx.2⟩, ⟨hj _ _ hy.1, hy.2⟩⟩, roots⟩, hm⟩

theorem CachePiece.seqR {p : Params} {S : Nat} {f : Nat → Prog isa}
    {I : Nat → State → State → Prop} :
    ∀ n a, (∀ k, a ≤ k → k < a + n → CachePiece p S (I k) (I (k + 1)) (f k)) →
      CachePiece p S (I a) (I (a + n)) (Impl.MlDsa.AArch64.Call.seqR f a n)
  | 0, a, _ => by
    simp only [Impl.MlDsa.AArch64.Call.seqR, Nat.add_zero]
    exact ⟨fun _ _ _ hs hc => WP.block_nil ⟨hs, hc⟩, RelCT.block_nil (fun _ _ h => h)⟩
  | n + 1, a, h => by
    have tail := CachePiece.seqR n (a + 1) (fun k h1 h2 => h k (by omega) (by omega))
    rw [show a + 1 + n = a + (n + 1) by omega] at tail
    exact (h a (Nat.le_refl _) (by omega)).seq tail

theorem dle_first {a b : Prog isa} (h : Message.DLe 1 (.seq a b)) : Message.DLe 1 a :=
  ⟨(Nat.max_le.mp h.le).1⟩

theorem depth16 {code : Prog isa} (h : Message.DLe 1 code) : 16 * code.aarch64Depth ≤ 16 := by
  simpa using Nat.mul_le_mul_left 16 h.le

theorem finish_dle (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    Message.DLe 1 (.seq (shake256With v.callee (hIns p) [⟨.x28, oCT, p.ctildeLen⟩])
      (cmpAnd (Impl.MlDsa.AArch64.Call.sc oCT) (.x27, 0) p.ctildeLen)) := by
  obtain ⟨ha, hp, hs⟩ := Message.keccak_dle v
  dle_tac

theorem compute_optimized_piece (v : Proof.Sha3.AArch64.Permutation) (hpaired : v.callee.pairedSha3 = true)
    {P : Prims} (hP : PrimsOk P 16) {p : Params} (hF : VFacts p) :
    CachePiece p 16 (fun σ s => VB p σ s ∧ Sign.StaticRoots 16 s) (VFin p)
      (Impl.MlDsa.AArch64.PreparedKey.Verify.compute v.callee P p) := by
  have hf (a : Impl.MlDsa.AArch64.Call.Ptr) : Message.DLe 1
      (Impl.MlDsa.AArch64.Verify.Optimized.forward a) := by
    simpa only [Impl.MlDsa.AArch64.PreparedKey.Verify.forward, hpaired, ↓reduceIte] using forward_dle v hP p a
  have hvec := Message.DLe.seqR (fun i => hf (zP p i)) 0 p.ℓ
  have hdot (r : Nat) : Message.DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.dot p r) := by
    have h := row_dle v hP p r
    simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.row, hpaired, ↓reduceIte] at h
    exact dle_first h
  simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.compute,
    Impl.MlDsa.AArch64.PreparedKey.Verify.forward, hpaired, ↓reduceIte]
  refine CachePiece.seq (J := Verify.Optimized.SCx p 16 p.ℓ false 0) ?_
    (CachePiece.seq (J := Verify.Optimized.SCx p 16 p.ℓ true 0) ?_
      (CachePiece.seq (J := Verify.Optimized.SCx p 16 p.ℓ true p.k) ?_ ?_))
  · apply CachePiece.of_old (fun _ _ h => h.1.vz.vc.top) (fun _ _ h => optimized_sc_top h)
      (fun σ s hp hs => Verify.Optimized.nttZ_vector_ok hF hp (Verify.Optimized.vb_sc hs.1 hs.2))
      ?_ (depth16 hvec) (by decide)
    exact RelCT.mono (Verify.Optimized.nttZ_vector_tr hF)
      (fun _ _ ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩ =>
        ⟨⟨σ, τ, ps, pt, pub, Verify.Optimized.vb_sc hx.1 hx.2,
          Verify.Optimized.vb_sc hy.1 hy.2⟩, roots⟩) (fun _ _ _ => trivial)
  · apply CachePiece.of_old (fun _ _ h => optimized_sc_top h) (fun _ _ h => optimized_sc_top h)
      (fun σ s hp ⟨h, A, c0, q, state⟩ => WP.mono (Verify.Optimized.nttC_ok hF hp state)
        fun t ht => ⟨h, A, c0, q, ht⟩)
      (RelCT.mono (Verify.Optimized.nttC_tr hF) (fun _ _ h => h) (fun _ _ _ => trivial))
      (depth16 (hf (cP p))) (by decide)
  · simpa only [Nat.zero_add] using CachePiece.seqR (I := fun r => Verify.Optimized.SCx p 16 p.ℓ true r)
      p.k 0 (fun r _ hr => (show CachePiece p 16
        (Verify.Optimized.SCx p 16 p.ℓ true r) (Verify.Optimized.SCx p 16 p.ℓ true (r + 1))
        (Impl.MlDsa.AArch64.PreparedKey.Verify.row v.callee P p r) from
        ⟨fun σ s hp ⟨h, A, c0, q, state⟩ cache => WP.mono
          (row_optimized hpaired hP hF hp (by omega) (depth16 (hdot r))
            (depth16 (row_dle v hP p r)) state cache)
          (fun t ht => ⟨⟨h, A, c0, q, ht.1⟩, ht.2⟩),
          row_optimized_tr hpaired hP hF (by omega) (depth16 (hdot r))
            (depth16 (keyRow_dle v hP p r)) (depth16 (row_dle v hP p r))⟩))
  · exact CachePiece.of_old (fun _ _ h => optimized_sc_top h) (fun _ _ h => h.1.top)
      (Verify.Optimized.finish_vpiece (keccak := v) (by decide) (by decide) hF).ok
      (RelCT.mono (Verify.Optimized.finish_rootPair (keccak := v) (by decide) (by decide) hF)
        (fun _ _ h => h) (fun _ _ _ => trivial)) (depth16 (finish_dle v p)) (by decide)
structure ScalarCachePiece (p : Params) (S : Nat) (I J : State → State → Prop) (code : Prog isa) : Prop where
  ok : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
    WP isa code s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t)
  tr : RelCT isa (CachedScalarRel p S I) code (CachedScalarRel p S J)

theorem ScalarCachePiece.seq {p : Params} {S : Nat} {I J K : State → State → Prop} {a b : Prog isa}
    (ha : ScalarCachePiece p S I J a) (hb : ScalarCachePiece p S J K b) : ScalarCachePiece p S I K (.seq a b) :=
  ⟨fun σ s hp hs hc => WP.seq (WP.mono (ha.ok σ s hp hs hc)
    fun t ht => hb.ok σ t hp ht.1 ht.2), RelCT.seq ha.tr hb.tr⟩

theorem ScalarCachePiece.of_old {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hw : ∀ σ s, vPre p S σ → I σ s → WP isa code s (J σ))
    (ht : RelCT isa (VR p S I) code fun _ _ => True)
    (hd : 16 * code.aarch64Depth ≤ S) (hS : S < 2 ^ 64) : ScalarCachePiece p S I J code :=
  ⟨fun σ s hp hs hc => WP.optionalCache (hw σ s hp hs) hc hd hS
    (fun t ht => ((hj _ _ ht).cs .x21 (by decide)).trans ((hi _ _ hs).cs .x21 (by decide)).symm)
    (fun t ht => ((hj _ _ ht).cs .x22 (by decide)).trans ((hi _ _ hs).cs .x22 (by decide)).symm),
    cached_scalar_lift hi hj hw ht hd hS⟩

theorem ScalarCachePiece.seqR {p : Params} {S : Nat} {f : Nat → Prog isa}
    {I : Nat → State → State → Prop} :
    ∀ n a, (∀ k, a ≤ k → k < a + n → ScalarCachePiece p S (I k) (I (k + 1)) (f k)) →
      ScalarCachePiece p S (I a) (I (a + n)) (Impl.MlDsa.AArch64.Call.seqR f a n)
  | 0, a, _ => by
    simp only [Impl.MlDsa.AArch64.Call.seqR, Nat.add_zero]
    exact ⟨fun _ _ _ hs hc => WP.block_nil ⟨hs, hc⟩, RelCT.block_nil (fun _ _ h => h)⟩
  | n + 1, a, h => by
    have tail := ScalarCachePiece.seqR n (a + 1) (fun k h1 h2 => h k (by omega) (by omega))
    rw [show a + 1 + n = a + (n + 1) by omega] at tail
    exact (h a (Nat.le_refl _) (by omega)).seq tail

theorem compute_scalar_piece (v : Proof.Sha3.AArch64.Permutation) (hpaired : v.callee.pairedSha3 = false)
    {P : Prims} (hP : PrimsOk P 16) {p : Params} (hF : VFacts p) :
    ScalarCachePiece p 16 (VB p) (VFin p)
      (Impl.MlDsa.AArch64.PreparedKey.Verify.compute v.callee P p) := by
  have hf (a : Impl.MlDsa.AArch64.Call.Ptr) : Message.DLe 1
      (nttAt P (Impl.MlDsa.AArch64.Call.sc oSS) a) := by
    simpa only [Impl.MlDsa.AArch64.PreparedKey.Verify.forward, hpaired,
      Bool.false_eq_true, ↓reduceIte] using forward_dle v hP p a
  have hvec := Message.DLe.seqR (fun i => hf (zP p i)) 0 p.ℓ
  have hdot (r : Nat) : Message.DLe 1 (Impl.MlDsa.AArch64.Verify.dot P p r) := by
    have h := row_dle v hP p r
    simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.row, hpaired, Bool.false_eq_true, ↓reduceIte] at h
    exact dle_first h
  have vec : VPiece p 16 (Verify.SCx p 0 false 0) (Verify.SCx p p.ℓ false 0)
      (Impl.MlDsa.AArch64.Call.seqR
        (fun i => nttAt P (Impl.MlDsa.AArch64.Call.sc oSS) (zP p i)) 0 p.ℓ) := by
    simpa only [Nat.zero_add] using VPiece.seqR (I := fun i => Verify.SCx p i false 0) p.ℓ 0
      (fun i _ hi => Verify.nttZ_vpiece hP hF (by omega))
  simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.compute,
    Impl.MlDsa.AArch64.PreparedKey.Verify.forward, hpaired, Bool.false_eq_true, ↓reduceIte]
  refine ScalarCachePiece.seq (J := Verify.SCx p p.ℓ false 0) ?_
    (ScalarCachePiece.seq (J := Verify.SCx p p.ℓ true 0) ?_
      (ScalarCachePiece.seq (J := Verify.SCx p p.ℓ true p.k) ?_ ?_))
  · apply ScalarCachePiece.of_old (fun _ _ h => h.vz.vc.top) (fun _ _ h => scalar_sc_top h)
      (fun σ s hp hs => vec.ok σ s hp (Verify.vb_sc hs)) ?_ (depth16 hvec) (by decide)
    exact RelCT.mono vec.tr
      (fun _ _ ⟨σ, τ, ps, pt, pub, hx, hy⟩ =>
        ⟨σ, τ, ps, pt, pub, Verify.vb_sc hx, Verify.vb_sc hy⟩) (fun _ _ _ => trivial)
  · exact ScalarCachePiece.of_old (fun _ _ h => scalar_sc_top h) (fun _ _ h => scalar_sc_top h)
      (Verify.nttC_vpiece hP hF).ok (Verify.nttC_vpiece hP hF).tr (depth16 (hf (cP p))) (by decide)
  · simpa only [Nat.zero_add] using ScalarCachePiece.seqR (I := fun r => Verify.SCx p p.ℓ true r)
      p.k 0 (fun r _ hr => (show ScalarCachePiece p 16
        (Verify.SCx p p.ℓ true r) (Verify.SCx p p.ℓ true (r + 1))
        (Impl.MlDsa.AArch64.PreparedKey.Verify.row v.callee P p r) from
        ⟨fun σ s hp hs cache => row_scalar hpaired hP hF hp (by omega)
          (depth16 (hdot r)) (depth16 (row_dle v hP p r)) hs cache,
          row_scalar_tr hpaired hP hF (by omega) (depth16 (hdot r))
            (depth16 (keyRow_dle v hP p r)) (depth16 (row_dle v hP p r))⟩))
  · have tail := (Verify.hash_vpiece (keccak := v) hP.s16 hP.s64 hF).seq (Verify.cmp_vpiece hF)
    exact ScalarCachePiece.of_old (fun _ _ h => scalar_sc_top h) (fun _ _ h => h.1.top)
      tail.ok tail.tr (depth16 (finish_dle v p)) (by decide)

theorem CachePiece.ifOk {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    {T : State → Prop} [DecidablePred T]
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hx : ∀ σ s, vPre p S σ → I σ s → s.gpr .x24 = if T σ then 1 else 0)
    (hT : ∀ σ τ, vPre p S σ → vPre p S τ → vPub p S σ τ → (T σ ↔ T τ))
    (ht : CachePiece p S (fun σ s => I σ s ∧ T σ) J code)
    (he : ∀ σ s, vPre p S σ → I σ s → ¬ T σ → J σ s) :
    CachePiece p S I J (Impl.MlDsa.AArch64.KeyGen.ifOk code) := by
  have ev (σ s : State) (hp : vPre p S σ) (hs : I σ s) :
      isa.eval (.nonzero .x .x24) s = some (decide (T σ)) := by
    change some (s.gpr .x24 != 0) = some (decide (T σ))
    rw [hx σ s hp hs]
    by_cases h : T σ <;> simp [h]
  have hw : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
      WP isa (Impl.MlDsa.AArch64.KeyGen.ifOk code) s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t) := by
    intro σ s hp hs hc
    unfold Impl.MlDsa.AArch64.KeyGen.ifOk
    exact WP.ite (decide (T σ)) (ev σ s hp hs)
      (fun hb => ht.ok σ s hp ⟨hs, of_decide_eq_true hb⟩ hc)
      (fun hb => WP.block_nil ⟨he σ s hp hs (of_decide_eq_false hb), hc⟩)
  refine ⟨hw, cached_v_progress hi hj hw ?_⟩
  unfold Impl.MlDsa.AArch64.KeyGen.ifOk
  refine RelCT.ite ?_ ?_ (RelCT.block_nil (fun _ _ _ => trivial))
  · rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩
    rw [ev σ x ps hx.1, ev τ y pt hy.1, decide_eq_decide.mpr (hT σ τ ps pt pub)]
  · refine RelCT.mono ht.tr ?_ (fun _ _ _ => trivial)
    rintro x y ⟨⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, roots⟩, hm⟩, hflag⟩
    rw [ev σ x ps hx.1] at hflag
    have tx : T σ := of_decide_eq_true (Option.some.inj hflag)
    have ty : T τ := (hT σ τ ps pt pub).mp tx
    exact ⟨⟨⟨σ, τ, ps, pt, pub, ⟨⟨hx.1, tx⟩, hx.2⟩, ⟨⟨hy.1, ty⟩, hy.2⟩⟩, roots⟩, hm⟩

theorem ScalarCachePiece.ifOk {p : Params} {S : Nat} {I J : State → State → Prop} {code : Prog isa}
    {T : State → Prop} [DecidablePred T]
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hx : ∀ σ s, vPre p S σ → I σ s → s.gpr .x24 = if T σ then 1 else 0)
    (hT : ∀ σ τ, vPre p S σ → vPre p S τ → vPub p S σ τ → (T σ ↔ T τ))
    (ht : ScalarCachePiece p S (fun σ s => I σ s ∧ T σ) J code)
    (he : ∀ σ s, vPre p S σ → I σ s → ¬ T σ → J σ s) :
    ScalarCachePiece p S I J (Impl.MlDsa.AArch64.KeyGen.ifOk code) := by
  have ev (σ s : State) (hp : vPre p S σ) (hs : I σ s) :
      isa.eval (.nonzero .x .x24) s = some (decide (T σ)) := by
    change some (s.gpr .x24 != 0) = some (decide (T σ))
    rw [hx σ s hp hs]
    by_cases h : T σ <;> simp [h]
  have hw : ∀ σ s, vPre p S σ → I σ s → (s.gpr .x22 ≠ 0 → PublicCache p S σ s) →
      WP isa (Impl.MlDsa.AArch64.KeyGen.ifOk code) s fun t => J σ t ∧ (t.gpr .x22 ≠ 0 → PublicCache p S σ t) := by
    intro σ s hp hs hc
    unfold Impl.MlDsa.AArch64.KeyGen.ifOk
    exact WP.ite (decide (T σ)) (ev σ s hp hs)
      (fun hb => ht.ok σ s hp ⟨hs, of_decide_eq_true hb⟩ hc)
      (fun hb => WP.block_nil ⟨he σ s hp hs (of_decide_eq_false hb), hc⟩)
  refine ⟨hw, cached_scalar_progress hi hj hw ?_⟩
  unfold Impl.MlDsa.AArch64.KeyGen.ifOk
  refine RelCT.ite ?_ ?_ (RelCT.block_nil (fun _ _ _ => trivial))
  · rintro x y ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, hm⟩
    rw [ev σ x ps hx.1, ev τ y pt hy.1, decide_eq_decide.mpr (hT σ τ ps pt pub)]
  · refine RelCT.mono ht.tr ?_ (fun _ _ _ => trivial)
    rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, hm⟩, hflag⟩
    rw [ev σ x ps hx.1] at hflag
    have tx : T σ := of_decide_eq_true (Option.some.inj hflag)
    have ty : T τ := (hT σ τ ps pt pub).mp tx
    exact ⟨⟨σ, τ, ps, pt, pub, ⟨⟨hx.1, tx⟩, hx.2⟩, ⟨⟨hy.1, ty⟩, hy.2⟩⟩, hm⟩

theorem CachePiece.of_piece {p : Params} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (h : Verify.Optimized.Piece p 16 I J code) (hd : 16 * code.aarch64Depth ≤ 16) :
    CachePiece p 16 I J code := CachePiece.of_old hi hj h.ok h.tr hd (by decide)

theorem body_optimized_piece (v : Proof.Sha3.AArch64.Permutation) (hpaired : v.callee.pairedSha3 = true)
    {P : Prims} (hP : PrimsOk P 16) {p : Params} (hF : VFacts p) :
    CachePiece p 16 (fun σ s => (VC p σ s ∧ s.gpr .x24 = 1) ∧ Sign.StaticRoots 16 s)
      (VFin p) (Impl.MlDsa.AArch64.PreparedKey.Verify.body v.callee P p) := by
  simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.body, hpaired, ↓reduceIte]
  refine CachePiece.seq (CachePiece.of_piece (fun _ _ h => h.1.1.top)
    (fun _ _ h => h.1.1.top) (Verify.Optimized.Piece.of_vpiece
      (OptimizedSamples.rooted_piece (Verify.hint_vpiece hP hF)
        (Verify.Optimized.hint_depth hP p) hP.s64)) (Verify.Optimized.hint_depth hP p))
    (CachePiece.ifOk (T := fun σ => (hintOf p σ).isSome = true)
      (fun _ _ h => h.1.1.top) (fun _ _ h => h.1.top) (fun _ _ _ h => h.1.2.1)
      (fun _ _ _ _ pub => by rw [hintOf, hintOf, (vPub_eq pub).2.2.2.1]) ?_ ?_)
  · refine CachePiece.seq (J := fun σ s => Z0 p p.ℓ σ s ∧ Sign.StaticRoots 16 s) ?_
      (CachePiece.ifOk (T := fun σ => normOk p σ p.ℓ)
        (fun _ _ h => h.1.1.vc.top) (fun _ _ h => h.1.top)
        (fun _ _ _ h => h.1.2)
        (fun _ _ _ _ pub => by simp only [normOk, zOf, (vPub_eq pub).2.2.2.1]) ?_ ?_)
    · refine CachePiece.mono (CachePiece.seqR
        (I := fun j σ s => Z0 p j σ s ∧ Sign.StaticRoots 16 s) p.ℓ 0
        (fun j _ hj => CachePiece.of_piece (fun _ _ h => h.1.1.vc.top)
          (fun _ _ h => h.1.1.vc.top) (Verify.Optimized.Piece.of_vpiece
            (OptimizedSamples.rooted_piece (Verify.zOne_vpiece hP hF (by omega))
              (Verify.Optimized.zOne_depth hP p j) hP.s64)) (Verify.Optimized.zOne_depth hP p j))) ?_ ?_
      · intro σ s ⟨⟨⟨hv, hx, hH⟩, roots⟩, ht⟩
        refine ⟨⟨⟨hv, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩, ?_⟩, roots⟩
        · obtain ⟨hh, e⟩ := Option.isSome_iff_exists.mp ht
          exact ⟨hh, e, hH hh e⟩
        · rw [hx]
          exact flag_congr (iff_of_true ht (Verify.normOk_zero p σ))
      · intro _ _ h; simpa only [Nat.zero_add] using h
    · refine CachePiece.mono ((CachePiece.of_piece (fun _ _ h => h.1.1.1.vc.top)
        (fun _ _ h => h.1.vz.vc.top) (Verify.Optimized.Piece.of_vpiece (OptimizedSamples.samples_rooted_vpiece hP hF))
        (OptimizedSamples.samples_depth hP p)).seq (compute_optimized_piece v hpaired hP hF)) ?_
        (fun _ _ h => h)
      intro _ _ ⟨⟨hz, roots⟩, hn⟩
      exact ⟨⟨hz, hn⟩, roots⟩
    · intro σ s _ ⟨h, _⟩ hn
      refine ⟨h.1.vc, .inr ⟨by rw [h.2]; exact VG.Proof.MlDsa.KeyGen.ifn hn _ _, ?_⟩⟩
      obtain ⟨hh, e, _⟩ := h.1.hint
      exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e
        (by rw [Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1]; exact hn)
  · intro σ s _ ⟨h, _⟩ hn
    refine ⟨h.1, .inr ⟨by rw [h.2.1]; exact VG.Proof.MlDsa.KeyGen.ifn hn _ _, ?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ (Option.not_isSome_iff_eq_none.mp hn)]
    nofun

theorem ScalarCachePiece.mono {p : Params} {S : Nat} {I J I' J' : State → State → Prop} {code : Prog isa}
    (h : ScalarCachePiece p S I J code)
    (hi : ∀ σ s, I' σ s → I σ s) (hj : ∀ σ s, J σ s → J' σ s) : ScalarCachePiece p S I' J' code := by
  refine ⟨fun σ s hp hs hc => WP.mono (h.ok σ s hp (hi σ s hs) hc)
    (fun t ht => ⟨hj σ t ht.1, ht.2⟩), RelCT.mono h.tr ?_ ?_⟩
  · rintro x y ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, hm⟩
    exact ⟨⟨σ, τ, ps, pt, pub, ⟨hi _ _ hx.1, hx.2⟩, ⟨hi _ _ hy.1, hy.2⟩⟩, hm⟩
  · rintro x y ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, hm⟩
    exact ⟨⟨σ, τ, ps, pt, pub, ⟨hj _ _ hx.1, hx.2⟩, ⟨hj _ _ hy.1, hy.2⟩⟩, hm⟩

theorem ScalarCachePiece.of_vpiece {p : Params} {I J : State → State → Prop} {code : Prog isa}
    (hi : ∀ σ s, I σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (hj : ∀ σ s, J σ s → VG.Proof.MlDsa.AArch64.KeyGen.Top σ s)
    (h : VPiece p 16 I J code) (hd : 16 * code.aarch64Depth ≤ 16) :
    ScalarCachePiece p 16 I J code := ScalarCachePiece.of_old hi hj h.ok h.tr hd (by decide)

theorem samples_scalar_dle {P : Prims} (hP : PrimsOk P 16) (p : Params) :
    Message.DLe 1 (Impl.MlDsa.AArch64.Verify.samples P p) := by
  have hr := Message.DLe.of_fd hP.rejNtt.fd
  have hr4 := Message.DLe.of_fd hP.rej4.fd
  have hb := Message.DLe.of_fd hP.ball.fd
  unfold Impl.MlDsa.AArch64.Verify.samples
  dle_tac

theorem body_scalar_piece (v : Proof.Sha3.AArch64.Permutation) (hpaired : v.callee.pairedSha3 = false)
    {P : Prims} (hP : PrimsOk P 16) {p : Params} (hF : VFacts p) :
    ScalarCachePiece p 16 (fun σ s => VC p σ s ∧ s.gpr .x24 = 1)
      (VFin p) (Impl.MlDsa.AArch64.PreparedKey.Verify.body v.callee P p) := by
  simp only [Impl.MlDsa.AArch64.PreparedKey.Verify.body, hpaired, Bool.false_eq_true, ↓reduceIte]
  refine ScalarCachePiece.seq (ScalarCachePiece.of_vpiece (fun _ _ h => h.1.top)
    (fun _ _ h => h.1.top) (Verify.hint_vpiece hP hF) (Verify.Optimized.hint_depth hP p))
    (ScalarCachePiece.ifOk (T := fun σ => (hintOf p σ).isSome = true)
      (fun _ _ h => h.1.top) (fun _ _ h => h.1.top) (fun _ _ _ h => h.2.1)
      (fun _ _ _ _ pub => by rw [hintOf, hintOf, (vPub_eq pub).2.2.2.1]) ?_ ?_)
  · refine ScalarCachePiece.seq (J := Z0 p p.ℓ) ?_
      (ScalarCachePiece.ifOk (T := fun σ => normOk p σ p.ℓ)
        (fun _ _ h => h.1.vc.top) (fun _ _ h => h.1.top) (fun _ _ _ h => h.2)
        (fun _ _ _ _ pub => by simp only [normOk, zOf, (vPub_eq pub).2.2.2.1]) ?_ ?_)
    · refine ScalarCachePiece.mono (ScalarCachePiece.seqR (I := fun j => Z0 p j) p.ℓ 0
        (fun j _ hj => ScalarCachePiece.of_vpiece (fun _ _ h => h.1.vc.top)
          (fun _ _ h => h.1.vc.top) (Verify.zOne_vpiece hP hF (by omega))
          (Verify.Optimized.zOne_depth hP p j))) ?_ ?_
      · intro σ s ⟨⟨hv, hx, hH⟩, ht⟩
        refine ⟨⟨hv, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩, ?_⟩
        · obtain ⟨hh, e⟩ := Option.isSome_iff_exists.mp ht
          exact ⟨hh, e, hH hh e⟩
        · rw [hx]
          exact flag_congr (iff_of_true ht (Verify.normOk_zero p σ))
      · intro _ _ h; simpa only [Nat.zero_add] using h
    · exact (ScalarCachePiece.of_vpiece (fun _ _ h => h.1.1.vc.top)
        (fun _ _ h => h.vz.vc.top) (Verify.samples_vpiece hP hF) (depth16 (samples_scalar_dle hP p))).seq
        (compute_scalar_piece v hpaired hP hF)
    · intro σ s _ h hn
      refine ⟨h.1.vc, .inr ⟨by rw [h.2]; exact VG.Proof.MlDsa.KeyGen.ifn hn _ _, ?_⟩⟩
      obtain ⟨hh, e, _⟩ := h.1.hint
      exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e
        (by rw [Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1]; exact hn)
  · intro σ s _ h hn
    refine ⟨h.1, .inr ⟨by rw [h.2.1]; exact VG.Proof.MlDsa.KeyGen.ifn hn _ _, ?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ (Option.not_isSome_iff_eq_none.mp hn)]
    nofun

public theorem verify_core_correct (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp3 : Sign.Ok3 p)
    (σ : State) (hpre : (verifyCoreK p v.callee.pairedSha3).pre σ) :
    ∃ tr t, Exec isa (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) σ tr t ∧
      abiPreserved σ t ∧ (verifyCoreK p v.callee.pairedSha3).post σ t := by
  have hP := KeyGen.prims_okWith (keccak := v)
  have hF := vfacts hp3
  have hp := hpre.1
  have cache := hpre.2.2
  have main : WP isa (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) σ
      fun t => abiPreserved σ t ∧ (verifyContract p abi 16).post σ t := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.core
    by_cases hpair : v.callee.pairedSha3 = true
    · have pro := WP.optionalCache
        ((OptimizedSamples.rooted_piece (Verify.pro_vpiece hF) (by change 0 ≤ 16; decide) hP.s64).ok
          σ σ hp ⟨rfl, hpre.2.1 hpair⟩) cache (Nat.zero_le _) hP.s64
        (fun t ht => ht.1.1.top.cs .x21 (by decide))
        (fun t ht => ht.1.1.top.cs .x22 (by decide))
      refine WP.seq (WP.mono pro fun t ⟨ht, hc⟩ => ?_)
      refine WP.seq (WP.mono ((body_optimized_piece v hpair hP hF).ok σ t hp ht hc)
        fun u hu => ?_)
      exact (Verify.epi_vpiece hF).ok σ u hp hu.1
    · have hfalse : v.callee.pairedSha3 = false := Bool.eq_false_iff.mpr hpair
      have pro := WP.optionalCache ((Verify.pro_vpiece hF).ok σ σ hp rfl) cache (Nat.zero_le _) hP.s64
        (fun t ht => ht.1.top.cs .x21 (by decide)) (fun t ht => ht.1.top.cs .x22 (by decide))
      refine WP.seq (WP.mono pro fun t ⟨ht, hc⟩ => ?_)
      refine WP.seq (WP.mono ((body_scalar_piece v hfalse hP hF).ok σ t hp ht hc)
        fun u hu => ?_)
      exact (Verify.epi_vpiece hF).ok σ u hp hu.1
  obtain ⟨tr, t, he, hp⟩ := main
  exact ⟨tr, t, he, hp⟩

def CoreRel (p : Params) (optimized : Bool) (x y : State) : Prop :=
  (verifyCoreK p optimized).pre x ∧ (verifyCoreK p optimized).pre y ∧ (verifyCoreK p optimized).pub x y

theorem same_cache_metadata {σ τ x y : State} (hx : VG.Proof.MlDsa.AArch64.KeyGen.Top σ x)
    (hy : VG.Proof.MlDsa.AArch64.KeyGen.Top τ y) (h : SameIn [.x21, .x22] σ τ) :
    SameIn [.x21, .x22] x y := by
  refine ⟨fun r hr => ?_, by rw [hx.sp, hy.sp, h.2]⟩
  have hk : r ∈ VG.Proof.MlDsa.AArch64.KeyGen.untouched := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  rw [hx.cs r hk, hy.cs r hk, h.1 r hr]

theorem pro_optimized_tr (v : Proof.Sha3.AArch64.Permutation) (hpair : v.callee.pairedSha3 = true)
    {p : Params} (hF : VFacts p) :
    RelCT isa (CoreRel p v.callee.pairedSha3) (.block pro)
      (CachedVRel p 16 (fun σ s => (VC p σ s ∧ s.gpr .x24 = 1) ∧ Sign.StaticRoots 16 s)) := by
  intro x y tx ty u w ⟨hx, hy, pub⟩ ex ey
  have hP := KeyGen.prims_okWith (keccak := v)
  have trace := ((Verify.pro_vpiece hF).tr _ _ _ _ _ _
    ⟨x, y, hx.1, hy.1, pub.1, rfl, rfl⟩ ex ey).1
  have wx := WP.optionalCache
    ((OptimizedSamples.rooted_piece (Verify.pro_vpiece hF) (by change 0 ≤ 16; decide) hP.s64).ok
      x x hx.1 ⟨rfl, hx.2.1 hpair⟩) hx.2.2 (Nat.zero_le _) hP.s64
    (fun t ht => ht.1.1.top.cs .x21 (by decide)) (fun t ht => ht.1.1.top.cs .x22 (by decide))
  have wy := WP.optionalCache
    ((OptimizedSamples.rooted_piece (Verify.pro_vpiece hF) (by change 0 ≤ 16; decide) hP.s64).ok
      y y hy.1 ⟨rfl, hy.2.1 hpair⟩) hy.2.2 (Nat.zero_le _) hP.s64
    (fun t ht => ht.1.1.top.cs .x21 (by decide)) (fun t ht => ht.1.1.top.cs .x22 (by decide))
  obtain ⟨_, u', eu, hu⟩ := wx
  obtain ⟨_, w', ew, hw⟩ := wy
  obtain ⟨_, rfl⟩ := Exec.det ex eu
  obtain ⟨_, rfl⟩ := Exec.det ey ew
  refine ⟨trace, ⟨⟨x, y, hx.1, hy.1, pub.1, hu, hw⟩, ?_⟩,
    same_cache_metadata hu.1.1.1.top hw.1.1.1.top pub.2.2⟩
  have symbols := pub.2.1 hpair
  simpa only [Sign.RootSymbolsEq, VG.AArch64.Exec.syms ex, VG.AArch64.Exec.syms ey] using symbols

theorem pro_scalar_tr (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hF : VFacts p) :
    RelCT isa (CoreRel p v.callee.pairedSha3) (.block pro)
      (CachedScalarRel p 16 (fun σ s => VC p σ s ∧ s.gpr .x24 = 1)) := by
  intro x y tx ty u w ⟨hx, hy, pub⟩ ex ey
  have hP := KeyGen.prims_okWith (keccak := v)
  have trace := ((Verify.pro_vpiece hF).tr _ _ _ _ _ _
    ⟨x, y, hx.1, hy.1, pub.1, rfl, rfl⟩ ex ey).1
  have wx := WP.optionalCache ((Verify.pro_vpiece hF).ok x x hx.1 rfl) hx.2.2 (Nat.zero_le _) hP.s64
    (fun t ht => ht.1.top.cs .x21 (by decide)) (fun t ht => ht.1.top.cs .x22 (by decide))
  have wy := WP.optionalCache ((Verify.pro_vpiece hF).ok y y hy.1 rfl) hy.2.2 (Nat.zero_le _) hP.s64
    (fun t ht => ht.1.top.cs .x21 (by decide)) (fun t ht => ht.1.top.cs .x22 (by decide))
  obtain ⟨_, u', eu, hu⟩ := wx
  obtain ⟨_, w', ew, hw⟩ := wy
  obtain ⟨_, rfl⟩ := Exec.det ex eu
  obtain ⟨_, rfl⟩ := Exec.det ey ew
  exact ⟨trace, ⟨x, y, hx.1, hy.1, pub.1, hu, hw⟩,
    same_cache_metadata hu.1.1.top hw.1.1.top pub.2.2⟩

public theorem verify_core_ct (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp3 : Sign.Ok3 p) :
    ConstantTime isa (verifyCoreK p v.callee.pairedSha3).pre (verifyCoreK p v.callee.pairedSha3).pub
      (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) := by
  have hP := KeyGen.prims_okWith (keccak := v)
  have hF := vfacts hp3
  have trace : RelCT isa (CoreRel p v.callee.pairedSha3)
      (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) (fun _ _ => True) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.core
    by_cases hpair : v.callee.pairedSha3 = true
    · refine RelCT.seq (pro_optimized_tr v hpair hF)
        (RelCT.seq (body_optimized_piece v hpair hP hF).tr ?_)
      refine RelCT.mono (Verify.epi_vpiece (S := 16) hF).tr ?_ (fun _ _ _ => trivial)
      rintro x y ⟨⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, _⟩, _⟩
      exact ⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩
    · have hfalse : v.callee.pairedSha3 = false := Bool.eq_false_iff.mpr hpair
      refine RelCT.seq (pro_scalar_tr v hF) (RelCT.seq (body_scalar_piece v hfalse hP hF).tr ?_)
      refine RelCT.mono (Verify.epi_vpiece (S := 16) hF).tr ?_ (fun _ _ _ => trivial)
      rintro x y ⟨⟨σ, τ, ps, pt, pub, hx, hy⟩, _⟩
      exact ⟨σ, τ, ps, pt, pub, hx.1, hy.1⟩
  intro x y tx ty u w hx hy pub ex ey
  exact (trace _ _ _ _ _ _ ⟨hx, hy, pub⟩ ex ey).1

public theorem verify_core_dle (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.core v.callee (primsWith v.callee) p) := by
  have hP := KeyGen.prims_okWith (keccak := v)
  have hvec := Message.DLe.seqR (fun i => forward_dle v hP p (zP p i)) 0 p.ℓ
  have hforward := forward_dle v hP p (cP p)
  have hrows := Message.DLe.seqR (fun r => row_dle v hP p r) 0 p.k
  have hfinish := finish_dle v p
  have hcomp : Message.DLe 1 (Impl.MlDsa.AArch64.PreparedKey.Verify.compute v.callee (primsWith v.callee) p) := by
    unfold Impl.MlDsa.AArch64.PreparedKey.Verify.compute
    exact Message.DLe.seq hvec (Message.DLe.seq hforward (Message.DLe.seq hrows hfinish))
  have hhint := Message.DLe.of_fd (Verify.Optimized.hint_depth hP p)
  have hz := Message.DLe.seqR (fun i => Message.DLe.of_fd (Verify.Optimized.zOne_depth hP p i)) 0 p.ℓ
  have hsamples : Message.DLe 1 (if v.callee.pairedSha3 then
      Impl.MlDsa.AArch64.Verify.OptimizedSamples.samples (primsWith v.callee) p
      else Impl.MlDsa.AArch64.Verify.samples (primsWith v.callee) p) := by
    split
    · exact Message.DLe.of_fd (OptimizedSamples.samples_depth hP p)
    · exact samples_scalar_dle hP p
  unfold Impl.MlDsa.AArch64.PreparedKey.Verify.core Impl.MlDsa.AArch64.PreparedKey.Verify.body
  dle_tac

end VG.Proof.MlDsa.AArch64.PreparedKey

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Verify.Optimized

def selectedConsts (v : Proof.Sha3.AArch64.Permutation) : List (String × List (BitVec 64)) :=
  if v.callee.pairedSha3 then Sign.signRootConsts else []

def selectedAbi (v : Proof.Sha3.AArch64.Permutation) : Abi isa :=
  abi.withConsts (selectedConsts v)

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
