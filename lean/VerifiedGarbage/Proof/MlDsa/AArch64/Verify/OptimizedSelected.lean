module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedVerifyCallPre
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedTop

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Verified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CachedVerifyVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Inst
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
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifySat
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.RootedCachedVerifyCorrect
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

section
variable {p : Params} {S : Nat} {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : Piece p S I J c₁) (h₂ : Piece p S J K c₂) :
    Piece p S I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (rootPair_progress h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : Piece p S I J c)
    (hI : ∀ σ s, vPre p S σ → I' σ s → I σ s) (hJ : ∀ σ s, vPre p S σ → J σ s → J' σ s) :
    Piece p S I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩,et⟩ => ⟨⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩,et⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → Piece p S (I k) (I (k + 1)) (f k)) →
      Piece p S (I a) (I (a + n)) (seqR f a n)
  | n, a, h =>
    ⟨fun σ s hp hs => seqR_ok (I := fun k => I k σ) n a (fun k h₁ h₂ s hs => (h k h₁ h₂).ok σ s hp hs) s hs,
      RelCT.mono (seqR_tr (Q := fun k => RootPair p S (I k)) n a fun k h₁ h₂ => rootPair_progress (h k h₁ h₂).ok (h k h₁ h₂).tr)
        (fun _ _ h => h) fun _ _ _ => trivial⟩

theorem Piece.ifOk {c : Prog isa} {T : State → Prop} [DecidablePred T]
    (hx : ∀ σ s, vPre p S σ → I σ s → s.gpr .x24 = if T σ then 1 else 0)
    (hT : ∀ σ₁ σ₂, vPre p S σ₁ → vPre p S σ₂ → vPub p S σ₁ σ₂ → (T σ₁ ↔ T σ₂))
    (ht : Piece p S (fun σ s => I σ s ∧ T σ) J c) (he : ∀ σ s, vPre p S σ → I σ s → ¬ T σ → J σ s) :
    Piece p S I J (ifOk c) := by
  have ev : ∀ σ s, vPre p S σ → I σ s → isa.eval (.nonzero .x .x24) s = some (decide (T σ)) := fun σ s hp hs => by
    rw [eval24, hx σ s hp hs]; by_cases h : T σ <;> simp [h]
  refine ⟨fun σ s hp hs => WP.ite (decide (T σ)) (ev σ s hp hs) (fun hb => ht.ok σ s hp ⟨hs, of_decide_eq_true hb⟩)
    fun hb => WP.block_nil (he σ s hp hs (of_decide_eq_false hb)), relIte ?_ ?_ ?_⟩
  · rintro x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩,et⟩
    rw [ev σ₁ x p₁ h₁, ev σ₂ y p₂ h₂, decide_eq_decide.mpr (hT σ₁ σ₂ p₁ p₂ pub)]
  · refine RelCT.mono ht.tr (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩,et⟩, hc⟩ => ?_) fun _ _ h => h
    rw [ev σ₁ x p₁ h₁] at hc
    have t₁ : T σ₁ := of_decide_eq_true (Option.some.inj hc)
    exact ⟨⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, t₁⟩, h₂, (hT σ₁ σ₂ p₁ p₂ pub).mp t₁⟩,et⟩
  · exact RelCT.block_nil fun _ _ _ => trivial

end

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

section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen

/-- All arithmetic uses the same Montgomery factor until the inverse removes
it; packed output is identical to the canonical verification algorithm. -/
theorem row_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) {h : List (Vector Bool n)} {A' : Nat→Nat→Poly}
    {c0 : Poly} {q : Bool} {r : Nat} (hr : r<p.k)
    (hs : SC p S σ h A' c0 q p.ℓ true r s) :
    WP isa (Impl.MlDsa.AArch64.Verify.Optimized.row P p r) s (SC p S σ h A' c0 q p.ℓ true (r+1)) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.row
  refine WP.seq (WP.mono (dot_ok hF hp hr hs) fun s ⟨hs,hw⟩=>?_)
  refine WP.seq (WP.mono (unpack_ok hP hF hp hr hs hw) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (nttT_ok hF hp hr hs hw ht) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (product_ok hF hp hr hs hw ht) fun s ⟨hs,hw,ht⟩=>?_)
  refine WP.seq (WP.mono (subtract_ok hF hp hr hs hw ht) fun s ⟨hs,hw⟩=>?_)
  refine WP.seq (WP.mono (inverse_ok hF hp hr hs hw) fun s ⟨hs,hw⟩=>?_)
  exact hintPack_ok hF hp hr hs hw

end VG.Proof.MlDsa.AArch64.Verify.Optimized
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

theorem rows_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) (hs : SCx p S p.ℓ true 0 σ s) :
    WP isa (seqR (Impl.MlDsa.AArch64.Verify.Optimized.row P p) 0 p.k) s
      (SCx p S p.ℓ true p.k σ) := by
  simpa only [Nat.zero_add] using seqR_ok (I:=fun r=>SCx p S p.ℓ true r σ) p.k 0
    (fun r _ hr s ⟨h,A,c,q,hs⟩=>WP.mono (row_ok hP hF hp (by omega) hs)
      fun t ht=>⟨h,A,c,q,ht⟩) s hs

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

theorem row_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {r : Nat} (hr : r<p.k) :
    RelCT isa (RootPair p S (SCx p S p.ℓ true r)) (Impl.MlDsa.AArch64.Verify.Optimized.row P p r)
      (RootPair p S (SCx p S p.ℓ true (r+1))) := by
  exact (dot_tr hF hr).seq ((unpack_tr hP hF hr).seq ((nttT_tr hF hr).seq
    ((product_tr hF hr).seq ((subtract_tr hF hP.s64 hr).seq
      ((inverse_tr hF hr).seq (hintPack_tr hF hr))))))
end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedCompute.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem compute_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>VB p σ s ∧ Sign.StaticRoots S s) (VFin p)
      (Impl.MlDsa.AArch64.Verify.Optimized.computeWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.computeWith
  refine Piece.seq (J:=SCx p S p.ℓ false 0) ?_ (Piece.seq (J:=SCx p S p.ℓ true 0) ?_
    (Piece.seq (J:=SCx p S p.ℓ true p.k) ?_ (Piece.of_vpiece (finish_vpiece hP.s16 hP.s64 hF))))
  · refine ⟨fun σ s hp hs=>nttZ_vector_ok hF hp (vb_sc hs.1 hs.2),?_⟩
    exact (nttZ_vector_tr hF).mono
      (fun _ _ ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,et⟩=>⟨⟨σ,τ,hσ,hτ,pub,vb_sc ix.1 ix.2,vb_sc iy.1 iy.2⟩,et⟩)
      (fun _ _ _=>trivial)
  · refine ⟨fun σ s hp ⟨h,A,c,q,hs⟩=>WP.mono (nttC_ok hF hp hs) fun t ht=>⟨h,A,c,q,ht⟩,?_⟩
    exact (nttC_tr hF).mono (fun _ _ h=>h) (fun _ _ _=>trivial)
  · refine ⟨fun σ s hp hs=>rows_ok hP hF hp hs,?_⟩
    have ht := seqR_tr (Q:=fun r=>RootPair p S (SCx p S p.ℓ true r)) p.k 0
      fun r _ hr=>row_tr hP hF (by omega)
    exact ht.mono (fun _ _ h=>h) (fun _ _ _=>trivial)

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

theorem body_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>(VC p σ s ∧ s.gpr .x24=1) ∧ Sign.StaticRoots S s) (VFin p)
      (Impl.MlDsa.AArch64.Verify.Optimized.bodyWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.bodyWith
  refine (Piece.of_vpiece (OptimizedSamples.rooted_piece (hint_vpiece hP hF) (hint_depth hP p) hP.s64)).seq
    (Piece.ifOk (T:=fun σ=>(hintOf p σ).isSome=true) (fun _ _ _ h=>h.1.2.1)
      (fun _ _ _ _ pub=>by rw [hintOf,hintOf,(vPub_eq pub).2.2.2.1]) ?_ ?_)
  · refine Piece.seq (J:=fun σ s=>Z0 p p.ℓ σ s ∧ Sign.StaticRoots S s) ?_
      (Piece.ifOk (T:=fun σ=>normOk p σ p.ℓ) (fun _ _ _ h=>h.1.2)
        (fun _ _ _ _ pub=>by simp only [normOk,zOf,(vPub_eq pub).2.2.2.1]) ?_ ?_)
    · refine Piece.mono (Piece.seqR (I:=fun j σ s=>Z0 p j σ s ∧ Sign.StaticRoots S s) p.ℓ 0
        fun j _ hj=>Piece.of_vpiece (OptimizedSamples.rooted_piece (zOne_vpiece hP hF (by omega))
          (zOne_depth hP p j) hP.s64)) ?_ ?_
      · intro σ s _ ⟨⟨⟨hv,hx,hH⟩,roots⟩,ht⟩
        refine ⟨⟨⟨hv,?_,fun _ h=>absurd h (Nat.not_lt_zero _)⟩,?_⟩,roots⟩
        · obtain ⟨hh,e⟩:=Option.isSome_iff_exists.mp ht
          exact ⟨hh,e,hH hh e⟩
        · rw [hx];exact flag_congr (iff_of_true ht (normOk_zero p σ))
      · intro _ _ _ h;simpa only [Nat.zero_add] using h
    · refine (Piece.of_vpiece (OptimizedSamples.samples_rooted_vpiece hP hF)).seq (compute_piece hP hF) |>.mono ?_ (fun _ _ _ h=>h)
      intro _ _ _ ⟨⟨hz,roots⟩,hn⟩
      exact ⟨⟨hz,hn⟩,roots⟩
    · intro σ s _ ⟨h,roots⟩ hn
      refine ⟨h.1.vc,.inr ⟨by rw [h.2];exact ifn hn _ _,?_⟩⟩
      obtain ⟨hh,e,_⟩:=h.1.hint
      exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e
        (by rw [Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1];exact hn)
  · intro σ s _ ⟨h,roots⟩ hn
    refine ⟨h.1,.inr ⟨by rw [h.2.1];exact ifn hn _ _,?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ (Option.not_isSome_iff_eq_none.mp hn)]
    nofun

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedPre.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)
open VG.Proof.MlDsa.AArch64.Optimized

def rootRegions (s : State) : List Region :=
  [⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩]

theorem entry {p : Params} {S : Nat} {s : State} (hS : 0<S)
    (h : (verifyContract p (abi.withConsts signRootConsts) S).pre s) :
    vPre p S s ∧ StaticRoots S s := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hS)
  sig_pre [verifyContract,verifySig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq,
    Abi.constRegions,Abi.constsHeld,TableConstants.staticNttWords_length,
    InverseTable.expandedWords_length,stackBelow,List.range,List.range.loop] at h
  obtain ⟨hsp,hd,hf,hi,hff,hfw,hfs,hif,hiw,his,hfa,hia,ht,hw,d1,d2,d3,
    k1,k2,k3,k4,n1,n2,n3,n4⟩ := h
  have hrd : s.rd=vInputs p s++rootRegions s := by
    rw [←List.take_append_drop (s.rd.length-2) s.rd,ht,hd]
    rfl
  refine ⟨⟨?_,fun r hr=>by rw [hrd]; exact List.mem_append_left _ hr⟩,
    ⟨⟨hf,hff,?_,hfw,?_,hfa⟩,⟨hi,hif,?_,hiw,?_,hia⟩⟩⟩
  · sig_pre [verifyContract,verifySig,abi,argRegs,List.range,List.range.loop]
    exact ⟨hsp,rfl,hw,d1,d2,d3,k1,k2,k3,k4,n1,n2,n3,n4⟩
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_NTT_EXPANDED",3904⟩,by rw [hrd]; simp [rootRegions],Region.contains_self _ _⟩
  · exact hfs
  · apply Covers.one
    exact ⟨⟨s.syms "VG_MLDSA_INV_FOLDED",3904⟩,by rw [hrd]; simp [rootRegions],Region.contains_self _ _⟩
  · exact his

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedContract.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Sign (Ok3 StaticRoots RootSymbolsEq signRootConsts)

/-- Internal proof boundary retains the original verifier semantics and adds
only the immutable transform tables and their public addresses. -/
def verifyK (p : Params) (S : Nat) : Contract isa where
  pre s := vPre p S s ∧ StaticRoots S s
  post := (verifyContract p abi S).post
  pub s t := vPub p S s t ∧ RootSymbolsEq s t

theorem shared_pub {p : Params} {S : Nat} {s t : State}
    (h : (verifyContract p (abi.withConsts signRootConsts) S).pub s t) :
    vPub p S s t ∧ RootSymbolsEq s t := by
  sig_pub [verifyContract,verifySig,abi,argRegs,Abi.withConsts,Sign.signRootConsts_eq] at h
  obtain ⟨hsp,hf,hi,hb,h0,h1,h2,h3⟩ := h
  refine ⟨?_,hf,hi⟩
  unfold vPub
  sig_pub [verifyContract,verifySig,abi,argRegs]
  exact ⟨hsp,hb,h0,h1,h2,h3⟩

theorem verifyK_implies {p : Params} (hp : Ok3 p) :
    (verifyK p 16).Implies (verifyContract p (abi.withConsts signRootConsts) 16) where
  pre := fun _ h=>entry (by decide) h
  post := by
    sig_implies_post [verifyK,verifyContract,verifySig,abi,argRegs,Abi.withConsts]
  pub := fun _ _ _ _ h=>shared_pub h
  sat := ⟨verifySat p,verify_sat hp⟩

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedVerified.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem verify_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>s=σ ∧ Sign.StaticRoots S s)
      (fun σ s=>abiPreserved σ s ∧ (verifyContract p abi S).post σ s)
      (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.verifyWith
  exact (Piece.of_vpiece (OptimizedSamples.rooted_piece (pro_vpiece hF)
    (by change 0≤S;omega) hP.s64)).seq
    ((body_piece hP hF).seq (Piece.of_vpiece (epi_vpiece hF)))

/-- Exact optimized verification under the unchanged public algorithm,
with only the two immutable artifact tables supplied by the ABI. -/
theorem verify_verified {P : Prims} (hP : PrimsOk P 16) {p : Params}
    (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) :
    Verified target (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith keccak.callee P p)
      (verifyContract p (abi.withConsts Sign.signRootConsts) 16) := by
  apply Verified.of_correct (k:=verifyK p 16)
  · intro σ h
    exact (verify_piece hP (vfacts hp)).ok σ σ h.1 ⟨rfl,h.2⟩
  · intro s t ts tt u v hs ht pub es et
    exact ((verify_piece hP (vfacts hp)).tr _ _ _ _ _ _
      ⟨⟨s,t,hs.1,ht.1,pub.1,⟨rfl,hs.2⟩,⟨rfl,ht.2⟩⟩,pub.2⟩ es et).1
  · exact verifyK_implies hp

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Verify/OptimizedDepth.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Message

/-- The selected arithmetic kernels have no nested stack frame; only the
existing sponge calls need the 16-byte stack reservation. -/
theorem verify_dle (v : Proof.Sha3.AArch64.Permutation) {P : Prims}
    (hP : PrimsOk P 16) (p : Params) :
    DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee P p) := by
  obtain ⟨ha,hpad,hs⟩ := keccak_dle v
  have hh := DLe.of_fd hP.hintUnpack.fd
  have hu := DLe.of_fd hP.bitUnpack.fd
  have ht := DLe.of_fd hP.unpackT1.fd
  have hnorm := DLe.of_fd hP.normLt.fd
  have hsample := DLe.of_fd (OptimizedSamples.samples_depth hP p)
  have hn := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.positiveNtt_callee 16).fd
  have hi := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.Inverse.inverseSingle_callee 16).fd
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.MontDot.dot p.ℓ) := by
    unfold Impl.MlDsa.AArch64.Optimized.MontDot.dot
    dle_tac
  have hm : DLe 1 Impl.MlDsa.AArch64.Optimized.MontProduct.code := by
    unfold Impl.MlDsa.AArch64.Optimized.MontProduct.code
    dle_tac
  have hsub : DLe 1 (Impl.MlDsa.AArch64.Optimized.AddSub.code true) := by
    unfold Impl.MlDsa.AArch64.Optimized.AddSub.code
    dle_tac
  have hpack : DLe 1 Impl.MlDsa.AArch64.Optimized.UseHintPack.prog := by
    unfold Impl.MlDsa.AArch64.Optimized.UseHintPack.prog
      Impl.MlDsa.AArch64.Round.zext Impl.MlDsa.AArch64.Round.onGamma
      Impl.MlDsa.AArch64.Optimized.UseHintPack.code
    dle_tac
  unfold Impl.MlDsa.AArch64.Verify.Optimized.verifyWith
    Impl.MlDsa.AArch64.Verify.Optimized.bodyWith
    Impl.MlDsa.AArch64.Verify.Optimized.computeWith
  repeat' (first
    | with_reducible assumption
    | (apply DLe.call; with_reducible assumption)
    | apply DLe.seq
    | apply DLe.ite
    | apply DLe.loop
    | (apply DLe.seqR; intro)
    | apply DLe.block)

/-- Every standard optimized raw verifier fits the existing stack budget,
for either verified Keccak permutation. -/
theorem verifyWith_dle (v : Proof.Sha3.AArch64.Permutation) (p : Params) :
    DLe 1 (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (primsWith v.callee) p) :=
  verify_dle v (KeyGen.prims_okWith (keccak:=v)) p

end VG.Proof.MlDsa.AArch64.Verify.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Optimized/RootedCachedVerifyVerified.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Message
open VG.Impl.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts)

/-- Cached-key message verification with both immutable transform tables,
original public leakage, and the unchanged cached-digest semantics. -/
theorem verifyMessage_verified (v : Proof.Sha3.AArch64.Permutation)
    {p : Params} {n : String} {c : Prog isa}
    (hV : Message.OptimizedVerify.VerifyFn p c) (hp : p ∈ params) :
    Verified AArch64.target (verifyMessageCached v.callee n c p)
      (verifyMessageCachedContract p (abi.withConsts signRootConsts) 16) := by
  refine ⟨fun _ h=>let ⟨tr,t,he,ha,hq⟩:=verifyMessageCached_wp v hV hp h;⟨tr,t,he,ha,hq⟩,
    verifyMessage_ct v hV hp,verifySat p,verify_sat ?_⟩
  simpa only [Sign.Ok3,params,List.mem_cons,List.not_mem_nil,or_false] using hp

end VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Verify.Optimized

/-- The feature-selected raw verifier shared by all public wrappers. -/
def selectedCode (v : Proof.Sha3.AArch64.Permutation) (p : Params) : Prog isa :=
  if v.callee.pairedSha3 then
    Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p
  else Impl.MlDsa.AArch64.Verify.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p

def selectedConsts (v : Proof.Sha3.AArch64.Permutation) : List (String × List (BitVec 64)) :=
  if v.callee.pairedSha3 then Sign.signRootConsts else []

def selectedAbi (v : Proof.Sha3.AArch64.Permutation) : Abi isa :=
  abi.withConsts (selectedConsts v)

theorem selected_verify_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    Verified target (selectedCode v p) (verifyContract p (selectedAbi v) 16) := by
  unfold selectedCode selectedAbi selectedConsts
  split
  · exact Optimized.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) hp
  · exact Verify.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) p hp (Verify.verify_sat p hp)

theorem optimizedVerifyFn (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p) :
    Message.OptimizedVerify.VerifyFn p
      (Impl.MlDsa.AArch64.Verify.Optimized.verifyWith v.callee (Impl.MlDsa.AArch64.KeyGen.primsWith v.callee) p) :=
  ⟨Optimized.verify_verified (keccak:=v) (KeyGen.prims_okWith (keccak:=v)) hp,verifyWith_dle v p⟩

theorem selected_cached_message_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hp : Sign.Ok3 p)
    (n : String) :
    Verified target (Impl.MlDsa.AArch64.Optimized.verifyMessageCached v.callee n (selectedCode v p) p)
      (verifyMessageCachedContract p (selectedAbi v) 16) := by
  have hm : p∈Message.params := by simpa only [Sign.Ok3,Message.params,List.mem_cons,List.not_mem_nil,or_false] using hp
  unfold selectedCode selectedAbi selectedConsts
  split
  · exact VG.Proof.MlDsa.AArch64.Optimized.RootedCachedVerify.verifyMessage_verified v (optimizedVerifyFn v hp) hm
  · exact VG.Proof.MlDsa.AArch64.Optimized.CachedVerify.verifyMessage_verified v (Message.verifyFn v hm) hm

end VG.Proof.MlDsa.AArch64.Verify.OptimizedSelected
