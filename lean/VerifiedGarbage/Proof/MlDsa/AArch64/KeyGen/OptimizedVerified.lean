module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsEntry
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedDepth
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSat
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Optimized
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp
public import VerifiedGarbage.Proof.MlDsa.RejNTT2Contract
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedMatrix
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCallTwo
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Call4
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Samp4
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MatrixMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MatrixMask
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Blocks
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedEntry
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.CallRound
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestRow
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotCallTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedNtt
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestPack
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedRest
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.PrimsOk
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
public import VerifiedGarbage.Spec.MlDsa
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seed4
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Seed4
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRestState
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRestState
meta import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Main
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejOutcome
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejPublic
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv
import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedDot
import VerifiedGarbage.Proof.MlKem.Arith
public import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inv
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit

/-! ### `MlDsa.AArch64.KeyGen.OptimizedTimingBase`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64
open VG.Spec.MlDsa (Params)

/-- Immutable table addresses are public, while every polynomial value keeps
its original secrecy classification. -/
def TableEq (x y : State) : Prop :=
  x.syms "VG_MLDSA_NTT_EXPANDED"=y.syms "VG_MLDSA_NTT_EXPANDED" ∧
  x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED"

def RootPair (p : Params) (S : Nat) (I : State → State → Prop) (x y : State) : Prop :=
  R p S (fun σ s => I σ s ∧ Sign.StaticRoots S s) x y ∧ TableEq x y

/-- Lift functional progress into the timing invariant without revealing any
additional input value. Symbol maps are preserved by execution semantics. -/
theorem rootPair_progress {p : Params} {S : Nat} {I J : State → State → Prop} {c : Prog isa}
    (hw : ∀σ s,kgPre p S σ → I σ s → Sign.StaticRoots S s →
      WP isa c s fun t => J σ t ∧ Sign.StaticRoots S t)
    (ht : RelCT isa (RootPair p S I) c fun _ _ => True) :
    RelCT isa (RootPair p S I) c (RootPair p S J) := by
  intro x y tx ty u v hr ex ey
  obtain ⟨he,_⟩ := ht _ _ _ _ _ _ hr ex ey
  obtain ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,et⟩ := hr
  obtain ⟨_,u',eu,ju⟩ := hw σ x hσ ix.1 ix.2
  obtain ⟨_,v',ev,jv⟩ := hw τ y hτ iy.1 iy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  refine ⟨he,⟨σ,τ,hσ,hτ,pub,ju,jv⟩,?_⟩
  simpa only [TableEq,VG.AArch64.Exec.syms eu,VG.AArch64.Exec.syms ev] using et

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

/-! ### `MlDsa.AArch64.KeyGen.OptimizedRest`, which only this module used -/

section

/-! ### `MlDsa.AArch64.KeyGen.OptimizedRow`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.KeyGen.OptimizedDotValue`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.KeyGen.OptimizedDot`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.Inverse

abbrev dotWrites (p : Params) (_i : Nat) : List (Ptr × Nat) := [(tP p,1024),(sc oSS,1024)]

def optimizedDotChk (p : Params) (i : Nat) : Bool :=
  let o := tP p; let a := aP (p.ℓ*i); let b := sP p 0; let z := sc oSS
  inB (kgR++kgW p) o 1024 && inB (kgR++kgW p) a (1024*p.ℓ) &&
  inB (kgR++kgW p) b (1024*p.ℓ) && inB (kgR++kgW p) z 1024 &&
  inB (kgW p) o 1024 && inB (kgW p) z 1024 &&
  sepB (kgR) (kgW p) o 1024 a (1024*p.ℓ) &&
  sepB (kgR) (kgW p) o 1024 b (1024*p.ℓ) &&
  sepB (kgR) (kgW p) o 1024 z 1024 &&
  sepB (kgR) (kgW p) a (1024*p.ℓ) z 1024 &&
  sepB (kgR) (kgW p) b (1024*p.ℓ) z 1024 && kcChk p (dotWrites p i)

theorem optimizedDotChk_ok {p : Params} (hp : PFacts p) : ∀i<p.k,optimizedDotChk p i=true := by
  rcases hp.mem with rfl | rfl | rfl <;> decide

theorem optimizedDotReady {p : Params} (hp : PFacts p) {S : Nat} {σ s : State} {i : Nat}
    (hc : optimizedDotChk p i=true) (hpre : kgPre p S σ) (hs : KC p σ s) (roots : Sign.StaticRoots S s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) :
    DotCallReady p.ℓ (tP p) (aP (p.ℓ*i)) (sP p 0) (sc oSS) s := by
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,oa⟩,ob⟩,oz⟩,az⟩,bz⟩,_⟩ := hc
  have L := hs.lay hp hpre
  refine ⟨L.nwp ro,L.nwp ra,L.nwp rb,L.nwp rz,roots.inverse.held,roots.inverse.fit,?_,
    L.disj oa,L.disj ob,L.disj oz,L.disj az,L.disj bz,ha,hb,?_,?_,roots.inverse.aligned⟩
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact roots.inverse.apart_write (L.inW wo)
    · exact roots.inverse.apart_write (L.inW wz)
  · exact Covers.cons (L.cR ra) (Covers.cons (L.cR rb)
      (Covers.cons roots.inverse.readable (Covers.cons (L.cR ro) (L.cR rz))))
  · exact Covers.cons (L.cW wo) (L.cW wz)

/-- Fused row arithmetic preserves all polynomial families outside its two
write slots. The returned frame can be applied directly to Fam/PosFam. -/
theorem optimizedDot_ok {p : Params} {S : Nat} {σ s : State} {i : Nat}
    (hp : PFacts p) (hc : optimizedDotChk p i=true) (hpre : kgPre p S σ) (hs : KC p σ s) (roots : Sign.StaticRoots S s)
    (ha : ∀j<p.ℓ,PositiveReduced s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
    (hb : ∀j<p.ℓ,PositiveReduced s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) s fun t =>
      KC p σ t ∧ Sign.StaticRoots S t ∧ t.gpr .x24=s.gpr .x24 ∧ PPostB S s t (dotWrites p i) ∧
      PolyIs t.mem (pa t (tP p)) (nttInv (dotNTT
        (fun j => polyAt s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
        (fun j => polyAt s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ)) := by
  have ready := optimizedDotReady hp hc hpre hs roots ha hb
  simp only [optimizedDotChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ro,ra⟩,rb⟩,rz⟩,wo⟩,wz⟩,_⟩,_⟩,_⟩,_⟩,_⟩,st⟩ := hc
  have hn : p.ℓ=4 ∨ p.ℓ=5 ∨ p.ℓ=7 := by rcases hp.mem with rfl | rfl | rfl <;> decide
  have L := hs.lay hp hpre
  refine WP.mono_syms (dotAt_ok L.s64 hn (ptr_ok (L.ptrBs ro)) (ptr_ok (L.ptrBs ra))
    (ptr_ok (L.ptrBs rb)) (ptr_ok (L.ptrBs rz)) ready) fun t ⟨hP,hv⟩ hy => ?_
  have hpB : PPostB S s t (dotWrites p i) := hP.b
  refine ⟨hs.step hp hpre hpB st,roots.step_layout L hpB hy ?_,hP.cs .x24 (by decide) (by decide),hpB,?_⟩
  · intro w hw
    simp only [dotWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact wo
    · exact wz
  · rw [hpB.pa (L.ptrBs ro)]; exact hv


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.KeyGen (dotK)

private theorem poly_addr (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j))) =
      pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

/-- The fused inverse consumes the lazy secret transforms directly. Its
canonical row is the same field sum as the scalar reference key generator. -/
theorem dotRow_value {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {i : Nat}
    (hi : i<p.k) (h : PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i s)
    (roots : Sign.StaticRoots S' s) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) s fun t =>
      PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i t ∧ Sign.StaticRoots S' t ∧
      PolyIs t.mem (pa t (tP p)) (nttInv (dotK p A S i p.ℓ)) := by
  have hA j (hj : j<p.ℓ) : PolyIs s.mem
      (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)) (A (p.ℓ*i+j)) := by
    have hv := h.aS _ (idx_lt hi hj)
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*i+j)))) _ at hv
    rw [poly_addr] at hv
    exact hv
  have hB j (hj : j<p.ℓ) : PosPolyIs s.mem
      (pa s (sP p 0)+BitVec.ofNat 64 (1024*j)) (ntt (toRq (S j))) := by
    have hv := h.s1 j hj
    simp only [ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+j)))) _ at hv
    rw [poly_addr] at hv
    simpa only [sP,Nat.add_zero] using hv
  refine WP.mono (optimizedDot_ok hF (optimizedDotChk_ok hF i hi) hp h.kc roots
    (fun j hj => (PosPolyIs.of_canonical (hA j hj)).bound)
    (fun j hj => (hB j hj).bound)) fun t ⟨_,rt,h24,hP,hv⟩ => ?_
  have hc : KRChk p (p.ℓ+p.k) p.ℓ i (dotWrites p i) := by
    have hk := hF.k; have hl := hF.l; have hs := hF.scr
    exact KRChk.append (ws₁ := [_])
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [SV, oP]; omega_using []) (.inr (Nat.le_refl _))
        (by rw [hs]; simp only [oP]; omega_using []))
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_of_lt hi) (by simp only [SV, oSS]; omega_using [])
        (.inl (by simp only [oSS, oP]; omega_using [])) (by rw [hs]; simp only [oSS]; omega_using []))
  refine ⟨h.keep hF hp hP h24 hc,rt,?_⟩
  have he : dotNTT
      (fun j => polyAt s.mem (pa s (aP (p.ℓ*i))+BitVec.ofNat 64 (1024*j)))
      (fun j => polyAt s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j))) p.ℓ = dotK p A S i p.ℓ := by
    unfold dotNTT dotK
    apply congrArg (List.foldl add zero)
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    dsimp only
    rw [(hA j hj).2,(hB j hj).value]
  simpa only [he] using hv

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRoundCall.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized (power2RoundAt)
open VG.Impl.MlDsa.AArch64.Call (Ptr)

theorem p2rAt_ok {S : Nat} (hS : S < 2 ^ 64) {P : Prims}
    (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {t t1 t0 : Ptr}
    (hc : p2rChk rbs wbs t t1 t0 = true) (hr : Reduced s.mem (pa s t)) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P t t1 t0) s fun s' => PPostB S s s' [(t1, 1024), (t0, 1024)] ∧
      s'.gpr .x24 = s.gpr .x24 ∧
      NatPolyIs s'.mem (pa s t1) ((polyAt s.mem (pa s t)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (pa s t0) ((polyAt s.mem (pa s t)).map fun c => ofInt (power2Round c).2) := by
  have hc' := hc
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  refine WP.mono (callAt_ok hS C (p2r_args L.ok c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => p2r_pre L hc hr h1) (p2r_cov L hc).1 (p2r_cov L hc).2)
    fun s' ⟨hP, s1, h1, hq⟩ => ⟨hP.b, hP.cs .x24 (by decide) (by decide), ?_⟩
  sig_post [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs] at hq
  rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.mem h1] at hq
  exact hq


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)

section
variable {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {σ : State} (hp : kgPre p S' σ)
  {i : Nat} (hi : i < p.k)
include hP hF hp hi

theorem addS2_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => nttInv (dotK p A S i p.ℓ)) A S s) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.addAt P (tP p) (sP p (p.ℓ + i))) s fun s' =>
      PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p (fun A S => tK p A S i) A S s' := by
  dsimp only [tIs] at ht
  have L := h.kc.lay hF hp
  have hS := h.s2 i hi
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.addAt
  refine WP.mono (accAt_ok (op := add) hP.s64 hP.add L (add_chk hF hi) ht.1 hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (chk_t hF hi), ?_⟩
  rw [tIs, hP'.pa (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.tK, ← hS.2, ← ht.2]
  exact hb

/-- `Power2Round` of `t`. -/
theorem p2r_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p (fun A S => tK p A S i) A S s) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P (tP p) (t1P p) (t0P p)) s fun s' =>
      PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧ NatPolyIs s'.mem (pa s' (t1P p)) (t1K p A S i) ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) := by
  dsimp only [tIs] at ht
  have L := h.kc.lay hF hp
  refine WP.mono (p2rAt_ok hP.s64 hP.power2Round L (p2r_chk hF hi) ht.1) fun s' ⟨hP', x', h1, h0⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (chk_p2r hF hi), ?_, ?_⟩
  · rw [hP'.pa (p := t1P p) (show Reg.x28 ∈ keptRegs by decide), Proof.MlDsa.KeyGen.t1K, ← ht.2]; exact h1
  · rw [hP'.pa (p := t0P p) (show Reg.x28 ∈ keptRegs by decide), ← ht.2]; exact h0

/-- `t₁[i]` to `pk`. -/
theorem sbp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s) (h1 : NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i))
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) s fun s' =>
      PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s' ∧
      PolyIs s'.mem (pa s' (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
      bytesAt s'.mem (pa s' (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  refine WP.mono (sbpAt_ok hP.s64 hP.simpleBitPack L (sbp_chk hF hi) sbpOk_t1 (t1_bound h1))
    fun s' ⟨hP', x', hb⟩ => ?_
  refine ⟨h.keep hF hp hP' x' (chk_sbp hF hi), L.keepPoly hP' (by layd) h0, ?_⟩
  rw [hP'.pa (show Reg.x26 ∈ keptRegs by decide), hb, h1]

/-- `t₀[i]` to `sk`. -/
theorem bp_ok {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ i s)
    (h0 : PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2))
    (h1 : bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023) :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) s
      (PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  refine WP.mono (bpAt_ok hP.s64 hP.bitPack L (bp_chk hF hi) bpOk_t0 h0.1 (range_t0 h0))
    fun s' ⟨hP', x', hb⟩ => ?_
  have hk' := h.keep hF hp hP' x' (chk_bp hF hi)
  refine ⟨hk'.kc, hk'.x24, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨by
      have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
      rw [L.keepBytes hP' (by layd)]; exact h1, ?_⟩
    rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), hb, h0.2, modPm_t0]
    rfl

end


/-- One complete measured row, retaining lazy secret transforms and emitting
exactly the reference public and private key encodings. -/
theorem row_ok {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params}
    (hF : PFacts p) {σ s : State} (hp : kgPre p S' σ) {i : Nat} (hi : i<p.k)
    {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    (h : PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i s)
    (roots : Sign.StaticRoots S' s)
    (hd : 16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S') :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i) s fun t =>
      PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ (i+1) t ∧ Sign.StaticRoots S' t := by
  apply roots.phase hd hP.s64
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.row
  apply WP.seq
  refine WP.mono (dotRow_value hF hp hi h roots) fun a ⟨ha,_,hv⟩ => ?_
  apply WP.seq
  refine WP.mono (addS2_ok hP hF hp hi ha hv) fun b ⟨hb,hv⟩ => ?_
  apply WP.seq
  refine WP.mono (p2r_ok hP hF hp hi hb hv) fun c ⟨hc,h1,h0⟩ => ?_
  apply WP.seq
  refine WP.mono (sbp_ok hP hF hp hi hc h1 h0) fun d ⟨hd,h0,h1⟩ => ?_
  exact bp_ok hP hF hp hi hd h0 h1

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

/-! ### `MlDsa.AArch64.KeyGen.OptimizedNtt`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)

theorem nttSecret_ok {S' : Nat} {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S' σ) {j : Nat} (hj : j < p.ℓ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : PositiveKR p σ A S R (p.ℓ + p.k) j 0 s) (roots : Sign.StaticRoots S' s) :
    WP isa (nttSecret p j) s fun t => PositiveKR p σ A S R (p.ℓ+p.k) (j+1) 0 t ∧ Sign.StaticRoots S' t := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  have hS := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hS
  have hr : inB (kgR++kgW p) (sP p j) 1024=true := by layd
  have hw : inB (kgW p) (sP p j) 1024=true := by layd
  refine WP.mono_syms (Sign.positiveNttAt_layout L hr hw
    ⟨roots.nttTableAt (L.inW hw),roots.forward.readable⟩ hS.1)
    fun s' ⟨hP',x',hb⟩ hy => ?_
  refine ⟨?_,roots.step_layout L hP' hy (fun w hw' => by
    obtain rfl := List.mem_singleton.mp hw'
    exact hw)⟩
  have hlen : lenS p = 96 ∨ lenS p = 128 := hF.eta.imp And.right And.right
  exact ⟨h.kc.step hF hp hP' (by unfold kcChk; layd), x'.trans h.x24, h.good,
    h.small, fun e he => L.keepPoly hP' (by layd) (h.aS e he),
    fun i hi => L.keepPoly hP' (by layd) (h.s2 i hi),
    fun j' hj' => if e : j' = j then by
        subst e; rw [ifp (Nat.lt_succ_self j'), hP'.pa (p := sP p j') (show Reg.x28 ∈ keptRegs by decide), ← hS.2]
        exact hb
      else by
        have hv := h.s1 j' hj'
        by_cases hlt : j' < j
        · simp only [ite_eq_left hlt] at hv
          simp only [ite_eq_left (show j' < j+1 by omega_using [hlt])]
          exact Sign.keepPosPoly L hP' (by layd) hv
        · simp only [ite_eq_right hlt] at hv
          simp only [ite_eq_right (show ¬ j' < j+1 by omega_using [e, hlt])]
          exact L.keepPoly hP' (by layd) hv,
    by rw [L.keepBytes hP' (by layd)]; exact h.pk0,
    by rw [L.keepBytes hP' (by layd)]; exact h.sk0,
    by rw [L.keepBytes hP' (by layd)]; exact h.sk1,
    fun r hr => by
      have : lenS p * r + lenS p ≤ lenS p * (p.ℓ + p.k) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega_using [hr])
      rw [L.keepBytes hP' (by rcases hlen with hlen | hlen <;> lay [hF.pk, hF.sk, hlen])]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

/-! ### `MlDsa.AArch64.KeyGen.OptimizedPackSecret`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Proof.MlDsa.KeyGen

theorem packSecret_ok {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S' σ) {r : Nat} (hr : r < p.ℓ + p.k) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R r 0 0 s) : WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p r) s (KR p σ A S R (r + 1) 0 0) := by
  have L := h.kc.lay hF hp
  have hS := h.sPoly hr
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt
  refine WP.mono (bpAt_ok hP.s64 hP.bitPack L (packS_chk hF hr) (bpOk_eta hF) hS.1
    (range_of (eta_le hF) hS (h.small r hr))) fun s' ⟨hP', x', hb⟩ => ?_
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hk' := h.keep hF hp hP' x' (KRChk.x27 (o := 128 + lenS p * r) (n := lenS p) hF (Nat.le_of_lt hr)
    (Nat.zero_le _) (by omega_using []) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega_using [hle]))
  refine ⟨hk'.kc, hk'.x24, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
    fun r' hr' => ?_, hk'.rows⟩
  rcases (by omega_using [hr'] : r' < r ∨ r' = r) with hr' | rfl
  · exact hk'.packs r' hr'
  · rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), hb, hS.2,
      Proof.MlDsa.KeyGen.modPm_toRq (small_big (eta_le hF) (h.small r' hr))]

theorem packSecret_tr {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : RelCT isa (R p S' (KRx p r 0 0)) (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p r) fun _ _ => True := by
  refine rel_of (Q := fun x y => Two p S' x y ∧ (Reduced x.mem (pa x (sP p r)) ∧ BpRange x.mem (pa x (sP p r)) p.η p.η) ∧
    (Reduced y.mem (pa y (sP p r)) ∧ BpRange y.mem (pa y (sP p r)) p.η p.η)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨(h₁.sPoly hr).1, range_of (eta_le hF) (h₁.sPoly hr) (h₁.small r hr)⟩,
        ⟨(h₂.sPoly hr).1, range_of (eta_le hF) (h₂.sPoly hr) (h₂.small r hr)⟩⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt
  exact bpAt_tr hP.bitPack (kgOk p) (packS_chk hF hr) (bpOk_eta hF) fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem packSecret_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : Piece p S' (KRx p r 0 0) (KRx p (r + 1) 0 0) (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p r) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (packSecret_ok hP hF hp hr h) fun _ h => ⟨A, S, R, h⟩, packSecret_tr hP hF hr⟩


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

/-! ### `MlDsa.AArch64.KeyGen.OptimizedFinish`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K pkK skK)
open VG.Spec.Sha3 (bytesAt)

abbrev KRx (p : Params) (np nj nr : Nat) (σ s : State) : Prop :=
  ∃ A S R, PositiveKR p σ A S R np nj nr s

theorem pk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {np nj : Nat} {s : State} (h : PositiveKR p σ A S R np nj p.k s) :
    bytesAt s.mem (pa s (.x26, 0)) p.pkLen = pkK p A S (rhoOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x26) 32 = rhoOf p σ := by rw [← pa_zero]; exact h.pk0
  rw [hF.pk, pa_zero, Proof.MlKem.bytesAt_add, h0,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x26) 32 320 p.k, pkK, t1Max_eq]
  exact congrArg _ (flatMap_congr_mem fun i hi => (h.rows i (List.mem_range.mp hi)).1)

theorem sk_bytes {p : Params} (hF : PFacts p) {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64}
    {nj : Nat} {s : State} (h : PositiveKR p σ A S R (p.ℓ + p.k) nj p.k s)
    (htr : bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64) :
    bytesAt s.mem (pa s (.x27, 0)) p.skLen = skK p A S (rhoOf p σ) (kOf p σ) := by
  have h0 : bytesAt s.mem (s.gpr .x27) 32 = rhoOf p σ := by rw [← pa_zero]; exact h.sk0
  have h1 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 32) 32 = kOf p σ := h.sk1
  have h2 : bytesAt s.mem (s.gpr .x27 + BitVec.ofNat 64 (32 + 32)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64 :=
    htr
  rw [hF.sk, oT0, show 128 = 32 + 32 + 64 from rfl, pa_zero, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add,
    Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h0, h1, h2,
    Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (32 + 32 + 64) (lenS p) (p.ℓ + p.k),
    ← oT0, Proof.MlDsa.KeyGen.bytesAt_pieces s.mem (s.gpr .x27) (oT0 p) 416 p.k, skK]
  rw [flatMap_congr_mem (g := fun r => bitPack (S r) p.η p.η) fun r hr => h.packs r (List.mem_range.mp hr),
    flatMap_congr_mem (g := fun i => bitPack (t0K p A S i) 4095 4096) fun i hi => (h.rows i (List.mem_range.mp hi)).2]
  rfl

/-! ## `tr = H(pk, 64)` -/

/-- At the end: the keys, but for the return. -/
abbrev KFin (p : Params) (σ s : State) : Prop :=
  ∃ A S R, PositiveKR p σ A S R (p.ℓ + p.k) p.ℓ p.k s ∧
    bytesAt s.mem (pa s (.x27, 64)) 64 = Spec.MlDsa.H (pkK p A S (rhoOf p σ)) 64

theorem trHash_piece {p : Params} (hF : PFacts p) {S' : Nat} (h16 : 16 ≤ S') (hSl : S' < 2 ^ 64) :
    Piece p S' (KRx p (p.ℓ + p.k) p.ℓ p.k) (KFin p) ((trHashWith keccak.callee) p) := by
  refine ⟨fun σ s hp ⟨A, S, R, h⟩ => ?_, rel_of (Q := Two p S') (trHash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  unfold trHashWith
  refine WP.mono (shake_ok h16 hSl L (by simp) (trHash_chk hF)) fun s' ⟨hP', x', ho⟩ => ⟨A, S, R, ?_, ?_⟩
  · have hc : KRChk p (p.ℓ + p.k) p.ℓ p.k [((.x28, 0), 200), ((.x28, 200), 640), ((.x27, 64), 64)] :=
      (KRChk.x28 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by rw [hF.scr]; omega_using [])).append (ws₁ := [_])
      ((KRChk.x28 hF (Nat.le_refl _) (Nat.le_refl _) (.inl (by decide)) (.inl (by decide))
        (by rw [hF.scr]; omega_using [])).append (ws₁ := [_])
      (KRChk.x27 hF (Nat.le_refl _) (Nat.le_refl _) (by decide) (.inl (by decide))
        (.inl (by simp only [oT0]; omega_using [])) (by rw [hF.sk, oT0]; omega_using [])))
    exact h.keep hF hp hP' x' hc
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x27 ∈ keptRegs by decide), ho]
    exact congrArg (Spec.MlDsa.H · 64) (pk_bytes hF h)

theorem epi_piece {p : Params} (hF : PFacts p) {S' : Nat} :
    Piece p S' (KFin p) (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S').post σ s)
      (.block epi) := by
  refine ⟨fun σ s hp ⟨A, S, R, h, htr⟩ => ?_, rel_of (Q := Two p S') (taintRel [.x28] (fun x y h => h.x28)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ => kc_two hF p₁ p₂ pub h₁.kc h₂.kc⟩
  have L := h.kc.lay hF hp
  have hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48 := by
    have := L.inR (p := svP) (l := 48) (by have := scr_ge hF; lay)
    rwa [pa, h.kc.top.x28] at this
  refine WP.mono (epi_ok h.kc.top hin) fun s' ⟨ha, hr, hm⟩ => ⟨ha, ?_⟩
  sig_post [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs]
  have e26 : pa s (.x26, 0) = σ.gpr .x1 := by rw [pa_zero, h.kc.top.x26]
  have e27 : pa s (.x27, 0) = σ.gpr .x2 := by rw [pa_zero, h.kc.top.x27]
  rw [hr, h.x24, hm, ← e26, ← e27, pk_bytes hF h, sk_bytes hF h htr]
  exact outcome_of (by have := hF.l; omega_using [this]) h.good


end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (seqR)
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- The complete optimized arithmetic suffix. Depth premises are syntactic
bounds on the supplied primitive implementations, discharged at registration. -/
theorem rest_ok {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params}
    (hF : PFacts p) {σ s : State} (hp : kgPre p S' σ)
    (h : KSamp p σ (p.k*p.ℓ) (p.ℓ+p.k) s) (roots : Sign.StaticRoots S' s)
    (hdpack : ∀j<p.ℓ+p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p j).aarch64Depth≤S')
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S') :
    WP isa (Impl.MlDsa.AArch64.KeyGen.Optimized.restWith keccak.callee P p) s (KFin p σ) := by
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.restWith
  apply WP.seq
  refine WP.mono (roots.phase (show 16*(Code.block copies).aarch64Depth≤S' from by
    change 0≤S'; omega_using []) hP.s64 (copies_ok hF hp h)) fun a ⟨⟨A,T,R,ha⟩,ra⟩ => ?_
  apply WP.seq
  refine WP.mono (seqR_ok (I := fun j t => KR p σ A T R j 0 0 t ∧ Sign.StaticRoots S' t)
    (p.ℓ+p.k) 0 (fun j _ hj t ⟨ht,rt⟩ =>
      rt.phase (hdpack j (by omega_using [hj])) hP.s64 (packSecret_ok hP hF hp (by omega_using [hj]) ht)) a ⟨ha,ra⟩)
    fun b ⟨hb,rb⟩ => ?_
  simp only [Nat.zero_add] at hb
  apply WP.seq
  refine WP.mono (seqR_ok (I := fun j t => PositiveKR p σ A T R (p.ℓ+p.k) j 0 t ∧ Sign.StaticRoots S' t)
    p.ℓ 0 (fun j _ hj t ⟨ht,rt⟩ => nttSecret_ok hF hp (by omega_using [hj]) ht rt)
    b ⟨PositiveKR.of_canonical hb,rb⟩) fun c ⟨hc,rc⟩ => ?_
  simp only [Nat.zero_add] at hc
  apply WP.seq
  refine WP.mono (seqR_ok (I := fun i t => PositiveKR p σ A T R (p.ℓ+p.k) p.ℓ i t ∧ Sign.StaticRoots S' t)
    p.k 0 (fun i _ hi t ⟨ht,rt⟩ => row_ok hP hF hp (by omega_using [hi]) ht rt (hdrow i (by omega_using [hi])))
    c ⟨hc,rc⟩) fun d ⟨hd,_⟩ => ?_
  simp only [Nat.zero_add] at hd
  exact (trHash_piece hF hP.s16 hP.s64).ok σ d hp ⟨A,T,R,hd⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

/-! ### `MlDsa.AArch64.KeyGen.OptimizedMatrixSeeds`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

/-- The four copies of the public matrix seed survive all row samplers. -/
def MatrixPrefixes (p : Params) (σ : State) (n : Nat) (s : State) : Prop :=
  ∀k<n,bytesAt s.mem (pa s (sc (oSA4+34*k))) 32=rhoOf p σ

theorem MatrixPrefixes.keep {p : Params} {S : Nat} {σ s t : State} {n : Nat}
    (L : Lay S kgR (kgW p) s) (h : MatrixPrefixes p σ n s)
    {ws : List (Ptr × Nat)} (hp : PPostB S s t ws)
    (hc : ∀k<n,keepB kgR (kgW p) ws (sc (oSA4+34*k)) 32=true) : MatrixPrefixes p σ n t := by
  intro k hk
  rw [L.keepBytes hp (hc k hk)]
  exact h k hk

theorem matrixCopy_ok {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : kgPre p S σ) {e j : Nat} (he : e≤p.k*p.ℓ) (hj : j<4)
    (hs : KSamp p σ e 0 s) (hr : MatrixPrefixes p σ j s) :
    WP isa (.block (copySeed4 j)) s fun t => KSamp p σ e 0 t ∧ MatrixPrefixes p σ (j+1) t := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := hs.k1.kc.lay hF hp
  refine WP.mono (copySeed4_ok hF L hj) fun t ⟨ht,hkeep,hbytes⟩ => ?_
  refine ⟨hs.keep hF hp ht (by unfold k1Chk kcChk; layd) (fun k hk => by layd)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hkeep.get .x24),?_⟩
  intro k hk
  by_cases hkj : k=j
  · subst k
    rw [sc_pa ht,hbytes,hs.k1.sa]
  · rw [L.keepBytes ht (by layd)]
    exact hr k (by omega_using [hk, hkj])

theorem matrixPrefixes_ok {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : kgPre p S σ) (hs : KSamp p σ 0 0 s) :
    WP isa (.block ((List.range 4).flatMap copySeed4)) s fun t =>
      KSamp p σ 0 0 t ∧ MatrixPrefixes p σ 4 t := by
  exact wp_range_flatMap (M := isa) (N := 4)
    (fun j t => KSamp p σ 0 0 t ∧ MatrixPrefixes p σ j t)
    (fun j t hj ht => matrixCopy_ok hF hp (Nat.zero_le _) hj ht.1 ht.2)
    4 (by omega_using []) s ⟨hs,fun _ h => False.elim (Nat.not_lt_zero _ h)⟩

/-- Updating the two row/column bytes leaves the hoisted seed prefix intact. -/
theorem matrixNonce_ok {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : kgPre p S σ) {e j : Nat} (he : e+j<p.k*p.ℓ) (hj : j<4)
    (hs : GS p σ e j s) (hr : MatrixPrefixes p σ 4 s) :
    WP isa (.block (setSR p e j)) s fun t => GS p σ e (j+1) t ∧ MatrixPrefixes p σ 4 t := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := hs.ks.k1.kc.lay hF hp
  unfold setSR
  refine WP.mono (setTwo_ok L (o := oSA4+34*j+32) (a := (e+j)%p.ℓ) (b := (e+j)/p.ℓ)
    (by dsimp only [oSA4]; omega_using [hj]) (by layd) (by layd)) fun t ⟨ht,hkeep,hbytes⟩ => ?_
  refine ⟨⟨hs.ks.keep hF hp ht (by unfold k1Chk kcChk; layd) (fun k hk => by lay)
    (fun _ h => False.elim (Nat.not_lt_zero _ h)) (hkeep.get .x24),?_⟩,
    hr.keep L ht (fun k hk => by layd)⟩
  intro k hk
  by_cases hkj : k=j
  · subst k
    rw [bytes34,L.keepBytes ht (by layd),hr j hj,sc_add,sc_pa ht,hbytes,
      Proof.MlDsa.KeyGen.seedA_eq]
  · rw [L.keepBytes ht (by layd)]
    exact hs.done k (by omega_using [hk, hkj])

theorem matrixPrefixes_tr {Q : State → State → Prop}
    (hq : ∀x y,Q x y → x.sp=y.sp ∧ x.gpr .x28=y.gpr .x28) :
    RelCT isa Q (.block ((List.range 4).flatMap copySeed4)) fun _ _ => True := by
  apply taintRel [.x28] (fun x y h => ⟨(hq x y h).1,?_⟩)
    (by taint_decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (hq x y h).2

theorem matrixNonce_tr (p : Params) (e j : Nat) {Q : State → State → Prop}
    (hq : ∀x y,Q x y → x.sp=y.sp ∧ x.gpr .x28=y.gpr .x28) :
    RelCT isa Q (.block (setSR p e j)) fun _ _ => True := by
  apply taintRel [.x28] (fun x y h => ⟨(hq x y h).1,?_⟩)
    (show (taint.check (Taint.ofRegs [.x28]) (.block (setSR p e j)) (.block [])).isSome=true from by
      with_unfolding_all rfl)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (hq x y h).2

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

/-! ### `MlDsa.AArch64.KeyGen.OptimizedCorrect`, which only this module used -/

section

/-! ### `MlDsa.AArch64.KeyGen.OptimizedMatrixTiming`, which only this module used -/

section

/-! ### `MlDsa.AArch64.KeyGen.OptimizedMatrixFour`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly rejNTTPoly minBounds)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs poly4 seed4)
open VG.Proof.MlDsa.KeyGen (seedA ifp ifn masked_one masked_zero)
open VG.Spec.Sha3 (bytesAt)

theorem matrixFour_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {σ : State} (hp : kgPre p S σ) {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) {s : State}
    (h : GS p σ (4*g) 4 s) (hr : MatrixPrefixes p σ 4 s) :
    WP isa (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
      (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (4*g)) 1024))) s (fun t => KSamp p σ (4*g+4) 0 t ∧ MatrixPrefixes p σ 4 t) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.ks.k1.kc.lay hF hp
  refine WP.seq (WP.mono (rej4At_ok hP.s64 hP.rej4 L
    (seed := sc oSA4) (a := aP (4*g)) (ss := sc (oR4 p)) (by unfold rej4Chk; layd))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩
    exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide)
    (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by
    rw [h20.get .x0]; exact hr01
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L20 (a := aP (4*g)) (N := 64) (by decide) (by decide) (by layd) (by layd) hr20)
    fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  refine ⟨?_,hr.keep L hP13 (fun k hk => by layd)⟩
  have e2 : pa s2 (aP (4*g)) = pa s (aP (4*g)) := sc_pa hP2 _
  have e20 : pa s20 (aP (4*g)) = pa s2 (aP (4*g)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 4, ∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (4*g))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (4*g))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega_using [hk, hi])
  have e3 : ∀ k,pa s3 (aP (4*g+k)) = poly4 (pa s (aP (4*g))) k := fun k => by
    rw [pa_poly4,sc_pa hP13]
  obtain ⟨A,S',hA,_,hG⟩ := h.ks.ex
  have h24' : s3.gpr .x24 = if s.gpr .x24 = 1 ∧ (s2.gpr .x0).setWidth 32 = 1 then 1 else 0 := by
    rw [k3.get .x24,e24,h24,Proof.MlDsa.KeyGen.and01 (good_01 hG) hr01]
  refine ⟨h.ks.k1.step hF hp hP13 (by unfold k1Chk kcChk; layd),
    fun e' => if e' < 4*g then A e' else polyAt s3.mem (pa s3 (aP e')),S',
    fun e' he' => ?_,fun _ h => False.elim (Nat.not_lt_zero _ h),?_⟩
  · dsimp only
    by_cases hlt : e' < 4*g
    · rw [ifp hlt]
      exact L.keepPoly hP13 (by lay) (hA e' hlt)
    · rw [ifn hlt]
      refine ⟨?_,rfl⟩
      obtain ⟨k,rfl⟩ : ∃ k,e' = 4*g+k := ⟨e'-4*g,by omega_using [hlt]⟩
      rw [e3]
      by_cases h1 : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one h1 (hco4 k (by omega_using [he']))).2 (hred h1 k (by omega_using [he']))
      · exact (masked_zero h1 (hco4 k (by omega_using [he']))).1
  · rw [h24']
    rcases hG with ⟨h1,b,hb,_⟩ | ⟨h0,hn⟩
    · rcases hout with ⟨ho,hb4⟩ | ⟨ho,k,hk,hn⟩
      · obtain ⟨n,hn⟩ := bound4 hb4
        refine .inl ⟨by rw [ifp ⟨h1,ho⟩],{ b with rejNTT := max b.rejNTT n },fun e' he' => ?_,
          fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
        dsimp only
        by_cases hlt : e' < 4*g
        · rw [ifp hlt]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_left _ _) (hb e' hlt)
        · rw [ifn hlt]
          obtain ⟨k,rfl⟩ : ∃ k,e' = 4*g+k := ⟨e'-4*g,by omega_using [hlt]⟩
          have hk : k < 4 := by omega_using [he']
          rw [e3,(masked_one ho (hco4 k hk)).1,← seed4_eq h hk]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_right _ _) (hn k hk)
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        rw [seed4_eq h hk] at hn
        have hq : (4*g+k)/p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p.ℓ p.k]; omega_using [hg, hk])
        exact .inr ⟨rfl,Proof.MlDsa.KeyGen.keyGenInternal_none_A hq (Nat.mod_lt _ (by omega_using [hl])) hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl,hn⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

/-! ### `MlDsa.AArch64.KeyGen.OptimizedMatrixTwo`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly rejNTTPoly minBounds)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs poly4 seed4)
open VG.Proof.MlDsa.KeyGen (seedA ifp ifn masked_one masked_zero)
open VG.Spec.Sha3 (bytesAt)

theorem seed2_eq {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 2 s) {k : Nat} (hk : k<2) :
    seed4 s.mem (pa s (sc oSA4)) k=seedA (rhoOf p σ) ((e+k)/p.ℓ) ((e+k)%p.ℓ) := by
  unfold seed4
  rw [show pa s (sc oSA4)+BitVec.ofNat 64 (34*k)=pa s (sc (oSA4+34*k)) from sc_add _ _ _]
  exact h.done k hk

theorem bound2 {ρ : Nat→List Byte} {x : Nat→Poly}
    (h : ∀k<2,∃b : Spec.MlDsa.Bounds,rejNTTPoly b.rejNTT (ρ k)=some (x k)) :
    ∃n,∀k<2,rejNTTPoly n (ρ k)=some (x k) := by
  obtain ⟨b0,h0⟩ := h 0 (by decide)
  obtain ⟨b1,h1⟩ := h 1 (by decide)
  refine ⟨max b0.rejNTT b1.rejNTT,fun k hk => ?_⟩
  rcases (by omega_using [hk] : k=0 ∨ k=1) with rfl | rfl
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega_using []) h0
  · exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (by omega_using []) h1

theorem matrixTwo_ok {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Proof.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : PFacts p)
    {σ : State} (hp : kgPre p S σ) {e : Nat} (he : e+2 ≤ p.k*p.ℓ) {s : State}
    (h : GS p σ e 2 s) (hr : MatrixPrefixes p σ 4 s) :
    WP isa (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p))))
      (.seq (.block and24) (VG.Impl.MlDsa.AArch64.Optimized.MatrixMask.code (aP (e)) 512))) s (fun t => KSamp p σ (e+2) 0 t ∧ MatrixPrefixes p σ 4 t) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.ks.k1.kc.lay hF hp
  refine WP.seq (WP.mono (rej2At_ok hS C L
    (seed := sc oSA4) (a := aP (e)) (ss := sc (oR4 p)) (by unfold rej2Chk; layd))
    fun s2 ⟨hP2,h24,hred,hout⟩ => ?_)
  have L2 := L.post hP2
  have hr01 : (s2.gpr .x0).setWidth 32 = 0 ∨ (s2.gpr .x0).setWidth 32 = 1 := by
    rcases hout with ⟨h1,_⟩ | ⟨h0,_⟩
    exacts [.inr h1,.inl h0]
  refine WP.seq (WP.mono (and24_ok s2) fun s20 ⟨h20,e24⟩ => ?_)
  have hP20 : PPostB S s2 s20 [] := postB_of_keep h20.keep (by decide)
    (by rw [h20.mem]; exact Frame.refl _ _)
  have L20 := L2.post hP20
  have hr20 : (s20.gpr .x0).setWidth 32 = 0 ∨ (s20.gpr .x0).setWidth 32 = 1 := by
    rw [h20.get .x0]; exact hr01
  refine WP.mono (VG.Proof.MlDsa.AArch64.Optimized.MatrixMask.mask_ok L20 (a := aP (e)) (N := 32) (by decide) (by decide) (by layd) (by layd) hr20)
    fun s3 ⟨hP3,k3,hco⟩ => ?_
  have hP23 := PPostB.app hP20 hP3 (sc_bases _ (by simp))
  have hP13 := PPostB.app hP2 hP23 (sc_bases _ (by simp))
  refine ⟨?_,hr.keep L hP13 (fun k hk => by layd)⟩
  have e2 : pa s2 (aP (e)) = pa s (aP (e)) := sc_pa hP2 _
  have e20 : pa s20 (aP (e)) = pa s2 (aP (e)) := sc_pa hP20 _
  rw [h20.get .x0,e20,e2,h20.mem] at hco
  have hco4 : ∀ k < 2, ∀ i < 256,coeffAt s3.mem (poly4 (pa s (aP (e))) k) i =
      if (s2.gpr .x0).setWidth 32 = 1 then coeffAt s2.mem (poly4 (pa s (aP (e))) k) i else 0 :=
    fun k hk i hi => by rw [coeffAt_poly4,coeffAt_poly4]; exact hco _ (by omega_using [hk, hi])
  have e3 : ∀ k,pa s3 (aP (e+k)) = poly4 (pa s (aP (e))) k := fun k => by
    rw [pa_poly4,sc_pa hP13]
  obtain ⟨A,S',hA,_,hG⟩ := h.ks.ex
  have h24' : s3.gpr .x24 = if s.gpr .x24 = 1 ∧ (s2.gpr .x0).setWidth 32 = 1 then 1 else 0 := by
    rw [k3.get .x24,e24,h24,Proof.MlDsa.KeyGen.and01 (good_01 hG) hr01]
  refine ⟨h.ks.k1.step hF hp hP13 (by unfold k1Chk kcChk; layd),
    fun e' => if e' < e then A e' else polyAt s3.mem (pa s3 (aP e')),S',
    fun e' he' => ?_,fun _ h => False.elim (Nat.not_lt_zero _ h),?_⟩
  · dsimp only
    by_cases hlt : e' < e
    · rw [ifp hlt]
      exact L.keepPoly hP13 (by lay) (hA e' hlt)
    · rw [ifn hlt]
      refine ⟨?_,rfl⟩
      obtain ⟨k,rfl⟩ : ∃ k,e' = e+k := ⟨e'-e,by omega_using [hlt]⟩
      rw [e3]
      by_cases h1 : (s2.gpr .x0).setWidth 32 = 1
      · exact (masked_one h1 (hco4 k (by omega_using [he']))).2 (hred h1 k (by omega_using [he']))
      · exact (masked_zero h1 (hco4 k (by omega_using [he']))).1
  · rw [h24']
    rcases hG with ⟨h1,b,hb,_⟩ | ⟨h0,hn⟩
    · rcases hout with ⟨ho,hb4⟩ | ⟨ho,k,hk,hn⟩
      · obtain ⟨n,hn⟩ := bound2 hb4
        refine .inl ⟨by rw [ifp ⟨h1,ho⟩],{ b with rejNTT := max b.rejNTT n },fun e' he' => ?_,
          fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
        dsimp only
        by_cases hlt : e' < e
        · rw [ifp hlt]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_left _ _) (hb e' hlt)
        · rw [ifn hlt]
          obtain ⟨k,rfl⟩ : ∃ k,e' = e+k := ⟨e'-e,by omega_using [hlt]⟩
          have hk : k < 2 := by omega_using [he']
          rw [e3,(masked_one ho (hco4 k hk)).1,← seed2_eq h hk]
          exact Proof.MlDsa.KeyGen.rejNTTPoly_mono (Nat.le_max_right _ _) (hn k hk)
      · rw [ifn (fun h => by rw [h.2] at ho; exact absurd ho (by decide))]
        rw [seed2_eq h hk] at hn
        have hq : (e+k)/p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm p.ℓ p.k]; omega_using [he, hk])
        exact .inr ⟨rfl,Proof.MlDsa.KeyGen.keyGenInternal_none_A hq (Nat.mod_lt _ (by omega_using [hl])) hn⟩
    · rw [ifn (fun h => by rw [h.1] at h0; exact absurd h0 (by decide))]
      exact .inr ⟨rfl,hn⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Spec.MlDsa (Params)
open VG.Spec.Sha3 (bytesAt)

theorem matrixMask_taint : ∀j<80,∀n∈[512,1024],
    (taint.check (Taint.ofRegs [.x28]) (code (sc (oP j)) n)
      (VG.Taint.hintOf taint (Taint.ofRegs [.x28]) (code (sc 0) n))).isSome=true := by
  decide +kernel

theorem matrixTail_tr {p : Params} {S j n : Nat} (hj : j<80) (hn : n∈[512,1024]) :
    RelCT isa (Two p S) (.seq (.block and24) (code (aP j) n)) fun _ _ => True :=
  RelCT.seq (Two.step (block_nomem_tr fun i hi _ => by
    simp only [and24,List.mem_singleton] at hi; subst hi; rfl)
    fun x _ => WP.mono (and24_ok x) fun _ ⟨o,_⟩ =>
      ⟨[],postB_of_keep o.keep (by decide) (by rw [o.mem]; exact Frame.refl _ _)⟩)
    (taintRel [.x28] (fun _ _ h => Two.x28 h) (matrixMask_taint j hj n hn))

theorem matrixFour_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {g : Nat} (hg : 4*g+4 ≤ p.k*p.ℓ) : Piece p S (fun σ s => GS p σ (4*g) 4 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (4*g+4) 0 s ∧ MatrixPrefixes p σ 4 s)
      (.seq (rej4At P (sc (oR4 p)) (sc oSA4) (aP (4*g)))
        (.seq (.block and24) (code (aP (4*g)) 1024))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => matrixFour_ok hP hF hp hg h.1 h.2,
    rel_of (Q := fun x y => Two p S x y ∧
      bytesAt x.mem (pa x (sc oSA4)) 136 = bytesAt y.mem (pa y (sc oSA4)) 136) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨kc_two hF hp hp' hq h.1.ks.k1.kc h'.1.ks.k1.kc,by
        rw [h.1.seeds,h'.1.seeds,rho_pub hq]⟩)⟩
  have hc : rej4Chk kgR (kgW p) (sc oSA4) (aP (4*g)) (sc (oR4 p)) = true := by
    unfold rej4Chk; lay
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rej4At_ok hP.s64 hP.rej4 L hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1)
    (rej4At_tr hP.rej4 (kgOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) (matrixTail_tr (by omega_using [hg, hkl]) (by simp))

theorem matrixTwo_seeds {p : Params} {σ : State} {e : Nat} {s : State} (h : GS p σ e 2 s) :
    bytesAt s.mem (pa s (sc oSA4)) 68=
      VG.Proof.MlDsa.KeyGen.seedA (rhoOf p σ) (e/p.ℓ) (e%p.ℓ) ++
      VG.Proof.MlDsa.KeyGen.seedA (rhoOf p σ) ((e+1)/p.ℓ) ((e+1)%p.ℓ) := by
  rw [show 68=34+34 from rfl,Proof.MlKem.bytesAt_add]
  have h0 := seed2_eq h (k := 0) (by decide)
  have h1 := seed2_eq h (k := 1) (by decide)
  simp only [Proof.MlDsa.seed4,Nat.mul_zero,Nat.add_zero,Nat.mul_one,
    VG.Proof.MlKem.AArch64.ptr_zero] at h0 h1
  rw [h0,h1]


theorem matrixTwo_piece {S : Nat} (hS : S<2^64) {cd : Prog isa} {nm : String}
    (C : CalleeOk S cd (VG.Proof.MlDsa.rejNTT2Contract AArch64.abi S)) {p : Params} (hF : PFacts p)
    {e : Nat} (he : e+2≤p.k*p.ℓ) : Piece p S (fun σ s => GS p σ e 2 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (e+2) 0 s ∧ MatrixPrefixes p σ 4 s)
      (.seq (callAt nm cd (rej2Args (sc oSA4) (aP e) (sc (oR4 p))))
        (.seq (.block and24) (code (aP (e)) 512))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  refine ⟨fun _ _ hp h => matrixTwo_ok hS C hF hp he h.1 h.2,
    rel_of (Q := fun x y => Two p S x y ∧
      bytesAt x.mem (pa x (sc oSA4)) 68 = bytesAt y.mem (pa y (sc oSA4)) 68) ?_
      (fun _ _ _ _ hp hp' hq h h' => ⟨kc_two hF hp hp' hq h.1.ks.k1.kc h'.1.ks.k1.kc,by
        rw [matrixTwo_seeds h.1,matrixTwo_seeds h'.1,rho_pub hq]⟩)⟩
  have hc : rej2Chk kgR (kgW p) (sc oSA4) (aP (e)) (sc (oR4 p)) = true := by
    unfold rej2Chk; lay
  have ok := fun x (L : Lay S kgR (kgW p) x) => WP.mono (rej2At_ok hS C L (nm := nm) hc)
    fun _ h => (⟨_,h.1⟩ : ∃ W,PostB S x _ W)
  exact RelCT.seq (RelCT.two (fun _ _ h => h.1)
    (rej2At_tr C (kgOk p) hc (fun _ _ h => ⟨h.1.lx,h.1.ly,h.2,h.1.same⟩))
    (fun x y h => ⟨ok x h.1.lx,ok y h.1.ly⟩)) (matrixTail_tr (by omega_using [he, hkl]) (by simp))

theorem matrixPrefixes_piece {p : Params} (hF : PFacts p) {S : Nat} :
    Piece p S (KSamp p · 0 0) (fun σ s => KSamp p σ 0 0 s ∧ MatrixPrefixes p σ 4 s)
      (.block ((List.range 4).flatMap copySeed4)) := by
  refine ⟨fun _ _ hp h => matrixPrefixes_ok hF hp h,rel_of (Q := Two p S) ?_ ?_⟩
  · exact matrixPrefixes_tr fun x y h => ⟨h.same.2,h.same.1 .x28 (by decide)⟩
  · intro σ τ x y hp hq pub hx hy
    exact kc_two hF hp hq pub hx.k1.kc hy.k1.kc

theorem matrixNonce_piece {p : Params} (hF : PFacts p) {S e j : Nat}
    (he : e+j<p.k*p.ℓ) (hj : j<4) :
    Piece p S (fun σ s => GS p σ e j s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => GS p σ e (j+1) s ∧ MatrixPrefixes p σ 4 s) (.block (setSR p e j)) := by
  refine ⟨fun _ _ hp h => matrixNonce_ok hF hp he hj h.1 h.2,rel_of (Q := Two p S) ?_ ?_⟩
  · exact matrixNonce_tr p e j fun x y h => ⟨h.same.2,h.same.1 .x28 (by decide)⟩
  · intro σ τ x y hp hq pub hx hy
    exact kc_two hF hp hq pub hx.1.ks.k1.kc hy.1.ks.k1.kc

theorem matrixNonces_piece {p : Params} (hF : PFacts p) {S e n : Nat}
    (he : e+n≤p.k*p.ℓ) (hn : n≤4) :
    Piece p S (fun σ s => KSamp p σ e 0 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => GS p σ e n s ∧ MatrixPrefixes p σ 4 s)
      (seqR (fun j => .block (setSR p e j)) 0 n) := by
  exact Piece.mono (Piece.seqR (I := fun j σ s => GS p σ e j s ∧ MatrixPrefixes p σ 4 s)
    n 0 (fun j _ hj => matrixNonce_piece hF (by omega_using [he, hj]) (by omega_using [hn, hj])))
    (fun _ _ _ h => ⟨⟨h.1,fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩,h.2⟩)
    (fun _ _ _ h => by simpa only [Nat.zero_add] using h)

theorem matrixGroup_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    {g : Nat} (hg : 4*g+4≤p.k*p.ℓ) :
    Piece p S (fun σ s => KSamp p σ (4*g) 0 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (4*g+4) 0 s ∧ MatrixPrefixes p σ 4 s)
      (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixGroup P p g) :=
  Piece.seq (matrixNonces_piece hF hg (by decide)) (matrixFour_piece hP hF hg)

theorem matrixTwoPhase_piece {S : Nat} (hS : S<2^64) {cd : Prog isa}
    (C : CalleeOk S cd (Proof.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) {e : Nat} (he : e+2≤p.k*p.ℓ) :
    Piece p S (fun σ s => KSamp p σ e 0 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (e+2) 0 s ∧ MatrixPrefixes p σ 4 s)
      (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixTwo cd p e) :=
  Piece.seq (matrixNonces_piece hF he (by decide)) (matrixTwo_piece hS C hF he)

theorem matrixWith_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {paired : Bool} {cd : Prog isa}
    (C : CalleeOk S cd (Proof.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p) :
    Piece p S (fun σ s => K1 p σ s ∧ s.gpr .x24=1) (KSamp p · (p.k*p.ℓ) 0)
      (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixWith paired cd P p) := by
  have groups : Piece p S (fun σ s => KSamp p σ 0 0 s ∧ MatrixPrefixes p σ 4 s)
      (fun σ s => KSamp p σ (4*(p.k*p.ℓ/4)) 0 s ∧ MatrixPrefixes p σ 4 s)
      (seqR (VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixGroup P p) 0 (p.k*p.ℓ/4)) := by
    simpa only [Nat.zero_add,Nat.mul_zero,Nat.mul_add,Nat.mul_one] using
      Piece.seqR (I := fun g σ s => KSamp p σ (4*g) 0 s ∧ MatrixPrefixes p σ 4 s)
        (p.k*p.ℓ/4) 0 (fun g _ hg => matrixGroup_piece hP hF (by omega_using [hg]))
  have tail : Piece p S
      (fun σ s => KSamp p σ (4*(p.k*p.ℓ/4)) 0 s ∧ MatrixPrefixes p σ 4 s)
      (KSamp p · (p.k*p.ℓ) 0)
      (if paired = true ∧ p.k*p.ℓ%4=2 then
          VG.Impl.MlDsa.AArch64.KeyGen.Optimized.matrixTwo cd p (4*(p.k*p.ℓ/4))
        else seqR (expA P p) (4*(p.k*p.ℓ/4)) (p.k*p.ℓ%4)) := by
    by_cases hc : paired = true ∧ p.k*p.ℓ%4=2
    · have hm := hc.2
      rw [VG.Proof.MlDsa.KeyGen.ifp hc]
      exact Piece.mono (matrixTwoPhase_piece hP.s64 C hF (by omega_using [hm]))
        (fun _ _ _ h => h) (fun _ _ _ h => by
          simpa only [show 4*(p.k*p.ℓ/4)+2=p.k*p.ℓ by omega_using [hm]] using h.1)
    · rw [VG.Proof.MlDsa.KeyGen.ifn hc]
      refine Piece.mono (Piece.seqR (I := fun e σ s => KSamp p σ e 0 s) (p.k*p.ℓ%4) (4*(p.k*p.ℓ/4))
        (fun e _ he => expA_piece hP hF (by omega_using [he]))) (fun _ _ _ h => h.1) (fun _ _ _ h => ?_)
      have he : 4*(p.k*p.ℓ/4)+p.k*p.ℓ%4 = p.k*p.ℓ := by omega_using []
      simpa only [he] using h
  exact Piece.mono (Piece.seq (matrixPrefixes_piece hF) (Piece.seq groups tail))
    (fun _ _ _ h => KSamp.zero h.1 h.2) (fun _ _ _ h => h)

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end


@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem prefix_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Proof.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p)
    (hs : (p.ℓ+p.k)%4=0 ∨ (p.ℓ+p.k)%4=3) :
    Piece p S (fun σ s => s=σ) (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k))
      (prefixWith keccak.callee P cd p) :=
  Piece.seq (pro_piece hF) (Piece.seq (seeds_piece hF hP.s16 hP.s64)
    (Piece.seq (matrixWith_piece hP C hF) (secrets_piece keccak.callee hF hs S)))

/-- The selected key-generation computation retains the original outcome and
ABI. Immutable tables are the only additional entry resources. -/
theorem codeWith_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Proof.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p)
    (hs : (p.ℓ+p.k)%4=0 ∨ (p.ℓ+p.k)%4=3)
    {s : State} (hp : kgPre p S s) (roots : Sign.StaticRoots S s)
    (hdprefix : 16*(prefixWith keccak.callee P cd p).aarch64Depth≤S)
    (hdpack : ∀j<p.ℓ+p.k,16*(packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    WP isa (codeWith keccak.callee P cd p) s fun t =>
      abiPreserved s t ∧ (Spec.MlDsa.keyGenContract p AArch64.abi S).post s t := by
  unfold codeWith
  apply WP.seq
  refine WP.mono (roots.phase hdprefix hP.s64 ((prefix_piece hP C hF hs).ok s s hp rfl))
    fun u ⟨hu,ru⟩ => ?_
  apply WP.seq
  refine WP.mono (rest_ok hP hF hp hu ru hdpack hdrow) fun v hv => ?_
  exact (epi_piece hF).ok s v hp hv

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end

/-! ### `MlDsa.AArch64.KeyGen.OptimizedPieceTiming`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64
open VG.Spec.MlDsa (Params)

/-- Ordinary key-generation pieces preserve the immutable root tables through
 their already-proved write footprint and the bounded call stack. -/
theorem piece_rooted {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (h : Piece p S I J c) (hd : 16*c.aarch64Depth≤S) (hS : S<2^64) :
    RelCT isa (RootPair p S I) c (RootPair p S J) := by
  apply rootPair_progress
  · intro σ s hp hi roots
    exact roots.phase hd hS (h.ok σ s hp hi)
  · apply RelCT.mono h.tr
    · rintro x y ⟨⟨σ,τ,hσ,hτ,pub,hx,hy⟩,_⟩
      exact ⟨σ,τ,hσ,hτ,pub,hx.1,hy.1⟩
    · intro _ _ _
      trivial

theorem rootPair_mono {p : Params} {S : Nat} {I J : State→State→Prop}
    (h : ∀σ s,I σ s→J σ s) {x y : State} (hr : RootPair p S I x y) : RootPair p S J x y := by
  obtain ⟨⟨σ,τ,hσ,hτ,pub,hx,hy⟩,et⟩ := hr
  exact ⟨⟨σ,τ,hσ,hτ,pub,⟨h _ _ hx.1,hx.2⟩,⟨h _ _ hy.1,hy.2⟩⟩,et⟩

theorem rootPair_finish {p : Params} {S : Nat} {I J : State→State→Prop} {c : Prog isa}
    (hw : ∀σ s,kgPre p S σ→I σ s→Sign.StaticRoots S s→WP isa c s (J σ))
    (ht : RelCT isa (RootPair p S I) c fun _ _ => True) :
    RelCT isa (RootPair p S I) c (R p S J) := by
  intro x y tx ty u v hr ex ey
  obtain ⟨he,_⟩ := ht _ _ _ _ _ _ hr ex ey
  obtain ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,_⟩ := hr
  obtain ⟨_,u',eu,ju⟩ := hw σ x hσ ix.1 ix.2
  obtain ⟨_,v',ev,jv⟩ := hw τ y hτ iy.1 iy.2
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨he,σ,τ,hσ,hτ,pub,ju,jv⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized

end

end


-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRoundTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Call

theorem p2rAt_tr {S : Nat} {P : Prims} (C : CalleeOk S P.power2Round (power2RoundContract AArch64.abi S))
    {rbs wbs : List (Reg × Nat)} (hB : LayOk (rbs ++ wbs)) {t t1 t0 : Ptr} (hc : p2rChk rbs wbs t t1 t0 = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → Lay S rbs wbs x ∧ Lay S rbs wbs y ∧ Reduced x.mem (pa x t) ∧ Reduced y.mem (pa y t) ∧
      SameB x y) :
    RelCT isa Q (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P t t1 t0) fun _ _ => True := by
  have hc' := hc
  simp only [p2rChk, Bool.and_eq_true, and_assoc] at hc'
  obtain ⟨_, _, _, c4, c5, c6, _, _⟩ := hc'
  have hb : t.1 ∈ bases ∧ t1.1 ∈ bases ∧ t0.1 ∈ bases := ⟨ptr_bs hB c4, ptr_bs hB c5, ptr_bs hB c6⟩
  refine callAt_tr C (p2r_args hB c4 c5 c6) (by simp only [List.map_cons, List.map_nil]; decide)
    fun x y x1 y1 hp h1 h2 => ?_
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, p2r_pre Lx hc rx h1, ?_, ?_, (p2r_cov Lx hc).1, (p2r_cov Lx hc).2, ?_, ?_⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact p2r_pre Ly hc ry h2
  · sig_pub [power2RoundContract, power2RoundSig, AArch64.abi, VG.AArch64.argRegs]
    rw [Args.r0 h1, Args.r1 h1, Args.r2 h1, Args.r0 h2, Args.r1 h2, Args.r2 h2, Args.sp h1, Args.sp h2]
    simp only [Arg.val]
    exact ⟨e.2, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  · rw [e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2]; exact (p2r_cov Ly hc).1
  · rw [e.pa hb.2.1, e.pa hb.2.2]; exact (p2r_cov Ly hc).2

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRowPieces.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K)

abbrev RowI (p : Params) (i : Nat) (f : (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, PositiveKR p σ A S R (p.ℓ+p.k) p.ℓ i s ∧ f A S s

section
variable {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {i : Nat} (hi : i<p.k)
include hP hF hi

theorem addS2_piece : Piece p S' (RowI p i (tIs p fun A S => nttInv (dotK p A S i p.ℓ)))
    (RowI p i (tIs p fun A S => tK p A S i)) (Impl.MlDsa.AArch64.KeyGen.Optimized.addAt P (tP p) (sP p (p.ℓ + i))) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (addS2_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (tP p)) ∧ Reduced x.mem (pa x (sP p (p.ℓ + i)))) ∧
    (Reduced y.mem (pa y (tP p)) ∧ Reduced y.mem (pa y (sP p (p.ℓ + i))))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂.1, (h₂.s2 i hi).1⟩⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.addAt
  exact accAt_tr (op := add) hP.add (kgOk p) (add_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem (pa s (t1P p)) (t1K p A S i) ∧
    PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

theorem p2r_piece : Piece p S' (RowI p i (tIs p fun A S => tK p A S i)) (RowI p i (p2rIs p i))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.power2RoundAt P (tP p) (t1P p) (t0P p)) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, ht⟩ => WP.mono (p2r_ok hP hF hp hi h ht) fun _ h => ⟨A, S, R, h.1, h.2⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ Reduced x.mem (pa x (tP p)) ∧ Reduced y.mem (pa y (tP p))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t₁.1, t₂.1⟩
  exact p2rAt_tr hP.power2Round (kgOk p) (p2r_chk hF hi) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (i : Nat) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem (pa s (t0P p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem (pa s (.x26, 32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

theorem sbp_piece : Piece p S' (RowI p i (p2rIs p i)) (RowI p i (sbpIs p i))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.simpleBitPackAt P (t1P p) 1023 (.x26, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h1, h0⟩ => WP.mono (sbp_ok hP hF hp hi h h1 h0) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧ (∀ j < 256, (coeffAt x.mem (pa x (t1P p)) j).toNat ≤ 1023) ∧
    (∀ j < 256, (coeffAt y.mem (pa y (t1P p)) j).toNat ≤ 1023)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, t1_bound t₁.1, t1_bound t₂.1⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.simpleBitPackAt
  exact sbpAt_tr hP.simpleBitPack (kgOk p) (sbp_chk hF hi) sbpOk_t1 fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem bp_piece : Piece p S' (RowI p i (sbpIs p i)) (KRx p (p.ℓ + p.k) p.ℓ (i + 1))
    (Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt P (t0P p) 4095 4096 (.x27, oT0 p + 416 * i) 416) := by
  refine ⟨fun _ _ hp ⟨A, S, R, h, h0, h1⟩ => WP.mono (bp_ok hP hF hp hi h h0 h1) fun _ h => ⟨A, S, R, h⟩, ?_⟩
  refine rel_of (Q := fun x y => Two p S' x y ∧
    (Reduced x.mem (pa x (t0P p)) ∧ BpRange x.mem (pa x (t0P p)) 4095 4096) ∧
    (Reduced y.mem (pa y (t0P p)) ∧ BpRange y.mem (pa y (t0P p)) 4095 4096)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨t₁.1.1, range_t0 t₁.1⟩, ⟨t₂.1.1, range_t0 t₂.1⟩⟩
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.bitPackAt
  exact bpAt_tr hP.bitPack (kgOk p) (bp_chk hF hi) bpOk_t0 fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

end
end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedDotTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG.Impl.MlDsa.AArch64.Call (Arg)
open VG.Proof.MlDsa.KeyGen (dotK)

private theorem slot_add (s : State) (b j : Nat) :
    pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (b+j))) =
      pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP b))+BitVec.ofNat 64 (1024*j) := by
  simp only [pa,oP,Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

theorem dotRow_ready {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {i : Nat} (hi : i<p.k)
    (h : KRx p (p.ℓ+p.k) p.ℓ i σ s) (roots : Sign.StaticRoots S' s) :
    DotCallReady p.ℓ (tP p) (aP (p.ℓ*i)) (sP p 0) (VG.Impl.MlDsa.AArch64.Call.sc oSS) s := by
  obtain ⟨A,T,R,h⟩ := h
  refine optimizedDotReady hF (optimizedDotChk_ok hF i hi) hp h.kc roots ?_ ?_
  · intro j hj
    have hv := h.aS _ (idx_lt hi hj)
    change PolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.ℓ*i+j)))) _ at hv
    rw [slot_add] at hv
    exact (PosPolyIs.of_canonical hv).bound
  · intro j hj
    have hv := h.s1 j hj
    simp only [ite_eq_left hj] at hv
    change PosPolyIs s.mem (pa s (VG.Impl.MlDsa.AArch64.Call.sc (oP (p.k*p.ℓ+j)))) _ at hv
    rw [slot_add] at hv
    have hv' : PosPolyIs s.mem (pa s (sP p 0)+BitVec.ofNat 64 (1024*j)) (ntt (toRq (T j))) := by
      simpa only [sP,Nat.add_zero] using hv
    exact hv'.bound

theorem dotRow_tr {p : Params} (hF : PFacts p) {S' : Nat} {i : Nat} (hi : i<p.k) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i) fun _ _=>True := by
  have hn : p.ℓ=4∨p.ℓ=5∨p.ℓ=7 := by rcases hF.mem with rfl|rfl|rfl <;> decide
  apply dotAt_tr (S:=S') hn
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
    (ptr_ok (show Reg.x28∈keptRegs from by decide))
  rintro x y ⟨⟨σ,τ,hσ,hτ,pub,⟨hx,rx⟩,⟨hy,ry⟩⟩,et⟩
  obtain ⟨A,T,R,hx'⟩ := hx
  obtain ⟨B,U,V,hy'⟩ := hy
  have ht := kc_two hF hσ hτ pub hx'.kc hy'.kc
  exact ⟨dotRow_ready hF hσ hi ⟨A,T,R,hx'⟩ rx,
    dotRow_ready hF hτ hi ⟨B,U,V,hy'⟩ ry,
    ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),ht.same.pa (show Reg.x28∈bases from by decide),
    ht.same.2,et.2⟩

theorem dotRow_relCT {p : Params} (hF : PFacts p) {S' : Nat} {i : Nat} (hi : i<p.k) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.dotRow p i)
      (RootPair p S' (RowI p i (tIs p fun A T=>nttInv (dotK p A T i p.ℓ)))) := by
  apply rootPair_progress (ht:=dotRow_tr hF hi)
  rintro σ s hp ⟨A,T,R,h⟩ roots
  exact WP.mono (dotRow_value hF hp hi h roots) fun t ⟨ht,rt,hv⟩=>⟨⟨A,T,R,ht,hv⟩,rt⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRowTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen

theorem row_relCT {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params}
    (hF : PFacts p) {i : Nat} (hi : i<p.k)
    (hd : 16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S') :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i)
      (RootPair p S' (KRx p (p.ℓ+p.k) p.ℓ (i+1))) := by
  have hd' : (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S'/16 :=
    (Nat.le_div_iff_mul_le (by decide : 0<16)).mpr (by simpa only [Nat.mul_comm] using hd)
  simp only [Impl.MlDsa.AArch64.KeyGen.Optimized.row,Code.aarch64Depth,Nat.max_le] at hd'
  have hrem := Nat.div_mul_le_self S' 16
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.row
  exact (dotRow_relCT hF hi).seq
    ((piece_rooted (addS2_piece hP hF hi) (by omega) hP.s64).seq
      ((piece_rooted (p2r_piece hP hF hi) (by omega) hP.s64).seq
        ((piece_rooted (sbp_piece hP hF hi) (by omega) hP.s64).seq
          (piece_rooted (bp_piece hP hF hi) (by omega) hP.s64))))

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedNttTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlDsa.AArch64.Optimized
open VG.Impl.MlDsa.AArch64.Call (Arg)

theorem nttSecret_ready {p : Params} (hF : PFacts p) {S' : Nat} {σ s : State}
    (hp : kgPre p S' σ) {j : Nat} (hj : j<p.ℓ)
    (h : KRx p (p.ℓ+p.k) j 0 σ s) (roots : Sign.StaticRoots S' s) :
    NttCallReady (sP p j) s := by
  obtain ⟨A,T,R,h⟩ := h
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  have hr : inB (kgR++kgW p) (sP p j) 1024=true := by layd
  have hw : inB (kgW p) (sP p j) 1024=true := by layd
  have hv := h.s1 j hj
  simp only [ite_eq_right (Nat.lt_irrefl j)] at hv
  exact ⟨L.nwp hr,roots.nttTableAt (L.inW hw),hv.1,
    Covers.cons roots.forward.readable (L.cR hr),L.cW hw⟩

theorem nttSecret_tr {p : Params} (hF : PFacts p) {S' : Nat} {j : Nat} (hj : j<p.ℓ) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) j 0))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.nttSecret p j) fun _ _ => True := by
  apply positiveNttAt_tr (S := S') (show (Arg.ptr (sP p j)).Ok from ptr_ok (show Reg.x28∈keptRegs from by decide))
  rintro x y ⟨⟨σ,τ,hσ,hτ,pub,⟨hx,rx⟩,⟨hy,ry⟩⟩,et⟩
  obtain ⟨A,T,R,hx'⟩ := hx
  obtain ⟨B,U,V,hy'⟩ := hy
  have ht := kc_two hF hσ hτ pub hx'.kc hy'.kc
  exact ⟨nttSecret_ready hF hσ hj ⟨A,T,R,hx'⟩ rx,
    nttSecret_ready hF hτ hj ⟨B,U,V,hy'⟩ ry,
    ht.same.pa (show Reg.x28∈bases from by decide),ht.same.2,et.1⟩

theorem nttSecret_relCT {p : Params} (hF : PFacts p) {S' : Nat} {j : Nat} (hj : j<p.ℓ) :
    RelCT isa (RootPair p S' (KRx p (p.ℓ+p.k) j 0))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.nttSecret p j)
      (RootPair p S' (KRx p (p.ℓ+p.k) (j+1) 0)) := by
  apply rootPair_progress (ht := nttSecret_tr hF hj)
  rintro σ s hp ⟨A,T,R,h⟩ roots
  exact WP.mono (nttSecret_ok hF hp hj h roots) fun t ht => ⟨⟨A,T,R,ht.1⟩,ht.2⟩

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedRestTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem canonicalRootPair {p : Params} {S : Nat} {x y : State}
    (h : RootPair p S (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ+p.k) 0 0) x y) :
    RootPair p S (KRx p (p.ℓ+p.k) 0 0) x y :=
  rootPair_mono (fun _ _ ⟨A,T,R,h⟩ => ⟨A,T,R,PositiveKR.of_canonical h⟩) h

theorem rest_tr_of_rows {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    (hdpack : ∀j<p.ℓ+p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p j).aarch64Depth≤S)
    (hr : ∀i<p.k,RelCT isa (RootPair p S (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i)
      (RootPair p S (KRx p (p.ℓ+p.k) p.ℓ (i+1)))) :
    RelCT isa (RootPair p S (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k)))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.restWith keccak.callee P p) fun _ _ => True := by
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.restWith
  apply RelCT.seq (piece_rooted (copies_piece hF) (by change 0≤S; omega) hP.s64)
  apply RelCT.seq
    (seqR_tr (Q := fun j => RootPair p S (VG.Proof.MlDsa.AArch64.KeyGen.KRx p j 0 0))
      (p.ℓ+p.k) 0 (fun j _ hj => piece_rooted (packSecret_piece hP hF (by omega)) (hdpack j (by omega)) hP.s64))
  simp only [Nat.zero_add]
  apply RelCT.seq
    (RelCT.mono (seqR_tr (Q := fun j => RootPair p S (KRx p (p.ℓ+p.k) j 0))
      p.ℓ 0 (fun j _ hj => nttSecret_relCT hF (by omega)))
      (fun _ _ h => canonicalRootPair h) (fun _ _ h => h))
  simp only [Nat.zero_add]
  apply RelCT.seq (seqR_tr (Q := fun i => RootPair p S (KRx p (p.ℓ+p.k) p.ℓ i))
    p.k 0 (fun i _ hi => hr i (by omega)))
  simp only [Nat.zero_add]
  apply RelCT.mono (trHash_piece (keccak := keccak) hF hP.s16 hP.s64).tr
  · rintro x y ⟨⟨σ,τ,hσ,hτ,pub,hx,hy⟩,_⟩
    exact ⟨σ,τ,hσ,hτ,pub,hx.1,hy.1⟩
  · intro _ _ _
    trivial

theorem rest_relCT {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    (hdpack : ∀j<p.ℓ+p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    RelCT isa (RootPair p S (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k)))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.restWith keccak.callee P p) (R p S (KFin p)) :=
  rootPair_finish (fun _ _ hp h roots => rest_ok hP hF hp h roots hdpack hdrow)
    (rest_tr_of_rows hP hF hdpack (fun i hi => row_relCT hP hF hi (hdrow i hi)))

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/KeyGen/OptimizedTiming.lean`, which only this module imported.
section

section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Spec.MlDsa (Params)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem codeWith_ct {P : Prims} {S : Nat} (hP : PrimsOk P S) {cd : Prog isa}
    (C : CalleeOk S cd (Proof.MlDsa.rejNTT2Contract AArch64.abi S))
    {p : Params} (hF : PFacts p)
    (hs : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3)
    (hdprefix : 16*(prefixWith keccak.callee P cd p).aarch64Depth≤S)
    (hdpack : ∀j<p.ℓ+p.k,16*(packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    ConstantTime isa (fun s => kgPre p S s ∧ Sign.StaticRoots S s)
      (fun s t => kgPub p S s t ∧ TableEq s t) (codeWith keccak.callee P cd p) := by
  have ht : RelCT isa (RootPair p S (fun σ s => s=σ))
      (codeWith keccak.callee P cd p) (fun _ _ => True) :=
    RelCT.seq (piece_rooted (prefix_piece hP C hF hs) hdprefix hP.s64)
      (RelCT.seq (rest_relCT hP hF hdpack hdrow) (epi_piece hF).tr)
  intro s t tr ur s' t' hs ht' pub es et
  exact (ht _ _ _ _ _ _ ⟨⟨s,t,hs.1,ht'.1,pub.1,⟨rfl,hs.2⟩,⟨rfl,ht'.2⟩⟩,pub.2⟩ es et).1

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Sign (signRootConsts signRootConsts_eq)

theorem keyGen_verified (v : Proof.Sha3.AArch64.Permutation) {p : Params}
    (hp : p=mlDsa44∨p=mlDsa65∨p=mlDsa87) :
    Verified target (keyGenWith v.callee p) (keyGenContract p (abi.withConsts signRootConsts) 16) := by
  have hF := pfacts hp
  have hs : (p.ℓ+p.k)%4=0∨(p.ℓ+p.k)%4=3 := by rcases hp with rfl|rfl|rfl <;> decide
  have hP := primitives_ok (keccak := v)
  have hdpre : 16*(prefixWith v.callee (primitives v.callee)
      Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p).aarch64Depth≤16 := by
    have h := (prefix_dle v hF).le; omega_using [h]
  have hdpack : ∀j<p.ℓ+p.k,16*(packSecret (primitives v.callee) p j).aarch64Depth≤16 := by
    intro j _; have h := (packSecret_dle v p j).le; omega_using [h]
  have hdrow : ∀i<p.k,16*(row (primitives v.callee) p i).aarch64Depth≤16 := by
    intro i _; have h := (row_dle v hp i).le; omega_using [h]
  refine ⟨?_,?_,⟨keyGenSat p,keyGen_sat hp⟩⟩
  · intro s h
    obtain ⟨pre,roots⟩ := staticRoots_entry (by decide) h
    exact codeWith_ok hP two_callee hF hs pre roots hdpre hdpack hdrow
  · intro s t tr ur s' t' hσ hτ pub es et
    have preσ := staticRoots_entry (by decide) hσ
    have preτ := staticRoots_entry (by decide) hτ
    have pb : kgPub p 16 s t ∧ TableEq s t := by
      sig_pub_keep [keyGenContract,keyGenSig,abi,argRegs,Abi.withConsts,signRootConsts_eq] at pub
      obtain ⟨hsp,hd,hf,hi,hb,h0,h1,h2,h3⟩ := pub
      refine ⟨?_,hf,hi⟩
      dsimp only [kgPub]
      sig_pub [keyGenContract,keyGenSig,abi,argRegs]
      exact ⟨hsp,hd,hb,h0,h1,h2,h3⟩
    exact codeWith_ct hP two_callee hF hs hdpre hdpack hdrow
      s t tr ur s' t' preσ preτ pb es et

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
