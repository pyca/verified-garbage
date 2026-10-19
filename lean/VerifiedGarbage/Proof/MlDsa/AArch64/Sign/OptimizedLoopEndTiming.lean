module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseLCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEnd
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseLCT
meta import Mathlib.Tactic.Conv
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Batch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.CanonicalizeVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotBank
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotMemoryValues
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.FiveInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseSliceComposition
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableConstants
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeccakMix
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Layout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemoryOuterPass
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.MemorySchedule
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttOutVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductRepresentation
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorb
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentAbsorbWord
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskCall
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentMaskVerified
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentParse
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRestoreG
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFinish
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseInit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseMath
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseZMemory
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableDecode
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TraversalCorrect
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Loop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedOutputPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseDCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Mem
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.MlKem.AArch64.Shared
meta import VerifiedGarbage.Proof.MlKem.Compress
meta import VerifiedGarbage.Proof.MlKem.Encode
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Chi
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.ChiWord
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Correction
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Cycle
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwLanes
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.HwRounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rho
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.RhoStep
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rotate
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Rounds
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Row
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.SaveRow
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
meta import VerifiedGarbage.Proof.Sha3.Arith

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem positiveDecF {D : Nat} {p : Params} (hc : lChk p = true) {σ : State} {s : State} (hk : PositiveIK p D σ s) :
    WP isa (.block cntDec) s fun s' =>
      s'.gpr .x9 = s.mem.readW (pa s (sc oCNT)) 64 - BitVec.ofNat 64 1 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      bytesAt s'.mem (pa s' (sc oCT)) (cLen p) = bytesAt s.mem (pa s (sc oCT)) (cLen p) ∧
      ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f := by
  simp only [lChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨w1, r1⟩, -⟩, -⟩, k3⟩, -⟩, f2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (cntDec_ok s (L.inW w1) (L.inR r1)) fun s' ⟨⟨hm, hz⟩, k⟩ => ?_
  have hf : Frame [⟨pa s (sc oCNT), 8⟩] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hP : PPostB D s s' [(sc oCNT, 8)] := postB_of_keep k (by decide) hf
  exact ⟨hz, k.get .x24, L.keepBytes hP k3, fun f h => HFam.keep L hP f2 h⟩

section
variable {p : Params} {D : Nat}

theorem liftRootQ {E I J G Q₀ Q F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (fun x y => RootRS p D E I x y ∧ G x y) c Q₀)
    (hQ : ∀ σ₁ σ₂ x y x' y', (signK p D).pre σ₁ → (signK p D).pre σ₂ → (signK p D).pub σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → G x y → J σ₁ x' → J σ₂ y' → F x x' → F y y' → Q₀ x' y' → RootSymbolsEq x' y' → Q x' y') :
    RelCT isa (fun x y => RootRS p D E I x y ∧ G x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  have roots := hr.1.2
  obtain ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, _⟩, hg⟩ := hr
  obtain ⟨_, u₁, f₁, j₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, j₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ _ _ _ _ p₁ p₂ hpub he i₁ i₂ hg j₁ j₂ g₁ g₂ hq (by
    simpa only [RootSymbolsEq, VG.AArch64.Exec.syms e₁, VG.AArch64.Exec.syms e₂] using roots)⟩

end

theorem PositiveLP.il {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : PositiveLP p D σ t s) (hz : s.gpr .x9 ≠ 0) :
    PositiveIL p D σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h hz

theorem PositiveLP.xs {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : PositiveLP p D σ t s) (hz : s.gpr .x9 = 0) :
    PositiveXS p D σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd hz h
  · exact h

abbrev PositiveOX (p : Params) (D : Nat) (x y : State) : Prop :=
  RootRS p D (fun _ _ => True) (PositiveXS p D) x y ∧ x.gpr .x24 = y.gpr .x24 ∧
    (x.gpr .x24 = 1 → bytesAt x.mem (pa x (sc oCT)) (cLen p) = bytesAt y.mem (pa y (sc oCT)) (cLen p) ∧
      ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f)

abbrev PositiveIX (p : Params) (D : Nat) (t : Nat) (x y : State) : Prop :=
  x.gpr .x9 = y.gpr .x9 ∧
    (x.gpr .x9 ≠ 0 → RootRS p D (LeakEq p (t + 1)) (fun σ s => PositiveIL p D σ (t + 1) s) x y) ∧
    (x.gpr .x9 = 0 → PositiveOX p D x y)

section
variable {p : Params} {D : Nat}
theorem positiveEndPF_tr (h3 : Ok3 p) (hp : ParamsOk p) (hc : lChk p = true) {t : Nat} :
    RelCT isa (fun x y => RootRS p D (LeakEq p t) (fun σ s => PositiveEP p D σ t s ∨ PositiveEF p D σ t s) x y ∧ True)
      (.block cntDec) (PositiveIX p D t) := by
  refine liftRootQ (J := fun σ s => PositiveLP p D σ t s) (fun σ s _ h => WP.conj (positiveDecEnd h3 hp hc (h.elim .inl (.inr ∘ .inl)))
      (positiveDecF hc (h.elim (·.k) (·.k))))
    (lrel_tr (fun x y h => h.1.1.lrel fun σ s h => h.elim (·.k.d.im.st) (·.k.d.im.st)) (by taint_decide)) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ ⟨z₁, r₁, b₁, h₁⟩ ⟨z₂, r₂, b₂, h₂⟩ _ roots
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.gpr .x9 = 0 := by rw [z₁, e₁.cnt, one_sub_one]
    have zy : y'.gpr .x9 = 0 := by rw [z₂, e₂.cnt, one_sub_one]
    refine ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
      j₁.xs zx, j₂.xs zy⟩, roots⟩, by rw [r₁, r₂, e₁.x24, e₂.x24], fun _ => ⟨by rw [b₁, b₂, e₁.ct, e₂.ct]; exact leq_ct he e₁.t_lt,
      Hv p σ₁ (p.ℓ * t), h₁ _ e₁.h, h₂ _ fun j hj => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) j (List.mem_range.mpr hj)]
    exact e₂.h j hj
  · exact absurd ((leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.gpr .x9 = y'.gpr .x9 := by rw [z₁, z₂, f₁.cnt, f₂.cnt]
    refine ⟨zxy, fun h => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, leq_succ he f₁.t_lt ⟨_, iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, roots⟩, fun h => ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, j₁.xs h, j₂.xs (zxy ▸ h)⟩, roots⟩,
      by rw [r₁, r₂, f₁.x24, f₂.x24], fun h1 => absurd (h1.symm.trans (r₁.trans f₁.x24)) (by decide)⟩⟩

theorem positiveEndB_tr (h3 : Ok3 p) (hp : ParamsOk p) (hc : lChk p = true) {t : Nat} :
    RelCT isa (fun x y => RootRS p D (LeakEq p t) (fun σ s => PositiveEB p D σ t s) x y ∧ True) (.block cntDec) (PositiveIX p D t) := by
  refine liftRootQ (J := fun σ s => PositiveLP p D σ t s) (fun σ s _ h => WP.conj (positiveDecEnd h3 hp hc (.inr (.inr h))) (positiveDecF hc h.k))
    (lrel_tr (fun x y h => h.1.1.lrel fun σ s h => h.k.d.im.st) (by taint_decide)) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ ⟨z₁, r₁, _⟩ ⟨z₂, r₂, _⟩ _ roots
  have zx : x'.gpr .x9 = 0 := by rw [z₁, e₁.cnt, one_sub_one]
  have zy : y'.gpr .x9 = 0 := by rw [z₂, e₂.cnt, one_sub_one]
  exact ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
    j₁.xs zx, j₂.xs zy⟩, roots⟩, by rw [r₁, r₂, e₁.x24, e₂.x24],
    fun h1 => absurd (h1.symm.trans (r₁.trans e₁.x24)) (by decide)⟩⟩

end
end VG.Proof.MlDsa.AArch64.Sign
