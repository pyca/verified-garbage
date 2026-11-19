module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLoop
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import Std.Tactic.BVDecide.Normalize.Prop
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4CT
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsPrologue
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejVerified
meta import VerifiedGarbage.Proof.MlDsa.DecideAt
meta import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedLoop
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedLoopEndTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitialization
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChecksEnd
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseOCT
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseCCTBase
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedChallenge
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedInitialization
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedDecodeTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
public import VerifiedGarbage.Spec.MlDsa
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BallResident
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Rej4.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsExecution
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseA4
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Common
meta import VerifiedGarbage.Spec.MlDsa

/-! ### `MlDsa.AArch64.Sign.OptimizedExpansion`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.AArch64.Message

theorem expandA_depth {P : Prims} {S : Nat} (hp : PrimsOk P S) (p : Params) :
    16*(Impl.MlDsa.AArch64.Sign.expandA P p).aarch64Depth≤S := by
  have hr : DLe (S/16) P.rejNTT := ⟨by have := hp.rejNTT.fd; omega_using [this], hp.rejNTT.nd⟩
  have h4 : DLe (S/16) P.rej4 := ⟨by have := hp.rej4.fd; omega_using [this], hp.rej4.nd⟩
  have hd : DLe (S/16) (Impl.MlDsa.AArch64.Sign.expandA P p) := by
    unfold Impl.MlDsa.AArch64.Sign.expandA
    dle_tac
  have := hd.le
  omega_using [this]

theorem expandA_noDit {P : Prims} {S : Nat} (hp : PrimsOk P S) (p : Params)  :
    (Impl.MlDsa.AArch64.Sign.expandA P p).all (fun i => !i.touchesDit) = true := by
  have hr : DLe (S/16) P.rejNTT := ⟨by have := hp.rejNTT.fd; omega_using [this], hp.rejNTT.nd⟩
  have h4 : DLe (S/16) P.rej4 := ⟨by have := hp.rej4.fd; omega_using [this], hp.rej4.nd⟩
  have hd : DLe (S/16) (Impl.MlDsa.AArch64.Sign.expandA P p) := by
    unfold Impl.MlDsa.AArch64.Sign.expandA
    dle_tac
  exact hd.nd

/-- Matrix expansion retains the immutable root tables without changing
its sampled values, public failure behavior, or instruction sequence. -/
theorem rooted_expandA_ok {P : Prims} {S : Nat} (hp : PrimsOk P S) {p : Params}
    (h3 : Ok3 p) (hc : aChk p=true) {σ s : State} (hs : RootedSt p S σ s)
    (hf : s.gpr .x24=1) : WP isa (Impl.MlDsa.AArch64.Sign.expandA P p) s
      fun t => IA p S σ (p.k*p.ℓ) t ∧ StaticRoots S t :=
  hs.2.phase (expandA_depth hp p) hp.s64 (expandA_ok hp h3 hc hs.1 hf)

end VG.Proof.MlDsa.AArch64.Sign

end

end

/-! ### `MlDsa.AArch64.Sign.OptimizedRestTiming`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Sign.OptimizedInitializationTiming`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

/-- The secret-vector transforms and mask-seed hash keep the original
initialization trace policy, adding only public static-table addresses. -/
theorem positiveInitialization_tr {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params}
    (hp : Ok3 p) {E : State → State → Prop} :
    RelCT isa (RootRS p S E (fun σ s => IM p S σ s ∧ StaticRoots S s))
      (positiveDecodeWith keccak.callee P p) (RootRS p S E (PositiveIK p S)) := by
  unfold positiveDecodeWith
  refine RelCT.seq (R := RootRS p S E (PositiveID p S · p.ℓ p.k p.k)) ?_ ?_
  · apply RelCT.mono (positiveDecodeSecrets_tr hP (dChk_ok hp))
    · intro x y h
      exact ⟨h.1.mono (fun _ _ h => h) (fun _ _ h =>
        ⟨h.1,h.2,by simp [PosFam],by simp [PosFam],by simp [PosFam]⟩),h.2⟩
    · intro _ _ h; exact h
  · apply liftRootT (fun _ _ h => ⟨h.im.st,h.roots⟩)
      (fun _ _ _ h => positiveSeed_ok hP hp h)
    exact vector_lrel_tr (fun _ _ h => h.1) keccak.mldsaSignDecodeTaint.choose_spec

end VG.Proof.MlDsa.AArch64.Sign

end

end

-- Formerly `VerifiedGarbage/Proof/MlDsa/AArch64/Sign/OptimizedOutputTiming.lean`, which only this module imported.
section

/-! ## From `OptimizedOutputPackTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Sign.Output
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc seqR)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Before the signature: an iteration passed, with `c̃`, `z` and `h`. -/
def IOi (p : Params) (D : Nat) (σ s : State) : Prop :=
  ∃ κ, St p D σ s ∧ bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ ∧ Fam s (yBase p) p.ℓ (Zv p σ κ) ∧
    HFam s 5 p.k (Hv p σ κ) ∧ PassV p σ κ ∧ s.gpr .x24 = 1

/-- `c̃` and the first `r` polynomials of `z` in `sig`, of an iteration that passed. -/
def IOr (p : Params) (D : Nat) (r : Nat) (σ s : State) : Prop := ∃ κ, OS p D σ κ r s ∧ PassV p σ κ

/-- Two runs agree on their hints. -/
abbrev HJ (p : Params) (x y : State) : Prop := ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f

section
variable {p : Params} {D : Nat}

theorem IOr.zr {r' : Nat} {σ s : State} (h : IOr p D r' σ s) {r : Nat} (hr : r < p.ℓ) :
    Reduced s.mem (pa s (yP p r)) ∧ InRange s.mem (pa s (yP p r)) (p.γ₁ - 1) p.γ₁ := by
  obtain ⟨κ, h, hpass⟩ := h
  have hzr := h.z r hr
  exact ⟨hzr.1, inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)⟩

theorem output_tr {P : Prims} (hP : PrimsOk P D) (hc : oChk p = true) {E : State → State → Prop} :
    RelCT isa (fun x y => RS p D E (IOi p D) x y ∧ HJ p x y) (output P p) fun _ _ => True := by
  have hc' := hc
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, -⟩, cz⟩, ch⟩, hhp⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc'
  unfold output
  refine RelCT.seq (R := fun x y => RS p D E (IOr p D 0) x y ∧ HJ p x y) (liftQ
    (F := fun s s' => ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f)
    (fun σ s _ ⟨κ, hk, hct, hz, hh, hpass, h15⟩ =>
      WP.mono (outCopy_ok hc hk hct hz hh h15) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
    (copy_tr (.inr rfl) rfl fun x y h => h.1.lrel fun σ s ⟨_, hk, _⟩ => hk)
    fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
      ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩) ?_
  refine RelCT.seq (R := fun x y => RS p D E (IOr p D p.ℓ) x y ∧ HJ p x y) (RelCT.mono (seqR_tr
    (Q := fun r x y => RS p D E (IOr p D r) x y ∧ HJ p x y) p.ℓ 0 fun r _ hr => liftQ
      (F := fun s s' => ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f)
      (fun σ s _ ⟨κ, h, hpass⟩ => WP.mono (packZ_ok hP hc (by omega_using [hr]) h hpass) fun _ h => ⟨⟨κ, h.1, hpass⟩, h.2⟩)
      (RelCT.mono (bpAt_tr hP hbp hzl (cz r (by omega_using [hr])).1.1) (fun x y ⟨h, _⟩ =>
        ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k, by
          obtain ⟨_, _, _, _, _, _, i₁, i₂⟩ := h
          exact ⟨i₁.zr (by omega_using [hr]), i₂.zr (by omega_using [hr])⟩⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ ⟨f, hx, hy⟩ j₁ j₂ g₁ g₂ _ =>
        ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, f, g₁ f hx, g₂ f hy⟩)
    (fun _ _ h => h) fun x y h => by rwa [Nat.zero_add] at h) ?_
  refine RelCT.mono (hbpAt_tr hP hhp ch) (fun x y ⟨h, f, hx, hy⟩ => ⟨h.lrel fun σ s ⟨_, h, _⟩ => h.k, ?_⟩)
    fun _ _ _ => trivial
  obtain ⟨_, _, _, _, _, _, ⟨_, o₁, a₁⟩, ⟨_, o₂, a₂⟩⟩ := h
  exact ⟨hones_ok o₁ a₁, hones_ok o₂ a₂, hint_coeffs hx hy⟩

end
end VG.Proof.MlDsa.AArch64.Sign.Output

end

/-! ## From `OptimizedOutputTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.Optimized

def ConversionI (p : Params) (S : Nat) (lo hi : Int) (r : Nat) (σ s : State) : Prop :=
  ∃κ,AcceptedConversion p S σ κ lo hi r s ∧ PassV p σ κ

theorem conversionReady {p : Params} {S : Nat} {σ s : State} {κ r : Nat} {lo hi : Int}
    (hp : Ok3 p) (hr : r<p.ℓ) (hl : -(q:Int)<lo) (hh : hi<(q:Int))
    (h : AcceptedConversion p S σ κ lo hi r s) : Response.CanonicalizeCallReady (yP p r) s := by
  have hc := canonicalizeZChk_ok hp r hr
  simp only [canonicalizeZChk,Bool.and_eq_true] at hc
  exact ⟨h.z.rooted.1.lay.nwp hc.1.1,centered_of_signed (h.z.pending r (by omega_using []) hr) hl hh,
    h.z.rooted.1.lay.cR hc.1.1,h.z.rooted.1.lay.cW hc.1.2⟩

theorem conversionStep_tr {p : Params} {S r : Nat} {lo hi : Int} {E : State → State → Prop}
    (hp : Ok3 p) (hr : r<p.ℓ) (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    RelCT isa (fun x y => RS p S E (ConversionI p S lo hi r) x y ∧ HJ p x y)
      (Impl.MlDsa.AArch64.Sign.Optimized.canonicalizeZ p r)
      (fun x y => RS p S E (ConversionI p S lo hi (r+1)) x y ∧ HJ p x y) := by
  refine liftQ (J := ConversionI p S lo hi (r+1)) (Q₀ := fun _ _ => True) (F := fun s t => ∀f,HFam s 5 p.k f → HFam t 5 p.k f) ?_ ?_ ?_
  · intro σ s _ ⟨κ,h,hpass⟩
    have hc := conversionOutputChk_ok hp
    simp only [conversionOutputChk,List.all_eq_true,List.mem_range,Bool.and_eq_true] at hc
    refine WP.mono (canonicalizeZ_step_post hr (canonicalizeZChk_ok hp r hr)
      (canonicalizeZKeepChk_ok hp) hl hh h.z) fun t ⟨hz,hpost⟩ => ?_
    have keepHints : ∀f,HFam s 5 p.k f → HFam t 5 p.k f :=
      fun _ hf => HFam.keep h.z.rooted.1.lay hpost (hc r hr).2 hf
    exact ⟨⟨κ,⟨hz,(h.z.rooted.1.lay.keepBytes hpost (hc r hr).1).trans h.ct,
      keepHints _ h.hints⟩,hpass⟩,fun _ hf => keepHints _ hf⟩
  · apply Response.canonicalizeAt_tr (S := S) (ptr_ok (by change Reg.x28∈keptRegs; decide))
    intro x y hxy
    have L := hxy.1.lrel (fun _ _ ⟨_,h,_⟩ => h.z.rooted.1)
    obtain ⟨_,_,_,_,_,_,⟨_,hx,_⟩,⟨_,hy,_⟩⟩ := hxy.1
    exact ⟨conversionReady hp hr hl hh hx,conversionReady hp hr hl hh hy,
      L.pa (by change Reg.x28∈bases; decide),L.sp⟩
  · intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ hHints j₁ j₂ g₁ g₂ _
    obtain ⟨f,hx,hy⟩ := hHints
    exact ⟨⟨σ₁,σ₂,p₁,p₂,hpub,he,j₁,j₂⟩,f,g₁ f hx,g₂ f hy⟩

theorem optimizedOutput_tr {P : Prims} {p : Params} {S : Nat} {lo hi : Int}
    {E : State → State → Prop} (hP : PrimsOk P S) (hp : Ok3 p)
    (hl : -(q:Int)<lo) (hh : hi<(q:Int)) :
    RelCT isa (fun x y => RS p S E (ConversionI p S lo hi 0) x y ∧ HJ p x y)
      (Impl.MlDsa.AArch64.Sign.Optimized.output P p) fun _ _ => True := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.output
  refine RelCT.seq (R := fun x y => RS p S E (ConversionI p S lo hi p.ℓ) x y ∧ HJ p x y) ?_ ?_
  · simpa only [Nat.zero_add] using seqR_tr
      (Q := fun r x y => RS p S E (ConversionI p S lo hi r) x y ∧ HJ p x y)
      p.ℓ 0 (fun r _ hr => conversionStep_tr hp (by omega_using [hr]) hl hh)
  · refine RelCT.mono (Output.output_tr hP (Output.oChk_ok hp) (E := E)) ?_ (fun _ _ h => h)
    intro x y ⟨h,hj⟩
    refine ⟨h.mono (fun _ _ he => he) ?_,hj⟩
    intro σ s ⟨κ,hs,hpass⟩
    exact ⟨κ,hs.z.rooted.1,hs.ct,hs.z.converted,hs.hints,hpass,hs.z.flag⟩

end VG.Proof.MlDsa.AArch64.Sign

end
end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

theorem PositiveXS.conversion {p : Params} {D : Nat} {σ x : State}
    (h : PositiveXS p D σ x) (h1 : x.gpr .x24=1) :
    ConversionI p D (-(q:Int)+1) ((q:Int)-1) 0 σ x := by
  obtain ⟨t,_,_,_,hpass,hct,hz,hh⟩ := h.pass h1
  exact ⟨p.ℓ*t,⟨⟨⟨h.k.d.im.st,h.k.d.roots⟩,by intro j hj; omega,
    fun j _ hj=>hz j hj,h1⟩,hct,hh⟩,hpass⟩

end VG.Proof.MlDsa.AArch64.Sign

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

def PositiveEntry (p : Params) (D : Nat) (x y : State) : Prop :=
  (signK p D).pre x ∧ (signK p D).pre y ∧ (signK p D).pub x y ∧
  StaticRoots D x ∧ StaticRoots D y ∧ RootSymbolsEq x y

theorem positivePro_tr {p : Params} {D : Nat} (hp : Ok3 p) :
    RelCT isa (PositiveEntry p D) (.block pro)
      (RR p D (fun σ s=>RootedSt p D σ s ∧ s.gpr .x24=1) RootSymbolsEq) := by
  have trace : RelCT isa (PositiveEntry p D) (.block pro) fun _ _=>True :=
    taintRel [.x0,.x1,.x2,.x3,.x4] (fun x y ⟨_,_,pub,_,_,_⟩=>by
      obtain ⟨e0,e1,e2,e3,e4,e5,_⟩ := pub
      refine ⟨e5,fun r hr=>?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl
      exacts [e0,e1,e2,e3,e4]) (by taint_decide)
  intro x y tx ty x' y' h ex ey
  obtain ⟨tr,_⟩ := trace _ _ _ _ _ _ h ex ey
  obtain ⟨px,py,pub,rx,ry,re⟩ := h
  obtain ⟨_,u,eu,hu⟩ := rooted_prologue hp px rx
  obtain ⟨_,v,ev,hv⟩ := rooted_prologue hp py ry
  obtain ⟨_,rfl⟩ := Exec.det ex eu
  obtain ⟨_,rfl⟩ := Exec.det ey ev
  exact ⟨tr,⟨x,y,px,py,pub,hu,hv⟩,by
    simpa only [RootSymbolsEq,VG.AArch64.Exec.syms ex,VG.AArch64.Exec.syms ey] using re⟩

def PositiveRA (p : Params) (D : Nat) (x y : State) : Prop :=
  RA p D (p.k*p.ℓ) x y ∧ StaticRoots D x ∧ StaticRoots D y ∧ RootSymbolsEq x y

theorem positiveExpand_tr {P : Prims} {p : Params} {D : Nat} (hP : PrimsOk P D) (hp : Ok3 p) :
    RelCT isa (RR p D (fun σ s=>RootedSt p D σ s ∧ s.gpr .x24=1) RootSymbolsEq)
      (Impl.MlDsa.AArch64.Sign.expandA P p) (PositiveRA p D) := by
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

end VG.Proof.MlDsa.AArch64.Sign
