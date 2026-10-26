module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DomainCallCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCore
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateArgs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DomainCallCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.Validate
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Basic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateCore
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ValidateArgs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
public import Mathlib.Algebra.Group.Nat.Defs

/-! # Timing of final parameter validation and its success/retry decision -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64
open VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.AArch64.Generation

structure ValidatePublic where
  input : ParametersInput
  B : Addr
  F : Addr
  S : Addr
  base : input.base = VG.Proof.Bignum.off B domainCheck
  frame : (⟨F, frameBytes⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩
  hash : (⟨S, oRsa⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩

def ValidatePublic.call (p : ValidatePublic) : DomainCallPublic := ⟨p.input, VG.Proof.Bignum.off p.B packed⟩

def ValidateBefore (pLen qLen : Nat) (p : ValidatePublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ (∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.B) ∧
  Scr s p.input.base Impl.Dsa.Layout.usedBytes ∧
  Src s p.input.base Impl.Dsa.Layout.usedBytes (VG.Proof.Bignum.off p.B packed) p.input.params ∧
  p.input.pLen = pLen ∧ p.input.qLen = qLen

theorem validateArgs_ready {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16) (h : ValidateBefore pLen qLen p s) :
    WP isa (.block (validateArgs pLen qLen)) s (DomainCallBefore p.call) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  refine WP.mono (validateArgs_ok L R hp hq) fun t ⟨hd, h8, hdx, hcx, hm, hk⟩ => ?_
  have hd' : t.gpr .x0 = VG.Proof.Bignum.off p.B packed := hb ▸ hd
  refine ⟨⟨hs.congr hk.wr, (hb ▸ h8).trans p.base.symm,
    by change t.gpr .x2 = BitVec.ofNat 64 p.input.pLen; rw [heP]; exact hdx,
    by change t.gpr .x3 = BitVec.ofNat 64 p.input.qLen; rw [heQ]; exact hcx, ?_⟩, hd'⟩
  rw [hd']
  exact src.congrK (fun _ _ => by rw [hm]) hk

def ValidateResult (p : ValidatePublic) (s : State) : Prop :=
  s.sp = p.F ∧ s.gpr .x0 = BitVec.ofNat 64
    (if Spec.Dsa.checkParametersBytes p.input.pLen p.input.qLen p.input.params then 1 else 0)

theorem validateCore_result (M : Mont)  {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16) (h : ValidateBefore pLen qLen p s) :
    WP isa (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.AArch64.Generate.checkParameters M.mm))
      s (ValidateResult p) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  have step := validateCore_ok M p.input L R (by rw [hb]; exact p.base)
    (by rw [heP]; exact hp) (by rw [heQ]; exact hq) hs (hb ▸ src) p.frame p.hash
  rw [heP, heQ] at step
  exact WP.mono step fun t ⟨hr, Lt, _, _, _⟩ =>
    ⟨Lt.sp, by simpa only [heP, heQ] using hr⟩

theorem validate_ct_of (M : Mont)  (pLen qLen : Nat)
    (hp : pLen < 2 ^ 16) (hq : qLen < 2 ^ 16)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (validateArgs pLen qLen)) hc).isSome = true) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate M.mm pLen qLen) (fun _ _ => True) := by
  have core : RelCT isa (Two (ValidateBefore pLen qLen))
      (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.AArch64.Generate.checkParameters M.mm))
      (Two ValidateResult) := by
    refine two_post (RelCT.seq (two_post
      (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht)
      (fun _ _ h => validateArgs_ready hp hq h))
      (two_map ValidatePublic.call (fun _ _ h => h) (domainCall_ct M)))
      (fun _ _ h => validateCore_result M hp hq h)
  unfold validate
  refine RelCT.seq core (two_ite (fun _ _ _ hs ht => by
    change some (_ == (0#64)) = some (_ == (0#64))
    simp only [State.read, Size.bits, BitVec.setWidth_eq, hs.2, ht.2]) ?_ ?_)
  all_goals exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

theorem validate_ct (M : Mont)  (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate M.mm pLen qLen) (fun _ _ => True) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact validate_ct_of M _ _ (by decide) (by decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
