module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DomainCallCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Validate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Validate

/-! # Timing of final parameter validation and its success/retry decision -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Dsa.Generation.Layout VG.Impl.Dsa.X86_64.Generation

structure ValidatePublic where
  input : ParametersInput
  B : Addr
  F : Addr
  S : Addr
  base : input.base = off B domainCheck
  frame : (⟨F, frameBytes⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩
  hash : (⟨S, oRsa⟩ : Region).Disjoint ⟨input.base, Impl.Dsa.Layout.usedBytes⟩

def ValidatePublic.call (p : ValidatePublic) : DomainCallPublic := ⟨p.input, off p.B packed⟩

def ValidateBefore (pLen qLen : Nat) (p : ValidatePublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ (∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.B) ∧
  Scr s p.input.base Impl.Dsa.Layout.usedBytes ∧
  Src s p.input.base Impl.Dsa.Layout.usedBytes (off p.B packed) p.input.params ∧
  p.input.pLen = pLen ∧ p.input.qLen = qLen

theorem validateArgs_ready {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 32) (hq : qLen < 2 ^ 32) (h : ValidateBefore pLen qLen p s) :
    WP isa (.block (validateArgs pLen qLen)) s (DomainCallBefore p.call) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  refine WP.mono (validateArgs_ok L R hp hq) fun t ⟨hd, h8, hdx, hcx, hm, hk⟩ => ?_
  have hd' : t.gpr .rdi = off p.B packed := hb ▸ hd
  refine ⟨⟨hs.congr hk.2.2, (hb ▸ h8).trans p.base.symm,
    by change t.gpr .rdx = BitVec.ofNat 64 p.input.pLen; rw [heP]; exact hdx,
    by change t.gpr .rcx = BitVec.ofNat 64 p.input.qLen; rw [heQ]; exact hcx, ?_⟩, hd'⟩
  rw [hd']
  exact src.congrK (fun _ _ => by rw [hm]) hk

def ValidateResult (p : ValidatePublic) (s : State) : Prop :=
  s.gpr .rsp = p.F ∧ s.gpr .rax = BitVec.ofNat 64
    (if Spec.Dsa.checkParametersBytes p.input.pLen p.input.qLen p.input.params then 1 else 0)

theorem validateCore_result (M : Mont) (Sq : MontS) {pLen qLen : Nat} {p : ValidatePublic} {s : State}
    (hp : pLen < 2 ^ 32) (hq : qLen < 2 ^ 32) (h : ValidateBefore pLen qLen p s) :
    WP isa (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.X86_64.Generate.checkParameters Sq.mm M.mm))
      s (ValidateResult p) := by
  obtain ⟨L, ⟨V, W, R, hb⟩, hs, src, heP, heQ⟩ := h
  have step := validateCore_ok M Sq p.input L R (by rw [hb]; exact p.base)
    (by rw [heP]; exact hp) (by rw [heQ]; exact hq) hs (hb ▸ src) p.frame p.hash
  rw [heP, heQ] at step
  exact WP.mono step fun t ⟨hr, Lt, _, _, _⟩ =>
    ⟨Lt.rsp, by simpa only [heP, heQ] using hr⟩

theorem validate_ct_of (M : Mont) (Sq : MontS) (pLen qLen : Nat)
    (hp : pLen < 2 ^ 32) (hq : qLen < 2 ^ 32)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (validateArgs pLen qLen)) hc).isSome = true) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate Sq.mm M.mm pLen qLen) (fun _ _ => True) := by
  have core : RelCT isa (Two (ValidateBefore pLen qLen))
      (.seq (.block (validateArgs pLen qLen)) (Impl.Dsa.X86_64.Generate.checkParameters Sq.mm M.mm))
      (Two ValidateResult) := by
    refine two_post (RelCT.seq (two_piece [.rsp] ?_ ht
      (fun _ _ h => validateArgs_ready hp hq h))
      (two_map ValidatePublic.call (fun _ _ h => h) (domainCall_ct M Sq)))
      (fun _ _ h => validateCore_result M Sq hp hq h)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.rsp.trans ht.1.rsp.symm
  unfold validate
  refine RelCT.seq core (RelCT.seq (two_piece (Ψ := fun (p : ValidatePublic) s => s.gpr .rsp = p.F ∧
    s.zf = some (!(Spec.Dsa.checkParametersBytes p.input.pLen p.input.qLen p.input.params)))
      [.rax] ?_ (by taint_decide) ?_) ?_)
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.trans ht.2.symm
  · intro p s h
    exact WP.mono (validateTest_ok h.2) fun t ⟨hz, _, hk⟩ => ⟨(hk.gpr (by decide)).trans h.1, hz⟩
  · refine two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    all_goals
      exact two_taint [.rsp] (fun _ _ _ hs ht r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact hs.1.1.trans ht.1.1.symm) (by taint_decide)

theorem validate_ct (M : Mont) (Sq : MontS) (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (ValidateBefore pLen qLen)) (validate Sq.mm M.mm pLen qLen) (fun _ _ => True) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals exact validate_ct_of M Sq _ _ (by decide) (by decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
