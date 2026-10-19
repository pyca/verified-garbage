module
public import Mathlib.Tactic.Conv
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Pack
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackPart
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT

/-! # Copy generated components using only public addresses and lengths -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.X86_64.Generation

structure PackPublic where
  B : Addr
  F : Addr
  S : Addr

def PackBefore (p : PackPublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ ∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.B

def PackReady (src dst len : Nat) (p : PackPublic) (s : State) : Prop :=
  s.gpr .rsi = off p.B src ∧ s.gpr .rdi = off p.B dst ∧
  s.gpr .rcx = BitVec.ofNat 64 len ∧ s.gpr .rdx = BitVec.ofNat 64 (8 * len)

theorem packPart_ct (src dst len : Nat) (hs : src < 2 ^ 31) (hd : dst < 2 ^ 31) (hl : len ≤ 1024)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rsp]) (.block (packArgs src dst len)) hc).isSome = true) :
    RelCT isa (Two PackBefore) (packPart src dst len) (fun _ _ => True) := by
  unfold packPart
  refine RelCT.seq (two_post (Ψ := PackReady src dst len) (two_taint [.rsp] ?_ ht) ?_) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.rsp.trans ht.1.rsp.symm
  · intro p s ⟨L, V, W, R, hb⟩
    exact WP.mono (packArgs_ok L R hs hd hl) fun t ⟨hsi, hdi, hcx, hdx, _, _⟩ =>
      ⟨hb ▸ hsi, hb ▸ hdi, hcx, hdx⟩
  · apply VG.Proof.Ffdh.X86_64.ParameterCandidate.witnessCut_ct
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hs.2.1.trans ht.2.1.symm
    · exact hs.1.trans ht.1.symm
    · exact hs.2.2.1.trans ht.2.2.1.symm
    · exact hs.2.2.2.trans ht.2.2.2.symm

end VG.Proof.Dsa.X86_64.Generation
