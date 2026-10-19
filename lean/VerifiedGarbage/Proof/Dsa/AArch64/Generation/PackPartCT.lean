module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPart
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PackPart
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT

/-! # Copy generated components using only public addresses and lengths -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

structure PackPublic where
  B : Addr
  F : Addr
  S : Addr

def PackBefore (p : PackPublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ ∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.B

def PackReady (src dst len : Nat) (p : PackPublic) (s : State) : Prop :=
  s.gpr .x12 = VG.Proof.Bignum.off p.B src ∧ s.gpr .x2 = VG.Proof.Bignum.off p.B dst ∧
  s.gpr .x9 = BitVec.ofNat 64 len

theorem packPart_ct (src dst len : Nat) (hs : src < 2 ^ 16) (hd : dst < 2 ^ 16) (hl : len ≤ 1024)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs []) (.block (packArgs src dst len)) hc).isSome = true) :
    RelCT isa (Two PackBefore) (packPart src dst len) (fun _ _ => True) := by
  unfold packPart
  refine RelCT.seq (two_post (Ψ := PackReady src dst len)
    (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht) ?_) ?_
  · intro p s ⟨L, V, W, R, hb⟩
    exact WP.mono (packArgs_ok L R hs hd hl) fun t ⟨hsi, hdi, hcx, _, _⟩ =>
      ⟨hb ▸ hsi, hb ▸ hdi, hcx⟩
  · exact two_taint [.x12, .x2, .x9] (fun p s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
