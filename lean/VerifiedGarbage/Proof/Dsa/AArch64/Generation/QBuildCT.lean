module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.HashCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QArgs
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.QShapeCT

/-! Subgroup hashing and byte shaping have public traces. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

structure QHashPlan where
  F : Addr
  S : Addr
  label : Addr
  len : Nat
  output : Addr
  width : len = 20 ∨ len = 32

structure QHashState (p : QHashPlan) (s : State) : Prop where
  layout : Lay s p.F p.S
  rep : ∃ V W, Rep s.mem p.F p.S V W ∧ LabAt s p.F p.S W p.label p.len ∧ W 0 = p.output

theorem qHash_ct (H : GenerationHashes) : RelCT isa (Two QHashState)
    (Impl.Dsa.AArch64.Generation.seedHash H.sha1 H.sha256) (Two QHashState) := by
  refine two_post ?_ ?_
  · intro s t tr1 tr2 u v hp e1 e2
    obtain ⟨p, hs, ht, _⟩ := hp
    obtain ⟨Vs, Ws, Rs, As, _⟩ := hs.rep
    obtain ⟨Vt, Wt, Rt, At, _⟩ := ht.rep
    exact seedHash_ct H.h1 H.h256 (by rcases p.width with h | h <;> omega) s t tr1 tr2 u v
      ⟨⟨Vs, Ws, hs.layout, Rs, As⟩, ⟨Vt, Wt, ht.layout, Rt, At⟩⟩ e1 e2
  · intro p s h
    obtain ⟨V, W, R, A, hop⟩ := h.rep
    exact WP.mono (seedHash_frame_ok H.h1 H.h256 H.hash1 H.hash256 H.size1 H.size256
      H.width1 H.width256 p.width h.layout R A)
      fun t ⟨Lt, step, _, V', Rt, _, _⟩ => ⟨Lt, V', W, Rt, A.congr step.rd step.wr rfl rfl, hop⟩

def QShapeState (p : QHashPlan) (s : State) : Prop :=
  s.gpr .x2 = p.output ∧ s.gpr .x12 = VG.Proof.Bignum.off p.S oDig ∧ s.gpr .x9 = BitVec.ofNat 64 p.len

theorem qArgs_ct : RelCT isa (Two QHashState) (.block Impl.Dsa.AArch64.Generation.qArgs) (Two QShapeState) := by
  refine two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)) ?_
  intro p s h
  obtain ⟨V, W, R, A, hop⟩ := h.rep
  exact WP.mono (qArgs_ok h.layout R hop A.hll) fun _ ⟨a, b, c, _, _⟩ => ⟨a, b, c⟩

theorem qCandidate_ct (H : GenerationHashes) : RelCT isa (Two QHashState)
    (Impl.Dsa.AArch64.Generation.qCandidate H.sha1 H.sha256) (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.qCandidate
  refine RelCT.seq (qHash_ct H) (RelCT.seq qArgs_ct (qShape_ct ?_))
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.1.trans ht.1.symm
  · exact hs.2.2.trans ht.2.2.symm

end VG.Proof.Dsa.AArch64.Generation
