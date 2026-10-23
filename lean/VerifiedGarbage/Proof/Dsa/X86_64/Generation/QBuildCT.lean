module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.QCandidate
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.QCandidate
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.QArgs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.TCB.Registration

/-! # Subgroup-candidate hashing and shaping have public traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

structure QHashPlan where
  hash : LQ
  output : Addr
  width : hash.labLen = 20 ∨ hash.labLen = 32

structure QHashState (n : Nat) (p : QHashPlan) (s : State) : Prop where
  frame : FrV n p.hash.F p.hash.ws s
  layout : Lay s p.hash.F p.hash.S
  rep : ∃ V W, Rep s.mem p.hash.F p.hash.S V W ∧
    LabAt s p.hash.F p.hash.S W p.hash.lab p.hash.labLen ∧ W 0 = p.output

theorem QHashState.label {n : Nat} {p : QHashPlan} {s : State} (h : QHashState n p s) : LW n p.hash s := by
  obtain ⟨V, W, R, A, _⟩ := h.rep
  exact ⟨h.frame, h.layout, V, W, R, A⟩

theorem qHash_ct (H : GenerationHashes) (n : Nat) (hn : n = 2 ∨ n = 3) (len : Nat) :
    RelCT isa (Two (QHashState n)) (Impl.Dsa.X86_64.Generation.seedHashAt H.sha1 H.sha256 len)
      (Two (QHashState n)) := by
  refine two_post (two_map QHashPlan.hash (fun _ _ h => h.label) (seedHashAt_ct H.h1 H.h256 n hn len)) ?_
  intro p s h
  obtain ⟨V, W, R, A, hop⟩ := h.rep
  unfold Impl.Dsa.X86_64.Generation.seedHashAt
  split
  · exact WP.mono (hash_bytes_frame H.h1 H.hash1 H.size1 h.layout R A)
      fun t ⟨L, rd, wr, _, _, V', R', _, _⟩ =>
        ⟨h.frame.congr (L.rsp.trans h.layout.rsp.symm) wr, L,
          V', W, R', A.congr rd wr rfl rfl, hop⟩
  · exact WP.mono (hash_bytes_frame H.h256 H.hash256 H.size256 h.layout R A)
      fun t ⟨L, rd, wr, _, _, V', R', _, _⟩ =>
        ⟨h.frame.congr (L.rsp.trans h.layout.rsp.symm) wr, L,
          V', W, R', A.congr rd wr rfl rfl, hop⟩

def QShapeState (p : QHashPlan) (s : State) : Prop :=
  s.gpr .rdi = p.output ∧ s.gpr .rsi = off p.hash.S oDig ∧
    s.gpr .rcx = BitVec.ofNat 64 p.hash.labLen ∧
    s.gpr .rdx = BitVec.ofNat 64 (8 * p.hash.labLen)

theorem qArgs_ct (n : Nat) :
    RelCT isa (Two (QHashState n)) (.block Impl.Dsa.X86_64.Generation.qArgs) (Two QShapeState) := by
  refine two_post (two_taint [.rsp] ?_ (by taint_decide)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · intro p s h
    obtain ⟨V, W, R, A, hop⟩ := h.rep
    exact WP.mono (qArgs_ok h.layout R hop A.hll) fun _ ⟨a, b, c, d, _, _⟩ => ⟨a, b, c, d⟩

theorem qCandidate_ct (H : GenerationHashes) (n : Nat) (hn : n = 2 ∨ n = 3) (len : Nat) :
    RelCT isa (Two (QHashState n)) (Impl.Dsa.X86_64.Generation.qCandidate H.sha1 H.sha256 len)
      (fun _ _ => True) := by
  refine RelCT.seq (qHash_ct H n hn len) (RelCT.seq (qArgs_ct n) ?_)
  apply VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ct
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.1.trans ht.2.1.symm
  · exact hs.2.2.1.trans ht.2.2.1.symm
  · exact hs.2.2.2.trans ht.2.2.2.symm

end VG.Proof.Dsa.X86_64.Generation
