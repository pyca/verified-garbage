module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
public import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.LabelCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Hash
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Seed-hash selection and streaming calls have public traces -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Pbkdf2.Md.X86_64

theorem hashTest_ct (n : Nat) :
    RelCT isa (Two (LW n)) (.block Impl.Dsa.X86_64.Generation.hashTest)
      (Two fun q s => LW n q s ∧ s.zf = some (BitVec.ofNat 64 q.labLen == 20)) := by
  refine two_post (two_taint [.rsp] ?_ (by taint_decide)) ?_
  · intro q s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.L.rsp.trans ht.L.rsp.symm
  · intro q s h
    obtain ⟨V, W, R, A⟩ := h.rep
    exact WP.mono (hashTest_ok h.L R A.hll) fun t ⟨hz, hm, hk⟩ =>
      ⟨h.congr (hk.gpr (by decide)) hk.2.1 hk.2.2 hm, hz⟩

theorem seedHash_ct {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Calls.StreamOK G1) (h256 : Calls.StreamOK G256)
    (n : Nat) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (LW n)) (Impl.Dsa.X86_64.Generation.seedHash G1 G256)
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.seedHash
  refine RelCT.seq (hashTest_ct n) ?_
  refine two_ite (fun q s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
  · exact (hashLabel_ct h1 n hn (Or.inl rfl)).mono
      (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  · exact (hashLabel_ct h256 n hn (Or.inl rfl)).mono
      (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)

theorem seedHashAt_ct {G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream}
    (h1 : Calls.StreamOK G1) (h256 : Calls.StreamOK G256)
    (n : Nat) (hn : n = 2 ∨ n = 3) (len : Nat) :
    RelCT isa (Two (LW n)) (Impl.Dsa.X86_64.Generation.seedHashAt G1 G256 len)
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.seedHashAt
  split
  · exact hashLabel_ct h1 n hn (Or.inl rfl)
  · exact hashLabel_ct h256 n hn (Or.inl rfl)

end VG.Proof.Dsa.X86_64.Generation
