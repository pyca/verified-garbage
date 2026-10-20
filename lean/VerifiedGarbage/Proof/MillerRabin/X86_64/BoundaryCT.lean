module

public import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.MillerRabin.X86_64.Round
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! # Staging and returning observe only workspace and stack addresses -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Impl.MillerRabin.X86_64

theorem stage_ct : RelCT isa (Two fun B : Addr => fun s : State => s.gpr .rdi = B)
    (.block stage) fun _ _ => True := by
  exact two_taint [.rdi] (fun B s t hs ht r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact hs.trans ht.symm) (by taint_decide)

theorem finish_ct : RelCT isa (Two fun p : Addr × Addr => fun s : State =>
    s.gpr .rdi = p.1 ∧ s.gpr .rsp = p.2) (.block finish) fun _ _ => True := by
  exact two_taint [.rdi, .rsp] (fun p s t hs ht r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm) (by taint_decide)

end VG.Proof.MillerRabin.X86_64
