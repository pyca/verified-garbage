module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SquareTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeSquares
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CopyTiming
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Advance a tooth with two fixed copies and a public-count squaring loop. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def SquareBasisReady (q : SquarePublic) (s : State) : Prop :=
 ∃ E,Basis q.p E s ∧ word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 q.n

def SquareCounterReady (q : SquarePublic) (s : State) : Prop :=
 ∃ E,Power q.p E s ∧ word s.mem q.p.B (8*sRows)=BitVec.ofNat 64 q.n

def squareWs (q : SquarePublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

theorem precomputeSquares_ct (M : Mont) :
 RelCT isa (Two SquareBasisReady) (Precompute.squares M.mm) (fun _ _ =>True) := by
 unfold Precompute.squares
 refine RelCT.seq (two_post (Ψ:=SquareCounterReady)
  (two_map squareWs (fun q s h => by obtain ⟨E,basis,_⟩:=h;exact ⟨q.p.mi,basis.good,q.p.room⟩)
   (copy_ct (by decide : 6<8) (by decide : 5<8) (by taint_decide))) ?_) ?_
 · rintro q s ⟨E,basis,rows⟩
   refine WP.mono (basis_to_power basis) ?_
   rintro t ⟨power,_,frame,_⟩
   exact ⟨E,power,(arrays_header frame (by decide)).trans rows⟩
 · refine RelCT.seq (two_piece (Ψ:=fun q s =>SquareReady q 0 s) [.x0] ?_ (by taint_decide) ?_) ?_
   · intro q s t hs ht r hr
     have eq : r= .x0 := by simpa using hr
     subst r
     obtain ⟨E,power,_⟩ := hs
     obtain ⟨F,other,_⟩ := ht
     exact power.good.x0.trans other.good.x0.symm
   · rintro q s ⟨E,power,rows⟩
     refine WP.mono (counterInit_ok power.good q.p.room rows) ?_
     rintro t ⟨good,counter,frame,_⟩
     exact ⟨E,power.after_header good frame (by decide),by simpa using counter⟩
   · refine RelCT.seq (two_post (Ψ:=fun q s =>GoodW (squareWs q) s) (squareLoop_ct M) ?_)
      (two_map squareWs (fun _ _ h =>h) (copy_ct (by decide : 5<8) (by decide : 6<8) (by taint_decide)))
     rintro q s ⟨E,power,counter⟩
     refine WP.mono (precomputeSquareLoop_ok M power (by simpa using counter) q.positive q.fit) ?_
     rintro t ⟨power,_,_,_⟩
     exact ⟨q.p.mi,power.good,q.p.room⟩

end VG.Proof.Ffdh.AArch64.Cached
