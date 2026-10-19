module

public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTLoop
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.Omega
meta import Mathlib.Tactic.Set
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PdCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.PdCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCounter
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.FoldedStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def Pre (p : PublicData) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧ X < p.N ∧
    X % p.N = x * 2^(64*p.L.w) % p.N

def Ready (p : PublicData) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ Facts p ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w < p.N ∧
    wv s.mem p.L.B (slot p.L.w aY) p.L.w % p.N = x * 2^(64*p.L.w) % p.N

theorem start_fw (p : PublicData) (s : State) (h : Pre p s) :
    WP isa Precomputed.start s (Ready p) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  exact WP.mono (start_ok hc hf.1 (by have := hf.2.1; omega) hf.2.2.1)
    fun t ⟨ct,yt,_,_,_⟩ => ⟨X,x,ct,hf,by rw [yt]; exact hlt,by rw [yt]; exact hx⟩

theorem init_fw (p : PublicData) (s : State) (h : Ready p s) :
    WP isa (.block [.mov32 .rax (.imm 16), .store (hdr sI) .rax]) s (Inv p 0) := by
  obtain ⟨X,x,hc,hf,hlt,hx⟩ := h
  have hb : p.L.B.toNat + slot p.L.w 8 ≤ 2^64 := by
    have := hc.good.scr.nowrap; have := hf.1; omega
  refine WP.mono (init_ok hc.good hf.1) fun t ⟨mt,kt⟩ => ?_
  have ct := ExpCtx.store hc hf.1 (i := sI) (by decide) (by decide) mt kt.2.2
    ((kt.gpr (by decide)).trans hc.good.rdi)
  have yt : wv t.mem p.L.B (slot p.L.w aY) p.L.w = wv s.mem p.L.B (slot p.L.w aY) p.L.w := by
    rw [mt,hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hb]
  exact ⟨t,X,x,⟨ct,by rw [yt]; exact hlt,by simpa only [yt,Nat.pow_zero,Nat.pow_one] using hx,
    by rw [mt,word_writeW_self]; rfl,Frm.refl _ _ _,Keep.refl _ _⟩,hf⟩

/-- `Y := X` and sixteen squares leak the same in runs with the same public
data. -/
theorem exp65536_ct (M : Mont) :
    RelCT isa (Two Pre) (Folded.exp65536 M.mm) (fun _ _ => True) := by
  unfold Folded.exp65536
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : PublicData => p.L)
    (fun _ _ ⟨_,_,hc,hf,_⟩ => ⟨hc.good,hf.1⟩) VG.Proof.Bignum.X86_64.start_ct) start_fw) ?_
  refine RelCT.seq (two_piece [.rdi]
    (fun p s t ⟨_,_,hs,_⟩ ⟨_,_,ht,_⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst r; rw [hs.good.rdi,ht.good.rdi])
    (by taint_decide) init_fw) ?_
  exact (two_map id (fun _ _ h => ⟨by decide,h⟩) (squares_ct M)).mono (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.Bignum.X86_64.FoldedPublic
