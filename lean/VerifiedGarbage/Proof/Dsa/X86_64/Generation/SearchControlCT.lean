module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchControl

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchStatus
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchAdvance
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Exp
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SearchAdvance
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Public controller counters and status determine every p-search branch -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

structure SearchControlPublic where
  B : Addr
  counter : Nat
  stride : Nat
  status : Nat
  statusBound : status ≤ 3

def SearchControlBefore (p : SearchControlPublic) (s : State) : Prop :=
  SearchControl p.B p.counter p.stride s ∧ word s.mem p.B 16 = BitVec.ofNat 64 p.status

def SearchControlCompared (p : SearchControlPublic) (s : State) : Prop :=
  SearchControlBefore p s ∧ s.zf = some (decide (p.status = 3))

theorem searchControl_compare {p : SearchControlPublic} {s : State} (h : SearchControlBefore p s) :
    WP isa (.block pSearchStatusCmp) s (SearchControlCompared p) := by
  exact WP.mono (searchStatusCmp_ok h.1 p.statusBound h.2) fun _ ⟨hz, hm, hk⟩ =>
    ⟨⟨h.1.congr hm hk, hm ▸ h.2⟩, hz⟩

theorem searchStatusCmp_ct : RelCT isa (Two SearchControlBefore) (.block pSearchStatusCmp)
    (Two SearchControlCompared) := by
  refine two_post (two_taint [.rdi] ?_ (by taint_decide)) (fun _ _ h => searchControl_compare h)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr; subst r
  exact hs.1.rdi.trans ht.1.rdi.symm

def SearchAdvanceBefore (limit stride : Nat) (p : SearchControlPublic) (s : State) : Prop :=
  SearchControlBefore p s ∧ p.counter < limit ∧ p.stride = stride

def SearchAdvanceReady (limit stride : Nat) (p : SearchControlPublic) (s : State) : Prop :=
  SearchControl p.B (p.counter + 1) stride s ∧ s.cf = some (decide (p.counter + 1 < limit))

theorem searchAdvanceHead_ct (limit stride : Nat) (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (pSearchAdvanceHead limit stride)) hc).isSome = true) :
    RelCT isa (Two (SearchAdvanceBefore limit stride)) (.block (pSearchAdvanceHead limit stride))
      (Two (SearchAdvanceReady limit stride)) := by
  refine two_post (two_taint [.rdi] ?_ ht) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.1.1.rdi.trans ht.1.1.rdi.symm
  · intro p s h
    have ctrl : SearchControl p.B p.counter stride s := by rw [← h.2.2]; exact h.1.1
    exact WP.mono (searchAdvanceHead_ok ctrl h.2.1 hl hs) fun _ ⟨hc, hf, _, _⟩ => ⟨hc, hf⟩

theorem searchAdvance_ct (limit stride : Nat) (hl : limit ≤ 12288) (hs : stride ≤ 12)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi]) (.block (pSearchAdvanceHead limit stride)) hc).isSome = true) :
    RelCT isa (Two (SearchAdvanceBefore limit stride)) (pSearchAdvance limit stride) (fun _ _ => True) := by
  refine RelCT.seq (searchAdvanceHead_ct limit stride hl hs ht)
    (two_ite (fun _ _ _ hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_)
  all_goals
    exact two_taint [.rdi] (by
      intro p s t hs ht r hr
      simp only [List.mem_singleton] at hr; subst r
      exact hs.1.1.rdi.trans ht.1.1.rdi.symm) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation
