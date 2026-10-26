module
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Impl.Dsa.AArch64.Random

import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyInit
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Impl.Dsa.AArch64.Random
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomCopyInit
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Copying a masked draw leaks addresses and width, not random bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure RandomCopyPublic where
  B : Addr
  R : Addr
  used : Nat
  qLen : Nat
  width : Nat

def RandomCopyPublic.src (p : RandomCopyPublic) : Addr := p.R + BitVec.ofNat 64 p.used
def RandomCopyPublic.dst (p : RandomCopyPublic) : Addr :=
  off p.B Random.oNonce + BitVec.ofNat 64 p.qLen - BitVec.ofNat 64 p.width

def RandomCopyPre (p : RandomCopyPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.sp = p.B ∧
  word s.mem p.B Random.oRand = p.R ∧
  word s.mem p.B Random.oUsed = BitVec.ofNat 64 p.used ∧
  word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.qLen ∧
  word s.mem p.B Random.oWidth = BitVec.ofNat 64 p.width ∧
  0 < p.width ∧ p.width < 2 ^ 64 ∧
  InRegions (s.rd ++ s.wr) p.src 1 ∧ InRegions s.wr p.dst 1

def RandomCopyMid (p : RandomCopyPublic) (s : State) : Prop :=
  s.sp = p.B ∧ s.gpr .x12 = p.src ∧ s.gpr .x2 = p.dst ∧
  s.gpr .x9 = BitVec.ofNat 64 p.width

def RandomCopyTail (p : RandomCopyPublic) (s : State) : Prop :=
  s.gpr .x12 = p.src + 1#64 ∧ s.gpr .x2 = p.dst + 1#64 ∧
  s.gpr .x9 = BitVec.ofNat 64 (p.width - 1)

private theorem header_ok {p : RandomCopyPublic} {s : State} (h : RandomCopyPre p s) :
    WP isa (.block Random.copyHeader) s (RandomCopyMid p) := by
  obtain ⟨hs, hsp, hr, hu, hl, hn, _⟩ := h
  refine WP.mono (WP.keep [.x4, .x12, .x9, .x2] (Q := fun t =>
    t.gpr .x12 = p.src ∧ t.gpr .x2 = p.dst ∧ t.gpr .x9 = BitVec.ofNat 64 p.width) ?_ rfl rfl rfl)
    fun _ ⟨ht, hk⟩ => ⟨hk.sp.trans hsp, ht⟩
  unfold Random.copyHeader RandomCopyPublic.src RandomCopyPublic.dst
  brun [exec_addSp (show Random.oNonce < 4096 by decide),
    exec_ldrSp (show Random.oRand % 8 = 0 ∧ Random.oRand < 32768 by decide),
    exec_ldrSp (show Random.oUsed % 8 = 0 ∧ Random.oUsed < 32768 by decide),
    exec_ldrSp (show Random.oWidth % 8 = 0 ∧ Random.oWidth < 32768 by decide),
    exec_ldrSp (show Random.oQLen % 8 = 0 ∧ Random.oQLen < 32768 by decide), hsp,
    hs.ld (d := Random.oRand) (by decide), hs.ld (d := Random.oUsed) (by decide),
    hs.ld (d := Random.oWidth) (by decide), hs.ld (d := Random.oQLen) (by decide), hr, hu, hl, hn]

private theorem init_tail {p : RandomCopyPublic} {s : State} (h : RandomCopyPre p s) :
    WP isa (.block Random.copyInit) s (RandomCopyTail p) := by
  obtain ⟨hs, hsp, hr, hu, hl, hn, hp, hb, hread, hwrite⟩ := h
  exact WP.mono (random_copyInit_ok hs hsp hr hu hn hl rfl rfl rfl hp hb hread hwrite)
    fun _ ⟨h10, hd, h11, _, _⟩ => ⟨h10, hd, h11⟩

theorem random_copy_ct : RelCT isa (Two RandomCopyPre) Random.copy (fun _ _ => True) := by
  unfold Random.copy
  refine RelCT.seq (two_post (Ψ := RandomCopyTail) ?_ (fun _ _ h => init_tail h)) ?_
  · unfold Random.copyInit
    apply RelCT.block_append
    refine RelCT.seq (two_piece (Ψ := RandomCopyMid) [] ?_ (by taint_decide)
      (fun _ _ h => header_ok h)) ?_
    · intro _ _ _ _ _ _ hr; cases hr
    · apply two_taint [.x12, .x2, .x9] ?_ (by taint_decide)
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm
  · unfold Random.copyRest
    refine two_ite (fun p s t hs ht => by simp only [eval, State.read, hs.2.2, ht.2.2]) ?_ ?_
    · apply two_taint [.x12, .x2, .x9] ?_ (by taint_decide)
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.1.trans ht.1.1.symm
      · exact hs.1.2.1.trans ht.1.2.1.symm
      · exact hs.1.2.2.trans ht.1.2.2.symm
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.AArch64
