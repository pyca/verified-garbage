module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.Random

import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Dsa.X86_64.Random
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomCopyInit
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Copying a masked draw leaks addresses and width, not random bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

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
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧
  word s.mem p.B Random.oRand = p.R ∧
  word s.mem p.B Random.oUsed = BitVec.ofNat 64 p.used ∧
  word s.mem p.B Random.oQLen = BitVec.ofNat 64 p.qLen ∧
  word s.mem p.B Random.oWidth = BitVec.ofNat 64 p.width ∧
  0 < p.width ∧ p.width < 2 ^ 64 ∧
  InRegions (s.rd ++ s.wr) p.src 1 ∧ InRegions s.wr p.dst 1

def RandomCopyMid (p : RandomCopyPublic) (s : State) : Prop :=
  s.gpr .rsp = p.B ∧ s.gpr .r10 = p.src ∧ s.gpr .rdx = p.dst ∧
  s.gpr .r11 = BitVec.ofNat 64 p.width

def RandomCopyTail (p : RandomCopyPublic) (s : State) : Prop :=
  s.gpr .r10 = p.src + 1 ∧ s.gpr .rdx = p.dst + 1 ∧
  s.gpr .r11 = BitVec.ofNat 64 (p.width - 1) ∧ s.zf = some (decide (p.width = 1))

private theorem header_ok {p : RandomCopyPublic} {s : State} (h : RandomCopyPre p s) :
    WP isa (.block Random.copyHeader) s (RandomCopyMid p) := by
  obtain ⟨hs, hsp, hr, hu, hl, hn, _⟩ := h
  refine WP.mono (WP.keep [.r10, .r11, .rdx] (Q := fun t =>
    t.gpr .r10 = p.src ∧ t.gpr .rdx = p.dst ∧ t.gpr .r11 = BitVec.ofNat 64 p.width) ?_ rfl)
    fun _ ⟨ht, hk⟩ => ⟨(hk.gpr (by decide)).trans hsp, ht⟩
  unfold Random.copyHeader Random.address RandomCopyPublic.src RandomCopyPublic.dst
  xrun [List.append_assoc, List.cons_append, List.nil_append, random_ea_sp, hsp,
    hs.ld (d := Random.oRand) (by decide), hs.ld (d := Random.oUsed) (by decide),
    hs.ld (d := Random.oWidth) (by decide), hs.ld (d := Random.oQLen) (by decide), hr, hu, hl, hn]
  rfl

private theorem init_tail {p : RandomCopyPublic} {s : State} (h : RandomCopyPre p s) :
    WP isa (.block Random.copyInit) s (RandomCopyTail p) := by
  obtain ⟨hs, hsp, hr, hu, hl, hn, hp, hb, hread, hwrite⟩ := h
  exact WP.mono (random_copyInit_ok hs hsp hr hu hn hl rfl rfl rfl hp hb hread hwrite)
    fun _ ⟨h10, hd, h11, hz, _, _⟩ => ⟨h10, hd, h11, hz⟩

theorem random_copy_ct : RelCT isa (Two RandomCopyPre) Random.copy (fun _ _ => True) := by
  unfold Random.copy
  refine RelCT.seq (two_post (Ψ := RandomCopyTail) ?_ (fun _ _ h => init_tail h)) ?_
  · unfold Random.copyInit
    apply RelCT.block_append
    refine RelCT.seq (two_piece (Ψ := RandomCopyMid) [.rsp] ?_ (by taint_decide)
      (fun _ _ h => header_ok h)) ?_
    · intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.2.1.trans ht.2.1.symm
    · apply two_taint [.rsp, .r10, .rdx, .r11] ?_ (by taint_decide)
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.1.trans ht.2.2.1.symm
      · exact hs.2.2.2.trans ht.2.2.2.symm
  · unfold Random.copyRest
    refine two_ite (fun p s t hs ht => by simp only [eval, hs.2.2.2, ht.2.2.2]) ?_ ?_
    · apply two_taint [.r10, .rdx, .r11] ?_ (by taint_decide)
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.1.trans ht.1.1.symm
      · exact hs.1.2.1.trans ht.1.2.1.symm
      · exact hs.1.2.2.1.trans ht.1.2.2.1.symm
    · exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

end VG.Proof.Dsa.X86_64
