module
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
public import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignZero
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Impl.Dsa.X86_64.RandomSign
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignZero
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.Attr.Core
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Output clearing and publication reveal only the public status and addresses. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

structure RandomFinishPublic where
  B : Addr
  out : Addr
  len : Nat
  usedPtr : Addr
  status : BitVec 64

structure RandomFinishPre (p : RandomFinishPublic) (s : State) : Prop where
  scr : Scr s p.B Random.frameBytes
  sp : s.gpr .rsp = p.B
  out : word s.mem p.B Random.oOut = p.out
  len : word s.mem p.B Random.oOutLen = BitVec.ofNat 64 p.len
  usedPtr : word s.mem p.B Random.oUsedPtr = p.usedPtr
  status : word s.mem p.B Random.oStatus = p.status
  positive : 0 < p.len
  bound : p.len < 2 ^ 64
  writes : ∀ j < p.len, InRegions s.wr (p.out + BitVec.ofNat 64 j) 1
  disjoint : ∀ d, d + 8 ≤ Random.frameBytes → Mem.Sep (off p.B d) 8 p.out p.len

def RandomFinishTailPre (p : RandomFinishPublic) (s : State) : Prop :=
  Scr s p.B Random.frameBytes ∧ s.gpr .rsp = p.B ∧ word s.mem p.B Random.oUsedPtr = p.usedPtr

private theorem zero_ct : RelCT isa (Two RandomFinishPre) RandomSign.zeroOut (fun _ _ => True) := by
  unfold RandomSign.zeroOut
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .r10 = p.out ∧ s.gpr .r11 = BitVec.ofNat 64 p.len)
    [.rsp] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.sp.trans ht.sp.symm
  · intro p s h
    xrun [random_ea_sp, h.sp, h.scr.ld (d := Random.oOut) (by decide),
      h.scr.ld (d := Random.oOutLen) (by decide), h.out, h.len]
  · apply two_taint [.r10, .r11] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact hs.2.trans ht.2.symm

private theorem zero_tail {p : RandomFinishPublic} {s : State} (h : RandomFinishPre p s) :
    WP isa RandomSign.zeroOut s (RandomFinishTailPre p) := by
  refine WP.mono (random_zeroOut_ok h.scr h.sp h.out h.len h.positive h.bound h.writes)
    fun t ⟨_, hf, hk⟩ => ?_
  exact ⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.sp,
    (random_zero_preserves_word hf (h.disjoint _ (by decide)) h.bound).trans h.usedPtr⟩

private theorem header_ok {p : RandomFinishPublic} {s : State} (h : RandomFinishPre p s) :
    WP isa (.block [.mov .rax (.mem (Random.sp Random.oStatus)), .alu .cmp .rax (.imm 1)]) s fun t =>
      RandomFinishPre p t ∧ t.zf = some (p.status == 1) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (p.status == 1))
    (by xrun [random_ea_sp, h.sp, h.scr.ld (d := Random.oStatus) (by decide), h.status]
        exact sub_beq_zero _ _) rfl) fun t ⟨⟨hm, hz⟩, hk⟩ => ?_
  exact ⟨⟨h.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.sp,
    by rw [hm]; exact h.out, by rw [hm]; exact h.len, by rw [hm]; exact h.usedPtr,
    by rw [hm]; exact h.status, h.positive, h.bound, by rw [hk.2.2]; exact h.writes, h.disjoint⟩, hz⟩

private theorem clear_tail {p : RandomFinishPublic} {s : State} (h : RandomFinishTailPre p s) :
    WP isa (.block Random.clearNonce) s (RandomFinishTailPre p) := by
  refine WP.mono (random_clear_ok h.1 h.2.1) fun t ⟨hm, hk⟩ => ?_
  refine ⟨h.1.congr hk.2.2, (hk.gpr (by decide)).trans h.2.1, ?_⟩
  rw [hm, (random_clear_outside _ _).word (by decide) (by decide)]
  exact h.2.2

private theorem tail_ct : RelCT isa (Two RandomFinishTailPre)
    (.block (Random.clearNonce ++ ([.mov .rdx (.mem (Random.sp Random.oUsedPtr)),
      .mov .rax (.mem (Random.sp Random.oUsed)), .store { base := .rdx } .rax,
      .mov .rax (.mem (Random.sp Random.oStatus))] : List Instr))) (fun _ _ => True) := by
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := RandomFinishTailPre) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => clear_tail h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.2.1.trans ht.2.1.symm
  · change RelCT isa (Two RandomFinishTailPre) (.block
      (([.mov .rdx (.mem (Random.sp Random.oUsedPtr)), .mov .rax (.mem (Random.sp Random.oUsed))] : List Instr) ++
      [.store { base := .rdx } .rax, .mov .rax (.mem (Random.sp Random.oStatus))])) _
    apply RelCT.block_append
    refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rsp = p.B ∧ s.gpr .rdx = p.usedPtr)
      [.rsp] ?_ (by taint_decide) ?_) ?_
    · intro p s t hs ht r hr
      rw [List.mem_singleton] at hr
      subst r
      exact hs.2.1.trans ht.2.1.symm
    · intro p s ⟨hs, hsp, hu⟩
      xrun [random_ea_sp, hsp, hs.ld (d := Random.oUsedPtr) (by decide),
        hs.ld (d := Random.oUsed) (by decide), hu]
    · apply two_taint [.rsp, .rdx] ?_ (by taint_decide)
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm

theorem random_finish_ct : RelCT isa (Two RandomFinishPre) RandomSign.finish (fun _ _ => True) := by
  unfold RandomSign.finish
  refine RelCT.seq (two_piece (Ψ := fun p s => RandomFinishPre p s ∧ s.zf = some (p.status == 1))
    [.rsp] ?_ (by taint_decide) (fun _ _ h => header_ok h)) ?_
  · intro p s t hs ht r hr
    rw [List.mem_singleton] at hr
    subst r
    exact hs.sp.trans ht.sp.symm
  · refine RelCT.seq ?_ tail_ct
    refine two_ite (fun p s t hs ht => by simp only [eval, hs.2, ht.2]) ?_ ?_
    · exact (two_post zero_ct (fun _ _ h => zero_tail h)).mono
        (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1.scr, h.1.1.sp, h.1.1.usedPtr⟩) h)

end VG.Proof.Dsa.X86_64
