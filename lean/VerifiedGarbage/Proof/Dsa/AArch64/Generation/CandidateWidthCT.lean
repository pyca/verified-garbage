module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
meta import VerifiedGarbage.Spec.Dsa
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Algebra.Group.Nat.Defs
meta import Mathlib.Tactic.Push
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToDual
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The candidate-width guard has public addressing and a public decision -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Dsa.AArch64.Generation

structure CandidateWidthPublic where
  B : Addr
  F : Addr
  Z : Nat
  w : Nat
  ptr : Addr
  len : Nat
  value : Nat
  positive : 0 < len
  fits : value < 256 ^ len

structure CandidateWidthBefore (p : CandidateWidthPublic) (s : State) : Prop where
  ws : Ws s p.B p.Z p.w
  stack : s.sp = p.F
  pointer : word s.mem p.B 160 = p.ptr
  bytes : Spec.Rsa.bytesAt s.mem p.ptr p.len = Spec.Dsa.encodeBE p.len p.value
  read : InRegions (s.rd ++ s.wr) p.ptr 1

def CandidateWidthAfter (p : CandidateWidthPublic) (s : State) : Prop :=
  CandidateWidthBefore p s ∧ eval (.zero .x .x3) s = some (decide (p.value < 2 ^ (8 * p.len - 1)))

theorem candidateWidth_ready {p : CandidateWidthPublic} {s : State} (h : CandidateWidthBefore p s) :
    WP isa (.block candidateWidth) s (CandidateWidthAfter p) := by
  refine WP.mono (candidateWidth_ok h.ws h.pointer p.positive p.fits h.bytes h.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  have ws : Ws t p.B p.Z p.w := by
    refine ⟨h.ws.scr.congr hk.wr, (hk.gpr _ (by decide)).trans h.ws.x0,
      hm ▸ h.ws.hw, hm ▸ h.ws.hS, ?_, h.ws.hZ, h.ws.w1, h.ws.w2⟩
    intro j hj; rw [hm]; exact h.ws.harr j hj
  exact ⟨⟨ws, hk.sp.trans h.stack, hm ▸ h.pointer,
    hm ▸ h.bytes, (by rw [hk.rd, hk.wr]; exact h.read)⟩, cf⟩

theorem candidateWidth_ct : RelCT isa (Two CandidateWidthBefore) (.block candidateWidth)
    (Two CandidateWidthAfter) := by
  refine two_post ?_ (fun _ _ h => candidateWidth_ready h)
  apply RelCT.block_append (M := isa) (l₁ := [VG.Impl.Bignum.AArch64.ldh .x1 20])
    (l₂ := [.ldrb .x3 .x1 0, .lsr .x .x3 .x3 7])
  refine RelCT.seq (two_post (Ψ := fun (p : CandidateWidthPublic) s => s.gpr .x1 = p.ptr)
    (two_taint [.x0] ?_ (by taint_decide)) ?_) (two_taint [.x1] ?_ (by taint_decide))
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.ws.x0.trans ht.ws.x0.symm
  · intro p s h
    have ld := h.ws.scr.ld (d := 160) (show 160 + 8 ≤ p.Z from Nat.le_trans (by decide) h.ws.h256)
    brun [h.ws.x0, hdr_enc (by decide : 20 < 32), ld, h.pointer]
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.trans ht.symm

end VG.Proof.Dsa.AArch64.Generation
