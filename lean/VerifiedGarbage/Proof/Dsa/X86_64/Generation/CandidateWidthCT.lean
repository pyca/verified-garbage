module
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.CandidateWidth
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Rsa.X86_64.Pieces

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateWidth
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
import VerifiedGarbage.Proof.Dsa.Generation.PReduction
import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.Inv
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.BitLengthBounds
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import VerifiedGarbage.Proof.Dsa.Generation.CandidateWidth
meta import VerifiedGarbage.Proof.Dsa.Generation.PReduction
meta import VerifiedGarbage.Proof.Dsa.Generation.QCandidate
meta import VerifiedGarbage.Proof.Ffdh.KeyScalar
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.Inv
meta import VerifiedGarbage.Proof.Rsa.X86_64.Loops

/-! # The candidate-width guard has public addressing and a public decision -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Dsa.X86_64.Generation

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
  stack : s.gpr .rsp = p.F
  pointer : word s.mem p.B 160 = p.ptr
  bytes : Spec.Rsa.bytesAt s.mem p.ptr p.len = Spec.Dsa.encodeBE p.len p.value
  read : InRegions (s.rd ++ s.wr) p.ptr 1

def CandidateWidthAfter (p : CandidateWidthPublic) (s : State) : Prop :=
  CandidateWidthBefore p s ∧ s.cf = some (decide (p.value < 2 ^ (8 * p.len - 1)))

theorem candidateWidth_ready {p : CandidateWidthPublic} {s : State} (h : CandidateWidthBefore p s) :
    WP isa (.block candidateWidth) s (CandidateWidthAfter p) := by
  refine WP.mono (candidateWidth_ok h.ws h.pointer p.positive p.fits h.bytes h.read)
    fun t ⟨cf, hm, hk⟩ => ?_
  have ws : Ws t p.B p.Z p.w := by
    refine ⟨h.ws.scr.congr hk.2.2, (hk.gpr (by decide)).trans h.ws.rdi,
      hm ▸ h.ws.hw, hm ▸ h.ws.hS, ?_, h.ws.hZ, h.ws.w1, h.ws.w2⟩
    intro j hj; rw [hm]; exact h.ws.harr j hj
  exact ⟨⟨ws, (hk.gpr (by decide)).trans h.stack, hm ▸ h.pointer,
    hm ▸ h.bytes, (by rw [hk.2.1, hk.2.2]; exact h.read)⟩, cf⟩

theorem candidateWidth_ct : RelCT isa (Two CandidateWidthBefore) (.block candidateWidth)
    (Two CandidateWidthAfter) := by
  refine two_post ?_ (fun _ _ h => candidateWidth_ready h)
  apply RelCT.block_append (M := isa) (l₁ := [.mov .rsi (.mem (hdr 20))])
    (l₂ := [.movzx8 .rax (at0 .rsi), .alu .cmp .rax (.imm 128)])
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rsi = p.ptr)
    (two_taint [.rdi] ?_ (by taint_decide)) ?_) (two_taint [.rsi] ?_ (by taint_decide))
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.ws.rdi.trans ht.ws.rdi.symm
  · intro p s h
    have ld := h.ws.scr.ld (d := 160) (show 160 + 8 ≤ p.Z from Nat.le_trans (by decide) h.ws.h256)
    xrun [State.ea, hdr, hdrOff, at0, h.ws.rdi, ld, h.pointer]
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.trans ht.symm

end VG.Proof.Dsa.X86_64.Generation
