module

public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
public import VerifiedGarbage.Proof.Dsa.X86_64.OddCheck
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.X86_64.LastByte
meta import VerifiedGarbage.Proof.Dsa.Layout
meta import VerifiedGarbage.Proof.Dsa.X86_64.LastByte
import Mathlib.Tactic.Set
meta import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
meta import VerifiedGarbage.Proof.Dsa.X86_64.Operands
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.DomainWidths
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShape
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Parity
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTR2
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTRedc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.Digest
meta import VerifiedGarbage.Proof.Dsa.DomainWidths
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
meta import VerifiedGarbage.Proof.Dsa.X86_64.DomainShape
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Masks
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parity
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTail
meta import VerifiedGarbage.Proof.Dsa.X86_64.TopMask
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MdStream.Spec
meta import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.RsaPss.Params
meta import VerifiedGarbage.Proof.Sha256.Stream

/-! # Timing of the final-byte reads in public domain checks -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem lastByte_ct (fp fl : Field) (r : Reg) (pointer : ShapePublic → Addr) (bytes : ShapePublic → List Byte)
    (hptr : ∀ p s, ShapeContext p s → word s.mem p.base fp.offset = pointer p)
    (hlen : ∀ p s, ShapeContext p s → word s.mem p.base fl.offset = BitVec.ofNat 64 (bytes p).length)
    {h₁ h₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi])
      (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl))]) h₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rsi, .rcx])
      (.block [.movzx8 r { base := .rsi, index := some .rcx, disp := -1 }]) h₂).isSome = true) :
    RelCT isa (Two ShapeContext) (.block [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl)),
      .movzx8 r { base := .rsi, index := some .rcx, disp := -1 }]) (fun _ _ => True) := by
  apply RelCT.block_append (M := isa) (l₁ := [.mov .rsi (.mem (Core.field fp)), .mov .rcx (.mem (Core.field fl))])
    (l₂ := [.movzx8 r { base := .rsi, index := some .rcx, disp := -1 }])
  refine RelCT.seq (two_piece (Ψ := fun p s => s.gpr .rsi = pointer p ∧
    s.gpr .rcx = BitVec.ofNat 64 (bytes p).length) [.rdi]
    (pins_of (fun p _ => p.base) (by
      intro p s h r hr; simp only [List.mem_singleton] at hr; subst r; exact h.rdi)) ht₁ ?_) ?_
  · intro p s h
    xrun [State.ea, Core.field, h.rdi, fieldAddress, hptr p s h, hlen p s h,
      h.scr.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fp).2 p.extentBound),
      h.scr.ld (Nat.le_trans (VG.Proof.Dsa.field_bounds fl).2 p.extentBound)]
  · exact two_taint [.rsi, .rcx] (pins_of (fun p r => if r = .rsi then pointer p else BitVec.ofNat 64 (bytes p).length) (by
      intro p s h r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1
      · exact h.2)) ht₂

theorem oddCheck_ct : RelCT isa (Two ShapeContext) (.block oddCheck) (fun _ _ => True) := by
  have hp := lastByte_ct .p .pLen .rax ShapePublic.pPointer ShapePublic.pBytes
    (fun _ _ h => h.pPointer) (fun _ _ h => h.pLength) (by taint_decide) (by taint_decide)
  have hq := lastByte_ct .q .qLen .rdx ShapePublic.qPointer ShapePublic.qBytes
    (fun _ _ h => h.qPointer) (fun _ _ h => h.qLength) (by taint_decide) (by taint_decide)
  have hp' : RelCT isa (Two ShapeContext)
      (.block [.mov .rsi (.mem (Core.field .p)), .mov .rcx (.mem (Core.field .pLen)),
        .movzx8 .rax { base := .rsi, index := some .rcx, disp := -1 }]) (Two ShapeContext) := by
    refine two_post hp ?_
    intro p s h
    have hi : p.pBytes.length - 1 < p.pBytes.length := by have := p.pPositive; omega
    exact WP.mono (lastByte_ok h.scr h.rdi p.extentBound .p .pLen .rax h.pPointer h.pLength
      p.pPositive p.pBound (h.pSource.rd _ hi) (h.pSource.val _ hi))
      fun t ⟨_, hm, hk⟩ => h.sameMem hm hk (by decide)
  have hq' : RelCT isa (Two ShapeContext)
      (.block [.mov .rsi (.mem (Core.field .q)), .mov .rcx (.mem (Core.field .qLen)),
        .movzx8 .rdx { base := .rsi, index := some .rcx, disp := -1 }]) (Two BasePublic) := by
    refine two_post (Ψ := fun p s => BasePublic p.base s) hq ?_ |>.mono
      (fun _ _ h => h) (fun _ _ h => ?_)
    · intro p s h
      have hi : p.qBytes.length - 1 < p.qBytes.length := by have := p.qPositive; omega
      exact WP.mono (lastByte_ok h.scr h.rdi p.extentBound .q .qLen .rdx h.qPointer h.qLength
        p.qPositive p.qBound (h.qSource.rd _ hi) (h.qSource.val _ hi))
        fun t ⟨_, _, hk⟩ => (hk.gpr (by decide)).trans h.rdi
    · obtain ⟨p, h1, h2⟩ := h
      exact ⟨p.base, h1, h2⟩
  unfold oddCheck
  rw [List.append_assoc, List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq hp' ?_
  apply RelCT.block_append
  exact RelCT.seq hq' (two_taint [.rdi] pins_base (by taint_decide))

end VG.Proof.Dsa.X86_64
