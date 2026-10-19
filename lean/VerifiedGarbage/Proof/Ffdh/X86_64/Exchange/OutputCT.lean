module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.StagesCT
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
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
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
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
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Entry
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Ffdh.X86_64.R2
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
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

/-! # FFDH exchange on x86-64: encode the secret result in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (sLink leave ws)

private def pre : List Instr :=
  [.mov32 .r15 (.imm 0), .alu .sub .r15 (.reg .rax), .mov .rbx (.mem (hdr (sArr aY))),
    .mov .rax (.mem (hdr sLink))]

private def ptrs : List Instr :=
  [.mov .rsi (.mem (ws .rax VG.Impl.Ffdh.X86_64.Domain.sOut)), .mov .rcx (.mem (ws .rax sK))]

private def fin : List Instr := [.mov .rax (.mem (hdr sF)), leave]

private theorem pre_ok (p : ExP) (s : State) (h : C4 p s) : WP isa (.block pre) s
    fun t => t.gpr .rax = p.B := by
  obtain ⟨xb, ⟨mi, hb, hc⟩, _⟩ := h
  unfold pre
  xrun [State.ea, hdr, hdrOff, hc.rdi, hc.hdr.harr aY (by decide), hc.link,
    hc.good.scr.ld (hdr_lt_slot p.w 8 (show sArr aY < 32 by decide)),
    hc.good.scr.ld (hdr_lt_slot p.w 8 (show sLink < 32 by decide))]

private theorem fin_ct : RelCT isa (Two C4) (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk)
    fun _ _ => True := by
  change RelCT isa (Two C4) (.block (pre ++ ptrs)) _
  refine RelCT.block_append (RelCT.seq
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, ⟨_, _, hc⟩, _⟩ := h; exact hc.rdi) (by taint_decide) pre_ok) ?_)
  exact two_taint [.rax] (pins_of (fun p _ => p.B) fun _ _ h _ hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h) (by taint_decide)

private def StoreP (p : ExP) (s : State) : Prop :=
  s.gpr .rbx = off p.B (inner p.w + slot p.w aY) ∧ s.gpr .rsi = p.op ∧ s.gpr .rcx = BitVec.ofNat 64 p.k ∧
    s.gpr .rdi = off p.B (inner p.w) ∧ WP isa (.seq storeBE (.block fin)) s (fun _ => True)

private theorem c4_store (p : ExP) (s : State) (h : C4 p s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk) s (StoreP p) := by
  obtain ⟨xb, hh⟩ := h
  have hh' := hh
  obtain ⟨⟨mi, hb, hc⟩, _⟩ := hh'
  have hw : WP isa (.seq (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk) (.seq storeBE (.block fin))) s
      (fun _ => True) := WP.mono (output_ok hh) fun _ _ => trivial
  have hr : WP isa (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk) s fun t =>
      t.gpr .rbx = off p.B (inner p.w + slot p.w aY) ∧ t.gpr .rsi = p.op ∧
        t.gpr .rcx = BitVec.ofNat 64 p.k ∧ t.gpr .rdi = off p.B (inner p.w) :=
    WP.mono (finBlk_ok hh) fun t ⟨⟨hbx, hsi, hcx, _⟩, _, k⟩ =>
      ⟨hbx, hsi, hcx, (k.gpr (by decide)).trans hc.rdi⟩
  exact WP.mono (WP.and hr (WP.seq_iff.mp hw))
    fun _ ⟨⟨hbx, hsi, hcx, hd⟩, htail⟩ => ⟨hbx, hsi, hcx, hd, htail⟩

private theorem store_keeps_rdi : ∀ i ∈ instrs storeBE, Taint.clobbers i .rdi = false := by
  have h : (instrs storeBE).all (fun i => !Taint.clobbers i .rdi) = true := by decide +kernel
  intro i hi
  simpa only [Bool.not_eq_true'] using List.all_eq_true.mp h i hi

private def FinalP (p : ExP) (s : State) : Prop := s.gpr .rdi = off p.B (inner p.w) ∧ WP isa (.block fin) s (fun _ => True)

theorem output_ct : RelCT isa (Two C4)
    (seqs [.block VG.Impl.Ffdh.X86_64.Domain.Exchange.finBlk, storeBE,
      .block [.mov .rax (.mem (hdr sF)), leave]]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (R := Two StoreP) (two_post fin_ct c4_store) ?_
  refine RelCT.seq (R := Two FinalP) (two_piece [.rbx, .rsi, .rcx] ?_ (by taint_decide) ?_) ?_
  · exact pins_of (fun p r => if r = .rbx then off p.B (inner p.w + slot p.w aY)
      else if r = .rsi then p.op else BitVec.ofNat 64 p.k) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [reduceCtorEq, ↓reduceIte]
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
  · intro p s h
    exact WP.mono (VG.X86_64.WP.gpr (WP.seq_iff.mp h.2.2.2.2) store_keeps_rdi)
      fun t ⟨hf, hd⟩ => ⟨hd.trans h.2.2.2.1, hf⟩
  exact two_taint [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => h.1) (by taint_decide)

end VG.Proof.Ffdh.X86_64.Exchange
