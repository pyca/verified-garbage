module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.StagesCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.StagesCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Output
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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
