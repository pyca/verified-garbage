module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawCTData
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestore
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.DrawCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.WitnessCut
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutRestore
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH parameter generation on x86-64: timing of masking and workspace restoration -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Impl.Bignum.X86_64 (hdr)
open VG.Impl.Rsa.X86_64.Crt (sLink ws)
open VG.Proof.MlKem.X86_64

structure CutAfter (d : DrawPublic) (s : State) : Prop where
  rbp : s.gpr .rbp = d.p.I
  link : word s.mem d.p.I (8 * sLink) = d.p.O
  wr : s.wr = d.wr
  kw : InnerKW d.p.O d.wr

private theorem cutBefore_pins : Pins CutBefore [.rdi, .rsi, .rcx, .rdx] := by
  intro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h₁.rdi.trans h₂.rdi.symm
  · exact h₁.rsi.trans h₂.rsi.symm
  · exact h₁.rcx.trans h₂.rcx.symm
  · exact h₁.rdx.trans h₂.rdx.symm

private theorem cut_after (d : DrawPublic) (s : State) (h : CutBefore d s) :
    WP isa witnessCut s (CutAfter d) := by
  have hlen : (d.bs.take d.p.len).length = d.p.len := by rw [List.length_take, Nat.min_eq_left h.available]
  refine WP.mono (witnessCut_ok (by omega_using [d.p.bits1]) d.p.bits2
    (show (d.bs.take d.p.len).length = (d.p.bits + 7) / 8 from hlen) h.rsi h.rdi
    (by rw [hlen]; exact h.rcx) h.rdx h.src.rd (fun i hi => h.out.wr i (by omega_using [hlen, hi]))
    (fun i hi => by
      rw [h.src.val i hi]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some])
    (fun i hi j hj he => h.apart j (by omega_using [hlen, hj]) i hi he.symm))
    fun t ⟨_, _, hf, k⟩ => ?_
  have hfi : OutOk s d.p.I d.p.IZ d.p.op d.p.len :=
    output_inner h.out (Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap)
  have hframe : ∀ a, (∀ i < d.p.len, a ≠ off d.p.op i) → t.mem a = s.mem a := by simpa only [hlen] using hf
  have hw := words_outside_bytes (show d.p.IZ ≤ 2 ^ 64 by
    have hz64 := Nat.le_trans (Nat.le_add_left _ _) h.scr.nowrap
    unfold WitnessParams.IZ; omega) hframe hfi.sep
  exact ⟨(k.gpr (by decide)).trans h.rbp,
    (hw _ d.p.space_bounds.2.1).trans h.link, k.2.2.trans h.wr, h.kw⟩

private theorem cutAfter_restore (d : DrawPublic) (s : State) (h : CutAfter d s) :
    WP isa (.block [.mov .rdi (.reg .rbp)]) s (LinkHeader ⟨d.p.O, d.wr⟩) := by
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = d.p.I ∧ t.mem = s.mem)
    (by xrun [h.rbp]) rfl) fun t ⟨⟨hd, hm⟩, k⟩ => ?_
  refine ⟨h.kw, hd, k.2.2.trans h.wr, ?_⟩
  intro e he
  simp only [List.mem_singleton] at he; subst e
  rw [hm]; exact h.link

private theorem drawLoad_ct : RelCT isa (Two CutAfter) (.block drawLoad) fun _ _ => True := by
  unfold drawLoad
  change RelCT isa (Two CutAfter) (.block ([.mov .rdi (.reg .rbp)] ++ _)) _
  refine RelCT.block_append (RelCT.seq
    (two_piece [.rbp] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h₁.rbp.trans h₂.rbp.symm)
      (by taint_decide) cutAfter_restore) ?_)
  exact two_map (fun d : DrawPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h) drawLoadTail_ct

theorem cutRestore_ct : RelCT isa (Two CutBefore) cutRestore fun _ _ => True := by
  unfold cutRestore
  exact RelCT.seq (two_post (witnessCut_ct cutBefore_pins) cut_after) drawLoad_ct

theorem cutRestore_inner (d : DrawPublic) (s : State) (h : CutBefore d s) :
    WP isa cutRestore s (InnerNumber d.inner) := by
  obtain ⟨s₀, hr, hwr, hw⟩ := h.retained
  refine WP.mono (cutRestore_ok hr hwr hw h.scr h.link h.outPtr h.len h.rdi h.rsi h.rbp h.rcx h.rdx
    h.src h.out h.apart (by rw [List.length_take, Nat.min_eq_left h.available]))
    fun t ⟨ht, hsi, hcx, _, _, _, _, k⟩ => ?_
  exact ⟨⟨h.kw, VG.Proof.RsaKeyGen.X86_64.good_hp ht.good (k.2.2.trans h.wr)⟩, hsi, hcx⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
