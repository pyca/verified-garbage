module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ScalarCT

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ScalarCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.SetupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Outputs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH on x86-64: only the permitted scalar rejection class controls a branch -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (loadArr leave)

private def CS (p : GkP) (s : State) : Prop := WorkIn p s ∧ s.gpr .rax = bit (p.sv = true)
private def CB (p : GkP) (s : State) : Prop :=
  WorkIn p s ∧ s.zf = some (!decide (p.sv = true)) ∧ s.gpr .rax = bit (p.sv = true)

private theorem scalar_stage (p : GkP) (s : State) (h : WorkIn p s) :
    WP isa (seqs VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange) s (CS p) := by
  obtain ⟨rb, mi, hw, hd, hm, hb⟩ := h
  exact WP.mono (CheckPrivate.scalar_ok hw hd (valid_facts hm hw.base.k1).1)
    fun _ ⟨⟨hw', hd', ha⟩, hi, _, k⟩ => ⟨⟨rb, mi, hw', hd', hm, hb.keep hi k⟩, ha⟩

private theorem test_stage (p : GkP) (s : State) (h : CS p s) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s (CB p) := by
  obtain ⟨⟨rb, mi, hw, hd, hm, hb⟩, ha⟩ := h
  refine WP.mono (test_bit_ok ha) fun t ⟨hz, hmem, k⟩ => ?_
  have hf : InScr p.B p.Z s.mem t.mem := by intro a _; rw [hmem]
  exact ⟨⟨rb, mi, hw.keep hmem k, (k.gpr (by decide)).trans hd, hm, hb.keep hf k⟩, hz,
    (k.gpr (by decide)).trans ha⟩

private theorem branch_eval {p : GkP} {s : State} (h : CB p s) :
    isa.eval .e s = some (!decide (p.sv = true)) := by simp [eval, h.2.1]

private theorem reject_mask (p : GkP) (s : State) (h : CB p s ∧ isa.eval .e s = some true) :
    WP isa (.block [leave]) s (MaskPre p) := by
  obtain ⟨⟨⟨rb, mi, hw, hd, _, hb⟩, _, ha⟩, _⟩ := h
  have hZ : 128 * p.k + 256 ≤ p.Z := hw.base.hZ
  have hk : p.k ≤ 1024 := hw.base.k2
  refine WP.mono (leave_ok (hw.mem.ctx hd)) fun t ⟨hdt, hm, k⟩ => ?_
  refine ⟨hw.base.scr.congr k.2.2, hdt, by omega, by omega, hb.ld, ?_, ?_, ?_,
    ⟨fun i hi => by rw [k.2.2]; exact hb.ox.wr i hi, hb.ox.sep⟩, decide (p.sv = true), ?_⟩
  · rw [hm]
    exact hw.base.hdr (sX, off p.xp p.ld) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  · rw [hm]
    exact hw.base.hdr (sXl, BitVec.ofNat 64 p.n) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  · rw [hm]
    exact hw.base.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CheckPrivate.KpP.headers, GkP.kp])
  · exact ((k.gpr (by decide)).trans ha).trans (bit_eq_bool (p.sv = true))

private theorem reject_ct : RelCT isa (Two fun p s => CB p s ∧ isa.eval .e s = some true)
    (seqs [.block [leave], VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, ret 2]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (R := Two MaskPre)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h.1.1; exact hd) (by taint_decide) reject_mask) ?_
  exact RelCT.seq mask_ct (two_taint [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))

theorem core_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two Sliced)
      (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core M.mm E.code (.seq (.block r2Head) R.code)))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.core
  simp only [List.append_assoc]
  refine RelCT.seqs_append (a := ([.block VG.Impl.Rsa.X86_64.head] ++ pSetup ++ loadArr aXm sX sXl))
    (b := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange ++ [.block [.alu .test .rax (.reg .rax)],
      .ite .e (seqs [.block [leave], VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, ret 2])
        (seqs (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.tail M.mm E.code (.seq (.block r2Head) R.code)))])
    (by simp [pSetup]) (by simp) (RelCT.seq setup_load_ct ?_)
  refine RelCT.seqs_append (a := VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange)
    (by simp [VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.scalarRange, isNonzero, geArr, cmpArr]) (by simp)
    (RelCT.seq (R := Two CS)
      (two_post (two_map GkP.kp (fun _ _ h => by
        obtain ⟨rb, mi, hw, hd, hm, _⟩ := h; exact ⟨_, mi, hw, hd, hm⟩)
        CheckPrivate.scalar_ct) scalar_stage) ?_)
  simp only [seqs]
  refine RelCT.seq (R := Two CB)
    (two_piece [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide) test_stage) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [branch_eval h₁, branch_eval h₂]) reject_ct
    (two_map id (fun _ _ h => h.1.1) (tail_ct M E R hE))

end VG.Proof.Ffdh.X86_64.GenerateKey
