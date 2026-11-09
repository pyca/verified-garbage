module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.ScalarCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.TailCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MaskCT

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.SetupCT
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

def CB (p : GkP) (s : State) : Prop :=
  WorkIn p s ∧ s.zf = some (!decide (p.sv = true)) ∧ s.gpr .rax = bit (p.sv = true)

theorem branch_eval {p : GkP} {s : State} (h : CB p s) :
    isa.eval .e s = some (!decide (p.sv = true)) := by simp [eval, h.2.1]

theorem reject_mask (p : GkP) (s : State) (h : CB p s ∧ isa.eval .e s = some true) :
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

theorem reject_ct : RelCT isa (Two fun p s => CB p s ∧ isa.eval .e s = some true)
    (seqs [.block [leave], VG.Impl.Ffdh.X86_64.Domain.GenerateKey.maskX, ret 2]) fun _ _ => True := by
  simp only [seqs]
  refine RelCT.seq (R := Two MaskPre)
    (two_piece [.rdi] (pins_rdiB (fun p => off p.B (inner p.w)) fun _ _ h => by
      obtain ⟨_, _, _, hd, _⟩ := h.1.1; exact hd) (by taint_decide) reject_mask) ?_
  exact RelCT.seq mask_ct (two_taint [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))

end VG.Proof.Ffdh.X86_64.GenerateKey
