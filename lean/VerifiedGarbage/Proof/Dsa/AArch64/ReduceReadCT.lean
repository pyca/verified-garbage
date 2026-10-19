module
public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import Mathlib.Tactic.Attr.Core
meta import Aesop.BuiltinRules
meta import Mathlib.Tactic.ToAdditive
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Constant-time reads of secret reduction input bytes -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure ReduceReadPublic where
  layout : Lay
  pointer : Addr

def ReduceReadPre (p : ReduceReadPublic) (s : State) : Prop :=
  GoodL p.layout s ∧ word s.mem p.layout.B (8 * Crt.sSrc) = p.pointer ∧
  InRegions (s.rd ++ s.wr) p.pointer 1

def ReduceReadHead (p : ReduceReadPublic) (s : State) : Prop :=
  GoodL p.layout s ∧ s.gpr .x1 = p.pointer ∧ InRegions (s.rd ++ s.wr) p.pointer 1

def ReduceReadStore (p : ReduceReadPublic) (s : State) : Prop :=
  s.gpr .x0 = p.layout.B ∧ s.gpr .x1 = p.pointer ∧
  s.gpr .x8 = off p.layout.B (slot p.layout.w aX)

theorem reduceRead_ct : RelCT isa (Two ReduceReadPre) (.block Arithmetic.reduceRead)
    (fun _ _ => True) := by
  change RelCT isa (Two ReduceReadPre) (.block (
    ([ldh .x1 Crt.sSrc] : List Instr) ++
    ([.ldrb .x3 .x1 0, ldh .x8 (sArr aX)] : List Instr) ++
    [st .x3 .x8, .addImm .x .x1 .x1 1, sth .x1 Crt.sSrc])) _
  rw [List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := ReduceReadHead) [.x0]
    (fun p s t hs ht => pins_good p.layout s t hs.1 ht.1) (by taint_decide) ?_) ?_
  · intro p s ⟨hg, hp, hr⟩
    refine WP.mono (WP.keep [.x1] (Q := fun t => t.gpr .x1 = p.pointer ∧ t.mem = s.mem)
      ?_ rfl rfl rfl) fun t ⟨⟨hsi, hm⟩, hk⟩ =>
      ⟨⟨⟨hg.1.scr.congr hk.wr, (hk.gpr .x0 (by decide)).trans hg.1.x0, hm ▸ hg.1.hdr⟩, hg.2⟩,
        hsi, by simpa only [hk.rd, hk.wr] using hr⟩
    brun [hg.1.x0, hdr_enc (show Crt.sSrc < 32 by decide), hp,
      hg.1.scr.ld (show 8 * Crt.sSrc + 8 ≤ p.layout.Z by
        have := hdr_lt_slot p.layout.w 8 (show Crt.sSrc < 32 by decide); have := hg.2; omega)]
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := ReduceReadStore) [.x0, .x1]
    (pins_of (fun p r => if r = .x0 then p.layout.B else p.pointer) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.x0
      · exact h.2.1)) (by taint_decide) ?_) ?_
  · intro p s ⟨hg, hsi, hr⟩
    refine WP.mono (WP.keep [.x3, .x8] (Q := fun t =>
      t.gpr .x8 = off p.layout.B (slot p.layout.w aX)) ?_ rfl rfl rfl)
      fun t ⟨hbx, hk⟩ => ⟨(hk.gpr .x0 (by decide)).trans hg.1.x0,
        (hk.gpr .x1 (by decide)).trans hsi, hbx⟩
    brun [hsi, hr, hg.1.x0, hdr_enc (show sArr aX < 32 by decide),
      hg.1.hdr.harr aX (by decide),
      hg.1.scr.ld (show 8 * sArr aX + 8 ≤ p.layout.Z by
        have := hdr_lt_slot p.layout.w 8 (show sArr aX < 32 by decide); have := hg.2; omega)]
  exact two_taint [.x0, .x1, .x8]
    (pins_of (fun p r => if r = .x0 then p.layout.B else if r = .x1 then p.pointer else
      off p.layout.B (slot p.layout.w aX)) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.AArch64
