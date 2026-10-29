module
public import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont

import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Bignum.X86_64.Mont
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import Aesop.BuiltinRules
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Constant-time reads of secret reduction input bytes -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ReduceReadPublic where
  layout : Lay
  pointer : Addr

def ReduceReadPre (p : ReduceReadPublic) (s : State) : Prop :=
  GoodL p.layout s ∧ word s.mem p.layout.B (8 * Crt.sSrc) = p.pointer ∧
  InRegions (s.rd ++ s.wr) p.pointer 1

def ReduceReadHead (p : ReduceReadPublic) (s : State) : Prop :=
  GoodL p.layout s ∧ s.gpr .rsi = p.pointer ∧ InRegions (s.rd ++ s.wr) p.pointer 1

def ReduceReadStore (p : ReduceReadPublic) (s : State) : Prop :=
  s.gpr .rdi = p.layout.B ∧ s.gpr .rsi = p.pointer ∧
  s.gpr .rbx = off p.layout.B (slot p.layout.w aX)

theorem reduceRead_ct : RelCT isa (Two ReduceReadPre) (.block Arithmetic.reduceRead)
    (fun _ _ => True) := by
  change RelCT isa (Two ReduceReadPre) (.block (
    ([.mov .rsi (.mem (hdr Crt.sSrc))] : List Instr) ++
    ([.movzx8 .rax (at0 .rsi), .mov .rbx (.mem (hdr (sArr aX)))] : List Instr) ++
    [.store (at0 .rbx) .rax, .alu .add .rsi (.imm 1), .store (hdr Crt.sSrc) .rsi])) _
  rw [List.append_assoc]
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := ReduceReadHead) [.rdi]
    (fun p s t hs ht => pins_good p.layout s t hs.1 ht.1) (by taint_decide) ?_) ?_
  · intro p s ⟨hg, hp, hr⟩
    refine WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = p.pointer ∧ t.mem = s.mem)
      ?_ rfl) fun t ⟨⟨hsi, hm⟩, hk⟩ =>
      ⟨⟨⟨hg.1.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩,
        hsi, by simpa only [hk.2.1, hk.2.2] using hr⟩
    xrun [State.ea, hdr, hg.1.rdi, hdrOff, hp,
      hg.1.scr.ld (show 8 * Crt.sSrc + 8 ≤ p.layout.Z by
        have := hdr_lt_slot p.layout.w 8 (show Crt.sSrc < 32 by decide); have := hg.2; omega)]
  apply RelCT.block_append
  refine RelCT.seq (two_piece (Ψ := ReduceReadStore) [.rdi, .rsi]
    (pins_of (fun p r => if r = .rdi then p.layout.B else p.pointer) (by
      intro p s h r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.1.1.rdi
      · exact h.2.1)) (by taint_decide) ?_) ?_
  · intro p s ⟨hg, hsi, hr⟩
    refine WP.mono (WP.keep [.rax, .rbx] (Q := fun t =>
      t.gpr .rbx = off p.layout.B (slot p.layout.w aX)) ?_ rfl)
      fun t ⟨hbx, hk⟩ => ⟨(hk.gpr (by decide)).trans hg.1.rdi,
        (hk.gpr (by decide)).trans hsi, hbx⟩
    xrun [State.ea, at0, hdr, hsi, hr, hg.1.rdi, hdrOff,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hg.1.hdr.harr aX (by decide),
      hg.1.scr.ld (show 8 * sArr aX + 8 ≤ p.layout.Z by
        have := hdr_lt_slot p.layout.w 8 (show sArr aX < 32 by decide); have := hg.2; omega)]
  exact two_taint [.rdi, .rsi, .rbx]
    (pins_of (fun p r => if r = .rdi then p.layout.B else if r = .rsi then p.pointer else
      off p.layout.B (slot p.layout.w aX)) (by
        intro p s h r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)) (by taint_decide)

end VG.Proof.Dsa.X86_64
