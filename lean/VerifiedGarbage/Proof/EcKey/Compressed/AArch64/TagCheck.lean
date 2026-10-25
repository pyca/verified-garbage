module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # Accept precisely 02 and 03 and preserve their parity bit -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

 theorem tagRead_ok {s : State} {q : Addr} (hq : s.gpr .x6 = q)
    (hin : InRegions (s.rd ++ s.wr) q 1) :
    WP isa (.block [zero7, .ldrb .x1 .x6 0]) s fun t =>
      t.gpr .x1 = (s.mem q).setWidth 64 ∧ t.gpr .x7 = 0 ∧ Keeps [.x1, .x7] s t := by
  have ha : s.gpr .x6 + BitVec.ofNat 64 0 = q := by rw [hq, BitVec.add_zero]
  apply WP.of_runBlock
  simp only [zero7, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Nat.mod_one,
    show 0 < 4096 * 1 by decide, show 16 * 0 < Size.x.bits by decide, and_self, ite_true, Option.bind_some, State.load,
    RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    reduceCtorEq, ite_false, ha, hin, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [read1_zext, RegUpd.mem_write], rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

 theorem tagBits_ok (s : State) :
    WP isa (.block [.movz .x .x5 1 0, .logic .orr .x .x1 .x1 .x5,
      .movz .x .x5 3 0, .logic .eor .x .x1 .x1 .x5]) s fun t =>
      t.gpr .x1 = (s.gpr .x1 ||| 1) ^^^ 3 ∧ Keeps [.x1, .x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show 16 * 0 < Size.x.bits by decide, ite_true, RegUpd.gpr_write,
    BitVec.setWidth_eq, reduceCtorEq, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

 theorem decompressTag_ok {c : Cfg} {s : State} {base q : Addr}
    (hs : Scr s base size) (hq : s.gpr .x6 = q)
    (hin : InRegions (s.rd ++ s.wr) q 1) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.decompressTag c)) s fun t =>
      t.gpr .x2 = mask (s.mem q = 2 ∨ s.mem q = 3) ∧
      word t.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      KeepRegs [.x1, .x2, .x5, .x7, .x16] s t ∧ Outside base (c.sl D) 8 s.mem t.mem := by
  change WP isa (.block ([zero7, .ldrb .x1 .x6 0] ++ ([st .x1 (c.sl D)] ++
    ([.movz .x .x5 1 0, .logic .orr .x .x1 .x1 .x5, .movz .x .x5 3 0,
      .logic .eor .x .x1 .x1 .x5] ++ Impl.Ecdh.AArch64.Cfg.isZero)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (tagRead_ok hq hin) fun s₁ ⟨v₁, z₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (st_out (hs.of_keeps k₁ (by decide)) hD (sl_mod8 c D) .x1)
    fun s₂ ⟨m₂, k₂, g₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tagBits_ok s₂) fun s₃ ⟨v₃, k₃⟩ => ?_
  refine WP.mono (isZero_ok s₃ (by rw [k₃.gpr _ (by decide), g₂, z₁]))
    fun s₄ ⟨v₄, k₄⟩ => ?_
  have m₄ : s₄.mem = s.mem.writeW (off base (c.sl D)) ((s.mem q).setWidth 64) := by
    rw [k₄.mem, k₃.mem, m₂, k₁.mem, v₁]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [v₄, v₃, g₂, v₁]
    have key : ∀ b : Byte, ((b.setWidth 64 ||| 1) ^^^ 3 = 0) = (b = 2 ∨ b = 3) := by decide
    simp only [mask, key]
  · rw [m₄, word_writeW_self]
  · exact (((Keeps.regs k₁).mono (by sub_regs)).trans (k₂.mono (by sub_regs))).trans
      (((Keeps.regs k₃).mono (by sub_regs)).trans ((Keeps.regs k₄).mono (by sub_regs)))
  · rw [m₄]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.AArch64
