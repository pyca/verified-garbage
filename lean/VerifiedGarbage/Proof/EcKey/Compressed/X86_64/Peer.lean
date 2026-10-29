module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed

import VerifiedGarbage.Proof.EcKey.Compressed.X86_64.Frame
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Ecdsa.X86_64.Scalar
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Framework.X86_64.Exec
/-! # Compressed tag, canonical x and curve constants -/

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86_64/TagCheck.lean`, which only this module imported.
section

/-! # Accept exactly SEC 1 tags 02 and 03, retaining the parity bit -/

section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdh.X86_64
open VG.Proof.X25519.X86_64 (Keeps)

private theorem tag_key : ∀ b : Byte,
    ((b.setWidth 64 &&& BitVec.signExtend 64 (-2 : BitVec 32)) ^^^
      BitVec.signExtend 64 (2 : BitVec 32) = 0) = (b = 2 ∨ b = 3) := by
  decide

theorem decompressTag_ok {c : Cfg} {s : State} {base q : Addr}
    (hs : Scr s base size) (hq : s.gpr .r9 = q)
    (hin : InRegions (s.rd ++ s.wr) q 1) (hD : c.sl D + 8 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.decompressTag c)) s fun s' =>
      s'.gpr .rdx = mask (s.mem q = 2 ∨ s.mem q = 3) ∧
      word s'.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      KeepRegs [.rdx] s s' ∧ Outside base (c.sl D) 8 s.mem s'.mem := by
  rw [show Impl.EcKey.Compressed.X86_64.decompressTag c =
    [.movzx8 .rdx { base := .r9 }, .store (sc (c.sl D)) .rdx,
      .alu .and .rdx (.imm (-2)), .alu .xor .rdx (.imm 2)] ++
    ([.alu .cmp .rdx (.imm 1)] ++ [.alu .sbb .rdx (.reg .rdx)]) from rfl,
    WP.block_append_iff]
  refine WP.mono (show WP isa (.block
    [.movzx8 .rdx { base := .r9 }, .store (sc (c.sl D)) .rdx,
      .alu .and .rdx (.imm (-2)), .alu .xor .rdx (.imm 2)]) s
    (fun t => t.gpr .rdx =
      ((s.mem q).setWidth 64 &&& BitVec.signExtend 64 (-2 : BitVec 32)) ^^^
        BitVec.signExtend 64 (2 : BitVec 32) ∧
      t.mem = s.mem.writeW (off base (c.sl D)) ((s.mem q).setWidth 64) ∧
      KeepRegs [.rdx] s t) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.map_some, Option.bind_some, State.load8, State.store64, ea_base, hq, hin,
      ea_sc, hs.rdi, st_sc hs hD, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
      RegUpd.wr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, rfl, fun r hr => ?_, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨e₁, m₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cmpOne_ok s₁) fun s₂ ⟨cf₂, k₂⟩ => ?_
  refine WP.mono (sbbRdx_ok s₂ cf₂) fun s₃ ⟨e₃, k₃⟩ => ?_
  have m₃ : s₃.mem = s₁.mem := k₃.2.1.trans k₂.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e₃, e₁]
    simp only [mask, tag_key, decide_eq_true_eq]
  · rw [m₃, m₁, word_writeW_self]
  · exact (k₁.trans ((Keeps.regs k₂).mono (by simp))).trans (Keeps.regs k₃)
  · rw [m₃, m₁]
    exact writeW_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.X86_64
end

end

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Impl.Ecdh.X86_64 (R2P BP)
open VG.Proof.Ecdsa.X86_64 VG.Proof.Mont VG.Proof.Mont.X86_64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdh.X86_64

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.X86_64.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (Impl.EcKey.Compressed.X86_64.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.X86_64.Cfg.checkLtP c (c.sl E)))) := by
  simp only [Impl.EcKey.Compressed.X86_64.decompressPeer, Impl.Ecdh.X86_64.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem decompressPeer_ok {c : Cfg} (hc : BaseCfgOk c) {base q : Addr} {s : State}
    (hs : Scr s base size) (hq : s.gpr .r9 = q)
    (hin : (⟨q, c.C.len + 1⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q, c.C.len + 1⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : word s.mem base (c.sl FLAG) = BitVec.allOnes 64) :
    WP isa (.block (Impl.EcKey.Compressed.X86_64.decompressPeer c)) s fun s' =>
      Scr s' base size ∧ KeepRegs [.rax, .rdx] s s' ∧
      Unch base (slW c [R2P, BP, D, FLAG]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      word s'.mem base (c.sl D) = (s.mem q).setWidth 64 ∧
      word s'.mem base (c.sl FLAG) = mask ((s.mem q = 2 ∨ s.mem q = 3) ∧ sv c base s E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hR := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hD := sl_le c h7 (i := D) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  rw [decompressPeer_eq, WP.block_append_iff]
  refine WP.mono (setConst_ok hs hR (Nat.lt_trans (Nat.mod_lt _ (by have := hc.p_ge; omega)) hc.p_lt))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by have := hc.p_ge; omega)) hc.p_lt)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) hR).trans (O₂.mono (Nat.zero_le _) hB)
  have q₂ : s₂.mem q = s.mem q := by
    have h := keep_of_disjoint' W₂ hd (by omega) (i := 0) (by omega) (by have := hc.len_hi; omega)
    simpa only [BitVec.add_zero] using h
  rw [WP.block_append_iff]
  refine WP.mono (decompressTag_ok (c := c) (q := q) hs₂
    (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hq])
    (by
      exact ⟨_, by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hin, by
        simpa using Offset.contains_base q (d := 0) (n := 1)
          (by omega : 0 + 1 ≤ c.C.len + 1) (by decide)⟩) (by omega)) fun s₃ ⟨mask₃, tag₃, k₃, O₃⟩ => ?_
  rw [q₂] at mask₃ tag₃
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ : Unch base (slW c [R2P, BP, D]) s.mem s₃.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (by omega) O₃)
  have flag₃ : word s₃.mem base (c.sl FLAG) = BitVec.allOnes 64 := by
    rw [U₃.word (fun w hw => by have := apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, D]) w hw; omega)
      (by omega), hf]
  rw [WP.block_append_iff]
  refine WP.mono (andFlag_ok' c hs₃ (by omega)) fun s₄ ⟨flag₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have U₄ : Unch base (slW c [R2P, BP, D, FLAG]) s.mem s₄.mem :=
    unch_same (U₃.mono (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_map_of_mem (List.mem_append_left [FLAG] hi)))
      (slot_frame (by simp) (by omega) O₄)
  have keep₄ {i : Nat} (hi : i < 45) (hm : i ∉ [R2P, BP, D, FLAG]) :
      sv c base s₄ i = sv c base s i := sv_unch U₄ h7 hn hi (apart_slW hm)
  refine WP.mono (checkLtP_ok c hs₄ h0 hE hM (by omega)) fun s₅ ⟨flag₅, k₅, O₅⟩ => ?_
  refine ⟨hs₄.of_keepRegs k₅ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans (k₃.mono (by simp))).trans
      (k₄.mono (by simp))).trans k₅
  · exact unch_same U₄ (slot_frame (by simp) (by omega) O₅)
  · rw [sv, sv_flag O₅ h0 h7 hn (by decide) (by decide), sv_flag O₄ h0 h7 hn (by decide) (by decide),
      sv_out (O₃.mono (Nat.le_refl _) (by omega : c.sl D + 8 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · rw [sv, sv_flag O₅ h0 h7 hn (by decide) (by decide), sv_flag O₄ h0 h7 hn (by decide) (by decide),
      sv_out (O₃.mono (Nat.le_refl _) (by omega : c.sl D + 8 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide)]
    exact e₂
  · rw [O₅.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega) (by omega),
      O₄.word (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega) (by omega)]
    exact tag₃
  · rw [flag₅, flag₄, flag₃, mask₃, BitVec.allOnes_and,
      show wordsVal s₄.mem base (c.sl E) c.n = sv c base s₄ E from rfl,
      show wordsVal s₄.mem base (c.sl MP) c.n = sv c base s₄ MP from rfl,
      keep₄ (by decide) (by decide), keep₄ (by decide) (by decide), hmp, mask_and]

end VG.Proof.EcKey.Compressed.X86_64
