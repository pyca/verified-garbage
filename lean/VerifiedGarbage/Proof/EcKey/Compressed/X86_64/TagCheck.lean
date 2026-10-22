module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86_64.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Ecdh.X86_64.Peer
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! # Accept exactly SEC 1 tags 02 and 03, retaining the parity bit -/

@[expose] public section

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
