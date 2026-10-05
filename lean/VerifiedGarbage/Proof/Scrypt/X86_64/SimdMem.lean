import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Impl.Scrypt.X86_64.Salsa

/-! Unaligned SSE2 copy and XOR, preserving every general-purpose register. -/
namespace VG.Proof.Scrypt.X86_64.SimdMem
open VG VG.X86_64 VG.Impl.Scrypt.X86_64

private theorem ea_setXmm (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) :
    (s.setXmm r v).ea m = s.ea m := rfl

theorem copy {s : State} {x d : Addr}
    (hx : s.ea (at_ .rdi 0) = x) (hd : s.ea (at_ .rsi 0) = d)
    (hin : InRegions (s.rd ++ s.wr) x 16) (hout : InRegions s.wr d 16) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .rdi 0), .movdquStore (at_ .rsi 0) .xmm0]) s
      fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.mem = s.mem.writeW d (s.mem.readW x 128) := by
  refine WP.block_cons_iff.mpr ⟨s.setXmm .xmm0 (s.mem.readW x 128), ?_, ?_⟩
  · simp only [exec, State.load128, hx, hin, ite_true, Option.map_some]
  refine WP.block_cons_iff.mpr
    ⟨{ s.setXmm .xmm0 (s.mem.readW x 128) with mem := s.mem.writeW d (s.mem.readW x 128) },
      ?_, WP.block_nil ⟨rfl, rfl, rfl, rfl⟩⟩
  simp only [exec, State.store128, ea_setXmm, hd, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, RegUpd.xmm_setXmm_self, hout, ite_true]

theorem xor {s : State} {x y d : Addr}
    (hx : s.ea (at_ .rdi 0) = x) (hy : s.ea (at_ .rsi 0) = y)
    (hd : s.ea (at_ .r8 0) = d)
    (hinx : InRegions (s.rd ++ s.wr) x 16) (hiny : InRegions (s.rd ++ s.wr) y 16)
    (hout : InRegions s.wr d 16) :
    WP isa (.block [.movdquLoad .xmm0 (at_ .rdi 0), .movdquLoad .xmm1 (at_ .rsi 0),
      .xop (.bin .pxor .xmm0 .xmm1), .movdquStore (at_ .r8 0) .xmm0]) s
      fun t => t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
        t.mem = s.mem.writeW d (s.mem.readW x 128 ^^^ s.mem.readW y 128) := by
  refine WP.block_cons_iff.mpr ⟨s.setXmm .xmm0 (s.mem.readW x 128), ?_, ?_⟩
  · simp only [exec, State.load128, hx, hinx, ite_true, Option.map_some]
  let t := (s.setXmm .xmm0 (s.mem.readW x 128)).setXmm .xmm1 (s.mem.readW y 128)
  refine WP.block_cons_iff.mpr ⟨t, ?_, ?_⟩
  · simp only [t, exec, State.load128, ea_setXmm, hy, RegUpd.rd_setXmm,
      RegUpd.wr_setXmm, RegUpd.mem_setXmm, hiny, ite_true, Option.map_some]
  let u := t.setXmm .xmm0 (s.mem.readW x 128 ^^^ s.mem.readW y 128)
  refine WP.block_cons_iff.mpr ⟨u, ?_, ?_⟩
  · simp only [u, t, exec, XOp.exec, XBinOp.eval,
      RegUpd.xmm_setXmm_of_ne _ _ (by decide : XReg.xmm0 ≠ XReg.xmm1),
      RegUpd.xmm_setXmm_self]
  refine WP.block_cons_iff.mpr
    ⟨{ u with mem := s.mem.writeW d (s.mem.readW x 128 ^^^ s.mem.readW y 128) },
      ?_, WP.block_nil ⟨rfl, rfl, rfl, rfl⟩⟩
  simp only [u, t, exec, State.store128, ea_setXmm, hd, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, RegUpd.xmm_setXmm_self, hout, ite_true]

end VG.Proof.Scrypt.X86_64.SimdMem
