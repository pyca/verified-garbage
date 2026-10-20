module

public import VerifiedGarbage.Proof.Bignum.X86.PublicBody
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The exponentiation iteration with its public countdown -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.PublicContext

theorem exponentStep_ok {n bytes m y b k : Nat} {base : Addr} {s : State}
    (h : Context n m base bytes s)
    (hy : wordsVal s.mem base (slot n 7) n = y * 2 ^ (64 * n) % m)
    (hb : wordsVal s.mem base (slot n 6) n = b * 2 ^ (64 * n) % m)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : s.gpr .esi = BitVec.ofNat 32 k) :
    WP isa (exponentStep n) s fun t =>
      t.gpr .esi = BitVec.ofNat 32 (k - 1) ∧ t.zf = some (decide (k = 1)) ∧
      Context n m base bytes t ∧
      wordsVal t.mem base (slot n 7) n =
        (if val32 s.mem base 128 2 % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 6) n = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base 128 2 = val32 s.mem base 128 2 / 2 ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold exponentStep
  refine WP.seq (WP.mono (exponentBody_ok h hy hb) fun u ⟨c, Y, B, E, O, K⟩ => ?_)
  have count : u.gpr .esi = BitVec.ofNat 32 k := (K.1 .esi (by decide)).trans hc
  refine wp_subS rfl fun v uv _ => ?_
  refine wp_cmpS rfl fun t ft zt => WP.block_nil ?_
  have mt : t.mem = u.mem := ft.mem.trans uv.mem
  have kt : Keeps powerClob u t := (uv.keeps.mono (by decide)).trans (ft.keeps _)
  have ct : Context n m base bytes t := ⟨c.scr.of_keeps kt (by decide), c.size_le,
    mt ▸ c.mod, c.gt_one, mt ▸ c.inverse⟩
  refine ⟨?_, ?_, ct, mt ▸ Y, mt ▸ B, mt ▸ E, mt ▸ O, (K.mono (by decide)).trans kt⟩
  · rw [ft.gpr, uv.gpr, count, counter_sub hk32 hk]
  · rw [zt, uv.gpr, count, counter_sub hk32 hk, counter_zero hk32 hk]

end VG.Proof.Bignum.X86.PublicContext
