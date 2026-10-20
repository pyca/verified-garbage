module

public import VerifiedGarbage.Impl.Dsa.X86.Stream
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # A byte fetch into a zero-padded runtime integer -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

private theorem wp_byte {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {op : MemOp} {a : Addr}
    (ha : s.ea op = a) (hr : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ t, Upd s t d ((s.mem a).setWidth 32) → WP isa (.block is) t Q) :
    WP isa (.block (.movzx8 d op :: is)) s Q := by
  refine VG.X86.Wp.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Upd.setReg _ _ _))
  simp only [exec, ha, State.load8, ite_eq_left hr, Option.map_some]

theorem fetchByte_ok {n size i : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (hs : Scr s base size) (hn : 0 < n) (hz : contextBytes n ≤ size)
    (hi : s.gpr .esi = p + BitVec.ofNat 32 i) (hfit : p.toNat + i < 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hpad : wordsVal s.mem base (slot n 7) n < 2 ^ 32) :
    WP isa (.block (fetchByte n)) s fun t =>
      wordsVal t.mem base (slot n 7) n = (s.mem (p.setWidth 64 + BitVec.ofNat 64 i)).toNat ∧
      Outside base (slot n 7) 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  have hd := slot_bound (n := n) (i := 7) (by decide)
  have hd0 := slot_header n 9
  have hsize : 64 ≤ size := by change slot n 9 ≤ size at hz; omega
  have nw := hs.nowrap
  unfold fetchByte
  have ha : s.ea (at_ .esi 0) = p.setWidth 64 + BitVec.ofNat 64 i := by
    change (s.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, hi]
    exact addr_eq hfit
  refine wp_byte ha hr fun s₃ u₃ => ?_
  have K₃ := u₃.keeps
  have hs₃ := hs.of_keeps K₃ (by decide)
  have ho : slot n 7 + 4 ≤ size := by unfold stride at hd; omega
  have W := writeW32_outside s₃.mem base (d := slot n 7) (s₃.gpr .eax) (by omega)
  refine wp_storeS (hs₃.ea (by omega)) (hs₃.write ho) fun t mt => WP.block_nil ⟨?_, ?_, K₃.trans (mt.keeps _)⟩
  · obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 1 := ⟨2 * n - 1, by omega⟩
    rw [wordsVal_eq_val32, hk, val32] at hpad
    have tail : val32 s.mem base (slot n 7 + 4) k = 0 := by omega
    rw [wordsVal_eq_val32, hk, val32, mt.mem, w32_write_self,
      W.val32 (by omega) (by unfold stride at hd; omega), u₃.mem, tail,
      Nat.mul_zero, Nat.add_zero, u₃.gpr, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.mem (p.setWidth 64 + BitVec.ofNat 64 i)).isLt (by decide))
  · rw [mt.mem, u₃.mem]
    exact writeW32_outside _ _ _ (by omega)

end VG.Proof.Dsa.X86
