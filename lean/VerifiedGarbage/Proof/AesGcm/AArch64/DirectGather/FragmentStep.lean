module

public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.AesGcm.AArch64.Loops

/-! The word-at-a-time tail of short gather encryption. Both source words
are read before either write, so both stores carry exactly the same ciphertext. -/

public section

namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.DirectGather

theorem xorWord_ok (sz : Size) (s : State)
    (src : InRegions (s.rd ++ s.wr) (s.gpr .x0) (sz.bits / 8))
    (key : InRegions (s.rd ++ s.wr) (s.gpr .x1) (sz.bits / 8))
    (dst : InRegions s.wr (s.gpr .x2) (sz.bits / 8))
    (auth : InRegions s.wr (s.gpr .x3) (sz.bits / 8)) :
    let n := sz.bits / 8
    let ct := s.mem.read (s.gpr .x0) n ^^^ s.mem.read (s.gpr .x1) n
    WP isa (.block (xorWord sz)) s fun t =>
      t.mem = (s.mem.write (s.gpr .x2) n ct).write (s.gpr .x3) n ct ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  cases sz <;> apply WP.of_runBlock
  all_goals
    simp only [Size.bits, Nat.reduceDiv] at src key dst auth
    simp only [xorWord, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
      State.read, Size.bits, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT, and_self,
      ↓reduceIte, Size.bytes, BitVec.add_zero, src, key, dst, auth, Option.map_some,
      Option.bind_some, gpr_write, mem_write, rd_write, wr_write, BitVec.setWidth_eq, reduceCtorEq,
      Option.some.injEq, exists_eq_left']
  all_goals simp +contextual [sp_write, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide)]

end VG.Proof.AesGcm.AArch64.DirectGather

/-! Machine steps of the direct short-record fragment loop. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather.Fragment

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64

abbrev advance (k : Nat) : List Instr :=
  [ptr .x0 .x0 k, ptr .x1 .x1 k, ptr .x2 .x2 k, ptr .x3 .x3 k]

abbrev blockData : List Instr :=
  [.ldrq .v0 .x0 0, .ldrq .v1 .x1 0, .vop (.logic .eor .v0 .v0 .v1),
   .strq .v0 .x2 0, .strq .v0 .x3 0]

abbrev byteData : List Instr :=
  [.ldrb .x14 .x0 0, .ldrb .x15 .x1 0, .logic .eor .w .x14 .x14 .x15,
   .strb .x14 .x2 0, .strb .x14 .x3 0]

abbrev blockStep := blockData ++ advance 16 ++ [.subImm .x .x13 .x13 1]
abbrev byteStep := byteData ++ advance 1 ++ [.subImm .x .x12 .x12 1]

/-- Memory and register obligations of all four XOR widths. -/
structure Access (s : State) (n : Nat) : Prop where
  src : InRegions (s.rd ++ s.wr) (s.gpr .x0) n
  key : InRegions (s.rd ++ s.wr) (s.gpr .x1) n
  dst : InRegions s.wr (s.gpr .x2) n
  auth : InRegions s.wr (s.gpr .x3) n

def putBoth (s : State) (n : Nat) : Mem :=
  let ct := s.mem.read (s.gpr .x0) n ^^^ s.mem.read (s.gpr .x1) n
  (s.mem.write (s.gpr .x2) n ct).write (s.gpr .x3) n ct

structure Kept (s t : State) (regs : List Reg) : Prop where
  gpr : ∀ r, r ∉ regs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

structure Wrote (s : State) (n : Nat) (regs : List Reg) (t : State) : Prop extends Kept s t regs where
  mem : t.mem = putBoth s n

set_option linter.unusedSimpArgs false in
theorem blockData_ok (s : State) (h : Access s 16) :
    WP isa (.block blockData) s (Wrote s 16 []) := by
  apply WP.of_runBlock
  simp only [blockData, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, ↓reduceIte, BitVec.add_zero,
    h.src, h.key, h.dst, h.auth, Option.map_some, Option.bind_some,
    rd_setV, wr_setV, mem_setV, gpr_setV, VOp.eval, v_setV, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, ?_⟩
  simp [putBoth, State.setV]

set_option linter.unusedSimpArgs false in
theorem byteData_ok (s : State) (h : Access s 1) :
    WP isa (.block byteData) s (Wrote s 1 [.x14, .x15]) := by
  apply WP.of_runBlock
  simp only [byteData, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, ↓reduceIte, BitVec.add_zero,
    h.src, h.key, h.dst, h.auth, Option.map_some, Option.bind_some, gpr_write, mem_write, rd_write, wr_write,
    BitVec.setWidth_eq, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2]
  · simp [putBoth, State.write, State.read, Size.bits, byte_xor]

theorem wordData_ok (sz : Size) (s : State) (h : Access s (sz.bits / 8)) :
    WP isa (.block (DirectGather.xorWord sz)) s (Wrote s (sz.bits / 8) [.x14,.x15]) := by
  refine (xorWord_ok sz s h.src h.key h.dst h.auth).mono fun t ⟨hm,hg,hsp,hr,hw⟩ => ?_
  exact ⟨⟨fun r hn => hg _ (fun he => hn (by simp [he])) (fun he => hn (by simp [he])), hsp, hr, hw⟩, hm⟩

end VG.Proof.AesGcm.AArch64.DirectGather.Fragment
