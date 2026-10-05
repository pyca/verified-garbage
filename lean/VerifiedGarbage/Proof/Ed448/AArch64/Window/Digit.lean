import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.X448.AArch64.BitBody
import VerifiedGarbage.Proof.Curve448.AArch64.Fast.MOp
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Store

/-!
# Ed448 verification on AArch64: a digit of the challenge

Untrusted: everything here is checked by Lean. `digitOf sh`, with `x19 = j`,
leaves in `x11` byte `j` of the challenge's copy at `KB` shifted right by `sh`
(0 or 4) and masked to 4 bits (`digitOf_ok`).
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Proof.X448.AArch64 (Scr Keeps off word)

/-- A nibble of a byte. -/
def nibOf (b : BitVec 8) (sh : Nat) : Nat := (b.toNat >>> sh) % 16

private theorem nib_fact : ∀ b : BitVec 8,
    ((b.setWidth 64 >>> 4) &&& ((15 : BitVec 16).setWidth 32).setWidth 64) = BitVec.ofNat 64 (nibOf b 4) ∧
    (b.setWidth 64 &&& ((15 : BitVec 16).setWidth 32).setWidth 64) = BitVec.ofNat 64 (nibOf b 0) := by
  decide +kernel

theorem nibOf_lt (b : BitVec 8) (sh : Nat) : nibOf b sh < 16 := Nat.mod_lt _ (by decide)

/-- `x11` := byte `KB + j` of the working space, through `x2`. -/
theorem loadByte_ok {s : State} {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 57)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.add .x .x2 .x3 .x19, .ldrb .x11 .x2 KB]) s fun t =>
      t.gpr .x11 = (s.mem (off base (KB + j))).setWidth 64 ∧ Keeps [.x2, .x11] s t ∧ t.mem = s.mem := by
  have enc : KB % 1 = 0 ∧ KB < 4096 := ⟨Nat.mod_one _, by decide⟩
  have hr : InRegions (s.rd ++ s.wr) (off base (KB + j)) 1 := hs.read (by simp only [KB]; omega)
  have ha : base + BitVec.ofNat 64 j + BitVec.ofNat 64 KB = off base (KB + j) := by
    rw [off_add', Nat.add_comm]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self, State.read, Size.bits,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq, hs.x3, hc,
    ha, State.load, hr, VG.Proof.X448.AArch64.read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := (s.mem (off base (KB + j))).isLt
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- **A digit** of the challenge: the nibble at shift `sh` of byte `KB + j` of the working space. -/
theorem digitOf_ok {s : State} {base : Addr} (hs : Scr s base) {j : Nat} (hj : j < 57)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) {sh : Nat} (hsh : sh = 0 ∨ sh = 4) :
    WP isa (.block (digitOf sh)) s fun t =>
      t.gpr .x11 = BitVec.ofNat 64 (nibOf (s.mem (off base (KB + j))) sh) ∧
      Keeps [.x2, .x11, .x10] s t ∧ t.mem = s.mem := by
  rw [digitOf, List.append_assoc, show ([.add .x .x2 .x3 .x19, .ldrb .x11 .x2 KB, .movz .x .x10 15 0] :
    List Instr) = [.add .x .x2 .x3 .x19, .ldrb .x11 .x2 KB] ++ [.movz .x .x10 15 0] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (loadByte_ok hs hj hc) fun a ⟨a11, ka, ma⟩ => ?_
  rcases hsh with rfl | rfl
  · simp only [↓reduceIte, List.nil_append, List.cons_append]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show 16 * 0 < Size.x.bits from by decide, ite_true, BitVec.shiftLeft_zero, Nat.mul_zero,
      RegUpd.gpr_write, BitVec.setWidth_eq, a11, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
    refine ⟨(nib_fact _).2, ⟨fun r hr => ?_, ka.2.1, ka.2.2⟩, ma⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.1, hr.2.2, ite_false]
    exact ka.1 _ (by simp [hr.1, hr.2.1])
  · simp only [show ¬ (4 : Nat) = 0 from by decide, ↓reduceIte, List.cons_append, List.nil_append]
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
      show 16 * 0 < Size.x.bits from by decide, show (4 : Nat) < 64 from by decide, ite_true,
      BitVec.shiftLeft_zero, Nat.mul_zero, RegUpd.gpr_write, BitVec.setWidth_eq, a11, ite_false, reduceCtorEq,
      Option.some.injEq, exists_eq_left']
    refine ⟨(nib_fact _).1, ⟨fun r hr => ?_, ka.2.1, ka.2.2⟩, ma⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.2.1, hr.2.2, ite_false]
    exact ka.1 _ (by simp [hr.1, hr.2.1])

end VG.Proof.Ed448.AArch64.Window
