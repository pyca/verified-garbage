module

public import VerifiedGarbage.Impl.Dsa.Arm.Entry
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Dsa.Arm.Shape
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-!
# DSA on 32-bit ARM: saving the registers and the arguments

The entry saves `r4`–`r11` and `lr` at offset 128 of the working space
(`save_ok`), the arguments the bodies use at their fields (`signArgs_ok`,
`verifyArgs_ok`), and the pointers to the key's components, each after the
one before (`keyPointers_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr wp_dp wp_movw op2_imm op2_reg dpVal)

/-- `t = ` the stack argument `i`. -/
theorem wp_ldrSp {s : State} {is : List Instr} {Q : State → Prop} {t : Reg} {i : Nat} (hi : 4 * i < 4096)
    (hin : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4)
    (k : ∀ s', Upd s s' t (stackArg s i) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: is)) s Q := by
  have e : stackArgAddr s i = State.addr (s.sp + BitVec.ofNat 32 (4 * i)) := rfl
  rw [e] at hin
  exact VG.Proof.X25519.Arm.WP.cons (by simp only [reduceExec, hi, ite_true, State.load32, hin, Option.map_some]; rfl)
    (k _ (VG.Proof.X25519.Arm.Upd.setReg _ _ _))

/-- `[r12 + d] = r`. -/
theorem wp_str12 {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {is : List Instr}
    {Q : State → Prop} {r : Reg} {d : Nat} (hd : d < 4096) (hd' : d + 4 ≤ size)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str r .r12 d :: is)) s Q :=
  wp_str hd (hs.ea12 (by omega_arith)) (hs.write hd') k

theorem readW_off_ne {m : Mem} {base : Addr} {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d + 4 ≤ 2 ^ 64)
    (he : e + 4 ≤ 2 ^ 64) (v : BitVec 32) :
    (m.writeW (off base e) v).readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_writeW_sep (Offset.sep base h hd he) (by decide)

theorem readW_off_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 32) :
    (m.writeW (off base d) v).readW (off base d) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

/-- The registers saved by `save`, at `[128 + 4i]`. -/
theorem save_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size) :
    WP isa (.block Entry.save) s fun t =>
      (∀ i < 9, t.mem.readW (off base (128 + 4 * i)) 32 = s.gpr (Entry.savedRegs.getD i .r0)) ∧
      Rest [] s t ∧ Outside base 128 36 s.mem t.mem := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r4 .r12 128, .str .r5 .r12 132, .str .r6 .r12 136, .str .r7 .r12 140,
    .str .r8 .r12 144, .str .r9 .r12 148, .str .r10 .r12 152, .str .r11 .r12 156, .str .lr .r12 160]) s _
  refine wp_str12 hs (by decide) (by omega_arith) fun s₁ m₁ => ?_
  have w₁ := hs.of_mupd m₁
  refine wp_str12 w₁ (by decide) (by omega_arith) fun s₂ m₂ => ?_
  have w₂ := w₁.of_mupd m₂
  refine wp_str12 w₂ (by decide) (by omega_arith) fun s₃ m₃ => ?_
  have w₃ := w₂.of_mupd m₃
  refine wp_str12 w₃ (by decide) (by omega_arith) fun s₄ m₄ => ?_
  have w₄ := w₃.of_mupd m₄
  refine wp_str12 w₄ (by decide) (by omega_arith) fun s₅ m₅ => ?_
  have w₅ := w₄.of_mupd m₅
  refine wp_str12 w₅ (by decide) (by omega_arith) fun s₆ m₆ => ?_
  have w₆ := w₅.of_mupd m₆
  refine wp_str12 w₆ (by decide) (by omega_arith) fun s₇ m₇ => ?_
  have w₇ := w₆.of_mupd m₇
  refine wp_str12 w₇ (by decide) (by omega_arith) fun s₈ m₈ => ?_
  have w₈ := w₇.of_mupd m₈
  refine wp_str12 w₈ (by decide) (by omega_arith) fun t m₉ => WP.block_nil ⟨?_, ?_, ?_⟩
  · have mt : t.mem = ((((((((s.mem.writeW (off base 128) (s.gpr .r4)).writeW (off base 132) (s.gpr .r5)).writeW
        (off base 136) (s.gpr .r6)).writeW (off base 140) (s.gpr .r7)).writeW (off base 144) (s.gpr .r8)).writeW
        (off base 148) (s.gpr .r9)).writeW (off base 152) (s.gpr .r10)).writeW (off base 156) (s.gpr .r11)).writeW
        (off base 160) (s.gpr .lr) := by
      rw [m₉.mem, m₈.mem, m₇.mem, m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem, m₈.gpr, m₇.gpr, m₆.gpr, m₅.gpr,
        m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr]
    intro i hi
    rw [mt]
    rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega_arith) only [readW_off_ne, readW_off_self, Entry.savedRegs, List.getD_cons_zero,
      List.getD_cons_succ, Nat.mul_zero, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd]
  · exact ((((((((m₁.rest _).trans (m₂.rest _)).trans (m₃.rest _)).trans (m₄.rest _)).trans (m₅.rest _)).trans
      (m₆.rest _)).trans (m₇.rest _)).trans (m₈.rest _)).trans (m₉.rest _)
  · have o : ∀ {m : Mem} {d : Nat} (v : BitVec 32), 128 ≤ d → d + 4 ≤ 164 → Outside base 128 36 m (m.writeW (off base d) v) :=
      fun v h₁ h₂ => (writeW32_outside _ _ _ (by omega_arith)).mono h₁ (by omega_arith)
    rw [m₉.mem]
    refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₈.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₇.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₆.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₅.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₄.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₃.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₂.mem]; refine (Outside.trans ?_ (o _ (by decide) (by decide)))
    rw [m₁.mem]; exact o _ (by decide) (by decide)

/-- The stack arguments are apart from the header. -/
def ArgsApart (s : State) (base : Addr) (n : Nat) : Prop :=
  ∀ i < n, ∀ d, d + 4 ≤ 164 → Mem.Sep (stackArgAddr s i) 4 (off base d) 4

theorem stackArg_mupd {s s' : State} {base : Addr} {d n i : Nat} {v : BitVec 32}
    (m : Mupd s s' (s.mem.writeW (off base d) v)) (ha : ArgsApart s base n) (hi : i < n) (hd : d + 4 ≤ 164) :
    stackArg s' i = stackArg s i := by
  unfold stackArg
  rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, m.sp], m.mem]
  exact Mem.readW_writeW_sep (ha i hi d hd) (by decide)

theorem ArgsApart.mupd {s s' : State} {base : Addr} {d n : Nat} {v : BitVec 32}
    (m : Mupd s s' (s.mem.writeW (off base d) v)) (ha : ArgsApart s base n) : ArgsApart s' base n :=
  fun i hi e he => by rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, m.sp]]; exact ha i hi e he

theorem ArgsApart.upd {s s' : State} {base : Addr} {n : Nat} {r : Reg} {v : BitVec 32}
    (u : Upd s s' r v) (ha : ArgsApart s base n) : ArgsApart s' base n :=
  fun i hi e he => by rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, u.sp]]; exact ha i hi e he

theorem stackArg_upd {s s' : State} {r : Reg} {v : BitVec 32} (u : Upd s s' r v) (i : Nat) :
    stackArg s' i = stackArg s i := by
  unfold stackArg; rw [show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, u.sp], u.mem]

/-- The readable stack arguments. -/
def ArgsRead (s : State) (n : Nat) : Prop := ∀ i < n, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4

theorem ArgsRead.keep {s s' : State} {n : Nat} (h : ArgsRead s n) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) : ArgsRead s' n :=
  fun i hi => by rw [hrd, hwr, show stackArgAddr s' i = stackArgAddr s i by simp only [stackArgAddr, hsp]]; exact h i hi

/-- A stored word, then one stored apart. -/
theorem stored {m : Mem} {base : Addr} {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d + 4 ≤ 2 ^ 64)
    (he : e + 4 ≤ 2 ^ 64) {v : BitVec 32} (hm : m.readW (off base d) 32 = v) (w : BitVec 32) :
    (m.writeW (off base e) w).readW (off base d) 32 = v := by
  rw [readW_off_ne h hd he, hm]

theorem outside_word {m : Mem} {base : Addr} {o n d : Nat} (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n) (hb : o + n ≤ 2 ^ 64)
    (v : BitVec 32) : Outside base o n m (m.writeW (off base d) v) :=
  (writeW32_outside _ _ _ (by omega_arith)).mono h₁ h₂

/-- The arguments of signing at their fields. -/
theorem signArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size)
    (hr : ArgsRead s 7) (ha : ArgsApart s base 7) :
    WP isa (.block (Entry.signArguments.flatMap Entry.saveArgument)) s fun t =>
      t.mem.readW (off base 96) 32 = s.gpr .r0 ∧ t.mem.readW (off base 64) 32 = s.gpr .r2 ∧
      t.mem.readW (off base 100) 32 = stackArg s 0 ∧ t.mem.readW (off base 88) 32 = stackArg s 1 ∧
      t.mem.readW (off base 104) 32 = stackArg s 2 ∧ t.mem.readW (off base 92) 32 = stackArg s 3 ∧
      t.mem.readW (off base 108) 32 = stackArg s 4 ∧
      Rest [.r4] s t ∧ Outside base 64 48 s.mem t.mem ∧ ∀ i < 7, stackArg t i = stackArg s i := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r0 .r12 96, .str .r2 .r12 64, .ldrSp .r4 (4 * 0), .str .r4 .r12 100,
    .ldrSp .r4 (4 * 1), .str .r4 .r12 88, .ldrSp .r4 (4 * 2), .str .r4 .r12 104,
    .ldrSp .r4 (4 * 3), .str .r4 .r12 92, .ldrSp .r4 (4 * 4), .str .r4 .r12 108]) s _
  refine wp_str12 hs (by decide) (by omega_arith) fun s₁ m₁ => ?_
  have a₁ := ha.mupd m₁
  refine wp_str12 (hs.of_mupd m₁) (by decide) (by omega_arith) fun s₂ m₂ => ?_
  have a₂ := a₁.mupd m₂
  have w₂ := (hs.of_mupd m₁).of_mupd m₂
  have r₂ : ArgsRead s₂ 7 := (hr.keep m₁.rd m₁.wr m₁.sp).keep m₂.rd m₂.wr m₂.sp
  have A₂ : ∀ i < 7, stackArg s₂ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₂ a₁ hi (by decide), stackArg_mupd m₁ ha hi (by decide)]
  refine wp_ldrSp (by decide) (r₂ 0 (by decide)) fun s₃ u₃ => wp_str12 (w₂.of_upd u₃ (by decide)) (by decide)
    (by omega_arith) fun s₄ m₄ => ?_
  have a₄ := (a₂.upd u₃).mupd m₄
  have w₄ := (w₂.of_upd u₃ (by decide)).of_mupd m₄
  have r₄ : ArgsRead s₄ 7 := (r₂.keep u₃.rd u₃.wr u₃.sp).keep m₄.rd m₄.wr m₄.sp
  have A₄ : ∀ i < 7, stackArg s₄ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₄ (a₂.upd u₃) hi (by decide), stackArg_upd u₃, A₂ i hi]
  refine wp_ldrSp (by decide) (r₄ 1 (by decide)) fun s₅ u₅ => wp_str12 (w₄.of_upd u₅ (by decide)) (by decide)
    (by omega_arith) fun s₆ m₆ => ?_
  have a₆ := (a₄.upd u₅).mupd m₆
  have w₆ := (w₄.of_upd u₅ (by decide)).of_mupd m₆
  have r₆ : ArgsRead s₆ 7 := (r₄.keep u₅.rd u₅.wr u₅.sp).keep m₆.rd m₆.wr m₆.sp
  have A₆ : ∀ i < 7, stackArg s₆ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₆ (a₄.upd u₅) hi (by decide), stackArg_upd u₅, A₄ i hi]
  refine wp_ldrSp (by decide) (r₆ 2 (by decide)) fun s₇ u₇ => wp_str12 (w₆.of_upd u₇ (by decide)) (by decide)
    (by omega_arith) fun s₈ m₈ => ?_
  have a₈ := (a₆.upd u₇).mupd m₈
  have w₈ := (w₆.of_upd u₇ (by decide)).of_mupd m₈
  have r₈ : ArgsRead s₈ 7 := (r₆.keep u₇.rd u₇.wr u₇.sp).keep m₈.rd m₈.wr m₈.sp
  have A₈ : ∀ i < 7, stackArg s₈ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₈ (a₆.upd u₇) hi (by decide), stackArg_upd u₇, A₆ i hi]
  refine wp_ldrSp (by decide) (r₈ 3 (by decide)) fun s₉ u₉ => wp_str12 (w₈.of_upd u₉ (by decide)) (by decide)
    (by omega_arith) fun s₁₀ m₁₀ => ?_
  have a₁₀ := (a₈.upd u₉).mupd m₁₀
  have w₁₀ := (w₈.of_upd u₉ (by decide)).of_mupd m₁₀
  have r₁₀ : ArgsRead s₁₀ 7 := (r₈.keep u₉.rd u₉.wr u₉.sp).keep m₁₀.rd m₁₀.wr m₁₀.sp
  have A₁₀ : ∀ i < 7, stackArg s₁₀ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₁₀ (a₈.upd u₉) hi (by decide), stackArg_upd u₉, A₈ i hi]
  refine wp_ldrSp (by decide) (r₁₀ 4 (by decide)) fun s₁₁ u₁₁ => wp_str12 (w₁₀.of_upd u₁₁ (by decide)) (by decide)
    (by omega_arith) fun t m₁₂ => WP.block_nil ?_
  have A : ∀ i < 7, stackArg t i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₁₂ (a₁₀.upd u₁₁) hi (by decide), stackArg_upd u₁₁, A₁₀ i hi]
  -- The words, each stored once.
  have v₁ : s₁.mem.readW (off base 96) 32 = s.gpr .r0 := by rw [m₁.mem]; exact readW_off_self _ _ _ _
  have v₂ : s₂.mem.readW (off base 64) 32 = s.gpr .r2 := by rw [m₂.mem, m₁.gpr]; exact readW_off_self _ _ _ _
  have v₄ : s₄.mem.readW (off base 100) 32 = stackArg s 0 := by
    rw [m₄.mem, u₃.gpr, A₂ 0 (by decide)]; exact readW_off_self _ _ _ _
  have v₆ : s₆.mem.readW (off base 88) 32 = stackArg s 1 := by
    rw [m₆.mem, u₅.gpr, A₄ 1 (by decide)]; exact readW_off_self _ _ _ _
  have v₈ : s₈.mem.readW (off base 104) 32 = stackArg s 2 := by
    rw [m₈.mem, u₇.gpr, A₆ 2 (by decide)]; exact readW_off_self _ _ _ _
  have v₁₀ : s₁₀.mem.readW (off base 92) 32 = stackArg s 3 := by
    rw [m₁₀.mem, u₉.gpr, A₈ 3 (by decide)]; exact readW_off_self _ _ _ _
  have v₁₂ : t.mem.readW (off base 108) 32 = stackArg s 4 := by
    rw [m₁₂.mem, u₁₁.gpr, A₁₀ 4 (by decide)]; exact readW_off_self _ _ _ _
  -- Later stores keep them.
  have k₁₂ : ∀ {d v}, d + 4 ≤ 108 → s₁₀.mem.readW (off base d) 32 = v → t.mem.readW (off base d) 32 = v :=
    fun hd h => by rw [m₁₂.mem, u₁₁.mem]; exact stored (.inl hd) (by omega_arith) (by omega_arith) h _
  have k₁₀ : ∀ {d v}, (d + 4 ≤ 92 ∨ 96 ≤ d) → d + 4 ≤ 164 → s₈.mem.readW (off base d) 32 = v →
      s₁₀.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₁₀.mem, u₉.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  have k₈ : ∀ {d v}, (d + 4 ≤ 104 ∨ 108 ≤ d) → d + 4 ≤ 164 → s₆.mem.readW (off base d) 32 = v →
      s₈.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₈.mem, u₇.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  have k₆ : ∀ {d v}, (d + 4 ≤ 88 ∨ 92 ≤ d) → d + 4 ≤ 164 → s₄.mem.readW (off base d) 32 = v →
      s₆.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₆.mem, u₅.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  have k₄ : ∀ {d v}, (d + 4 ≤ 100 ∨ 104 ≤ d) → d + 4 ≤ 164 → s₂.mem.readW (off base d) 32 = v →
      s₄.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₄.mem, u₃.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  have k₂ : ∀ {d v}, (d + 4 ≤ 64 ∨ 68 ≤ d) → d + 4 ≤ 164 → s₁.mem.readW (off base d) 32 = v →
      s₂.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₂.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  refine ⟨k₁₂ (by decide) (k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide)
      (k₄ (by decide) (by decide) (k₂ (by decide) (by decide) v₁))))),
    k₁₂ (by decide) (k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide)
      (k₄ (by decide) (by decide) v₂)))),
    k₁₂ (by decide) (k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) (k₆ (by decide) (by decide) v₄))),
    k₁₂ (by decide) (k₁₀ (by decide) (by decide) (k₈ (by decide) (by decide) v₆)),
    k₁₂ (by decide) (k₁₀ (by decide) (by decide) v₈), k₁₂ (by decide) v₁₀, v₁₂, ?_, ?_, A⟩
  · exact (((((((((((m₁.rest _).trans (m₂.rest _)).trans (u₃.rest (by decide))).trans (m₄.rest _)).trans
      (u₅.rest (by decide))).trans (m₆.rest _)).trans (u₇.rest (by decide))).trans (m₈.rest _)).trans
      (u₉.rest (by decide))).trans (m₁₀.rest _)).trans (u₁₁.rest (by decide))).trans (m₁₂.rest _)
  · rw [m₁₂.mem, u₁₁.mem, m₁₀.mem, u₉.mem, m₈.mem, u₇.mem, m₆.mem, u₅.mem, m₄.mem, u₃.mem, m₂.mem, m₁.mem]
    exact (((((((outside_word (by decide) (by decide) (by omega_arith) _).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _))

/-- The arguments of verification at their fields. -/
theorem verifyArgs_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size)
    (hr : ArgsRead s 6) (ha : ArgsApart s base 6) :
    WP isa (.block (Entry.verifyArguments.flatMap Entry.saveArgument)) s fun t =>
      t.mem.readW (off base 64) 32 = s.gpr .r0 ∧ t.mem.readW (off base 100) 32 = s.gpr .r2 ∧
      t.mem.readW (off base 104) 32 = s.gpr .r3 ∧ t.mem.readW (off base 84) 32 = stackArg s 0 ∧
      t.mem.readW (off base 92) 32 = stackArg s 2 ∧ t.mem.readW (off base 108) 32 = stackArg s 3 ∧
      Rest [.r4] s t ∧ Outside base 64 48 s.mem t.mem ∧ ∀ i < 6, stackArg t i = stackArg s i := by
  have nw := hs.nowrap
  show WP isa (.block [.str .r0 .r12 64, .str .r2 .r12 100, .str .r3 .r12 104, .ldrSp .r4 (4 * 0), .str .r4 .r12 84,
    .ldrSp .r4 (4 * 2), .str .r4 .r12 92, .ldrSp .r4 (4 * 3), .str .r4 .r12 108]) s _
  refine wp_str12 hs (by decide) (by omega_arith) fun s₁ m₁ => ?_
  refine wp_str12 (hs.of_mupd m₁) (by decide) (by omega_arith) fun s₂ m₂ => ?_
  refine wp_str12 ((hs.of_mupd m₁).of_mupd m₂) (by decide) (by omega_arith) fun s₃ m₃ => ?_
  have a₃ := ((ha.mupd m₁).mupd m₂).mupd m₃
  have w₃ := ((hs.of_mupd m₁).of_mupd m₂).of_mupd m₃
  have r₃ : ArgsRead s₃ 6 := ((hr.keep m₁.rd m₁.wr m₁.sp).keep m₂.rd m₂.wr m₂.sp).keep m₃.rd m₃.wr m₃.sp
  have A₃ : ∀ i < 6, stackArg s₃ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₃ ((ha.mupd m₁).mupd m₂) hi (by decide), stackArg_mupd m₂ (ha.mupd m₁) hi (by decide),
      stackArg_mupd m₁ ha hi (by decide)]
  refine wp_ldrSp (by decide) (r₃ 0 (by decide)) fun s₄ u₄ => wp_str12 (w₃.of_upd u₄ (by decide)) (by decide)
    (by omega_arith) fun s₅ m₅ => ?_
  have a₅ := (a₃.upd u₄).mupd m₅
  have w₅ := (w₃.of_upd u₄ (by decide)).of_mupd m₅
  have r₅ : ArgsRead s₅ 6 := (r₃.keep u₄.rd u₄.wr u₄.sp).keep m₅.rd m₅.wr m₅.sp
  have A₅ : ∀ i < 6, stackArg s₅ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₅ (a₃.upd u₄) hi (by decide), stackArg_upd u₄, A₃ i hi]
  refine wp_ldrSp (by decide) (r₅ 2 (by decide)) fun s₆ u₆ => wp_str12 (w₅.of_upd u₆ (by decide)) (by decide)
    (by omega_arith) fun s₇ m₇ => ?_
  have a₇ := (a₅.upd u₆).mupd m₇
  have w₇ := (w₅.of_upd u₆ (by decide)).of_mupd m₇
  have r₇ : ArgsRead s₇ 6 := (r₅.keep u₆.rd u₆.wr u₆.sp).keep m₇.rd m₇.wr m₇.sp
  have A₇ : ∀ i < 6, stackArg s₇ i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₇ (a₅.upd u₆) hi (by decide), stackArg_upd u₆, A₅ i hi]
  refine wp_ldrSp (by decide) (r₇ 3 (by decide)) fun s₈ u₈ => wp_str12 (w₇.of_upd u₈ (by decide)) (by decide)
    (by omega_arith) fun t m₉ => WP.block_nil ?_
  have A : ∀ i < 6, stackArg t i = stackArg s i := fun i hi => by
    rw [stackArg_mupd m₉ (a₇.upd u₈) hi (by decide), stackArg_upd u₈, A₇ i hi]
  have v₁ : s₁.mem.readW (off base 64) 32 = s.gpr .r0 := by rw [m₁.mem]; exact readW_off_self _ _ _ _
  have v₂ : s₂.mem.readW (off base 100) 32 = s.gpr .r2 := by rw [m₂.mem, m₁.gpr]; exact readW_off_self _ _ _ _
  have v₃ : s₃.mem.readW (off base 104) 32 = s.gpr .r3 := by
    rw [m₃.mem, m₂.gpr, m₁.gpr]; exact readW_off_self _ _ _ _
  have v₅ : s₅.mem.readW (off base 84) 32 = stackArg s 0 := by
    rw [m₅.mem, u₄.gpr, A₃ 0 (by decide)]; exact readW_off_self _ _ _ _
  have v₇ : s₇.mem.readW (off base 92) 32 = stackArg s 2 := by
    rw [m₇.mem, u₆.gpr, A₅ 2 (by decide)]; exact readW_off_self _ _ _ _
  have v₉ : t.mem.readW (off base 108) 32 = stackArg s 3 := by
    rw [m₉.mem, u₈.gpr, A₇ 3 (by decide)]; exact readW_off_self _ _ _ _
  have k₉ : ∀ {d v}, (d + 4 ≤ 108 ∨ 112 ≤ d) → d + 4 ≤ 164 → s₇.mem.readW (off base d) 32 = v →
      t.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₉.mem, u₈.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  have k₇ : ∀ {d v}, (d + 4 ≤ 92 ∨ 96 ≤ d) → d + 4 ≤ 164 → s₅.mem.readW (off base d) 32 = v →
      s₇.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₇.mem, u₆.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  have k₅ : ∀ {d v}, (d + 4 ≤ 84 ∨ 88 ≤ d) → d + 4 ≤ 164 → s₃.mem.readW (off base d) 32 = v →
      s₅.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₅.mem, u₄.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  have k₃ : ∀ {d v}, (d + 4 ≤ 104 ∨ 108 ≤ d) → d + 4 ≤ 164 → s₂.mem.readW (off base d) 32 = v →
      s₃.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₃.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  have k₂ : ∀ {d v}, (d + 4 ≤ 100 ∨ 104 ≤ d) → d + 4 ≤ 164 → s₁.mem.readW (off base d) 32 = v →
      s₂.mem.readW (off base d) 32 = v :=
    fun hd hd' h => by rw [m₂.mem]; exact stored hd (by omega_arith) (by omega_arith) h _
  refine ⟨k₉ (by decide) (by decide) (k₇ (by decide) (by decide) (k₅ (by decide) (by decide)
      (k₃ (by decide) (by decide) (k₂ (by decide) (by decide) v₁)))),
    k₉ (by decide) (by decide) (k₇ (by decide) (by decide) (k₅ (by decide) (by decide) (k₃ (by decide) (by decide) v₂))),
    k₉ (by decide) (by decide) (k₇ (by decide) (by decide) (k₅ (by decide) (by decide) v₃)),
    k₉ (by decide) (by decide) (k₇ (by decide) (by decide) v₅), k₉ (by decide) (by decide) v₇, v₉, ?_, ?_, A⟩
  · exact (m₁.rest _).trans (m₂.rest _) |>.trans (m₃.rest _) |>.trans (u₄.rest (by decide)) |>.trans (m₅.rest _)
      |>.trans (u₆.rest (by decide)) |>.trans (m₇.rest _) |>.trans (u₈.rest (by decide)) |>.trans (m₉.rest _)
  · rw [m₉.mem, u₈.mem, m₇.mem, u₆.mem, m₅.mem, u₄.mem, m₃.mem, m₂.mem, m₁.mem]
    exact ((((((outside_word (by decide) (by decide) (by omega_arith) _).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _))

/-- The pointers to the key's components, each after the one before. -/
theorem keyPointers_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (hz : 164 ≤ size)
    {K PL QL : BitVec 32} (hK : s.mem.readW (off base 64) 32 = K) (hP : s.mem.readW (off base 100) 32 = PL)
    (hQ : s.mem.readW (off base 104) 32 = QL) :
    WP isa (.block Entry.keyPointers) s fun t =>
      t.mem.readW (off base 68) 32 = K + PL ∧ t.mem.readW (off base 72) 32 = K + PL + QL ∧
      t.mem.readW (off base 76) 32 = K + PL + QL + PL ∧ t.mem.readW (off base 80) 32 = K + PL + QL + PL + PL ∧
      Rest [.r4, .r5] s t ∧ Outside base 68 16 s.mem t.mem := by
  have nw := hs.nowrap
  show WP isa (.block [.ldr .r4 .r12 64, .ldr .r5 .r12 100, .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 68,
    .ldr .r5 .r12 104, .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 72,
    .ldr .r5 .r12 100, .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 76,
    .ldr .r5 .r12 100, .dp .add .r4 .r4 (.reg .r5), .str .r4 .r12 80]) s _
  refine wp_ldr12 hs (by decide) (by omega_arith) fun s₁ u₁ => ?_
  have w₁ := hs.of_upd u₁ (by decide)
  refine wp_ldr12 w₁ (by decide) (by omega_arith) fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  have w₃ := (w₁.of_upd u₂ (by decide)).of_upd u₃ (by decide)
  refine wp_str12 w₃ (by decide) (by omega_arith) fun s₄ m₄ => ?_
  have w₄ := w₃.of_mupd m₄
  -- Reads of words below 68 and at 100 and 104 are kept by the stores.
  have k₄ : ∀ d, (d + 4 ≤ 68 ∨ 72 ≤ d) → d + 4 ≤ 164 → s₄.mem.readW (off base d) 32 = s.mem.readW (off base d) 32 :=
    fun d hd hd' => by rw [m₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact readW_off_ne hd (by omega_arith) (by omega_arith) _
  refine wp_ldr12 w₄ (by decide) (by omega_arith) fun s₅ u₅ => wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  have w₆ := (w₄.of_upd u₅ (by decide)).of_upd u₆ (by decide)
  refine wp_str12 w₆ (by decide) (by omega_arith) fun s₇ m₇ => ?_
  have w₇ := w₆.of_mupd m₇
  have k₇ : ∀ d, (d + 4 ≤ 72 ∨ 76 ≤ d) → d + 4 ≤ 164 → s₇.mem.readW (off base d) 32 = s₄.mem.readW (off base d) 32 :=
    fun d hd hd' => by rw [m₇.mem, u₆.mem, u₅.mem]; exact readW_off_ne hd (by omega_arith) (by omega_arith) _
  refine wp_ldr12 w₇ (by decide) (by omega_arith) fun s₈ u₈ => wp_dp (op2_reg _ _) fun s₉ u₉ => ?_
  have w₉ := (w₇.of_upd u₈ (by decide)).of_upd u₉ (by decide)
  refine wp_str12 w₉ (by decide) (by omega_arith) fun s₁₀ m₁₀ => ?_
  have w₁₀ := w₉.of_mupd m₁₀
  have k₁₀ : ∀ d, (d + 4 ≤ 76 ∨ 80 ≤ d) → d + 4 ≤ 164 → s₁₀.mem.readW (off base d) 32 = s₇.mem.readW (off base d) 32 :=
    fun d hd hd' => by rw [m₁₀.mem, u₉.mem, u₈.mem]; exact readW_off_ne hd (by omega_arith) (by omega_arith) _
  refine wp_ldr12 w₁₀ (by decide) (by omega_arith) fun s₁₁ u₁₁ => wp_dp (op2_reg _ _) fun s₁₂ u₁₂ => ?_
  have w₁₂ := (w₁₀.of_upd u₁₁ (by decide)).of_upd u₁₂ (by decide)
  refine wp_str12 w₁₂ (by decide) (by omega_arith) fun t m₁₃ => WP.block_nil ?_
  have k₁₃ : ∀ d, (d + 4 ≤ 80 ∨ 84 ≤ d) → d + 4 ≤ 164 → t.mem.readW (off base d) 32 = s₁₀.mem.readW (off base d) 32 :=
    fun d hd hd' => by rw [m₁₃.mem, u₁₂.mem, u₁₁.mem]; exact readW_off_ne hd (by omega_arith) (by omega_arith) _
  have r4₃ : s₃.gpr .r4 = K + PL := by
    rw [u₃.gpr, dpVal, u₂.other .r4 (by decide), u₁.gpr, u₂.gpr]
    simp only [hdr]
    rw [u₁.mem, hK, hP]
  have r4₆ : s₆.gpr .r4 = K + PL + QL := by
    rw [u₆.gpr, dpVal, u₅.other .r4 (by decide), m₄.gpr, r4₃, u₅.gpr]
    simp only [hdr]
    rw [k₄ 104 (by decide) (by decide), hQ]
  have r4₉ : s₉.gpr .r4 = K + PL + QL + PL := by
    rw [u₉.gpr, dpVal, u₈.other .r4 (by decide), m₇.gpr, r4₆, u₈.gpr]
    simp only [hdr]
    rw [k₇ 100 (by decide) (by decide), k₄ 100 (by decide) (by decide), hP]
  have r4₁₂ : s₁₂.gpr .r4 = K + PL + QL + PL + PL := by
    rw [u₁₂.gpr, dpVal, u₁₁.other .r4 (by decide), m₁₀.gpr, r4₉, u₁₁.gpr]
    simp only [hdr]
    rw [k₁₀ 100 (by decide) (by decide), k₇ 100 (by decide) (by decide), k₄ 100 (by decide) (by decide), hP]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₁₃ 68 (by decide) (by decide), k₁₀ 68 (by decide) (by decide), k₇ 68 (by decide) (by decide), m₄.mem,
      r4₃]; exact readW_off_self _ _ _ _
  · rw [k₁₃ 72 (by decide) (by decide), k₁₀ 72 (by decide) (by decide), m₇.mem, r4₆]; exact readW_off_self _ _ _ _
  · rw [k₁₃ 76 (by decide) (by decide), m₁₀.mem, r4₉]; exact readW_off_self _ _ _ _
  · rw [m₁₃.mem, r4₁₂]; exact readW_off_self _ _ _ _
  · exact (u₁.rest (by decide)).trans (u₂.rest (by decide)) |>.trans (u₃.rest (by decide)) |>.trans (m₄.rest _)
      |>.trans (u₅.rest (by decide)) |>.trans (u₆.rest (by decide)) |>.trans (m₇.rest _) |>.trans (u₈.rest (by decide))
      |>.trans (u₉.rest (by decide)) |>.trans (m₁₀.rest _) |>.trans (u₁₁.rest (by decide)) |>.trans
      (u₁₂.rest (by decide)) |>.trans (m₁₃.rest _)
  · rw [m₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀.mem, u₉.mem, u₈.mem, m₇.mem, u₆.mem, u₅.mem, m₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact (((outside_word (by decide) (by decide) (by omega_arith) _).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)).trans (outside_word (by decide) (by decide) (by omega_arith) _)).trans
      (outside_word (by decide) (by decide) (by omega_arith) _)

end VG.Proof.Dsa.Arm
