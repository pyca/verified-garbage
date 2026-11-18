module

public import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.TripleDes.KeyMemory
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.Loops
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.TripleDes.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.Permutation
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-! ### `TripleDes.RISCV64.Key.Steps`, which only this module used -/

section

/-! ### `TripleDes.RISCV64.Key.Words`, which only this module used -/

section

/-! # The key schedule's halves, with shifts -/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Key

/-- Two shifts keep the low `n` bits. -/
theorem mask_shift (y : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    (y <<< (64 - n)) >>> (64 - n) = (y.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hj,
    decide_true, Bool.true_and]
  by_cases h : j < n
  · simp (disch := omega) only [h, decide_true, show 64 - n + j < 64 by omega_using [hn, h],
      show ¬ 64 - n + j < 64 - n by omega_using [], decide_false, Bool.not_false, Bool.true_and,
      show 64 - n + j - (64 - n) = j by omega_using []]
  · simp only [h, decide_false, show ¬ 64 - n + j < 64 by omega_using [h], Bool.false_and]

/-- A rotation of a 28-bit half, as the code computes it. -/
theorem rot28_word (x : BitVec 28) (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    ((x.setWidth 64 <<< n ^^^ x.setWidth 64 >>> (28 - n)) <<< 36) >>> 36 =
      (x.rotateLeft n).setWidth 64 := by
  rw [show (36 : Nat) = 64 - 28 from rfl, mask_shift _ 28 (by decide)]
  apply congrArg (BitVec.setWidth 64)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hn']
  by_cases h : j < n
  · simp (disch := omega) [h, hj, show j < 64 by omega_using [hj], show 28 - n + j < 64 by omega_using [hj]]
  · simp (disch := omega) [h, hj, show j < 64 by omega_using [hj], show j - n < 64 by omega_using [hj],
      BitVec.getLsbD_of_ge]

/-- C and D joined, as the code computes it. -/
theorem pack28_word (c d : BitVec 28) :
    ((c.setWidth 64 <<< 28 ^^^ d.setWidth 64).setWidth 56) = c ++ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, hj, decide_true, Bool.true_and]
  by_cases h : j < 28
  · simp (disch := omega_arith) [h, show j < 64 by omega_using [hj]]
  · simp (disch := omega) [h, show j < 64 by omega_using [hj], show j - 28 < 64 by omega_using [hj],
      BitVec.getLsbD_of_ge]

end VG.Proof.TripleDes.RISCV64.Key

end

end


/-!
# The steps of key expansion

`load_ok`: a component key, through PC-1, into C (`a3`) and D (`a4`);
`rotation_ok`: the round's rotation of both; `storeRound_ok`: PC-2 of them
stored in the round's slot, and on to the next.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Key

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.RegUpd VG.RISCV64.ByteLoad
open VG.Impl.TripleDes.RISCV64 VG.Proof.TripleDes.RISCV64

/-- The registers key expansion keeps: its arguments. -/
def keyKept : List Reg := [.a0, .a1, .a2]

structure LoadPost (x : BitVec 56) (component : Nat) (s s' : State) : Prop where
  c : s'.gpr .a3 = ((x >>> 28).setWidth 28).setWidth 64
  d : s'.gpr .a4 = (x.setWidth 28).setWidth 64
  counter : s'.gpr .a6 = 0
  ptr : s'.gpr .a5 = s.gpr .a2 + BitVec.ofNat 64 (128 * component)
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r

theorem load_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset ≤ 16)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 offset) 8) :
    WP isa (.block (Impl.TripleDes.RISCV64.Key.load offset component)) s
      (LoadPost (Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .a0 + BitVec.ofNat 64 offset)))) component s) := by
  unfold Impl.TripleDes.RISCV64.Key.load
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadBE64_ok (d := .t0) (tmp := .t1) (n := .a0) (by decide) (by decide)
    (by decide) (by omega_using [ho]) hr) fun u₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  have hcode : permuteCode Spec.TripleDes.pc1 64 .t2 .t0 .t3 = instrs keyPermutation1.lit :=
    congrArg instrs keyPermutation1.lit_eq
  rw [hcode]
  obtain ⟨u₂, run₂, word₂, rd₂, wr₂, sp₂, mem₂, regs₂⟩ := fixedPermutation_ok Spec.TripleDes.pc1
    (by decide) (by decide) (by decide) .t0 .t2 _ keyPermutation1_check _
  have hkeep : ∀ r ∈ keyKept,
      ((instrs keyPermutation1.lit).all fun i => Straight.dst i != some r) = true := by
    decide +kernel
  refine WP.of_runBlock ⟨u₂, run₂, ?_⟩
  let x := Spec.TripleDes.permute Spec.TripleDes.pc1 (Spec.TripleDes.decodeBlock
    (Spec.TripleDes.blockAt s.mem (s.gpr .a0 + BitVec.ofNat 64 offset)))
  have hx : u₂.gpr .t2 = x.setWidth 64 := by
    rw [word₂, gpr_write_self, be64_decode]
    simp [x]
  have hk₂ : ∀ r ∈ keyKept, u₂.gpr r = s.gpr r := by
    intro r hr
    have h1 : r ≠ .t0 ∧ r ≠ .t1 := by revert hr; decide +revert
    rw [regs₂ r (hkeep r hr), gpr_write_of_ne _ _ h1.1, gpr_write_of_ne _ _ h1.2]
  simp only [List.cons_append, List.nil_append, mask]
  refine wp_srl (by decide) fun u₃ h₃ => wp_mv fun u₄ h₄ => wp_sll (by decide) fun u₅ h₅ =>
    wp_srl (by decide) fun u₆ h₆ => wp_li (imm := 0) (by decide) fun u₇ h₇ =>
    wp_addi (by omega_using [hc]) fun u₈ h₈ => WP.block_nil ?_
  have g : ∀ r, r ≠ .a3 → r ≠ .a4 → r ≠ .a6 → r ≠ .a5 → u₈.gpr r = u₂.gpr r := fun r a b c d => by
    rw [h₈.other r d, h₇.other r c, h₆.other r b, h₅.other r b, h₄.other r b, h₃.other r a]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₈.other _ (by decide), h₇.other _ (by decide), h₆.other _ (by decide),
      h₅.other _ (by decide), h₄.other _ (by decide), h₃.gpr, hx]
    exact VG.Proof.TripleDes.split28_upper x
  · rw [h₈.other _ (by decide), h₇.other _ (by decide), h₆.gpr, h₅.gpr, h₄.gpr,
      h₃.other _ (by decide), hx, show 64 - 28 = 36 from rfl, ← show 64 - 28 = 36 from rfl,
      mask_shift _ 28 (by decide), BitVec.setWidth_setWidth_of_le x (by decide : 28 ≤ 64)]
  · rw [h₈.other _ (by decide), h₇.gpr]; rfl
  · rw [h₈.gpr, h₇.other _ (by decide), h₆.other _ (by decide), h₅.other _ (by decide),
      h₄.other _ (by decide), h₃.other _ (by decide), hk₂ .a2 (by decide)]
  · rw [h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, mem₂]; rfl
  · rw [h₈.rd, h₇.rd, h₆.rd, h₅.rd, h₄.rd, h₃.rd, rd₂]; rfl
  · rw [h₈.wr, h₇.wr, h₆.wr, h₅.wr, h₄.wr, h₃.wr, wr₂]; rfl
  · rw [h₈.sp, h₇.sp, h₆.sp, h₅.sp, h₄.sp, h₃.sp, sp₂]; rfl
  · have h' : r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a6 ∧ r ≠ .a5 := by revert hr; decide +revert
    rw [g r h'.1 h'.2.1 h'.2.2.1 h'.2.2.2, hk₂ r hr]

/-- What a block that writes only some registers leaves. -/
structure Only (rs : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .t0)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (.block (Impl.TripleDes.RISCV64.Key.rotate28 r n)) s fun s' =>
      s'.gpr r = (x.rotateLeft n).setWidth 64 ∧ Only [r, .t0] s s' := by
  simp only [Impl.TripleDes.RISCV64.Key.rotate28, mask, List.cons_append, List.nil_append]
  refine wp_srl (by omega_using []) fun u₁ h₁ => wp_sll (by omega_using [hn']) fun u₂ h₂ => wp_xor fun u₃ h₃ =>
    wp_sll (by decide) fun u₄ h₄ => wp_srl (by decide) fun u₅ h₅ => WP.block_nil ?_
  refine ⟨?_, ⟨fun r' hr' => ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [h₅.gpr, h₄.gpr, h₃.gpr, h₂.gpr, h₂.other _ (Ne.symm hr), h₁.gpr, h₁.other _ hr, hx]
    exact rot28_word x n hn hn'
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [h₅.other _ hr'.1, h₄.other _ hr'.1, h₃.other _ hr'.1, h₂.other _ hr'.1, h₁.other _ hr'.2]
  · rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  · rw [h₅.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd]
  · rw [h₅.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr]
  · rw [h₅.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp]

structure RotatePost (c d : BitVec 28) (n : Nat) (s s' : State) : Prop where
  c : s'.gpr .a3 = (c.rotateLeft n).setWidth 64
  d : s'.gpr .a4 = (d.rotateLeft n).setWidth 64
  only : Only [.a3, .a4, .t0] s s'

theorem rotate_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .a3 = c.setWidth 64) (hd : s.gpr .a4 = d.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (Impl.TripleDes.RISCV64.Key.rotate n) s (RotatePost c d n s) := by
  rw [Impl.TripleDes.RISCV64.Key.rotate, WP.block_append_iff]
  refine WP.mono (rotate28_ok s .a3 (by decide) c hc n hn hn') fun s₁ ⟨c₁, o₁⟩ => ?_
  have d₁ : s₁.gpr .a4 = d.setWidth 64 := (o₁.reg .a4 (by decide)).trans hd
  refine WP.mono (rotate28_ok s₁ .a4 (by decide) d d₁ n hn hn') fun s₂ ⟨d₂, o₂⟩ => ?_
  refine ⟨(o₂.reg .a3 (by decide)).trans c₁, d₂, ?_⟩
  refine ⟨fun r hr => ?_, o₂.mem.trans o₁.mem, o₂.rd.trans o₁.rd, o₂.wr.trans o₁.wr,
    o₂.sp.trans o₁.sp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [o₂.reg r (by simp [hr.2.1, hr.2.2]), o₁.reg r (by simp [hr.1, hr.2.2])]

theorem comparison_values : ∀ j < 16, ∀ k < 16,
    ((BitVec.ofNat 64 j >>> 1) == (0 : BitVec 64)) = decide (j < 2) ∧
    ((BitVec.ofNat 64 j - BitVec.ofNat 64 k) == (0 : BitVec 64)) = decide (j = k) := by
  decide

theorem rotation_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .a3 = c.setWidth 64) (hd : s.gpr .a4 = d.setWidth 64)
    (hjreg : s.gpr .a6 = BitVec.ofNat 64 j) :
    WP isa Impl.TripleDes.RISCV64.Key.rotation s
      (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
  have hrot (s' : State) (h : Only [.t0] s s') (n : Nat) (hn : 1 ≤ n) (hn' : n < 28)
      (hv : Spec.TripleDes.rotations.getD j 0 = n) :
      WP isa (Impl.TripleDes.RISCV64.Key.rotate n) s'
        (RotatePost c d (Spec.TripleDes.rotations.getD j 0) s) := by
    apply WP.mono (rotate_ok s' c d ((h.reg .a3 (by simp)).trans hc)
      ((h.reg .a4 (by simp)).trans hd) n hn hn')
    intro t ht
    rw [hv]
    exact ⟨ht.c, ht.d, ⟨fun r hr => (ht.only.reg r hr).trans (h.reg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.2.2)),
      ht.only.mem.trans h.mem, ht.only.rd.trans h.rd, ht.only.wr.trans h.wr,
      ht.only.sp.trans h.sp⟩⟩
  have test (u : State) (hu : Only [.t0] s u) (k : Nat) (hk : k < 16) (rest : Prog isa)
      (P : State → Prop)
      (hrest : ∀ u', Only [.t0] s u' → isa.eval (.zero .t0) u' = some (decide (j = k)) →
        WP isa rest u' P) :
      WP isa (.seq (.block [.addi .t0 .a6 (-(k : Int))]) rest) u P := by
    apply WP.seq
    refine wp_subi (by omega_using [hk]) fun u' h' => WP.block_nil (hrest u' ?_ ?_)
    · exact ⟨fun r hr => (h'.other r (by simpa using hr)).trans (hu.reg r hr),
        h'.mem.trans hu.mem, h'.rd.trans hu.rd, h'.wr.trans hu.wr, h'.sp.trans hu.sp⟩
    · rw [eval_zero, h'.gpr, hu.reg .a6 (by simp), hjreg]
      exact congrArg some (comparison_values j hj k hk).2
  rw [Impl.TripleDes.RISCV64.Key.rotation]
  apply WP.seq
  refine wp_srl (by decide) fun s₁ h₁ => WP.block_nil ?_
  have o₁ : Only [.t0] s s₁ := ⟨fun r hr => h₁.other r (by simpa using hr), h₁.mem, h₁.rd,
    h₁.wr, h₁.sp⟩
  have cond₁ : isa.eval (.zero .t0) s₁ = some (decide (j < 2)) := by
    rw [eval_zero, h₁.gpr, hjreg]
    exact congrArg some (comparison_values j hj 0 (by decide)).1
  by_cases h2 : j < 2
  · apply WP.ite true (by simpa only [h2, decide_true] using cond₁)
    · intro _
      exact hrot s₁ o₁ 1 (by decide) (by decide)
        (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inl h2)])
    · simp
  · apply WP.ite false (by simpa only [h2, decide_false] using cond₁)
    · simp
    · intro _
      refine test s₁ o₁ 8 (by decide) _ _ fun s₂ o₂ cond₂ => ?_
      by_cases h8 : j = 8
      · apply WP.ite true (by simpa only [h8, decide_true] using cond₂)
        · intro _
          exact hrot s₂ o₂ 1 (by decide) (by decide)
            (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inl h8))])
        · simp
      · apply WP.ite false (by simpa only [h8, decide_false] using cond₂)
        · simp
        · intro _
          refine test s₂ o₂ 15 (by decide) _ _ fun s₃ o₃ cond₃ => ?_
          by_cases h15 : j = 15
          · apply WP.ite true (by simpa only [h15, decide_true] using cond₃)
            · intro _
              exact hrot s₃ o₃ 1 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_left (Or.inr (Or.inr h15))])
            · simp
          · apply WP.ite false (by simpa only [h15, decide_false] using cond₃)
            · simp
            · intro _
              exact hrot s₃ o₃ 2 (by decide) (by decide)
                (by rw [VG.Proof.TripleDes.rotation_value j hj, ite_eq_right (by
                  simp only [h2, h8, h15, or_self, not_false_eq_true])])

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 16) != 0) = decide (j ≠ 15) := by
  decide

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .a5)
    ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .a5 = s.gpr .a5 + 8
  counter : s'.gpr .a6 = BitVec.ofNat 64 (j + 1)
  flag : isa.eval (.nonzero .t0) s' = some (decide (j ≠ 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  reg : ∀ r ∈ (keyKept ++ [.a3, .a4]), s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .a3 = c.setWidth 64) (hd : s.gpr .a4 = d.setWidth 64)
    (hjreg : s.gpr .a6 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .a5) 8) :
    WP isa (.block Impl.TripleDes.RISCV64.Key.storeRound) s (StorePost c d j s) := by
  unfold Impl.TripleDes.RISCV64.Key.storeRound
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_sll (by decide) fun u₁ h₁ => wp_xor fun u₂ h₂ => ?_
  have hx : (u₂.gpr .t0).setWidth 56 = c ++ d := by
    rw [h₂.gpr, h₁.gpr, h₁.other .a4 (by decide), hc, hd]
    exact pack28_word c d
  rw [WP.block_append_iff]
  have hcode : permuteCode Spec.TripleDes.pc2 56 .t2 .t0 .t3 = instrs keyPermutation2.lit :=
    congrArg instrs keyPermutation2.lit_eq
  rw [hcode]
  obtain ⟨u₃, run₃, word₃, rd₃, wr₃, sp₃, mem₃, regs₃⟩ := fixedPermutation_ok Spec.TripleDes.pc2
    (by decide) (by decide) (by decide) .t0 .t2 _ keyPermutation2_check u₂
  have hkeep : ∀ r ∈ (keyKept ++ [.a3, .a4, .a5, .a6]),
      ((instrs keyPermutation2.lit).all fun i => Straight.dst i != some r) = true := by
    decide +kernel
  refine WP.of_runBlock ⟨u₃, run₃, ?_⟩
  have hk₃ : ∀ r ∈ (keyKept ++ [.a3, .a4, .a5, .a6]), u₃.gpr r = s.gpr r := by
    intro r hr
    have h' : r ≠ .t0 := by revert hr; decide +revert
    rw [regs₃ r (hkeep r hr), h₂.other _ h', h₁.other _ h']
  have hv : u₃.gpr .t2 = (Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64 := by
    rw [word₃, hx]
  rw [WP.block_append_iff]
  refine WP.mono (Words64.storeLE64_ok (v := .t2) (tmp := .t1) (tmp2 := .t4) (n := .a5) (off := 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by
      rw [wr₃, h₂.wr, h₁.wr, hk₃ .a5 (by decide), BitVec.add_zero]; exact hw))
    fun u₄ ⟨g₄, m₄, rd₄, wr₄, sp₄⟩ => ?_
  have hk₄ : ∀ r ∈ (keyKept ++ [.a3, .a4, .a5, .a6]), u₄.gpr r = s.gpr r := by
    intro r hr
    have h' : r ≠ .t1 ∧ r ≠ .t4 := by revert hr; decide +revert
    rw [g₄ r h'.1 h'.2, hk₃ r hr]
  refine wp_addi (by decide) fun u₅ h₅ => wp_addi (by decide) fun u₆ h₆ =>
    wp_subi (by decide) fun u₇ h₇ => WP.block_nil ?_
  have h6 : u₆.gpr .a6 = BitVec.ofNat 64 (j + 1) := by
    rw [h₆.gpr, h₅.other _ (by decide), hk₄ .a6 (by decide), hjreg]
    exact (nextRound_values j hj).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₇.mem, h₆.mem, h₅.mem, m₄, hv, BitVec.add_zero, mem₃, h₂.mem, h₁.mem,
      regs₃ .a5 (hkeep .a5 (by decide)), h₂.other _ (by decide), h₁.other _ (by decide)]
  · rw [h₇.other _ (by decide), h₆.other _ (by decide), h₅.gpr, hk₄ .a5 (by decide)]; rfl
  · rw [h₇.other _ (by decide), h6]
  · rw [eval_nonzero, h₇.gpr, h6]
    exact congrArg some (nextRound_values j hj).2
  · rw [h₇.rd, h₆.rd, h₅.rd, rd₄, rd₃, h₂.rd, h₁.rd]
  · rw [h₇.wr, h₆.wr, h₅.wr, wr₄, wr₃, h₂.wr, h₁.wr]
  · rw [h₇.sp, h₆.sp, h₅.sp, sp₄, sp₃, h₂.sp, h₁.sp]
  · have h' : r ≠ .t0 ∧ r ≠ .a6 ∧ r ≠ .a5 ∧ r ∈ (keyKept ++ [.a3, .a4, .a5, .a6]) := by
      revert hr; cases r <;> decide
    rw [h₇.other _ h'.1, h₆.other _ h'.2.1, h₅.other _ h'.2.2.1, hk₄ r h'.2.2.2]

end VG.Proof.TripleDes.RISCV64.Key

end

end

/-! ### `TripleDes.RISCV64.Key.Loop`, which only this module used -/

section

/-!
# One component's schedule

`loop_ok`: the sixteen rounds of a component key's expansion, storing the
round keys from `base` on; `component_ok`: with the key's load.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Key

open VG VG.RISCV64
open VG.Proof.TripleDes (keyPrefix keyInitial keyStep keyPrefix_succ)

structure LoopState (key : BitVec 64) (base : Addr) (origin : State) (j : Nat) (s : State) :
    Prop where
  c : s.gpr .a3 = (keyPrefix key j).1.setWidth 64
  d : s.gpr .a4 = (keyPrefix key j).2.1.setWidth 64
  counter : s.gpr .a6 = BitVec.ofNat 64 j
  pointer : s.gpr .a5 = base + BitVec.ofNat 64 (8 * j)
  keys : ∀ i < j, ∀ hi : i < 16, s.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 =
    ((keyPrefix key j).2.2[i]'hi).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [⟨base, 128⟩] origin.mem s.mem

def LoopInv (key : BitVec 64) (base : Addr) (origin : State) (n : Nat) (s : State) : Prop :=
  1 ≤ n ∧ n ≤ 16 ∧ LoopState key base origin (16 - n) s

theorem loopBody_ok (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (j : Nat) (hj : j < 16) (s : State) (hs : LoopState key base origin j s) :
    WP isa (.seq Impl.TripleDes.RISCV64.Key.rotation (.block Impl.TripleDes.RISCV64.Key.storeRound)) s
      (fun s' => isa.eval (.nonzero .t0) s' = some (decide (j ≠ 15)) ∧
        LoopState key base origin (j + 1) s') := by
  apply WP.seq
  apply WP.mono (rotation_ok s _ _ j hj hs.c hs.d hs.counter)
  intro s₁ h₁
  have reg₁ : ∀ r ∈ (keyKept ++ [.a6, .a5]), s₁.gpr r = s.gpr r := by
    intro r hr
    exact h₁.only.reg r (by revert hr; cases r <;> decide)
  have write₁ : InRegions s₁.wr (s₁.gpr .a5) 8 := by
    rw [h₁.only.wr, hs.wr, reg₁ .a5 (by decide), hs.pointer]
    exact hw j hj
  apply WP.mono (storeRound_ok s₁ _ _ j hj h₁.c h₁.d
    ((reg₁ .a6 (by decide)).trans hs.counter) write₁)
  intro s₂ h₂
  have hmem : s₂.mem = s.mem.writeW (base + BitVec.ofNat 64 (8 * j))
      ((Spec.TripleDes.permute Spec.TripleDes.pc2
        ((keyPrefix key j).1.rotateLeft (Spec.TripleDes.rotations.getD j 0) ++
          (keyPrefix key j).2.1.rotateLeft (Spec.TripleDes.rotations.getD j 0))).setWidth 64) := by
    rw [h₂.mem, h₁.only.mem, reg₁ .a5 (by decide), hs.pointer]
  refine ⟨h₂.flag, ⟨?_, ?_, h₂.counter, ?_, ?_, h₂.rd.trans (h₁.only.rd.trans hs.rd),
    h₂.wr.trans (h₁.only.wr.trans hs.wr), h₂.sp.trans (h₁.only.sp.trans hs.sp), ?_, ?_⟩⟩
  · rw [keyPrefix_succ]
    exact (h₂.reg .a3 (by decide)).trans h₁.c
  · rw [keyPrefix_succ]
    exact (h₂.reg .a4 (by decide)).trans h₁.d
  · rw [h₂.ptr, reg₁ .a5 (by decide), hs.pointer]
    change base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 8 = _
    rw [Offset.add_ofNat_add_ofNat]
    exact congrArg (fun n => base + BitVec.ofNat 64 n) (by omega_using [])
  · intro i hi hi16
    rw [hmem, keyPrefix_succ]
    by_cases he : i = j
    · subst i
      rw [Mem.readW_writeW_self64]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_self hj).symm
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega_using [hi, he])
        (by omega_using [hi16]) (by omega_using [hj])) (by decide), hs.keys i (by omega_using [hi, he]) hi16]
      exact congrArg (BitVec.setWidth 64) (Vector.getElem_set!_ne hi16 (Ne.symm he)).symm
  · intro r hr
    exact (h₂.reg r (by revert hr; cases r <;> decide)).trans
      ((reg₁ r (by revert hr; cases r <;> decide)).trans (hs.reg r hr))
  · rw [hmem]
    exact hs.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains_base base (by omega_using [hj]) (by omega_using [hj]))

theorem loopStep (key : BitVec 64) (base : Addr) (origin : State)
    (hw : ∀ j < 16, InRegions origin.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (n : Nat) (s : State) (hs : LoopInv key base origin n s) :
    WP isa (.seq Impl.TripleDes.RISCV64.Key.rotation (.block Impl.TripleDes.RISCV64.Key.storeRound)) s
      (fun s' => (isa.eval (.nonzero .t0) s' = some false ∧ LoopState key base origin 16 s') ∨
        (isa.eval (.nonzero .t0) s' = some true ∧ ∃ m < n, LoopInv key base origin m s')) := by
  apply WP.mono (loopBody_ok key base origin hw (16 - n) (by omega_using [hs.1]) s hs.2.2)
  intro s' h
  by_cases last : n = 1
  · left
    have idx : 16 - n = 15 := by omega_using [last]
    refine ⟨?_, ?_⟩
    · simpa only [idx, ne_eq, not_true_eq_false, decide_false] using h.1
    · simpa only [idx] using h.2
  · right
    have idx : ¬16 - n = 15 := by omega_using [hs.1, hs.2.1, last]
    refine ⟨?_, n - 1, by omega_using [hs.1], ?_⟩
    · simpa only [idx, ne_eq, not_false_eq_true, decide_true] using h.1
    · refine ⟨by omega_using [hs.1, last], by omega_using [hs.2.1], ?_⟩
      have eq : 16 - n + 1 = 16 - (n - 1) := by omega_using [hs.1, hs.2.1]
      rw [← eq]
      exact h.2

theorem loop_ok (key : BitVec 64) (base : Addr) (s : State)
    (hw : ∀ j < 16, InRegions s.wr (base + BitVec.ofNat 64 (8 * j)) 8)
    (hc : s.gpr .a3 = (keyInitial key).1.setWidth 64)
    (hd : s.gpr .a4 = (keyInitial key).2.1.setWidth 64)
    (hcount : s.gpr .a6 = 0) (hptr : s.gpr .a5 = base) :
    WP isa (.loop (.seq Impl.TripleDes.RISCV64.Key.rotation
      (.block Impl.TripleDes.RISCV64.Key.storeRound)) (.nonzero .t0)) s (LoopState key base s 16) := by
  apply WP.loop (M := isa) (body := .seq Impl.TripleDes.RISCV64.Key.rotation
      (.block Impl.TripleDes.RISCV64.Key.storeRound)) (c := .nonzero .t0)
    (Q := LoopState key base s 16) (LoopInv key base s) (loopStep key base s hw) 16 s
  refine ⟨by decide, by decide, hc, hd, hcount, ?_, ?_, rfl, rfl, rfl, fun _ _ => rfl,
    Frame.refl _ _⟩
  · exact hptr.trans (BitVec.add_zero base).symm
  · intro i hi
    omega

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) :
    Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset ≤ 16)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 offset) 8)
    (hw : ∀ j < 16, InRegions s.wr
      (s.gpr .a2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (Impl.TripleDes.RISCV64.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .a0 + BitVec.ofNat 64 offset))))
        (s.gpr .a2 + BitVec.ofNat 64 (128 * component)) s) := by
  rw [Impl.TripleDes.RISCV64.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hc ho hr)
  intro s₁ h₁
  have writes : ∀ j < 16, InRegions s₁.wr
      (s.gpr .a2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h₁.wr]; exact hw
  apply WP.mono (loop_ok _ _ s₁ writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.RISCV64.Key

end

end


/-!
# The three components

`body_ok`: key expansion writes the three components' schedules, the third
a copy of the first for a 16-byte key (`Components … 3`), and
`Components.schedule`: they are the expanded key.
-/

@[expose] public section

namespace VG.Proof.TripleDes.RISCV64.Key

open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.TripleDes (componentKeys componentOffset)

abbrev keyR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev outputR (s : State) : Region := ⟨s.gpr .a2, 384⟩

def slot (base : Addr) (c j : Nat) : Addr := base + BitVec.ofNat 64 (128 * c + 8 * j)

structure Components (origin s : State) (done : Nat) : Prop where
  keys : ∀ c < done, ∀ j < 16, s.mem.readW (slot (origin.gpr .a2) c j) 64 =
    ((componentKeys origin.mem (origin.gpr .a0) (origin.gpr .a1).toNat c).getD j 0).setWidth 64
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  reg : ∀ r ∈ keyKept, s.gpr r = origin.gpr r
  frame : Frame [outputR origin] origin.mem s.mem

structure Permissions (s : State) : Prop where
  reads : ∀ offset, offset + 8 ≤ (s.gpr .a1).toNat →
    InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 offset) 8
  writes : ∀ offset, offset + 8 ≤ 384 → InRegions s.wr (s.gpr .a2 + BitVec.ofNat 64 offset) 8
  keyOutput : (keyR s).Disjoint (outputR s)
  valid : Spec.TripleDes.validKey (s.gpr .a1).toNat

theorem componentStep_ok (origin s : State) (c : Nat) (hc : c < 3)
    (hp : Permissions origin) (hs : Components origin s c)
    (hoff : componentOffset (origin.gpr .a1).toNat c = 8 * c) :
    WP isa (Impl.TripleDes.RISCV64.Key.component (8 * c) c) s
      (Components origin · (c + 1)) := by
  have offsetBound := VG.Proof.TripleDes.componentOffset_bound _ c hp.valid hc
  rw [hoff] at offsetBound
  have read : InRegions (s.rd ++ s.wr) (s.gpr .a0 + BitVec.ofNat 64 (8 * c)) 8 := by
    rw [hs.rd, hs.wr, hs.reg .a0 (by decide)]
    exact hp.reads _ offsetBound
  have write : ∀ j < 16, InRegions s.wr
      (s.gpr .a2 + BitVec.ofNat 64 (128 * c) + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [hs.wr, hs.reg .a2 (by decide), Offset.add_ofNat_add_ofNat]
    exact hp.writes _ (by omega_using [hc, hj])
  apply WP.mono (component_ok s (8 * c) c hc (by omega_using [hc]) read write)
  intro t ht
  have frame : Frame [⟨origin.gpr .a2 + BitVec.ofNat 64 (128 * c), 128⟩] s.mem t.mem := by
    have hf := ht.frame
    rw [hs.reg .a2 (by decide)] at hf
    exact hf
  have key : Spec.TripleDes.blockAt s.mem (s.gpr .a0 + BitVec.ofNat 64 (8 * c)) =
      Spec.TripleDes.blockAt origin.mem (origin.gpr .a0 + BitVec.ofNat 64 (8 * c)) := by
    rw [hs.reg .a0 (by decide)]
    apply VG.Proof.TripleDes.blockAt_eq_of_frame _ hs.frame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hp.keyOutput.sub_left (Offset.sub_base _ offsetBound)
  refine ⟨?_, ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun r hr => (ht.reg r hr).trans (hs.reg r hr), hs.frame.trans (frame.sub ?_)⟩
  · intro k hk j hj
    by_cases he : k = c
    · subst k
      have h := ht.keys j hj
      rw [key, hs.reg .a2 (by decide), Offset.add_ofNat_add_ofNat] at h
      unfold componentKeys
      rw [hoff]
      exact h
    · have before : k < c := by omega_using [hk, he]
      have sep : (Region.mk (slot (origin.gpr .a2) k j) 8).Disjoint
          ⟨origin.gpr .a2 + BitVec.ofNat 64 (128 * c), 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [hk, hc, hj]) (by omega_using [hc])
      have hmem := frame.readW (a := slot (origin.gpr .a2) k j) (w := 64)
        (r := ⟨slot (origin.gpr .a2) k j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys k before j hj)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by omega_using [hc])⟩

theorem WP.and_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

theorem copyThird_ok (origin s : State) (hp : Permissions origin)
    (hs : Components origin s 2) (hn : (origin.gpr .a1).toNat = 16) :
    WP isa Impl.TripleDes.RISCV64.Key.copyThird s (Components origin · 3) := by
  have hB := hs.reg .a2 (by decide)
  rw [Impl.TripleDes.RISCV64.Key.copyThird]
  apply WP.seq
  refine wp_mv fun u₁ h₁ => wp_addi (by decide) fun u₂ h₂ => wp_li (imm := 128) (by decide)
    fun u₃ h₃ => WP.block_nil ?_
  have src₃ : u₃.gpr .t0 = origin.gpr .a2 := by
    rw [h₃.other _ (by decide), h₂.other _ (by decide), h₁.gpr, hB]
  have dst₃ : u₃.gpr .t1 = origin.gpr .a2 + BitVec.ofNat 64 256 := by
    rw [h₃.other _ (by decide), h₂.gpr, h₁.other _ (by decide), hB]
  have rd₃ : u₃.rd = origin.rd := by rw [h₃.rd, h₂.rd, h₁.rd, hs.rd]
  have wr₃ : u₃.wr = origin.wr := by rw [h₃.wr, h₂.wr, h₁.wr, hs.wr]
  have mem₃ : u₃.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  refine WP.mono (WP.and_sp (copyLoop_ok (tmp := .t3) (src := .t0) (dst := .t1) (cnt := .t2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) u₃ (N := 128)
    (by decide) (by decide) h₃.gpr (fun i hi => by
      rw [rd₃, wr₃, src₃]
      obtain ⟨r, hr, hc⟩ := CallLay.inRegions_sub (hp.writes (8 * (i / 8)) (by omega_using [hi]))
        (off := i % 8) (l := 1) (by omega_using []) (by decide)
      refine ⟨r, List.mem_append_right _ hr, ?_⟩
      rwa [Offset.add_ofNat_add_ofNat, show 8 * (i / 8) + i % 8 = i by omega_using []] at hc) (fun i hi => by
      rw [wr₃, dst₃, Offset.add_ofNat_add_ofNat]
      have h := CallLay.inRegions_sub (hp.writes (8 * ((256 + i) / 8)) (by omega_using [hi]))
        (off := (256 + i) % 8) (l := 1) (by omega_using []) (by decide)
      rwa [Offset.add_ofNat_add_ofNat, show 8 * ((256 + i) / 8) + (256 + i) % 8 = 256 + i by omega_using []]
        at h) (by
      rw [dst₃, src₃]
      exact fun x h₁ h₂ => Offset.sep (origin.gpr .a2) (d := 256) (n := 128) (e := 0) (k := 128)
        (by decide) (by decide) (by decide) x (by simpa using h₁) (by simpa using h₂))))
    fun t ⟨⟨hcopy, hframe, hkeep⟩, hsp⟩ => ?_
  rw [mem₃, dst₃, src₃] at hcopy
  rw [mem₃, dst₃] at hframe
  refine ⟨?_, hkeep.2.1.trans rd₃, hkeep.2.2.trans wr₃,
    hsp.trans (by rw [h₃.sp, h₂.sp, h₁.sp, hs.sp]), fun r hr => ?_,
    hs.frame.trans (hframe.sub ?_)⟩
  · intro c hc j hj
    by_cases he : c = 2
    · subst c
      have hRepeat : componentKeys origin.mem (origin.gpr .a0) (origin.gpr .a1).toNat 2 =
          componentKeys origin.mem (origin.gpr .a0) (origin.gpr .a1).toNat 0 := by
        rw [hn]; rfl
      rw [hRepeat]
      have first := hs.keys 0 (by decide) j hj
      refine Eq.trans (Bytes.dword_ext fun i hi => ?_) first
      rw [Bytes.readW64_byte _ _ hi, Bytes.readW64_byte _ _ hi]
      have h := hcopy (8 * j + i) (by omega_using [hj, hi])
      rw [Offset.add_ofNat_add_ofNat] at h
      simp only [slot, Offset.add_ofNat_add_ofNat]
      rw [show 128 * 2 + 8 * j + i = 256 + (8 * j + i) by omega_using [],
        show 128 * 0 + 8 * j + i = 8 * j + i by omega_using [], h]
    · have before : c < 2 := by omega_using [hc, he]
      have sep : (Region.mk (slot (origin.gpr .a2) c j) 8).Disjoint
          ⟨origin.gpr .a2 + BitVec.ofNat 64 256, 128⟩ :=
        Offset.disjoint _ (by omega_using [before, hj])
          (by omega_using [before, hj]) (by decide)
      have hmem := hframe.readW (a := slot (origin.gpr .a2) c j) (w := 64)
        (r := ⟨slot (origin.gpr .a2) c j, 8⟩)
        (Region.contains_self _ _) (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact sep)
        (by decide)
      exact hmem.trans (hs.keys c before j hj)
  · rw [hkeep.gpr (by revert hr; cases r <;> decide)]
    have h' : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2 := by revert hr; cases r <;> decide
    rw [h₃.other _ h'.2.2, h₂.other _ h'.2.1, h₁.other _ h'.1, hs.reg r hr]
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨outputR origin, by simp, Offset.sub_base _ (by decide)⟩

theorem Components.keep {origin s t : State} {n : Nat} (hs : Components origin s n)
    (ht : Only [.t0] s t) : Components origin t n :=
  ⟨fun c hc j hj => by rw [ht.mem]; exact hs.keys c hc j hj,
    ht.rd.trans hs.rd, ht.wr.trans hs.wr, ht.sp.trans hs.sp,
    fun r hr => (ht.reg r (by revert hr; cases r <;> decide)).trans (hs.reg r hr),
    by rw [ht.mem]; exact hs.frame⟩

theorem beq16_toNat (x : BitVec 64) : (x - BitVec.ofNat 64 16 == 0) = decide (x.toNat = 16) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor <;> intro h <;> bv_omega

theorem body_ok (origin s : State) (hp : Permissions origin) (hs : Components origin s 0) :
    WP isa Impl.TripleDes.RISCV64.Key.expandKey s (Components origin · 3) := by
  rw [Impl.TripleDes.RISCV64.Key.expandKey]
  apply WP.seq
  apply WP.mono (componentStep_ok origin s 0 (by decide) hp hs (by rfl))
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (componentStep_ok origin s₁ 1 (by decide) hp hs₁ (by rfl))
  intro s₂ hs₂
  apply WP.seq
  refine wp_subi (by decide) fun s₃ h₃ => WP.block_nil ?_
  have hs₃ := hs₂.keep ⟨fun r hr => h₃.other r (by simpa using hr), h₃.mem, h₃.rd, h₃.wr, h₃.sp⟩
  have flag : isa.eval (.zero .t0) s₃ = some (decide ((origin.gpr .a1).toNat = 16)) := by
    rw [eval_zero, h₃.gpr, hs₂.reg .a1 (by decide), beq16_toNat]
  by_cases h16 : (origin.gpr .a1).toNat = 16
  · apply WP.ite true (by simpa only [h16, decide_true] using flag)
    · intro _; exact copyThird_ok origin s₃ hp hs₃ h16
    · simp
  · apply WP.ite false (by simpa only [h16, decide_false] using flag)
    · simp
    · intro _
      exact componentStep_ok origin s₃ 2 (by decide) hp hs₃
        (by simp only [VG.Proof.TripleDes.componentOffset, h16, and_false, ite_false])

def componentIndex (i : Nat) : Nat := if i < 16 then 0 else if i < 32 then 1 else 2

theorem index_partition : ∀ i < 48, componentIndex i < 3 ∧ i % 16 < 16 ∧
    8 * i = 128 * componentIndex i + 8 * (i % 16) := by decide

theorem Components.schedule {origin s : State} (h : Components origin s 3) :
    Spec.TripleDes.scheduleAt s.mem (origin.gpr .a2) =
      VG.Proof.TripleDes.expandedMemory origin.mem (origin.gpr .a0) (origin.gpr .a1).toNat := by
  apply Vector.ext
  intro i hi
  have fact := index_partition i hi
  have keys := h.keys (componentIndex i) fact.1 (i % 16) fact.2.1
  rw [slot, ← fact.2.2] at keys
  rw [VG.Proof.TripleDes.scheduleAt_readW s.mem (origin.gpr .a2) i hi]
  simp only [VG.Proof.TripleDes.expandedMemory, Vector.getElem_ofFn]
  by_cases h16 : i < 16
  · simpa only [componentIndex, h16, ite_true] using keys
  · by_cases h32 : i < 32
    · simpa only [componentIndex, h16, h32, ite_false, ite_true] using keys
    · simpa only [componentIndex, h16, h32, ite_false] using keys

end VG.Proof.TripleDes.RISCV64.Key
