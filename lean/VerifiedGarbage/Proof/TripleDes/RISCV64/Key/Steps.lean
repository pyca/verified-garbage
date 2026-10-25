module

public import VerifiedGarbage.Impl.TripleDes.RISCV64.ExpandKey
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Words
import VerifiedGarbage.Proof.TripleDes.RISCV64.Bytes
import VerifiedGarbage.Proof.TripleDes.RISCV64.Permutation
import VerifiedGarbage.Proof.TripleDes.KeySchedule
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

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
    (by decide) (by omega) hr) fun u₁ e₁ => ?_
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
    wp_addi (by omega) fun u₈ h₈ => WP.block_nil ?_
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

theorem Only.trans {rs : List Reg} {s s' s'' : State} (h : Only rs s s') (h' : Only rs s' s'') :
    Only rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem rotate28_ok (s : State) (r : Reg) (hr : r ≠ .t0)
    (x : BitVec 28) (hx : s.gpr r = x.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 28) :
    WP isa (.block (Impl.TripleDes.RISCV64.Key.rotate28 r n)) s fun s' =>
      s'.gpr r = (x.rotateLeft n).setWidth 64 ∧ Only [r, .t0] s s' := by
  simp only [Impl.TripleDes.RISCV64.Key.rotate28, mask, List.cons_append, List.nil_append]
  refine wp_srl (by omega) fun u₁ h₁ => wp_sll (by omega) fun u₂ h₂ => wp_xor fun u₃ h₃ =>
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
    refine wp_subi (by omega) fun u' h' => WP.block_nil (hrest u' ?_ ?_)
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
