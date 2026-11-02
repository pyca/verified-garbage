module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillInput
public import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.FillDep
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.MemoryInit
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Scratch
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Argon2.Contract

/-!
# Argon2 on RISC-V: writing the new block

`writeWords_ok`: the doublewords of a block (at `a1`: G's output, or a
lane's last block) to the current block (at `a3`), XORed into the old ones
after the first pass.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_add wp_sub wp_addi wp_subi wp_li wp_mv wp_ld wp_sd wp_xor)
open VG.Proof.Argon2.RISCV64 (wp_sll wp_srl wp_srlw wp_mul wp_mulhu wp_or wp_and wp_lwu wp_sw)

open VG.Impl.Argon2.RISCV64.Derive (writeWord)

/-- Doublewords of the memory matrix. -/
abbrev md (s₀ : State) (m : Mem) (o : Nat) : BitVec 64 := m.readW (memP s₀ + BitVec.ofNat 64 o) 64

theorem cell_get {s₀ : State} (m : Mem) (C : Nat) {j : Nat} (hj : j < 128) :
    (blockAt m (matrixCell (memP s₀) C))[j] = md s₀ m (C * 1024 + 8 * j) := by
  rw [blockAt_get _ _ hj, matrixCell, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A doubleword of the matrix after a store to another, or the same. -/
theorem md_store (m : Mem) {a b : Nat} (ha : a + 8 ≤ blocksN s₀ * 1024) (hb : b + 8 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 8 ≤ b ∨ b + 8 ≤ a) (v : BitVec 64) :
    md s₀ (m.writeW (memP s₀ + BitVec.ofNat 64 a) v) b = if a = b then v else md s₀ m b := by
  have := hp.mem_fits
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self64 _ _ _
  · rw [ite_eq_right e]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- The doublewords of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : Addr} (h4 : s.gpr .a1 = P) (hPa : P.toNat % 8 = 0)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, P = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨P, 1024⟩ ⟨matrixCell (memP s₀) cur, 1024⟩)
    (h6 : s.gpr .a3 = memP s₀ + BitVec.ofNat 64 (cur * 1024)) :
    ∀ n ≤ 128, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      Inv s₀ t ∧ (∀ r, r ≠ .a0 → r ≠ .a2 → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 128, md s₀ t.mem (cur * 1024 + 8 * i) = if i < n then
        (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * i)
          else s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64)
        else md s₀ s.mem (cur * 1024 + 8 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega)]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    have hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((writeWords_ok h hc xo h4 hPa hPw hPC h6 n (by omega)).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memP s₀) cur = memP s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    have b1 : cur * 1024 + 8 * n + 8 ≤ blocksN s₀ * 1024 := by omega
    -- The source doubleword is kept: only the current block has been written.
    have sw_t : t.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 = s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 := by
      refine ft.readW (r := ⟨P + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega))
    have ea : t.gpr .a1 + BitVec.ofNat 64 (8 * n) = P + BitVec.ofNat 64 (8 * n) := by
      rw [gt _ (by decide) (by decide), h4]
    have eb : t.gpr .a3 + BitVec.ofNat 64 (8 * n) = memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n) := by
      rw [gt _ (by decide) (by decide), h6, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have inS : InRegions (t.rd ++ t.wr) (P + BitVec.ofNat 64 (8 * n)) 8 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 64 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 64; decide⟩
        · exact ⟨mem_mem hp, Nat.le_trans (Nat.le_add_left _ _) hm⟩
      rw [bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega) (by have := RW.2; omega)⟩
    have inMc : (memR s₀).Contains (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 :=
      Offset.contains_base _ b1 (by omega)
    have inC : (⟨matrixCell (memP s₀) cur, 1024⟩ : Region).Contains
        (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 := by
      have bl := blocks_lt' hp
      rw [cell]
      exact Offset.contains (e := cur * 1024) (k := 1024) (d := cur * 1024 + 8 * n) (n := 8) _
        (Nat.le_add_right _ _) (by omega_using [hn]) (by omega_using [hc, bl])
    have inM : ∀ u : State, Inv s₀ u → InRegions u.wr (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) 8 :=
      fun u iu => ⟨memR s₀, by rw [iu.wr]; exact mem_mem hp, inMc⟩
    have o8 : 8 * n < 2048 := by omega
    have aP : (P + BitVec.ofNat 64 (8 * n)).toNat % 8 = 0 := Spill.al8 hPa (by omega)
    have aC : (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)).toNat % 8 = 0 :=
      Spill.al8 hp.mem_al (by omega)
    -- The doubleword.
    have fin : ∀ (v : BitVec 64) (u : State), u.mem = t.mem.writeW (memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) v →
        u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r, r ≠ .a0 → r ≠ .a2 → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * n)
          else s.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64) →
        Inv s₀ u ∧ (∀ r, r ≠ .a0 → r ≠ .a2 → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 128, md s₀ u.mem (cur * 1024 + 8 * i) = if i < n + 1 then
          (if xo then s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64 ^^^ md s₀ s.mem (cur * 1024 + 8 * i)
            else s.mem.readW (P + BitVec.ofNat 64 (8 * i)) 64)
          else md s₀ s.mem (cur * 1024 + 8 * i) := fun v u hmu hrd hwr hsp gu ev => by
      have fu : Frame [⟨matrixCell (memP s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hmu]; exact ft.writeW (List.mem_singleton_self _) v inC
      have iu : Inv s₀ u := it.step hsp (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        (fun r hr => by
          rw [gu r (by revert hr; revert r; decide) (by revert hr; revert r; decide),
            gt r (by revert hr; revert r; decide) (by revert hr; revert r; decide)])
        hrd hwr (by rw [hmu]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hmu, md_store hp _ b1 (by omega) (by omega), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 8 * n = cur * 1024 + 8 * i by omega)]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega)]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega)]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ld o8 ea aP inS fun u₁ v₁ => ?_
      refine wp_sd (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₁.other .a3 (by decide)]; exact eb) aC (by rw [v₁.wr]; exact inM _ it)
        fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem, v₁.gpr]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (by rw [mu.sp, v₁.sp]) (fun r a b => by rw [mu.gpr, v₁.other r a, gt r a b]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [← sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ld o8 ea aP inS fun u₁ v₁ => ?_
      refine wp_ld (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₁.other .a3 (by decide)]; exact eb) aC
        (by rw [v₁.rd, v₁.wr]; exact ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩)
        fun u₂ v₂ => wp_xor fun u₃ v₃ => ?_
      refine wp_sd (a := memP s₀ + BitVec.ofNat 64 (cur * 1024 + 8 * n)) o8 (by rw [v₃.other .a3 (by decide), v₂.other .a3 (by decide), v₁.other .a3 (by decide)]; exact eb) aC
        (by rw [v₃.wr, v₂.wr, v₁.wr]; exact inM _ it) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₃.mem, v₂.mem, v₁.mem, v₃.gpr]) (by rw [mu.rd, v₃.rd, v₂.rd, v₁.rd])
        (by rw [mu.wr, v₃.wr, v₂.wr, v₁.wr]) (by rw [mu.sp, v₃.sp, v₂.sp, v₁.sp])
        (fun r a b => by rw [mu.gpr, v₃.other r a, v₂.other r b, v₁.other r a, gt r a b]) ?_
      simp only [ite_true]
      rw [v₂.other .a0 (by decide), v₁.gpr, v₂.gpr, v₁.mem]
      change t.mem.readW (P + BitVec.ofNat 64 (8 * n)) 64 ^^^ md s₀ t.mem (cur * 1024 + 8 * n) = _
      rw [sw_t, wt n (by omega),
        ite_eq_right (show ¬n < n by omega)]

end

end VG.Proof.Argon2.RISCV64.Derive
