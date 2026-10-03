import VerifiedGarbage.Proof.Argon2.Arm.Derive.FillPtr
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Argon2 on ARMv7: writing the new block

`writeWords_ok`: the words of G's output (at `r1`) to the current block (at
`r3`), XORed into the old ones after the first pass.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_ldr wp_str op2_reg)
open VG.Proof.Blake2.Arm.Stream (wp_eor)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.Arm (blk ofWords blk_of_words)
open VG.Proof.Sha512.Arm (A)
open VG.Impl.Argon2.Arm.Derive (writeWord)

/-- Words of the memory matrix. -/
abbrev mw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (A (memP s₀) o) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks22 : blocksN s₀ < 2 ^ 22 := by
  have hb := hp.blocks_lt
  omega

theorem mem_addr' {o : Nat} (ho : o < blocksN s₀ * 1024) : A (memP s₀) o = memB s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.mem_fits; omega)

/-- A word of the matrix after a store to another, or the same. -/
theorem mw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ blocksN s₀ * 1024) (hb : b + 4 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    mw s₀ (m.writeW (A (memP s₀) a) v) b = if a = b then v else mw s₀ m b := by
  have := blocks22 hp
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, mw, mw, mem_addr' hp (by omega), mem_addr' hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- The words of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : BitVec 32} (hsi : s.gpr .r1 = P) (hPfit : P.toNat + 1024 ≤ 2 ^ 32)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, State.addr P = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨State.addr P, 1024⟩ ⟨matrixCell (memB s₀) cur, 1024⟩)
    (hdi : s.gpr .r3 = memP s₀ + BitVec.ofNat 32 (cur * 1024)) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      Inv s₀ t ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 256, mw s₀ t.mem (cur * 1024 + 4 * i) = if i < n then
        (if xo then s.mem.readW (A P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i) else s.mem.readW (A P (4 * i)) 32)
        else mw s₀ s.mem (cur * 1024 + 4 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega)]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    have hb := blocks22 hp
    have hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((writeWords_ok h hc xo hsi hPfit hPw hPC hdi n (by omega)).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memB s₀) cur = memB s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    -- The source word is kept: only the current block has been written.
    have eP : A P (4 * n) = State.addr P + BitVec.ofNat 64 (4 * n) := addr_add (by omega_using [hPfit, hn])
    have sw_t : t.mem.readW (A P (4 * n)) 32 = s.mem.readW (A P (4 * n)) 32 := by
      rw [eP]
      refine ft.readW (r := ⟨State.addr P + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    have ea : State.addr (t.gpr .r1 + BitVec.ofNat 32 (4 * n)) = A P (4 * n) := by
      rw [gt _ (by decide) (by decide), hsi]
    have eb : State.addr (t.gpr .r3 + BitVec.ofNat 32 (4 * n)) = A (memP s₀) (cur * 1024 + 4 * n) := by
      rw [gt _ (by decide) (by decide), hdi, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    have b1 : cur * 1024 + 4 * n + 4 ≤ blocksN s₀ * 1024 := by omega_using [hc', hn]
    have b2 : cur * 1024 + 1024 < 2 ^ 64 := by omega_using [hc', hb]
    have inS : InRegions (t.rd ++ t.wr) (A P (4 * n)) 4 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 32 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 32; decide⟩
        · exact ⟨mem_mem hp, by show blocksN s₀ * 1024 ≤ 2 ^ 32; omega_using [hm]⟩
      rw [eP, bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [lR, hn])
        (by have := RW.2; omega_using [lR, hn, this])⟩
    have inMc : (memR s₀).Contains (A (memP s₀) (cur * 1024 + 4 * n)) 4 := by
      rw [mem_addr' hp (by omega_using [b1])]
      exact Offset.contains_base _ b1 (by omega_using [b1, hb])
    have inC : (⟨matrixCell (memB s₀) cur, 1024⟩ : Region).Contains (A (memP s₀) (cur * 1024 + 4 * n)) 4 := by
      rw [mem_addr' hp (by omega_using [b1]), cell]
      exact Offset.contains _ (by omega_using []) (by omega_using [hn]) b2
    have inM : ∀ u : State, Inv s₀ u → InRegions u.wr (A (memP s₀) (cur * 1024 + 4 * n)) 4 :=
      fun u iu => ⟨memR s₀, by rw [iu.wr]; exact mem_mem hp, inMc⟩
    -- The word.
    have fin : ∀ (v : BitVec 32) (u : State), u.mem = t.mem.writeW (A (memP s₀) (cur * 1024 + 4 * n)) v →
        u.rd = t.rd → u.wr = t.wr → u.sp = t.sp → (∀ r, r ≠ .r0 → r ≠ .r2 → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (A P (4 * n)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * n)
          else s.mem.readW (A P (4 * n)) 32) →
        Inv s₀ u ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 256, mw s₀ u.mem (cur * 1024 + 4 * i) = if i < n + 1 then
          (if xo then s.mem.readW (A P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i)
            else s.mem.readW (A P (4 * i)) 32)
          else mw s₀ s.mem (cur * 1024 + 4 * i) := fun v u hm hrd hwr hsp gu ev => by
      have fu : Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hm]; exact ft.writeW (List.mem_singleton_self _) v inC
      have iu : Inv s₀ u := it.step hsp (by rw [gu _ (by decide) (by decide), gt _ (by decide) (by decide)])
        hrd hwr (by rw [hm]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hm, mw_store hp _ b1 (by omega_using [hi, hc', hb]) (by omega_using []), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 4 * n = cur * 1024 + 4 * i by omega_using [e])]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega_using [c, e])]
    have o4 : 4 * n < 4096 := by omega_using [hn]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ldr o4 ea inS fun u₁ v₁ => ?_
      refine wp_str (a := A (memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₁.other .r3 (by decide)]; exact eb) (by rw [v₁.wr]; exact inM _ it)
        fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem, v₁.gpr]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (by rw [mu.sp, v₁.sp]) (fun r a b => by rw [mu.gpr, v₁.other r a, gt r a b]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ldr o4 ea inS fun u₁ v₁ => ?_
      refine wp_ldr (a := A (memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₁.other .r3 (by decide)]; exact eb)
        (by rw [v₁.rd, v₁.wr]; exact ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩)
        fun u₂ v₂ => wp_eor (op2_reg _ _) fun u₃ v₃ => ?_
      refine wp_str (a := A (memP s₀) (cur * 1024 + 4 * n)) o4 (by rw [v₃.other .r3 (by decide), v₂.other .r3 (by decide), v₁.other .r3 (by decide)]; exact eb)
        (by rw [v₃.wr, v₂.wr, v₁.wr]; exact inM _ it) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₃.mem, v₂.mem, v₁.mem, v₃.gpr]) (by rw [mu.rd, v₃.rd, v₂.rd, v₁.rd])
        (by rw [mu.wr, v₃.wr, v₂.wr, v₁.wr]) (by rw [mu.sp, v₃.sp, v₂.sp, v₁.sp])
        (fun r a b => by rw [mu.gpr, v₃.other r a, v₂.other r b, v₁.other r a, gt r a b]) ?_
      simp only [ite_true]
      rw [v₂.other .r0 (by decide), v₁.gpr, v₂.gpr, v₁.mem, sw_t, ← mw, wt n (by omega_using [hn]),
        ite_eq_right (show ¬n < n by omega_using [])]

end

end VG.Proof.Argon2.Arm.Derive
