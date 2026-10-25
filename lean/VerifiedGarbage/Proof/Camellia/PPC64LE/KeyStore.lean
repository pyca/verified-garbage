module

public import VerifiedGarbage.Impl.Camellia.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Camellia.Common
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Camellia.PPC64LE.Keys
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Storing the subkeys on PPC64LE

The key schedule keeps the 64-bit halves of `KL`, `KR`, `KA` and `KB` as ECB
loads them: little-endian words of their big-endian bytes (`WordOf`), which
a byte reversal turns into the halves as numbers (`rev_of_wordOf`).

`storeSubkeys_ok`: with the halves of `KL`, `KR`, `KA` and `KB` in their
registers (`hiReg`, `loReg`), `storeSubkeys ks` stores each subkey of `ks`,
the half of a rotation (`rotHalf`), big-endian (`stdbrx`, indexed by
`r12`), at its word of the schedule at `r5`.
-/

@[expose] public section

namespace VG.Proof.Camellia.PPC64LE

open VG VG.PPC64LE VG.Impl.Camellia.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR)

/-! ## Halves as little-endian words -/

theorem rev64_bit (a : BitVec 64) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (rev64 a).getLsbD (56 - 8 * i + j) = a.getLsbD (8 * i + j) := by
  unfold rev64
  change BitVec.getLsbD (w := 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8) _ _ = _
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals (rw [decide_eq_true (by omega_arith), Bool.true_and]; congr 1; omega_arith)

/-- `rev` of such a word is the half. -/
theorem rev_of_wordOf {w h : BitVec 64} (hw : WordOf w h) : rev64 w = h := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have h1 := rev64_bit w (i := (63 - t) / 8) (j := t % 8) (by omega_arith) (by omega_arith)
  rw [show 56 - 8 * ((63 - t) / 8) + t % 8 = t by omega_arith] at h1
  rw [h1, hw _ (by omega_arith) _ (by omega_arith), Camellia.getLsbD_byteOf _ (by omega_arith) (by omega_arith)]
  congr 1; omega_arith

/-! ## Single instructions -/

theorem shift_ok (s : State) (left : Bool) (d n : Reg) {sh : Nat} (h : sh < 64) :
    ∃ s', runBlock isa [if left then .lsl d n sh else .lsr .d d n sh] s = some s' ∧
      s'.gpr d = (if left then s.gpr n <<< sh else s.gpr n >>> sh) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases left
  · exact ⟨s.write d (s.gpr n >>> sh), by
      simp only [Bool.false_eq_true, ↓reduceIte, runBlock_cons, exec_lsr_d h, runStep_some, runBlock_nil],
      RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩
  · exact ⟨s.write d (s.gpr n <<< sh), by
      simp only [↓reduceIte, runBlock_cons, exec_lsl h, runStep_some, runBlock_nil],
      RegUpd.gpr_write_self _ _ _, fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem orr_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [orR d n m] s = some s' ∧ s'.gpr d = s.gpr n ||| s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n ||| s.gpr m), by
    simp only [orR, runBlock_cons, runStep_some, runBlock_nil, exec_logic],
    RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `li r12, d; stdbrx t, n, r12`. -/
theorem strRev_ok (s : State) (t n : Reg) {d : Nat} (hd : d < 32768) (ht : t ≠ .r12) (hn : n ≠ .r12)
    (hn0 : n ≠ .r0) (hw : InRegions s.wr (s.gpr n + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.li .r12 d, .storeRev .d t n .r12] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr n + BitVec.ofNat 64 d) (rev64 (s.gpr t)) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .r12 (BitVec.ofNat 64 d)
  have hn₁ : s₁.gpr n = s.gpr n := RegUpd.gpr_write_of_ne _ _ hn
  have h12 : s₁.gpr .r12 = BitVec.ofNat 64 d := RegUpd.gpr_write_self _ _ _
  have hw' : InRegions s₁.wr (s₁.gpr n + s₁.gpr .r12) 8 := by rw [hn₁, h12]; exact hw
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr n + s₁.gpr .r12) (rev64 (s₁.gpr t)) }, ?_, ?_,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl⟩
  · simp only [runBlock_cons, exec_li hd, runStep_some]
    rw [exec_storeRev_d hn0 hw', runStep_some, runBlock_nil]
  · show Mem.writeW _ _ _ = _
    rw [hn₁, h12, RegUpd.gpr_write_of_ne _ _ ht]; rfl

/-! ## The subkeys -/

theorem hiReg_ne : ∀ v < 4, hiReg v ≠ t0 ∧ hiReg v ≠ t1 ∧ loReg v ≠ t0 ∧ loReg v ≠ t1 := by decide

theorem hiReg_ne12 : ∀ v < 4, hiReg v ≠ .r12 ∧ loReg v ≠ .r12 := by decide

/-- One subkey, stored byte-swapped at word `i` of `r5`. -/
theorem subkey_ok (s : State) {i v r : Nat} {hi : Bool} (hv : v < 4) (hi34 : i < 34)
    (hw : InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * i)) 8) :
    ∃ s', runBlock isa (subkey i v r hi) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r5 + BitVec.ofNat 64 (8 * i))
        (rev64 (Camellia.rotHalf (s.gpr (hiReg v)) (s.gpr (loReg v)) r hi)) ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → r' ≠ .r12 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨n1, n2, n3, n4⟩ := hiReg_ne v hv
  have hr3 : Reg.r5 ≠ t0 := by decide
  have hx1 : Reg.r5 ≠ t1 := by decide
  have hd : 8 * i % 8 = 0 ∧ 8 * i < 32768 := ⟨by omega_arith, by omega_arith⟩
  -- The two halves, `a` first.
  let a := if (r < 64) = (hi = true) then hiReg v else loReg v
  let b := if (r < 64) = (hi = true) then loReg v else hiReg v
  have ha : a ≠ t0 ∧ a ≠ t1 := by simp only [a]; split <;> exact ⟨by assumption, by assumption⟩
  have hb : b ≠ t0 ∧ b ≠ t1 := by simp only [b]; split <;> exact ⟨by assumption, by assumption⟩
  have hrot : Camellia.rotHalf (s.gpr (hiReg v)) (s.gpr (loReg v)) r hi =
      if r % 64 = 0 then s.gpr a else (s.gpr a <<< (r % 64)) ||| (s.gpr b >>> (64 - r % 64)) := by
    by_cases h64 : r < 64 <;> cases hi <;> simp [Camellia.rotHalf, a, b, h64]
  have hcode : subkey i v r hi =
      (if r % 64 = 0 then [movR t0 a] else [.lsl t0 a (r % 64), .lsr .d t1 b (64 - r % 64), orR t0 t0 t1]) ++
        ([Instr.li .r12 (8 * i), .storeRev .d t0 .r5 .r12] : List Instr) := by
    by_cases h64 : r < 64 <;> cases hi <;> simp [subkey, a, b, h64]
  by_cases h0 : r % 64 = 0
  · obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s t0 a
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := strRev_ok s₁ t0 .r5 hd.2 (by decide) (by decide) (by decide)
      (by rw [wr₁, o₁ _ hr3]; exact hw)
    refine ⟨s₃, by rw [hcode, ite_eq_left h0, runBlock_append', e₁, Option.bind_some, e₃], ?_, ?_, ?_, ?_⟩
    · rw [m₃, m₁, o₁ _ hr3, r₁, hrot, ite_eq_left h0]
    · intro r' h1 h2 h3; rw [g₃ _ h3, o₁ _ h1]
    · rw [rd₃, rd₁]
    · rw [wr₃, wr₁]
  · obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := shift_ok s true t0 a (sh := r % 64) (by omega_arith)
    obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := shift_ok s₁ false t1 b (sh := 64 - r % 64) (by omega_arith)
    obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := orr_ok s₂ t0 t0 t1
    have g₃ : ∀ r', r' ≠ t0 → r' ≠ t1 → s₃.gpr r' = s.gpr r' := fun r' h1 h2 => by
      rw [o₃ _ h1, o₂ _ h2, o₁ _ h1]
    obtain ⟨s₅, e₅, m₅, g₅, rd₅, wr₅⟩ := strRev_ok s₃ t0 .r5 hd.2 (by decide) (by decide) (by decide)
      (by rw [wr₃, wr₂, wr₁, g₃ _ hr3 hx1]; exact hw)
    refine ⟨s₅, by
      rw [hcode, ite_eq_right h0, show ([.lsl t0 a (r % 64), .lsr .d t1 b (64 - r % 64), orR t0 t0 t1] :
          List Instr) = [if true then .lsl t0 a (r % 64) else .lsr .d t0 a (r % 64)] ++
          ([if false then .lsl t1 b (64 - r % 64) else .lsr .d t1 b (64 - r % 64)] ++ [orR t0 t0 t1]) from rfl,
        runBlock_append', runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some, e₃,
        Option.bind_some, e₅], ?_, ?_, ?_, ?_⟩
    · have v0 : s₂.gpr t0 = s.gpr a <<< (r % 64) := by
        rw [o₂ _ (by decide : t0 ≠ t1), r₁]; rfl
      have v1 : s₂.gpr t1 = s.gpr b >>> (64 - r % 64) := by
        rw [r₂, o₁ _ hb.1]; rfl
      rw [m₅, m₃, m₂, m₁, g₃ _ hr3 hx1, r₃, v0, v1, hrot, ite_eq_right h0]
    · intro r' h1 h2 h3; rw [g₅ _ h3, g₃ _ h1 h2]
    · rw [rd₅, rd₃, rd₂, rd₁]
    · rw [wr₅, wr₃, wr₂, wr₁]

theorem q_ne_t (n : Nat) : q n ≠ t0 ∧ q n ≠ t1 ∧ q n ≠ .r12 := by
  unfold q; split <;> decide

theorem regs_ne_t (x : Nat) : hiReg x ≠ t0 ∧ hiReg x ≠ t1 ∧ loReg x ≠ t0 ∧ loReg x ≠ t1 :=
  ⟨(q_ne_t _).1, (q_ne_t _).2.1, (q_ne_t _).1, (q_ne_t _).2.1⟩

theorem regs_ne_12 (x : Nat) : hiReg x ≠ .r12 ∧ loReg x ≠ .r12 := ⟨(q_ne_t _).2.2, (q_ne_t _).2.2⟩

/-- Byte `j` of a byte-swapped word stored little-endian is byte `j` of the word, the most significant first. -/
theorem writeW_rev_byte (m : Mem) (a : Addr) (w : BitVec 64) {j : Nat} (hj : j < 8) :
    m.writeW a (rev64 w) (a + BitVec.ofNat 64 j) = Camellia.byteOf w j := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show j < 2 ^ 64 by omega_arith),
    show j < 64 / 8 by omega_arith, ite_true, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_extractLsb', Camellia.getLsbD_byteOf _ hj hk, show 8 * j + k = 8 * j + k from rfl]
  have := rev64_bit w (i := 7 - j) (j := k) (by omega_arith) hk
  rw [show 56 - 8 * (7 - j) + k = 8 * j + k by omega_arith] at this
  simp only [hk, decide_true, Bool.true_and, this]
  congr 1; omega_arith

/-- The subkey words `ks` from word `n` of `r5` on. -/
theorem storeSubkeys_ok (ks : List (Nat × Nat × Bool)) (hv : ∀ k ∈ ks, k.1 < 4) :
    ∀ (n : Nat) (s : State), (∀ i < ks.length, InRegions s.wr (s.gpr .r5 + BitVec.ofNat 64 (8 * (n + i))) 8) →
      n + ks.length ≤ 34 →
    ∃ s', runBlock isa ((ks.zipIdx n).flatMap fun ((v, r, hi), i) => subkey i v r hi) s = some s' ∧
      (∀ i < ks.length, ∀ j < 8,
        s'.mem (s.gpr .r5 + BitVec.ofNat 64 (8 * (n + i) + j)) =
          Camellia.byteOf (Camellia.rotHalf (s.gpr (hiReg (ks.getD i (0, 0, true)).1))
            (s.gpr (loReg (ks.getD i (0, 0, true)).1)) (ks.getD i (0, 0, true)).2.1
            (ks.getD i (0, 0, true)).2.2) j) ∧
      Frame [⟨s.gpr .r5 + BitVec.ofNat 64 (8 * n), 8 * ks.length⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → r' ≠ .r12 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction ks with
  | nil => intro n s _ _; exact ⟨s, rfl, fun i hi => by simp at hi, Frame.refl _ _, fun _ _ _ _ => rfl, rfl, rfl⟩
  | cons k ks ih =>
    intro n s hw hfit
    obtain ⟨v, r, hi⟩ := k
    have hv0 : v < 4 := hv _ List.mem_cons_self
    simp only [List.length_cons] at hfit
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := subkey_ok s (i := n) (r := r) (hi := hi) hv0 (by omega_arith)
      (by simpa using hw 0 (by simp))
    have hx2 : s₁.gpr .r5 = s.gpr .r5 := g₁ _ (by decide) (by decide) (by decide)
    obtain ⟨s', e', b', f', g', rd', wr'⟩ := ih (fun k hk => hv k (List.mem_cons_of_mem _ hk)) (n + 1) s₁
      (fun i hi => by
        rw [wr₁, hx2, show n + 1 + i = n + (i + 1) by omega_arith]
        exact hw (i + 1) (by simp; omega_arith)) (by omega_arith)
    refine ⟨s', by
      rw [List.zipIdx_cons, List.flatMap_cons, runBlock_append', e₁, Option.bind_some]; exact e',
      fun i hi j hj => ?_, ?_, fun r' h1 h2 h3 => by rw [g' r' h1 h2 h3, g₁ r' h1 h2 h3], by rw [rd', rd₁],
      by rw [wr', wr₁]⟩
    · cases i with
      | zero =>
        have hout : ∀ R ∈ [(⟨s₁.gpr .r5 + BitVec.ofNat 64 (8 * (n + 1)), 8 * ks.length⟩ : Region)],
            ¬ R.Contains (s.gpr .r5 + BitVec.ofNat 64 (8 * (n + 0) + j)) 1 := fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; rw [hx2]
          by_cases h0 : ks.length = 0
          · simp only [Region.Contains, h0]; omega_arith
          · exact not_contains_off _ (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith)
        rw [f' _ hout, m₁, Nat.add_zero, ← addr_add, writeW_rev_byte _ _ _ hj]
        simp only [List.getD_cons_zero]
      | succ i =>
        have := b' i (by simp at hi; omega_arith) j hj
        simp only [hx2, g₁ _ (regs_ne_t _).1 (regs_ne_t _).2.1 (regs_ne_12 _).1,
          g₁ _ (regs_ne_t _).2.2.1 (regs_ne_t _).2.2.2 (regs_ne_12 _).2] at this
        rw [show n + (i + 1) = n + 1 + i by omega_arith, this, List.getD_cons_succ]
    · have f₁ : Frame [⟨s.gpr .r5 + BitVec.ofNat 64 (8 * n), 8 * ((v, r, hi) :: ks).length⟩] s.mem s₁.mem := by
        rw [m₁]; exact frame_writeW _ (Region.sub_prefix (by simp only [List.length_cons]; omega_arith))
      refine f₁.trans (f'.sub fun R hR => ⟨_, List.mem_singleton_self _, ?_⟩)
      simp only [List.mem_singleton] at hR; subst hR
      rw [hx2]
      exact VG.Offset.sub _ (by omega_arith) (by simp; omega_arith)

end VG.Proof.Camellia.PPC64LE
