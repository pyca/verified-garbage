import VerifiedGarbage.Proof.Camellia.X86_64.KeyWords
import VerifiedGarbage.Proof.Camellia.X86_64.Group
import VerifiedGarbage.Proof.Camellia.KeySched
import VerifiedGarbage.Impl.Camellia.X86_64.ExpandKey

/-!
# Storing the subkeys on x86-64

`storeSubkeys_ok`: with the halves of `KL`, `KR`, `KA` and `KB` in their
registers (`hiReg`, `loReg`), `storeSubkeys ks` stores each subkey of `ks`,
the half of a rotation (`rotHalf`), big-endian, at its word of the
schedule at `rdx`.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR at_)

theorem shiftImm_ok (s : State) (op : ShiftOp) (hop : op = .shl ∨ op = .shr) (d : Reg) {n : Nat}
    (h1 : 1 ≤ n) (h2 : n ≤ 63) :
    ∃ s', runBlock isa [.shift op d n] s = some s' ∧
      s'.gpr d = (if op = .shl then s.gpr d <<< n else s.gpr d >>> n) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rcases hop with rfl | rfl
  · refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, h1, h2, and_self,
      ↓reduceIte]; rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg_self, ↓reduceIte]
    · intro r hr; simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]
    all_goals rfl
  · refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execShift, h1, h2, and_self,
      ↓reduceIte]; rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg_self, reduceCtorEq, ↓reduceIte]
    · intro r hr; simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]
    all_goals rfl

theorem orReg_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [.alu .or d (.reg r)] s = some s' ∧ s'.gpr d = s.gpr d ||| s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg_self]
  · intro r' hr; simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  all_goals rfl

theorem bswap_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.bswap d] s = some s' ∧ s'.gpr d = bswap64 (s.gpr d) ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec]; rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_setReg_self]
  · intro r' hr; simp only [RegUpd.gpr_setReg_of_ne _ _ hr]
  all_goals rfl

theorem storeAt_ok (s : State) (b : Reg) (d : Nat) (r : Reg)
    (hw : InRegions s.wr (s.gpr b + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.store (at_ b d) r] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr b + BitVec.ofNat 64 d) (s.gpr r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨{ s with mem := s.mem.writeW (s.gpr b + BitVec.ofNat 64 d) (s.gpr r) }, ?_, rfl, rfl, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, State.ea, ofInt_nat, hw,
    ite_true]

theorem hiReg_ne : ∀ v < 4, hiReg v ≠ t0 ∧ hiReg v ≠ t1 ∧ loReg v ≠ t0 ∧ loReg v ≠ t1 := by decide

/-- One subkey, stored byte-swapped at word `i` of `rdx`. -/
theorem subkey_ok (s : State) {i v r : Nat} {hi : Bool} (hv : v < 4)
    (hw : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8) :
    ∃ s', runBlock isa (subkey i v r hi) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rdx + BitVec.ofNat 64 (8 * i))
        (bswap64 (Camellia.rotHalf (s.gpr (hiReg v)) (s.gpr (loReg v)) r hi)) ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨n1, n2, n3, n4⟩ := hiReg_ne v hv
  have hrdx0 : Reg.rdx ≠ t0 := by decide
  have hrdx1 : Reg.rdx ≠ t1 := by decide
  -- The two halves, `a` first.
  let a := if (r < 64) = (hi = true) then hiReg v else loReg v
  let b := if (r < 64) = (hi = true) then loReg v else hiReg v
  have ha : a ≠ t0 ∧ a ≠ t1 := by simp only [a]; split <;> exact ⟨by assumption, by assumption⟩
  have hb : b ≠ t0 ∧ b ≠ t1 := by simp only [b]; split <;> exact ⟨by assumption, by assumption⟩
  have hrot : Camellia.rotHalf (s.gpr (hiReg v)) (s.gpr (loReg v)) r hi =
      if r % 64 = 0 then s.gpr a else (s.gpr a <<< (r % 64)) ||| (s.gpr b >>> (64 - r % 64)) := by
    by_cases h64 : r < 64 <;> cases hi <;> simp [Camellia.rotHalf, a, b, h64]
  have hcode : subkey i v r hi = [movR t0 a] ++
      ((if r % 64 = 0 then [] else [.shift .shl t0 (r % 64), movR t1 b, .shift .shr t1 (64 - r % 64),
        .alu .or t0 (.reg t1)]) ++ ([Instr.bswap t0] ++ [.store (at_ .rdx (8 * i)) t0])) := by
    by_cases h64 : r < 64 <;> cases hi <;> simp [subkey, a, b, h64]
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s t0 a
  by_cases h0 : r % 64 = 0
  · obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := bswap_ok s₁ t0
    obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeAt_ok s₂ .rdx (8 * i) t0
      (by rw [wr₂, wr₁, o₂ _ hrdx0, o₁ _ hrdx0]; exact hw)
    refine ⟨s₃, by rw [hcode, ite_eq_left h0, List.nil_append, runBlock_append', e₁, Option.bind_some,
      runBlock_append', e₂, Option.bind_some, e₃], ?_, ?_, ?_, ?_⟩
    · rw [m₃, m₂, m₁, o₂ _ hrdx0, o₁ _ hrdx0, r₂, r₁, hrot, ite_eq_left h0]
    · intro r' h1 h2; rw [g₃, o₂ _ h1, o₁ _ h1]
    · rw [rd₃, rd₂, rd₁]
    · rw [wr₃, wr₂, wr₁]
  · have hr1 : 1 ≤ r % 64 := by omega
    have hr2 : r % 64 ≤ 63 := by omega
    obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := shiftImm_ok s₁ .shl (Or.inl rfl) t0 hr1 hr2
    obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ t1 b
    obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := shiftImm_ok s₃ .shr (Or.inr rfl) t1
      (n := 64 - r % 64) (by omega) (by omega)
    obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := orReg_ok s₄ t0 t1
    obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := bswap_ok s₅ t0
    have g₆ : ∀ r', r' ≠ t0 → r' ≠ t1 → s₆.gpr r' = s.gpr r' := fun r' h1 h2 => by
      rw [o₆ _ h1, o₅ _ h1, o₄ _ h2, o₃ _ h2, o₂ _ h1, o₁ _ h1]
    obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := storeAt_ok s₆ .rdx (8 * i) t0
      (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, g₆ _ hrdx0 hrdx1]; exact hw)
    refine ⟨s₇, by
      rw [hcode, ite_eq_right h0, show ([Instr.shift .shl t0 (r % 64), movR t1 b, .shift .shr t1 (64 - r % 64),
          .alu .or t0 (.reg t1)] : List Instr) = [.shift .shl t0 (r % 64)] ++ ([movR t1 b] ++
          ([.shift .shr t1 (64 - r % 64)] ++ [.alu .or t0 (.reg t1)])) from rfl,
        runBlock_append', e₁, Option.bind_some, runBlock_append', runBlock_append', e₂, Option.bind_some,
        runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some, e₅, Option.bind_some,
        runBlock_append', e₆, Option.bind_some, e₇], ?_, ?_, ?_, ?_⟩
    · have v0 : s₄.gpr t0 = s.gpr a <<< (r % 64) := by
        rw [o₄ _ (by decide : t0 ≠ t1), o₃ _ (by decide : t0 ≠ t1), r₂, r₁]; rfl
      have v1 : s₄.gpr t1 = s.gpr b >>> (64 - r % 64) := by
        rw [r₄, r₃, o₂ _ hb.1, o₁ _ hb.1]; rfl
      rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁, g₆ _ hrdx0 hrdx1, r₆, r₅, v0, v1, hrot, ite_eq_right h0]
    · intro r' h1 h2; rw [g₇, g₆ _ h1 h2]
    · rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
    · rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]

theorem regs_ne_t (x : Nat) : hiReg x ≠ t0 ∧ hiReg x ≠ t1 ∧ loReg x ≠ t0 ∧ loReg x ≠ t1 := by
  unfold hiReg loReg; split <;> decide

/-- Byte `j` of a byte-swapped word stored little-endian is byte `j` of the word, the most significant first. -/
theorem writeW_bswap_byte (m : Mem) (a : Addr) (w : BitVec 64) {j : Nat} (hj : j < 8) :
    m.writeW a (bswap64 w) (a + BitVec.ofNat 64 j) = Camellia.byteOf w j := by
  simp only [Mem.writeW, Mem.write, Mem.sub_ofNat_toNat a (show j < 2 ^ 64 by omega),
    show j < 64 / 8 by omega, ite_true, BitVec.setWidth_eq]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [BitVec.getLsbD_extractLsb', Camellia.getLsbD_byteOf _ hj hk, show 8 * j + k = 8 * j + k from rfl]
  have := bswap64_bit w (i := 7 - j) (j := k) (by omega) hk
  rw [show 56 - 8 * (7 - j) + k = 8 * j + k by omega] at this
  simp only [hk, decide_true, Bool.true_and, this]
  congr 1; omega

/-- The subkey words `ks` from word `n` of `rdx` on. -/
theorem storeSubkeys_ok (ks : List (Nat × Nat × Bool)) (hv : ∀ k ∈ ks, k.1 < 4) :
    ∀ (n : Nat) (s : State), (∀ i < ks.length, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * (n + i))) 8) →
      8 * (n + ks.length) < 2 ^ 64 →
    ∃ s', runBlock isa ((ks.zipIdx n).flatMap fun ((v, r, hi), i) => subkey i v r hi) s = some s' ∧
      (∀ i < ks.length, ∀ j < 8,
        s'.mem (s.gpr .rdx + BitVec.ofNat 64 (8 * (n + i) + j)) =
          Camellia.byteOf (Camellia.rotHalf (s.gpr (hiReg (ks.getD i (0, 0, true)).1))
            (s.gpr (loReg (ks.getD i (0, 0, true)).1)) (ks.getD i (0, 0, true)).2.1
            (ks.getD i (0, 0, true)).2.2) j) ∧
      Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (8 * n), 8 * ks.length⟩] s.mem s'.mem ∧
      (∀ r', r' ≠ t0 → r' ≠ t1 → s'.gpr r' = s.gpr r') ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  induction ks with
  | nil => intro n s _ _; exact ⟨s, rfl, fun i hi => by simp at hi, Frame.refl _ _, fun _ _ _ => rfl, rfl, rfl⟩
  | cons k ks ih =>
    intro n s hw hfit
    obtain ⟨v, r, hi⟩ := k
    have hv0 : v < 4 := hv _ List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := subkey_ok s (i := n) (r := r) (hi := hi) hv0
      (by simpa using hw 0 (by simp))
    have hrdx : s₁.gpr .rdx = s.gpr .rdx := g₁ _ (by decide) (by decide)
    obtain ⟨s', e', b', f', g', rd', wr'⟩ := ih (fun k hk => hv k (List.mem_cons_of_mem _ hk)) (n + 1) s₁
      (fun i hi => by
        rw [wr₁, hrdx, show n + 1 + i = n + (i + 1) by omega]
        exact hw (i + 1) (by simp; omega)) (by simp at hfit; omega)
    refine ⟨s', by
      rw [List.zipIdx_cons, List.flatMap_cons, runBlock_append', e₁, Option.bind_some]; exact e',
      fun i hi j hj => ?_, ?_, fun r' h1 h2 => by rw [g' r' h1 h2, g₁ r' h1 h2], by rw [rd', rd₁],
      by rw [wr', wr₁]⟩
    · have hfit' : 8 * (n + (ks.length + 1)) < 2 ^ 64 := by simpa using hfit
      cases i with
      | zero =>
        have hout : ∀ R ∈ [(⟨s₁.gpr .rdx + BitVec.ofNat 64 (8 * (n + 1)), 8 * ks.length⟩ : Region)],
            ¬ R.Contains (s.gpr .rdx + BitVec.ofNat 64 (8 * (n + 0) + j)) 1 := fun R hR => by
          simp only [List.mem_singleton] at hR; subst hR; rw [hrdx]
          by_cases h0 : ks.length = 0
          · simp only [Region.Contains, h0]; omega
          · exact not_contains_off _ (Or.inl (by omega)) (by omega) (by omega) (by omega)
        rw [f' _ hout, m₁, Nat.add_zero, ← addr_add, writeW_bswap_byte _ _ _ hj]
        simp only [List.getD_cons_zero]
      | succ i =>
        have := b' i (by simp at hi; omega) j hj
        simp only [hrdx, g₁ _ (regs_ne_t _).1 (regs_ne_t _).2.1, g₁ _ (regs_ne_t _).2.2.1 (regs_ne_t _).2.2.2] at this
        rw [show n + (i + 1) = n + 1 + i by omega, this, List.getD_cons_succ]
    · have hfit' : 8 * (n + (ks.length + 1)) < 2 ^ 64 := by simpa using hfit
      have f₁ : Frame [⟨s.gpr .rdx + BitVec.ofNat 64 (8 * n), 8 * ((v, r, hi) :: ks).length⟩] s.mem s₁.mem := by
        rw [m₁]; exact frame_writeW _ (Region.sub_prefix (by simp; omega))
      refine f₁.trans (f'.sub fun R hR => ⟨_, List.mem_singleton_self _, ?_⟩)
      simp only [List.mem_singleton] at hR; subst hR
      rw [hrdx]
      exact VG.Offset.sub _ (by omega) (by simp; omega)

end VG.Proof.Camellia.X86_64
