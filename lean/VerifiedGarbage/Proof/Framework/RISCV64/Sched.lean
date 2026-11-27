module

public import VerifiedGarbage.Impl.Words.RISCV64.Sched
public import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd

/-!
# RISC-V: reordered straight-line code

Untrusted: everything here is checked by Lean. Independent instructions
(`Impl/Words/RISCV64/Sched.lean`) commute (`indep_comm`), so code in another
order, `sched ks c`, runs as `c` (`run_sched`, `WP.sched`), whatever `ks` is.
-/

@[expose] public section

namespace VG.RISCV64

open VG VG.Interleave VG.Impl.Words.RISCV64

/-! ## Bits -/

theorem ctorIdx_inj {a b : Reg} (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← Reg.ofNat_ctorIdx a, h, Reg.ofNat_ctorIdx]

theorem testBit_rbit (r q : Reg) : (rbit r).testBit q.ctorIdx = decide (q = r) := by
  rw [rbit, Nat.testBit_two_pow]
  by_cases h : q = r
  · subst h; simp
  · simp only [h, decide_false, decide_eq_false_iff_not]
    exact fun e => h (ctorIdx_inj e.symm)

/-- A register of one set is not in the other. -/
theorem ne_of_and {a b : Nat} (h : a &&& b = 0) {i : Nat} (ha : a.testBit i = true) : b.testBit i = false := by
  have := congrArg (Nat.testBit · i) h
  simpa [Nat.testBit_and, ha] using this

/-! ## What an instruction does -/

/-- The states agree on the registers of `m`, and on what they may access. -/
structure Agree (m : Nat) (s t : State) : Prop where
  gpr : ∀ r : Reg, m.testBit r.ctorIdx = true → s.gpr r = t.gpr r
  rd : s.rd = t.rd
  wr : s.wr = t.wr

/-- What an instruction that writes a register does. -/
structure RegI (i : Instr) (f : Fp) (d : Reg) (v : State → Option (BitVec 64)) : Prop where
  w : f.w = rbit d
  base : f.k = 1 → f.r.testBit f.n = true
  run : ∀ s, exec i s = (v s).map (s.write d)
  same : ∀ s t, Agree f.r s t → (f.k = 1 → ∀ n : Reg, n.ctorIdx = f.n →
    s.mem.read (s.gpr n + BitVec.ofNat 64 f.off) 8 = t.mem.read (t.gpr n + BitVec.ofNat 64 f.off) 8) → v s = v t

/-- `v` is what the instruction writes to `d`, whatever it is. -/
theorem regI_of {i : Instr} {f : Fp} {d : Reg} (w : f.w = rbit d) (hk : f.k = 0)
    (run : ∀ s, exec i s = ((exec i s).map (·.gpr d)).map (s.write d))
    (same : ∀ s t, Agree f.r s t → (f.k = 1 → ∀ n : Reg, n.ctorIdx = f.n →
      s.mem.read (s.gpr n + BitVec.ofNat 64 f.off) 8 = t.mem.read (t.gpr n + BitVec.ofNat 64 f.off) 8) →
      (exec i s).map (·.gpr d) = (exec i t).map (·.gpr d)) : ∃ d v, RegI i f d v :=
  ⟨d, _, w, fun h => absurd (hk.symm.trans h) (by decide), run, same⟩

theorem exec_alu {i : Instr} {f : Fp} (hf : fp i = some f) (hk : f.k ≠ 2) : ∃ d v, RegI i f d v := by
  cases i
  case load wd t n off =>
    cases wd <;> simp only [fp, reduceCtorEq, Option.some.injEq] at hf
    subst hf
    refine ⟨t, fun s => (addr s 8 n off).bind fun a => s.load a 8, rfl, fun _ => by simp [testBit_rbit], fun s => ?_, fun s u h hm => ?_⟩
    · simp only [exec, Width.bytes, BitVec.setWidth_eq, Option.map_bind]
      rfl
    · have hn := h.gpr n (by simp [testBit_rbit])
      have hm := hm rfl n rfl
      simp only [addr, State.load, hn, h.rd, h.wr] at hm ⊢
      split
      · simp only [Option.bind_some, hm]
      · rfl
  case store wd t n off =>
    cases wd <;> simp only [fp, reduceCtorEq, Option.some.injEq] at hf
    subst hf; exact absurd rfl hk
  case shift op sz d n sh =>
    simp only [fp, Option.some.injEq] at hf
    subst hf
    refine regI_of rfl rfl (fun s => ?_) fun s u h _ => ?_
    · cases sz <;> simp only [exec] <;> split <;> simp [RegUpd.gpr_write_self]
    · have hn := h.gpr n (by simp [testBit_rbit])
      cases sz <;> simp only [exec, hn] <;> split <;> simp [RegUpd.gpr_write_self]
  case addi d n imm | addiw d n imm | logicImm _ d n imm =>
    simp only [fp, Option.some.injEq] at hf
    subst hf
    refine regI_of rfl rfl (fun s => ?_) fun s u h _ => ?_
    · simp only [exec]; split <;> simp [RegUpd.gpr_write_self]
    · have hn := h.gpr n (by simp [testBit_rbit])
      simp only [exec, hn]; split <;> simp [RegUpd.gpr_write_self]
  case li d imm =>
    simp only [fp, Option.some.injEq] at hf
    subst hf
    refine regI_of rfl rfl (fun s => ?_) fun s u h _ => ?_
    · simp only [exec]; split <;> simp [RegUpd.gpr_write_self]
    · simp only [exec]; split <;> simp [RegUpd.gpr_write_self]
  all_goals simp only [fp, reduceCtorEq, Option.some.injEq] at hf
  all_goals subst hf
  case lui d imm => exact regI_of rfl rfl (fun s => by simp [exec, RegUpd.gpr_write_self]) fun s u h _ => by simp [exec, RegUpd.gpr_write_self]
  all_goals
    refine regI_of rfl rfl (fun s => by simp [exec, RegUpd.gpr_write_self]) fun s u h _ => ?_
    simp only [exec, Option.map_some, RegUpd.gpr_write_self]
    rw [h.gpr _ (by simp only [Nat.testBit_or, testBit_rbit, decide_true, Bool.true_or]),
      h.gpr _ (by simp only [Nat.testBit_or, testBit_rbit, decide_true, Bool.or_true])]

/-- What a store does. -/
theorem exec_st {i : Instr} {f : Fp} (hf : fp i = some f) (hk : f.k = 2) :
    ∃ (t n : Reg) (off : Nat), f = ⟨0, rbit n ||| rbit t, 2, n.ctorIdx, off⟩ ∧ i = .store .d t n off := by
  cases i
  case store wd t n off =>
    cases wd <;> simp only [fp, reduceCtorEq, Option.some.injEq] at hf
    exact ⟨t, n, off, hf.symm, rfl⟩
  case load wd t n off =>
    cases wd <;> simp only [fp, reduceCtorEq, Option.some.injEq] at hf
    subst hf; simp at hk
  all_goals simp only [fp, reduceCtorEq, Option.some.injEq] at hf
  all_goals subst hf; simp at hk

/-! ## Independent instructions commute -/

theorem write_comm {s : State} {d e : Reg} (h : d ≠ e) (a b : BitVec 64) :
    (s.write d a).write e b = (s.write e b).write d a := by
  unfold State.write
  congr 1
  funext r
  by_cases h1 : r = d <;> by_cases h2 : r = e <;> simp_all

/-- Writing a register an instruction does not read changes nothing for it. -/
theorem RegI.write {j : Instr} {g : Fp} {e : Reg} {w : State → Option (BitVec 64)} (hj : RegI j g e w) {d : Reg}
    (hd : g.r.testBit d.ctorIdx = false) (s : State) (x : BitVec 64) : w (s.write d x) = w s := by
  obtain n : ∀ r : Reg, g.r.testBit r.ctorIdx = true → (s.write d x).gpr r = s.gpr r := fun r hr =>
    RegUpd.gpr_write_of_ne _ _ fun c => by rw [c, hd] at hr; exact absurd hr (by decide)
  exact hj.same _ _ ⟨n, rfl, rfl⟩ fun hk r hr => by rw [n r (hr ▸ hj.base hk), RegUpd.mem_write]

theorem comm_reg {i j : Instr} {f g : Fp} {d e : Reg} {v w : State → Option (BitVec 64)} (hi : RegI i f d v)
    (hj : RegI j g e w) (h : indep f g = true) (s : State) : (exec i s).bind (exec j) = (exec j s).bind (exec i) := by
  simp only [indep, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, -⟩ := h
  obtain hd : f.w.testBit d.ctorIdx = true := by rw [hi.w, testBit_rbit]; simp
  obtain he : g.w.testBit e.ctorIdx = true := by rw [hj.w, testBit_rbit]; simp
  obtain n1 := ne_of_and h1 hd
  obtain n2 := ne_of_and h2 he
  rw [Nat.testBit_or, Bool.or_eq_false_iff] at n1
  obtain hde : d ≠ e := fun c => by rw [c, he] at n1; exact absurd n1.2 (by decide)
  obtain a1 := hj.write n1.1 s
  obtain a2 := hi.write n2 s
  rw [hi.run, hj.run]
  cases hv : v s with
  | none =>
    cases hw : w s with
    | none => rfl
    | some y => simp [hi.run, a2, hv]
  | some x =>
    cases hw : w s with
    | none => simp [hj.run, a1, hw]
    | some y => simp [hi.run, hj.run, a1, a2, hv, hw, write_comm hde]

theorem sepOff_sep {a b : Nat} (h : sepOff a b = true) (p : Addr) :
    VG.Mem.Sep (p + BitVec.ofNat 64 a) 8 (p + BitVec.ofNat 64 b) 8 := by
  simp only [sepOff, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq] at h
  exact Offset.sep p (d := a) (n := 8) (e := b) (k := 8) (by omega_using [h]) (by omega_using [h]) (by omega_using [h])

/-- The store's address is not affected by writing a register it does not read. -/
theorem exec_store_write {t n : Reg} {off : Nat} {s : State} {d : Reg} (x : BitVec 64) (hn : n ≠ d) (ht : t ≠ d) :
    exec (.store .d t n off) (s.write d x) = (exec (.store .d t n off) s).map (·.write d x) := by
  simp only [exec, addr, State.store, RegUpd.gpr_write_of_ne _ _ hn, RegUpd.gpr_write_of_ne _ _ ht]
  split
  · simp only [Option.bind_some, show (s.write d x).wr = s.wr from rfl]
    split <;> rfl
  · rfl

theorem comm_store {t n : Reg} {off : Nat} {j : Instr} {g : Fp} {e : Reg} {w : State → Option (BitVec 64)}
    (hj : RegI j g e w) (h : indep ⟨0, rbit n ||| rbit t, 2, n.ctorIdx, off⟩ g = true) (s : State) :
    (exec (.store .d t n off) s).bind (exec j) = (exec j s).bind (exec (.store .d t n off)) := by
  simp only [indep, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨-, h2⟩, h3⟩ := h
  obtain he : g.w.testBit e.ctorIdx = true := by rw [hj.w, testBit_rbit]; simp
  obtain n2 := ne_of_and h2 he
  simp only [Nat.testBit_or, testBit_rbit, Bool.or_eq_false_iff, decide_eq_false_iff_not] at n2
  -- The store keeps what `j` reads.
  obtain a1 : ∀ s', exec (.store .d t n off) s = some s' → w s' = w s := fun s' hs => by
    simp only [exec, addr, Width.bytes] at hs
    split at hs
    · simp only [Option.bind_some, State.store] at hs
      split at hs
      · simp only [Option.some.injEq] at hs
        subst hs
        refine hj.same _ _ ⟨fun _ _ => rfl, rfl, rfl⟩ fun hk1 r hr => ?_
        simp only [memOk, hk1, Nat.reduceAdd, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h3
        obtain h3 | ⟨⟨-, hb⟩, hs⟩ := h3
        · exact absurd h3 (by decide)
        · obtain rfl : n = r := ctorIdx_inj (hb.trans hr.symm)
          exact VG.Mem.read_write_sep (fun x h1 h2 => sepOff_sep hs _ x h2 h1) (by decide)
      · cases hs
    · cases hs
  rw [hj.run]
  cases hw : w s with
  | none =>
    cases hs : exec (.store .d t n off) s with
    | none => rfl
    | some s' => simp [hj.run, a1 s' hs, hw]
  | some y =>
    simp only [Option.map_some, Option.bind_some, exec_store_write y (Ne.symm n2.1) (Ne.symm n2.2)]
    cases hs : exec (.store .d t n off) s with
    | none => rfl
    | some s' => simp [hj.run, a1 s' hs, hw]

theorem indep_symm {a b : Fp} (h : indep a b = true) : indep b a = true := by
  simp only [indep, memOk, sepOff, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.ble_eq] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Nat.and_or_distrib_left, Nat.or_eq_zero_iff]
    rw [Nat.and_or_distrib_left, Nat.or_eq_zero_iff] at h1
    exact ⟨h2, by rw [Nat.and_comm]; exact h1.2⟩
  · rw [Nat.and_or_distrib_left, Nat.or_eq_zero_iff] at h1
    exact h1.1
  · simp only [Nat.add_comm b.k, eq_comm (a := b.n)]
    rcases h3 with h3 | ⟨h3, h4 | h4⟩
    · exact .inl h3
    · exact .inr ⟨h3, .inr h4⟩
    · exact .inr ⟨h3, .inl h4⟩

/-- Independent instructions commute. -/
theorem indep_comm {i j : Instr} {f g : Fp} (hi : fp i = some f) (hj : fp j = some g) (h : indep f g = true) :
    CommuteOn isa (fun _ => True) i j := fun s _ => by
  by_cases ki : f.k = 2 <;> by_cases kj : g.k = 2
  · simp [indep, memOk, ki, kj] at h
  · obtain ⟨t, n, off, rfl, rfl⟩ := exec_st hi ki
    obtain ⟨e, w, hw⟩ := exec_alu hj kj
    exact comm_store hw h s
  · obtain ⟨t, n, off, rfl, rfl⟩ := exec_st hj kj
    obtain ⟨e, w, hw⟩ := exec_alu hi ki
    exact (comm_store hw (indep_symm h) s).symm
  · obtain ⟨d, v, hv⟩ := exec_alu hi ki
    obtain ⟨e, w, hw⟩ := exec_alu hj kj
    exact comm_reg hv hw h s

/-! ## Reordered code -/

theorem passes_comm {i : Instr} {f : Fp} (hi : fp i = some f) : ∀ {l : List Instr},
    passes f (l.map fun i => (fp i, i)) = true → ∀ x ∈ l, CommuteOn isa (fun _ => True) x i
  | [], _ => fun _ h => absurd h List.not_mem_nil
  | y :: l, h => by
    intro x hx
    rw [List.map_cons] at h
    cases hy : fp y with
    | none => rw [hy] at h; exact absurd h (by simp [passes])
    | some g =>
      rw [hy, passes, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact indep_comm hy hi h.1
      · exact passes_comm hi h.2 x hx

theorem run_move {i : Instr} {a b : List Instr} (h : ∀ x ∈ a, CommuteOn isa (fun _ => True) x i) (s : State) :
    runBlock isa (i :: (a ++ b)) s = runBlock isa (a ++ i :: b) s := by
  rw [runBlock_append]
  show (exec i s).bind (runBlock isa (a ++ b)) = _
  obtain c := comm_block (M := isa) (P := fun _ => True) (y := i) (a := a)
    (fun x hx => ⟨fun _ _ _ _ => trivial, h x hx⟩) (s := s) trivial
  rw [show runBlock isa (a ++ b) = fun u => (runBlock isa a u).bind (runBlock isa b) from
    funext (runBlock_append (M := isa) a b), ← Option.bind_assoc]
  show ((isa.exec i s).bind (runBlock isa a)).bind _ = _
  rw [c, Option.bind_assoc]
  rfl

theorem run_sched : ∀ (ks : List Nat) (c : List Instr) (s : State),
    runBlock isa (schedGo ks (c.map fun i => (fp i, i))) s = runBlock isa c s
  | [], c, s => by simp only [schedGo, List.map_map, Function.comp_def, List.map_id']
  | k :: ks, c, s => by
    obtain base : (c.map fun i => (fp i, i)).map (·.2) = c := by
      simp only [List.map_map, Function.comp_def, List.map_id']
    rw [schedGo, ← List.map_drop, ← List.map_take]
    cases hd : c.drop k with
    | nil => simp [base]
    | cons x rest =>
      simp only [List.map_cons]
      cases hf : fp x with
      | none => simp only [base]
      | some f =>
        simp only
        cases hp : passes f ((c.take k).map fun i => (fp i, i)) with
        | false => simp only [base]
        | true =>
          simp only
          rw [← List.map_append]
          conv => rhs; rw [← List.take_append_drop k c, hd, ← run_move (passes_comm hf hp)]
          show (isa.exec x s).bind _ = (isa.exec x s).bind _
          exact congrArg _ (funext (run_sched ks _))

/-- Reordered code does what the code does. -/
theorem WP.sched {ks : List Nat} {c : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block c) s Q) :
    WP isa (.block (sched ks c)) s Q := by
  obtain ⟨s', h', hq⟩ := runBlock_of_WP h
  exact WP.of_runBlock ⟨s', by rw [Impl.Words.RISCV64.sched, run_sched]; exact h', hq⟩

end VG.RISCV64
