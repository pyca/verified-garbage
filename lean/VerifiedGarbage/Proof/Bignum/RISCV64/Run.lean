module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words

/-!
# Multiword arithmetic on RISC-V: running blocks

The working space is `size` bytes at `base` (`Scr`), writable, not wrapping
around, and with `base` a multiple of 8, so that its doublewords at offsets
that are multiples of 8 are aligned; a number of `k` words at byte offset
`d` of it is `wordsVal m base d k` (`Proof/Mont/Words.lean`).

* `brun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), with the state a chain of `State.write`s and memory
  updates, read through with `RegUpd.gpr_write` (an `if`, decided for
  literal registers), so that a register of the result is the value last
  written to it, as PPC64LE's `prun` does. A block lemma takes the accesses
  it makes as hypotheses (`Scr.ld`, `Scr.st`, `Scr.al`) on the addresses `off
  base d`, to which `off_add` brings a pointer plus an offset.
* `count_loop`, `wp_countdown`: a loop on a counter that its body
  decrements.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont

/-! ## The working space -/

/-- The working space: `size` bytes at `base`, within a writable region, not
wrapping around, `base` a multiple of 8. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  wr : ∃ B₀ : Addr, ∃ o L : Nat, (⟨B₀, L⟩ : Region) ∈ s.wr ∧ base = off B₀ o ∧ o + size ≤ L ∧ L ≤ 2 ^ 64
  nowrap : base.toNat + size ≤ 2 ^ 64
  al : base.toNat % 8 = 0

/-- A writable region is a working space. -/
theorem Scr.of_mem {s : State} {base : Addr} {size : Nat} (h : (⟨base, size⟩ : Region) ∈ s.wr)
    (hn : base.toNat + size ≤ 2 ^ 64) (ha : base.toNat % 8 = 0) : Scr s base size :=
  ⟨⟨base, 0, size, h, by simp [off], by omega, by omega⟩, hn, ha⟩

theorem Scr.region {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : ∃ r ∈ s.wr, r.Contains (off base d) n := by
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, _, _⟩ := hs
  refine ⟨_, hm, ?_⟩
  rw [hb, show off (off B₀ o) d = off B₀ (o + d) by simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
  exact Offset.contains_base B₀ (by omega) (by omega)

theorem Scr.ld {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) (hn : 0 < n := by decide) : InRegions (s.rd ++ s.wr) (off base d) n :=
  let ⟨_, hm, hc⟩ := hs.region hd hn
  ⟨_, List.mem_append_right _ hm, hc⟩

theorem Scr.st {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (hd : d + n ≤ size) (hn : 0 < n := by decide) : InRegions s.wr (off base d) n :=
  let ⟨_, hm, hc⟩ := hs.region hd hn
  ⟨_, hm, hc⟩

/-- A doubleword of the working space at an offset that is a multiple of 8 is
aligned. -/
theorem Scr.al8 {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) (h8 : d % 8 = 0) : (off base d).toNat % 8 = 0 := by
  have hn := hs.nowrap
  have ha := hs.al
  have e : (off base d).toNat = base.toNat + d := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [e]
  omega

theorem Scr.congr {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h : s'.wr = s.wr) : Scr s' base size :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, h ▸ hm, hb, hL, hL'⟩, hs.nowrap, hs.al⟩

/-! ## Addresses -/

/-- A pointer into the working space plus an offset. -/
theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- A pointer into the working space less an offset. -/
theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) : off p a - BitVec.ofNat 64 b = off p (a - b) := by
  simp only [off]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## Frames of what a block keeps -/

namespace Keep

theorem trans' {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs s₂ s₃) :
    Keep rs s₁ s₃ :=
  (h₁.trans h₂).mono fun r h => by simpa using h

/-- A write keeps every other register. -/
theorem write (s : State) (d : Reg) (v : BitVec 64) : Keep [d] s (s.write d v) :=
  ⟨fun r hr => ite_eq_right_iff.mpr fun h => absurd h fun h' => hr (by simp [h']), rfl, rfl⟩

/-- A store keeps every register. -/
theorem mem (s : State) (m : Mem) : Keep [] s { s with mem := m } := ⟨fun _ _ => rfl, rfl, rfl⟩

end Keep

theorem gpr_mem (s : State) (m : Mem) : ({ s with mem := m } : State).gpr = s.gpr := rfl
theorem mem_mem (s : State) (m : Mem) : ({ s with mem := m } : State).mem = m := rfl
theorem rd_mem (s : State) (m : Mem) : ({ s with mem := m } : State).rd = s.rd := rfl
theorem wr_mem (s : State) (m : Mem) : ({ s with mem := m } : State).wr = s.wr := rfl
theorem sp_mem (s : State) (m : Mem) : ({ s with mem := m } : State).sp = s.sp := rfl

/-! ## Loops -/

theorem ne_zero_iff (x : BitVec 64) : (x != 0) = decide (x.toNat ≠ 0) := by
  have e : x = 0 ↔ x.toNat = 0 :=
    ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩
  by_cases h : x.toNat = 0
  · have : x = 0 := e.mpr h
    subst this; rfl
  · have : x ≠ 0 := fun h' => h (e.mp h')
    simpa [h] using this

/-- A do-while loop on a register not being zero that runs its body `n > 0`
times: the register is not zero exactly until the last iteration. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ ((s'.gpr cr).toNat ≠ 0 ↔ k + 1 ≠ n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero cr) s' = some (decide (k + 1 ≠ n)) := by
    rw [Steps.eval_nonzero, ne_zero_iff]
    exact congrArg some (decide_eq_decide.mpr hc)
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-- A do-while loop whose body decrements `cnt`, from `N > 0`: it runs `N`
times. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 64) (hN0 : 0 < N)
    (Inv : Nat → State → Prop)
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 64 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1)
    {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 64 N) :
    WP isa (.loop body (.nonzero cnt)) s (Inv N) := by
  refine WP.mono (count_loop (cr := cnt) hN0 (fun k s => Inv k s ∧ s.gpr cnt = BitVec.ofNat 64 (N - k))
    (fun k hk s ⟨hI, hc⟩ => WP.mono (hbody k hk s hI hc) fun s' ⟨hI', hc'⟩ => ⟨⟨hI', ?_⟩, ?_⟩)
    ⟨h0, by rw [hc, Nat.sub_zero]⟩) fun _ h => h.1
  · rw [hc', hc]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [hc', hc, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-! ## Running a block -/

/-- `addi` of a numeral below 2048, as an `Int` literal. -/
theorem exec_addi_lit {s : State} {d n : Reg} {m : Nat} (h : m < 2048) :
    exec (.addi d n (OfNat.ofNat m : Int)) s = some (s.write d (s.gpr n + BitVec.ofNat 64 m)) :=
  exec_addi_nat h

/-- `addi` of `-1`. -/
theorem exec_addi_m1 {s : State} {d n : Reg} :
    exec (.addi d n (-1)) s = some (s.write d (s.gpr n - 1)) :=
  exec_addi_neg_nat (m := 1) (by decide)

/-- `brun`: symbolic execution of a block by `simp` (see the module doc),
with extra lemmas (the block's accesses, …). -/
tactic_template "brun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp only [runBlock_cons, runStep_some, runBlock_nil,
                         exec_load_b, exec_load_d, exec_store_b, exec_store_d, exec_add, exec_sub,
                         exec_sltu, exec_mul, exec_mulhu, exec_logic, ↓exec_li_nat, ↓exec_addi_nat,
                         ↓exec_addi_neg_nat, exec_shift_d, exec_logicImm,
                         gpr_write, mem_write, rd_write, wr_write, sp_write, gpr_mem, mem_mem,
                         rd_mem, wr_mem, sp_mem, off_add, Nat.add_zero, Option.some.injEq,
                         exists_eq_left', ite_true, ite_false, reduceCtorEq, ↓reduceIte, ne_eq,
                         not_false_eq_true, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reduceLeDiff,
                         Nat.reduceAdd, Nat.reducePow, Nat.reduceEqDiff, implies_true, true_implies, and_self,
                         true_and, and_true, List.cons_append, List.nil_append, imm12, Int.reduceLE,
                         Int.reduceLT, Int.reduceNeg, $ls,*]))

/-- Reading the registers and memory of a state built by writes. -/
tactic_template "gsimp" : tactic => `(tactic| (
                       set_option linter.unusedSimpArgs false in
                       simp only [gpr_write, mem_write, rd_write, wr_write,
                         sp_write, gpr_mem, mem_mem, rd_mem, wr_mem, sp_mem, ite_true,
                         ite_false, reduceCtorEq, ↓reduceIte]))

/-- `brun []`. -/
tactic_template "brun" : tactic => `(tactic| brun [])

end VG.Proof.Bignum.RISCV64
