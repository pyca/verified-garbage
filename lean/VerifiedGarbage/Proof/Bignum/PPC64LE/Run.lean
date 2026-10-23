module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
public import VerifiedGarbage.Proof.Mont.Words32
public meta import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Multiword arithmetic on PPC64LE: running blocks

The working space is `size` bytes at `base` (`Scr`), writable and not
wrapping around; a number of `k` 32-bit digits at byte offset `d` of it is
`val32 m base d k` (`Proof/Mont/Words32.lean`).

* `prun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), with the state a chain of `State.write`s and memory
  updates, read through with `gpr_write` (an `if`, decided for literal
  registers), so that a register of the result is the value last written to
  it. A block lemma takes the accesses it makes as hypotheses (`Scr.ld`,
  `Scr.st`) on the addresses `off base d`, to which `off_add` brings a
  pointer plus an offset.
* `WP.keep`: the registers no instruction of the code writes are kept
  (`writesOnly`, checked by evaluation), with the permissions, the stack
  pointer and the link register (`Keep`).
* `count_loop`: a loop on a counter that its body decrements.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont

/-! ## Reading a state after a write -/

section
variable (s : State)

theorem gpr_write (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.write d v).gpr r = if r = d then v else s.gpr r := rfl
theorem mem_write (d : Reg) (v : BitVec 64) : (s.write d v).mem = s.mem := rfl
theorem rd_write (d : Reg) (v : BitVec 64) : (s.write d v).rd = s.rd := rfl
theorem wr_write (d : Reg) (v : BitVec 64) : (s.write d v).wr = s.wr := rfl
theorem sp_write (d : Reg) (v : BitVec 64) : (s.write d v).sp = s.sp := rfl
theorem lr_write (d : Reg) (v : BitVec 64) : (s.write d v).lr = s.lr := rfl

theorem gpr_mem (m : Mem) : ({ s with mem := m } : State).gpr = s.gpr := rfl
theorem mem_mem (m : Mem) : ({ s with mem := m } : State).mem = m := rfl
theorem rd_mem (m : Mem) : ({ s with mem := m } : State).rd = s.rd := rfl
theorem wr_mem (m : Mem) : ({ s with mem := m } : State).wr = s.wr := rfl
theorem sp_mem (m : Mem) : ({ s with mem := m } : State).sp = s.sp := rfl
theorem lr_mem (m : Mem) : ({ s with mem := m } : State).lr = s.lr := rfl

end

/-! ## The working space -/

/-- The working space: `size` bytes at `base`, within a writable region,
not wrapping around. -/
structure Scr (s : State) (base : Addr) (size : Nat) : Prop where
  wr : ∃ B₀ : Addr, ∃ o L : Nat, (⟨B₀, L⟩ : Region) ∈ s.wr ∧ base = off B₀ o ∧ o + size ≤ L ∧ L ≤ 2 ^ 64
  nowrap : base.toNat + size ≤ 2 ^ 64

/-- A writable region is a working space. -/
theorem Scr.of_mem {s : State} {base : Addr} {size : Nat} (h : (⟨base, size⟩ : Region) ∈ s.wr)
    (hn : base.toNat + size ≤ 2 ^ 64) : Scr s base size :=
  ⟨⟨base, 0, size, h, by simp [off], by omega, by omega⟩, hn⟩

theorem Scr.region {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : ∃ r ∈ s.wr, r.Contains (off base d) n := by
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, _⟩ := hs
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

theorem Scr.congr {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h : s'.wr = s.wr) : Scr s' base size :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, h ▸ hm, hb, hL, hL'⟩, hs.nowrap⟩

/-! ## Addresses -/

/-- A pointer into the working space plus an offset. -/
theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-! ## Frames of what a block keeps -/

/-- The registers but `rs`, the permissions, the stack pointer and the link
register keep their values. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  lr : s'.lr = s.lr

namespace Keep

theorem refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs' s₂ s₃) :
    Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1], h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₂.lr.trans h₁.lr⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hr : ∀ r ∈ rs, r ∈ rs' := by decide) : Keep rs' s s' :=
  ⟨fun r hn => h.gpr r fun h' => hn (hr r h'), h.rd, h.wr, h.sp, h.lr⟩

theorem trans' {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂) (h₂ : Keep rs s₂ s₃) :
    Keep rs s₁ s₃ :=
  (h₁.trans h₂).mono fun r h => by simpa using h

/-- A write keeps every other register. -/
theorem write (s : State) (d : Reg) (v : BitVec 64) : Keep [d] s (s.write d v) :=
  ⟨fun r hr => ite_eq_right_iff.mpr fun h => absurd h fun h' => hr (by simp [h']), rfl, rfl, rfl, rfl⟩

/-- A store keeps every register. -/
theorem mem (s : State) (m : Mem) : Keep [] s { s with mem := m } := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

end Keep

/-- Whether every instruction of `c` writes, if any register, one of `rs`,
and none writes the link register. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  (instrs c).all fun i => (match dstOf i with | some d => rs.contains d | none => true) && !i.writesLr

/-- The registers no instruction writes are kept (code without calls). -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : c.noCalls = true := by first | rfl | decide) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  unfold writesOnly at hc
  rw [List.all_eq_true] at hc
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi hd => ?_) he (.inl hn), (Exec.rdwr he).1,
    (Exec.rdwr he).2.1, (Exec.rdwr he).2.2, Exec.lr he hn ?_⟩⟩
  · have := hc i hi
    rw [hd] at this
    simp only [Bool.and_eq_true] at this
    exact hr (by simpa using this.1)
  · rw [List.all_eq_true]
    intro i hi
    have := hc i hi
    simp only [Bool.and_eq_true] at this
    exact this.2

/-! ## Loops -/

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

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
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .d cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero .d cr) s' = some (decide (k + 1 ≠ n)) := by
    rw [eval_nonzero, ne_zero_iff]
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
    WP isa (.loop body (.nonzero .d cnt)) s (Inv N) := by
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

/-- `prun`: symbolic execution of a block by `simp` (see the module doc),
with extra lemmas (the block's accesses, …). -/
tactic_template "prun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp only [runBlock_cons, runStep_some, runBlock_nil,
                         exec_load_w, exec_load_d, exec_store_w, exec_store_d, exec_add, exec_sub, exec_mul,
                         exec_logic, exec_addi, exec_subi, exec_li, exec_lsr_w, exec_lsr_d, exec_lsl,
                         gpr_write, mem_write, rd_write, wr_write, sp_write, lr_write, gpr_mem, mem_mem,
                         rd_mem, wr_mem, sp_mem, lr_mem, off_add, Nat.add_zero, Option.some.injEq,
                         exists_eq_left', ite_true, ite_false, reduceCtorEq, ↓reduceIte, ne_eq,
                         not_false_eq_true, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, Nat.reduceLeDiff,
                         Nat.reduceAdd, Nat.reducePow, Nat.reduceEqDiff, implies_true, true_implies, and_self,
                         true_and, and_true, List.cons_append, List.nil_append, $ls,*]))

/-- Reading the registers and memory of a state built by writes. -/
tactic_template "gsimp" : tactic => `(tactic| (
                       set_option linter.unusedSimpArgs false in
                       simp only [gpr_write, mem_write, rd_write, wr_write,
                         sp_write, lr_write, gpr_mem, mem_mem, rd_mem, wr_mem, sp_mem, lr_mem, ite_true,
                         ite_false, reduceCtorEq, ↓reduceIte]))

/-- `prun []`. -/
tactic_template "prun" : tactic => `(tactic| prun [])

end VG.Proof.Bignum.PPC64LE
