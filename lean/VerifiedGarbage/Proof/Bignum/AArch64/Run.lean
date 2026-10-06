import VerifiedGarbage.Impl.Bignum.AArch64
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# Multiword arithmetic on AArch64: running blocks

The working space is `size` bytes at `base` (`Scr`), writable and not
wrapping around; a number of `n` words at byte offset `d` of it is
`wv m base d n` (`Proof/Bignum/Words.lean`).

* `brun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), with the state a chain of `State.write`s, flag updates and
  memory updates whose registers `RegUpd` reads, so that a register of the
  result is the value last written to it. A block lemma takes the accesses
  it makes as hypotheses (`Scr.ld`, `Scr.st`) on the addresses `off base d`,
  to which `off_add` brings a pointer plus an offset.
* `WP.keep`: the registers no instruction of the code writes are kept
  (`writesOnly`, checked by evaluation), with ML-KEM's `Keep`
  (`Proof/MlKem/AArch64/Wp.lean`, about the ISA only).
* `wp_countdown`: a loop on `cbnz` of a counter that its body decrements.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_nonzero ne_zero_iff)

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

/-- Part of a working space is one. -/
theorem Scr.sub {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {o n : Nat}
    (h : o + n ≤ size) (hn0 : 0 < n) : Scr s (off base o) n := by
  obtain ⟨⟨B₀, o₀, L, hm, hb, hL, hL'⟩, hn⟩ := hs
  refine ⟨⟨B₀, o₀ + o, L, hm, ?_, by omega, hL'⟩, ?_⟩
  · subst hb; simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [show (off base o).toNat = base.toNat + o by
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]]
    omega

theorem Scr.region {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d n : Nat}
    (h : d + n ≤ size) (hn : 0 < n) : ∃ r ∈ s.wr, r.Contains (off base d) n := by
  obtain ⟨⟨B₀, o, L, hm, hb, hL, hL'⟩, _⟩ := hs
  refine ⟨_, hm, ?_⟩
  rw [hb, show off (off B₀ o) d = off B₀ (o + d) by simp only [off, BitVec.add_assoc, BitVec.ofNat_add]]
  exact Offset.contains_base B₀ (by omega) (by omega)

theorem Scr.ld {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions (s.rd ++ s.wr) (off base d) 8 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, List.mem_append_right _ hm, hc⟩

theorem Scr.st {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 8 ≤ size) : InRegions s.wr (off base d) 8 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, hm, hc⟩

theorem Scr.ld1 {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 1 ≤ size) : InRegions (s.rd ++ s.wr) (off base d) 1 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, List.mem_append_right _ hm, hc⟩

theorem Scr.st1 {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat}
    (hd : d + 1 ≤ size) : InRegions s.wr (off base d) 1 :=
  let ⟨_, hm, hc⟩ := hs.region hd (by decide)
  ⟨_, hm, hc⟩

theorem Scr.congr {s s' : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (h : s'.wr = s.wr) : Scr s' base size :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, h ▸ hm, hb, hL, hL'⟩, hs.nowrap⟩

/-! ## Addresses -/

/-- A pointer into the working space plus an offset. -/
theorem off_add (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem off_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-! ## The instructions, for `simp` -/

section
variable {s : State}

theorem exec_mul_x {d n m : Reg} :
    exec (.mul .x d n m) s = some (s.write .x d (s.gpr n * s.gpr m)) := rfl

theorem exec_umulh {d n m : Reg} :
    exec (.umulh d n m) s =
      some (s.write .x d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64))) := rfl

theorem exec_adds_x {d n m : Reg} :
    exec (.adds .x d n m) s = some (s.addWithCarry .x d (s.gpr n) (s.gpr m) false) := rfl

theorem exec_adcs_x {d n m : Reg} :
    exec (.adcs .x d n m) s = some (s.addWithCarry .x d (s.gpr n) (s.gpr m) s.c) := rfl

theorem exec_subs_x {d n m : Reg} :
    exec (.subs .x d n m) s = some (s.addWithCarry .x d (s.gpr n) (~~~s.gpr m) true) := rfl

theorem exec_sbcs_x {d n m : Reg} :
    exec (.sbcs .x d n m) s = some (s.addWithCarry .x d (s.gpr n) (~~~s.gpr m) s.c) := rfl

theorem exec_adc_x {d n m : Reg} :
    exec (.adc .x d n m) s = some (s.write .x d (s.gpr n + s.gpr m + BitVec.ofNat 64 s.c.toNat)) := rfl

theorem exec_csel_x {d n m : Reg} :
    exec (.csel .x d n m) s = some (s.write .x d (if s.c then s.gpr n else s.gpr m)) := rfl

theorem exec_add_x {d n m : Reg} :
    exec (.add .x d n m) s = some (s.write .x d (s.gpr n + s.gpr m)) := rfl

theorem exec_sub_x {d n m : Reg} :
    exec (.sub .x d n m) s = some (s.write .x d (s.gpr n - s.gpr m)) := rfl

theorem exec_logic_x {op : LogicOp} {d n m : Reg} :
    exec (.logic op .x d n m) s = some (s.write .x d (match op with
      | .and => s.gpr n &&& s.gpr m | .orr => s.gpr n ||| s.gpr m
      | .eor => s.gpr n ^^^ s.gpr m)) := rfl

theorem exec_lsl_x {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.gpr n <<< sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_lsr_x' {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_movz_x {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true]
  exact congrArg (fun v => some (s.write .x d v)) (BitVec.shiftLeft_zero _)

theorem exec_addImm_x' {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp [exec, h, State.read]

theorem exec_subImm_x' {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp [exec, h, State.read]

theorem exec_ldr_x' {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.ldr .x t n off) s = some (s.write .x t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) :=
  exec_ldr_x ho h

theorem exec_str_x' {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.str .x t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) } :=
  exec_str_x ho h

theorem exec_ldrb' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.ldrb t n off) s =
      some (s.write .w t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 32)) := by
  simp only [exec, addr, Nat.mod_one, ho, and_self, ite_true, Option.bind_some, State.load, h,
    Option.map_some]

theorem exec_strb' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.gpr t).setWidth 8) } := by
  simp only [exec, addr, Nat.mod_one, ho, and_self, ite_true, Option.bind_some, State.store, h,
    State.read, Size.bits]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]

end

/-! ## The state after a step, for `simp` -/

section
variable (s : State)

theorem gpr_mem (m : Mem) (r : Reg) : ({ s with mem := m } : State).gpr r = s.gpr r := rfl
theorem mem_mem (m : Mem) : ({ s with mem := m } : State).mem = m := rfl
theorem rd_mem (m : Mem) : ({ s with mem := m } : State).rd = s.rd := rfl
theorem wr_mem (m : Mem) : ({ s with mem := m } : State).wr = s.wr := rfl
theorem c_mem (m : Mem) : ({ s with mem := m } : State).c = s.c := rfl

theorem c_addWithCarry_x (d : Reg) (a b : BitVec 64) (c : Bool) :
    (s.addWithCarry .x d a b c).c = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := rfl

theorem gpr_addWithCarry_x (d : Reg) (a b : BitVec 64) (c : Bool) (r : Reg) :
    (s.addWithCarry .x d a b c).gpr r = if r = d then a + b + BitVec.ofNat 64 c.toNat else s.gpr r := by
  simp only [RegUpd.gpr_addWithCarry, Size.bits, BitVec.setWidth_eq]

end

/-- `brun`: symbolic execution of a block by `simp` (see the module doc),
with extra lemmas (the block's accesses, …). -/
syntax "brun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brun) => `(tactic| brun [])
  | `(tactic| brun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [runBlock_cons, runStep_some, runBlock_nil,
        exec_ldr_x', exec_str_x', exec_ldrb', exec_strb', exec_add_x, exec_sub_x, exec_logic_x, exec_mul_x,
        exec_umulh, exec_adds_x, exec_adcs_x, exec_subs_x, exec_sbcs_x, exec_adc_x, exec_csel_x,
        exec_addImm_x', exec_subImm_x', exec_lsl_x, exec_lsr_x', exec_movz_x,
        ld, st, ldh, sth, mov, movi, next,
        State.read, Size.bits, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
        RegUpd.sp_write, RegUpd.c_write, gpr_addWithCarry_x, c_addWithCarry_x, RegUpd.mem_addWithCarry,
        RegUpd.rd_addWithCarry, RegUpd.wr_addWithCarry, RegUpd.sp_addWithCarry, gpr_mem, mem_mem, rd_mem,
        wr_mem, c_mem, BitVec.setWidth_eq, off_add, off_zero, Nat.add_zero, Option.some.injEq,
        exists_eq_left', ite_true, ite_false, reduceCtorEq, true_and, and_true, List.cons_append,
        List.nil_append, $ls,*]))

/-! ## What a block keeps -/

/-- Whether every instruction of `c` writes, if any register, one of `rs`. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => match dstOf i with
    | none => true
    | some d => rs.contains d

/-- A register that no instruction writes keeps its value (code without calls). -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : c.noCalls = true := by first | rfl | decide)
    (hv : c.allInstrs keepsV = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), (Exec.rdwr he).1,
    (Exec.rdwr he).2.1, (Exec.rdwr he).2.2, Exec.preservedV he hv⟩⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := hc i hi
  intro e
  rw [e] at this
  simp only [List.contains_iff_mem] at this
  exact hr (by simpa using this)

/-! ## Loops -/

/-- A do-while loop on `cbnz cnt` whose body decrements `cnt`, from `N > 0`:
it runs `N` times. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 64) (hN0 : 0 < N)
    (Inv : Nat → State → Prop)
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 64 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1)
    {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 64 N) :
    WP isa (.loop body (.nonzero .x cnt)) s (Inv N) := by
  refine WP.mono (count_loop (cr := cnt) hN0 (fun k s => Inv k s ∧ s.gpr cnt = BitVec.ofNat 64 (N - k))
    (fun k hk s ⟨hI, hc⟩ => WP.mono (hbody k hk s hI hc) fun s' ⟨hI', hc'⟩ => ⟨⟨hI', ?_⟩, ?_⟩)
    ⟨h0, by rw [hc, Nat.sub_zero]⟩) fun _ h => h.1
  · rw [hc', hc]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [hc', hc, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-! ## Sequences -/

theorem wp_seqs_append {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) {s : State} {Q : State → Prop}
    (h : WP isa (seqs a) s fun t => WP isa (seqs b) t Q) : WP isa (seqs (a ++ b)) s Q := by
  induction a generalizing s with
  | nil => exact absurd rfl ha
  | cons c a ih =>
    cases a with
    | nil =>
      obtain ⟨d, rest, rfl⟩ := List.exists_cons_of_ne_nil hb
      exact WP.seq h
    | cons d rest =>
      simp only [seqs, List.cons_append] at h ⊢
      exact WP.seq (WP.mono (WP.seq_iff.mp h) fun t ht => ih (by simp) ht)

end VG.Proof.Bignum.AArch64
