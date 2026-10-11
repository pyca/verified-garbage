import VerifiedGarbage.Impl.Blowfish.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Inline

/-!
# Blowfish on ARMv7: running blocks

`brun [facts]` runs a block symbolically (`runBlock_cons`, `runStep_some`,
the semantics of the instructions the code uses, reading through the writes
with `RegUpd`), keeping the flag and memory updates folded, as RC4's `arun`
(`Proof/Rc4/Arm/Run.lean`). `Keep rs s s'` says that `s'` has the registers
of `s` but for `rs`, and its regions and stack pointer; `WP.keep` proves it
of a block none of whose instructions writes another register.
-/

namespace VG.Proof.Blowfish.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Blowfish.Arm

/-! ## Registers kept -/

def Keep (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem Keep.gpr {rs : List Reg} {s s' : State} (h : Keep rs s s') {r : Reg} (hr : r ∉ rs) :
    s'.gpr r = s.gpr r := h.1 r hr

theorem Keep.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂)
    (h₂ : Keep rs' s₂ s₃) : Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keep.mono {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- `Keep.trans` into a given list. -/
theorem Keep.trans' {rs rs' rs'' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂)
    (h₂ : Keep rs' s₂ s₃) (hs : ∀ r, r ∈ rs ∨ r ∈ rs' → r ∈ rs'') : Keep rs'' s₁ s₃ :=
  (h₁.trans h₂).mono fun r hr => hs r (List.mem_append.mp hr)

/-- `Keep.trans`, the second list within the first. -/
theorem Keep.trans_sub {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keep rs s₁ s₂)
    (h₂ : Keep rs' s₂ s₃) (hs : rs'.all (rs.contains ·) = true) : Keep rs s₁ s₃ :=
  (h₁.trans h₂).mono fun r hr => by
    rcases List.mem_append.mp hr with h | h
    · exact h
    · have := List.all_eq_true.mp hs r h
      simpa only [List.contains_iff_mem] using this

/-- Whether every instruction of `is` writes only registers of `rs`. -/
def writesOnly (rs : List Reg) (is : List Instr) : Bool :=
  is.all fun i => match dstOf i with
    | some r => rs.contains r
    | none => true

theorem WP.keep {is : List Instr} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa (.block is) s Q) (hc : writesOnly rs is = true) :
    WP isa (.block is) s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  have he' := Exec.block_iff.mp he
  obtain ⟨r, w, p, -⟩ := execBlock_regions he'
  refine ⟨t, s', he, hq, fun r' hr => execBlock_gpr (fun i hi e => hr ?_) he', r, w, p⟩
  have := List.all_eq_true.mp hc i hi
  simp only [e, List.contains_iff_mem] at this
  exact this

/-- Code that calls nothing keeps the registers it never writes, its
regions and the stack pointer. -/
theorem WP.keepCode {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg)
    (h : WP isa c s Q) (hc : (instrs c).all (fun i => (dstOf i).all rs.contains) = true)
    (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  obtain ⟨hrd, hwr, hsp⟩ := Exec.rdwr he
  refine ⟨t, s', he, hq, fun r' hr => Exec.gpr (fun i hi e => hr ?_) he (.inl hn), hrd, hwr, hsp⟩
  have := List.all_eq_true.mp hc i hi
  simp only [e, Option.all_some, List.contains_iff_mem] at this
  exact this

theorem WP.reassoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a b) c) s Q) : WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-! ## Symbolic execution -/

theorem gpr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).gpr = s.gpr := rfl
theorem mem_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).mem = s.mem := rfl
theorem rd_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).rd = s.rd := rfl
theorem wr_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).wr = s.wr := rfl
theorem sp_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).sp = s.sp := rfl
theorem z_subFlags (s : State) (x y : BitVec 32) : (subFlags s x y).z = (x - y == 0#32) := rfl
theorem c_subFlags (s : State) (x y : BitVec 32) :
    (subFlags s x y).c = decide (y.toNat ≤ x.toNat) := rfl

/-- `s` with the memory `m`: what a store leaves, kept folded. -/
def withMem (s : State) (m : Mem) : State := { s with mem := m }

theorem store32_eq (s : State) (a : Addr) (x : BitVec 32) :
    s.store32 a x = if InRegions s.wr a 4 then some (withMem s (s.mem.writeW a x)) else none := rfl
theorem store8_eq (s : State) (a : Addr) (x : BitVec 8) :
    s.store8 a x = if InRegions s.wr a 1 then some (withMem s (s.mem.writeW a x)) else none := rfl
theorem sp_store (s : State) (m : Mem) : (withMem s m).sp = s.sp := rfl
theorem gpr_store (s : State) (m : Mem) : (withMem s m).gpr = s.gpr := rfl
theorem rd_store (s : State) (m : Mem) : (withMem s m).rd = s.rd := rfl
theorem wr_store (s : State) (m : Mem) : (withMem s m).wr = s.wr := rfl
theorem mem_store (s : State) (m : Mem) : (withMem s m).mem = m := rfl
theorem z_store (s : State) (m : Mem) : (withMem s m).z = s.z := rfl
theorem c_store (s : State) (m : Mem) : (withMem s m).c = s.c := rfl

/-- The carry `adc` adds, as a number. -/
theorem ite_carry (b : Bool) : (if b = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 b.toNat := by
  cases b <;> rfl

/-- An immediate below 256 is encodable (rotation 0). -/
theorem encodable_of_lt {v : BitVec 32} (h : v.toNat < 256) : encodable v = true :=
  List.any_eq_true.2 ⟨0, by simp, by
    have h0 : v.rotateLeft (2 * 0) = v := by ext i; simp
    simpa only [h0, decide_eq_true_eq] using h⟩

theorem encodable_lt {n : Nat} (h : n < 256) : encodable (BitVec.ofNat 32 n) = true :=
  encodable_of_lt (by rw [BitVec.toNat_ofNat]; omega)

/-- The code's immediates that need a rotation. -/
theorem encodable_768 : encodable (BitVec.ofNat 32 768) = true := by decide
theorem encodable_4096 : encodable (BitVec.ofNat 32 4096) = true := by decide
theorem encodable_4160 : encodable (BitVec.ofNat 32 4160) = true := by decide

/-- Runs a block of the Blowfish code. -/
syntax "brun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| brun) => `(tactic| brun [])
  | `(tactic| brun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (disch := decide) only [runBlock_cons, runStep_some, runBlock_nil, exec,
        encodable_of_lt, encodable_768, encodable_4096, encodable_4160,
        Op2.eval, imm, sch, xL, xR, fReg, qReg, acc, mReg, lane, ones, tmp, rowPtr, rows, pPtr,
        gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg, c_setReg,
        gpr_subFlags, mem_subFlags, rd_subFlags, wr_subFlags, sp_subFlags, z_subFlags, c_subFlags,
        State.load32, store32_eq, State.load8, store8_eq, sp_store, gpr_store, rd_store, wr_store,
        mem_store, z_store, c_store, ↓ite_carry, ite_true, ite_false, ↓reduceIte, reduceCtorEq,
        Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
        and_self, Option.map_some,
        Option.some.injEq, exists_eq_left', List.cons_append, List.nil_append, and_true, true_and,
        $ls,*]))

/-! ## Offsets from a pointer -/

theorem ofs_add (S : BitVec 32) (a b : Nat) :
    S + BitVec.ofNat 32 a + BitVec.ofNat 32 b = S + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ofs_sub (S : BitVec 32) {a b : Nat} (h : b ≤ a) :
    S + BitVec.ofNat 32 a - BitVec.ofNat 32 b = S + BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ofs_diff (S : BitVec 32) (a : Nat) : S + BitVec.ofNat 32 a - S = BitVec.ofNat 32 a := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem ofNat_sub_beq {a c : Nat} (ha : a < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 c == 0#32) = decide (a = c) := by
  by_cases h : a = c
  · subst h; simp
  · have : BitVec.ofNat 32 a - BitVec.ofNat 32 c ≠ 0#32 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      omega
    simp [this, h]

/-- The branch conditions. -/
theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

theorem region_in {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.Blowfish.Arm
