import VerifiedGarbage.Impl.Rc4.Arm
import VerifiedGarbage.Proof.Rc4.Scan32
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Inline

/-!
# RC4 on ARMv7: running blocks

`arun [facts]` runs a block symbolically (`runBlock_cons`, `runStep_some`,
the semantics of the instructions the code uses, reading through the
writes with `RegUpd`), keeping the flag and memory updates folded.
`Keep rs s s'` says that `s'` has the registers of `s` but for `rs`, and its
regions and stack pointer; `WP.keep` proves it of a block none of whose
instructions writes another register.
-/

namespace VG.Proof.Rc4.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc4.Arm VG.Proof.Rc4

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

/-- An immediate below 256 is encodable (no rotation). -/
theorem encodable_lt {n : Nat} (h : n < 256) : encodable (BitVec.ofNat 32 n) = true := by
  unfold encodable
  refine List.any_eq_true.mpr ⟨0, List.mem_range.mpr (by decide), ?_⟩
  have h0 : (BitVec.ofNat 32 n).rotateLeft (2 * 0) = BitVec.ofNat 32 n := by
    rw [BitVec.rotateLeft_def]
    simp only [Nat.mul_zero, Nat.zero_mod, BitVec.shiftLeft_zero, Nat.sub_zero,
      BitVec.ushiftRight_eq_zero (Nat.le_refl 32), BitVec.or_zero]
  rw [h0, decide_eq_true_eq, BitVec.toNat_ofNat]
  omega

/-- The carry `adc` adds, as a number (rewritten before the flag inside it,
so that the `if` never depends on a rewritten instance). -/
theorem ite_carry (b : Bool) : (if b = true then (1 : BitVec 32) else 0) = BitVec.ofNat 32 b.toNat := by
  cases b <;> rfl

/-- Runs a block of the RC4 code. -/
syntax "arun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| arun) => `(tactic| arun [])
  | `(tactic| arun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
        Op2.eval, imm, gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg, c_setReg,
        gpr_subFlags, mem_subFlags, rd_subFlags, wr_subFlags, sp_subFlags, z_subFlags, c_subFlags,
        State.load32, store32_eq, State.load8, store8_eq, sp_store, gpr_store, rd_store, wr_store,
        mem_store, z_store, c_store, ↓ite_carry, ite_true, ite_false, reduceCtorEq, Option.map_some,
        Option.some.injEq, exists_eq_left', List.cons_append, List.nil_append, and_true, true_and,
        $ls,*]))

/-- Closes a conjunction of reflexive equations. -/
macro "conj_rfl" : tactic => `(tactic| repeat' (first | exact rfl | refine ⟨?_, ?_⟩))

/-! ## Values -/

theorem ones_eq : ((0xFFFF : BitVec 16) ++
    (((0xFFFF : BitVec 16).setWidth 32).extractLsb' 0 16) : BitVec 32) = BitVec.allOnes 32 := by
  decide

/-- The mask `adc d, ones, #0` leaves after a comparison that set the carry to `c`. -/
theorem adc_mask (c : Bool) (y : BitVec 32) :
    (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 c.toNat) &&& y =
      if c = true then 0 else y := by
  cases c
  · rw [show BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 false.toNat =
      BitVec.allOnes 32 by decide, BitVec.allOnes_and]
    rfl
  · rw [show BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 true.toNat = 0 by decide]
    exact BitVec.zero_and

theorem adc_mask' (c : Bool) (y : BitVec 32) :
    y &&& (BitVec.allOnes 32 + BitVec.ofNat 32 0 + BitVec.ofNat 32 c.toNat) =
      if c = true then 0 else y := by
  rw [BitVec.and_comm, adc_mask]

/-- The address of word `k` of the table at `P`, which does not wrap around. -/
theorem row_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) {k : Nat} (hk : k < 64) :
    State.addr (P + BitVec.ofNat 32 (4 * k)) = State.addr P + BitVec.ofNat 64 (4 * k) :=
  addr_add (by omega)

/-- The address of byte `i` of the table at `P`. -/
theorem idx_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) (i : Byte) :
    State.addr (P + i.setWidth 32 + BitVec.ofNat 32 0) = State.addr P + BitVec.ofNat 64 i.toNat := by
  rw [BitVec.add_zero, byte32]
  exact addr_add (by have := i.isLt; omega)

/-- The branch conditions. -/
theorem eval_ne (s : State) : isa.eval .ne s = some !s.z := rfl
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

theorem region_in {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

end VG.Proof.Rc4.Arm
