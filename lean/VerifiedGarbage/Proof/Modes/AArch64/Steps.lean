import VerifiedGarbage.Impl.Modes.AArch64.Ctr
import VerifiedGarbage.Proof.Modes.Addr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Straight
import VerifiedGarbage.Spec.Aes

/-!
# Steps of the modes on AArch64

The single instructions the modes are made of (moves, slots of the scratch
buffer at `sb`, immediates), and the bytes in memory around stores and
frames. Nothing here depends on a cipher.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight
open VG.Impl.Aes.AArch64 (sb movR ldS stS eorR)
open VG.Spec.Aes (bytesAt)

theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

theorem addr_add (b : Addr) (x y : Nat) :
    b + BitVec.ofNat 64 x + BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x + y) := VG.Offset.add_add b x y

theorem read_x (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, Size.bits, BitVec.setWidth_eq]

/-- `cbnz r`: whether `r` is not zero. -/
theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .x r) s = some !(s.gpr r == 0) := by
  show VG.AArch64.eval (.nonzero .x r) s = _
  simp only [VG.AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq, bne]

/-- `cbz r`: whether `r` is zero. -/
theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  show VG.AArch64.eval (.zero .x r) s = _
  simp only [VG.AArch64.eval, State.read, Size.bits, BitVec.setWidth_eq]

/-- A register write, as the steps below state it. -/
theorem write_ok (s : State) (d : Reg) (v : BitVec 64) :
    (s.write .x d v).gpr d = v ∧ (∀ r, r ≠ d → (s.write .x d v).gpr r = s.gpr r) ∧
      (s.write .x d v).mem = s.mem ∧ (s.write .x d v).rd = s.rd ∧ (s.write .x d v).wr = s.wr := by
  refine ⟨by simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write_of_ne _ _ _ hr]

/-- `mov d, n` (`add d, n, #0`). -/
theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (s.gpr n + BitVec.ofNat 64 0), ?_, ?_, (write_ok _ _ _).2.1, rfl, rfl, rfl⟩
  · simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide), read_x]
  · rw [(write_ok _ _ _).1, BitVec.add_zero]

theorem rev_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [.rev d n] s = some s' ∧ s'.gpr d = rev64 (s.gpr n) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (rev64 (s.gpr n)), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl, rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_rev, read_x]

theorem addImm_ok (s : State) (d n : Reg) {v : Nat} (hv : v < 4096) :
    ∃ s', runBlock isa [.addImm .x d n v] s = some s' ∧ s'.gpr d = s.gpr n + BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (s.gpr n + BitVec.ofNat 64 v), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl,
    rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x hv, read_x]

theorem subImm_ok (s : State) (d n : Reg) {v : Nat} (hv : v < 4096) :
    ∃ s', runBlock isa [.subImm .x d n v] s = some s' ∧ s'.gpr d = s.gpr n - BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (s.gpr n - BitVec.ofNat 64 v), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl,
    rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x hv, read_x]

/-- `sub d, n, m`. -/
theorem subReg_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.sub .x d n m] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (s.gpr n - s.gpr m), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl, rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x]

/-- `eor d, n, m`. -/
theorem eor_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [eorR d n m] s = some s' ∧ s'.gpr d = s.gpr n ^^^ s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (s.gpr n ^^^ s.gpr m), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl, rfl⟩
  simp only [eorR, runBlock_cons, runStep_some, runBlock_nil, exec_logic, read_x]

/-- `movz d, #v` (`v < 2¹⁶`). -/
theorem movz_ok (s : State) (d : Reg) {v : Nat} (hv : v < 2 ^ 16) :
    ∃ s', runBlock isa [.movz .x d (BitVec.ofNat 16 v) 0] s = some s' ∧ s'.gpr d = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (BitVec.ofNat 64 v), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl, rfl⟩
  have e : (BitVec.ofNat 16 v).setWidth 64 <<< (16 * 0) = BitVec.ofNat 64 v := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_zero,
      Nat.shiftLeft_zero]
    omega
  simp only [runBlock_cons, exec, Size.bits, show 16 * 0 < 64 by decide, ite_true, e, runStep_some,
    runBlock_nil]

/-- `lsr d, n, #sh`. -/
theorem lsr_ok (s : State) (d n : Reg) {sh : Nat} (h : sh < 64) :
    ∃ s', runBlock isa [.lsr .x d n sh] s = some s' ∧ s'.gpr d = s.gpr n >>> sh ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d (s.gpr n >>> sh), ?_, (write_ok _ _ _).1, (write_ok _ _ _).2.1, rfl, rfl, rfl⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_lsr_x h, read_x]

/-- `ldr d, [n, #off]`. -/
theorem ldr_ok (s : State) (d n : Reg) {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    ∃ s', runBlock isa [.ldr .x d n off] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x ho hr], (write_ok _ _ _).1,
    (write_ok _ _ _).2.1, rfl, rfl, rfl⟩

/-- `str t, [n, #off]`. -/
theorem str_ok (s : State) (t n : Reg) {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (hw : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    ∃ s', runBlock isa [.str .x t n off] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr :=
  ⟨{ s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) },
    by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_str_x ho hw], rfl, rfl, rfl, rfl⟩

/-- `str r, [sb, #8 k]`. -/
theorem stS_ok {s : State} {b : Addr} {k : Nat} (r : Reg) (hb : s.gpr sb = b) (hk : 8 * k < 32768)
    (hw : InRegions s.wr (wordAddr b k) 8) :
    ∃ s', runBlock isa [stS k r] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, m, g, rd, wr⟩ := str_ok s r sb (off := 8 * k) ⟨by omega, hk⟩ (by rw [hb]; exact hw)
  exact ⟨s', e, by rw [m, hb], g, rd, wr⟩

/-- `ldr d, [sb, #8 k]`. -/
theorem ldS_ok {s : State} {b : Addr} {k : Nat} (d : Reg) (hb : s.gpr sb = b) (hk : 8 * k < 32768)
    (hr : InRegions (s.rd ++ s.wr) (wordAddr b k) 8) :
    ∃ s', runBlock isa [ldS d k] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 64 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e, v, o, m, rd, wr⟩ := ldr_ok s d sb (off := 8 * k) ⟨by omega, hk⟩ (by rw [hb]; exact hr)
  exact ⟨s', e, by rw [v, hb], o, m, rd, wr⟩

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- Slot `k` of a scratch buffer of `n` slots at `B` is writable. -/
theorem slot_wr {rs : List Region} {B : Addr} {n : Nat} (h : (⟨B, 8 * n⟩ : Region) ∈ rs) (hn : 8 * n < 2 ^ 64)
    {k : Nat} (hk : k < n) : InRegions rs (wordAddr B k) 8 :=
  ⟨_, h, VG.Offset.contains_base B (by omega) (by omega)⟩

theorem readW_slot_write {m : Mem} {b : Addr} {j k : Nat} (v : BitVec 64) (hj : 8 * j < 2 ^ 64)
    (hk : 8 * k < 2 ^ 64) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 64 = if j = k then v else m.readW (wordAddr b j) 64 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self64 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b hj hk h) (by decide)

end VG.Proof.Modes.AArch64
