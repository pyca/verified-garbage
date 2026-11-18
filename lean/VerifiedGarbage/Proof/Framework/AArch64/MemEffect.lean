module

public import VerifiedGarbage.Proof.Framework.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# What an instruction writes to memory (AArch64)

`exec_mem`: an instruction's run leaves the memory as its stores write it
(`stores`), each the bytes of a register at the address of a base (a
register or the stack pointer) and an offset, read in the state before it;
every other instruction leaves the memory as it was.
-/

@[expose] public section

namespace VG.AArch64.MemEffect

open VG.AArch64

/-- The base of a store's address. -/
inductive Base | reg (r : Reg) | sp
  deriving DecidableEq, Repr

/-- What a store writes: the low bytes of a general-purpose register, or a vector register. -/
inductive Src | gpr (r : Reg) | vec (v : VReg)
  deriving DecidableEq, Repr

def Base.val (b : Base) (s : State) : Addr :=
  match b with
  | .reg r => s.gpr r
  | .sp => s.sp

/-- The `n` bytes `src` writes, in `s`. -/
def Src.val (src : Src) (n : Nat) (s : State) : BitVec (8 * n) :=
  match src with
  | .gpr r => (s.gpr r).setWidth (8 * n)
  | .vec v => (s.v v).setWidth (8 * n)

/-- The stores of an instruction: base, offset, bytes and source. -/
def stores : Instr → List (Base × Nat × Nat × Src)
  | .str sz t n off => [(.reg n, off, sz.bytes, .gpr t)]
  | .strb t n off => [(.reg n, off, 1, .gpr t)]
  | .stp t1 t2 n off => [(.reg n, off, 8, .gpr t1), (.reg n, off + 8, 8, .gpr t2)]
  | .strq t n off => [(.reg n, off, 16, .vec t)]
  | .strSp t off => [(.sp, off, 8, .gpr t)]
  | _ => []

/-- The memory after the stores `l`, from `s`. -/
def writeAll (s : State) : List (Base × Nat × Nat × Src) → Mem → Mem
  | [], m => m
  | (b, off, n, src) :: l, m =>
    writeAll s l (m.write (b.val s + BitVec.ofNat 64 off) n (src.val n s))

theorem exec_mem {i : Instr} {s s' : State} (h : exec i s = some s') :
    s'.mem = writeAll s (stores i) s.mem := by
  by_cases hr : Residue.regOnly i = true
  · obtain ⟨-, -, hm⟩ := Residue.exec_regOnly hr h
    rw [hm]
    cases i <;> simp_all [Residue.regOnly, stores, writeAll]
  · cases i <;> simp only [Residue.regOnly, Bool.false_eq_true, not_false_eq_true,
      not_true_eq_false] at hr
    case str sz t n off =>
      simp only [exec, Option.bind_eq_some_iff, State.store, addr] at h
      obtain ⟨a, ha, h⟩ := h
      split at ha <;> [skip; cases ha]
      obtain rfl := Option.some.inj ha
      split at h <;> [skip; cases h]
      obtain rfl := Option.some.inj h
      simp only [stores, writeAll, Base.val, Src.val, State.read]
      congr 1
      cases sz <;> first | rfl | simp | (rw [BitVec.setWidth_setWidth_of_le _ (by decide)])
    case strb t n off =>
      simp only [exec, Option.bind_eq_some_iff, State.store, addr] at h
      obtain ⟨a, ha, h⟩ := h
      split at ha <;> [skip; cases ha]
      obtain rfl := Option.some.inj ha
      split at h <;> [skip; cases h]
      obtain rfl := Option.some.inj h
      simp only [stores, writeAll, Base.val, Src.val, State.read]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
    case strq t n off =>
      simp only [exec, Option.bind_eq_some_iff, State.store, addr] at h
      obtain ⟨a, ha, h⟩ := h
      split at ha <;> [skip; cases ha]
      obtain rfl := Option.some.inj ha
      split at h <;> [skip; cases h]
      obtain rfl := Option.some.inj h
      simp [stores, writeAll, Base.val, Src.val]
    case strSp t off =>
      simp only [exec] at h
      split at h <;> [skip; cases h]
      simp only [State.store] at h
      split at h <;> [skip; cases h]
      obtain rfl := Option.some.inj h
      simp [stores, writeAll, Base.val, Src.val, State.read]
    case stp t1 t2 n off =>
      simp only [exec] at h
      split at h <;> [skip; cases h]
      obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [State.store] at hu h
      split at hu <;> [skip; cases hu]
      obtain rfl := Option.some.inj hu
      split at h <;> [skip; cases h]
      obtain rfl := Option.some.inj h
      simp only [stores, writeAll, Base.val, Src.val, State.read, BitVec.setWidth_eq]
      rw [show s.gpr n + BitVec.ofNat 64 off + 8 = s.gpr n + BitVec.ofNat 64 (off + 8) by
        rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl]
    case ldr sz t n off =>
      simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, -, v, -, rfl⟩ := h
      simp [stores, writeAll, State.write]
    case ldrb t n off =>
      simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, -, v, -, rfl⟩ := h
      simp [stores, writeAll, State.write]
    case ldrq t n off =>
      simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨a, -, v, -, rfl⟩ := h
      simp [stores, writeAll, State.setV]
    case ldrSp t off =>
      simp only [exec] at h
      split at h <;> [skip; cases h]
      obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [stores, writeAll, State.write]
    case ldp t1 t2 n off =>
      simp only [exec] at h
      split at h <;> [skip; cases h]
      obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
      simp [stores, writeAll, State.write]
    case ldrqTbl t n off name ws =>
      simp only [exec] at h
      split at h <;> [skip; cases h]
      obtain rfl := Option.some.inj h
      simp [stores, writeAll, State.setV]
    case ldrTbl sz t n off name ws =>
      simp only [exec] at h
      split at h <;> [skip; cases h]
      obtain rfl := Option.some.inj h
      simp [stores, writeAll, State.write]
    case ccmp sz n imm nzcv cond =>
      simp only [exec] at h
      split at h <;> [skip; cases h]
      obtain rfl := Option.some.inj h
      split <;> simp [stores, writeAll, State.flagsAdd]
    case adrSym d name =>
      simp only [exec] at h
      obtain rfl := Option.some.inj h
      simp [stores, writeAll, State.write]
    all_goals simp only [exec] at h; cases h

end VG.AArch64.MemEffect
