module

public import VerifiedGarbage.Proof.Framework.X86_64.Spill
public import VerifiedGarbage.Impl.AesXts.X86_64Unit
public import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
public import VerifiedGarbage.Proof.Aes.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesCbc.X86_64.Block
import VerifiedGarbage.Proof.AesXts.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Contract

/-!
# XTS-AES of data units on x86-64: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_ok`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc.X86_64 (offset_nat)
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

theorem save_eq : save = Spill.saveCode .rax saved := rfl

theorem restore_eq : restore = Spill.restoreCode .r15 saved := rfl

theorem ldS_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    runBlock isa ldS s =
      some (s.setReg .rax (s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64)) := by
  simp only [ldS, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea,
    offset_nat, hr, ite_true, Option.map_some]

theorem setup_ok (s : State) :
    ∃ s', runBlock isa setup s = some s' ∧
      s'.gpr .r15 = s.gpr .rax ∧ s'.gpr .rbx = s.gpr .rdi ∧ s'.gpr .rbp = s.gpr .rdx ∧
      s'.gpr .r12 = s.gpr .r8 ∧ s'.gpr .r13 = s.gpr .r9 ∧
      (∀ r, r ≠ .r15 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [setup, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · simp [gpr_setReg]
  · intro r h₁ h₂ h₃ h₄ h₅; simp [gpr_setReg, h₁, h₂, h₃, h₄, h₅]

/-- The memory after zeroing the block at `c`. -/
def zero2 (m : Mem) (c : Addr) : Mem :=
  (m.writeW c (BitVec.setWidth 64 (0 : BitVec 32))).writeW (c + BitVec.ofNat 64 8) (BitVec.setWidth 64 (0 : BitVec 32))

theorem zero2_frame (m : Mem) (c : Addr) : Frame [⟨c, 16⟩] m (zero2 m c) := AesCbc.frame_store2 _ _ _

theorem zero2_bytes (m : Mem) (c : Addr) : bytesAt (zero2 m c) c 16 = List.replicate 16 0 := by
  rw [zero2, Proof.Cmac.bytesAt_store2]; decide

theorem zeroZ_ok (s : State) {Z : Addr} (hz : s.gpr .r15 + BitVec.ofNat 64 zO = Z)
    (hz8 : s.gpr .r15 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8)
    (w0 : InRegions s.wr Z 8) (w8 : InRegions s.wr (Z + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa zeroZ s = some s' ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = zero2 s.mem Z ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, zeroZ, runBlock_cons, runStep_some, runBlock_nil, at_, exec,
      readSrc32, State.store64, State.ea, State.setReg32, offset_nat, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, hz, hz8, w0, w8]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp [gpr_setReg, hr]

theorem tArgs_ok (s : State) :
    ∃ s', runBlock isa tArgs s = some s' ∧
      s'.gpr .rdi = s.gpr .rsi ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 zO ∧ s'.gpr .rcx = s.gpr .r15 + BitVec.ofNat 64 tO ∧
      s'.gpr .r8 = 1 ∧ s'.gpr .r9 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [tArgs, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]; rfl
  · simp [gpr_setReg, State.setReg32]; rfl
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, State.setReg32]

theorem shr4 (x : BitVec 64) : x >>> 4 = BitVec.ofNat 64 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem shr4_shl4 (x : BitVec 64) : (x >>> 4) <<< 4 = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.reducePow]
  omega

theorem argsAll_ok (s : State) :
    ∃ s', runBlock isa argsAll s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 tO ∧ s'.gpr .rcx = s.gpr .r12 ∧
      s'.gpr .r8 = BitVec.ofNat 64 ((s.gpr .r13).toNat / 16) ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [argsAll, runBlock_cons, runStep_some, exec, readSrc, execAlu, execShift,
      Option.bind_some, Option.map_some, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, gpr_setFlags]
  · simp [gpr_setReg, gpr_setFlags]
  · simp [gpr_setReg, gpr_setFlags]; rfl
  · simp [gpr_setReg, gpr_setFlags]
  · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, reduceCtorEq, ↓reduceIte, shr4]
  · simp [gpr_setReg, gpr_setFlags]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, gpr_setFlags]

theorem argsHead_ok (s : State) (hm : 1 ≤ (s.gpr .r13).toNat / 16) :
    ∃ s', runBlock isa argsHead s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 tO ∧ s'.gpr .rcx = s.gpr .r12 ∧
      s'.gpr .r8 = BitVec.ofNat 64 ((s.gpr .r13).toNat / 16 - 1) ∧ s'.gpr .r9 = s.gpr .r15 ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, cs₁, mem₁, rd₁, wr₁⟩ := argsAll_ok s
  refine ⟨_, by
    rw [argsHead, runBlock_append, run₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, mem₁, rd₁, wr₁⟩
  · simp [gpr_setReg, rdi₁]
  · simp [gpr_setReg, rsi₁]
  · simp [gpr_setReg, rdx₁]
  · simp [gpr_setReg, rcx₁]
  · simp only [gpr_setReg, ite_true, r8₁]
    rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat hm]
  · simp [gpr_setReg, r9₁]
  · intro r hr
    have := cs₁ r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [gpr_setReg] using this

theorem beq_zero64 {x : Nat} (hx : x < 2 ^ 64) : (BitVec.ofNat 64 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro he
    have := congrArg BitVec.toNat he
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at this
    simpa using this
  · intro he; rw [he]; rfl

theorem split_ok (s : State) :
    ∃ s', runBlock isa split s = some s' ∧
      s'.gpr .rax = BitVec.ofNat 64 (16 * ((s.gpr .r13).toNat / 16)) ∧
      s'.gpr .r8 = BitVec.ofNat 64 ((s.gpr .r13).toNat % 16) ∧
      s'.zf = some (decide ((s.gpr .r13).toNat % 16 = 0)) ∧
      (∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e : s.gpr .r13 - BitVec.ofNat 64 (16 * ((s.gpr .r13).toNat / 16)) =
      BitVec.ofNat 64 ((s.gpr .r13).toNat % 16) := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .r13).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega)]
    omega
  refine ⟨_, by
    simp only [split, runBlock_cons, runStep_some, exec, readSrc, execShift,
      Option.map_some, show 1 ≤ 4 ∧ 4 ≤ 63 from by decide]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ↓reduceIte, shr4_shl4]
  · simp only [gpr_setReg, gpr_setFlags, reduceCtorEq, ↓reduceIte, shr4_shl4, e]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_setFlags, reduceCtorEq, ↓reduceIte,
      shr4_shl4, e]
    rw [beq_zero64 (by omega)]
  · intro r h₁ h₂; simp [gpr_setReg, gpr_setFlags, h₁, h₂]

theorem lastAddr_ok (s : State) :
    ∃ s', runBlock isa lastAddr s = some s' ∧ s'.gpr .rdx = s.gpr .r12 + s.gpr .rax - 16 ∧
      (∀ r, r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [lastAddr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg]
  · intro r h; simp [gpr_setReg, h]

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : Addr) {m : Nat} (hm : 1 ≤ m) (h : 16 * m < 2 ^ 64) :
    p + BitVec.ofNat 64 (16 * m) - 16 = p + BitVec.ofNat 64 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega, ← Offset.add_add]
  exact BitVec.add_sub_cancel _ _

theorem argsL_ok (s : State) {o : Nat} (ho : BitVec.signExtend 64 (BitVec.ofNat 32 o) = BitVec.ofNat 64 o) :
    ∃ s', runBlock isa (argsL o) s = some s' ∧
      s'.gpr .rdi = s.gpr .rbx ∧ s'.gpr .rsi = s.gpr .rbp ∧
      s'.gpr .rdx = s.gpr .r15 + BitVec.ofNat 64 o ∧ s'.gpr .rcx = s.gpr .rdx ∧
      s'.gpr .r8 = 1 ∧ s'.gpr .r9 = s.gpr .r15 ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [argsL, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
      Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32, ho]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · simp [gpr_setReg, State.setReg32]
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [gpr_setReg, State.setReg32]

/-! ## The swap -/

theorem swapStep_ok (s : State) {L : Addr} {k b : Nat} (hd : s.gpr .rdx = L)
    (hc : s.gpr .rcx = BitVec.ofNat 64 k) (h8 : s.gpr .r8 = BitVec.ofNat 64 b)
    (w₀ : InRegions s.wr (L + BitVec.ofNat 64 k) 1) (w₁ : InRegions s.wr (L + BitVec.ofNat 64 (16 + k)) 1) :
    ∃ s', runBlock isa swapBody s = some s' ∧
      s'.mem = (s.mem.writeW (L + BitVec.ofNat 64 k) (s.mem (L + BitVec.ofNat 64 (16 + k)))).writeW
        (L + BitVec.ofNat 64 (16 + k)) (s.mem (L + BitVec.ofNat 64 k)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 k + 1 ∧
      s'.zf = some (BitVec.ofNat 64 k + 1 - BitVec.ofNat 64 b == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 k) 1 :=
    let ⟨r, hr, c⟩ := w₀; ⟨r, List.mem_append_right _ hr, c⟩
  have r₁ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 (16 + k)) 1 :=
    let ⟨r, hr, c⟩ := w₁; ⟨r, List.mem_append_right _ hr, c⟩
  have ea₀ : s.gpr .rdx + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = L + BitVec.ofNat 64 k := by
    rw [hd, hc, BitVec.mul_one]; simp
  have ea₁ : s.gpr .rdx + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofInt 64 16 = L + BitVec.ofNat 64 (16 + k) := by
    rw [hd, hc, BitVec.mul_one, BitVec.add_assoc, Nat.add_comm, BitVec.ofNat_add]; rfl
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, swapBody, lo, hi, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, State.load8, State.store8, State.ea, Option.bind_some, Option.map_some, gpr_setReg,
      mem_setReg, rd_setReg, wr_setReg, ea₀, ea₁, r₀, r₁, w₀, w₁]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide),
      BitVec.setWidth_eq]
  · simp [gpr_setReg, hc]
  · simp [gpr_setReg, hc, h8]
  · intro r h₁ h₂ h₃; simp [gpr_setReg, h₁, h₂, h₃]

theorem swap_ok (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hd : s.gpr .rdx = L)
    (hc : s.gpr .rcx = 0) (h8 : s.gpr .r8 = BitVec.ofNat 64 b)
    (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => s'.mem = swapMem s.mem L b ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .rcx = BitVec.ofNat 64 k ∧
      t.mem = swapMem s.mem L k ∧
      (∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (b - 0) _
    ⟨0, rfl, hb₀, hc, (Proof.AesXts.Unit.swapMem_zero _ _).symm, fun _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨k, rfl, hk, rcx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', rcx', zf', g', rd', wr'⟩ := swapStep_ok t (k := k) (b := b)
    (by rw [g _ (by decide) (by decide) (by decide), hd]) rcx (by rw [g _ (by decide) (by decide) (by decide), h8])
    (by rw [wr]; exact hw k (by omega)) (by rw [wr]; exact hw (16 + k) (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega), swapMem_hi _ _ (Nat.le_refl k) (by omega),
      swapMem_step _ _ (by omega)]
  have hz : t'.zf = some (decide (k + 1 = b)) := by
    rw [zf', Offset.add_one_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .rcx → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  by_cases he : k + 1 = b
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by simp [eval, hz, he], b - (k + 1), by omega, k + 1, rfl, by omega, ?_, hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩
    rw [rcx', Offset.add_one_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-! ## The next tweak -/

theorem nextT_ok (s : State) {T Z : Addr} (ht : s.gpr .r15 + BitVec.ofNat 64 tO = T)
    (ht8 : s.gpr .r15 + BitVec.ofNat 64 (tO + 8) = T + BitVec.ofNat 64 8)
    (hz : s.gpr .r15 + BitVec.ofNat 64 zO = Z) (hz8 : s.gpr .r15 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8)
    (r0 : InRegions (s.rd ++ s.wr) T 8) (r8 : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 8) 8)
    (w0 : InRegions s.wr Z 8) (w8 : InRegions s.wr (Z + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa nextT s = some s' ∧ (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      Frame [⟨Z, 16⟩] s.mem s'.mem ∧ bytesAt s'.mem Z 16 = Spec.Xts.mulAlpha (bytesAt s.mem T 16) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, g₁, rax₁, rcx₁, mem₁, rd₁, wr₁⟩ : ∃ s₁,
      runBlock isa [.mov .rax (.mem (at_ .r15 tO)), .mov .rcx (.mem (at_ .r15 (tO + 8)))] s = some s₁ ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s₁.gpr r = s.gpr r) ∧ s₁.gpr .rax = s.mem.readW T 64 ∧
      s₁.gpr .rcx = s.mem.readW (T + BitVec.ofNat 64 8) 64 ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc,
        State.load64, State.ea, offset_nat, Option.map_some, gpr_setReg, mem_setReg, rd_setReg,
        wr_setReg, ht, ht8, r0, r8]
      rfl, ?_⟩
    refine ⟨fun r h₁ h₂ => ?_, ?_, ?_, rfl, rfl, rfl⟩
    · simp [gpr_setReg, h₁, h₂]
    · simp [gpr_setReg]
    · simp [gpr_setReg]
  obtain ⟨s₂, run₂, g₂, rax₂, rcx₂, mem₂, rd₂, wr₂⟩ := Proof.AesXts.X86_64.mulA_ok s₁
  have z₂ : s₂.gpr .r15 + BitVec.ofNat 64 zO = Z := by rw [g₂ _ (by decide) (by decide) (by decide),
    g₁ _ (by decide) (by decide), hz]
  have z₂8 : s₂.gpr .r15 + BitVec.ofNat 64 (zO + 8) = Z + BitVec.ofNat 64 8 := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), hz8]
  have w₂0 : InRegions s₂.wr Z 8 := by rw [wr₂, wr₁]; exact w0
  have w₂8 : InRegions s₂.wr (Z + BitVec.ofNat 64 8) 8 := by rw [wr₂, wr₁]; exact w8
  refine ⟨_, by
    rw [nextT, runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some]
    simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, at_, exec, State.store64, State.ea,
      offset_nat, z₂, z₂8, w₂0, w₂8]
    rfl, ?_⟩
  refine ⟨fun r h₁ h₂ h₃ => ?_, ?_, ?_, by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · show s₂.gpr r = s.gpr r
    rw [g₂ r h₁ h₂ h₃, g₁ r h₁ h₂]
  · show Frame [⟨Z, 16⟩] s.mem ((s₂.mem.writeW Z (s₂.gpr .rax)).writeW (Z + BitVec.ofNat 64 8) (s₂.gpr .rcx))
    rw [mem₂, mem₁]; exact AesCbc.frame_store2 _ _ _
  · show bytesAt ((s₂.mem.writeW Z (s₂.gpr .rax)).writeW (Z + BitVec.ofNat 64 8) (s₂.gpr .rcx)) Z 16 = _
    rw [Proof.Cmac.bytesAt_store2, rax₂, rcx₂, rax₁, rcx₁, ← Proof.AesXts.X86_64.tw_readW s.mem T,
      ← Proof.AesXts.X86_64.mulAlpha_le8]

end VG.Proof.AesXts.X86_64.Unit
