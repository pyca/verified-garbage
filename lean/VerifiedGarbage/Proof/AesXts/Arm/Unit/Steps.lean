module

import VerifiedGarbage.Proof.AesXts.Arm.Steps
public import VerifiedGarbage.Proof.Cmac.Mem32
public import VerifiedGarbage.Impl.AesXts.ArmUnit
public import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# XTS-AES of data units on ARMv7: the code between the calls

Each straight-line piece of `encrypt` and `decrypt`, run once, with the
registers and memory it leaves, and the swap loop (`swap_ok`), which leaves
`swapMem` (`Proof/AesXts/Unit.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesXts.ArmUnit
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.MdStream.Arm (op2_reg op2_imm op2_lsr op2_lsl)
open VG.Proof.AesXts.Unit (swapMem swapMem_step swapMem_lo swapMem_hi)
open VG.Spec.Aes (bytesAt)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (exec x s).bind (runBlock isa (a ++ b)) = ((exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

/-- The block at `Q` copied to `P`, a word at a time, read before any is written. -/
def copy4 (m : Mem) (P Q : Addr) : Mem :=
  Proof.Cmac.store4 m P (m.readW Q 32) (m.readW (Q + BitVec.ofNat 64 4) 32) (m.readW (Q + BitVec.ofNat 64 8) 32)
    (m.readW (Q + BitVec.ofNat 64 12) 32)

theorem copy4_frame (m : Mem) (P Q : Addr) : Frame [⟨P, 16⟩] m (copy4 m P Q) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem copy4_bytes (m : Mem) (P Q : Addr) : bytesAt (copy4 m P Q) P 16 = bytesAt m Q 16 := by
  rw [copy4, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, ← Proof.Cmac.bytesAt_split4]

/-- The block at `c` zeroed. -/
def zero4 (m : Mem) (c : Addr) : Mem := Proof.Cmac.store4 m c 0 0 0 0

theorem zero4_frame (m : Mem) (c : Addr) : Frame [⟨c, 16⟩] m (zero4 m c) := Proof.Cmac.frame_store4 _ _ _ _ _

theorem zero4_bytes (m : Mem) (c : Addr) : bytesAt (zero4 m c) c 16 = List.replicate 16 0 := by
  rw [zero4, Proof.Cmac.bytesAt_store4]; decide

/-- The words of a block at an offset of a register, as addresses. -/
theorem addrs_of {s : State} {b : Reg} {e : Nat} {Q : Addr} (hq : State.addr (s.gpr b) + BitVec.ofNat 64 e = Q)
    (hf : (s.gpr b).toNat + e + 16 ≤ 2 ^ 32) (k : Nat) (hk : k < 16) :
    State.addr (s.gpr b + BitVec.ofNat 32 (e + k)) = Q + BitVec.ofNat 64 k := by
  rw [addr_add (by omega), ← Offset.add_add, hq]

theorem addr0_of {s : State} {b : Reg} {e : Nat} {Q : Addr} (hq : State.addr (s.gpr b) + BitVec.ofNat 64 e = Q)
    (hf : (s.gpr b).toNat + e + 16 ≤ 2 ^ 32) : State.addr (s.gpr b + BitVec.ofNat 32 e) = Q := by
  rw [addr_add (by omega), hq]

/-- `i` copied to the tweak. -/
theorem copyI_ok (s : State) {P Q : Addr} (hq : State.addr (s.gpr .r3) + BitVec.ofNat 64 0 = Q)
    (hqf : (s.gpr .r3).toNat + 0 + 16 ≤ 2 ^ 32) (hp : State.addr (s.gpr .r8) + BitVec.ofNat 64 tO = P)
    (hpf : (s.gpr .r8).toNat + tO + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa (copy .r12 .lr .r0 .r2 .r8 tO .r3 0) s = some s' ∧
      (∀ r, r ≠ .r12 → r ≠ .lr → r ≠ .r0 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = copy4 s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a := addrs_of hq hqf
  have b := addrs_of hp hpf
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr P 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, copy, runBlock_cons, runStep_some, runBlock_nil, exec,
      State.load32, State.store32, Option.map_some, Nat.reduceLT, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      show tO < 4096 from by decide, show tO + 4 < 4096 from by decide, show tO + 8 < 4096 from by decide,
      show tO + 12 < 4096 from by decide, show 0 + 4 < 4096 from by decide, show 0 + 8 < 4096 from by decide,
      show 0 + 12 < 4096 from by decide, addr0_of hq hqf, addr0_of hp hpf, a 4 (by decide), a 8 (by decide),
      a 12 (by decide), b 4 (by decide), b 8 (by decide), b 12 (by decide), r0, hr 4 4 (by decide),
      hr 8 4 (by decide), hr 12 4 (by decide), w0, hw 4 4 (by decide), hw 8 4 (by decide), hw 12 4 (by decide)]
    rfl, ?_⟩
  exact ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_setReg, h₁, h₂, h₃, h₄], rfl, rfl, rfl, rfl⟩

/-- The tweak copied to the second tweak. -/
theorem copyT_ok (s : State) {P Q : Addr} (hq : State.addr (s.gpr .r8) + BitVec.ofNat 64 tO = Q)
    (hqf : (s.gpr .r8).toNat + tO + 16 ≤ 2 ^ 32) (hp : State.addr (s.gpr .r8) + BitVec.ofNat 64 zO = P)
    (hpf : (s.gpr .r8).toNat + zO + 16 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa (copy .r0 .r1 .r2 .r3 .r8 zO .r8 tO) s = some s' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = copy4 s.mem P Q ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a := addrs_of hq hqf
  have b := addrs_of hp hpf
  have r0 : InRegions (s.rd ++ s.wr) Q 4 := by simpa using hr 0 4 (by decide)
  have w0 : InRegions s.wr P 4 := by simpa using hw 0 4 (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, copy, runBlock_cons, runStep_some, runBlock_nil, exec,
      State.load32, State.store32, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      show tO < 4096 from by decide, show tO + 4 < 4096 from by decide, show tO + 8 < 4096 from by decide,
      show tO + 12 < 4096 from by decide, show zO < 4096 from by decide, show zO + 4 < 4096 from by decide,
      show zO + 8 < 4096 from by decide, show zO + 12 < 4096 from by decide, addr0_of hq hqf, addr0_of hp hpf,
      a 4 (by decide), a 8 (by decide), a 12 (by decide), b 4 (by decide), b 8 (by decide), b 12 (by decide),
      r0, hr 4 4 (by decide), hr 8 4 (by decide), hr 12 4 (by decide), w0, hw 4 4 (by decide),
      hw 8 4 (by decide), hw 12 4 (by decide)]
    rfl, ?_⟩
  exact ⟨fun r h₁ h₂ h₃ h₄ => by simp [gpr_setReg, h₁, h₂, h₃, h₄], rfl, rfl, rfl, rfl⟩

theorem zeroZ_ok (s : State) {Z : Addr} (hz : State.addr (s.gpr .r8) + BitVec.ofNat 64 zO = Z)
    (hzf : (s.gpr .r8).toNat + zO + 16 ≤ 2 ^ 32) (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Z + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa zeroZ s = some s' ∧ (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.mem = zero4 s.mem Z ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have b := addrs_of hz hzf
  have w0 : InRegions s.wr Z 4 := by simpa using hw 0 4 (by decide)
  have i0 (t : State) : (Op2.imm 0).eval t = some 0 := op2_imm (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, zeroZ, runBlock_cons, runStep_some, runBlock_nil, exec, i0,
      State.store32, Option.map_some, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      show zO < 4096 from by decide, show zO + 4 < 4096 from by decide,
      show zO + 8 < 4096 from by decide, show zO + 12 < 4096 from by decide, addr0_of hz hzf,
      b 4 (by decide), b 8 (by decide), b 12 (by decide), w0, hw 4 4 (by decide), hw 8 4 (by decide),
      hw 12 4 (by decide)]
    rfl, ?_⟩
  exact ⟨fun r h => by simp [gpr_setReg, h], rfl, rfl, rfl, rfl⟩

theorem preserved_ne (r : Reg) (hr : r ∈ preserved) (hl : r ≠ .lr) :
    r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl hl

theorem ez : encodable (BitVec.ofNat 32 zO) = true := by decide
theorem et : encodable (BitVec.ofNat 32 tO) = true := by decide

theorem tArgs_ok (s : State) :
    ∃ s', runBlock isa tArgs s = some s' ∧
      s'.gpr .r0 = s.gpr .r1 ∧ s'.gpr .r1 = s.gpr .r5 ∧
      s'.gpr .r2 = s.gpr .r8 + BitVec.ofNat 32 zO ∧ s'.gpr .r3 = s.gpr .r8 + BitVec.ofNat 32 tO ∧
      s'.gpr .r12 = BitVec.ofNat 32 1 ∧ s'.gpr .lr = s.gpr .r8 ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := op2_imm (by decide)
  have iz (t : State) : (Op2.imm (BitVec.ofNat 32 zO)).eval t = some (BitVec.ofNat 32 zO) := op2_imm ez
  have it (t : State) : (Op2.imm (BitVec.ofNat 32 tO)).eval t = some (BitVec.ofNat 32 tO) := op2_imm et
  refine ⟨_, by
    simp only [tArgs, mov, runBlock_cons, runStep_some, runBlock_nil, exec, op2_reg, i1, iz, it, Option.map_some]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], fun r hr hl => ?_, rfl, rfl, rfl, rfl⟩
  obtain ⟨h₀, h₁, h₂, h₃, h₁₂⟩ := preserved_ne r hr hl
  simp [gpr_setReg, h₀, h₁, h₂, h₃, h₁₂, hl]

theorem shr4 (x : BitVec 32) : x >>> 4 = BitVec.ofNat 32 (x.toNat / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem shr4_shl4 (x : BitVec 32) : (x >>> 4) <<< 4 = BitVec.ofNat 32 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.reducePow]
  omega

theorem argsAll_ok (s : State) :
    ∃ s', runBlock isa argsAll s = some s' ∧
      s'.gpr .r0 = s.gpr .r4 ∧ s'.gpr .r1 = s.gpr .r5 ∧
      s'.gpr .r2 = s.gpr .r8 + BitVec.ofNat 32 tO ∧ s'.gpr .r3 = s.gpr .r9 ∧
      s'.gpr .r12 = BitVec.ofNat 32 ((s.gpr .r7).toNat / 16) ∧ s'.gpr .lr = s.gpr .r8 ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have it (t : State) : (Op2.imm (BitVec.ofNat 32 tO)).eval t = some (BitVec.ofNat 32 tO) := op2_imm et
  have l4 (t : State) : (Op2.shifted .r7 .lsr 4).eval t = some (t.gpr .r7 >>> 4) := op2_lsr (by decide)
  refine ⟨_, by
    simp only [argsAll, mov, runBlock_cons, runStep_some, runBlock_nil, exec, op2_reg, it, l4, Option.map_some]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg, shr4], by simp [gpr_setReg], fun r hr hl => ?_, rfl, rfl, rfl, rfl⟩
  obtain ⟨h₀, h₁, h₂, h₃, h₁₂⟩ := preserved_ne r hr hl
  simp [gpr_setReg, h₀, h₁, h₂, h₃, h₁₂, hl]

theorem argsHead_ok (s : State) (hm : 1 ≤ (s.gpr .r7).toNat / 16) :
    ∃ s', runBlock isa argsHead s = some s' ∧
      s'.gpr .r0 = s.gpr .r4 ∧ s'.gpr .r1 = s.gpr .r5 ∧
      s'.gpr .r2 = s.gpr .r8 + BitVec.ofNat 32 tO ∧ s'.gpr .r3 = s.gpr .r9 ∧
      s'.gpr .r12 = BitVec.ofNat 32 ((s.gpr .r7).toNat / 16 - 1) ∧ s'.gpr .lr = s.gpr .r8 ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, x0₁, x1₁, x2₁, x3₁, x12₁, lr₁, cs₁, sp₁, mem₁, rd₁, wr₁⟩ := argsAll_ok s
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := op2_imm (by decide)
  have run : runBlock isa argsHead s = some (s₁.setReg .r12 (s₁.gpr .r12 - 1)) := by
    rw [argsHead, runBlock_append, run₁, Option.bind_some]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, i1, Option.map_some]
  refine ⟨_, run, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr hl => ?_, sp₁, mem₁, rd₁, wr₁⟩
  · simp [gpr_setReg, x0₁]
  · simp [gpr_setReg, x1₁]
  · simp [gpr_setReg, x2₁]
  · simp [gpr_setReg, x3₁]
  · simp only [gpr_setReg, ite_true, x12₁]
    exact Proof.MdStream.Arm.sub_ofNat hm
  · simp [gpr_setReg, lr₁]
  · rw [gpr_setReg_of_ne _ _ (preserved_ne r hr hl).2.2.2.2, cs₁ r hr hl]

theorem split_ok (s : State) :
    ∃ s', runBlock isa split s = some s' ∧
      s'.gpr .r0 = BitVec.ofNat 32 (16 * ((s.gpr .r7).toNat / 16)) ∧
      s'.gpr .r1 = BitVec.ofNat 32 ((s.gpr .r7).toNat % 16) ∧
      s'.z = decide ((s.gpr .r7).toNat % 16 = 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have e : s.gpr .r7 - BitVec.ofNat 32 (16 * ((s.gpr .r7).toNat / 16)) =
      BitVec.ofNat 32 ((s.gpr .r7).toNat % 16) := by
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .r7).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega)]
    omega
  have l4 (t : State) : (Op2.shifted .r7 .lsr 4).eval t = some (t.gpr .r7 >>> 4) := op2_lsr (by decide)
  have k4 (t : State) : (Op2.shifted .r0 .lsl 4).eval t = some (t.gpr .r0 <<< 4) := op2_lsl (by decide)
  refine ⟨_, by
    simp only [split, runBlock_cons, runStep_some, runBlock_nil, exec, op2_reg, l4, k4, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_setReg, subFlags, shr4_shl4]
  · simp only [gpr_setReg, subFlags, reduceCtorEq, ↓reduceIte, shr4_shl4, e]
  · simp only [z_setReg, subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte, shr4_shl4, e]
    exact Proof.MdStream.Arm.ofNat_beq_zero (by omega)
  · simp [gpr_setReg, subFlags, h₁, h₂]

theorem lastAddr_ok (s : State) :
    ∃ s', runBlock isa lastAddr s = some s' ∧ s'.gpr .r2 = s.gpr .r9 + s.gpr .r0 - 16 ∧
      (∀ r, r ≠ .r2 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i16 (t : State) : (Op2.imm 16).eval t = some 16 := op2_imm (by decide)
  refine ⟨_, by
    simp only [lastAddr, runBlock_cons, runStep_some, runBlock_nil, exec, op2_reg, i16, Option.map_some]
    rfl, ?_⟩
  exact ⟨by simp [gpr_setReg], fun r h => by simp [gpr_setReg, h], rfl, rfl, rfl, rfl⟩

/-- The last whole block, from the bytes of the whole blocks. -/
theorem last_eq (p : BitVec 32) {m : Nat} (hm : 1 ≤ m) :
    p + BitVec.ofNat 32 (16 * m) - 16 = p + BitVec.ofNat 32 (16 * (m - 1)) := by
  rw [show 16 * m = 16 * (m - 1) + 16 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem argsL_ok (s : State) {o : Nat} (ho : encodable (BitVec.ofNat 32 o) = true) :
    ∃ s', runBlock isa (argsL o) s = some s' ∧
      s'.gpr .r0 = s.gpr .r4 ∧ s'.gpr .r1 = s.gpr .r5 ∧
      s'.gpr .r2 = s.gpr .r8 + BitVec.ofNat 32 o ∧ s'.gpr .r3 = s.gpr .r9 + s.gpr .r0 - 16 ∧
      s'.gpr .r12 = BitVec.ofNat 32 1 ∧ s'.gpr .lr = s.gpr .r8 ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := op2_imm (by decide)
  have i16 (t : State) : (Op2.imm 16).eval t = some 16 := op2_imm (by decide)
  have io (t : State) : (Op2.imm (BitVec.ofNat 32 o)).eval t = some (BitVec.ofNat 32 o) := op2_imm ho
  refine ⟨_, by
    simp only [argsL, mov, runBlock_cons, runStep_some, runBlock_nil, exec, op2_reg, i1, i16, io, Option.map_some]
    rfl, ?_⟩
  refine ⟨by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg], by simp [gpr_setReg],
    by simp [gpr_setReg], by simp [gpr_setReg], fun r hr hl => ?_, rfl, rfl, rfl, rfl⟩
  obtain ⟨h₀, h₁, h₂, h₃, h₁₂⟩ := preserved_ne r hr hl
  simp [gpr_setReg, h₀, h₁, h₂, h₃, h₁₂, hl]

/-! ## The swap -/

theorem byte_rt (b : Byte) : BitVec.setWidth 8 (BitVec.setWidth 32 b) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem swapStep_ok (s : State) {L : Addr} {k b : Nat} (hx : State.addr (s.gpr .r2) = L + BitVec.ofNat 64 k)
    (hxf : (s.gpr .r2).toNat + 17 ≤ 2 ^ 32) (hc : s.gpr .r1 = BitVec.ofNat 32 b) (hb : 1 ≤ b) (hb' : b < 16)
    (w₀ : InRegions s.wr (L + BitVec.ofNat 64 k) 1) (w₁ : InRegions s.wr (L + BitVec.ofNat 64 (16 + k)) 1) :
    ∃ s', runBlock isa swapBody s = some s' ∧
      s'.mem = (s.mem.writeW (L + BitVec.ofNat 64 k) (s.mem (L + BitVec.ofNat 64 (16 + k)))).writeW
        (L + BitVec.ofNat 64 (16 + k)) (s.mem (L + BitVec.ofNat 64 k)) ∧
      s'.gpr .r2 = s.gpr .r2 + 1 ∧ s'.gpr .r1 = BitVec.ofNat 32 (b - 1) ∧ s'.z = decide (b - 1 = 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 k) 1 :=
    let ⟨r, hr, c⟩ := w₀; ⟨r, List.mem_append_right _ hr, c⟩
  have r₁ : InRegions (s.rd ++ s.wr) (L + BitVec.ofNat 64 (16 + k)) 1 :=
    let ⟨r, hr, c⟩ := w₁; ⟨r, List.mem_append_right _ hr, c⟩
  have a0 : State.addr (s.gpr .r2 + BitVec.ofNat 32 0) = L + BitVec.ofNat 64 k := by
    rw [BitVec.add_zero]; exact hx
  have a16 : State.addr (s.gpr .r2 + BitVec.ofNat 32 16) = L + BitVec.ofNat 64 (16 + k) := by
    rw [addr_add (by omega), hx, Offset.add_add, Nat.add_comm]
  have i1 (t : State) : (Op2.imm 1).eval t = some 1 := op2_imm (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, swapBody, runBlock_cons, runStep_some, runBlock_nil, exec, i1,
      State.load8, State.store8, Option.map_some, Nat.reduceLT, gpr_setReg, mem_setReg, rd_setReg, wr_setReg,
      a0, a16, r₀, r₁, w₀, w₁]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => by simp [gpr_setReg, subFlags, h₁, h₂, h₃, h₄], rfl, rfl, rfl⟩
  · simp only [mem_setReg, subFlags, byte_rt]
  · simp [gpr_setReg, subFlags]
  · simp only [gpr_setReg, subFlags, ↓reduceIte, hc]
    exact Proof.MdStream.Arm.sub_ofNat hb
  · have e1 : BitVec.ofNat 32 b - 1 = BitVec.ofNat 32 (b - 1) := Proof.MdStream.Arm.sub_ofNat hb
    simp only [z_setReg, subFlags, hc, e1]
    exact Proof.MdStream.Arm.ofNat_beq_zero (by omega)

theorem swap_ok (s : State) {L : Addr} {b : Nat} (hb₀ : 0 < b) (hb : b < 16) (hx : State.addr (s.gpr .r2) = L)
    (hxf : (s.gpr .r2).toNat + 16 + b ≤ 2 ^ 32) (hc : s.gpr .r1 = BitVec.ofNat 32 b)
    (hw : ∀ i < 16 + b, InRegions s.wr (L + BitVec.ofNat 64 i) 1) :
    WP isa swap s fun s' => s'.mem = swapMem s.mem L b ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block swapBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ k, n = b - k ∧ k < b ∧ t.gpr .r2 = s.gpr .r2 + BitVec.ofNat 32 k ∧
      t.gpr .r1 = BitVec.ofNat 32 (b - k) ∧ t.mem = swapMem s.mem L k ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      t.wr = s.wr) ?_ (b - 0) _
    ⟨0, rfl, hb₀, by rw [BitVec.add_zero], hc, (Proof.AesXts.Unit.swapMem_zero _ _).symm,
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨k, rfl, hk, r2, r1, mem, g, sp, rd, wr⟩
  have hx' : State.addr (t.gpr .r2) = L + BitVec.ofNat 64 k := by rw [r2, addr_add (by omega), hx]
  have hxf' : (t.gpr .r2).toNat + 17 ≤ 2 ^ 32 := by
    rw [r2, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨t', run', mem', r2', r1', z', g', sp', rd', wr'⟩ := swapStep_ok t (k := k) (b := b - k) hx' hxf' r1
    (by omega) (by omega) (by rw [wr]; exact hw k (by omega)) (by rw [wr]; exact hw (16 + k) (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega), swapMem_hi _ _ (Nat.le_refl k) (by omega),
      swapMem_step _ _ (by omega)]
  have hz : isa.eval .ne t' = some !decide (b - k - 1 = 0) := by
    show VG.Arm.eval .ne t' = _; rw [Proof.MdStream.Arm.eval_ne, z']
  have gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [hz]; simp [show b - k - 1 = 0 by omega], by rw [hmem, he], gg, by rw [sp', sp],
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [hz]; simp [show b - k - 1 ≠ 0 by omega], b - (k + 1), by omega, k + 1, rfl, by omega, ?_,
      by rw [r1', show b - k - 1 = b - (k + 1) by omega], hmem, gg, by rw [sp', sp], by rw [rd', rd],
      by rw [wr', wr]⟩
    rw [r2', r2, BitVec.add_assoc, show BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) from
      (BitVec.ofNat_add k 1).symm]

/-! ## The next tweak -/

theorem nextT_ok (s : State) {T Z : Addr} (ht : State.addr (s.gpr .r8) + BitVec.ofNat 64 tO = T)
    (hz : State.addr (s.gpr .r8) + BitVec.ofNat 64 zO = Z) (hf : (s.gpr .r8).toNat + 2208 ≤ 2 ^ 32)
    (hr : ∀ d n, d + n ≤ 16 → InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 d) n)
    (hw : ∀ d n, d + n ≤ 16 → InRegions s.wr (Z + BitVec.ofNat 64 d) n) :
    ∃ s', runBlock isa nextT s = some s' ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → r ≠ .r6 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ Frame [⟨Z, 16⟩] s.mem s'.mem ∧
      bytesAt s'.mem Z 16 = Spec.Xts.mulAlpha (bytesAt s.mem T 16) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have iz (t : State) : (Op2.imm (BitVec.ofNat 32 zO)).eval t = some (BitVec.ofNat 32 zO) := op2_imm ez
  obtain ⟨s₁, run₁, e₁⟩ : ∃ s₁, runBlock isa [.dp .add .r6 .r8 (.imm (BitVec.ofNat 32 zO))] s = some s₁ ∧
      s₁ = s.setReg .r6 (s.gpr .r8 + BitVec.ofNat 32 zO) := by
    refine ⟨_, ?_, rfl⟩
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, iz, Option.map_some]
  subst e₁
  have g8 : (s.setReg .r6 (s.gpr .r8 + BitVec.ofNat 32 zO)).gpr .r8 = s.gpr .r8 :=
    gpr_setReg_of_ne _ _ (by decide)
  obtain ⟨s₂, run₂, g₂, sp₂, mem₂, rd₂, wr₂⟩ := copyT_ok (s.setReg .r6 (s.gpr .r8 + BitVec.ofNat 32 zO))
    (P := Z) (Q := T) (by rw [g8, ht]) (by rw [g8]; simp only [tO]; omega) (by rw [g8, hz])
    (by rw [g8]; simp only [zO]; omega) hr hw
  have r6₂ : State.addr (s₂.gpr .r6) = Z := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), gpr_setReg_self, addr_add (by simp only [zO]; omega),
      hz]
  have r6f : (s₂.gpr .r6).toNat + 16 ≤ 2 ^ 32 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), gpr_setReg_self, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := zO) (by simp only [zO]; omega), Nat.mod_eq_of_lt (by simp only [zO]; omega)]
    simp only [zO]; omega
  obtain ⟨s₃, run₃, g₃, sp₃, mem₃, rd₃, wr₃⟩ := Proof.AesXts.Arm.mulA_ok s₂ (Q := Z) r6₂ r6f
    (fun d n h => by
      rw [rd₂, wr₂]
      obtain ⟨r, hr', c⟩ := hw d n h
      exact ⟨r, List.mem_append_right _ hr', c⟩)
    (fun d n h => by rw [wr₂]; exact hw d n h)
  refine ⟨s₃, by
    rw [nextT, runBlock_append, runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃], ?_⟩
  refine ⟨fun r h₀ h₁ h₂ h₃ h₁₂ hl h₆ => ?_, by rw [sp₃, sp₂]; rfl, ?_, ?_, by rw [rd₃, rd₂]; rfl,
    by rw [wr₃, wr₂]; rfl⟩
  · rw [g₃ r h₀ h₁ h₂ h₃ h₁₂ hl, g₂ r h₀ h₁ h₂ h₃]; exact gpr_setReg_of_ne _ _ h₆
  · rw [mem₃, mem₂]
    exact (copy4_frame _ _ _).trans (Proof.AesXts.Arm.alphaMem_frame _ _)
  · rw [mem₃, Proof.AesXts.Arm.alphaMem_bytes, mem₂, copy4_bytes]; rfl

end VG.Proof.AesXts.Arm.Unit
