module

import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Argon2.Arm.Push
public import VerifiedGarbage.Proof.AesCbc.Arm.Loop
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Impl.AesXts.ArmUnit
import VerifiedGarbage.Proof.AesXts.Arm.Body
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.AesXts.Arm.Steps
public import VerifiedGarbage.Proof.Cmac.Mem32
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `AesXts.Arm.Unit.Steps`, which this module and modules that import it used -/

section

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
  rw [addr_add (by omega_arith), ← Offset.add_add, hq]

theorem addr0_of {s : State} {b : Reg} {e : Nat} {Q : Addr} (hq : State.addr (s.gpr b) + BitVec.ofNat 64 e = Q)
    (hf : (s.gpr b).toNat + e + 16 ≤ 2 ^ 32) : State.addr (s.gpr b + BitVec.ofNat 32 e) = Q := by
  rw [addr_add (by omega_arith), hq]

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
    Nat.mod_eq_of_lt (by have := x.isLt; omega_arith)]

theorem shr4_shl4 (x : BitVec 32) : (x >>> 4) <<< 4 = BitVec.ofNat 32 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  simp only [Nat.reducePow]
  omega_arith

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
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * _) (by omega_arith),
      Nat.mod_eq_of_lt (a := _ % 16) (by omega_arith)]
    omega_arith
  have l4 (t : State) : (Op2.shifted .r7 .lsr 4).eval t = some (t.gpr .r7 >>> 4) := op2_lsr (by decide)
  have k4 (t : State) : (Op2.shifted .r0 .lsl 4).eval t = some (t.gpr .r0 <<< 4) := op2_lsl (by decide)
  refine ⟨_, by
    simp only [split, runBlock_cons, runStep_some, runBlock_nil, exec, op2_reg, l4, k4, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, fun r h₁ h₂ => ?_, rfl, rfl, rfl, rfl⟩
  · simp [gpr_setReg, subFlags, shr4_shl4]
  · simp only [gpr_setReg, subFlags, reduceCtorEq, ↓reduceIte, shr4_shl4, e]
  · simp only [z_setReg, subFlags, gpr_setReg, reduceCtorEq, ↓reduceIte, shr4_shl4, e]
    exact Proof.MdStream.Arm.ofNat_beq_zero (by omega_arith)
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
  rw [show 16 * m = 16 * (m - 1) + 16 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc]
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
  omega_arith

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
    rw [addr_add (by omega_arith), hx, Offset.add_add, Nat.add_comm]
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
    exact Proof.MdStream.Arm.ofNat_beq_zero (by omega_arith)

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
  have hx' : State.addr (t.gpr .r2) = L + BitVec.ofNat 64 k := by rw [r2, addr_add (by omega_arith), hx]
  have hxf' : (t.gpr .r2).toNat + 17 ≤ 2 ^ 32 := by
    rw [r2, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  obtain ⟨t', run', mem', r2', r1', z', g', sp', rd', wr'⟩ := swapStep_ok t (k := k) (b := b - k) hx' hxf' r1
    (by omega_arith) (by omega_arith) (by rw [wr]; exact hw k (by omega_arith)) (by rw [wr]; exact hw (16 + k) (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = swapMem s.mem L (k + 1) := by
    rw [mem', mem, swapMem_lo _ _ (Nat.le_refl k) (by omega_arith), swapMem_hi _ _ (Nat.le_refl k) (by omega_arith),
      swapMem_step _ _ (by omega_arith)]
  have hz : isa.eval .ne t' = some !decide (b - k - 1 = 0) := by
    show VG.Arm.eval .ne t' = _; rw [Proof.MdStream.Arm.eval_ne, z']
  have gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : k + 1 = b
  · left
    refine ⟨by rw [hz]; simp [show b - k - 1 = 0 by omega_arith], by rw [hmem, he], gg, by rw [sp', sp],
      by rw [rd', rd], by rw [wr', wr]⟩
  · right
    refine ⟨by rw [hz]; simp [show b - k - 1 ≠ 0 by omega_arith], b - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, ?_,
      by rw [r1', show b - k - 1 = b - (k + 1) by omega_arith], hmem, gg, by rw [sp', sp], by rw [rd', rd],
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
    (P := Z) (Q := T) (by rw [g8, ht]) (by rw [g8]; simp only [tO]; omega_arith) (by rw [g8, hz])
    (by rw [g8]; simp only [zO]; omega_arith) hr hw
  have r6₂ : State.addr (s₂.gpr .r6) = Z := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), gpr_setReg_self, addr_add (by simp only [zO]; omega_arith),
      hz]
  have r6f : (s₂.gpr .r6).toNat + 16 ≤ 2 ^ 32 := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide), gpr_setReg_self, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := zO) (by simp only [zO]; omega_arith), Nat.mod_eq_of_lt (by simp only [zO]; omega_arith)]
    simp only [zO]; omega_arith
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

end

end

/-! ### `AesXts.Arm.Unit.Pre`, which this module and modules that import it used -/

section

/-! ### `AesXts.Arm.Unit.Contract`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on ARMv7: the contract the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Xts/Contract.lean` with 16 bytes of stack, which
imply `unitArm` (`Verified.lean`): `(schedule = r0, tweak_schedule = r1,
rounds = r2, i = r3, data = [sp], len = [sp + 4], scratch = [sp + 8])`.

`UPre` names the facts of the precondition; the regions of the scratch
buffer (`tR`, `zR`, `wkR`, the slots of the saved registers) are apart from
each other and from everything else.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm
open VG.Spec.Aes (bytesAt)

section
variable (s : State)

abbrev W : BitVec 32 := s.gpr .r0
abbrev K : BitVec 32 := s.gpr .r1
abbrev R : Nat := (s.gpr .r2).toNat
abbrev I : BitVec 32 := s.gpr .r3
abbrev D : BitVec 32 := stackArg s 0
abbrev Len : Nat := (stackArg s 1).toNat
abbrev S : BitVec 32 := stackArg s 2

/-- The scratch buffer and the data, as addresses. -/
abbrev Sa : Addr := State.addr (S s)
abbrev Da : Addr := State.addr (D s)

abbrev schR : Region := ⟨State.addr (W s), 240⟩
abbrev tschR : Region := ⟨State.addr (K s), 240⟩
abbrev iR : Region := ⟨State.addr (I s), 16⟩
abbrev dataR : Region := ⟨Da s, Len s⟩
abbrev scrR : Region := ⟨Sa s, 2432⟩
abbrev argsR : Region := ⟨stackArgAddr s 0, 12⟩
/-- The 16 bytes of stack below the stack pointer the calls use. -/
abbrev stkR : Region := ⟨State.addr s.sp - BitVec.ofNat 64 16, 16⟩

/-- The tweak, the second tweak, and the working space of the calls, in the
scratch buffer. -/
abbrev tR : Region := ⟨Sa s + BitVec.ofNat 64 Impl.AesXts.ArmUnit.tO, 16⟩
abbrev zR : Region := ⟨Sa s + BitVec.ofNat 64 Impl.AesXts.ArmUnit.zO, 16⟩
abbrev wkR : Region := ⟨Sa s, 2176⟩

/-- The number of whole blocks, the bytes after them, and the last whole block. -/
abbrev M : Nat := Len s / 16
abbrev B : Nat := Len s % 16
abbrev L : Addr := Da s + BitVec.ofNat 64 (16 * (M s - 1))

end

/-- What the functions need: the permissions, the buffers apart, from the
arguments on the stack and from the 16 bytes below the stack pointer,
`rounds` of 10, 12 or 14, and a data unit of 16 bytes to 2²⁰ blocks. -/
def unitPre (s : State) : Prop :=
  (16 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32) ∧
    s.rd = [schR s, tschR s, iR s, argsR s] ∧ s.wr = [dataR s, scrR s] ∧
    (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (scrR s) ∧ (tschR s).Disjoint (dataR s) ∧
    (tschR s).Disjoint (scrR s) ∧ (iR s).Disjoint (dataR s) ∧ (iR s).Disjoint (scrR s) ∧
    (dataR s).Disjoint (scrR s) ∧ (dataR s).Disjoint (argsR s) ∧ (scrR s).Disjoint (argsR s) ∧
    (stkR s).Disjoint (schR s) ∧ (stkR s).Disjoint (tschR s) ∧ (stkR s).Disjoint (iR s) ∧
    (stkR s).Disjoint (dataR s) ∧ (stkR s).Disjoint (scrR s) ∧ (stkR s).Disjoint (argsR s) ∧
    (W s).toNat + 240 ≤ 2 ^ 32 ∧ (K s).toNat + 240 ≤ 2 ^ 32 ∧ (I s).toNat + 16 ≤ 2 ^ 32 ∧
    (D s).toNat + Len s ≤ 2 ^ 32 ∧ (S s).toNat + 2432 ≤ 2 ^ 32 ∧
    (R s = 10 ∨ R s = 12 ∨ R s = 14) ∧ 16 ≤ Len s ∧ Len s ≤ 16 * Spec.Xts.maxBlocks

/-- XTS-AES of the data unit in a direction. -/
def xtsOf : Bool → List Byte → List Byte → List Byte → Option (List Byte)
  | true => Spec.Xts.aesXtsEncrypt
  | false => Spec.Xts.aesXtsDecrypt

def unitPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2

/-- `vg_aes_xts_encrypt_unit` (`enc`) or `vg_aes_xts_decrypt_unit`. -/
def unitArm (enc : Bool) : Contract isa where
  pre := unitPre
  post s s' := ∀ key, Spec.Xts.KeySchedules s.mem (State.addr (s.gpr .r0)) (State.addr (s.gpr .r1))
      (s.gpr .r2).toNat key →
    xtsOf enc key (bytesAt s.mem (State.addr (s.gpr .r3)) 16)
        (bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat) =
      some (bytesAt s'.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub := unitPub

/-- The precondition, by name. -/
structure UPre (s : State) : Prop where
  sp16 : 16 ≤ s.sp.toNat
  sp_fit : s.sp.toNat + 12 ≤ 2 ^ 32
  rd : s.rd = [schR s, tschR s, iR s, argsR s]
  wr : s.wr = [dataR s, scrR s]
  sch_data : (schR s).Disjoint (dataR s)
  sch_scr : (schR s).Disjoint (scrR s)
  tsch_data : (tschR s).Disjoint (dataR s)
  tsch_scr : (tschR s).Disjoint (scrR s)
  i_data : (iR s).Disjoint (dataR s)
  i_scr : (iR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  data_args : (dataR s).Disjoint (argsR s)
  scr_args : (scrR s).Disjoint (argsR s)
  stk_sch : (stkR s).Disjoint (schR s)
  stk_tsch : (stkR s).Disjoint (tschR s)
  stk_i : (stkR s).Disjoint (iR s)
  stk_data : (stkR s).Disjoint (dataR s)
  stk_scr : (stkR s).Disjoint (scrR s)
  stk_args : (stkR s).Disjoint (argsR s)
  sch_fit : (W s).toNat + 240 ≤ 2 ^ 32
  tsch_fit : (K s).toNat + 240 ≤ 2 ^ 32
  i_fit : (I s).toNat + 16 ≤ 2 ^ 32
  data_fit : (D s).toNat + Len s ≤ 2 ^ 32
  scr_fit : (S s).toNat + 2432 ≤ 2 ^ 32
  rounds : R s = 10 ∨ R s = 12 ∨ R s = 14
  len_lo : 16 ≤ Len s
  len_hi : Len s ≤ 16 * Spec.Xts.maxBlocks

theorem UPre.of {s : State} (h : unitPre s) : UPre s :=
  let ⟨⟨a, b⟩, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a', b'⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, a', b'⟩

/-! ## Regions -/

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x h => h₂ x (h₁ x h)

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_using [])

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.m_pos : 1 ≤ M s := by have := hp.len_lo; simp only [M]; omega_using [this]

omit hp in
theorem len_eq (s : State) : Len s = 16 * M s + B s := by simp only [M, B]; omega_using []

/-- An offset of the scratch buffer, as an address. -/
theorem UPre.scrA {d : Nat} (hd : d < 2432) : State.addr (S s + BitVec.ofNat 32 d) = Sa s + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega_using [hd, this])

/-- An offset of the data, as an address. -/
theorem UPre.dataA {d : Nat} (hd : d < Len s) : State.addr (D s + BitVec.ofNat 32 d) = Da s + BitVec.ofNat 64 d :=
  addr_add (by have := hp.data_fit; omega_using [hd, this])

theorem UPre.scr_wrap : (Sa s).toNat + 2432 ≤ 2 ^ 32 := by rw [addr_toNat]; exact hp.scr_fit

theorem UPre.data_wrap : (Da s).toNat + Len s ≤ 2 ^ 32 := by rw [addr_toNat]; exact hp.data_fit

omit hp in
theorem scr_sub {d n : Nat} (h : d + n ≤ 2432) : Region.Sub ⟨Sa s + BitVec.ofNat 64 d, n⟩ (scrR s) :=
  Offset.sub_base _ h

omit hp in
theorem data_sub {d n : Nat} (h : d + n ≤ Len s) : Region.Sub ⟨Da s + BitVec.ofNat 64 d, n⟩ (dataR s) :=
  Offset.sub_base _ h

omit hp in
theorem wk_sub : Region.Sub (wkR s) (scrR s) := Region.sub_prefix (by decide)

theorem UPre.t_wk : (tR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.ArmUnit.tO]; omega_using [])

theorem UPre.z_wk : (zR s).Disjoint (wkR s) :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; simp only [Impl.AesXts.ArmUnit.zO]; omega_using [])

theorem UPre.t_z : (tR s).Disjoint (zR s) :=
  Offset.disjoint _ (by simp only [Impl.AesXts.ArmUnit.tO, Impl.AesXts.ArmUnit.zO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.ArmUnit.tO]; omega_using [])
    (by have := hp.scr_wrap; simp only [Impl.AesXts.ArmUnit.zO]; omega_using [])

/-- Everything the code writes but the slots lies within the data, the
first 2208 bytes of the scratch buffer or the stack below the stack pointer. -/
theorem UPre.slots_disj {r : Region}
    (hr : Region.Sub r (dataR s) ∨ Region.Sub r ⟨Sa s, 2208⟩ ∨ Region.Sub r (stkR s)) :
    (⟨Sa s + BitVec.ofNat 64 2208, 28⟩ : Region).Disjoint r := by
  have slot : Region.Sub ⟨Sa s + BitVec.ofNat 64 2208, 28⟩ (scrR s) := scr_sub (by decide)
  rcases hr with h | h | h
  · exact (hp.data_scr.symm.sub_left slot).sub_right h
  · exact (Offset.disjoint_base _ (by decide) (by have := hp.scr_wrap; omega_using [])).sub_right h
  · exact (hp.stk_scr.symm.sub_left slot).sub_right h

omit hp in
theorem t_sub : Region.Sub (tR s) ⟨Sa s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem z_sub : Region.Sub (zR s) ⟨Sa s, 2208⟩ := Offset.sub_base _ (by decide)
omit hp in
theorem s_sub : Region.Sub ⟨Sa s, 2208⟩ (scrR s) := Region.sub_prefix (by decide)

theorem UPre.l_sub : Region.Sub ⟨L s, 16⟩ (dataR s) := data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.l_wrap : (L s).toNat + 16 ≤ 2 ^ 32 := by
  have := hp.data_wrap; have := len_eq s; have := hp.m_pos
  rw [L, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 * (M s - 1)) (by omega),
    Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

end

/-! ## The parts of the data unit -/

section
variable {s : State} (hp : UPre s)
include hp

theorem UPre.wrapD : (Da s).toNat + 16 * M s + B s ≤ 2 ^ 32 := by
  have := hp.data_wrap; have := len_eq s; omega_arith

omit hp in
theorem blocks_sub {N : Nat} (h : N ≤ M s) : Region.Sub ⟨Da s, 16 * N⟩ (dataR s) :=
  Region.sub_prefix (by have := len_eq s; omega_using [h, this])

theorem UPre.lb_sub : Region.Sub ⟨L s, 16 + B s⟩ (dataR s) :=
  data_sub (by have := len_eq s; have := hp.m_pos; omega_arith)

theorem UPre.tl_eq : L s + 16 = Da s + BitVec.ofNat 64 (16 * M s) := by
  rw [L, Proof.AesXts.Unit.add16, show 16 * (M s - 1) + 16 = 16 * M s by have := hp.m_pos; omega_using [this]]

theorem UPre.tl_sub : Region.Sub ⟨L s + 16, B s⟩ (dataR s) := by
  rw [hp.tl_eq]; exact data_sub (by have := len_eq s; omega_using [this])

theorem UPre.hd_lb : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16 + B s⟩ :=
  Offset.base_disjoint _ (Nat.le_refl _) (by have := hp.wrapD; have := hp.m_pos; omega_arith)

theorem UPre.hd_l : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  hp.hd_lb.sub_right (Region.sub_prefix (by omega_using []))

theorem UPre.hd_tl : (⟨Da s, 16 * (M s - 1)⟩ : Region).Disjoint ⟨L s + 16, B s⟩ := by
  rw [hp.tl_eq]
  exact Offset.base_disjoint _ (by omega_using []) (by have := hp.wrapD; omega_using [this])

omit hp in
theorem tl_l : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨L s, 16⟩ :=
  Offset.disjoint_base (L s) (d := 16) (n := B s) (k := 16) (Nat.le_refl _) (by simp only [B]; omega_using [])

theorem UPre.tl_blocks : (⟨L s + 16, B s⟩ : Region).Disjoint ⟨Da s, 16 * M s⟩ := by
  rw [hp.tl_eq]
  exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.wrapD; omega_using [this])

theorem UPre.l_hd : (⟨L s, 16⟩ : Region).Disjoint ⟨Da s, 16 * (M s - 1)⟩ := hp.hd_l.symm

end

end VG.Proof.AesXts.Arm.Unit

end

end

/-! ### `AesXts.Arm.Unit.Call`, which this module and modules that import it used -/

section

/-!
# XTS-AES of data units on ARMv7: a call of a whole-block function

`xts_call`: a call of `vg_aes_xts_encrypt` or `vg_aes_xts_decrypt` (`enc`
true or false), in the frame of its stack arguments (`xcall`), on `N` blocks
at `D`, from the tweak at `T`, with working space `S`, from its contract
(`frameCall_ok`): the blocks are then XTS of them, the tweak the one after
them, and only the tweak, the blocks, `S` and the 16 bytes below the stack
pointer change. `xts_rel`: such calls, with the same arguments and stack
pointer in both runs, are constant time.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.AesCbc.Arm (modeArm)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesXts.Unit (blocks_bytesAt)
open VG.Spec.Aes (bytesAt)

/-- The whole-block functions. -/
def xcode : Bool → Prog isa
  | true => Impl.AesXts.Arm.encrypt
  | false => Impl.AesXts.Arm.decrypt

abbrev xname : Bool → String
  | true => "vg_aes_xts_encrypt"
  | false => "vg_aes_xts_decrypt"

theorem xts_ok : ∀ enc s, (modeArm (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa (xcode enc) s t s' ∧ abiPreserved s s' ∧ (modeArm (AesXts.xtsMode enc)).post s s'
  | true, _, hs => Proof.AesXts.Arm.encrypt_wp hs
  | false, _, hs => Proof.AesXts.Arm.decrypt_wp hs

theorem xts_ct : ∀ enc, ConstantTime isa (modeArm (AesXts.xtsMode enc)).pre (modeArm (AesXts.xtsMode enc)).pub
    (xcode enc)
  | true => Proof.AesXts.Arm.encrypt_ct
  | false => Proof.AesXts.Arm.decrypt_ct

theorem xts_stack : ∀ enc, armStack (xcode enc) ≤ 8
  | true => by decide +kernel
  | false => by decide +kernel

/-- The 16 bytes below a stack pointer. -/
abbrev stk16 (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 16, 16⟩

/-- What a call of a whole-block function on `N` blocks needs. -/
structure XPre (s : State) (W T D S : BitVec 32) (N R : Nat) : Prop where
  r0 : s.gpr .r0 = W
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = T
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 N
  lr : s.gpr .lr = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  n : N < 2 ^ 28
  sp16 : 16 ≤ s.sp.toNat
  wt : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr T, 16⟩
  wd : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr D, 16 * N⟩
  ws : (⟨State.addr W, 240⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  td : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * N⟩
  ts : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  ds : (⟨State.addr D, 16 * N⟩ : Region).Disjoint ⟨State.addr S, 2176⟩
  stkW : (stk16 s.sp).Disjoint ⟨State.addr W, 240⟩
  stkT : (stk16 s.sp).Disjoint ⟨State.addr T, 16⟩
  stkD : (stk16 s.sp).Disjoint ⟨State.addr D, 16 * N⟩
  stkS : (stk16 s.sp).Disjoint ⟨State.addr S, 2176⟩
  fitW : W.toNat + 240 ≤ 2 ^ 32
  fitT : T.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * N ≤ 2 ^ 32
  fitS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨State.addr W, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr T, 16⟩, ⟨State.addr D, 16 * N⟩, ⟨State.addr S, 2176⟩] s.wr

/-- What a call of a whole-block function on `N` blocks leaves. -/
structure XPost (enc : Bool) (s : State) (W T D S : BitVec 32) (N R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr T, 16⟩, ⟨State.addr D, 16 * N⟩, ⟨State.addr S, 2176⟩, stk16 s.sp] s.mem s'.mem
  out : Spec.Cbc.blocksAt s'.mem (State.addr D) N =
    Spec.Xts.crypt (ciphOf enc R (bytesAt s.mem (State.addr W) (16 * (R + 1)))) (bytesAt s.mem (State.addr T) 16)
      (Spec.Cbc.blocksAt s.mem (State.addr D) N)
  tw : bytesAt s'.mem (State.addr T) 16 = Spec.Xts.next (bytesAt s.mem (State.addr T) 16) N

theorem toNat_n {N : Nat} (h : N < 2 ^ 28) : (BitVec.ofNat 32 N).toNat = N := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [h])

theorem toNat_r {R : Nat} (h : R = 10 ∨ R = 12 ∨ R = 14) : (BitVec.ofNat 32 R).toNat = R := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [h])

/-- The regions the callee is given. -/
abbrev xRd (sp W : BitVec 32) : List Region := [⟨State.addr W, 240⟩, ⟨State.addr sp - BitVec.ofNat 64 8, 8⟩]
abbrev xWr (T D S : BitVec 32) (N : Nat) : List Region :=
  [⟨State.addr T, 16⟩, ⟨State.addr D, 16 * N⟩, ⟨State.addr S, 2176⟩]

/-- The state the callee runs from. -/
abbrev xView (s : State) (W T D S : BitVec 32) (N : Nat) : State :=
  (pushed [.r12, .lr] s).callEntry.withRegions (xRd s.sp W) (xWr T D S N)

namespace XPre
variable {s : State} {W T D S : BitVec 32} {N R : Nat} (h : XPre s W T D S N R)
include h

theorem h8 : 4 * [Reg.r12, .lr].length ≤ s.sp.toNat := by have := h.sp16; simp; omega_using [this]

theorem below_sub : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩ (stk16 s.sp) :=
  Argon2.Arm.stkR_sub (by decide) (by have := h.sp16; omega_using [this])

omit h in
theorem view_sp : (xView s W T D S N).sp = s.sp - BitVec.ofNat 32 8 := rfl

theorem view_below : (⟨State.addr (xView s W T D S N).sp - BitVec.ofNat 64 8, 8⟩ : Region) =
    ⟨State.addr s.sp - BitVec.ofNat 64 16, 8⟩ := by
  rw [view_sp, addr_sub' (by have := h.sp16; omega_using [this]), BitVec.sub_sub, ← BitVec.ofNat_add]

omit h in
theorem below2_sub : Region.Sub ⟨State.addr s.sp - BitVec.ofNat 64 16, 8⟩ (stk16 s.sp) :=
  Region.sub_prefix (by decide)

omit h in
theorem view_gpr (r : Reg) (hr : r ∉ linkRegs) : (xView s W T D S N).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem arg0 : stackArg (xView s W T D S N) 0 = BitVec.ofNat 32 N := by
  rw [Argon2.Arm.pushed_arg h.h8 (by decide)]; exact h.r12

theorem arg1 : stackArg (xView s W T D S N) 1 = S := by
  rw [Argon2.Arm.pushed_arg h.h8 (by decide)]; exact h.lr

theorem argAddr : stackArgAddr (xView s W T D S N) 0 = State.addr s.sp - BitVec.ofNat 64 8 :=
  Argon2.Arm.pushed_argAddr h.h8

theorem pre (enc : Bool) : (modeArm (AesXts.xtsMode enc)).pre (xView s W T D S N) := by
  have hR := toNat_r h.rounds
  have hN := toNat_n h.n
  have hsp : (xView s W T D S N).sp.toNat = s.sp.toNat - 8 := by
    rw [view_sp]; exact sub_toNat' (by have := h.sp16; omega_using [this])
  simp only [modeArm, h.arg0, h.arg1, h.argAddr, view_gpr .r0 (by decide), view_gpr .r1 (by decide),
    view_gpr .r2 (by decide), view_gpr .r3 (by decide), h.r0, h.r1, h.r2, h.r3, hR, hN, State.withRegions_rd,
    State.withRegions_wr, h.view_below, hsp]
  refine ⟨trivial, trivial, h.wt, h.wd, h.ws, h.td, h.ts, h.ds, (h.stkT.sub_left h.below_sub).symm,
    (h.stkD.sub_left h.below_sub).symm, (h.stkS.sub_left h.below_sub).symm, h.stkW.sub_left below2_sub,
    h.stkT.sub_left below2_sub, h.stkD.sub_left below2_sub, h.stkS.sub_left below2_sub,
    h.fitW, h.fitT, h.fitD, h.fitS, by have := h.sp16; omega_using [this], by have := s.sp.isLt; omega_using [], h.rounds⟩

theorem cov : Covers (xRd s.sp W ++ xWr T D S N) ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r', hr', hc'⟩ := h.reads x n' ⟨_, List.mem_singleton_self _, hc⟩
    refine ⟨r', ?_, hc'⟩
    rcases List.mem_append.mp hr' with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')
  · refine ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..), ?_⟩
    rwa [show 4 * [Reg.r12, .lr].length = 8 from rfl, addr_sub' (by have := h.sp16; omega_using [this])]
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.writes x n' ⟨_, by simp, hc⟩
    exact ⟨r', List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (xWr T D S N) (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem fp : Frame [Argon2.Arm.stkR s.sp (4 * [Reg.r12, .lr].length)] s.mem (pushed [.r12, .lr] s).mem :=
  Argon2.Arm.pushed_stk h.h8

theorem push_keeps {X : Region} (hX : (stk16 s.sp).Disjoint X) (hn : X.len ≤ 2 ^ 64) :
    bytesAt (pushed [.r12, .lr] s).mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame h.fp (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hX.sub_left (Argon2.Arm.stkR_sub (a := 4 * [Reg.r12, .lr].length) (b := 16) (by decide) (by have := h.sp16; omega_using [this]))).symm) hn

end XPre

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Cbc.blocksAt m' p n = Spec.Cbc.blocksAt m p n := by
  rw [← blocks_bytesAt, ← blocks_bytesAt, Proof.Cmac.bytesAt_frame hf hd hn]

theorem xts_call (enc : Bool) {s : State} {W T D S : BitVec 32} {N R : Nat} (h : XPre s W T D S N R) :
    WP isa (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length))) s
      (XPost enc s W T D S N R) := by
  have hR := toNat_r h.rounds
  have hN := toNat_n h.n
  refine Argon2.Arm.frameCall_ok (rs := [.r12, .lr]) (t := .r12) (by decide) (by decide) (by decide)
    (n := xname enc) (c := xcode enc) (xts_ok enc) (K := 16) (by have := xts_stack enc; simp; omega_using [this]) h.sp16 (h.pre enc) h.cov h.covW ?_
  intro s₂ a hpost
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h' | h' | h' <;> omega_using [h']
  have eW : bytesAt (pushed [.r12, .lr] s).mem (State.addr W) (16 * (R + 1)) =
      bytesAt s.mem (State.addr W) (16 * (R + 1)) :=
    h.push_keeps (X := ⟨State.addr W, 16 * (R + 1)⟩) (h.stkW.sub_right (Region.sub_prefix hRb)) (by dsimp only; omega_using [hR])
  have eT : bytesAt (pushed [.r12, .lr] s).mem (State.addr T) 16 = bytesAt s.mem (State.addr T) 16 :=
    h.push_keeps (X := ⟨State.addr T, 16⟩) h.stkT (by simp)
  have eD : Spec.Cbc.blocksAt (pushed [.r12, .lr] s).mem (State.addr D) N = Spec.Cbc.blocksAt s.mem (State.addr D) N :=
    blocksAt_frame h.fp (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.stkD.sub_left (Argon2.Arm.stkR_sub (a := 4 * [Reg.r12, .lr].length) (b := 16) (by decide) (by have := h.sp16; omega_using [this]))).symm)
      (by have := h.fitD; omega_using [hN])
  simp only [modeArm, AesXts.xtsMode, State.withRegions_mem, State.callEntry_mem, h.arg0,
    XPre.view_gpr .r0 (by decide), XPre.view_gpr .r1 (by decide), XPre.view_gpr .r2 (by decide),
    XPre.view_gpr .r3 (by decide), h.r0, h.r1, h.r2, h.r3, hR, hN, Proof.AesXts.Unit.length_blocksAt,
    eW, eT, eD] at hpost
  refine ⟨a.rd, a.wr, a.sp, a.cs, ?_, ?_, ?_⟩
  · refine a.frame.sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  · simpa using hpost.1
  · simpa using hpost.2

/-- Calls of a whole-block function, with the same arguments and stack
pointer in both runs, are constant time. -/
theorem xts_rel (enc : Bool) {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : BitVec 32, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length)))
      fun _ _ => True := by
  refine (RelCT.exists_ (P := fun (q : (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) × (Nat × Nat) × BitVec 32)
      (a b : State) => XPre a q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2 ∧
        XPre b q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2 ∧ a.sp = q.2.2 ∧ b.sp = q.2.2) fun q => ?_).mono
    (fun a b hp => by
      obtain ⟨W, T, D, S, N, R, h₁, h₂, e⟩ := h a b hp
      exact ⟨((W, T, D, S), (N, R), a.sp), h₁, h₂, rfl, e.symm⟩) fun _ _ h => h
  obtain ⟨⟨W, T, D, S⟩, ⟨N, R⟩, sp⟩ := q
  refine Argon2.Arm.frameCall_rel (rs := [.r12, .lr]) (t := .r12) (by decide) (xts_ok enc) (xts_ct enc)
    (xRd sp W) (xWr T D S N) fun s₁ s₂ ⟨h₁, h₂, e₁, e₂⟩ => ?_
  dsimp only at h₁ h₂ e₁ e₂
  have p₁ := h₁.pre enc
  have p₂ := h₂.pre enc
  unfold xView at p₁ p₂
  rw [e₁] at p₁
  rw [e₂] at p₂
  have c₁ := h₁.cov
  have c₂ := h₂.cov
  rw [e₁] at c₁
  rw [e₂] at c₂
  refine ⟨by rw [e₁, e₂], p₁, p₂, ?_, c₁, h₁.covW, c₂, h₂.covW⟩
  have a₁ := (Argon2.Arm.pushed_arg (rd := xRd sp W) (wr := xWr T D S N) h₁.h8 (i := 0) (by decide)).trans h₁.r12
  have b₁ := (Argon2.Arm.pushed_arg (rd := xRd sp W) (wr := xWr T D S N) h₁.h8 (i := 1) (by decide)).trans h₁.lr
  have a₂ := (Argon2.Arm.pushed_arg (rd := xRd sp W) (wr := xWr T D S N) h₂.h8 (i := 0) (by decide)).trans h₂.r12
  have b₂ := (Argon2.Arm.pushed_arg (rd := xRd sp W) (wr := xWr T D S N) h₂.h8 (i := 1) (by decide)).trans h₂.lr
  simp only [modeArm, a₁, b₁, a₂, b₂, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    pushed_sp, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), pushed_gpr, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₂.r0, h₂.r1,
    h₂.r2, h₂.r3, e₁, e₂]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.AesXts.Arm.Unit

end

end

/-!
# XTS-AES of data units on ARMv7: the arguments of each call

The five calls of a whole-block function the functions make, each with
`XPre` from the precondition (`UPre`), for a state with the permissions and
stack pointer of the entry state and the call's arguments in its registers:

* `xpre_tweak`: the tweak value `i`, copied to the tweak (`tR`), enciphered
  with `tweak_schedule` from the zero second tweak (`zR`);
* `xpre_blocks`: the first `N` whole blocks of the data, from the tweak;
* `xpre_last`: the last whole block (`L`), from the tweak (`o = tO`) or from
  the second tweak (`o = zO`).
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm
open VG.Impl.AesXts.ArmUnit (tO zO)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.scrN {d : Nat} (hd : d < 2432) : (S s₀ + BitVec.ofNat 32 d).toNat = (S s₀).toNat + d := by
  have := hp.scr_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

theorem UPre.dataN {d : Nat} (hd : d < Len s₀) : (D s₀ + BitVec.ofNat 32 d).toNat = (D s₀).toNat + d := by
  have := hp.data_fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd, this]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

/-- The last whole block, as a register holds it. -/
abbrev Lv (s₀ : State) : BitVec 32 := D s₀ + BitVec.ofNat 32 (16 * (M s₀ - 1))

theorem UPre.lA : State.addr (Lv s₀) = L s₀ :=
  hp.dataA (by have := len_eq s₀; have := hp.m_pos; omega_arith)

omit hp in
theorem UPre.stk_eq {s : State} (hsp : s.sp = s₀.sp) : stk16 s.sp = stkR s₀ := by rw [hsp]

theorem UPre.cS (d n : Nat) (h : d + n ≤ 2432) : (scrR s₀).Contains (Sa s₀ + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by have := hp.scr_wrap; omega_using [h])

end

section
variable {s₀ s : State} (hp : UPre s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
include hp hrd hwr hsp

theorem xpre_tweak (r0 : s.gpr .r0 = K s₀) (r1 : s.gpr .r1 = BitVec.ofNat 32 (R s₀))
    (r2 : s.gpr .r2 = S s₀ + BitVec.ofNat 32 zO) (r3 : s.gpr .r3 = S s₀ + BitVec.ofNat 32 tO)
    (r12 : s.gpr .r12 = BitVec.ofNat 32 1) (lr : s.gpr .lr = S s₀) :
    XPre s (K s₀) (S s₀ + BitVec.ofNat 32 zO) (S s₀ + BitVec.ofNat 32 tO) (S s₀) 1 (R s₀) := by
  have aT := hp.scrA (d := tO) (by decide)
  have aZ := hp.scrA (d := zO) (by decide)
  have stk := UPre.stk_eq (s₀ := s₀) hsp
  exact {
    r0 := r0
    r1 := r1
    r2 := r2
    r3 := r3
    r12 := r12
    lr := lr
    rounds := hp.rounds
    n := by decide
    sp16 := by rw [hsp]; exact hp.sp16
    wt := by rw [aZ]; exact hp.tsch_scr.sub_right (sub_trans z_sub s_sub)
    wd := by rw [aT]; exact hp.tsch_scr.sub_right (sub_trans t_sub s_sub)
    ws := hp.tsch_scr.sub_right wk_sub
    td := by rw [aZ, aT]; exact hp.t_z.symm
    ts := by rw [aZ]; exact hp.z_wk
    ds := by rw [aT]; exact hp.t_wk
    stkW := by rw [stk]; exact hp.stk_tsch
    stkT := by rw [stk, aZ]; exact hp.stk_scr.sub_right (sub_trans z_sub s_sub)
    stkD := by rw [stk, aT]; exact hp.stk_scr.sub_right (sub_trans t_sub s_sub)
    stkS := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.tsch_fit
    fitT := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [zO]; omega_using [this]
    fitD := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [tO]; omega_using [this]
    fitS := by have := hp.scr_fit; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨tschR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aZ, aT]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, zO, rfl, by simp [zO]⟩
      · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

theorem xpre_blocks {N : Nat} (hN : 16 * N ≤ Len s₀) (r0 : s.gpr .r0 = W s₀)
    (r1 : s.gpr .r1 = BitVec.ofNat 32 (R s₀)) (r2 : s.gpr .r2 = S s₀ + BitVec.ofNat 32 tO)
    (r3 : s.gpr .r3 = D s₀) (r12 : s.gpr .r12 = BitVec.ofNat 32 N) (lr : s.gpr .lr = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 32 tO) (D s₀) (S s₀) N (R s₀) := by
  have aT := hp.scrA (d := tO) (by decide)
  have stk := UPre.stk_eq (s₀ := s₀) hsp
  have dS : Region.Sub ⟨State.addr (D s₀), 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  exact {
    r0 := r0
    r1 := r1
    r2 := r2
    r3 := r3
    r12 := r12
    lr := lr
    rounds := hp.rounds
    n := by have := hp.len_hi; simp only [Spec.Xts.maxBlocks] at this; omega_using [hN, this]
    sp16 := by rw [hsp]; exact hp.sp16
    wt := by rw [aT]; exact hp.sch_scr.sub_right (sub_trans t_sub s_sub)
    wd := hp.sch_data.sub_right dS
    ws := hp.sch_scr.sub_right wk_sub
    td := by rw [aT]; exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right dS
    ts := by rw [aT]; exact hp.t_wk
    ds := (hp.data_scr.sub_left dS).sub_right wk_sub
    stkW := by rw [stk]; exact hp.stk_sch
    stkT := by rw [stk, aT]; exact hp.stk_scr.sub_right (sub_trans t_sub s_sub)
    stkD := by rw [stk]; exact hp.stk_data.sub_right dS
    stkS := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.sch_fit
    fitT := by rw [hp.scrN (by decide)]; have := hp.scr_fit; simp only [tO]; omega_using [this]
    fitD := by have := hp.data_fit; omega_using [hN, this]
    fitS := by have := hp.scr_fit; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aT]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, tO, rfl, by simp [tO]⟩
      · exact ⟨dataR s₀, by simp, 0, by simp, by simpa using hN⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

theorem xpre_last {o : Nat} (ho : o = tO ∨ o = zO) (r0 : s.gpr .r0 = W s₀)
    (r1 : s.gpr .r1 = BitVec.ofNat 32 (R s₀)) (r2 : s.gpr .r2 = S s₀ + BitVec.ofNat 32 o)
    (r3 : s.gpr .r3 = Lv s₀) (r12 : s.gpr .r12 = BitVec.ofNat 32 1) (lr : s.gpr .lr = S s₀) :
    XPre s (W s₀) (S s₀ + BitVec.ofNat 32 o) (Lv s₀) (S s₀) 1 (R s₀) := by
  have ol : o + 16 ≤ 2208 := by rcases ho with rfl | rfl <;> decide
  have aO := hp.scrA (d := o) (by omega_using [ol])
  have aL := hp.lA
  have stk := UPre.stk_eq (s₀ := s₀) hsp
  have oS : Region.Sub ⟨Sa s₀ + BitVec.ofNat 64 o, 16⟩ ⟨Sa s₀, 2208⟩ := Offset.sub_base _ ol
  have oW : (⟨Sa s₀ + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint (wkR s₀) := by
    rcases ho with rfl | rfl
    · exact hp.t_wk
    · exact hp.z_wk
  have lS : Region.Sub ⟨L s₀, 16 * 1⟩ (dataR s₀) := hp.l_sub
  exact {
    r0 := r0
    r1 := r1
    r2 := r2
    r3 := r3
    r12 := r12
    lr := lr
    rounds := hp.rounds
    n := by decide
    sp16 := by rw [hsp]; exact hp.sp16
    wt := by rw [aO]; exact hp.sch_scr.sub_right (sub_trans oS s_sub)
    wd := by rw [aL]; exact hp.sch_data.sub_right lS
    ws := hp.sch_scr.sub_right wk_sub
    td := by rw [aO, aL]; exact (hp.data_scr.symm.sub_left (sub_trans oS s_sub)).sub_right lS
    ts := by rw [aO]; exact oW
    ds := by rw [aL]; exact (hp.data_scr.sub_left lS).sub_right wk_sub
    stkW := by rw [stk]; exact hp.stk_sch
    stkT := by rw [stk, aO]; exact hp.stk_scr.sub_right (sub_trans oS s_sub)
    stkD := by rw [stk, aL]; exact hp.stk_data.sub_right lS
    stkS := by rw [stk]; exact hp.stk_scr.sub_right wk_sub
    fitW := hp.sch_fit
    fitT := by rw [hp.scrN (by omega_using [ol])]; have := hp.scr_fit; omega_using [ol, this]
    fitD := by
      have := hp.l_wrap
      rw [← aL, addr_toNat] at this
      omega_using [this]
    fitS := by have := hp.scr_fit; omega_using [this]
    reads := by
      rw [hrd, hwr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
    writes := by
      rw [hwr, hp.wr, aO, aL]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, o, rfl, by simp; omega_using [ol]⟩
      · exact ⟨dataR s₀, by simp, 16 * (M s₀ - 1), rfl, by
          have := len_eq s₀; have := hp.m_pos; simp only [M, B] at *; omega_using [this]⟩
      · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩ }

end

end VG.Proof.AesXts.Arm.Unit

end

end

/-! ### `AesXts.Arm.Unit.Run`, which only this module used -/

section

/-!
# XTS-AES of data units on ARMv7: the tweak, and what every piece keeps

`Inv`: between the calls the code keeps its arguments in `r4`, `r5`, `r7`,
`r8` and `r9`, its caller's callee-saved registers (but `r10` and `r11`,
which it keeps in place) and its return address in their slots, and changes
memory only in the data, the scratch buffer and the 16 bytes below the stack
pointer (`Inv.step`, for any code whose frame is in those). `tweak_wp`: the
prologue and the call enciphering the tweak value leave
`T = AES-enc(Key2, i)` in the tweak (`TwPost`). `fin_wp`: the epilogue
restores the registers.
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesXts.ArmUnit
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.MdStream.Arm (op2_reg wp_mov wp_ldrSp)
open VG.Spec.Aes (bytesAt)

section
variable (s₀ : State)

/-- The tweak and the second tweak, as addresses and as register values. -/
abbrev Tp : Addr := Sa s₀ + BitVec.ofNat 64 tO
abbrev Zp : Addr := Sa s₀ + BitVec.ofNat 64 zO
abbrev Tv : BitVec 32 := S s₀ + BitVec.ofNat 32 tO
abbrev Zv : BitVec 32 := S s₀ + BitVec.ofNat 32 zO

/-- `T = AES-enc(Key2, i)`. -/
abbrev t0 : List Byte :=
  Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem (State.addr (K s₀)) (16 * (R s₀ + 1)))
    (bytesAt s₀.mem (State.addr (I s₀)) 16)

/-- `AES-enc(Key1, ·)` (`enc`) or `AES-dec(Key1, ·)`. -/
abbrev ciph (enc : Bool) : Spec.Cbc.Cipher :=
  ciphOf enc (R s₀) (bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)))

end

/-- What the code keeps between the calls. -/
structure Inv (s₀ s : State) : Prop where
  r4 : s.gpr .r4 = W s₀
  r5 : s.gpr .r5 = s₀.gpr .r2
  r7 : s.gpr .r7 = stackArg s₀ 1
  r8 : s.gpr .r8 = S s₀
  r9 : s.gpr .r9 = D s₀
  rest : ∀ r ∈ ([.r10, .r11] : List Reg), s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [dataR s₀, scrR s₀, stkR s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (Sa s₀) s₀.gpr saved

theorem saved_slots : Spill.Slots 2208 2236 saved := by decide

/-- The registers `Inv` pins. -/
abbrev pinned : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11]

theorem rest_pinned : ∀ r ∈ ([.r10, .r11] : List Reg), r ∈ pinned := by decide

theorem pinned_pres : ∀ r ∈ pinned, r ∈ preserved ∧ r ≠ .lr := by decide

theorem r1_ofNat (s₀ : State) : BitVec.ofNat 32 (R s₀) = s₀.gpr .r2 := by
  rw [R, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem in_rw {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs) (h : r.Contains a n) :
    InRegions rs a n := ⟨r, hr, h⟩

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- `Inv` across code that keeps the registers and writes only within
`rs`, each in the data, the first 2208 bytes of the scratch buffer or the
stack below the stack pointer. -/
theorem Inv.step {s s' : State} (h : Inv s₀ s) {rs : List Region}
    (hrs : ∀ r ∈ rs, Region.Sub r (dataR s₀) ∨ Region.Sub r ⟨Sa s₀, 2208⟩ ∨ Region.Sub r (stkR s₀))
    (hf : Frame rs s.mem s'.mem) (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv s₀ s' where
  r4 := by rw [hg _ (by simp), h.r4]
  r5 := by rw [hg _ (by simp), h.r5]
  r7 := by rw [hg _ (by simp), h.r7]
  r8 := by rw [hg _ (by simp), h.r8]
  r9 := by rw [hg _ (by simp), h.r9]
  rest r hr := by rw [hg r (rest_pinned r hr), h.rest r hr]
  sp := by rw [hsp, h.sp]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := h.frame.trans (hf.sub fun r hr => by
    rcases hrs r hr with h | h | h
    · exact ⟨dataR s₀, by simp, h⟩
    · exact ⟨scrR s₀, by simp, sub_trans h s_sub⟩
    · exact ⟨stkR s₀, by simp, h⟩)
  saved := h.saved.frame saved_slots hf fun r hr => hp.slots_disj (hrs r hr)

/-- `Inv` across a call of a whole-block function. -/
theorem Inv.call {enc : Bool} {s s' : State} (h : Inv s₀ s) {Wk T Dd : BitVec 32} {N Rr : Nat}
    (hT : Region.Sub ⟨State.addr T, 16⟩ ⟨Sa s₀, 2208⟩)
    (hD : Region.Sub ⟨State.addr Dd, 16 * N⟩ (dataR s₀) ∨ Region.Sub ⟨State.addr Dd, 16 * N⟩ ⟨Sa s₀, 2208⟩)
    (hc : XPost enc s Wk T Dd (S s₀) N Rr s') : Inv s₀ s' :=
  Inv.step hp h (rs := [⟨State.addr T, 16⟩, ⟨State.addr Dd, 16 * N⟩, ⟨State.addr (S s₀), 2176⟩, stk16 s.sp])
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact .inr (.inl hT)
      · exact hD.elim .inl fun h => .inr (.inl h)
      · exact .inr (.inl (Region.sub_prefix (by decide)))
      · exact .inr (.inr (by rw [UPre.stk_eq h.sp]; exact fun _ h => h)))
    hc.frame (fun r hr => hc.saved r (pinned_pres r hr).1 (pinned_pres r hr).2) hc.sp hc.rd hc.wr

/-! ## The prologue -/

/-- Before the call enciphering the tweak value. -/
structure ProPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (K s₀) (Zv s₀) (Tv s₀) (S s₀) 1 (R s₀)
  frame : Frame [scrR s₀] s₀.mem s.mem
  ti : bytesAt s.mem (Tp s₀) 16 = bytesAt s₀.mem (State.addr (I s₀)) 16
  z : bytesAt s.mem (Zp s₀) 16 = List.replicate 16 0

theorem UPre.arg_in {k : Nat} (hk : k < 3) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  have := hp.sp_fit
  obtain e : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
    simp only [stackArgAddr]
    rw [addr_add (by omega_using [hk, this]), addr_add (by omega_using [])]
    simp
  rw [e]
  exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])

/-- The slots, as seen from the memory after the saves. -/
theorem slots_in (d : Nat) (h₁ : d + 4 ≤ 2432) :
    InRegions s₀.wr (Sa s₀ + BitVec.ofNat 64 d) 4 := by
  rw [hp.wr]; exact in_rw (r := scrR s₀) (by simp) (hp.cS _ _ h₁)

theorem pro_wp : WP isa (.block pro) s₀ (ProPost s₀) := by
  have hsc := hp.scr_fit
  rw [pro, List.append_assoc, List.append_assoc, List.append_assoc, save, List.cons_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine Spill.saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_slots.bound hp'
    rw [h12, u₁.wr]
    exact ⟨by omega_using [hb], by omega_using [hsc, hb], slots_in hp _ (by omega_using [hb])⟩
  rw [h12, u₁.mem] at m₂
  obtain f₂ : Frame [scrR s₀] s₀.mem s₂.mem := by
    rw [m₂]
    exact (Spill.saveMem_frame_slots saved_slots s₀.mem (Sa s₀) s₁.gpr).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, scr_sub (by decide)⟩
  have harg (k : Nat) (hk : k < 3) : s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := by
    refine f₂.readW (r := ⟨stackArgAddr s₀ k, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have := hp.sp_fit
    refine (hp.scr_args.sub_right ?_).symm
    obtain e : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
      simp only [stackArgAddr]
      rw [addr_add (by omega_using [hk, this]), addr_add (by omega_using [])]
      simp
    rw [e]; exact Offset.sub_base _ (by omega_using [hk])
  -- `setup`
  simp only [setup, mov, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => ?_
  obtain sp₅ : s₅.sp = s₀.sp := by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  obtain rdwr₅ : s₅.rd ++ s₅.wr = s₀.rd ++ s₀.wr := by
    rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [sp₅]; rfl)
    (by rw [rdwr₅]; exact hp.arg_in (by decide)) fun s₆ u₆ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₆.sp, sp₅]; rfl)
    (by rw [u₆.rd, u₆.wr, rdwr₅]; exact hp.arg_in (by decide)) fun s₇ u₇ => ?_
  obtain m₇ : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain r8₇ : s₇.gpr .r8 = S s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr, g₂, h12]
  obtain k₇ : ∀ r, r ≠ .r8 → r ≠ .r4 → r ≠ .r5 → r ≠ .r9 → r ≠ .r7 → r ≠ .r12 → s₇.gpr r = s₀.gpr r :=
    fun r h8 h4 h5 h9 h7 h12' => by
      rw [u₇.other r h7, u₆.other r h9, u₅.other r h5, u₄.other r h4, u₃.other r h8, congrFun g₂ r,
        u₁.other r h12']
  obtain r4₇ : s₇.gpr .r4 = W s₀ := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, g₂, u₁.other]
  obtain r5₇ : s₇.gpr .r5 = s₀.gpr .r2 := by
    simp (disch := decide) only [u₇.other, u₆.other, u₅.gpr, u₄.other, u₃.other, g₂, u₁.other]
  obtain r9₇ : s₇.gpr .r9 = D s₀ := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, harg 0 (by decide)]
  obtain r7₇ : s₇.gpr .r7 = stackArg s₀ 1 := by
    rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, harg 1 (by decide)]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  obtain sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, sp₅]
  obtain rdwr₇ : s₇.rd ++ s₇.wr = [schR s₀, tschR s₀, iR s₀, argsR s₀, dataR s₀, scrR s₀] := by
    rw [rd₇, wr₇, hp.rd, hp.wr]; rfl
  obtain wr₇' : s₇.wr = [dataR s₀, scrR s₀] := by rw [wr₇]; exact hp.wr
  -- The copy of `i`.
  rw [WP.block_append_iff]
  obtain r3₇ : s₇.gpr .r3 = I s₀ := k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s₈, run₈, g₈, sp₈, mem₈, rd₈, wr₈⟩ := copyI_ok s₇ (P := Tp s₀) (Q := State.addr (I s₀))
    (by rw [r3₇]; simp) (by rw [r3₇]; have := hp.i_fit; omega_using [this]) (by rw [r8₇])
    (by rw [r8₇]; simp only [tO]; omega_using [hsc])
    (fun d n h => by
      rw [rdwr₇]
      exact in_rw (r := iR s₀) (by simp) (Offset.contains_base _ h (by omega_using [h])))
    (fun d n h => by rw [wr₇']; exact in_rw (r := scrR s₀) (by simp) (by
      rw [Offset.add_add]; exact hp.cS _ _ (by simp only [tO]; omega_using [h])))
  refine WP.of_runBlock ⟨s₈, run₈, ?_⟩
  rw [WP.block_append_iff]
  obtain r8₈ : s₈.gpr .r8 = S s₀ := by rw [g₈ _ (by decide) (by decide) (by decide) (by decide), r8₇]
  obtain wr₈' : s₈.wr = [dataR s₀, scrR s₀] := by rw [wr₈, wr₇']
  obtain ⟨s₉, run₉, g₉, sp₉, mem₉, rd₉, wr₉⟩ := zeroZ_ok s₈ (Z := Zp s₀) (by rw [r8₈])
    (by rw [r8₈]; simp only [zO]; omega_using [hsc])
    (fun d n h => by rw [wr₈']; exact in_rw (r := scrR s₀) (by simp) (by
      rw [Offset.add_add]; exact hp.cS _ _ (by simp only [zO]; omega_using [h])))
  refine WP.of_runBlock ⟨s₉, run₉, ?_⟩
  obtain ⟨s₁₀, run₁₀, x0, x1, x2, x3, x12, xlr, cs₁₀, sp₁₀', mem₁₀, rd₁₀, wr₁₀⟩ := tArgs_ok s₉
  refine WP.of_runBlock ⟨s₁₀, run₁₀, ?_⟩
  -- The registers.
  obtain k₉ : ∀ r, r ≠ .r12 → r ≠ .lr → r ≠ .r0 → r ≠ .r2 → s₉.gpr r = s₇.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g₉ r h₁, g₈ r h₁ h₂ h₃ h₄]
  obtain r8₉ : s₉.gpr .r8 = S s₀ := by rw [k₉ _ (by decide) (by decide) (by decide) (by decide), r8₇]
  have cs (r : Reg) (hr : r ∈ preserved) (hl : r ≠ .lr) : s₁₀.gpr r = s₇.gpr r := by
    have := preserved_ne r hr hl
    rw [cs₁₀ r hr hl, k₉ r this.2.2.2.2 hl this.1 this.2.2.1]
  obtain rd₁₀' : s₁₀.rd = s₀.rd := by rw [rd₁₀, rd₉, rd₈, rd₇]
  obtain wr₁₀' : s₁₀.wr = s₀.wr := by rw [wr₁₀, wr₉, wr₈, wr₇]
  obtain sp₁₀ : s₁₀.sp = s₀.sp := by rw [sp₁₀', sp₉, sp₈, sp₇]
  -- The memory.
  obtain f₈ : Frame [⟨Tp s₀, 16⟩] s₇.mem s₈.mem := by rw [mem₈]; exact copy4_frame _ _ _
  obtain f₉ : Frame [⟨Zp s₀, 16⟩] s₈.mem s₉.mem := by rw [mem₉]; exact zero4_frame _ _
  obtain f₇ : Frame [scrR s₀] s₀.mem s₇.mem := by rw [m₇]; exact f₂
  obtain frame : Frame [scrR s₀] s₀.mem s₁₀.mem := by
    rw [mem₁₀]
    refine f₇.trans ((f₈.sub fun r hr => ?_).trans (f₉.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [tO])⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, scr_sub (by simp [zO])⟩
  obtain sv₇ : Spill.Saved s₇.mem (Sa s₀) s₀.gpr saved := by
    intro p hp'
    rw [m₇, m₂, Spill.saveMem_saved (Sa s₀) s₁.gpr s₀.mem saved saved_slots p hp']
    obtain hne : p.1 ≠ .r12 := by revert hp'; revert p; decide
    exact u₁.other _ hne
  obtain sdisj : ∀ (r : Region), Region.Sub r ⟨Sa s₀, 2208⟩ → ∀ r' ∈ [r],
      Region.Disjoint ⟨Sa s₀ + BitVec.ofNat 64 2208, 2236 - 2208⟩ r' := fun r hr r' hr' => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hp.slots_disj (.inr (.inl hr))
  obtain sv₁₀ : Spill.Saved s₁₀.mem (Sa s₀) s₀.gpr saved := by
    rw [mem₁₀, mem₉]
    exact (sv₇.frame saved_slots f₈ (sdisj _ t_sub)).frame saved_slots (zero4_frame _ _) (sdisj _ z_sub)
  refine ⟨⟨by rw [cs _ (by simp [preserved]) (by decide), r4₇], by rw [cs _ (by simp [preserved]) (by decide), r5₇],
    by rw [cs _ (by simp [preserved]) (by decide), r7₇], by rw [cs _ (by simp [preserved]) (by decide), r8₇],
    by rw [cs _ (by simp [preserved]) (by decide), r9₇], fun r hr => by
      obtain hr' : r ∈ preserved ∧ r ≠ .lr := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
      rw [cs r hr'.1 hr'.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;>
        exact k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), sp₁₀, rd₁₀', wr₁₀',
    frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩, sv₁₀⟩, ?_, frame, ?_, ?_⟩
  · refine xpre_tweak hp rd₁₀' wr₁₀' sp₁₀ ?_ ?_ (by rw [x2, r8₉]) (by rw [x3, r8₉]) x12 (by rw [xlr, r8₉])
    · rw [x0, k₉ _ (by decide) (by decide) (by decide) (by decide),
        k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [x1, k₉ _ (by decide) (by decide) (by decide) (by decide), r5₇, r1_ofNat]
  · rw [mem₁₀, mem₉, Proof.Cmac.bytesAt_frame (zero4_frame _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), mem₈, copy4_bytes, m₇,
      Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.i_scr) (by decide)]
  · rw [mem₁₀, mem₉, zero4_bytes]

/-! ## The tweak -/

/-- After the call enciphering the tweak value. -/
structure TwPost (s₀ s : State) : Prop where
  inv : Inv s₀ s
  frame : Frame [scrR s₀, stkR s₀] s₀.mem s.mem
  t : bytesAt s.mem (Tp s₀) 16 = t0 s₀

theorem UPre.sched_frame {s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hd : ∀ r ∈ rs, r = dataR s₀ ∨ r = scrR s₀ ∨ r = stkR s₀ ∨ Region.Sub r (dataR s₀)) :
    bytesAt s.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) = bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega_using [hRb])
  rcases hd r hr with rfl | rfl | rfl | h
  · exact hp.sch_data.sub_left (Region.sub_prefix hRb)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hRb)
  · exact hp.stk_sch.symm.sub_left (Region.sub_prefix hRb)
  · exact (hp.sch_data.sub_left (Region.sub_prefix hRb)).sub_right h

/-- The call enciphering the tweak value. -/
theorem tcall_wp {s₂ : State} (h₂ : ProPost s₀ s₂) : WP isa encCall s₂ (TwPost s₀) := by
  refine WP.mono (xts_call true h₂.pre) fun s₃ c => ?_
  obtain hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega_using [h]
  obtain stk := UPre.stk_eq (s₀ := s₀) h₂.inv.sp
  obtain aT := hp.scrA (d := tO) (by decide)
  obtain aZ := hp.scrA (d := zO) (by decide)
  obtain eK : bytesAt s₂.mem (State.addr (K s₀)) (16 * (R s₀ + 1)) =
      bytesAt s₀.mem (State.addr (K s₀)) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.tsch_scr.sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])
  refine ⟨Inv.call hp h₂.inv (by rw [aZ]; exact z_sub) (.inr (by rw [aT]; exact t_sub)) c, ?_, ?_⟩
  · refine (h₂.frame.sub fun r hr => ?_).trans (c.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, by rw [aZ]; exact sub_trans z_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, by rw [aT]; exact sub_trans t_sub s_sub⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stkR s₀, by simp, by rw [stk]; exact fun _ h => h⟩
  · have o := c.out
    rw [aZ, aT] at o
    have := Proof.AesXts.Unit.tweak_of (R := R s₀) (w := bytesAt s₂.mem (State.addr (K s₀)) (16 * (R s₀ + 1)))
      o h₂.z
    rw [this, h₂.ti, eK]

theorem tweak_wp : WP isa tweak s₀ (TwPost s₀) :=
  WP.seq (WP.mono (pro_wp hp) fun _ h₂ => tcall_wp hp h₂)

/-! ## A call on whole blocks from the tweak -/

/-- After the call on the first `N` whole blocks from the tweak `T`. -/
structure AllPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  out : Spec.Cbc.blocksAt s.mem (Da s₀) N =
    Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (Da s₀) N)
  tw : bytesAt s.mem (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N
  frame : Frame [⟨Da s₀, 16 * N⟩, scrR s₀, stkR s₀] s₀.mem s.mem

theorem blocks_call (enc : Bool) {N : Nat} (hN : 16 * N ≤ Len s₀) {s : State} (h : TwPost s₀ s)
    (hpre : XPre s (W s₀) (Tv s₀) (D s₀) (S s₀) N (R s₀)) :
    WP isa (.frame (.push [.r12, .lr]) (.call (xname enc) (xcode enc)) (.pop .r12 (4 * [Reg.r12, .lr].length))) s
      (AllPost enc s₀ N) := by
  refine WP.mono (xts_call enc hpre) fun s' x => ?_
  obtain aT := hp.scrA (d := tO) (by decide)
  obtain stk := UPre.stk_eq (s₀ := s₀) h.inv.sp
  obtain dS : Region.Sub ⟨Da s₀, 16 * N⟩ (dataR s₀) := Region.sub_prefix hN
  obtain eW := hp.sched_frame (h.inv.frame) (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  obtain eD : Spec.Cbc.blocksAt s.mem (Da s₀) N = Spec.Cbc.blocksAt s₀.mem (Da s₀) N :=
    blocksAt_frame h.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.data_scr.sub_left dS
      · exact hp.stk_data.symm.sub_left dS) (by have := hp.data_fit; omega_using [hN, this])
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl dS) x, ?_, ?_, ?_⟩
  · have o := x.out
    rw [aT] at o
    rw [o, eW, h.t, eD]
  · have o := x.tw
    rw [aT] at o
    rw [o, h.t]
  · refine (h.frame.sub fun r hr => ?_).trans (x.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scrR s₀, by simp, by rw [aT]; exact sub_trans t_sub s_sub⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, wk_sub⟩
      · exact ⟨stkR s₀, by simp, by rw [stk]; exact fun _ h => h⟩

/-- `TwPost` across code that keeps the callee-saved registers and memory. -/
theorem TwPost.keep {s s' : State} (h : TwPost s₀ s) (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : TwPost s₀ s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _)
    (fun r hr => hg r (pinned_pres r hr).1 (pinned_pres r hr).2) hsp hrd hwr
  frame := by rw [hm]; exact h.frame
  t := by rw [hm]; exact h.t

/-! ## The epilogue -/

omit hp in
theorem restore_eq :
    restore = (saved.take 6 ++ [((Reg.r8, 2232) : Reg × Nat)]).map (fun (p : Reg × Nat) => Instr.ldr p.1 .r8 p.2) ++
      [] := rfl

theorem fin_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem := by
  rw [restore_eq]
  obtain hsv : Spill.Saved s.mem (State.addr (s.gpr .r8)) s₀.gpr (saved.take 6 ++ [((Reg.r8, 2232) : Reg × Nat)]) := by
    rw [h.r8]; exact h.saved
  refine Spill.restoreBase_slots_ok (lo := 2208) (hi := 2236) (by decide) (by decide)
    (by rw [h.r8]; have := hp.scr_fit; omega_using [this]) (fun d h₁ h₂ => ?_) hsv
    fun s' ld ho m _ _ sp => WP.block_nil ⟨⟨fun r hr => ?_, by rw [sp, h.sp]⟩, m⟩
  · rw [h.rd, h.wr, h.r8, hp.rd, hp.wr]
    exact in_rw (r := scrR s₀) (by simp) (hp.cS _ _ (by omega_using [h₂]))
  · by_cases hs : r ∈ (saved.take 6 ++ [(Reg.r8, 2232)]).map Prod.fst
    · exact Spill.restored_reg ld hs
    · have hk : ∀ r ∈ preserved, r ∉ (saved.take 6 ++ [(Reg.r8, 2232)]).map Prod.fst → r = .r10 ∨ r = .r11 := by
        decide
      rw [ho r hs]
      rcases hk r hr hs with rfl | rfl
      · exact h.rest _ (by simp)
      · exact h.rest _ (by simp)

/-! ## Bytes of the data a call keeps -/

/-- The bytes of a part `X` of the data that a call on other blocks keeps. -/
theorem call_keeps {enc : Bool} {s s' : State} {Wk T Dd : BitVec 32} {N Rr : Nat} {X : Region}
    (hX : Region.Sub X (dataR s₀)) (hXD : X.Disjoint ⟨State.addr Dd, 16 * N⟩)
    (hT : Region.Sub ⟨State.addr T, 16⟩ (scrR s₀)) (hsp : s.sp = s₀.sp)
    (c : XPost enc s Wk T Dd (S s₀) N Rr s') (hn : X.len ≤ 2 ^ 64) :
    bytesAt s'.mem X.base X.len = bytesAt s.mem X.base X.len :=
  Proof.Cmac.bytesAt_frame c.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.data_scr.sub_left hX).sub_right hT
    · exact hXD
    · exact (hp.data_scr.sub_left hX).sub_right wk_sub
    · rw [UPre.stk_eq hsp]; exact hp.stk_data.symm.sub_left hX) hn

end

end VG.Proof.AesXts.Arm.Unit

end

end


/-!
# XTS-AES of data units on ARMv7: encryption

`encrypt_wp`: the tweak, the call on the whole blocks, and for a partial
block the swap and the call on the last whole block, then the epilogue. The
data unit is `encWith` of the cipher and the tweak, which is
`aesXtsEncrypt` of any key whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.Arm.Unit

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesXts.ArmUnit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (Da s₀) (Len s₀) =
    withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (Da s₀) (Len s₀))

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (Da s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (Da s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨Da s₀, 16 * N⟩, scrR s₀, stkR s₀] s₀.mem m

theorem AllPost.mem {enc : Bool} {s₀ : State} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tv s₀) (D s₀) (S s₀) N (R s₀)

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  r0 : s.gpr .r0 = BitVec.ofNat 32 (16 * M s₀)
  r1 : s.gpr .r1 = BitVec.ofNat 32 (B s₀)
  z : s.z = decide (B s₀ = 0)

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 32 o) (Lv s₀) (S s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hsp hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- `r9 + r0 − 16` is the last whole block. -/
theorem last_of {s : State} (h9 : s.gpr .r9 = D s₀) (h0 : s.gpr .r0 = BitVec.ofNat 32 (16 * M s₀)) :
    s.gpr .r9 + s.gpr .r0 - 16 = Lv s₀ := by
  rw [h9, h0, last_eq _ hp.m_pos]

theorem UPre.l_fit : (Lv s₀).toNat + 16 + B s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := len_eq s₀; have := hp.m_pos
  rw [hp.dataN (by omega_arith)]
  omega_arith

theorem UPre.lb_in {s : State} (hwr : s.wr = s₀.wr) (i : Nat) (hi : i < 16 + B s₀) :
    InRegions s.wr (L s₀ + BitVec.ofNat 64 i) 1 := by
  have : B s₀ < 16 := Nat.mod_lt _ (by decide)
  rw [hwr, hp.wr]
  exact in_rw (r := dataR s₀) (by simp)
    (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi]) (by omega_using [hi, this])))

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 (16 * M s₀)) (h1 : s.gpr .r1 = BitVec.ofNat 32 (B s₀))
    (h2 : s.gpr .r2 = Lv s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.mono (swap_ok s (Nat.pos_of_ne_zero hB) hb (by rw [h2]; exact hp.lA)
      (by rw [h2]; exact hp.l_fit) h1 (hp.lb_in hi.wr))
    fun s₂ ⟨mem₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨s₃, run₃, x0₃, x1₃, x2₃, x3₃, x12₃, lr₃, cs₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    argsL_ok s₂ (o := o) (by rcases ho with rfl | rfl <;> decide)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₂ (r : Reg) (hr : r ∈ pinned) : s₂.gpr r = s.gpr r := by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g₂ _ (by decide) (by decide) (by decide) (by decide)
  obtain inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₂ sp₂ rd₂ wr₂
  obtain inv₃ : Inv s₀ s₃ := Inv.step hp inv₂ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₃]; exact Frame.refl _ _) (fun r hr => cs₃ r (pinned_pres r hr).1 (pinned_pres r hr).2) sp₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr inv₃.sp ho (by rw [x0₃, inv₂.r4])
    (by rw [x1₃, inv₂.r5, r1_ofNat]) (by rw [x2₃, inv₂.r8]) ?_ x12₃ (by rw [lr₃, inv₂.r8]), by rw [mem₃, mem₂]⟩
  rw [x3₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.r9 h0

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m)
    (hB : B s₀ ≠ 0) : WP isa encCall s (Fin true s₀) := by
  obtain hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  obtain aT := hp.scrA (d := tO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call true h.pre) fun s₄ c => ?_
  obtain sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  obtain tS : Region.Sub ⟨State.addr (S s₀ + BitVec.ofNat 32 tO), 16⟩ (scrR s₀) := by
    rw [aT]; exact sub_trans t_sub s_sub
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl (by rw [aL]; exact hp.l_sub)) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub
      · exact hp.stk_data.symm.sub_left hp.tl_sub) (by omega_using [hb])
  · have o := c.out
    rw [aT, aL] at o
    rw [Proof.AesXts.Unit.crypt_one_of o,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp), h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨Da s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) (by rw [aL]; exact hp.hd_l)
      tS h.inv.sp c (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) tS h.inv.sp c
      (by dsimp only; omega_using [hb]), h.mem]

/-- The last whole block's address, after `split`. -/
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h0 : s.gpr .r0 = BitVec.ofNat 32 (16 * M s₀)) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .r2 = Lv s₀ → (∀ r, r ≠ .r2 → s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block lastAddr) s Q := by
  obtain ⟨s', run', x2', g', sp', mem', rd', wr'⟩ := lastAddr_ok s
  exact WP.of_runBlock ⟨s', run', hq s' (by rw [x2']; exact last_of hp hi.r9 h0) g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_r2 {s s' : State} (hg : ∀ r, r ≠ .r2 → s'.gpr r = s.gpr r) : ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => hg r (by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (lastAddr_wp hp h.all.inv h.r0 fun s₁ x2₁ g₁ sp₁ mem₁ rd₁ wr₁ => ?_))
  obtain h₁ := AllPost.keep hp h.all (keep_r2 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.r0])
    (by rw [g₁ _ (by decide), h.r1]) x2₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa encSteal s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (Da s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (Da s₀) (Len s₀))) :
    (unitArm enc).post s₀ s' := by
  intro key hk
  obtain hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (State.addr (I s₀)) 16) hk
  obtain hl : 16 ≤ (bytesAt s₀.mem (Da s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `r0`, the bytes after
them in `r1`, and Z set if there are none. -/
theorem split_wp {s : State} (h : Inv s₀ s) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .r0 = BitVec.ofNat 32 (16 * M s₀) → s'.gpr .r1 = BitVec.ofNat 32 (B s₀) →
      s'.z = decide (B s₀ = 0) → (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) → s'.sp = s.sp →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block split) s Q := by
  obtain ⟨s', run', x0', x1', z', g', sp', mem', rd', wr'⟩ := split_ok s
  rw [h.r7] at x0' x1' z'
  exact WP.of_runBlock ⟨s', run', hq s' x0' x1' z' g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_r0r1 {s s' : State} (hg : ∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) :
    ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) := by
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x12₂, lr₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := argsAll_ok s
  obtain h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
  exact WP.of_runBlock ⟨s₂, run₂, h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr h₂.inv.sp (N := M s₀)
    (by rw [len_eq s₀]; omega_using []) (by rw [x0₂, h.inv.r4]) (by rw [x1₂, h.inv.r5, r1_ofNat])
    (by rw [x2₂, h.inv.r8]) (by rw [x3₂, h.inv.r9]) (by rw [x12₂, h.inv.r7]) (by rw [lr₂, h.inv.r8])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  split_wp h.inv fun _ x0₄ x1₄ z₄ g₄ sp₄ mem₄ rd₄ wr₄ =>
    ⟨AllPost.keep hp h (keep_r0r1 g₄) sp₄ mem₄ rd₄ wr₄, x0₄, x1₄, z₄⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.z = decide (B s₀ = 0)) : isa.eval .eq s = some (decide (B s₀ = 0)) := by
  show VG.Arm.eval .eq s = _; rw [Proof.MdStream.Arm.eval_eq, h]

theorem encrypt_wp :
    WP isa Impl.AesXts.ArmUnit.encrypt s₀ fun s' => abiPreserved s₀ s' ∧ (unitArm true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true (by rw [len_eq s₀]; omega_using []) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.z)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.Arm.Unit
