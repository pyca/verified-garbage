module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Rsa.MontContract
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Ffdh.Arm.Block
public import VerifiedGarbage.Proof.X25519.Arm.Instr

/-! ### `Ffdh.Arm.ParameterCandidate.TablePointer`, which this module and modules that import it used -/

section

/-! Locate the compact small-prime table beyond the primality workspace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

private theorem tableStride (n : Nat) (bound : n ≤ 1024) :
    (((BitVec.ofNat 32 n + 7) >>> 3) + 2) <<< 3 = BitVec.ofNat 32 (8 * ((n + 7) / 8 + 2)) := by
  have shift : BitVec.ofNat 32 (n + 7) >>> 3 = BitVec.ofNat 32 ((n + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega_using [bound] : n + 7 < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [bound] : (n + 7) / 8 < 2 ^ 32)]
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change (((BitVec.ofNat 32 n + BitVec.ofNat 32 7) >>> 3) + BitVec.ofNat 32 2) * BitVec.ofNat 32 8 = _
  rw [BitVec.ofNat_add_ofNat, shift, BitVec.ofNat_add_ofNat, BitVec.ofNat_mul_ofNat]
  congr 1
  omega_using []

private theorem tableAddress (base : BitVec 32) (n : Nat) :
    (34 * BitVec.ofNat 32 (8 * ((n + 7) / 8 + 2)) + base) + 256 =
      base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34) := by
  change (BitVec.ofNat 32 34 * BitVec.ofNat 32 (8 * ((n + 7) / 8 + 2)) + base) + BitVec.ofNat 32 256 = _
  rw [BitVec.ofNat_mul_ofNat, BitVec.add_comm _ base, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have equal : 34 * (8 * ((n + 7) / 8 + 2)) + 256 = arrAt ((n + 7) / 8) 34 := by
    simp only [arrAt, VG.Proof.Rsa.Mont.hdrBytes]
    omega_using []
  exact congrArg (fun d : Nat => base + BitVec.ofNat 32 d) equal

theorem tablePointer_ok (s : State) (base : BitVec 32) (n : Nat) (bound : n ≤ 1024)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12#32)) 4)
    (savedBase : s.mem.readW (State.addr s.sp) 32 = base)
    (savedWidth : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer) s fun t =>
      (t.gpr .r11 = base + BitVec.ofNat 32 (arrAt ((n + 7) / 8) 34) ∧ t.mem = s.mem) ∧
        Rest [.r0, .r7, .r11] s t := by
  refine withRest_all [.r0, .r7, .r11] ?_ (by rfl) (by rfl)
  have enc256 : encodable (256 : BitVec 32) = true := by decide
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, mov_exec, mul_exec, logic_exec, ldrSp_exec, Op2.eval,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.sp_setReg, Option.map_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, reduceCtorEq, and_true, Nat.reduceLT, Nat.reduceLeDiff,
    (by decide : encodable (7 : BitVec 32) = true), (by decide : encodable (2 : BitVec 32) = true),
    (by decide : encodable (34 : BitVec 32) = true), BitVec.add_zero, readBase, readWidth, savedBase, savedWidth,
    enc256, tableStride n bound, tableAddress base n]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.TableWrites`, which this module and modules that import it used -/

section

/-! The complete RSA-prime table uses the same entries as RSA's sieve. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem tableEntry_small {i : Nat} (bound : i < 1024) : VG.Impl.RsaKeyGen.tabEntry i < 2^16 := by
  have := (VG.Proof.RsaKeyGen.tabEntry_facts bound).2.2
  omega_using [this]

theorem tableWrites_ok {s : State} {base : BitVec 32} {size offset : Nat}
    (space : Workspace s base size) (ptr : s.gpr .r11 = base + BitVec.ofNat 32 offset) :
    ∀ count, count ≤ 1024 → offset + 4 * count ≤ size →
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrites count)) s fun t =>
      (∀ j < count, w32 t.mem (State.addr base) (offset + 4 * j) = VG.Impl.RsaKeyGen.tabEntry j) ∧
      Outside (State.addr base) offset (4 * count) s.mem t.mem ∧ Rest [.r1] s t
  | 0, _, _ => WP.block_nil ⟨by intro j hj; omega, Outside.refl _ _ _ _, Rest.refl _ _⟩
  | count + 1, bounded, fit => by
    rw [VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrites, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (tableWrites_ok space ptr count (by omega_using [bounded]) (by omega_using [fit])) ?_
    rintro u ⟨values, outside, rest⟩
    have small := tableEntry_small (i := count) (by omega_using [bounded])
    refine wp_movw fun v moved => ?_
    have kept : Rest [.r1] s v := rest.trans (moved.rest (by simp))
    have address : State.addr (v.gpr .r11 + BitVec.ofNat 32 (4 * count)) =
        off (State.addr base) (offset + 4 * count) := by
      rw [kept.gpr .r11 (by simp), ptr, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact VG.Arm.addr_add (by have := space.nowrap; omega_using [fit, this])
    refine wp_str (by omega_using [bounded]) address ((space.congr kept.wr).write (by omega_using [fit])) fun t store => WP.block_nil ?_
    have changed : Outside (State.addr base) (offset + 4 * count) 4 u.mem t.mem := by
      rw [store.mem, moved.mem]
      exact writeW32_outside _ _ _ (by have := space.nowrap; omega_using [fit, this])
    refine ⟨?_, (outside.mono (Nat.le_refl _) (by omega_using [])).trans (changed.mono (by omega_using []) (by omega_using [])),
      kept.trans (store.rest _)⟩
    intro j hj
    by_cases earlier : j < count
    · rw [changed.w32 (by omega_using [earlier]) (by have := space.nowrap; omega_using [fit, hj, this])]
      exact values j earlier
    · have same : j = count := by omega_using [hj, earlier]
      subst j
      rw [store.mem, moved.gpr, w32_write_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_using [small] : VG.Impl.RsaKeyGen.tabEntry count < 2 ^ 16),
        Nat.mod_eq_of_lt (by omega_using [small] : VG.Impl.RsaKeyGen.tabEntry count < 2 ^ 32)]

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Initialize exactly the table prefix the FFDH small-prime sieve uses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

def TableData (base : BitVec 32) (n : Nat) (m : Mem) : Prop :=
  ∀ i < 1024, w32 m (State.addr base) (arrAt ((n + 7) / 8) 34 + 4 * i) = VG.Impl.RsaKeyGen.tabEntry i

theorem tableWrite_ok {s : State} {base : BitVec 32} {size n : Nat}
    (space : Workspace s base size) (bound : n ≤ 1024)
    (fit : arrAt ((n + 7) / 8) 34 + 4096 ≤ size)
    (readBase : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12#32)) 4)
    (savedBase : s.mem.readW (State.addr s.sp) 32 = base)
    (savedWidth : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 n) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) s fun t =>
      TableData base n t.mem ∧
      Frame [⟨off (State.addr base) (arrAt ((n + 7) / 8) 34), 4096⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r7, .r11] s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite, WP.block_append_iff]
  refine WP.mono (tablePointer_ok s base n bound readBase readWidth savedBase savedWidth) ?_
  rintro u ⟨⟨ptr, memory⟩, rest⟩
  refine WP.mono (tableWrites_ok (space.congr rest.wr) ptr 1024 (by decide) fit) ?_
  rintro t ⟨values, outside, keep⟩
  rw [memory] at outside
  exact ⟨values, VG.Proof.Bignum.outside_frame outside (by have := space.nowrap; omega_using [fit, this]),
    (rest.mono (by simp)).trans (keep.mono (by simp))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
