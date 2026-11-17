module

public import VerifiedGarbage.Impl.Argon2.X86_64.AddressCache
public import VerifiedGarbage.Proof.Argon2.X86_64.AddressCallsStage
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceStart

/-! ### `Argon2.X86_64.AddressCacheMeta`, which this module and modules that import it used -/

section

/-! Public cache counters and indexed-word arguments. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

def counter (index : Addr) : Addr := (index >>> 7) + 1

theorem check_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 8) 8) :
    WP isa (.block check) s fun t => t.gpr .rax = counter (s.gpr .r15) ∧
      t.zf = decide (counter (s.gpr .r15) = s.mem.readW (off (s.gpr .rbp) 8) 64) ∧
      Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [check, counter, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, execAlu, State.load64, ea_at, hr, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_arithFlags, reduceCtorEq, ite_true, ite_false, and_self,
    show 1 ≤ (7 : Nat) ∧ (7 : Nat) ≤ 63 from by decide,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, ?_⟩
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ReferenceStart.sub_zero_iff]
    exact ⟨fun h => decide_eq_true h, of_decide_eq_true⟩
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr, ite_false]
    all_goals rfl

theorem counter_nat (index : Addr) : counter index = BitVec.ofNat 64 (index.toNat / 128 + 1) := by
  have shifted : index >>> 7 = BitVec.ofNat 64 (index.toNat / 128) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := index.isLt; omega_using [])]
  unfold counter
  rw [shifted]
  exact (BitVec.ofNat_add _ _).symm

theorem counter_ne_zero (index : Addr) : counter index ≠ 0 := by
  have bound : index.toNat / 128 + 1 < 2 ^ 64 := by have := index.isLt; omega_using []
  intro h
  have nat := congrArg BitVec.toNat h
  rw [counter_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound] at nat
  change index.toNat / 128 + 1 = 0 at nat
  omega_using [nat]

theorem wordArgs_ok (s : State)
    (hr : InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) 248) 8) :
    WP isa (.block wordArgs) s fun t => t.gpr .rcx = AddressCalls.work s ∧
      t.gpr .rax = s.gpr .r15 &&& 127 ∧ Divide.Keeps [.rcx, .rax] s t := by
  apply WP.of_runBlock
  simp only [wordArgs, AddressCalls.work, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, ea_at, hr, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_true, ite_false,
    show BitVec.signExtend 64 (127 : BitVec 32) = (127 : Addr) from rfl,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem index_nat (index : Addr) : index &&& 127 = BitVec.ofNat 64 (index.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  exact Nat.and_two_pow_sub_one_eq_mod index.toNat 7

end VG.Proof.Argon2.X86_64.AddressCache

end

end

/-! Read exactly the public indexed word of the cached address block. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

def wordAddress (s : State) : Addr :=
  s.gpr .rcx + s.gpr .rax * BitVec.ofNat 64 8 + BitVec.ofInt 64 6144

theorem wordRead_ok (s : State) (hr : InRegions (s.rd ++ s.wr) (wordAddress s) 8) :
    WP isa (.block wordRead) s fun t => t.gpr .rdi = s.mem.readW (wordAddress s) 64 ∧
      Divide.Keeps [.rdi] s t := by
  dsimp only [wordAddress] at hr
  apply WP.of_runBlock
  simp only [wordRead, wordAddress, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, State.load64, State.ea, hr, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]
  all_goals rfl

theorem wordAddress_args {s a : State}
    (scratch : a.gpr .rcx = AddressCalls.work s)
    (index : a.gpr .rax = s.gpr .r15 &&& 127) :
    wordAddress a = off (off (AddressCalls.work s) 6144) (8 * ((s.gpr .r15).toNat % 128)) := by
  unfold wordAddress off
  rw [scratch, index, index_nat, ← BitVec.ofNat_mul, Nat.mul_comm]
  change AddressCalls.work s + BitVec.ofNat 64 (8 * ((s.gpr .r15).toNat % 128)) +
    BitVec.ofNat 64 6144 = _
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * ((s.gpr .r15).toNat % 128)))
    (BitVec.ofNat 64 6144), ← BitVec.add_assoc]

theorem word_ok (s : State) (h : AddressCalls.Ready s) :
    WP isa Impl.Argon2.X86_64.AddressCache.word s fun t => t.gpr .rdi =
      (blockAt s.mem (off (AddressCalls.work s) 6144))[(s.gpr .r15).toNat % 128]'(Nat.mod_lt _ (by decide)) ∧
      Divide.Keeps [.rcx, .rax, .rdi] s t := by
  unfold Impl.Argon2.X86_64.AddressCache.word
  refine WP.seq ((wordArgs_ok s h.frameRead).mono ?_)
  rintro a ⟨scratch, index, keeps⟩
  have address := wordAddress_args scratch index
  have read : InRegions (a.rd ++ a.wr) (wordAddress a) 8 := by
    rw [address, keeps.rd, keeps.wr]
    have cover := AddressCalls.work_cover s h 6144 1024 (by decide)
    have writable := cover _ _ ⟨⟨off (AddressCalls.work s) 6144, 1024⟩, by simp,
      Offset.contains_base _ (d := 8 * ((s.gpr .r15).toNat % 128)) (n := 8) (k := 1024)
        (by have := Nat.mod_lt (s.gpr .r15).toNat (by decide : 0 < 128); omega_using []) (by omega_using [])⟩
    obtain ⟨r, hr, hc⟩ := writable
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine (wordRead_ok a read).mono ?_
  rintro t ⟨value, tail⟩
  refine ⟨?_, (keeps.mono (by decide)).trans (tail.mono (by decide))⟩
  rw [value, address, keeps.mem]
  change s.mem.readW _ 64 = (blockAt _ _)[(⟨_, Nat.mod_lt _ (by decide)⟩ : Fin 128)]
  rw [blockAt_get]

end VG.Proof.Argon2.X86_64.AddressCache
