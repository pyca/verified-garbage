module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Inverse
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

import VerifiedGarbage.Proof.RsaKeyGen.X86.DisjointBounds
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Halve32
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Bignum.ByteWords
/-! # `vg_rsa_keygen_inverse`'s precondition: its arguments and its working space -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/InverseNum.lean`, which only this module imported.
section

/-! # `vg_rsa_keygen_inverse`'s numbers are the workspace's little-endian words -/

section
namespace VG.Proof.RsaKeyGen
open VG VG.Proof.Mont

theorem os2ip_snoc (l : List Byte) (b : Byte) : Spec.Rsa.os2ip (l ++ [b]) = 256 * Spec.Rsa.os2ip l + b.toNat := by
  simp only [Spec.Rsa.os2ip, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem bytesAt_succ (m : Mem) (a : Addr) (n : Nat) :
    Spec.Rsa.bytesAt m a (n + 1) = m a :: Spec.Rsa.bytesAt m (a + 1) n := by
  unfold Spec.Rsa.bytesAt
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    congr 1
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega

/-- The octets at `a`, least significant first, are the value of the little-endian read. -/
theorem os2ip_reverse_bytesAt (m : Mem) : ∀ (n : Nat) (a : Addr),
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m a n).reverse = (m.read a n).toNat
  | 0, _ => rfl
  | n + 1, a => by
    rw [bytesAt_succ, List.reverse_cons, os2ip_snoc, os2ip_reverse_bytesAt m n (a + 1), read_toNat_succ]
    omega

theorem inverseNum_eq (m : Mem) (ws : Addr) (len j : Nat) :
    Proof.RsaKeyGen.inverseNum m ws len j =
      val32 m ws (160 + j * (Proof.RsaKeyGen.inverseBytes len + 8)) (2 * ((len + 7) / 8)) := by
  unfold Proof.RsaKeyGen.inverseNum
  rw [os2ip_reverse_bytesAt, show Proof.RsaKeyGen.inverseBytes len = 4 * (2 * ((len + 7) / 8)) by
    unfold Proof.RsaKeyGen.inverseBytes; omega]
  exact VG.Proof.Bignum.read_eq_val32 m ws _ _

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Bignum.X86 (CallArgument)

/-- The frame's sixteen bytes, and below them the twenty the workspace keeps apart from (`StkOk`). -/
def inverseStack : Nat := 36

def contract : Contract isa := Proof.RsaKeyGen.inverseContract abi inverseStack

def base (s : State) : Addr := (arg s 0).setWidth 64
def size (s : State) : Nat := 8 * (arg s 1).toNat
def len (s : State) : Nat := (arg s 2).toNat
def argsRegion (s : State) : Region := ⟨argAddr s 0, 12⟩

/-- The precondition, unpacked. -/
structure Entry (s : State) : Prop where
  low : 36 ≤ (s.gpr .esp).toNat
  argsFit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  rd : s.rd = [argsRegion s]
  wr : s.wr = [⟨base s, size s⟩]
  wsArgs : (⟨base s, size s⟩ : Region).Disjoint (argsRegion s)
  stackWs : (⟨(s.gpr .esp).setWidth 64 - 36#64, 36⟩ : Region).Disjoint ⟨base s, size s⟩
  stackArgs : (⟨(s.gpr .esp).setWidth 64 - 36#64, 36⟩ : Region).Disjoint (argsRegion s)
  returnWs : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨base s, size s⟩
  wsFit : (arg s 0).toNat + size s ≤ 2 ^ 32
  lenLow : 1 ≤ len s
  lenHigh : len s ≤ 1024
  room : 160 + 15 * (Proof.RsaKeyGen.inverseBytes (len s) + 8) ≤ size s
  odd : Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 8 % 2 = 1
  large : 1 < Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 8
  v : Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 1 = Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 8
  x₁ : Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 2 = 1
  x₂ : Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 3 = 0
  negated : Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 9 + Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 8 =
    2 ^ (8 * Proof.RsaKeyGen.inverseBytes (len s))
  zero : Proof.RsaKeyGen.inverseNum s.mem (base s) (len s) 10 = 0

theorem entry {s : State} (h : contract.pre s) : Entry s := by
  sig_pre [contract, inverseStack, Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor
  all_goals (try dsimp only [base, size, len, argsRegion])
  all_goals (try simp only [Nat.mul_comm] at *)
  all_goals first | with_reducible assumption | exact Region.Disjoint.symm (by with_reducible assumption) |
    omega_arith

theorem Entry.argOffset {s : State} (A : Entry s) {i : Nat} (hi : i < 3) :
    argAddr s i = argAddr s 0 + BitVec.ofNat 64 (4 * i) := by
  have := A.argsFit
  apply BitVec.eq_of_toNat_eq
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem entered_address (s : State) (i : Nat) :
    VG.Proof.Dsa.X86.stackAddress (Compact.entered s) (i + 4) = argAddr s i := by
  change ((Compact.entered s).gpr .esp + BitVec.ofNat 32 (4 + 4 * (i + 4))).setWidth 64 = _
  rw [Compact.entered, pushed_esp, show 4 * Compact.savedRegisters.length = 16 from rfl,
    show 4 + 4 * (i + 4) = 16 + (4 + 4 * i) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem Entry.argument {s : State} (A : Entry s) {i : Nat} (hi : i < 3) :
    CallArgument (Compact.entered s) (base s) (size s) (i + 4) (arg s i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have contains : (argsRegion s).Contains (argAddr s i) 4 := by
    rw [A.argOffset hi]
    exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [entered_address, Compact.entered, pushed_rd, A.rd]
    exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), contains⟩
  · rw [entered_address, A.argOffset hi]
    exact A.wsArgs.symm.sub_left (Offset.sub_base _ (by change 4 * i + 4 ≤ 12; omega))
  · change (Compact.entered s).mem.readW (VG.Proof.Dsa.X86.stackAddress (Compact.entered s) (i + 4)) 32 = _
    rw [entered_address]
    have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
    have separate : (argsRegion s).Disjoint (below (s.gpr .esp) 16) := by
      unfold below
      rw [Taint.sub_setWidth fit]
      exact (A.stackArgs.sub_left (Offset.sub_below _ (by decide) (by decide))).symm
    exact saved.readW contains (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)

theorem Entry.base_toNat {s : State} (_A : Entry s) : (base s).toNat = (arg s 0).toNat := by
  unfold base
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (arg s 0).isLt (by decide))]

theorem Entry.stkOk {s : State} (A : Entry s) :
    StkOk ((Compact.entered s).gpr .esp) (base s) (size s) := by
  have low := A.low
  have room := A.room
  have espU : ((Compact.entered s).gpr .esp).toNat = (s.gpr .esp).toNat - 16 := by
    rw [Compact.entered, pushed_esp, show 4 * Compact.savedRegisters.length = 16 from rfl,
      BitVec.toNat_sub, BitVec.toNat_ofNat]
    have := (s.gpr .esp).isLt
    omega
  have below36 : ((s.gpr .esp).setWidth 64 - 36#64).toNat = (s.gpr .esp).toNat - 36 := by
    rw [BitVec.toNat_sub, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .esp).isLt (by decide))]
    have := (s.gpr .esp).isLt
    simp only [BitVec.toNat_ofNat]
    omega
  have bounds := VG.Proof.RsaKeyGen.X86.Key.disjoint_bounds (by decide : 0 < 36) (by omega) A.stackWs
  rw [below36, A.base_toNat] at bounds
  unfold StkOk
  rw [espU, A.base_toNat]
  omega

theorem start_ok {s : State} (A : Entry s) :
    WP isa (.block (VG.Impl.Rsa.X86.KeyRt.restoreEdi VG.Impl.RsaKeyGen.X86.Inverse.lay)) (Compact.entered s) fun u =>
      RtWs VG.Impl.RsaKeyGen.X86.Inverse.lay u (base s) (size s) (len s) 15 ∧
        u.mem = (Compact.entered s).mem ∧ Keeps [.edi] (Compact.entered s) u := by
  have ws := A.argument (i := 0) (by decide)
  have ln := A.argument (i := 2) (by decide)
  refine wp_movS ws.readSrc fun u U _ => WP.block_nil ?_
  have edi : u.gpr .edi = arg s 0 := U.gpr
  have outside : Outside (base s) 0 (size s) (Compact.entered s).mem u.mem := by
    rw [U.mem]; exact Outside.refl _ _ _ _
  have room := A.room
  have lenHigh := A.lenHigh
  have lenLow := A.lenLow
  have scr : Scr u (base s) (size s) := by
    refine ⟨by rw [edi]; rfl, ?_, by rw [A.base_toNat]; exact A.wsFit, ?_⟩
    · rw [U.wr, Compact.entered, pushed_wr, A.wr]
      exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · rw [U.other _ (by decide)]
      exact A.stkOk
  refine ⟨⟨⟨scr, ?_, ?_, ?_⟩, ⟨len s, lenHigh, rfl, ?_⟩, ?_, by omega, by decide⟩, U.mem, U.keeps⟩
  · unfold VG.Proof.Rsa.X86.Keys.arr VG.Proof.Rsa.X86.Keys.S VG.Impl.Rsa.X86.Keys.hdr
    unfold Proof.RsaKeyGen.inverseBytes at room
    simp only [kw, Spec.Rsa.modulusWords]
    omega
  · simp only [kw, Spec.Rsa.modulusWords]; omega
  · simp only [kw, Spec.Rsa.modulusWords]; omega
  · have H := ln.keep U.keeps (by decide) outside
    change CallArgument u (base s) (size s) 6 (BitVec.ofNat 32 (arg s 2).toNat)
    rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have H := ws.keep U.keeps (by decide) outside
    change CallArgument u (base s) (size s) 4 (BitVec.ofNat 32 (base s).toNat)
    rwa [A.base_toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem inverseNum_num (m : Mem) (B : Addr) (len j : Nat) :
    Proof.RsaKeyGen.inverseNum m B len j = VG.Proof.Rsa.X86.Keys.num m B (kw len) j := by
  rw [VG.Proof.RsaKeyGen.inverseNum_eq]
  unfold VG.Proof.Rsa.X86.Keys.num VG.Proof.Rsa.X86.Keys.arr VG.Proof.Rsa.X86.Keys.S VG.Impl.Rsa.X86.Keys.hdr
    Proof.RsaKeyGen.inverseBytes
  simp only [kw, Spec.Rsa.modulusWords]
  rw [show 4 * (2 * ((len + 7) / 8) + 2) = 8 * ((len + 7) / 8) + 8 by omega]

/-- The frame's push leaves the working space. -/
theorem Entry.entered_num {s : State} (A : Entry s) {j : Nat} (hj : j < 15) :
    VG.Proof.Rsa.X86.Keys.num (Compact.entered s).mem (base s) (kw (len s)) j =
      VG.Proof.Rsa.X86.Keys.num s.mem (base s) (kw (len s)) j := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega
  have room := A.room
  have saved := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have separate : (⟨base s, size s⟩ : Region).Disjoint (below (s.gpr .esp) 16) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact (A.stackWs.sub_left (Offset.sub_below _ (by decide) (by decide))).symm
  apply val32_congr_at
  intro i hi
  have inside : VG.Proof.Rsa.X86.Keys.arr (kw (len s)) j + 4 * i + 4 ≤ size s := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Proof.Rsa.X86.Keys.S VG.Impl.Rsa.X86.Keys.hdr
    unfold Proof.RsaKeyGen.inverseBytes at room
    simp only [kw, Spec.Rsa.modulusWords] at hi ⊢
    have : j * (4 * (2 * ((len s + 7) / 8) + 2)) + 4 * (2 * ((len s + 7) / 8) + 2) ≤
        15 * (8 * ((len s + 7) / 8) + 8) := by
      have := Nat.mul_le_mul_right (4 * (2 * ((len s + 7) / 8) + 2)) (show j + 1 ≤ 15 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    omega
  have wsFit := A.wsFit
  unfold w32
  congr 1
  apply saved.readW (r := ⟨base s, size s⟩) _ (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)
  exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.RsaKeyGen.X86.Inverse
