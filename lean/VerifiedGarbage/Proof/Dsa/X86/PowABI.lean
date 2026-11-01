module

public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.ModPowContract

/-! # Resources for the shared IA-32 modular-exponentiation contract -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Pow

abbrev ws (s : State) : Addr := (arg s 0).setWidth 64
abbrev bytes (s : State) : Nat := (arg s 1).toNat * 8

/-- The facts of the contract's precondition, for a contract of `k` bytes of
stack: the exponentiation's own (96, for its calls) or a caller's view of it
as a body of its own (20). -/
structure ABI (n e : Nat) (s : State) (k : Nat := 20) : Prop where
  stackLow : k ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  rd : s.rd = [⟨argAddr s 0, 8⟩]
  wr : s.wr = [⟨ws s, bytes s⟩]
  retScratch : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨ws s, bytes s⟩
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 k, k⟩ : Region).Disjoint ⟨ws s, bytes s⟩
  bound : (arg s 0).toNat + bytes s ≤ 2 ^ 32
  size : contextBytes n ≤ bytes s
  odd : Proof.Dsa.ModPow.numAt s.mem (ws s) (slot n 0) (8 * n) % 2 = 1
  gt_one : 1 < Proof.Dsa.ModPow.numAt s.mem (ws s) (slot n 0) (8 * n)

theorem abi_of {n e : Nat} {s : State}
    (h : (Proof.Dsa.ModPow.powContract (layout n e) abi 96).pre s) : ABI n e s 96 := by
  sig_pre [Proof.Dsa.ModPow.powContract, Proof.Dsa.ModPow.sig, layout, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> try with_reducible assumption
  dsimp only [bytes]
  omega

theorem ABI.entry {n e k : Nat} {s : State} (A : ABI n e s k) (hk : 20 ≤ k := by decide) :
    Entry s (ws s) (bytes s) := by
  have H : (ws s).toNat + bytes s ≤ 2 ^ 32 := by
    simpa only [ws, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (arg s 0).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using A.bound
  refine ⟨?_, rfl, ?_, H, ?_⟩
  · rw [A.rd, A.wr]
    refine ⟨⟨argAddr s 0, 8⟩, List.mem_cons_self .., ?_⟩
    simpa only [BitVec.add_zero] using
      Offset.contains_base (argAddr s 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [A.wr]; exact List.mem_cons_self ..
  · apply VG.Proof.Weierstrass.X86.stkOk_of hk A.stackLow H ?_ A.belowScratch
    have B := A.size
    simp only [contextBytes, slot, stride] at B
    omega

/-- The 96 bytes of stack the calls use lie apart from the working space. -/
theorem ABI.room {n e : Nat} {s : State} (A : ABI n e s 96) : CallRoom (s.gpr .esp) (ws s) (bytes s) := by
  refine ⟨A.stackLow, ?_⟩
  have h := A.belowScratch
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth A.stackLow]
  exact h

theorem read_eq_val32 (m : Mem) (base : Addr) : ∀ (k d : Nat),
    (m.read (off base d) (4 * k)).toNat = val32 m base d k
  | 0, d => by simp [Mem.read, val32]
  | k + 1, d => by
    rw [show 4 * (k + 1) = 4 * k + 4 from rfl, read_toNat_add, val32, ← read_eq_val32 m base k (d + 4),
      Offset.add_add]
    congr 1

theorem numAt_eq8 (m : Mem) (base : Addr) (d n : Nat) :
    Proof.Dsa.ModPow.numAt m base d (8 * n) = wordsVal m base d n := read_eq_wordsVal m base n d

theorem numAt_eq4 (m : Mem) (base : Addr) (d e : Nat) :
    Proof.Dsa.ModPow.numAt m base d (4 * e) = val32 m base d e := read_eq_val32 m base e d

end VG.Proof.Dsa.X86.Pow
