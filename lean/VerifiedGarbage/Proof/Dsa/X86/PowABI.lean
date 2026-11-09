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
