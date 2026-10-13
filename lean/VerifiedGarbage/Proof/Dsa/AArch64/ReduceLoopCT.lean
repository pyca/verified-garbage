module

public import VerifiedGarbage.Proof.Dsa.AArch64.ReduceByteCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Constant time of nonempty streaming reduction -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def ReducePublic.remaining (p : ReducePublic) (j : Nat) : ReducePublic :=
  { p with bytes := { p.bytes with ptr := p.bytes.ptr + BitVec.ofNat 64 j, len := p.bytes.len - j }
           lengthBound := Nat.lt_of_le_of_lt (Nat.sub_le _ _) p.lengthBound }

def ReduceLoopPre (p : ReducePublic) (j : Nat) (s : State) : Prop :=
  ∃ (bs : List Byte) (acc : Nat), bs.length = p.bytes.len - j ∧
    ReduceState s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv (p.bytes.ptr + BitVec.ofNat 64 j) bs acc

theorem reduceLoop_step (M : Mont) {p : ReducePublic} {j : Nat} {s : State}
    (hj : j < p.bytes.len) (h : ReduceLoopPre p j s) :
    WP isa (Arithmetic.reduceByte M.mm) s fun t =>
      isa.eval (.nonzero .x .x3) t = some (decide (j + 1 < p.bytes.len)) ∧ ReduceLoopPre p (j + 1) t := by
  obtain ⟨bs, acc, hlen, h⟩ := h
  cases bs with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons b bs =>
    refine WP.mono (reduceByte_ok M h p.lower (by have := p.fits; have := p.upper; omega)
      p.greater255 p.odd (by have := p.lengthBound; omega))
      fun t ⟨ht, hz, _, _⟩ => ?_
    have hpos : p.bytes.ptr + BitVec.ofNat 64 j + 1 = p.bytes.ptr + BitVec.ofNat 64 (j + 1) := by
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
    refine ⟨?_, bs, _, ?_, hpos ▸ ht⟩
    · simp only [List.length_cons] at hlen
      have hb : bs.length < 2 ^ 64 := by have := p.lengthBound; omega
      rw [eval_nonzero, hz, ne_zero_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]
      exact congrArg some (decide_eq_decide.mpr (by omega))
    · simp only [List.length_cons] at hlen
      omega

theorem reduceLoop_ct (M : Mont) :
    RelCT isa (Two fun p s => 0 < p.bytes.len ∧ ReduceLoopPre p 0 s)
      (.loop (Arithmetic.reduceByte M.mm) (.nonzero .x .x3)) (fun _ _ => True) := by
  have hct := two_map (Φ := fun (p : ReducePublic × Nat) s => p.2 < p.1.bytes.len ∧ ReduceLoopPre p.1 p.2 s)
    (fun p : ReducePublic × Nat => p.1.remaining p.2)
    (fun p s ⟨hj, bs, acc, hlen, h⟩ =>
      ⟨bs, acc, hlen, by omega, h⟩) (reduceByte_ct M)
  refine (two_loop (Φ := ReduceLoopPre) (Ψ := fun _ _ => True) (fun p => p.bytes.len) hct ?_).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)
  intro p j s hj hs
  exact WP.mono (reduceLoop_step M hj hs) fun t ⟨hz, ht⟩ => ⟨hz, fun _ => ht, fun _ => trivial⟩

end VG.Proof.Dsa.AArch64
