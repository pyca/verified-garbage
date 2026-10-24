module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Result
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64Shift
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The native GCD's low and high words encode one exactly when the return bit is set -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Gcd64

theorem equals_one (low high : BitVec 32) :
    ((low - 1) ||| high).toNat = 0 ↔ Mod64.pair low high = 1 := by
  have zero (x : BitVec 32) : x = 0#32 ↔ x.toNat = 0 :=
    ⟨fun H => congrArg BitVec.toNat H, fun H => BitVec.eq_of_toNat_eq H⟩
  rw [← zero, BitVec.or_eq_zero_iff, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  constructor
  · rintro ⟨L, H⟩
    rw [L, H]
    rfl
  · intro H
    unfold Mod64.pair at H
    have highZero : high.toNat = 0 := by omega
    refine ⟨?_, BitVec.eq_of_toNat_eq highZero⟩
    apply BitVec.eq_of_toNat_eq
    change low.toNat = 1
    omega

theorem result_ok {s : State} {base : Addr} {size : Nat}
    (scratch : Scr s base size) (fit : 184 ≤ size) :
    WP isa (.block result) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (val32 s.mem base 176 2 = 1)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
  unfold result
  refine wp_movS (readSrc_sc scratch (by omega)) fun a A _ => wp_subS rfl fun b B _ => ?_
  have Kb : Keeps [.eax] s b := A.keeps.trans B.keeps
  have read := readSrc_sc (scratch.of_keeps Kb (by decide)) (d := 180) (by omega)
  rw [B.mem, A.mem] at read
  refine wp_orS read fun c C => wp_movS rfl fun d D _ => wp_subS rfl fun e E cfE =>
    wp_adcS rfl cfE fun f F _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have tested : d.gpr .eax = (s.mem.readW (off base 176) 32 - 1) ||| s.mem.readW (off base 180) 32 := by
    rw [D.other .eax (by decide), C.gpr, B.gpr, A.gpr]
  refine ⟨?_, ?_, (((((Kb.mono (by decide)).widen C.keeps).widen D.keeps).widen E.keeps).widen F.keeps).widen T.keeps⟩
  · rw [T.gpr, F.gpr, E.other .ecx (by decide), D.gpr]
    change 0#32 + 0#32 + _ = _
    rw [BitVec.zero_add, BitVec.zero_add, Near.carry_bit, tested]
    change Near.bit (decide ((((s.mem.readW (off base 176) 32 - 1) ||| s.mem.readW (off base 180) 32).toNat) < 1)) = _
    have eq : val32 s.mem base 176 2 = Mod64.pair (s.mem.readW (off base 176) 32) (s.mem.readW (off base 180) 32) := by
      simp only [val32, Nat.mul_zero, Nat.add_zero]
      rfl
    rw [eq]
    apply congrArg (fun b : Bool => BitVec.ofNat 32 b.toNat)
    apply decide_eq_decide.mpr
    rw [← equals_one]
    omega
  · rw [T.mem, F.mem, E.mem, D.mem, C.mem, B.mem, A.mem]

end VG.Proof.RsaKeyGen.X86.Gcd64
