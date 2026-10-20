module

public import VerifiedGarbage.Impl.Bignum.Arm.TwoPower
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Bignum.Arm.TwoPower
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Load the complete native decomposition count and call RSA's shared
fixed-step construction of the u64 metadata word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem exponentPowerWord_ok {s : State} {count : Nat} (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 60#32)) 32 = BitVec.ofNat 32 count) :
    WP isa (.block (([.ldrSp .r1 60] : List Instr) ++ VG.Impl.Bignum.Arm.TwoPower.code)) s fun t =>
      (t.gpr .r3 ++ t.gpr .r2 : BitVec 64) = BitVec.twoPow 64 (count % 64) ∧
      t.mem = s.mem ∧ Rest [.r1, .r2, .r3, .r4] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 60#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  change WP isa (.block (.ldrSp .r1 60 :: VG.Impl.Bignum.Arm.TwoPower.code)) s _
  refine wp_loadStack (by decide) rfl read fun u load => ?_
  refine WP.mono (VG.Proof.Bignum.Arm.TwoPower.code_word_ok u) ?_
  rintro t ⟨word, mem, rest⟩
  rw [load.gpr, saved, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd count (by decide : 64 ∣ 2 ^ 32)] at word
  exact ⟨word, mem.trans load.mem, (load.rest (by simp)).trans rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
