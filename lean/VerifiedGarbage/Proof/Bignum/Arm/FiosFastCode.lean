module

public import VerifiedGarbage.Proof.Bignum.Arm.FiosFastChoice
public import VerifiedGarbage.Proof.Bignum.Arm.FiosState
import VerifiedGarbage.Proof.Bignum.Arm.FiosCode
import VerifiedGarbage.Proof.Bignum.Arm.FiosPipelinedCode
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Fixed and general scans meet the same arithmetic and memory postcondition. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.FiosFast
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem code_ok (s : State) {base : BitVec 32} {size acc b mod n : Nat}
    (ctx : Fios.Ctx s base size acc b mod n) (positive : 4≤n) (even : n%2=0)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 b)
    (modulus : s.gpr .r4=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carryA : s.gpr .r7=0) (carryM : s.gpr .r8=0)
    (inverse : (val32 s.mem (State.addr base) mod n*(s.gpr .r2).toNat+1)%2^32=0)
    (capacity : ∀ q<2^32, val32 s.mem (State.addr base) acc (n+2)+
      (s.gpr .r1).toNat*val32 s.mem (State.addr base) b n+
      q*val32 s.mem (State.addr base) mod n<2^(32*(n+2))) :
    WP isa VG.Impl.Bignum.Arm.FiosFast.code s (Post s base acc b mod n) := by
  have small : n<2^32 := by have := ctx.workspace.nowrap;have := ctx.accFits;omega
  have ws (u : State) (r : Rest [] s u) : Fios.Ctx u base size acc b mod n :=
    ⟨ctx.workspace.congr r.wr,ctx.accFits,ctx.bFits,ctx.mFits,ctx.accB,ctx.accM⟩
  have fixed (u : State) (r : Rest [] s u) (mem : u.mem=s.mem) (special : n=16 ∨ n=32) :
      WP isa (VG.Impl.Bignum.Arm.FiosPipelined.code n) u (Post s base acc b mod n) := by
    refine WP.mono (FiosPipelined.code_ok u (ws u r) positive even
      (by rcases special with rfl|rfl <;> decide)
      (by rcases special with rfl|rfl <;> decide)
      (by rcases special with rfl|rfl <;> decide)
      (by rw [r.gpr .r0 (by simp)];exact ptr)
      (by rw [r.gpr .r12 (by simp)];exact source)
      (by rw [r.gpr .r4 (by simp)];exact modulus)
      (by rw [r.gpr .lr (by simp)];exact count)
      (by rw [r.gpr .r7 (by simp)];exact carryA)
      (by rw [r.gpr .r8 (by simp)];exact carryM)
      (by rw [mem,r.gpr .r2 (by simp)];exact inverse)
      (by intro q hq;rw [mem,r.gpr .r1 (by simp)];exact capacity q hq)) ?_
    exact fun _ h => Post.prefix h mem r
  have general (u : State) (r : Rest [] s u) (mem : u.mem=s.mem) :
      WP isa VG.Impl.Bignum.Arm.Fios.code u (Post s base acc b mod n) := by
    refine WP.mono (Fios.code_ok u (ws u r) positive even
      (by rw [r.gpr .r0 (by simp)];exact ptr)
      (by rw [r.gpr .r12 (by simp)];exact source)
      (by rw [r.gpr .r4 (by simp)];exact modulus)
      (by rw [r.gpr .lr (by simp)];exact count)
      (by rw [r.gpr .r7 (by simp)];exact carryA)
      (by rw [r.gpr .r8 (by simp)];exact carryM)
      (by rw [mem,r.gpr .r2 (by simp)];exact inverse)
      (by intro q hq;rw [mem,r.gpr .r1 (by simp)];exact capacity q hq)) ?_
    exact fun _ h => Post.prefix h mem r
  rw [VG.Impl.Bignum.Arm.FiosFast.code,WP.seq_iff]
  refine WP.mono (choose_ok s n 16 small (by decide) (by decide) count) ?_
  rintro u ⟨z1,m1,r1⟩
  refine WP.ite u.z rfl ?_ ?_
  · intro selected
    have eq : n=16 := of_decide_eq_true (z1.symm.trans selected)
    subst n
    exact fixed u r1 m1 (Or.inl rfl)
  · intro _
    rw [WP.seq_iff]
    refine WP.mono (choose_ok u n 32 small (by decide) (by decide)
      (by rw [r1.gpr .lr (by simp)];exact count)) ?_
    rintro v ⟨z2,m2,r2⟩
    refine WP.ite v.z rfl ?_ ?_
    · intro selected
      have eq : n=32 := of_decide_eq_true (z2.symm.trans selected)
      subst n
      exact fixed v (r1.trans r2) (m2.trans m1) (Or.inr rfl)
    · intro _
      exact general v (r1.trans r2) (m2.trans m1)

end VG.Proof.Bignum.Arm.FiosFast
