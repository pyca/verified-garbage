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
  have fixed (u : State) (r : Rest [] s u) (mem : u.mem=s.mem) (bound : n≤1000)
      (h4 : encodable (BitVec.ofNat 32 (4*(n-2)))=true) (h1 : encodable (BitVec.ofNat 32 (n-2))=true) :
      WP isa (VG.Impl.Bignum.Arm.FiosPipelined.code n) u (Post s base acc b mod n) := by
    refine WP.mono (FiosPipelined.code_ok u (ws u r) positive even bound h4 h1
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
  -- Each width with a fixed scan: its comparison, offsets and counts encodable.
  have select (ks : List Nat) (good : ∀ k ∈ ks, k≤1000 ∧ encodable (BitVec.ofNat 32 k)=true ∧
      encodable (BitVec.ofNat 32 (4*(k-2)))=true ∧ encodable (BitVec.ofNat 32 (k-2))=true) :
      ∀ u, Rest [] s u → u.mem=s.mem →
        WP isa (VG.Impl.Bignum.Arm.FiosFast.select ks) u (Post s base acc b mod n) := by
    induction ks with
    | nil => exact general
    | cons k ks ih =>
      intro u r m
      obtain ⟨bk,ek,h4k,h1k⟩ := good k List.mem_cons_self
      rw [VG.Impl.Bignum.Arm.FiosFast.select,WP.seq_iff]
      refine WP.mono (choose_ok u n k small (by omega) ek
        (by rw [r.gpr .lr (by simp)];exact count)) ?_
      rintro v ⟨z,mv,rv⟩
      refine WP.ite v.z rfl ?_ ?_
      · intro selected
        have eq : n=k := of_decide_eq_true (z.symm.trans selected)
        rw [← eq] at bk h4k h1k ⊢
        exact fixed v (r.trans rv) (mv.trans m) bk h4k h1k
      · intro _
        exact ih (fun j hj => good j (List.mem_cons_of_mem _ hj)) v (r.trans rv) (mv.trans m)
  exact select _ (by decide) s (Rest.refl [] s) rfl

end VG.Proof.Bignum.Arm.FiosFast
