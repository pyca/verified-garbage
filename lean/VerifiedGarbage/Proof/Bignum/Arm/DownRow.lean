module

public import VerifiedGarbage.Proof.Bignum.Arm.DownRowState
public import VerifiedGarbage.Impl.Bignum.Arm.DownRow
import VerifiedGarbage.Proof.Bignum.Arm.DownRowBody
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.Block

/-! A nonempty downward-write row computes the same multiply-add without
copying its result down a word afterwards. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.DownRow
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest mask16 wp_dp op2_lsl dpVal)

theorem loop_ok {s0 s : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : Ctx s0 base size o b n) (inv : LoopInv s0 x base o b n i s) (hi : i<n)
    (h1 : s0.gpr .r1=x&&&mask16) (h10 : s0.gpr .r10=x>>>16) (h9 : s0.gpr .r9=mask16) :
    WP isa VG.Impl.Bignum.Arm.DownRow.loop s (LoopInv s0 x base o b n n) := by
  let I := fun k t => ∃ j, j+k=n ∧ 0<k ∧ LoopInv s0 x base o b n j t
  unfold VG.Impl.Bignum.Arm.DownRow.loop
  refine WP.loop (M:=isa) I ?_ (n-i) s ⟨i,by omega,by omega,inv⟩
  intro k t h
  obtain ⟨j,hjk,hk,hj⟩ := h
  refine WP.mono (body_ok ctx hj (by omega) h1 h10 h9) ?_
  rintro u ⟨hu,hz⟩
  by_cases last : j+1=n
  · left
    refine ⟨?_,last ▸ hu⟩
    change some (!u.z)=some false
    simp only [hz,last,decide_true,Bool.not_true]
  · right
    refine ⟨?_,k-1,by omega,j+1,by omega,by omega,hu⟩
    change some (!u.z)=some true
    simp only [hz,last,decide_false,Bool.not_false]

theorem code_ok (s : State) {base : BitVec 32} {size o b n : Nat}
    (ctx : Ctx s base size o b n) (hn : 0<n)
    (hp0 : s.gpr .r0=base+BitVec.ofNat 32 o)
    (hp12 : s.gpr .r12=base+BitVec.ofNat 32 b)
    (hcount : s.gpr .lr=BitVec.ofNat 32 n) :
    WP isa VG.Impl.Bignum.Arm.DownRow.code s (Inv s base o b n n) := by
  let x := s.gpr .r1
  rw [VG.Impl.Bignum.Arm.DownRow.code,WP.seq_iff]
  refine WP.mono (rowSplit_ok s) ?_
  rintro s1 ⟨h1,h10,h9,mem1,rest1⟩
  have ctx1 : Ctx s1 base size o b n := { ctx with
    writable := by rw [rest1.wr]; exact ctx.writable }
  have inv1 : LoopInv s1 x base o b n 0 s1 := by
    refine ⟨by omega,?_,?_,?_,Outside.refl _ _ _ _,?_,Rest.refl _ _⟩
    · simpa only [Nat.mul_zero,Nat.add_zero] using (rest1.gpr .r0 (by simp)).trans hp0
    · simpa only [Nat.mul_zero,Nat.add_zero] using (rest1.gpr .r12 (by simp)).trans hp12
    · simpa only [Nat.sub_zero] using (rest1.gpr .lr (by simp)).trans hcount
    · simp only [val32,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  rw [WP.seq_iff]
  refine WP.mono (loop_ok ctx1 inv1 hn h1 h10 h9) ?_
  intro t ht
  refine wp_dp (op2_lsl (by decide)) fun u hu => WP.block_nil ?_
  have r1 : u.gpr .r1=s.gpr .r1 := by
    rw [hu.gpr,dpVal,ht.rest.gpr .r1 (by simp),ht.rest.gpr .r10 (by simp),h1,h10]
    exact join16 _
  refine ⟨ht.index,?_,?_,?_,?_,?_,?_⟩
  · rw [hu.other .r0 (by decide)]; exact ht.outPtr
  · rw [hu.other .r12 (by decide)]; exact ht.inPtr
  · rw [hu.other .lr (by decide)]; exact ht.count
  · rw [hu.mem,←mem1]; exact ht.outside
  · rw [hu.mem,hu.other .r11 (by decide),←mem1,←rest1.gpr .r11 (by simp)]
    exact ht.value
  · refine ⟨fun r hr => ?_,?_,?_,?_⟩
    · by_cases e : r=.r1
      · subst e; exact r1
      · rw [hu.other r e,ht.rest.gpr r (by cases r <;> simp_all [loopClobbers]),
          rest1.gpr r (by cases r <;> simp_all [loopClobbers])]
    · rw [hu.rd,ht.rest.rd,rest1.rd]
    · rw [hu.wr,ht.rest.wr,rest1.wr]
    · rw [hu.sp,ht.rest.sp,rest1.sp]

end VG.Proof.Bignum.Arm.DownRow
