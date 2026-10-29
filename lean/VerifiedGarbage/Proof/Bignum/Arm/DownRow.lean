module

public import VerifiedGarbage.Proof.Bignum.Arm.DownRowState
public import VerifiedGarbage.Impl.Bignum.Arm.DownRow

import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! A nonempty downward-write row computes the same multiply-add without
copying its result down a word afterwards. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/DownRowStep.lean`, which only this module imported.
section

/-! One multiply-add reads the old accumulator one word ahead of its output. -/

section
namespace VG.Proof.Bignum.Arm.DownRow
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest mask16 wp_ldr wp_str)

theorem step_ok (s : State) (a acc b : Addr) (x : BitVec 32)
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (ha : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (hb : State.addr (s.gpr .r12 + BitVec.ofNat 32 0) = b)
    (hacc : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) = acc)
    (haccRead : InRegions (s.rd ++ s.wr) acc 4)
    (hread : InRegions (s.rd ++ s.wr) b 4) (hwrite : InRegions s.wr a 4) :
    WP isa (VG.Impl.Bignum.Arm.DownRow.step) s fun t =>
      (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
        x.toNat * (s.mem.readW b 32).toNat +
          (s.mem.readW acc 32).toNat + (s.gpr .r11).toNat ∧
      t.mem = s.mem.writeW a (t.gpr .r3) ∧ Rest rowClobbers s t := by
  rw [VG.Impl.Bignum.Arm.DownRow.step, WP.seq_iff]
  refine wp_ldr (by decide) hb hread fun s1 u1 => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (rowProduct_ok s1 x (by rw [u1.other .r1 (by decide), h1])
    (by rw [u1.other .r10 (by decide), h10]) (by rw [u1.other .r9 (by decide), h9])) ?_
  rintro s2 ⟨prod, frame2⟩
  have ptr2 : s2.gpr .r0 = s.gpr .r0 :=
    (frame2.regs .r0 (by decide)).trans (u1.other .r0 (by decide))
  rw [WP.seq_iff]
  refine wp_ldr (a := acc) (by decide) (by rw [ptr2]; exact hacc)
    (by rw [frame2.rd, frame2.wr, u1.rd, u1.wr]; exact haccRead) fun s3 u3 => WP.block_nil ?_
  have mem3 : s3.mem = s.mem := u3.mem.trans (frame2.mem.trans u1.mem)
  have acc3 : s3.gpr .r5 = s.mem.readW acc 32 := by rw [u3.gpr, frame2.mem, u1.mem]
  have carry3 : s3.gpr .r11 = s.gpr .r11 :=
    (u3.other .r11 (by decide)).trans ((frame2.regs .r11 (by decide)).trans (u1.other .r11 (by decide)))
  have prod3 : (s3.gpr .r3).toNat + (s3.gpr .r4).toNat * 2 ^ 32 =
      x.toNat * (s.mem.readW b 32).toNat := by
    rw [u3.other .r3 (by decide), u3.other .r4 (by decide), prod, u1.gpr]
  have hb := mac_bound x (s.mem.readW b 32) (s.mem.readW acc 32) (s.gpr .r11)
  rw [WP.seq_iff]
  apply WP.block_append_iff.mpr
  refine WP.mono (addWord_ok s3 .r5 (by rw [prod3, acc3]; omega)) ?_
  rintro s4 ⟨sum4, frame4⟩
  have carry4 : s4.gpr .r11 = s.gpr .r11 := (frame4.regs .r11 (by decide)).trans carry3
  refine WP.mono (addCarry_ok s4 (by rw [sum4, prod3, acc3, carry4]; exact hb)) ?_
  rintro s5 ⟨sum5, frame5⟩
  have ptr5 : s5.gpr .r0 = s.gpr .r0 :=
    (frame5.regs .r0 (by decide)).trans ((frame4.regs .r0 (by decide)).trans
      ((u3.other .r0 (by decide)).trans ptr2))
  refine wp_str (a := a) (by decide) (by rw [ptr5]; exact ha)
    (by rw [frame5.wr, frame4.wr, u3.wr, frame2.wr, u1.wr]; exact hwrite) fun s6 u6 => WP.block_nil ?_
  have out6 : s6.gpr .r3 = s5.gpr .r3 := congrFun u6.gpr .r3
  have carry6 : s6.gpr .r11 = s5.gpr .r11 := congrFun u6.gpr .r11
  refine ⟨?_, ?_, ?_⟩
  · rw [out6, carry6, sum5, sum4, prod3, acc3, carry4]
  · rw [u6.mem, frame5.mem, frame4.mem, mem3, out6]
  · have r2 : Rest rowClobbers s1 s2 := ⟨fun r hr => frame2.regs r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h | h | h | h | h | h <;> simp [h]), frame2.rd, frame2.wr, frame2.sp⟩
    have r4 : Rest rowClobbers s3 s4 := ⟨fun r hr => frame4.regs r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h <;> simp [h]), frame4.rd, frame4.wr, frame4.sp⟩
    have r5 : Rest rowClobbers s4 s5 := ⟨fun r hr => frame5.regs r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h <;> simp [h]), frame5.rd, frame5.wr, frame5.sp⟩
    exact (u1.rest (by decide)).trans (r2.trans ((u3.rest (by decide)).trans (r4.trans (r5.trans
      (u6.rest _)))))


end VG.Proof.Bignum.Arm.DownRow
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/DownRowBody.lean`, which only this module imported.
section

/-! # One iteration preserves the full row invariant -/

section

namespace VG.Proof.Bignum.Arm.DownRow
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest mask16 ofNat_beq_zero)

theorem body_ok {s0 s : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : Ctx s0 base size o b n) (inv : LoopInv s0 x base o b n i s) (hi : i < n)
    (h1 : s0.gpr .r1 = x &&& mask16) (h10 : s0.gpr .r10 = x >>> 16) (h9 : s0.gpr .r9 = mask16) :
    WP isa VG.Impl.Bignum.Arm.DownRow.body s fun t => LoopInv s0 x base o b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hn := ctx.nowrap
  have readB := writable ctx inv.rest.wr (d := b + 4 * i) (by omega_arith)
  have readB' : InRegions (s.rd ++ s.wr) (off (State.addr base) (b + 4 * i)) 4 := by
    rcases readB with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [VG.Impl.Bignum.Arm.DownRow.body, WP.seq_iff]
  have readAcc := writable ctx inv.rest.wr (d := o + 4 + 4 * i) (by omega_arith)
  have readAcc' : InRegions (s.rd ++ s.wr) (off (State.addr base) (o + 4 + 4 * i)) 4 := by
    rcases readAcc with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  have accAddr : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) =
      off (State.addr base) (o + 4 + 4 * i) := by
    rw [inv.outPtr, Offset.add_add]
    have := VG.Arm.addr_add (a := base) (k := o + 4 * i + 4) (by omega_arith)
    simpa only [show o + 4 * i + 4 = o + 4 + 4 * i by omega_arith] using this
  refine WP.mono (step_ok s _ _ _ x (by rw [inv.rest.gpr .r1 (by decide), h1])
    (by rw [inv.rest.gpr .r10 (by decide), h10]) (by rw [inv.rest.gpr .r9 (by decide), h9])
    (addr ctx inv.outPtr (by omega_arith)) (addr ctx inv.inPtr (by omega_arith))
    accAddr readAcc' readB' (writable ctx inv.rest.wr (by omega_arith))) ?_
  rintro s1 ⟨v1, m1, k1⟩
  obtain ⟨outside, value⟩ := value_step ctx inv hi m1 v1
  refine WP.mono (rowAdvance_ok s1) ?_
  rintro s2 ⟨p0, p12, cnt, zero, mem, k2⟩
  have count1 : s1.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (k1.gpr .lr (by decide)).trans inv.count
  have count2 : s2.gpr .lr = BitVec.ofNat 32 (n - (i + 1)) := by
    rw [cnt, count1]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  refine ⟨⟨by omega_arith, ?_, ?_, count2, ?_, ?_, ?_⟩, ?_⟩
  · rw [p0, k1.gpr .r0 (by decide), inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [p12, k1.gpr .r12 (by decide), inv.inPtr]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]
    congr 1
  · rw [mem]; exact outside
  · rw [mem, k2.gpr .r11 (by decide)]; exact value
  · refine inv.rest.trans ((k1.mono ?_).trans (k2.mono ?_))
    all_goals decide
  · rw [zero, count1]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_arith]

end VG.Proof.Bignum.Arm.DownRow
end

end

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
    · simpa only [Nat.mul_zero,Nat.add_zero] using (rest1.gpr .r0 (by decide)).trans hp0
    · simpa only [Nat.mul_zero,Nat.add_zero] using (rest1.gpr .r12 (by decide)).trans hp12
    · simpa only [Nat.sub_zero] using (rest1.gpr .lr (by decide)).trans hcount
    · simp only [val32,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  rw [WP.seq_iff]
  refine WP.mono (loop_ok ctx1 inv1 hn h1 h10 h9) ?_
  intro t ht
  refine wp_dp (op2_lsl (by decide)) fun u hu => WP.block_nil ?_
  have r1 : u.gpr .r1=s.gpr .r1 := by
    rw [hu.gpr,dpVal,ht.rest.gpr .r1 (by decide),ht.rest.gpr .r10 (by decide),h1,h10]
    exact join16 _
  refine ⟨ht.index,?_,?_,?_,?_,?_,?_⟩
  · rw [hu.other .r0 (by decide)]; exact ht.outPtr
  · rw [hu.other .r12 (by decide)]; exact ht.inPtr
  · rw [hu.other .lr (by decide)]; exact ht.count
  · rw [hu.mem,←mem1]; exact ht.outside
  · rw [hu.mem,hu.other .r11 (by decide),←mem1,←rest1.gpr .r11 (by decide)]
    exact ht.value
  · refine ⟨fun r hr => ?_,?_,?_,?_⟩
    · by_cases e : r=.r1
      · subst e; exact r1
      · rw [hu.other r e,ht.rest.gpr r (by revert hr e; cases r <;> decide),
          rest1.gpr r (by revert hr e; cases r <;> decide)]
    · rw [hu.rd,ht.rest.rd,rest1.rd]
    · rw [hu.wr,ht.rest.wr,rest1.wr]
    · rw [hu.sp,ht.rest.sp,rest1.sp]

end VG.Proof.Bignum.Arm.DownRow
