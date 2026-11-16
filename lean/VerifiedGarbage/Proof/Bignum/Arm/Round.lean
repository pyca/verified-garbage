module
public import VerifiedGarbage.Impl.Bignum.Arm.Round
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.ProductStage
public import VerifiedGarbage.Impl.Bignum.Arm.FusedReduction
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Bignum.Arm.WideMul
public import VerifiedGarbage.Impl.Bignum.Arm.DownRow
import VerifiedGarbage.Proof.Bignum.Arm.Row
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Bignum.Arm.RowAdvance
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.RowCarryMemory
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Bignum.Arm.ReductionArgs
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.MontMath
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinish
import VerifiedGarbage.Proof.Bignum.Arm.RoundFinishMemory

/-! ### `Bignum.Arm.FusedReductionStage`, which only this module used -/

section

/-! ### `Bignum.Arm.FusedReductionBody`, which only this module used -/

section

/-! ### `Bignum.Arm.DownRow`, which only this module used -/

section

/-! ### `Bignum.Arm.DownRowState`, which only this module used -/

section

/-! # The invariant of a packed-word multiply-add row -/

@[expose] public section

namespace VG.Proof.Bignum.Arm.DownRow
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

abbrev loopClobbers : List Reg := [.r0, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]

/-- The arrays are disjoint subranges of a writable workspace within the
32-bit address space. No access uses the pointers past the arrays. -/
structure Ctx (s : State) (base : BitVec 32) (size o b n : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  outFits : o + 4 * (n + 1) ≤ size
  inFits : b + 4 * n ≤ size
  separate : o + 4 * (n + 1) ≤ b ∨ b + 4 * n ≤ o
  writable : (⟨State.addr base, size⟩ : Region) ∈ s.wr

/-- After `i` steps, the stored prefix plus the outstanding carry is the
original prefix plus the scalar product and initial carry. -/
structure Inv (s0 : State) (base : BitVec 32) (o b n i : Nat) (s : State) : Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  inPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
    val32 s0.mem (State.addr base) (o + 4) i + (s0.gpr .r1).toNat * val32 s0.mem (State.addr base) b i +
      (s0.gpr .r11).toNat
  rest : Rest loopClobbers s0 s

/-- What one step of the row's loop may change: the scalar's halves in `r1`
and `r10`, and the mask in `r9`, stay for the whole loop. -/
abbrev stepClobbers : List Reg := [.r0, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r11, .r12, .lr]

/-- `Inv` inside the loop, from the state `s0` after the scalar `x` is
split: the same pointers, counter and value, `x` for the scalar. -/
structure LoopInv (s0 : State) (x : BitVec 32) (base : BitVec 32) (o b n i : Nat) (s : State) :
    Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  inPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
    val32 s0.mem (State.addr base) (o + 4) i + x.toNat * val32 s0.mem (State.addr base) b i +
      (s0.gpr .r11).toNat
  rest : Rest stepClobbers s0 s

/-- Form the effective address of a word anywhere in the workspace. -/
theorem addr {s0 s : State} {base : BitVec 32} {size o b n d : Nat}
    (ctx : Ctx s0 base size o b n) {r : Reg}
    (hr : s.gpr r = base + BitVec.ofNat 32 d) (hd : d < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 0) = off (State.addr base) d := by
  rw [hr, Offset.add_add, Nat.add_zero]
  exact VG.Arm.addr_add (by have := ctx.nowrap; omega_using [hd, this])

/-- Any word in the workspace remains writable throughout the row. -/
theorem writable {s0 s : State} {base : BitVec 32} {size o b n d : Nat}
    (ctx : Ctx s0 base size o b n) (hr : s.wr = s0.wr) (hd : d + 4 ≤ size) :
    InRegions s.wr (off (State.addr base) d) 4 := by
  rw [hr]
  refine ⟨_, ctx.writable, Offset.contains_base _ hd ?_⟩
  have := ctx.nowrap
  omega_using [hd, this]

/-- Extend the arithmetic invariant with the next stored word, from the
invariant's memory facts alone. -/
theorem value_step_of {s0 s t : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : Ctx s0 base size o b n)
    (houtside : Outside (State.addr base) o (4 * i) s0.mem s.mem)
    (hvalue : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
      val32 s0.mem (State.addr base) (o + 4) i + x.toNat * val32 s0.mem (State.addr base) b i +
        (s0.gpr .r11).toNat) (hi : i < n)
    (hm : t.mem = s.mem.writeW (off (State.addr base) (o + 4 * i)) (t.gpr .r3))
    (hv : (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
      x.toNat * w32 s.mem (State.addr base) (b + 4 * i) +
        w32 s.mem (State.addr base) (o + 4 + 4 * i) + (s.gpr .r11).toNat) :
    Outside (State.addr base) o (4 * (i + 1)) s0.mem t.mem ∧
      val32 t.mem (State.addr base) o (i + 1) + 2 ^ (32 * (i + 1)) * (t.gpr .r11).toNat =
        val32 s0.mem (State.addr base) (o + 4) (i + 1) +
          x.toNat * val32 s0.mem (State.addr base) b (i + 1) + (s0.gpr .r11).toNat := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hs := ctx.separate
  obtain own := houtside.w32 (d := o + 4 + 4 * i) (by omega_using []) (by omega_using [hi, hn, ho])
  obtain src := houtside.w32 (d := b + 4 * i) (by omega_using [hi, hs]) (by omega_using [hi, hn, hb])
  rw [own, src] at hv
  obtain wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r3) (by omega_using [hi, hn, ho])
  rw [← hm] at wr
  obtain low := wr.val32 (d := o) (k := i) (by omega_using []) (by omega_using [hi, hn, ho])
  obtain top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r3).toNat := by
    rw [hm, w32_write_self]
  refine ⟨(houtside.mono (Nat.le_refl _) (by omega_using [])).trans (wr.mono (by omega_using []) (by omega_using [])), ?_⟩
  rw [val32_succ, val32_succ, val32_succ, low, top, pow32_succ]
  have prior := hvalue
  generalize 2 ^ (32 * i) = P at *
  grind

/-- Extend the arithmetic invariant with the next stored word. -/
theorem value_step {s0 s t : State} {x base : BitVec 32} {size o b n i : Nat}
    (ctx : Ctx s0 base size o b n) (inv : LoopInv s0 x base o b n i s) (hi : i < n)
    (hm : t.mem = s.mem.writeW (off (State.addr base) (o + 4 * i)) (t.gpr .r3))
    (hv : (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
      x.toNat * w32 s.mem (State.addr base) (b + 4 * i) +
        w32 s.mem (State.addr base) (o + 4 + 4 * i) + (s.gpr .r11).toNat) :
    Outside (State.addr base) o (4 * (i + 1)) s0.mem t.mem ∧
      val32 t.mem (State.addr base) o (i + 1) + 2 ^ (32 * (i + 1)) * (t.gpr .r11).toNat =
        val32 s0.mem (State.addr base) (o + 4) (i + 1) +
          x.toNat * val32 s0.mem (State.addr base) b (i + 1) + (s0.gpr .r11).toNat :=
  value_step_of ctx inv.outside inv.value hi hm hv

end VG.Proof.Bignum.Arm.DownRow

end

end

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
  obtain ptr2 : s2.gpr .r0 = s.gpr .r0 :=
    (frame2.regs .r0 (by decide)).trans (u1.other .r0 (by decide))
  rw [WP.seq_iff]
  refine wp_ldr (a := acc) (by decide) (by rw [ptr2]; exact hacc)
    (by rw [frame2.rd, frame2.wr, u1.rd, u1.wr]; exact haccRead) fun s3 u3 => WP.block_nil ?_
  obtain mem3 : s3.mem = s.mem := u3.mem.trans (frame2.mem.trans u1.mem)
  obtain acc3 : s3.gpr .r5 = s.mem.readW acc 32 := by rw [u3.gpr, frame2.mem, u1.mem]
  obtain carry3 : s3.gpr .r11 = s.gpr .r11 :=
    (u3.other .r11 (by decide)).trans ((frame2.regs .r11 (by decide)).trans (u1.other .r11 (by decide)))
  obtain prod3 : (s3.gpr .r3).toNat + (s3.gpr .r4).toNat * 2 ^ 32 =
      x.toNat * (s.mem.readW b 32).toNat := by
    rw [u3.other .r3 (by decide), u3.other .r4 (by decide), prod, u1.gpr]
  obtain hb := mac_bound x (s.mem.readW b 32) (s.mem.readW acc 32) (s.gpr .r11)
  rw [WP.seq_iff]
  apply WP.block_append_iff.mpr
  refine WP.mono (addWord_ok s3 .r5 (by rw [prod3, acc3]; omega)) ?_
  rintro s4 ⟨sum4, frame4⟩
  obtain carry4 : s4.gpr .r11 = s.gpr .r11 := (frame4.regs .r11 (by decide)).trans carry3
  refine WP.mono (addCarry_ok s4 (by rw [sum4, prod3, acc3, carry4]; exact hb)) ?_
  rintro s5 ⟨sum5, frame5⟩
  obtain ptr5 : s5.gpr .r0 = s.gpr .r0 :=
    (frame5.regs .r0 (by decide)).trans ((frame4.regs .r0 (by decide)).trans
      ((u3.other .r0 (by decide)).trans ptr2))
  refine wp_str (a := a) (by decide) (by rw [ptr5]; exact ha)
    (by rw [frame5.wr, frame4.wr, u3.wr, frame2.wr, u1.wr]; exact hwrite) fun s6 u6 => WP.block_nil ?_
  obtain out6 : s6.gpr .r3 = s5.gpr .r3 := congrFun u6.gpr .r3
  obtain carry6 : s6.gpr .r11 = s5.gpr .r11 := congrFun u6.gpr .r11
  refine ⟨?_, ?_, ?_⟩
  · rw [out6, carry6, sum5, sum4, prod3, acc3, carry4]
  · rw [u6.mem, frame5.mem, frame4.mem, mem3, out6]
  · have r2 : Rest rowClobbers s1 s2 := ⟨fun r hr => frame2.regs r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h | h | h | h | h | h <;> simp [h]), frame2.rd, frame2.wr, frame2.sp⟩
    obtain r4 : Rest rowClobbers s3 s4 := ⟨fun r hr => frame4.regs r (by
        intro h; apply hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h <;> simp [h]), frame4.rd, frame4.wr, frame4.sp⟩
    obtain r5 : Rest rowClobbers s4 s5 := ⟨fun r hr => frame5.regs r (by
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
  obtain readB := writable ctx inv.rest.wr (d := b + 4 * i) (by omega_arith)
  obtain readB' : InRegions (s.rd ++ s.wr) (off (State.addr base) (b + 4 * i)) 4 := by
    rcases readB with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  rw [VG.Impl.Bignum.Arm.DownRow.body, WP.seq_iff]
  obtain readAcc := writable ctx inv.rest.wr (d := o + 4 + 4 * i) (by omega_arith)
  obtain readAcc' : InRegions (s.rd ++ s.wr) (off (State.addr base) (o + 4 + 4 * i)) 4 := by
    rcases readAcc with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  obtain accAddr : State.addr (s.gpr .r0 + BitVec.ofNat 32 4) =
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
  obtain count1 : s1.gpr .lr = BitVec.ofNat 32 (n - i) :=
    (k1.gpr .lr (by decide)).trans inv.count
  obtain count2 : s2.gpr .lr = BitVec.ofNat 32 (n - (i + 1)) := by
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
  refine WP.loop (M:=isa) I ?_ (n-i) s ⟨i,by omega_using [hi],by omega_using [hi],inv⟩
  intro k t h
  obtain ⟨j,hjk,hk,hj⟩ := h
  refine WP.mono (body_ok ctx hj (by omega_using [hjk, hk]) h1 h10 h9) ?_
  rintro u ⟨hu,hz⟩
  by_cases last : j+1=n
  · left
    refine ⟨?_,last ▸ hu⟩
    change some (!u.z)=some false
    simp only [hz,last,decide_true,Bool.not_true]
  · right
    refine ⟨?_,k-1,by omega_using [hk],j+1,by omega_using [hjk, hk],by omega_using [hjk, hk, last],hu⟩
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
  obtain ctx1 : Ctx s1 base size o b n := { ctx with
    writable := by rw [rest1.wr]; exact ctx.writable }
  obtain inv1 : LoopInv s1 x base o b n 0 s1 := by
    refine ⟨by omega_using [],?_,?_,?_,Outside.refl _ _ _ _,?_,Rest.refl _ _⟩
    · simpa only [Nat.mul_zero,Nat.add_zero] using (rest1.gpr .r0 (by decide)).trans hp0
    · simpa only [Nat.mul_zero,Nat.add_zero] using (rest1.gpr .r12 (by decide)).trans hp12
    · simpa only [Nat.sub_zero] using (rest1.gpr .lr (by decide)).trans hcount
    · simp only [val32,Nat.mul_zero,Nat.pow_zero,Nat.one_mul,Nat.zero_add]
  rw [WP.seq_iff]
  refine WP.mono (loop_ok ctx1 inv1 hn h1 h10 h9) ?_
  intro t ht
  refine wp_dp (op2_lsl (by decide)) fun u hu => WP.block_nil ?_
  obtain r1 : u.gpr .r1=s.gpr .r1 := by
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

end

end

/-! The fused cancellation row computes the quotient without moving its array. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FusedReductionFirst.lean`, which only this module imported.
section

/-! The low Montgomery word cancels without being stored or shifted. -/

section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov wp_dp wp_subs op2_reg op2_imm dpVal)

theorem first_ok (s : State) {base : BitVec 32} {size acc mod n : Nat}
    (ws : Workspace s base size) (accFit : acc+4≤size) (modFit : mod+4≤size)
    (positive : 0<n) (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carry : s.gpr .r11=0)
    (cancel : ((s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
      w32 s.mem (State.addr base) acc)%2^32=0) :
    WP isa VG.Impl.Bignum.Arm.FusedReduction.first s fun t =>
      t.gpr .r0=base+BitVec.ofNat 32 acc ∧
      t.gpr .r12=base+BitVec.ofNat 32 (mod+4) ∧
      t.gpr .lr=BitVec.ofNat 32 (n-1) ∧ t.gpr .r1=s.gpr .r1 ∧
      2^32*(t.gpr .r11).toNat=(s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
        w32 s.mem (State.addr base) acc ∧
      t.mem=s.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.FusedReduction.first, WP.seq_iff]
  obtain args : WP isa (.block VG.Impl.Bignum.Arm.FusedReduction.firstArgs) s fun u =>
      u.gpr .r2=s.mem.readW (off (State.addr base) mod) 32 ∧
      u.gpr .r10=s.mem.readW (off (State.addr base) acc) 32 ∧
      u.mem=s.mem ∧ Rest [.r2,.r10] s u := by
    unfold VG.Impl.Bignum.Arm.FusedReduction.firstArgs
    refine wp_ldr (a:=off (State.addr base) mod) (by decide)
      (by simpa only [Nat.add_zero] using ws.ea source (imm:=0) (by omega)) (ws.read modFit) fun u h => ?_
    refine wp_ldr (a:=off (State.addr base) acc) (by decide)
      (by rw [h.other .r0 (by decide)]; simpa only [Nat.add_zero] using ws.ea ptr (imm:=0) (by omega))
      (by rw [h.rd,h.wr]; exact ws.read accFit) fun v k => WP.block_nil ?_
    exact ⟨(k.other .r2 (by decide)).trans h.gpr,
      by rw [k.gpr,h.mem],k.mem.trans h.mem,(h.rest (by decide)).trans (k.rest (by decide))⟩
  refine WP.mono args ?_
  rintro u ⟨input,accumulator,memU,restU⟩
  rw [WP.seq_iff]
  refine WP.mono (mac_ok u) ?_
  rintro v ⟨value,frame⟩
  obtain r0 : v.gpr .r0=base+BitVec.ofNat 32 acc :=
    (frame.regs .r0 (by decide)).trans ((restU.gpr .r0 (by decide)).trans ptr)
  obtain r1 : v.gpr .r1=s.gpr .r1 :=
    (frame.regs .r1 (by decide)).trans (restU.gpr .r1 (by decide))
  obtain r12 : v.gpr .r12=base+BitVec.ofNat 32 mod :=
    (frame.regs .r12 (by decide)).trans ((restU.gpr .r12 (by decide)).trans source)
  obtain lr : v.gpr .lr=BitVec.ofNat 32 n :=
    (frame.regs .lr (by decide)).trans ((restU.gpr .lr (by decide)).trans count)
  rw [restU.gpr .r1 (by decide),input,accumulator,restU.gpr .r11 (by decide),carry] at value
  simp only [show (0:BitVec 32).toNat=0 from rfl,Nat.add_zero] at value
  obtain high : 2^32*(v.gpr .r4).toNat=(s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
      w32 s.mem (State.addr base) acc := by
    change (v.gpr .r3).toNat+(v.gpr .r4).toNat*2^32=_ at value
    obtain low := (v.gpr .r3).isLt
    dsimp only [w32] at cancel ⊢
    omega
  obtain kept : Rest roundClobbers s v := (restU.mono (by decide)).trans
    ((show Rest clobbers u v from ⟨frame.regs,frame.rd,frame.wr,frame.sp⟩).mono
      (by decide))
  unfold VG.Impl.Bignum.Arm.FusedReduction.firstNext
  refine wp_mov (op2_reg _ _) fun a ha => ?_
  refine wp_dp (op2_imm (by decide)) fun b hb => ?_
  refine wp_subs (op2_imm (by decide)) fun t ht _zero => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.other .r0 (by decide),hb.other .r0 (by decide),ha.other .r0 (by decide)]; exact r0
  · rw [ht.other .r12 (by decide),hb.gpr,dpVal,ha.other .r12 (by decide),r12]
    exact Offset.add_add _ _ _
  · rw [ht.gpr,hb.other .lr (by decide),ha.other .lr (by decide),lr]
    exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) positive
  · rw [ht.other .r1 (by decide),hb.other .r1 (by decide),ha.other .r1 (by decide)]; exact r1
  · rw [ht.other .r11 (by decide),hb.other .r11 (by decide),ha.gpr]; exact high
  · rw [ht.mem,hb.mem,ha.mem,frame.mem,memU]
  · exact kept.trans ((ha.rest (by decide)).trans
      ((hb.rest (by decide)).trans (ht.rest (by decide))))

end VG.Proof.Bignum.Arm.FusedReduction
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FusedReductionTop.lean`, which only this module imported.
section

/-! Add the last row carry and store the two high quotient words directly. -/

section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp op2_imm dpVal)

theorem top_ok (s : State) {base : BitVec 32} {size d : Nat}
    (ws : Workspace s base size) (fit : d+12≤size)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 d)
    (bound : w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8)+
      (s.gpr .r11).toNat<2^64) :
    WP isa VG.Impl.Bignum.Arm.FusedReduction.top s fun t =>
      (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=
        w32 s.mem (State.addr base) (d+4)+2^32*w32 s.mem (State.addr base) (d+8)+
          (s.gpr .r11).toNat ∧
      t.mem=(s.mem.writeW (off (State.addr base) d) (t.gpr .r3)).writeW
        (off (State.addr base) (d+4)) (t.gpr .r4) ∧
      t.gpr .r0=base+BitVec.ofNat 32 (d+8) ∧ Rest [.r0,.r3,.r4] s t := by
  rw [VG.Impl.Bignum.Arm.FusedReduction.top,WP.seq_iff]
  obtain loads : WP isa (.block [.ldr .r3 .r0 4,.ldr .r4 .r0 8]) s fun u =>
      u.gpr .r3=s.mem.readW (off (State.addr base) (d+4)) 32 ∧
      u.gpr .r4=s.mem.readW (off (State.addr base) (d+8)) 32 ∧
      u.mem=s.mem ∧ Rest [.r3,.r4] s u := by
    refine wp_ldr (a:=off (State.addr base) (d+4)) (by decide) (ws.ea ptr (by omega))
      (ws.read (by omega)) fun u h => ?_
    refine wp_ldr (a:=off (State.addr base) (d+8)) (by decide)
      (by rw [h.other .r0 (by decide)];exact ws.ea ptr (by omega))
      (by rw [h.rd,h.wr];exact ws.read (by omega)) fun v k => WP.block_nil ?_
    exact ⟨(k.other .r3 (by decide)).trans h.gpr,by rw [k.gpr,h.mem],
      k.mem.trans h.mem,(h.rest (by decide)).trans (k.rest (by decide))⟩
  refine WP.mono loads ?_
  rintro u ⟨low,high,memU,restU⟩
  obtain carry : u.gpr .r11=s.gpr .r11 := restU.gpr .r11 (by decide)
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok u .r11 (by rw [low,high,carry];dsimp only [w32] at bound;omega)) ?_
  rintro v ⟨value,frame⟩
  obtain pv : v.gpr .r0=base+BitVec.ofNat 32 d :=
    (frame.regs .r0 (by decide)).trans ((restU.gpr .r0 (by decide)).trans ptr)
  obtain mv : v.mem=s.mem := frame.mem.trans memU
  obtain wv : v.wr=s.wr := frame.wr.trans restU.wr
  obtain wsv := ws.congr wv
  refine wp_str (a:=off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using wsv.ea pv (imm:=0) (by omega))
    (by rw [wv];exact ws.write (by omega)) fun a ha => ?_
  refine wp_str (a:=off (State.addr base) (d+4)) (by decide)
    (by rw [ha.gpr];exact wsv.ea pv (by omega))
    (by rw [ha.wr,wv];exact ws.write (by omega)) fun b hb => ?_
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨?_,?_,?_,?_⟩
  · rw [ht.other .r3 (by decide),ht.other .r4 (by decide),hb.gpr,ha.gpr]
    rw [low,high,carry] at value
    simpa only [w32,Nat.mul_comm] using value
  · rw [ht.mem,hb.mem,ha.mem,mv,ht.other .r3 (by decide),ht.other .r4 (by decide),hb.gpr,ha.gpr]
  · rw [ht.gpr,dpVal,hb.gpr,ha.gpr,pv]
    exact Offset.add_add _ _ _
  · have rv : Rest [.r3,.r4] s v := restU.trans ⟨frame.regs,frame.rd,frame.wr,frame.sp⟩
    exact (rv.mono (by decide)).trans ((ha.rest _).trans
      ((hb.rest _).trans (ht.rest (by decide))))

end VG.Proof.Bignum.Arm.FusedReduction
end

end

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/FusedReductionMath.lean`, which only this module imported.
section

/-! The cancellation carry and the downward row together divide exactly. -/

section
namespace VG.Proof.Bignum.Arm.FusedReduction

theorem quotient_value {B P T M t0 tl th m0 ml q c0 rl cr rh : Nat}
    (acc : T=t0+B*(tl+P*th)) (modulus : M=m0+B*ml)
    (first : B*c0=q*m0+t0) (row : rl+P*cr=tl+q*ml+c0)
    (top : rh=th+cr) : B*(rl+P*rh)=T+q*M := by
  obtain step := congrArg (fun x => B*x) row
  grind

end VG.Proof.Bignum.Arm.FusedReduction
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem code_ok (s : State) {base : BitVec 32} {size acc mod n : Nat}
    (ws : Workspace s base size) (positive : 1<n) (accFit : acc+4*(n+2)≤size)
    (modFit : mod+4*n≤size)
    (separate : acc+4*(n+2)≤mod ∨ mod+4*n≤acc)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 acc)
    (source : s.gpr .r12=base+BitVec.ofNat 32 mod)
    (count : s.gpr .lr=BitVec.ofNat 32 n) (carry : s.gpr .r11=0)
    (cancel : ((s.gpr .r1).toNat*w32 s.mem (State.addr base) mod+
      w32 s.mem (State.addr base) acc)%2^32=0)
    (capacity : val32 s.mem (State.addr base) acc (n+2)+
      (s.gpr .r1).toNat*val32 s.mem (State.addr base) mod n<2^(32*(n+2))) :
    WP isa VG.Impl.Bignum.Arm.FusedReduction.code s fun t =>
      2^32*val32 t.mem (State.addr base) acc (n+1)=
        val32 s.mem (State.addr base) acc (n+2)+
          (s.gpr .r1).toNat*val32 s.mem (State.addr base) mod n ∧
      t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
      Outside (State.addr base) acc (4*(n+1)) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Bignum.Arm.FusedReduction.code,WP.seq_iff]
  refine WP.mono (first_ok s ws (by omega_arith) (by omega_arith) (by omega_arith) ptr source count carry cancel) ?_
  rintro u ⟨ptrU,sourceU,countU,scalarU,first,memU,restU⟩
  obtain ctx : DownRow.Ctx u base size acc (mod+4) (n-1) :=
    ⟨ws.nowrap,by omega_arith,by omega_arith,by rcases separate with h|h <;> omega_arith,
      by rw [restU.wr];exact ws.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (DownRow.code_ok u ctx (by omega_arith) ptrU sourceU countU) ?_
  intro v row
  let P := 2^(32*(n-1))
  let H := val32 s.mem (State.addr base) (acc+4*n) 2
  let L := val32 s.mem (State.addr base) (acc+4) (n-1)
  let Q := (s.gpr .r1).toNat
  obtain rowValue : val32 v.mem (State.addr base) acc (n-1)+P*(v.gpr .r11).toNat=
      L+Q*val32 s.mem (State.addr base) (mod+4) (n-1)+(u.gpr .r11).toNat := by
    simpa only [memU,scalarU] using row.value
  obtain accSplit : val32 s.mem (State.addr base) acc (n+2)=
      w32 s.mem (State.addr base) acc+2^32*(L+P*H) := by
    rw [show n+2=(n+1)+1 by omega_arith,val32]
    obtain split := val32_append s.mem (State.addr base) (acc+4) (n-1) 2
    simpa only [show n-1+2=n+1 by omega_arith,show acc+4+4*(n-1)=acc+4*n by omega_arith] using
      congrArg (fun x => w32 s.mem (State.addr base) acc+2^32*x) split
  obtain modSplit : val32 s.mem (State.addr base) mod n=
      w32 s.mem (State.addr base) mod+2^32*val32 s.mem (State.addr base) (mod+4) (n-1) := by
    calc
      _ = val32 s.mem (State.addr base) mod ((n-1)+1) := by congr 1;omega_arith
      _ = _ := rfl
  obtain total : 2^32*(val32 v.mem (State.addr base) acc (n-1)+P*(H+(v.gpr .r11).toNat))=
      val32 s.mem (State.addr base) acc (n+2)+Q*val32 s.mem (State.addr base) mod n :=
    quotient_value accSplit modSplit first rowValue rfl
  obtain power : 2^32*(P*2^64)=2^(32*(n+2)) := by
    dsimp only [P]
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    omega_arith
  obtain topBound : H+(v.gpr .r11).toNat<2^64 := by
    have cap := capacity
    change _+Q*_< _ at cap
    rw [←total,←power] at cap
    obtain small : 2^32*(P*(H+(v.gpr .r11).toNat))<2^32*(P*2^64) :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) cap
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_left small)
  obtain outside : Outside (State.addr base) acc (4*(n-1)) s.mem v.mem := by
    simpa only [memU] using row.outside
  have oldTop (j : Nat) (hj : j<2) :
      w32 v.mem (State.addr base) (acc+4*n+4*j)=w32 s.mem (State.addr base) (acc+4*n+4*j) :=
    outside.w32 (by omega_arith) (by have := ws.nowrap;omega_arith)
  obtain fitTop : acc+4*(n-1)+12≤size := by omega_arith
  obtain native : Rest roundClobbers u v := (row.rest.mono (by decide))
  obtain rest : Rest roundClobbers s v := restU.trans native
  obtain workspaceV := ws.congr rest.wr
  refine WP.mono (top_ok v workspaceV fitTop row.outPtr ?_) ?_
  · have lo := oldTop 0 (by decide)
    obtain hi := oldTop 1 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at lo hi
    rw [show acc+4*(n-1)+4=acc+4*n by omega_arith,
      show acc+4*(n-1)+8=acc+4*n+4 by omega_arith,lo,hi]
    simpa only [H,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using topBound
  · rintro t ⟨topValue,memT,ptrT,restT⟩
    obtain nowrap : (State.addr base).toNat+size≤2^32 := by
      simpa only [VG.Proof.X25519.Arm.addr_toNat] using ws.nowrap
    obtain ⟨outTop,whole⟩ := rowCarry_memory (base:=State.addr base) (n:=n-1)
      nowrap (by omega_arith) memT
    obtain topEquation : (t.gpr .r3).toNat+2^32*(t.gpr .r4).toNat=H+(v.gpr .r11).toNat := by
      obtain lo := oldTop 0 (by decide)
      obtain hi := oldTop 1 (by decide)
      simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at lo hi
      rw [show acc+4*(n-1)+4=acc+4*n by omega_arith,
        show acc+4*(n-1)+8=acc+4*n+4 by omega_arith,lo,hi] at topValue
      simpa only [H,val32,Nat.mul_zero,Nat.add_zero,Nat.add_assoc] using topValue
    refine ⟨?_,?_,?_,?_⟩
    · rw [show n+1=(n-1)+2 by omega_arith,whole,topEquation]
      exact total
    · rw [ptrT]
      congr 2
      omega_arith
    · exact (outside.mono (Nat.le_refl _) (by omega_arith)).trans
        (outTop.mono (by omega_arith) (by omega_arith))
    · exact rest.trans (restT.mono (by decide))

end VG.Proof.Bignum.Arm.FusedReduction

end

end


/-! The Montgomery reduction and radix division share one downward-write pass. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem fusedStage_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n)
    (hdr : RoundMeta s.mem base tmp a b mod acc n i inv)
    (ptr : s.gpr .r0=base+BitVec.ofNat 32 (acc+4*n))
    (inverse : (val32 s.mem (State.addr base) mod n*inv.toNat+1)%2^32=0)
    (capacity : val32 s.mem (State.addr base) acc (n+2)+
      (inv*s.mem.readW (off (State.addr base) acc) 32).toNat*val32 s.mem (State.addr base) mod n<
        2^(32*(n+2))) :
    WP isa fusedReductionStage s fun t =>
      2^32*val32 t.mem (State.addr base) acc (n+1)=val32 s.mem (State.addr base) acc (n+2)+
        (inv*s.mem.readW (off (State.addr base) acc) 32).toNat*val32 s.mem (State.addr base) mod n ∧
      RoundMeta t.mem base tmp a b mod acc n i inv ∧
      t.gpr .r0=base+BitVec.ofNat 32 (acc+4*(n+1)) ∧
      Outside (State.addr base) acc (4*(n+1)) s.mem t.mem ∧ Rest roundClobbers s t := by
  have count := ctx.count
  have fits := ctx.tmpFits
  have layout := ctx.layout
  have accFit := ctx.accFits
  rw [fusedReductionStage,WP.seq_iff]
  refine WP.mono (reductionArgs_ok s (acc:=acc) (mod:=mod) (n:=n) inv ctx.workspace
    (by omega_using [fits, layout]) (by omega_using [accFit]) ptr ?_ ?_ ?_ ?_) ?_
  · simpa only [show acc+4*n+16=tmp by omega_using [layout]] using hdr.count
  · simpa only [show acc+4*n+24=tmp+8 by omega_using [layout]] using hdr.mPtr
  · simpa only [show acc+4*n+28=tmp+12 by omega_using [layout]] using hdr.inverse
  · simpa only [show acc+4*n+44=tmp+28 by omega_using [layout]] using hdr.accPtr
  · rintro u ⟨scalar,p0,p12,cnt,carry,memU,restU⟩
    obtain modLow : val32 s.mem (State.addr base) mod n%2^32=w32 s.mem (State.addr base) mod := by
      simpa only [show n-1+1=n by omega_using [count]] using val32_mod_low s.mem (State.addr base) mod (n-1)
    obtain lowInverse : (w32 s.mem (State.addr base) mod*inv.toNat+1)%2^32=0 := by
      simpa only [Nat.add_mod,Nat.mul_mod,modLow,Nat.mod_mod] using inverse
    obtain cancel : ((u.gpr .r1).toNat*w32 u.mem (State.addr base) mod+
        w32 u.mem (State.addr base) acc)%2^32=0 := by
      rw [memU,scalar,BitVec.toNat_mul]
      simpa only [w32,Nat.mul_comm] using
        mont_low (w32 s.mem (State.addr base) acc) inv.toNat (w32 s.mem (State.addr base) mod) lowInverse
    refine WP.mono (FusedReduction.code_ok u (ctx.workspace.congr restU.wr) (by omega_using [count])
      accFit ctx.mFits ctx.accM p0 p12 cnt carry cancel ?_) ?_
    · simpa only [memU,scalar] using capacity
    · rintro t ⟨value,pointer,outside,rest⟩
      rw [memU,scalar] at value
      rw [memU] at outside
      exact ⟨value,hdr.of_outside outside (by omega_using [layout]) (by have := ctx.workspace.nowrap;omega_using [fits, this]),
        pointer,outside,(restU.mono (by decide)).trans rest⟩

end VG.Proof.Bignum.Arm

end

end


/-! # A complete ARMv7 Montgomery round, including its memory and loop state -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (ofNat_beq_zero)
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont

theorem montRound_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n) (hdr : RoundMeta s.mem base tmp a b mod acc n i inv)
    (hi : i < n) (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp)
    (hT : val32 s.mem (State.addr base) acc (n + 2) < 2 * val32 s.mem (State.addr base) mod n)
    (hB : val32 s.mem (State.addr base) b n < val32 s.mem (State.addr base) mod n)
    (hInv : (val32 s.mem (State.addr base) mod n * inv.toNat + 1) % 2 ^ 32 = 0) :
    WP isa montRound s fun t => RoundPost s t base tmp a b mod acc n i inv := by
  have nowrap := ctx.workspace.nowrap
  have mfits := ctx.mFits
  have sep := ctx.accM
  rw [montRound, WP.seq_iff]
  refine WP.mono (productStage_ok s ctx hdr hi ptr hT hB) ?_
  rintro u ⟨product, hdrU, ptrU, outsideU, keepU⟩
  obtain modulus := outsideU.val32 (d := mod) (k := n) (by omega_using [sep]) (by omega_using [nowrap, mfits])
  obtain ctxU := ctx.congr keepU.wr
  let q := (inv * u.mem.readW (off (State.addr base) acc) 32).toNat
  obtain hq : q < 2 ^ 32 := (inv * u.mem.readW (off (State.addr base) acc) 32).isLt
  obtain ha : w32 s.mem (State.addr base) (a + 4 * i) < 2 ^ 32 :=
    (s.mem.readW (off (State.addr base) (a + 4 * i)) 32).isLt
  obtain capacity := round_fit hT ha hB hq (val32_lt s.mem (State.addr base) mod n)
  rw [WP.seq_iff]
  refine WP.mono (fusedStage_ok u ctxU hdrU ptrU (by rw [modulus];exact hInv) ?_) ?_
  · rw [product,modulus]
    exact capacity
  · rintro v ⟨quotient,hdrV,ptrV,outsideV,keepV⟩
    obtain ctxV := ctxU.congr keepV.wr
    refine WP.mono (roundFinish_ok (tmp:=tmp) (top:=acc+4*(n+1)) v ctxV.workspace (by have := ctx.tmpFits;omega_using [this])
      (by have := ctx.layout;omega_using [this]) ptrV) ?_
    rintro t ⟨memT,ptrT,zero,keepT⟩
    have mt : t.mem=finishMem v.mem (State.addr base) (acc+4*(n+1)) tmp := memT
    obtain nowrap' : (State.addr base).toNat+size≤2^32 := by
      simpa only [VG.Proof.X25519.Arm.addr_toNat] using nowrap
    obtain ⟨result,frame⟩ := finish_value (mem:=v.mem) (acc:=acc) (n:=n) (tmp:=tmp)
      nowrap' (by have := ctx.tmpFits;omega_using [this]) rfl (by have := ctx.layout;omega_using [this])
    rw [←mt] at result frame
    obtain value : 2^32*val32 t.mem (State.addr base) acc (n+2)=
        val32 s.mem (State.addr base) acc (n+2)+
          w32 s.mem (State.addr base) (a+4*i)*val32 s.mem (State.addr base) b n+
            q*val32 s.mem (State.addr base) mod n := by
      rw [result,quotient,product,modulus]
    refine ⟨?_,ptrT,⟨q,hq,value⟩,round_lt value hT ha hB hq,?_,?_,?_⟩
    · rw [mt]
      exact finish_meta nowrap ctx.tmpFits (by have := ctx.layout;omega_using [this]) hdrV hi
    · exact (Outs.of_outside (outsideU.trans
        (outsideV.mono (Nat.le_refl _) (by omega_using []))) (by simp)).trans frame
    · rw [zero,hdrV.remaining]
      change (BitVec.ofNat 32 (n-i)-BitVec.ofNat 32 1==0)=_
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]),ofNat_beq_zero (by omega_using [nowrap, mfits])]
      simp only [show n-i-1=0↔i+1=n by omega_using [hi]]
    · exact keepU.trans (keepV.trans (keepT.mono (by decide)))

end VG.Proof.Bignum.Arm
