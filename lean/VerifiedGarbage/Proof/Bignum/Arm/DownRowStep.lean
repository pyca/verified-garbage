module

public import VerifiedGarbage.Impl.Bignum.Arm.DownRow
public import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Block

/-! One multiply-add reads the old accumulator one word ahead of its output. -/

@[expose] public section
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
