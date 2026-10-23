module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.State
public import VerifiedGarbage.Proof.Bignum.Arm.Mac
import VerifiedGarbage.Proof.Bignum.Arm.FiosArithmetic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-! The tops of both rows: row `i`'s top words plus its carries, row `i + 1`'s
last word, and its top plus its carries, stored as three words. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_mov wp_dp op2_imm op2_reg dpVal)

theorem macFrame_rest {rs : List Reg} {s t : State} (h : MacFrame rs s t) : Rest rs s t :=
  ⟨h.regs, h.rd, h.wr, h.sp⟩

/-- With `r0`, `r12` and `r4` at offsets `d`, `bb` and `mm`, the three words
stored at `d`, `d + 4` and `d + 8` are row `i + 1`'s products with the words
at `bb + 4` and `mm + 4`, plus the words at `d + 8` and `d + 12` and the four
carries. -/
theorem top_ok (s : State) {base : BitVec 32} {size d bb mm : Nat}
    (ws : Workspace s base size) (fd : d + 16 ≤ size) (fb : bb + 8 ≤ size) (fm : mm + 8 ≤ size)
    (pd : s.gpr .r0 = base + BitVec.ofNat 32 d)
    (pb : s.gpr .r12 = base + BitVec.ofNat 32 bb)
    (pm : s.gpr .r4 = base + BitVec.ofNat 32 mm)
    (bound : w32 s.mem (State.addr base) (d + 8) + 2 ^ 32 * w32 s.mem (State.addr base) (d + 12) +
      (s.gpr .r7).toNat + (s.gpr .r8).toNat < 2 ^ 64) :
    WP isa VG.Impl.Bignum.Arm.Fios2.top s fun t =>
      ∃ v0 v1 v2 : BitVec 32,
        t.mem = ((s.mem.writeW (off (State.addr base) d) v0).writeW (off (State.addr base) (d + 4)) v1).writeW
          (off (State.addr base) (d + 8)) v2 ∧
        v0.toNat + 2 ^ 32 * (v1.toNat + 2 ^ 32 * v2.toNat) =
          w32 s.mem (State.addr base) (bb + 4) * (s.gpr .r9).toNat +
          w32 s.mem (State.addr base) (mm + 4) * (s.gpr .r10).toNat +
          (w32 s.mem (State.addr base) (d + 8) + 2 ^ 32 * w32 s.mem (State.addr base) (d + 12)) + carries s ∧
        t.gpr .r0 = base + BitVec.ofNat 32 (d + 12) ∧
        Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r11] s t := by
  have nowrap := ws.nowrap
  rw [VG.Impl.Bignum.Arm.Fios2.top, WP.seq_iff]
  -- the last words of b and m, and the top words of the accumulator
  refine wp_ldr (a := off (State.addr base) (bb + 4)) (by decide) (ws.ea pb (by omega)) (ws.read (by omega))
    fun s1 h1 => ?_
  refine wp_ldr (a := off (State.addr base) (mm + 4)) (by decide)
    (by rw [h1.other .r4 (by decide)]; exact ws.ea pm (by omega))
    (by rw [h1.rd, h1.wr]; exact ws.read (by omega)) fun s2 h2 => ?_
  refine wp_ldr (a := off (State.addr base) (d + 8)) (by decide)
    (by rw [h2.other .r0 (by decide), h1.other .r0 (by decide)]; exact ws.ea pd (by omega))
    (by rw [h2.rd, h2.wr, h1.rd, h1.wr]; exact ws.read (by omega)) fun s3 h3 => ?_
  refine wp_ldr (a := off (State.addr base) (d + 12)) (by decide)
    (by rw [h3.other .r0 (by decide), h2.other .r0 (by decide), h1.other .r0 (by decide)]
        exact ws.ea pd (by omega))
    (by rw [h3.rd, h3.wr, h2.rd, h2.wr, h1.rd, h1.wr]; exact ws.read (by omega))
    fun s4 h4 => WP.block_nil ?_
  have K4 : Rest [.r1, .r2, .r3, .r4] s s4 :=
    (h1.rest (by simp)).trans ((h2.rest (by simp)).trans ((h3.rest (by simp)).trans (h4.rest (by simp))))
  have m4 : s4.mem = s.mem := h4.mem.trans (h3.mem.trans (h2.mem.trans h1.mem))
  have b4 : s4.gpr .r1 = s.mem.readW (off (State.addr base) (bb + 4)) 32 := by
    rw [h4.other .r1 (by decide), h3.other .r1 (by decide), h2.other .r1 (by decide), h1.gpr]
  have mm4 : s4.gpr .r2 = s.mem.readW (off (State.addr base) (mm + 4)) 32 := by
    rw [h4.other .r2 (by decide), h3.other .r2 (by decide), h2.gpr, h1.mem]
  have t3 : s4.gpr .r3 = s.mem.readW (off (State.addr base) (d + 8)) 32 := by
    rw [h4.other .r3 (by decide), h3.gpr, h2.mem, h1.mem]
  have t4 : s4.gpr .r4 = s.mem.readW (off (State.addr base) (d + 12)) 32 := by
    rw [h4.gpr, h3.mem, h2.mem, h1.mem]
  have t3n : (s4.gpr .r3).toNat = w32 s.mem (State.addr base) (d + 8) := by rw [t3]
  have t4n : (s4.gpr .r4).toNat = w32 s.mem (State.addr base) (d + 12) := by rw [t4]
  have b4n : (s4.gpr .r1).toNat = w32 s.mem (State.addr base) (bb + 4) := by rw [b4]
  have mm4n : (s4.gpr .r2).toNat = w32 s.mem (State.addr base) (mm + 4) := by rw [mm4]
  -- row i's top: r4:r3 += r7, r8
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s4 .r7 (by
    rw [t3, t4, K4.gpr .r7 (by simp)]; simp only [w32] at bound; omega)) ?_
  rintro s5 ⟨v5, f5⟩
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s5 .r8 (by
    rw [v5, t3, t4, K4.gpr .r7 (by simp), f5.regs .r8 (by simp), K4.gpr .r8 (by simp)]
    simp only [w32] at bound; omega)) ?_
  rintro s6 ⟨v6, f6⟩
  -- row i + 1's last word
  rw [WP.seq_iff]
  refine WP.mono (Fios.umaal_ok s6 .r3 .r5 .r1 .r9 (by decide)) ?_
  rintro s7 ⟨v7, f7⟩
  rw [WP.seq_iff]
  refine WP.mono (Fios.umaal_ok s7 .r3 .r11 .r2 .r10 (by decide)) ?_
  rintro s8 ⟨v8, f8⟩
  have K8 : Rest [.r1, .r2, .r3, .r4, .r5, .r11] s s8 :=
    (K4.mono (by simp)).trans ((macFrame_rest f5).mono (by simp) |>.trans
      ((macFrame_rest f6).mono (by simp) |>.trans ((macFrame_rest f7).mono (by simp) |>.trans
        ((macFrame_rest f8).mono (by simp)))))
  have m8 : s8.mem = s.mem := f8.mem.trans (f7.mem.trans (f6.mem.trans (f5.mem.trans m4)))
  have p8 : s8.gpr .r0 = base + BitVec.ofNat 32 d := (K8.gpr .r0 (by simp)).trans pd
  have ws8 := ws.congr K8.wr
  -- store it, then row i + 1's top: r4:r3 := the high word, += r5, r11
  rw [WP.seq_iff]
  refine wp_str (a := off (State.addr base) d) (by decide)
    (by simpa only [Nat.add_zero] using ws8.ea p8 (imm := 0) (by omega)) (ws8.write (by omega)) fun s9 h9 => ?_
  refine wp_mov (op2_reg _ .r4) fun s10 h10 => ?_
  refine wp_mov (op2_imm (by decide)) fun s11 h11 => WP.block_nil ?_
  have hi11 : s11.gpr .r3 = s8.gpr .r4 := by rw [h11.other .r3 (by decide), h10.gpr, h9.gpr]
  have z11 : s11.gpr .r4 = 0 := h11.gpr
  have c5 : s11.gpr .r5 = s8.gpr .r5 := by rw [h11.other .r5 (by decide), h10.other .r5 (by decide), h9.gpr]
  have c11 : s11.gpr .r11 = s8.gpr .r11 := by
    rw [h11.other .r11 (by decide), h10.other .r11 (by decide), h9.gpr]
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s11 .r5 (by
    rw [hi11, z11, c5]; have := (s8.gpr .r5).isLt; change _ + 0 * _ + _ < _; omega)) ?_
  rintro s12 ⟨v12, f12⟩
  rw [WP.seq_iff]
  refine WP.mono (addWord_ok s12 .r11 (by
    rw [v12, hi11, z11, c5, f12.regs .r11 (by simp), c11]
    have := (s8.gpr .r5).isLt; have := (s8.gpr .r11).isLt; change _ + 0 * _ + _ + _ < _; omega)) ?_
  rintro s13 ⟨v13, f13⟩
  have f1213 := f12.trans f13
  have m13 : s13.mem = s9.mem := f1213.mem.trans (h11.mem.trans h10.mem)
  have p13 : s13.gpr .r0 = base + BitVec.ofNat 32 d := by
    rw [f1213.regs .r0 (by simp), h11.other .r0 (by decide), h10.other .r0 (by decide), h9.gpr, p8]
  have w13 : s13.wr = s.wr := by rw [f1213.wr, h11.wr, h10.wr, h9.wr, K8.wr]
  refine wp_str (a := off (State.addr base) (d + 4)) (by decide) ((ws.congr w13).ea p13 (by omega))
    (by rw [w13]; exact ws.write (by omega)) fun s14 h14 => ?_
  refine wp_str (a := off (State.addr base) (d + 8)) (by decide)
    (by rw [h14.gpr]; exact (ws.congr w13).ea p13 (by omega))
    (by rw [h14.wr, w13]; exact ws.write (by omega)) fun s15 h15 => ?_
  refine wp_dp (op2_imm (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨s8.gpr .r3, s13.gpr .r3, s13.gpr .r4, ?_, ?_, ?_, ?_⟩
  · rw [ht.mem, h15.mem, h14.gpr, h14.mem, m13, h9.mem, m8]
  · -- the arithmetic
    have e7 : s6.gpr .r9 = s.gpr .r9 := by
      rw [f6.regs .r9 (by simp), f5.regs .r9 (by simp), K4.gpr .r9 (by simp)]
    have e10 : s7.gpr .r10 = s.gpr .r10 := by
      rw [f7.regs .r10 (by simp), f6.regs .r10 (by simp), f5.regs .r10 (by simp), K4.gpr .r10 (by simp)]
    have e1 : s6.gpr .r1 = s4.gpr .r1 := by rw [f6.regs .r1 (by simp), f5.regs .r1 (by simp)]
    have e2 : s7.gpr .r2 = s4.gpr .r2 := by
      rw [f7.regs .r2 (by simp), f6.regs .r2 (by simp), f5.regs .r2 (by simp)]
    have e5 : s6.gpr .r5 = s.gpr .r5 := by
      rw [f6.regs .r5 (by simp), f5.regs .r5 (by simp), K4.gpr .r5 (by simp)]
    have e11 : s7.gpr .r11 = s.gpr .r11 := by
      rw [f7.regs .r11 (by simp), f6.regs .r11 (by simp), f5.regs .r11 (by simp), K4.gpr .r11 (by simp)]
    have e8 : s5.gpr .r8 = s.gpr .r8 := (f5.regs .r8 (by simp)).trans (K4.gpr .r8 (by simp))
    have r4 : s8.gpr .r4 = s6.gpr .r4 := (f8.regs .r4 (by simp)).trans (f7.regs .r4 (by simp))
    rw [t3n, t4n, K4.gpr .r7 (by simp)] at v5
    rw [v5, e8] at v6
    rw [e1, b4n, e7, e5] at v7
    rw [e2, mm4n, e10, e11] at v8
    have r5' : s8.gpr .r5 = s7.gpr .r5 := f8.regs .r5 (by simp)
    rw [v12, hi11, z11, c5, f12.regs .r11 (by simp), c11] at v13
    unfold carries
    rw [r4] at v13
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero] at v13
    rw [r5'] at v13
    omega
  · rw [ht.gpr, dpVal, h15.gpr, h14.gpr, p13]
    exact Offset.add_add _ _ _
  · have k11 : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r11] s s11 :=
      (K8.mono (by simp)).trans ((h9.rest _).trans ((h10.rest (by simp)).trans (h11.rest (by simp))))
    have k13 : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r11] s s13 :=
      k11.trans ((macFrame_rest f1213).mono (by simp))
    exact k13.trans ((h14.rest _).trans ((h15.rest _).trans (ht.rest (by simp))))

end VG.Proof.Bignum.Arm.Fios2
