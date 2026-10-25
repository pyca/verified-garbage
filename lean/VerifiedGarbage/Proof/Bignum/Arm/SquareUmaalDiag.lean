module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareDiag
public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
import VerifiedGarbage.Proof.Bignum.Arm.MacUmaal
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # UMAAL diagonal products preserve the existing squaring invariant -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_mov wp_subs op2_imm op2_reg dpVal ofNat_beq_zero)

theorem diagStepU_ok (s : State) {base : BitVec 32} {size A T : Nat} (ws : Workspace s base size)
    (fitA : A + 4 ≤ size) (fitT : T + 8 ≤ size)
    (p12 : s.gpr .r12 = base + BitVec.ofNat 32 A) (p0 : s.gpr .r0 = base + BitVec.ofNat 32 T) :
    WP isa diagStepU s fun t =>
      w32 t.mem (State.addr base) T + 2 ^ 32 * w32 t.mem (State.addr base) (T + 4) +
          2 ^ 64 * (t.gpr .r11).toNat =
        w32 s.mem (State.addr base) A * w32 s.mem (State.addr base) A + w32 s.mem (State.addr base) T +
          2 ^ 32 * w32 s.mem (State.addr base) (T + 4) + (s.gpr .r11).toNat ∧
      Outside (State.addr base) T 8 s.mem t.mem ∧ t.gpr .r0 = s.gpr .r0 ∧ t.gpr .r12 = s.gpr .r12 ∧
      t.gpr .lr = s.gpr .lr ∧ Rest roundClobbers s t := by
  have nowrap := ws.nowrap
  rw [diagStepU, WP.seq_iff]
  refine wp_ldr (by decide) (by simpa only [Nat.add_zero] using sq_ea nowrap p12 (imm := 0) (by omega_arith))
    (ws.read fitA) fun s1 u1 => ?_
  refine wp_mov (op2_reg _ _) fun s2 u2 => ?_
  refine wp_ldr (a := off (State.addr base) T) (by decide) (by
      rw [u2.other .r0 (by decide), u1.other .r0 (by decide)]
      simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega_arith))
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact ws.read (by omega_arith)) fun s3 u3 => WP.block_nil ?_
  rw [WP.seq_iff]
  refine WP.mono (macU_ok s3) ?_
  rintro s4 ⟨mac4, f4⟩
  have q0 : s4.gpr .r0 = s.gpr .r0 := by
    rw [f4.regs .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide),
      u1.other .r0 (by decide)]
  have mem4 : s4.mem = s.mem := by rw [f4.mem, u3.mem, u2.mem, u1.mem]
  have wr4 : s4.wr = s.wr := by rw [f4.wr, u3.wr, u2.wr, u1.wr]
  have rd4 : s4.rd = s.rd := by rw [f4.rd, u3.rd, u2.rd, u1.rd]
  have ea0 : State.addr (s4.gpr .r0 + BitVec.ofNat 32 0) = off (State.addr base) T := by
    rw [q0]; simpa only [Nat.add_zero] using sq_ea nowrap p0 (imm := 0) (by omega_arith)
  have ea4 {u : State} (hu : u.gpr .r0 = s.gpr .r0) :
      State.addr (u.gpr .r0 + BitVec.ofNat 32 4) = off (State.addr base) (T + 4) := by
    rw [hu]; exact sq_ea nowrap p0 (by omega_arith)
  refine wp_str (by decide) ea0 (by rw [wr4]; exact ws.write (by omega_arith)) fun s5 u5 => ?_
  refine wp_ldr (by decide) (ea4 (by rw [u5.gpr, q0])) (by rw [u5.rd, u5.wr, rd4, wr4]; exact ws.read (by omega_arith))
    fun s6 u6 => ?_
  refine wp_adds (op2_reg _ _) fun s7 u7 c7 => ?_
  refine wp_mov_c (op2_imm (by decide)) fun s8 u8 c8 => ?_
  refine wp_adc (op2_imm (by decide)) fun s9 u9 _ => ?_
  refine wp_str (by decide) (ea4 (by rw [u9.other .r0 (by decide), u8.other .r0 (by decide),
      u7.other .r0 (by decide), u6.other .r0 (by decide), u5.gpr, q0]))
    (by rw [u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, wr4]; exact ws.write (by omega_arith)) fun t u10 => WP.block_nil ?_
  -- Values.
  have x : s3.gpr .r10 = s.mem.readW (off (State.addr base) T) 32 := by rw [u3.gpr, u2.mem, u1.mem]
  have w1 : s3.gpr .r1 = s.mem.readW (off (State.addr base) A) 32 := by
    rw [u3.other .r1 (by decide), u2.other .r1 (by decide), u1.gpr]
  have w2 : s3.gpr .r2 = s.mem.readW (off (State.addr base) A) 32 := by
    rw [u3.other .r2 (by decide), u2.gpr, u1.gpr]
  have y : s6.gpr .r10 = s.mem.readW (off (State.addr base) (T + 4)) 32 := by
    rw [u6.gpr, u5.mem, mem4, rd_other _ (by omega_arith) (by omega_arith) (by omega_arith)]
  have lo : s9.gpr .r3 = s4.gpr .r3 := by
    rw [u9.other .r3 (by decide), u8.other .r3 (by decide), u7.other .r3 (by decide),
      u6.other .r3 (by decide), u5.gpr]
  have hi : s9.gpr .r4 = s4.gpr .r4 + s.mem.readW (off (State.addr base) (T + 4)) 32 := by
    rw [u9.other .r4 (by decide), u8.other .r4 (by decide), u7.gpr, u6.other .r4 (by decide), u5.gpr, y]
  have c1 : (s9.gpr .r11).toNat = (if 2 ^ 32 ≤ (s4.gpr .r4).toNat +
      (s.mem.readW (off (State.addr base) (T + 4)) 32).toNat then 1 else 0) := by
    rw [u9.gpr, c8, c7, u8.gpr, u6.other .r4 (by decide), u5.gpr, y]
    by_cases hc : 2 ^ 32 ≤ (s4.gpr .r4).toNat + (s.mem.readW (off (State.addr base) (T + 4)) 32).toNat <;>
      simp only [hc, decide_true, decide_false, ↓reduceIte] <;> rfl
  have memT : t.mem = (s.mem.writeW (off (State.addr base) T) (s4.gpr .r3)).writeW
      (off (State.addr base) (T + 4)) (s4.gpr .r4 + s.mem.readW (off (State.addr base) (T + 4)) 32) := by
    rw [u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, mem4, hi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [w32]
    rw [u10.gpr, c1, memT, rd_other (d := T + 4) (e := T) _ (by omega_arith) (by omega_arith) (by omega_arith), rd_self, rd_self]
    have ac := add_carry (s4.gpr .r4) (s.mem.readW (off (State.addr base) (T + 4)) 32)
    rw [x, w1, w2] at mac4
    change _ = (s.mem.readW (off (State.addr base) A) 32).toNat * (s.mem.readW (off (State.addr base) A) 32).toNat +
      (s.mem.readW (off (State.addr base) T) 32).toNat + 2 ^ 32 * (s.mem.readW (off (State.addr base) (T + 4)) 32).toNat +
      (s.gpr .r11).toNat
    rw [u3.other .r11 (by decide), u2.other .r11 (by decide), u1.other .r11 (by decide)] at mac4
    generalize (s4.gpr .r4 + s.mem.readW (off (State.addr base) (T + 4)) 32).toNat = h4 at *
    generalize (if 2 ^ 32 ≤ (s4.gpr .r4).toNat + (s.mem.readW (off (State.addr base) (T + 4)) 32).toNat
      then 1 else 0) = cc at *
    omega_arith
  · rw [memT]
    exact ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
      ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · rw [u10.gpr, u9.other .r0 (by decide), u8.other .r0 (by decide), u7.other .r0 (by decide),
      u6.other .r0 (by decide), u5.gpr, q0]
  · rw [u10.gpr, u9.other .r12 (by decide), u8.other .r12 (by decide), u7.other .r12 (by decide),
      u6.other .r12 (by decide), u5.gpr, f4.regs .r12 (by decide), u3.other .r12 (by decide),
      u2.other .r12 (by decide), u1.other .r12 (by decide)]
  · rw [u10.gpr, u9.other .lr (by decide), u8.other .lr (by decide), u7.other .lr (by decide),
      u6.other .lr (by decide), u5.gpr, f4.regs .lr (by decide), u3.other .lr (by decide),
      u2.other .lr (by decide), u1.other .lr (by decide)]
  · have k4 : Rest roundClobbers s3 s4 := ⟨fun r hr => f4.regs r (by revert hr; cases r <;> decide),
      f4.rd, f4.wr, f4.sp⟩
    exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (k4.trans
      ((u5.rest _).trans ((u6.rest (by decide)).trans ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans
      ((u9.rest (by decide)).trans (u10.rest _)))))))))

theorem diagLoopBodyU_ok {s0 s : State} {base : BitVec 32} {size T A n i : Nat}
    (ctx : DiagCtx s0 base size T A n) (inv : DiagLoopInv s0 base T A n i s) (hi : i < n) :
    WP isa (.seq diagStepU (.block diagAdvance)) s fun t => DiagLoopInv s0 base T A n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  have nowrap := ctx.workspace.nowrap
  have := ctx.tFits; have := ctx.aFits; have := ctx.sep
  have ws := ctx.workspace.congr inv.rest.wr
  rw [WP.seq_iff]
  refine WP.mono (diagStepU_ok s (A := A + 4 * i) (T := T + 8 * i) ws (by omega_arith) (by omega_arith) inv.aptr inv.ptr) ?_
  rintro s1 ⟨v1, o1, p0, p12, plr, r1⟩
  refine WP.mono (diagAdvance_ok s1) ?_
  rintro t ⟨q0, q12, qlr, z, mem, r2⟩
  have aw : w32 s.mem (State.addr base) (A + 4 * i) = w32 s0.mem (State.addr base) (A + 4 * i) :=
    inv.outside.w32 (by omega_arith) (by omega_arith)
  have tw0 : w32 s.mem (State.addr base) (T + 8 * i) = w32 s0.mem (State.addr base) (T + 8 * i) :=
    inv.outside.w32 (by omega_arith) (by omega_arith)
  have tw1 : w32 s.mem (State.addr base) (T + 8 * i + 4) = w32 s0.mem (State.addr base) (T + 8 * i + 4) :=
    inv.outside.w32 (by omega_arith) (by omega_arith)
  have low : val32 s1.mem (State.addr base) T (2 * i) = val32 s.mem (State.addr base) T (2 * i) :=
    o1.val32 (by omega_arith) (by omega_arith)
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [q0, p0, inv.ptr]
    change base + BitVec.ofNat 32 (T + 8 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show T + 8 * i + 8 = T + 8 * (i + 1) by omega_arith]
  · rw [q12, p12, inv.aptr]
    change base + BitVec.ofNat 32 (A + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add, show A + 4 * i + 4 = A + 4 * (i + 1) by omega_arith]
  · rw [qlr, plr, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith)]
    congr 1
  · rw [mem]
    exact (inv.outside.mono (Nat.le_refl _) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))
  · rw [mem, r2.gpr .r11 (by decide), show 2 * (i + 1) = 2 * i + 2 by omega_arith, val32_append s1.mem _ T (2 * i) 2,
      val32_append s0.mem _ T (2 * i) 2, show T + 4 * (2 * i) = T + 8 * i by omega_arith]
    simp only [val32, diagSum, Nat.mul_zero, Nat.add_zero]
    rw [show T + 8 * i + 4 = T + 8 * i + 4 from rfl, low, ← tw0, ← tw1, ← aw,
      show 32 * (2 * i) = 64 * i by omega_arith, show 64 * (i + 1) = 64 * i + 64 by omega_arith, Nat.pow_add]
    have e1 := inv.value
    have e2 := v1
    generalize 2 ^ (64 * i) = P at *
    grind
  · exact inv.rest.trans (r1.trans (r2.mono (by decide)))
  · rw [z, plr, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_arith), ofNat_beq_zero (by omega_arith)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_arith]

theorem diagLoopU_ok (s : State) {base : BitVec 32} {size T A n : Nat}
    (ctx : DiagCtx s base size T A n) (hn : 0 < n)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 T) (p12 : s.gpr .r12 = base + BitVec.ofNat 32 A)
    (plr : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa diagLoopU s (DiagLoopInv s base T A n n) := by
  let loopInv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ DiagLoopInv s base T A n i t
  unfold diagLoopU
  refine WP.loop (M := isa) loopInv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (diagLoopBodyU_ok ctx hi (by omega_arith)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_arith, i + 1, by omega_arith, by omega_arith, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega_arith, hn, ?_⟩
    refine ⟨by omega_arith, ?_, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using p0
    · simpa only [Nat.mul_zero, Nat.add_zero] using p12
    · simpa only [Nat.sub_zero] using plr
    · simp only [val32, diagSum, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqDiagPhaseU_ok (s : State) (h : DblInv m0 base size out a mod M n inv s) :
    WP isa sqDiagU s fun t => ProdInv m0 base size out a mod M n inv t ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header; have := env.sepA; have := env.aFits
  rw [sqDiagU, WP.seq_iff]
  refine WP.mono (sqAnchor_ok s env) ?_
  rintro s1 ⟨p1, m1, r1⟩
  have e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (sqDiagArgs_ok s1 (M := M) (n := n) (a := a) e1.workspace (by omega_arith) p1
    (by rw [m1]; exact h.md.count) (by rw [m1]; exact h.md.aPtr)) ?_
  rintro s2 ⟨p12, plr, p0, p11, m2, r2⟩
  have e2 := e1.of_mem m2 r2
  have ctx : DiagCtx s2 base size (M + 24) a n := ⟨e2.workspace, by omega_arith, by omega_arith, by omega_arith⟩
  refine WP.mono (diagLoopU_ok s2 ctx (by omega_arith) p0 p12 plr) ?_
  intro t di
  have ms : s2.mem = s.mem := m2.trans m1
  have et := e2.next (Outs.of_outside (di.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega_arith)
    (by omega_arith)) (by simp)) di.rest
  have dg : diagSum s2.mem (State.addr base) a n = diagSum m0 (State.addr base) a n :=
    sqDiag_congr fun j hj => e2.aWord hj
  have v := di.value
  rw [p11, dg, ms, h.value] at v
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] at v
  have sq := sq_eq m0 (State.addr base) a n
  rw [sqCross_last m0 (State.addr base) a n (by omega_arith)] at sq
  have lt := val32_lt m0 (State.addr base) a n
  have big : val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n < 2 ^ (64 * n) := by
    have := Nat.mul_lt_mul'' lt lt
    rwa [← Nat.pow_add, show 32 * n + 32 * n = 64 * n by omega_arith] at this
  have c0 : (t.gpr .r11).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (t.gpr .r11).toNat with c | c
    · exact c
    · have : 2 ^ (64 * n) * 1 ≤ 2 ^ (64 * n) * (t.gpr .r11).toNat := Nat.mul_le_mul_left _ c
      omega_arith
  refine ⟨⟨et, ?_, ?_, ?_⟩, ?_⟩
  · refine h.md.congr fun d hd => ?_
    rw [outside_read32 di.outside (by omega_arith) (by omega_arith), ms]
  · rw [c0, Nat.mul_zero, Nat.add_zero] at v
    rw [show 2 * n = 2 * n from rfl, v]
    omega_arith
  · rw [di.outside.val32 (by omega_arith) (by omega_arith), ms]; exact h.top
  · exact (r1.mono (by decide)).trans ((r2.mono (by decide)).trans di.rest)

end

end VG.Proof.Bignum.Arm
