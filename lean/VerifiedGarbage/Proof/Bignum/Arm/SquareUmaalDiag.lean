module

public import VerifiedGarbage.Proof.Bignum.Arm.SquareDiag
public import VerifiedGarbage.Impl.Bignum.Arm.SquareUmaal
import VerifiedGarbage.Proof.Bignum.Arm.SquareFusedStep
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Fused doubling and UMAAL diagonal products -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_dp wp_mov wp_subs op2_imm op2_reg dpVal ofNat_beq_zero)

structure FusedDiagLoopInv (s0 : State) (base : BitVec 32) (T A n i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r0 = base + BitVec.ofNat 32 (T + 8 * i)
  aptr : s.gpr .r12 = base + BitVec.ofNat 32 (A + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) T (8 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) T (2 * i) + 2 ^ (64 * i) * (s.gpr .r11).toNat =
    2 * val32 s0.mem (State.addr base) T (2 * i) + diagSum s0.mem (State.addr base) A i + (s0.gpr .r11).toNat
  rest : Rest roundClobbers s0 s

theorem diagLoopBodyU_ok {s0 s : State} {base : BitVec 32} {size T A n i : Nat}
    (ctx : DiagCtx s0 base size T A n) (inv : FusedDiagLoopInv s0 base T A n i s) (hi : i < n) :
    WP isa (.seq diagStepU (.block diagAdvance)) s fun t => FusedDiagLoopInv s0 base T A n (i + 1) t ∧
      t.z = decide (i + 1 = n) := by
  have nowrap := ctx.workspace.nowrap
  have := ctx.tFits; have := ctx.aFits; have := ctx.sep
  have ws := ctx.workspace.congr inv.rest.wr
  rw [WP.seq_iff]
  refine WP.mono (fusedDiagStep_ok s (A := A + 4 * i) (T := T + 8 * i) ws (by omega) (by omega) inv.aptr inv.ptr) ?_
  rintro s1 ⟨v1, o1, p0, p12, plr, r1⟩
  refine WP.mono (diagAdvance_ok s1) ?_
  rintro t ⟨q0, q12, qlr, z, mem, r2⟩
  have aw : w32 s.mem (State.addr base) (A + 4 * i) = w32 s0.mem (State.addr base) (A + 4 * i) :=
    inv.outside.w32 (by omega) (by omega)
  have tw0 : w32 s.mem (State.addr base) (T + 8 * i) = w32 s0.mem (State.addr base) (T + 8 * i) :=
    inv.outside.w32 (by omega) (by omega)
  have tw1 : w32 s.mem (State.addr base) (T + 8 * i + 4) = w32 s0.mem (State.addr base) (T + 8 * i + 4) :=
    inv.outside.w32 (by omega) (by omega)
  have low : val32 s1.mem (State.addr base) T (2 * i) = val32 s.mem (State.addr base) T (2 * i) :=
    o1.val32 (by omega) (by omega)
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [q0, p0, inv.ptr]
    change base + BitVec.ofNat 32 (T + 8 * i) + BitVec.ofNat 32 8 = _
    rw [Offset.add_add, show T + 8 * i + 8 = T + 8 * (i + 1) by omega]
  · rw [q12, p12, inv.aptr]
    change base + BitVec.ofNat 32 (A + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add, show A + 4 * i + 4 = A + 4 * (i + 1) by omega]
  · rw [qlr, plr, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [mem]
    exact (inv.outside.mono (Nat.le_refl _) (by omega)).trans (o1.mono (by omega) (by omega))
  · rw [mem, r2.gpr .r11 (by simp), show 2 * (i + 1) = 2 * i + 2 by omega, val32_append s1.mem _ T (2 * i) 2,
      val32_append s0.mem _ T (2 * i) 2, show T + 4 * (2 * i) = T + 8 * i by omega]
    simp only [val32, diagSum, Nat.mul_zero, Nat.add_zero]
    rw [show T + 8 * i + 4 = T + 8 * i + 4 from rfl, low, ← tw0, ← tw1, ← aw,
      show 32 * (2 * i) = 64 * i by omega, show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add]
    have e1 := inv.value
    have e2 := v1
    generalize 2 ^ (64 * i) = P at *
    grind
  · exact inv.rest.trans (r1.trans (r2.mono (by simp [roundClobbers])))
  · rw [z, plr, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

theorem diagLoopU_ok (s : State) {base : BitVec 32} {size T A n : Nat}
    (ctx : DiagCtx s base size T A n) (hn : 0 < n)
    (p0 : s.gpr .r0 = base + BitVec.ofNat 32 T) (p12 : s.gpr .r12 = base + BitVec.ofNat 32 A)
    (plr : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa diagLoopU s (FusedDiagLoopInv s base T A n n) := by
  let loopInv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ FusedDiagLoopInv s base T A n i t
  unfold diagLoopU
  refine WP.loop (M := isa) loopInv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (diagLoopBodyU_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    refine ⟨by omega, ?_, ?_, ?_, Outside.refl _ _ _ _, ?_, Rest.refl _ _⟩
    · simpa only [Nat.mul_zero, Nat.add_zero] using p0
    · simpa only [Nat.mul_zero, Nat.add_zero] using p12
    · simpa only [Nat.sub_zero] using plr
    · simp only [val32, diagSum, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem sqDiagPhaseU_ok (s : State) (h : CrossInv m0 base size out a mod M n inv (n - 1) s) :
    WP isa sqDiagU s fun t => ProdInv m0 base size out a mod M n inv t ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header; have := env.sepA; have := env.aFits
  have topS : val32 s.mem (State.addr base) (M + 24 + 8 * n) 2 = 0 := by
    have z := h.top
    rw [show n - 1 + n = 2 * n - 1 by omega, show n + 2 - (n - 1) = 1 + 2 by omega] at z
    have z' := val32_zero_tail z
    rwa [show M + 24 + 4 * (2 * n - 1) + 4 * 1 = M + 24 + 8 * n by omega] at z'
  have lowS : val32 s.mem (State.addr base) (M + 24) (2 * n) = sqCross m0 (State.addr base) a n (n - 1) := by
    have v := h.value
    rw [val32_append s.mem (State.addr base) (M + 24) (2 * n) 2,
      show M + 24 + 4 * (2 * n) = M + 24 + 8 * n by omega, topS, Nat.mul_zero, Nat.add_zero] at v
    exact v
  rw [sqDiagU, WP.seq_iff]
  refine WP.mono (sqAnchor_ok s env) ?_
  rintro s1 ⟨p1, m1, r1⟩
  have e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (sqDiagArgs_ok s1 (M := M) (n := n) (a := a) e1.workspace (by omega) p1
    (by rw [m1]; exact h.md.count) (by rw [m1]; exact h.md.aPtr)) ?_
  rintro s2 ⟨p12, plr, p0, p11, m2, r2⟩
  have e2 := e1.of_mem m2 r2
  have ctx : DiagCtx s2 base size (M + 24) a n := ⟨e2.workspace, by omega, by omega, by omega⟩
  refine WP.mono (diagLoopU_ok s2 ctx (by omega) p0 p12 plr) ?_
  intro t di
  have ms : s2.mem = s.mem := m2.trans m1
  have et := e2.next (Outs.of_outside (di.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega)
    (by omega)) (by simp)) di.rest
  have dg : diagSum s2.mem (State.addr base) a n = diagSum m0 (State.addr base) a n :=
    sqDiag_congr fun j hj => e2.aWord hj
  have v := di.value
  rw [p11, dg, ms, lowS] at v
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] at v
  have sq := sq_eq m0 (State.addr base) a n
  rw [sqCross_last m0 (State.addr base) a n (by omega)] at sq
  have lt := val32_lt m0 (State.addr base) a n
  have big : val32 m0 (State.addr base) a n * val32 m0 (State.addr base) a n < 2 ^ (64 * n) := by
    have := Nat.mul_lt_mul'' lt lt
    rwa [← Nat.pow_add, show 32 * n + 32 * n = 64 * n by omega] at this
  have c0 : (t.gpr .r11).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (t.gpr .r11).toNat with c | c
    · exact c
    · have : 2 ^ (64 * n) * 1 ≤ 2 ^ (64 * n) * (t.gpr .r11).toNat := Nat.mul_le_mul_left _ c
      omega
  refine ⟨⟨et, ?_, ?_, ?_⟩, ?_⟩
  · refine h.md.congr fun d hd => ?_
    rw [outside_read32 di.outside (by omega) (by omega), ms]
  · rw [c0, Nat.mul_zero, Nat.add_zero] at v
    rw [show 2 * n = 2 * n from rfl, v]
    omega
  · rw [di.outside.val32 (by omega) (by omega), ms]; exact topS
  · exact (r1.mono (by simp [roundClobbers])).trans ((r2.mono (by simp [roundClobbers])).trans di.rest)

end

end VG.Proof.Bignum.Arm
