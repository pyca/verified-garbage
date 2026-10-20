module

public import VerifiedGarbage.Impl.Bignum.Arm.SquareReduceWith
public import VerifiedGarbage.Proof.Bignum.Arm.RowKernel
public import VerifiedGarbage.Proof.Bignum.Arm.SquareReduce
import VerifiedGarbage.Proof.Bignum.Arm.RoundMath
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Bignum.Arm.SquareCross
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_ldr wp_str wp_dp wp_mov wp_mul op2_imm op2_reg dpVal)

section
variable {m0 : Mem} {base : BitVec 32} {size out a mod M n : Nat} {inv : BitVec 32}

theorem redRoundWith_ok (K : RowKernel) (s : State) {k : Nat} (h : RedInv m0 base size out a mod M n inv k s) (hk : k < n) :
    WP isa (redRoundWith K.code) s fun t => RedInv m0 base size out a mod M n inv (k + 1) t ∧
      t.z = decide (k + 1 = n) ∧ Rest roundClobbers s t := by
  have env := h.env
  have nowrap := env.nowrap
  have := env.fits; have := env.count; have := env.header; have := env.sepM; have := env.mFits
  obtain ⟨o, ho⟩ : ∃ o, o = M + 24 + 4 * k := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = o + 4 * n := ⟨_, rfl⟩
  rw [redRoundWith, WP.seq_iff]
  refine WP.mono (sqBase_ok s env .r0) ?_
  rintro s1 ⟨p1, m1, r1⟩
  have e1 := env.of_mem m1 r1
  rw [WP.seq_iff]
  refine WP.mono (redHeader_ok s1 e1.workspace (by omega) p1 e1.modNow e1.invNow e1.metaNow) ?_
  rintro s2 ⟨q12, q1, q0, m2, r2⟩
  have e2 := e1.of_mem m2 r2
  rw [WP.seq_iff]
  refine WP.mono (redArgs_ok s2 (P := o) e2.workspace (by omega) q0 (by rw [m2, m1]; exact h.md.count)
    (by rw [m2, m1, ho]; exact h.tptr)) ?_
  rintro s3 ⟨g3lr, g30, m3, r3⟩
  have o3 := writeW32_outside s2.mem (State.addr base) (d := M + 20) (base + BitVec.ofNat 32 (o + 4)) (by omega)
  rw [← m3] at o3
  have e3 := e2.next (Outs.of_outside (o3.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega))
    (by simp)) r3
  rw [WP.seq_iff]
  refine WP.mono (redScalar_ok s3 e3.workspace (D := o) (by omega) g30) ?_
  rintro s4 ⟨g41, g411, g40, m4, r4⟩
  have e4 := e3.of_mem m4 r4
  have ctx : RowCtx s4 base size o mod n := ⟨nowrap, by omega, by omega, by omega, e4.workspace.writable⟩
  rw [WP.seq_iff]
  refine WP.mono (K.correct s4 ctx (by omega) (g40.trans g30)
    (by rw [r4.gpr .r12 (by simp), r3.gpr .r12 (by simp)]; exact q12)
    (by rw [r4.gpr .lr (by simp)]; exact g3lr)) ?_
  intro s5 ri
  have e5 := e4.next (Outs.of_outside (ri.outside.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega)
    (by omega)) (by simp)) ri.rest
  rw [WP.seq_iff]
  refine WP.mono (sqBase_ok s5 e5 .r2) ?_
  rintro s6 ⟨p6, m6, r6⟩
  have e6 := e5.of_mem m6 r6
  rw [WP.seq_iff]
  refine wp_ldr (by decide) (sq_ea0 nowrap p6 (by omega)) (e6.read (by omega)) fun s7 u7 => WP.block_nil ?_
  have e7 := e6.of_mem u7.mem (u7.rest (ws := [.r2]) (by simp))
  have p72 : s7.gpr .r2 = base + BitVec.ofNat 32 M := u7.gpr.trans e6.metaNow
  have p70 : s7.gpr .r0 = base + BitVec.ofNat 32 D := by
    rw [u7.other .r0 (by decide), r6.gpr .r0 (by simp), ri.outPtr, hD]
  rw [WP.seq_iff]
  refine WP.mono (redCarry_ok s7 e7.workspace (D := D) (M := M) (by omega) (by omega) p70 p72) ?_
  rintro s8 ⟨lo, hi, car, m8, p80, r8⟩
  have o8a := writeW32_outside s7.mem (State.addr base) (d := D) lo (by omega)
  have o8b := writeW32_outside (s7.mem.writeW (off (State.addr base) D) lo) (State.addr base) (d := M + 12) hi
    (by omega)
  rw [← m8] at o8b
  have e8 := e7.next (Outs.of_outside ((o8a.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega)).trans
    (o8b.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega))) (by simp)) r8
  have cnt8 : s8.mem.readW (off (State.addr base) (M + 16)) 32 = BitVec.ofNat 32 (n - k) := by
    rw [m8, rd_other _ (by omega) (by omega) (by omega), rd_other _ (by omega) (by omega) (by omega), u7.mem, m6,
      outside_read32 ri.outside (by omega) (by omega), m4, m3, rd_other _ (by omega) (by omega) (by omega), m2, m1]
    exact h.cnt
  refine WP.mono (sqCount_ok s8 e8.workspace (by omega) p80 cnt8 (by omega) (by omega)) ?_
  rintro t ⟨m9, z9, r9⟩
  have o9 := writeW32_outside s8.mem (State.addr base) (d := M + 16) (BitVec.ofNat 32 (n - k - 1)) (by omega)
  rw [← m9] at o9
  have et := e8.next (Outs.of_outside (o9.mono (o' := M) (n' := 4 * (2 * n + 8)) (by omega) (by omega))
    (by simp)) r9
  -- Where memory changed.
  obtain ⟨w, hw⟩ : ∃ w, w = s7.mem.writeW (off (State.addr base) D) lo := ⟨_, rfl⟩
  rw [← hw] at o8a o8b m8
  have hw7 : s7.mem = s5.mem := u7.mem.trans m6
  have o8a' : Outside (State.addr base) D 4 s5.mem w := by rw [← hw7]; exact o8a
  have OW : Outside (State.addr base) o (4 * n + 4) s4.mem w :=
    (ri.outside.mono (by omega) (by omega)).trans (o8a'.mono (by omega) (by omega))
  have all : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s.mem t.mem := by
    have A1 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s2.mem s3.mem :=
      Outs.of_outside (o3.mono (o' := M + 12) (n' := 12) (by omega) (by omega)) (by simp)
    have A2 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s4.mem w := Outs.of_outside OW (by simp)
    have A4 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] w s8.mem :=
      Outs.of_outside (o8b.mono (o' := M + 12) (n' := 12) (by omega) (by omega)) (by simp)
    have A5 : Outs (State.addr base) [(M + 12, 12), (o, 4 * n + 4)] s8.mem t.mem :=
      Outs.of_outside (o9.mono (o' := M + 12) (n' := 12) (by omega) (by omega)) (by simp)
    rw [m2, m1] at A1
    rw [m4] at A2
    exact A1.trans (A2.trans (A4.trans A5))
  -- The carry in, and the old values.
  have c4 : s4.mem.readW (off (State.addr base) (M + 12)) 32 = s.mem.readW (off (State.addr base) (M + 12)) 32 := by
    rw [m4, m3, rd_other _ (by omega) (by omega) (by omega), m2, m1]
  have c7 : s7.mem.readW (off (State.addr base) (M + 12)) 32 = s.mem.readW (off (State.addr base) (M + 12)) 32 := by
    rw [hw7, outside_read32 ri.outside (by omega) (by omega), c4]
  have x7 : s7.mem.readW (off (State.addr base) D) 32 = s4.mem.readW (off (State.addr base) D) 32 := by
    rw [hw7, outside_read32 ri.outside (by omega) (by omega)]
  have r7 : s7.gpr .r11 = s5.gpr .r11 := by rw [u7.other .r11 (by decide), r6.gpr .r11 (by simp)]
  have VT : val32 s4.mem (State.addr base) (M + 24) (2 * n) = val32 s.mem (State.addr base) (M + 24) (2 * n) := by
    rw [m4, o3.val32 (by omega) (by omega), m2, m1]
  have inv4 : s4.gpr .r1 = inv * s4.mem.readW (off (State.addr base) o) 32 := by
    rw [g41, r3.gpr .r1 (by simp), q1, m4]
  have N4 : val32 s4.mem (State.addr base) mod n = val32 m0 (State.addr base) mod n := e4.modVal
  have row := ri.value
  rw [g411, inv4, N4] at row
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero] at row
  rw [x7, r7, c7] at car
  have rep := val32_replace (m := s4.mem) (m' := w) (base := State.addr base) (d := M + 24) (i := k) (j := n + 1)
    (k := n - k - 1) (OW.val32 (by omega) (by omega)) (OW.val32 (by omega) (by omega))
  rw [show k + (n + 1) + (n - k - 1) = 2 * n by omega, show M + 24 + 4 * k = o by omega] at rep
  have hX := val32_succ s4.mem (State.addr base) o n
  have hX' := val32_succ w (State.addr base) o n
  rw [o8a'.val32 (d := o) (k := n) (by omega) (by omega), ← hD, hw, w32_write_self, ← hw] at hX'
  rw [← hD] at hX
  have step := red_value (W := 2 ^ 32) rep (by rw [hX, Nat.mul_comm]) (by rw [hX', Nat.mul_comm]) row car
  obtain ⟨Q, hQ, value⟩ := h.value
  have pk : 2 ^ (32 * (k + 1 + n)) = 2 ^ (32 * k) * 2 ^ (32 * n) * 2 ^ 32 := by
    rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
  have pk' : 2 ^ (32 * (k + n)) = 2 ^ (32 * k) * 2 ^ (32 * n) := by
    rw [← Nat.pow_add]; congr 1; omega
  have mlt := (inv * s4.mem.readW (off (State.addr base) o) 32).isLt
  -- The cleared word.
  have hu : (inv * s4.mem.readW (off (State.addr base) o) 32).toNat =
      val32 s4.mem (State.addr base) o n * inv.toNat % 2 ^ 32 := by
    have := coefficient_value inv s4.mem (State.addr base) o (n - 1)
    rw [show n - 1 + 1 = n by omega] at this
    exact this
  have cancel := round_cancel (T := val32 s4.mem (State.addr base) o n)
    (T' := val32 s5.mem (State.addr base) o n + 2 ^ (32 * n) * (s5.gpr .r11).toNat) e4.invOk hu row
  rw [show 32 * n = 32 + 32 * (n - 1) by omega, Nat.pow_add, Nat.mul_assoc, Nat.add_mul_mod_self_left,
    show n = n - 1 + 1 by omega, val32_mod_low] at cancel
  refine ⟨⟨et, h.md.of_outs all (by simp; omega) (by omega), by omega, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [m9, rd_self, show n - k - 1 = n - (k + 1) by omega]
  · rw [m9, rd_other _ (by omega) (by omega) (by omega), m8, rd_other _ (by omega) (by omega) (by omega),
      outside_read32 o8a' (by omega) (by omega), outside_read32 ri.outside (by omega) (by omega), m4, m3, rd_self,
      ho, show M + 24 + 4 * k + 4 = M + 24 + 4 * (k + 1) by omega]
  · refine ⟨Q + 2 ^ (32 * k) * (inv * s4.mem.readW (off (State.addr base) o) 32).toNat, ?_, ?_⟩
    · rw [show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add]
      exact red_q hQ mlt
    · rw [o9.val32 (by omega) (by omega), o8b.val32 (by omega) (by omega), m9,
        rd_other _ (by omega) (by omega) (by omega), m8, rd_self, pk]
      rw [VT] at step
      rw [step, ← pk', value]
      grind
  · rw [val32_succ, all.val32 (by simp; omega) (by omega), h.low, o9.w32 (by omega) (by omega),
      o8b.w32 (by omega) (by omega), o8a'.w32 (by omega) (by omega), show M + 24 + 4 * k = o by omega, cancel,
      Nat.mul_zero]
  · rw [all.val32 (by simp; omega) (by omega)]; exact h.top
  · rw [z9]; simp only [show n - k = 1 ↔ k + 1 = n by omega]
  · exact (r1.mono (by simp [roundClobbers])).trans ((r2.mono (by simp [roundClobbers])).trans
      ((r3.mono (by simp [roundClobbers])).trans ((r4.mono (by simp [roundClobbers])).trans
      ((ri.rest.mono (by simp [loopClobbers, roundClobbers])).trans ((r6.mono (by simp [roundClobbers])).trans
      ((u7.rest (by simp [roundClobbers])).trans ((r8.mono (by simp [roundClobbers])).trans
      (r9.mono (by simp [roundClobbers])))))))))

theorem redRoundsWith_ok (K : RowKernel) (s : State) (h : RedInv m0 base size out a mod M n inv 0 s) :
    WP isa (redRoundsWith K.code) s fun t => RedInv m0 base size out a mod M n inv n t ∧ Rest roundClobbers s t := by
  have hn := h.env.count
  let loopInv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧
    RedInv m0 base size out a mod M n inv i t ∧ Rest roundClobbers s t
  unfold redRoundsWith
  refine WP.loop (M := isa) loopInv ?_ n s ?_
  · intro k t hk
    obtain ⟨i, hik, hk, hi, rest⟩ := hk
    refine WP.mono (redRoundWith_ok K t hi (by omega)) ?_
    rintro u ⟨hu, hz, ru⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu, rest.trans ru⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu, rest.trans ru⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · exact ⟨0, by omega, by omega, h, Rest.refl _ _⟩

theorem sqReduceWith_ok (K : RowKernel) (s : State) (h : ProdInv m0 base size out a mod M n inv s) :
    WP isa (sqReduceWith K.code) s fun t => RedInv m0 base size out a mod M n inv n t ∧ Rest roundClobbers s t := by
  rw [sqReduceWith, WP.seq_iff]
  refine WP.mono (sqReduceInit_ok s h) ?_
  rintro u ⟨hu, ru⟩
  exact WP.mono (redRoundsWith_ok K u hu) fun t ⟨ht, rt⟩ => ⟨ht, ru.trans rt⟩

end
end VG.Proof.Bignum.Arm
