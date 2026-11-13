module

public import VerifiedGarbage.Impl.Bignum.Arm.MaskRow
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Bignum.Arm.MaskRow
meta import VerifiedGarbage.Proof.Bignum.Arm.RowState
meta import VerifiedGarbage.Proof.Bignum.Arm.AddCarry
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Mem

/-! # The masked-add row on ARMv7

`maskRow_ok`: `maskRow` is `row` for a scalar of `0` or `1`, from the mask `r1` (`0` or all
ones), with `row`'s pointers, count and carry (`RowCtx`). `maskRow_ct`: its addresses and
branches depend only on `r0`, `r12`, `lr` and `r7`–`r9`.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp wp_mov wp_subs op2_imm op2_reg ofNat_beq_zero dpVal)

/-- What `maskRow` may change: its pointers, count, carry and scratch. -/
abbrev maskRowClobbers : List Reg := [.r0, .r2, .r3, .r4, .r10, .r11, .r12, .lr]

/-- The mask's multiplier: `1` for all ones, `0` for zero. -/
abbrev mbit (m : BitVec 32) : BitVec 32 := BitVec.ofNat 32 (m.toNat / (2 ^ 32 - 1))

theorem mbit_toNat (m : BitVec 32) : (mbit m).toNat = m.toNat / (2 ^ 32 - 1) := by
  have := m.isLt
  simp only [mbit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- A word ANDed with the mask is the multiplier times the word. -/
theorem and_mask {m : BitVec 32} (hm : m = 0 ∨ m = BitVec.allOnes 32) (w : BitVec 32) :
    (w &&& m).toNat = (mbit m).toNat * w.toNat := by
  rw [mbit_toNat]
  rcases hm with rfl | rfl
  · simp
  · rw [BitVec.and_allOnes, BitVec.toNat_allOnes]; simp

/-- After `i` words. -/
structure MaskRowInv (s0 : State) (base : BitVec 32) (o b n i : Nat) (s : State) : Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  inPtr : s.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  zero : s.gpr .r10 = 0
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : val32 s.mem (State.addr base) o i + 2 ^ (32 * i) * (s.gpr .r11).toNat =
    val32 s0.mem (State.addr base) o i + (mbit (s0.gpr .r1)).toNat * val32 s0.mem (State.addr base) b i +
      (s0.gpr .r11).toNat
  rest : Rest maskRowClobbers s0 s

/-- `adds; adc` twice: the sum of three words as a word and a carry. -/
theorem add3 (A M c : BitVec 32) :
    (A + M + c).toNat + ((0 : BitVec 32) + 0 + (if decide (2 ^ 32 ≤ A.toNat + M.toNat) then 1 else 0) + 0 +
      (if decide (2 ^ 32 ≤ (A + M).toNat + c.toNat) then 1 else 0)).toNat * 2 ^ 32 =
      A.toNat + M.toNat + c.toNat := by
  have := A.isLt; have := M.isLt; have := c.isLt
  have e1 := BitVec.toNat_add (A + M) c
  have e2 := BitVec.toNat_add A M
  have k00 : ((0 : BitVec 32) + 0 + 0 + 0 + 0).toNat = 0 := rfl
  have k01 : ((0 : BitVec 32) + 0 + 0 + 0 + 1).toNat = 1 := rfl
  have k10 : ((0 : BitVec 32) + 0 + 1 + 0 + 0).toNat = 1 := rfl
  have k11 : ((0 : BitVec 32) + 0 + 1 + 0 + 1).toNat = 2 := rfl
  by_cases h1 : 2 ^ 32 ≤ A.toNat + M.toNat <;> by_cases h2 : 2 ^ 32 ≤ (A + M).toNat + c.toNat <;>
    simp only [h1, h2, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true, k00, k01, k10, k11]
  all_goals omega

/-- One word of the row. -/
theorem maskWord_ok {s0 s : State} {base : BitVec 32} {size o b n i : Nat}
    (ctx : RowCtx s0 base size o b n) (inv : MaskRowInv s0 base o b n i s) (hi : i < n)
    (hm : s0.gpr .r1 = 0 ∨ s0.gpr .r1 = BitVec.allOnes 32) :
    WP isa (.block maskWord) s fun t => MaskRowInv s0 base o b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hn := ctx.nowrap
  have rd : ∀ d, d + 4 ≤ size → InRegions (s.rd ++ s.wr) (off (State.addr base) d) 4 := fun d hd => by
    rcases row_writable ctx inv.rest.wr hd with ⟨R, hR, hsub⟩
    exact ⟨R, List.mem_append_right _ hR, hsub⟩
  have r1s : s.gpr .r1 = s0.gpr .r1 := inv.rest.gpr _ (by decide)
  simp only [maskWord]
  refine wp_ldr (by decide) (row_addr (d := b + 4 * i) ctx inv.inPtr (by omega)) (rd _ (by omega)) fun s1 u1 => ?_
  refine wp_ldr (a := off (State.addr base) (o + 4 * i)) (by decide)
    (by rw [u1.other _ (by decide)]; exact row_addr (d := o + 4 * i) ctx inv.outPtr (by omega))
    (by rw [u1.rd, u1.wr]; exact rd _ (by omega)) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_adds (op2_reg _ _) fun s4 u4 c4 => ?_
  refine wp_adc (op2_imm (by decide)) fun s5 u5 c5 => ?_
  refine wp_adds (op2_reg _ _) fun s6 u6 c6 => ?_
  refine wp_adc (op2_imm (by decide)) fun s7 u7 c7 => ?_
  have p7 : s7.gpr .r0 = s.gpr .r0 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have wr7 : s7.wr = s0.wr := by
    rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact inv.rest.wr
  refine wp_str (by decide) (by rw [p7]; exact row_addr (d := o + 4 * i) ctx inv.outPtr (by omega))
    (row_writable ctx wr7 (by omega)) fun s8 u8 => ?_
  refine wp_dp (op2_imm (by decide)) fun s9 u9 => ?_
  refine wp_dp (op2_imm (by decide)) fun s10 u10 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u11 z11 => WP.block_nil ?_
  -- The word's value.
  have m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have r3t : t.gpr .r3 = s7.gpr .r3 := by
    rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.gpr]
  have r11t : t.gpr .r11 = s7.gpr .r11 := by
    rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), u8.gpr]
  have mt : t.mem = s.mem.writeW (off (State.addr base) (o + 4 * i)) (t.gpr .r3) := by
    rw [u11.mem, u10.mem, u9.mem, u8.mem, m7, r3t]
  have hv : (t.gpr .r3).toNat + (t.gpr .r11).toNat * 2 ^ 32 =
      (mbit (s0.gpr .r1)).toNat * w32 s.mem (State.addr base) (b + 4 * i) +
        w32 s.mem (State.addr base) (o + 4 * i) + (s.gpr .r11).toNat := by
    have e3 : s3.gpr .r2 = s.mem.readW (off (State.addr base) (b + 4 * i)) 32 &&& s0.gpr .r1 := by
      rw [u3.gpr, dpVal, u2.other _ (by decide), u1.gpr, u2.other _ (by decide), u1.other _ (by decide), r1s]
    have e2 : s3.gpr .r3 = s.mem.readW (off (State.addr base) (o + 4 * i)) 32 := by
      rw [u3.other _ (by decide), u2.gpr, u1.mem]
    have e10 : s4.gpr .r10 = 0 := by
      rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), inv.zero]
    have e11 : s5.gpr .r11 = s.gpr .r11 := by
      rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
        u1.other _ (by decide)]
    rw [r3t, r11t, u7.gpr, u7.other _ (by decide), c6, u6.gpr, u6.other _ (by decide), u5.gpr,
      u5.other _ (by decide), e11, c4, e10, u4.gpr, e2, e3, add3]
    simp only [w32]
    rw [← and_mask hm (s.mem.readW (off (State.addr base) (b + 4 * i)) 32)]
    omega
  obtain ⟨outside, value⟩ := row_value_step_of (x := mbit (s0.gpr .r1)) ctx inv.outside inv.value hi mt hv
  have keep : ∀ r, r ∉ ([.r2, .r3, .r4, .r11] : List Reg) → s8.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u8.gpr, u7.other _ hr.2.2.2, u6.other _ hr.2.1, u5.other _ hr.2.2.1, u4.other _ hr.2.1, u3.other _ hr.1,
      u2.other _ hr.2.1, u1.other _ hr.1]
  have lr10 : s10.gpr .lr = BitVec.ofNat 32 (n - i) := by
    rw [u10.other _ (by decide), u9.other _ (by decide), keep .lr (by decide), inv.count]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, outside, value, ?_⟩, ?_⟩
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.gpr, dpVal, keep .r0 (by decide), inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [VG.Offset.add_add]
    congr 1
  · rw [u11.other _ (by decide), u10.gpr, dpVal, u9.other _ (by decide), keep .r12 (by decide), inv.inPtr]
    change base + BitVec.ofNat 32 (b + 4 * i) + BitVec.ofNat 32 4 = _
    rw [VG.Offset.add_add]
    congr 1
  · rw [u11.gpr, lr10]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [u11.other _ (by decide), u10.other _ (by decide), u9.other _ (by decide), keep .r10 (by decide), inv.zero]
  · exact inv.rest.trans <| (u1.rest (by simp)).trans <| (u2.rest (by simp)).trans <| (u3.rest (by simp)).trans <|
      (u4.rest (by simp)).trans <| (u5.rest (by simp)).trans <| (u6.rest (by simp)).trans <|
      (u7.rest (by simp)).trans <| (u8.rest _).trans <| (u9.rest (by simp)).trans <| (u10.rest (by simp)).trans
      (u11.rest (by simp))
  · rw [z11, lr10]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

/-- `maskRow`: `n > 0` words of `[o] += m & [b]` plus the carry, `m` all ones or zero (`r1`). -/
theorem maskRow_ok (s : State) {base : BitVec 32} {size o b n : Nat}
    (ctx : RowCtx s base size o b n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o) (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 b)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) (hm : s.gpr .r1 = 0 ∨ s.gpr .r1 = BitVec.allOnes 32) :
    WP isa maskRow s fun t =>
      t.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * n) ∧ t.gpr .r12 = base + BitVec.ofNat 32 (b + 4 * n) ∧
      Outside (State.addr base) o (4 * n) s.mem t.mem ∧ t.gpr .r1 = s.gpr .r1 ∧
      val32 t.mem (State.addr base) o n + 2 ^ (32 * n) * (t.gpr .r11).toNat =
        val32 s.mem (State.addr base) o n +
          (s.gpr .r1).toNat / (2 ^ 32 - 1) * val32 s.mem (State.addr base) b n + (s.gpr .r11).toNat ∧
      Rest maskRowClobbers s t := by
  rw [maskRow, WP.seq_iff]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => WP.block_nil ?_
  have I0 : MaskRowInv s base o b n 0 s1 :=
    ⟨Nat.zero_le _, by rw [u1.other _ (by decide), hp0]; rfl, by rw [u1.other _ (by decide), hp12]; rfl,
      by rw [u1.other _ (by decide), hcount]; rfl, u1.gpr, by rw [u1.mem]; exact Outside.refl _ _ _ _,
      by rw [u1.mem, u1.other _ (by decide)]; simp [val32], u1.rest (by simp)⟩
  refine WP.mono (WP.loop (M := isa) (Q := MaskRowInv s base o b n n)
    (fun k t => ∃ i, i + k = n ∧ 0 < k ∧ MaskRowInv s base o b n i t) ?_ n s1 ⟨0, by omega, hn, I0⟩) fun t I => ?_
  · rintro k t ⟨i, hik, hk, hi⟩
    refine WP.mono (maskWord_ok ctx hi (by omega) hm) fun u ⟨hu, hz⟩ => ?_
    by_cases he : i + 1 = n
    · exact Or.inl ⟨by change some (!u.z) = some false; simp only [hz, he, decide_true, Bool.not_true], he ▸ hu⟩
    · exact Or.inr ⟨by change some (!u.z) = some true; simp only [hz, he, decide_false, Bool.not_false],
        k - 1, by omega, i + 1, by omega, by omega, hu⟩
  refine ⟨I.outPtr, I.inPtr, I.outside, I.rest.gpr _ (by decide), ?_, I.rest⟩
  rw [I.value, mbit_toNat]

/-- `maskRow`'s addresses and branches depend only on `r0`, `r12`, `lr` and `r7`–`r9`. -/
theorem maskRow_ct : ConstantTime isa (fun _ => True)
    (fun s t => s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r12 = t.gpr .r12 ∧ s.gpr .lr = t.gpr .lr ∧
      s.gpr .r7 = t.gpr .r7 ∧ s.gpr .r8 = t.gpr .r8 ∧ s.gpr .r9 = t.gpr .r9) maskRow := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r12, .lr, .r7, .r8, .r9]) ?_ (by taint_decide)
  intro s t _ _ ⟨h0, h12, hl, h7, h8, h9⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h12
  · exact hl
  · exact h7
  · exact h8
  · exact h9

end VG.Proof.Bignum.Arm
