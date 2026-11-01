module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.Arm.RowState
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.Proof.Bignum.Arm.SubState
public import VerifiedGarbage.Proof.Bignum.Arm.SelectAliasState
public import VerifiedGarbage.Proof.Bignum.Arm.Zero
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem

/-! # The working space of `inverse` on ARMv7: arrays of the stride `S W`, numbers of `k` words

`Gk s B Z W k N`: `Ws` with `r9 = k ≤ W` in place of `W`. `nk m B W j L` is the number in the
low `L` words of array `j`.
-/

@[expose] public section

/-! ## `shr30` on ARMv7: `n + 1` words shifted right by 30 bits, as a signed number -/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rsa.Arm.Keys VG.Proof.Mont
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm (Rest Upd ofNat_beq_zero wp_ldr wp_str wp_dp wp_mov wp_subs op2_imm op2_lsl op2_lsr
  dpVal toNat_shr toNat_shl)
open VG.Proof.Bignum.Arm (RowCtx row_addr row_writable)

abbrev shrClob : List Reg := [.r0, .r1, .r2, .r12, .lr]

theorem shr_word (x y : BitVec 32) :
    2 ^ 30 * ((x >>> 30) + (y <<< 2)).toNat = x.toNat - x.toNat % 2 ^ 30 + 2 ^ 32 * (y.toNat % 2 ^ 30) := by
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hx := x.isLt
  have hy := y.isLt
  have e : x.toNat / 2 ^ 30 + y.toNat * 2 ^ 2 % 2 ^ 32 < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt e]
  omega

theorem shrStep_ok (s : State) (a a' o : Addr)
    (ha : State.addr (s.gpr .r12 + BitVec.ofNat 32 0) = a)
    (ha' : State.addr (s.gpr .r12 + BitVec.ofNat 32 4) = a')
    (ho : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = o)
    (ra : InRegions (s.rd ++ s.wr) a 4) (ra' : InRegions (s.rd ++ s.wr) a' 4) (wo : InRegions s.wr o 4) :
    WP isa (.block shrStep) s fun t =>
      2 ^ 30 * (t.gpr .r1).toNat = (s.mem.readW a 32).toNat - (s.mem.readW a 32).toNat % 2 ^ 30 +
        2 ^ 32 * ((s.mem.readW a' 32).toNat % 2 ^ 30) ∧
      t.mem = s.mem.writeW o (t.gpr .r1) ∧ t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .r12 = s.gpr .r12 + 4 ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧ Rest shrClob s t := by
  unfold shrStep
  refine wp_ldr (by decide) ha ra fun s1 u1 => ?_
  refine wp_ldr (a := a') (by decide) (by rw [u1.other .r12 (by decide), ha'])
    (by rw [u1.rd, u1.wr]; exact ra') fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => ?_
  have p0 : s4.gpr .r0 = s.gpr .r0 := by
    rw [u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  refine wp_str (a := o) (by decide) (by rw [p0]; exact ho)
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact wo) fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u8 hz => WP.block_nil ?_
  have value : t.gpr .r1 = (s.mem.readW a 32 >>> 30) + (s.mem.readW a' 32 <<< 2) := by
    rw [u8.other .r1 (by decide), u7.other .r1 (by decide), u6.other .r1 (by decide), u5.gpr, u4.gpr, dpVal,
      u3.gpr, u3.other .r2 (by decide), u2.gpr, u2.other .r1 (by decide), u1.gpr, u1.mem]
  have count : s7.gpr .lr = s.gpr .lr := by
    rw [u7.other .lr (by decide), u6.other .lr (by decide), u5.gpr, u4.other .lr (by decide),
      u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value]; exact shr_word _ _
  · rw [u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u8.other .r1 (by decide),
      u7.other .r1 (by decide), u6.other .r1 (by decide), u5.gpr]
  · rw [u8.other .r0 (by decide), u7.other .r0 (by decide), u6.gpr, dpVal, u5.gpr, p0]
  · rw [u8.other .r12 (by decide), u7.gpr, dpVal, u6.other .r12 (by decide), u5.gpr, u4.other .r12 (by decide),
      u3.other .r12 (by decide), u2.other .r12 (by decide), u1.other .r12 (by decide)]
  · rw [u8.gpr, count]
  · rw [hz, count]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      ((u5.rest _).trans ((u6.rest (by simp)).trans ((u7.rest (by simp)).trans (u8.rest (by simp))))))))

structure ShrCtx (s : State) (base : BitVec 32) (size o a n : Nat) : Prop where
  nowrap : base.toNat + size ≤ 2 ^ 32
  outFits : o + 4 * (n + 1) ≤ size
  inFits : a + 4 * (n + 1) ≤ size
  separate : o + 4 * (n + 1) ≤ a ∨ a + 4 * (n + 1) ≤ o
  writable : (⟨State.addr base, size⟩ : Region) ∈ s.wr

structure ShrInv (s0 : State) (base : BitVec 32) (o a n i : Nat) (s : State) : Prop where
  index : i ≤ n
  outPtr : s.gpr .r0 = base + BitVec.ofNat 32 (o + 4 * i)
  inPtr : s.gpr .r12 = base + BitVec.ofNat 32 (a + 4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  outside : Outside (State.addr base) o (4 * i) s0.mem s.mem
  value : 2 ^ 30 * val32 s.mem (State.addr base) o i + w32 s0.mem (State.addr base) a % 2 ^ 30 =
    val32 s0.mem (State.addr base) a i + 2 ^ (32 * i) * (w32 s0.mem (State.addr base) (a + 4 * i) % 2 ^ 30)
  rest : Rest shrClob s0 s

theorem ShrCtx.addr {s0 s : State} {base : BitVec 32} {size o a n d : Nat} (ctx : ShrCtx s0 base size o a n)
    {r : Reg} {k : Nat} (hr : s.gpr r = base + BitVec.ofNat 32 d) (hd : d + k < size) :
    State.addr (s.gpr r + BitVec.ofNat 32 k) = off (State.addr base) (d + k) := by
  rw [hr, Offset.add_add]
  exact VG.Arm.addr_add (by have := ctx.nowrap; omega)

theorem ShrCtx.wr {s0 s : State} {base : BitVec 32} {size o a n d : Nat} (ctx : ShrCtx s0 base size o a n)
    (hr : s.wr = s0.wr) (hd : d + 4 ≤ size) : InRegions s.wr (off (State.addr base) d) 4 := by
  rw [hr]
  exact ⟨_, ctx.writable, Offset.contains_base _ hd (by have := ctx.nowrap; omega)⟩

theorem ShrCtx.rd {s0 s : State} {base : BitVec 32} {size o a n d : Nat} (ctx : ShrCtx s0 base size o a n)
    (hr : s.wr = s0.wr) (hd : d + 4 ≤ size) : InRegions (s.rd ++ s.wr) (off (State.addr base) d) 4 := by
  obtain ⟨R, hR, h⟩ := ctx.wr hr hd
  exact ⟨R, List.mem_append_right _ hR, h⟩

theorem shrBody_ok {s0 s : State} {base : BitVec 32} {size o a n i : Nat}
    (ctx : ShrCtx s0 base size o a n) (inv : ShrInv s0 base o a n i s) (hi : i < n) :
    WP isa (.block shrStep) s fun t => ShrInv s0 base o a n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hn := ctx.nowrap
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hs := ctx.separate
  refine WP.mono (shrStep_ok s _ _ _ (ctx.addr inv.inPtr (by omega))
    (ctx.addr inv.inPtr (by omega)) (ctx.addr inv.outPtr (by omega))
    (ctx.rd inv.rest.wr (by omega)) (ctx.rd inv.rest.wr (by omega)) (ctx.wr inv.rest.wr (by omega))) ?_
  rintro t ⟨hv, hm, p0, p12, plr, hz, hr⟩
  simp only [Nat.add_zero] at hv hm
  have src := inv.outside.w32 (d := a + 4 * i) (by omega) (by omega)
  have src' := inv.outside.w32 (d := a + 4 * i + 4) (by omega) (by omega)
  change 2 ^ 30 * (t.gpr .r1).toNat = w32 s.mem (State.addr base) (a + 4 * i) -
      w32 s.mem (State.addr base) (a + 4 * i) % 2 ^ 30 + 2 ^ 32 * (w32 s.mem (State.addr base) (a + 4 * i + 4) % 2 ^ 30)
    at hv
  rw [src, src'] at hv
  have wr := writeW32_outside s.mem (State.addr base) (d := o + 4 * i) (t.gpr .r1) (by omega)
  rw [← hm] at wr
  have low := wr.val32 (d := o) (k := i) (by omega) (by omega)
  have top : w32 t.mem (State.addr base) (o + 4 * i) = (t.gpr .r1).toNat := by rw [hm, w32_write_self]
  refine ⟨⟨by omega, ?_, ?_, ?_, (inv.outside.mono (Nat.le_refl _) (by omega)).trans
      (wr.mono (by omega) (by omega)), ?_, inv.rest.trans hr⟩, ?_⟩
  · rw [p0, inv.outPtr]
    change base + BitVec.ofNat 32 (o + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]; congr 2
  · rw [p12, inv.inPtr]
    change base + BitVec.ofNat 32 (a + 4 * i) + BitVec.ofNat 32 4 = _
    rw [Offset.add_add]; congr 2
  · rw [plr, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), Nat.sub_sub]
  · rw [val32_succ, val32_succ, low, top, pow32_succ, show a + 4 * (i + 1) = a + 4 * i + 4 by omega]
    have prior := inv.value
    have hx := Nat.div_add_mod (w32 s0.mem (State.addr base) (a + 4 * i)) (2 ^ 30)
    generalize 2 ^ (32 * i) = P at *
    generalize w32 s0.mem (State.addr base) (a + 4 * i) = x at *
    generalize w32 s0.mem (State.addr base) (a + 4 * i + 4) = y at *
    generalize (t.gpr .r1).toNat = T at *
    have e1 : 2 ^ 30 * (P * T) = P * (2 ^ 30 * T) := by rw [Nat.mul_left_comm]
    have e2 : P * (x - x % 2 ^ 30 + 2 ^ 32 * (y % 2 ^ 30)) = P * (x - x % 2 ^ 30) + 2 ^ 32 * P * (y % 2 ^ 30) := by
      rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_assoc]
    have e3 : P * (x - x % 2 ^ 30) + P * (x % 2 ^ 30) = P * x := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [Nat.mul_add, e1, hv, e2]
    omega
  · rw [hz, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]; omega

theorem shr_top_word (x : BitVec 32) :
    ((x >>> 30) - ((x >>> 31) <<< 2)).toNat = x.toNat / 2 ^ 30 + if 2 ^ 31 ≤ x.toNat then 2 ^ 32 - 4 else 0 := by
  have hx := x.isLt
  have a : (x >>> 30).toNat = x.toNat / 2 ^ 30 := toNat_shr x 30
  have b : (x >>> 31).toNat = x.toNat / 2 ^ 31 := toNat_shr x 31
  have c : ((x >>> 31) <<< 2).toNat = x.toNat / 2 ^ 31 * 4 := by
    rw [toNat_shl, b]; omega
  rw [BitVec.toNat_sub, a, c]
  split <;> omega

theorem shrTop_ok (s : State) (a o : Addr)
    (ha : State.addr (s.gpr .r12 + BitVec.ofNat 32 0) = a) (ho : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = o)
    (ra : InRegions (s.rd ++ s.wr) a 4) (wo : InRegions s.wr o 4) :
    WP isa (.block shrTop) s fun t =>
      (t.gpr .r2).toNat = (s.mem.readW a 32).toNat / 2 ^ 30 +
        (if 2 ^ 31 ≤ (s.mem.readW a 32).toNat then 2 ^ 32 - 4 else 0) ∧
      t.mem = s.mem.writeW o (t.gpr .r2) ∧ Rest shrClob s t := by
  unfold shrTop
  refine wp_ldr (by decide) ha ra fun s1 u1 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s2 u2 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s4 u4 => ?_
  refine wp_str (a := o) (by decide) (by rw [u4.other .r0 (by decide), u3.other .r0 (by decide),
    u2.other .r0 (by decide), u1.other .r0 (by decide)]; exact ho)
    (by rw [u4.wr, u3.wr, u2.wr, u1.wr]; exact wo) fun t u5 => WP.block_nil ?_
  have v : t.gpr .r2 = (s.mem.readW a 32 >>> 30) - ((s.mem.readW a 32 >>> 31) <<< 2) := by
    rw [u5.gpr, u4.gpr, dpVal, u3.other .r2 (by decide), u2.gpr, u3.gpr, u2.other .r1 (by decide), u1.gpr]
  refine ⟨by rw [v]; exact shr_top_word _, ?_, ?_⟩
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u5.gpr]
  · exact (u1.rest (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      (u5.rest _))))

/-- The final arithmetic: the shifted words and the top. -/
theorem shr_final {P W X x T r0 rn : Nat} (hW : W < P) (hx : x < 2 ^ 32)
    (inv : 2 ^ 30 * W + r0 = X + P * rn) (hr0 : r0 < 2 ^ 30) (hrn : rn = x % 2 ^ 30)
    (hT : T = x / 2 ^ 30 + if 2 ^ 31 ≤ x then 2 ^ 32 - 4 else 0) :
    W + P * T = ((X + P * x + 2 ^ 32 * P * (if 2 ^ 31 ≤ x then 2 ^ 32 - 1 else 0)) / 2 ^ 30) % (2 ^ 32 * P) := by
  have hq := Nat.div_add_mod x (2 ^ 30)
  have hq3 : x / 2 ^ 30 ≤ 3 := by omega
  have px : P * x = 2 ^ 30 * (P * (x / 2 ^ 30)) + P * (x % 2 ^ 30) := by
    rw [Nat.mul_left_comm, ← Nat.mul_add, hq]
  have hA : P * (x / 2 ^ 30) ≤ 3 * P := by rw [Nat.mul_comm 3]; exact Nat.mul_le_mul_left _ hq3
  have hQ : 2 ^ 32 * P = 2 ^ 30 * (4 * P) := by rw [← Nat.mul_assoc]
  generalize hAd : P * (x / 2 ^ 30) = A at *
  subst hrn
  generalize P * (x % 2 ^ 30) = R at *
  generalize hQd : 2 ^ 32 * P = Q at *
  have e : X + P * x = 2 ^ 30 * (W + A) + r0 := by omega
  split at hT
  · rename_i hs
    simp only [hs, ↓reduceIte]
    have hPT : P * T = A + (Q - 4 * P) := by
      rw [hT, Nat.mul_add, hAd, Nat.mul_sub, Nat.mul_comm P (2 ^ 32), hQd, Nat.mul_comm P 4]
    have e2 : X + P * x + Q * (2 ^ 32 - 1) = 2 ^ 30 * (W + A + (Q - 4 * P) + 3 * Q) + r0 := by
      have : Q * (2 ^ 32 - 1) = 2 ^ 30 * (4 * P) * (2 ^ 32 - 1) := by rw [hQ]
      have h4 : 4 * P * (2 ^ 32 - 1) = (Q - 4 * P) + 3 * Q := by
        rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm (4 * P), ← Nat.mul_assoc, Nat.mul_comm (2 ^ 32) 4,
          Nat.mul_assoc, hQd]
        have : 4 * P ≤ Q := by omega
        omega
      rw [this, Nat.mul_assoc, h4, e]; omega
    rw [e2, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hr0, Nat.add_zero, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega), hPT]; omega
  · rename_i hs
    simp only [hs, ↓reduceIte, Nat.mul_zero, Nat.add_zero] at hT ⊢
    have hPT : P * T = A := by rw [hT, hAd]
    have h1 : x / 2 ^ 30 ≤ 1 := by omega
    have hA1 : A ≤ P := by rw [← hAd]; exact Nat.le_trans (Nat.mul_le_mul_left _ h1) (by omega)
    rw [e, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hr0, Nat.add_zero, Nat.mod_eq_of_lt (by omega), hPT]

/-- `shr30`: `n + 1` words at `base + o` := the `n + 1` words at `base + a`, as a signed number (its
sign word appended, all ones if negative), shifted right by 30 bits. -/
theorem shr30_ok (s : State) {base : BitVec 32} {size o a n : Nat}
    (ctx : ShrCtx s base size o a n) (hn : 0 < n)
    (hp0 : s.gpr .r0 = base + BitVec.ofNat 32 o) (hp12 : s.gpr .r12 = base + BitVec.ofNat 32 a)
    (hcount : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa shr30 s fun t =>
      Outside (State.addr base) o (4 * (n + 1)) s.mem t.mem ∧
      val32 t.mem (State.addr base) o (n + 1) =
        ((val32 s.mem (State.addr base) a (n + 1) + 2 ^ (32 * (n + 1)) *
          (if 2 ^ 31 ≤ w32 s.mem (State.addr base) (a + 4 * n) then 2 ^ 32 - 1 else 0)) / 2 ^ 30) %
          2 ^ (32 * (n + 1)) ∧
      Rest shrClob s t := by
  have hN := ctx.nowrap
  have ho := ctx.outFits
  have hb := ctx.inFits
  have hs := ctx.separate
  unfold shr30
  rw [WP.seq_iff]
  refine WP.mono (Q := fun t => ShrInv s base o a n n t) (WP.loop (M := isa)
    (fun k t => ∃ i, i + k = n ∧ 0 < k ∧ ShrInv s base o a n i t) ?_ n s ⟨0, by omega, hn, by omega,
      by simpa using hp0, by simpa using hp12, by simpa using hcount, Outside.refl _ _ _ _,
      by simp [val32], Rest.refl _ _⟩) ?_
  · rintro k t ⟨i, hik, hk, hi⟩
    refine WP.mono (shrBody_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · exact Or.inl ⟨by change some (!u.z) = some false; simp only [hz, he, decide_true, Bool.not_true], he ▸ hu⟩
    · exact Or.inr ⟨by change some (!u.z) = some true; simp only [hz, he, decide_false, Bool.not_false],
        k - 1, by omega, i + 1, by omega, by omega, hu⟩
  · intro t inv
    refine WP.mono (shrTop_ok t _ _ (ctx.addr inv.inPtr (by omega)) (ctx.addr inv.outPtr (by omega))
      (ctx.rd inv.rest.wr (by omega)) (ctx.wr inv.rest.wr (by omega))) ?_
    rintro u ⟨hv, hm, hr⟩
    simp only [Nat.add_zero] at hv hm
    have src := inv.outside.w32 (d := a + 4 * n) (by omega) (by omega)
    change (u.gpr .r2).toNat = w32 t.mem (State.addr base) (a + 4 * n) / 2 ^ 30 +
      (if 2 ^ 31 ≤ w32 t.mem (State.addr base) (a + 4 * n) then 2 ^ 32 - 4 else 0) at hv
    rw [src] at hv
    have wr := writeW32_outside t.mem (State.addr base) (d := o + 4 * n) (u.gpr .r2) (by omega)
    rw [← hm] at wr
    have low := wr.val32 (d := o) (k := n) (by omega) (by omega)
    have top : w32 u.mem (State.addr base) (o + 4 * n) = (u.gpr .r2).toNat := by rw [hm, w32_write_self]
    refine ⟨(inv.outside.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega)), ?_,
      inv.rest.trans hr⟩
    rw [val32_succ, val32_succ, low, top, pow32_succ, Nat.mul_comm (2 ^ (32 * n)) (w32 s.mem _ _)]
    have := shr_final (P := 2 ^ (32 * n)) (val32_lt _ _ _ _)
      (BitVec.isLt _) inv.value (Nat.mod_lt _ (by decide)) rfl hv
    rw [Nat.mul_comm (w32 s.mem _ _)]
    exact this

end VG.Proof.Rsa.Arm.Inv

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm (Rest Upd)
open VG.Proof.Bignum.Arm (SubCtx SelectCtx RowCtx ZeroCtx)

structure Gk (s : State) (B : BitVec 32) (Z W k N : Nat) : Prop where
  nowrap : B.toNat + Z ≤ 2 ^ 32
  writable : (⟨State.addr B, Z⟩ : Region) ∈ s.wr
  fits : arr W N ≤ Z
  kpos : 0 < k
  kle : k ≤ W
  wle : W ≤ 1024
  r7 : s.gpr .r7 = BitVec.ofNat 32 (S W)
  r8 : s.gpr .r8 = B
  r9 : s.gpr .r9 = BitVec.ofNat 32 k

/-- The low `L` words of array `j`. -/
abbrev nk (m : Mem) (B : BitVec 32) (W j L : Nat) : Nat := val32 m (State.addr B) (arr W j) L

theorem Gk.of {s t : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N)
    (e7 : t.gpr .r7 = s.gpr .r7) (e8 : t.gpr .r8 = s.gpr .r8) (e9 : t.gpr .r9 = s.gpr .r9)
    (wr : t.wr = s.wr) : Gk t B Z W k N :=
  ⟨h.nowrap, wr ▸ h.writable, h.fits, h.kpos, h.kle, h.wle, e7.trans h.r7, e8.trans h.r8, e9.trans h.r9⟩

theorem Gk.rest {s t : State} {B : BitVec 32} {Z W k N : Nat} {ws : List Reg} (h : Gk s B Z W k N)
    (r : Rest ws s t) (h7 : .r7 ∉ ws := by decide) (h8 : .r8 ∉ ws := by decide)
    (h9 : .r9 ∉ ws := by decide) : Gk t B Z W k N :=
  h.of (r.gpr _ h7) (r.gpr _ h8) (r.gpr _ h9) r.wr

theorem Gk.arr_fit {s : State} {B : BitVec 32} {Z W k N j : Nat} (h : Gk s B Z W k N) (hj : j < N) :
    arr W j + S W ≤ Z := Nat.le_trans (arr_end hj) h.fits

theorem Gk.fit64 {s : State} {B : BitVec 32} {Z W k N j : Nat} (h : Gk s B Z W k N) (hj : j < N) :
    arr W j + S W ≤ 2 ^ 64 := by
  have := h.arr_fit hj; have := h.nowrap; omega

theorem Gk.addr {s : State} {B : BitVec 32} {Z W k N d : Nat} (h : Gk s B Z W k N) (hd : d < Z) :
    State.addr (B + BitVec.ofNat 32 d) = off (State.addr B) d :=
  VG.Arm.addr_add (by have := h.nowrap; omega)

theorem Gk.write {s : State} {B : BitVec 32} {Z W k N d : Nat} (h : Gk s B Z W k N) (hd : d + 4 ≤ Z) :
    InRegions s.wr (off (State.addr B) d) 4 :=
  ⟨_, h.writable, Offset.contains_base _ hd (by have := h.nowrap; omega)⟩

theorem Gk.read {s : State} {B : BitVec 32} {Z W k N d : Nat} (h : Gk s B Z W k N) (hd : d + 4 ≤ Z) :
    InRegions (s.rd ++ s.wr) (off (State.addr B) d) 4 := by
  obtain ⟨R, hR, hsub⟩ := h.write hd
  exact ⟨R, List.mem_append_right _ hR, hsub⟩

/-- `ptr r j` under `Gk`. -/
theorem Gk.ptr_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) {r : Reg}
    (hr : r ∉ [.r7, .r8, .r9]) {j : Nat} (hj : j < 256) {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, t.gpr r = B + BitVec.ofNat 32 (arr W j) → Rest [r] s t → t.mem = s.mem →
      Gk t B Z W k N → WP isa (.block rest) t Q) :
    WP isa (.block (ptr r j ++ rest)) s Q := by
  have r7 : r ≠ .r7 := fun e => hr (by simp [e])
  have r8 : r ≠ .r8 := fun e => hr (by simp [e])
  have r9 : r ≠ .r9 := fun e => hr (by simp [e])
  refine ptr_regs_ok r7 r8 hj h.r7 h.r8 fun t p rest mem => ?_
  exact kk t p rest mem (h.rest rest (by simpa using r7.symm)
    (by simpa using r8.symm) (by simpa using r9.symm))

/-- Three pointers. -/
theorem Gk.ptr3_ok {s : State} {B : BitVec 32} {Z W k N o a b : Nat} (h : Gk s B Z W k N)
    (ho : o < 256) (ha : a < 256) (hb : b < 256) {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, t.gpr .r0 = B + BitVec.ofNat 32 (arr W o) → t.gpr .r10 = B + BitVec.ofNat 32 (arr W a) →
      t.gpr .r12 = B + BitVec.ofNat 32 (arr W b) → Rest [.r0, .r10, .r12] s t → t.mem = s.mem →
      Gk t B Z W k N → WP isa (.block rest) t Q) :
    WP isa (.block (ptr .r0 o ++ ptr .r10 a ++ ptr .r12 b ++ rest)) s Q := by
  simp only [List.append_assoc]
  refine h.ptr_ok (by decide) ho fun s1 p1 r1 m1 h1 => ?_
  refine h1.ptr_ok (by decide) ha fun s2 p2 r2 m2 h2 => ?_
  refine h2.ptr_ok (by decide) hb fun t p3 r3 m3 h3 => ?_
  refine kk t ?_ ?_ p3 ((r1.mono (by simp)).trans ((r2.mono (by simp)).trans (r3.mono (by simp))))
    (m3.trans (m2.trans m1)) h3
  · rw [r3.gpr _ (by decide), r2.gpr _ (by decide), p1]
  · rw [r3.gpr _ (by decide), p2]

/-! ## Contexts of the word loops, for arrays and `L ≤ W + 1` words -/

theorem Gk.subCtx {s : State} {B : BitVec 32} {Z W k N o a b L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hoa : o ≠ a) (hob : o ≠ b) (hL : L ≤ W + 2) :
    SubCtx s B Z (arr W o) (arr W a) (arr W b) L := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have da := arr_disj (w := W) hoa
  have db := arr_disj (w := W) hob
  have hS : S W = 4 * (W + 2) := rfl
  exact ⟨h.nowrap, by omega, by omega, by omega, by omega, by omega, h.writable⟩

theorem Gk.selCtx {s : State} {B : BitVec 32} {Z W k N o a b L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hb : b < N) (hL : L ≤ W + 2) :
    SelectCtx s B Z (arr W o) (arr W a) (arr W b) L := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have fb := h.arr_fit hb
  have hS : S W = 4 * (W + 2) := rfl
  refine ⟨h.nowrap, by omega, by omega, by omega, ?_, ?_, h.writable⟩
  · by_cases e : o = a
    · exact .inr (.inr (by rw [e]))
    · have := arr_disj (w := W) e; omega
  · by_cases e : o = b
    · exact .inr (.inr (by rw [e]))
    · have := arr_disj (w := W) e; omega

theorem Gk.rowCtx {s : State} {B : BitVec 32} {Z W k N o b L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (hb : b < N) (hob : o ≠ b) (hL : L ≤ W + 2) :
    RowCtx s B Z (arr W o) (arr W b) L := by
  have fo := h.arr_fit ho
  have fb := h.arr_fit hb
  have db := arr_disj (w := W) hob
  have hS : S W = 4 * (W + 2) := rfl
  exact ⟨h.nowrap, by omega, by omega, by omega, h.writable⟩

theorem Gk.shrCtx {s : State} {B : BitVec 32} {Z W k N o a L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (ha : a < N) (hoa : o ≠ a) (hL : L + 1 ≤ W + 2) :
    ShrCtx s B Z (arr W o) (arr W a) L := by
  have fo := h.arr_fit ho
  have fa := h.arr_fit ha
  have da := arr_disj (w := W) hoa
  have hS : S W = 4 * (W + 2) := rfl
  exact ⟨h.nowrap, by omega, by omega, by omega, h.writable⟩

theorem Gk.zeroCtx {s : State} {B : BitVec 32} {Z W k N o L : Nat} (h : Gk s B Z W k N)
    (ho : o < N) (hL : L ≤ W + 2) : ZeroCtx s B Z (arr W o) L := by
  have fo := h.arr_fit ho
  have hS : S W = 4 * (W + 2) := rfl
  exact ⟨h.nowrap, by omega, ⟨_, h.writable, Region.contains_self _ _⟩⟩

/-! ## Frames at a width -/

/-- The low `L ≤ W + 2` words of an array outside the frame. -/
theorem Keep.nk {B : BitVec 32} {W : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B W js ds m m') {j L : Nat} (hL : L ≤ W + 2) (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : arr W j + S W ≤ 2 ^ 64) : nk m' B W j L = nk m B W j L := by
  refine Outs.val32 h (fun r hr => ?_) (by simp only [S] at fit; omega)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨k, hk, rfl⟩ | ⟨d, hd', rfl⟩
  · have := arr_disj (w := W) (hj k hk); dsimp only; simp only [S] at *; omega
  · have := hd d hd'; have : hdr ≤ arr W j := Nat.le_add_right _ _; dsimp only; omega

/-- An array's low `L` words from a frame of its other words. -/
theorem Outside.nk {B : BitVec 32} {W j L d n : Nat} {m m' : Mem}
    (h : Outside (State.addr B) (arr W j + d) n m m') (hL : 4 * L ≤ d) (fit : arr W j + 4 * L ≤ 2 ^ 64) :
    nk m' B W j L = nk m B W j L :=
  h.val32 (by omega) fit

end VG.Proof.Rsa.Arm.Inv
