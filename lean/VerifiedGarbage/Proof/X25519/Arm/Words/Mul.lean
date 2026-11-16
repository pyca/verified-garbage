module

public import VerifiedGarbage.Proof.X25519.Arm.Words.Chain
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on 32-bit ARM with `umaal`: multiplication

The fold at bit 255 (`fold19_ok`), for any registers, and `mul` (`mul_ok`):
after `i` rows the words of `ACC` below `i` and the eight registers
`rg (i + 1 + j)` hold `a_{<i} · b` (`RowInv`); `lo + 38 hi` and the fold
leave a number below `2p`, congruent to the product.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Words

open VG VG.Arm VG.Impl.X25519.Arm.Words
open VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)
open VG.Proof.X25519 (fold255 fold256)

/-! ## The registers of a product -/

theorem rg_mod (n : Nat) : rg n = rg (n % 9) := by simp only [rg, Nat.mod_mod]

theorem rg_inj9 : ∀ i < 9, ∀ j < 9, rg i = rg j → i = j := by decide

theorem rg_eq {m n : Nat} (h : rg m = rg n) : m % 9 = n % 9 :=
  rg_inj9 _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) ((rg_mod m).symm.trans (h.trans (rg_mod n)))

theorem rg_of_mod {m n : Nat} (h : m % 9 = n % 9) : rg m = rg n := by rw [rg_mod m, rg_mod n, h]

theorem rg_ne9 : ∀ i < 9, Reg.r0 ≠ rg i ∧ Reg.r1 ≠ rg i ∧ Reg.r2 ≠ rg i ∧ Reg.r12 ≠ rg i ∧ Reg.lr ≠ rg i := by
  decide

theorem rg_ne (n : Nat) : Reg.r0 ≠ rg n ∧ Reg.r1 ≠ rg n ∧ Reg.r2 ≠ rg n ∧ Reg.r12 ≠ rg n ∧ Reg.lr ≠ rg n := by
  rw [rg_mod n]; exact rg_ne9 _ (Nat.mod_lt _ (by decide))

/-! ## The fold at bit 255 -/

theorem toNat_bic31 (x : BitVec 32) : (x &&& ~~~(0x80000000 : BitVec 32)).toNat = x.toNat % 2 ^ 31 := by
  rw [show ~~~(0x80000000 : BitVec 32) = 0x7fffffff by decide, BitVec.toNat_and,
    show (0x7fffffff : BitVec 32).toNat = 2 ^ 31 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number `x + 2²⁵⁶ c` with bit 255 and above folded in as 19 times
itself. -/
theorem fold19_num {x : Nat → Nat} (hx : x 7 < 2 ^ 32) (hlo : val32 x 7 < 2 ^ 224) {cv : Nat} (hcv : cv < 2 ^ 26)
    {r c8 : Nat}
    (h : r + 2 ^ 256 * c8 = val32 (fun k => if k = 7 then x 7 % 2 ^ 31 else x k) 8 + 19 * (x 7 / 2 ^ 31 + 2 * cv)) :
    r % P = (val32 x 8 + 2 ^ 256 * cv) % P ∧ r < 2 * P := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have e7 : val32 (fun k => if k = 7 then x 7 % 2 ^ 31 else x k) 7 = val32 x 7 :=
    val32_congr fun k hk => by simp only [show k ≠ 7 by omega_arith, ite_false]
  rw [val32_succ, e7] at h
  simp only [ite_true] at h
  have hc8 : c8 = 0 := by omega_arith
  subst hc8
  have hr : r = (val32 x 7 + 2 ^ 224 * (x 7 % 2 ^ 31)) + 19 * (x 7 / 2 ^ 31 + 2 * cv) := by omega_arith
  refine ⟨?_, by omega_arith⟩
  have e8 : val32 x 8 = val32 x 7 + 2 ^ 224 * x 7 := rfl
  rw [hr, ← fold255, e8]
  congr 1
  omega_arith

theorem fold19_ok {X : Nat → Reg} {c : Reg} (hinj : ∀ i < 8, ∀ j < 8, X i = X j → i = j)
    (hX : ∀ j < 8, Reg.r12 ≠ X j ∧ Reg.lr ≠ X j ∧ c ≠ X j) (hc : c ≠ .r12 ∧ c ≠ .lr)
    {s : State} {cv : Nat} (hcv : (s.gpr c).toNat = cv) (hb : cv < 2 ^ 26) :
    WP isa (.block (fold19 X c)) s fun s' =>
      val32 (fun k => (s'.gpr (X k)).toNat) 8 % P =
        (val32 (fun k => (s.gpr (X k)).toNat) 8 + 2 ^ 256 * cv) % P ∧
      val32 (fun k => (s'.gpr (X k)).toNat) 8 < 2 * P ∧
      (∀ r, r ≠ .r12 → r ≠ .lr → (∀ j < 8, r ≠ X j) → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h7 := hX 7 (by decide)
  have hx7 := (s.gpr (X 7)).isLt
  unfold fold19
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by decide)) fun s1 u1 => wp_dp (op2_lsl (by decide)) fun s2 u2 =>
    wp_dp (op2_imm (by decide)) fun s3 u3 => wp_dp (op2_lsl (by decide)) fun s4 u4 =>
    wp_dp (op2_lsl (by decide)) fun s5 u5 => wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  -- `q` in `r12`, then `19 q`.
  have e2 : (s2.gpr .r12).toNat = (s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv := by
    rw [u2.gpr]
    show (s1.gpr .r12 + s1.gpr c <<< 1).toNat = _
    rw [u1.gpr, u1.other c hc.1, BitVec.toNat_add, toNat_shr, toNat_shl, hcv]
    omega_arith
  have e4 : (s4.gpr .lr).toNat = 3 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv) := by
    rw [u4.gpr]
    show (s3.gpr .r12 + s3.gpr .r12 <<< 1).toNat = _
    rw [u3.other _ h7.1, BitVec.toNat_add, toNat_shl, e2]
    omega_arith
  have e5 : (s5.gpr .r12).toNat = 19 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv) := by
    rw [u5.gpr]
    show (s4.gpr .lr + s4.gpr .r12 <<< 4).toNat = _
    rw [BitVec.toNat_add, toNat_shl, e4, u4.other .r12 (by decide), u3.other .r12 h7.1, e2]
    omega_arith
  have e3 : (s3.gpr (X 7)).toNat = (s.gpr (X 7)).toNat % 2 ^ 31 := by
    rw [u3.gpr]
    show (s2.gpr (X 7) &&& ~~~(0x80000000 : BitVec 32)).toNat = _
    rw [toNat_bic31, u2.other _ h7.1.symm, u1.other _ h7.1.symm]
  -- The words before the chain.
  have ex : ∀ k < 8, (s6.gpr (X k)).toNat =
      if k = 7 then (s.gpr (X 7)).toNat % 2 ^ 31 else (s.gpr (X k)).toNat := by
    intro k hk
    have hk' := hX k hk
    rw [u6.other _ hk'.2.1.symm, u5.other _ hk'.1.symm, u4.other _ hk'.2.1.symm]
    by_cases h : k = 7
    · subst h; rw [e3]; simp only [ite_true]
    · simp only [h, ite_false]
      rw [u3.other _ (fun e => h (hinj k hk 7 (by decide) e)), u2.other _ hk'.1.symm, u1.other _ hk'.1.symm]
  refine WP.mono (uchain_ok (X := X) (C := .r12) (N := .lr) (M := fun _ => .lr) (T := []) (pre := fun _ => [])
    (nv := 0) (mv := fun _ => 0)
    (xv := fun k => if k = 7 then (s.gpr (X 7)).toNat % 2 ^ 31 else (s.gpr (X k)).toNat)
    (cin := 19 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv)) (fun j hj => (hX j hj).1.symm)
    (fun _ _ => List.not_mem_nil) List.not_mem_nil hinj (by rw [u6.other _ (by decide), e5])
    fun k hk t ht => WP.block_nil ⟨?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s7 h7' => ?_
  · rw [ht.keep _ List.not_mem_nil (hX k hk).1.symm fun j hj e => absurd (hinj k hk j (Nat.lt_trans hj hk) e)
      (Nat.ne_of_gt hj)]
    exact ex k hk
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j hj => (hX j (Nat.lt_trans hj hk)).2.1, u6.gpr]; rfl
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j hj => (hX j (Nat.lt_trans hj hk)).2.1, u6.gpr]; rfl
  · have hv := uc_val8 0 (fun _ => 0)
      (fun k => if k = 7 then (s.gpr (X 7)).toNat % 2 ^ 31 else (s.gpr (X k)).toNat)
      (19 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv))
    rw [Nat.zero_mul, Nat.zero_add] at hv
    have hlo : val32 (fun k => (s.gpr (X k)).toNat) 7 < 2 ^ 224 := val32_lt fun k _ => (s.gpr (X k)).isLt
    have hn := fold19_num (x := fun k => (s.gpr (X k)).toNat) hx7 hlo hb hv
    rw [val32_congr (g := uo 0 (fun _ => 0)
      (fun k => if k = 7 then (s.gpr (X 7)).toNat % 2 ^ 31 else (s.gpr (X k)).toNat)
      (19 * ((s.gpr (X 7)).toNat / 2 ^ 31 + 2 * cv))) h7'.outs]
    refine ⟨hn.1, hn.2, fun r h12 hlr hr => ?_, ?_, ?_, ?_, ?_⟩
    · rw [h7'.keep r List.not_mem_nil h12 hr, u6.other r hlr, u5.other r h12, u4.other r hlr,
        u3.other r (hr 7 (by decide)), u2.other r h12, u1.other r h12]
    · rw [h7'.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    · rw [h7'.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
    · rw [h7'.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
    · rw [h7'.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp]

/-! ## Multiplication -/

/-- A row of a product: the low word joins `lo`, and the others and the carry
are the accumulator `t'`. -/
theorem row_num {lo lo' t t' y : Nat → Nat} {i a pa : Nat}
    (hv : val32 lo i + 2 ^ (32 * i) * val32 t 8 = pa * val32 y 8)
    (hlo : ∀ k < i, lo' k = lo k) (hi : lo' i = uo a y t 0 0)
    (ht : ∀ j < 7, t' j = uo a y t 0 (j + 1)) (h7 : t' 7 = uc a y t 0 8) :
    val32 lo' (i + 1) + 2 ^ (32 * (i + 1)) * val32 t' 8 = (pa + 2 ^ (32 * i) * a) * val32 y 8 := by
  have hc := uc_val8 a y t 0
  rw [val32_cons (uo a y t 0) 7] at hc
  have e1 : val32 lo' (i + 1) = val32 lo i + 2 ^ (32 * i) * uo a y t 0 0 := by
    rw [val32_succ, val32_congr hlo, hi]
  have e2 : val32 t' 8 = val32 (fun k => uo a y t 0 (k + 1)) 7 + 2 ^ 224 * uc a y t 0 8 := by
    rw [val32_succ, val32_congr ht, h7]
  rw [e1, e2, show 32 * (i + 1) = 32 * i + 32 by omega_arith, Nat.pow_add]
  generalize 2 ^ (32 * i) = E at *
  generalize val32 (fun k => uo a y t 0 (k + 1)) 7 = S7 at *
  generalize uo a y t 0 0 = u0 at *
  generalize uc a y t 0 8 = c8 at *
  generalize val32 y 8 = Vy at *
  generalize val32 t 8 = Vt at *
  generalize val32 lo i = L at *
  have key : E * 2 ^ 32 * (S7 + 2 ^ 224 * c8) = E * (2 ^ 32 * S7 + 2 ^ 256 * c8) := by
    rw [Nat.mul_assoc, Nat.mul_add, ← Nat.mul_assoc (2 ^ 32)]
  rw [key, Nat.add_assoc, ← Nat.mul_add, show u0 + (2 ^ 32 * S7 + 2 ^ 256 * c8) = a * Vy + Vt by omega_arith,
    Nat.mul_add, Nat.add_mul, ← hv, Nat.mul_assoc]
  omega_arith

section
variable {b : BitVec 32}

theorem zeros_ok {s : State} :
    WP isa (.block ((List.range 8).flatMap fun j => ([.mov (rg (j + 1)) (.imm 0)] : List Instr))) s fun s' =>
      (∀ j < 8, s'.gpr (rg (j + 1)) = 0) ∧ Kp s s' ∧ s'.mem = s.mem := by
  refine wp_range_flatMap (M := isa)
    (fun m s' => (∀ j < m, s'.gpr (rg (j + 1)) = 0) ∧ Kp s s' ∧ s'.mem = s.mem)
    (fun m s' hm ⟨h1, h2, h3⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _, rfl⟩
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => WP.block_nil
    ⟨fun j hj => ?_, h2.trans (Kp.of_upd u2 (rg_ne _).1), by rw [u2.mem, h3]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [u2.other _ fun e => by have := rg_eq e; omega_using [this, hj, hm]]; exact h1 j hj
  · exact u2.gpr

/-- After `i` rows of the product of `[a]` and `[c]` from `s0`: its low words
in `ACC`, and the accumulator in the registers. -/
structure RowInv (b : BitVec 32) (a c : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  kp : Kp s0 s
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 4 * i⟩] s0.mem s.mem
  val : val32 (fun k => wd s.mem (State.addr b) (ACC + 4 * k)) i +
      2 ^ (32 * i) * val32 (fun j => (s.gpr (rg (i + 1 + j))).toNat) 8 =
        val32 (fun k => wd s0.mem (State.addr b) (a + 4 * k)) i * W s0.mem (State.addr b) c

theorem mulRow_ok {a c i : Nat} (ha : a + 32 ≤ ACC) (hb : c + 32 ≤ ACC) (hi : i < 8) {s0 s : State}
    (hc : Ctx b s0) (h : RowInv b a c s0 i s) :
    WP isa (.block (mulRow a c i)) s (RowInv b a c s0 (i + 1)) := by
  have hA : ACC = 544 := rfl
  have hcs : Ctx b s := h.kp.ctx hc
  have hw : ∀ d, d + 4 ≤ ACC → wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hd])) (by omega_using [hd, hA]) (by omega_using [hi, hA])
  have r2n : ∀ n, rg n ∉ [Reg.r2] := fun n hm => (rg_ne n).2.2.1 (List.mem_singleton.mp hm).symm
  unfold mulRow
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hcs (d := a + 4 * i) (by omega_using [ha, hA, hi]) fun s1 u1 =>
    wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (rg_ne _).1)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (uchain_ok (X := fun j => rg (i + 1 + j)) (C := rg i) (N := .r1) (M := fun _ => .r2)
    (T := [.r2]) (pre := fun j => [.ldr .r2 .r0 (c + 4 * j)]) (nv := wd s0.mem (State.addr b) (a + 4 * i))
    (mv := fun j => wd s0.mem (State.addr b) (c + 4 * j)) (xv := fun j => (s.gpr (rg (i + 1 + j))).toNat)
    (cin := 0) (fun j hj e => by have := rg_eq e; omega_using [this, hj])
    (fun j _ => r2n _) (r2n _) (fun j hj j' hj' e => by have := rg_eq e; omega_using [this, hj, hj'])
    (by rw [u2.gpr]; rfl) fun j hj t ht => ?_) fun s3 h3 => ?_
  · have kt : Kp s2 t := ht.kp (by decide) (rg_ne _).1 fun _ _ => (rg_ne _).1
    refine ldr0_ok (kt.ctx (k2.ctx hcs)) (d := c + 4 * j) (by omega_using [hb, hA, hj]) fun t1 v1 =>
      WP.block_nil ⟨?_, ?_, ?_, fun r hT _ => v1.other r fun e => hT (e ▸ List.mem_singleton_self _), v1.mem,
        v1.rd, v1.wr, v1.sp⟩
    · rw [v1.other _ (rg_ne _).2.2.1.symm, ht.keep _ (r2n _) (fun e => by have := rg_eq e; omega_using [this, hj])
        (fun j' hj' e => by have := rg_eq e; omega_using [this, hj, hj']),
        u2.other _ (fun e => by have := rg_eq e; omega_using [this, hj]), u1.other _ (rg_ne _).2.1.symm]
    · rw [v1.other _ (by decide), ht.keep _ (by decide) (rg_ne _).2.1 (fun _ _ => (rg_ne _).2.1),
        u2.other _ (rg_ne _).2.1, u1.gpr]
      exact hw _ (by omega_using [ha, hi])
    · rw [v1.gpr, ht.mem, hm2]
      exact hw _ (by omega_using [hb, hj])
  · have k3 : Kp s2 s3 := h3.kp (by decide) (rg_ne _).1 fun _ _ => (rg_ne _).1
    refine str0_ok (k3.ctx (k2.ctx hcs)) (d := ACC + 4 * i) (by omega_using [hA, hi]) fun s4 u4 =>
      WP.block_nil ⟨h.kp.trans (k2.trans (k3.trans (Kp.of_mupd u4))), ?_, ?_⟩
    · rw [u4.mem, h3.mem, hm2]
      exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hA, hi]))
    · have hm4 : s4.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (ACC + 4 * i)) (s3.gpr (rg (i + 1))) := by
        rw [u4.mem, h3.mem, hm2]
      have := row_num (lo' := fun k => wd s4.mem (State.addr b) (ACC + 4 * k))
        (t' := fun j => (s4.gpr (rg (i + 1 + 1 + j))).toNat) (a := wd s0.mem (State.addr b) (a + 4 * i))
        h.val ?_ ?_ ?_ ?_
      · rw [val32_succ]; exact this
      · intro k hk
        show wd s4.mem _ _ = _
        rw [hm4, wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [hA, hk, hi]) (by omega_using [hA, hi])]
      · show wd s4.mem _ _ = _
        rw [hm4, wd_write_self]; exact h3.outs 0 (by decide)
      · intro j hj
        show (s4.gpr _).toNat = _
        rw [u4.gpr, show rg (i + 1 + 1 + j) = rg (i + 1 + (j + 1)) from congrArg rg (by omega_arith)]
        exact h3.outs (j + 1) (by omega_using [hj])
      · show (s4.gpr _).toNat = _
        rw [u4.gpr, rg_of_mod (show (i + 1 + 1 + 7) % 9 = i % 9 by omega_arith)]; exact h3.c

/-- `[o] = [a] · [c]`: a number below `2p`, congruent to the product. -/
theorem mul_ok {o a c : Nat} (ho : o + 32 ≤ 4096) (ha : a + 32 ≤ ACC) (hb : c + 32 ≤ ACC) {s : State}
    (hc : Ctx b s) :
    WP isa (.block (mul o a c)) s fun s' =>
      Kp s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 32⟩] s.mem s'.mem ∧
      W s'.mem (State.addr b) o % P = (W s.mem (State.addr b) a * W s.mem (State.addr b) c) % P ∧
      W s'.mem (State.addr b) o < 2 * P := by
  have hA : ACC = 544 := rfl
  unfold mul
  simp only [List.append_assoc]
  refine WP.append zeros_ok fun s1 ⟨hz, k1, hm1⟩ => ?_
  have hc1 : Ctx b s1 := k1.ctx hc
  have ez : val32 (fun j => (s1.gpr (rg (0 + 1 + j))).toNat) 8 = 0 := by
    rw [val32_congr (g := fun _ => 0) fun j hj => by
      show (s1.gpr (rg (0 + 1 + j))).toNat = 0
      rw [show rg (0 + 1 + j) = rg (j + 1) from congrArg rg (by omega_arith), hz j hj]; rfl, val32_zero_fn]
  have h0 : RowInv b a c s1 0 s1 := ⟨Kp.refl _, Frame.refl _ _, by rw [ez]; simp [val32]⟩
  refine WP.append (wp_range_flatMap (M := isa) (RowInv b a c s1) (fun i t hi h => mulRow_ok ha hb hi hc1 h) 8
    (Nat.le_refl _) s1 h0) fun s8 h8 => ?_
  have hc8 : Ctx b s8 := h8.kp.ctx hc1
  unfold mulFold
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s9 u9 => wp_mov (op2_imm (by decide)) fun s10 u10 => ?_
  have k10 : Kp s8 s10 := (Kp.of_upd u9 (by decide)).trans (Kp.of_upd u10 (by decide))
  have hm10 : s10.mem = s8.mem := by rw [u10.mem, u9.mem]
  refine WP.append (uchain_ok (X := fun k => rg (k + 8)) (C := .r1) (N := .r2) (M := rg) (T := [])
    (pre := fun k => [.ldr (rg (k + 8)) .r0 (ACC + 4 * k)]) (nv := 38)
    (mv := fun k => (s8.gpr (rg (8 + 1 + k))).toNat) (xv := fun k => wd s8.mem (State.addr b) (ACC + 4 * k))
    (cin := 0) (fun j _ => (rg_ne _).2.1.symm) (fun _ _ => List.not_mem_nil) List.not_mem_nil
    (fun j hj j' hj' e => by have := rg_eq e; omega_using [this, hj, hj'])
    (by rw [u10.other _ (by decide), u9.gpr]; rfl) fun k hk t ht => ?_) fun s11 h11 => ?_
  · have kt : Kp s10 t := ht.kp List.not_mem_nil (by decide) fun _ _ => (rg_ne _).1
    refine ldr0_ok (kt.ctx (k10.ctx hc8)) (d := ACC + 4 * k) (by omega_using [hA, hk]) fun t1 v1 =>
      WP.block_nil ⟨?_, ?_, ?_, fun r _ hX => v1.other r hX, v1.mem, v1.rd, v1.wr, v1.sp⟩
    · rw [v1.gpr, ht.mem, hm10]; rfl
    · rw [v1.other _ (rg_ne _).2.2.1, ht.keep _ List.not_mem_nil (by decide) (fun _ _ => (rg_ne _).2.2.1),
        u10.gpr]; rfl
    · rw [v1.other _ (fun e => by have := rg_eq e; omega_using [this, hk]),
        ht.keep _ List.not_mem_nil (rg_ne _).2.1.symm (fun j hj e => by have := rg_eq e; omega_using [this, hj, hk]),
        u10.other _ (rg_ne _).2.2.1.symm, u9.other _ (rg_ne _).2.1.symm,
        rg_of_mod (show k % 9 = (8 + 1 + k) % 9 by omega_arith)]
  · -- `lo + 38 hi`, and its carry, at most 38.
    have hv := uc_val8 38 (fun k => (s8.gpr (rg (8 + 1 + k))).toNat)
      (fun k => wd s8.mem (State.addr b) (ACC + 4 * k)) 0
    have h8v := h8.val
    have hhi : val32 (fun k => (s8.gpr (rg (8 + 1 + k))).toNat) 8 < 2 ^ 256 :=
      val32_lt8 fun k _ => (s8.gpr _).isLt
    have hlo : val32 (fun k => wd s8.mem (State.addr b) (ACC + 4 * k)) 8 < 2 ^ 256 :=
      val32_lt8 fun k _ => wd_lt _ _ _
    have hc38 : uc 38 (fun k => (s8.gpr (rg (8 + 1 + k))).toNat)
        (fun k => wd s8.mem (State.addr b) (ACC + 4 * k)) 0 8 < 2 ^ 26 := by omega_arith
    have k11 : Kp s10 s11 := h11.kp List.not_mem_nil (by decide) fun _ _ => (rg_ne _).1
    refine WP.append (fold19_ok (X := fun k => rg (k + 8)) (c := .r1)
      (fun j hj j' hj' e => by have := rg_eq e; omega_using [this, hj, hj'])
      (fun j _ => ⟨(rg_ne _).2.2.2.1, (rg_ne _).2.2.2.2, (rg_ne _).2.1⟩) (by decide) h11.c hc38)
      fun s12 ⟨hval, hle, hkeep, hm12, hrd, hwr, hsp⟩ => ?_
    have k12 : Kp s11 s12 := ⟨hkeep _ (by decide) (by decide) fun _ _ => (rg_ne _).1, hrd, hwr, hsp⟩
    have hc12 : Ctx b s12 := k12.ctx (k11.ctx (k10.ctx hc8))
    refine WP.mono (stores_ok ho hc12) fun s13 ⟨hw, hf, hg, hr⟩ => ⟨?_, ?_, ?_, ?_⟩
    · exact k1.trans (h8.kp.trans (k10.trans (k11.trans (k12.trans (Kp.of_rest hr List.not_mem_nil)))))
    · rw [← hm1]
      refine (h8.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]).trans ?_
      rw [← hm10, ← h11.mem, ← hm12]
      exact hf.mono fun r hr => by simp [List.mem_singleton.mp hr]
    · rw [W_of hw, hval, val32_congr (g := uo 38 (fun k => (s8.gpr (rg (8 + 1 + k))).toNat)
        (fun k => wd s8.mem (State.addr b) (ACC + 4 * k)) 0) h11.outs, hv, Nat.add_zero, Nat.add_comm, ← fold256,
        h8v, ← hm1]
      rfl
    · rw [W_of hw]; exact hle

end

end VG.Proof.X25519.Arm.Words
