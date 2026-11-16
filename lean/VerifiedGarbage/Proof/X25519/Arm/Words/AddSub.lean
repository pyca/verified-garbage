module

public import VerifiedGarbage.Proof.X25519.Arm.Words.Chain
import VerifiedGarbage.Proof.X25519.Arm.Words.Mul
import VerifiedGarbage.Proof.X25519.Field
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# X25519 on 32-bit ARM with `umaal`: sums

`add`, `sub` and `addA24` (`add_ok`, `sub_ok`, `addA24_ok`), and the full
reduction of a number below `2p` in the registers (`freeze_ok`), each a chain
that loads its operands and one that folds its carry in.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Words

open VG VG.Arm VG.Impl.X25519.Arm.Words
open VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)
open VG.Proof.X25519 (fold256)

/-! ## The registers of a sum -/

theorem xr_inj : ∀ i < 8, ∀ j < 8, xr i = xr j → i = j := by decide

theorem xr_ne (n : Nat) : Reg.r0 ≠ xr n ∧ Reg.r1 ≠ xr n ∧ Reg.r2 ≠ xr n ∧ Reg.r3 ≠ xr n ∧ Reg.r12 ≠ xr n ∧
    Reg.lr ≠ xr n := by
  unfold xr; split <;> decide

theorem xr_inj' {i j : Nat} (hi : i < 8) (hj : j < i) : xr i ≠ xr j := fun e =>
  absurd (xr_inj i hi j (Nat.lt_trans hj hi) e) (Nat.ne_of_gt hj)

/-! ## Instructions -/

theorem wp_movt {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_mvn {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {o : Op2} {v : BitVec 32}
    (ho : o.eval s = some v) (k : ∀ s', Upd s s' d (~~~v) → WP isa (.block is) s' Q) :
    WP isa (.block (.mvn d o :: is)) s Q :=
  WP.cons (s' := s.setReg d (~~~v)) (by simp only [exec, ho, Option.map_some]) (k _ (Upd.setReg _ _ _))

section
variable {b : BitVec 32}

/-- Word `k` of `[a]` into `xr k` and of `[c]` into `r3`. -/
theorem ld2_ok {a c k : Nat} (ha : a + 4 * k + 4 ≤ 4096) (hc' : c + 4 * k + 4 ≤ 4096) {t : State}
    (hc : Ctx b t) :
    WP isa (.block [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k)]) t fun t' =>
      (t'.gpr (xr k)).toNat = wd t.mem (State.addr b) (a + 4 * k) ∧
      (t'.gpr .r3).toNat = wd t.mem (State.addr b) (c + 4 * k) ∧ UKeep (xr k) [.r3] t t' := by
  refine ldr0_ok hc (d := a + 4 * k) ha fun t1 v1 => ?_
  refine ldr0_ok ((Kp.of_upd v1 (xr_ne k).1).ctx hc) (d := c + 4 * k) hc' fun t2 v2 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [v2.other _ (xr_ne k).2.2.2.1.symm, v1.gpr]; rfl
  · rw [v2.gpr, v1.mem]; rfl
  · exact ⟨fun r hT hX => by
      rw [v2.other r fun e => hT (e ▸ List.mem_singleton_self _), v1.other r hX],
      by rw [v2.mem, v1.mem], by rw [v2.rd, v1.rd], by rw [v2.wr, v1.wr], by rw [v2.sp, v1.sp]⟩

/-- A chain that adds `nv` times `[c]` to `[a]`, with the carry in `r1` and
`nv` in `r2`. -/
theorem ldChain_ok {a c : Nat} (ha : a + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) {s : State} (hc : Ctx b s)
    {nv cin : Nat} (h1 : (s.gpr .r1).toNat = cin) (h2 : (s.gpr .r2).toNat = nv) :
    WP isa (.block ((List.range 8).flatMap fun k =>
      ([.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k), .umaal (xr k) .r1 .r2 .r3] : List Instr))) s
      (UInv xr .r1 [.r3] nv (fun k => wd s.mem (State.addr b) (c + 4 * k))
        (fun k => wd s.mem (State.addr b) (a + 4 * k)) cin s 8) := by
  refine uchain_ok (X := xr) (C := .r1) (N := .r2) (M := fun _ => .r3) (T := [.r3])
    (pre := fun k => [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k)])
    (fun j _ => (xr_ne j).2.1.symm) (fun j _ hm => (xr_ne j).2.2.2.1 (List.mem_singleton.mp hm).symm)
    (by decide) xr_inj h1 fun k hk t ht => ?_
  have kt : Kp s t := ht.kp (by decide) (by decide) fun j _ => (xr_ne j).1
  refine WP.mono (ld2_ok (a := a) (c := c) (by omega_using [ha, hk]) (by omega_using [hc', hk]) (kt.ctx hc))
    fun t' ⟨hx, hm, hk'⟩ => ⟨by rw [hx, ht.mem], ?_, by rw [hm, ht.mem], hk'⟩
  rw [hk'.keep _ (by decide) (xr_ne k).2.2.1, ht.keep _ (by decide) (by decide) fun j _ => (xr_ne j).2.2.1, h2]

/-! ## Addition -/

theorem add_num {wa wc u1 c1 u2 c2 : Nat} (ha : wa < 2 * P) (hc : wc < 2 * P) (hu1 : u1 < 2 ^ 256)
    (h1 : u1 + 2 ^ 256 * c1 = 1 * wc + wa + 0) (h2 : u2 + 2 ^ 256 * c2 = u1 + 38 * c1) :
    u2 % P = (wa + wc) % P := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have hc1 : c1 ≤ 1 := by omega_arith
  have hc2 : c2 = 0 := by omega_arith
  subst hc2
  rw [show u2 = u1 + 38 * c1 by omega_arith, ← fold256]
  congr 1
  omega_arith

/-- `[o] = [a] + [c]`, for operands below `2p`. -/
theorem add_ok {o a c : Nat} (ho : o + 32 ≤ 4096) (ha : a + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) {s : State}
    (hc : Ctx b s) (hla : W s.mem (State.addr b) a < 2 * P) (hlc : W s.mem (State.addr b) c < 2 * P) :
    WP isa (.block (add o a c)) s fun s' =>
      Kp s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      W s'.mem (State.addr b) o % P = (W s.mem (State.addr b) a + W s.mem (State.addr b) c) % P := by
  unfold add
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (ldChain_ok (a := a) (c := c) ha hc' (k2.ctx hc) (nv := 1) (cin := 0)
    (by rw [u2.other _ (by decide), u1.gpr]; rfl) (by rw [u2.gpr]; rfl)) fun s3 h3 => ?_
  rw [hm2] at h3
  have hv1 := uc_val8 1 (fun k => wd s.mem (State.addr b) (c + 4 * k))
    (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0
  have hu1 : val32 (uo 1 (fun k => wd s.mem (State.addr b) (c + 4 * k))
      (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0) 8 < 2 ^ 256 := val32_lt8 fun k _ => uo_lt _ _ _ _ _
  have hP : P = 2 ^ 255 - 19 := rfl
  have hc1 : uc 1 (fun k => wd s.mem (State.addr b) (c + 4 * k))
      (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0 8 ≤ 1 := by
    have e1 : val32 (fun k => wd s.mem (State.addr b) (c + 4 * k)) 8 = W s.mem (State.addr b) c := rfl
    have e2 : val32 (fun k => wd s.mem (State.addr b) (a + 4 * k)) 8 = W s.mem (State.addr b) a := rfl
    omega_arith
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => wp_mul fun s5 u5 =>
    wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  have e1 : (s6.gpr .r1).toNat = 38 * uc 1 (fun k => wd s.mem (State.addr b) (c + 4 * k))
      (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0 8 := by
    rw [u6.other _ (by decide), u5.gpr, u4.gpr, u4.other _ (by decide),
      toNat_mul_lt (by rw [h3.c]; show _ * 38 < _; omega_using [hc1]), h3.c]
    show _ * 38 = _
    omega_arith
  refine WP.append (uchain_ok (X := xr) (C := .r1) (N := .r3) (M := fun _ => .r3) (T := []) (pre := fun _ => [])
    (nv := 0) (mv := fun _ => 0)
    (xv := uo 1 (fun k => wd s.mem (State.addr b) (c + 4 * k)) (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0)
    (fun j _ => (xr_ne j).2.1.symm) (fun _ _ => List.not_mem_nil) List.not_mem_nil xr_inj e1
    fun k hk t ht => WP.block_nil ⟨?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s7 h7 => ?_
  · rw [ht.keep _ List.not_mem_nil (xr_ne k).2.1.symm fun j hj => xr_inj' hk hj, u6.other _ (xr_ne k).2.2.2.1.symm,
      u5.other _ (xr_ne k).2.1.symm, u4.other _ (xr_ne k).2.2.2.1.symm]
    exact h3.outs k hk
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, u6.gpr]; rfl
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, u6.gpr]; rfl
  · have k3 : Kp s2 s3 := h3.kp (by decide) (by decide) fun j _ => (xr_ne j).1
    have k6 : Kp s3 s6 := (Kp.of_upd u4 (by decide)).trans ((Kp.of_upd u5 (by decide)).trans (Kp.of_upd u6 (by decide)))
    have k7 : Kp s6 s7 := h7.kp List.not_mem_nil (by decide) fun j _ => (xr_ne j).1
    have hm7 : s7.mem = s.mem := by rw [h7.mem, u6.mem, u5.mem, u4.mem, h3.mem, hm2]
    refine WP.mono (stores_ok ho (k7.ctx (k6.ctx (k3.ctx (k2.ctx hc))))) fun s8 ⟨hw, hf, hg, hr⟩ =>
      ⟨k2.trans (k3.trans (k6.trans (k7.trans (Kp.of_rest hr List.not_mem_nil)))), by rw [← hm7]; exact hf, ?_⟩
    have hv2 := uc_val8 0 (fun _ => 0)
      (uo 1 (fun k => wd s.mem (State.addr b) (c + 4 * k)) (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0)
      (38 * uc 1 (fun k => wd s.mem (State.addr b) (c + 4 * k)) (fun k => wd s.mem (State.addr b) (a + 4 * k)) 0 8)
    rw [Nat.zero_mul, Nat.zero_add] at hv2
    rw [W_of hw, val32_congr h7.outs]
    exact add_num hla hlc hu1 hv1 hv2

/-! ## The fix-up of a difference -/

theorem val32_not {y : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, y k < 2 ^ 32) →
    val32 (fun k => 2 ^ 32 - 1 - y k) n + val32 y n + 1 = 2 ^ (32 * n)
  | 0, _ => rfl
  | n + 1, h => by
    have ih := val32_not (n := n) fun k hk => h k (Nat.lt_succ_of_lt hk)
    have hn := h n (Nat.lt_succ_self n)
    rw [val32_succ, val32_succ, Nat.mul_succ, Nat.pow_add]
    have e : 2 ^ (32 * n) * (2 ^ 32 - 1 - y n) + 2 ^ (32 * n) * y n + 2 ^ (32 * n) = 2 ^ (32 * n) * 2 ^ 32 := by
      rw [← Nat.mul_add, ← Nat.mul_succ]; congr 1; omega_arith
    omega_arith

theorem val32_mask (K : Nat) (hK : K < 2 ^ 32) :
    val32 (fun k => if k = 0 then 2 ^ 32 - 1 - K else 2 ^ 32 - 1) 8 = 2 ^ 256 - 1 - K := by
  simp only [val32, Nat.reduceMul, Nat.reducePow, ↓reduceIte, Nat.reduceEqDiff, Nat.reduceSub]
  omega_arith

/-- `fixup K`: `2²⁵⁶ - 1 - K` added to `xr` if `r1` is 0, and nothing if it is 1. -/
theorem fixup_ok {K : BitVec 32} (hK : encodable K = true) {s : State} {c1 : Nat}
    (h1 : (s.gpr .r1).toNat = c1) (hc1 : c1 ≤ 1) (h2 : s.gpr .r2 = 1) :
    WP isa (.block (fixup K)) s fun s' =>
      (∃ c2, val32 (fun k => (s'.gpr (xr k)).toNat) 8 + 2 ^ 256 * c2 =
        val32 (fun k => (s.gpr (xr k)).toNat) 8 + (1 - c1) * (2 ^ 256 - 1 - K.toNat)) ∧
      (∀ r, r ∉ [Reg.r1, .r3, .r12] → (∀ j < 8, r ≠ xr j) → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold fixup
  simp only [List.cons_append, List.nil_append]
  refine wp_dp (op2_imm (by decide)) fun s1 u1 => wp_dp (op2_imm hK) fun s2 u2 =>
    wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  -- The mask, and its lowest word.
  have em : (s3.gpr .r1).toNat = (1 - c1) * (2 ^ 32 - 1) ∧ (s3.gpr .r3).toNat = (1 - c1) * (2 ^ 32 - 1 - K.toNat) := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr]
    show ((s.gpr .r1 - 1).toNat = _ ∧ ((s.gpr .r1 - 1) &&& ~~~K).toNat = _)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with rfl | rfl
    · rw [show s.gpr .r1 = 0 from BitVec.eq_of_toNat_eq h1, show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide,
        BitVec.allOnes_and, BitVec.toNat_not]
      exact ⟨rfl, by omega_arith⟩
    · rw [show s.gpr .r1 = 1 from BitVec.eq_of_toNat_eq h1, show (1 : BitVec 32) - 1 = 0#32 by decide,
        BitVec.zero_and]
      exact ⟨rfl, (Nat.zero_mul _).symm⟩
  refine WP.mono (uchain_ok (X := xr) (C := .r12) (N := .r2) (M := fun k => if k = 0 then .r3 else .r1) (T := [])
    (pre := fun _ => []) (nv := 1)
    (mv := fun k => if k = 0 then (1 - c1) * (2 ^ 32 - 1 - K.toNat) else (1 - c1) * (2 ^ 32 - 1))
    (xv := fun k => (s.gpr (xr k)).toNat) (cin := 0)
    (fun j _ => (xr_ne j).2.2.2.2.1.symm) (fun _ _ => List.not_mem_nil) List.not_mem_nil xr_inj
    (by rw [u3.gpr]; rfl)
    fun k hk t ht => WP.block_nil ⟨?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s4 h4 =>
      ⟨⟨uc 1 (fun k => if k = 0 then (1 - c1) * (2 ^ 32 - 1 - K.toNat) else (1 - c1) * (2 ^ 32 - 1))
        (fun k => (s.gpr (xr k)).toNat) 0 8, ?_⟩, ?_, ?_⟩
  · rw [ht.keep _ List.not_mem_nil (xr_ne k).2.2.2.2.1.symm fun j hj => xr_inj' hk hj,
      u3.other _ (xr_ne k).2.2.2.2.1.symm, u2.other _ (xr_ne k).2.2.2.1.symm, u1.other _ (xr_ne k).2.1.symm]
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.1, u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide), h2]; rfl
  · by_cases h : k = 0
    · simp only [h, ite_true]
      rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, em.2]
    · simp only [h, ite_false]
      rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.1, em.1]
  · have hv := uc_val8 1 (fun k => if k = 0 then (1 - c1) * (2 ^ 32 - 1 - K.toNat) else (1 - c1) * (2 ^ 32 - 1))
      (fun k => (s.gpr (xr k)).toNat) 0
    have eM : val32 (fun k => if k = 0 then (1 - c1) * (2 ^ 32 - 1 - K.toNat) else (1 - c1) * (2 ^ 32 - 1)) 8 =
        (1 - c1) * (2 ^ 256 - 1 - K.toNat) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with rfl | rfl
      · simp only [Nat.sub_zero, Nat.one_mul]; exact val32_mask _ K.isLt
      · simp only [Nat.sub_self, Nat.zero_mul, ite_self]; exact val32_zero_fn 8
    rw [eM] at hv
    rw [val32_congr h4.outs, hv]
    omega_arith
  · intro r hr hX
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h4.keep r List.not_mem_nil hr.2.2 fun j hj => hX j hj, u3.other r hr.2.2, u2.other r hr.2.1, u1.other r hr.1]
  · exact ⟨by rw [h4.mem, u3.mem, u2.mem, u1.mem], by rw [h4.rd, u3.rd, u2.rd, u1.rd],
      by rw [h4.wr, u3.wr, u2.wr, u1.wr], by rw [h4.sp, u3.sp, u2.sp, u1.sp]⟩

/-! ## Subtraction -/

theorem sub_num {wa wc u1 c1 u2 c2 m : Nat} (hc : wc < 2 * P) (hwa : wa < 2 ^ 256)
    (hm : m + wc + 1 = 2 ^ 256)
    (h1 : u1 + 2 ^ 256 * c1 = 1 * m + wa + 1) (hu1 : u1 < 2 ^ 256) (hu2 : u2 < 2 ^ 256)
    (h2 : u2 + 2 ^ 256 * c2 = u1 + (1 - c1) * (2 ^ 256 - 1 - 37)) :
    (u2 + wc) % P = wa % P := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have hc1 : c1 = 0 ∨ c1 = 1 := by omega_arith
  rcases hc1 with rfl | rfl
  · simp only [Nat.sub_zero, Nat.one_mul] at h2
    rw [show u2 + wc = wa + 2 * P by omega_arith, Nat.add_mul_mod_self_right]
  · simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at h2
    rw [show u2 + wc = wa by omega_arith]

/-- `[o] = [a] - [c]`, for a subtrahend below `2p`. -/
theorem sub_ok {o a c : Nat} (ho : o + 32 ≤ 4096) (ha : a + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) {s : State}
    (hc : Ctx b s) (hlc : W s.mem (State.addr b) c < 2 * P) :
    WP isa (.block (sub o a c)) s fun s' =>
      Kp s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      (W s'.mem (State.addr b) o + W s.mem (State.addr b) c) % P = W s.mem (State.addr b) a % P := by
  unfold sub
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have k2 : Kp s s2 := (Kp.of_upd u1 (by decide)).trans (Kp.of_upd u2 (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (uchain_ok (X := xr) (C := .r1) (N := .r2) (M := fun _ => .r3) (T := [.r3])
    (pre := fun k => [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k), .mvn .r3 (.reg .r3)])
    (nv := 1) (mv := fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k))
    (xv := fun k => wd s.mem (State.addr b) (a + 4 * k)) (cin := 1)
    (fun j _ => (xr_ne j).2.1.symm) (fun j _ hm => (xr_ne j).2.2.2.1 (List.mem_singleton.mp hm).symm)
    (by decide) xr_inj (by rw [u2.other _ (by decide), u1.gpr]; rfl) fun k hk t ht => ?_) fun s3 h3 => ?_
  · have kt : Kp s2 t := ht.kp (by decide) (by decide) fun j _ => (xr_ne j).1
    refine WP.append (l := [.ldr (xr k) .r0 (a + 4 * k), .ldr .r3 .r0 (c + 4 * k)])
      (rest := [.mvn .r3 (.reg .r3)])
      (ld2_ok (a := a) (c := c) (by omega_using [ha, hk]) (by omega_using [hc', hk]) (kt.ctx (k2.ctx hc)))
      fun t' ⟨hx, hm, hk'⟩ => wp_mvn (op2_reg _ _) fun t3 v3 => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
    · rw [v3.other _ (xr_ne k).2.2.2.1.symm, hx, ht.mem, hm2]
    · rw [v3.other _ (by decide), hk'.keep _ (by decide) (xr_ne k).2.2.1,
        ht.keep _ (by decide) (by decide) fun j _ => (xr_ne j).2.2.1, u2.gpr]; rfl
    · rw [v3.gpr, BitVec.toNat_not, hm, ht.mem, hm2]
    · exact ⟨fun r hT hX => by
        rw [v3.other r fun e => hT (e ▸ List.mem_singleton_self _), hk'.keep r hT hX],
        by rw [v3.mem, hk'.mem], by rw [v3.rd, hk'.rd], by rw [v3.wr, hk'.wr], by rw [v3.sp, hk'.sp]⟩
  · have hv1 := uc_val8 1 (fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k))
      (fun k => wd s.mem (State.addr b) (a + 4 * k)) 1
    have hn : val32 (fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k)) 8 + W s.mem (State.addr b) c + 1 =
        2 ^ 256 := val32_not (n := 8) fun k _ => wd_lt _ _ _
    have hwa : W s.mem (State.addr b) a < 2 ^ 256 := W_lt _ _ _
    have ea : val32 (fun k => wd s.mem (State.addr b) (a + 4 * k)) 8 = W s.mem (State.addr b) a := rfl
    have hu1 : val32 (uo 1 (fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k))
        (fun k => wd s.mem (State.addr b) (a + 4 * k)) 1) 8 < 2 ^ 256 := val32_lt8 fun k _ => uo_lt _ _ _ _ _
    have hc1 : uc 1 (fun k => 2 ^ 32 - 1 - wd s.mem (State.addr b) (c + 4 * k))
        (fun k => wd s.mem (State.addr b) (a + 4 * k)) 1 8 ≤ 1 := by omega_arith
    have k3 : Kp s2 s3 := h3.kp (by decide) (by decide) fun j _ => (xr_ne j).1
    refine WP.append (fixup_ok (K := 37) (by decide) h3.c hc1 (by
      rw [h3.keep _ (by decide) (by decide) fun j _ => (xr_ne j).2.2.1, u2.gpr]))
      fun s4 ⟨⟨c2, hfix⟩, hkeep, hm4, hrd, hwr, hsp⟩ => ?_
    have k4 : Kp s3 s4 := ⟨hkeep _ (by decide) fun j _ => (xr_ne j).1, hrd, hwr, hsp⟩
    have hm4' : s4.mem = s.mem := by rw [hm4, h3.mem, hm2]
    refine WP.mono (stores_ok ho (k4.ctx (k3.ctx (k2.ctx hc)))) fun s5 ⟨hw, hf, hg, hr⟩ =>
      ⟨k2.trans (k3.trans (k4.trans (Kp.of_rest hr List.not_mem_nil))), by rw [← hm4']; exact hf, ?_⟩
    rw [val32_congr h3.outs, show (37 : BitVec 32).toNat = 37 from rfl] at hfix
    rw [W_of hw]
    exact sub_num hlc hwa hn (by rw [ea] at hv1; exact hv1) hu1 (val32_lt8 fun k _ => (s4.gpr _).isLt) hfix

/-! ## `b + 121665 a` -/

/-- `[o] = [c] + 121665 [a]`: a number below `2p`. -/
theorem addA24_ok {o c a : Nat} (ho : o + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) (ha : a + 32 ≤ 4096) {s : State}
    (hc : Ctx b s) :
    WP isa (.block (addA24 o c a)) s fun s' =>
      Kp s s' ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      W s'.mem (State.addr b) o % P = (W s.mem (State.addr b) c + 121665 * W s.mem (State.addr b) a) % P ∧
      W s'.mem (State.addr b) o < 2 * P := by
  unfold addA24
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_movw fun s1 u1 => wp_movt fun s2 u2 => wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have k3 : Kp s s3 := (Kp.of_upd u1 (by decide)).trans ((Kp.of_upd u2 (by decide)).trans (Kp.of_upd u3 (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine WP.append (ldChain_ok (a := c) (c := a) hc' ha (k3.ctx hc) (nv := 121665) (cin := 0)
    (by rw [u3.gpr]; rfl) (by rw [u3.other _ (by decide), u2.gpr, u1.gpr]; rfl)) fun s4 h4 => ?_
  rw [hm3] at h4
  have hv := uc_val8 121665 (fun k => wd s.mem (State.addr b) (a + 4 * k))
    (fun k => wd s.mem (State.addr b) (c + 4 * k)) 0
  have ea : val32 (fun k => wd s.mem (State.addr b) (a + 4 * k)) 8 = W s.mem (State.addr b) a := rfl
  have ec : val32 (fun k => wd s.mem (State.addr b) (c + 4 * k)) 8 = W s.mem (State.addr b) c := rfl
  rw [ea, ec] at hv
  have hwa : W s.mem (State.addr b) a < 2 ^ 256 := W_lt _ _ _
  have hwc : W s.mem (State.addr b) c < 2 ^ 256 := W_lt _ _ _
  have hc26 : uc 121665 (fun k => wd s.mem (State.addr b) (a + 4 * k))
      (fun k => wd s.mem (State.addr b) (c + 4 * k)) 0 8 < 2 ^ 26 := by omega_arith
  have k4 : Kp s3 s4 := h4.kp (by decide) (by decide) fun j _ => (xr_ne j).1
  refine WP.append (fold19_ok (X := xr) (c := .r1) xr_inj
    (fun j _ => ⟨(xr_ne j).2.2.2.2.1, (xr_ne j).2.2.2.2.2, (xr_ne j).2.1⟩) (by decide) h4.c hc26)
    fun s5 ⟨hval, hlt, hkeep, hm5, hrd, hwr, hsp⟩ => ?_
  have k5 : Kp s4 s5 := ⟨hkeep _ (by decide) (by decide) fun j _ => (xr_ne j).1, hrd, hwr, hsp⟩
  have hm5' : s5.mem = s.mem := by rw [hm5, h4.mem, hm3]
  refine WP.mono (stores_ok ho (k5.ctx (k4.ctx (k3.ctx hc)))) fun s6 ⟨hw, hf, hg, hr⟩ =>
    ⟨k3.trans (k4.trans (k5.trans (Kp.of_rest hr List.not_mem_nil))), by rw [← hm5']; exact hf, ?_, ?_⟩
  · rw [W_of hw, hval, val32_congr h4.outs, hv, Nat.add_zero, Nat.add_comm]
  · rw [W_of hw]; exact hlt

/-! ## The full reduction -/

theorem freeze_num {v y c z c2 : Nat} (hv : v < 2 * P) (hy : y + 2 ^ 256 * c = v + 19)
    (hz : z + 2 ^ 256 * c2 = y + (1 - y / 2 ^ 255) * (2 ^ 256 - 1 - 18)) (hy' : y < 2 ^ 256) (hz' : z < 2 ^ 256) :
    z % 2 ^ 255 = v % P := by
  have hP : P = 2 ^ 255 - 19 := rfl
  have hq : y / 2 ^ 255 = 0 ∨ y / 2 ^ 255 = 1 := by omega_arith
  rcases hq with e | e
  · rw [e] at hz
    simp only [Nat.sub_zero, Nat.one_mul] at hz
    rw [Nat.mod_eq_of_lt (show v < P by omega_arith)]
    omega_arith
  · rw [e] at hz
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at hz
    rw [Nat.mod_eq_sub_mod (show v ≥ P by omega_arith), Nat.mod_eq_of_lt (show v - P < P by omega_arith)]
    omega_arith

/-- The number in `xr`, below `2p`, reduced fully. -/
theorem freeze_ok {s : State} (hv : val32 (fun k => (s.gpr (xr k)).toNat) 8 < 2 * P) :
    WP isa (.block freeze) s fun s' =>
      val32 (fun k => (s'.gpr (xr k)).toNat) 8 = val32 (fun k => (s.gpr (xr k)).toNat) 8 % P ∧
      (∀ r, r ∉ [Reg.r1, .r2, .r3, .r12] → (∀ j < 8, r ≠ xr j) → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold freeze
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  refine WP.append (uchain_ok (X := xr) (C := .r12) (N := .r3) (M := fun _ => .r3) (T := []) (pre := fun _ => [])
    (nv := 0) (mv := fun _ => 0) (xv := fun k => (s.gpr (xr k)).toNat) (cin := 19)
    (fun j _ => (xr_ne j).2.2.2.2.1.symm) (fun _ _ => List.not_mem_nil) List.not_mem_nil xr_inj
    (by rw [u2.other _ (by decide), u1.gpr]; rfl)
    fun k hk t ht => WP.block_nil ⟨?_, ?_, ?_, fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s3 h3 => ?_
  · rw [ht.keep _ List.not_mem_nil (xr_ne k).2.2.2.2.1.symm fun j hj => xr_inj' hk hj,
      u2.other _ (xr_ne k).2.2.2.1.symm, u1.other _ (xr_ne k).2.2.2.2.1.symm]
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, u2.gpr]; rfl
  · rw [ht.keep _ List.not_mem_nil (by decide) fun j _ => (xr_ne j).2.2.2.1, u2.gpr]; rfl
  have hy := uc_val8 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19
  rw [Nat.zero_mul, Nat.zero_add] at hy
  have hy' : val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 8 < 2 ^ 256 :=
    val32_lt8 fun k _ => uo_lt _ _ _ _ _
  have hy7 : val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 7 < 2 ^ 224 :=
    val32_lt fun k _ => uo_lt _ _ _ _ _
  have e8 : val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 8 =
      val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 7 +
        2 ^ 224 * uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19 7 := rfl
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  have e1 : (s5.gpr .r1).toNat = val32 (uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19) 8 / 2 ^ 255 := by
    rw [u5.other _ (by decide), u4.gpr, toNat_shr, h3.outs 7 (by decide)]
    omega_arith
  refine WP.append (fixup_ok (K := 18) (by decide) e1 (by omega_arith) u5.gpr)
    fun s6 ⟨⟨c2, hfix⟩, hkeep, hm6, hrd, hwr, hsp⟩ => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => WP.block_nil ⟨?_, fun r hr hX => ?_, ?_⟩
  · have hz7 : val32 (fun k => (s6.gpr (xr k)).toNat) 7 < 2 ^ 224 := val32_lt fun k _ => (s6.gpr _).isLt
    have ez : val32 (fun k => (s6.gpr (xr k)).toNat) 8 =
        val32 (fun k => (s6.gpr (xr k)).toNat) 7 + 2 ^ 224 * (s6.gpr (xr 7)).toNat := rfl
    have e7 : val32 (fun k => (s7.gpr (xr k)).toNat) 8 =
        val32 (fun k => (s6.gpr (xr k)).toNat) 7 + 2 ^ 224 * ((s6.gpr (xr 7)).toNat % 2 ^ 31) := by
      rw [val32_succ, val32_congr (g := fun k => (s6.gpr (xr k)).toNat) fun k hk => by
        show (s7.gpr (xr k)).toNat = _
        rw [u7.other _ fun e => absurd (xr_inj k (by omega_arith) 7 (by decide) e) (by omega_arith)]]
      show _ + _ * (s7.gpr (xr 7)).toNat = _
      rw [u7.gpr]
      show _ + _ * (s6.gpr (xr 7) &&& ~~~(0x80000000 : BitVec 32)).toNat = _
      rw [toNat_bic31]
    have hs5 : ∀ k < 8, (s5.gpr (xr k)).toNat = uo 0 (fun _ => 0) (fun k => (s.gpr (xr k)).toNat) 19 k :=
      fun k hk => by rw [u5.other _ (xr_ne k).2.2.1.symm, u4.other _ (xr_ne k).2.1.symm]; exact h3.outs k hk
    rw [val32_congr hs5, show (18 : BitVec 32).toNat = 18 from rfl] at hfix
    have := freeze_num hv hy hfix hy' (val32_lt8 fun k _ => (s6.gpr _).isLt)
    rw [← this, e7]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u7.other r (hX 7 (by decide)), hkeep r (by simp [hr.1, hr.2.2.1, hr.2.2.2]) hX, u5.other r hr.2.1,
      u4.other r hr.1, h3.keep r List.not_mem_nil hr.2.2.2 fun j hj => hX j hj, u2.other r hr.2.2.1,
      u1.other r hr.2.2.2]
  · exact ⟨by rw [u7.mem, hm6, u5.mem, u4.mem, h3.mem, u2.mem, u1.mem],
      by rw [u7.rd, hrd, u5.rd, u4.rd, h3.rd, u2.rd, u1.rd], by rw [u7.wr, hwr, u5.wr, u4.wr, h3.wr, u2.wr, u1.wr],
      by rw [u7.sp, hsp, u5.sp, u4.sp, h3.sp, u2.sp, u1.sp]⟩

end

end VG.Proof.X25519.Arm.Words
