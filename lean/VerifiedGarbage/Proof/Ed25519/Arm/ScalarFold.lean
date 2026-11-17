module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass
public import VerifiedGarbage.Proof.Ed25519.Arm.Field
public import VerifiedGarbage.Proof.X25519.Arm.Mul
public import VerifiedGarbage.Proof.X25519.Arm.Pass
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.X25519.Arm.Cswap
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Impl.Ed25519.Arm.Scalar
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Ed25519 on ARMv7: a scalar modulo the subgroup order, a product at a time

`scalarFold` leaves in `SR` the 32 limbs at `ACC` modulo `L`
(`scalarFold_ok`): the two products by `d = 16 L - 2²⁵⁶` row by row
(`scalarRow_ok`, the loop invariant `MulDInv`), the sum `T`
(`scalarSum_ok`), its top folded in (`scalarTop_ok`, `scalarLow_ok`) and the
subtraction of `L` (`scalarCondSub_ok`); `Proof/Ed25519/Arm/ScalarPass.lean`
has the numbers. `scalarReduceEngine` unpacks 64 bytes into `ACC` first
(`scalarReduceEngine_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed25519 (L bytesAt decodeLE)

variable {b : BitVec 32}

/-! ## Instructions -/

theorem wp_mla {d n m a : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m + s.gpr a) → WP isa (.block is) s' Q) :
    WP isa (.block (.mla d n m a :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem toNat_mla_lt {x y z : BitVec 32} (h : x.toNat * y.toNat + z.toNat < 2 ^ 32) :
    (x * y + z).toNat = x.toNat * y.toNat + z.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.mod_add_mod, Nat.mod_eq_of_lt h]

theorem toNat_movw {v : Nat} (h : v < 65536) : ((BitVec.ofNat 16 v).setWidth 32).toNat = v := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))

theorem scalarMla_ok {v : Nat} (hv : v < 65536) {s : State}
    (hlt : (s.gpr .r1).toNat * v + (s.gpr .r3).toNat < 2 ^ 32) :
    WP isa (.block (scalarMla v)) s fun t =>
      (t.gpr .r3).toNat = (s.gpr .r1).toNat * v + (s.gpr .r3).toNat ∧ Rest [.r2, .r3] s t ∧
        t.mem = s.mem := by
  rw [scalarMla]
  refine wp_movw fun t1 u1 => wp_mla fun t2 u2 => WP.block_nil ⟨?_, ?_, by rw [u2.mem, u1.mem]⟩
  · have e2 : (t1.gpr .r2).toNat = v := by rw [u1.gpr]; exact toNat_movw hv
    rw [u2.gpr, toNat_mla_lt (by rw [e2, u1.other _ (by decide), u1.other _ (by decide)]; exact hlt),
      e2, u1.other _ (by decide), u1.other _ (by decide)]
  · exact (u1.rest (by decide)).trans (u2.rest (by decide))

/-- `r3 += r1 · v`, where the code has it: for the limbs of a constant that
are not zero. -/
theorem scalarMlaIf_ok {c : Prop} [Decidable c] {v : Nat} (hv : v < 65536) (hz : ¬ c → v = 0)
    {s : State} (hlt : (s.gpr .r1).toNat * v + (s.gpr .r3).toNat < 2 ^ 32) :
    WP isa (.block (if c then scalarMla v else [])) s fun t =>
      (t.gpr .r3).toNat = (s.gpr .r1).toNat * v + (s.gpr .r3).toNat ∧ Rest [.r2, .r3] s t ∧
        t.mem = s.mem := by
  by_cases h : c
  · rw [ite_eq_left h]; exact scalarMla_ok hv hlt
  · rw [ite_eq_right h]
    exact WP.block_nil ⟨by rw [hz h, Nat.mul_zero, Nat.zero_add], Rest.refl _ _, rfl⟩

/-- A word outside the one region a frame names. -/
theorem wd_outside {m m' : Mem} {B : Addr} {e len d : Nat}
    (hf : Frame [⟨B + BitVec.ofNat 64 e, len⟩] m m') (h : d + 4 ≤ e ∨ e + len ≤ d)
    (hd : d + 4 ≤ 2 ^ 64) (he : e + len ≤ 2 ^ 64) : wd m' B d = wd m B d :=
  wd_frame hf fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ h hd he

/-- `pass_ok`, for the `n` limbs of a shorter number. -/
theorem passN_ok {n : Nat} {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.r2, .r3, .r4, .r5]) (ho : o + 4 * n ≤ 4096)
    (hfit : (s0.gpr rb).toNat + o + 4 * n ≤ 2 ^ 32)
    (hw : ∀ k < n, InRegions s0.wr (State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k)) 4)
    (h6 : s0.gpr .r6 = mask16) (h5 : (s0.gpr .r5).toNat = cin)
    (hc : ∀ k < n, c k + 65536 ≤ 2 ^ 32) (hcin : cin < 65536)
    (hsrc : ∀ k < n, ∀ s, PassInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .r3).toNat = c k ∧ Rest [.r2, .r3, .r4] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (passN n rb o src)) s0 (PassInv rb o s0 c cin n) := by
  have hr := not_mem4 hrb
  refine wp_range_flatMap (M := isa) (PassInv rb o s0 c cin) (fun k s hk h => ?_) n (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h5]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h3, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1, hr.2.2.1]), h.rest.gpr _ hrb]
  have h51 : s1.gpr .r5 = s.gpr .r5 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (carryStep_ok (a := State.addr (s0.gpr rb) + BitVec.ofNat 64 (o + 4 * k))
    ⟨hr.2.1, hr.2.2.1⟩ (by omega_using [ho, hk]) (by rw [hrb1]; exact ea (by omega_using [hfit, hk]))
    (by rw [hr1.wr, h.rest.wr]; exact hw k hk)
    (by rw [hr1.gpr _ (by decide), h.rest.gpr _ (by decide), h6])
    (by rw [h3, h51, h.r5]; exact hsum)) fun s2 ⟨e5, ⟨v, hv, hm2⟩, hr2⟩ => ?_
  rw [h3, h51, h.r5] at e5 hv
  rw [hm1] at hm2
  refine ⟨h.rest.trans ((hr1.mono (by decide)).trans (hr2.mono (by decide))), by rw [e5]; rfl, ?_,
    fun j hj => ?_⟩
  · rw [hm2]
    refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) v
      (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [hfit, hk]))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega_using [])
  · rw [hm2]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [hfit, hk])]
      exact h.outs j hj
    · rw [wd_write_self, hv]; rfl

/-! ## A product by `d` -/

/-- The loop invariant of the rows of `scalarMulD acc x n` from `s0`, after
`i` rows. -/
structure MulDInv (acc x n : Nat) (b : BitVec 32) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s0 s
  r6 : s.gpr .r6 = mask16
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  r9 : s.gpr .r9 = BitVec.ofNat 32 (n - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 acc, 4 * (n + 9)⟩] s0.mem s.mem
  lt : ∀ k < i + 9, accw acc s.mem (State.addr b) k < 65536
  val : val16 (accw acc s.mem (State.addr b)) (i + 9) =
    val16 (limb s0.mem (State.addr b) x) i * val16 scalarD 9

theorem scalarRow_ok {acc x n : Nat} (hA : acc + 4 * (n + 9) ≤ 4096) (hX : x + 4 * n ≤ 4096)
    (hxa : x + 4 * n ≤ acc ∨ acc + 4 * (n + 9) ≤ x) {s0 : State}
    (hlx : ∀ i < n, limb s0.mem (State.addr b) x i < 65536) {i : Nat} (hi : i < n) {s : State}
    (h : MulDInv acc x n b s0 i s) :
    WP isa (.block (scalarRow acc x)) s fun s' =>
      MulDInv acc x n b s0 (i + 1) s' ∧ s'.z = decide (n - (i + 1) = 0) := by
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega_arith
  obtain hx0 : limb s.mem (State.addr b) x i = limb s0.mem (State.addr b) x i :=
    wd_outside h.frame (by omega_using [hxa, hi]) (by omega_using [hX, hi]) (by omega_using [hA])
  simp only [scalarRow, List.cons_append, List.nil_append]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * i)) (by omega_using [hX, hi])
    (by rw [h.r7, ea7 hfit (by omega_using [hX, hi]), Nat.add_comm])
    (h.ctx.inR (by omega_using [hX, hi])) fun s1 u1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  obtain hr2 : Rest [.r1, .r5] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx b s2 := h.ctx.of_rest hr2 (by decide)
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain e1 : (s2.gpr .r1).toNat = limb s0.mem (State.addr b) x i := by
    rw [u2.other _ (by decide), u1.gpr, ← hx0]; rfl
  obtain e7 : s2.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hr2.gpr _ (by decide), h.r7]
  obtain P7 : State.addr (s2.gpr .r7) = State.addr b + BitVec.ofNat 64 (4 * i) := by
    rw [e7]; exact addr7 hfit (by omega_using [hA, hi])
  obtain hlt : ∀ j < 9, rowC (accw acc s.mem (State.addr b)) (limb s0.mem (State.addr b) x)
      scalarD i j + 65536 ≤ 2 ^ 32 := fun j hj =>
    rowC_le (hlx i hi) (scalarD_lt j) (h.lt (i + j) (by omega_using [hj]))
  refine WP.append (passN_ok (rb := .r7) (o := acc) (s0 := s2)
    (c := rowC (accw acc s.mem (State.addr b)) (limb s0.mem (State.addr b) x) scalarD i)
    (cin := 0) (by decide) (by omega_using [hA])
    (by rw [e7, toNat7 hfit (by omega_using [hA, hi])]; omega_using [hA, hi, hfit])
    (fun k hk => by rw [P7, Offset.add_add]; exact hc2.inW (by omega_using [hA, hi, hk]))
    (by rw [hr2.gpr _ (by decide), h.r6]) (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    obtain hc' : Ctx b s' := hc2.of_rest hp'.rest (by decide)
    obtain hf' : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + acc), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [P7, Offset.add_add] at this
    simp only [scalarRowSrc, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (4 * i + (acc + 4 * k)))
      (by omega_using [hA, hk])
      (by rw [hp'.rest.gpr _ (by decide), e7, ea7 hfit (by omega_using [hA, hi, hk])])
      (hc'.inR (by omega_using [hA, hi, hk])) fun t1 v1 => ?_
    obtain e3 : (t1.gpr .r3).toNat = accw acc s.mem (State.addr b) (i + k) := by
      rw [v1.gpr, accw, ← hm2]
      show wd s'.mem _ _ = _
      rw [wd_outside hf' (.inr (by omega_arith)) (by omega_using [hA, hi, hk]) (by omega_using [hA, hi, hk])]
      congr 1; omega_arith
    obtain ea : (t1.gpr .r1).toNat = limb s0.mem (State.addr b) x i := by
      rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
    obtain hab := Nat.mul_le_mul (Nat.le_of_lt_succ (hlx i hi)) (Nat.le_of_lt_succ (scalarD_lt k))
    obtain hacc := h.lt (i + k) (by omega_using [hk])
    refine WP.mono (scalarMla_ok (scalarD_lt k) (by rw [ea, e3]; omega_using [hab, hacc]))
      fun t2 ⟨e2, k2, m2⟩ => ⟨?_, ?_, by rw [m2, v1.mem]⟩
    · rw [e2, ea, e3]; rfl
    · exact (v1.rest (by decide)).trans (k2.mono (by decide))
  · -- The carry, and the next row.
    obtain hc3 : Ctx b s3 := hc2.of_rest hp.rest (by decide)
    obtain e7' : s3.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [hp.rest.gpr _ (by decide), e7]
    refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * i + (acc + 36))) (by omega_using [hA, hi])
      (by rw [e7', ea7 hfit (by omega_using [hA, hi])]) (hc3.inW (by omega_using [hA, hi])) fun s4 u4 => ?_
    refine wp_dp (op2_imm (by decide)) fun s5 u5 => wp_subs (op2_imm (by decide)) fun s6 u6 hz => ?_
    refine WP.block_nil ?_
    obtain hr6 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s s6 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans (u6.rest (by decide)))))
    obtain hm6 : s6.mem = s3.mem.writeW (State.addr b + BitVec.ofNat 64 (4 * i + (acc + 36))) (s3.gpr .r5) := by
      rw [u6.mem, u5.mem, u4.mem]
    obtain hpf : Frame [⟨State.addr b + BitVec.ofNat 64 (4 * i + acc), 4 * 9⟩] s.mem s3.mem := by
      have := hp.frame; rw [P7, Offset.add_add] at this; rw [← hm2]; exact this
    obtain hr9 : s6.gpr .r9 = BitVec.ofNat 32 (n - (i + 1)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide), hr2.gpr _ (by decide), h.r9]
      have t1 : (1 : BitVec 32).toNat = 1 := rfl
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sub_le (by rw [toNat_imm (by omega_using [hA]), t1]; omega_using [hi]),
        toNat_imm (by omega_using [hA]), toNat_imm (by omega_using [hA]), t1]
      omega_arith
    -- The limbs of `acc` after the row.
    obtain hacc : ∀ k < i + (9 + 1), accw acc s6.mem (State.addr b) k =
        rowAccW 9 (accw acc s.mem (State.addr b)) (limb s0.mem (State.addr b) x) scalarD i k := by
      intro k hk
      rw [accw, hm6]
      rcases Nat.lt_or_ge k (i + 9) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_using [hA, hi, hk]) (by omega_using [hA, hi])]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_outside hpf (.inl (by omega_arith)) (by omega_using [hA, hi, hki]) (by omega_using [hA, hi])]
          simp only [rowAccW, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega_arith)
          rw [P7, wd_shift, show 4 * i + (acc + 4 * (k - i)) = acc + 4 * k by omega_arith] at this
          rw [this]
          simp only [rowAccW, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
      · rw [show acc + 4 * k = 4 * i + (acc + 36) by omega_arith, wd_write_self, hp.r5]
        simp only [rowAccW, show ¬ k < i by omega_arith, show ¬ k < i + 9 by omega_arith, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r7, .r9]).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
        (by decide), h.rest.trans hr6, by rw [hr6.gpr _ (by decide), h.r6], ?_, hr9, ?_,
      fun k hk => ?_, ?_⟩, ?_⟩
    · rw [u6.other _ (by decide), u5.gpr, u4.gpr, e7']
      show b + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = _
      rw [Offset.add_add, Nat.mul_succ]
    · rw [hm6]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_using [hi]) (by omega_using [hA]))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_using [hi])
    · rw [hacc k hk]
      exact rowAccW_lt (fun k hk => h.lt k (by omega_arith)) hlt k hk
    · rw [val16_congr hacc]; exact rowW_val h.val
    · rw [hz, ← u6.gpr, hr9, ofNat_beq_zero (by omega_using [hA])]

theorem scalarMulD_ok {acc x n : Nat} (hA : acc + 4 * (n + 9) ≤ 4096)
    (hX : x + 4 * n ≤ 4096) (hxa : x + 4 * n ≤ acc ∨ acc + 4 * (n + 9) ≤ x) (hn : 0 < n)
    (henc : encodable (BitVec.ofNat 32 n) = true) {s : State} (hc : Ctx b s)
    (h6 : s.gpr .r6 = mask16) (hlx : ∀ i < n, limb s.mem (State.addr b) x i < 65536) :
    WP isa (scalarMulD acc x n) s fun t =>
      Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 acc, 4 * (n + 9)⟩] s.mem t.mem ∧
      (∀ k < n + 9, accw acc t.mem (State.addr b) k < 65536) ∧
      val16 (accw acc t.mem (State.addr b)) (n + 9) =
        val16 (limb s.mem (State.addr b) x) n * val16 scalarD 9 := by
  unfold scalarMulD
  rw [List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s0 u0 => ?_)
  obtain hc0 : Ctx b s0 := hc.of_rest (u0.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.append (stores_ok (by omega_using [hA]) hc0) fun s1 ⟨hz, hf1, _, hr1⟩ => ?_
  obtain hc1 : Ctx b s1 := hc0.of_rest hr1 (by decide)
  refine wp_mov (op2_reg _ _) fun s2 u2 => wp_mov (op2_imm henc) fun s3 u3 => WP.block_nil ?_
  obtain hr3 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s s3 :=
    (u0.rest (by decide)).trans ((hr1.mono (by decide)).trans ((u2.rest (by decide)).trans
      (u3.rest (by decide))))
  obtain hm3 : s3.mem = s1.mem := by rw [u3.mem, u2.mem]
  obtain hz' : ∀ k < 9, accw acc s3.mem (State.addr b) k = 0 := fun k hk => by
    rw [accw, hm3, hz k hk, u0.gpr]; rfl
  obtain h0 : MulDInv acc x n b s 0 s3 := by
    refine ⟨hc.of_rest hr3 (by decide), hr3, by rw [hr3.gpr _ (by decide), h6], ?_, u3.gpr, ?_,
      fun k hk => ?_, ?_⟩
    · rw [u3.other _ (by decide), u2.gpr, hc1.r0]; exact (BitVec.add_zero b).symm
    · rw [hm3, ← u0.mem]; exact hf1.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩
    · rw [hz' k (by omega_using [hk])]; decide
    · rw [val16_congr (g := fun _ => 0) (fun k hk => hz' k (by omega_using [hk])), val16_zero_fn]
      exact (Nat.zero_mul _).symm
  refine WP.mono (Q := MulDInv acc x n b s n) (WP.loop (M := isa)
    (fun m t => ∃ i, m = n - i ∧ i < n ∧ MulDInv acc x n b s i t) ?_ n s3 ⟨0, rfl, hn, h0⟩)
    fun t ht => ⟨ht.rest, ht.frame, ht.lt, ht.val⟩
  rintro m t ⟨i, rfl, hi, ht⟩
  refine WP.mono (scalarRow_ok hA hX hxa hlx hi ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hl : i + 1 = n
  · refine .inl ⟨by rw [eval_ne, hz]; simp [hl], ?_⟩
    rw [hl] at hu; exact hu
  · exact .inr ⟨by rw [eval_ne, hz]; simp; omega_arith, n - (i + 1), by omega_arith,
      i + 1, rfl, by omega_arith, hu⟩

/-! ## The sum, its top and the subtraction -/

theorem scalarPass_result {x : Nat} {s t : State} {f : Nat → Nat} {cin : Nat}
    (hc : Ctx b s) (hp : PassInv .r0 x s f cin 16 t) :
    Frame [⟨State.addr b + BitVec.ofNat 64 x, 64⟩] s.mem t.mem ∧
    Lim t.mem (State.addr b) x ∧
    V t.mem (State.addr b) x + 2 ^ 256 * (t.gpr .r5).toNat = val16 f 16 + cin := by
  obtain outs : ∀ k < 16, limb t.mem (State.addr b) x k = out f cin k := by
    intro k hk; have he := hp.outs k hk; rwa [hc.r0] at he
  refine ⟨by have hf := hp.frame; rwa [hc.r0] at hf,
    fun k hk => by rw [outs k hk]; exact out_lt _ _ _, ?_⟩
  change val16 _ _ + _ = _
  rw [val16_congr outs, hp.r5]
  exact chain_val f cin 16

/-- The 32 limbs at `acc` are two numbers of 16. -/
theorem wide_split (acc : Nat) (m : Mem) (B : Addr) :
    val16 (accw acc m B) 32 = V m B acc + 2 ^ 256 * V m B (acc + 64) := by
  rw [show (32 : Nat) = 16 + 16 from rfl, val16_append]
  obtain he : val16 (fun k => accw acc m B (16 + k)) 16 = V m B (acc + 64) := by
    apply val16_congr
    intro k _
    unfold accw limb
    rw [show acc + 4 * (16 + k) = acc + 64 + 4 * k by omega_arith]
  rw [he]
  rfl

theorem scalarSum_ok {s : State} (hc : Ctx b s) (h6 : s.gpr .r6 = mask16)
    (hn : Lim s.mem (State.addr b) ACC) (hp1 : Lim s.mem (State.addr b) SQ1)
    (hp2 : Lim s.mem (State.addr b) SQ2) (hh : wd s.mem (State.addr b) (SQ2 + 64) ≤ 1) :
    WP isa (.block scalarSum) s fun t =>
      Rest [.r1, .r2, .r3, .r4, .r5] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 SR, 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) SR ∧ (t.gpr .r5).toNat < 65536 ∧
      V t.mem (State.addr b) SR + 2 ^ 256 * (t.gpr .r5).toNat =
        val16 (scalarSumC (limb s.mem (State.addr b) ACC) (limb s.mem (State.addr b) SQ1)
          (limb s.mem (State.addr b) SQ2) (1 - wd s.mem (State.addr b) (SQ2 + 64))) 16 + 1 := by
  have hA : ACC = 1472 := rfl
  have hR : SR = 256 := rfl
  have h1 : SQ1 = 384 := rfl
  have h2 : SQ2 = 512 := rfl
  have afit := hc.fit
  simp only [scalarSum, List.cons_append, List.nil_append]
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 =>
    wp_dp (op2_reg _ _) fun s3 u3 => wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  obtain k4 : Rest [.r1, .r2, .r5] s s4 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans (u4.rest (by decide))))
  obtain m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hc4 := hc.of_rest k4 (by decide)
  obtain e2 : (s2.gpr .r2).toNat = wd s.mem (State.addr b) (SQ2 + 64) := by
    rw [u2.other _ (by decide), u1.gpr]; rfl
  obtain g4 : (s4.gpr .r1).toNat = 1 - wd s.mem (State.addr b) (SQ2 + 64) := by
    rw [u4.other _ (by decide), u3.gpr]
    show (s2.gpr .r1 - s2.gpr .r2).toNat = _
    rw [toNat_sub_le (by rw [e2, u2.gpr]; exact hh), e2, u2.gpr]
    rfl
  obtain hle := scalarSumC_le (p1 := limb s.mem (State.addr b) SQ1) hn hp2
    (Nat.sub_le 1 (wd s.mem (State.addr b) (SQ2 + 64)))
  refine WP.mono (pass_ok (rb := .r0) (o := SR) (s0 := s4)
    (c := scalarSumC (limb s.mem (State.addr b) ACC) (limb s.mem (State.addr b) SQ1)
      (limb s.mem (State.addr b) SQ2) (1 - wd s.mem (State.addr b) (SQ2 + 64))) (cin := 1)
    (by decide) (by decide) (by rw [hc4.r0]; omega_using [hR, afit])
    (fun k hk => by rw [hc4.r0]; exact hc4.inW (by omega_using [hR, hk]))
    (by rw [k4.gpr _ (by decide), h6]) (by rw [u4.gpr]; rfl) hle (by decide) ?_) fun t ht => ?_
  · intro k hk t ht
    obtain hct := hc4.of_rest ht.rest (by decide)
    obtain rq : ∀ d, 384 ≤ d → d + 4 ≤ 4096 → wd t.mem (State.addr b) d = wd s.mem (State.addr b) d :=
      fun d hd hd' => by
        rw [wd_pass hc4 ht.frame (.inr (by omega_using [hR, hk, hd])) hd' (by omega_using [hR, hk]), m4]
    obtain ln := hn k hk
    obtain l1 := hp1 k hk
    obtain l2 := hp2 k hk
    simp only [scalarSumSrc, List.cons_append, List.nil_append]
    refine ldr0_ok hct (by omega_using [hA, hk]) fun v1 w1 => wp_dp (op2_reg _ _) fun v2 w2 => ?_
    obtain c2 := hct.of_rest ((w1.rest (ws := [.r2, .r3]) (by decide)).trans (w2.rest (by decide)))
      (by decide)
    refine ldr0_ok c2 (by omega_using [h1, hk]) fun v3 w3 => wp_dp (op2_reg _ _) fun v4 w4 => ?_
    obtain c4 := c2.of_rest ((w3.rest (ws := [.r2, .r3]) (by decide)).trans (w4.rest (by decide)))
      (by decide)
    refine ldr0_ok c4 (by omega_using [h2, hk]) fun v5 w5 => wp_dp (op2_reg _ _) fun v6 w6 => ?_
    obtain x1 : (v1.gpr .r3).toNat = limb s.mem (State.addr b) ACC k := by
      rw [w1.gpr]; exact rq _ (by omega_using [hA]) (by omega_using [hA, hk])
    obtain x2 : (v2.gpr .r3).toNat = limb s.mem (State.addr b) ACC k + 65535 := by
      rw [w2.gpr]
      show (v1.gpr .r3 + v1.gpr .r6).toNat = _
      rw [w1.other .r6 (by decide), ht.rest.gpr _ (by decide), k4.gpr _ (by decide), h6,
        toNat_add_lt (by rw [x1]; exact Nat.lt_trans (Nat.add_lt_add_right ln _) (by decide)), x1]
      rfl
    obtain x3 : (v3.gpr .r2).toNat = limb s.mem (State.addr b) SQ1 k := by
      rw [w3.gpr, w2.mem, w1.mem]; exact rq _ (by omega_using [h1]) (by omega_using [h1, hk])
    obtain x4 : (v4.gpr .r3).toNat =
        limb s.mem (State.addr b) ACC k + 65535 - limb s.mem (State.addr b) SQ1 k := by
      rw [w4.gpr]
      show (v3.gpr .r3 - v3.gpr .r2).toNat = _
      rw [w3.other .r3 (by decide), toNat_sub_le (by rw [x3, x2]; omega_using [l1]), x3, x2]
    obtain x5 : (v5.gpr .r2).toNat = limb s.mem (State.addr b) SQ2 k := by
      rw [w5.gpr, w4.mem, w3.mem, w2.mem, w1.mem]
      exact rq _ (by omega_using [h2]) (by omega_using [h2, hk])
    obtain x6 : (v6.gpr .r3).toNat = limb s.mem (State.addr b) ACC k + 65535 -
        limb s.mem (State.addr b) SQ1 k + limb s.mem (State.addr b) SQ2 k := by
      rw [w6.gpr]
      show (v5.gpr .r3 + v5.gpr .r2).toNat = _
      rw [w5.other .r3 (by decide), toNat_add_lt (by rw [x4, x5]; omega_using [ln, l2]), x4, x5]
    obtain y1 : (v6.gpr .r1).toNat = 1 - wd s.mem (State.addr b) (SQ2 + 64) := by
      rw [w6.other _ (by decide), w5.other _ (by decide), w4.other _ (by decide),
        w3.other _ (by decide), w2.other _ (by decide), w1.other _ (by decide),
        ht.rest.gpr _ (by decide), g4]
    obtain hk' := hle k hk
    simp only [scalarSumC] at hk'
    refine WP.mono (scalarMlaIf_ok (scalarD_lt k) (fun h9 => scalarD_high k hk (by omega_using [h9]))
      (by rw [y1, x6]; omega_using [hk'])) fun v7 ⟨e7, k7, m7⟩ => ⟨?_, ?_, by
        rw [m7, w6.mem, w5.mem, w4.mem, w3.mem, w2.mem, w1.mem]⟩
    · rw [e7, y1, x6, scalarSumC, Nat.add_comm]
    · exact (w1.rest (by decide)).trans ((w2.rest (by decide)).trans ((w3.rest (by decide)).trans
        ((w4.rest (by decide)).trans ((w5.rest (by decide)).trans ((w6.rest (by decide)).trans
          (k7.mono (by decide)))))))
  · obtain ⟨ft, lt, vt⟩ := scalarPass_result hc4 ht
    refine ⟨(k4.mono (by decide)).trans (ht.rest.mono (by decide)), by rw [← m4]; exact ft, lt, ?_, vt⟩
    rw [ht.r5]
    exact chain_lt hle (by decide) 16 (Nat.le_refl _)

theorem scalarTop_ok {s : State} (hc : Ctx b s) {c : Nat}
    (h5 : (s.gpr .r5).toNat = c) (hq : limb s.mem (State.addr b) SR 15 / 4096 + 16 * c ≤ 64) :
    WP isa (.block scalarTop) s fun t =>
      Rest [.r1, .r2, .r3, .r5] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 SR, 64⟩] s.mem t.mem ∧
      (∀ k < 16, limb t.mem (State.addr b) SR k = mask12 (limb s.mem (State.addr b) SR) k) ∧
      (t.gpr .r1).toNat = 64 - (limb s.mem (State.addr b) SR 15 / 4096 + 16 * c) ∧
      (t.gpr .r5).toNat = 0 := by
  have hR : SR = 256 := rfl
  unfold scalarTop
  refine ldr0_ok hc (by decide) fun s1 u1 => wp_mov (op2_lsr (by decide)) fun s2 u2 =>
    wp_dp (op2_lsl (by decide)) fun s3 u3 => wp_mov (op2_imm (by decide)) fun s4 u4 =>
    wp_dp (op2_reg _ _) fun s5 u5 => wp_mov (op2_lsl (by decide)) fun s6 u6 =>
    wp_mov (op2_lsr (by decide)) fun s7 u7 => ?_
  obtain k7 : Rest [.r1, .r2, .r3] s s7 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans
      ((u6.rest (by decide)).trans (u7.rest (by decide)))))))
  obtain m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine str0_ok (hc.of_rest k7 (by decide)) (by decide) fun s8 u8 =>
    wp_mov (op2_imm (by decide)) fun s9 u9 => WP.block_nil ?_
  obtain e1 : (s1.gpr .r3).toNat = limb s.mem (State.addr b) SR 15 := by rw [u1.gpr]; rfl
  obtain e2 : (s2.gpr .r2).toNat = limb s.mem (State.addr b) SR 15 / 4096 := by
    rw [u2.gpr, toNat_shr, e1]
  obtain e5 : (s2.gpr .r5 <<< 4).toNat = 16 * c := by
    rw [toNat_shl, u2.other _ (by decide), u1.other _ (by decide), h5]
    omega_using [hq]
  obtain e3 : (s3.gpr .r2).toNat = limb s.mem (State.addr b) SR 15 / 4096 + 16 * c := by
    rw [u3.gpr]
    show (s2.gpr .r2 + (s2.gpr .r5 <<< 4)).toNat = _
    rw [toNat_add_lt (by rw [e2, e5]; omega_using [hq]), e2, e5]
  obtain e7 : (s7.gpr .r3).toNat = limb s.mem (State.addr b) SR 15 % 4096 := by
    rw [u7.gpr, toNat_shr, u6.gpr, toNat_shl, u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), e1]
    omega_using []
  obtain m9 : s9.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (SR + 60)) (s7.gpr .r3) := by
    rw [u9.mem, u8.mem, m7]
  refine ⟨k7.mono (by decide) |>.trans ((u8.rest _).trans (u9.rest (by decide))), ?_,
    fun k hk => ?_, ?_, by rw [u9.gpr]; rfl⟩
  · rw [m9]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by decide) (by decide) (by decide))
  · rw [limb, m9]
    rcases Nat.lt_or_ge k 15 with hk' | hk'
    · rw [wd_write_other _ _ _ (by omega_using [hk']) (by omega_using [hR, hk]) (by decide)]
      simp only [mask12, show k ≠ 15 by omega_arith, ite_false]; rfl
    · obtain rfl : k = 15 := by omega_arith
      rw [show SR + 4 * 15 = SR + 60 from rfl, wd_write_self, e7]; rfl
  · rw [u9.other _ (by decide), u8.gpr, u7.other _ (by decide), u6.other _ (by decide), u5.gpr]
    show (s4.gpr .r1 - s4.gpr .r2).toNat = _
    rw [toNat_sub_le (by rw [u4.gpr, u4.other _ (by decide), e3]; exact hq), u4.gpr,
      u4.other _ (by decide), e3]
    rfl

theorem scalarLow_ok {s : State} (hc : Ctx b s) (h6 : s.gpr .r6 = mask16)
    (hl : Lim s.mem (State.addr b) SR) {g : Nat} (h1 : (s.gpr .r1).toNat = g) (hg : g ≤ 64)
    (h5 : (s.gpr .r5).toNat = 0) :
    WP isa (.block (pass .r0 SR scalarLowSrc)) s
      (PassInv .r0 SR s (scalarLowC (limb s.mem (State.addr b) SR) g) 0 16) := by
  have hR : SR = 256 := rfl
  have afit := hc.fit
  obtain hle := scalarLowC_le hl hg
  refine pass_ok (by decide) (by decide) (by rw [hc.r0]; omega_using [hR, afit])
    (fun k hk => by rw [hc.r0]; exact hc.inW (by omega_using [hR, hk])) h6 h5 hle (by decide) ?_
  intro k hk t ht
  obtain hct := hc.of_rest ht.rest (by decide)
  obtain lk := hl k hk
  obtain hk' := hle k hk
  simp only [scalarLowC] at hk'
  simp only [scalarLowSrc, List.cons_append, List.nil_append]
  refine ldr0_ok hct (by omega_using [hR, hk]) fun v1 w1 => ?_
  obtain x1 : (v1.gpr .r3).toNat = limb s.mem (State.addr b) SR k := by
    rw [w1.gpr]
    exact wd_pass hc ht.frame (.inr (by omega_arith)) (by omega_using [hR, hk]) (by omega_using [hR, hk])
  obtain y1 : (v1.gpr .r1).toNat = g := by rw [w1.other _ (by decide), ht.rest.gpr _ (by decide), h1]
  refine WP.append (scalarMlaIf_ok (scalarC_lt k) (fun h8 => scalarC_high k hk (by omega_using [h8]))
    (by rw [y1, x1]; omega_using [hk'])) fun v2 ⟨e2, k2, m2⟩ => ?_
  refine wp_movw fun v3 w3 => wp_dp (op2_reg _ _) fun v4 w4 => WP.block_nil ⟨?_, ?_, by
    rw [w4.mem, w3.mem, m2, w1.mem]⟩
  · have e3 : (v3.gpr .r2).toNat = scalarE k := by rw [w3.gpr]; exact toNat_movw (scalarE_lt k)
    rw [w4.gpr]
    show (v3.gpr .r3 + v3.gpr .r2).toNat = _
    rw [w3.other .r3 (by decide), toNat_add_lt (by rw [e2, e3, y1, x1]; omega_using [hk']), e2, e3,
      y1, x1, scalarLowC, Nat.add_comm (g * scalarC k)]
  · exact (w1.rest (by decide)).trans ((k2.mono (by decide)).trans ((w3.rest (by decide)).trans
      (w4.rest (by decide))))

/-- `SR` and the candidate after subtracting `L`. -/
def scalarSubRegions (b : BitVec 32) : List Region :=
  [⟨State.addr b + BitVec.ofNat 64 SR, 64⟩, ⟨State.addr b + BitVec.ofNat 64 SD, 64⟩]

theorem scalarCondSub_ok {s : State} (hc : Ctx b s) (h6 : s.gpr .r6 = mask16)
    (hl : Lim s.mem (State.addr b) SR) (hv : V s.mem (State.addr b) SR < 2 * L) :
    WP isa (.block scalarCondSub) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r9] s t ∧ Frame (scalarSubRegions b) s.mem t.mem ∧
      Lim t.mem (State.addr b) SR ∧ V t.mem (State.addr b) SR = V s.mem (State.addr b) SR % L := by
  have hR : SR = 256 := rfl
  have hD : SD = 320 := rfl
  rw [scalarCondSub, List.append_assoc, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have hc3 := hc.of_rest (u3.rest (ws := [.r5]) (by decide)) (by decide)
  refine WP.append (scalarSubtractPass_ok hc3 (u3.mem ▸ hl) (by rw [u3.gpr]; rfl)
    (by rw [u3.other _ (by decide), h6])) fun s4 h4 => ?_
  have subf := scalarSubtract_facts (f := limb s3.mem (State.addr b) SR)
    (by change V s3.mem (State.addr b) SR < _; rw [u3.mem]; exact hv)
  have f4 : Frame [⟨State.addr b + BitVec.ofNat 64 SD, 64⟩] s3.mem s4.mem := by
    have hf := h4.frame; rwa [hc3.r0] at hf
  have lr4 : ∀ k < 16, limb s4.mem (State.addr b) SR k = limb s3.mem (State.addr b) SR k :=
    limb_frame f4 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  have ld4 : ∀ k < 16, limb s4.mem (State.addr b) SD k =
      out (fun k => limb s3.mem (State.addr b) SR k + scalarComplement k) 1 k := by
    intro k hk; have he := h4.outs k hk; rwa [hc3.r0] at he
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => wp_dp (op2_reg _ _) fun s6 u6 => ?_
  have k6 : Rest [.r2, .r3, .r4, .r5, .r9] s s6 := (u3.rest (by decide)).trans
    ((h4.rest.mono (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))
  have m6 : s6.mem = s4.mem := by rw [u6.mem, u5.mem]
  have mask6 : s6.gpr .r9 = 0 - BitVec.ofNat 32
      (chain (fun k => limb s3.mem (State.addr b) SR k + scalarComplement k) 1 16) := by
    rw [u6.gpr]
    show s5.gpr .r9 - s5.gpr .r5 = _
    rw [u5.gpr, u5.other _ (by decide)]
    apply congrArg (fun x : BitVec 32 => 0 - x)
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm (by have := subf.1; omega_arith), h4.r5]
  refine WP.mono (cswap_ok (by decide) (by decide) (Or.inl (by decide))
    (hc.of_rest k6 (by decide)) subf.1 mask6) fun t ht => ?_
  have ltout : ∀ k < 16, limb t.mem (State.addr b) SR k =
      sel (chain (fun j => limb s3.mem (State.addr b) SR j + scalarComplement j) 1 16)
        (limb s3.mem (State.addr b) SR k)
        (out (fun j => limb s3.mem (State.addr b) SR j + scalarComplement j) 1 k) := by
    intro k hk
    rw [ht.lx k hk, m6, lr4 k hk, ld4 k hk]
  refine ⟨k6.trans (ht.rest.mono (by decide)), ?_, ?_, ?_⟩
  · have fb : Frame (scalarSubRegions b) s.mem s4.mem := by
      rw [← u3.mem]; exact f4.mono fun r hr => List.mem_cons_of_mem _ hr
    have fc : Frame (scalarSubRegions b) s4.mem t.mem := by rw [← m6]; exact ht.frame
    exact fb.trans fc
  · intro k hk
    rw [ltout k hk]; unfold sel
    split
    · exact out_lt _ _ _
    · rw [u3.mem]; exact hl k hk
  · unfold V
    rw [val16_congr ltout, subf.2, u3.mem]

/-! ## The reduction -/

abbrev scalarBodyClob : List Reg := [.r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9]

/-- What `scalarFold` writes: `SR`, `SD`, `SQ1` and `SQ2`. -/
def scalarFoldR (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 SR, 328⟩

theorem scalarFold_ok {s : State} (hc : Ctx b s)
    (la : ∀ k < 32, accw ACC s.mem (State.addr b) k < 65536) :
    WP isa scalarFold s fun t =>
      Rest scalarBodyClob s t ∧ Frame [scalarFoldR b] s.mem t.mem ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = val16 (accw ACC s.mem (State.addr b)) 32 % L := by
  have hA : ACC = 1472 := rfl
  have hR : SR = 256 := rfl
  have hD : SD = 320 := rfl
  have h1 : SQ1 = 384 := rfl
  have h2 : SQ2 = 512 := rfl
  obtain into : ∀ {o n : Nat}, 256 ≤ o → o + n ≤ 584 →
      (⟨State.addr b + BitVec.ofNat 64 o, n⟩ : Region).Sub (scalarFoldR b) :=
    fun ho hn => Offset.sub _ ho (by omega_using [hR, hn])
  obtain ln : Lim s.mem (State.addr b) ACC := fun k hk => la k (by omega_using [hk])
  obtain lh : Lim s.mem (State.addr b) (ACC + 64) := fun k hk => by
    have := la (16 + k) (by omega_using [hk])
    unfold accw at this
    rwa [show ACC + 4 * (16 + k) = ACC + 64 + 4 * k by omega_arith] at this
  unfold scalarFold
  refine WP.seq (wp_movw fun s1 u1 => WP.block_nil ?_)
  obtain hc1 := hc.of_rest (u1.rest (ws := [.r6]) (by decide)) (by decide)
  -- `P₁ = N₁ d`.
  refine WP.seq (WP.mono (scalarMulD_ok (acc := SQ1) (x := ACC + 64) (n := 16) (by decide) (by decide)
    (by decide) (by decide) (by decide) hc1 u1.gpr (u1.mem ▸ lh)) fun s2 ⟨k2, f2, l2, v2⟩ => ?_)
  obtain hc2 := hc1.of_rest k2 (by decide)
  rw [u1.mem] at f2 v2
  obtain lp1 : Lim s2.mem (State.addr b) SQ1 := fun k hk => l2 k (by omega_using [hk])
  obtain eq1 : ∀ k, accw SQ1 s2.mem (State.addr b) (16 + k) = limb s2.mem (State.addr b) (SQ1 + 64) k :=
    fun k => by unfold accw limb; rw [show SQ1 + 4 * (16 + k) = SQ1 + 64 + 4 * k by omega_arith]
  obtain lp1h : ∀ i < 9, limb s2.mem (State.addr b) (SQ1 + 64) i < 65536 := fun k hk => by
    rw [← eq1]; exact l2 (16 + k) (by omega_using [hk])
  rw [val16_append, val16_congr (fun k _ => eq1 k), scalarD_val9] at v2
  change V s2.mem (State.addr b) SQ1 + _ = V s.mem (State.addr b) (ACC + 64) * _ at v2
  -- `P₂ = (P₁ >> 256) d`.
  refine WP.seq (WP.mono (scalarMulD_ok (acc := SQ2) (x := SQ1 + 64) (n := 9) (by decide) (by decide)
    (by decide) (by decide) (by decide) hc2
    (by rw [k2.gpr _ (by decide), u1.gpr]) lp1h) fun s3 ⟨k3, f3, l3, v3⟩ => ?_)
  obtain hc3 := hc2.of_rest k3 (by decide)
  rw [show (9 + 9 : Nat) = 16 + (1 + 1) from rfl, val16_append, scalarD_val9] at v3
  change V s3.mem (State.addr b) SQ2 + _ = _ at v3
  obtain lp2 : Lim s3.mem (State.addr b) SQ2 := fun k hk => l3 k (by omega_using [hk])
  obtain sf := scalarSum_facts (N0 := V s.mem (State.addr b) ACC) (V_lt ln) (V_lt lh) (V_lt lp2) v2 v3
  obtain eh : val16 (fun k => accw SQ2 s3.mem (State.addr b) (16 + k)) (1 + 1) =
      wd s3.mem (State.addr b) (SQ2 + 64) := val16_low1 sf.1
  rw [eh] at sf v3
  -- The limbs the sum reads, as the products left them.
  obtain a3 : ∀ k < 16, limb s3.mem (State.addr b) ACC k = limb s.mem (State.addr b) ACC k :=
    fun k hk => by
      rw [limb, wd_outside f3 (.inr (by omega_arith)) (by omega_using [hA, hk]) (by decide),
        wd_outside f2 (.inr (by omega_arith)) (by omega_using [hA, hk]) (by decide)]
      rfl
  obtain p3 : ∀ k < 16, limb s3.mem (State.addr b) SQ1 k = limb s2.mem (State.addr b) SQ1 k :=
    fun k hk => by
      rw [limb, wd_outside f3 (.inl (by omega_using [h1, h2, hk])) (by omega_using [h1, hk]) (by decide)]
      rfl
  rw [List.append_assoc, List.append_assoc]
  refine WP.append (scalarSum_ok hc3 (by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), u1.gpr])
    (fun k hk => by rw [a3 k hk]; exact ln k hk) (fun k hk => by rw [p3 k hk]; exact lp1 k hk) lp2
    sf.1) fun s4 ⟨k4, f4, l4, c4, v4⟩ => ?_
  obtain hc4 := hc3.of_rest k4 (by decide)
  obtain h64 : s4.gpr .r6 = mask16 := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), u1.gpr]
  obtain sv := scalarSumC_val (n := limb s3.mem (State.addr b) ACC)
    (p1 := limb s3.mem (State.addr b) SQ1) (p2 := limb s3.mem (State.addr b) SQ2) (g := 1 - wd s3.mem (State.addr b) (SQ2 + 64))
    (fun k hk => by rw [p3 k hk]; exact lp1 k hk)
  change _ + V s3.mem (State.addr b) SQ1 + 1 =
    V s3.mem (State.addr b) ACC + _ + V s3.mem (State.addr b) SQ2 + _ at sv
  rw [show V s3.mem (State.addr b) ACC = V s.mem (State.addr b) ACC from val16_congr a3,
    show V s3.mem (State.addr b) SQ1 = V s2.mem (State.addr b) SQ1 from val16_congr p3] at sv
  obtain ⟨tlt, tmod⟩ := sf.2 (V s4.mem (State.addr b) SR + 2 ^ 256 * (s4.gpr .r5).toNat)
    (by omega_using [sv, v4])
  -- `T = l + 2²⁵² q`.
  obtain ⟨me, ml, mb⟩ := mask12_facts l4
  change V s4.mem (State.addr b) SR = _ at me
  obtain hq : limb s4.mem (State.addr b) SR 15 / 4096 + 16 * (s4.gpr .r5).toNat ≤ 64 := by
    omega_using [me, tlt]
  refine WP.append (scalarTop_ok hc4 rfl hq) fun s5 ⟨k5, f5, l5, g5, c5⟩ => ?_
  obtain hc5 := hc4.of_rest k5 (by decide)
  refine WP.append (scalarLow_ok hc5 (by rw [k5.gpr _ (by decide), h64])
    (fun k hk => by rw [l5 k hk]; exact mb k hk) g5 (Nat.sub_le _ _) c5) fun s6 h6 => ?_
  obtain ⟨f6, l6, v6⟩ := scalarPass_result hc5 h6
  obtain hc6 := hc5.of_rest h6.rest (by decide)
  rw [scalarLowC_val, show val16 (limb s5.mem (State.addr b) SR) 16 =
    val16 (mask12 (limb s4.mem (State.addr b) SR)) 16 from val16_congr l5, Nat.add_zero] at v6
  obtain ⟨ult, umod⟩ := scalarLow_facts ml hq
  obtain bound := order_bound
  obtain e6 : V s6.mem (State.addr b) SR = val16 (mask12 (limb s4.mem (State.addr b) SR)) 16 +
      (64 - (limb s4.mem (State.addr b) SR 15 / 4096 + 16 * (s4.gpr .r5).toNat)) * (L - 2 ^ 252) +
      (64 * 2 ^ 252 - 63 * L) := by
    obtain zero : (s6.gpr .r5).toNat = 0 := by
      rcases Nat.eq_zero_or_pos (s6.gpr .r5).toNat with hz | hp
      · exact hz
      · have := Nat.le_mul_of_pos_right (2 ^ 256) hp
        have := V_lt l6
        omega_using [this, v6, ult, bound, ‹2 ^ 256 ≤ 2 ^ 256 * (s6.gpr .r5).toNat›]
    rw [zero, Nat.mul_zero, Nat.add_zero] at v6
    exact v6
  refine WP.mono (scalarCondSub_ok hc6 (by rw [h6.rest.gpr _ (by decide), k5.gpr _ (by decide), h64])
    l6 (by rw [e6]; exact ult)) fun t ⟨kt, ft, lt, vt⟩ => ?_
  refine ⟨(u1.rest (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans
    ((k4.mono (by decide)).trans ((k5.mono (by decide)).trans ((h6.rest.mono (by decide)).trans
      (kt.mono (by decide))))))), ?_, lt, ?_⟩
  · obtain one : ∀ {m m' : Mem} {o n : Nat}, 256 ≤ o → o + n ≤ 584 →
        Frame [⟨State.addr b + BitVec.ofNat 64 o, n⟩] m m' → Frame [scalarFoldR b] m m' :=
      fun ho hn hf => hf.sub fun z hz => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hz]; exact into ho hn⟩
    obtain ft' : Frame [scalarFoldR b] s6.mem t.mem := ft.sub fun z hz => ⟨_, List.mem_singleton_self _, by
      simp only [scalarSubRegions, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> exact into (by decide) (by decide)⟩
    exact (one (by decide) (by decide) f2).trans ((one (by decide) (by decide) f3).trans
      ((one (by decide) (by decide) f4).trans ((one (by decide) (by decide) f5).trans
        ((one (by decide) (by decide) f6).trans ft'))))
  · rw [vt, e6, umod, wide_split, ← tmod]
    apply congrArg (· % L)
    omega_using [me]

/-! The complete 64-byte integer at `r12`, unpacked into `ACC` and reduced. -/

def scalarRegions (b : BitVec 32) : List Region := [scalarFoldR b, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩]

structure ScalarBodyKeep (b : BitVec 32) (s t : State) : Prop where
  rest : Rest scalarBodyClob s t
  frame : Frame (scalarRegions b) s.mem t.mem

theorem ScalarBodyKeep.ctx {s t : State} (h : ScalarBodyKeep b s t) (hc : Ctx b s) : Ctx b t :=
  hc.of_rest h.rest (by decide)

theorem scalarReduceEngine_ok {p : BitVec 32} {s : State} (hc : Ctx b s)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 64 ≤ 2 ^ 32)
    (hread : ∀ n < 64, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 n) 1)
    (hsep : ∀ r ∈ scalarRegions b, (⟨State.addr p, 64⟩ : Region).Disjoint r) :
    WP isa scalarReduceEngine s fun t => ScalarBodyKeep b s t ∧
      Lim t.mem (State.addr b) SR ∧
      V t.mem (State.addr b) SR = decodeLE (bytesAt s.mem (State.addr p) 64) % L := by
  have hA : ACC = 1472 := rfl
  obtain sepA : (⟨State.addr p, 64⟩ : Region).Disjoint ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩ :=
    hsep _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  obtain inA : ∀ {o n : Nat}, 1472 ≤ o → o + n ≤ 1600 →
      (⟨State.addr b + BitVec.ofNat 64 o, n⟩ : Region).Sub ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩ :=
    fun ho hn => Offset.sub _ ho (by omega_using [hA, hn])
  unfold scalarReduceEngine
  refine WP.seq (WP.append (unpackField_ok (p := p) (o := ACC) (src := 0) hc (by decide) (by decide) hp
    (by omega_using [hfit])
    (fun i hi => by simpa only [Nat.zero_add] using hread i (by omega_using [hi]))
    (by rw [BitVec.add_zero]
        exact (sepA.sub_left (Region.sub_prefix (by decide))).sub_right (inA (by decide) (by decide))))
    fun u ⟨ku, fu, lu, vu⟩ => ?_)
  obtain hcu := hc.of_rest ku (by decide)
  refine WP.mono (unpackField_ok (p := p) (o := ACC + 64) (src := 32) hcu (by decide) (by decide)
    ((ku.gpr _ (by decide)).trans hp) (by omega_using [hfit])
    (fun i hi => by rw [ku.rd, ku.wr]; exact hread (32 + i) (by omega_using [hi]))
    ((sepA.sub_left (Offset.sub_base _ (by decide))).sub_right (inA (by decide) (by decide))))
    fun v ⟨kv, fv, lv, vv⟩ => ?_
  obtain hcv := hcu.of_rest kv (by decide)
  obtain av : ∀ k < 16, limb v.mem (State.addr b) ACC k = limb u.mem (State.addr b) ACC k :=
    fun k hk => wd_outside fv (.inl (by omega_arith)) (by omega_using [hA, hk]) (by decide)
  obtain la : ∀ k < 32, accw ACC v.mem (State.addr b) k < 65536 := by
    intro k hk
    rcases Nat.lt_or_ge k 16 with hk16 | hk16
    · rw [show accw ACC v.mem (State.addr b) k = limb v.mem (State.addr b) ACC k from rfl, av k hk16]
      exact lu k hk16
    · have he : accw ACC v.mem (State.addr b) k = limb v.mem (State.addr b) (ACC + 64) (k - 16) := by
        unfold accw limb; rw [show ACC + 4 * k = ACC + 64 + 4 * (k - 16) by omega_arith]
      rw [he]; exact lv _ (by omega_arith)
  refine WP.mono (scalarFold_ok hcv la) fun t ⟨kt, ft, lt, vt⟩ => ⟨⟨(ku.mono (by decide)).trans
    ((kv.mono (by decide)).trans kt), ?_⟩, lt, ?_⟩
  · obtain fu' : Frame (scalarRegions b) s.mem u.mem := fu.sub fun z hz =>
      ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
        rw [List.mem_singleton.mp hz]; exact inA (by decide) (by decide)⟩
    obtain fv' : Frame (scalarRegions b) u.mem v.mem := fv.sub fun z hz =>
      ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), by
        rw [List.mem_singleton.mp hz]; exact inA (by decide) (by decide)⟩
    exact fu'.trans (fv'.trans (ft.mono fun z hz => by
      rw [List.mem_singleton.mp hz]; exact List.mem_cons_self))
  · rw [vt, wide_split, show V v.mem (State.addr b) ACC = V u.mem (State.addr b) ACC from
      val16_congr av, vu, vv, BitVec.add_zero]
    rw [packedV_frame fu (fun z hz => by
      rw [List.mem_singleton.mp hz]
      exact (sepA.sub_left (Offset.sub_base _ (by decide))).sub_right (inA (by decide) (by decide)))]
    apply congrArg (· % L)
    change _ = decodeLE (Spec.X25519.bytesAt s.mem _ (32 + 32))
    rw [VG.Proof.X25519.bytesAt_add, decodeLE_append, VG.Proof.X25519.length_bytesAt]
    change _ = decodeLE (bytesAt s.mem _ 32) + 256 ^ 32 * decodeLE (bytesAt s.mem _ 32)
    rw [scalar_packed_decode, scalar_packed_decode]

end VG.Proof.Ed25519.Arm
