module

import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarReduce
public import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.X25519.RISCV64.AddSub
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarCompare
import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarLoop
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Base

/-!
# `vg_ed25519_scalar_mul_add` on RISCV64: correctness

The function rounds `scratch` up (`align_ok`), copies `r`, `k` and `s` to
bytes 64, 96 and 128 of it, a word at a time, computes the 512-bit `k s` row by
row at `ACC` (X25519's product, `wideMul_ok`), adds `r` (`wideAdd_ok`),
stores the sum's 64 bytes at byte 512 (`packWide_ok`), reduces them modulo
`L` (`engine_ok`) and copies the remainder to `out`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (L decodeLE bytesAt)
open VG.Proof.X25519

section
variable {b : Addr}

theorem wideMul_ok {x y : Nat} (hx : x + 32 ≤ ACC) (hy : y + 32 ≤ ACC) (hx4 : x % 4 = 0)
    (hy4 : y % 4 = 0) {s : State} (hc : Ctx b s) :
    WP isa (scalarWideMul x y) s (RowInv ACC b x y s 8) := by
  have hA := eACC_eq
  unfold scalarWideMul
  refine WP.seq (WP.mono (mulPre_ok (by omega_arith) (by decide) (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.loop (M := isa) (fun n s' => ∃ i, n = 8 - i ∧ i < 8 ∧ RowInv ACC b x y s i s') ?_ 8 s1
    ⟨0, rfl, by decide, h1⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok (by omega_arith) hx hy (by decide) hx4 hy4 hi hr) fun s'' ⟨hr', hz⟩ => ?_
  by_cases h8 : i + 1 = 8
  · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h8], ?_⟩
    rw [h8] at hr'; exact hr'
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 8 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hr'⟩

/-- The sum's limbs: `k s + r`, at `ACC`. -/
theorem wideAdd_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 16 + V s.mem b 64 < 2 ^ 512) :
    WP isa (.block (scalarWideAdd 64)) s fun t =>
      Rest [.a2, .a4, .a5] s t ∧ Frame [⟨b + BitVec.ofNat 64 ACC, 64⟩] s.mem t.mem ∧
      val32 (accw ACC t.mem b) 16 = val32 (accw ACC s.mem b) 16 + V s.mem b 64 := by
  have hA := eACC_eq
  have hl : ∀ k < 16, accw ACC s.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
  have hr : ∀ k < 8, limb s.mem b 64 k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  unfold scalarWideAdd
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.a5]) (by decide)) (by decide)
  let c1 : Nat → Nat := fun k => accw ACC s.mem b k + limb s.mem b 64 k
  refine WP.append (pass_ok (s0 := s1) (c := c1) (cin := 0) (by decide) (by omega_arith)
    (fun k hk => by rw [hc1.a3]; exact hc1.inW (by omega_arith))
    (fun _ _ => by rw [hc1.a3]; exact al4 hc1.al (by omega_arith)) (by rw [u1.gpr]; rfl)
    (fun k hk => by have := hl k (by omega_arith); have := hr k hk; simp only [c1]; omega_arith) (by decide) ?_)
    fun s2 hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
    simp only [Impl.X25519.RISCV64.addSrc]
    refine lw0_ok hc' (d := ACC + 4 * k) (by omega_arith) (by omega_arith) fun t1 v1 => ?_
    refine lw0_ok (hc'.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)) (d := 64 + 4 * k) (by omega_arith)
      (by omega_arith) fun t2 v2 => wp_add fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
    · have ea : wd s'.mem b (ACC + 4 * k) = accw ACC s.mem b k := by
        rw [wd_pass hc1 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u1.mem]; rfl
      have er : wd t1.mem b (64 + 4 * k) = limb s.mem b 64 k := by
        rw [v1.mem, wd_pass hc1 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u1.mem]; rfl
      have := hl k (by omega_arith); have := hr k hk
      rw [v3.gpr, v2.other .a4 (by decide), v1.gpr, v2.gpr]
      unfold wd at ea er
      rw [toNat_add_lt (by rw [toNat_ext32, toNat_ext32, ea, er]; omega_arith), toNat_ext32, toNat_ext32, ea, er]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))
  -- The high half, with the carry.
  have hr2 : Rest [.a2, .a4, .a5] s s2 := (u1.rest (by decide)).trans hp.rest
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have hf2 : Frame [⟨b + BitVec.ofNat 64 ACC, 32⟩] s.mem s2.mem := by
    have := hp.frame; rw [hc1.a3, show 4 * 8 = 32 from rfl] at this; rw [← u1.mem]; exact this
  have hlo : ∀ j < 8, accw ACC s2.mem b j = out c1 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.a3] at this
  have hhi : ∀ j < 8, accw ACC s2.mem b (8 + j) = accw ACC s.mem b (8 + j) := fun j hj => by
    unfold accw
    refine wd_frame hf2 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  let c2 : Nat → Nat := fun k => accw ACC s.mem b (8 + k)
  have hch1 : chain c1 0 8 ≤ 1 := by
    have hv := chain_val c1 0 8
    have h1 := val32_lt (f := accw ACC s.mem b) (n := 8) fun k hk => hl k (by omega_arith)
    have h2 := V_lt s.mem b 64
    have hc1v : val32 c1 8 = val32 (accw ACC s.mem b) 8 + V s.mem b 64 := by
      simp only [c1]; rw [val32_add]; rfl
    rw [show 32 * 8 = 256 from rfl] at hv h1
    rcases Nat.lt_or_ge (chain c1 0 8) 2 with h | h
    · omega_arith
    · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h; omega_arith
  refine WP.mono (pass_ok (s0 := s2) (c := c2) (cin := chain c1 0 8) (by decide) (by omega_arith)
    (fun k hk => by rw [hc2.a3]; exact hc2.inW (by omega_arith))
    (fun _ _ => by rw [hc2.a3]; exact al4 hc2.al (by omega_arith)) hp.a5
    (fun k hk => by have := hl (8 + k) (by omega_arith); simp only [c2]; omega_arith) (by omega_arith) ?_) fun t hq => ?_
  · intro k hk s' hq
    have hc' : Ctx b s' := hc2.of_rest hq.rest (by decide)
    refine WP.mono (ldSrc_ok hc' (o := ACC + 32) (k := k) (by omega_arith) (by omega_arith)) fun t1 ⟨e1, r1, m1⟩ => ⟨?_, r1.mono (by decide), m1⟩
    rw [e1, wd_pass hc2 hq.frame (by omega_arith) (by omega_arith) (by omega_arith), show ACC + 32 + 4 * k = ACC + 4 * (8 + k) by omega_arith]
    exact hhi k hk
  · have hfq : Frame [⟨b + BitVec.ofNat 64 (ACC + 32), 32⟩] s2.mem t.mem := by
      have := hq.frame; rwa [hc2.a3, show 4 * 8 = 32 from rfl] at this
    refine ⟨hr2.trans hq.rest, ?_, ?_⟩
    · refine (hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hfq.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · have hlo' : ∀ j < 8, accw ACC t.mem b j = out c1 0 j := fun j hj => by
        rw [← hlo j hj]
        unfold accw
        refine wd_frame hfq fun r hr => ?_
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      have hhi' : ∀ j < 8, accw ACC t.mem b (8 + j) = out c2 (chain c1 0 8) j := fun j hj => by
        have := hq.outs j hj
        rw [hc2.a3] at this
        unfold accw
        rw [show ACC + 4 * (8 + j) = ACC + 32 + 4 * j by omega_arith]; exact this
      have v1 := chain_val c1 0 8
      have v2 := chain_val c2 (chain c1 0 8) 8
      have hc1v : val32 c1 8 = val32 (accw ACC s.mem b) 8 + V s.mem b 64 := by
        simp only [c1]; rw [val32_add]; rfl
      have hsum : val32 (accw ACC t.mem b) 16 = val32 (out c1 0) 8 + 2 ^ 256 * val32 (out c2 (chain c1 0 8)) 8 := by
        rw [show (16 : Nat) = 8 + 8 from rfl, val32_append, val32_congr hlo', val32_congr hhi']
      have hs16 : val32 (accw ACC s.mem b) 16 = val32 (accw ACC s.mem b) 8 + 2 ^ 256 * val32 c2 8 := by
        rw [show (16 : Nat) = 8 + 8 from rfl, val32_append]
      -- The final carry is zero: the sum is below `2^512`.
      have ho2 := (pass_value (c := c2) (cin := chain c1 0 8)).2
      rw [show 32 * 8 = 256 from rfl] at v1 v2
      have hch2 : chain c2 (chain c1 0 8) 8 = 0 := by
        rcases Nat.eq_zero_or_pos (chain c2 (chain c1 0 8) 8) with h | h
        · exact h
        · exfalso
          have := Nat.mul_le_mul_left (2 ^ 256) h
          have : val32 c2 8 + chain c1 0 8 < 2 ^ 256 := by
            rcases Nat.lt_or_ge (val32 c2 8 + chain c1 0 8) (2 ^ 256) with h' | h'
            · exact h'
            · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h'; omega_arith
          omega_arith
      rw [hch2, Nat.mul_zero, Nat.add_zero] at v2
      rw [hsum, v2]
      omega_arith

/-- 64 bytes, as their two halves' words. -/
theorem decode64 (m : Mem) (q : Addr) :
    decodeLE (bytesAt m q 64) = decodeLE (bytesAt m q 32) + 2 ^ 256 * decodeLE (bytesAt m (q + 32) 32) := by
  rw [Proof.Ed25519.decodeLE_eq, Proof.Ed25519.decodeLE_eq, Proof.Ed25519.decodeLE_eq]
  show Proof.X25519.leNum (Spec.X25519.bytesAt m q (32 + 32)) = _
  rw [Proof.X25519.bytesAt_add, Proof.X25519.leNum_append, Proof.X25519.length_bytesAt]
  rfl

/-- The sum's 64 bytes, at byte 512 of the working space. -/
theorem packWide_ok {s : State} (hc : Ctx b s) :
    WP isa (.block scalarPackWide) s fun t =>
      Rest [.a4, .a5, .t3] s t ∧ Frame [⟨b + BitVec.ofNat 64 512, 64⟩] s.mem t.mem ∧
      t.gpr .t3 = b + BitVec.ofNat 64 512 ∧
      decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 512) 64) = val32 (accw ACC s.mem b) 16 := by
  have hA := eACC_eq
  unfold scalarPackWide
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) fun s1 u1 => ?_
  have e14 : s1.gpr .t3 = b + BitVec.ofNat 64 512 := by rw [u1.gpr, hc.a3]
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.t3]) (by decide)) (by decide)
  have hw : ∀ (t : State), Ctx b t → ∀ d, d + 32 ≤ 64 → ∀ k < 8,
      InRegions t.wr (b + BitVec.ofNat 64 512 + BitVec.ofNat 64 (d + 4 * k)) 4 := fun t ht d hd k hk => by
    rw [Offset.add_add]; exact ht.inW (by omega_arith)
  have hd : ∀ d a, d + 32 ≤ 64 → a + 32 ≤ 512 ∨ 576 ≤ a → a + 32 ≤ 2048 →
      (⟨b + BitVec.ofNat 64 512 + BitVec.ofNat 64 d, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 32⟩ :=
    fun d a hd ha ha' => by rw [Offset.add_add]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  refine WP.append (packField_ok hc1 (p := .t3) (by decide) e14 (a := ACC) (dst := 0) (by omega_arith) (by decide) (by decide)
    (hw _ hc1 0 (by omega_arith))
    (hd 0 ACC (by omega_arith) (by omega_arith) (by omega_arith))) fun s2 h2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest h2.rest (by decide)
  refine WP.mono (packField_ok hc2 (p := .t3) (by decide) (by rw [h2.rest.gpr _ (by decide), e14])
    (a := ACC + 32) (dst := 32) (by omega_arith) (by decide) (by decide) (hw _ hc2 32 (by omega_arith)) (hd 32 (ACC + 32) (by omega_arith) (by omega_arith) (by omega_arith)))
    fun t h3 => ⟨(u1.rest (by decide)).trans ((h2.rest.trans h3.rest).mono (by decide)), ?_,
      by rw [h3.rest.gpr _ (by decide), h2.rest.gpr _ (by decide), e14], ?_⟩
  · rw [← u1.mem]
    have f2 := h2.frame
    have f3 := h3.frame
    rw [Offset.add_add] at f2 f3
    refine (f2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (f3.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · have hq : ∀ j < 8, wd t.mem b (512 + 4 * j) = wd s2.mem b (512 + 4 * j) := fun j hj => by
      have f3 := h3.frame
      rw [Offset.add_add] at f3
      refine wd_frame f3 fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    have hhi : ∀ j < 8, limb s2.mem b (ACC + 32) j = limb s1.mem b (ACC + 32) j := fun j hj => by
      have f2 := h2.frame
      rw [Offset.add_add] at f2
      refine wd_frame f2 fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    have lo : decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 512) 32) = V s1.mem b ACC := by
      refine bytes_of_words fun j hj => ?_
      rw [wd_shift, hq j hj, ← wd_shift, ← Nat.zero_add (4 * j)]
      exact h2.outs j hj
    have hi : decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 512 + 32) 32) = V s1.mem b (ACC + 32) := by
      rw [show b + BitVec.ofNat 64 512 + 32 = b + BitVec.ofNat 64 544 by rw [BitVec.add_assoc]; rfl]
      refine bytes_of_words fun j hj => ?_
      have := h3.outs j hj
      rw [wd_shift] at this
      rw [wd_shift, show 544 + 4 * j = 512 + (32 + 4 * j) by omega_arith, this, hhi j hj]
    rw [decode64, lo, hi, u1.mem, show (16 : Nat) = 8 + 8 from rfl, val32_append]
    have e2 : limb s.mem b (ACC + 32) = fun k => accw ACC s.mem b (8 + k) :=
      funext fun k => show wd s.mem b (ACC + 32 + 4 * k) = wd s.mem b (ACC + 4 * (8 + k)) from
        congrArg (wd s.mem b) (by omega_arith)
    rw [V, V, e2]
    rfl

theorem lowsub (b : Addr) {d n : Nat} (h : d + n ≤ 1024) : Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ ⟨b, 1024⟩ :=
  Offset.sub_base b h

/-- Bytes apart from the working space keep their values through writes within it. -/
theorem bytes_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 1024⟩) {q : Addr} {n : Nat}
    (hd : (⟨q, n⟩ : Region).Disjoint ⟨b, 1024⟩) (hn : n < 2 ^ 64) : bytesAt m' q n = bytesAt m q n := by
  simp only [bytesAt, List.map_inj_left]
  intro i hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by have := List.mem_range.mp hi; omega_arith)
    (by have := List.mem_range.mp hi; omega_arith)) (hs r hr _ hc)

/-- `k s + r` modulo `L`, into `SR`, writing nothing above byte 1023. -/
theorem mulAddEngine_ok {b : Addr} {s : State} (hc : Ctx b s) {R K Sc : Nat} (hVr : V s.mem b 64 = R)
    (hVk : V s.mem b 96 = K) (hVs : V s.mem b 128 = Sc) :
    WP isa scalarMulAddEngine s fun t =>
      Rest [.a1, .a2, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s t ∧ Frame [⟨b, 1024⟩] s.mem t.mem ∧
      V t.mem b SR = (K * Sc + R) % L := by
  have hA := eACC_eq
  have hS := SR_eq
  unfold scalarMulAddEngine
  refine WP.seq (WP.mono (wideMul_ok (x := 96) (y := 128) (by omega_arith) (by omega_arith) (by decide) (by decide) hc) fun s8 h8 => ?_)
  have hc8 : Ctx b s8 := h8.ctx
  have hv8 : val32 (accw ACC s8.mem b) 16 = K * Sc := by rw [← hVk, ← hVs]; exact h8.val
  have hr8 : V s8.mem b 64 = R := by
    rw [← hVr]; unfold V
    exact val32_congr (limb_frame h8.frame fun r hr j hj => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
  have hK256 : K < 2 ^ 256 := by rw [← hVk]; exact V_lt _ _ _
  have hS256 : Sc < 2 ^ 256 := by rw [← hVs]; exact V_lt _ _ _
  have hR256 : R < 2 ^ 256 := by rw [← hr8]; exact V_lt _ _ _
  have hprod : K * Sc ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  refine WP.seq (WP.append (wideAdd_ok hc8 (by rw [hv8, hr8]; omega_arith)) fun s9 ⟨r9, f9, v9⟩ => ?_)
  have hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.mono (packWide_ok hc9) fun s10 ⟨r10, f10, e10, v10⟩ => ?_
  have hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  have sub1 : ∀ o n, o + n ≤ 1024 → ∀ r ∈ ([⟨b + BitVec.ofNat 64 o, n⟩] : List Region),
      ∃ r' ∈ ([⟨b, 1024⟩] : List Region), r.Sub r' := fun o n ho r hr =>
    ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact lowsub b ho⟩
  refine WP.mono (engine_ok hc10 (p := b + BitVec.ofNat 64 512) e10
    (fun k hk => by rw [Offset.add_add]; exact hc10.inR (by omega_arith))) fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_⟩
  · exact (h8.rest.mono (by decide)).trans ((r9.mono (by decide)).trans ((r10.mono (by decide)).trans
      (rt.mono (by decide))))
  · exact (h8.frame.sub (sub1 ACC 64 (by omega_arith))).trans ((f9.sub (sub1 ACC 64 (by omega_arith))).trans
      ((f10.sub (sub1 512 64 (by omega_arith))).trans (ft.sub (sub1 SR 64 (by omega_arith)))))
  · rw [vt, v10, v9, hv8, hr8]

end

/-- The precondition, by register: `out` in `a0`, `r`, `k` and `s` in `a1`–`a3`, `scratch` in `a4`. -/
structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 32⟩, ⟨s.gpr .a2, 32⟩, ⟨s.gpr .a3, 32⟩]
  wr : s.wr = [⟨s.gpr .a0, 32⟩, ⟨s.gpr .a4, 8192⟩]
  out_ws : (⟨s.gpr .a0, 32⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  r_ws : (⟨s.gpr .a1, 32⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  k_ws : (⟨s.gpr .a2, 32⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  s_ws : (⟨s.gpr .a3, 32⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩

/-- The low 1024 bytes of the rounded working space, in `scratch`. -/
theorem low_sub (q : Addr) : Region.Sub ⟨base q, 1024⟩ ⟨q, 8192⟩ := by
  have := base_sub q (o := 0) (n := 1024) (by decide)
  rwa [BitVec.add_zero] at this

/-- An input's 32 bytes at `p`, into the element at `o`. -/
theorem loadInput_ok {b : Addr} {s : State} (hc : Ctx b s) {o : Nat} (ho : o + 32 ≤ 1024) (ho4 : o % 4 = 0)
    {p : Reg} (hp : p ∉ [Reg.a4, .a5]) {q : Addr} (hq : s.gpr p = q) (hr : (⟨q, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : (⟨q, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 o, 32⟩) :
    WP isa (.block (unpackField p o 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem t.mem ∧
      V t.mem b o = decodeLE (bytesAt s.mem q 32) := by
  refine WP.mono (unpackField_ok hc hp hq (src := 0) (by omega) ho4 (by decide)
    (fun k hk => in_base hr (by omega) (by omega)) (by rw [BitVec.add_zero]; exact hd))
    fun t ⟨rt, ft, lt⟩ => ⟨rt, ft, (bytes_of_words fun j hj => by rw [lt j hj, Nat.zero_add]).symm⟩

/-- After the arguments of `scalar_mul_add`, from `s`. -/
structure ArgsPost (s : State) (t : State) : Prop where
  ctx : Ctx (base (s.gpr .a4)) t
  rest : Rest [.a3, .a4, .a5, .t5] s t
  vr : V t.mem (base (s.gpr .a4)) 64 = decodeLE (bytesAt s.mem (s.gpr .a1) 32)
  vk : V t.mem (base (s.gpr .a4)) 96 = decodeLE (bytesAt s.mem (s.gpr .a2) 32)
  vs : V t.mem (base (s.gpr .a4)) 128 = decodeLE (bytesAt s.mem (s.gpr .a3) 32)

theorem mulAddArgs_ok {s : State} (hp : MulAddPre s) : WP isa (.block scalarMulAddArgs) s (ArgsPost s) := by
  have hws : (⟨s.gpr .a4, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hrin : ∀ r : Reg, r = .a1 ∨ r = .a2 ∨ r = .a3 → (⟨s.gpr r, 32⟩ : Region) ∈ s.rd ++ s.wr := by
    rintro r (rfl | rfl | rfl) <;> (rw [hp.rd]; simp)
  unfold scalarMulAddArgs
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mv fun s1 u1 => wp_mv fun s2 u2 => ?_
  refine WP.append (align_ok (q := s.gpr .a4) (by rw [u2.gpr, u1.other _ (by decide)])
    (by rw [u2.wr, u1.wr]; exact hws)) fun s3 ⟨hc3, hr3, hm3⟩ => ?_
  let B := base (s.gpr .a4)
  have hr03 : Rest [.a3, .t5] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (hr3.mono (by decide)))
  have hm03 : s3.mem = s.mem := by rw [hm3, u2.mem, u1.mem]
  have g3 : ∀ r : Reg, r = .a1 ∨ r = .a2 → s3.gpr r = s.gpr r := by
    rintro r (rfl | rfl) <;> exact hr03.gpr _ (by decide)
  have e15 : s3.gpr .t5 = s.gpr .a3 := by
    rw [hr3.gpr _ (by decide), u2.other _ (by decide), u1.gpr]
  have hdws : ∀ r : Reg, r = .a1 ∨ r = .a2 ∨ r = .a3 →
      (⟨s.gpr r, 32⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩ := by
    rintro r (rfl | rfl | rfl)
    · exact hp.r_ws
    · exact hp.k_ws
    · exact hp.s_ws
  have hlow : ∀ o, o + 32 ≤ 1024 → ∀ r : Reg, r = .a1 ∨ r = .a2 ∨ r = .a3 →
      (⟨s.gpr r, 32⟩ : Region).Disjoint ⟨B + BitVec.ofNat 64 o, 32⟩ := fun o ho r hr =>
    (hdws r hr).sub_right (base_sub _ (by omega))
  refine WP.append (loadInput_ok hc3 (o := 64) (by decide) (by decide) (p := .a1) (by decide)
    (g3 _ (.inl rfl)) (by rw [hr03.rd, hr03.wr]; exact hrin _ (.inl rfl)) (hlow 64 (by decide) _ (.inl rfl)))
    fun s5 ⟨rr5, f5, v5⟩ => ?_
  have hc5 : Ctx B s5 := hc3.of_rest rr5 (by decide)
  refine WP.append (loadInput_ok hc5 (o := 96) (by decide) (by decide) (p := .a2) (by decide)
    (by rw [rr5.gpr _ (by decide), g3 _ (.inr rfl)])
    (by rw [rr5.rd, rr5.wr, hr03.rd, hr03.wr]; exact hrin _ (.inr (.inl rfl)))
    (hlow 96 (by decide) _ (.inr (.inl rfl)))) fun s6 ⟨rr6, f6, v6⟩ => ?_
  have hc6 : Ctx B s6 := hc5.of_rest rr6 (by decide)
  refine WP.mono (loadInput_ok hc6 (o := 128) (by decide) (by decide) (p := .t5) (by decide)
    (by rw [rr6.gpr _ (by decide), rr5.gpr _ (by decide), e15])
    (by rw [rr6.rd, rr6.wr, rr5.rd, rr5.wr, hr03.rd, hr03.wr]; exact hrin _ (.inr (.inr rfl)))
    (hlow 128 (by decide) _ (.inr (.inr rfl)))) fun s7 ⟨rr7, f7, v7⟩ => ?_
  have sub1 : ∀ o, o + 32 ≤ 1024 → ∀ r ∈ ([⟨B + BitVec.ofNat 64 o, 32⟩] : List Region),
      ∃ r' ∈ ([⟨B, 1024⟩] : List Region), r.Sub r' := fun o ho r hr =>
    ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact lowsub B ho⟩
  -- The inputs' bytes, kept by the copies.
  have keep : ∀ {m' : Mem}, Frame [⟨B, 1024⟩] s3.mem m' → ∀ r : Reg, r = .a1 ∨ r = .a2 ∨ r = .a3 →
      bytesAt m' (s.gpr r) 32 = bytesAt s.mem (s.gpr r) 32 := fun hf r hr => by
    have hd := (hdws r hr).sub_right (low_sub _)
    rw [bytes_keep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) hd (by decide), hm03]
  have disj : ∀ o o', o + 32 ≤ o' ∨ o' + 32 ≤ o → o + 32 ≤ 2048 → o' + 32 ≤ 2048 →
      ∀ r ∈ ([⟨B + BitVec.ofNat 64 o', 32⟩] : List Region), ∀ k < 8,
        (⟨B + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r := fun o o' h h1 h2 r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨hc6.of_rest rr7 (by decide), (hr03.mono (by decide)).trans ((rr5.trans (rr6.trans rr7)).mono (by decide)),
    ?_, ?_, ?_⟩
  · rw [V, val32_congr (limb_frame f7 (disj 64 128 (by decide) (by decide) (by decide))),
      val32_congr (limb_frame f6 (disj 64 96 (by decide) (by decide) (by decide))), ← V, v5,
      keep (Frame.refl _ _) _ (.inl rfl)]
  · rw [V, val32_congr (limb_frame f7 (disj 96 128 (by decide) (by decide) (by decide))), ← V, v6,
      keep (f5.sub (sub1 64 (by decide))) _ (.inr (.inl rfl))]
  · rw [v7, keep ((f5.sub (sub1 64 (by decide))).trans (f6.sub (sub1 96 (by decide)))) _ (.inr (.inr rfl))]

theorem mulAdd_ok {s : State} (hp : MulAddPre s) :
    WP isa scalarMulAdd s fun t =>
      bytesAt t.mem (s.gpr .a0) 32 = Spec.Ed25519.scalarMulAdd (bytesAt s.mem (s.gpr .a1) 32)
        (bytesAt s.mem (s.gpr .a2) 32) (bytesAt s.mem (s.gpr .a3) 32) := by
  have hS := SR_eq
  have hout : (⟨s.gpr .a0, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold scalarMulAdd
  refine WP.seq (WP.mono (mulAddArgs_ok hp) fun s7 h7 => ?_)
  refine WP.seq (WP.mono (mulAddEngine_ok h7.ctx h7.vr h7.vk h7.vs) fun s11 ⟨r11, _, v11⟩ => ?_)
  refine WP.mono (finish_ok (h7.ctx.of_rest r11 (by decide))
    (by rw [r11.gpr _ (by decide), h7.rest.gpr _ (by decide)]) (by rw [r11.wr, h7.rest.wr]; exact hout)
    (hp.out_ws.sub_right (base_sub _ (by decide))) v11) fun t ht => ?_
  rw [ht, Nat.add_comm]; rfl

end VG.Proof.Ed25519.RISCV64
