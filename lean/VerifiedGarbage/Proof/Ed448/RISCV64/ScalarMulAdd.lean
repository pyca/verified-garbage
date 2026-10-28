module

import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarReduce
public import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.X448.RISCV64.Setup
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.Binary
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.RISCV64.Pack
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarLoop
import VerifiedGarbage.Proof.X448.RISCV64.Pass
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# `vg_ed448_scalar_mul_add` on RISCV64: correctness

The function rounds `scratch` up to a multiple of 8, reduces `k`, `s` and
`r` modulo `L` into `SK`, `SS` and `SA` (`inputs_ok`, by `engine_ok`),
computes their product row by row at `ACC` (X448's rows, `product_ok`), adds
`SA` (`sum_ok`), stores the sum's 112 bytes at `WIDE`, reduces them modulo
`L` into `SR` (`engine_ok`) and writes `SR` to `out` (`finish_ok`). It writes
only the rounded working space's first 1064 bytes (`LOW`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Impl.X448.RISCV64 (pass ldSrc addSrc zeroAcc row ACC)
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq RowInv mulPre_ok row_ok
  zeroAcc_ok
open VG.Proof.X25519
open VG.Spec.Ed448 (L decodeLE bytesAt)
open VG.Proof.Ed25519.RISCV64 (base base_sub)

theorem SK_eq : SK = 112 := rfl
theorem SS_eq : SS = 168 := rfl
theorem SA_eq : SA = 224 := rfl
theorem WIDE_eq : WIDE = 280 := rfl

theorem rem_SK : Rem SK := ⟨by decide, by decide, by decide⟩
theorem rem_SS : Rem SS := ⟨by decide, by decide, by decide⟩
theorem rem_SA : Rem SA := ⟨by decide, by decide, by decide⟩

/-- What the function writes of the working space. -/
abbrev LOW (b : Addr) : Region := ⟨b, 1064⟩

theorem sub_low (b : Addr) {d n : Nat} (h : d + n ≤ 1064) : Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (LOW b) :=
  Offset.sub_base b h

theorem frame_low {b : Addr} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (LOW b)) : Frame [LOW b] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem RD_low {b : Addr} {o : Nat} (ho : o + 56 ≤ 1064) : ∀ r ∈ RD b o, Region.Sub r (LOW b) := by
  intro r hr
  have hD := SD_eq
  simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact sub_low b (by omega_arith)

theorem low_ws (b : Addr) : Region.Sub (LOW b) ⟨b, 2048⟩ := Region.sub_prefix (by decide)

/-- The bytes of a buffer apart from the working space are in none of its parts. -/
theorem out_RD {q b : Addr} {N : Nat} (hN : N < 2 ^ 64) (hd : (⟨q, N⟩ : Region).Disjoint ⟨b, 2048⟩) {o : Nat} (ho : o + 56 ≤ 1064) :
    ∀ i < N, ∀ r ∈ RD b o, ¬ r.Contains (q + BitVec.ofNat 64 i) 1 := fun i hi r hr hc =>
  hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (low_ws b _ (RD_low ho r hr _ hc))

/-- The bytes of a buffer apart from the working space, through a frame in it. -/
theorem bytesAt_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p b : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨b, 2048⟩) (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 2048⟩)
    (hn : n < 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt, List.map_inj_left]
  intro i hi
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (hs r hr _ hc)

section
variable {b : Addr}

/-- `k`, `s` and `r` (at `t3`, `t6` and `t2`) modulo `L` into `SK`, `SS` and `SA`. -/
theorem inputs_ok {s : State} (hc : Ctx b s) {pk ps pr : Addr} (h14 : s.gpr .t3 = pk)
    (h17 : s.gpr .t6 = ps) (h26 : s.gpr .t2 = pr)
    (hk : (⟨pk, 57⟩ : Region) ∈ s.rd) (hs : (⟨ps, 57⟩ : Region) ∈ s.rd) (hr : (⟨pr, 57⟩ : Region) ∈ s.rd)
    (dk : (⟨pk, 57⟩ : Region).Disjoint ⟨b, 2048⟩) (ds : (⟨ps, 57⟩ : Region).Disjoint ⟨b, 2048⟩)
    (dr : (⟨pr, 57⟩ : Region).Disjoint ⟨b, 2048⟩) :
    WP isa scalarInputs s fun t =>
      Rest [.a2, .a4, .a5, .t0, .t3, .t4, .t5] s t ∧ Frame [LOW b] s.mem t.mem ∧
      V t.mem b SK = decodeLE (bytesAt s.mem pk 57) % L ∧ V t.mem b SS = decodeLE (bytesAt s.mem ps 57) % L ∧
      V t.mem b SA = decodeLE (bytesAt s.mem pr 57) % L := by
  have hK := SK_eq
  have hS := SS_eq
  have hA := SA_eq
  have hD := SD_eq
  have inr : ∀ (t : State) (q : Addr), t.rd = s.rd → t.wr = s.wr → (⟨q, 57⟩ : Region) ∈ s.rd →
      ∀ i < 57, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 i) 1 := fun t q h1 h2 hq i hi => by
    rw [h1, h2]; exact in_base (List.mem_append_left _ hq) (by omega_arith) (by omega_arith)
  have keep : ∀ {m m' : Mem} {o : Nat}, o + 56 ≤ 1064 → Frame (RD b o) m m' → ∀ (q : Addr),
      (⟨q, 57⟩ : Region).Disjoint ⟨b, 2048⟩ → bytesAt m' q 57 = bytesAt m q 57 := fun ho hf q hq =>
    bytesAt_keep hf hq (fun r hr x hx => low_ws b x (RD_low ho r hr x hx)) (by decide)
  have vkeep : ∀ {m m' : Mem} {o a : Nat}, Rem o → (o + 56 ≤ a ∨ a + 56 ≤ o) → Rem a → Frame (RD b a) m m' →
      V m' b o = V m b o := fun ho hoa ha hf => by
    have := ha.fits; have := ha.sep; have := ho.fits; have := ho.sep
    unfold V
    exact val32_congr (limb_frame hf fun r hr k hk => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
  unfold scalarInputs
  refine WP.seq (WP.mono (engine_ok rem_SK (N := 57) (by decide) (by decide) hc h14
    (inr s pk rfl rfl hk) (out_RD (by decide) dk (by omega_arith))) fun s1 ⟨r1, f1, v1⟩ => ?_)
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  refine WP.seq (wp_addi (by decide) fun s2 u2 => WP.block_nil ?_)
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.t3]) (by decide)) (by decide)
  have e14 : s2.gpr .t3 = ps := by rw [u2.gpr, r1.gpr _ (by decide), h17, BitVec.add_zero]
  refine WP.seq (WP.mono (engine_ok rem_SS (N := 57) (by decide) (by decide) hc2 e14
    (inr s2 ps (by rw [u2.rd, r1.rd]) (by rw [u2.wr, r1.wr]) hs) (out_RD (by decide) ds (by omega_arith)))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  have hc3 : Ctx b s3 := hc2.of_rest r3 (by decide)
  refine WP.seq (wp_addi (by decide) fun s4 u4 => WP.block_nil ?_)
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.t3]) (by decide)) (by decide)
  have e14' : s4.gpr .t3 = pr := by
    rw [u4.gpr, r3.gpr _ (by decide), u2.other _ (by decide), r1.gpr _ (by decide), h26, BitVec.add_zero]
  refine WP.mono (engine_ok rem_SA (N := 57) (by decide) (by decide) hc4 e14'
    (inr s4 pr (by rw [u4.rd, r3.rd, u2.rd, r1.rd]) (by rw [u4.wr, r3.wr, u2.wr, r1.wr]) hr) (out_RD (by decide) dr (by omega_arith)))
    fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans (rt.mono (by decide)))))
  · rw [u4.mem] at ft
    rw [u2.mem] at f3
    exact (frame_low f1 (RD_low (by omega_arith))).trans ((frame_low f3 (RD_low (by omega_arith))).trans
      (frame_low ft (RD_low (by omega_arith))))
  · rw [vkeep rem_SK (by omega_arith) rem_SA ft, u4.mem, vkeep rem_SK (by omega_arith) rem_SS f3, u2.mem, v1]
  · rw [vkeep rem_SS (by omega_arith) rem_SA ft, u4.mem, v3, u2.mem, keep (by omega_arith) f1 ps ds]
  · rw [vt, u4.mem, keep (by omega_arith) f3 pr dr, u2.mem, keep (by omega_arith) f1 pr dr]

/-- The 28 limbs of the product of `SK` and `SS` at `ACC`. -/
theorem product_ok {s : State} (hc : Ctx b s) :
    WP isa scalarProduct s (RowInv b SK SS s 14) := by
  have hA := ACC_eq
  unfold scalarProduct
  refine WP.seq (WP.mono (mulPre_ok (x := SK) (y := SS) hc) fun s1 h1 => ?_)
  refine WP.loop (M := isa) (fun n s' => ∃ i, n = 14 - i ∧ i < 14 ∧ RowInv b SK SS s i s') ?_ 14 s1
    ⟨0, rfl, by decide, h1⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok (by decide) (by decide) (by decide) (by decide) hi hr) fun s'' ⟨hr', hz⟩ => ?_
  by_cases h14 : i + 1 = 14
  · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h14], ?_⟩
    rw [h14] at hr'; exact hr'
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 14 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hr'⟩

/-- The sum's limbs: the product plus `SA`, at `ACC`. -/
theorem wideAdd_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 28 + V s.mem b SA < 2 ^ 224 * 2 ^ 224 * (2 ^ 224 * 2 ^ 224)) :
    WP isa (.block (([.li .a5 0] : List Instr) ++ pass .a3 ACC (addSrc ACC SA) ++ pass .a3 (ACC + 56) (ldSrc (ACC + 56)))) s
      fun t => Rest [.a2, .a4, .a5] s t ∧ Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem t.mem ∧
        val32 (accw ACC t.mem b) 28 = val32 (accw ACC s.mem b) 28 + V s.mem b SA := by
  have hA := ACC_eq
  have hSA := SA_eq
  have hl : ∀ k < 28, accw ACC s.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
  have hr : ∀ k < 14, limb s.mem b SA k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.a5]) (by decide)) (by decide)
  let c1 : Nat → Nat := fun k => accw ACC s.mem b k + limb s.mem b SA k
  refine WP.append (pass_ok (s0 := s1) (c := c1) (cin := 0) (by decide) (by omega_arith)
    (fun k hk => by rw [hc1.a3]; exact hc1.inW (by omega_arith))
    (fun k hk => by rw [hc1.a3]; exact al4 hc1.al (by omega_arith)) (by rw [u1.gpr]; rfl)
    (fun k hk => by have := hl k (by omega_arith); have := hr k hk; simp only [c1]; omega_arith) (by decide) ?_)
    fun s2 hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
    simp only [Impl.X448.RISCV64.addSrc]
    refine lw0_ok hc' (d := ACC + 4 * k) (by omega_arith) (by omega_arith) fun t1 v1 => ?_
    refine lw0_ok (hc'.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)) (d := SA + 4 * k) (by omega_arith) (by omega_arith)
      fun t2 v2 => wp_add fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
    · have ea : wd s'.mem b (ACC + 4 * k) = accw ACC s.mem b k := by
        rw [wd_pass hc1 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u1.mem]; rfl
      have er : wd t1.mem b (SA + 4 * k) = limb s.mem b SA k := by
        rw [v1.mem, wd_pass hc1 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u1.mem]; rfl
      have := hl k (by omega_arith); have := hr k hk
      rw [v3.gpr, v2.other .a4 (by decide), v1.gpr, v2.gpr]
      unfold wd at ea er
      rw [toNat_add_lt (by rw [toNat_ext32, toNat_ext32, ea, er]; omega_arith), toNat_ext32, toNat_ext32, ea, er]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))
  -- The high half, with the carry.
  have hr2 : Rest [.a2, .a4, .a5] s s2 := (u1.rest (by decide)).trans hp.rest
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have hf2 : Frame [⟨b + BitVec.ofNat 64 ACC, 56⟩] s.mem s2.mem := by
    have := hp.frame; rw [hc1.a3] at this; rw [← u1.mem]; exact this
  have hlo : ∀ j < 14, accw ACC s2.mem b j = out c1 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.a3] at this
  have hhi : ∀ j < 14, accw ACC s2.mem b (14 + j) = accw ACC s.mem b (14 + j) := fun j hj => by
    unfold accw
    refine wd_frame hf2 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  let c2 : Nat → Nat := fun k => accw ACC s.mem b (14 + k)
  have hc1v : val32 c1 14 = val32 (accw ACC s.mem b) 14 + V s.mem b SA := by
    simp only [c1]; rw [val32_add]; rfl
  have v1 := chain_val c1 0 14
  rw [pow448] at v1
  have hch1 : chain c1 0 14 ≤ 1 := by
    have h1 := val32_lt (f := accw ACC s.mem b) (n := 14) fun k hk => hl k (by omega_arith)
    have h2 := V_lt s.mem b SA
    rw [pow448] at h1
    omega_arith
  refine WP.mono (pass_ok (s0 := s2) (c := c2) (cin := chain c1 0 14) (by decide) (by omega_arith)
    (fun k hk => by rw [hc2.a3]; exact hc2.inW (by omega_arith))
    (fun k hk => by rw [hc2.a3]; exact al4 hc2.al (by omega_arith)) hp.a5
    (fun k hk => by have := hl (14 + k) (by omega_arith); simp only [c2]; omega_arith) (by omega_arith) ?_) fun t hq => ?_
  · intro k hk s' hq
    have hc' : Ctx b s' := hc2.of_rest hq.rest (by decide)
    refine WP.mono (ldSrc_ok hc' (o := ACC + 56) (k := k) (by omega_arith) (by omega_arith)) fun t1 ⟨e1, r1, m1⟩ =>
      ⟨?_, r1.mono (by decide), m1⟩
    rw [e1, wd_pass hc2 hq.frame (by omega_arith) (by omega_arith) (by omega_arith), show ACC + 56 + 4 * k = ACC + 4 * (14 + k) by omega_arith]
    exact hhi k hk
  · have hfq : Frame [⟨b + BitVec.ofNat 64 (ACC + 56), 56⟩] s2.mem t.mem := by
      have := hq.frame; rwa [hc2.a3] at this
    refine ⟨hr2.trans hq.rest, ?_, ?_⟩
    · refine (hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hfq.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · have hlo' : ∀ j < 14, accw ACC t.mem b j = out c1 0 j := fun j hj => by
        rw [← hlo j hj]
        unfold accw
        refine wd_frame hfq fun r hr => ?_
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      have hhi' : ∀ j < 14, accw ACC t.mem b (14 + j) = out c2 (chain c1 0 14) j := fun j hj => by
        have := hq.outs j hj
        rw [hc2.a3] at this
        unfold accw
        rw [show ACC + 4 * (14 + j) = ACC + 56 + 4 * j by omega_arith]; exact this
      have v2 := chain_val c2 (chain c1 0 14) 14
      rw [pow448] at v2
      have hsum : val32 (accw ACC t.mem b) 28 =
          val32 (out c1 0) 14 + 2 ^ 224 * 2 ^ 224 * val32 (out c2 (chain c1 0 14)) 14 := by
        rw [show (28 : Nat) = 14 + 14 from rfl, val32_append, val32_congr hlo', val32_congr hhi', pow448]
      have hs28 : val32 (accw ACC s.mem b) 28 = val32 (accw ACC s.mem b) 14 + 2 ^ 224 * 2 ^ 224 * val32 c2 14 := by
        rw [show (28 : Nat) = 14 + 14 from rfl, val32_append, pow448]
      have ho2 := val32_lt (f := out c2 (chain c1 0 14)) (n := 14) fun k _ => out_lt _ _ _
      rw [pow448] at ho2
      -- The final carry is zero: the sum is below `2⁸⁹⁶`.
      have hch2 : chain c2 (chain c1 0 14) 14 = 0 := by
        rw [hs28] at hb
        have : val32 c2 14 + chain c1 0 14 < 2 ^ 224 * 2 ^ 224 := by
          rcases Nat.lt_or_ge (val32 c2 14 + chain c1 0 14) (2 ^ 224 * 2 ^ 224) with h' | h'
          · exact h'
          · exfalso
            have := Nat.mul_le_mul_left (2 ^ 224 * 2 ^ 224) h'
            omega_arith
        omega_arith
      rw [hch2, Nat.mul_zero, Nat.add_zero] at v2
      rw [hsum, v2]
      omega_arith

/-- `4n` bytes in memory, as the number of their words. -/
theorem decode_words (m : Mem) (q : Addr) (n : Nat) :
    decodeLE (bytesAt m q (4 * n)) = val32 (fun j => wd m q (4 * j)) n := by
  rw [Proof.Ed448.decodeLE_eq]
  exact leNum_bytesAt4 m q n

/-- `SA` added to the product, and the sum's 112 bytes to `WIDE`. -/
theorem sum_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 28 + V s.mem b SA < 2 ^ 224 * 2 ^ 224 * (2 ^ 224 * 2 ^ 224)) :
    WP isa (.block scalarSum) s fun t =>
      Rest [.a2, .a4, .a5, .t3] s t ∧ Frame [LOW b] s.mem t.mem ∧ t.gpr .t3 = b + BitVec.ofNat 64 WIDE ∧
      decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 WIDE) 112) = val32 (accw ACC s.mem b) 28 + V s.mem b SA := by
  have hA := ACC_eq
  have hW := WIDE_eq
  unfold scalarSum
  rw [List.append_assoc (([.li .a5 0] : List Instr) ++ pass .a3 ACC (addSrc ACC SA) ++
    pass .a3 (ACC + 56) (ldSrc (ACC + 56))) ([.addi .t3 .a3 WIDE] : List Instr) (packWords ACC 28)]
  refine WP.append (wideAdd_ok hc hb) fun s1 ⟨r1, f1, v1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  rw [List.cons_append]
  refine wp_addi (by decide) fun s2 u2 => ?_
  have e14 : s2.gpr .t3 = b + BitVec.ofNat 64 WIDE := by rw [u2.gpr, hc1.a3]
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.t3]) (by decide)) (by decide)
  refine WP.mono (packWords_ok hc2 e14 (a := ACC) (n := 28) (by omega_arith) (by decide) (by decide)
    (fun k hk => by rw [Offset.add_add]; exact al4 hc2.al (by omega_arith))
    (fun k hk => by rw [Offset.add_add]; exact hc2.inW (by omega_arith))
    (Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) fun t ht => ⟨?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans (ht.rest.mono (by decide)))
  · have f2 := ht.frame
    rw [u2.mem] at f2
    exact (frame_low f1 fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega_arith)).trans
      (frame_low f2 fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega_arith))
  · rw [ht.rest.gpr _ (by decide), e14]
  · rw [show (112 : Nat) = 4 * 28 from rfl, decode_words, ← v1]
    exact val32_congr fun j hj => (ht.outs j hj).trans (by rw [limb, u2.mem]; rfl)

end

theorem mulAdd_mod (a b c n : Nat) : (a % n * (b % n) + c % n) % n = (c + a * b) % n := by
  rw [Nat.add_comm c, Nat.add_mod (a * b), Nat.mul_mod a b, Nat.mod_add_mod]

/-- The precondition, by register: `out` in `a0`, `r`, `k` and `s` in `a1`–`a3`, `scratch` in `a4`. -/
structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 57⟩, ⟨s.gpr .a2, 57⟩, ⟨s.gpr .a3, 57⟩]
  wr : s.wr = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a4, 8192⟩]
  out_ws : (⟨s.gpr .a0, 57⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  r_ws : (⟨s.gpr .a1, 57⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  k_ws : (⟨s.gpr .a2, 57⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  s_ws : (⟨s.gpr .a3, 57⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩

theorem mulAdd_ok {s : State} (hp : MulAddPre s) :
    WP isa scalarMulAdd s fun t =>
      bytesAt t.mem (s.gpr .a0) 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem (s.gpr .a1) 57)
        (bytesAt s.mem (s.gpr .a2) 57) (bytesAt s.mem (s.gpr .a3) 57) := by
  have hA := ACC_eq
  have hS := SR_eq
  have hW := WIDE_eq
  have hD := SD_eq
  have hws : (⟨s.gpr .a4, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hout : (⟨s.gpr .a0, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain ⟨b, hb⟩ : ∃ b, b = base (s.gpr .a4) := ⟨_, rfl⟩
  have hsub : Region.Sub ⟨b, 2048⟩ ⟨s.gpr .a4, 8192⟩ := by
    have := base_sub (s.gpr .a4) (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero, ← hb] at this
  unfold scalarMulAdd scalarMulAddArgs
  rw [align_eq]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s1 u1 => wp_mv fun s2 u2 => wp_mv fun s3 u3 => wp_mv fun s4 u4 => ?_)
  have hr4 : Rest [.t6, .t2, .t3, .a3] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  refine WP.append (Proof.Ed25519.RISCV64.align_ok (q := s.gpr .a4)
    (by rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]) (by rw [hr4.wr]; exact hws))
    fun s5 ⟨hc5, hr5, hm5⟩ => WP.block_nil ?_
  rw [← hb] at hc5
  have hr45 : Rest [.t6, .t2, .t3, .a3] s s5 := hr4.trans (hr5.mono (by decide))
  have hm45 : s5.mem = s.mem := by rw [hm5, u4.mem, u3.mem, u2.mem, u1.mem]
  have e14 : s5.gpr .t3 = s.gpr .a2 := by
    rw [hr5.gpr _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.other _ (by decide)]
  have e17 : s5.gpr .t6 = s.gpr .a3 := by
    rw [hr5.gpr _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  have e26 : s5.gpr .t2 = s.gpr .a1 := by
    rw [hr5.gpr _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]
  have e27 : s5.gpr .a0 = s.gpr .a0 := hr45.gpr _ (by decide)
  have hin : ∀ r : Reg, r = .a1 ∨ r = .a2 ∨ r = .a3 → (⟨s.gpr r, 57⟩ : Region) ∈ s5.rd := by
    rintro r (rfl | rfl | rfl) <;> (rw [hr45.rd, hp.rd]; simp)
  refine WP.seq (WP.mono (inputs_ok hc5 e14 e17 e26 (hin _ (.inr (.inl rfl))) (hin _ (.inr (.inr rfl)))
    (hin _ (.inl rfl)) (hp.k_ws.sub_right hsub) (hp.s_ws.sub_right hsub) (hp.r_ws.sub_right hsub))
    fun s7 ⟨r7, f7, vk, vs, vr⟩ => ?_)
  rw [hm45] at vk vs vr
  have hc7 : Ctx b s7 := hc5.of_rest r7 (by decide)
  refine WP.seq (WP.mono (product_ok hc7) fun s8 h8 => ?_)
  have hc8 := h8.ctx
  have hvA : V s8.mem b SA = V s7.mem b SA := by
    unfold V
    exact val32_congr (limb_frame h8.frame fun r hr j hj => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by rw [SA_eq]; omega_arith)) (by rw [SA_eq]; omega_arith)
        (by omega_arith))
  have hKL : V s7.mem b SK < L := by rw [vk]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  have hSL : V s7.mem b SS < L := by rw [vs]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  have hAL : V s7.mem b SA < L := by rw [vr]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  have hLt := L_lt
  have hprod : V s7.mem b SK * V s7.mem b SS ≤ (2 ^ 224 * 2 ^ 222) * (2 ^ 224 * 2 ^ 222) :=
    Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have hv8 : val32 (accw ACC s8.mem b) 28 = V s7.mem b SK * V s7.mem b SS := h8.val
  refine WP.seq (WP.mono (sum_ok hc8 (by rw [hv8, hvA]; omega_arith)) fun s9 ⟨r9, f9, e9, v9⟩ => ?_)
  have hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.seq (WP.mono (engine_ok rem_SR (N := 112) (by decide) (by decide) hc9 e9
    (fun i hi => by rw [Offset.add_add]; exact hc9.inR (by omega_arith))
    (fun i hi r hr => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Offset.add_add]
      rcases hr with rfl | rfl <;>
        exact fun hc => Offset.disjoint b (d := WIDE + i) (n := 1) (k := 56) (.inr (by omega_arith))
          (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) hc)) fun s10 ⟨r10, f10, v10⟩ => ?_)
  have hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  have hr10 : Rest [.a1, .a2, .a4, .a5, .a6, .a7, .t0, .t3, .t4, .t5] s5 s10 :=
    (r7.mono (by decide)).trans ((h8.rest.mono (by decide)).trans ((r9.mono (by decide)).trans (r10.mono (by decide))))
  refine WP.mono (finish_ok hc10 (q := s.gpr .a0) (by rw [hr10.gpr _ (by decide), e27])
    (by rw [hr10.wr, hr45.wr]; exact hout)
    ((hp.out_ws.sub_right hsub).sub_right (Offset.sub_base _ (by omega_arith))))
    fun t ⟨_, _, h3⟩ => ?_
  rw [h3, v10, v9, hv8, hvA, vk, vs, vr]
  unfold Spec.Ed448.scalarMulAdd
  exact congrArg (Spec.Ed448.encodeLE 57) (mulAdd_mod _ _ _ _)

end VG.Proof.Ed448.RISCV64
