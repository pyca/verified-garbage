module

import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarReduce
public import VerifiedGarbage.Proof.X448.PPC64LE.Mul
import VerifiedGarbage.Proof.X448.PPC64LE.Setup
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.Binary
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed448.PPC64LE.Pack
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarLoop
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# `vg_ed448_scalar_mul_add` on PPC64LE: correctness

The function saves the nonvolatile registers it uses, reduces `k`, `s` and
`r` modulo `L` into `SK`, `SS` and `SA` (`inputs_ok`, by `engine_ok`),
computes their product row by row at `ACC` (X448's rows, `product_ok`), adds
`SA` (`sum_ok`), stores the sum's 112 bytes at `WIDE`, reduces them modulo
`L` into `SR` (`engine_ok`) and writes `SR` to `out` (`finish_ok`). Below
`SAVE`, it writes only the working space's first 1064 bytes (`LOW`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Impl.X448.PPC64LE (pass ldSrc addSrc zeroAcc row ACC)
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame ACC_eq RowInv mulPre_ok row_ok
  zeroAcc_ok
open VG.Spec.Ed448 (L decodeLE bytesAt)

theorem SK_eq : SK = 112 := rfl
theorem SS_eq : SS = 168 := rfl
theorem SA_eq : SA = 224 := rfl
theorem WIDE_eq : WIDE = 280 := rfl

theorem rem_SK : Rem SK := ⟨by decide, by decide⟩
theorem rem_SS : Rem SS := ⟨by decide, by decide⟩
theorem rem_SA : Rem SA := ⟨by decide, by decide⟩

/-- What the function writes below `SAVE`. -/
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
  rcases hr with rfl | rfl <;> exact sub_low b (by omega)

theorem low_ws (b : Addr) : Region.Sub (LOW b) ⟨b, 8192⟩ := Region.sub_prefix (by decide)

/-- The bytes of a buffer apart from the working space are in none of its parts. -/
theorem out_RD {q b : Addr} {N : Nat} (hN : N < 2 ^ 64) (hd : (⟨q, N⟩ : Region).Disjoint ⟨b, 8192⟩) {o : Nat} (ho : o + 56 ≤ 1064) :
    ∀ i < N, ∀ r ∈ RD b o, ¬ r.Contains (q + BitVec.ofNat 64 i) 1 := fun i hi r hr hc =>
  hd _ (Offset.contains_base _ (by omega) (by omega)) (low_ws b _ (RD_low ho r hr _ hc))

section
variable {b : Addr}

/-- `k`, `s` and `r` (at `r14`, `r17` and `r26`) modulo `L` into `SK`, `SS` and `SA`. -/
theorem inputs_ok {s : State} (hc : Ctx b s) {pk ps pr : Addr} (h14 : s.gpr .r14 = pk)
    (h17 : s.gpr .r17 = ps) (h26 : s.gpr .r26 = pr)
    (hk : (⟨pk, 57⟩ : Region) ∈ s.rd) (hs : (⟨ps, 57⟩ : Region) ∈ s.rd) (hr : (⟨pr, 57⟩ : Region) ∈ s.rd)
    (dk : (⟨pk, 57⟩ : Region).Disjoint ⟨b, 8192⟩) (ds : (⟨ps, 57⟩ : Region).Disjoint ⟨b, 8192⟩)
    (dr : (⟨pr, 57⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa scalarInputs s fun t =>
      Rest [.r5, .r7, .r8, .r11, .r14, .r15, .r16] s t ∧ Frame [LOW b] s.mem t.mem ∧
      V t.mem b SK = decodeLE (bytesAt s.mem pk 57) % L ∧ V t.mem b SS = decodeLE (bytesAt s.mem ps 57) % L ∧
      V t.mem b SA = decodeLE (bytesAt s.mem pr 57) % L := by
  have hK := SK_eq
  have hS := SS_eq
  have hA := SA_eq
  have hD := SD_eq
  have inr : ∀ (t : State) (q : Addr), t.rd = s.rd → t.wr = s.wr → (⟨q, 57⟩ : Region) ∈ s.rd →
      ∀ i < 57, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 i) 1 := fun t q h1 h2 hq i hi => by
    rw [h1, h2]; exact in_base (List.mem_append_left _ hq) (by omega) (by omega)
  have keep : ∀ {m m' : Mem} {o : Nat}, o + 56 ≤ 1064 → Frame (RD b o) m m' → ∀ (q : Addr),
      (⟨q, 57⟩ : Region).Disjoint ⟨b, 8192⟩ → bytesAt m' q 57 = bytesAt m q 57 := fun ho hf q hq =>
    bytesAt_keep hf hq (fun r hr x hx => low_ws b x (RD_low ho r hr x hx)) (by decide)
  have vkeep : ∀ {m m' : Mem} {o a : Nat}, Rem o → (o + 56 ≤ a ∨ a + 56 ≤ o) → Rem a → Frame (RD b a) m m' →
      V m' b o = V m b o := fun ho hoa ha hf => by
    have := ha.fits; have := ha.sep; have := ho.fits; have := ho.sep
    unfold V
    exact val32_congr (limb_frame hf fun r hr k hk => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega))
  unfold scalarInputs
  refine WP.seq (WP.mono (engine_ok rem_SK (N := 57) (by decide) (by decide) hc h14
    (inr s pk rfl rfl hk) (out_RD (by decide) dk (by omega))) fun s1 ⟨r1, f1, v1⟩ => ?_)
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  refine WP.seq (wp_addi (by decide) (by decide) fun s2 u2 => WP.block_nil ?_)
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.r14]) (by decide)) (by decide)
  have e14 : s2.gpr .r14 = ps := by rw [u2.gpr, r1.gpr _ (by decide), h17, BitVec.add_zero]
  refine WP.seq (WP.mono (engine_ok rem_SS (N := 57) (by decide) (by decide) hc2 e14
    (inr s2 ps (by rw [u2.rd, r1.rd]) (by rw [u2.wr, r1.wr]) hs) (out_RD (by decide) ds (by omega)))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  have hc3 : Ctx b s3 := hc2.of_rest r3 (by decide)
  refine WP.seq (wp_addi (by decide) (by decide) fun s4 u4 => WP.block_nil ?_)
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r14]) (by decide)) (by decide)
  have e14' : s4.gpr .r14 = pr := by
    rw [u4.gpr, r3.gpr _ (by decide), u2.other _ (by decide), r1.gpr _ (by decide), h26, BitVec.add_zero]
  refine WP.mono (engine_ok rem_SA (N := 57) (by decide) (by decide) hc4 e14'
    (inr s4 pr (by rw [u4.rd, r3.rd, u2.rd, r1.rd]) (by rw [u4.wr, r3.wr, u2.wr, r1.wr]) hr) (out_RD (by decide) dr (by omega)))
    fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans (rt.mono (by decide)))))
  · rw [u4.mem] at ft
    rw [u2.mem] at f3
    exact (frame_low f1 (RD_low (by omega))).trans ((frame_low f3 (RD_low (by omega))).trans
      (frame_low ft (RD_low (by omega))))
  · rw [vkeep rem_SK (by omega) rem_SA ft, u4.mem, vkeep rem_SK (by omega) rem_SS f3, u2.mem, v1]
  · rw [vkeep rem_SS (by omega) rem_SA ft, u4.mem, v3, u2.mem, keep (by omega) f1 ps ds]
  · rw [vt, u4.mem, keep (by omega) f3 pr dr, u2.mem, keep (by omega) f1 pr dr]

/-- The 28 limbs of the product of `SK` and `SS` at `ACC`. -/
theorem product_ok {s : State} (hc : Ctx b s) :
    WP isa scalarProduct s (RowInv b SK SS s 14) := by
  have hA := ACC_eq
  unfold scalarProduct
  refine WP.seq (WP.mono (mulPre_ok (x := SK) (y := SS) hc) fun s1 h1 => ?_)
  refine WP.loop (M := isa) (fun n s' => ∃ i, n = 14 - i ∧ i < 14 ∧ RowInv b SK SS s i s') ?_ 14 s1
    ⟨0, rfl, by decide, h1⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok (by decide) (by decide) hi hr) fun s'' ⟨hr', hz⟩ => ?_
  by_cases h14 : i + 1 = 14
  · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h14], ?_⟩
    rw [h14] at hr'; exact hr'
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega, 14 - (i + 1), by omega, i + 1, rfl, by omega, hr'⟩

/-- The sum's limbs: the product plus `SA`, at `ACC`. -/
theorem wideAdd_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 28 + V s.mem b SA < 2 ^ 224 * 2 ^ 224 * (2 ^ 224 * 2 ^ 224)) :
    WP isa (.block (([.li .r8 0] : List Instr) ++ pass .r6 ACC (addSrc ACC SA) ++ pass .r6 (ACC + 56) (ldSrc (ACC + 56)))) s
      fun t => Rest [.r5, .r7, .r8] s t ∧ Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem t.mem ∧
        val32 (accw ACC t.mem b) 28 = val32 (accw ACC s.mem b) 28 + V s.mem b SA := by
  have hA := ACC_eq
  have hSA := SA_eq
  have hl : ∀ k < 28, accw ACC s.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
  have hr : ∀ k < 14, limb s.mem b SA k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r8]) (by decide)) (by decide)
  let c1 : Nat → Nat := fun k => accw ACC s.mem b k + limb s.mem b SA k
  refine WP.append (pass_ok (s0 := s1) (c := c1) (cin := 0) (by decide) (by decide) (by omega)
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega)) (by rw [u1.gpr]; rfl)
    (fun k hk => by have := hl k (by omega); have := hr k hk; simp only [c1]; omega) (by decide) ?_)
    fun s2 hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
    simp only [Impl.X448.PPC64LE.addSrc]
    refine lw0_ok hc' (d := ACC + 4 * k) (by omega) fun t1 v1 => ?_
    refine lw0_ok (hc'.of_rest (v1.rest (ws := [.r7]) (by decide)) (by decide)) (d := SA + 4 * k) (by omega)
      fun t2 v2 => wp_add fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
    · have ea : wd s'.mem b (ACC + 4 * k) = accw ACC s.mem b k := by
        rw [wd_pass hc1 hp.frame (by omega) (by omega) (by omega), u1.mem]; rfl
      have er : wd t1.mem b (SA + 4 * k) = limb s.mem b SA k := by
        rw [v1.mem, wd_pass hc1 hp.frame (by omega) (by omega) (by omega), u1.mem]; rfl
      have := hl k (by omega); have := hr k hk
      rw [v3.gpr, v2.other .r7 (by decide), v1.gpr, v2.gpr]
      unfold wd at ea er
      rw [toNat_add_lt (by rw [toNat_ext32, toNat_ext32, ea, er]; omega), toNat_ext32, toNat_ext32, ea, er]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))
  -- The high half, with the carry.
  have hr2 : Rest [.r5, .r7, .r8] s s2 := (u1.rest (by decide)).trans hp.rest
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have hf2 : Frame [⟨b + BitVec.ofNat 64 ACC, 56⟩] s.mem s2.mem := by
    have := hp.frame; rw [hc1.r6] at this; rw [← u1.mem]; exact this
  have hlo : ∀ j < 14, accw ACC s2.mem b j = out c1 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.r6] at this
  have hhi : ∀ j < 14, accw ACC s2.mem b (14 + j) = accw ACC s.mem b (14 + j) := fun j hj => by
    unfold accw
    refine wd_frame hf2 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  let c2 : Nat → Nat := fun k => accw ACC s.mem b (14 + k)
  have hc1v : val32 c1 14 = val32 (accw ACC s.mem b) 14 + V s.mem b SA := by
    simp only [c1]; rw [val32_add]; rfl
  have v1 := chain_val c1 0 14
  rw [pow448] at v1
  have hch1 : chain c1 0 14 ≤ 1 := by
    have h1 := val32_lt (f := accw ACC s.mem b) (n := 14) fun k hk => hl k (by omega)
    have h2 := V_lt s.mem b SA
    rw [pow448] at h1
    omega
  refine WP.mono (pass_ok (s0 := s2) (c := c2) (cin := chain c1 0 14) (by decide) (by decide) (by omega)
    (fun k hk => by rw [hc2.r6]; exact hc2.inW (by omega)) hp.r8
    (fun k hk => by have := hl (14 + k) (by omega); simp only [c2]; omega) (by omega) ?_) fun t hq => ?_
  · intro k hk s' hq
    have hc' : Ctx b s' := hc2.of_rest hq.rest (by decide)
    refine WP.mono (ldSrc_ok hc' (o := ACC + 56) (k := k) (by omega)) fun t1 ⟨e1, r1, m1⟩ =>
      ⟨?_, r1.mono (by decide), m1⟩
    rw [e1, wd_pass hc2 hq.frame (by omega) (by omega) (by omega), show ACC + 56 + 4 * k = ACC + 4 * (14 + k) by omega]
    exact hhi k hk
  · have hfq : Frame [⟨b + BitVec.ofNat 64 (ACC + 56), 56⟩] s2.mem t.mem := by
      have := hq.frame; rwa [hc2.r6] at this
    refine ⟨hr2.trans hq.rest, ?_, ?_⟩
    · refine (hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hfq.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · have hlo' : ∀ j < 14, accw ACC t.mem b j = out c1 0 j := fun j hj => by
        rw [← hlo j hj]
        unfold accw
        refine wd_frame hfq fun r hr => ?_
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      have hhi' : ∀ j < 14, accw ACC t.mem b (14 + j) = out c2 (chain c1 0 14) j := fun j hj => by
        have := hq.outs j hj
        rw [hc2.r6] at this
        unfold accw
        rw [show ACC + 4 * (14 + j) = ACC + 56 + 4 * j by omega]; exact this
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
            omega
        omega
      rw [hch2, Nat.mul_zero, Nat.add_zero] at v2
      rw [hsum, v2]
      omega

/-- `4n` bytes in memory, as the number of their words. -/
theorem decode_words (m : Mem) (q : Addr) (n : Nat) :
    decodeLE (bytesAt m q (4 * n)) = val32 (fun j => wd m q (4 * j)) n := by
  rw [Proof.Ed448.decodeLE_eq]
  exact leNum_bytesAt4 m q n

/-- `SA` added to the product, and the sum's 112 bytes to `WIDE`. -/
theorem sum_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 28 + V s.mem b SA < 2 ^ 224 * 2 ^ 224 * (2 ^ 224 * 2 ^ 224)) :
    WP isa (.block scalarSum) s fun t =>
      Rest [.r5, .r7, .r8, .r14] s t ∧ Frame [LOW b] s.mem t.mem ∧ t.gpr .r14 = b + BitVec.ofNat 64 WIDE ∧
      decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 WIDE) 112) = val32 (accw ACC s.mem b) 28 + V s.mem b SA := by
  have hA := ACC_eq
  have hW := WIDE_eq
  unfold scalarSum
  rw [List.append_assoc (([.li .r8 0] : List Instr) ++ pass .r6 ACC (addSrc ACC SA) ++
    pass .r6 (ACC + 56) (ldSrc (ACC + 56))) ([.addi .r14 .r6 WIDE] : List Instr) (packWords ACC 28)]
  refine WP.append (wideAdd_ok hc hb) fun s1 ⟨r1, f1, v1⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  rw [List.cons_append]
  refine wp_addi (by decide) (by decide) fun s2 u2 => ?_
  have e14 : s2.gpr .r14 = b + BitVec.ofNat 64 WIDE := by rw [u2.gpr, hc1.r6]
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.mono (packWords_ok hc2 e14 (a := ACC) (n := 28) (by omega) (by decide)
    (fun k hk => by rw [Offset.add_add]; exact hc2.inW (by omega))
    (Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))) fun t ht => ⟨?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans (ht.rest.mono (by decide)))
  · have f2 := ht.frame
    rw [u2.mem] at f2
    exact (frame_low f1 fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega)).trans
      (frame_low f2 fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega))
  · rw [ht.rest.gpr _ (by decide), e14]
  · rw [show (112 : Nat) = 4 * 28 from rfl, decode_words, ← v1]
    exact val32_congr fun j hj => (ht.outs j hj).trans (by rw [limb, u2.mem]; rfl)

end

theorem mulAdd_mod (a b c n : Nat) : (a % n * (b % n) + c % n) % n = (c + a * b) % n := by
  rw [Nat.add_comm c, Nat.add_mod (a * b), Nat.mul_mod a b, Nat.mod_add_mod]

/-- The precondition, by register: `out` in `r3`, `r`, `k` and `s` in `r4`–`r6`, `scratch` in `r7`. -/
structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 57⟩, ⟨s.gpr .r5, 57⟩, ⟨s.gpr .r6, 57⟩]
  wr : s.wr = [⟨s.gpr .r3, 57⟩, ⟨s.gpr .r7, 8192⟩]
  out_ws : (⟨s.gpr .r3, 57⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  r_ws : (⟨s.gpr .r4, 57⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  k_ws : (⟨s.gpr .r5, 57⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  s_ws : (⟨s.gpr .r6, 57⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩

theorem mulAdd_ok {s : State} (hp : MulAddPre s) :
    WP isa scalarMulAdd s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      bytesAt t.mem (s.gpr .r3) 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem (s.gpr .r4) 57)
        (bytesAt s.mem (s.gpr .r5) 57) (bytesAt s.mem (s.gpr .r6) 57) := by
  have hV := SAVE_eq
  have hA := ACC_eq
  have hS := SR_eq
  have hW := WIDE_eq
  have hD := SD_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r7 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  have hout : (⟨s.gpr .r3, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold scalarMulAdd scalarMulAddArgs
  rw [scalarSave_eq]
  have hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega) (by omega)
  refine WP.seq (Spill.save_ok (b := .r7) (by decide) saveList_fits hsin ?_)
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .r7) s.gpr saveList } : State) = s1
  have hsv : Spill.Saved b s.gpr saveList s1.mem := by rw [← hs1, hb]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf1 : Frame [⟨b, 8192⟩] s.mem s1.mem := by
    rw [← hs1, hb]
    exact Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega) (by decide) _ _ _
  have hg1 : s1.gpr = s.gpr := by rw [← hs1]
  have hrd1 : s1.rd = s.rd := by rw [← hs1]
  have hwr1 : s1.wr = s.wr := by rw [← hs1]
  have hsp1 : s1.sp = s.sp := by rw [← hs1]
  refine wp_addi (by decide) (by decide) fun s2 u2 => wp_addi (by decide) (by decide) fun s3 u3 =>
    wp_addi (by decide) (by decide) fun s4 u4 => wp_addi (by decide) (by decide) fun s5 u5 =>
    wp_addi (by decide) (by decide) fun s6 u6 => WP.block_nil ?_
  have hr6 : Rest [.r6, .r14, .r17, .r26, .r27] s1 s6 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans ((u4.rest (by decide)).trans
      ((u5.rest (by decide)).trans (u6.rest (by decide)))))
  have hm6 : s6.mem = s1.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
  have e6 : s6.gpr .r6 = b := by
    rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      BitVec.add_zero, hg1, hb]
  have e14 : s6.gpr .r14 = s.gpr .r5 := by
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      BitVec.add_zero, hg1]
  have e17 : s6.gpr .r17 = s.gpr .r6 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide), u2.other _ (by decide),
      BitVec.add_zero, hg1]
  have e26 : s6.gpr .r26 = s.gpr .r4 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide),
      BitVec.add_zero, hg1]
  have e27 : s6.gpr .r27 = s.gpr .r3 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr,
      BitVec.add_zero, hg1]
  have hrd6 : s6.rd = s.rd := hr6.rd.trans hrd1
  have hwr6 : s6.wr = s.wr := hr6.wr.trans hwr1
  have hc6 : Ctx b s6 := ⟨e6, 8192, by decide, by rw [hwr6]; exact hws⟩
  have hin : ∀ r : Reg, r = .r4 ∨ r = .r5 ∨ r = .r6 → (⟨s.gpr r, 57⟩ : Region) ∈ s6.rd := by
    rintro r (rfl | rfl | rfl) <;> (rw [hrd6, hp.rd]; simp)
  -- The inputs' bytes, kept by the saves.
  have keep1 : ∀ q : Addr, (⟨q, 57⟩ : Region).Disjoint ⟨b, 8192⟩ → bytesAt s6.mem q 57 = bytesAt s.mem q 57 :=
    fun q hq => by
      rw [hm6]; exact bytesAt_keep hf1 hq (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) (by decide)
  refine WP.seq (WP.mono (inputs_ok hc6 e14 e17 e26 (hin _ (.inr (.inl rfl))) (hin _ (.inr (.inr rfl)))
    (hin _ (.inl rfl)) (hb ▸ hp.k_ws) (hb ▸ hp.s_ws) (hb ▸ hp.r_ws)) fun s7 ⟨r7, f7, vk, vs, vr⟩ => ?_)
  rw [keep1 _ (hb ▸ hp.k_ws)] at vk
  rw [keep1 _ (hb ▸ hp.s_ws)] at vs
  rw [keep1 _ (hb ▸ hp.r_ws)] at vr
  have hc7 : Ctx b s7 := hc6.of_rest r7 (by decide)
  refine WP.seq (WP.mono (product_ok hc7) fun s8 h8 => ?_)
  have hc8 := h8.ctx
  have hvA : V s8.mem b SA = V s7.mem b SA := by
    unfold V
    exact val32_congr (limb_frame h8.frame fun r hr j hj => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by rw [SA_eq]; omega)) (by rw [SA_eq]; omega)
        (by omega))
  have hKL : V s7.mem b SK < L := by rw [vk]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  have hSL : V s7.mem b SS < L := by rw [vs]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  have hAL : V s7.mem b SA < L := by rw [vr]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  have hLt := L_lt
  have hprod : V s7.mem b SK * V s7.mem b SS ≤ (2 ^ 224 * 2 ^ 222) * (2 ^ 224 * 2 ^ 222) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hv8 : val32 (accw ACC s8.mem b) 28 = V s7.mem b SK * V s7.mem b SS := h8.val
  refine WP.seq (WP.mono (sum_ok hc8 (by rw [hv8, hvA]; omega)) fun s9 ⟨r9, f9, e9, v9⟩ => ?_)
  have hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.seq (WP.mono (engine_ok rem_SR (N := 112) (by decide) (by decide) hc9 e9
    (fun i hi => by rw [Offset.add_add]; exact hc9.inR (by omega))
    (fun i hi r hr => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Offset.add_add]
      rcases hr with rfl | rfl <;>
        exact fun hc => Offset.disjoint b (d := WIDE + i) (n := 1) (k := 56) (.inr (by omega))
          (by omega) (by omega) _ (Region.contains_self _ _) hc)) fun s10 ⟨r10, f10, v10⟩ => ?_)
  have hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  -- The saved registers, through the writes below `SAVE`.
  have hlowsave : ∀ r ∈ [LOW b], Region.Disjoint ⟨b + BitVec.ofNat 64 SAVE, 96⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega) (by omega)
  have hsv10 : Spill.Saved b s.gpr saveList s10.mem := by
    rw [← hm6] at hsv
    have f8 : Frame [LOW b] s7.mem s8.mem :=
      frame_low h8.frame fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega)
    exact ((((hsv.frame_in saveList_in f7 hlowsave).frame_in saveList_in f8 hlowsave).frame_in saveList_in f9
      hlowsave).frame_in saveList_in (frame_low f10 (RD_low (by omega))) hlowsave)
  have hr610 : Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16] s6 s10 :=
    (r7.mono (by decide)).trans ((h8.rest.mono (by decide)).trans ((r9.mono (by decide)).trans (r10.mono (by decide))))
  refine WP.mono (finish_ok (s0 := s) hc10 (q := s.gpr .r3) (by rw [hr610.gpr _ (by decide), e27])
    (by rw [hr610.wr, hwr6]; exact hout) (by rw [hr610.rd, hrd6]) (by rw [hr610.wr, hwr6]) hws (hb ▸ hp.out_ws) hsv10
    fun r hr hm => ?_) fun t ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, hr610.sp, hr6.sp, hsp1], ?_⟩
  · have h3 : r ∉ ([.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16] : List Reg) := by
      revert hr hm; cases r <;> decide
    have h4 : r ∉ ([.r6, .r14, .r17, .r26, .r27] : List Reg) := by revert hr hm; cases r <;> decide
    rw [hr610.gpr _ h3, hr6.gpr _ h4, hg1]
  · rw [h3, v10, v9, hv8, hvA, vk, vs, vr]
    unfold Spec.Ed448.scalarMulAdd
    exact congrArg (Spec.Ed448.encodeLE 57) (mulAdd_mod _ _ _ _)

end VG.Proof.Ed448.PPC64LE
