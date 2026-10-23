module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarReduce
public import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBit
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarLoop

/-!
# `vg_ed25519_scalar_mul_add` on PPC64LE: correctness

The function saves the nonvolatile registers it uses, copies `r`, `k` and
`s` to bytes 64, 96 and 128 of `scratch`, computes the 512-bit `k s` row by
row at `ACC` (X25519's product, `wideMul_ok`), adds `r` (`wideAdd_ok`),
stores the sum's 64 bytes at byte 512 (`packWide_ok`), reduces them modulo
`L` (`engine_ok`) and copies the remainder to `out`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (L decodeLE bytesAt)

section
variable {b : Addr}

theorem wideMul_ok {x y : Nat} (hx : x + 32 ≤ ACC) (hy : y + 32 ≤ ACC) {s : State} (hc : Ctx b s) :
    WP isa (scalarWideMul x y) s (RowInv ACC b x y s 8) := by
  have hA := ACC_eq
  unfold scalarWideMul
  refine WP.seq (WP.mono (mulPre_ok (by omega) (x := x) (y := y) hc) fun s1 h1 => ?_)
  refine WP.loop (M := isa) (fun n s' => ∃ i, n = 8 - i ∧ i < 8 ∧ RowInv ACC b x y s i s') ?_ 8 s1
    ⟨0, rfl, by decide, h1⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok (by omega) hx hy hi hr) fun s'' ⟨hr', hz⟩ => ?_
  by_cases h8 : i + 1 = 8
  · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h8], ?_⟩
    rw [h8] at hr'; exact hr'
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega, 8 - (i + 1), by omega, i + 1, rfl, by omega, hr'⟩

/-- The sum's limbs: `k s + r`, at `ACC`. -/
theorem wideAdd_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 16 + V s.mem b 64 < 2 ^ 512) :
    WP isa (.block (scalarWideAdd 64)) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ Frame [⟨b + BitVec.ofNat 64 ACC, 64⟩] s.mem t.mem ∧
      val32 (accw ACC t.mem b) 16 = val32 (accw ACC s.mem b) 16 + V s.mem b 64 := by
  have hA := ACC_eq
  have hl : ∀ k < 16, accw ACC s.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
  have hr : ∀ k < 8, limb s.mem b 64 k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  unfold scalarWideAdd
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r8]) (by decide)) (by decide)
  let c1 : Nat → Nat := fun k => accw ACC s.mem b k + limb s.mem b 64 k
  refine WP.append (pass_ok (s0 := s1) (c := c1) (cin := 0) (by decide) (by decide) (by omega)
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega)) (by rw [u1.gpr]; rfl)
    (fun k hk => by have := hl k (by omega); have := hr k hk; simp only [c1]; omega) (by decide) ?_)
    fun s2 hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
    simp only [Impl.X25519.PPC64LE.addSrc]
    refine lw0_ok hc' (d := ACC + 4 * k) (by omega) fun t1 v1 => ?_
    refine lw0_ok (hc'.of_rest (v1.rest (ws := [.r7]) (by decide)) (by decide)) (d := 64 + 4 * k) (by omega)
      fun t2 v2 => wp_add fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
    · have ea : wd s'.mem b (ACC + 4 * k) = accw ACC s.mem b k := by
        rw [wd_pass hc1 hp.frame (by omega) (by omega) (by omega), u1.mem]; rfl
      have er : wd t1.mem b (64 + 4 * k) = limb s.mem b 64 k := by
        rw [v1.mem, wd_pass hc1 hp.frame (by omega) (by omega) (by omega), u1.mem]; rfl
      have := hl k (by omega); have := hr k hk
      rw [v3.gpr, v2.other .r7 (by decide), v1.gpr, v2.gpr]
      unfold wd at ea er
      rw [toNat_add_lt (by rw [toNat_ext32, toNat_ext32, ea, er]; omega), toNat_ext32, toNat_ext32, ea, er]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))
  -- The high half, with the carry.
  have hr2 : Rest [.r5, .r7, .r8] s s2 := (u1.rest (by decide)).trans hp.rest
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have hf2 : Frame [⟨b + BitVec.ofNat 64 ACC, 32⟩] s.mem s2.mem := by
    have := hp.frame; rw [hc1.r6, show 4 * 8 = 32 from rfl] at this; rw [← u1.mem]; exact this
  have hlo : ∀ j < 8, accw ACC s2.mem b j = out c1 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.r6] at this
  have hhi : ∀ j < 8, accw ACC s2.mem b (8 + j) = accw ACC s.mem b (8 + j) := fun j hj => by
    unfold accw
    refine wd_frame hf2 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  let c2 : Nat → Nat := fun k => accw ACC s.mem b (8 + k)
  have hch1 : chain c1 0 8 ≤ 1 := by
    have hv := chain_val c1 0 8
    have h1 := val32_lt (f := accw ACC s.mem b) (n := 8) fun k hk => hl k (by omega)
    have h2 := V_lt s.mem b 64
    have hc1v : val32 c1 8 = val32 (accw ACC s.mem b) 8 + V s.mem b 64 := by
      simp only [c1]; rw [val32_add]; rfl
    rw [show 32 * 8 = 256 from rfl] at hv h1
    rcases Nat.lt_or_ge (chain c1 0 8) 2 with h | h
    · omega
    · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h; omega
  refine WP.mono (pass_ok (s0 := s2) (c := c2) (cin := chain c1 0 8) (by decide) (by decide) (by omega)
    (fun k hk => by rw [hc2.r6]; exact hc2.inW (by omega)) hp.r8
    (fun k hk => by have := hl (8 + k) (by omega); simp only [c2]; omega) (by omega) ?_) fun t hq => ?_
  · intro k hk s' hq
    have hc' : Ctx b s' := hc2.of_rest hq.rest (by decide)
    refine WP.mono (ldSrc_ok hc' (o := ACC + 32) (k := k) (by omega)) fun t1 ⟨e1, r1, m1⟩ => ⟨?_, r1.mono (by decide), m1⟩
    rw [e1, wd_pass hc2 hq.frame (by omega) (by omega) (by omega), show ACC + 32 + 4 * k = ACC + 4 * (8 + k) by omega]
    exact hhi k hk
  · have hfq : Frame [⟨b + BitVec.ofNat 64 (ACC + 32), 32⟩] s2.mem t.mem := by
      have := hq.frame; rwa [hc2.r6, show 4 * 8 = 32 from rfl] at this
    refine ⟨hr2.trans hq.rest, ?_, ?_⟩
    · refine (hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hfq.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · have hlo' : ∀ j < 8, accw ACC t.mem b j = out c1 0 j := fun j hj => by
        rw [← hlo j hj]
        unfold accw
        refine wd_frame hfq fun r hr => ?_
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
      have hhi' : ∀ j < 8, accw ACC t.mem b (8 + j) = out c2 (chain c1 0 8) j := fun j hj => by
        have := hq.outs j hj
        rw [hc2.r6] at this
        unfold accw
        rw [show ACC + 4 * (8 + j) = ACC + 32 + 4 * j by omega]; exact this
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
            · exfalso; have := Nat.mul_le_mul_left (2 ^ 256) h'; omega
          omega
      rw [hch2, Nat.mul_zero, Nat.add_zero] at v2
      rw [hsum, v2]
      omega

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
      Rest [.r7, .r14] s t ∧ Frame [⟨b + BitVec.ofNat 64 512, 64⟩] s.mem t.mem ∧
      t.gpr .r14 = b + BitVec.ofNat 64 512 ∧
      decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 512) 64) = val32 (accw ACC s.mem b) 16 := by
  have hA := ACC_eq
  unfold scalarPackWide
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun s1 u1 => ?_
  have e14 : s1.gpr .r14 = b + BitVec.ofNat 64 512 := by rw [u1.gpr, hc.r6]
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r14]) (by decide)) (by decide)
  have hw : ∀ (t : State), Ctx b t → ∀ d, d + 32 ≤ 64 → ∀ k < 8,
      InRegions t.wr (b + BitVec.ofNat 64 512 + BitVec.ofNat 64 (d + 4 * k)) 4 := fun t ht d hd k hk => by
    rw [Offset.add_add]; exact ht.inW (by omega)
  have hd : ∀ d a, d + 32 ≤ 64 → a + 32 ≤ 512 ∨ 576 ≤ a → a + 32 ≤ 4096 →
      (⟨b + BitVec.ofNat 64 512 + BitVec.ofNat 64 d, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 32⟩ :=
    fun d a hd ha ha' => by rw [Offset.add_add]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine WP.append (packField_ok hc1 e14 (a := ACC) (dst := 0) (by omega) (by decide) (hw _ hc1 0 (by omega))
    (hd 0 ACC (by omega) (by omega) (by omega))) fun s2 h2 => ?_
  have hc2 : Ctx b s2 := hc1.of_rest h2.rest (by decide)
  refine WP.mono (packField_ok hc2 (by rw [h2.rest.gpr _ (by decide), e14]) (a := ACC + 32) (dst := 32)
    (by omega) (by decide) (hw _ hc2 32 (by omega)) (hd 32 (ACC + 32) (by omega) (by omega) (by omega)))
    fun t h3 => ⟨(u1.rest (by decide)).trans ((h2.rest.trans h3.rest).mono (by decide)), ?_,
      by rw [h3.rest.gpr _ (by decide), h2.rest.gpr _ (by decide), e14], ?_⟩
  · rw [← u1.mem]
    have f2 := h2.frame
    have f3 := h3.frame
    rw [Offset.add_add] at f2 f3
    refine (f2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (f3.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
  · have hq : ∀ j < 8, wd t.mem b (512 + 4 * j) = wd s2.mem b (512 + 4 * j) := fun j hj => by
      have f3 := h3.frame
      rw [Offset.add_add] at f3
      refine wd_frame f3 fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    have hhi : ∀ j < 8, limb s2.mem b (ACC + 32) j = limb s1.mem b (ACC + 32) j := fun j hj => by
      have f2 := h2.frame
      rw [Offset.add_add] at f2
      refine wd_frame f2 fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    have lo : decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 512) 32) = V s1.mem b ACC := by
      refine bytes_of_words fun j hj => ?_
      rw [wd_shift, hq j hj, ← wd_shift, ← Nat.zero_add (4 * j)]
      exact h2.outs j hj
    have hi : decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 512 + 32) 32) = V s1.mem b (ACC + 32) := by
      rw [show b + BitVec.ofNat 64 512 + 32 = b + BitVec.ofNat 64 544 by rw [BitVec.add_assoc]; rfl]
      refine bytes_of_words fun j hj => ?_
      have := h3.outs j hj
      rw [wd_shift] at this
      rw [wd_shift, show 544 + 4 * j = 512 + (32 + 4 * j) by omega, this, hhi j hj]
    rw [decode64, lo, hi, u1.mem, show (16 : Nat) = 8 + 8 from rfl, val32_append]
    rfl

/-- An input's 32 bytes at `p`, into the element at `o`. -/
theorem loadInput_ok {s : State} (hc : Ctx b s) {o : Nat} (ho : o + 32 ≤ 4096) {p : Reg} (hp : p ≠ .r0)
    {q : Addr} (hq : s.gpr p = q) (hr : (⟨q, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : (⟨q, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 o, 32⟩) :
    WP isa (.block (scalarLoadInput o p)) s fun t =>
      Rest [.r7, .r14] s t ∧ Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem t.mem ∧
      V t.mem b o = decodeLE (bytesAt s.mem q 32) := by
  unfold scalarLoadInput
  simp only [List.cons_append, List.nil_append]
  refine wp_addi hp (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.mono (unpackField_ok hc1 (q := q) (src := 0) (by rw [u1.gpr, hq, BitVec.add_zero]) ho (by decide)
    (fun k hk => by rw [u1.rd, u1.wr]; exact in_base hr (by omega) (by omega))
    (by rw [BitVec.add_zero]; exact hd)) fun t ⟨rt, ft, lt⟩ =>
      ⟨(u1.rest (by decide)).trans (rt.mono (by decide)), by rw [← u1.mem]; exact ft, ?_⟩
  rw [← u1.mem]
  exact (bytes_of_words fun j hj => by rw [lt j hj, Nat.zero_add]).symm

/-- Bytes apart from the working space keep their values through writes within it. -/
theorem bytes_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩) {q : Addr} {n : Nat}
    (hd : (⟨q, n⟩ : Region).Disjoint ⟨b, 8192⟩) (hn : n < 2 ^ 64) : bytesAt m' q n = bytesAt m q n := by
  simp only [bytesAt, List.map_inj_left]
  intro i hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by have := List.mem_range.mp hi; omega)
    (by have := List.mem_range.mp hi; omega)) (hs r hr _ hc)

end

/-- The precondition, by register: `out` in `r3`, `r`, `k` and `s` in `r4`–`r6`, `scratch` in `r7`. -/
structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 32⟩, ⟨s.gpr .r5, 32⟩, ⟨s.gpr .r6, 32⟩]
  wr : s.wr = [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r7, 8192⟩]
  out_ws : (⟨s.gpr .r3, 32⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  r_ws : (⟨s.gpr .r4, 32⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  k_ws : (⟨s.gpr .r5, 32⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩
  s_ws : (⟨s.gpr .r6, 32⟩ : Region).Disjoint ⟨s.gpr .r7, 8192⟩

theorem sub_ws (b : Addr) {d n : Nat} (h : d + n ≤ 8192) : Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ ⟨b, 8192⟩ :=
  Offset.sub_base b h

theorem disj_ws {q b : Addr} {n d k : Nat} (h : (⟨q, n⟩ : Region).Disjoint ⟨b, 8192⟩) (hd : d + k ≤ 8192) :
    (⟨q, n⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 d, k⟩ :=
  h.sub_right (sub_ws b hd)

/-- After the arguments of `scalar_mul_add`, from `s`. -/
structure ArgsPost (s : State) (b : Addr) (t : State) : Prop where
  ctx : Ctx b t
  rest : Rest [.r6, .r7, .r14, .r17, .r18] s t
  r18 : t.gpr .r18 = s.gpr .r3
  saved : Spill.Saved b s.gpr saveList t.mem
  vr : V t.mem b 64 = decodeLE (bytesAt s.mem (s.gpr .r4) 32)
  vk : V t.mem b 96 = decodeLE (bytesAt s.mem (s.gpr .r5) 32)
  vs : V t.mem b 128 = decodeLE (bytesAt s.mem (s.gpr .r6) 32)

theorem lowsub (b : Addr) {d n : Nat} (h : d + n ≤ 1024) : Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ ⟨b, 1024⟩ :=
  Offset.sub_base b h

theorem low_ws (b : Addr) : Region.Sub ⟨b, 1024⟩ ⟨b, 8192⟩ := fun x hx => by
  simp only [Region.Contains] at hx ⊢; omega

theorem mulAddArgs_ok {s : State} (hp : MulAddPre s) {b : Addr} (hb : b = s.gpr .r7) :
    WP isa (.block scalarMulAddArgs) s (ArgsPost s b) := by
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  have hV := SAVE_eq
  unfold scalarMulAddArgs
  rw [scalarSave_eq]
  simp only [List.append_assoc]
  have hsin : ∀ p ∈ saveList, InRegions s.wr (s.gpr .r7 + BitVec.ofNat 64 p.2) 8 := fun p hpl => by
    have := saveList_in p hpl
    rw [← hb]; exact in_base hws (by omega) (by omega)
  refine Spill.save_ok (b := .r7) (by decide) saveList_fits hsin ?_
  generalize hs1 : ({ s with mem := Spill.saveMem s.mem (s.gpr .r7) s.gpr saveList } : State) = s1
  have hsv : Spill.Saved b s.gpr saveList s1.mem := by rw [← hs1, hb]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf1 : Frame [⟨b, 8192⟩] s.mem s1.mem := by
    rw [← hs1, hb]
    exact Spill.saveMem_frame_base (fun p hpl => by have := saveList_in p hpl; omega) (by decide) _ _ _
  have hg1 : s1.gpr = s.gpr := by rw [← hs1]
  have hrd1 : s1.rd = s.rd := by rw [← hs1]
  have hwr1 : s1.wr = s.wr := by rw [← hs1]
  simp only [List.cons_append, List.nil_append]
  refine wp_addi (by decide) (by decide) fun s2 u2 => wp_addi (by decide) (by decide) fun s3 u3 =>
    wp_addi (by decide) (by decide) fun s4 u4 => ?_
  have hr4 : Rest [.r6, .r17, .r18] s1 s4 :=
    (u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide)))
  have hm4 : s4.mem = s1.mem := by rw [u4.mem, u3.mem, u2.mem]
  have e6 : s4.gpr .r6 = b := by
    rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), BitVec.add_zero, hg1, hb]
  have e17 : s4.gpr .r17 = s.gpr .r6 := by
    rw [u4.other _ (by decide), u3.gpr, u2.other _ (by decide), BitVec.add_zero, hg1]
  have e18 : s4.gpr .r18 = s.gpr .r3 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr, BitVec.add_zero, hg1]
  have hrd4 : s4.rd = s.rd := hr4.rd.trans hrd1
  have hwr4 : s4.wr = s.wr := hr4.wr.trans hwr1
  have hc4 : Ctx b s4 := ⟨e6, 8192, by decide, by rw [hwr4]; exact hws⟩
  have hwsb := hb ▸ hp.r_ws
  have hwsk := hb ▸ hp.k_ws
  have hwss := hb ▸ hp.s_ws
  have hrin : ∀ r : Reg, r = .r4 ∨ r = .r5 ∨ r = .r6 → (⟨s.gpr r, 32⟩ : Region) ∈ s4.rd ++ s4.wr := by
    rintro r (rfl | rfl | rfl) <;> (rw [hrd4, hp.rd]; simp)
  have g4 : ∀ r : Reg, r = .r4 ∨ r = .r5 → s4.gpr r = s.gpr r := by
    rintro r (rfl | rfl) <;> rw [hr4.gpr _ (by decide), hg1]
  refine WP.append (loadInput_ok hc4 (o := 64) (by omega) (p := .r4) (by decide) (q := s.gpr .r4)
    (g4 _ (.inl rfl)) (hrin _ (.inl rfl)) (disj_ws hwsb (by omega))) fun s5 ⟨rr5, f5, v5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest rr5 (by decide)
  refine WP.append (loadInput_ok hc5 (o := 96) (by omega) (p := .r5) (by decide) (q := s.gpr .r5)
    (by rw [rr5.gpr _ (by decide), g4 _ (.inr rfl)])
    (by rw [rr5.rd, rr5.wr]; exact hrin _ (.inr (.inl rfl))) (disj_ws hwsk (by omega))) fun s6 ⟨rr6, f6, v6⟩ => ?_
  have hc6 : Ctx b s6 := hc5.of_rest rr6 (by decide)
  refine WP.mono (loadInput_ok hc6 (o := 128) (by omega) (p := .r17) (by decide) (q := s.gpr .r6)
    (by rw [rr6.gpr _ (by decide), rr5.gpr _ (by decide), e17])
    (by rw [rr6.rd, rr6.wr, rr5.rd, rr5.wr]; exact hrin _ (.inr (.inr rfl))) (disj_ws hwss (by omega)))
    fun s7 ⟨rr7, f7, v7⟩ => ?_
  have hr47 : Rest [.r7, .r14] s4 s7 := rr5.trans (rr6.trans rr7)
  have sub1 : ∀ o, o + 32 ≤ 1024 → ∀ r ∈ ([⟨b + BitVec.ofNat 64 o, 32⟩] : List Region),
      ∃ r' ∈ ([⟨b, 1024⟩] : List Region), r.Sub r' := fun o ho r hr =>
    ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact lowsub b ho⟩
  have hf47 : Frame [⟨b, 1024⟩] s4.mem s7.mem :=
    (f5.sub (sub1 64 (by omega))).trans ((f6.sub (sub1 96 (by omega))).trans (f7.sub (sub1 128 (by omega))))
  -- The inputs' bytes, kept by the saves and the copies.
  have keep : ∀ {m' : Mem}, Frame [⟨b, 1024⟩] s4.mem m' → ∀ (q : Addr), (⟨q, 32⟩ : Region).Disjoint ⟨b, 8192⟩ →
      bytesAt m' q 32 = bytesAt s.mem q 32 := fun hf q hq => by
    rw [bytes_keep hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact low_ws b) hq (by decide),
      hm4, bytes_keep hf1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact fun _ h => h) hq (by decide)]
  have disj : ∀ o o', o + 32 ≤ o' ∨ o' + 32 ≤ o → o + 32 ≤ 4096 → o' + 32 ≤ 4096 →
      ∀ r ∈ ([⟨b + BitVec.ofNat 64 o', 32⟩] : List Region), ∀ k < 8,
        (⟨b + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r := fun o o' h h1 h2 r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine ⟨hc6.of_rest rr7 (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hr01 : Rest [] s s1 := ⟨fun r _ => by rw [hg1], hrd1, hwr1, by rw [← hs1]⟩
    exact (hr01.mono (by decide)).trans ((hr4.mono (by decide)).trans (hr47.mono (by decide)))
  · rw [rr7.gpr _ (by decide), rr6.gpr _ (by decide), rr5.gpr _ (by decide), e18]
  · rw [← hm4] at hsv
    refine hsv.frame_in (lo := SAVE) (n := 96) saveList_in hf47 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint_base _ (by omega) (by omega)
  · rw [V, val32_congr (limb_frame f7 (disj 64 128 (by omega) (by omega) (by omega))),
      val32_congr (limb_frame f6 (disj 64 96 (by omega) (by omega) (by omega))), ← V, v5,
      keep (Frame.refl _ _) _ hwsb]
  · rw [V, val32_congr (limb_frame f7 (disj 96 128 (by omega) (by omega) (by omega))), ← V, v6,
      keep (f5.sub (sub1 64 (by omega))) _ hwsk]
  · rw [v7, keep ((f5.sub (sub1 64 (by omega))).trans (f6.sub (sub1 96 (by omega)))) _ hwss]

/-- `k s + r` modulo `L`, into `SR`, writing nothing above byte 1023. -/
theorem mulAddEngine_ok {b : Addr} {s : State} (hc : Ctx b s) {R K Sc : Nat} (hVr : V s.mem b 64 = R)
    (hVk : V s.mem b 96 = K) (hVs : V s.mem b 128 = Sc) :
    WP isa scalarMulAddEngine s fun t =>
      Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16] s t ∧ Frame [⟨b, 1024⟩] s.mem t.mem ∧
      V t.mem b SR = (K * Sc + R) % L := by
  have hA := ACC_eq
  have hS := SR_eq
  unfold scalarMulAddEngine
  refine WP.seq (WP.mono (wideMul_ok (x := 96) (y := 128) (by omega) (by omega) hc) fun s8 h8 => ?_)
  have hc8 : Ctx b s8 := h8.ctx
  have hv8 : val32 (accw ACC s8.mem b) 16 = K * Sc := by rw [← hVk, ← hVs]; exact h8.val
  have hr8 : V s8.mem b 64 = R := by
    rw [← hVr]; unfold V
    exact val32_congr (limb_frame h8.frame fun r hr j hj => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
  have hK256 : K < 2 ^ 256 := by rw [← hVk]; exact V_lt _ _ _
  have hS256 : Sc < 2 ^ 256 := by rw [← hVs]; exact V_lt _ _ _
  have hR256 : R < 2 ^ 256 := by rw [← hr8]; exact V_lt _ _ _
  have hprod : K * Sc ≤ (2 ^ 256 - 1) * (2 ^ 256 - 1) := Nat.mul_le_mul (by omega) (by omega)
  refine WP.seq (WP.append (wideAdd_ok hc8 (by rw [hv8, hr8]; omega)) fun s9 ⟨r9, f9, v9⟩ => ?_)
  have hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.mono (packWide_ok hc9) fun s10 ⟨r10, f10, e10, v10⟩ => ?_
  have hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  have sub1 : ∀ o n, o + n ≤ 1024 → ∀ r ∈ ([⟨b + BitVec.ofNat 64 o, n⟩] : List Region),
      ∃ r' ∈ ([⟨b, 1024⟩] : List Region), r.Sub r' := fun o n ho r hr =>
    ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact lowsub b ho⟩
  refine WP.mono (engine_ok hc10 (p := b + BitVec.ofNat 64 512) e10
    (fun i hi => by rw [Offset.add_add]; exact hc10.inR (by omega))
    (fun i hi => by
      rw [Offset.add_add]
      exact fun hc => Offset.disjoint b (d := 512 + i) (n := 1) (e := SR) (k := 64) (.inr (by omega))
        (by omega) (by omega) _ (Region.contains_self _ _) hc)) fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_⟩
  · exact (h8.rest.mono (by decide)).trans ((r9.mono (by decide)).trans ((r10.mono (by decide)).trans
      (rt.mono (by decide))))
  · exact (h8.frame.sub (sub1 ACC 64 (by omega))).trans ((f9.sub (sub1 ACC 64 (by omega))).trans
      ((f10.sub (sub1 512 64 (by omega))).trans (ft.sub (sub1 SR 64 (by omega)))))
  · rw [vt, v10, v9, hv8, hr8]

/-- The element at `a` to `out` (at `P`), and the registers restored from the slots. -/
theorem scalarOut_ok {b : Addr} {u : State} (hc : Ctx b u) {a : Nat} (ha : a + 32 ≤ 1024) {P : Reg} (hP : P ≠ .r0) {q : Addr}
    (hq : u.gpr P = q) (hout : (⟨q, 32⟩ : Region) ∈ u.wr) (hd : (⟨q, 32⟩ : Region).Disjoint ⟨b, 8192⟩)
    (hws : (⟨b, 8192⟩ : Region) ∈ u.wr) {g : Reg → BitVec 64} (hsv : Spill.Saved b g saveList u.mem) :
    WP isa (.block (([.addi .r14 P 0] : List Instr) ++ packField a 0 ++ scalarRestore)) u fun t =>
      (∀ r ∈ savedRegs, t.gpr r = g r) ∧ (∀ r, r ∉ savedRegs → r ≠ .r7 → r ≠ .r14 → t.gpr r = u.gpr r) ∧
      t.sp = u.sp ∧ bytesAt t.mem q 32 = Spec.Ed25519.encodeLE 32 (V u.mem b a) := by
  have hV := SAVE_eq
  rw [scalarRestore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addi hP (by decide) fun s1 u1 => ?_
  have e14 : s1.gpr .r14 = q := by rw [u1.gpr, hq, BitVec.add_zero]
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r14]) (by decide)) (by decide)
  refine WP.append (packField_ok hc1 e14 (a := a) (dst := 0) (by omega) (by decide)
    (fun k hk => by rw [u1.wr]; exact in_base hout (by omega) (by omega))
    (by rw [BitVec.add_zero]; exact disj_ws hd (by omega))) fun s2 hp2 => ?_
  have hsv2 : Spill.Saved b g saveList s2.mem := by
    rw [← u1.mem] at hsv
    refine hsv.frame_in (lo := SAVE) (n := 96) saveList_in hp2.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, BitVec.add_zero]
    exact fun x h₁ h₂ => hd x h₂ (Offset.sub_base _ (by omega) x h₁)
  refine Spill.restore_ok (b := .r6) (B := b) (by decide)
    (by rw [hp2.rest.gpr _ (by decide), u1.other _ (by decide), hc.r6])
    saveList_fits saveList_restorable
    (fun p hpl => by
      have := saveList_in p hpl
      rw [hp2.rest.rd, hp2.rest.wr, u1.rd, u1.wr]
      exact in_base (List.mem_append_right _ hws) (by omega) (by omega)) hsv2
    fun s3 h3 => WP.block_nil ⟨fun r hr => ?_, fun r hr h7 h14 => ?_, ?_, ?_⟩
  · rw [← saveList_regs] at hr
    exact h3.gpr_of (.inl hr)
  · rw [← saveList_regs] at hr
    rw [h3.other _ hr, hp2.rest.gpr _ (by simpa using h7), u1.other _ h14]
  · rw [h3.sp, hp2.rest.sp, u1.sp]
  · rw [h3.mem]
    exact out_bytes (fun j hj => by rw [← Nat.zero_add (4 * j)]; exact hp2.outs j hj) (by rw [u1.mem])

theorem mulAdd_ok {s : State} (hp : MulAddPre s) :
    WP isa scalarMulAdd s fun t =>
      (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧
      bytesAt t.mem (s.gpr .r3) 32 = Spec.Ed25519.scalarMulAdd (bytesAt s.mem (s.gpr .r4) 32)
        (bytesAt s.mem (s.gpr .r5) 32) (bytesAt s.mem (s.gpr .r6) 32) := by
  have hV := SAVE_eq
  obtain ⟨b, hb⟩ : ∃ b, b = s.gpr .r7 := ⟨_, rfl⟩
  have hws : (⟨b, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr, hb]; simp
  have hout : (⟨s.gpr .r3, 32⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  unfold scalarMulAdd
  refine WP.seq (WP.mono (mulAddArgs_ok hp hb) fun s7 h7 => ?_)
  refine WP.seq (WP.mono (mulAddEngine_ok h7.ctx h7.vr h7.vk h7.vs) fun s11 ⟨r11, f11, v11⟩ => ?_)
  have hwr : s11.wr = s.wr := by rw [r11.wr, h7.rest.wr]
  have hsv : Spill.Saved b s.gpr saveList s11.mem :=
    h7.saved.frame_in (lo := SAVE) (n := 96) saveList_in f11 fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega) (by omega)
  refine WP.mono (scalarOut_ok (h7.ctx.of_rest r11 (by decide)) (a := SR) (by decide) (P := .r18) (by decide)
    (by rw [r11.gpr _ (by decide), h7.r18]) (by rw [hwr]; exact hout) (hb ▸ hp.out_ws) (by rw [hwr]; exact hws) hsv)
    fun t ⟨hg, ho, hsp, hbytes⟩ => ⟨fun r hr => ?_, ?_, ?_⟩
  · by_cases hm : r ∈ savedRegs
    · exact hg r hm
    · have h1 : r ≠ .r7 := by revert hr; cases r <;> decide
      have h2 : r ≠ .r14 := by revert hm; cases r <;> decide
      have h3 : r ∉ ([.r4, .r5, .r7, .r8, .r9, .r10, .r11, .r14, .r15, .r16] : List Reg) := by
        revert hr hm; cases r <;> decide
      have h4 : r ∉ ([.r6, .r7, .r14, .r17, .r18] : List Reg) := by revert hr hm; cases r <;> decide
      rw [ho r hm h1 h2, r11.gpr _ h3, h7.rest.gpr _ h4]
  · rw [hsp, r11.sp, h7.rest.sp]
  · rw [hbytes, v11, Nat.add_comm]; rfl

end VG.Proof.Ed25519.PPC64LE
