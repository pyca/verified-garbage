module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.MulFn
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Word
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# Ed25519 on PPC64LE: `vg_gf25519_r32_mul`'s code

From the working space at `r3` and the offsets `o`, `a` and `c` in the low
words of `r4`–`r6`, `mulFn` stores at `o` a number congruent to the product
of the elements at `a` and `c` (`mulFn_ok`): the 16 limbs of the product at
`ACC` row by row (`row_ok`, X25519's `RowInv` with the operands through
pointers), then `lo + 38 hi` and the carry folded in, at `o` through `r12`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)

/-- `r3` holds the working space `b`, at least 4096 writable bytes. -/
structure Ctx3 (b : Addr) (s : State) : Prop where
  r3 : s.gpr .r3 = b
  wr : ∃ n, 4096 ≤ n ∧ (⟨b, n⟩ : Region) ∈ s.wr

theorem Ctx3.of_rest {b : Addr} {s s' : State} {ws : List Reg} (h : Ctx3 b s) (hr : Rest ws s s')
    (h3 : Reg.r3 ∉ ws) : Ctx3 b s' :=
  ⟨by rw [hr.gpr _ h3, h.r3], by rw [hr.wr]; exact h.wr⟩

theorem Ctx3.inW {b : Addr} {s : State} (h : Ctx3 b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n := by
  obtain ⟨k, hk, hw⟩ := h.wr
  exact in_base hw (by omega_using [hd, hk]) (by omega_using [hd])

theorem Ctx3.inR {b : Addr} {s : State} (h : Ctx3 b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) n := by
  obtain ⟨k, hk, hw⟩ := h.wr
  exact in_base (List.mem_append_right _ hw) (by omega_using [hd, hk]) (by omega_using [hd])

theorem wp_rotr0 {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat % 2 ^ 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rotr .w d n 0 :: is)) s Q := by
  have e : (((s.gpr n).setWidth 32).rotateRight 0).setWidth 64 = BitVec.ofNat 64 ((s.gpr n).toNat % 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    have r0 : ∀ v : BitVec 32, v.rotateRight 0 = v := fun v => by
      simp [BitVec.rotateRight, BitVec.rotateRightAux]
    simp only [r0, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact WP.cons (exec_rotr_w (by decide)) (by rw [e]; exact k _ (Upd.write _ _ _))

/-- The registers `mulFn` changes. -/
abbrev mulFnClob : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

section
variable {b : Addr}

/-- After `mulSetup` from `s0`, for the operands at `x` and `y` and the
result at `o`. -/
structure MulPre (b : Addr) (o x y : Nat) (s0 s : State) : Prop where
  ctx : Ctx3 b s
  rest : Rest mulFnClob s0 s
  r0 : s.gpr .r0 = 38
  r12 : s.gpr .r12 = b + BitVec.ofNat 64 o
  r10 : s.gpr .r10 = b + BitVec.ofNat 64 x
  r6 : s.gpr .r6 = b + BitVec.ofNat 64 y
  r9 : s.gpr .r9 = b
  r11 : s.gpr .r11 = 8
  frame : Frame [⟨b + BitVec.ofNat 64 ACC, 32⟩] s0.mem s.mem
  zero : ∀ j < 8, accw ACC s.mem b j = 0

theorem mulSetup_ok {o x y : Nat} {s : State} (hc : Ctx3 b s)
    (h4 : (s.gpr .r4).toNat % 2 ^ 32 = o) (h5 : (s.gpr .r5).toNat % 2 ^ 32 = x)
    (h6 : (s.gpr .r6).toNat % 2 ^ 32 = y) :
    WP isa (.seq (.block mulZext) (.block mulSetup)) s (MulPre b o x y s) := by
  have hA := ACC_eq
  refine WP.seq (wp_rotr0 fun s1 u1 => wp_rotr0 fun s2 u2 => wp_rotr0 fun s3 u3 => WP.block_nil ?_)
  simp only [mulSetup, List.cons_append, List.nil_append, List.map, List.range, List.range.loop]
  refine wp_add fun s4 u4 => wp_add fun s5 u5 => wp_add fun s6 u6 => ?_
  refine wp_li (by decide) fun s7 u7 => wp_li (by decide) fun s8 u8 => ?_
  have hr8 : Rest mulFnClob s s8 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide))))))))
  have hc8 : Ctx3 b s8 := hc.of_rest hr8 (by decide)
  have g3 : ∀ t : State, Rest mulFnClob s t → t.gpr .r3 = b := fun t ht => by
    rw [ht.gpr _ (by decide), hc.r3]
  have st : ∀ (t : State), Ctx3 b t → ∀ d, d + 4 ≤ 4096 → ∀ {is : List Instr} {Q : State → Prop},
      (∀ t', Mupd t t' (t.mem.writeW (b + BitVec.ofNat 64 d) ((t.gpr .r7).setWidth 32)) →
        WP isa (.block is) t' Q) → WP isa (.block (.store .w .r7 .r3 d :: is)) t Q :=
    fun t ht d hd _ _ k => wp_sw (by decide) (by omega_arith) (by rw [ht.r3]) (ht.inW hd) k
  -- The eight stores of zero.
  have hz : ∀ t : State, Rest [] s8 t → t.gpr .r7 = 0 := fun t ht => by
    rw [ht.gpr _ (by decide), u8.gpr]; rfl
  refine st _ hc8 _ (by omega_arith) fun t1 v1 => ?_
  refine st _ (hc8.of_rest (v1.rest []) (by decide)) _ (by omega_arith) fun t2 v2 => ?_
  have r2 : Rest [] s8 t2 := (v1.rest []).trans (v2.rest [])
  refine st _ (hc8.of_rest r2 (by decide)) _ (by omega_arith) fun t3 v3 => ?_
  have r3 : Rest [] s8 t3 := r2.trans (v3.rest [])
  refine st _ (hc8.of_rest r3 (by decide)) _ (by omega_arith) fun t4 v4 => ?_
  have r4 : Rest [] s8 t4 := r3.trans (v4.rest [])
  refine st _ (hc8.of_rest r4 (by decide)) _ (by omega_arith) fun t5 v5 => ?_
  have r5 : Rest [] s8 t5 := r4.trans (v5.rest [])
  refine st _ (hc8.of_rest r5 (by decide)) _ (by omega_arith) fun t6 v6 => ?_
  have r6 : Rest [] s8 t6 := r5.trans (v6.rest [])
  refine st _ (hc8.of_rest r6 (by decide)) _ (by omega_arith) fun t7 v7 => ?_
  have r7 : Rest [] s8 t7 := r6.trans (v7.rest [])
  refine st _ (hc8.of_rest r7 (by decide)) _ (by omega_arith) fun t8 v8 => ?_
  have r8 : Rest [] s8 t8 := r7.trans (v8.rest [])
  refine wp_addi (by decide) (by decide) fun t9 w9 => wp_li (by decide) fun t10 w10 => WP.block_nil ?_
  have hm : t10.mem = ((((((((s8.mem.writeW (b + BitVec.ofNat 64 (ACC + 4 * 0)) (0 : BitVec 32)).writeW
      (b + BitVec.ofNat 64 (ACC + 4 * 1)) (0 : BitVec 32)).writeW (b + BitVec.ofNat 64 (ACC + 4 * 2)) (0 : BitVec 32)).writeW
      (b + BitVec.ofNat 64 (ACC + 4 * 3)) (0 : BitVec 32)).writeW (b + BitVec.ofNat 64 (ACC + 4 * 4)) (0 : BitVec 32)).writeW
      (b + BitVec.ofNat 64 (ACC + 4 * 5)) (0 : BitVec 32)).writeW (b + BitVec.ofNat 64 (ACC + 4 * 6)) (0 : BitVec 32)).writeW
      (b + BitVec.ofNat 64 (ACC + 4 * 7)) (0 : BitVec 32)) := by
    have z : ∀ t : State, Rest [] s8 t → (t.gpr .r7).setWidth 32 = 0 := fun t ht => by rw [hz t ht]; rfl
    rw [w10.mem, w9.mem, v8.mem, z _ r7, v7.mem, z _ r6, v6.mem, z _ r5, v5.mem, z _ r4, v4.mem, z _ r3,
      v3.mem, z _ r2, v2.mem, z _ (v1.rest []), v1.mem, z _ (Rest.refl _ _)]
  have hr10 : Rest mulFnClob s t10 := hr8.trans ((r8.mono (by decide)).trans ((w9.rest (by decide)).trans
    (w10.rest (by decide))))
  have e3 : s3.gpr .r3 = b := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hc.r3]
  have eo : (s3.gpr .r4) = BitVec.ofNat 64 o := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h4]
  have ex : (s3.gpr .r5) = BitVec.ofNat 64 x := by
    rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), h5]
  have ey : (s3.gpr .r6) = BitVec.ofNat 64 y := by rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide), h6]
  have g8 : ∀ r, r ∉ ([.r9, .r11] : List Reg) → t10.gpr r = s8.gpr r := fun r hr => by
    rw [w10.other _ (by simp at hr; exact hr.2), w9.other _ (by simp at hr; exact hr.1), r8.gpr _ (by simp)]
  refine ⟨hc.of_rest hr10 (by decide), hr10, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · rw [g8 _ (by decide), u8.other _ (by decide), u7.gpr]; rfl
  · rw [g8 _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.other _ (by decide), u4.gpr, e3, eo]
  · rw [g8 _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
      u5.gpr, u4.other .r3 (by decide), u4.other .r5 (by decide), e3, ex]
  · rw [g8 _ (by decide), u8.other _ (by decide), u7.other _ (by decide), u6.gpr, u5.other .r3 (by decide),
      u5.other .r6 (by decide), u4.other .r3 (by decide), u4.other .r6 (by decide), e3, ey]
  · rw [w10.other _ (by decide), w9.gpr, r8.gpr _ (by decide), hc8.r3, BitVec.add_zero]
  · rw [w10.gpr]; rfl
  · have m1 := List.mem_singleton_self (⟨b + BitVec.ofNat 64 ACC, 32⟩ : Region)
    have c : ∀ k < 8, (⟨b + BitVec.ofNat 64 ACC, 32⟩ : Region).Contains (b + BitVec.ofNat 64 (ACC + 4 * k)) (32 / 8) :=
      fun k hk => Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [hm, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact (((((((((Frame.refl _ _).writeW m1 _ (c 0 (by decide))).writeW m1 _ (c 1 (by decide))).writeW m1 _
      (c 2 (by decide))).writeW m1 _ (c 3 (by decide))).writeW m1 _ (c 4 (by decide))).writeW m1 _
      (c 5 (by decide))).writeW m1 _ (c 6 (by decide))).writeW m1 _ (c 7 (by decide)))
  · rw [accw, hm]
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega_arith
    rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := omega_arith) only [wd_write_other, wd_write_self] <;> rfl

/-- The loop invariant of the rows of `mulFn` from `s0`, after `i` rows. -/
structure RowInvF (b : Addr) (o x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx3 b s
  rest : Rest mulFnClob s0 s
  r0 : s.gpr .r0 = 38
  r12 : s.gpr .r12 = b + BitVec.ofNat 64 o
  r10 : s.gpr .r10 = b + BitVec.ofNat 64 (x + 4 * i)
  r6 : s.gpr .r6 = b + BitVec.ofNat 64 y
  r9 : s.gpr .r9 = b + BitVec.ofNat 64 (4 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (8 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 ACC, 64⟩] s0.mem s.mem
  val : val32 (accw ACC s.mem b) (i + 8) = val32 (limb s0.mem b x) i * V s0.mem b y

theorem rowF_ok {o x y : Nat} (hx : x + 32 ≤ 768) (hy : y + 32 ≤ 768)
    {s0 : State} {i : Nat} (hi : i < 8) {s : State} (h : RowInvF b o x y s0 i s) :
    WP isa (.block mulRow) s fun s' =>
      RowInvF b o x y s0 (i + 1) s' ∧ (s'.gpr .r11 != 0) = decide (8 - (i + 1) ≠ 0) := by
  have hA := ACC_eq
  have hframe0 : ∀ z : Nat, z + 32 ≤ 768 → ∀ k < 8,
      limb s.mem b z k = limb s0.mem b z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [mulRow, List.cons_append, List.nil_append]
  refine wp_lw (a := b + BitVec.ofNat 64 (x + 4 * i)) (by decide) (by decide)
    (by rw [h.r10]; simp) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  have hr2 : Rest [.r4, .r8] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx3 b s2 := h.ctx.of_rest hr2 (by decide)
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have e1 : (s2.gpr .r4).toNat = limb s0.mem b x i := by
    rw [u2.other _ (by decide), u1.gpr, toNat_ext32, ← hframe0 x hx i hi]; rfl
  have e9 : s2.gpr .r9 = b + BitVec.ofNat 64 (4 * i) := by rw [hr2.gpr _ (by decide), h.r9]
  have e6 : s2.gpr .r6 = b + BitVec.ofNat 64 y := by rw [hr2.gpr _ (by decide), h.r6]
  have hlt : ∀ j < 8, rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i j + 2 ^ 32 ≤ 2 ^ 64 :=
    fun j _ => rowC_le (limb_lt _ _ _ _) (limb_lt _ _ _ _) (wd_lt _ _ _)
  refine WP.append (pass_ok (rb := .r9) (o := ACC) (s0 := s2)
    (c := rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i)
    (cin := 0) (by decide) (by decide) (by omega_arith)
    (fun k hk => by rw [e9, Offset.add_add]; exact hc2.inW (by omega_arith))
    (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    have hc' : Ctx3 b s' := hc2.of_rest hp'.rest (by decide)
    have hf' : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
      have := hp'.frame; rwa [e9, Offset.add_add] at this
    simp only [mulRowSrc]
    refine wp_lw (a := b + BitVec.ofNat 64 (y + 4 * k)) (by decide) (by omega_arith)
      (by rw [hp'.rest.gpr _ (by decide), e6, Offset.add_add]) (hc'.inR (by omega_arith)) fun t1 v1 => ?_
    refine wp_mul fun t2 v2 => ?_
    refine wp_lw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 4 * k))) (by decide) (by omega_arith)
      (by rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), e9,
        Offset.add_add]) (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc'.inR (by omega_arith))
      fun t3 v3 => ?_
    refine wp_add fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have ey : (t1.gpr .r5).toNat = limb s0.mem b y k := by
        rw [v1.gpr, toNat_ext32, ← hframe0 y hy k hk, ← hm2]
        show wd s'.mem _ _ = wd s2.mem _ _
        exact wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      have ea : (t1.gpr .r4).toNat = limb s0.mem b x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      have e2 : (t2.gpr .r5).toNat = limb s0.mem b x i * limb s0.mem b y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; exact mul32_lt (limb_lt _ _ _ _) (limb_lt _ _ _ _)), ea, ey]
      have e3 : (t3.gpr .r7).toNat = accw ACC s.mem b (i + k) := by
        rw [v3.gpr, toNat_ext32, v2.mem, v1.mem, accw, ← hm2]
        show wd s'.mem _ _ = _
        rw [wd_frame hf' fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)]
        congr 1; omega_arith
      have := hlt k hk
      rw [v4.gpr, v3.other .r5 (by decide)]
      rw [toNat_add_lt (by rw [e3, e2]; simp only [rowC] at this; omega_arith), e3, e2,
        rowC, Nat.add_comm]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  · -- The carry, and the next row.
    have hc3 : Ctx3 b s3 := hc2.of_rest hp.rest (by decide)
    have e9' : s3.gpr .r9 = b + BitVec.ofNat 64 (4 * i) := by rw [hp.rest.gpr _ (by decide), e9]
    refine wp_sw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 32))) (by decide) (by omega_arith)
      (by rw [e9', Offset.add_add]) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
    refine wp_addi (by decide) (by decide) fun s5 u5 => wp_addi (by decide) (by decide) fun s6 u6 =>
      wp_subi (by decide) (by decide) fun s7 u7 => ?_
    refine WP.block_nil ?_
    have hr7 : Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s s7 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide))))))
    have hm7 : s7.mem = s3.mem.writeW (b + BitVec.ofNat 64 (4 * i + (ACC + 32))) ((s3.gpr .r8).setWidth 32) := by
      rw [u7.mem, u6.mem, u5.mem, u4.mem]
    have hpf : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 32⟩] s.mem s3.mem := by
      have := hp.frame; rw [e9, Offset.add_add] at this; rw [← hm2]; exact this
    have hr11 : s7.gpr .r11 = BitVec.ofNat 64 (8 - (i + 1)) := by
      rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide),
        hr2.gpr _ (by decide), h.r11, ofNat_sub_one (by omega_arith) (by omega_arith)]
      congr 1
    have hch := chain_lt (cin := 0) hlt (by decide) 8 (Nat.le_refl _)
    have hacc : ∀ k < i + 9, accw ACC s7.mem b k =
        rowAcc (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i k := by
      intro k hk
      rw [accw, hm7]
      rcases Nat.lt_or_ge k (i + 8) with hk' | hk'
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
        rcases Nat.lt_or_ge k i with hki | hki
        · rw [wd_frame hpf fun r hr => by
            rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)]
          simp only [rowAcc, hki, ite_true]; rfl
        · have := hp.outs (k - i) (by omega_arith)
          rw [e9, wd_shift, show 4 * i + (ACC + 4 * (k - i)) = ACC + 4 * k by omega_arith] at this
          rw [this]
          simp only [rowAcc, show ¬ k < i by omega_arith, hk', ite_false, ite_true]
      · rw [show ACC + 4 * k = 4 * i + (ACC + 32) by omega_arith, wd_write_self, toNat_lo32, hp.r8,
          Nat.mod_eq_of_lt hch]
        simp only [rowAcc, show ¬ k < i by omega_arith, show ¬ k < i + 8 by omega_arith, ite_false]
    refine ⟨⟨hc3.of_rest ((u4.rest [.r9, .r10, .r11]).trans ((u5.rest (by decide)).trans
        ((u6.rest (by decide)).trans (u7.rest (by decide))))) (by decide),
      h.rest.trans (hr7.mono (by decide)), by rw [hr7.gpr _ (by decide), h.r0],
      by rw [hr7.gpr _ (by decide), h.r12], ?_, by rw [hr7.gpr _ (by decide), h.r6], ?_, hr11, ?_, ?_⟩, ?_⟩
    · rw [u7.other _ (by decide), u6.gpr, u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide),
        hr2.gpr _ (by decide), h.r10, Offset.add_add, Nat.mul_succ, Nat.add_assoc]
    · rw [u7.other _ (by decide), u6.other _ (by decide), u5.gpr, u4.gpr, e9', Offset.add_add, Nat.mul_succ]
    · rw [hm7]
      refine (h.frame.trans (hpf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [val32_congr hacc]; exact row_val h.val
    · rw [hr11, ofNat_ne_zero (by omega_arith)]

/-- `mulFinal` from the state after the rows, with the product's limbs at
`ACC`: `lo + 38 hi` into the limbs at `o` (through `r12`), the carry out
folded in twice. -/
theorem mulFinal_ok {o : Nat} (ho : o + 32 ≤ 768) {s : State} (hc : Ctx3 b s)
    (h0 : s.gpr .r0 = 38) (h12 : s.gpr .r12 = b + BitVec.ofNat 64 o) :
    WP isa (.block mulFinal) s fun s' =>
      Rest [.r5, .r7, .r8] s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s'.mem ∧
      V s'.mem b o % P = val32 (accw ACC s.mem b) 16 % P := by
  have hA := ACC_eq
  have t38 : (38 : BitVec 64).toNat = 38 := rfl
  have hl16 : ∀ k < 16, accw ACC s.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
  have hlo := val32_lt (f := accw ACC s.mem b) (n := 8) fun k hk => hl16 k (by omega_arith)
  have hhi := val32_lt (f := fun k => accw ACC s.mem b (8 + k)) (n := 8) fun k hk => hl16 (8 + k) (by omega_arith)
  rw [show 32 * 8 = 256 from rfl] at hlo hhi
  have hv : val32 (foldC (accw ACC s.mem b)) 8 < 39 * 2 ^ 256 := by rw [val32_foldC]; omega_arith
  have hrb : ∀ t : State, Rest [.r5, .r7, .r8] s t → t.gpr .r12 = b + BitVec.ofNat 64 o := fun t ht => by
    rw [ht.gpr _ (by decide), h12]
  have hw : ∀ t : State, Rest [.r5, .r7, .r8] s t → ∀ k < 8,
      InRegions t.wr (t.gpr .r12 + BitVec.ofNat 64 (0 + 4 * k)) 4 := fun t ht k hk => by
    rw [hrb t ht, Offset.add_add]; exact (hc.of_rest ht (by decide)).inW (by omega_arith)
  simp only [mulFinal, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_li (by decide) fun s1 u1 => ?_
  have hr1 : Rest [.r5, .r7, .r8] s s1 := u1.rest (by decide)
  have hc1 : Ctx3 b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r12) (o := 0) (s0 := s1) (c := foldC (accw ACC s.mem b)) (cin := 0)
    (by decide) (by decide) (by decide) (hw s1 hr1) (by rw [u1.gpr]; rfl) (foldC_le hl16) (by decide) ?_)
    fun s2 hp => ?_
  · intro k hk s' hp'
    have hc' : Ctx3 b s' := hc1.of_rest hp'.rest (by decide)
    have hfr : ∀ d, d + 4 ≤ 4096 → (d + 4 ≤ o ∨ o + 32 ≤ d) → wd s'.mem b d = wd s.mem b d := fun d hd hd' => by
      rw [← u1.mem]
      refine wd_frame hp'.frame fun r hr => ?_
      rw [List.mem_singleton.mp hr, hrb s1 hr1, Offset.add_add]
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
    simp only [mulFnSrc]
    refine wp_lw (a := b + BitVec.ofNat 64 (ACC + 4 * k)) (by decide) (by omega_arith)
      (by rw [hc'.r3]) (hc'.inR (by omega_arith)) fun t1 v1 => ?_
    refine wp_lw (a := b + BitVec.ofNat 64 (ACC + 32 + 4 * k)) (by decide) (by omega_arith)
      (by rw [v1.other _ (by decide), hc'.r3]) (by rw [v1.rd, v1.wr]; exact hc'.inR (by omega_arith)) fun t2 v2 => ?_
    refine wp_mul fun t3 v3 => wp_add fun t4 v4 => WP.block_nil ⟨?_, ?_, by
      rw [v4.mem, v3.mem, v2.mem, v1.mem]⟩
    · have el : (t1.gpr .r7).toNat = accw ACC s.mem b k := by
        rw [v1.gpr, toNat_ext32]; show wd s'.mem _ _ = _
        rw [hfr _ (by omega_arith) (by omega_arith)]; rfl
      have eh : (t2.gpr .r5).toNat = accw ACC s.mem b (8 + k) := by
        rw [v2.gpr, toNat_ext32, v1.mem]; show wd s'.mem _ _ = _
        rw [hfr _ (by omega_arith) (by omega_arith), accw]
        congr 1; omega_arith
      have e0 : t2.gpr .r0 = 38 := by
        rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), hr1.gpr _ (by decide), h0]
      have hh := hl16 (8 + k) (by omega_arith)
      have hl := hl16 k (by omega_arith)
      have e3 : (t3.gpr .r5).toNat = accw ACC s.mem b (8 + k) * 38 := by
        rw [v3.gpr, e0, toNat_mul_lt (by rw [eh, t38]; omega_arith), eh, t38]
      rw [v4.gpr, v3.other .r7 (by decide), v2.other .r7 (by decide),
        toNat_add_lt (by rw [el, e3]; omega_arith), el, e3, foldC, Nat.mul_comm 38]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  -- The fold done; the carry out, folded in as 38 times itself.
  have hr2 : Rest [.r5, .r7, .r8] s s2 := hr1.trans hp.rest
  have hc2 : Ctx3 b s2 := hc.of_rest hr2 (by decide)
  have hpo : ∀ j < 8, wd s2.mem b (o + 4 * j) = out (foldC (accw ACC s.mem b)) 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hrb s1 hr1, wd_shift, Nat.zero_add] at this
  have hpf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s2.mem := by
    have := hp.frame; rw [hrb s1 hr1, Offset.add_add, Nat.add_zero] at this; rw [← u1.mem]; exact this
  have hcl := carry_le hv
  refine wp_mul fun s3 u3 => ?_
  have e3 : (s3.gpr .r8).toNat = 38 * chain (foldC (accw ACC s.mem b)) 0 8 := by
    rw [u3.gpr, hr2.gpr .r0 (by decide), h0, toNat_mul_lt (by rw [hp.r8, t38]; omega_arith), hp.r8, t38]
    omega_arith
  have hr3 : Rest [.r5, .r7, .r8] s s3 := hr2.trans (u3.rest (by decide))
  have hl : ∀ k < 8, limb s2.mem b o k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  have ht := tail_facts hl (c8 := chain (foldC (accw ACC s.mem b)) 0 8) hcl
  refine WP.append (pass_ok (rb := .r12) (o := 0) (s0 := s3) (c := limb s2.mem b o)
    (cin := 38 * chain (foldC (accw ACC s.mem b)) 0 8)
    (by decide) (by decide) (by decide) (hw s3 hr3) e3 (fun k hk => by have := hl k hk; omega_arith) (by omega_arith) ?_)
    fun s4 hp4 => ?_
  · intro k hk s' hp'
    have hc' : Ctx3 b s' := (hc.of_rest hr3 (by decide)).of_rest hp'.rest (by decide)
    simp only [mulTailSrc]
    refine wp_lw (a := b + BitVec.ofNat 64 (o + 4 * k)) (by decide) (by omega_arith)
      (by rw [hp'.rest.gpr _ (by decide), hrb s3 hr3, Offset.add_add]) (hc'.inR (by omega_arith))
      fun t1 v1 => WP.block_nil ⟨?_, v1.rest (by decide), v1.mem⟩
    rw [v1.gpr, toNat_ext32]
    show wd s'.mem _ _ = _
    rw [← u3.mem]
    refine wd_frame hp'.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr, hrb s3 hr3, Offset.add_add]
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  have hr4 : Rest [.r5, .r7, .r8] s s4 := hr3.trans hp4.rest
  have hc4 : Ctx3 b s4 := hc.of_rest hr4 (by decide)
  have hpo4 : ∀ j < 8, wd s4.mem b (o + 4 * j) = out (limb s2.mem b o) (38 * chain (foldC (accw ACC s.mem b)) 0 8) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hrb s3 hr3, wd_shift, Nat.zero_add] at this
  have hpf4 : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hrb s3 hr3, Offset.add_add, Nat.add_zero] at this
  refine wp_mul fun s5 u5 => ?_
  have e5 : (s5.gpr .r8).toNat = 38 * chain (limb s2.mem b o) (38 * chain (foldC (accw ACC s.mem b)) 0 8) 8 := by
    rw [u5.gpr, hr4.gpr .r0 (by decide), h0, toNat_mul_lt (by rw [hp4.r8, t38]; have := ht.1; omega_arith), hp4.r8, t38]
    omega_arith
  have hr5 : Rest [.r5, .r7, .r8] s s5 := hr4.trans (u5.rest (by decide))
  refine wp_lw (a := b + BitVec.ofNat 64 o) (by decide) (by decide)
    (by rw [hrb s5 hr5]; simp) ((hc.of_rest hr5 (by decide)).inR (by omega_arith)) fun s6 u6 => ?_
  refine wp_add fun s7 u7 => ?_
  have hr7 : Rest [.r5, .r7, .r8] s s7 := hr5.trans ((u6.rest (by decide)).trans (u7.rest (by decide)))
  refine wp_sw (a := b + BitVec.ofNat 64 o) (by decide) (by decide)
    (by rw [hrb s7 hr7]; simp) ((hc.of_rest hr7 (by decide)).inW (by omega_arith)) fun s8 u8 => WP.block_nil ?_
  have h0' := ht.2.1 0 (by decide)
  have o0 := hpo4 0 (by decide)
  rw [Nat.mul_zero, Nat.add_zero] at o0
  have e7 : (s7.gpr .r7).toNat = tailL (limb s2.mem b o) (chain (foldC (accw ACC s.mem b)) 0 8) 0 := by
    rw [u7.gpr, u6.gpr, u6.other .r8 (by decide), u5.mem]
    simp only [tailL, ite_true] at h0' ⊢
    unfold wd at o0
    rw [toNat_add_lt (by rw [toNat_ext32, e5, o0]; omega_arith), toNat_ext32, e5, o0]
  have hm8 : s8.mem = s4.mem.writeW (b + BitVec.ofNat 64 o) ((s7.gpr .r7).setWidth 32) := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem]
  have hlimb : ∀ k < 8, limb s8.mem b o k = tailL (limb s2.mem b o) (chain (foldC (accw ACC s.mem b)) 0 8) k := by
    intro k hk
    rw [limb, hm8]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_write_self, toNat_lo32, e7, Nat.mod_eq_of_lt h0']
    · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), hpo4 k hk]
      simp only [tailL, show k ≠ 0 by omega_arith, ite_false]
  refine ⟨hr7.trans (u8.rest _), ?_, ?_⟩
  · rw [hm8]
    refine (hpf.trans (?_ : Frame _ s2.mem s4.mem)).writeW (List.mem_singleton_self _) _
      (Offset.contains b (d := o) (n := 32 / 8) (e := o) (k := 32) (Nat.le_refl _) (by omega_arith) (by omega_arith))
    rw [← u3.mem]; exact hpf4
  · rw [V, val32_congr hlimb, ht.2.2, val32_congr (f := limb s2.mem b o) hpo]
    have hcv := chain_val (foldC (accw ACC s.mem b)) 0 8
    rw [show 32 * 8 = 256 from rfl, Nat.add_zero] at hcv
    rw [hcv, val32_foldC, ← Proof.X25519.fold256, show (16 : Nat) = 8 + 8 from rfl, val32_append,
      show 32 * 8 = 256 from rfl]


/-- The whole multiplication: `r3` the working space, `r4`, `r5` and `r6` the
offsets of the product and the factors (as words). -/
theorem mulFn_ok {o x y : Nat} (ho : o + 32 ≤ 768) (hx : x + 32 ≤ 768) (hy : y + 32 ≤ 768)
    {s : State} (hc : Ctx3 b s)
    (h4 : (s.gpr .r4).toNat % 2 ^ 32 = o) (h5 : (s.gpr .r5).toNat % 2 ^ 32 = x)
    (h6 : (s.gpr .r6).toNat % 2 ^ 32 = y) :
    WP isa mulFn s fun s' =>
      Rest mulFnClob s s' ∧
      Frame [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b x * V s.mem b y) % P := by
  unfold mulFn
  refine WP.assoc (WP.seq (WP.mono (mulSetup_ok (o := o) hc h4 h5 h6) fun s1 h1 => ?_))
  have r0 : RowInvF b o x y s 0 s1 := by
    refine ⟨h1.ctx, h1.rest, h1.r0, h1.r12, by rw [h1.r10]; rfl, h1.r6, by rw [h1.r9]; simp,
      by rw [h1.r11]; rfl, ?_, ?_⟩
    · refine h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [Nat.zero_add, val32_congr (g := fun _ => 0) h1.zero, val32_zero_fn]
      exact (Nat.zero_mul _).symm
  refine WP.seq (WP.mono (Q := RowInvF b o x y s 8) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 8 - i ∧ i < 8 ∧ RowInvF b o x y s i s') ?_ 8 s1 ⟨0, rfl, by decide, r0⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (rowF_ok hx hy hi hr) fun s'' ⟨hr', hz⟩ => ?_
    by_cases h8 : i + 1 = 8
    · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h8], ?_⟩
      rw [h8] at hr'; exact hr'
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 8 - (i + 1), by omega_arith, i + 1, rfl,
        by omega_arith, hr'⟩
  · refine WP.mono (mulFinal_ok ho h2.ctx h2.r0 h2.r12) fun s3 ⟨hr3, hf3, hv3⟩ => ⟨?_, ?_, ?_⟩
    · exact h2.rest.trans (hr3.mono (by decide))
    · exact (h2.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]).trans
        (hf3.mono fun r hr => by simp [List.mem_singleton.mp hr])
    · rw [hv3, h2.val]; rfl

end

end VG.Proof.Ed25519.PPC64LE
