module

public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Power
public import VerifiedGarbage.Proof.X25519.Chain250
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Spec.Ed25519
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.X25519.PPC64LE.AddSub
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.MulFn
public import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Word
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-! ### `Ed25519.PPC64LE.MulFn`, which this module and modules that import it used -/

section

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
  obtain e : (((s.gpr n).setWidth 32).rotateRight 0).setWidth 64 = BitVec.ofNat 64 ((s.gpr n).toNat % 2 ^ 32) := by
    apply BitVec.eq_of_toNat_eq
    obtain r0 : ∀ v : BitVec 32, v.rotateRight 0 = v := fun v => by
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
  obtain hr8 : Rest mulFnClob s s8 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide))))))))
  obtain hc8 : Ctx3 b s8 := hc.of_rest hr8 (by decide)
  obtain g3 : ∀ t : State, Rest mulFnClob s t → t.gpr .r3 = b := fun t ht => by
    rw [ht.gpr _ (by decide), hc.r3]
  obtain st : ∀ (t : State), Ctx3 b t → ∀ d, d + 4 ≤ 4096 → ∀ {is : List Instr} {Q : State → Prop},
      (∀ t', Mupd t t' (t.mem.writeW (b + BitVec.ofNat 64 d) ((t.gpr .r7).setWidth 32)) →
        WP isa (.block is) t' Q) → WP isa (.block (.store .w .r7 .r3 d :: is)) t Q :=
    fun t ht d hd _ _ k => wp_sw (by decide) (by omega_arith) (by rw [ht.r3]) (ht.inW hd) k
  -- The eight stores of zero.
  obtain hz : ∀ t : State, Rest [] s8 t → t.gpr .r7 = 0 := fun t ht => by
    rw [ht.gpr _ (by decide), u8.gpr]; rfl
  refine st _ hc8 _ (by omega_arith) fun t1 v1 => ?_
  refine st _ (hc8.of_rest (v1.rest []) (by decide)) _ (by omega_arith) fun t2 v2 => ?_
  obtain r2 : Rest [] s8 t2 := (v1.rest []).trans (v2.rest [])
  refine st _ (hc8.of_rest r2 (by decide)) _ (by omega_arith) fun t3 v3 => ?_
  obtain r3 : Rest [] s8 t3 := r2.trans (v3.rest [])
  refine st _ (hc8.of_rest r3 (by decide)) _ (by omega_arith) fun t4 v4 => ?_
  obtain r4 : Rest [] s8 t4 := r3.trans (v4.rest [])
  refine st _ (hc8.of_rest r4 (by decide)) _ (by omega_arith) fun t5 v5 => ?_
  obtain r5 : Rest [] s8 t5 := r4.trans (v5.rest [])
  refine st _ (hc8.of_rest r5 (by decide)) _ (by omega_arith) fun t6 v6 => ?_
  obtain r6 : Rest [] s8 t6 := r5.trans (v6.rest [])
  refine st _ (hc8.of_rest r6 (by decide)) _ (by omega_arith) fun t7 v7 => ?_
  obtain r7 : Rest [] s8 t7 := r6.trans (v7.rest [])
  refine st _ (hc8.of_rest r7 (by decide)) _ (by omega_arith) fun t8 v8 => ?_
  obtain r8 : Rest [] s8 t8 := r7.trans (v8.rest [])
  refine wp_addi (by decide) (by decide) fun t9 w9 => wp_li (by decide) fun t10 w10 => WP.block_nil ?_
  obtain hm : t10.mem = ((((((((s8.mem.writeW (b + BitVec.ofNat 64 (ACC + 4 * 0)) (0 : BitVec 32)).writeW
      (b + BitVec.ofNat 64 (ACC + 4 * 1)) (0 : BitVec 32)).writeW (b + BitVec.ofNat 64 (ACC + 4 * 2)) (0 : BitVec 32)).writeW
      (b + BitVec.ofNat 64 (ACC + 4 * 3)) (0 : BitVec 32)).writeW (b + BitVec.ofNat 64 (ACC + 4 * 4)) (0 : BitVec 32)).writeW
      (b + BitVec.ofNat 64 (ACC + 4 * 5)) (0 : BitVec 32)).writeW (b + BitVec.ofNat 64 (ACC + 4 * 6)) (0 : BitVec 32)).writeW
      (b + BitVec.ofNat 64 (ACC + 4 * 7)) (0 : BitVec 32)) := by
    obtain z : ∀ t : State, Rest [] s8 t → (t.gpr .r7).setWidth 32 = 0 := fun t ht => by rw [hz t ht]; rfl
    rw [w10.mem, w9.mem, v8.mem, z _ r7, v7.mem, z _ r6, v6.mem, z _ r5, v5.mem, z _ r4, v4.mem, z _ r3,
      v3.mem, z _ r2, v2.mem, z _ (v1.rest []), v1.mem, z _ (Rest.refl _ _)]
  obtain hr10 : Rest mulFnClob s t10 := hr8.trans ((r8.mono (by decide)).trans ((w9.rest (by decide)).trans
    (w10.rest (by decide))))
  obtain e3 : s3.gpr .r3 = b := by rw [u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide), hc.r3]
  obtain eo : (s3.gpr .r4) = BitVec.ofNat 64 o := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, h4]
  obtain ex : (s3.gpr .r5) = BitVec.ofNat 64 x := by
    rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), h5]
  obtain ey : (s3.gpr .r6) = BitVec.ofNat 64 y := by rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide), h6]
  obtain g8 : ∀ r, r ∉ ([.r9, .r11] : List Reg) → t10.gpr r = s8.gpr r := fun r hr => by
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
    obtain c : ∀ k < 8, (⟨b + BitVec.ofNat 64 ACC, 32⟩ : Region).Contains (b + BitVec.ofNat 64 (ACC + 4 * k)) (32 / 8) :=
      fun k hk => Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)
    rw [hm, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    exact (((((((((Frame.refl _ _).writeW m1 _ (c 0 (by decide))).writeW m1 _ (c 1 (by decide))).writeW m1 _
      (c 2 (by decide))).writeW m1 _ (c 3 (by decide))).writeW m1 _ (c 4 (by decide))).writeW m1 _
      (c 5 (by decide))).writeW m1 _ (c 6 (by decide))).writeW m1 _ (c 7 (by decide)))
  · rw [accw, hm]
    obtain hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega_arith
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
  obtain hframe0 : ∀ z : Nat, z + 32 ≤ 768 → ∀ k < 8,
      limb s.mem b z k = limb s0.mem b z k := fun z hz k hk =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [mulRow, List.cons_append, List.nil_append]
  refine wp_lw (a := b + BitVec.ofNat 64 (x + 4 * i)) (by decide) (by decide)
    (by rw [h.r10]; simp) (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  obtain hr2 : Rest [.r4, .r8] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx3 b s2 := h.ctx.of_rest hr2 (by decide)
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain e1 : (s2.gpr .r4).toNat = limb s0.mem b x i := by
    rw [u2.other _ (by decide), u1.gpr, toNat_ext32, ← hframe0 x hx i hi]; rfl
  obtain e9 : s2.gpr .r9 = b + BitVec.ofNat 64 (4 * i) := by rw [hr2.gpr _ (by decide), h.r9]
  obtain e6 : s2.gpr .r6 = b + BitVec.ofNat 64 y := by rw [hr2.gpr _ (by decide), h.r6]
  obtain hlt : ∀ j < 8, rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i j + 2 ^ 32 ≤ 2 ^ 64 :=
    fun j _ => rowC_le (limb_lt _ _ _ _) (limb_lt _ _ _ _) (wd_lt _ _ _)
  refine WP.append (pass_ok (rb := .r9) (o := ACC) (s0 := s2)
    (c := rowC (accw ACC s.mem b) (limb s0.mem b x) (limb s0.mem b y) i)
    (cin := 0) (by decide) (by decide) (by omega_arith)
    (fun k hk => by rw [e9, Offset.add_add]; exact hc2.inW (by omega_arith))
    (by rw [u2.gpr]; rfl) hlt (by decide) ?_) fun s3 hp => ?_
  · -- The sums of the row.
    intro k hk s' hp'
    obtain hc' : Ctx3 b s' := hc2.of_rest hp'.rest (by decide)
    obtain hf' : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 4 * k⟩] s2.mem s'.mem := by
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
      obtain ea : (t1.gpr .r4).toNat = limb s0.mem b x i := by
        rw [v1.other _ (by decide), hp'.rest.gpr _ (by decide), e1]
      obtain e2 : (t2.gpr .r5).toNat = limb s0.mem b x i * limb s0.mem b y k := by
        rw [v2.gpr, toNat_mul_lt (by rw [ea, ey]; exact mul32_lt (limb_lt _ _ _ _) (limb_lt _ _ _ _)), ea, ey]
      obtain e3 : (t3.gpr .r7).toNat = accw ACC s.mem b (i + k) := by
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
    obtain hc3 : Ctx3 b s3 := hc2.of_rest hp.rest (by decide)
    obtain e9' : s3.gpr .r9 = b + BitVec.ofNat 64 (4 * i) := by rw [hp.rest.gpr _ (by decide), e9]
    refine wp_sw (a := b + BitVec.ofNat 64 (4 * i + (ACC + 32))) (by decide) (by omega_arith)
      (by rw [e9', Offset.add_add]) (hc3.inW (by omega_arith)) fun s4 u4 => ?_
    refine wp_addi (by decide) (by decide) fun s5 u5 => wp_addi (by decide) (by decide) fun s6 u6 =>
      wp_subi (by decide) (by decide) fun s7 u7 => ?_
    refine WP.block_nil ?_
    obtain hr7 : Rest [.r4, .r5, .r7, .r8, .r9, .r10, .r11] s s7 :=
      (hr2.mono (by decide)).trans ((hp.rest.mono (by decide)).trans ((u4.rest _).trans
        ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide))))))
    obtain hm7 : s7.mem = s3.mem.writeW (b + BitVec.ofNat 64 (4 * i + (ACC + 32))) ((s3.gpr .r8).setWidth 32) := by
      rw [u7.mem, u6.mem, u5.mem, u4.mem]
    obtain hpf : Frame [⟨b + BitVec.ofNat 64 (4 * i + ACC), 32⟩] s.mem s3.mem := by
      have := hp.frame; rw [e9, Offset.add_add] at this; rw [← hm2]; exact this
    obtain hr11 : s7.gpr .r11 = BitVec.ofNat 64 (8 - (i + 1)) := by
      rw [u7.gpr, u6.other _ (by decide), u5.other _ (by decide), u4.gpr, hp.rest.gpr _ (by decide),
        hr2.gpr _ (by decide), h.r11, ofNat_sub_one (by omega_arith) (by omega_arith)]
      congr 1
    obtain hch := chain_lt (cin := 0) hlt (by decide) 8 (Nat.le_refl _)
    obtain hacc : ∀ k < i + 9, accw ACC s7.mem b k =
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
  obtain hl16 : ∀ k < 16, accw ACC s.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
  obtain hlo := val32_lt (f := accw ACC s.mem b) (n := 8) fun k hk => hl16 k (by omega_arith)
  obtain hhi := val32_lt (f := fun k => accw ACC s.mem b (8 + k)) (n := 8) fun k hk => hl16 (8 + k) (by omega_arith)
  rw [show 32 * 8 = 256 from rfl] at hlo hhi
  obtain hv : val32 (foldC (accw ACC s.mem b)) 8 < 39 * 2 ^ 256 := by rw [val32_foldC]; omega_arith
  obtain hrb : ∀ t : State, Rest [.r5, .r7, .r8] s t → t.gpr .r12 = b + BitVec.ofNat 64 o := fun t ht => by
    rw [ht.gpr _ (by decide), h12]
  obtain hw : ∀ t : State, Rest [.r5, .r7, .r8] s t → ∀ k < 8,
      InRegions t.wr (t.gpr .r12 + BitVec.ofNat 64 (0 + 4 * k)) 4 := fun t ht k hk => by
    rw [hrb t ht, Offset.add_add]; exact (hc.of_rest ht (by decide)).inW (by omega_arith)
  simp only [mulFinal, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_li (by decide) fun s1 u1 => ?_
  obtain hr1 : Rest [.r5, .r7, .r8] s s1 := u1.rest (by decide)
  obtain hc1 : Ctx3 b s1 := hc.of_rest hr1 (by decide)
  refine WP.append (pass_ok (rb := .r12) (o := 0) (s0 := s1) (c := foldC (accw ACC s.mem b)) (cin := 0)
    (by decide) (by decide) (by decide) (hw s1 hr1) (by rw [u1.gpr]; rfl) (foldC_le hl16) (by decide) ?_)
    fun s2 hp => ?_
  · intro k hk s' hp'
    obtain hc' : Ctx3 b s' := hc1.of_rest hp'.rest (by decide)
    obtain hfr : ∀ d, d + 4 ≤ 4096 → (d + 4 ≤ o ∨ o + 32 ≤ d) → wd s'.mem b d = wd s.mem b d := fun d hd hd' => by
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
      obtain eh : (t2.gpr .r5).toNat = accw ACC s.mem b (8 + k) := by
        rw [v2.gpr, toNat_ext32, v1.mem]; show wd s'.mem _ _ = _
        rw [hfr _ (by omega_arith) (by omega_arith), accw]
        congr 1; omega_arith
      obtain e0 : t2.gpr .r0 = 38 := by
        rw [v2.other _ (by decide), v1.other _ (by decide), hp'.rest.gpr _ (by decide), hr1.gpr _ (by decide), h0]
      obtain hh := hl16 (8 + k) (by omega_arith)
      obtain hl := hl16 k (by omega_arith)
      obtain e3 : (t3.gpr .r5).toNat = accw ACC s.mem b (8 + k) * 38 := by
        rw [v3.gpr, e0, toNat_mul_lt (by rw [eh, t38]; omega_arith), eh, t38]
      rw [v4.gpr, v3.other .r7 (by decide), v2.other .r7 (by decide),
        toNat_add_lt (by rw [el, e3]; omega_arith), el, e3, foldC, Nat.mul_comm 38]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
        (v4.rest (by decide))))
  -- The fold done; the carry out, folded in as 38 times itself.
  obtain hr2 : Rest [.r5, .r7, .r8] s s2 := hr1.trans hp.rest
  obtain hc2 : Ctx3 b s2 := hc.of_rest hr2 (by decide)
  obtain hpo : ∀ j < 8, wd s2.mem b (o + 4 * j) = out (foldC (accw ACC s.mem b)) 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hrb s1 hr1, wd_shift, Nat.zero_add] at this
  obtain hpf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s.mem s2.mem := by
    have := hp.frame; rw [hrb s1 hr1, Offset.add_add, Nat.add_zero] at this; rw [← u1.mem]; exact this
  obtain hcl := carry_le hv
  refine wp_mul fun s3 u3 => ?_
  obtain e3 : (s3.gpr .r8).toNat = 38 * chain (foldC (accw ACC s.mem b)) 0 8 := by
    rw [u3.gpr, hr2.gpr .r0 (by decide), h0, toNat_mul_lt (by rw [hp.r8, t38]; omega_arith), hp.r8, t38]
    omega_arith
  obtain hr3 : Rest [.r5, .r7, .r8] s s3 := hr2.trans (u3.rest (by decide))
  obtain hl : ∀ k < 8, limb s2.mem b o k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ht := tail_facts hl (c8 := chain (foldC (accw ACC s.mem b)) 0 8) hcl
  refine WP.append (pass_ok (rb := .r12) (o := 0) (s0 := s3) (c := limb s2.mem b o)
    (cin := 38 * chain (foldC (accw ACC s.mem b)) 0 8)
    (by decide) (by decide) (by decide) (hw s3 hr3) e3 (fun k hk => by have := hl k hk; omega_arith) (by omega_arith) ?_)
    fun s4 hp4 => ?_
  · intro k hk s' hp'
    obtain hc' : Ctx3 b s' := (hc.of_rest hr3 (by decide)).of_rest hp'.rest (by decide)
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
  obtain hr4 : Rest [.r5, .r7, .r8] s s4 := hr3.trans hp4.rest
  obtain hc4 : Ctx3 b s4 := hc.of_rest hr4 (by decide)
  obtain hpo4 : ∀ j < 8, wd s4.mem b (o + 4 * j) = out (limb s2.mem b o) (38 * chain (foldC (accw ACC s.mem b)) 0 8) j :=
    fun j hj => by have := hp4.outs j hj; rwa [hrb s3 hr3, wd_shift, Nat.zero_add] at this
  obtain hpf4 : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] s3.mem s4.mem := by
    have := hp4.frame; rwa [hrb s3 hr3, Offset.add_add, Nat.add_zero] at this
  refine wp_mul fun s5 u5 => ?_
  obtain e5 : (s5.gpr .r8).toNat = 38 * chain (limb s2.mem b o) (38 * chain (foldC (accw ACC s.mem b)) 0 8) 8 := by
    rw [u5.gpr, hr4.gpr .r0 (by decide), h0, toNat_mul_lt (by rw [hp4.r8, t38]; have := ht.1; omega_arith), hp4.r8, t38]
    omega_arith
  obtain hr5 : Rest [.r5, .r7, .r8] s s5 := hr4.trans (u5.rest (by decide))
  refine wp_lw (a := b + BitVec.ofNat 64 o) (by decide) (by decide)
    (by rw [hrb s5 hr5]; simp) ((hc.of_rest hr5 (by decide)).inR (by omega_arith)) fun s6 u6 => ?_
  refine wp_add fun s7 u7 => ?_
  obtain hr7 : Rest [.r5, .r7, .r8] s s7 := hr5.trans ((u6.rest (by decide)).trans (u7.rest (by decide)))
  refine wp_sw (a := b + BitVec.ofNat 64 o) (by decide) (by decide)
    (by rw [hrb s7 hr7]; simp) ((hc.of_rest hr7 (by decide)).inW (by omega_arith)) fun s8 u8 => WP.block_nil ?_
  obtain h0' := ht.2.1 0 (by decide)
  obtain o0 := hpo4 0 (by decide)
  rw [Nat.mul_zero, Nat.add_zero] at o0
  obtain e7 : (s7.gpr .r7).toNat = tailL (limb s2.mem b o) (chain (foldC (accw ACC s.mem b)) 0 8) 0 := by
    rw [u7.gpr, u6.gpr, u6.other .r8 (by decide), u5.mem]
    simp only [tailL, ite_true] at h0' ⊢
    unfold wd at o0
    rw [toNat_add_lt (by rw [toNat_ext32, e5, o0]; omega_arith), toNat_ext32, e5, o0]
  obtain hm8 : s8.mem = s4.mem.writeW (b + BitVec.ofNat 64 o) ((s7.gpr .r7).setWidth 32) := by
    rw [u8.mem, u7.mem, u6.mem, u5.mem]
  obtain hlimb : ∀ k < 8, limb s8.mem b o k = tailL (limb s2.mem b o) (chain (foldC (accw ACC s.mem b)) 0 8) k := by
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
    obtain hcv := chain_val (foldC (accw ACC s.mem b)) 0 8
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
  obtain r0 : RowInvF b o x y s 0 s1 := by
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

end

end

/-! ### `Ed25519.PPC64LE.Power`, which this module and modules that import it used -/

section

/-! ### `Ed25519.PPC64LE.FieldProg`, which this module and modules that import it used -/

section

/-!
# Ed25519 on PPC64LE: field programs

The slots as residues (`env`), what an operation does to them (`evalOp`),
and the code of a list of operations doing that (`fieldCode_ok`), keeping
every register but `fclob` and every byte outside the field area `FA`
(`Keep`). A call of `vg_gf25519_r32_mul` (`mulCall_ok`) is the inlined
product's equal. The extended Edwards addition of the slots is
`Spec.Ed25519.pointAdd` (`pointAdd_eval`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)

abbrev Env := Slot → Spec.X25519.Fe

/-- The slots' elements. -/
def env (m : Mem) (b : Addr) : Env := fun i => FS m b (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b | .mulc o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

/-- The registers field code writes: X25519's, and those of a call of the product. -/
abbrev fclob : List Reg := [.r0, .r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12]

structure Keep (b : Addr) (s s' : State) : Prop where
  rest : Rest fclob s s'
  frame : Frame [FA b] s.mem s'.mem

theorem Keep.refl (b : Addr) (s : State) : Keep b s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Keep.trans {b : Addr} {s t u : State} (h : Keep b s t) (k : Keep b t u) : Keep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem Keep.ctx {b : Addr} {s t : State} (h : Keep b s t) (hs : Ctx b s) : Ctx b t :=
  hs.of_rest h.rest (by decide)

/-- An operation's frame: the result's slot and the product's limbs. -/
abbrev opFrame (b : Addr) (o : Nat) : List Region :=
  [⟨b + BitVec.ofNat 64 o, 32⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩]

theorem slot_frame {b : Addr} {m m' : Mem} {o i : Slot} (hne : i ≠ o)
    (hf : Frame (opFrame b (offset o)) m m') : FS m' b (offset i) = FS m b (offset i) := by
  have hi := slot_range i
  have ho := slot_range o
  have hA := ACC_eq
  have hsep : offset i + 32 ≤ offset o ∨ offset o + 32 ≤ offset i := by
    have hv : i.val ≠ o.val := fun e => hne (Fin.ext e)
    simp only [offset]
    omega_arith
  refine congrArg Proof.X25519.toFe (val32_congr (limb_frame hf fun r hr k hk => ?_))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)

theorem field_update {b : Addr} {m m' : Mem} (o : Slot) (hf : Frame (opFrame b (offset o)) m m') :
    env m' b = Function.update (env m b) o (FS m' b (offset o)) := by
  funext i
  by_cases hi : i = o
  · subst hi; simp only [Function.update_self, env]
  · rw [Function.update_of_ne hi]
    exact slot_frame hi hf

theorem frame_FA {b : Addr} {o : Slot} {m m' : Mem} (hf : Frame (opFrame b (offset o)) m m') :
    Frame [FA b] m m' := by
  have ho := slot_range o
  have hA := ACC_eq
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem frame_o {b : Addr} {o : Nat} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 o, 32⟩] m m') :
    Frame (opFrame b o) m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem field_finish {b : Addr} {s t : State} (o : Slot) (hr : Rest fclob s t)
    (hf : Frame (opFrame b (offset o)) s.mem t.mem) {v : Spec.X25519.Fe}
    (hv : FS t.mem b (offset o) = v) :
    Keep b s t ∧ env t.mem b = Function.update (env s.mem b) o v := by
  rw [← hv]
  exact ⟨⟨hr, frame_FA hf⟩, field_update o hf⟩

/-! ## A call of the product -/

/-- What a call of `vg_gf25519_r32_mul` asks of the function: the working space's first 4096
bytes, and the offsets of `o`, `a` and `c` in `r4`–`r6`. -/
def mulK (b : Addr) (o a c : Slot) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨b, 4096⟩] ∧ Ctx3 b t ∧ (t.gpr .r4).toNat % 2 ^ 32 = offset o ∧
    (t.gpr .r5).toNat % 2 ^ 32 = offset a ∧ (t.gpr .r6).toNat % 2 ^ 32 = offset c
  post t t' := Rest mulFnClob t t' ∧ Frame [FA b] t.mem t'.mem ∧
    env t'.mem b = Function.update (env t.mem b) o (env t.mem b a * env t.mem b c)
  pub _ _ := True

/-- `mulFn` keeps the ABI's registers and the link register. -/
theorem mulFn_abi {s s' : State} {t : List Leak} (he : VG.Exec isa mulFn s t s')
    (hr : Rest mulFnClob s s') : abiPreserved s s' :=
  ⟨fun r hr' => hr.gpr r (by revert hr'; cases r <;> decide), hr.sp,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩

theorem mulK_ok {b : Addr} (o a c : Slot) :
    ∀ t, (mulK b o a c).pre t → ∃ tr t', VG.Exec isa mulFn t tr t' ∧ abiPreserved t t' ∧
      (mulK b o a c).post t t' := fun t ⟨_, _, ht, t4, t5, t6⟩ => by
  obtain ⟨tr, t', he, hR, hF, hV⟩ := mulFn_ok (slot_range o).2 (slot_range a).2 (slot_range c).2 ht t4 t5 t6
  refine ⟨tr, t', he, mulFn_abi he hR, hR, frame_FA hF, ?_⟩
  exact (field_update o hF).trans (congrArg _ (Proof.X25519.toFe_mul hV))

theorem offset_word (o : Slot) : (BitVec.ofNat 64 (offset o)).toNat % 2 ^ 32 = offset o := by
  have := slot_range o
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- **A call of `vg_gf25519_r32_mul`**, as the inlined product. -/
theorem mulCall_ok {b : Addr} {s : State} (hc : Ctx b s) (o a c : Slot) :
    WP isa (mulCall (offset o) (offset a) (offset c)) s fun t => Keep b s t ∧
      env t.mem b = Function.update (env s.mem b) o (env s.mem b a * env s.mem b c) := by
  have ho := slot_range o
  have ha := slot_range a
  have hc' := slot_range c
  obtain ⟨n, hn, hw⟩ := hc.wr
  unfold mulCall
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => wp_li (by omega_arith) fun s2 u2 =>
    wp_li (by omega_arith) fun s3 u3 => wp_li (by omega_arith) fun s4 u4 => WP.block_nil ?_)
  have hr4 : Rest [.r3, .r4, .r5, .r6] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  have hm4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  have e3 : s4.gpr .r3 = b := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr, hc.r6]
    simp
  have e4 : s4.gpr .r4 = BitVec.ofNat 64 (offset o) := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
  have e5 : s4.gpr .r5 = BitVec.ofNat 64 (offset a) := by rw [u4.other _ (by decide), u3.gpr]
  have e6 : s4.gpr .r6 = BitVec.ofNat 64 (offset c) := u4.gpr
  have g : ∀ q, q ∉ linkRegs → (s4.callEntry.withRegions [] [⟨b, 4096⟩]).gpr q = s4.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hsub : ∀ r ∈ ([⟨b, 4096⟩] : List Region), ∃ r' ∈ s4.wr, ∃ off,
      r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := fun r hr => by
    rw [List.mem_singleton.mp hr, hr4.wr]
    exact ⟨_, hw, 0, by simp, by simp only; omega_arith⟩
  refine WP.seq (WP.call (k := mulK b o a c) (mulK_ok o a c) (rd := []) (wr := [⟨b, 4096⟩])
    ⟨rfl, rfl, ⟨by rw [g _ (by decide)]; exact e3, 4096, Nat.le_refl _, List.mem_singleton_self _⟩,
      by rw [g _ (by decide), e4]; exact offset_word o, by rw [g _ (by decide), e5]; exact offset_word a,
      by rw [g _ (by decide), e6]; exact offset_word c⟩
    (Covers.of_sub fun r hr => by
      obtain ⟨r', hr', h'⟩ := hsub r (by simpa using hr)
      exact ⟨r', List.mem_append_right _ hr', h'⟩)
    (Covers.of_sub hsub) ?_ (by decide +kernel))
  intro t hrd hwr hsp _ _ _ ⟨hR, hF, hV⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at hF hV
  rw [hm4] at hF hV
  have hg : ∀ q, q ∉ mulFnClob → t.gpr q = s4.gpr q := fun q hq => by
    have := hR.gpr q hq
    simp only [State.withRegions_gpr] at this
    rw [this, State.callEntry_gpr _ (by revert hq; cases q <;> decide)]
  refine wp_addi (by decide) (by decide) fun t1 v1 => WP.block_nil ⟨⟨⟨fun q hq => ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · by_cases h6 : q = .r6
    · subst h6
      rw [v1.gpr, hg _ (by decide), e3, hc.r6]; simp
    · rw [v1.other _ h6, hg _ (by revert hq h6; cases q <;> decide), hr4.gpr _ (by revert hq h6; cases q <;> decide)]
  · rw [v1.rd, hrd, hr4.rd]
  · rw [v1.wr, hwr, hr4.wr]
  · rw [v1.sp, hsp, hr4.sp]
  · rw [v1.mem]; exact hF
  · rw [v1.mem]; exact hV

/-! ## Operations and programs -/

theorem fieldOp_ok {b : Addr} {s : State} (hc : Ctx b s) (op : FieldOp) :
    WP isa op.code s fun t => Keep b s t ∧ env t.mem b = evalOp op (env s.mem b) := by
  have hA := ACC_eq
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) hv
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) hv
  | mul o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (mul_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hc) fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) hf (Proof.X25519.toFe_mul hv)
  | mulc o a c => exact mulCall_ok hc o a c
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (add_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) hc)
      fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) (Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (sub_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) hc)
      fun t ⟨hr, hf, hv⟩ => ?_
    exact field_finish o (hr.mono (by decide)) (frame_o hf) (Proof.X25519.toFe_sub hv)

theorem fieldCode_ok (ops : List FieldOp) {s : State} {b : Addr} (hc : Ctx b s) :
    WP isa (fieldCode ops) s fun t => Keep b s t ∧ env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, rfl⟩
  | cons op ops ih =>
    refine WP.seq (WP.mono (fieldOp_ok hc op) fun t ⟨ht, et⟩ => ?_)
    refine WP.mono (ih (ht.ctx hc)) fun u ⟨hu, eu⟩ => ?_
    exact ⟨ht.trans hu, by rw [eu, et]; rfl⟩

/-! ## Inline programs, framed by the slots they write -/

/-- The slot an operation writes. -/
def opOut : FieldOp → Slot
  | .copy o _ | .const o _ | .mul o _ _ | .mulc o _ _ | .add o _ _ | .sub o _ _ => o

/-- An inline operation changes no register but X25519's `clob`, and no memory but its result
and the product's limbs. -/
theorem fieldOpW_ok {b : Addr} {s : State} (hc : Ctx b s) (op : FieldOp) (hi : op.inline = true) :
    WP isa op.code s fun t => Rest clob s t ∧ Frame (opFrame b (offset (opOut op))) s.mem t.mem ∧
      env t.mem b = evalOp op (env s.mem b) := by
  have hA := ACC_eq
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a) fun t ⟨hr, hf, hv⟩ => ⟨hr.mono (by decide), frame_o hf, ?_⟩
    rw [field_update o (frame_o hf), hv]; rfl
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, hv⟩ => ⟨hr.mono (by decide), frame_o hf, ?_⟩
    rw [field_update o (frame_o hf), hv]; rfl
  | mul o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (mul_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hc) fun t ⟨hr, hf, hv⟩ =>
      ⟨hr, hf, ?_⟩
    rw [field_update o hf]; exact congrArg _ (Proof.X25519.toFe_mul hv)
  | mulc => simp [FieldOp.inline] at hi
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (add_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) hc)
      fun t ⟨hr, hf, hv⟩ => ⟨hr, frame_o hf, ?_⟩
    rw [field_update o (frame_o hf)]; exact congrArg _ (Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    have := slot_al o; have := slot_al a; have := slot_al c
    refine WP.mono (sub_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith) hc)
      fun t ⟨hr, hf, hv⟩ => ⟨hr, frame_o hf, ?_⟩
    rw [field_update o (frame_o hf)]; exact congrArg _ (Proof.X25519.toFe_sub hv)

/-- Inline field code, framed by any regions `R` that hold the results and the product's limbs. -/
theorem fieldCodeW_ok (ops : List FieldOp) (hi : ops.all FieldOp.inline = true) {b : Addr}
    (R : List Region) (hR : ∀ op ∈ ops, ∀ r ∈ opFrame b (offset (opOut op)), ∃ r' ∈ R, r.Sub r')
    {s : State} (hc : Ctx b s) :
    WP isa (fieldCode ops) s fun t =>
      Rest clob s t ∧ Frame R s.mem t.mem ∧ env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, rfl⟩
  | cons op ops ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hi
    refine WP.seq (WP.mono (fieldOpW_ok hc op hi.1) fun t ⟨rt, ft, et⟩ => ?_)
    refine WP.mono (ih hi.2 (fun op' h' => hR op' (List.mem_cons_of_mem _ h')) (hc.of_rest rt (by decide)))
      fun u ⟨ru, fu, eu⟩ => ⟨rt.trans ru, (ft.sub (hR op List.mem_cons_self)).trans fu, by rw [eu, et]; rfl⟩

/-! ## The addition formula -/

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

/-- The sum of the points at slots 0–3 and 4–7, as the formula computes it. -/
def addResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * (e 5 - e 4)
  let b := (e 1 + e 0) * (e 5 + e 4)
  let c := (e 3 * e 16 + e 3 * e 16) * e 7
  let dd := (e 2 + e 2) * e 6
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : Env) : point (evalOps pointAddOps e) 0 1 2 3 = addResult e := rfl

theorem pointAdd_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 4 5 6 7) := by
  rw [pointAdd_formula]
  simp only [addResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: the addition chain to `z^(2^250 - 1)` and `z^11`

`chain250` with inlined products (`PSpec`): it changes no register but the
counter `r12` and X25519's `clob`, and no memory but bytes 512 to 1023 of the
working space (`PR`: slots 14 to 17 and the product's limbs), and maps the
slots by `power250Env`, whose slots 15 and 14 are `chainF`'s results.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.X25519 (sqn)

def opMul (o a b : Slot) (e : Env) : Env := Function.update e o (e a * e b)

def opSqn (o a : Slot) (n : Nat) (e : Env) : Env := Function.update e o (sqn (e a) n)

theorem opMul_update (o : Slot) (e : Env) (v : Spec.X25519.Fe) :
    opMul o o o (Function.update e o v) = Function.update e o (v * v) := by
  simp only [opMul, Function.update_self, Function.update_idem]

/-- What the chain writes: bytes 512 to 1023 of the working space. -/
abbrev PR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 512, 512⟩

/-- `c` maps the slots by `f`, changing no register but `r12` and `clob`
and no memory but `PR`. -/
def PSpec (b : Addr) (c : Prog isa) (f : Env → Env) : Prop :=
  ∀ s, Ctx b s → WP isa c s fun t =>
    Rest (.r12 :: clob) s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = f (env s.mem b)

theorem PSpec.seq {b : Addr} {c₁ c₂ : Prog isa} {f g : Env → Env}
    (h₁ : PSpec b c₁ f) (h₂ : PSpec b c₂ g) : PSpec b (.seq c₁ c₂) fun e => g (f e) :=
  fun s hc => WP.seq (WP.mono (h₁ s hc) fun _ ⟨r₁, f₁, e₁⟩ =>
    WP.mono (h₂ _ (hc.of_rest r₁ (by decide))) fun _ ⟨r₂, f₂, e₂⟩ =>
      ⟨r₁.trans r₂, f₁.trans f₂, by rw [e₂, e₁]⟩)

theorem frame_PR {b : Addr} {o : Slot} (ho : 14 ≤ o.val) {m m' : Mem}
    (hf : Frame (opFrame b (offset o)) m m') : Frame [PR b] m m' := by
  have hs := slot_range o
  have hA := ACC_eq
  have ho' : 512 ≤ offset o := by simp only [offset]; omega_arith
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · exact Offset.sub _ (by omega_arith) (by omega_arith)

theorem mulP_ok {b : Addr} {s : State} (hc : Ctx b s) (o x y : Slot) (ho : 14 ≤ o.val) :
    WP isa (mulP o x y) s fun t =>
      Rest clob s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = opMul o x y (env s.mem b) := by
  have hA := ACC_eq
  have h1 := slot_range o
  have h2 := slot_range x
  have h3 := slot_range y
  have := slot_al o; have := slot_al x; have := slot_al y
  refine WP.mono (mul_ok (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) hc) fun t ⟨hr, hf, hv⟩ =>
    ⟨hr, frame_PR ho hf, ?_⟩
  rw [field_update o hf]
  exact congrArg _ (Proof.X25519.toFe_mul hv)

theorem mulPS (b : Addr) (o x y : Slot) (ho : 14 ≤ o.val) : PSpec b (mulP o x y) (opMul o x y) :=
  fun _ hc => WP.mono (mulP_ok hc o x y ho) fun _ ⟨r, f, e⟩ => ⟨r.mono (by decide), f, e⟩

theorem sqLoop_ok {s₀ : State} {b : Addr} (hc : Ctx b s₀) (o : Slot) (ho : 14 ≤ o.val)
    (x : Spec.X25519.Fe) (n : Nat) (hn : n < 2 ^ 15) :
    ∀ m s, 1 ≤ m → m ≤ n → Rest (.r12 :: clob) s₀ s → Frame [PR b] s₀.mem s.mem →
      s.gpr .r12 = BitVec.ofNat 64 m →
      env s.mem b = Function.update (env s₀.mem b) o (sqn x (n - m)) →
      WP isa (.loop (.seq (mulP o o o) (.block [.subi .r12 .r12 1])) (.nonzero .d .r12)) s fun t =>
        Rest (.r12 :: clob) s₀ t ∧ Frame [PR b] s₀.mem t.mem ∧
        env t.mem b = Function.update (env s₀.mem b) o (sqn x n) := by
  intro m s h1 h2 hr hf hb he
  refine WP.loop (M := isa) (fun m (s : State) =>
    1 ≤ m ∧ m ≤ n ∧ Rest (.r12 :: clob) s₀ s ∧ Frame [PR b] s₀.mem s.mem ∧
    s.gpr .r12 = BitVec.ofNat 64 m ∧
    env s.mem b = Function.update (env s₀.mem b) o (sqn x (n - m))) ?_
    m s ⟨h1, h2, hr, hf, hb, he⟩
  intro m s ⟨h1, h2, hr, hf, hb, he⟩
  have hcs : Ctx b s := hc.of_rest hr (by decide)
  refine WP.seq (WP.mono (mulP_ok hcs o o o ho) fun s1 ⟨r1, f1, e1⟩ => ?_)
  refine wp_subi (by decide) (by decide) fun s2 u2 => WP.block_nil ?_
  have b2 : s2.gpr .r12 = BitVec.ofNat 64 (m - 1) := by
    rw [u2.gpr, r1.gpr _ (by decide), hb, ofNat_sub_one h1 (by omega_arith)]
  have k2 : Rest (.r12 :: clob) s₀ s2 := hr.trans ((r1.mono (by decide)).trans (u2.rest (by decide)))
  have f2 : Frame [PR b] s₀.mem s2.mem := by rw [u2.mem]; exact hf.trans f1
  have e2 : env s2.mem b = Function.update (env s₀.mem b) o (sqn x (n - (m - 1))) := by
    rw [u2.mem, e1, he, opMul_update]
    apply congrArg (Function.update (env s₀.mem b) o)
    rw [show n - (m - 1) = (n - m) + 1 by omega_arith]
    rfl
  have hz : (s2.gpr .r12 != 0) = decide (m - 1 ≠ 0) := by rw [b2, ofNat_ne_zero (by omega_arith)]
  rw [eval_nonzero, hz]
  by_cases hm : m - 1 = 0
  · exact .inl ⟨by simp [hm], k2, f2, by rw [e2, hm, Nat.sub_zero]⟩
  · exact .inr ⟨by simp [hm], m - 1, by omega_arith, by omega_arith, by omega_arith, k2, f2, b2, e2⟩

theorem sqnS (b : Addr) (o a : Slot) (n : Nat) (ho : 14 ≤ o.val) (hn : 2 ≤ n) (hn' : n < 2 ^ 15) :
    PSpec b (Impl.Ed25519.PPC64LE.sqn o a n) (opSqn o a n) := by
  intro s hc
  refine WP.seq (WP.mono (mulP_ok hc o a a ho) fun s1 ⟨r1, f1, e1⟩ => ?_)
  refine WP.seq (wp_li (by omega_arith) fun s2 u2 => WP.block_nil ?_)
  have k2 : Rest (.r12 :: clob) s s2 := (r1.mono (by decide)).trans (u2.rest (by decide))
  refine sqLoop_ok hc o ho (env s.mem b a) n hn' (n - 1) s2 (by omega_arith) (by omega_arith) k2
    (by rw [u2.mem]; exact f1) u2.gpr ?_
  rw [u2.mem, e1, show n - (n - 1) = 1 by omega_arith]
  rfl

def power250Env (e : Env) : Env :=
  opMul 15 16 15 (opSqn 16 16 50 (opMul 16 17 16 (opSqn 17 16 100
    (opMul 16 16 15 (opSqn 16 15 50 (opMul 15 16 15 (opSqn 16 16 10 (opMul 16 17 16 (opSqn 17 16 20
    (opMul 16 16 15 (opSqn 16 15 10 (opMul 15 16 15 (opSqn 16 15 5 (opMul 15 15 16
    (opMul 16 14 14 (opMul 14 14 15 (opMul 15 2 15 (opMul 15 15 15 (opMul 15 14 14
    (opMul 14 2 2 e))))))))))))))))))))

theorem chain250S (b : Addr) : PSpec b chain250 power250Env :=
  (mulPS b 14 2 2 (by decide)).seq <|
  (mulPS b 15 14 14 (by decide)).seq <|
  (mulPS b 15 15 15 (by decide)).seq <|
  (mulPS b 15 2 15 (by decide)).seq <|
  (mulPS b 14 14 15 (by decide)).seq <|
  (mulPS b 16 14 14 (by decide)).seq <|
  (mulPS b 15 15 16 (by decide)).seq <|
  (sqnS b 16 15 5 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide)).seq <|
  (sqnS b 16 15 10 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 16 15 (by decide)).seq <|
  (sqnS b 17 16 20 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 17 16 (by decide)).seq <|
  (sqnS b 16 16 10 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide)).seq <|
  (sqnS b 16 15 50 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 16 15 (by decide)).seq <|
  (sqnS b 17 16 100 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 16 17 16 (by decide)).seq <|
  (sqnS b 16 16 50 (by decide) (by decide) (by decide)).seq <|
  (mulPS b 15 16 15 (by decide))

theorem power250Env_eval (e : Env) :
    power250Env e 15 = (Proof.X25519.chainF (e 2)).1 ∧ power250Env e 14 = (Proof.X25519.chainF (e 2)).2 := by
  simp only [power250Env, opMul, opSqn, Function.update_apply]
  simp only [↓reduceIte, Fin.isValue, Fin.reduceEq]
  exact ⟨rfl, rfl⟩

/-- `vg_gf25519_r32_pow250`'s code, from the working space in `r3`. -/
theorem pow250Fn_ok {b : Addr} {s : State} (h3 : s.gpr .r3 = b)
    (hw : ∃ n, 4096 ≤ n ∧ (⟨b, n⟩ : Region) ∈ s.wr) :
    WP isa pow250Fn s fun t =>
      Rest (.r6 :: .r12 :: clob) s t ∧ Frame [PR b] s.mem t.mem ∧ env t.mem b = power250Env (env s.mem b) := by
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have hc : Ctx b s1 := ⟨by rw [u1.gpr, h3]; simp, by rw [u1.wr]; exact hw⟩
  refine WP.mono (chain250S b s1 hc) fun t ⟨hr, hf, he⟩ => ⟨?_, by rw [u1.mem] at hf; exact hf, by rw [he, u1.mem]⟩
  exact (u1.rest (by decide)).trans (hr.mono (by decide))

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: the elements as the contracts read them

An element's 32 bytes, little-endian, are its eight words (`read_V`), so the
contracts' `valAt` and `elemAt` are the proofs' `V` and `FS` (`valAt_eq`,
`elemAt_eq`), and their `Keeps` follow from the frames of the code.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)

theorem read_V (m : Mem) (b : Addr) (o : Nat) : (m.read (b + BitVec.ofNat 64 o) 32).toNat = V m b o := by
  have e : ∀ k, b + BitVec.ofNat 64 (o + 4 * k) = b + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k) :=
    fun k => by rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [← Proof.X25519.leNum_bytesAt_read, Proof.X25519.leNum_bytesAt_words32]
  simp only [V, val32, limb, wd, e]
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  simp only [Nat.reduceMul, BitVec.add_zero]

theorem valAt_eq (m : Mem) (b : Addr) (o : BitVec 32) : Proof.X25519.Field32.valAt m b o = V m b o.toNat :=
  read_V m b o.toNat

theorem valAt_ofNat (m : Mem) (b : Addr) (i : Slot) :
    Proof.X25519.Field32.valAt m b (BitVec.ofNat 32 (offset i)) = V m b (offset i) := by
  have := slot_range i
  rw [valAt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [this])]

theorem elemAt_eq (m : Mem) (b : Addr) (i : Slot) :
    Proof.Ed25519.Point32.elemAt m b (offset i) = env m b i :=
  congrArg (Fin.ofNat P) (read_V m b (offset i))

theorem pointAt_eq (m : Mem) (b : Addr) :
    Proof.Ed25519.Point32.pointAt m b Proof.Ed25519.Point32.pAt = point (env m b) 0 1 2 3 := by
  simp only [Proof.Ed25519.Point32.pointAt, point, ← elemAt_eq]; rfl

theorem pointAt_q (m : Mem) (b : Addr) :
    Proof.Ed25519.Point32.pointAt m b Proof.Ed25519.Point32.qAt = point (env m b) 4 5 6 7 := by
  simp only [Proof.Ed25519.Point32.pointAt, point, ← elemAt_eq]; rfl

/-- A byte of the working space outside `[e, e + k)` is in no region of a frame there. -/
theorem byte_out {b : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨b + BitVec.ofNat 64 e, k⟩ : Region).Contains (b + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint b (d := i) (n := 1) (e := e) (k := k) (by omega_using [h]) (by omega_using [hi]) (by omega_using [he]) _ (Region.contains_self _ _) hc

/-- `pow250`'s `Keeps₂`, from its frame. -/
theorem keeps_pow {b : Addr} {m m' : Mem} (hf : Frame [PR b] m m') : Proof.X25519.Field32.Keeps₂ b m m' := by
  intro i hi hown
  simp only [Proof.X25519.Field32.wsBytes, Proof.X25519.Field32.eAt, Proof.X25519.Field32.ownEnd] at hi hown
  exact hf _ fun r hr => by rw [List.mem_singleton.mp hr]; exact byte_out (by omega_using [hi]) (by omega_using []) hown

/-- What the point addition writes: the sum, the temporaries and the product's limbs. -/
abbrev addW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 64, 128⟩, ⟨b + BitVec.ofNat 64 320, 256⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩]

/-- The point addition's `Keeps`, from its frame. -/
theorem keeps_add {b : Addr} {m m' : Mem} (hf : Frame (addW b) m m') : Proof.Ed25519.Point32.Keeps b m m' := by
  intro i hi hp ht ho
  simp only [Proof.Ed25519.Point32.wsBytes, Proof.Ed25519.Point32.pAt, Proof.Ed25519.Point32.elemBytes] at hi hp ht ho
  have hA := ACC_eq
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact byte_out (by omega_using [hi]) (by omega_using []) hp
  · exact byte_out (by omega_using [hi]) (by omega_using []) ht
  · exact byte_out (by omega_using [hi]) (by omega_using [hA]) (by omega_using [ho, hA])

/-- A power, as the contract states it. -/
theorem val_of_env {m m' : Mem} {b : Addr} {i j : Slot} {e : Nat}
    (h : env m' b i = Proof.X25519.pw (env m b j) e) :
    V m' b (offset i) % P = V m b (offset j) ^ e % P := by
  have := congrArg Fin.val h
  simp only [env, FS, Proof.X25519.toFe_val, Proof.X25519.pw, Fin.val_ofNat] at this
  rw [this, ← Nat.pow_mod]

end VG.Proof.Ed25519.PPC64LE
