import VerifiedGarbage.Proof.X448.X86.MulLoop
import VerifiedGarbage.Proof.X448.X86.Reduce
import VerifiedGarbage.Proof.X448.X86.FnCtx

/-!
# X448 on x86 (32-bit): field multiplication

`vg_gf448_r16_mul`'s product (`Impl/X448/X86.lean`, `mulFn`): `esi` points
at `b` and `ebp` at `a`, and the 28 unrolled rows (`mulRowU_ok`, as
`rowWith_ok` with the product's words at constant offsets of `edi`) produce
the 56 limbs of the product, which are folded and normalized modulo the
prime into the element at `o` (`mulTail_ok`).
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- After the product's first `i` rows: as `RowInv`, with `ebp` and `esi`, the
operands' pointers, kept. -/
structure RowInvU (base : Addr) (a b : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  scr : Scr s base
  regs : Keeps [.eax, .ebx, .ecx, .edx] s0 s
  mem : Outside base ACC 224 s0.mem s.mem
  lt : ∀ k < i + 28, accw s.mem base k < radix
  val : valN (accw s.mem base) (i + 28) = valN (limbs s0.mem base a) i * fe s0.mem base b

theorem rowSrcU_ok {s : State} {base : Addr} (hs : Scr s base) {b i j : Nat}
    (hb : Slot b) (hi : i < 28) (hj : j < 28) (hp : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 b)
    (hc : (s.gpr .ecx).toNat < radix) (hy : limbs s.mem base b j < radix)
    (hacc : accw s.mem base (i + j) < radix) :
    WP isa (.block (rowSrcU i j)) s fun t =>
      (t.gpr .eax).toNat = (s.gpr .ecx).toNat * limbs s.mem base b j + accw s.mem base (i + j) ∧
      Keeps [.eax, .edx] s t ∧ t.mem = s.mem := by
  have hb' : b + 112 ≤ 3584 := hb
  unfold rowSrcU
  refine wp_load (hs.ea_ptr hp (by omega)) (hs.read (by omega)) fun t ht => ?_
  refine wp_mul fun u uv um uk => ?_
  have us := (hs.of_upd ht (by decide)).of_keeps uk (by decide)
  have rd : readSrc u (.mem (sc (ACC + 4 * (i + j)))) = some (word u.mem base (ACC + 4 * (i + j))) := by
    simp only [readSrc, us.ea (d := ACC + 4 * (i + j)) (by simp only [ACC]; omega), State.load32,
      us.read (d := ACC + 4 * (i + j)) (n := 4) (by simp only [ACC]; omega), ite_true]
  refine wp_alu (Or.inl rfl) rd fun v hv _ => WP.block_nil ⟨?_, ?_, hv.mem.trans (um.trans ht.mem)⟩
  · rw [hv.gpr]
    change (u.gpr .eax + word u.mem base (ACC + 4 * (i + j))).toNat = _
    rw [uv, ht.gpr, ht.other .ecx (by decide), um, ht.mem, BitVec.toNat_add, BitVec.toNat_ofNat]
    have prod := Nat.mul_le_mul (Nat.le_of_lt_succ hc) (Nat.le_of_lt_succ hy)
    simp only [radix] at hc hy hacc prod
    change ((limbs s.mem base b j * (s.gpr .ecx).toNat) % 2 ^ 32 + accw s.mem base (i + j)) % 2 ^ 32 = _
    rw [Nat.mul_comm (limbs s.mem base b j)]
    omega
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest (by decide)))

/-- Row `i` of the product. -/
theorem mulRowU_ok {base : Addr} {a b : Nat} (ha : Slot a) (hb : Slot b) {s0 s : State}
    (ab : Bounded s0.mem base a) (bb : Bounded s0.mem base b) {i : Nat} (hi : i < 28)
    (hpa : s0.gpr .ebp = s0.gpr .edi + BitVec.ofNat 32 a)
    (hpb : s0.gpr .esi = s0.gpr .edi + BitVec.ofNat 32 b) (h : RowInvU base a b s0 i s) :
    WP isa (.block (mulRowU i)) s (RowInvU base a b s0 (i + 1)) := by
  have ha' : a + 112 ≤ 3584 := ha
  have hb' : b + 112 ≤ 3584 := hb
  have input : ∀ o, Slot o → ∀ j < 28, limbs s.mem base o j = limbs s0.mem base o j := by
    intro o ho j hj
    exact h.mem.limbs (Or.inl ho) (Nat.le_trans ho (by decide)) hj
  have sp : ∀ {u : State} (r : Reg), r ∉ [Reg.eax, .ebx, .ecx, .edx] → Keeps [.eax, .ebx, .ecx, .edx] s0 u →
      u.gpr r = s0.gpr r := fun r hr k => k.1 r hr
  unfold mulRowU
  rw [List.append_assoc, WP.block_append_iff]
  have pa : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 a := by
    rw [sp .ebp (by decide) h.regs, sp .edi (by decide) h.regs]; exact hpa
  refine wp_load (h.scr.ea_ptr pa (by omega)) (h.scr.read (by omega)) fun t ht => ?_
  refine wp_mov rfl fun u hu => ?_
  have ku : Keeps [.ecx, .ebx] s u := (ht.rest (by decide)).trans (hu.rest (by decide))
  have us := h.scr.of_keeps ku (by decide)
  have um : u.mem = s.mem := hu.mem.trans ht.mem
  have uc : (u.gpr .ecx).toNat = limbs s0.mem base a i := by
    rw [hu.other .ecx (by decide), ht.gpr]
    exact (input a ha i hi).symm ▸ rfl
  have k0u : Keeps [.eax, .ebx, .ecx, .edx] s0 u := h.regs.trans (ku.mono (by decide))
  let c := rowC (accw s.mem base) (limbs s0.mem base a) (limbs s0.mem base b) i
  have cb : ∀ j < 28, c j ≤ 2 ^ 32 - radix := by
    intro j hj
    exact rowC_bound (ab i hi) (bb j hj) (h.lt (i + j) (by omega))
  refine WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryPass_ok (s0 := u) (base := base) (o := ACC + 4 * i) (c := c)
    (by decide) (by simp only [ACC]; omega)
    (fun j hj => by
      rw [show ACC + 4 * i + 4 * j = ACC + 4 * i + 4 * j from rfl]
      exact us.ea (by simp only [ACC]; omega))
    (fun j hj => us.write (by simp only [ACC]; omega)) (by rw [hu.gpr]; rfl) cb ?_) fun v hv => ?_
  · intro j hj v hv
    have vs := us.of_keeps hv.regs (by decide)
    have vk : Keeps [.eax, .ebx, .ecx, .edx] s0 v := k0u.trans (hv.regs.mono (by decide))
    have vp : v.gpr .esi = v.gpr .edi + BitVec.ofNat 32 b := by
      rw [sp .esi (by decide) vk, sp .edi (by decide) vk]; exact hpb
    have va : (v.gpr .ecx).toNat = limbs s0.mem base a i := by rw [hv.regs.1 _ (by decide), uc]
    have vb : limbs v.mem base b j = limbs s0.mem base b j := by
      rw [hv.mem.limbs (Or.inl (by simp only [ACC]; omega)) (by omega) hj, um, input b hb j hj]
    have vacc : accw v.mem base (i + j) = accw s.mem base (i + j) := by
      change (word v.mem base (ACC + 4 * (i + j))).toNat = _
      rw [hv.mem.word (Or.inr (by omega)) (by simp only [ACC]; omega), um]
    refine WP.mono (rowSrcU_ok vs hb hi hj vp (by rw [va]; exact ab i hi) (by rw [vb]; exact bb j hj)
      (by rw [vacc]; exact h.lt (i + j) (by omega))) fun w ⟨wv, wk, wm⟩ => ⟨?_, wk, wm⟩
    rw [va, vb, vacc] at wv
    have e : ACC + 4 * (i + j) = ACC + 4 * i + 4 * j := by omega
    exact wv
  · have vs := us.of_keeps hv.regs (by decide)
    refine store_ok vs (o := ACC + 4 * (i + 28)) (by simp only [ACC]; omega) fun w hw => WP.block_nil ?_
    have passMem : Outside base (ACC + 4 * i) 112 s.mem v.mem := by rw [← um]; exact hv.mem
    have kv : Keeps [.eax, .ebx, .ecx, .edx] s v := (ku.mono (by decide)).trans (hv.regs.mono (by decide))
    have wm : w.mem = v.mem.writeW (off base (ACC + 4 * (i + 28))) (v.gpr .ebx) := hw.mem
    have limbsOut : ∀ k < i + 29, accw w.mem base k =
        rowAcc (accw s.mem base) (limbs s0.mem base a) (limbs s0.mem base b) i k := by
      intro k hk
      change (word w.mem base (ACC + 4 * k)).toNat = _
      rw [wm, word_write v.mem base (by simp only [ACC]; omega) (by simp only [ACC]; omega)]
      by_cases he : k = i + 28
      · rw [ite_eq_left he, hv.carry]
        simp only [c, rowAcc, he, show ¬i + 28 < i by omega, Nat.lt_irrefl, ite_false]
      · rw [ite_eq_right he]
        by_cases hk' : k < i
        · rw [passMem.word (Or.inl (by omega)) (by simp only [ACC]; omega)]
          simp only [rowAcc, hk', ite_true]
        · have out := hv.outs (k - i) (by omega)
          rw [acc_shift, show i + (k - i) = k by omega] at out
          change accw v.mem base k = _
          rw [out]
          simp only [c, rowAcc, hk', show k < i + 28 by omega, ite_false, ite_true]
    refine ⟨vs.of_keeps (hw.rest []) (by decide), h.regs.trans (kv.trans ((hw.rest []).mono (by decide))),
      ?_, ?_, ?_⟩
    · rw [wm]
      exact (h.mem.trans (passMem.mono (by omega) (by omega))).trans
        ((writeW_outside _ _ _ (by simp only [ACC]; omega)).mono (by omega) (by omega))
    · intro k hk
      rw [limbsOut k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega)) cb k hk
    · rw [valN_congr limbsOut]
      exact row_val h.val

/-- `esi = ws + b`, `ebp = ws + a` and the accumulator zeroed. -/
theorem mulSetup_ok {s : State} {base : Addr} {o a b : Nat} (hc : FnCtx s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) :
    WP isa (.block (argPtr .esi 3 ++ argPtr .ebp 2 ++ zeroAcc)) s fun t =>
      ∃ s0, RowInvU base a b s0 0 t ∧ s0.gpr .esi = s0.gpr .edi + BitVec.ofNat 32 b ∧
        s0.gpr .ebp = s0.gpr .edi + BitVec.ofNat 32 a ∧ Keeps [.esi, .ebp] s s0 ∧ s0.mem = s.mem := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (argPtr_ok hc.args (by decide) (by decide) hvb) fun s1 ⟨p1, m1, k1⟩ => ?_
  have c1 := hc.keep k1 (by decide) (by decide) (by rw [m1]; exact Outside.refl _ _ _ _)
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok c1.args (by decide) (by decide) c1.argA) fun s0 ⟨p0, m0, k0⟩ => ?_
  have hs0 := c1.scr.of_keeps k0 (by decide)
  refine WP.mono (zeroAcc_ok hs0) fun t ⟨tf, tm, tk⟩ => ⟨s0, ?_, ?_, p0, ?_, m0.trans m1⟩
  · refine ⟨hs0.of_keeps tk (by decide), tk.mono (by decide), tm.mono (by decide) (by decide), ?_, ?_⟩
    · intro i hi; rw [tf i hi]; decide
    · rw [valN_congr tf, valN_zero]; simp [valN]
  · rw [k0.1 _ (by decide), k0.1 _ (by decide)]; exact p1
  · exact (k1.mono (by decide)).trans (k0.mono (by decide))

/-- The product's 28 rows. -/
theorem mulRows_ok {s0 t : State} {base : Addr} {a b : Nat} (ha : Slot a) (hb : Slot b)
    (hpa : s0.gpr .ebp = s0.gpr .edi + BitVec.ofNat 32 a) (hpb : s0.gpr .esi = s0.gpr .edi + BitVec.ofNat 32 b)
    (ab : Bounded s0.mem base a) (bb : Bounded s0.mem base b) (ht : RowInvU base a b s0 0 t) :
    WP isa (.block ((List.range 28).flatMap mulRowU)) t (RowInvU base a b s0 28) :=
  wp_range_flatMap (M := isa) (RowInvU base a b s0) (fun _ _ hi h => mulRowU_ok ha hb ab bb hi hpa hpb h)
    28 (Nat.le_refl _) t ht

/-- The product folded and normalized into the element at `o`. -/
theorem mulTail_ok {s0 u : State} {base : Addr} {o a b : Nat} (hc : FnCtx s0 base 4 o a)
    (hu : RowInvU base a b s0 28 u) :
    WP isa (.block ((List.range 28).flatMap reduceCol ++ normalize)) u fun w =>
      FieldMem base o u.mem w.mem WORK ∧ Bounded w.mem base o ∧
      F w.mem base o = F s0.mem base a * F s0.mem base b ∧ Keeps [.eax, .ebx, .edx, .ebp] u w := by
  have uk : Keeps clob s0 u := hu.regs.mono (by decide)
  have us := hu.scr
  let f := limbs u.mem base ACC
  have fb : ∀ i < 56, f i < radix := hu.lt
  have fv : valN f 56 = fe s0.mem base a * fe s0.mem base b := hu.val
  have uc : FnCtx u base 4 o a := hc.keep uk (by decide) (by decide) (hu.mem.mono (by decide) (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok us (fun _ _ => rfl) fb) fun v ⟨vf, vm, vk⟩ => ?_
  have vc : FnCtx v base 4 o a := uc.keep vk (by decide) (by decide) (vm.mono (by decide) (by decide))
  refine WP.mono (normalize_ok vc.scr vc.args (by decide) vc.slotO vc.argO vf (reduced_bound fb))
    fun w ⟨wf, wm, wk⟩ => ?_
  have value : fe w.mem base o % Spec.X448.P = (fe s0.mem base a * fe s0.mem base b) % Spec.X448.P := by
    rw [show fe w.mem base o = valN (normalized (reduced f)) 28 from valN_congr wf,
      normalized_mod (reduced_bound fb), reduced_mod, fv]
  refine ⟨(FieldMem.work vm (by decide) (by decide)).trans wm, ?_, toFe_mul value,
    (vk.mono (by decide)).trans wk⟩
  intro i hi
  rw [wf i hi]
  exact digit_lt _ _

end VG.Proof.X448.X86
