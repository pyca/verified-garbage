module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86.Mem
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Instr
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X448.X86.FnCtx
public import VerifiedGarbage.Proof.X448.X86.Normalize
public import VerifiedGarbage.Proof.X448.X86.RowMem
import VerifiedGarbage.Proof.X448.X86.Init
import VerifiedGarbage.Proof.X448.X86.RowPass
import VerifiedGarbage.Proof.X448.X86.Row
import VerifiedGarbage.Proof.X448.X86.Small
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.X448.X86.AddSub
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `X448.X86.Mul`, which only this module used -/

section

/-! ### `X448.X86.Reduce`, which only this module used -/

section

/-!
# X448 on x86 (32-bit): reducing product limbs

The upper half folds using `2^448 = 2^224 + 1` modulo the field prime.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem loadAdd_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 4 ≤ 4096) :
    WP isa (.block [.alu .add .eax (.mem (sc d))]) s fun t =>
      t.gpr .eax = s.gpr .eax + word s.mem base d ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  have rd : readSrc s (.mem (sc d)) = some (word s.mem base d) := by
    simp only [readSrc, hs.ea (d := d) (by omega_using [hd]), State.load32,
      hs.read (d := d) (n := 4) (by omega_using [hd]), ite_true]
  refine wp_alu (Or.inl rfl) rd fun t ht _ => WP.block_nil ⟨ht.gpr, ht.mem, ht.rest (by decide)⟩

/-- A bounded sum of words, accumulated into `eax`. -/
def addWords (ds : List Nat) : List Instr :=
  ds.flatMap fun d => [.alu .add .eax (.mem (sc d))]

theorem addWords_ok {s : State} {base : Addr} (hs : Scr s base) {ds : List Nat}
    (hd : ∀ d ∈ ds, d + 4 ≤ 4096) :
    WP isa (.block (addWords ds)) s fun t =>
      t.gpr .eax = s.gpr .eax + (ds.map fun d => word s.mem base d).sum ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  induction ds generalizing s with
  | nil => exact WP.block_nil ⟨(BitVec.add_zero _).symm, rfl, Keeps.refl _ _⟩
  | cons d ds ih =>
    change WP isa (.block (([.alu .add .eax (.mem (sc d))] : List Instr) ++ addWords ds)) s _
    rw [WP.block_append_iff]
    refine WP.mono (loadAdd_ok hs (hd d List.mem_cons_self)) fun t ⟨tv, tm, tk⟩ => ?_
    refine WP.mono (ih (hs.of_keeps tk (by decide)) (fun d h => hd d (List.mem_cons_of_mem _ h)))
      fun u ⟨uv, um, uk⟩ => ⟨?_, um.trans tm, tk.trans uk⟩
    rw [uv, tv, tm]
    simp only [List.map_cons, List.sum_cons, BitVec.add_assoc]

/-- The extra offsets folded into product limb `k`. -/
def colOffsets (k : Nat) : List Nat :=
  [ACC + 4 * (k + 28)] ++
    if k < 14 then [ACC + 4 * (k + 42)] else [ACC + 4 * (k + 14), ACC + 4 * (k + 28)]

theorem colOffsets_bound {k : Nat} (hk : k < 28) : ∀ d ∈ colOffsets k, d + 4 ≤ 4096 := by
  intro d hd
  simp only [colOffsets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | hd
  · simp only [ACC]; omega_using [hk]
  · split at hd <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    · subst d; simp only [ACC]; omega_using [hk]
    · rcases hd with rfl | rfl <;> simp only [ACC] <;> omega_using [hk]

theorem reduceCol_code (k : Nat) : reduceCol k =
    [ld .eax (ACC + 4 * k)] ++ addWords (colOffsets k) ++ [st .eax (TMP + 4 * k)] := by
  unfold reduceCol colOffsets
  split <;> rfl

theorem reduceCol_ok {s : State} {base : Addr} (hs : Scr s base) {k : Nat} (hk : k < 28)
    {f : Nat → Nat} (hf : ∀ i < 56, limbs s.mem base ACC i = f i)
    (hb : ∀ i < 56, f i < radix) :
    WP isa (.block (reduceCol k)) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 4 * k)) (BitVec.ofNat 32 (reduced f k)) ∧
      Keeps [.eax] s t := by
  rw [reduceCol_code, List.append_assoc]
  refine load_ok hs (by simp only [ACC]; omega_using [hk]) fun t ht => ?_
  change WP isa (.block (addWords (colOffsets k) ++ ([st .eax (TMP + 4 * k)] : List Instr))) t _
  rw [WP.block_append_iff]
  refine WP.mono (addWords_ok (hs.of_upd ht (by decide)) (colOffsets_bound hk))
    fun u ⟨uv, um, uk⟩ => ?_
  have us := (hs.of_upd ht (by decide)).of_keeps uk (by decide)
  refine store_ok us (by simp only [TMP]; omega_using [hk]) fun v hv => WP.block_nil ⟨?_, ?_⟩
  · rw [hv.mem, um, ht.mem, uv, ht.gpr, ht.mem]
    apply congrArg (s.mem.writeW _)
    apply BitVec.eq_of_toNat_eq
    have f0 := hf k (by omega_using [hk])
    have f1 := hf (k + 28) (by omega_using [hk])
    have b0 := hb k (by omega_using [hk])
    have b1 := hb (k + 28) (by omega_using [hk])
    by_cases h : k < 14
    · have f2 := hf (k + 42) (by omega_using [h])
      have b2 := hb (k + 42) (by omega_using [h])
      simp only [colOffsets, h, ite_true, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, reduced, h, ite_true]
      change (limbs s.mem base ACC k + (limbs s.mem base ACC (k + 28) +
        (limbs s.mem base ACC (k + 42)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [radix] at b0 b1 b2
      omega_using []
    · have f2 := hf (k + 14) (by omega_using [hk])
      have b2 := hb (k + 14) (by omega_using [hk])
      simp only [colOffsets, h, ite_false, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, reduced, h, ite_false]
      change (limbs s.mem base ACC k + (limbs s.mem base ACC (k + 28) +
        (limbs s.mem base ACC (k + 14) + (limbs s.mem base ACC (k + 28)) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32) % 2 ^ 32 = _
      rw [f0, f1, f2]
      simp only [radix] at b0 b1 b2
      omega_using []
  · exact (ht.rest (by decide)).trans (uk.trans (hv.rest _))

/-- Fold all fifty-six product limbs into twenty-eight, ready for carries. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base) {f : Nat → Nat}
    (hf : ∀ i < 56, limbs s.mem base ACC i = f i) (hb : ∀ i < 56, f i < radix) :
    WP isa (.block ((List.range 28).flatMap reduceCol)) s fun t =>
      (∀ i < 28, limbs t.mem base TMP i = reduced f i) ∧
      Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, limbs t.mem base TMP i = reduced f i) ∧
    Outside base TMP 112 s.mem t.mem ∧ Keeps [.eax] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (reduceCol n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    have ft : ∀ i < 56, limbs t.mem base ACC i = f i := by
      intro i hi
      change (word t.mem base (ACC + 4 * i)).toNat = _
      rw [tm.word (Or.inl (by simp only [ACC, TMP]; omega_using [hi])) (by simp only [ACC]; omega_using [hi])]
      exact hf i hi
    refine WP.mono (reduceCol_ok (hs.of_keeps tk (by decide)) hn ft hb) fun u ⟨um, uk⟩ => ?_
    have out : Outside base (TMP + 4 * n) 4 t.mem u.mem := by
      rw [um]; exact writeW_outside _ _ _ (by simp only [TMP]; omega_using [hn])
    refine ⟨?_, tm.trans (out.mono (by omega_using []) (by omega_using [hn])), tk.trans uk⟩
    intro i hi
    change (word u.mem base (TMP + 4 * i)).toNat = _
    rw [um, word_write t.mem base (by simp only [TMP]; omega_using [hn]) (by simp only [TMP]; omega_using [hn, hi])]
    by_cases h : i = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (reduced_bound hb n hn) (by decide))]
    · rw [ite_eq_right h]; exact tf i (by omega_using [hi, h])
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hi => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

end


/-!
# X448 on x86 (32-bit): field multiplication

`vg_gf448_r16_mul`'s product (`Impl/X448/X86.lean`, `mulFn`): `esi` points
at `b` and `ebp` at `a`, and the 28 unrolled rows (`mulRowU_ok`, as
`rowWith_ok` with the product's words at constant offsets of `edi`) produce
the 56 limbs of the product, which are folded and normalized modulo the
prime into the element at `o` (`mulTail_ok`).
-/

@[expose] public section

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
  refine wp_load (hs.ea_ptr hp (by omega_arith)) (hs.read (by omega_arith)) fun t ht => ?_
  refine wp_mul fun u uv um uk => ?_
  have us := (hs.of_upd ht (by decide)).of_keeps uk (by decide)
  have rd : readSrc u (.mem (sc (ACC + 4 * (i + j)))) = some (word u.mem base (ACC + 4 * (i + j))) := by
    simp only [readSrc, us.ea (d := ACC + 4 * (i + j)) (by simp only [ACC]; omega_arith), State.load32,
      us.read (d := ACC + 4 * (i + j)) (n := 4) (by simp only [ACC]; omega_arith), ite_true]
  refine wp_alu (Or.inl rfl) rd fun v hv _ => WP.block_nil ⟨?_, ?_, hv.mem.trans (um.trans ht.mem)⟩
  · rw [hv.gpr]
    change (u.gpr .eax + word u.mem base (ACC + 4 * (i + j))).toNat = _
    rw [uv, ht.gpr, ht.other .ecx (by decide), um, ht.mem, BitVec.toNat_add, BitVec.toNat_ofNat]
    have prod := Nat.mul_le_mul (Nat.le_of_lt_succ hc) (Nat.le_of_lt_succ hy)
    simp only [radix] at hc hy hacc prod
    change ((limbs s.mem base b j * (s.gpr .ecx).toNat) % 2 ^ 32 + accw s.mem base (i + j)) % 2 ^ 32 = _
    rw [Nat.mul_comm (limbs s.mem base b j)]
    omega_arith
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
  refine wp_load (h.scr.ea_ptr pa (by omega_arith)) (h.scr.read (by omega_arith)) fun t ht => ?_
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
    exact rowC_bound (ab i hi) (bb j hj) (h.lt (i + j) (by omega_arith))
  refine WP.block_nil ?_
  rw [WP.block_append_iff]
  refine WP.mono (carryPass_ok (s0 := u) (base := base) (o := ACC + 4 * i) (c := c)
    (by decide) (by simp only [ACC]; omega_arith)
    (fun j hj => by
      rw [show ACC + 4 * i + 4 * j = ACC + 4 * i + 4 * j from rfl]
      exact us.ea (by simp only [ACC]; omega_arith))
    (fun j hj => us.write (by simp only [ACC]; omega_arith)) (by rw [hu.gpr]; rfl) cb ?_) fun v hv => ?_
  · intro j hj v hv
    have vs := us.of_keeps hv.regs (by decide)
    have vk : Keeps [.eax, .ebx, .ecx, .edx] s0 v := k0u.trans (hv.regs.mono (by decide))
    have vp : v.gpr .esi = v.gpr .edi + BitVec.ofNat 32 b := by
      rw [sp .esi (by decide) vk, sp .edi (by decide) vk]; exact hpb
    have va : (v.gpr .ecx).toNat = limbs s0.mem base a i := by rw [hv.regs.1 _ (by decide), uc]
    have vb : limbs v.mem base b j = limbs s0.mem base b j := by
      rw [hv.mem.limbs (Or.inl (by simp only [ACC]; omega_arith)) (by omega_arith) hj, um, input b hb j hj]
    have vacc : accw v.mem base (i + j) = accw s.mem base (i + j) := by
      change (word v.mem base (ACC + 4 * (i + j))).toNat = _
      rw [hv.mem.word (Or.inr (by omega_arith)) (by simp only [ACC]; omega_arith), um]
    refine WP.mono (rowSrcU_ok vs hb hi hj vp (by rw [va]; exact ab i hi) (by rw [vb]; exact bb j hj)
      (by rw [vacc]; exact h.lt (i + j) (by omega_arith))) fun w ⟨wv, wk, wm⟩ => ⟨?_, wk, wm⟩
    rw [va, vb, vacc] at wv
    have e : ACC + 4 * (i + j) = ACC + 4 * i + 4 * j := by omega_arith
    exact wv
  · have vs := us.of_keeps hv.regs (by decide)
    refine store_ok vs (o := ACC + 4 * (i + 28)) (by simp only [ACC]; omega_arith) fun w hw => WP.block_nil ?_
    have passMem : Outside base (ACC + 4 * i) 112 s.mem v.mem := by rw [← um]; exact hv.mem
    have kv : Keeps [.eax, .ebx, .ecx, .edx] s v := (ku.mono (by decide)).trans (hv.regs.mono (by decide))
    have wm : w.mem = v.mem.writeW (off base (ACC + 4 * (i + 28))) (v.gpr .ebx) := hw.mem
    have limbsOut : ∀ k < i + 29, accw w.mem base k =
        rowAcc (accw s.mem base) (limbs s0.mem base a) (limbs s0.mem base b) i k := by
      intro k hk
      change (word w.mem base (ACC + 4 * k)).toNat = _
      rw [wm, word_write v.mem base (by simp only [ACC]; omega_arith) (by simp only [ACC]; omega_arith)]
      by_cases he : k = i + 28
      · rw [ite_eq_left he, hv.carry]
        simp only [c, rowAcc, he, show ¬i + 28 < i by omega_arith, Nat.lt_irrefl, ite_false]
      · rw [ite_eq_right he]
        by_cases hk' : k < i
        · rw [passMem.word (Or.inl (by omega_arith)) (by simp only [ACC]; omega_arith)]
          simp only [rowAcc, hk', ite_true]
        · have out := hv.outs (k - i) (by omega_arith)
          rw [acc_shift, show i + (k - i) = k by omega_arith] at out
          change accw v.mem base k = _
          rw [out]
          simp only [c, rowAcc, hk', show k < i + 28 by omega_arith, ite_false, ite_true]
    refine ⟨vs.of_keeps (hw.rest []) (by decide), h.regs.trans (kv.trans ((hw.rest []).mono (by decide))),
      ?_, ?_, ?_⟩
    · rw [wm]
      exact (h.mem.trans (passMem.mono (by omega_arith) (by omega_arith))).trans
        ((writeW_outside _ _ _ (by simp only [ACC]; omega_arith)).mono (by omega_arith) (by omega_arith))
    · intro k hk
      rw [limbsOut k hk]
      exact rowAcc_lt (fun k hk => h.lt k (by omega_arith)) cb k hk
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

end

end


/-!
# X448 on x86 (32-bit): the field functions

`vg_gf448_r16_{mul,add,sub,mul_a24}` (`Impl/X448/X86.lean`) from their entry
(`FnEntry`: the working space `ws` at `base` and the offsets on the stack):
`fnEntry` loads `ws` into `edi` and saves the callee-saved registers in the
last 16 bytes of the functions' own working space (`fnEntry_ok`), the
operation writes its result (`Mul.lean`, `AddSub.lean`, `Small.lean`), and
`fnExit` restores the registers (`fnExit_ok`). Each function changes only
`eax`, `ecx`, `edx` and the flags, the result and its own working space
(`FnOut`).
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- A field function's entry: the working space `ws` (its first argument) at
`base`, writable and not wrapping around; the first `n` arguments readable
outside it, as is the return address; the offsets `o` and `a` of the result
and the first operand, below the functions' own working space. -/
structure FnEntry (s : State) (base : Addr) (n o a : Nat) : Prop where
  ws : (arg s 0).setWidth 64 = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : (arg s 0).toNat + 8192 ≤ 2 ^ 32
  args : ArgArea s base n
  n3 : 3 ≤ n
  ret : ∀ k < 4, 8192 ≤ ofs base ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k)
  argO : arg s 1 = BitVec.ofNat 32 o
  argA : arg s 2 = BitVec.ofNat 32 a
  slotO : Slot o
  slotA : Slot a

/-- What a field function changes: `eax`, `ecx` and `edx`, and in memory
the result at `o` and its own working space; the result's limbs are below
`2^16`. -/
structure FnOut (base : Addr) (o : Nat) (s t : State) : Prop where
  keeps : Keeps [.eax, .ecx, .edx] s t
  mem : FieldMem base o s.mem t.mem
  bounded : Bounded t.mem base o

/-- Where the field functions save the callee-saved registers. -/
def fnSlots : Spill.Slots := [(.ebx, SAVE), (.esi, SAVE + 4), (.edi, SAVE + 8), (.ebp, SAVE + 12)]

theorem fnSlots_fits : Spill.Fits 8192 fnSlots := by decide

abbrev FnSaved (base : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop := Spill.Saved m (off base) g fnSlots

/-- A frame of the `n` bytes at offset `d`. -/
theorem Outside.of_frameAt {base : Addr} {d n : Nat} {m m' : Mem} (hd : d + n ≤ 8192)
    (hf : Frame [⟨off base d, n⟩] m m') : Outside base d n m m' :=
  fun x hx => hf x fun r hr => by
    rw [List.mem_singleton.mp hr]
    change ¬ ((x - (base + BitVec.ofNat 64 d)).toNat + 1 ≤ n)
    have := (Offset.lt_iff x base (d := d) (n := n) (by omega_arith)).mp
    simp only [ofs] at hx
    intro h
    have := this (by omega_arith)
    omega_arith

theorem fnEntry_ok {s : State} {base : Addr} {n o a : Nat} (h : FnEntry s base n o a) :
    WP isa (.block fnEntry) s fun t =>
      FnCtx t base n o a ∧ FnSaved base s.gpr t.mem ∧ Outside base SAVE 16 s.mem t.mem ∧
      Keeps [.eax, .edi] s t := by
  change WP isa (.block (.mov .eax (.mem (argOp 0)) ::
    (Spill.saveCode .eax fnSlots ++ [.mov .edi (.reg .eax)]))) s _
  refine h.args.load (by have := h.n3; omega_arith) fun t ht => ?_
  refine Spill.save_ofNat_ok fnSlots fnSlots_fits (by rw [ht.gpr]; exact h.nowrap)
    (fun p hp => by
      rw [ht.gpr, ht.wr, h.ws]
      exact ⟨_, h.wr, contains_sc (by have := fnSlots_fits.1 p hp; omega_arith)⟩) fun u hu => ?_
  have hm : u.mem = Spill.saveMem s.mem (off base) s.gpr fnSlots := by
    rw [hu.mem, ht.gpr, ht.mem, h.ws]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp => ht.other _ (by revert p hp; decide)
  refine wp_mov rfl fun v hv => WP.block_nil ?_
  have kv : Keeps [.eax, .edi] s v :=
    ((ht.rest (by decide)).trans (⟨fun r _ => by rw [hu.gpr], hu.rd, hu.wr⟩ : Keeps [.eax, .edi] t u)).trans
      (hv.rest (by decide))
  have mv : Outside base SAVE 16 s.mem v.mem := by
    rw [hv.mem, hm]
    refine Outside.of_frameAt (by decide) (Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp => ?_)
    have := fnSlots_fits.1 p hp
    have h2 : SAVE ≤ p.2 ∧ p.2 + 4 ≤ SAVE + 16 := by revert p hp; decide
    exact Offset.contains _ h2.1 h2.2 (by simp only [SAVE]; omega_arith)
  have vs : Scr v base := ⟨by rw [hv.gpr, hu.gpr, ht.gpr]; exact h.ws, by rw [hv.wr, hu.wr, ht.wr]; exact h.wr,
    by rw [hv.gpr, hu.gpr, ht.gpr]; exact h.nowrap⟩
  obtain ⟨va, varg⟩ := h.args.keep (kv.1 _ (by decide)) kv.2.1 kv.2.2 (mv.mono (by decide) (by decide))
  refine ⟨⟨vs, va, h.n3, by rw [varg 1 (by have := h.n3; omega_arith)]; exact h.argO,
    by rw [varg 2 (by have := h.n3; omega_arith)]; exact h.argA, h.slotO, h.slotA⟩, ?_, mv, kv⟩
  rw [hv.mem, hm]
  exact Spill.saveMem_saved_ofNat _ _ _ fnSlots_fits (by decide)

theorem fnExit_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 32}
    (hsv : FnSaved base g s.mem) :
    WP isa (.block fnExit) s fun t =>
      (∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], t.gpr r = g r) ∧ t.mem = s.mem ∧
      Keeps [.ebx, .esi, .edi, .ebp] s t := by
  change WP isa (.block (Spill.restoreCode .edi ([(.ebx, SAVE), (.esi, SAVE + 4), (.ebp, SAVE + 12)] ++
    [(.edi, SAVE + 8)]) ++ [])) s _
  have hb : (s.gpr .edi).setWidth 64 = base := hs.edi
  have slot : ∀ p ∈ ([(.ebx, SAVE), (.esi, SAVE + 4), (.ebp, SAVE + 12)] ++ [(.edi, SAVE + 8)] : Spill.Slots),
      p ∈ fnSlots := by decide
  refine Spill.restoreBase_ok (g := g) _ (by decide) (fun p hp => ?_) (fun p hp => ?_) fun t ht => WP.block_nil ?_
  · have := fnSlots_fits.1 p (slot p hp)
    rw [Spill.addr_eq_of hs.nowrap (n := 8192) (by omega_arith), hb]
    exact hs.read (by omega_arith)
  · have := fnSlots_fits.1 p (slot p hp)
    rw [Spill.addr_eq_of hs.nowrap (n := 8192) (by omega_arith), hb]
    exact hsv p (slot p hp)
  · refine ⟨fun r hr => ?_, ht.mem, ⟨fun r hr => ht.other r (by
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hr ⊢
      exact ⟨⟨hr.1, hr.2.1, hr.2.2.2⟩, hr.2.2.1⟩), ht.rd, ht.wr⟩⟩
    have := ht.regs r (by revert r hr; decide)
    exact this

theorem FnSaved.keep {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (hs : FnSaved base g m)
    {o : Nat} (ho : Slot o) (h : FieldMem base o m m' WORK) : FnSaved base g m' := by
  have ho' : o + 112 ≤ 3584 := ho
  refine hs.of_readW fun p hp => ?_
  have hp' : SAVE ≤ p.2 ∧ p.2 + 4 ≤ SAVE + 16 := by revert p hp; decide
  have hs' : p.2 + 4 < 2 ^ 64 := by simp only [SAVE] at hp'; omega_arith
  exact Mem.readW_congr fun i hi => h _
    (Or.inr (by rw [ofs_off base (d := p.2) (i := i) (by omega_arith)]; simp only [SAVE] at hp'; omega_arith))
    (Or.inr (by rw [ofs_off base (d := p.2) (i := i) (by omega_arith)]; simp only [SAVE, ACC, WORK, TMP] at hp' ⊢; omega_arith))

/-- The exit, after a body that changed the registers `rs` (not `esp`) and,
in the working space, the result and the arithmetic's own bytes. -/
theorem fnExit_out {s t u : State} {base : Addr} {n o a : Nat} (tc : FnCtx t base n o a)
    (tv : FnSaved base s.gpr t.mem) (tm : Outside base SAVE 16 s.mem t.mem) (tk : Keeps [.eax, .edi] s t)
    {rs : List Reg} (hrs : .esp ∉ rs) (uk : Keeps rs t u) (us : Scr u base)
    (um : FieldMem base o t.mem u.mem WORK) (ub : Bounded u.mem base o) :
    WP isa (.block fnExit) u fun w => FnOut base o s w ∧ w.mem = u.mem := by
  refine WP.mono (fnExit_ok us (tv.keep tc.slotO um)) fun w ⟨wr, wm, wk⟩ => ?_
  refine ⟨⟨⟨fun r hr => ?_, wk.2.1.trans (uk.2.1.trans tk.2.1), wk.2.2.trans (uk.2.2.trans tk.2.2)⟩,
    ?_, by rw [wm]; exact ub⟩, wm⟩
  · by_cases hs : r ∈ [Reg.ebx, .esi, .edi, .ebp]
    · exact wr r hs
    · have hr' : r = .esp := by
        cases r <;> first | rfl | exact absurd (by decide) hr | exact absurd (by decide) hs
      subst hr'
      rw [wk.1 _ (by decide), uk.1 _ hrs, tk.1 _ (by decide)]
  · rw [wm]
    exact (FieldMem.work tm (by decide) (by decide)).trans (um.mono (by decide))

/-- A field function of one block: its entry, its `body`, and its exit. -/
theorem fnBlock_ok {s : State} {base : Addr} {n o a : Nat} (h : FnEntry s base n o a) {body : List Instr}
    {Q : Mem → Prop}
    (hb : ∀ t, FnCtx t base n o a → Outside base SAVE 16 s.mem t.mem → Keeps [.eax, .edi] s t →
      WP isa (.block body) t fun u => FnPost base o t u ∧ Q u.mem) :
    WP isa (.block (fnEntry ++ body ++ fnExit)) s fun w => FnOut base o s w ∧ Q w.mem := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (fnEntry_ok h) fun t ⟨tc, tv, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hb t tc tm tk) fun u ⟨⟨uk, um, ub⟩, uq⟩ => ?_
  refine WP.mono (fnExit_out tc tv tm tk (by decide) uk (tc.scr.of_keeps uk (by decide)) um ub)
    fun w ⟨hw, wm⟩ => ⟨hw, by rw [wm]; exact uq⟩

theorem mulA24Fn_ok {s : State} {base : Addr} {o a : Nat} (h : FnEntry s base 3 o a)
    (ab : Bounded s.mem base a) :
    WP isa mulA24Fn s fun t => FnOut base o s t ∧ F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  have ha' : a + 112 ≤ 3584 := h.slotA
  refine WP.mono (fnBlock_ok (body := argPtr .esi 2 ++ a24Cols ++ normalize)
    (Q := fun m => F m base o = Spec.X448.a24 * F s.mem base a) h fun t tc tm _ => ?_) fun _ h => h
  have ea : fe t.mem base a = fe s.mem base a := tm.fe (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith)
  have bt : Bounded t.mem base a := fun i hi => by
    rw [tm.limbs (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith) hi]; exact ab i hi
  refine WP.mono (a24Body_ok tc bt) fun u ⟨up, uv⟩ => ⟨up, ?_⟩
  rw [uv, F, F, ea]

/-- The third argument after the entry. -/
theorem argB_keep {s t : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (tk : Keeps [.eax, .edi] s t)
    (tm : Outside base SAVE 16 s.mem t.mem) : arg t 3 = BitVec.ofNat 32 b := by
  rw [(h.args.keep (tk.1 _ (by decide)) tk.2.1 tk.2.2 (tm.mono (by decide) (by decide))).2 3 (by decide), hvb]

/-- Operands below the own working space read the same after the entry. -/
theorem entry_operand {s t : State} {base : Addr} {a : Nat} (ha : Slot a)
    (tm : Outside base SAVE 16 s.mem t.mem) :
    fe t.mem base a = fe s.mem base a ∧ (Bounded s.mem base a → Bounded t.mem base a) := by
  have ha' : a + 112 ≤ 3584 := ha
  refine ⟨tm.fe (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith), fun ab i hi => ?_⟩
  rw [tm.limbs (Or.inl (by simp only [SAVE]; omega_arith)) (by omega_arith) hi]; exact ab i hi

theorem addFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa addFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a + F s.mem base b := by
  rw [show addFn = .block (fnEntry ++ (argPtr .esi 2 ++ argPtr .ebp 3 ++ addCols ++ normalize) ++ fnExit)
    by simp only [addFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a + F s.mem base b) h fun t tc tm tk => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  exact WP.mono (addBody_ok tc (argB_keep h hvb tk tm) hb (ba ab) (bb' bb)) fun u ⟨up, uv⟩ =>
    ⟨up, by rw [uv, F, F, ea, eb]⟩

theorem subFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa subFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a - F s.mem base b := by
  rw [show subFn = .block (fnEntry ++ (argPtr .esi 2 ++ argPtr .ebp 3 ++ subCols ++ normalize) ++ fnExit)
    by simp only [subFn, List.append_assoc]]
  refine fnBlock_ok (Q := fun m => F m base o = F s.mem base a - F s.mem base b) h fun t tc tm tk => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  exact WP.mono (subBody_ok tc (argB_keep h hvb tk tm) hb (ba ab) (bb' bb)) fun u ⟨up, uv⟩ =>
    ⟨up, by rw [uv, F, F, ea, eb]⟩

theorem mulFn_ok {s : State} {base : Addr} {o a b : Nat} (h : FnEntry s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) (hb : Slot b) (ab : Bounded s.mem base a)
    (bb : Bounded s.mem base b) :
    WP isa mulFn s fun t => FnOut base o s t ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  unfold mulFn
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fnEntry_ok h) fun t ⟨tc, tv, tm, tk⟩ => ?_
  obtain ⟨ea, ba⟩ := entry_operand h.slotA tm
  obtain ⟨eb, bb'⟩ := entry_operand hb tm
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulSetup_ok tc (argB_keep h hvb tk tm)) fun u ⟨s0, hu, hp, hpa, k0, m0⟩ => ?_
  have c0 := tc.keep k0 (by decide) (by decide) (by rw [m0]; exact Outside.refl _ _ _ _)
  rw [WP.block_append_iff]
  refine WP.mono (mulRows_ok h.slotA hb hpa hp (by rw [m0]; exact ba ab) (by rw [m0]; exact bb' bb) hu)
    fun v hv => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulTail_ok c0 hv) fun w ⟨wm, wb, wv, wk⟩ => ?_
  have kw : Keeps (.esi :: clob) t w :=
    ((k0.mono (by decide)).trans (hv.regs.mono (by decide))).trans (wk.mono (by decide))
  have mw : FieldMem base o t.mem w.mem WORK := by
    rw [← m0]
    exact (FieldMem.work hv.mem (by decide) (by decide)).trans wm
  refine WP.mono (fnExit_out tc tv tm tk (by decide) kw (tc.scr.of_keeps kw (by decide)) mw wb)
    fun x ⟨hx, xm⟩ => ⟨hx, ?_⟩
  rw [xm, wv, F, F, F, F, m0, ea, eb]

end VG.Proof.X448.X86
