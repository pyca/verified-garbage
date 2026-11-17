module

public import VerifiedGarbage.Impl.Weierstrass.Arm.Window
public import VerifiedGarbage.Proof.Mont.Arm.Words
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombCorrect
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombScan
import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# A table of points past the working space's first 4096 bytes, on 32-bit ARM: correctness

What the code of `Impl/Weierstrass/Arm/Window.lean` does to the bytes, for a
working space whose first `size` bytes `r12` reaches (`Scr`) in a writable
region of `len` bytes (`Far`), with the table at offsets from `size` on:

* `wp_farPtr`, `wp_entryPtr`: the register is `r12` plus the offset;
* `storeFar_ok`, `storePt_ok`: the words, or the point's three coordinates,
  are at the offset `r5` is at, and nothing else changes;
* `scan_ok`: the slots at `o` hold the words of entry `r9`, by a loop over
  every entry (`upLoop_ok`, a loop counting up) that keeps the words of the
  entry whose number is `r9` (`scanWord_ok`, under the comb's mask
  `eqMask_ok`).
-/

-- separate module: the table's stores and scan on the working space's bytes, which changes to the
-- windows' field programs and points (its importer) need not check again

@[expose] public section

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_dp wp_mul wp_movw wp_cmp wp_ldr wp_str op2_imm op2_reg
  dpVal)

/-! ## Loops counting up -/

/-- A loop whose body takes the invariant from `j` to `j + 1` and leaves `Z`
set iff `j + 1 = n`, run from `i < n`. -/
theorem upLoop_ok {body : Prog isa} {Inv : Nat → State → Prop} {Q : State → Prop} {n i : Nat}
    (hstep : ∀ j s, i ≤ j → j < n → Inv j s →
      WP isa body s fun s' => Inv (j + 1) s' ∧ s'.z = decide (j + 1 = n))
    (hQ : ∀ s, Inv n s → Q s) (hi : i < n) {s : State} (hs : Inv i s) :
    WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ i ≤ j ∧ j < n ∧ Inv j s)
    (fun m s ⟨j, hm, hij, hjn, hI⟩ => ?_) (n - i) s ⟨i, rfl, Nat.le_refl _, hi, hs⟩
  refine WP.mono (hstep j s hij hjn hI) fun s' ⟨hI', hz⟩ => ?_
  by_cases h : j + 1 = n
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true h]; rfl, hQ s' (h ▸ hI')⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false h]; rfl, n - (j + 1),
      by omega_using [hm, hjn], j + 1, rfl, by omega_using [hij], by omega_using [hjn, h], hI'⟩

/-! ## Numbers from their words -/

/-- Numbers whose 32-bit words agree. -/
theorem val32_congr' {m m' : Mem} {base : Addr} {d d' : Nat} :
    ∀ {k : Nat}, (∀ j < k, w32 m' base (d' + 4 * j) = w32 m base (d + 4 * j)) →
      val32 m' base d' k = val32 m base d k
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_succ, h k (Nat.lt_succ_self _),
      val32_congr' fun j hj => h j (by omega_using [hj])]

/-- Numbers of `n` 64-bit words whose 32-bit words agree. -/
theorem wordsVal_of_w32 {m m' : Mem} {base : Addr} {d d' n : Nat}
    (h : ∀ j < 2 * n, w32 m' base (d' + 4 * j) = w32 m base (d + 4 * j)) :
    wordsVal m' base d' n = wordsVal m base d n := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]; exact val32_congr' h

/-! ## Pointers past the working space -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `farPtr r d`: `r = r12 + d`. -/
theorem wp_farPtr {r : Reg} {d : Nat} (hd : d < 2 ^ 16) (hr : r ≠ .r12)
    (k : ∀ t, Rest [r] s t → t.mem = s.mem → t.gpr r = t.gpr .r12 + BitVec.ofNat 32 d →
      WP isa (.block is) t Q) :
    WP isa (.block (farPtr r d ++ is)) s Q := by
  simp only [farPtr, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ =>
    k s₂ ((u₁.rest (by simp)).trans (u₂.rest (by simp))) (by rw [u₂.mem, u₁.mem]) ?_
  rw [u₂.gpr, dpVal, u₁.gpr, u₂.other _ (Ne.symm hr), u₁.other _ (Ne.symm hr)]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.Weierstrass.Arm.Point.movw_toNat hd, BitVec.toNat_ofNat]
  omega_using [hd]

/-- `entryPtr tbl bytes`, for `r11 = e`: `r5 = r12 + tbl + bytes · e`. -/
theorem wp_entryPtr {tbl bytes e : Nat} (hb : encodable (BitVec.ofNat 32 bytes) = true) (ht : tbl < 2 ^ 16)
    (he : s.gpr .r11 = BitVec.ofNat 32 e)
    (k : ∀ t, Rest [.r4, .r5] s t → t.mem = s.mem →
      t.gpr .r5 = t.gpr .r12 + BitVec.ofNat 32 (tbl + bytes * e) → WP isa (.block is) t Q) :
    WP isa (.block (entryPtr tbl bytes ++ is)) s Q := by
  simp only [entryPtr, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov (op2_imm hb) fun s₁ u₁ => wp_mul fun s₂ u₂ => ?_
  have k₂ : Rest [.r4, .r5] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have g₂ : s₂.gpr .r4 = BitVec.ofNat 32 (bytes * e) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), he, BitVec.ofNat_mul]
  refine wp_farPtr ht (by decide) fun s₃ k₃ m₃ p₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => k s₄ ((k₂.trans (k₃.mono (by simp))).trans (u₄.rest (by simp)))
    (by rw [u₄.mem, m₃, m₂]) ?_
  rw [u₄.gpr, dpVal, p₃, k₃.gpr .r4 (by decide), g₂, u₄.other .r12 (by decide), BitVec.add_assoc,
    ← BitVec.ofNat_add]

end

/-! ## Stores -/

/-- `[r5 + d] = [a]`, for `r5 = r12 + K`: the `k` words at `a` in the working
space are at `K + d`, past it. -/
theorem storeFar_ok {size len : Nat} : ∀ (k : Nat) {s : State} {base : Addr} {K d a : Nat},
    Scr s base size → Far s base len → s.gpr .r5 = s.gpr .r12 + BitVec.ofNat 32 K →
    a + 4 * k ≤ size → size ≤ K + d → K + d + 4 * k ≤ len → d + 4 * k ≤ 4096 →
    WP isa (.block (storeFar k d a)) s fun s' =>
      val32 s'.mem base (K + d) k = val32 s.mem base a k ∧ Rest [.r4] s s' ∧
      Outside base (K + d) (4 * k) s.mem s'.mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ =>
    WP.block_nil ⟨rfl, Rest.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, s, base, K, d, a, hs, hf, hp, ha, hsep, hl, hd => by
    have hn := hf.nowrap
    rw [storeFar, List.cons_append, List.cons_append, List.nil_append]
    refine wp_ldr (hs.off_lt (by omega_using [ha])) (hs.ea (by omega_using [ha]))
      (hs.read (d := a) (n := 4) (by omega_using [ha])) fun s₁ u₁ => ?_
    have k₁ : Rest [.r4] s s₁ := u₁.rest (by simp)
    have hs₁ := hs.of_rest k₁ (by decide)
    have hf₁ := hf.of_rest k₁
    have hp₁ : s₁.gpr .r5 = s₁.gpr .r12 + BitVec.ofNat 32 K := by
      rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), hp]
    refine wp_str (by omega_using [hd]) (hf₁.ea_reg hs₁ hp₁ (by omega_using [hl]))
      (hf₁.write (d := K + d) (n := 4) (by omega_using [hl])) fun s₂ m₂ => ?_
    have k₂ : Rest [.r4] s s₂ := k₁.trans (m₂.rest _)
    have O₂ : Outside base (K + d) 4 s.mem s₂.mem := by
      rw [m₂.mem, u₁.mem]; exact writeW32_outside _ _ _ (by omega_using [hl, hn])
    refine WP.mono (storeFar_ok k (hs.of_rest k₂ (by decide)) (hf.of_rest k₂) (K := K) (d := d + 4)
      (a := a + 4) (by rw [k₂.gpr _ (by decide), k₂.gpr _ (by decide), hp]) (by omega_using [ha])
      (by omega_using [hsep]) (by omega_using [hl]) (by omega_using [hd]))
      fun s₃ ⟨e₃, k₃, O₃⟩ => ⟨?_, k₂.trans k₃, (O₂.mono (Nat.le_refl _) (by omega_using [])).trans
        (O₃.mono (by omega_using []) (by omega_using []))⟩
    rw [← Nat.add_assoc] at e₃
    rw [val32, val32, O₃.w32 (by omega_using []) (by omega_using [hl, hn]), e₃,
      O₂.val32 (by omega_using [ha, hsep]) (by omega_using [ha, hn, hsep, hl]), m₂.mem, w32_write_self, u₁.gpr]

/-- The point `p` of the working space is at `K + d`, for `r5 = r12 + K`,
past it. -/
theorem storePt_ok {s : State} {base : Addr} {size len : Nat} (hs : Scr s base size) (hf : Far s base len)
    {n K d : Nat} {p : Pt} (hp : s.gpr .r5 = s.gpr .r12 + BitVec.ofNat 32 K)
    (hin : ∀ x ∈ [p.x, p.y, p.z], x + 8 * n ≤ size) (hsep : size ≤ K + d) (hl : K + d + 24 * n ≤ len)
    (hd : d + 24 * n ≤ 4096) :
    WP isa (.block (storePt n d p)) s fun s' =>
      wordsVal s'.mem base (K + d) n = wordsVal s.mem base p.x n ∧
      wordsVal s'.mem base (K + d + 8 * n) n = wordsVal s.mem base p.y n ∧
      wordsVal s'.mem base (K + d + 16 * n) n = wordsVal s.mem base p.z n ∧
      Rest [.r4] s s' ∧ Outside base (K + d) (24 * n) s.mem s'.mem := by
  have hn := hf.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  obtain ⟨ix, iy, iz⟩ := hin
  simp only [wordsVal_eq_val32]
  rw [storePt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeFar_ok (2 * n) hs hf hp (by omega_using [ix]) hsep (by omega_using [hl])
    (by omega_using [hd])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  have hf₁ := hf.of_rest k₁
  have hp₁ : s₁.gpr .r5 = s₁.gpr .r12 + BitVec.ofNat 32 K := by
    rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), hp]
  rw [WP.block_append_iff]
  refine WP.mono (storeFar_ok (2 * n) hs₁ hf₁ hp₁ (d := d + 8 * n) (by omega_using [iy])
    (by omega_using [hsep]) (by omega_using [hl]) (by omega_using [hd])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have k₁₂ := k₁.trans k₂
  have hp₂ : s₂.gpr .r5 = s₂.gpr .r12 + BitVec.ofNat 32 K := by
    rw [k₁₂.gpr _ (by decide), k₁₂.gpr _ (by decide), hp]
  refine WP.mono (storeFar_ok (2 * n) (hs.of_rest k₁₂ (by decide)) (hf.of_rest k₁₂) hp₂ (d := d + 16 * n)
    (by omega_using [iz]) (by omega_using [hsep]) (by omega_using [hl]) (by omega_using [hd]))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [← Nat.add_assoc] at e₂ e₃ O₂ O₃
  refine ⟨?_, ?_, ?_, k₁₂.trans k₃, ?_⟩
  · rw [O₃.val32 (by omega_using []) (by omega_using [hl, hn]), O₂.val32 (by omega_using []) (by omega_using [hl, hn]), e₁]
  · rw [O₃.val32 (by omega_using []) (by omega_using [hl, hn]), e₂,
      O₁.val32 (by omega_using [iy, hsep]) (by omega_using [iy, hsep, hl, hn])]
  · rw [e₃, O₂.val32 (by omega_using [iz, hsep]) (by omega_using [iz, hsep, hl, hn]),
      O₁.val32 (by omega_using [iz, hsep]) (by omega_using [iz, hsep, hl, hn])]
  · exact ((O₁.mono (Nat.le_refl _) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using []))).trans
      (O₃.mono (by omega_using []) (by omega_using []))

/-! ## The scan -/

/-- One word: `[o + 4 i]` is the word `i` of the entry at `X`, where `r8`
is, if the mask is set. -/
theorem scanWord_ok {s : State} {base : Addr} {size len o X i : Nat} (hs : Scr s base size)
    (hf : Far s base len) (hX : s.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 X) (ho : o + 4 * i + 4 ≤ size)
    (hi : 4 * i + 4 ≤ 4096) (hl : X + 4 * i + 4 ≤ len) (b : Bool)
    (hc : s.gpr .r10 = if b then BitVec.allOnes 32 else 0) :
    WP isa (.block (scanWord o i)) s fun t =>
      w32 t.mem base (o + 4 * i) = (if b then w32 s.mem base (X + 4 * i) else w32 s.mem base (o + 4 * i)) ∧
      Rest [.r4, .r5] s t ∧ Outside base (o + 4 * i) 4 s.mem t.mem := by
  have hn := hs.nowrap
  unfold scanWord
  refine wp_ldr (hs.off_lt (by omega_using [ho])) (hs.ea (by omega_using [ho])) (hs.read ho) fun s₁ u₁ => ?_
  have k₁ : Rest [.r4] s s₁ := u₁.rest (by simp)
  have hs₁ := hs.of_rest k₁ (by decide)
  have hf₁ := hf.of_rest k₁
  have hX₁ : s₁.gpr .r8 = s₁.gpr .r12 + BitVec.ofNat 32 X := by
    rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), hX]
  refine wp_ldr (by omega_using [hi]) (hf₁.ea_reg hs₁ hX₁ (by omega_using [hl]))
    (hf₁.read (d := X + 4 * i) (n := 4) (by omega_using [hl])) fun s₂ u₂ =>
    wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have k₅ : Rest [.r4, .r5] s s₅ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp)))))
  have hs₅ := hs.of_rest k₅ (by decide)
  refine wp_str (hs.off_lt (by omega_using [ho])) (hs₅.ea (by omega_using [ho])) (hs₅.write ho)
    fun s₆ m₆ => WP.block_nil ?_
  have a₂ : s₂.gpr .r4 = s.mem.readW (off base (o + 4 * i)) 32 := by
    rw [u₂.other .r4 (by decide), u₁.gpr]
  have d₂ : s₂.gpr .r5 = s.mem.readW (off base (X + 4 * i)) 32 := by rw [u₂.gpr, u₁.mem]
  have c₂ : s₂.gpr .r10 = s.gpr .r10 := by
    rw [u₂.other .r10 (by decide), u₁.other .r10 (by decide)]
  have d₃ : s₃.gpr .r5 = s.mem.readW (off base (X + 4 * i)) 32 ^^^ s.mem.readW (off base (o + 4 * i)) 32 := by
    rw [u₃.gpr, dpVal, d₂, a₂]
  have d₄ : s₄.gpr .r5 = (s.mem.readW (off base (X + 4 * i)) 32 ^^^ s.mem.readW (off base (o + 4 * i)) 32) &&&
      (if b then BitVec.allOnes 32 else 0) := by
    rw [u₄.gpr, dpVal, d₃, u₃.other .r10 (by decide), c₂, hc]
  have v₅ : s₅.gpr .r4 = if b then s.mem.readW (off base (X + 4 * i)) 32
      else s.mem.readW (off base (o + 4 * i)) 32 := by
    rw [u₅.gpr, dpVal, d₄, u₄.other .r4 (by decide), u₃.other .r4 (by decide), a₂]
    exact select_val _ _ b
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨?_, k₅.trans (m₆.rest _), ?_⟩
  · rw [m₆.mem, w32_write_self, v₅]
    cases b <;> rfl
  · rw [m₆.mem, mem₅]; exact writeW32_outside _ _ _ (by omega_using [ho, hn])

/-- The `k` words of an entry. -/
theorem scanWords_ok {s : State} {base : Addr} {size len o X : Nat} (hs : Scr s base size)
    (hf : Far s base len) (hX : s.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 X) (b : Bool)
    (hc : s.gpr .r10 = if b then BitVec.allOnes 32 else 0) :
    ∀ k, o + 4 * k ≤ size → size ≤ X → X + 4 * k ≤ len → 4 * k ≤ 4096 →
    WP isa (.block ((List.range k).flatMap (scanWord o))) s fun t =>
      (∀ i < k, w32 t.mem base (o + 4 * i) =
        if b then w32 s.mem base (X + 4 * i) else w32 s.mem base (o + 4 * i)) ∧
      Rest [.r4, .r5] s t ∧ Outside base o (4 * k) s.mem t.mem
  | 0, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, ho, hX', hl, hk => by
    have hn := hf.nowrap
    have hsn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (scanWords_ok hs hf hX b hc k (by omega_using [ho]) hX'
      (by omega_using [hl]) (by omega_using [hk])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    have hf₁ := hf.of_rest k₁
    have hX₁ : s₁.gpr .r8 = s₁.gpr .r12 + BitVec.ofNat 32 X := by
      rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), hX]
    have hc₁ : s₁.gpr .r10 = if b then BitVec.allOnes 32 else 0 := by rw [k₁.gpr _ (by decide), hc]
    refine WP.mono (scanWord_ok (i := k) hs₁ hf₁ hX₁ (by omega_using [ho]) (by omega_using [hk])
      (by omega_using [hl]) b hc₁) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
    refine ⟨fun i hi => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega_using [])).trans (O₂.mono (by omega_using []) (by omega_using []))⟩
    by_cases hik : i < k
    · rw [O₂.w32 (by omega_using [hik]) (by omega_using [ho, hsn, hik]), e₁ i hik]
    · have ei : i = k := by omega_using [hi, hik]
      subst ei
      rw [v₂, O₁.w32 (d := X + 4 * i) (by omega_using [ho, hX']) (by omega_using [hl, hn]),
        O₁.w32 (d := o + 4 * i) (by omega_using []) (by omega_using [ho, hsn])]

/-- The scan's invariant before entry `m`: `r8` is at it, `r7` is `m`, and
the slots hold the words of entry `a` if it is below `m`. -/
structure ScanInv (base : Addr) (o k tbl a : Nat) (s₀ : State) (m : Nat) (s : State) : Prop where
  ptr : s.gpr .r8 = s.gpr .r12 + BitVec.ofNat 32 (tbl + 4 * k * m)
  index : s.gpr .r7 = BitVec.ofNat 32 m
  keep : Rest [.r4, .r5, .r7, .r8, .r10] s₀ s
  unch : Outside base o (4 * k) s₀.mem s.mem
  val : a < m → ∀ i < k, w32 s.mem base (o + 4 * i) = w32 s₀.mem base (tbl + 4 * k * a + 4 * i)

/-- The scan of one entry. -/
theorem scanBody_ok {s₀ s : State} {base : Addr} {size len o k cnt tbl a m : Nat} (hs₀ : Scr s₀ base size)
    (hf₀ : Far s₀ base len) (ga : s₀.gpr .r9 = BitVec.ofNat 32 a) (ha : a < cnt) (hcnt : cnt < 2 ^ 31)
    (ho : o + 4 * k ≤ size) (ht : size ≤ tbl) (hl : tbl + 4 * k * cnt ≤ len) (hk : 4 * k ≤ 4096)
    (ek : encodable (BitVec.ofNat 32 (4 * k)) = true) (ec : encodable (BitVec.ofNat 32 cnt) = true)
    (hm : m < cnt) (I : ScanInv base o k tbl a s₀ m s) :
    WP isa (.block (scanBody o k cnt)) s fun t =>
      ScanInv base o k tbl a s₀ (m + 1) t ∧ t.z = decide (m + 1 = cnt) := by
  have hn := hf₀.nowrap
  have hs := hs₀.of_rest I.keep (by decide)
  have hf := hf₀.of_rest I.keep
  have hmul : 4 * k * m + 4 * k ≤ 4 * k * cnt := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hm
  unfold scanBody
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (TComb.eqMask_ok (op2_reg s .r7)) fun s₁ ⟨v₁, k₁, mem₁⟩ => ?_
  have cm₁ : s₁.gpr .r10 = if decide (a = m) then BitVec.allOnes 32 else 0 := by
    rw [v₁, I.keep.gpr _ (by decide), ga, I.index, TComb.equality_mask
      (by rw [BitVec.toNat_ofNat]; omega_using [ha, hcnt]) (by rw [BitVec.toNat_ofNat]; omega_using [hm, hcnt])]
    simp only [TComb.ofNat32_eq (by omega_using [ha, hcnt] : a < 2 ^ 32) (by omega_using [hm, hcnt] : m < 2 ^ 32),
      decide_eq_true_eq]
  have hs₁ := hs.of_rest k₁ (by decide)
  have hf₁ := hf.of_rest k₁
  have hX₁ : s₁.gpr .r8 = s₁.gpr .r12 + BitVec.ofNat 32 (tbl + 4 * k * m) := by
    rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), I.ptr]
  refine VG.Proof.X25519.Arm.WP.append (scanWords_ok hs₁ hf₁ hX₁ (decide (a = m)) cm₁ k ho
    (by omega_using [ht]) (by omega_using [hl, hmul]) hk) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  have k₁₂ : Rest [.r4, .r5, .r10] s s₂ := (k₁.mono (by simp)).trans (k₂.mono (by simp))
  refine wp_dp (op2_imm ek) fun s₃ u₃ => wp_dp (op2_imm (by decide)) fun s₄ u₄ =>
    wp_cmp (op2_imm ec) fun s₅ f₅ z₅ => WP.block_nil ?_
  have k₃₅ : Rest [.r7, .r8] s₂ s₅ := (u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (f₅.rest _))
  have k₅ : Rest [.r4, .r5, .r7, .r8, .r10] s s₅ := (k₁₂.mono (by simp)).trans (k₃₅.mono (by simp))
  have mem₅ : s₅.mem = s₂.mem := by rw [f₅.mem, u₄.mem, u₃.mem]
  have g₇ : s₄.gpr .r7 = BitVec.ofNat 32 (m + 1) := by
    rw [u₄.gpr, dpVal, u₃.other .r7 (by decide), k₁₂.gpr .r7 (by decide), I.index]
    exact (BitVec.ofNat_add _ _).symm
  refine ⟨⟨?_, by rw [f₅.gpr, g₇], I.keep.trans k₅, ?_, fun ham i hi => ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other .r8 (by decide), u₃.gpr, dpVal, k₁₂.gpr .r8 (by decide), I.ptr,
      u₄.other .r12 (by decide), u₃.other .r12 (by decide), k₁₂.gpr .r12 (by decide), BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.mul_succ, Nat.add_assoc]
  · rw [mem₅]; rw [mem₁] at O₂; exact I.unch.trans O₂
  · rw [mem₅, v₂ i hi, mem₁]
    by_cases h : a = m
    · subst h
      simp only [decide_true, ↓reduceIte]
      exact I.unch.w32 (by omega_using [ho, ht]) (by omega_using [hl, hn, hmul, hi])
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact I.val (by omega_using [ham, h]) i hi
  · rw [z₅, g₇]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    change BitVec.ofNat 32 (m + 1) - BitVec.ofNat 32 cnt = 0#32 ↔ m + 1 = cnt
    rw [TComb.sub_zero_iff, TComb.ofNat32_eq (by omega_using [hm, hcnt]) (by omega_using [hcnt])]

/-- `scan o k cnt tbl`: the slots at `o` hold the `k` words of entry `a`,
the number in `r9`, of the table at `tbl`, past the working space; only they
and `r4`, `r5`, `r7`, `r8` and `r10` change. -/
theorem scan_ok {s : State} {base : Addr} {size len o k cnt tbl a : Nat} (hs : Scr s base size)
    (hf : Far s base len) (ga : s.gpr .r9 = BitVec.ofNat 32 a) (ha : a < cnt) (hcnt : cnt < 2 ^ 31)
    (ho : o + 4 * k ≤ size) (ht : size ≤ tbl) (hl : tbl + 4 * k * cnt ≤ len) (hk : 4 * k ≤ 4096)
    (ht16 : tbl < 2 ^ 16) (ek : encodable (BitVec.ofNat 32 (4 * k)) = true)
    (ec : encodable (BitVec.ofNat 32 cnt) = true) :
    WP isa (scan o k cnt tbl) s fun t =>
      (∀ i < k, w32 t.mem base (o + 4 * i) = w32 s.mem base (tbl + 4 * k * a + 4 * i)) ∧
      Rest [.r4, .r5, .r7, .r8, .r10] s t ∧ Outside base o (4 * k) s.mem t.mem := by
  rw [scan]
  refine WP.seq (wp_farPtr ht16 (by decide) fun s₁ k₁ m₁ p₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ =>
    WP.block_nil ?_)
  have k₂ : Rest [.r4, .r5, .r7, .r8, .r10] s s₂ := (k₁.mono (by simp)).trans (u₂.rest (by simp))
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, m₁]
  have hs₂ := hs.of_rest k₂ (by decide)
  have hf₂ := hf.of_rest k₂
  refine upLoop_ok (Inv := fun m t => ScanInv base o k tbl a s₂ m t) (n := cnt) (i := 0)
    (fun m t _ hm I => scanBody_ok hs₂ hf₂ (by rw [k₂.gpr _ (by decide), ga]) ha hcnt ho ht hl hk ek ec hm I)
    (fun t I => ⟨fun i hi => ?_, k₂.trans I.keep, ?_⟩) (by omega_using [ha]) ?_
  · exact ⟨by rw [u₂.other _ (by decide), p₁, u₂.other _ (by decide), Nat.mul_zero, Nat.add_zero], u₂.gpr,
      Rest.refl _ _, VG.Proof.Mont.Outside.refl _ _ _ _, fun h => absurd h (Nat.not_lt_zero _)⟩
  · rw [I.val ha i hi, m₂]
  · rw [← m₂]; exact I.unch

end VG.Proof.Weierstrass.Arm
