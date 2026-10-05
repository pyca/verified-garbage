import VerifiedGarbage.Proof.Weierstrass.X86_64.InvStep
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Weierstrass.InvMask

/-!
# Inversion by divsteps on x86-64: numbers of several words

The operations of a batch on words of the working space, as numbers: the
mask of a word's sign (`maskOf_ok`), a masked copy (`maskCopy_ok`), the
signed linear combination `w [x] + w' [y]` (`lin_ok`, from the wide
Montgomery multiplication's rows), and the arithmetic shift by 59
(`shr59_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-! ## Masks -/

/-- The mask of a word's sign. -/
def smask (x : BitVec 64) : BitVec 64 := 0 - x >>> 63

theorem smask_toNat (x : BitVec 64) : (smask x).toNat = sgnW x := by
  rw [smask, BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  unfold sgnW; split <;> simp <;> omega

theorem smask_isMask (x : BitVec 64) : IsMask (smask x) := by
  have hv := smask_toNat x
  unfold sgnW at hv; split at hv
  · exact Or.inr (BitVec.eq_of_toNat_eq (by rw [hv, BitVec.toNat_allOnes]))
  · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [hv]; rfl))

/-- `v` masked by a word's sign: `v` if it is negative. -/
theorem masked_smask (x : BitVec 64) (v : Nat) : masked (smask x) v = if 2 ^ 63 ≤ x.toNat then v else 0 := by
  have hv := smask_toNat x
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have e : smask x = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by
      rw [hv, BitVec.toNat_allOnes]; unfold sgnW; simp only [h, ↓reduceIte])
    simp only [masked, e, h, ↓reduceIte]
  · have e : smask x ≠ BitVec.allOnes 64 := fun e => by
      rw [e, BitVec.toNat_allOnes] at hv; unfold sgnW at hv; simp only [h, ↓reduceIte] at hv
      exact absurd hv (by decide)
    simp only [masked, e, h, ↓reduceIte]

/-- `d = ` the mask of `src`'s sign, through `rax`. -/
theorem maskOf_ok (s : State) {d src : Reg} (hd : d ≠ .rax) :
    WP isa (.block (maskOf d src)) s fun t =>
      t.gpr d = smask (s.gpr src) ∧ Keeps [d, .rax] s t := by
  irun [maskOf, RegUpd.gpr_setReg_self]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [hd, ite_false, smask]
    rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

/-! ## Masked copies -/

/-- `[dst] = [src] & m` (`k` words). -/
theorem maskCopy_ok {base : Addr} {size : Nat} {m : Reg} (hm : m ≠ .r8) :
    ∀ (k : Nat) {s : State} {dst src : Nat}, Scr s base size → IsMask (s.gpr m) →
      dst + 8 * k ≤ size → src + 8 * k ≤ size → (dst + 8 * k ≤ src ∨ src + 8 * k ≤ dst) →
      WP isa (.block (maskCopy m dst src k)) s fun t =>
        wordsVal t.mem base dst k = masked (s.gpr m) (wordsVal s.mem base src k) ∧
        KeepRegs [.r8] s t ∧ Outside base dst (8 * k) s.mem t.mem
  | 0, s, _, _, _, _, _, _, _ => WP.block_nil ⟨by simp [wordsVal, masked], ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, s, dst, src, hs, hmask, hdst, hsrc, hsep => by
    have hn := hs.nowrap
    rw [maskCopy, WP.block_append_iff]
    have h1 : WP isa (.block [.mov .r8 (.mem (sc src)), .alu .and .r8 (.reg m), .store (sc dst) .r8]) s
        fun t => t.mem = s.mem.writeW (off base dst) (word s.mem base src &&& s.gpr m) ∧ KeepRegs [.r8] s t := by
      rw [← List.singleton_append, WP.block_append_iff]
      refine WP.mono (movMem_ok hs .r8 (d := src) (by omega)) fun u ⟨lu, _, ku⟩ => ?_
      rw [← List.singleton_append, WP.block_append_iff]
      have hmu : u.gpr m = s.gpr m := ku.1 m (by simp [hm])
      have ha : WP isa (.block [.alu .and .r8 (.reg m)]) u fun v =>
          v.gpr .r8 = word s.mem base src &&& s.gpr m ∧ Keeps [.r8] u v := by
        irun [hmu, lu]
        exact ⟨fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
      refine WP.mono ha fun v ⟨av, kv⟩ => ?_
      have hsv := (hs.of_keeps ku (by decide)).of_keeps kv (by decide)
      refine WP.mono (storeReg_ok hsv .r8 (d := dst) (by omega)) fun t ⟨mt, gt, _, kt⟩ => ⟨?_, ?_⟩
      · rw [mt, av, kv.2.1, ku.2.1]
      · exact ((Keeps.regs ku).trans (Keeps.regs kv)).trans (kt.mono (by decide))
    refine WP.mono h1 fun s₁ ⟨m₁, k₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base dst 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega)
    have hm₁ : s₁.gpr m = s.gpr m := k₁.gpr m (by simp [hm])
    refine WP.mono (maskCopy_ok hm k hs₁ (dst := dst + 8) (src := src + 8) (by rw [hm₁]; exact hmask)
      (by omega) (by omega) (by omega)) fun t ⟨e, kt, Ot⟩ => ?_
    refine ⟨?_, k₁.trans kt, fun x hx => by rw [Ot x (by omega), O₁ x (by omega)]⟩
    have hS : wordsVal s₁.mem base (src + 8) k = wordsVal s.mem base (src + 8) k :=
      O₁.wordsVal (by omega) (by omega)
    have hw : word t.mem base dst = word s₁.mem base dst := Ot.word (by omega) (by omega)
    rw [hm₁, hS] at e
    simp only [wordsVal]
    rw [hw, e, m₁, word_writeW_self, and_mask hmask, ← masked_add]

/-! ## The signed linear combination -/

/-- `rcx = src`. -/
theorem movRcx_ok (s : State) (src : Reg) :
    WP isa (.block [.mov .rcx (.reg src)]) s fun t => t.gpr .rcx = s.gpr src ∧ Keeps [.rcx] s t := by
  irun
  exact ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩

/-- `[T] -= 2^64 ([x] & mask(w))` modulo `2^(64 K)`, the masked words copied to
`[U]` first: `[T] + 2^64 masked = [T]₀` modulo `2^(64 K)`. -/
theorem subSh_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (w : Reg) {T x U K : Nat} (hK : 2 ≤ K) (hT : T + 8 * K ≤ size)
    (hx : x + 8 * (K - 1) ≤ size) (hU : U + 8 * (K - 1) ≤ size)
    (hUT : U + 8 * (K - 1) ≤ T ∨ T + 8 * K ≤ U) (hUx : U + 8 * (K - 1) ≤ x ∨ x + 8 * (K - 1) ≤ U) :
    WP isa (.block (maskOf .r13 w ++ maskCopy .r13 U x (K - 1) ++ chainW .sub .sbb (K - 1) (T + 8) (T + 8) U)) s
      fun t =>
        (wordsVal t.mem base T K + 2 ^ 64 * masked (smask (s.gpr w)) (wordsVal s.mem base x (K - 1))) %
            2 ^ (64 * K) = wordsVal s.mem base T K % 2 ^ (64 * K) ∧
        KeepRegs [.rax, .r8, .r13] s t ∧ Unch base [(T, 8 * K), (U, 8 * (K - 1))] s.mem t.mem := by
  have hn := hs.nowrap
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (maskOf_ok s (d := .r13) (src := w) (by decide)) fun s₁ ⟨g₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maskCopy_ok (m := .r13) (by decide) (K - 1) hs₁ (dst := U) (src := x)
    (by rw [g₁]; exact smask_isMask _) hU hx hUx) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain ⟨L, rfl⟩ : ∃ L, K = L + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at e₂ O₂ hx hU hUT hUx ⊢
  refine WP.mono (chainWSub_ok L hs₂ (op := .sub) (c := false) (t := T + 8) (a := T + 8) (b := U)
    (.inl ⟨rfl, rfl⟩) (.inl (by omega)) (by omega) (by omega) (by omega) (.inl rfl) (by
      rcases hUT with h | h
      · exact .inr (.inl (by omega))
      · exact .inr (.inr (by omega)))) fun t ⟨c, _, e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans (k₃.mono (by decide))),
    ?_⟩
  · -- The words of `T`: the lowest kept, the others less the masked ones.
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    have hw0 : word t.mem base T = word s.mem base T := by
      rw [O₃.word (by omega) (by omega), O₂.word (by omega) (by omega), hm₁]
    have hT₂ : wordsVal s₂.mem base (T + 8) L = wordsVal s.mem base (T + 8) L := by
      rw [O₂.wordsVal (by omega) (by omega), hm₁]
    rw [hm₁, g₁] at e₂
    simp only [Bool.toNat_false, Nat.add_zero, hT₂, e₂] at e₃
    simp only [wordsVal]
    rw [hw0, pow64_succ]
    have : (word s.mem base T).toNat + 2 ^ 64 * wordsVal t.mem base (T + 8) L +
        2 ^ 64 * masked (smask (s.gpr w)) (wordsVal s.mem base x L) =
        (word s.mem base T).toNat + 2 ^ 64 * wordsVal s.mem base (T + 8) L +
          2 ^ 64 * (2 ^ (64 * L) * c.toNat) := by
      rw [Nat.add_assoc, ← Nat.mul_add, e₃, Nat.mul_add, ← Nat.add_assoc]
    rw [this, ← Nat.mul_assoc, Nat.add_mul_mod_self_left]
  · rw [← k₁.2.1]
    refine ((O₂.trans (Outside.refl _ _ _ _)).unch.trans (O₃.mono (o' := T) (n' := 8 * (L + 1)) (by omega)
      (by omega)).unch).mono fun v hv => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
    rcases hv with h | h <;> simp [h]

/-- The products' code of `lin`. -/
def prods (w w' : Reg) (t x y k K : Nat) : List Instr :=
  zeroWords K t ++
  [.mov .rcx (.reg w)] ++ memRow k t x ++ (if k < K then [.store (sc (t + 8 * k)) .rbp] else []) ++
  [.mov .rcx (.reg w')] ++ memRow k t y ++
  (if k < K then [.mov .r8 (.mem (sc (t + 8 * k))), .alu .add .r8 (.reg .rbp), .store (sc (t + 8 * k)) .r8]
    else [])

theorem lin_eq (w w' : Reg) (t x y U k K : Nat) :
    lin w w' t x y U k K = prods w w' t x y k K ++
      ((maskOf .r13 w ++ maskCopy .r13 U x (K - 1) ++ chainW .sub .sbb (K - 1) (t + 8) (t + 8) U) ++
        (maskOf .r13 w' ++ maskCopy .r13 U y (K - 1) ++ chainW .sub .sbb (K - 1) (t + 8) (t + 8) U)) := by
  simp only [lin, prods, List.append_assoc]

/-- `[t + 8 k] += rbp`, through `r8`. -/
theorem addTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .r8 (.mem (sc d)), .alu .add .r8 (.reg .rbp), .store (sc d) .r8]) s fun t =>
      t.mem = s.mem.writeW (off base d) (word s.mem base d + s.gpr .rbp) ∧ KeepRegs [.r8] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 hd) fun u ⟨lu, _, ku⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have ha : WP isa (.block [.alu .add .r8 (.reg .rbp)]) u fun v =>
      v.gpr .r8 = word s.mem base d + s.gpr .rbp ∧ Keeps [.r8] u v := by
    irun [lu, ku.1 .rbp (by decide)]
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono ha fun v ⟨av, kv⟩ => ?_
  have hsv := (hs.of_keeps ku (by decide)).of_keeps kv (by decide)
  refine WP.mono (storeReg_ok hsv .r8 hd) fun t ⟨mt, _, _, kt⟩ => ⟨?_, ?_⟩
  · rw [mt, av, kv.2.1, ku.2.1]
  · exact ((Keeps.regs ku).trans (Keeps.regs kv)).trans (kt.mono (by decide))

/-- `wordsVal` of the first `k ≤ K` of `K` zero words. -/
theorem wordsVal_zero_le {m : Mem} {base : Addr} {d k K : Nat} (h : wordsVal m base d K = 0) (hk : k ≤ K) :
    wordsVal m base d k = 0 := by
  induction K generalizing d k with
  | zero => rw [Nat.le_zero.mp hk]; rfl
  | succ K ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [wordsVal] at h ⊢
      have h1 : (word m base d).toNat = 0 := by omega
      have h2 : wordsVal m base (d + 8) K = 0 := by
        rcases Nat.eq_zero_or_pos (wordsVal m base (d + 8) K) with h' | h'
        · exact h'
        · omega
      rw [h1, ih h2 (by omega)]

/-- A top word modulo `2^64`, under `X = 2^(64 k)` above `A < X`. -/
theorem mod_top (A X c : Nat) : (A + X * (c % 2 ^ 64)) % (X * 2 ^ 64) = (A + X * c) % (X * 2 ^ 64) := by
  conv => rhs; rw [← Nat.mod_add_div c (2 ^ 64), Nat.mul_add, ← Nat.add_assoc, ← Nat.mul_assoc]
  rw [Nat.add_mul_mod_self_left]

/-- The products of `lin`: `[t] = w [x] + w' [y]` modulo `2^(64 K)`, unsigned. -/
theorem prods_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi])
    {T x y k K : Nat} (hkK : k ≤ K) (hk' : K ≤ k + 1)
    (hx : x + 8 * k ≤ size) (hy : y + 8 * k ≤ size) (hT : T + 8 * K ≤ size)
    (hTx : T + 8 * K ≤ x ∨ x + 8 * k ≤ T) (hTy : T + 8 * K ≤ y ∨ y + 8 * k ≤ T) :
    WP isa (.block (prods w w' T x y k K)) s fun t =>
      wordsVal t.mem base T K % 2 ^ (64 * K) =
        ((s.gpr w).toNat * wordsVal s.mem base x k + (s.gpr w').toNat * wordsVal s.mem base y k) %
          2 ^ (64 * K) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8] s t ∧ Outside base T (8 * K) s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw hw'
  simp only [prods, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zeroWords_ok hs (k := K) (t := T) hT) fun s₁ ⟨z₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movRcx_ok s₁ w) fun s₂ ⟨c₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (memRow_ok hs₂ (k := k) (t := T) (d := x) (by omega) hx (by omega)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have hX : wordsVal s₂.mem base x k = wordsVal s.mem base x k := by
    rw [k₂.2.1]; exact O₁.wordsVal (by omega) (by omega)
  have hY₃ : wordsVal s₃.mem base y k = wordsVal s.mem base y k := by
    rw [O₃.wordsVal (by omega) (by omega), k₂.2.1]; exact O₁.wordsVal (by omega) (by omega)
  have hT₂ : wordsVal s₂.mem base T k = 0 := by rw [k₂.2.1]; exact wordsVal_zero_le z₁ hkK
  rw [hT₂, Nat.zero_add, c₂, k₁.gpr w (by simp [hw.2.2.2.2.1]), hX] at e₃
  have hw'₃ : s₃.gpr w' = s.gpr w' := by
    rw [k₃.gpr w' (by simp [hw'.2.2.2.2.1, hw'.1, hw'.2.2.1, hw'.2.2.2.1]), k₂.1 w' (by simp [hw'.2.1]),
      k₁.gpr w' (by simp [hw'.2.2.2.2.1])]
  by_cases hk : k < K
  · -- `K = k + 1`: the carry words stored on top.
    have hK : K = k + 1 := by omega
    subst hK
    simp only [hk, ↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (storeReg_ok hs₃ .rbp (d := T + 8 * k) (by omega)) fun s₄ ⟨m₄, g₄, _, k₄⟩ => ?_
    have hs₄ := hs₃.of_keepRegs k₄ (by decide)
    have O₄ : Outside base (T + 8 * k) 8 s₃.mem s₄.mem := by rw [m₄]; exact writeW_outside _ _ _ (by omega)
    rw [WP.block_append_iff]
    refine WP.mono (movRcx_ok s₄ w') fun s₅ ⟨c₅, k₅⟩ => ?_
    have hs₅ := hs₄.of_keeps k₅ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (memRow_ok hs₅ (k := k) (t := T) (d := y) (by omega) hy (by omega))
      fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
    have hs₆ := hs₅.of_keepRegs k₆ (by decide)
    refine WP.mono (addTop_ok hs₆ (d := T + 8 * k) (by omega)) fun t ⟨m₇, k₇⟩ => ?_
    refine ⟨?_, ((((k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (k₃.mono (by decide))).trans ((k₄.mono (by decide)).trans ((Keeps.regs k₅).mono (by decide)))).trans
      ((k₆.mono (by decide)).trans (k₇.mono (by decide))), fun a ha => ?_⟩
    · have hY₅ : wordsVal s₅.mem base y k = wordsVal s.mem base y k := by
        rw [k₅.2.1, O₄.wordsVal (by omega) (by omega), hY₃]
      have hT₅ : wordsVal s₅.mem base T k = wordsVal s₃.mem base T k := by
        rw [k₅.2.1, O₄.wordsVal (by omega) (by omega)]
      rw [hT₅, hY₅, c₅, k₄.gpr w' (by simp), hw'₃] at e₆
      have htop₆ : word s₆.mem base (T + 8 * k) = s₃.gpr .rbp := by
        rw [O₆.word (by omega) (by omega), k₅.2.1, m₄, word_writeW_self]
      rw [m₇, wordsVal_succ_top, word_writeW_self, (writeW_outside s₆.mem base (d := T + 8 * k) _
        (by omega)).wordsVal (by omega) (by omega), htop₆, BitVec.toNat_add]
      have key : wordsVal s₆.mem base T k + 2 ^ (64 * k) * ((s₃.gpr .rbp).toNat + (s₆.gpr .rbp).toNat) =
          (s.gpr w).toNat * wordsVal s.mem base x k + (s.gpr w').toNat * wordsVal s.mem base y k := by
        rw [Nat.mul_add]; omega
      rw [pow64_succ, Nat.mul_comm (2 ^ 64) (2 ^ (64 * k)), mod_top, key]
    · have O₇ : Outside base (T + 8 * k) 8 s₆.mem t.mem := by rw [m₇]; exact writeW_outside _ _ _ (by omega)
      rw [O₇ a (by omega), O₆ a (by omega), k₅.2.1, O₄ a (by omega), O₃ a (by omega), k₂.2.1, O₁ a ha]
  · -- `K = k`: the carry words dropped.
    have hK : K = k := by omega
    subst hK
    simp only [hk, ↓reduceIte, List.append_nil, List.nil_append]
    rw [WP.block_append_iff]
    refine WP.mono (movRcx_ok s₃ w') fun s₅ ⟨c₅, k₅⟩ => ?_
    have hs₅ := hs₃.of_keeps k₅ (by decide)
    refine WP.mono (memRow_ok hs₅ (t := T) (d := y) (by omega) hy (by omega)) fun t ⟨e₆, k₆, O₆⟩ => ?_
    refine ⟨?_, (((k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (k₃.mono (by decide))).trans (((Keeps.regs k₅).mono (by decide)).trans (k₆.mono (by decide))),
      fun a ha => ?_⟩
    · rw [k₅.2.1, hY₃, c₅, hw'₃] at e₆
      rw [show (s.gpr w).toNat * wordsVal s.mem base x K + (s.gpr w').toNat * wordsVal s.mem base y K =
          wordsVal t.mem base T K + 2 ^ (64 * K) * ((s₃.gpr .rbp).toNat + (t.gpr .rbp).toNat) by
        rw [Nat.mul_add]; omega, Nat.add_mul_mod_self_left]
    · rw [O₆ a ha, k₅.2.1, O₃ a ha, k₂.2.1, O₁ a ha]

/-- Apart from each range of a list written out. -/
local macro "apart" : tactic => `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
  forall_eq_or_imp, forall_eq] <;> omega))

/-- `[T] = w [x] + w' [y] - 2^64 (([x] & mask(w)) + ([y] & mask(w')))` modulo
`2^(64 K)` (`[x]`, `[y]` of `k` words, `K - 1 ≤ k ≤ K`). -/
theorem lin_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {T x y U k K : Nat} (hkK : k ≤ K) (hK : 2 ≤ K) (hk' : K ≤ k + 1)
    (hx : x + 8 * k ≤ size) (hy : y + 8 * k ≤ size) (hT : T + 8 * K ≤ size) (hU : U + 8 * (K - 1) ≤ size)
    (hTx : T + 8 * K ≤ x ∨ x + 8 * k ≤ T) (hTy : T + 8 * K ≤ y ∨ y + 8 * k ≤ T)
    (hUT : U + 8 * (K - 1) ≤ T ∨ T + 8 * K ≤ U) (hUx : U + 8 * (K - 1) ≤ x ∨ x + 8 * k ≤ U)
    (hUy : U + 8 * (K - 1) ≤ y ∨ y + 8 * k ≤ U) :
    WP isa (.block (lin w w' T x y U k K)) s fun t =>
      (wordsVal t.mem base T K + 2 ^ 64 * (masked (smask (s.gpr w)) (wordsVal s.mem base x (K - 1)) +
        masked (smask (s.gpr w')) (wordsVal s.mem base y (K - 1)))) % 2 ^ (64 * K) =
      ((s.gpr w).toNat * wordsVal s.mem base x k + (s.gpr w').toNat * wordsVal s.mem base y k) % 2 ^ (64 * K) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧ Unch base [(T, 8 * K), (U, 8 * (K - 1))] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw hw'
  rw [lin_eq, WP.block_append_iff]
  refine WP.mono (prods_ok hs (w := w) (w' := w') (by simp [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1,
    hw.2.2.2.2.2.1]) (by simp [hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, hw'.2.2.2.2.1, hw'.2.2.2.2.2.1])
    hkK hk' hx hy hT hTx hTy) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (subSh_ok hs₁ w (T := T) (x := x) (U := U) hK hT (by omega) hU hUT (by omega))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (subSh_ok hs₂ w' (T := T) (x := y) (U := U) hK hT (by omega) hU hUT (by omega))
    fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide)),
      (O₁.unch.trans (O₂.trans O₃)).mono fun v hv => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
        rcases hv with h | h | h | h | h <;> simp [h]⟩
  have gw : s₁.gpr w = s.gpr w := k₁.gpr w (by simp [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1])
  have gw' : s₂.gpr w' = s.gpr w' := by
    rw [k₂.gpr w' (by simp [hw'.1, hw'.2.2.2.2.1, hw'.2.2.2.2.2.2]),
      k₁.gpr w' (by simp [hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, hw'.2.2.2.2.1])]
  have mx : wordsVal s₁.mem base x (K - 1) = wordsVal s.mem base x (K - 1) :=
    O₁.wordsVal (by omega) (by omega)
  have my : wordsVal s₂.mem base y (K - 1) = wordsVal s.mem base y (K - 1) := by
    rw [O₂.wordsVal (by apart) (by omega)]; exact O₁.wordsVal (by omega) (by omega)
  rw [gw, mx] at e₂
  rw [gw', my] at e₃
  generalize 2 ^ (64 * K) = M at *
  generalize masked (smask (s.gpr w)) (wordsVal s.mem base x (K - 1)) = a at *
  generalize masked (smask (s.gpr w')) (wordsVal s.mem base y (K - 1)) = b at *
  rw [show wordsVal t.mem base T K + 2 ^ 64 * (a + b) = (wordsVal t.mem base T K + 2 ^ 64 * b) + 2 ^ 64 * a by
    rw [Nat.mul_add]; omega, ← Nat.mod_add_mod, e₃, Nat.mod_add_mod, e₂, e₁]

/-! ## The shift by 59 -/

/-- `r8 *= 32`. -/
theorem shl5_ok (s : State) :
    WP isa (.block shl5) s fun t => (t.gpr .r8).toNat = (s.gpr .r8).toNat * 32 % 2 ^ 64 ∧ Keeps [.r8] s t := by
  irun [shl5, List.replicate]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [BitVec.toNat_add]; omega
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- A word of the shift: `(lo >> 59) + 32 hi` does not wrap. -/
theorem shr_word (lo y : BitVec 64) {hi : Nat} (hy : y.toNat = hi * 32 % 2 ^ 64) :
    (lo >>> 59 + y).toNat = (lo.toNat / 2 ^ 59 + 2 ^ 5 * hi) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hy]
  have := lo.isLt
  omega

/-- `[d] = (rax >> 59) + 32 r8`. -/
theorem shrTail_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block (shrTail d)) s fun t =>
      (word t.mem base d).toNat = ((s.gpr .rax).toNat / 2 ^ 59 + 2 ^ 5 * (s.gpr .r8).toNat) % 2 ^ 64 ∧
      KeepRegs [.rax, .r8] s t ∧ Outside base d 8 s.mem t.mem := by
  have hn := hs.nowrap
  rw [shrTail, List.append_assoc, WP.block_append_iff]
  have h1 : WP isa (.block [.shift .shr .rax 59]) s fun t => t.gpr .rax = s.gpr .rax >>> 59 ∧ Keeps [.rax] s t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h1 fun s₁ ⟨a₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (shl5_ok s₁) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have h3 : WP isa (.block [.alu .add .rax (.reg .r8)]) s₂ fun t =>
      t.gpr .rax = s₂.gpr .rax + s₂.gpr .r8 ∧ Keeps [.rax] s₂ t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h3 fun s₃ ⟨a₃, k₃⟩ => ?_
  have hs₃ := ((hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
  refine WP.mono (storeReg_ok hs₃ .rax hd) fun t ⟨mt, _, _, kt⟩ => ⟨?_, ?_, ?_⟩
  · rw [mt, word_writeW_self, a₃, k₂.1 .rax (by decide), a₁,
      shr_word _ _ (by rw [c₂, k₁.1 .r8 (by decide)])]
  · exact ((((Keeps.regs k₁).mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      ((Keeps.regs k₃).mono (by decide))).trans (kt.mono (by decide))
  · rw [mt, k₃.2.1, k₂.2.1, k₁.2.1]; exact writeW_outside _ _ _ (by omega)

/-- `d = src`. -/
theorem movReg_ok (s : State) (d src : Reg) :
    WP isa (.block [.mov d (.reg src)]) s fun t => t.gpr d = s.gpr src ∧ Keeps [d] s t := by
  irun [RegUpd.gpr_setReg_self]
  exact ⟨fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩

/-- Words `0 … j - 1` of `[src] >> 59` (`j + 1 ≤ L` words of `[src]`). -/
theorem shrRows_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src L : Nat}
    (hsrc : src + 8 * L ≤ size) (hdst : dst + 8 * L ≤ size) (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) :
    ∀ j, j + 1 ≤ L → WP isa (.block ((List.range j).flatMap (shrStep dst src))) s fun t =>
      wordsVal t.mem base dst j = (wordsVal s.mem base src (j + 1) / 2 ^ 59) % 2 ^ (64 * j) ∧
      KeepRegs [.rax, .r8] s t ∧ Outside base dst (8 * j) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp only [wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one],
    ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (shrRows_ok hs hsrc hdst hsep j (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [shrStep, ← List.singleton_append, List.append_assoc, WP.block_append_iff]
    refine WP.mono (movMem_ok hs₁ .rax (d := src + 8 * j) (by omega)) fun s₂ ⟨l₂, _, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (movMem_ok hs₂ .r8 (d := src + 8 * (j + 1)) (by omega)) fun s₃ ⟨l₃, _, k₃⟩ => ?_
    have hs₃ := hs₂.of_keeps k₃ (by decide)
    refine WP.mono (shrTail_ok hs₃ (d := dst + 8 * j) (by omega)) fun t ⟨e, kt, Ot⟩ =>
      ⟨?_, ((k₁.trans ((Keeps.regs k₂).mono (by decide))).trans ((Keeps.regs k₃).mono (by decide))).trans kt,
        fun x hx => by rw [Ot x (by omega), k₃.2.1, k₂.2.1, O₁ x (by omega)]⟩
    have w₂ : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := O₁.word (by omega) (by omega)
    have w₃ : word s₂.mem base (src + 8 * (j + 1)) = word s.mem base (src + 8 * (j + 1)) := by
      rw [k₂.2.1]; exact O₁.word (by omega) (by omega)
    rw [wordsVal_succ_top, Ot.wordsVal (by omega) (by omega), k₃.2.1, k₂.2.1, e₁, e, k₃.1 .rax (by decide), l₂,
      l₃, w₂, w₃, wordsVal_succ_top s.mem base src (j + 1), wordsVal_succ_top s.mem base src j, pow64_succ,
      Nat.mul_comm (2 ^ 64) (2 ^ (64 * j))]
    exact (shr_arith j _ _ _ (wordsVal_lt _ _ _ _)).symm

/-- `[dst] = [src] >> 59`, arithmetic (`L ≥ 1` words). -/
theorem shr59_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst src L : Nat} (hL : 1 ≤ L)
    (hsrc : src + 8 * L ≤ size) (hdst : dst + 8 * L ≤ size) (hsep : dst + 8 * L ≤ src ∨ src + 8 * L ≤ dst) :
    WP isa (.block (shr59 dst src L)) s fun t =>
      wordsVal t.mem base dst L = (sext s.mem base src L / 2 ^ 59) % 2 ^ (64 * L) ∧
      KeepRegs [.rax, .rdx, .r8] s t ∧ Outside base dst (8 * L) s.mem t.mem := by
  have hn := hs.nowrap
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
  simp only [shr59, Nat.add_sub_cancel]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (shrRows_ok hs hsrc hdst hsep j (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movMem_ok hs₁ .rdx (d := src + 8 * j) (by omega)) fun s₂ ⟨l₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₂ (d := .r8) (src := .rdx) (by decide)) fun s₃ ⟨g₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movReg_ok s₃ .rax .rdx) fun s₄ ⟨g₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (shrTail_ok hs₄ (d := dst + 8 * j) (by omega)) fun t ⟨e, kt, Ot⟩ =>
    ⟨?_, (((k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (((Keeps.regs k₃).mono (by decide)).trans ((Keeps.regs k₄).mono (by decide)))).trans (kt.mono (by decide)),
      fun x hx => by rw [Ot x (by omega), k₄.2.1, k₃.2.1, k₂.2.1, O₁ x (by omega)]⟩
  have w₂ : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := O₁.word (by omega) (by omega)
  rw [wordsVal_succ_top, Ot.wordsVal (by omega) (by omega), k₄.2.1, k₃.2.1, k₂.2.1, e₁, e, g₄,
    k₄.1 .r8 (by decide), g₃, smask_toNat, k₃.1 .rdx (by decide), l₂, w₂, sext, Nat.add_sub_cancel,
    wordsVal_succ_top s.mem base src j, pow64_succ, Nat.mul_comm (2 ^ 64) (2 ^ (64 * j))]
  exact (shr_arith j _ _ _ (wordsVal_lt _ _ _ _)).symm

end VG.Proof.Weierstrass.X86_64
