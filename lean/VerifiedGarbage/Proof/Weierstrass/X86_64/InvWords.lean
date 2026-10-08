import VerifiedGarbage.Proof.Weierstrass.X86_64.InvStep
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Weierstrass.InvMask
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Inversion by divsteps on x86-64: numbers of several words

The operations of a batch on words of the working space, as numbers: the
mask of a word's sign (`maskOf_ok`), a masked copy (`maskCopy_ok`), the
signed linear combination `w [x] + w' [y]` (`lin_ok`, from the wide
Montgomery multiplication's rows; `linR_ok`, column by column in registers),
and the arithmetic shift by 59 (`shr59_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono toNat_ofBool)

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
      refine WP.mono (movMem_ok hs .r8 (d := src) (by omega_using [hsrc])) fun u ⟨lu, _, ku⟩ => ?_
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
      refine WP.mono (storeReg_ok hsv .r8 (d := dst) (by omega_using [hdst])) fun t ⟨mt, gt, _, kt⟩ => ⟨?_, ?_⟩
      · rw [mt, av, kv.2.1, ku.2.1]
      · exact ((Keeps.regs ku).trans (Keeps.regs kv)).trans (kt.mono (by decide))
    refine WP.mono h1 fun s₁ ⟨m₁, k₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have O₁ : Outside base dst 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by omega_using [hdst, hn])
    have hm₁ : s₁.gpr m = s.gpr m := k₁.gpr m (by simp [hm])
    refine WP.mono (maskCopy_ok hm k hs₁ (dst := dst + 8) (src := src + 8) (by rw [hm₁]; exact hmask)
      (by omega_using [hdst]) (by omega_using [hsrc]) (by omega_using [hsep])) fun t ⟨e, kt, Ot⟩ => ?_
    refine ⟨?_, k₁.trans kt, fun x hx => by rw [Ot x (by omega_using [hx]), O₁ x (by omega_using [hx])]⟩
    have hS : wordsVal s₁.mem base (src + 8) k = wordsVal s.mem base (src + 8) k :=
      O₁.wordsVal (by omega_using [hsep]) (by omega_using [hsrc, hn])
    have hw : word t.mem base dst = word s₁.mem base dst := Ot.word (by omega_using []) (by omega_using [hdst, hn])
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
  obtain ⟨L, rfl⟩ : ∃ L, K = L + 1 := ⟨K - 1, by omega_using [hK]⟩
  simp only [Nat.add_sub_cancel] at e₂ O₂ hx hU hUT hUx ⊢
  refine WP.mono (chainWSub_ok L hs₂ (op := .sub) (c := false) (t := T + 8) (a := T + 8) (b := U)
    (.inl ⟨rfl, rfl⟩) (.inl (by omega_using [hK])) (by omega_using [hT]) (by omega_using [hT]) (by omega_using [hU]) (.inl rfl) (by
      rcases hUT with h | h
      · exact .inr (.inl (by omega_using [h]))
      · exact .inr (.inr (by omega_using [h])))) fun t ⟨c, _, e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans (k₃.mono (by decide))),
    ?_⟩
  · -- The words of `T`: the lowest kept, the others less the masked ones.
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    have hw0 : word t.mem base T = word s.mem base T := by
      rw [O₃.word (by omega_using []) (by omega_using [hn, hT]), O₂.word (by omega_using [hUT]) (by omega_using [hn, hT]), hm₁]
    have hT₂ : wordsVal s₂.mem base (T + 8) L = wordsVal s.mem base (T + 8) L := by
      rw [O₂.wordsVal (by omega_using [hUT]) (by omega_using [hn, hT]), hm₁]
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
    refine ((O₂.trans (Outside.refl _ _ _ _)).unch.trans (O₃.mono (o' := T) (n' := 8 * (L + 1)) (by omega_using [])
      (by omega_using [])).unch).mono fun v hv => ?_
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
      have h1 : (word m base d).toNat = 0 := by omega_using [h]
      have h2 : wordsVal m base (d + 8) K = 0 := by
        rcases Nat.eq_zero_or_pos (wordsVal m base (d + 8) K) with h' | h'
        · exact h'
        · omega_using [h]
      rw [h1, ih h2 (by omega_using [hk])]

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
  refine WP.mono (memRow_ok hs₂ (k := k) (t := T) (d := x) (by omega_using [hkK, hT]) hx (by omega_using [hkK, hTx])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have hX : wordsVal s₂.mem base x k = wordsVal s.mem base x k := by
    rw [k₂.2.1]; exact O₁.wordsVal (by omega_using [hTx]) (by omega_using [hx, hn])
  have hY₃ : wordsVal s₃.mem base y k = wordsVal s.mem base y k := by
    rw [O₃.wordsVal (by omega_using [hkK, hTy]) (by omega_using [hy, hn]), k₂.2.1]; exact O₁.wordsVal (by omega_using [hTy]) (by omega_using [hy, hn])
  have hT₂ : wordsVal s₂.mem base T k = 0 := by rw [k₂.2.1]; exact wordsVal_zero_le z₁ hkK
  rw [hT₂, Nat.zero_add, c₂, k₁.gpr w (by simp [hw.2.2.2.2.1]), hX] at e₃
  have hw'₃ : s₃.gpr w' = s.gpr w' := by
    rw [k₃.gpr w' (by simp [hw'.2.2.2.2.1, hw'.1, hw'.2.2.1, hw'.2.2.2.1]), k₂.1 w' (by simp [hw'.2.1]),
      k₁.gpr w' (by simp [hw'.2.2.2.2.1])]
  by_cases hk : k < K
  · -- `K = k + 1`: the carry words stored on top.
    have hK : K = k + 1 := by omega_using [hk', hk]
    subst hK
    simp only [hk, ↓reduceIte]
    rw [WP.block_append_iff]
    refine WP.mono (storeReg_ok hs₃ .rbp (d := T + 8 * k) (by omega_using [hT])) fun s₄ ⟨m₄, g₄, _, k₄⟩ => ?_
    have hs₄ := hs₃.of_keepRegs k₄ (by decide)
    have O₄ : Outside base (T + 8 * k) 8 s₃.mem s₄.mem := by rw [m₄]; exact writeW_outside _ _ _ (by omega_using [hn, hT])
    rw [WP.block_append_iff]
    refine WP.mono (movRcx_ok s₄ w') fun s₅ ⟨c₅, k₅⟩ => ?_
    have hs₅ := hs₄.of_keeps k₅ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (memRow_ok hs₅ (k := k) (t := T) (d := y) (by omega_using [hT]) hy (by omega_using [hTy]))
      fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
    have hs₆ := hs₅.of_keepRegs k₆ (by decide)
    refine WP.mono (addTop_ok hs₆ (d := T + 8 * k) (by omega_using [hT])) fun t ⟨m₇, k₇⟩ => ?_
    refine ⟨?_, ((((k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (k₃.mono (by decide))).trans ((k₄.mono (by decide)).trans ((Keeps.regs k₅).mono (by decide)))).trans
      ((k₆.mono (by decide)).trans (k₇.mono (by decide))), fun a ha => ?_⟩
    · have hY₅ : wordsVal s₅.mem base y k = wordsVal s.mem base y k := by
        rw [k₅.2.1, O₄.wordsVal (by omega_using [hTy]) (by omega_using [hy, hn]), hY₃]
      have hT₅ : wordsVal s₅.mem base T k = wordsVal s₃.mem base T k := by
        rw [k₅.2.1, O₄.wordsVal (by omega_using []) (by omega_using [hn, hT])]
      rw [hT₅, hY₅, c₅, k₄.gpr w' (by simp), hw'₃] at e₆
      have htop₆ : word s₆.mem base (T + 8 * k) = s₃.gpr .rbp := by
        rw [O₆.word (by omega_using []) (by omega_using [hn, hT]), k₅.2.1, m₄, word_writeW_self]
      rw [m₇, wordsVal_succ_top, word_writeW_self, (writeW_outside s₆.mem base (d := T + 8 * k) _
        (by omega_using [hn, hT])).wordsVal (by omega_using []) (by omega_using [hn, hT]), htop₆, BitVec.toNat_add]
      have key : wordsVal s₆.mem base T k + 2 ^ (64 * k) * ((s₃.gpr .rbp).toNat + (s₆.gpr .rbp).toNat) =
          (s.gpr w).toNat * wordsVal s.mem base x k + (s.gpr w').toNat * wordsVal s.mem base y k := by
        rw [Nat.mul_add]; omega_using [e₃, e₆]
      rw [pow64_succ, Nat.mul_comm (2 ^ 64) (2 ^ (64 * k)), mod_top, key]
    · have O₇ : Outside base (T + 8 * k) 8 s₆.mem t.mem := by rw [m₇]; exact writeW_outside _ _ _ (by omega_using [hn, hT])
      rw [O₇ a (by omega_using [ha]), O₆ a (by omega_using [ha]), k₅.2.1, O₄ a (by omega_using [ha]), O₃ a (by omega_using [ha]), k₂.2.1, O₁ a ha]
  · -- `K = k`: the carry words dropped.
    have hK : K = k := by omega_using [hkK, hk]
    subst hK
    simp only [hk, ↓reduceIte, List.append_nil, List.nil_append]
    rw [WP.block_append_iff]
    refine WP.mono (movRcx_ok s₃ w') fun s₅ ⟨c₅, k₅⟩ => ?_
    have hs₅ := hs₃.of_keeps k₅ (by decide)
    refine WP.mono (memRow_ok hs₅ (t := T) (d := y) (by omega_using [hT]) hy (by omega_using [hTy])) fun t ⟨e₆, k₆, O₆⟩ => ?_
    refine ⟨?_, (((k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (k₃.mono (by decide))).trans (((Keeps.regs k₅).mono (by decide)).trans (k₆.mono (by decide))),
      fun a ha => ?_⟩
    · rw [k₅.2.1, hY₃, c₅, hw'₃] at e₆
      rw [show (s.gpr w).toNat * wordsVal s.mem base x K + (s.gpr w').toNat * wordsVal s.mem base y K =
          wordsVal t.mem base T K + 2 ^ (64 * K) * ((s₃.gpr .rbp).toNat + (t.gpr .rbp).toNat) by
        rw [Nat.mul_add]; omega_using [e₃, e₆], Nat.add_mul_mod_self_left]
    · rw [O₆ a ha, k₅.2.1, O₃ a ha, k₂.2.1, O₁ a ha]

/-- Apart from each range of a list written out. -/
local macro "apart" : tactic => `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false,
  forall_eq_or_imp, forall_eq] <;> omega))

set_option hygiene false in
/-- `omega` on the layout alone of `lin_ok` and `linR_ok`: first without its disjunctions,
which it would split, then with one. -/
local macro "lin_omega" : tactic =>
  `(tactic| first
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hTx]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hTy]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hUT]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hUx]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hn, hUy]
    | omega_using [hkK, hK, hk', hx, hy, hT, hU, hTx, hTy, hUT, hUx, hUy, hn])

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
  refine WP.mono (subSh_ok hs₁ w (T := T) (x := x) (U := U) hK hT (by lin_omega) hU hUT (by lin_omega))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (subSh_ok hs₂ w' (T := T) (x := y) (U := U) hK hT (by lin_omega) hU hUT (by lin_omega))
    fun t ⟨e₃, k₃, O₃⟩ => ⟨?_, ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide)),
      (O₁.unch.trans (O₂.trans O₃)).mono fun v hv => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
        rcases hv with h | h | h | h | h <;> simp [h]⟩
  have gw : s₁.gpr w = s.gpr w := k₁.gpr w (by simp [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1])
  have gw' : s₂.gpr w' = s.gpr w' := by
    rw [k₂.gpr w' (by simp [hw'.1, hw'.2.2.2.2.1, hw'.2.2.2.2.2.2]),
      k₁.gpr w' (by simp [hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, hw'.2.2.2.2.1])]
  have mx : wordsVal s₁.mem base x (K - 1) = wordsVal s.mem base x (K - 1) :=
    O₁.wordsVal (by lin_omega) (by lin_omega)
  have my : wordsVal s₂.mem base y (K - 1) = wordsVal s.mem base y (K - 1) := by
    rw [O₂.wordsVal (by apart) (by lin_omega)]; exact O₁.wordsVal (by lin_omega) (by lin_omega)
  rw [gw, mx] at e₂
  rw [gw', my] at e₃
  generalize 2 ^ (64 * K) = M at *
  generalize masked (smask (s.gpr w)) (wordsVal s.mem base x (K - 1)) = a at *
  generalize masked (smask (s.gpr w')) (wordsVal s.mem base y (K - 1)) = b at *
  rw [show wordsVal t.mem base T K + 2 ^ 64 * (a + b) = (wordsVal t.mem base T K + 2 ^ 64 * b) + 2 ^ 64 * a by
    rw [Nat.mul_add]; omega_using [], ← Nat.mod_add_mod, e₃, Nat.mod_add_mod, e₂, e₁]

/-! ## The shift by 59 -/

/-- `r8 *= 32`. -/
theorem shl5_ok (s : State) :
    WP isa (.block shl5) s fun t => (t.gpr .r8).toNat = (s.gpr .r8).toNat * 32 % 2 ^ 64 ∧ Keeps [.r8] s t := by
  irun [shl5]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

/-- A word of the shift: `(lo >> 59) + 32 hi` does not wrap. -/
theorem shr_word (lo y : BitVec 64) {hi : Nat} (hy : y.toNat = hi * 32 % 2 ^ 64) :
    (lo >>> 59 + y).toNat = (lo.toNat / 2 ^ 59 + 2 ^ 5 * hi) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hy]
  have := lo.isLt
  omega_using []

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
  · rw [mt, k₃.2.1, k₂.2.1, k₁.2.1]; exact writeW_outside _ _ _ (by omega_using [hd, hn])

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
    refine WP.mono (shrRows_ok hs hsrc hdst hsep j (by omega_using [hj])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [shrStep, ← List.singleton_append, List.append_assoc, WP.block_append_iff]
    refine WP.mono (movMem_ok hs₁ .rax (d := src + 8 * j) (by omega_using [hsrc, hj])) fun s₂ ⟨l₂, _, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (movMem_ok hs₂ .r8 (d := src + 8 * (j + 1)) (by omega_using [hsrc, hj])) fun s₃ ⟨l₃, _, k₃⟩ => ?_
    have hs₃ := hs₂.of_keeps k₃ (by decide)
    refine WP.mono (shrTail_ok hs₃ (d := dst + 8 * j) (by omega_using [hdst, hj])) fun t ⟨e, kt, Ot⟩ =>
      ⟨?_, ((k₁.trans ((Keeps.regs k₂).mono (by decide))).trans ((Keeps.regs k₃).mono (by decide))).trans kt,
        fun x hx => by rw [Ot x (by omega_using [hx]), k₃.2.1, k₂.2.1, O₁ x (by omega_using [hx])]⟩
    have w₂ : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := O₁.word (by omega_using [hsep, hj]) (by omega_using [hsrc, hj, hn])
    have w₃ : word s₂.mem base (src + 8 * (j + 1)) = word s.mem base (src + 8 * (j + 1)) := by
      rw [k₂.2.1]; exact O₁.word (by omega_using [hsep, hj]) (by omega_using [hsrc, hj, hn])
    rw [wordsVal_succ_top, Ot.wordsVal (by omega_using []) (by omega_using [hdst, hj, hn]), k₃.2.1, k₂.2.1, e₁, e, k₃.1 .rax (by decide), l₂,
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
  obtain ⟨j, rfl⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega_using [hL]⟩
  simp only [shr59, Nat.add_sub_cancel]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (shrRows_ok hs hsrc hdst hsep j (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movMem_ok hs₁ .rdx (d := src + 8 * j) (by omega_using [hsrc])) fun s₂ ⟨l₂, _, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (maskOf_ok s₂ (d := .r8) (src := .rdx) (by decide)) fun s₃ ⟨g₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (movReg_ok s₃ .rax .rdx) fun s₄ ⟨g₄, k₄⟩ => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.mono (shrTail_ok hs₄ (d := dst + 8 * j) (by omega_using [hdst])) fun t ⟨e, kt, Ot⟩ =>
    ⟨?_, (((k₁.mono (by decide)).trans ((Keeps.regs k₂).mono (by decide))).trans
      (((Keeps.regs k₃).mono (by decide)).trans ((Keeps.regs k₄).mono (by decide)))).trans (kt.mono (by decide)),
      fun x hx => by rw [Ot x (by omega_using [hx]), k₄.2.1, k₃.2.1, k₂.2.1, O₁ x (by omega_using [hx])]⟩
  have w₂ : word s₁.mem base (src + 8 * j) = word s.mem base (src + 8 * j) := O₁.word (by omega_using [hsep]) (by omega_using [hn, hsrc])
  rw [wordsVal_succ_top, Ot.wordsVal (by omega_using []) (by omega_using [hn, hdst]), k₄.2.1, k₃.2.1, k₂.2.1, e₁, e, g₄,
    k₄.1 .r8 (by decide), g₃, smask_toNat, k₃.1 .rdx (by decide), l₂, w₂, sext, Nat.add_sub_cancel,
    wordsVal_succ_top s.mem base src j, pow64_succ, Nat.mul_comm (2 ^ 64) (2 ^ (64 * j))]
  exact (shr_arith j _ _ _ (wordsVal_lt _ _ _ _)).symm

/-! ## The signed linear combination in registers

`linR` computes what `lin` does (`linR_ok`, stated as `linM_ok`), the signed
`w [x] + w' [y]` modulo `2^(64 K)`, with fewer instructions: with `a = |w|`
and `M` the mask of `w`'s sign, `w X ≡ a (X ⊕ M) + (a & M)` (`X ⊕ M` over `K`
words is `X` or `2^(64 K) - 1 - X`, `xorSum_zero`, `xorSum_ones`), and the
sum is taken column by column: each column's two products added to the
accumulator `r8`, `r13`, which never overflows for `a`, `|w'| ≤ 2^62`
(`linCol_ok`), its low word stored. -/

/-! ## Absolute values -/

/-- `|x|` of a signed word: `(x ⊕ mask) - mask`. -/
def absW (x : BitVec 64) : BitVec 64 := (x ^^^ smask x) - smask x

theorem absW_toNat (x : BitVec 64) : (absW x).toNat = x.toInt.natAbs := by
  have hx := x.isLt
  have ht := Divstep.toInt_sgn x
  have hv := smask_toNat x
  unfold sgnW at hv
  unfold absW
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have e : smask x = BitVec.allOnes 64 := BitVec.eq_of_toNat_eq (by rw [hv, BitVec.toNat_allOnes, ite_eq_left_of_eq_true _ _ (eq_true h)])
    rw [e, BitVec.xor_allOnes, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes]
    simp only [h, ↓reduceIte] at ht
    omega_using [h, ht]
  · have e : smask x = 0 := BitVec.eq_of_toNat_eq (by rw [hv, ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl)
    rw [e]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.xor_zero, BitVec.sub_zero]
    simp only [h, ↓reduceIte] at ht
    omega_using [ht]

/-- `a = |w|` and `[sl]` the mask of `w`'s sign. -/
theorem absMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w a : Reg}
    (hw : w ∉ [Reg.rax, .rdx]) (ha : a ∉ [Reg.rax, .rdx]) (haw : a ≠ w) {sl : Nat} (hsl : sl + 8 ≤ size) :
    WP isa (.block (absMask w a sl)) s fun t =>
      t.gpr a = absW (s.gpr w) ∧ t.mem = s.mem.writeW (off base sl) (smask (s.gpr w)) ∧
      KeepRegs [.rax, .rdx, a] s t := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw ha
  rw [absMask, show ∀ (i₁ i₂ i₃ i₄ i₅ i₆ i₇ i₈ : Instr), [i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈] =
    [i₁, i₂, i₃, i₄] ++ ([i₅] ++ [i₆, i₇, i₈]) from fun _ _ _ _ _ _ _ _ => rfl, WP.block_append_iff]
  have h₁ : WP isa (.block [.mov .rax (.reg w), .shift .shr .rax 63, .mov32 .rdx (.imm 0),
      .alu .sub .rdx (.reg .rax)]) s fun t => t.gpr .rdx = smask (s.gpr w) ∧ Keeps [.rax, .rdx] s t := by
    irun
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · simp only [smask]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  refine WP.mono h₁ fun s₁ ⟨d₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storeReg_ok hs₁ .rdx hsl) fun s₂ ⟨m₂, g₂, _, k₂⟩ => ?_
  have hw₂ : s₂.gpr w = s.gpr w := by rw [g₂]; exact k₁.1 w (by simp [hw.1, hw.2])
  have hd₂ : s₂.gpr .rdx = smask (s.gpr w) := by rw [g₂, d₁]
  have h₃ : WP isa (.block [.mov a (.reg w), .alu .xor a (.reg .rdx), .alu .sub a (.reg .rdx)]) s₂
      fun t => t.gpr a = absW (s.gpr w) ∧ Keeps [a] s₂ t := by
    have h1 : ¬Reg.rdx = a := fun h => ha.2 h.symm
    have h2 : ¬w = a := fun h => haw h.symm
    irun [h1, h2, RegUpd.gpr_setReg_self]
    refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · rw [hw₂, hd₂]; rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  refine WP.mono h₃ fun t ⟨at', kt⟩ => ⟨at', ?_, ?_⟩
  · rw [kt.2.1, m₂, d₁, k₁.2.1]
  · exact ((Keeps.regs k₁).mono (by simp)).trans ((k₂.mono (by simp)).trans ((Keeps.regs kt).mono (by simp)))

/-! ## Small blocks -/

/-- `d &= [x]`. -/
theorem andMem_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (d : Reg) {x : Nat}
    (hx : x + 8 ≤ size) :
    WP isa (.block [.alu .and d (.mem (sc x))]) s fun t =>
      t.gpr d = s.gpr d &&& word s.mem base x ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc_sc hs hx, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `d ^= [x]`. -/
theorem xorMem_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (d : Reg) {x : Nat}
    (hx : x + 8 ≤ size) :
    WP isa (.block [.alu .xor d (.mem (sc x))]) s fun t =>
      t.gpr d = s.gpr d ^^^ word s.mem base x ∧ Keeps [d] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc_sc hs hx, Option.bind_some,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The arithmetic of `r8, r13 += rdx:rax` (`add`, `adc`), which does not overflow. -/
theorem acc_arith (lo hi a c : BitVec 64) {P : Nat} (hlo : lo.toNat = P % 2 ^ 64) (hhi : hi.toNat = P / 2 ^ 64)
    (hb : a.toNat + 2 ^ 64 * c.toNat + P < 2 ^ 128) :
    (a + lo).toNat + 2 ^ 64 *
        (c + hi + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + lo.toNat))).setWidth 64).toNat =
      a.toNat + 2 ^ 64 * c.toNat + P := by
  have ha := a.isLt; have hc := c.isLt
  simp only [BitVec.toNat_add, toNat_ofBool, hlo, hhi]
  by_cases h : 2 ^ 64 ≤ a.toNat + P % 2 ^ 64 <;>
    simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [hb, h]

/-- `r8, r13 += rax · m`. -/
theorem macc_ok (s : State) (m : Reg)
    (hb : (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + (s.gpr .rax).toNat * (s.gpr m).toNat < 2 ^ 128) :
    WP isa (.block [.mul m, .alu .add .r8 (.reg .rax), .alu .adc .r13 (.reg .rdx)]) s fun t =>
      (t.gpr .r8).toNat + 2 ^ 64 * (t.gpr .r13).toNat =
        (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + (s.gpr .rax).toNat * (s.gpr m).toNat ∧
      Keeps [.rax, .rdx, .r8, .r13] s t := by
  irun [RegUpd.cf_setReg]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have hp := Nat.mul_lt_mul'' (s.gpr .rax).isLt (s.gpr m).isLt
    exact acc_arith _ _ _ _ (BitVec.toNat_ofNat _ _)
      (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hp])) hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2, ite_false]

/-- `[x] ⊕ [sl]`, as a number. -/
abbrev xorW (m : Mem) (base : Addr) (x sl : Nat) : Nat := (word m base x ^^^ word m base sl).toNat

/-- `r8, r13 += m · ([x] ⊕ [sl])`. -/
theorem linTerm_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m : Reg}
    (hm : m ≠ .rax) {x sl : Nat} (hx : x + 8 ≤ size) (hsl : sl + 8 ≤ size)
    (hb : (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + 2 ^ 64 * (s.gpr m).toNat ≤ 2 ^ 128) :
    WP isa (.block (linTerm m x sl)) s fun t =>
      (t.gpr .r8).toNat + 2 ^ 64 * (t.gpr .r13).toNat =
        (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + (s.gpr m).toNat * xorW s.mem base x sl ∧
      Keeps [.rax, .rdx, .r8, .r13] s t := by
  rw [linTerm, show ∀ (i₁ i₂ i₃ i₄ i₅ : Instr), [i₁, i₂, i₃, i₄, i₅] = [i₁] ++ ([i₂] ++ [i₃, i₄, i₅])
    from fun _ _ _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rax hx) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (xorMem_ok hs₁ .rax hsl) fun s₂ ⟨l₂, k₂⟩ => ?_
  have g : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r hr =>
    (k₂.1 r (by simp [hr])).trans (k₁.1 r (by simp [hr]))
  have hv : (s₂.gpr .rax).toNat = xorW s.mem base x sl := by rw [l₂, l₁, k₁.2.1]
  have hwl := (word s.mem base x ^^^ word s.mem base sl).isLt
  have hml : xorW s.mem base x sl * (s.gpr m).toNat ≤ (2 ^ 64 - 1) * (s.gpr m).toNat :=
    Nat.mul_le_mul_right _ (by omega_using [hv])
  refine WP.mono (macc_ok s₂ m (by
    rw [hv, g .r8 (by decide), g .r13 (by decide), g m hm]
    rw [Nat.sub_mul, Nat.one_mul] at hml
    omega_using [hb, hml])) fun t ⟨e, kt⟩ => ⟨?_, ((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans kt⟩
  rw [e, hv, g .r8 (by decide), g .r13 (by decide), g m hm, Nat.mul_comm (s.gpr m).toNat]

/-- `r8, r13 += m · [sl]`. -/
theorem linTermTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {m : Reg}
    (hm : m ≠ .rax) {sl : Nat} (hsl : sl + 8 ≤ size)
    (hb : (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + 2 ^ 64 * (s.gpr m).toNat ≤ 2 ^ 128) :
    WP isa (.block (linTermTop m sl)) s fun t =>
      (t.gpr .r8).toNat + 2 ^ 64 * (t.gpr .r13).toNat =
        (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r13).toNat + (s.gpr m).toNat * (word s.mem base sl).toNat ∧
      Keeps [.rax, .rdx, .r8, .r13] s t := by
  rw [linTermTop, show ∀ (i₁ i₂ i₃ i₄ : Instr), [i₁, i₂, i₃, i₄] = [i₁] ++ [i₂, i₃, i₄]
    from fun _ _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .rax hsl) fun s₁ ⟨l₁, _, k₁⟩ => ?_
  have g : ∀ r, r ≠ .rax → s₁.gpr r = s.gpr r := fun r hr => k₁.1 r (by simp [hr])
  have hwl := (word s.mem base sl).isLt
  have hml : (word s.mem base sl).toNat * (s.gpr m).toNat ≤ (2 ^ 64 - 1) * (s.gpr m).toNat :=
    Nat.mul_le_mul_right _ (by omega_using [])
  refine WP.mono (macc_ok s₁ m (by
    rw [l₁, g .r8 (by decide), g .r13 (by decide), g m hm]
    rw [Nat.sub_mul, Nat.one_mul] at hml
    omega_using [hb, hml])) fun t ⟨e, kt⟩ => ⟨?_, (k₁.mono (by simp)).trans kt⟩
  rw [e, l₁, g .r8 (by decide), g .r13 (by decide), g m hm, Nat.mul_comm (s.gpr m).toNat]

/-- `[T] = r8`, `r8 = r13`, `r13 = 0`. -/
theorem linOut_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {T : Nat} (hT : T + 8 ≤ size) :
    WP isa (.block (linOut T)) s fun t =>
      t.mem = s.mem.writeW (off base T) (s.gpr .r8) ∧ t.gpr .r8 = s.gpr .r13 ∧ t.gpr .r13 = 0 ∧
      KeepRegs [.r8, .r13] s t := by
  rw [linOut, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (storeReg_ok hs .r8 hT) fun s₁ ⟨m₁, g₁, _, k₁⟩ => ?_
  have h : WP isa (.block [.mov .r8 (.reg .r13), .mov32 .r13 (.imm 0)]) s₁ fun t =>
      t.gpr .r8 = s₁.gpr .r13 ∧ t.gpr .r13 = 0 ∧ Keeps [.r8, .r13] s₁ t := by
    irun
    refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]
  refine WP.mono h fun t ⟨e8, e13, kt⟩ => ⟨by rw [kt.2.1, m₁], by rw [e8, g₁], e13,
    (k₁.mono (by simp)).trans (Keeps.regs kt)⟩

/-- The accumulator's start: `r8 = (rcx & [U]) + (rbp & [U + 8])`, `r13 = 0`. -/
theorem linInit_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {U : Nat} (hU : U + 16 ≤ size)
    (hm : IsMask (word s.mem base U)) (hm' : IsMask (word s.mem base (U + 8)))
    (ha : (s.gpr .rcx).toNat ≤ 2 ^ 62) (hb : (s.gpr .rbp).toNat ≤ 2 ^ 62) :
    WP isa (.block (linInit U)) s fun t =>
      (t.gpr .r8).toNat = masked (word s.mem base U) (s.gpr .rcx).toNat +
        masked (word s.mem base (U + 8)) (s.gpr .rbp).toNat ∧ t.gpr .r13 = 0 ∧ Keeps [.rax, .r8, .r13] s t := by
  rw [linInit, show ∀ (i₁ i₂ i₃ i₄ i₅ i₆ : Instr), [i₁, i₂, i₃, i₄, i₅, i₆] =
    [i₁] ++ ([i₂] ++ ([i₃] ++ ([i₄] ++ [i₅, i₆]))) from fun _ _ _ _ _ _ => rfl, WP.block_append_iff]
  have h₁ : WP isa (.block [.mov .r8 (.reg .rcx)]) s fun t => t.gpr .r8 = s.gpr .rcx ∧ Keeps [.r8] s t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h₁ fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (andMem_ok hs₁ .r8 (x := U) (by omega_using [hU])) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [WP.block_append_iff]
  have h₃ : WP isa (.block [.mov .rax (.reg .rbp)]) s₂ fun t => t.gpr .rax = s₂.gpr .rbp ∧ Keeps [.rax] s₂ t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h₃ fun s₃ ⟨e₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (andMem_ok hs₃ .rax (x := U + 8) (by omega_using [hU])) fun s₄ ⟨e₄, k₄⟩ => ?_
  have hm₄ : s₄.mem = s.mem := by rw [k₄.2.1, k₃.2.1, k₂.2.1, k₁.2.1]
  have hm₃ : s₃.mem = s.mem := by rw [k₃.2.1, k₂.2.1, k₁.2.1]
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have v8 : (s₄.gpr .r8).toNat = masked (word s.mem base U) (s.gpr .rcx).toNat := by
    rw [k₄.1 .r8 (by decide), k₃.1 .r8 (by decide), e₂, e₁, hm₁, and_mask hm]
  have vax : (s₄.gpr .rax).toNat = masked (word s.mem base (U + 8)) (s.gpr .rbp).toNat := by
    rw [e₄, e₃, hm₃, k₂.1 .rbp (by decide), k₁.1 .rbp (by decide), and_mask hm']
  have h₅ : WP isa (.block [.alu .add .r8 (.reg .rax), .mov32 .r13 (.imm 0)]) s₄ fun t =>
      t.gpr .r8 = s₄.gpr .r8 + s₄.gpr .rax ∧ t.gpr .r13 = 0 ∧ Keeps [.r8, .r13] s₄ t := by
    irun
    exact ⟨fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false], rfl, rfl, rfl⟩
  refine WP.mono h₅ fun t ⟨e8, e13, kt⟩ => ⟨?_, e13, ?_⟩
  · have m1 := masked_le (word s.mem base U) (s.gpr .rcx).toNat
    have m2 := masked_le (word s.mem base (U + 8)) (s.gpr .rbp).toNat
    rw [e8, BitVec.toNat_add, v8, vax]
    exact Nat.mod_eq_of_lt (by omega_using [ha, hb, m1, m2])
  · exact ((((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans (k₃.mono (by simp))).trans
      (k₄.mono (by simp))).trans (kt.mono (by simp))

/-- A column: `[T'] + 2^64 r8' = r8 + rcx X + rbp Y` for `X`, `Y` the
terms' words; `r13` stays zero. -/
theorem linCol_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {T x y U i : Nat} (hx : x + 8 * i + 8 ≤ size) (hy : y + 8 * i + 8 ≤ size) (hU : U + 16 ≤ size)
    (hT : (T + 8 * i) + 8 ≤ size) (h13 : s.gpr .r13 = 0) (ha : (s.gpr .rcx).toNat ≤ 2 ^ 62)
    (hb : (s.gpr .rbp).toNat ≤ 2 ^ 62) :
    WP isa (.block (linCol T x y U i)) s fun t =>
      (word t.mem base (T + 8 * i)).toNat + 2 ^ 64 * (t.gpr .r8).toNat =
        (s.gpr .r8).toNat + (s.gpr .rcx).toNat * xorW s.mem base (x + 8 * i) U + (s.gpr .rbp).toNat * xorW s.mem base (y + 8 * i) (U + 8) ∧
      t.gpr .r13 = 0 ∧ KeepRegs [.rax, .rdx, .r8, .r13] s t ∧ Outside base (T + 8 * i) 8 s.mem t.mem := by
  have hn := hs.nowrap
  rw [linCol, List.append_assoc, WP.block_append_iff]
  have hr8 := (s.gpr .r8).isLt
  have z : (s.gpr .r13).toNat = 0 := by rw [h13]; rfl
  refine WP.mono (linTerm_ok hs (m := .rcx) (by decide) (x := x + 8 * i) (sl := U) hx (by omega_using [hU]) (by
    rw [z]; omega_using [])) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [z, Nat.mul_zero, Nat.add_zero] at e₁
  have hXl : xorW s.mem base (x + 8 * i) U < 2 ^ 64 := BitVec.isLt _
  have hYl : xorW s.mem base (y + 8 * i) (U + 8) < 2 ^ 64 := BitVec.isLt _
  have hmX : (s.gpr .rcx).toNat * xorW s.mem base (x + 8 * i) U ≤ 2 ^ 62 * (2 ^ 64 - 1) := Nat.mul_le_mul ha (by omega_using [hXl])
  have hmY : (s.gpr .rbp).toNat * xorW s.mem base (y + 8 * i) (U + 8) ≤ 2 ^ 62 * (2 ^ 64 - 1) := Nat.mul_le_mul hb (by omega_using [hYl])
  have g₁ : ∀ r, r ∉ [Reg.rax, .rdx, .r8, .r13] → s₁.gpr r = s.gpr r := k₁.1
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (linTerm_ok hs₁ (m := .rbp) (by decide) (x := y + 8 * i) (sl := U + 8) hy (by omega_using [hU]) (by
    rw [e₁, g₁ .rbp (by decide)]; omega_using [hb, hmX])) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (linOut_ok hs₂ hT) fun t ⟨mt, e8, e13, kt⟩ => ⟨?_, e13, ?_, ?_⟩
  · have hsum : (s₂.gpr .r8).toNat + 2 ^ 64 * (s₂.gpr .r13).toNat =
        (s.gpr .r8).toNat + (s.gpr .rcx).toNat * xorW s.mem base (x + 8 * i) U + (s.gpr .rbp).toNat * xorW s.mem base (y + 8 * i) (U + 8) := by
      rw [e₂, e₁, g₁ .rbp (by decide), hm₁]
    rw [mt, word_writeW_self, e8, hsum]
  · exact ((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (kt.mono (by simp))
  · rw [mt, k₂.2.1, hm₁]; exact writeW_outside _ _ _ (by omega_using [hT, hn])

/-- A column: `[T'] + 2^64 r8' = r8 + rcx X + rbp Y` for `X`, `Y` the
terms' words; `r13` stays zero. -/
theorem linColTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {T U k : Nat} (hU : U + 16 ≤ size)
    (hT : (T + 8 * k) + 8 ≤ size) (h13 : s.gpr .r13 = 0) (ha : (s.gpr .rcx).toNat ≤ 2 ^ 62)
    (hb : (s.gpr .rbp).toNat ≤ 2 ^ 62) :
    WP isa (.block (linColTop T U k)) s fun t =>
      (word t.mem base (T + 8 * k)).toNat + 2 ^ 64 * (t.gpr .r8).toNat =
        (s.gpr .r8).toNat + (s.gpr .rcx).toNat * (word s.mem base U).toNat + (s.gpr .rbp).toNat * (word s.mem base (U + 8)).toNat ∧
      t.gpr .r13 = 0 ∧ KeepRegs [.rax, .rdx, .r8, .r13] s t ∧ Outside base (T + 8 * k) 8 s.mem t.mem := by
  have hn := hs.nowrap
  rw [linColTop, List.append_assoc, WP.block_append_iff]
  have hr8 := (s.gpr .r8).isLt
  have z : (s.gpr .r13).toNat = 0 := by rw [h13]; rfl
  refine WP.mono (linTermTop_ok hs (m := .rcx) (by decide) (sl := U) (by omega_using [hU]) (by
    rw [z]; omega_using [])) fun s₁ ⟨e₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [z, Nat.mul_zero, Nat.add_zero] at e₁
  have hXl : (word s.mem base U).toNat < 2 ^ 64 := BitVec.isLt _
  have hYl : (word s.mem base (U + 8)).toNat < 2 ^ 64 := BitVec.isLt _
  have hmX : (s.gpr .rcx).toNat * (word s.mem base U).toNat ≤ 2 ^ 62 * (2 ^ 64 - 1) := Nat.mul_le_mul ha (by omega_using [])
  have hmY : (s.gpr .rbp).toNat * (word s.mem base (U + 8)).toNat ≤ 2 ^ 62 * (2 ^ 64 - 1) := Nat.mul_le_mul hb (by omega_using [])
  have g₁ : ∀ r, r ∉ [Reg.rax, .rdx, .r8, .r13] → s₁.gpr r = s.gpr r := k₁.1
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  rw [WP.block_append_iff]
  refine WP.mono (linTermTop_ok hs₁ (m := .rbp) (by decide) (sl := U + 8) (by omega_using [hU]) (by
    rw [e₁, g₁ .rbp (by decide)]; omega_using [hb, hmX])) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (linOut_ok hs₂ hT) fun t ⟨mt, e8, e13, kt⟩ => ⟨?_, e13, ?_, ?_⟩
  · have hsum : (s₂.gpr .r8).toNat + 2 ^ 64 * (s₂.gpr .r13).toNat =
        (s.gpr .r8).toNat + (s.gpr .rcx).toNat * (word s.mem base U).toNat + (s.gpr .rbp).toNat * (word s.mem base (U + 8)).toNat := by
      rw [e₂, e₁, g₁ .rbp (by decide), hm₁]
    rw [mt, word_writeW_self, e8, hsum]
  · exact ((Keeps.regs k₁).trans (Keeps.regs k₂)).trans (kt.mono (by simp))
  · rw [mt, k₂.2.1, hm₁]; exact writeW_outside _ _ _ (by omega_using [hT, hn])

/-! ## The columns -/

/-- `[x …] ⊕ [sl]` over `i` words, as a number. -/
def xorSum (m : Mem) (base : Addr) (x sl : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => xorSum m base x sl i + 2 ^ (64 * i) * xorW m base (x + 8 * i) sl

theorem xorSum_congr {m m' : Mem} {base : Addr} {x sl : Nat} :
    ∀ {i : Nat}, (∀ j < i, xorW m' base (x + 8 * j) sl = xorW m base (x + 8 * j) sl) →
      xorSum m' base x sl i = xorSum m base x sl i
  | 0, _ => rfl
  | i + 1, h => by
    simp only [xorSum]
    rw [xorSum_congr fun j hj => h j (by omega_using [hj]), h i (by omega_using [])]

/-- Columns `0 … i - 1`: `[T …] + 2^(64 i) r8' = r8 + rcx (X ⊕ M) + rbp (Y ⊕ M')`. -/
theorem linCols_ok {base : Addr} {size T x y U : Nat} (hU : U + 16 ≤ size) :
    ∀ (i : Nat) {s : State}, Scr s base size → x + 8 * i ≤ size → y + 8 * i ≤ size → T + 8 * i ≤ size →
      (T + 8 * i ≤ x ∨ x + 8 * i ≤ T) → (T + 8 * i ≤ y ∨ y + 8 * i ≤ T) → (T + 8 * i ≤ U ∨ U + 16 ≤ T) →
      s.gpr .r13 = 0 → (s.gpr .rcx).toNat ≤ 2 ^ 62 → (s.gpr .rbp).toNat ≤ 2 ^ 62 →
      WP isa (.block (linCols T x y U i)) s fun t =>
        wordsVal t.mem base T i + 2 ^ (64 * i) * (t.gpr .r8).toNat =
          (s.gpr .r8).toNat + (s.gpr .rcx).toNat * xorSum s.mem base x U i +
            (s.gpr .rbp).toNat * xorSum s.mem base y (U + 8) i ∧
        t.gpr .r13 = 0 ∧ KeepRegs [.rax, .rdx, .r8, .r13] s t ∧ Outside base T (8 * i) s.mem t.mem
  | 0, s, _, _, _, _, _, _, _, h13, _, _ => WP.block_nil ⟨by simp [wordsVal, xorSum], h13,
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | i + 1, s, hs, hx, hy, hT, hTx, hTy, hTU, h13, ha, hb => by
    have hn := hs.nowrap
    rw [linCols, WP.block_append_iff]
    refine WP.mono (linCols_ok hU i hs (by omega_using [hx]) (by omega_using [hy]) (by omega_using [hT]) (by omega_using [hTx]) (by omega_using [hTy]) (by omega_using [hTU])
      h13 ha hb) fun s₁ ⟨e₁, z₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have gc : s₁.gpr .rcx = s.gpr .rcx := k₁.gpr _ (by decide)
    have gb : s₁.gpr .rbp = s.gpr .rbp := k₁.gpr _ (by decide)
    refine WP.mono (linCol_ok hs₁ (T := T) (x := x) (y := y) (U := U) (i := i) (by omega_using [hx]) (by omega_using [hy]) hU
      (by omega_using [hT]) z₁ (by rw [gc]; exact ha) (by rw [gb]; exact hb)) fun t ⟨e₂, z₂, k₂, O₂⟩ =>
        ⟨?_, z₂, k₁.trans k₂, fun a ha' => by
          rw [O₂ a (by omega_using [ha']), O₁ a (by omega_using [ha'])]⟩
    have wx : xorW s₁.mem base (x + 8 * i) U = xorW s.mem base (x + 8 * i) U := by
      simp only [xorW]; rw [O₁.word (by omega_using [hTx]) (by omega_using [hx, hn]), O₁.word (by omega_using [hTU]) (by omega_using [hU, hn])]
    have wy : xorW s₁.mem base (y + 8 * i) (U + 8) = xorW s.mem base (y + 8 * i) (U + 8) := by
      simp only [xorW]; rw [O₁.word (by omega_using [hTy]) (by omega_using [hy, hn]), O₁.word (by omega_using [hTU]) (by omega_using [hU, hn])]
    have wT : wordsVal t.mem base T i = wordsVal s₁.mem base T i := O₂.wordsVal (by omega_using []) (by omega_using [hT, hn])
    rw [gc, gb, wx, wy] at e₂
    rw [wordsVal_succ_top, wT, pow64_succ]
    simp only [xorSum]
    generalize 2 ^ (64 * i) = P at *
    generalize (word t.mem base (T + 8 * i)).toNat = W at *
    generalize (s.gpr .rcx).toNat = A at *
    generalize (s.gpr .rbp).toNat = B at *
    grind

/-- With a zero mask, `X ⊕ M = X`. -/
theorem xorSum_zero {m : Mem} {base : Addr} {x sl : Nat} (h : word m base sl = 0) :
    ∀ k, xorSum m base x sl k = wordsVal m base x k
  | 0 => rfl
  | k + 1 => by
    rw [xorSum, xorSum_zero h k, wordsVal_succ_top, xorW, h]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.xor_zero]

/-- With an all-ones mask, `X ⊕ M = 2^(64 k) - 1 - X`. -/
theorem xorSum_ones {m : Mem} {base : Addr} {x sl : Nat} (h : word m base sl = BitVec.allOnes 64) :
    ∀ k, xorSum m base x sl k + wordsVal m base x k + 1 = 2 ^ (64 * k)
  | 0 => rfl
  | k + 1 => by
    have ih := xorSum_ones (x := x) h k
    have hw : xorW m base (x + 8 * k) sl + (word m base (x + 8 * k)).toNat = 2 ^ 64 - 1 := by
      rw [xorW, h, BitVec.xor_allOnes, BitVec.toNat_not]
      have := (word m base (x + 8 * k)).isLt; omega_using []
    rw [xorSum, wordsVal_succ_top, pow64_succ]
    generalize 2 ^ (64 * k) = P at *
    generalize xorW m base (x + 8 * k) sl = A at *
    generalize (word m base (x + 8 * k)).toNat = B at *
    have : P * A + P * B = P * (2 ^ 64 - 1) := by rw [← Nat.mul_add, hw]
    rw [Nat.mul_sub, Nat.mul_one] at this
    have hP : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
    omega_using [ih, this]

/-- One side of the sum: `(|w| & M) + |w| (X ⊕ M) ≡ w X` modulo `Q`, for
`X ⊕ M = X` with `M = 0` and `Q - 1 - X` with `M` all ones. -/
theorem side_cong {w : BitVec 64} {X S Q : Nat} (h0 : smask w = 0 → S = X)
    (h1 : smask w = BitVec.allOnes 64 → S + X + 1 = Q) :
    ∃ j : Int, ((masked (smask w) (absW w).toNat + (absW w).toNat * S : Nat) : Int) =
      w.toInt * X + j * Q := by
  have ht := Divstep.toInt_sgn w
  have hv := smask_toNat w
  have ha := absW_toNat w
  unfold sgnW at hv
  have hw := w.isLt
  by_cases h : 2 ^ 63 ≤ w.toNat
  · have e : smask w = BitVec.allOnes 64 :=
      BitVec.eq_of_toNat_eq (by rw [hv, BitVec.toNat_allOnes, ite_eq_left_of_eq_true _ _ (eq_true h)])
    have hS := h1 e
    simp only [h, ↓reduceIte] at ht
    refine ⟨(absW w).toNat, ?_⟩
    simp only [masked, e, ↓reduceIte]
    have hA : ((absW w).toNat : Int) = -w.toInt := by rw [ha]; omega_using [ht]
    have hS' : (S : Int) = Q - 1 - X := by omega_using [hS]
    push_cast
    rw [hS', hA]
    grind
  · have e : smask w = 0 := BitVec.eq_of_toNat_eq (by rw [hv, ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl)
    have hS := h0 e
    simp only [h, ↓reduceIte] at ht
    refine ⟨0, ?_⟩
    simp only [masked, e, show (0 : BitVec 64) ≠ BitVec.allOnes 64 by decide, ↓reduceIte]
    have hA : ((absW w).toNat : Int) = w.toInt := by rw [ha]; omega_using [ht]
    push_cast
    rw [hS, hA]
    grind

/-! ## The combination -/


/-- `[T] = w [x] + w' [y]` modulo `2^(64 K)` (`k ≤ K ≤ k + 1`), for `|w|`, `|w'| ≤ 2^62`. -/
theorem linR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {w w' : Reg}
    (hw : w ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13]) (hw' : w' ∉ [Reg.rax, .rcx, .rdx, .rbp, .r8, .rdi, .r13])
    {T x y U k K : Nat} (hkK : k ≤ K) (hK : 3 ≤ K) (hk' : K ≤ k + 1)
    (hx : x + 8 * k ≤ size) (hy : y + 8 * k ≤ size) (hT : T + 8 * K ≤ size) (hU : U + 8 * (K - 1) ≤ size)
    (hTx : T + 8 * K ≤ x ∨ x + 8 * k ≤ T) (hTy : T + 8 * K ≤ y ∨ y + 8 * k ≤ T)
    (hUT : U + 8 * (K - 1) ≤ T ∨ T + 8 * K ≤ U) (hUx : U + 8 * (K - 1) ≤ x ∨ x + 8 * k ≤ U)
    (hUy : U + 8 * (K - 1) ≤ y ∨ y + 8 * k ≤ U)
    (hu : (s.gpr w).toInt.natAbs ≤ 2 ^ 62) (hv : (s.gpr w').toInt.natAbs ≤ 2 ^ 62) :
    WP isa (.block (linR w w' T x y U k K)) s fun t =>
      (wordsVal t.mem base T K : Int) % ((2 ^ (64 * K) : Nat) : Int) =
        ((s.gpr w).toInt * wordsVal s.mem base x k + (s.gpr w').toInt * wordsVal s.mem base y k) %
          ((2 ^ (64 * K) : Nat) : Int) ∧
      KeepRegs [.rax, .rcx, .rdx, .rbp, .r8, .r13] s t ∧ Unch base [(T, 8 * K), (U, 8 * (K - 1))] s.mem t.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw hw'
  rw [linR, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  -- `rcx = |w|`, `[U]` its mask.
  refine WP.mono (absMask_ok hs (w := w) (a := .rcx) (by simp [hw.1, hw.2.2.1]) (by decide)
    (fun h => hw.2.1 h.symm) (sl := U) (by lin_omega)) fun s₁ ⟨a₁, m₁, k₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have gw' : s₁.gpr w' = s.gpr w' := k₁.gpr _ (by simp [hw'.1, hw'.2.1, hw'.2.2.1])
  rw [WP.block_append_iff]
  -- `rbp = |w'|`, `[U + 8]` its mask.
  refine WP.mono (absMask_ok hs₁ (w := w') (a := .rbp) (by simp [hw'.1, hw'.2.2.1]) (by decide)
    (fun h => hw'.2.2.2.1 h.symm) (sl := U + 8) (by lin_omega)) fun s₂ ⟨a₂, m₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [gw'] at a₂ m₂
  have c₂ : s₂.gpr .rcx = absW (s.gpr w) := by rw [k₂.gpr _ (by decide), a₁]
  have O₁ : Outside base U 8 s.mem s₁.mem := by rw [m₁]; exact writeW_outside _ _ _ (by lin_omega)
  have O₂ : Outside base (U + 8) 8 s₁.mem s₂.mem := by rw [m₂]; exact writeW_outside _ _ _ (by lin_omega)
  have U₂ : Unch base [(U, 16)] s.mem s₂.mem := fun a ha => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at ha
    rw [O₂ a (by omega_using [ha]), O₁ a (by omega_using [ha])]
  have wU : word s₂.mem base U = smask (s.gpr w) := by
    rw [O₂.word (by lin_omega) (by lin_omega), m₁, word_writeW_self]
  have wU8 : word s₂.mem base (U + 8) = smask (s.gpr w') := by rw [m₂, word_writeW_self]
  have bA : (absW (s.gpr w)).toNat ≤ 2 ^ 62 := by rw [absW_toNat]; exact hu
  have bB : (absW (s.gpr w')).toNat ≤ 2 ^ 62 := by rw [absW_toNat]; exact hv
  rw [WP.block_append_iff]
  -- The accumulator's start.
  refine WP.mono (linInit_ok hs₂ (U := U) (by lin_omega) (by rw [wU]; exact smask_isMask _)
    (by rw [wU8]; exact smask_isMask _) (by rw [c₂]; exact bA) (by rw [a₂]; exact bB))
    fun s₃ ⟨e₃, z₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  have c₃ : s₃.gpr .rcx = absW (s.gpr w) := by rw [k₃.1 _ (by decide), c₂]
  have b₃ : s₃.gpr .rbp = absW (s.gpr w') := by rw [k₃.1 _ (by decide), a₂]
  have hm₃ : s₃.mem = s₂.mem := k₃.2.1
  rw [c₂, a₂, wU, wU8] at e₃
  rw [WP.block_append_iff]
  -- The columns of the numbers' words.
  refine WP.mono (linCols_ok (T := T) (x := x) (y := y) (U := U) (by lin_omega) k hs₃ hx hy (by lin_omega)
    (by lin_omega) (by lin_omega) (by lin_omega) z₃ (by rw [c₃]; exact bA) (by rw [b₃]; exact bB))
    fun s₄ ⟨e₄, z₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  rw [c₃, b₃, hm₃, e₃] at e₄
  -- `X ⊕ M` as `X` or `2^(64 k) - 1 - X`.
  have eX : wordsVal s₂.mem base x k = wordsVal s.mem base x k := U₂.wordsVal (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; lin_omega) (by lin_omega)
  have eY : wordsVal s₂.mem base y k = wordsVal s.mem base y k := U₂.wordsVal (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; lin_omega) (by lin_omega)
  have zx := fun h => (xorSum_zero (m := s₂.mem) (base := base) (x := x) (sl := U) (wU.trans h) k).trans eX
  have zy := fun h => (xorSum_zero (m := s₂.mem) (base := base) (x := y) (sl := U + 8) (wU8.trans h) k).trans eY
  have ox := fun h => eX ▸ xorSum_ones (m := s₂.mem) (base := base) (x := x) (sl := U) (wU.trans h) k
  have oy := fun h => eY ▸ xorSum_ones (m := s₂.mem) (base := base) (x := y) (sl := U + 8) (wU8.trans h) k
  have hall := (BitVec.allOnes 64 : BitVec 64).isLt
  have hallv : (BitVec.allOnes 64 : BitVec 64).toNat = 2 ^ 64 - 1 := BitVec.toNat_allOnes
  -- The result, from the sum and the carry out `R`.
  have fin : ∀ {t : State} {R : Nat} (Sx Sy : Nat),
      wordsVal t.mem base T K + 2 ^ (64 * K) * R =
        masked (smask (s.gpr w)) (absW (s.gpr w)).toNat + masked (smask (s.gpr w')) (absW (s.gpr w')).toNat +
          (absW (s.gpr w)).toNat * Sx + (absW (s.gpr w')).toNat * Sy →
      (smask (s.gpr w) = 0 → Sx = wordsVal s.mem base x k) →
      (smask (s.gpr w) = BitVec.allOnes 64 → Sx + wordsVal s.mem base x k + 1 = 2 ^ (64 * K)) →
      (smask (s.gpr w') = 0 → Sy = wordsVal s.mem base y k) →
      (smask (s.gpr w') = BitVec.allOnes 64 → Sy + wordsVal s.mem base y k + 1 = 2 ^ (64 * K)) →
      (wordsVal t.mem base T K : Int) % ((2 ^ (64 * K) : Nat) : Int) =
        ((s.gpr w).toInt * wordsVal s.mem base x k + (s.gpr w').toInt * wordsVal s.mem base y k) %
          ((2 ^ (64 * K) : Nat) : Int) := by
    intro t R Sx Sy hsum h0 h1 h0' h1'
    obtain ⟨j₁, e₁⟩ := side_cong h0 h1
    obtain ⟨j₂, e₂⟩ := side_cong h0' h1'
    have hI := congrArg (Nat.cast : Nat → Int) hsum
    push_cast at hI e₁ e₂
    have : (wordsVal t.mem base T K : Int) = (s.gpr w).toInt * wordsVal s.mem base x k +
        (s.gpr w').toInt * wordsVal s.mem base y k + (j₁ + j₂ - R) * ((2 ^ (64 * K) : Nat) : Int) := by
      push_cast; grind
    rw [this, Int.add_mul_emod_self_right]
  by_cases hk : k < K
  · -- The column past the numbers' words.
    have eK : K = k + 1 := by omega_using [hk', hk]
    simp only [hk, ↓reduceIte]
    refine WP.mono (linColTop_ok hs₄ (T := T) (U := U) (k := k) (by lin_omega) (by omega_using [hT, eK]) z₄
      (by rw [k₄.gpr _ (by decide), c₃]; exact bA) (by rw [k₄.gpr _ (by decide), b₃]; exact bB))
      fun t ⟨e₅, _, k₅, O₅⟩ => ⟨?_, ?_, ?_⟩
    · have wU' : word s₄.mem base U = smask (s.gpr w) := by rw [O₄.word (by lin_omega) (by lin_omega), hm₃, wU]
      have wU8' : word s₄.mem base (U + 8) = smask (s.gpr w') := by
        rw [O₄.word (by lin_omega) (by lin_omega), hm₃, wU8]
      rw [k₄.gpr .rcx (by decide), k₄.gpr .rbp (by decide), c₃, b₃, wU', wU8'] at e₅
      have wT : wordsVal t.mem base T k = wordsVal s₄.mem base T k := O₅.wordsVal (by lin_omega) (by lin_omega)
      refine fin (R := (t.gpr .r8).toNat)
        (xorSum s₂.mem base x U k + 2 ^ (64 * k) * (smask (s.gpr w)).toNat)
        (xorSum s₂.mem base y (U + 8) k + 2 ^ (64 * k) * (smask (s.gpr w')).toNat) ?_ ?_ ?_ ?_ ?_
      · rw [eK, wordsVal_succ_top, wT, pow64_succ]
        generalize 2 ^ (64 * k) = P at *
        grind
      · intro h; rw [h, zx h]; simp
      · intro h; rw [h, hallv, eK, pow64_succ]; have := ox h
        generalize 2 ^ (64 * k) = P at *
        rw [Nat.mul_sub, Nat.mul_one]
        have hP : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
        omega_using [this]
      · intro h; rw [h, zy h]; simp
      · intro h; rw [h, hallv, eK, pow64_succ]; have := oy h
        generalize 2 ^ (64 * k) = P at *
        rw [Nat.mul_sub, Nat.mul_one]
        have hP : P ≤ P * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
        omega_using [this]
    · exact (((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans
        ((Keeps.regs k₃).mono (by simp))).trans ((k₄.trans k₅).mono (by simp))
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ha
      rw [O₅ a (by omega_using [ha, eK]), O₄ a (by omega_using [ha, eK]), hm₃, U₂ a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_using [ha, hK])]
  · have eK : K = k := by omega_using [hkK, hk]
    simp only [hk, ↓reduceIte]
    refine WP.block_nil ⟨?_, ?_, ?_⟩
    · subst eK
      exact fin (R := (s₄.gpr .r8).toNat) (xorSum s₂.mem base x U K) (xorSum s₂.mem base y (U + 8) K)
        (by rw [e₄]) zx ox zy oy
    · exact (((k₁.mono (by simp)).trans (k₂.mono (by simp))).trans
        ((Keeps.regs k₃).mono (by simp))).trans (k₄.mono (by simp))
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at ha
      rw [O₄ a (by omega_using [ha, eK, hkK]), hm₃, U₂ a (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; omega_using [ha, hK])]

end VG.Proof.Weierstrass.X86_64
