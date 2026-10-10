import VerifiedGarbage.Proof.Weierstrass.X86.TCombJDigit
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.X86.TCombOne
import VerifiedGarbage.Proof.Weierstrass.X86.TComb

/-! ## `TCombJMask` -/

section

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- `f 0 ||| … ||| f (m - 1)`. -/
def orAll (f : Nat → BitVec 32) : Nat → BitVec 32
  | 0 => 0
  | m + 1 => orAll f m ||| f m

theorem orAll_eq_zero (f : Nat → BitVec 32) : ∀ m, orAll f m = 0 ↔ ∀ i < m, f i = 0
  | 0 => by simp [orAll]
  | m + 1 => by
    rw [orAll]
    have ih := orAll_eq_zero f m
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h
      have h1 := ih.mp h1
      intro i hi
      rcases Nat.lt_or_ge i m with h | h
      · exact h1 i h
      · obtain rfl : i = m := by omega
        exact h2
    · intro h
      exact BitVec.or_eq_zero_iff.mpr ⟨ih.mpr fun i hi => h i (by omega), h m (by omega)⟩

/-- `eax |= [z + 4 (i + 1)]` for `i < m`, from `eax = [z]`. -/
theorem orChain_ok {base : Addr} {size z : Nat} : ∀ m, ∀ (s : State), Scr s base size → z + 4 * (m + 1) ≤ size →
    s.gpr .eax = orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) 1 →
    WP isa (.block ((List.range m).map fun i => .alu .or .eax (.mem (sc (z + 4 * (i + 1)))))) s fun t =>
      t.gpr .eax = orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (m + 1) ∧ CKeeps [.eax] s t
  | 0, s, _, _, hr => WP.block_nil ⟨hr, fun _ _ => rfl, rfl, rfl, rfl⟩
  | m + 1, s, hs, hz, hr => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (orChain_ok m s hs (by omega) hr) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁.keeps (by decide)
    apply WP.of_runBlock
    simp only [List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      Option.bind_some, readSrc_sc hs₁ (d := z + 4 * (m + 1)) (by omega), RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, ite_true, Option.some.injEq, exists_eq_left', e₁, k₁.2.1]
    refine ⟨rfl, fun r hr' => ?_, k₁.2.1, k₁.2.2.1, k₁.2.2.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr', ite_false]
    exact k₁.1 r (by simp [hr'])

/-- `ecx` all ones if the `2 n` 32-bit words at `z` are not all zero (`n ≥ 1`), through
`eax`. -/
theorem nzMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n z : Nat} (hn1 : 1 ≤ n)
    (hz : z + 8 * n ≤ size) :
    WP isa (.block (nzMask n z)) s fun t =>
      t.gpr .ecx = bmask (decide (wordsVal s.mem base z n ≠ 0)) ∧ CKeeps [.eax, .ecx] s t := by
  have hnw := hs.nowrap
  rw [nzMask, WP.block_append_iff]
  refine WP.mono (show WP isa (.block (.mov .eax (.mem (sc z)) :: (List.range (2 * n - 1)).map
      fun i => .alu .or .eax (.mem (sc (z + 4 * (i + 1)))))) s (fun s₂ =>
      s₂.gpr .eax = orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (2 * n) ∧ CKeeps [.eax] s s₂) by
    rw [← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov .eax (.mem (sc z))]) s (fun s₁ =>
        s₁.gpr .eax = orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) 1 ∧ CKeeps [.eax] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.map_some,
        readSrc_sc hs (d := z) (by omega), RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨by simp [orAll], fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨e₁, k₁⟩ => ?_
    have hs₁ := hs.of_keeps k₁.keeps (by decide)
    refine WP.mono (orChain_ok (2 * n - 1) s₁ hs₁ (by omega) (by rw [k₁.2.1]; exact e₁)) fun s₂ ⟨e₂, k₂⟩ => ?_
    rw [k₁.2.1, show 2 * n - 1 + 1 = 2 * n by omega] at e₂
    exact ⟨e₂, k₁.trans k₂⟩) fun s₂ ⟨e₂, k₂⟩ => ?_
  have hz' : (orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (2 * n) = 0) ↔ wordsVal s.mem base z n = 0 := by
    rw [orAll_eq_zero, wordsVal_eq_val32, val32_eq_zero_iff]
    exact forall_congr' fun i => forall_congr' fun _ =>
      ⟨fun h => by simp [w32, h], fun h => BitVec.eq_of_toNat_eq h⟩
  apply WP.of_runBlock
  set_option linter.unusedSimpArgs false in
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.cf_setReg, reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left', e₂,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags]
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · by_cases h0 : wordsVal s.mem base z n = 0
    · have h1 := hz'.mpr h0
      rw [h1]; simp [h0]; rfl
    · have h1 : orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (2 * n) ≠ 0 := fun h => h0 (hz'.mp h)
      have : 0 < (orAll (fun i => s.mem.readW (off base (z + 4 * i)) 32) (2 * n)).toNat := by
        refine Nat.pos_of_ne_zero fun h => h1 (BitVec.eq_of_toNat_eq h)
      simp [h0, this]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
    exact k₂.1 r (by simp [hr.1])
  · exact k₂.2.1
  · exact k₂.2.2.1
  · exact k₂.2.2.2

end VG.Proof.Weierstrass.X86

end

/-! ## `TCombJOut` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- OR a masked constant into one coordinate word. -/
def orConstWord (y v i : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 (v / 2 ^ (32 * i)))), .alu .and .eax (.reg .ecx),
    .alu .or .eax (.mem (sc (y + 4 * i))), .store (sc (y + 4 * i)) .eax]

theorem orConstWord_ok {s : State} {base : Addr} {size y v i : Nat} (hs : Scr s base size)
    {M : BitVec 32} (hc : s.gpr .ecx = M) (hy : y + 4 * i + 4 ≤ size) :
    WP isa (.block (orConstWord y v i)) s fun t =>
      t.mem = s.mem.writeW (off base (y + 4 * i))
        ((BitVec.ofNat 32 (v / 2 ^ (32 * i)) &&& M) ||| s.mem.readW (off base (y + 4 * i)) 32) ∧
      Keeps [.eax] s t := by
  simp only [orConstWord]
  refine wp_movS rfl fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  have hs₂ := (hs.of_keeps u₁.keeps (by decide)).of_keeps u₂.keeps (by decide)
  refine wp_orS (readSrc_sc hs₂ hy) fun s₃ u₃ => ?_
  have hs₃ := hs₂.of_keeps u₃.keeps (by decide)
  refine wp_storeS (hs₃.ea (by omega)) (hs₃.write (n := 4) hy) fun t u₄ => WP.block_nil ⟨?_, ?_⟩
  · simp only [u₄.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .ecx (by decide), hc,
      u₃.mem, u₂.mem, u₁.mem, ite_true]
  · exact ((u₁.keeps.trans u₂.keeps).trans u₃.keeps).trans (u₄.keeps _)

/-- The masked constant, word by word, without changing the mask. -/
theorem orConstWords_ok {s : State} {base : Addr} {size y v : Nat} (hs : Scr s base size)
    {M : BitVec 32} (hc : s.gpr .ecx = M) : ∀ k, y + 4 * k ≤ size →
    WP isa (.block ((List.range k).flatMap (orConstWord y v))) s fun t =>
      (∀ i < k, t.mem.readW (off base (y + 4 * i)) 32 =
        (BitVec.ofNat 32 (v / 2 ^ (32 * i)) &&& M) ||| s.mem.readW (off base (y + 4 * i)) 32) ∧
      Keeps [.eax] s t ∧ Outside base y (4 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (orConstWords_ok hs hc k (by omega)) fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
    refine WP.mono (orConstWord_ok (hs.of_keeps k₁ (by decide)) ((k₁.1 _ (by decide)).trans hc)
      (i := k) (by omega)) fun s₂ ⟨m₂,k₂⟩ => ?_
    have O₂ : Outside base (y + 4 * k) 4 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun i hi => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    have read_eq {m m' : Mem} {a b n : Nat} (O : Outside base a n m m')
        (hab : b + 4 ≤ a ∨ a + n ≤ b) (hb : b + 4 ≤ 2 ^ 64) :
        m'.readW (off base b) 32 = m.readW (off base b) 32 :=
      BitVec.eq_of_toNat_eq (O.w32 hab hb)
    rcases Nat.lt_or_ge i k with h | h
    · rw [read_eq O₂ (by omega) (by omega), e₁ i h]
    · obtain rfl : i = k := by omega
      rw [m₂, Mem.readW_writeW_self32, read_eq O₁ (by omega) (by omega)]

theorem notMask_ok (s : State) {b : Bool} (hc : s.gpr .ecx = bmask b) :
    WP isa (.block [.alu .xor .ecx (.imm (-1))]) s fun t =>
      t.gpr .ecx = bmask (!b) ∧ CKeeps [.ecx] s t := by
  crun [hc]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases b <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- Restore Montgomery one in Y where the Jacobian accumulator is infinity. -/
theorem outFix_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn1 : 1 ≤ K.M.n) (hone : K.one < 2 ^ (64 * K.M.n)) (hy : K.A.y + 8 * K.M.n ≤ size)
    (hz : K.A.z + 8 * K.M.n ≤ size) (hzero : K.zero + 8 * K.M.n ≤ size)
    (hy0 : K.A.y + 8 * K.M.n ≤ K.zero ∨ K.zero + 8 * K.M.n ≤ K.A.y)
    (h0 : wordsVal s.mem base K.zero K.M.n = 0) :
    WP isa (.block K.outFix) s fun t =>
      wordsVal t.mem base K.A.y K.M.n =
        (if wordsVal s.mem base K.A.z K.M.n = 0 then K.one else wordsVal s.mem base K.A.y K.M.n) ∧
      KeepRegs [.eax, .ecx, .edx] s t ∧ Outside base K.A.y (8 * K.M.n) s.mem t.mem := by
  have hn := hs.nowrap
  unfold TCombCfg.outFix
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (nzMask_ok hs hn1 hz) fun s₁ ⟨c₁,k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁.keeps (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selWords_ok hs₁ (decide (wordsVal s.mem base K.A.z K.M.n ≠ 0)) c₁
    (o := K.A.y) (a := K.zero) (b := K.A.y) hy hzero hy (by omega) (.inl (Nat.le_refl _)))
    fun s₂ ⟨e₂,k₂,O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (notMask_ok s₂ (b := decide (wordsVal s.mem base K.A.z K.M.n ≠ 0)) (by rw [k₂.1 _ (by decide), c₁])) fun s₃ ⟨c₃,k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃.keeps (by decide)
  refine WP.mono (orConstWords_ok hs₃ c₃ (v := K.one) (2 * K.M.n) (by omega)) fun t ⟨e₄,k₄,O₄⟩ => ?_
  rw [k₁.2.1] at e₂
  refine ⟨?_, ((k₁.keeps.mono (by decide)).trans (k₂.mono (by decide))).trans
    ((k₃.keeps.mono (by decide)).trans (k₄.mono (by decide))), ?_⟩
  · have hor (x : BitVec 32) : x ||| (0 : BitVec 32) = x := BitVec.or_zero
    have hand (x y : BitVec 32) : (x &&& (0 : BitVec 32)) ||| y = y := by
      have hz : x &&& (0 : BitVec 32) = 0 := BitVec.and_zero
      rw [hz]; exact BitVec.zero_or
    rw [wordsVal_eq_val32]
    by_cases h : wordsVal s.mem base K.A.z K.M.n = 0
    · simp only [h, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
        Bool.not_false, bmask, BitVec.and_allOnes] at e₂ e₄ ⊢
      rw [h0, wordsVal_eq_val32] at e₂
      have hw0 := (val32_eq_zero_iff _ _ _ _).mp e₂
      refine val32_of_shifts _ _ _ _ _ (by rw [show 32 * (2 * K.M.n) = 64 * K.M.n by omega]; exact hone) fun i hi => ?_
      have hzword : s₃.mem.readW (off base (K.A.y + 4 * i)) 32 = 0 :=
        BitVec.eq_of_toNat_eq (by rw [k₃.2.1]; exact hw0 i hi)
      simp only [w32, e₄ i hi, hzword, hor, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    · simp only [h, ne_eq, not_false_eq_true, decide_true, ↓reduceIte,
        Bool.not_true, bmask, Bool.false_eq_true, hand] at e₂ e₄ ⊢
      rw [← e₂, wordsVal_eq_val32]
      exact val32_congr fun i hi => by simp only [w32, e₄ i hi, k₃.2.1]
  · intro x hx
    rw [show 4 * (2 * K.M.n) = 8 * K.M.n by omega] at O₄
    rw [O₄ x hx, k₃.2.1, O₂ x hx, k₁.2.1]

end VG.Proof.Weierstrass.X86

end

/-! ## `TCombJSelect` -/

section

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-- `o = a` unless `c`, in place: `selPt n o a o`, for `o`'s words apart from
each other and from `a`'s. -/
theorem selPtKeep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0)) {n : Nat} {o a : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o a o)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base o.x n else wordsVal s.mem base a.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base o.y n else wordsVal s.mem base a.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base o.z n else wordsVal s.mem base a.z n) ∧
      KeepRegs [.eax, .edx] s s' ∧
      ∀ x, (ofs base x < o.x ∨ o.x + 8 * n ≤ ofs base x) → (ofs base x < o.y ∨ o.y + 8 * n ≤ ofs base x) →
        (ofs base x < o.z ∨ o.z + 8 * n ≤ ofs base x) → s'.mem x = s.mem x := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (selWords_ok hs c hc iox iax iox (by omega_using [xax]) (Or.inl (Nat.le_refl _)))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (selWords_ok hs₁ c (by rw [k₁.gpr _ (by decide), hc]) ioy iay ioy (by omega_using [yay])
    (Or.inl (Nat.le_refl _))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (selWords_ok hs₂ c (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc]) ioz iaz ioz
    (by omega_using [zaz]) (Or.inl (Nat.le_refl _))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, fun x h₁ h₂ h₃ => by rw [O₃ x h₃, O₂ x h₂, O₁ x h₁]⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := o.y) (by omega_using [xy]) (by omega_using [ioy, hn]),
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := o.z) (by omega_using [yz]) (by omega_using [ioz, hn]),
      O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := o.z) (by omega_using [xz]) (by omega_using [ioz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]

end VG.Proof.Weierstrass.X86

end
