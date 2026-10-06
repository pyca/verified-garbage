import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectY

/-!
# The comb from tables in memory on x86-64: the selection

The entry of table `j` for the magnitude `a` in `r8`, in constant time: the
pass over the table (`selPass_ok`, `TCombSelectPass.lean`, or with AVX2
`selPassY_ok`, `TCombSelectY.lean`: `selPassV_ok`) leaves piece `c` of entry
`a` (zero for `a = 0`) at `E.x + 16 c`, then `selOne_ok` sets `y = R` for
`a = 0` and `Z = R` unless `a = 0` (`select_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- The words the selection stores: those of entry `a` of the table at `X`
if `1 ≤ a ≤ H`, else zero. -/
theorem accVal_word {mem mem' : Mem} {base X : Addr} {n a H o : Nat}
    (h : ∀ c < n, mem'.readW (off base (o + 16 * c)) 128 = accVal mem X (16 * n) (16 * ·) a H c) :
    ∀ i < 2 * n, word mem' base (o + 8 * i) =
      if 1 ≤ a ∧ a ≤ H then word mem X (16 * n * (a - 1) + 8 * i) else 0 := by
  intro i hi
  obtain ⟨c, q, hq, rfl⟩ : ∃ c q, q < 2 ∧ i = 2 * c + q := ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega⟩
  have e := readW_extract mem' (off base (o + 16 * c)) (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * 8 = 64 from rfl, off, Offset.add_add, show o + 16 * c + 8 * q = o + 8 * (2 * c + q) by omega] at e
  rw [Mont.word, off, ← e, h c (by omega), accVal]
  split
  · have e2 := readW_extract mem (X + BitVec.ofNat 64 (16 * n * (a - 1) + 16 * c)) (w := 128)
      (k := 8 * q) (n := 8) (by omega)
    rw [show 8 * 8 = 64 from rfl, Offset.add_add] at e2
    rw [e2, Mont.word, off]
    rw [show 16 * n * (a - 1) + 16 * c + 8 * q = 16 * n * (a - 1) + 8 * (2 * c + q) by omega]
  · simp

/-- Word `q < 2` of a stored accumulator: that of its piece of entry `a` of
the table at `X` if `1 ≤ a ≤ H`, else zero. -/
theorem accVal_word1 {mem mem' : Mem} {base X : Addr} {st : Nat} {po : Nat → Nat} {a H c o q : Nat}
    (h : mem'.readW (off base o) 128 = accVal mem X st po a H c) (hq : q < 2) :
    word mem' base (o + 8 * q) = if 1 ≤ a ∧ a ≤ H then word mem X (st * (a - 1) + po c + 8 * q) else 0 := by
  have e := readW_extract mem' (off base o) (w := 128) (k := 8 * q) (n := 8) (by omega)
  rw [show 8 * 8 = 64 from rfl, off, Offset.add_add] at e
  rw [Mont.word, off, ← e, h, accVal]
  split
  · have e2 := readW_extract mem (X + BitVec.ofNat 64 (st * (a - 1) + po c)) (w := 128)
      (k := 8 * q) (n := 8) (by omega)
    rw [show 8 * 8 = 64 from rfl, Offset.add_add] at e2
    rw [e2, Mont.word, off]
  · simp

/-- `rcx` all ones if `r8 = a` is zero, else zero. -/
theorem isZero_ok (s : State) {a : Nat} (ha : a < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block [.mov .rcx (.reg .r8), .alu .cmp .rcx (.imm 1), .alu .sbb .rcx (.reg .rcx)]) s fun t =>
      t.gpr .rcx = bmask (decide (a = 0)) ∧ Keeps [.rcx] s t ∧ t.xmm = s.xmm := by
  crun [h8, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat = 1 := by decide
    have hx : decide ((BitVec.ofNat 64 a).toNat < 1) = decide (a = 0) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]; exact decide_eq_decide.mpr (by omega)
    rw [BitVec.sub_self, h1, hx]
    cases decide (a = 0) <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `[y + 8 i] |= wordOf v i & rcx` for `i < k`, through `rax`. -/
theorem orSteps_ok {base : Addr} {size v y : Nat} {M : BitVec 64} : ∀ k, ∀ (s : State), Scr s base size →
    s.gpr .rcx = M → y + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap fun i => [.movImm64 .rax (wordOf v i), .alu .and .rax (.reg .rcx),
        .alu .or .rax (.mem (sc (y + 8 * i))), .store (sc (y + 8 * i)) .rax])) s fun t =>
      (∀ i < k, word t.mem base (y + 8 * i) = (wordOf v i &&& M) ||| word s.mem base (y + 8 * i)) ∧
      KeepRegs [.rax] s t ∧ Outside base y (8 * k) s.mem t.mem ∧ t.xmm = s.xmm
  | 0, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _, rfl⟩
  | k + 1, s, hs, hc, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (orSteps_ok k s hs hc (by omega)) fun s₁ ⟨e₁, k₁, O₁, x₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hc₁ : s₁.gpr .rcx = M := by rw [k₁.gpr _ (by decide), hc]
    refine WP.mono (show WP isa (.block [.movImm64 .rax (wordOf v k), .alu .and .rax (.reg .rcx),
        .alu .or .rax (.mem (sc (y + 8 * k))), .store (sc (y + 8 * k)) .rax]) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (off base (y + 8 * k)) ((wordOf v k &&& M) ||| word s₁.mem base (y + 8 * k)) ∧
          KeepRegs [.rax] s₁ s₂ ∧ s₂.xmm = s₁.xmm) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
        State.store64, ea_sc, hc₁, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg,
        RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
        RegUpd.mem_arithFlags, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags, reduceCtorEq, ite_true,
        ite_false, hs₁.rdi, ld_sc hs₁ (d := y + 8 * k) (by omega), st_sc hs₁ (d := y + 8 * k) (by omega),
        Option.bind_some, Option.some.injEq, exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_
    have O₂ : Outside base (y + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun i hi => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)), x₂.trans x₁⟩
    rcases Nat.lt_or_ge i k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ i h]
    · obtain rfl : i = k := by omega
      rw [m₂, word_writeW_self, O₁.word (by omega) (by omega)]

/-- `[z + 8 i] = wordOf v i & rcx` for `i < k`, through `rax`. -/
theorem andSteps_ok {base : Addr} {size v z : Nat} {M : BitVec 64} : ∀ k, ∀ (s : State), Scr s base size →
    s.gpr .rcx = M → z + 8 * k ≤ size →
    WP isa (.block ((List.range k).flatMap fun i => [.movImm64 .rax (wordOf v i), .alu .and .rax (.reg .rcx),
        .store (sc (z + 8 * i)) .rax])) s fun t =>
      (∀ i < k, word t.mem base (z + 8 * i) = wordOf v i &&& M) ∧
      KeepRegs [.rax] s t ∧ Outside base z (8 * k) s.mem t.mem ∧ t.xmm = s.xmm
  | 0, s, _, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _, rfl⟩
  | k + 1, s, hs, hc, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (andSteps_ok k s hs hc (by omega)) fun s₁ ⟨e₁, k₁, O₁, x₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hc₁ : s₁.gpr .rcx = M := by rw [k₁.gpr _ (by decide), hc]
    refine WP.mono (show WP isa (.block [.movImm64 .rax (wordOf v k), .alu .and .rax (.reg .rcx),
        .store (sc (z + 8 * k)) .rax]) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (off base (z + 8 * k)) (wordOf v k &&& M) ∧
          KeepRegs [.rax] s₁ s₂ ∧ s₂.xmm = s₁.xmm) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.store64, ea_sc,
        hc₁, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg,
        RegUpd.mem_setReg, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags,
        RegUpd.xmm_setReg, RegUpd.xmm_arithFlags, reduceCtorEq, ite_true, ite_false, hs₁.rdi,
        st_sc hs₁ (d := z + 8 * k) (by omega), Option.bind_some, Option.some.injEq,
        exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₂ ⟨m₂, k₂, x₂⟩ => ?_
    have O₂ : Outside base (z + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun i hi => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)), x₂.trans x₁⟩
    rcases Nat.lt_or_ge i k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ i h]
    · obtain rfl : i = k := by omega
      rw [m₂, word_writeW_self]

/-- `rcx = ~rcx`. -/
theorem notMask_ok (s : State) {b : Bool} (hc : s.gpr .rcx = bmask b) :
    WP isa (.block [.alu .xor .rcx (.imm (-1))]) s fun t =>
      t.gpr .rcx = bmask (!b) ∧ Keeps [.rcx] s t ∧ t.xmm = s.xmm := by
  crun [hc, RegUpd.xmm_setReg, RegUpd.xmm_arithFlags]
  refine ⟨by cases b <;> decide, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `y |= R` if the magnitude `r8 = a` is zero, and `Z = R` unless it is, word
by word, through `rax` and `rcx`. -/
theorem selOne_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hy : K.E.y + 8 * K.M.n ≤ size)
    (hz : K.E.z + 8 * K.M.n ≤ size) (hyz : K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y) :
    WP isa (.block K.selOne) s fun t =>
      (∀ i < K.M.n, word t.mem base (K.E.y + 8 * i) =
        (wordOf K.one i &&& bmask (decide (a = 0))) ||| word s.mem base (K.E.y + 8 * i)) ∧
      (∀ i < K.M.n, word t.mem base (K.E.z + 8 * i) = wordOf K.one i &&& bmask (!decide (a = 0))) ∧
      KeepRegs [.rax, .rcx] s t ∧ Unch base [(K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem ∧
      t.xmm = s.xmm := by
  have hn := hs.nowrap
  unfold TCombCfg.selOne
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (isZero_ok s ha h8) fun s₁ ⟨c₁, k₁, x₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.mono (orSteps_ok K.M.n s₁ hs₁ c₁ hy) fun s₂ ⟨e₂, k₂, O₂, x₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (notMask_ok s₂ (b := decide (a = 0)) (by rw [k₂.gpr _ (by decide), c₁]))
    fun s₃ ⟨c₃, k₃, x₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.mono (andSteps_ok K.M.n s₃ hs₃ c₃ hz) fun t ⟨e₄, k₄, O₄, x₄⟩ =>
    ⟨fun i hi => ?_, e₄, ?_, ?_, by rw [x₄, x₃, x₂, x₁]⟩
  · rw [O₄.word (by omega) (by omega), k₃.2.1, e₂ i hi, k₁.2.1]
  · exact ((Keeps.regs k₁).mono (by decide)).trans ((k₂.mono (by decide)).trans
      (((Keeps.regs k₃).mono (by decide)).trans (k₄.mono (by decide))))
  · have U := ((O₂.unch.trans (show Unch base [] s₂.mem s₃.mem by rw [k₃.2.1]; exact Unch.refl _ _ _)).trans
      O₄.unch)
    rw [k₁.2.1] at U
    exact U.mono fun w hw => by simp only [List.append_nil, List.mem_append] at hw; simp only [List.mem_cons,
      List.not_mem_nil, or_false]; rcases hw with hw | hw <;> simp only [List.mem_singleton] at hw <;>
      simp [hw]

/-- Numbers with the same words. -/
theorem wordsVal_congr₂ {m m' : Mem} {b b' : Addr} : ∀ (o o' k : Nat),
    (∀ i < k, word m' b' (o' + 8 * i) = word m b (o + 8 * i)) → wordsVal m' b' o' k = wordsVal m b o k
  | _, _, 0, _ => rfl
  | o, o', k + 1, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    rw [wordsVal, wordsVal, h0, wordsVal_congr₂ (o + 8) (o' + 8) k fun i hi => by
      rw [show o + 8 + 8 * i = o + 8 * (i + 1) by omega, show o' + 8 + 8 * i = o' + 8 * (i + 1) by omega]
      exact h (i + 1) (by omega)]

theorem Unch.split {base : Addr} {o k : Nat} {m m' : Mem} (h : Unch base [(o, 2 * k)] m m') :
    Unch base [(o, k), (o + k, k)] m m' := fun x hx => h x fun w hw => by
  simp only [List.mem_singleton] at hw; subst hw
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  dsimp only at h1 h2 ⊢; omega

/-- What the selection leaves: in `E`, entry `a`'s `x` and `y` (of the table
at `X`) and `R` if `a ≥ 1`, else `(0, R, 0)`. -/
structure SelPost (K : TCombCfg) (base : Addr) (s : State) (a : Nat) (X : Addr) (t : State) : Prop where
  x : wordsVal t.mem base K.E.x K.M.n = if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1)) K.M.n else 0
  y : wordsVal t.mem base K.E.y K.M.n =
    if 1 ≤ a then wordsVal s.mem X (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n else K.one
  z : wordsVal t.mem base K.E.z K.M.n = if 1 ≤ a then K.one else 0
  keep : KeepRegs [.rax, .rcx, .rdx] s t
  unch : Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem

theorem bv_and_or_true (x y : BitVec 64) : (x &&& bmask true) ||| y = x ||| y := by
  rw [show bmask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
theorem bv_and_or_false (x y : BitVec 64) : (x &&& bmask false) ||| y = y := by
  rw [show bmask false = 0 from rfl]; simp
theorem bv_and_true (x : BitVec 64) : x &&& bmask true = x := by
  rw [show bmask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
theorem bv_or_zero (x : BitVec 64) : x ||| 0 = x := by simp
theorem bv_and_false (x : BitVec 64) : x &&& bmask false = 0 := by
  rw [show bmask false = 0 from rfl]; simp

/-- The words of `v < 2^(64 k)`, word by word, are `v`. -/
theorem wordsVal_wordOf {m : Mem} {b : Addr} {o k v : Nat} (hv : v < 2 ^ (64 * k))
    (h : ∀ i < k, word m b (o + 8 * i) = wordOf v i) : wordsVal m b o k = v :=
  wordsVal_of_shifts m b o k v hv h

/-- Zero words. -/
theorem wordsVal_zeros {m : Mem} {b : Addr} {o k : Nat} (h : ∀ i < k, word m b (o + 8 * i) = 0) :
    wordsVal m b o k = 0 :=
  wordsVal_of_shifts m b o k 0 (Nat.two_pow_pos _) fun i hi => by rw [h i hi, Nat.zero_shiftRight]; rfl

/-- The entry of table `rbx = j` for the magnitude `r8 = a ≤ H` into `E`:
selected from the table at `T + j · tblBytes`, the static `tsym`'s address
plus `j` tables. -/
theorem select_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hn : 1 ≤ K.M.n ∧ K.M.n ≤ 14) (hH : K.H < 2 ^ 31) (htb : K.tblBytes < 2 ^ 31)
    (hexy : K.E.y = K.E.x + 8 * K.M.n) (hy : K.E.y + 8 * K.M.n ≤ size) (hz : K.E.z + 8 * K.M.n ≤ size)
    (hxz : K.E.x + 16 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) (hone : K.one < 2 ^ (64 * K.M.n))
    {j a : Nat} {T : Addr} (hb : s.gpr .rbx = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = BitVec.ofNat 64 a)
    (ha : a ≤ K.H) (hT : s.syms K.tsym = T)
    (hreg : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (j * K.tblBytes)) K.tblBytes) :
    WP isa (.block K.select) s (SelPost K base s a (T + BitVec.ofNat 64 (j * K.tblBytes))) := by
  have hnw := hs.nowrap
  have htbe : K.tblBytes = 16 * K.M.n * K.H := rfl
  rw [TCombCfg.select, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (selSetup_ok K s hb hT htb) fun s₁ ⟨x₁, k₁, _, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have h8₁ : s₁.gpr .r8 = BitVec.ofNat 64 a := by rw [k₁.1 _ (by decide), h8]
  have hr : ∀ e < K.H, ∀ c < K.M.n, InRegions (s₁.rd ++ s₁.wr)
      (T + BitVec.ofNat 64 (j * K.tblBytes) + BitVec.ofNat 64 (16 * K.M.n * e + 16 * c)) 16 := by
    intro e he c hc
    rw [k₁.2.2.1, k₁.2.2.2]
    refine VG.CallLay.inRegions_sub hreg ?_ (by omega)
    have := Nat.mul_le_mul_left (16 * K.M.n) (show e + 1 ≤ K.H by omega)
    rw [Nat.mul_succ] at this; omega
  refine WP.mono (selPassV_ok K hs₁ hn.2 hH (by omega) h8₁ x₁ hr (by rw [k₁.2.2.1, k₁.2.2.2]; exact hreg) htb
    (by omega)) fun s₂ ⟨a₂, O₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have h8₂ : s₂.gpr .r8 = BitVec.ofNat 64 a := by rw [k₂.gpr _ (by decide), h8₁]
  refine WP.mono (selOne_ok K hs₂ (by omega) h8₂ hy hz (by omega)) fun t ⟨ey, ez, k₃, U₃, _⟩ => ?_
  have W := accVal_word a₂
  rw [k₁.2.1] at W
  have hxw : ∀ i < K.M.n, word t.mem base (K.E.x + 8 * i) = word s₂.mem base (K.E.x + 8 * i) := fun i hi =>
    U₃.word (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> dsimp only <;> omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [hxw i hi, W i (by omega), ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [hxw i hi, W i (by omega), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  · have hyw : ∀ i < K.M.n, word s₂.mem base (K.E.y + 8 * i) =
        if 1 ≤ a ∧ a ≤ K.H then word s.mem (T + BitVec.ofNat 64 (j * K.tblBytes))
          (16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i) else 0 := fun i hi => by
      rw [hexy, show K.E.x + 8 * K.M.n + 8 * i = K.E.x + 8 * (K.M.n + i) by omega, W _ (by omega),
        show 16 * K.M.n * (a - 1) + 8 * (K.M.n + i) = 16 * K.M.n * (a - 1) + 8 * K.M.n + 8 * i by omega]
    by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_congr₂ _ _ _ fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, ha⟩),
          decide_eq_false (show ¬ a = 0 by omega), bv_and_or_false]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_wordOf hone fun i hi => by
        rw [ey i hi, hyw i hi, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          decide_eq_true (show a = 0 by omega), bv_and_or_true, bv_or_zero]
  · by_cases h1 : 1 ≤ a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      exact wordsVal_wordOf hone fun i hi => by
        rw [ez i hi, decide_eq_false (show ¬ a = 0 by omega), Bool.not_false, bv_and_true]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      exact wordsVal_zeros fun i hi => by
        rw [ez i hi, decide_eq_true (show a = 0 by omega), Bool.not_true, bv_and_false]
  · exact ((Keeps.regs k₁).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))
  · have U₂ : Unch base [(K.E.x, 8 * K.M.n), (K.E.x + 8 * K.M.n, 8 * K.M.n)] s.mem s₂.mem := by
      rw [← k₁.2.1]
      exact Unch.split (by rw [show 2 * (8 * K.M.n) = 16 * K.M.n by omega]; exact O₂.unch)
    rw [← hexy] at U₂
    exact (U₂.trans U₃).mono fun w hw => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with h | h | h | h <;> simp [h]

end VG.Proof.Weierstrass.X86_64
