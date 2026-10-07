import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV

/-! Direct table selection for public verification scalars. -/
set_option linter.unusedSimpArgs false

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-- A scalar load from the selected entry. -/
theorem direct_load {s : State} {p : Addr} {o : Nat}
    (hp : s.gpr .x16 = p) (ho : o % 8 = 0 ∧ o < 32768)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 o) 8) :
    WP isa (.block [.ldr .x .x4 .x16 o]) s fun t =>
      t.gpr .x4 = word s.mem p o ∧ Keeps [.x4] s t ∧ t.c = s.c := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runBlock_nil, runStep_some, exec, addr, Size.bytes, ho,
    and_self, ite_true, State.load, hp, hr, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_write_self, BitVec.setWidth_eq]
  refine ⟨rfl, ⟨?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  intro r hr
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr)

/-- Copy words from a public address outside the scratch space, preserving
its contents while writing the selected coordinate. -/
theorem directWords_ok {s : State} {base p : Addr} {size src dst value n : Nat}
    (hs : Scr s base size) (hp : s.gpr .x16 = p)
    (hd : dst + 8 * n ≤ size) (hd8 : dst % 8 = 0)
    (hs8 : src % 8 = 0) (hsrc : src + 8 * n ≤ 32768)
    (hr : ∀ i < n, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (src + 8 * i)) 8)
    (hout : ∀ i < n, ∀ b < 8, size ≤ ofs base
      (p + BitVec.ofNat 64 (src + 8 * i) + BitVec.ofNat 64 b)) :
    ∀ k ≤ n, WP isa (.block (TCombCfg.directWords src dst value k)) s fun t =>
      (∀ i < k, word t.mem base (dst + 8 * i) =
        if s.c then word s.mem p (src + 8 * i) else wordOf value i) ∧
      t.c = s.c ∧ KeepRegs [.x4, .x6] s t ∧ Outside base dst (8 * k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl,
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [TCombCfg.directWords, List.range_succ, List.flatMap_append, List.flatMap_singleton,
      WP.block_append_iff]
    refine WP.mono (directWords_ok hs hp hd hd8 hs8 hsrc hr hout k (by omega)) fun s₁ ⟨e₁, c₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [List.append_assoc, WP.block_append_iff]
    refine WP.mono (direct_load (p := p) (o := src + 8 * k) (by rw [k₁.gpr _ (by decide), hp]) (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr k (by omega))) fun s₂ ⟨e₂, k₂, c₂'⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (const64c_ok s₂ .x6 (wordOf value k)) fun s₃ ⟨e₃, k₃, c₃'⟩ => ?_
    have hs₃ := hs₂.of_keeps k₃ (by decide)
    have x4 : s₃.gpr .x4 = word s₁.mem p (src + 8 * k) := by rw [k₃.gpr _ (by decide), e₂]
    have c₃ : s₃.c = s.c := by rw [c₃', c₂', c₁]
    rw [← List.singleton_append, WP.block_append_iff]
    have hsel : WP isa (.block [.csel .x .x4 .x4 .x6]) s₃ fun t =>
        t.gpr .x4 = (if s.c then word s₁.mem p (src + 8 * k) else wordOf value k) ∧
        Keeps [.x4] s₃ t ∧ t.c = s.c := by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec_csel, State.read, x4, e₃, c₃,
        RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.c_write, Option.some.injEq, exists_eq_left']
      refine ⟨?_, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr),
        rfl, rfl, rfl, rfl⟩, ?_⟩
      · cases s.c <;> simp
      · trivial
    refine WP.mono hsel fun s₄ ⟨e₄, k₄, c₄⟩ => ?_
    have hs₄ := hs₃.of_keeps k₄ (by decide)
    refine WP.mono (st_ok hs₄ (d := dst + 8 * k) (by omega) (by omega) .x4) fun t et => ?_
    have mt : t.mem = s₄.mem.writeW (off base (dst + 8 * k)) (s₄.gpr .x4) := by rw [et]
    have kt : KeepRegs [] s₄ t := by subst et; exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    have ct : t.c = s₄.c := by rw [et]
    have O₂ : Outside base (dst + 8 * k) 8 s₄.mem t.mem := by
      rw [mt]; exact writeW_outside _ _ _ (by omega)
    have hm₄ : s₄.mem = s₁.mem := by rw [k₄.mem, k₃.mem, k₂.mem]
    have old : word s₁.mem p (src + 8 * k) = word s.mem p (src + 8 * k) :=
      Mem.readW_congr fun b hb => O₁ _ (Or.inr (by have := hout k (by omega) b (by omega); dsimp only [off]; omega))
    refine ⟨fun i hi => ?_, by rw [ct, c₄], ?_, ?_⟩
    · rcases Nat.lt_or_ge i k with h | h
      · rw [O₂.word (by omega) (by omega), hm₄, e₁ i h]
      · obtain rfl : i = k := by omega
        rw [mt, word_writeW_self, e₄, old]
    · exact k₁.trans ((((Keeps.regs k₂).mono (by sub_regs)).trans ((Keeps.regs k₃).mono (by sub_regs))).trans
        (((Keeps.regs k₄).mono (by sub_regs)).trans (kt.mono (fun _ h => absurd h List.not_mem_nil))))
    · refine (O₁.mono (Nat.le_refl _) (by omega)).trans ?_
      rw [← hm₄]
      exact O₂.mono (by omega) (by omega)

/-- The public entry's address and nonzero flag. -/
theorem directAddress_ok (K : TCombCfg) {s : State} {a : Nat} {p : Addr}
    (ha : a < 2 ^ 64) (hn : 16 * K.M.n < 65536)
    (hp : s.gpr .x16 = p) (h2 : s.gpr .x2 = BitVec.ofNat 64 a)
    (h5 : s.gpr .x5 = 1) (h7 : s.gpr .x7 = 0) :
    WP isa (.block K.directAddress) s fun t =>
      t.gpr .x16 = p + BitVec.ofNat 64 (16 * K.M.n * (a - 1)) ∧
      t.c = decide (1 ≤ a) ∧ Keeps [.x3, .x16, .x17] s t := by
  apply WP.of_runBlock
  simp only [TCombCfg.directAddress, runBlock_cons, runStep_some, runBlock_nil, exec,
    exec_csel, read_x, State.read, h2, h5, h7, hp, RegUpd.gpr_write, RegUpd.c_write,
    RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, BitVec.setWidth_eq, Size.bits,
    show 16 * 0 < 64 from by decide, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  have hc : decide (2 ^ 64 ≤ (BitVec.ofNat 64 a).toNat + (~~~(1 : BitVec 64)).toNat +
      (true).toNat) = decide (1 ≤ a) := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      show (~~~(1 : BitVec 64)).toNat = 2 ^ 64 - 2 from by decide, Bool.toNat_true]
    by_cases h : 1 ≤ a
    · have hh : 2 ^ 64 ≤ a + (2 ^ 64 - 2) + 1 := by omega
      simp only [hh, h, decide_true]
    · have hh : ¬(2 ^ 64 ≤ a + (2 ^ 64 - 2) + 1) := by omega
      simp only [hh, h, decide_false]
  rw [hc]
  refine ⟨?_, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · by_cases h : 1 ≤ a
    · simp only [h, decide_true, ite_true]
      simp only [Bool.toNat_true, BitVec.ofNat_eq_ofNat, Nat.mul_zero, BitVec.shiftLeft_zero]
      rw [BitVec.add_assoc, ← BitVec.neg_eq_not_add, ← BitVec.sub_eq_add_neg]
      change p + (BitVec.ofNat 64 a - BitVec.ofNat 64 1) *
        (BitVec.ofNat 16 (16 * K.M.n)).setWidth 64 = _
      rw [BitVec.ofNat_sub_ofNat_of_le a 1 (by decide) h]
      refine congrArg (fun x : BitVec 64 => p + x) ?_
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt hn, Nat.mod_mod]
      rw [← Nat.mul_mod, Nat.mul_comm]
    · have az : a = 0 := by omega
      simp [h, az]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]

theorem wordsVal_addr (m : Mem) (p : Addr) (e o n : Nat) :
    wordsVal m (p + BitVec.ofNat 64 e) o n = wordsVal m p (e + o) n := by
  refine wordsVal_of_words₂ _ _ _ fun i hi => ?_
  simp only [word, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem directWords_value {m m' : Mem} {base p : Addr} {dst src n value : Nat} {c : Bool}
    (hv : value < 2 ^ (64 * n))
    (h : ∀ i < n, word m' base (dst + 8 * i) = if c then word m p (src + 8 * i) else wordOf value i) :
    wordsVal m' base dst n = if c then wordsVal m p src n else value := by
  cases c
  · exact wordsVal_of_shifts _ _ _ _ _ hv fun i hi => by
      have e := h i hi
      simp only [Bool.false_eq_true, ↓reduceIte] at e
      exact e
  · exact wordsVal_of_words₂ _ _ _ fun i hi => by simpa only [↓reduceIte] using h i hi

/-- Public selection has the same coordinate and frame postcondition as
constant-time selection, but uses just the selected entry. -/
theorem tselectPublic_ok (K : TCombCfg) (hn : K.M.n ≤ 9)
    {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {j a : Nat} {T : Addr}
    (hx19 : s.gpr .x19 = BitVec.ofNat 64 j) (hx2 : s.gpr .x2 = BitVec.ofNat 64 a)
    (ha : a ≤ K.H) (hHpos : 0 < K.H) (htb : K.tblBytes < 65536) (hHlt : K.H < 2 ^ 64)
    (hT : s.syms K.tsym = T)
    (hE : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ size ∧ d % 8 = 0)
    (hap : (K.E.x + 8 * K.M.n ≤ K.E.y ∨ K.E.y + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.x + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.x) ∧
      (K.E.y + 8 * K.M.n ≤ K.E.z ∨ K.E.z + 8 * K.M.n ≤ K.E.y))
    (hone : K.one < 2 ^ (64 * K.M.n))
    (hreg : InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * K.H))
    (hout : ∀ e < K.H, ∀ i < 2 * K.M.n, ∀ b < 8, size ≤ ofs base
      (T + BitVec.ofNat 64 (j * K.tblBytes) + BitVec.ofNat 64 (16 * K.M.n * e + 8 * i) + BitVec.ofNat 64 b)) :
    WP isa (.block K.selectPublic) s fun t =>
      wordsVal t.mem base K.E.x K.M.n = (if 1 ≤ a then
        wordsVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1)) K.M.n else 0) ∧
      wordsVal t.mem base K.E.y K.M.n = (if 1 ≤ a then
        wordsVal s.mem (T + BitVec.ofNat 64 (j * K.tblBytes)) (16 * K.M.n * (a - 1) + 8 * K.M.n) K.M.n
        else K.one) ∧
      wordsVal t.mem base K.E.z K.M.n = (if 1 ≤ a then K.one else 0) ∧
      KeepRegs (.x1 :: .x2 :: .x3 :: .x4 :: .x5 :: .x6 :: .x7 :: .x16 :: .x17 :: entryRegs K.M.n) s t ∧
      Unch base [(K.E.x, 8 * K.M.n), (K.E.y, 8 * K.M.n), (K.E.z, 8 * K.M.n)] s.mem t.mem := by
  have hnw := hs.nowrap
  have ha64 : a < 2 ^ 64 := by omega
  have he : a - 1 < K.H := by omega
  have hEx := hE K.E.x (by simp)
  have hEy := hE K.E.y (by simp)
  have hEz := hE K.E.z (by simp)
  obtain ⟨axy, axz, ayz⟩ := hap
  let B := T + BitVec.ofNat 64 (j * K.tblBytes)
  let P := B + BitVec.ofNat 64 (16 * K.M.n * (a - 1))
  have addr (i : Nat) : P + BitVec.ofNat 64 (8 * i) = B + BitVec.ofNat 64 (16 * K.M.n * (a - 1) + 8 * i) := by
    dsimp only [P]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have out : ∀ i < 2 * K.M.n, ∀ b < 8, size ≤ ofs base (P + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) := by
    intro i hi b hb; rw [addr]; exact hout (a - 1) he i hi b hb
  have reg : ∀ i < 2 * K.M.n, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi; rw [addr]
    obtain ⟨r, hr, hc⟩ := hreg
    refine ⟨r, hr, Region.contains_off hc ?_⟩
    have : 16 * K.M.n * ((a - 1) + 1) ≤ 16 * K.M.n * K.H := Nat.mul_le_mul_left _ he
    rw [Nat.mul_succ] at this
    omega
  rw [TCombCfg.selectPublic, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono_syms (selSetup_ok K hx19 hT htb) fun s₁ ⟨p₁, z₁, one₁, _, k₁⟩ _ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (directAddress_ok K ha64 (by omega) p₁ (by rw [k₁.gpr _ (by decide), hx2]) one₁ z₁)
    fun s₂ ⟨p₂, c₂, k₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have hm₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
  rw [WP.block_append_iff]
  refine WP.mono (directWords_ok (p := P) (src := 0) (value := 0) (n := K.M.n) hs₂ p₂ hEx.1 hEx.2 (by omega)
    (by omega) (fun i hi => by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; simpa only [Nat.zero_add] using reg i (by omega))
    (fun i hi b hb => by simpa only [Nat.zero_add] using out i (by omega) b hb) K.M.n (Nat.le_refl _)) fun s₃ ⟨wx, c₃, k₃, Ox⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have vx := directWords_value (Nat.two_pow_pos (64 * K.M.n)) wx
  rw [hm₂, c₂, wordsVal_addr, Nat.add_zero] at vx
  have source : ∀ i < 2 * K.M.n, word s₃.mem P (8 * i) = word s.mem P (8 * i) := by
    intro i hi
    rw [← hm₂]
    exact Mem.readW_congr fun b hb => Ox _ (Or.inr (by have := out i hi b (by omega); dsimp only [off]; omega))
  rw [WP.block_append_iff]
  refine WP.mono (directWords_ok (p := P) (src := 8 * K.M.n) (value := K.one) (n := K.M.n) hs₃
    (by rw [k₃.gpr _ (by decide)]; exact p₂) hEy.1 hEy.2 (by omega) (by omega)
    (fun i hi => by rw [k₃.rd, k₃.wr, k₂.rd, k₂.wr, k₁.rd, k₁.wr,
      show 8 * K.M.n + 8 * i = 8 * (K.M.n + i) by omega]; exact reg _ (by omega))
    (fun i hi b hb => by rw [show 8 * K.M.n + 8 * i = 8 * (K.M.n + i) by omega]; exact out _ (by omega) b hb)
    K.M.n (Nat.le_refl _)) fun s₄ ⟨wy, c₄, k₄, Oy⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have sy : wordsVal s₃.mem P (8 * K.M.n) K.M.n = wordsVal s.mem P (8 * K.M.n) K.M.n :=
    wordsVal_of_words₂ _ _ _ fun i hi => by
      rw [show 8 * K.M.n + 8 * i = 8 * (K.M.n + i) by omega]; exact source _ (by omega)
  have vy := directWords_value hone wy
  rw [c₃, c₂, sy, wordsVal_addr] at vy
  rw [TCombCfg.selZ, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (selZ_carry s₄ ha64
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide), hx2])
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), one₁])) fun s₅ ⟨c₅, k₅⟩ => ?_
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  refine WP.mono (zWords_ok K hs₅ (by rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide),
      k₂.gpr _ (by decide), z₁]) hEz.1 hEz.2 K.M.n (Nat.le_refl _)) fun t ⟨wz, _, kt, Oz⟩ => ?_
  have b64 : ∀ d ∈ [K.E.x, K.E.y, K.E.z], d + 8 * K.M.n ≤ 2 ^ 64 := fun d hd => by
    have := (hE d hd).1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Oz.wordsVal axz (b64 _ (by simp)), k₅.mem, Oy.wordsVal axy (b64 _ (by simp)), vx]
    simp only [decide_eq_true_eq, B]
  · rw [Oz.wordsVal ayz (b64 _ (by simp)), k₅.mem, vy]
    simp only [decide_eq_true_eq, B]
  · refine wordsVal_of_shifts _ _ _ _ _ (by split <;> [exact hone; exact Nat.two_pow_pos _]) fun i hi => ?_
    rw [wz i hi, c₅]
    by_cases h : 1 ≤ a <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> [rfl; simp]
  · exact ((((((Keeps.regs k₁).mono (by sub_regs)).trans ((Keeps.regs k₂).mono (by sub_regs))).trans
      (k₃.mono (by sub_regs))).trans (k₄.mono (by sub_regs))).trans
      ((Keeps.regs k₅).mono (by sub_regs))).trans (kt.mono (by sub_regs))
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [Oz x hx.2.2, k₅.mem, Oy x hx.2.1, Ox x hx.1, hm₂]

end VG.Proof.Weierstrass.AArch64
