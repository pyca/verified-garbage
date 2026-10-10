import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.BytesLen

/-!
# Short Weierstrass curves on AArch64: numbers of `len` bytes

For encodings that are not whole words (P-521's 66 bytes in nine words):
`loadBytes len n o src` reads the `len` bytes at `src`, big-endian, into
`[o]` (`loadBytes_ok`), its whole words through `x17` when `len` is not a
multiple of 8 (`ldr` takes only multiples of 8), its top word from the first
eight bytes shifted right; `shrWords n o sh` shifts `[o]` right by `sh` bits
in place (`shrWords_ok`), a word at a time by `extr`; and
`storeBytes len n dst d a` writes `[a]` masked with `x3` to the `len` bytes
at `dst + d` (`storeBytes_ok`), its top word a byte at a time.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

/-! ## Single instructions -/

/-- `d = n + imm`. -/
theorem addImm_ok (s : State) {d n : Reg} {imm : Nat} (h : imm < 4096) :
    WP isa (.block [.addImm .x d n imm]) s fun s' =>
      s'.gpr d = s.gpr n + BitVec.ofNat 64 imm ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_addImm_x h, runStep_some, runBlock_nil, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq]

/-- `d = n >>> sh`. -/
theorem lsr_ok (s : State) {d n : Reg} {sh : Nat} (h : sh < 64) :
    WP isa (.block [.lsr .x d n sh]) s fun s' => s'.gpr d = s.gpr n >>> sh ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_lsr_x h, runStep_some, runBlock_nil, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq]

/-- `d = ` bits `sh … sh + 63` of `hi : lo`. -/
theorem extr_ok (s : State) {d hi lo : Reg} {sh : Nat} (h : sh < 64) :
    WP isa (.block [.extr .x d hi lo sh]) s fun s' =>
      s'.gpr d = (s.gpr hi ++ s.gpr lo).extractLsb' sh 64 ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_extr (sz := .x) (show sh < Size.x.bits from h), runStep_some, runBlock_nil,
    read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq]

/-- `extr` of two words is the low word shifted right, or'd with the low
`sh` bits of the high word rotated to the top. -/
theorem extr_eq (hi lo : BitVec 64) {sh : Nat} (h0 : 0 < sh) (h64 : sh < 64) :
    (hi ++ lo).extractLsb' sh 64 =
      (lo >>> sh) ||| (hi &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi64
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    hi64, decide_true, Bool.true_and]
  rw [Nat.mod_eq_of_lt h64]
  by_cases h : sh + i < 64
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
      Nat.testBit_two_pow_sub_one, decide_eq_false (by omega_arith : ¬ sh + i < sh)]
    simp only [Bool.and_false, Bool.or_false]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)),
      Nat.testBit_two_pow_sub_one, decide_eq_true (by omega_arith : i - (64 - sh) < sh),
      decide_eq_true (by omega_arith : i - (64 - sh) < 64), show sh + i - 64 = i - (64 - sh) by omega_arith,
      BitVec.getLsbD_of_ge lo (sh + i) (by omega_arith)]
    simp only [Bool.and_true, Bool.false_or]

/-! ## Loads

A top word beyond the encoding is zero, allowing P-192’s 24-byte values
to use four-word arithmetic.
-/

/-- One word of `loadBytes`. -/
def ldStepL (len o : Nat) (src : Reg) (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ len then
    if len % 8 = 0 then [.ldr .x .x5 src (len - 8 * (j + 1)), .rev .x5 .x5, st .x5 (o + 8 * j)]
    else [.addImm .x .x17 src (len - 8 * (j + 1)), .ldr .x .x5 .x17 0, .rev .x5 .x5, st .x5 (o + 8 * j)]
  else if len ≤ 8 * j then const64 .x5 0 ++ [st .x5 (o + 8 * j)]
  else [.ldr .x .x5 src 0, .rev .x5 .x5, .lsr .x .x5 .x5 (8 * (8 * (j + 1) - len)), st .x5 (o + 8 * j)]

theorem loadBytes_eq (len n o : Nat) (src : Reg) :
    loadBytes len n o src = (List.range n).flatMap (ldStepL len o src) := rfl

/-- The word `j` that `loadBytes` reads from `p`. -/
def ldWord (m : Mem) (p : Addr) (len j : Nat) : BitVec 64 :=
  if 8 * (j + 1) ≤ len then byteRev64 (m.readW (p + BitVec.ofNat 64 (len - 8 * (j + 1))) 64)
  else byteRev64 (m.readW p 64) >>> (8 * (8 * (j + 1) - len))

/-- Word `k` of `loadBytes`. -/
theorem ldStepL_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len o k : Nat}
    {src : Reg} (ho : o + 8 * k + 8 ≤ size) (ho8 : o % 8 = 0) (h8 : 8 ≤ len)
    (hk : 8 * k ≤ len) (hl : len ≤ 4096)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8) :
    WP isa (.block (ldStepL len o src k)) s fun s' =>
      s'.mem = s.mem.writeW (off base (o + 8 * k)) (ldWord s.mem (s.gpr src) len k) ∧
      KeepRegs [.x5, .x17] s s' := by
  by_cases hc : 8 * (k + 1) ≤ len
  · by_cases h8m : len % 8 = 0
    · rw [ldStepL, ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true h8m),
        show ([.ldr .x .x5 src (len - 8 * (k + 1)), .rev .x5 .x5, st .x5 (o + 8 * k)] : List Instr) =
          [.ldr .x .x5 src (len - 8 * (k + 1)), .rev .x5 .x5] ++ [st .x5 (o + 8 * k)] from rfl,
        WP.block_append_iff]
      refine WP.mono (ldRev_ok s (t := .x5) ⟨by omega_arith, by omega_arith⟩ (hr _ (by omega_arith))) fun s₁ ⟨v₁, k₁⟩ => ?_
      have hs₁ := hs.of_keeps k₁ (by decide)
      refine WP.mono (st_out hs₁ (o := o + 8 * k) (by omega_arith) (by omega_arith) .x5) fun s₂ ⟨m₂, k₂, _⟩ => ⟨?_, ?_⟩
      · rw [m₂, v₁, k₁.mem, ldWord, ite_eq_left_of_eq_true _ _ (eq_true hc)]
      · exact ((Keeps.regs k₁).mono (by simp)).trans (k₂.mono (by simp))
    · rw [ldStepL, ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_right_of_eq_false _ _ (eq_false h8m),
        show ([.addImm .x .x17 src (len - 8 * (k + 1)), .ldr .x .x5 .x17 0, .rev .x5 .x5, st .x5 (o + 8 * k)] :
          List Instr) = [.addImm .x .x17 src (len - 8 * (k + 1))] ++
            ([.ldr .x .x5 .x17 0, .rev .x5 .x5] ++ [st .x5 (o + 8 * k)]) from rfl,
        WP.block_append_iff]
      refine WP.mono (addImm_ok s (d := .x17) (n := src) (show len - 8 * (k + 1) < 4096 by omega_arith))
        fun s₀ ⟨a₀, k₀⟩ => ?_
      have hp : s₀.gpr .x17 + BitVec.ofNat 64 0 = s.gpr src + BitVec.ofNat 64 (len - 8 * (k + 1)) := by
        rw [BitVec.add_zero, a₀]
      rw [WP.block_append_iff]
      refine WP.mono (ldRev_ok s₀ (t := .x5) (r := .x17) (e := 0) ⟨by decide, by decide⟩
        (by rw [k₀.rd, k₀.wr, hp]; exact hr _ (by omega_arith))) fun s₁ ⟨v₁, k₁⟩ => ?_
      have hs₁ := (hs.of_keeps k₀ (by decide)).of_keeps k₁ (by decide)
      refine WP.mono (st_out hs₁ (o := o + 8 * k) (by omega_arith) (by omega_arith) .x5) fun s₂ ⟨m₂, k₂, _⟩ => ⟨?_, ?_⟩
      · rw [m₂, v₁, hp, k₁.mem, k₀.mem, ldWord, ite_eq_left_of_eq_true _ _ (eq_true hc)]
      · exact (((Keeps.regs k₀).mono (by simp)).trans ((Keeps.regs k₁).mono (by simp))).trans
          (k₂.mono (by simp))
  · by_cases hz : len ≤ 8 * k
    · have hshift : 8 * (8 * (k + 1) - len) = 64 := by omega_arith
      rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_left_of_eq_true _ _ (eq_true hz)]
      change WP isa (.block (const64 .x5 0 ++ [st .x5 (o + 8 * k)])) s _
      rw [WP.block_append_iff]
      refine WP.mono (const64_ok s .x5 0) fun s₁ ⟨v₁, k₁⟩ => ?_
      have hs₁ := hs.of_keeps k₁ (by decide)
      refine WP.mono (st_out hs₁ (o := o + 8 * k) (by omega_arith) (by omega_arith) .x5)
        fun s₂ ⟨m₂, k₂, _⟩ => ⟨?_, ?_⟩
      · simp [m₂, v₁, k₁.mem, ldWord, hc, hshift, BitVec.ushiftRight_eq_zero (Nat.le_refl 64)]
      · exact ((Keeps.regs k₁).mono (by simp)).trans (k₂.mono (by simp))
    · rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc),
        ite_eq_right_of_eq_false _ _ (eq_false hz),
        show ([.ldr .x .x5 src 0, .rev .x5 .x5, .lsr .x .x5 .x5 (8 * (8 * (k + 1) - len)), st .x5 (o + 8 * k)] :
          List Instr) = [.ldr .x .x5 src 0, .rev .x5 .x5] ++
            ([.lsr .x .x5 .x5 (8 * (8 * (k + 1) - len))] ++ [st .x5 (o + 8 * k)]) from rfl,
        WP.block_append_iff]
      refine WP.mono (ldRev_ok s (t := .x5) (e := 0) ⟨by decide, by decide⟩ (hr _ (by omega_arith)))
        fun s₁ ⟨v₁, k₁⟩ => ?_
      rw [WP.block_append_iff]
      refine WP.mono (lsr_ok s₁ (d := .x5) (n := .x5) (show 8 * (8 * (k + 1) - len) < 64 by omega_arith))
        fun s₂ ⟨v₂, k₂⟩ => ?_
      have hs₂ := (hs.of_keeps k₁ (by decide)).of_keeps k₂ (by decide)
      refine WP.mono (st_out hs₂ (o := o + 8 * k) (by omega_arith) (by omega_arith) .x5) fun s₃ ⟨m₃, k₃, _⟩ => ⟨?_, ?_⟩
      · rw [m₃, v₂, v₁, k₂.mem, k₁.mem, BitVec.add_zero, ldWord, ite_eq_right_of_eq_false _ _ (eq_false hc)]
      · exact (((Keeps.regs k₁).mono (by simp)).trans ((Keeps.regs k₂).mono (by simp))).trans
          (k₃.mono (by simp))

theorem ldStepsL_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .x5) (hsrc' : src ≠ .x17) (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0)
    (h8 : 8 ≤ len) (hlo : 8 * n ≤ len + 8) (hhi : len ≤ 8 * n) (hl : len ≤ 4096)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, len⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (ldStepL len o src))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = ldWord s.mem (s.gpr src) len j) ∧
      KeepRegs [.x5, .x17] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ldStepsL_ok hs hsrc hsrc' ho ho8 h8 hlo hhi hl hr hd k (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simp [hsrc, hsrc'])
    have hkeep : ∀ d, d + 8 ≤ len → s₁.mem.readW (s.gpr src + BitVec.ofNat 64 d) 64 =
        s.mem.readW (s.gpr src + BitVec.ofNat 64 d) 64 := fun d hd' =>
      readW_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega_arith)) hd (by omega_arith)
        (by omega_arith) (by omega_arith)
    refine WP.mono (ldStepL_ok hs₁ (k := k) (by omega_arith) ho8 h8 (by omega_arith) hl
      (fun d hd' => by rw [k₁.rd, k₁.wr, hp₁]; exact hr d hd')) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega_arith) (by omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₂, word_writeW_self, hp₁, ldWord, ldWord]
      split
      · rw [hkeep _ (by omega_arith)]
      · rw [show s.gpr src = s.gpr src + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm,
          hkeep _ (by omega_arith)]

/-- `[o] = ` the `len` bytes at `src`, big-endian (`8 (n - 1) ≤ len ≤ 8 n`,
`8 ≤ len`). -/
theorem loadBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .x5) (hsrc' : src ≠ .x17) (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0)
    (h8 : 8 ≤ len) (hlo : 8 * n ≤ len + 8) (hhi : len ≤ 8 * n) (hl : len ≤ 4096)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, len⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBytes len n o src)) s fun s' =>
      wordsVal s'.mem base o n = Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr src) len) ∧
      KeepRegs [.x5, .x17] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBytes_eq]
  refine WP.mono (ldStepsL_ok hs hsrc hsrc' ho ho8 h8 hlo hhi hl hr hd n (Nat.le_refl _))
    fun s' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega_arith⟩
  exact wordsVal_eq_ofBytes_len _ _ _ _ o n' len (by omega_arith) hhi fun j hj => e j hj

/-! ## Shifting right in place -/

/-- One word of `shrWords`. -/
def shrStep (n o sh j : Nat) : List Instr :=
  [ld .x1 (o + 8 * j)] ++
  (if j + 1 < n then [ld .x2 (o + 8 * (j + 1)), .extr .x .x1 .x2 .x1 sh] else [.lsr .x .x1 .x1 sh]) ++
  [st .x1 (o + 8 * j)]

theorem shrWords_eq (n o sh : Nat) : shrWords n o sh = (List.range n).flatMap (shrStep n o sh) := rfl

/-- Word `j` of `[o]` shifted right by `sh`, from the words of `m`. -/
def shrWord (m : Mem) (base : Addr) (n o sh j : Nat) : BitVec 64 :=
  if j + 1 < n then (word m base (o + 8 * j) >>> sh) |||
    (word m base (o + 8 * (j + 1)) &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh
  else word m base (o + 8 * j) >>> sh

/-- Word `k` of `shrWords`, from words `k` and `k + 1` of `m`. -/
theorem shrStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh k : Nat}
    (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) (hk : k < n) {m : Mem}
    (hm : ∀ j, k ≤ j → j < n → word s.mem base (o + 8 * j) = word m base (o + 8 * j)) :
    WP isa (.block (shrStep n o sh k)) s fun s' =>
      s'.mem = s.mem.writeW (off base (o + 8 * k)) (shrWord m base n o sh k) ∧ KeepRegs [.x1, .x2] s s' := by
  rw [shrStep, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := o + 8 * k) (by omega_arith) (by omega_arith) .x1) fun s₁ ⟨l₁, k₁, _⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  by_cases hc : k + 1 < n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := o + 8 * (k + 1)) (by omega_arith) (by omega_arith) .x2) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    refine WP.mono (extr_ok s₂ (d := .x1) (hi := .x2) (lo := .x1) hsh') fun s₃ ⟨v₃, k₃⟩ => ?_
    have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
    refine WP.mono (st_out hs₃ (o := o + 8 * k) (by omega_arith) (by omega_arith) .x1) fun s₄ ⟨m₄, k₄, _⟩ => ⟨?_, ?_⟩
    · rw [m₄, v₃, l₂, k₂.gpr _ (by decide), l₁, k₃.mem, k₂.mem, k₁.mem, extr_eq _ _ (by omega_arith) hsh',
        shrWord, ite_eq_left_of_eq_true _ _ (eq_true hc), hm k (Nat.le_refl _) hk, hm (k + 1) (by omega_arith) hc]
    · exact ((((Keeps.regs k₁).mono (by simp)).trans ((Keeps.regs k₂).mono (by simp))).trans
        ((Keeps.regs k₃).mono (by simp))).trans (k₄.mono (by simp))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    refine WP.mono (lsr_ok s₁ (d := .x1) (n := .x1) hsh') fun s₂ ⟨v₂, k₂⟩ => ?_
    have hs₂ := hs₁.of_keeps k₂ (by decide)
    refine WP.mono (st_out hs₂ (o := o + 8 * k) (by omega_arith) (by omega_arith) .x1) fun s₃ ⟨m₃, k₃, _⟩ => ⟨?_, ?_⟩
    · rw [m₃, v₂, l₁, k₂.mem, k₁.mem, shrWord, ite_eq_right_of_eq_false _ _ (eq_false hc),
        hm k (Nat.le_refl _) hk]
    · exact (((Keeps.regs k₁).mono (by simp)).trans ((Keeps.regs k₂).mono (by simp))).trans
        (k₃.mono (by simp))

theorem shrSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (shrStep n o sh))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = shrWord s.mem base n o sh j) ∧
      KeepRegs [.x1, .x2] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (shrSteps_ok hs ho ho8 hsh hsh' k (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    refine WP.mono (shrStep_ok hs₁ ho ho8 hsh hsh' (k := k) (by omega_arith) (m := s.mem)
      fun j hj _ => O₁.word (by omega_arith) (by omega_arith)) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega_arith) (by omega_arith), e₁ j h]
    · obtain rfl : j = k := by omega_arith
      rw [m₂, word_writeW_self]

/-- `[o] = [o] >> sh`, `n` words, for `0 < sh < 64`. -/
theorem shrWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) :
    WP isa (.block (shrWords n o sh)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base o n >>> sh ∧
      KeepRegs [.x1, .x2] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [shrWords_eq]
  exact WP.mono (shrSteps_ok hs ho ho8 hsh hsh' n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨wordsVal_shr _ _ _ _ _ _ (by omega_arith) hsh' fun j hj => e j hj, k, O⟩

/-! ## Stores -/

/-- A whole word of `storeBytes`. -/
def stStepW (len : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [ld .x1 (a + 8 * j), .logic .and .x .x1 .x1 .x3, .rev .x1 .x1] ++
  (if (d + len) % 8 = 0 then [.str .x .x1 dst (d + (len - 8 * (j + 1)))]
  else [.addImm .x .x17 dst (d + (len - 8 * (j + 1))), .str .x .x1 .x17 0])

/-- Byte `i` of a top word of `t` bytes in `x1`. -/
def stByte (t : Nat) (dst : Reg) (d i : Nat) : List Instr :=
  if t - 1 - i = 0 then [.strb .x1 dst (d + i)]
  else [.lsr .x .x2 .x1 (8 * (t - 1 - i)), .strb .x2 dst (d + i)]

/-- A top word of `t` bytes. -/
def stTop (t : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [ld .x1 (a + 8 * j), .logic .and .x .x1 .x1 .x3] ++ (List.range t).flatMap (stByte t dst d)

theorem storeBytes_eq (len n : Nat) (dst : Reg) (d a : Nat) :
    storeBytes len n dst d a = (List.range n).flatMap fun j =>
      if 8 * (j + 1) ≤ len then stStepW len dst d a j else stTop (len - 8 * j) dst d a j := rfl

/-- `[n + off] = ` the low byte of `t`. -/
theorem strb_ok (s : State) {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    WP isa (.block [.strb t n off]) s fun s' =>
      s' = { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (BitVec.ofNat 8 (s.gpr t).toNat) } := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, addr, Nat.mod_one, show off < 4096 * 1 by omega_arith, true_and, ite_true,
    Option.bind_some, State.store, h, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  have hv : ((s.read .w t).setWidth 8 : BitVec (8 * 1)) = BitVec.ofNat 8 (s.gpr t).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [State.read, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Size.bits]
    exact Nat.mod_mod_of_dvd _ (by decide)
  rw [hv]; rfl

/-- One whole word: the byte reversal of the masked word `j` to
`dst + d + len - 8 (j + 1)`. -/
theorem stStepW_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len d a j : Nat}
    {dst : Reg} (hdst : dst ≠ .x1) (ha : a + 8 * j + 8 ≤ size) (ha8 : a % 8 = 0)
    (hj : 8 * (j + 1) ≤ len) (hdl : d + len < 4096)
    (hw : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1))) 8) :
    WP isa (.block (stStepW len dst d a j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1)))
        (byteRev64 (word s.mem base (a + 8 * j) &&& s.gpr .x3)) ∧ KeepRegs [.x1, .x17] s s' := by
  have hq : s.gpr dst + BitVec.ofNat 64 (d + (len - 8 * (j + 1))) =
      s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1)) := (Offset.add_add _ _ _).symm
  rw [stStepW, WP.block_append_iff, show ([ld .x1 (a + 8 * j), .logic .and .x .x1 .x1 .x3, .rev .x1 .x1] :
    List Instr) = [ld .x1 (a + 8 * j)] ++ [.logic .and .x .x1 .x1 .x3, .rev .x1 .x1] from rfl,
    WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := a + 8 * j) (by omega_arith) (by omega_arith) .x1) fun s₁ ⟨l₁, k₁, _⟩ => ?_
  refine WP.mono (andRev_ok s₁) fun s₂ ⟨v₂, k₂⟩ => ?_
  have hq₂ : s₂.gpr dst = s.gpr dst := by
    rw [k₂.gpr _ (by simpa using hdst), k₁.gpr _ (by simpa using hdst)]
  have hx3 : s₁.gpr .x3 = s.gpr .x3 := k₁.gpr _ (by decide)
  have hK : KeepRegs [.x1, .x17] s s₂ := ((Keeps.regs k₁).mono (by simp)).trans ((Keeps.regs k₂).mono (by simp))
  by_cases h8 : (d + len) % 8 = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h8)]
    refine WP.mono (strReg_ok s₂ (r := dst) (t := .x1) ⟨by omega_arith, by omega_arith⟩
      (by rw [k₂.wr, k₁.wr, hq₂, hq]; exact hw)) fun s₃ e₃ => ?_
    subst e₃
    exact ⟨by rw [hq₂, hq, v₂, l₁, hx3, k₂.mem, k₁.mem], hK.trans ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h8), ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (addImm_ok s₂ (d := .x17) (n := dst) (show d + (len - 8 * (j + 1)) < 4096 by omega_arith))
      fun s₃ ⟨a₃, k₃⟩ => ?_
    have hp : s₃.gpr .x17 + BitVec.ofNat 64 0 =
        s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1)) := by
      rw [BitVec.add_zero, a₃, hq₂, hq]
    refine WP.mono (strReg_ok s₃ (r := .x17) (t := .x1) (e := 0) ⟨by decide, by decide⟩
      (by rw [k₃.wr, k₂.wr, k₁.wr, hp]; exact hw)) fun s₄ e₄ => ?_
    subst e₄
    refine ⟨by rw [hp, k₃.gpr _ (by decide), v₂, l₁, hx3, k₃.mem, k₂.mem, k₁.mem], ?_⟩
    exact (hK.trans ((Keeps.regs k₃).mono (by simp))).trans ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem stSteps_wordsL {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len d a : Nat}
    {dst : Reg} (hdst : dst ≠ .x1) (hdst' : dst ≠ .x17) {c : Bool}
    (hc : s.gpr .x3 = (if c then BitVec.allOnes 64 else 0))
    {k : Nat} (ha : a + 8 * k ≤ size) (ha8 : a % 8 = 0) (hlen : 8 * k ≤ len) (hdl : d + len < 4096)
    (hl : len ≤ 2 ^ 64)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * k⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, len⟩) : ∀ k', k' ≤ k →
    WP isa (.block ((List.range k').flatMap (stStepW len dst d a))) s fun s' =>
      (∀ j < k', s'.mem.readW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1))) 64 =
        byteRev64 (word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0))) ∧
      KeepRegs [.x1, .x17] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) (len - 8 * k') (8 * k') s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k' + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stSteps_wordsL hs hdst hdst' hc ha ha8 hlen hdl hl hw hd k' (by omega_arith))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simp [hdst, hdst'])
    have hc₁ : s₁.gpr .x3 = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hword : word s₁.mem base (a + 8 * k') = word s.mem base (a + 8 * k') := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k')) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k')) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega_arith)) hd (by omega_arith)
        (by omega_arith) (by omega_arith)
    refine WP.mono (stStepW_ok hs₁ hdst (j := k') (by omega_arith) ha8 (by omega_arith) hdl
      (by rw [k₁.wr, hq₁]; exact hw _ _ (by omega_arith))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [hq₁, hc₁, hword] at m₂
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) (len - 8 * (k' + 1)) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (by omega_arith) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k' with h | h
    · rw [m₂, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), e₁ j h]
    · obtain rfl : j = k' := by omega_arith
      rw [m₂, Mem.readW_writeW_self64]

theorem stByte_ok {s : State} {v : BitVec 64} (ha : s.gpr .x1 = v) {dst : Reg} (hdst : dst ≠ .x2)
    {t d i : Nat} (hi : i < t) (ht : t ≤ 8) (hd : d + i < 4096)
    (hw : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stByte t dst d i)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧ KeepRegs [.x2] s s' := by
  have hq : s.gpr dst + BitVec.ofNat 64 (d + i) = s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i :=
    (Offset.add_add _ _ _).symm
  by_cases h0 : t - 1 - i = 0
  · rw [stByte, ite_eq_left_of_eq_true _ _ (eq_true h0)]
    refine WP.mono (strb_ok s (t := .x1) (n := dst) hd (by rw [hq]; exact hw)) fun s' e => ?_
    subst e
    exact ⟨by rw [hq, ha, h0, Nat.mul_zero, Nat.shiftRight_zero], ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  · rw [stByte, ite_eq_right_of_eq_false _ _ (eq_false h0), ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (lsr_ok s (d := .x2) (n := .x1) (show 8 * (t - 1 - i) < 64 by omega_arith)) fun s₁ ⟨v₁, k₁⟩ => ?_
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    refine WP.mono (strb_ok s₁ (t := .x2) (n := dst) hd (by rw [k₁.wr, hq₁, hq]; exact hw)) fun s' e => ?_
    subst e
    exact ⟨by rw [hq₁, hq, v₁, ha, BitVec.toNat_ushiftRight, k₁.mem],
      ((Keeps.regs k₁).mono (by simp)).trans ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩

theorem stBytes_ok {s : State} {v : BitVec 64} (ha : s.gpr .x1 = v) {dst : Reg} (hdst : dst ≠ .x2)
    {t d : Nat} (ht : t ≤ 8) (hdt : d + t ≤ 4096) (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + t ≤ 2 ^ 64)
    (hw : ∀ i < t, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) : ∀ i', i' ≤ t →
    WP isa (.block ((List.range i').flatMap (stByte t dst d))) s fun s' =>
      (∀ i < i', s'.mem (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧
      KeepRegs [.x2] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 i' s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | i' + 1, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stBytes_ok ha hdst ht hdt hq hw i' (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    refine WP.mono (stByte_ok (s := s₁) (v := v) (by rw [k₁.gpr _ (by decide), ha]) hdst (t := t) (d := d)
      (i := i') (by omega_arith) ht (by omega_arith) (by rw [k₁.wr, hq₁]; exact hw i' (by omega_arith))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [hq₁] at m₂
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) i' 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega_arith)
    refine ⟨fun i hi' => ?_, k₁.trans k₂, (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge i i' with h | h
    · rw [O₂ _ (by rw [ofs_off0 _ (by omega_arith)]; omega_arith), e₁ i h]
    · obtain rfl : i = i' := by omega_arith
      rw [m₂, writeW8_self]

theorem stTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst : Reg}
    (hdst : dst ≠ .x1) (hdst' : dst ≠ .x2) {c : Bool} (hc : s.gpr .x3 = (if c then BitVec.allOnes 64 else 0))
    {t d a j : Nat} (ha : a + 8 * (j + 1) ≤ size) (ha8 : a % 8 = 0) (ht : t ≤ 8) (hdt : d + t ≤ 4096)
    (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + t ≤ 2 ^ 64)
    (hw : ∀ i < t, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stTop t dst d a j)) s fun s' =>
      (∀ i < t, s'.mem (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 ((word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0)).toNat >>>
          (8 * (t - 1 - i)))) ∧
      KeepRegs [.x1, .x2] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 t s.mem s'.mem := by
  rw [stTop, WP.block_append_iff, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := a + 8 * j) (by omega_arith) (by omega_arith) .x1) fun s₁ ⟨l₁, k₁, _⟩ => ?_
  refine WP.mono (show WP isa (.block [.logic .and .x .x1 .x1 .x3]) s₁ fun s₂ =>
      s₂.gpr .x1 = s₁.gpr .x1 &&& s₁.gpr .x3 ∧ Keeps [.x1] s₁ s₂ by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, RegUpd.gpr_write_self,
      BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_singleton] at hq
    rw [RegUpd.gpr_write_of_ne _ _ _ hq]) fun s₂ ⟨a₂, k₂⟩ => ?_
  have hq₂ : s₂.gpr dst = s.gpr dst := by
    rw [k₂.gpr _ (by simpa using hdst), k₁.gpr _ (by simpa using hdst)]
  have ha₂ : s₂.gpr .x1 = word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0) := by
    rw [a₂, l₁, k₁.gpr _ (by decide), hc]
  refine WP.mono (stBytes_ok ha₂ hdst' ht hdt (by rw [hq₂]; exact hq)
    (fun i hi => by rw [k₂.wr, k₁.wr, hq₂]; exact hw i hi) t (Nat.le_refl _)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hq₂] at e₃ O₃
  rw [k₂.mem, k₁.mem] at O₃
  exact ⟨e₃, (((Keeps.regs k₁).mono (by simp)).trans ((Keeps.regs k₂).mono (by simp))).trans (k₃.mono (by simp)), O₃⟩

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} : ∀ (k : Nat), (∀ j < k, f j = g j) →
    ((List.range k).flatMap f : List α) = (List.range k).flatMap g
  | 0, _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr k fun j hj => h j (by omega_arith),
      List.flatMap_singleton, List.flatMap_singleton, h k (by omega_arith)]

/-- The `len` bytes at `dst + d` (`8 (n - 1) ≤ len ≤ 8 n`) are `[a]`
big-endian if the mask `x3` is all ones (`c`), zeros if it is zero. -/
theorem storeBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n d a : Nat}
    {dst : Reg} (hdst : dst ≠ .x1) (hdst' : dst ≠ .x2) (hdst'' : dst ≠ .x17) (c : Bool)
    (hc : s.gpr .x3 = (if c then BitVec.allOnes 64 else 0)) (ha : a + 8 * n ≤ size) (ha8 : a % 8 = 0)
    (hpos : 0 < len) (hlo : 8 * n ≤ len + 8) (hhi : len ≤ 8 * n) (hdl : d + len < 4096)
    (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + len ≤ 2 ^ 64)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, len⟩) :
    WP isa (.block (storeBytes len n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (s.gpr dst + BitVec.ofNat 64 d) len =
        (if c then Spec.Weierstrass.toBytes len (wordsVal s.mem base a n) else List.replicate len 0) ∧
      KeepRegs [.x1, .x2, .x17] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 len s.mem s'.mem := by
  have hn := hs.nowrap
  have hl : len ≤ 2 ^ 64 := by omega_arith
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega_arith⟩
  rw [storeBytes_eq]
  by_cases hf : 8 * (k + 1) ≤ len
  · rw [flatMap_range_congr (g := stStepW len dst d a) (k + 1) fun j hj =>
      ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))]
    refine WP.mono (stSteps_wordsL hs hdst hdst'' hc ha ha8 (by omega_arith) hdl hl hw hd (k + 1) (Nat.le_refl _))
      fun s' ⟨e, k', O⟩ => ⟨?_, k'.mono (by simp), ?_⟩
    · exact bytesAt_eq_toBytes_len _ _ _ _ c (k := k) (by omega_arith) hhi (fun j hj _ => e j hj)
        fun h => absurd h (by omega_arith)
    · rw [show len - 8 * (k + 1) = 0 by omega_arith, show 8 * (k + 1) = len by omega_arith] at O; exact O
  · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      flatMap_range_congr (g := stStepW len dst d a) k fun j hj =>
        ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
      ite_eq_right_of_eq_false _ _ (eq_false hf), WP.block_append_iff]
    have hsub : Region.Sub ⟨off base a, 8 * k⟩ ⟨off base a, 8 * (k + 1)⟩ := by
      have := Offset.sub_base (off base a) (d := 0) (n := 8 * k) (k := 8 * (k + 1)) (by omega_arith)
      rwa [show off base a + BitVec.ofNat 64 0 = off base a from BitVec.add_zero _] at this
    refine WP.mono (stSteps_wordsL hs hdst hdst'' hc (k := k) (by omega_arith) ha8 (by omega_arith) hdl hl hw
      (hd.sub_left hsub) k (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simp [hdst, hdst''])
    have hc₁ : s₁.gpr .x3 = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hword : word s₁.mem base (a + 8 * k) = word s.mem base (a + 8 * k) := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega_arith)) hd (by omega_arith)
        (by omega_arith) (by omega_arith)
    refine WP.mono (stTop_ok hs₁ hdst hdst' hc₁ (t := len - 8 * k) (d := d) (a := a) (j := k) ha ha8 (by omega_arith)
      (by omega_arith) (by rw [hq₁]; omega_arith) (fun i hi => by rw [k₁.wr, hq₁]; exact hw _ _ (by omega_arith)))
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    rw [hq₁, hword] at e₂
    rw [hq₁] at O₂
    refine ⟨?_, (k₁.mono (by simp)).trans (k₂.mono (by simp)),
      (O₁.mono (Nat.zero_le _) (by omega_arith)).trans (O₂.mono (Nat.le_refl _) (by omega_arith))⟩
    refine bytesAt_eq_toBytes_len _ _ _ _ c (k := k) (by omega_arith) hhi (fun j hj hj8 => ?_) fun _ => e₂
    refine Eq.trans ?_ (e₁ j (by omega_arith))
    exact readW_keep fun i hi => O₂ _ (by rw [ofs_off0 _ (by omega_arith)]; omega_arith)

end VG.Proof.Weierstrass.AArch64
