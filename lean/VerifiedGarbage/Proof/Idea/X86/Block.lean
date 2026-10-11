import VerifiedGarbage.Proof.Idea.X86.Round
import VerifiedGarbage.Proof.Framework.Bswap

/-!
# IDEA on x86 (32-bit): a block

`cryptBlockWith_run`: `Impl.Idea.X86.cryptBlockWith pre` replaces the block
at the address in the scratch buffer's `dataSlot` with `Spec.Idea.cryptBlock`
of it under the subkeys at `esi`, writing no memory but the block and
`t₀`'s slot, keeping `esi` and `esp`, and leaves the block's address in
`eax` and what `pre` reads in `edx`: the interface a mode reuses it
through.
-/

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

/-! ## Words of bytes -/

theorem cat4 (b0 b1 b2 b3 : BitVec 8) (i : Nat) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec 32).getLsbD i =
      if i < 8 then b3.getLsbD i else if i < 16 then b2.getLsbD (i - 8)
      else if i < 24 then b1.getLsbD (i - 16) else b0.getLsbD (i - 24) := getLsbD_cat4 b0 b1 b2 b3 i
theorem cat2 (b0 b1 : BitVec 8) (i : Nat) :
    (b0 ++ b1 : BitVec 16).getLsbD i = if i < 8 then b1.getLsbD i else b0.getLsbD (i - 8) :=
  BitVec.getLsbD_append
theorem hi16 (b0 b1 b2 b3 : BitVec 8) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec 32) >>> 16 = (b0 ++ b1).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, cat4, BitVec.getLsbD_setWidth, cat2, decide_eq_true hi, Bool.true_and]
  by_cases h : i < 8
  · simp only [show ¬16 + i < 8 by omega, show ¬16 + i < 16 by omega, show 16 + i < 24 by omega, h,
      ite_true, ite_false, show 16 + i - 16 = i by omega]
  · simp only [show ¬16 + i < 8 by omega, show ¬16 + i < 16 by omega, show ¬16 + i < 24 by omega, h,
      ite_false, show 16 + i - 24 = i - 8 by omega]
theorem lo16 (b0 b1 b2 b3 : BitVec 8) :
    (b0 ++ b1 ++ b2 ++ b3 : BitVec 32) &&& 65535 = (b2 ++ b3).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm : (65535 : BitVec 32).getLsbD i = decide (i < 16) := by
    rw [show (65535 : BitVec 32) = BitVec.ofNat 32 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat]
    simp only [Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_and, hm, cat4, BitVec.getLsbD_setWidth, cat2, decide_eq_true hi, Bool.true_and]
  by_cases h : i < 8
  · simp only [h, ite_true, show i < 16 by omega, decide_true, Bool.and_true]
  · by_cases h' : i < 16
    · simp only [h, h', ite_true, ite_false, decide_true, Bool.and_true]
    · simp only [h, h', ite_false, decide_false, Bool.and_false]
      exact (BitVec.getLsbD_of_ge _ _ (by omega)).symm
theorem join16 (y₁ y₂ : BitVec 16) :
    (y₁.setWidth 32).rotateRight 16 ||| y₂.setWidth 32 = (y₁ ++ y₂ : BitVec 32) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  by_cases h : i < 16
  · simp only [h, ite_true, BitVec.getLsbD_setWidth, show 16 % 32 + i < 32 by omega,
      decide_true, Bool.true_and, hi]
    rw [BitVec.getLsbD_of_ge _ _ (by omega), Bool.false_or]
  · simp only [h, ite_false, BitVec.getLsbD_setWidth, decide_eq_true hi, decide_true,
      Bool.true_and, show i - (32 - 16 % 32) < 32 by omega, show i - (32 - 16 % 32) = i - 16 by omega]
    rw [BitVec.getLsbD_of_ge y₂ _ (by omega), Bool.or_false]

theorem bswap_readW' (m : Mem) (A : Addr) (k : Nat) :
    bswap (m.readW (A + BitVec.ofNat 64 k) 32) =
      (m (A + BitVec.ofNat 64 k) ++ m (A + BitVec.ofNat 64 (k + 1)) ++ m (A + BitVec.ofNat 64 (k + 2)) ++
        m (A + BitVec.ofNat 64 (k + 3)) : BitVec 32) := by
  rw [bswap_readW]
  simp only [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.add_ofNat_add_ofNat]

/-- Byte `i` of a byte-reversed word is byte `3 - i` of the word. -/
theorem bswap_byte (w : BitVec 32) {i : Nat} (hi : i < 4) :
    (bswap w).extractLsb' (8 * i) 8 = w.extractLsb' (24 - 8 * i) 8 := by
  have h := byteRev32_extract w
  have e : ∀ j, j < 4 → (byteRev32 w).extractLsb' (8 * j) 8 =
      [w.extractLsb' 24 8, w.extractLsb' 16 8, w.extractLsb' 8 8, w.extractLsb' 0 8][j]! := by
    intro j hj
    rw [← h]
    simp [hj]
  rw [show bswap w = byteRev32 w from rfl, e i hi]
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals rfl

/-- The bytes of two words, high first. -/
theorem join_byte (y₁ y₂ : BitVec 16) {i : Nat} (hi : i < 4) :
    (y₁ ++ y₂ : BitVec 32).extractLsb' (24 - 8 * i) 8 =
      ((if i < 2 then y₁ else y₂) >>> (8 * (1 - i % 2))).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_append, decide_eq_true ht, Bool.true_and]
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · simp only [show ¬24 - 8 * 0 + t < 16 by omega, show (0 : Nat) < 2 by omega, ite_true, ite_false]
    congr 1; omega
  · simp only [show ¬24 - 8 * 1 + t < 16 by omega, show (1 : Nat) < 2 by omega, ite_true, ite_false]
    congr 1; omega
  · simp only [show 24 - 8 * 2 + t < 16 by omega, show ¬(2 : Nat) < 2 by omega, ite_true, ite_false,
      Bool.true_and]
  · simp only [show 24 - 8 * 3 + t < 16 by omega, show ¬(3 : Nat) < 2 by omega, ite_true, ite_false,
      Bool.true_and]

/-! ## Single instructions -/

theorem bswap_run (d : Reg) (s : State) :
    ∃ s', runBlock isa [.bswap d] s = some s' ∧ s'.gpr d = bswap (s.gpr d) ∧ Keep [d] s s' := by
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, true_and]
  keep_tac

theorem shift_run (op : ShiftOp) (d : Reg) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 31) (s : State) :
    ∃ s', runBlock isa [.shift op d n] s = some s' ∧
      s'.gpr d = (match op with | .ror => (s.gpr d).rotateRight n | .shr => s.gpr d >>> n) ∧
      Keep [d] s s' := by
  cases op <;>
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, execShift, hn, and_self, ↓reduceIte,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, true_and] <;>
  keep_tac

/-- A 32-bit load at `[b + d]`. -/
theorem load_src {s : State} {b : Reg} {d : Nat} (h : InRegions (s.rd ++ s.wr) (addr (s.gpr b) d) 4) :
    readSrc s (.mem (at_ b d)) = some (s.mem.readW (addr (s.gpr b) d) 32) := by
  simp only [readSrc, State.load32]
  exact ite_eq_left h

theorem store_run (b r : Reg) (d : Nat) (s : State) (h : InRegions s.wr (addr (s.gpr b) d) 4) :
    ∃ s', runBlock isa [.store (at_ b d) r] s = some s' ∧
      s'.mem = s.mem.writeW (addr (s.gpr b) d) (s.gpr r) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions s.wr (s.ea (at_ b d)) 4 := h
  simp only [runBlock_cons, isa, exec, State.store32, hin, ite_true, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Loading -/

/-- The block's address `P` is in `dataSlot` of the scratch buffer at `esi`;
the block (64-bit address `A`) does not wrap around and can be read. -/
structure BlockAt (z : Spec.Idea.Schedule) (P : BitVec 32) (A : Addr) (s : State) : Prop where
  key : KeyOk z s
  slot : s.mem.readW (addr (s.gpr .esi) dataSlot) 32 = P
  addr : P.setWidth 64 = A
  fit : P.toNat + 8 ≤ 2 ^ 32
  rd0 : InRegions (s.rd ++ s.wr) A 4
  rd4 : InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 4) 4

theorem slot_src {z : Spec.Idea.Schedule} {s : State} (h : KeyOk z s) {d : Nat} (hd : d + 4 ≤ 4 * slots) :
    readSrc s (.mem (at_ .esi d)) = some (s.mem.readW (addr (s.gpr .esi) d) 32) :=
  load_src (by obtain ⟨R, hR, hc⟩ := h.slot hd; exact ⟨R, List.mem_append_right _ hR, hc⟩)

theorem addrP {P : BitVec 32} {A : Addr} (hA : P.setWidth 64 = A) (hf : P.toNat + 8 ≤ 2 ^ 32) {d : Nat}
    (hd : d < 8) : addr P d = A + BitVec.ofNat 64 d := by
  rw [addr_eq (by omega), hA]

theorem load_run {z : Spec.Idea.Schedule} {P : BitVec 32} {A : Addr} (s : State) (h : BlockAt z P A s) :
    ∃ s', runBlock isa load s = some s' ∧
      Holds (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)) .ecx .edi s' ∧
      Keep [.eax, .ebx, .ecx, .edi, .ebp] s s' := by
  have w (k : Nat) (hk : k < 4) := decodeBlock_blockAt s.mem A hk
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax _ _ s (slot_src h.key (d := dataSlot) (by decide))
  rw [h.slot] at v₁
  have rd₀ : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .eax) 0) 4 := by
    rw [e₁.rd, e₁.wr, v₁, addrP h.addr h.fit (by decide)]
    simpa using h.rd0
  have rd₄ : InRegions (s₁.rd ++ s₁.wr) (addr (s₁.gpr .eax) 4) 4 := by
    rw [e₁.rd, e₁.wr, v₁, addrP h.addr h.fit (by decide)]; exact h.rd4
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mov_run .ebx _ _ s₁ (load_src rd₀)
  obtain ⟨s₃, h₃, v₃, e₃⟩ := bswap_run .ebx s₂
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mov_run .ecx (.reg .ebx) _ s₃ rfl
  obtain ⟨s₅, h₅, v₅, e₅⟩ := shift_run .shr .ebx 16 (by decide) s₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := alu_run .and (by simp) .ecx (.imm 0xffff) 0xffff s₅ rfl
  have e₂₆ : Keep [.ebx, .ecx] s₂ s₆ :=
    (((e₃.weaken (by decide)).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans
      (e₆.weaken (by decide))
  have rd₄' : InRegions (s₆.rd ++ s₆.wr) (addr (s₆.gpr .eax) 4) 4 := by
    rw [e₂₆.rd, e₂₆.wr, e₂.rd, e₂.wr, e₂₆.reg .eax (by decide), e₂.reg .eax (by decide)]; exact rd₄
  obtain ⟨s₇, h₇, v₇, e₇⟩ := mov_run .edi _ _ s₆ (load_src rd₄')
  obtain ⟨s₈, h₈, v₈, e₈⟩ := bswap_run .edi s₇
  obtain ⟨s₉, h₉, v₉, e₉⟩ := mov_run .ebp (.reg .edi) _ s₈ rfl
  obtain ⟨s₁₀, h₁₀, v₁₀, e₁₀⟩ := shift_run .shr .edi 16 (by decide) s₉
  obtain ⟨s₁₁, h₁₁, v₁₁, e₁₁⟩ := alu_run .and (by simp) .ebp (.imm 0xffff) 0xffff s₁₀ rfl
  simp only [aluF] at v₆ v₁₁
  simp only at v₅ v₁₀
  have mem₆ : s₆.mem = s.mem := by rw [e₂₆.mem, e₂.mem, e₁.mem]
  have eax₆ : s₆.gpr .eax = P := by rw [e₂₆.reg .eax (by decide), e₂.reg .eax (by decide), v₁]
  have word0 : bswap (s₂.gpr .ebx) = (s.mem (A + BitVec.ofNat 64 0) ++ s.mem (A + BitVec.ofNat 64 1) ++
      s.mem (A + BitVec.ofNat 64 2) ++ s.mem (A + BitVec.ofNat 64 3) : BitVec 32) := by
    rw [v₂, e₁.mem, v₁, addrP h.addr h.fit (by decide), bswap_readW']
  have word1 : bswap (s₇.gpr .edi) = (s.mem (A + BitVec.ofNat 64 4) ++ s.mem (A + BitVec.ofNat 64 5) ++
      s.mem (A + BitVec.ofNat 64 6) ++ s.mem (A + BitVec.ofNat 64 7) : BitVec 32) := by
    rw [v₇, mem₆, eax₆, addrP h.addr h.fit (by decide), bswap_readW']
  refine ⟨s₁₁, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact run_append (run_append (run_append (run_append (run_append (run_append (run_append
      (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉) h₁₀) h₁₁
  · rw [e₁₁.reg .ebx (by decide), e₁₀.reg .ebx (by decide), e₉.reg .ebx (by decide), e₈.reg .ebx (by decide),
      e₇.reg .ebx (by decide), e₆.reg .ebx (by decide), v₅, e₄.reg .ebx (by decide), v₃, word0, hi16,
      w 0 (by decide)]
  · rw [e₁₁.reg .ecx (by decide), e₁₀.reg .ecx (by decide), e₉.reg .ecx (by decide), e₈.reg .ecx (by decide),
      e₇.reg .ecx (by decide), v₆, e₅.reg .ecx (by decide), v₄, v₃, word0, lo16, w 1 (by decide)]
  · rw [e₁₁.reg .edi (by decide), v₁₀, e₉.reg .edi (by decide), v₈, word1, hi16, w 2 (by decide)]
  · rw [v₁₁, e₁₀.reg .ebp (by decide), v₉, v₈, word1, lo16, w 3 (by decide)]
  · exact ((((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₂₆.weaken (by decide))).trans
      ((((((e₇.weaken (by decide)).trans (e₈.weaken (by decide))).trans (e₉.weaken (by decide))).trans
      (e₁₀.weaken (by decide))).trans (e₁₁.weaken (by decide)))))

/-! ## The rounds -/

theorem regB_succ (n : Nat) : regB (n + 1) = regC n := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega]

theorem regC_succ (n : Nat) : regC (n + 1) = regB n := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h, show (n + 1) % 2 = 0 ↔ ¬ n % 2 = 0 by omega]

theorem regBC_ok (n : Nat) : (regB n == .ecx && regC n == .edi || regB n == .edi && regC n == .ecx) = true := by
  unfold regB regC; by_cases h : n % 2 = 0 <;> simp [h]

theorem rounds_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) :
    ∀ n ≤ 8, ∀ s : State, Holds x .ecx .edi s → KeyOk z s →
      ∃ s', runBlock isa ((List.range n).flatMap round) s = some s' ∧
        Holds (roundsSpec z n x) (regB n) (regC n) s' ∧ KeepT roundWrites s s'
  | 0, _, s, hx, _ => ⟨s, by simp [runBlock_nil], hx, (Keep.refl _ _).toT⟩
  | n + 1, hn, s, hx, hk => by
    obtain ⟨s₁, h₁, x₁, e₁⟩ := rounds_run z x n (by omega) s hx hk
    obtain ⟨s₂, h₂, x₂, e₂⟩ := round_run n (by omega) (regB n) (regC n) (regBC_ok n) z _ s₁ x₁
      (hk.keepT e₁ (by decide))
    refine ⟨s₂, ?_, ?_, e₁.trans (by decide) e₂⟩
    · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
      exact run_append h₁ h₂
    · simp only [roundsSpec, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        regB_succ, regC_succ]
      exact x₂

/-! ## The output transformation -/

/-- The output words: `Y₁` in `ebx`, `Y₂` in `edi`, `Y₃` in `ecx`, `Y₄` in `ebp`. -/
structure OutHolds (y : Spec.Idea.State) (s : State) : Prop where
  ebx : s.gpr .ebx = (y.getD 0 0).setWidth 32
  edi : s.gpr .edi = (y.getD 1 0).setWidth 32
  ecx : s.gpr .ecx = (y.getD 2 0).setWidth 32
  ebp : s.gpr .ebp = (y.getD 3 0).setWidth 32

theorem output_run (z : Spec.Idea.Schedule) (x : Spec.Idea.State) (s : State) (hx : Holds x .ecx .edi s)
    (hk : KeyOk z s) :
    ∃ s', runBlock isa output s = some s' ∧
      OutHolds (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0) x) s' ∧
      Keep roundWrites s s' := by
  obtain ⟨s₁, h₁, v₁, e₁⟩ := mov_run .eax (.reg .ebx) _ s rfl
  obtain ⟨s₂, h₂, v₂, e₂⟩ := mulKey_run z 48 (by decide) s₁ (hk.keep e₁ (by decide))
  obtain ⟨s₃, h₃, v₃, e₃⟩ := mov_run .ebx (.reg .edx) _ s₂ rfl
  have e₀₃ : Keep [.eax, .ebx, .edx] s s₃ :=
    ((e₁.weaken (by decide)).trans (e₂.weaken (by decide))).trans (e₃.weaken (by decide))
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mov_run .eax (.reg .ebp) _ s₃ rfl
  obtain ⟨s₅, h₅, v₅, e₅⟩ := mulKey_run z 51 (by decide) s₄ ((hk.keep e₀₃ (by decide)).keep e₄ (by decide))
  obtain ⟨s₆, h₆, v₆, e₆⟩ := mov_run .ebp (.reg .edx) _ s₅ rfl
  have e₀₆ : Keep [.eax, .ebx, .edx, .ebp] s s₆ :=
    (((e₀₃.weaken (by decide)).trans (e₄.weaken (by decide))).trans (e₅.weaken (by decide))).trans
      (e₆.weaken (by decide))
  obtain ⟨s₇, h₇, v₇, e₇⟩ := addKey_run z .edi 49 (by decide) s₆ (hk.keep e₀₆ (by decide))
  obtain ⟨s₈, h₈, v₈, e₈⟩ := addKey_run z .ecx 50 (by decide) s₇ ((hk.keep e₀₆ (by decide)).keep e₇ (by decide))
  refine ⟨s₈, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [output, mulKey]
    exact run_append (run_append (run_append (run_append (run_append (run_append
      (run_append h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈
  · rw [e₈.reg .ebx (by decide), e₇.reg .ebx (by decide), e₆.reg .ebx (by decide), e₅.reg .ebx (by decide),
      e₄.reg .ebx (by decide), v₃, v₂, v₁, hx.ebx, setWidth_setWidth16_32]
    rfl
  · rw [e₈.reg .edi (by decide), v₇, e₀₆.reg .edi (by decide), hx.c, setWidth_setWidth16_32]
    rfl
  · rw [v₈, e₇.reg .ecx (by decide), e₀₆.reg .ecx (by decide), hx.b, setWidth_setWidth16_32]
    rfl
  · rw [e₈.reg .ebp (by decide), e₇.reg .ebp (by decide), v₆, v₅, v₄, e₀₃.reg .ebp (by decide), hx.ebp,
      setWidth_setWidth16_32]
    rfl
  · exact ((e₀₆.weaken (by decide)).trans (e₇.weaken (by decide))).trans (e₈.weaken (by decide))

/-! ## Storing -/

/-- A 32-bit write at `A + 4` leaves the bytes `A … A + 3`. -/
theorem writeW4_other (m : Mem) (A : Addr) (v : BitVec 32) {i : Nat} (hi : i < 4) :
    (m.writeW (A + BitVec.ofNat 64 4) v) (A + BitVec.ofNat 64 i) = m (A + BitVec.ofNat 64 i) := by
  refine Mem.write_apply ?_
  rw [Offset.add_sub_add_left, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- Byte `i` of a 32-bit word written at `a`. -/
theorem writeW4_byte (m : Mem) (a : Addr) (v : BitVec 32) {i : Nat} (hi : i < 4) :
    (m.writeW a v) (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 := by
  rw [Mem.readW_byte (m.writeW a v) a hi, Mem.readW_writeW_self32]

theorem store_block (m : Mem) (A : Addr) (y : Spec.Idea.State) :
    Spec.Idea.blockAt ((m.writeW (A + BitVec.ofNat 64 0)
        (bswap ((y.getD 0 0 ++ y.getD 1 0 : BitVec 32)))).writeW (A + BitVec.ofNat 64 4)
        (bswap ((y.getD 2 0 ++ y.getD 3 0 : BitVec 32)))) A = Spec.Idea.encodeBlock y := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Idea.blockAt, Vector.getElem_ofFn, encodeBlock_get _ hi]
  by_cases h4 : i < 4
  · rw [writeW4_other _ _ _ h4, show A + BitVec.ofNat 64 i = A + BitVec.ofNat 64 0 + BitVec.ofNat 64 i by
      rw [Offset.add_ofNat_add_ofNat, Nat.zero_add], writeW4_byte _ _ _ h4, bswap_byte _ h4, join_byte _ _ h4]
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals rfl
  · rw [show A + BitVec.ofNat 64 i = A + BitVec.ofNat 64 4 + BitVec.ofNat 64 (i - 4) by
      rw [Offset.add_ofNat_add_ofNat, show 4 + (i - 4) = i by omega], writeW4_byte _ _ _ (by omega),
      bswap_byte _ (by omega), join_byte _ _ (by omega)]
    obtain rfl | rfl | rfl | rfl : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals rfl

/-! ## A block -/

/-- `ror r, 16; or r, s; bswap r`: two words, high first, byte-swapped. -/
theorem join_run (r q : Reg) (hrq : r ≠ q) (y₁ y₂ : Spec.Idea.Word) (s : State)
    (hr : s.gpr r = y₁.setWidth 32) (hq : s.gpr q = y₂.setWidth 32) :
    ∃ s', runBlock isa [.shift .ror r 16, .alu .or r (.reg q), .bswap r] s = some s' ∧
      s'.gpr r = bswap (y₁ ++ y₂ : BitVec 32) ∧ Keep [r] s s' := by
  obtain ⟨s₁, h₁, v₁, e₁⟩ := shift_run .ror r 16 (by decide) s
  obtain ⟨s₂, h₂, v₂, e₂⟩ := alu_run .or (by simp) r (.reg q) _ s₁ rfl
  obtain ⟨s₃, h₃, v₃, e₃⟩ := bswap_run r s₂
  refine ⟨s₃, run_append h₁ (run_append h₂ h₃), ?_, (e₁.trans e₂).trans e₃⟩
  simp only [aluF] at v₂
  simp only at v₁
  rw [v₃, v₂, v₁, e₁.reg q (by simpa using Ne.symm hrq), hr, hq, join16]

theorem cryptBlockWith_run (z : Spec.Idea.Schedule) (pre : List Instr) (R : BitVec 32 → Prop)
    {P : BitVec 32} {A : Addr} (s : State) (h : BlockAt z P A s)
    (hw0 : InRegions s.wr A 4) (hw4 : InRegions s.wr (A + BitVec.ofNat 64 4) 4)
    (hpre : ∀ t : State, t.gpr .esi = s.gpr .esi → t.rd = s.rd → t.wr = s.wr →
      Frame [⟨addr (s.gpr .esi) t0Slot, 4⟩] s.mem t.mem →
      ∃ t', runBlock isa pre t = some t' ∧ Keep [.edx] t t' ∧ R (t'.gpr .edx)) :
    ∃ s', runBlock isa (cryptBlockWith pre) s = some s' ∧
      Spec.Idea.blockAt s'.mem A = Spec.Idea.cryptBlock z (Spec.Idea.blockAt s.mem A) ∧
      Frame [⟨A, 8⟩, ⟨addr (s.gpr .esi) t0Slot, 4⟩] s.mem s'.mem ∧ s'.gpr .eax = P ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      R (s'.gpr .edx) := by
  obtain ⟨s₁, h₁, x₁, e₁⟩ := load_run s h
  obtain ⟨s₂, h₂, x₂, e₂⟩ := rounds_run z _ 8 (by decide) s₁ x₁ (h.key.keep e₁ (by decide))
  have e₀₂ : KeepT roundWrites s s₂ := ((e₁.weaken (by decide)).toT).trans (by decide) e₂
  obtain ⟨s₃, h₃, x₃, e₃⟩ := output_run z _ s₂ x₂ (h.key.keepT e₀₂ (by decide))
  have e₀₃ : KeepT roundWrites s s₃ := e₀₂.trans (by decide) e₃.toT
  have esi₃ : s₃.gpr .esi = s.gpr .esi := e₀₃.reg .esi (by decide)
  have k₃ : KeyOk z s₃ := h.key.keepT e₀₃ (by decide)
  have slot₃ : s₃.mem.readW (addr (s₃.gpr .esi) dataSlot) 32 = P := by
    rw [esi₃, ← h.slot]
    refine e₀₃.frame.readW (r := ⟨addr (s.gpr .esi) dataSlot, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have := h.key.fit
    rw [addr_eq (by simp only [dataSlot, slots] at *; omega), addr_eq (by simp only [t0Slot, slots] at *; omega)]
    exact Offset.disjoint _ (by decide) (by decide) (by decide)
  obtain ⟨s₄, h₄, v₄, e₄⟩ := mov_run .eax _ _ s₃ (slot_src k₃ (d := dataSlot) (by decide))
  rw [slot₃] at v₄
  obtain ⟨s₅, h₅, e₅, r₅⟩ := hpre s₄ ((e₄.reg .esi (by decide)).trans esi₃) (e₄.rd.trans e₀₃.rd)
    (e₄.wr.trans e₀₃.wr) (by rw [e₄.mem]; exact e₀₃.frame)
  -- The stores.
  have y₀ : s₅.gpr .ebx = _ := (e₅.reg .ebx (by decide)).trans ((e₄.reg .ebx (by decide)).trans x₃.ebx)
  have y₁ : s₅.gpr .edi = _ := (e₅.reg .edi (by decide)).trans ((e₄.reg .edi (by decide)).trans x₃.edi)
  have y₂ : s₅.gpr .ecx = _ := (e₅.reg .ecx (by decide)).trans ((e₄.reg .ecx (by decide)).trans x₃.ecx)
  have y₃ : s₅.gpr .ebp = _ := (e₅.reg .ebp (by decide)).trans ((e₄.reg .ebp (by decide)).trans x₃.ebp)
  have eax₅ : s₅.gpr .eax = P := (e₅.reg .eax (by decide)).trans v₄
  obtain ⟨s₆, h₆, v₆, e₆⟩ := join_run .ebx .edi (by decide) _ _ s₅ y₀ y₁
  have wr₆ : s₆.wr = s.wr := by rw [e₆.wr, e₅.wr, e₄.wr, e₀₃.wr]
  have eax₆ : s₆.gpr .eax = P := (e₆.reg .eax (by decide)).trans eax₅
  obtain ⟨s₇, h₇, m₇, g₇, rd₇, wr₇⟩ := store_run .eax .ebx 0 s₆
    (by rw [eax₆, addrP h.addr h.fit (by decide), wr₆]; simpa using hw0)
  obtain ⟨s₈, h₈, v₈, e₈⟩ := join_run .ecx .ebp (by decide) _ _ s₇
    (by rw [g₇, e₆.reg .ecx (by decide), y₂]) (by rw [g₇, e₆.reg .ebp (by decide), y₃])
  have eax₈ : s₈.gpr .eax = P := by rw [e₈.reg .eax (by decide), g₇, eax₆]
  obtain ⟨s₉, h₉, m₉, g₉, rd₉, wr₉⟩ := store_run .eax .ecx 4 s₈
    (by rw [eax₈, addrP h.addr h.fit (by decide), e₈.wr, wr₇, wr₆]; exact hw4)
  have mem₅ : s₅.mem = s₃.mem := by rw [e₅.mem, e₄.mem]
  have hm : s₉.mem = (s₃.mem.writeW (A + BitVec.ofNat 64 0)
      (bswap (((Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0)
        (roundsSpec z 8 (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)))).getD 0 0 ++
        (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0)
        (roundsSpec z 8 (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)))).getD 1 0 : BitVec 32)))).writeW
      (A + BitVec.ofNat 64 4)
      (bswap (((Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0)
        (roundsSpec z 8 (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)))).getD 2 0 ++
        (Spec.Idea.output (z.getD 48 0) (z.getD 49 0) (z.getD 50 0) (z.getD 51 0)
        (roundsSpec z 8 (Spec.Idea.decodeBlock (Spec.Idea.blockAt s.mem A)))).getD 3 0 : BitVec 32))) := by
    rw [m₉, e₈.mem, m₇, e₆.mem, mem₅, eax₈, eax₆, addrP h.addr h.fit (by decide),
      addrP h.addr h.fit (by decide), v₈, v₆]
  refine ⟨s₉, ?_, ?_, ?_, by rw [g₉, eax₈], ?_, ?_, by rw [rd₉, e₈.rd, rd₇, e₆.rd, e₅.rd, e₄.rd, e₀₃.rd],
    by rw [wr₉, e₈.wr, wr₇, wr₆], ?_⟩
  · have hs : runBlock isa store s₅ = some s₉ :=
      run_append (a := [_, _, _]) h₆ (run_append (a := [_]) h₇ (run_append (a := [_, _, _]) h₈ h₉))
    exact run_append (run_append (run_append (run_append (run_append h₁ h₂) h₃) h₄) h₅) hs
  · rw [hm, store_block, Spec.Idea.cryptBlock, crypt_eq]
  · rw [hm]
    have hf : Frame [⟨A, 8⟩, ⟨addr (s.gpr .esi) t0Slot, 4⟩] s.mem s₃.mem :=
      e₀₃.frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
    refine (hf.writeW (List.mem_cons_self) _ (Offset.contains_base A (by decide) (by decide))).writeW
      (List.mem_cons_self) _ (Offset.contains_base A (by decide) (by decide))
  · rw [g₉, e₈.reg .esi (by decide), g₇, e₆.reg .esi (by decide), e₅.reg .esi (by decide),
      e₄.reg .esi (by decide), esi₃]
  · rw [g₉, e₈.reg .esp (by decide), g₇, e₆.reg .esp (by decide), e₅.reg .esp (by decide),
      e₄.reg .esp (by decide), e₀₃.reg .esp (by decide)]
  · rw [g₉, e₈.reg .edx (by decide), g₇, e₆.reg .edx (by decide)]; exact r₅

end VG.Proof.Idea.X86
