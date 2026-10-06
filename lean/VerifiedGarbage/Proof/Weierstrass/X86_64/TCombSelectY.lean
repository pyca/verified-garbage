import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombSelectPass

/-!
# The comb from tables in memory on x86-64: the selection's pass with AVX2

`selPassY` (`Impl/Weierstrass/X86_64/TComb.lean`) is `selPassAt` 32 bytes at a
time: lane `l` of the 256-bit accumulator `c` is the 16-byte accumulator of
piece `2 c + l`. The mask of entry `m` is `vpcmpeqd` of the broadcasts of `m`
(a counter, incremented by `vpaddd`) and of the magnitude `a`
(`pcmpeqd_bcast`), so that after entry `m` each lane holds its piece of entry
`a` if `1 ≤ a ≤ m`, else zero (`accVal`, as in `TCombSelectPass.lean`), and the
stored pieces are `selPass_ok`'s (`selPassY_ok`, `selPassV_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- `x` in every doubleword. -/
abbrev bcast32 (x : BitVec 32) : BitVec 128 := ofDwords x x x x

theorem pcmpeqd_bcast (x y : BitVec 32) :
    XBinOp.eval .pcmpeqd (bcast32 x) (bcast32 y) = bmask128 (decide (x = y)) := by
  by_cases h : x = y
  · subst h
    simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3,
      ite_true, decide_true]
    decide
  · simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3, h,
      ite_false, decide_false]
    decide

theorem paddd_bcast (x y : BitVec 32) : XBinOp.eval .paddd (bcast32 x) (bcast32 y) = bcast32 (x + y) := by
  simp only [XBinOp.eval, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

/-- Doubleword 0 of `vmovq`'s result. -/
theorem dword_movq {a : Nat} (ha : a < 2 ^ 32) :
    dword ((0 : BitVec 64) ++ BitVec.ofNat 64 a) 0 = BitVec.ofNat 32 a := by
  apply BitVec.eq_of_toNat_eq
  simp only [dword_eq, BitVec.extractLsb'_toNat, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mul_zero,
    Nat.shiftRight_zero, show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_shiftLeft, Nat.zero_or]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt ha]

/-- Lane `l` of a 256-bit load. -/
theorem lane_load256 (m : Mem) (a : Addr) {l : Nat} (hl : l < 2) :
    (if l = 0 then (m.readW a 256).extractLsb' 0 128 else (m.readW a 256).extractLsb' 128 128) =
      m.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · exact readW_extract m a (k := 0) (n := 16) (by decide)
  · exact readW_extract m a (k := 16) (n := 16) (by decide)

theorem selAcc_neY : ∀ c < 11, selAcc c ≠ .xmm11 ∧ selAcc c ≠ .xmm12 ∧ selAcc c ≠ .xmm13 ∧
    selAcc c ≠ .xmm14 ∧ selAcc c ≠ .xmm15 := by decide

/-- What the pass leaves of the other registers: the general-purpose
registers but `rs`, the memory and the regions, and both lanes of the vector
registers but those of `xs`. -/
structure YKeep (rs : List Reg) (xs : XReg → Prop) (s t : State) : Prop where
  gpr : ∀ r, r ∉ rs → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  lane : ∀ r, ¬ xs r → ∀ l, t.lane r l = s.lane r l

theorem YKeep.refl (rs : List Reg) (xs : XReg → Prop) (s : State) : YKeep rs xs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem YKeep.trans {rs : List Reg} {xs : XReg → Prop} {s₁ s₂ s₃ : State} (h₁ : YKeep rs xs s₁ s₂)
    (h₂ : YKeep rs xs s₂ s₃) : YKeep rs xs s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, fun r hr l => (h₂.lane r hr l).trans (h₁.lane r hr l)⟩

theorem YKeep.mono {rs rs' : List Reg} {xs xs' : XReg → Prop} {s t : State} (h : YKeep rs xs s t)
    (hr : ∀ r ∈ rs, r ∈ rs') (hx : ∀ r, xs r → xs' r) : YKeep rs' xs' s t :=
  ⟨fun r h' => h.gpr r fun h'' => h' (hr r h''), h.mem, h.rd, h.wr,
    fun r h' l => h.lane r (fun h'' => h' (hx r h'')) l⟩

/-- Piece `c` (32 bytes) of an entry of the table at `rdx = X`, at `d`, kept
under the mask `ymm15` in accumulator `c`. -/
theorem selStepY_ok (s : State) {X : Addr} (hx : s.gpr .rdx = X) {d c : Nat} (hc : c < 11)
    (hr : InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 d) 32) :
    WP isa (.block [.vbinLoad .vpand .l256 .xmm11 .xmm15 (tblAt d),
        .vop (.vbin .vpor .l256 (selAcc c) (selAcc c) .xmm11)]) s fun t =>
      (∀ l < 2, t.lane (selAcc c) l = s.lane (selAcc c) l |||
        (s.mem.readW (X + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * l)) 128 &&& s.lane .xmm15 l)) ∧
      YKeep [] (fun r => r = selAcc c ∨ r = .xmm11) s t := by
  obtain ⟨h11, -, -, -, -⟩ := selAcc_neY c hc
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_tblAt, hx, State.load256, hr,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr l => ?_⟩⟩
  · simp only [lane_vbin256, State.lane_setV256, ↓reduceIte, h11, VBinOp.sse, XBinOp.eval]
    rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
    · simp only [↓reduceIte]
      rw [show (s.mem.readW (X + BitVec.ofNat 64 d) 256).extractLsb' 0 128 =
        s.mem.readW (X + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * 0)) 128 from lane_load256 _ _ (l := 0) hl,
        BitVec.and_comm]
    · simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [show (s.mem.readW (X + BitVec.ofNat 64 d) 256).extractLsb' 128 128 =
        s.mem.readW (X + BitVec.ofNat 64 d + BitVec.ofNat 64 (16 * 1)) 128 from lane_load256 _ _ (l := 1) hl,
        BitVec.and_comm]
  · simp only [not_or] at hr
    simp only [lane_vbin256, State.lane_setV256, hr.1, hr.2, ↓reduceIte]

/-- The pieces `c < k` of entry `m` of the table at `rdx = X` (entries `st`
bytes apart) kept under the mask `ymm15` in their accumulators: lane `l` of
accumulator `c`, piece `2 c + l`. -/
theorem selStepsY_ok {np st m : Nat} (hn : np ≤ 11) {X : Addr} :
    ∀ k ≤ np, ∀ (s : State), s.gpr .rdx = X →
    (∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (m - 1) + 32 * c)) 32) →
    WP isa (.block ((List.range k).flatMap fun c =>
        [.vbinLoad .vpand .l256 .xmm11 .xmm15 (tblAt (st * (m - 1) + 32 * c)),
          .vop (.vbin .vpor .l256 (selAcc c) (selAcc c) .xmm11)])) s fun t =>
      (∀ c < 11, ∀ l < 2, t.lane (selAcc c) l = if c < k then s.lane (selAcc c) l |||
          (s.mem.readW (X + BitVec.ofNat 64 (st * (m - 1) + 16 * (2 * c + l))) 128 &&& s.lane .xmm15 l)
        else s.lane (selAcc c) l) ∧
      YKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm11) s t
  | 0, _, s, _, _ => WP.block_nil ⟨fun c _ l _ => by simp, YKeep.refl _ _ _⟩
  | k + 1, hk, s, hx, hr => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selStepsY_ok hn k (by omega) s hx hr) fun s₁ ⟨a₁, k₁⟩ => ?_
    have h15 : ∀ l, s₁.lane .xmm15 l = s.lane .xmm15 l := k₁.lane _ (by
      rintro (⟨c, hc, h⟩ | h)
      · exact (selAcc_neY c (by omega)).2.2.2.2 h.symm
      · exact absurd h (by decide))
    refine WP.mono (selStepY_ok s₁ ((k₁.gpr _ List.not_mem_nil).trans hx) (c := k) (by omega)
      (by rw [k₁.rd, k₁.wr]; exact hr k (by omega))) fun t ⟨a₂, k₂⟩ => ⟨fun c hc l hl => ?_, ?_⟩
    · by_cases hck : c = k
      · rw [hck, a₂ l hl, a₁ k (by omega) l hl, h15, k₁.mem, BitVec.add_assoc, ← BitVec.ofNat_add,
          show st * (m - 1) + 32 * k + 16 * l = st * (m - 1) + 16 * (2 * k + l) by omega]
        simp only [Nat.lt_irrefl, ↓reduceIte, Nat.lt_succ_self]
      · rw [k₂.lane _ (by
          rintro (h | h)
          · exact hck (selAcc_inj c (by omega) k (by omega) h)
          · exact (selAcc_neY c hc).1 h) l, a₁ c hc l hl]
        by_cases hlt : c < k
        · simp only [hlt, show c < k + 1 by omega, ↓reduceIte]
        · simp only [hlt, show ¬ c < k + 1 by omega, ↓reduceIte]
    · exact k₁.trans (k₂.mono (fun _ h => h) fun r h => by
        rcases h with h | h
        · exact Or.inl ⟨k, by omega, h⟩
        · exact Or.inr h)

theorem ofNat32_eq {a m : Nat} (ha : a < 2 ^ 32) (hm : m < 2 ^ 32) :
    decide (BitVec.ofNat 32 m = BitVec.ofNat 32 a) = decide (a = m) := by
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => by rw [h]⟩
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hm] at this
  exact this.symm

/-- The mask of `a = m` in `ymm15`, from the counter `ymm14 = m` and the
broadcast magnitude `ymm13 = a`, and the counter incremented by `ymm12 = 1`. -/
theorem selMaskY_ok (s : State) {a m : Nat} (ha : a < 2 ^ 31) (hm : m < 2 ^ 31)
    (h13 : ∀ l < 2, s.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a))
    (h12 : ∀ l < 2, s.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1))
    (h14 : ∀ l < 2, s.lane .xmm14 l = bcast32 (BitVec.ofNat 32 m)) :
    WP isa (.block [.vop (.vbin .vpcmpeqd .l256 .xmm15 .xmm14 .xmm13),
        .vop (.vbin .vpaddd .l256 .xmm14 .xmm14 .xmm12)]) s fun t =>
      (∀ l < 2, t.lane .xmm15 l = bmask128 (decide (a = m))) ∧
      (∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (m + 1))) ∧
      YKeep [] (fun r => r = .xmm14 ∨ r = .xmm15) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun l hl => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun r hr l => ?_⟩⟩
  · simp only [lane_vbin256, ↓reduceIte, show XReg.xmm15 ≠ XReg.xmm14 from by decide, VBinOp.sse,
      h14 l hl, h13 l hl, pcmpeqd_bcast, ofNat32_eq (show a < 2 ^ 32 by omega) (show m < 2 ^ 32 by omega)]
  · simp only [lane_vbin256, ↓reduceIte, show XReg.xmm14 ≠ XReg.xmm15 from by decide,
      show XReg.xmm12 ≠ XReg.xmm15 from by decide, VBinOp.sse, h14 l hl, h12 l hl, paddd_bcast,
      ← BitVec.ofNat_add]
  · simp only [not_or] at hr
    simp only [lane_vbin256, hr.1, hr.2, ↓reduceIte]

/-- The accumulators after entries `1 … m`: lane `l` of accumulator `c` is
piece `2 c + l` (`accVal`). -/
def AccY (t : State) (mem : Mem) (X : Addr) (st a m np : Nat) : Prop :=
  ∀ c < np, ∀ l < 2, t.lane (selAcc c) l = accVal mem X st (16 * ·) a m (2 * c + l)

/-- Entry `m` of the table at `rdx = X` kept in the accumulators under the
mask of `a = m`, and the counter incremented. -/
theorem selEntryY_ok {st np : Nat} {s : State} {X : Addr} {a m : Nat} (hn : np ≤ 11)
    (hm1 : 1 ≤ m) (hm : m < 2 ^ 31) (ha : a < 2 ^ 31) (hx : s.gpr .rdx = X)
    (h13 : ∀ l < 2, s.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a))
    (h12 : ∀ l < 2, s.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1))
    (h14 : ∀ l < 2, s.lane .xmm14 l = bcast32 (BitVec.ofNat 32 m))
    (hr : ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * (m - 1) + 32 * c)) 32)
    (hacc : AccY s s.mem X st a (m - 1) np) :
    WP isa (.block (selEntryY st np m)) s fun t =>
      AccY t s.mem X st a m np ∧ (∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (m + 1))) ∧
      YKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm11 ∨ r = .xmm14 ∨ r = .xmm15) s t := by
  rw [selEntryY, WP.block_append_iff]
  refine WP.mono (selMaskY_ok s ha hm h13 h12 h14) fun s₁ ⟨x₁, c₁, k₁⟩ => ?_
  refine WP.mono (selStepsY_ok (X := X) hn np (Nat.le_refl _) s₁ (by rw [k₁.gpr _ List.not_mem_nil, hx])
    (by rw [k₁.rd, k₁.wr]; exact hr)) fun t ⟨a₂, k₂⟩ => ⟨fun c hc l hl => ?_, fun l hl => ?_, ?_⟩
  · obtain ⟨-, -, -, h14', h15'⟩ := selAcc_neY c (by omega)
    rw [a₂ c (by omega) l hl, ite_eq_left_of_eq_true _ _ (eq_true hc), x₁ l hl, k₁.mem,
      k₁.lane _ (by rintro (h | h); exacts [h14' h, h15' h]) l, hacc c hc l hl]
    exact accVal_step _ _ _ (16 * ·) _ _ _ hm1
  · rw [k₂.lane _ (by
      rintro (⟨c, hc, h⟩ | h)
      · exact (selAcc_neY c (by omega)).2.2.2.1 h.symm
      · exact absurd h (by decide)) l, c₁ l hl]
  · exact (k₁.mono (fun _ h => h) fun r h => by
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))).trans (k₂.mono (fun _ h => h) fun r h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))

/-- The entries `1 … h` of the table at `rdx = X` kept in the cleared
accumulators under the masks of `a`, the counter from 1. -/
theorem selEntriesY_ok {st np : Nat} {X : Addr} {a : Nat} (hn : np ≤ 11) (ha : a < 2 ^ 31) :
    ∀ h, h < 2 ^ 31 → ∀ (s : State), s.gpr .rdx = X →
    (∀ l < 2, s.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a)) →
    (∀ l < 2, s.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1)) →
    (∀ l < 2, s.lane .xmm14 l = bcast32 (BitVec.ofNat 32 1)) →
    (∀ e < h, ∀ c < np, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (st * e + 32 * c)) 32) →
    (∀ c < np, ∀ l < 2, s.lane (selAcc c) l = 0) →
    WP isa (.block ((List.range h).flatMap fun m => selEntryY st np (m + 1))) s fun t =>
      AccY t s.mem X st a h np ∧ (∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 (h + 1))) ∧
      YKeep [] (fun r => (∃ c < np, r = selAcc c) ∨ r = .xmm11 ∨ r = .xmm14 ∨ r = .xmm15) s t
  | 0, _, s, _, _, _, h14, _, h0 => WP.block_nil ⟨fun c hc l hl => by
      rw [h0 c hc l hl, accVal, ite_eq_right_of_eq_false _ _ (eq_false (by omega))], h14, YKeep.refl _ _ _⟩
  | h + 1, hh, s, hx, h13, h12, h14, hr, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (selEntriesY_ok hn ha h (by omega) s hx h13 h12 h14 (fun e he => hr e (by omega)) h0)
      fun s₁ ⟨a₁, c₁, k₁⟩ => ?_
    have n13 : ¬ ((∃ c < np, XReg.xmm13 = selAcc c) ∨ XReg.xmm13 = .xmm11 ∨ XReg.xmm13 = .xmm14 ∨
        XReg.xmm13 = .xmm15) := by
      rintro (⟨c, hc, h⟩ | h | h | h)
      · exact (selAcc_neY c (by omega)).2.2.1 h.symm
      all_goals exact absurd h (by decide)
    have n12 : ¬ ((∃ c < np, XReg.xmm12 = selAcc c) ∨ XReg.xmm12 = .xmm11 ∨ XReg.xmm12 = .xmm14 ∨
        XReg.xmm12 = .xmm15) := by
      rintro (⟨c, hc, h⟩ | h | h | h)
      · exact (selAcc_neY c (by omega)).2.1 h.symm
      all_goals exact absurd h (by decide)
    refine WP.mono (selEntryY_ok (X := X) (m := h + 1) hn (by omega) hh ha
      (by rw [k₁.gpr _ (by decide), hx]) (fun l hl => by rw [k₁.lane _ n13 l, h13 l hl])
      (fun l hl => by rw [k₁.lane _ n12 l, h12 l hl]) c₁
      (fun c hc => by rw [k₁.rd, k₁.wr, Nat.add_sub_cancel]; exact hr h (by omega) c hc)
      (fun c hc l hl => by rw [a₁ c hc l hl, k₁.mem, Nat.add_sub_cancel])) fun t ⟨a₂, c₂, k₂⟩ =>
      ⟨fun c hc l hl => by rw [a₂ c hc l hl, k₁.mem], c₂, k₁.trans k₂⟩

theorem ifT {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_iff.mpr fun h' => absurd h h'

theorem ifF {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_iff.mpr fun h' => absurd h' h

theorem lane_vmovq (d : XReg) (r : Reg) (s : State) (x : XReg) (l : Nat) :
    ((VOp.vmovq d r).exec s).lane x l =
      if x = d then (if l = 0 then (0 : BitVec 64) ++ s.gpr r else 0) else s.lane x l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : x = d <;> by_cases hl : l = 0 <;> simp [h, hl]

theorem lane_vpbroadcastd256 (d r : XReg) (s : State) (x : XReg) (l : Nat) :
    ((VOp.vpbroadcastd .l256 d r).exec s).lane x l =
      if x = d then bcast32 (dword (s.xmm r) 0) else s.lane x l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : x = d <;> by_cases hl : l = 0 <;> simp [h, hl]

theorem lane_vmovdqa256 (d r : XReg) (s : State) (x : XReg) (l : Nat) :
    ((VOp.vmovdqa .l256 d r).exec s).lane x l = if x = d then s.lane r l else s.lane x l := by
  simp only [VOp.exec, State.lane, State.setV]
  by_cases h : x = d <;> by_cases hl : l = 0 <;> simp [h, hl]

/-- `r = a` broadcast to every doubleword of `d`. -/
theorem bcastY_ok (s : State) (d : XReg) (r : Reg) {a : Nat} (ha : a < 2 ^ 32)
    (hr : s.gpr r = BitVec.ofNat 64 a) :
    WP isa (.block [.vop (.vmovq d r), .vop (.vpbroadcastd .l256 d d)]) s fun t =>
      (∀ l < 2, t.lane d l = bcast32 (BitVec.ofNat 32 a)) ∧ YKeep [] (· = d) s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l _ => ?_, ⟨fun _ _ => rfl, rfl, rfl, rfl, fun x hx l => ?_⟩⟩
  · have e : ((VOp.vmovq d r).exec s).xmm d = (0 : BitVec 64) ++ s.gpr r := by
      have := lane_vmovq d r s d 0
      simp only [State.lane, ↓reduceIte] at this
      exact this
    rw [lane_vpbroadcastd256, ifT rfl, e, hr, dword_movq ha]
  · rw [lane_vpbroadcastd256, lane_vmovq, ifF hx, ifF hx]

/-- The magnitude `r8 = a` broadcast to `ymm13`, and one to `ymm12` and the
counter `ymm14`, through `rcx`. -/
theorem selSetY_ok (s : State) {a : Nat} (ha : a < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) :
    WP isa (.block [.vop (.vmovq .xmm13 .r8), .vop (.vpbroadcastd .l256 .xmm13 .xmm13), .mov32 .rcx (.imm 1),
      .vop (.vmovq .xmm12 .rcx), .vop (.vpbroadcastd .l256 .xmm12 .xmm12),
      .vop (.vmovdqa .l256 .xmm14 .xmm12)]) s fun t =>
      (∀ l < 2, t.lane .xmm13 l = bcast32 (BitVec.ofNat 32 a)) ∧
      (∀ l < 2, t.lane .xmm12 l = bcast32 (BitVec.ofNat 32 1)) ∧
      (∀ l < 2, t.lane .xmm14 l = bcast32 (BitVec.ofNat 32 1)) ∧
      YKeep [.rcx] (fun r => r = .xmm12 ∨ r = .xmm13 ∨ r = .xmm14) s t := by
  rw [show ([.vop (.vmovq .xmm13 .r8), .vop (.vpbroadcastd .l256 .xmm13 .xmm13), .mov32 .rcx (.imm 1),
      .vop (.vmovq .xmm12 .rcx), .vop (.vpbroadcastd .l256 .xmm12 .xmm12),
      .vop (.vmovdqa .l256 .xmm14 .xmm12)] : List Instr) =
    [.vop (.vmovq .xmm13 .r8), .vop (.vpbroadcastd .l256 .xmm13 .xmm13)] ++ ([.mov32 .rcx (.imm 1)] ++
      ([.vop (.vmovq .xmm12 .rcx), .vop (.vpbroadcastd .l256 .xmm12 .xmm12)] ++
        [.vop (.vmovdqa .l256 .xmm14 .xmm12)])) from rfl, WP.block_append_iff]
  refine WP.mono (bcastY_ok s .xmm13 .r8 (by omega) h8) fun s₁ ⟨b₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.mov32 .rcx (.imm 1)]) s₁ (fun s₂ =>
      s₂.gpr .rcx = BitVec.ofNat 64 1 ∧ YKeep [.rcx] (fun _ => False) s₁ s₂) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
      Option.some.injEq, exists_eq_left', State.setReg32, RegUpd.gpr_setReg, ite_true]
    refine ⟨by decide, fun r hr => ?_, rfl, rfl, rfl, fun _ _ _ => rfl⟩
    simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨c₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (bcastY_ok s₂ .xmm12 .rcx (by decide) c₂) fun s₃ ⟨b₃, k₃⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, ⟨fun r hr => ?_, ?_, ?_, ?_, fun x hx l => ?_⟩⟩
  · rw [lane_vmovdqa256, ifF (by decide), k₃.lane _ (by decide) l, k₂.lane _ id l, b₁ l hl]
  · rw [lane_vmovdqa256, ifF (by decide), b₃ l hl]
  · rw [lane_vmovdqa256, ifT rfl, b₃ l hl]
  · rw [VOp.exec_gpr, k₃.gpr r List.not_mem_nil, k₂.gpr r hr, k₁.gpr r List.not_mem_nil]
  · rw [VOp.exec_mem, k₃.mem, k₂.mem, k₁.mem]
  · rw [VOp.exec_rd, k₃.rd, k₂.rd, k₁.rd]
  · rw [VOp.exec_wr, k₃.wr, k₂.wr, k₁.wr]
  · simp only [not_or] at hx
    rw [lane_vmovdqa256, ifF hx.2.2, k₃.lane _ hx.1 l, k₂.lane _ id l, k₁.lane _ hx.2.1 l]

/-- The 256-bit accumulators `c < k` cleared. -/
theorem clearAccY_ok : ∀ k ≤ 11, ∀ (s : State),
    WP isa (.block ((List.range k).map fun c => .vop (.vbin .vpxor .l256 (selAcc c) (selAcc c) (selAcc c)))) s
      fun t => (∀ c < k, ∀ l < 2, t.lane (selAcc c) l = 0) ∧ YKeep [] (fun r => ∃ c < k, r = selAcc c) s t
  | 0, _, s => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), YKeep.refl _ _ _⟩
  | k + 1, hk, s => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (clearAccY_ok k (by omega) s) fun s₁ ⟨a₁, k₁⟩ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left']
    refine ⟨fun c hc l hl => ?_, ⟨fun r hr => by rw [VOp.exec_gpr, k₁.gpr r hr], by rw [VOp.exec_mem, k₁.mem],
      by rw [VOp.exec_rd, k₁.rd], by rw [VOp.exec_wr, k₁.wr], fun r hr l => ?_⟩⟩
    · rw [lane_vbin256]
      by_cases hck : c = k
      · rw [hck, ifT rfl]
        simp only [VBinOp.sse, XBinOp.eval, BitVec.xor_self]
        rfl
      · rw [ifF (fun h => hck (selAcc_inj c (by omega) k (by omega) h)), a₁ c (by omega) l hl]
    · rw [lane_vbin256, ifF (fun h => hr ⟨k, by omega, h⟩),
        k₁.lane r (fun ⟨c, hc, h⟩ => hr ⟨c, by omega, h⟩) l]

/-- A 32-byte write changes only its bytes. -/
theorem writeW256_out (m : Mem) (base : Addr) {d : Nat} (v : BitVec 256) (h : d + 32 ≤ 2 ^ 64) :
    Outside base d 32 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

/-- Lane `l` of a 256-bit register, as the bytes `16 l …` of its value. -/
theorem extract_ymm_lane (s : State) (r : XReg) {l : Nat} (hl : l < 2) :
    (s.ymm r).extractLsb' (8 * (16 * l)) (8 * 16) = s.lane r l := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [State.ymm, State.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    decide_eq_true hj, Bool.true_and]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · simp only [show 8 * (16 * 0) + j < 128 by omega, ↓reduceIte]
    exact congrArg _ (by omega)
  · simp only [show ¬ 8 * (16 * 1) + j < 128 by omega, ite_false, show (1 : Nat) ≠ 0 by omega]
    exact congrArg _ (by omega)

/-- The 256-bit accumulators `c < k` stored to the 32 bytes at `o + 32 c`:
lane `l` at `o + 16 (2 c + l)`. -/
theorem storeAccY_ok {base : Addr} {size o : Nat} : ∀ k, ∀ (s : State), Scr s base size → o + 32 * k ≤ size →
    WP isa (.block ((List.range k).map fun c => .vmovdquStore .l256 (sc (o + 32 * c)) (selAcc c))) s fun t =>
      (∀ c < k, ∀ l < 2, t.mem.readW (off base (o + 16 * (2 * c + l))) 128 = s.lane (selAcc c) l) ∧
      Outside base o (32 * k) s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      (∀ r l, t.lane r l = s.lane r l)
  | 0, s, _, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl,
      rfl, fun _ _ => rfl⟩
  | k + 1, s, hs, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (storeAccY_ok k s hs (by omega)) fun s₁ ⟨a₁, O₁, g₁, r₁, w₁, x₁⟩ => ?_
    have hw : InRegions s₁.wr (off base (o + 32 * k)) 32 := by
      rw [w₁]; exact ⟨_, hs.wr, hs.contains (by omega) (by decide)⟩
    have hd₁ : s₁.gpr .rdi = base := by rw [g₁]; exact hs.rdi
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hd₁, State.store256, hw,
      ite_true, Option.some.injEq, exists_eq_left']
    have O₂ := writeW256_out s₁.mem base (s₁.ymm (selAcc k)) (d := o + 32 * k) (by omega)
    refine ⟨fun c hc l hl => ?_, (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega)),
      g₁, r₁, w₁, fun r l => x₁ r l⟩
    by_cases hck : c = k
    · rw [hck]
      have e : off base (o + 16 * (2 * k + l)) = off base (o + 32 * k) + BitVec.ofNat 64 (16 * l) := by
        simp only [off]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show o + 32 * k + 16 * l = o + 16 * (2 * k + l) by omega]
      have h := readW_writeW_inside s₁.mem (off base (o + 32 * k)) (s₁.ymm (selAcc k)) (k := 16 * l) (n := 16)
        (by omega) (by decide)
      rw [extract_ymm_lane _ _ hl, x₁] at h
      rw [e]
      exact h
    · rw [O₂.read128 (by omega) (by omega), a₁ c (by omega) l hl]

theorem vzeroupper_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun t =>
      t.mem = s.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    VOp.exec_mem, VOp.exec_gpr, VOp.exec_rd, VOp.exec_wr]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- `selPassY`: `selPass_ok`'s postcondition, 32 bytes at a time, for an even
number of words, from a table in one region. -/
theorem selPassY_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {X : Addr} {a : Nat} (hn : K.M.n ≤ 14) (he : K.M.n % 2 = 0) (hH : K.H < 2 ^ 31) (ha : a < 2 ^ 31)
    (htb : 16 * K.M.n * K.H < 2 ^ 31) (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hx : s.gpr .rdx = X)
    (hreg : InRegions (s.rd ++ s.wr) X (16 * K.M.n * K.H)) (hE : K.E.x + 16 * K.M.n ≤ size) :
    WP isa (.block (selPassY K.E.x K.H (16 * K.M.n) (K.M.n / 2))) s fun t =>
      (∀ c < K.M.n, t.mem.readW (off base (K.E.x + 16 * c)) 128 = accVal s.mem X (16 * K.M.n) (16 * ·) a K.H c) ∧
      Outside base K.E.x (16 * K.M.n) s.mem t.mem ∧ KeepRegs [.rcx] s t := by
  have hnp : K.M.n / 2 ≤ 11 := by omega
  unfold selPassY
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (selSetY_ok s ha h8) fun s₁ ⟨b13, b12, b14, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (clearAccY_ok (K.M.n / 2) hnp s₁) fun s₂ ⟨z₂, k₂⟩ => ?_
  have n12 : ¬ ∃ c < K.M.n / 2, XReg.xmm12 = selAcc c := fun ⟨c, hc, h⟩ =>
    (selAcc_neY c (by omega)).2.1 h.symm
  have n13 : ¬ ∃ c < K.M.n / 2, XReg.xmm13 = selAcc c := fun ⟨c, hc, h⟩ =>
    (selAcc_neY c (by omega)).2.2.1 h.symm
  have n14 : ¬ ∃ c < K.M.n / 2, XReg.xmm14 = selAcc c := fun ⟨c, hc, h⟩ =>
    (selAcc_neY c (by omega)).2.2.2.1 h.symm
  rw [WP.block_append_iff]
  refine WP.mono (selEntriesY_ok (X := X) (st := 16 * K.M.n) hnp ha K.H hH s₂
    (by rw [k₂.gpr _ List.not_mem_nil, k₁.gpr _ (by decide), hx])
    (fun l hl => by rw [k₂.lane _ n13 l, b13 l hl]) (fun l hl => by rw [k₂.lane _ n12 l, b12 l hl])
    (fun l hl => by rw [k₂.lane _ n14 l, b14 l hl])
    (fun e he c hc => by
      rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]
      refine VG.CallLay.inRegions_sub hreg ?_ (by omega)
      have := Nat.mul_le_mul_left (16 * K.M.n) (show e + 1 ≤ K.H by omega)
      rw [Nat.mul_succ] at this
      omega)
    z₂) fun s₃ ⟨a₃, _, k₃⟩ => ?_
  have hs₃ : Scr s₃ base size :=
    ⟨by rw [k₃.gpr _ List.not_mem_nil, k₂.gpr _ List.not_mem_nil, k₁.gpr _ (by decide)]; exact hs.rdi,
      by rw [k₃.wr, k₂.wr, k₁.wr]; exact hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (storeAccY_ok (o := K.E.x) (K.M.n / 2) s₃ hs₃ (by omega))
    fun s₄ ⟨a₄, O₄, g₄, r₄, w₄, _⟩ => ?_
  refine WP.mono (vzeroupper_ok s₄) fun t ⟨m₅, g₅, r₅, w₅⟩ => ⟨fun c hc => ?_, ?_, ?_⟩
  · have h := a₄ (c / 2) (by omega) (c % 2) (by omega)
    rw [a₃ (c / 2) (by omega) (c % 2) (by omega), k₂.mem, k₁.mem,
      show 2 * (c / 2) + c % 2 = c by omega] at h
    rw [m₅]
    exact h
  · rw [k₃.mem, k₂.mem, k₁.mem, show 32 * (K.M.n / 2) = 16 * K.M.n by omega] at O₄
    rw [m₅]
    exact O₄
  · exact ⟨fun r hr => by rw [g₅, g₄, k₃.gpr r List.not_mem_nil, k₂.gpr r List.not_mem_nil, k₁.gpr r hr],
      by rw [r₅, r₄, k₃.rd, k₂.rd, k₁.rd], by rw [w₅, w₄, k₃.wr, k₂.wr, k₁.wr]⟩

/-- The selection's pass (`selPassV`): with AVX2 or not, `selPass_ok`'s
postcondition. -/
theorem selPassV_ok (K : TCombCfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {X : Addr} {a : Nat} (hn : K.M.n ≤ 14) (hH : K.H < 2 ^ 31) (ha : a < 2 ^ 31)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 a) (hx : s.gpr .rdx = X)
    (hr : ∀ e < K.H, ∀ c < K.M.n, InRegions (s.rd ++ s.wr) (X + BitVec.ofNat 64 (16 * K.M.n * e + 16 * c)) 16)
    (hreg : InRegions (s.rd ++ s.wr) X (16 * K.M.n * K.H)) (htb : 16 * K.M.n * K.H < 2 ^ 31)
    (hE : K.E.x + 16 * K.M.n ≤ size) :
    WP isa (.block K.selPassV) s fun t =>
      (∀ c < K.M.n, t.mem.readW (off base (K.E.x + 16 * c)) 128 = accVal s.mem X (16 * K.M.n) (16 * ·) a K.H c) ∧
      Outside base K.E.x (16 * K.M.n) s.mem t.mem ∧ KeepRegs [.rcx] s t := by
  unfold TCombCfg.selPassV
  split
  · next h =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact selPassY_ok K hs hn h.2 hH ha htb h8 hx hreg hE
  · exact selPass_ok K hs hn hH ha h8 hx hr hE

end VG.Proof.Weierstrass.X86_64
