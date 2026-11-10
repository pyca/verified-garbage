module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# Four-bit windows on PPC64LE: selecting `T_d`

`select_ok`: array 5 := table entry `d` (array `8 + d`), for the digit `d`
in `r18`, by a scan of the whole table, word-major: for each group of up to
four words, each accumulator starts as all ones and takes `&= T_j[c] | m_j`
for every entry `j`, with `m_j = 0` if `j = d` and all ones otherwise
(`accVal_step`), so that it ends as `T_d[c]` and no address depends on `d`.
`selEntry_ok` is an entry, `selGroup_ok` a group, `selGroups_ok` a loop of
groups.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Win

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.ModExp
open VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

theorem sub1_sign {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have : x = 0 ↔ x.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    this]
  split <;> omega_arith

/-- `notDigit`: `r20 :=` 0 if `j = d`, else all ones. -/
theorem notDigit_ok {s : State} {j d : Nat} (h19 : s.gpr .r19 = BitVec.ofNat 64 j)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hj : j < 16) (hd : d < 16) :
    WP isa (.block notDigit) s fun t =>
      (t.gpr .r20 = (if j = d then 0 else BitVec.allOnes 64) ∧ t.mem = s.mem) ∧ Keep [.r3, .r20] s t := by
  have hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
  have he : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0) ↔ j = d := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
        at this
    · rintro rfl; rfl
  refine WP.keep _ ?_ (by decide)
  unfold notDigit
  prun [h19, h18, sub1_sign hx]
  by_cases e : j = d
  · subst e; simp only [BitVec.xor_self, ite_true]; rfl
  · simp only [e, show ¬ (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0) from fun h => e (he.mp h), ite_false]; rfl

/-- What accumulator `c` of the group at word `i` holds once the entries
below `j` are gathered: its word of `T_d` if `d < j`, else all ones. -/
abbrev accVal (m : Mem) (B : Addr) (w d i j c : Nat) : BitVec 64 :=
  if d < j then word m B (slot w (8 + d) + 8 * (i + c)) else BitVec.allOnes 64

theorem accVal_step (m : Mem) (B : Addr) (w d i j c : Nat) :
    accVal m B w d i j c &&& (word m B (slot w (8 + j) + 8 * (i + c)) ||| (if j = d then 0 else BitVec.allOnes 64)) =
      accVal m B w d i (j + 1) c := by
  by_cases e : j = d
  · subst e
    simp only [accVal, Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true, BitVec.allOnes_and]
    exact BitVec.or_zero
  · have : (d < j + 1) ↔ d < j := ⟨fun h => by omega_arith, fun h => by omega_arith⟩
    simp only [accVal, e, ite_false, BitVec.or_allOnes, BitVec.and_allOnes, this]

theorem acc_inj : ∀ c < 4, ∀ c' < 4, acc c = acc c' → c = c' := by decide

theorem acc_ne : ∀ c < 4, acc c ≠ .r0 ∧ acc c ≠ .r3 ∧ acc c ≠ .r5 ∧ acc c ≠ .r8 ∧ acc c ≠ .r19 ∧
    acc c ≠ .r20 ∧ acc c ≠ .r4 ∧ acc c ≠ .r9 ∧ acc c ≠ .r18 ∧ acc c ≠ .r10 ∧ acc c ≠ .r11 ∧
    acc c ≠ .r12 ∧ acc c ≠ .r29 := by decide

theorem acc_mem : ∀ c < 4, acc c ∈ [.r14, .r15, .r16, .r17] := by decide

theorem keep_pick {s t : State} {c : Nat} (hc : c < 4) (h : Keep [.r0, acc c] s t) :
    Keep [.r0, .r14, .r15, .r16, .r17] s t :=
  h.mono fun r hr => by
    have := acc_mem c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr this ⊢
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr this

theorem keep_one {s t : State} {c : Nat} (hc : c < 4) (h : Keep [acc c] s t) : Keep [.r14, .r15, .r16, .r17] s t :=
  h.mono fun r hr => by
    have := acc_mem c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr this
    rw [hr]
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using this

/-- `pick c`: accumulator `c &=` the word at `r8 + 8 c` `| r20`. -/
theorem pick_ok {s : State} {B : Addr} {Z x : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B x) :
    ∀ c < 4, x + 8 * c + 8 ≤ Z → WP isa (.block (pick c)) s fun t =>
      (t.gpr (acc c) = s.gpr (acc c) &&& (word s.mem B (x + 8 * c) ||| s.gpr .r20) ∧ t.mem = s.mem) ∧
        Keep [.r0, acc c] s t
  | 0, _, hx => WP.keep _ (by unfold pick; prun [h8, hs.ld (d := x) (n := 8) (by omega_arith), show acc 0 = .r14 from rfl]) (by decide)
  | 1, _, hx => WP.keep _ (by unfold pick; prun [h8, hs.ld (d := x + 8) (n := 8) (by omega_arith), show acc 1 = .r15 from rfl]) (by decide)
  | 2, _, hx => WP.keep _ (by unfold pick; prun [h8, hs.ld (d := x + 16) (n := 8) (by omega_arith), show acc 2 = .r16 from rfl]) (by decide)
  | 3, _, hx => WP.keep _ (by unfold pick; prun [h8, hs.ld (d := x + 24) (n := 8) (by omega_arith), show acc 3 = .r17 from rfl]) (by decide)

/-- The picks of the `k ≤ 4` words of a group, the mask `v` in `r20`. -/
theorem picks_ok {s : State} {B : Addr} {Z x : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B x) :
    ∀ k ≤ 4, x + 8 * k ≤ Z → WP isa (.block ((List.range k).flatMap pick)) s fun t =>
      ((∀ c < 4, t.gpr (acc c) =
        if c < k then s.gpr (acc c) &&& (word s.mem B (x + 8 * c) ||| s.gpr .r20) else s.gpr (acc c)) ∧
        t.mem = s.mem) ∧ Keep [.r0, .r14, .r15, .r16, .r17] s t
  | 0, _, _ => WP.block_nil ⟨⟨fun c _ => by simp, rfl⟩, (Keep.refl [] s).mono (by decide)⟩
  | k + 1, hk, hx => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (picks_ok hs h8 k (by omega_arith) (by omega_arith)) fun t ⟨⟨ta, tm⟩, tk⟩ => ?_
    have ht8 : t.gpr .r8 = off B x := (tk.gpr _ (by decide)).trans h8
    refine WP.mono (pick_ok (hs.congr tk.wr) ht8 k (by omega_arith) (by omega_arith))
      fun u ⟨⟨ua, um⟩, uk⟩ =>
        ⟨⟨fun c hc => ?_, um.trans tm⟩, (tk.trans (keep_pick (by omega_arith) uk)).mono (by decide)⟩
    · by_cases e : c = k
      · subst e
        rw [ua, ta c hc, tm, tk.gpr .r20 (by decide)]
        simp
      · have hne : acc c ≠ acc k := fun h => e (acc_inj c hc k (by omega_arith) h)
        rw [uk.gpr _ (by simp [hne, (acc_ne c hc).1]), ta c hc]
        have : (c < k + 1) ↔ c < k := ⟨fun h => by omega_arith, fun h => by omega_arith⟩
        simp only [this]

/-- The registers an entry of `select` writes. -/
def entryRegs : List Reg := [.r0, .r3, .r8, .r14, .r15, .r16, .r17, .r19, .r20]

/-- `selEntry k`: entry `j` gathered into the accumulators of the group of
`k ≤ 4` words at word `i`. -/
theorem selEntry_ok {k : Nat} (hk : k ≤ 4) {s : State} {B : Addr} {Z w N d i j : Nat} (h : WCtx s B Z w N)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) (hj : j < 16) (hi : i + k ≤ w)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = off B (slot w (8 + j) + 8 * i))
    (ha : ∀ c < k, s.gpr (acc c) = accVal s.mem B w d i j c) :
    WP isa (.block (selEntry k)) s fun t =>
      (t.gpr .r19 = BitVec.ofNat 64 (j + 1) ∧ t.gpr .r8 = off B (slot w (8 + (j + 1)) + 8 * i) ∧
        (∀ c < k, t.gpr (acc c) = accVal s.mem B w d i (j + 1) c) ∧ t.mem = s.mem) ∧ Keep entryRegs s t := by
  have hT := h.sl (j := 8 + j) (by omega_arith)
  unfold selEntry
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (notDigit_ok h19 h18 hj hd) fun t ⟨⟨t20, tm⟩, tk⟩ => ?_
  refine WP.mono (picks_ok (h.scr.congr tk.wr) ((tk.gpr _ (by decide)).trans h8) k hk (by omega_arith))
    fun u ⟨⟨ua, um⟩, uk⟩ => ?_
  have hu19 : u.gpr .r19 = BitVec.ofNat 64 j := by rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h19]
  have hu8 : u.gpr .r8 = off B (slot w (8 + j) + 8 * i) := by rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h8]
  have hu29 : u.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) := by
    rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h.r29]
  have htail : WP isa (.block [.add .r8 .r8 .r29, .addi .r19 .r19 1]) u fun v =>
      (v.gpr .r19 = BitVec.ofNat 64 (j + 1) ∧ v.gpr .r8 = off B (slot w (8 + (j + 1)) + 8 * i) ∧ v.mem = u.mem) ∧
        Keep [.r8, .r19] u v := by
    refine WP.keep _ ?_ (by decide)
    have e : slot w (8 + (j + 1)) + 8 * i = slot w (8 + j) + 8 * i + 8 * (w + 2) := by
      unfold slot; rw [show 8 + (j + 1) = (8 + j) + 1 by omega_arith, Nat.succ_mul]; omega_arith
    prun [hu19, hu8, hu29, e, ← BitVec.ofNat_add]
  refine WP.mono htail fun v ⟨⟨v19, v8, vm⟩, vk⟩ => ⟨⟨v19, v8, fun c hc => ?_, by rw [vm, um, tm]⟩, ?_⟩
  · have hc4 : c < 4 := by omega_arith
    rw [vk.gpr _ (by have := acc_ne c hc4; simp [this.2.2.2.1, this.2.2.2.2.1]), ua c hc4]
    simp only [hc, ↓reduceIte]
    rw [tm, tk.gpr _ (by have := acc_ne c hc4; simp [this.2.1, this.2.2.2.2.2.1]), t20, ha c hc, show slot w (8 + j) + 8 * i + 8 * c = slot w (8 + j) + 8 * (i + c) by omega_arith, accVal_step]
  · exact ((tk.trans uk).trans vk).mono

/-- Entries `0` to `n - 1` gathered. -/
theorem selEntries_ok {k : Nat} (hk : k ≤ 4) {s : State} {B : Addr} {Z w N d i : Nat} (h : WCtx s B Z w N)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) (hi : i + k ≤ w)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 0) (h8 : s.gpr .r8 = off B (slot w 8 + 8 * i))
    (ha : ∀ c < k, s.gpr (acc c) = BitVec.allOnes 64) :
    ∀ n ≤ 16, WP isa (.block (List.replicate n (selEntry k)).flatten) s fun t =>
      (t.gpr .r19 = BitVec.ofNat 64 n ∧ t.gpr .r8 = off B (slot w (8 + n) + 8 * i) ∧
        (∀ c < k, t.gpr (acc c) = accVal s.mem B w d i n c) ∧ t.mem = s.mem) ∧ Keep entryRegs s t
  | 0, _ => WP.block_nil ⟨⟨h19, h8, fun c hc => by rw [ha c hc]; simp only [accVal, Nat.not_lt_zero, ite_false],
      rfl⟩, (Keep.refl [] s).mono (by decide)⟩
  | n + 1, hn => by
    rw [List.replicate_succ', List.flatten_append, List.flatten_singleton, WP.block_append_iff]
    refine WP.mono (selEntries_ok hk h h18 hd hi h19 h8 ha n (by omega_arith)) fun t ⟨⟨t19, t8, ta, tm⟩, tk⟩ => ?_
    have ht := h.regs tk (by decide) tm
    refine WP.mono (selEntry_ok hk ht (by rw [tk.gpr _ (by decide), h18]) hd (by omega_arith) hi t19 t8
      (fun c hc => by rw [ta c hc, tm])) fun u ⟨⟨u19, u8, ua, um⟩, uk⟩ =>
      ⟨⟨u19, u8, fun c hc => by rw [ua c hc, tm], um.trans tm⟩, (tk.trans uk).mono⟩

/-- The accumulators of `k ≤ 4` words := all ones. -/
theorem accInit_ok {s : State} :
    ∀ k ≤ 4, WP isa (.block ((List.range k).flatMap fun c => [.li (acc c) 0, .subi (acc c) (acc c) 1])) s
      fun t => ((∀ c < k, t.gpr (acc c) = BitVec.allOnes 64) ∧ t.mem = s.mem) ∧ Keep [.r14, .r15, .r16, .r17] s t
  | 0, _ => WP.block_nil ⟨⟨fun c hc => absurd hc (Nat.not_lt_zero _), rfl⟩, (Keep.refl [] s).mono (by decide)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (accInit_ok k (by omega_arith)) fun t ⟨⟨ta, tm⟩, tk⟩ => ?_
    have one : ∀ c < 4, WP isa (.block [.li (acc c) 0, .subi (acc c) (acc c) 1]) t fun u =>
        (u.gpr (acc c) = BitVec.allOnes 64 ∧ u.mem = t.mem) ∧ Keep [acc c] t u := by
      intro c hc
      match c, hc with
      | 0, _ => exact WP.keep _ (by prun [show acc 0 = .r14 from rfl]; rfl) (by decide)
      | 1, _ => exact WP.keep _ (by prun [show acc 1 = .r15 from rfl]; rfl) (by decide)
      | 2, _ => exact WP.keep _ (by prun [show acc 2 = .r16 from rfl]; rfl) (by decide)
      | 3, _ => exact WP.keep _ (by prun [show acc 3 = .r17 from rfl]; rfl) (by decide)
    refine WP.mono (one k (by omega_arith)) fun u ⟨⟨ua, um⟩, uk⟩ =>
      ⟨⟨fun c hc => ?_, um.trans tm⟩, (tk.trans (keep_one (by omega_arith) uk)).mono (by decide)⟩
    · by_cases e : c = k
      · subst e; exact ua
      · rw [uk.gpr _ (by simpa using fun h => e (acc_inj c (by omega_arith) k (by omega_arith) h)),
          ta c (by omega_arith)]

/-- The `k ≤ 4` accumulators stored at `r5`, the offset `x`. -/
theorem accStore_ok {s : State} {B : Addr} {Z x : Nat} (hs : Scr s B Z) (h5 : s.gpr .r5 = off B x) :
    ∀ k ≤ 4, x + 8 * k ≤ Z → WP isa (.block ((List.range k).flatMap fun c => [.store .d (acc c) .r5 (8 * c)])) s
      fun t => ((∀ c < k, word t.mem B (x + 8 * c) = s.gpr (acc c)) ∧ Outside B x (8 * k) s.mem t.mem) ∧
        Keep [] s t
  | 0, _, _ => WP.block_nil ⟨⟨fun c hc => absurd hc (Nat.not_lt_zero _), Outside.refl _ _ _ _⟩, Keep.refl _ _⟩
  | k + 1, hk, hx => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (accStore_ok hs h5 k (by omega_arith) (by omega_arith)) fun t ⟨⟨ta, to⟩, tk⟩ => ?_
    have one : WP isa (.block [.store .d (acc k) .r5 (8 * k)]) t fun u =>
        (u.mem = t.mem.writeW (off B (x + 8 * k)) (t.gpr (acc k))) ∧ Keep [] t u := by
      refine WP.keep _ ?_ (by rfl)
      prun [(tk.gpr _ (by decide)).trans h5, (hs.congr tk.wr).st (show x + 8 * k + 8 ≤ Z by omega_arith),
        show 8 * k < 2 ^ 15 by omega_arith, show 8 * k % 4 = 0 by omega_arith]
    refine WP.mono one fun u ⟨um, uk⟩ => ⟨⟨fun c hc => ?_, ?_⟩, (tk.trans uk).mono⟩
    · rw [um]
      by_cases e : c = k
      · subst e; rw [word_writeW_self, tk.gpr _ (by simp)]
      · rw [(writeW_outside t.mem B (d := x + 8 * k) _ (by omega_arith)).word (by omega_arith) (by omega_arith),
          ta c (by omega_arith)]
    · rw [um]
      exact (to.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW_outside _ B (d := x + 8 * k) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- The registers a group of `select` writes, but its counter. -/
def groupRegs : List Reg := [.r0, .r3, .r5, .r8, .r14, .r15, .r16, .r17, .r19, .r20]

/-- `selGroup k cnt`: the `k ≤ 4` words of array 5 from word `i` := those
of `T_d`, `r5` past them, `cnt -= 1`. -/
theorem selGroup_ok {k : Nat} (hk : k ≤ 4) {cnt : Reg} (hcnt : cnt = .r4 ∨ cnt = .r9) {s : State} {B : Addr}
    {Z w N d i : Nat} (h : WCtx s B Z w N) (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) (hi : i + k ≤ w)
    (h5 : s.gpr .r5 = off B (slot w 5 + 8 * i)) :
    WP isa (.block (selGroup k cnt)) s fun t =>
      (t.gpr .r5 = off B (slot w 5 + 8 * (i + k)) ∧ t.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1 ∧
        (∀ c < k, word t.mem B (slot w 5 + 8 * (i + c)) = word s.mem B (slot w (8 + d) + 8 * (i + c))) ∧
        Outside B (slot w 5 + 8 * i) (8 * k) s.mem t.mem) ∧ Keep (cnt :: groupRegs) s t := by
  have hO := h.sl (j := 5) (by decide)
  have hnw := h.scr.nowrap
  unfold selGroup
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (accInit_ok (s := s) k hk) fun t ⟨⟨ta, tm⟩, tk⟩ => ?_
  have ht := h.regs tk (by decide) tm
  have hpre : WP isa (.block [.li .r19 0, .add .r8 .r5 .r29, .add .r8 .r8 .r29, .add .r8 .r8 .r29]) t fun u =>
      (u.gpr .r19 = BitVec.ofNat 64 0 ∧ u.gpr .r8 = off B (slot w 8 + 8 * i) ∧ u.mem = t.mem) ∧
        Keep [.r19, .r8] t u := by
    refine WP.keep _ ?_ (by decide)
    have e : slot w 8 + 8 * i = slot w 5 + 8 * i + 8 * (w + 2) + 8 * (w + 2) + 8 * (w + 2) := by
      unfold slot; omega_arith
    prun [(tk.gpr _ (by decide)).trans h5, ht.r29, e, ← BitVec.ofNat_add]
  refine WP.mono hpre fun u ⟨⟨u19, u8, um⟩, uk⟩ => ?_
  have hu := ht.regs uk (by decide) um
  refine WP.mono (selEntries_ok hk hu (by rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h18]) hd hi u19 u8
    (fun c hc => by rw [uk.gpr _ (by have := acc_ne c (by omega_arith); simp [this.2.2.2.1, this.2.2.2.2.1]),
      ta c hc]) 16 (Nat.le_refl _)) fun v ⟨⟨_, _, va, vm⟩, vk⟩ => ?_
  have hv5 : v.gpr .r5 = off B (slot w 5 + 8 * i) := by
    rw [vk.gpr _ (by decide), uk.gpr _ (by decide), tk.gpr _ (by decide), h5]
  refine WP.mono (accStore_ok (h.scr.congr (vk.wr.trans (uk.wr.trans tk.wr))) hv5 k hk (by omega_arith))
    fun x ⟨⟨xa, xo⟩, xk⟩ => ?_
  have htail : WP isa (.block [.addi .r5 .r5 (8 * k), .subi cnt cnt 1]) x fun y =>
      (y.gpr .r5 = off B (slot w 5 + 8 * (i + k)) ∧ y.gpr cnt = x.gpr cnt - BitVec.ofNat 64 1 ∧ y.mem = x.mem) ∧
        Keep [.r5, cnt] x y := by
    have h5x : x.gpr .r5 = off B (slot w 5 + 8 * i) := (xk.gpr _ (by decide)).trans hv5
    have e : slot w 5 + 8 * (i + k) = slot w 5 + 8 * i + 8 * k := by omega_arith
    rcases hcnt with rfl | rfl
    · exact WP.keep _ (by prun [h5x, e, ← BitVec.ofNat_add, show 8 * k < 2 ^ 15 by omega_arith]) (by rfl)
    · exact WP.keep _ (by prun [h5x, e, ← BitVec.ofNat_add, show 8 * k < 2 ^ 15 by omega_arith]) (by rfl)
  have hc : ∀ {r : Reg}, r = .r4 ∨ r = .r9 → x.gpr r = s.gpr r := fun {r} hr => by
    rcases hr with rfl | rfl <;>
      rw [xk.gpr _ (by decide), vk.gpr _ (by decide), uk.gpr _ (by decide), tk.gpr _ (by decide)]
  refine WP.mono htail fun y ⟨⟨y5, yc, ym⟩, yk⟩ => ⟨⟨y5, by rw [yc, hc hcnt], fun c hc' => ?_, ?_⟩, ?_⟩
  · rw [ym, show slot w 5 + 8 * (i + c) = slot w 5 + 8 * i + 8 * c by omega_arith, xa c hc', va c hc']
    simp only [accVal, hd, ↓reduceIte]
    rw [um, tm]
  · rw [ym]; rw [vm, um, tm] at xo; exact xo
  · rcases hcnt with rfl | rfl <;> exact ((((tk.trans uk).trans vk).trans xk).trans yk).mono (by decide)

/-- `selGroups k cnt`: `n` groups (`cnt = n`) of `k ≤ 4` words of array 5
from word `i`, each word := that of `T_d`. -/
theorem selGroups_ok {k : Nat} (hk : k ≤ 4) {cnt : Reg} (hcnt : cnt = .r4 ∨ cnt = .r9) {s : State} {B : Addr}
    {Z w N d i n : Nat} (h : WCtx s B Z w N) (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16)
    (hi : i + k * n ≤ w) (hnw' : n ≤ w) (h5 : s.gpr .r5 = off B (slot w 5 + 8 * i))
    (hc : s.gpr cnt = BitVec.ofNat 64 n) :
    WP isa (selGroups k cnt) s fun t =>
      (WCtx t B Z w N ∧ t.gpr .r18 = BitVec.ofNat 64 d ∧ t.gpr .r5 = off B (slot w 5 + 8 * (i + k * n)) ∧
        (∀ c < k * n, word t.mem B (slot w 5 + 8 * (i + c)) = word s.mem B (slot w (8 + d) + 8 * (i + c))) ∧
        Outside B (slot w 5 + 8 * i) (8 * (k * n)) s.mem t.mem) ∧ Keep (cnt :: groupRegs) s t := by
  have hw := h.w31
  have hO := h.sl (j := 5) (by decide)
  have hnw := h.nw
  have := slot_lt (w := w) (show 5 < 24 by decide)
  have := slot_lt (w := w) (show 8 + d < 24 by omega_arith)
  have hn : n < 2 ^ 64 := by omega_arith
  have hcr : ∀ {r : Reg}, r = .r4 ∨ r = .r9 → (r ∈ cnt :: groupRegs ↔ r = cnt) := fun {r} hr => by
    rcases hr with rfl | rfl <;> rcases hcnt with rfl | rfl <;> decide
  unfold selGroups
  refine WP.ite _ (eval_zero_ofNat s cnt hn hc) (fun hz => ?_) (fun hz => ?_)
  · have e : n = 0 := of_decide_eq_true hz
    subst e
    exact WP.block_nil ⟨⟨h, h18, by rw [h5, Nat.mul_zero, Nat.add_zero], fun c hc => absurd hc (by simp),
      Outside.refl _ _ _ _⟩, (Keep.refl [] s).mono (by simp)⟩
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hz)
  let Inv : Nat → State → Prop := fun g t =>
    WCtx t B Z w N ∧ t.gpr .r18 = BitVec.ofNat 64 d ∧ t.gpr .r5 = off B (slot w 5 + 8 * (i + k * g)) ∧
      (∀ c < k * g, word t.mem B (slot w 5 + 8 * (i + c)) = word s.mem B (slot w (8 + d) + 8 * (i + c))) ∧
      Outside B (slot w 5 + 8 * i) (8 * (k * g)) s.mem t.mem ∧ Keep (cnt :: groupRegs) s t
  refine WP.mono (wp_countdown (body := .block (selGroup k cnt)) (cnt := cnt) (N := n) hn hn0 Inv
    (fun g hg t ⟨et, t18, t5, tw, to, tk⟩ _ => ?_)
    ⟨h, h18, by rw [h5, Nat.mul_zero, Nat.add_zero], fun c hc => absurd hc (by simp), Outside.refl _ _ _ _,
      (Keep.refl [] s).mono (by simp)⟩ hc) fun t ⟨a, b, c, d, e, f⟩ => ⟨⟨a, b, c, d, e⟩, f⟩
  have hkg : k * g + k ≤ k * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hg
  refine WP.mono (selGroup_ok hk hcnt et t18 hd (i := i + k * g) (by omega_arith) t5)
    fun u ⟨⟨u5, uc, uw, uo⟩, uk⟩ => ⟨⟨?_, ?_, ?_, fun c hc => ?_, ?_, ?_⟩, uc⟩
  -- What changed is in array 5.
  · have := (uo.mono (o' := slot w 5) (n' := 8 * (w + 2)) (by omega_arith) (by omega_arith))
    exact et.of uk (by rcases hcnt with rfl | rfl <;> decide) (win_of_out this (by decide) (by decide))
  · rw [uk.gpr _ (by rcases hcnt with rfl | rfl <;> decide), t18]
  · rw [u5, Nat.mul_succ, Nat.add_assoc]
  · rw [Nat.mul_succ] at hc
    have tT : word t.mem B (slot w (8 + d) + 8 * (i + c)) = word s.mem B (slot w (8 + d) + 8 * (i + c)) := by
      have := slot_lt (w := w) (show 5 < 8 + d by omega_arith)
      have := slot_lt (w := w) (show 8 + d < 24 by omega_arith)
      have := h.sl (j := 8 + d) (by omega_arith)
      exact to.word (by omega_arith) (by omega_arith)
    by_cases hlt : c < k * g
    · rw [uo.word (by omega_arith) (by omega_arith), tw c hlt]
    · obtain ⟨c', rfl⟩ : ∃ c', c = k * g + c' := ⟨c - k * g, by omega_arith⟩
      have := uw c' (by omega_arith)
      rw [show i + (k * g + c') = i + k * g + c' by omega_arith, this, ← show i + (k * g + c') = i + k * g + c' by
        omega_arith, tT]
  · rw [Nat.mul_succ, Nat.mul_add]
    exact (to.mono (Nat.le_refl _) (by omega_arith)).trans (uo.mono (by omega_arith) (by omega_arith))
  · rcases hcnt with rfl | rfl <;> exact (tk.trans uk).mono (by decide)

theorem wordsVal_congr {m m' : Mem} {B : Addr} :
    ∀ (n : Nat) {d d' : Nat}, (∀ c < n, Mont.word m' B (d' + 8 * c) = Mont.word m B (d + 8 * c)) →
      wordsVal m' B d' n = wordsVal m B d n
  | 0, _, _, _ => rfl
  | n + 1, d, d', h => by
    simp only [wordsVal]
    rw [show Mont.word m' B d' = Mont.word m B d by simpa using h 0 (by omega_arith),
      wordsVal_congr n (d := d + 8) (d' := d' + 8) fun c hc => by
        simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_comm 8] using h (c + 1) (by omega_arith)]

theorem ofNat_shr3 {n : Nat} (hn : n < 2 ^ 62) : BitVec.ofNat 64 (2 * n) >>> 3 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

theorem ofNat_and3 (n : Nat) :
    BitVec.ofNat 64 (2 * n) >>> 1 &&& BitVec.ofNat 64 3 = BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show (3 : Nat) % 2 ^ 64 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

/-- The registers the selection writes. -/
def selectRegs : List Reg := [.r0, .r3, .r4, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r19, .r20]

/-- `select`: array 5 := `T_d`, for `d` in `r18`; only array 5 changes. -/
theorem select_ok {s : State} {B : Addr} {Z w N d : Nat} (h : WCtx s B Z w N)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa select s fun t =>
      (A t.mem B w 5 = A s.mem B w (8 + d) ∧ (∀ j < 24, j ≠ 3 → j ≠ 5 → A t.mem B w j = A s.mem B w j) ∧ WCtx t B Z w N ∧
        Outs B (win w) s.mem t.mem) ∧ Keep selectRegs s t := by
  have hw := h.w31
  have hO := h.sl (j := 5) (by decide)
  have hnw := h.nw
  unfold select
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hpre : WP isa (.block [.lsr .d .r4 .r11 3, .lsr .d .r0 .r11 1, .li .r9 3, .logic .and .r9 .r0 .r9]) s
      fun t => (t.gpr .r4 = BitVec.ofNat 64 (w / 4) ∧ t.gpr .r9 = BitVec.ofNat 64 (w % 4) ∧ t.mem = s.mem) ∧
        Keep [.r4, .r0, .r9] s t := by
    refine WP.keep _ ?_ (by decide)
    prun [h.r11, ofNat_shr3 (show w < 2 ^ 62 by omega_arith), ofNat_and3 w]
  refine WP.mono hpre fun t ⟨⟨t4, t9, tm⟩, tk⟩ => ?_
  have ht := h.regs tk (by decide) tm
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ht.r10 ht.r29 5) fun u ⟨⟨u5, um⟩, uk⟩ => ?_
  have hu := ht.regs uk (by decide) um
  have hm : u.mem = s.mem := um.trans tm
  refine WP.seq (WP.mono (selGroups_ok (k := 4) (by decide) (.inl rfl) hu (n := w / 4) (i := 0)
    (by rw [uk.gpr _ (by decide), tk.gpr _ (by decide), h18]) hd (by omega_arith) (by omega_arith) (by rw [u5]; rfl)
    (by rw [uk.gpr _ (by decide), t4])) fun v ⟨⟨ev, v18, v5, vw, vo⟩, vk⟩ => ?_)
  refine WP.mono (selGroups_ok (k := 1) (by decide) (.inr rfl) ev (n := w % 4) (i := 4 * (w / 4)) v18 hd
    (by omega_arith) (by omega_arith) (by rw [v5, Nat.zero_add])
    (by rw [vk.gpr _ (by decide), uk.gpr _ (by decide), t9])) fun x ⟨⟨ex, _, _, xw, xo⟩, xk⟩ => ?_
  have hw4 : 4 * (w / 4) + 1 * (w % 4) = w := by omega_arith
  -- Only array 5 changed.
  have o5 : Outside B (slot w 5) (8 * (w + 2)) s.mem x.mem := by
    rw [← hm]
    exact (vo.mono (Nat.le_refl _) (by omega_arith)).trans (xo.mono (by omega_arith) (by omega_arith))
  refine ⟨⟨?_, fun j hj _ h5 => arr_out o5 hj h5 hnw, ex, win_of_out o5 (by decide) (by decide)⟩, ?_⟩
  · simp only [A, ← wordsVal_eq_val32]
    refine wordsVal_congr w fun c hc => ?_
    have := slot_lt (w := w) (show 5 < 8 + d by omega_arith)
    have := slot_lt (w := w) (show 8 + d < 24 by omega_arith)
    have := h.sl (j := 8 + d) (by omega_arith)
    by_cases hlt : c < 4 * (w / 4)
    · refine (xo.word (by omega_arith) (by omega_arith)).trans ?_
      have := vw c hlt
      simp only [Nat.zero_add, hm] at this
      exact this
    · obtain ⟨c', rfl⟩ : ∃ c', c = 4 * (w / 4) + c' := ⟨c - 4 * (w / 4), by omega_arith⟩
      refine (xw c' (by omega_arith)).trans ((vo.word (by omega_arith) (by omega_arith)).trans ?_)
      rw [hm]
  · exact ((((tk.trans uk).trans vk).trans xk)).mono (by decide)

end VG.Proof.Bignum.PPC64LE.Win
