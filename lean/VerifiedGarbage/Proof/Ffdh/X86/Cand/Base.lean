module

public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordCut32
import VerifiedGarbage.Proof.Weierstrass.Words32

/-!
# The FFDH candidate on i686: words of numbers and of the header

The header words a stage writes (`hdr_store`), the lowest word of a number
(`lowWord_ok`), its lowest bit set (`setLow_ok`), and a number cut to its low
`k` bits, its top bit set or not (`cut_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- A header word the candidate keeps its state in: above the operations' own words and below the
saved registers, or between the multiplier's word and the product. -/
abbrev Hdr (d : Nat) : Prop := ((16 ≤ d ∧ d + 4 ≤ 32) ∨ (52 ≤ d ∧ d + 4 ≤ 256)) ∧ d % 4 = 0

theorem hdr_cur : Hdr curOff := ⟨.inl ⟨by decide, by decide⟩, by decide⟩
theorem hdr_oct : Hdr octOff := ⟨.inr ⟨by decide, by decide⟩, by decide⟩

theorem hdr_fit (h : In Ex base bytes len args s) {d : Nat} (hd : Hdr d) : d + 4 ≤ bytes := by
  have := h.need
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  omega

/-- A header word, within `fR`. -/
theorem hdr_inF {d : Nat} (hd : Hdr d) : InF len (d, 4) := by
  have nb : numBase = 3336 := rfl
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  rcases hd.1 with h | h
  · exact .inl h.2
  · exact .inr ⟨by dsimp only; omega, by dsimp only; omega⟩

/-- A header word read. -/
theorem hdr_read (h : In Ex base bytes len args s) {d : Nat} (hd : Hdr d) :
    readSrc s (.mem (sc d)) = some (BitVec.ofNat 32 (w32 s.mem base d)) := by
  rw [readSrc_sc h.scratch (hdr_fit h hd), w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A register stored into a header word: a stage, the word written, the others kept. -/
theorem hdr_store {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {d : Nat} (hd : Hdr d)
    {r : Reg}
    (k : ∀ t, Step Ex base bytes len args s t → w32 t.mem base d = (s.gpr r).toNat →
      Kept base len [] [d] s.mem t.mem → Outside base d 4 s.mem t.mem → (∀ q, t.gpr q = s.gpr q) →
      t.cf = s.cf → t.zf = s.zf → WP isa (.block is) t Q) :
    WP isa (.block (.store (sc d) r :: is)) s Q := by
  have bl := h.bytes_lt
  have hf := hdr_fit h hd
  refine wp_storeS (h.scratch.ea (d := d) (by omega)) (h.scratch.write (d := d) (n := 4) (by omega)) fun u M => ?_
  have O : Outside base d 4 s.mem u.mem := by rw [M.mem]; exact writeW32_outside _ _ _ (by omega)
  have K : Keeps [] s u := M.keeps []
  have I : In Ex base bytes len args u := h.keep K (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega))
  refine k u ⟨I, fR_of_outside h O (hdr_inF hd), K.mono (by decide)⟩ ?_ ?_ O (fun q => K.1 q (by simp)) M.cf M.zf
  · show (u.mem.readW (off base d) 32).toNat = _
    rw [M.mem, Mem.readW_writeW_self32]
  · have nb : numBase = 3336 := rfl
    refine ⟨fun j hj9 hj _ => ?_, fun e he he' e4 hn => ?_⟩
    · have f := slot_fit1 h (j := j) (by omega)
      rw [cb1] at f
      have := lo_wide len j
      have ce := bc_eq_cwc len .wide
      exact O.val32 (.inr (by omega)) (by omega)
    · exact O.w32 (by simp only [List.mem_singleton] at hn; omega) (by omega)

/-! ## The lowest word of a number -/

/-- The lowest word of a wide slot. -/
theorem low_w32 (m : Mem) (len j : Nat) (hw : 0 < cwc len .wide) :
    w32 m base (lo len (.slot .wide j)) = sv m base len .wide j % 2 ^ 32 := by
  obtain ⟨k, hk⟩ : ∃ k, cwc len .wide = k + 1 := ⟨cwc len .wide - 1, by omega⟩
  show _ = val32 m base (lo len (.slot .wide j)) (cwc len .wide) % 2 ^ 32
  rw [hk, val32]
  have hl : w32 m base (lo len (.slot .wide j)) < 2 ^ 32 := (m.readW _ 32).isLt
  omega

theorem cwc_pos (h : In Ex base bytes len args s) : 0 < cwc len .wide := by
  have := bc_ge h.lower' .wide
  simp only [cwc]; omega

/-- `eax` the lowest word of wide slot `j`; `edx` changes. -/
theorem lowWord_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27)
    (k : ∀ t, t.mem = s.mem → Keeps [.eax, .edx] s t →
      t.gpr .eax = BitVec.ofNat 32 (sv s.mem base len .wide j % 2 ^ 32) → WP isa (.block is) t Q) :
    WP isa (.block (lowWord (.slot .wide j) ++ is)) s Q := by
  have bl := h.bytes_lt
  have f := slot_fit1 h hj
  rw [cb1] at f
  have bg := bc_ge h.lower' .wide
  unfold lowWord
  rw [List.append_assoc]
  refine ptrTo_ok (r := .eax) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega)
    fun u Ku mu pu => ?_
  have hw := h.ws.of_keeps Ku
  refine wp_movS (readSrc_ptr hw pu (d := 0) (by omega)) fun t U _ => k t (by rw [U.mem, mu])
    (Ku.trans (U.keeps.mono (by decide))) ?_
  rw [U.gpr, Nat.add_zero, mu, ← low_w32 s.mem len j (cwc_pos h), w32, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## A number's lowest bit set -/

theorem val32_or_one (m m' : Mem) (d k : Nat) (hk : 0 < k)
    (low : w32 m' base d = w32 m base d ||| 1)
    (rest : val32 m' base (d + 4) (k - 1) = val32 m base (d + 4) (k - 1)) :
    val32 m' base d k = val32 m base d k ||| 1 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at rest
  rw [val32, val32, rest, low]
  have hl : w32 m base d < 2 ^ 32 := (m.readW _ 32).isLt
  have hl' : w32 m base d ||| 1 < 2 ^ 32 := Nat.or_lt_two_pow hl (by decide)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.add_comm (w32 m base d ||| 1), Nat.testBit_two_pow_mul_add _ hl',
    Nat.testBit_or (w32 m base d + 2 ^ 32 * _) 1, Nat.add_comm (w32 m base d), Nat.testBit_two_pow_mul_add _ hl]
  split
  · rw [Nat.testBit_or]
  · rename_i hi
    have : (1 : Nat).testBit i = false := Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
    simp [this]

/-- A wide slot's lowest bit set; `eax`, `ebx` and `edx` change. -/
theorem setLow_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27)
    (k : ∀ t, In Ex base bytes len args t → Outside base (lo len (.slot .wide j)) 4 s.mem t.mem →
      sv t.mem base len .wide j = sv s.mem base len .wide j ||| 1 → Keeps [.eax, .ebx, .edx] s t →
      WP isa (.block is) t Q) :
    WP isa (.block (setLow (.slot .wide j) ++ is)) s Q := by
  have bl := h.bytes_lt
  have f := slot_fit1 h hj
  rw [cb1] at f
  have bg := bc_ge h.lower' .wide
  have bw := bc_eq_cwc len .wide
  have cp := cwc_pos h
  unfold setLow
  rw [List.append_assoc]
  refine ptrTo_ok (r := .ebx) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega)
    fun u Ku mu pu => ?_
  have hw := h.ws.of_keeps Ku
  refine wp_movS (readSrc_ptr hw pu (d := 0) (by omega)) fun u₁ U₁ _ => ?_
  refine wp_orS rfl fun u₂ U₂ => ?_
  have hw₂ := hw.of_keeps (U₁.keeps.trans U₂.keeps)
  have p₂ : PtrAt u₂ base .ebx (lo len (.slot .wide j)) := by
    rw [PtrAt, U₂.other _ (by decide), U₁.other _ (by decide)]; exact pu
  refine wp_storeS (ea_ptr hw₂ p₂ (d := 0) (by omega)) (ws_write hw₂ (y := _ + 0) (n := 4) (by omega))
    fun t M => ?_
  have K : Keeps [.eax, .ebx, .edx] s t :=
    ((Ku.mono (by decide)).trans ((U₁.keeps.trans U₂.keeps).mono (by decide))).trans (M.keeps _)
  have mt : t.mem = s.mem.writeW (off base (lo len (.slot .wide j))) (s.mem.readW (off base (lo len (.slot .wide j))) 32 ||| 1) := by
    rw [M.mem, U₂.mem, U₁.mem, U₂.gpr, U₁.gpr, mu]; simp only [Nat.add_zero]
  have O : Outside base (lo len (.slot .wide j)) 4 s.mem t.mem := by
    rw [mt]; exact writeW32_outside _ _ _ (by omega)
  refine k t (h.keep K (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega))) O ?_ K
  refine val32_or_one _ _ _ _ cp ?_ ?_
  · rw [mt, w32_write_self, BitVec.toNat_or]; rfl
  · exact O.val32 (.inr (by omega)) (by omega)

/-! ## A mask of `r` bits -/

/-- `eax := 2^r − 1` for `ecx = r`, `1 ≤ r ≤ 32`; `ecx` ends at zero. -/
theorem maskLoop_ok {r : Nat} (hr1 : 1 ≤ r) (hr : r ≤ 32) (hc : s.gpr .ecx = BitVec.ofNat 32 r) :
    WP isa Impl.Ffdh.X86.Candidate.maskLoop s fun t => t.gpr .eax = BitVec.ofNat 32 (2 ^ r - 1) ∧ t.mem = s.mem ∧
      Keeps [.eax, .ecx] s t := by
  unfold Impl.Ffdh.X86.Candidate.maskLoop
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  refine WP.loop (M := isa) (fun n t => ∃ i, n = r - i ∧ i < r ∧ t.gpr .eax = BitVec.ofNat 32 (2 ^ i - 1) ∧
      t.gpr .ecx = BitVec.ofNat 32 (r - i) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx] s t) ?_ r u
    ⟨0, by omega, by omega, U.gpr, by rw [U.other _ (by decide), hc]; rfl, U.mem, U.keeps.mono (by decide)⟩
  rintro n t ⟨i, rfl, hi, ea, ec, mt, K⟩
  refine wp_addS rfl fun t₁ U₁ _ => wp_addS rfl fun t₂ U₂ _ => wp_subZ rfl fun t₃ U₃ z => WP.block_nil ?_
  have pw : 2 ^ (i + 1) ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  have p2 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [Nat.pow_succ]; omega
  have e₃ : t₃.gpr .eax = BitVec.ofNat 32 (2 ^ (i + 1) - 1) := by
    rw [U₃.other _ (by decide), U₂.gpr, U₁.gpr, ea]
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    have hx : 2 ^ i - 1 < 2 ^ 32 := by omega
    have hy : 2 ^ (i + 1) - 1 < 2 ^ 32 := by omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h1, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    have one := Nat.one_le_two_pow (n := i)
    rw [p2] at hy pw ⊢
    generalize 2 ^ i = x at *
    omega
  have c₂ : t₂.gpr .ecx = BitVec.ofNat 32 (r - i) := by
    rw [U₂.other _ (by decide), U₁.other _ (by decide), ec]
  have c₃ : t₃.gpr .ecx = BitVec.ofNat 32 (r - (i + 1)) := by
    rw [U₃.gpr, c₂]
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1]
    omega
  have K₃ : Keeps [.eax, .ecx] s t₃ :=
    K.trans (((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide)))
  have m₃ : t₃.mem = s.mem := by rw [U₃.mem, U₂.mem, U₁.mem, mt]
  have zf : (t₂.gpr .ecx - 1 == 0) = decide (r - i = 1) := by
    rw [c₂, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]
  by_cases last : i + 1 = r
  · refine .inl ⟨?_, by rw [e₃, last], m₃, K₃⟩
    show t₃.zf.map (!·) = some false
    rw [z, zf]
    simp [show r - i = 1 by omega]
  · refine .inr ⟨?_, r - (i + 1), by omega, i + 1, rfl, by omega, e₃, c₃, m₃, K₃⟩
    show t₃.zf.map (!·) = some true
    rw [z, zf]
    simp only [Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not]
    omega

/-! ## A number cut to its low bits -/

theorem testBit_mask32' (r i : Nat) : (2 ^ r - 1 : Nat).testBit i = decide (i < r) := by
  rw [Nat.testBit_two_pow_sub_one]

/-- A number whose word `j` is cut to its low `r` bits and or'ed with its bit `r − 1` if `top`,
and whose words above `j` are zero: the number modulo `2^(32 j + r)`, or'ed with that bit if `top`. -/
theorem val32_cutTop {m m' : Mem} {d w j r : Nat} (top : Bool) (hj : j < w) (hr1 : 1 ≤ r) (hr : r ≤ 32)
    (small : val32 m base d w < 2 ^ (32 * (j + 1)))
    (word : w32 m' base (d + 4 * j) =
      (w32 m base (d + 4 * j) &&& (2 ^ r - 1)) ||| (if top then 2 ^ (r - 1) else 0))
    (other : ∀ i, i < w → i ≠ j → w32 m' base (d + 4 * i) = w32 m base (d + 4 * i)) :
    val32 m' base d w = val32 m base d w % 2 ^ (32 * j + r) ||| (if top then 2 ^ (32 * j + r - 1) else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_mod_two_pow]
  have tb : ∀ {e n : Nat}, (if top then 2 ^ e else 0 : Nat).testBit n = (top && decide (n = e)) := by
    intro e n
    cases top
    · simp
    · simp only [ite_true, Nat.testBit_two_pow, Bool.true_and]; exact decide_eq_decide.mpr ⟨Eq.symm, Eq.symm⟩
  rw [tb]
  by_cases within : i < 32 * w
  · have index : i / 32 < w := by omega
    have bit : i % 32 < 32 := Nat.mod_lt _ (by decide)
    have split : i = 32 * (i / 32) + i % 32 := by omega
    have readNew := VG.Proof.Weierstrass.testBit_val32 m' base d w (i / 32) (i % 32) index bit
    have readOld := VG.Proof.Weierstrass.testBit_val32 m base d w (i / 32) (i % 32) index bit
    rw [← split] at readNew readOld
    rw [readNew]
    by_cases atTop : i / 32 = j
    · have e : d + 4 * (i / 32) = d + 4 * j := by rw [atTop]
      rw [e, word, Nat.testBit_or, Nat.testBit_and, testBit_mask32', tb, ← e, ← readOld]
      have e1 : decide (i % 32 < r) = decide (i < 32 * j + r) := decide_eq_decide.mpr (by omega)
      have e2 : decide (i % 32 = r - 1) = decide (i = 32 * j + r - 1) := decide_eq_decide.mpr (by omega)
      rw [e1, e2, Bool.and_comm]
    · rw [other (i / 32) index atTop, ← readOld]
      have e2 : decide (i = 32 * j + r - 1) = false := decide_eq_false (by omega)
      rw [e2, Bool.and_false, Bool.or_false]
      by_cases below : i / 32 < j
      · have keep : i < 32 * j + r := by omega
        simp only [keep, decide_true, Bool.true_and]
      · have high : 32 * (j + 1) ≤ i := by omega
        have zero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le small
          (Nat.pow_le_pow_right (by decide : 0 < 2) high))
        rw [zero]
        simp only [Bool.and_false]
  · have scale := Nat.pow_le_pow_right (by decide : 0 < 2) (show 32 * w ≤ i by omega)
    have oldZero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m base d w) scale)
    have newZero := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (val32_lt m' base d w) scale)
    rw [oldZero, newZero]
    have e2 : decide (i = 32 * j + r - 1) = false := decide_eq_false (by omega)
    simp only [e2, Bool.and_false, Bool.or_false]

theorem xor_mask {r : Nat} (hr1 : 1 ≤ r) : (2 ^ r - 1) ^^^ (2 ^ (r - 1) - 1) = 2 ^ (r - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
  by_cases h1 : i < r - 1
  · simp [h1, show i < r by omega, show r - 1 ≠ i by omega]
  · by_cases h2 : i = r - 1
    · subst h2; simp [show r - 1 < r by omega]
    · simp [h1, show ¬i < r by omega, Ne.symm h2]

/-- The last block of `cut`: word `wi` of the slot (`edx = 4 wi`) and'ed with the mask in `eax`,
`2^r − 1`, and or'ed with its top bit if `top`. -/
theorem cutTail_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27)
    {r wi : Nat} (hr1 : 1 ≤ r) (hr : r ≤ 32) (hwi : wi < cwc len .wide) (top : Bool)
    (ha : s.gpr .eax = BitVec.ofNat 32 (2 ^ r - 1)) (hd : s.gpr .edx = BitVec.ofNat 32 (4 * wi))
    (k : ∀ t, In Ex base bytes len args t → Outside base (lo len (.slot .wide j) + 4 * wi) 4 s.mem t.mem →
      w32 t.mem base (lo len (.slot .wide j) + 4 * wi) =
        (w32 s.mem base (lo len (.slot .wide j) + 4 * wi) &&& (2 ^ r - 1)) |||
          (if top then 2 ^ (r - 1) else 0) →
      Keeps [.eax, .ebx, .ecx, .ebp] s t → WP isa (.block is) t Q) :
    WP isa (.block ((ptrTo (.slot .wide j) .ebx .ecx ++ ([.alu .add .ebx (.reg .edx), .mov .ecx (.mem (at_ .ebx 0)),
      .alu .and .ecx (.reg .eax)] : List Instr) ++
      (if top then [.mov .ebp (.reg .eax), .shift .shr .ebp 1, .alu .xor .eax (.reg .ebp), .alu .or .ecx (.reg .eax)]
        else []) ++ ([.store (at_ .ebx 0) .ecx] : List Instr)) ++ is)) s Q := by
  have bl := h.bytes_lt
  have f := slot_fit1 h hj
  rw [cb1] at f
  have bw := bc_eq_cwc len .wide
  have pm : 2 ^ r - 1 < 2 ^ 32 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; have := Nat.one_le_two_pow (n := r); omega
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ptrTo_ok (r := .ebx) (t := .ecx) (by decide) (by decide) h.edi h.width h.upper' (by omega)
    fun u Ku mu pu => ?_
  have hw := h.ws.of_keeps Ku
  refine wp_addS rfl fun u₁ U₁ _ => ?_
  have p₁ : PtrAt u₁ base .ebx (lo len (.slot .wide j) + 4 * wi) := by
    rw [PtrAt, U₁.gpr, ptr_add pu, Ku.1 .edx (by decide), hd, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4 * wi) (by omega)]
  have hw₁ := hw.of_keeps U₁.keeps
  refine wp_movS (readSrc_ptr hw₁ p₁ (d := 0) (by omega)) fun u₂ U₂ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun u₃ U₃ => ?_
  have ea₃ : u₃.gpr .eax = BitVec.ofNat 32 (2 ^ r - 1) := by
    rw [U₃.other _ (by decide), U₂.other _ (by decide), U₁.other _ (by decide), Ku.1 .eax (by decide), ha]
  have ec₃ : u₃.gpr .ecx = s.mem.readW (off base (lo len (.slot .wide j) + 4 * wi)) 32 &&& BitVec.ofNat 32 (2 ^ r - 1) := by
    rw [U₃.gpr]; simp only [↓reduceIte]
    rw [U₂.gpr, U₁.mem, mu, Nat.add_zero, U₂.other _ (by decide), U₁.other _ (by decide), Ku.1 .eax (by decide), ha]
  have p₃ : PtrAt u₃ base .ebx (lo len (.slot .wide j) + 4 * wi) := by
    rw [PtrAt, U₃.other _ (by decide), U₂.other _ (by decide)]; exact p₁
  have m₃ : u₃.mem = s.mem := by rw [U₃.mem, U₂.mem, U₁.mem, mu]
  have K₃ : Keeps [.eax, .ebx, .ecx, .ebp] s u₃ :=
    (Ku.mono (by decide)).trans ((U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans
      (U₃.keeps.mono (by decide))))
  -- The rest, from a state with the new word in `ecx`.
  have fin : ∀ v : State, Keeps [.eax, .ebx, .ecx, .ebp] s v → v.mem = s.mem →
      PtrAt v base .ebx (lo len (.slot .wide j) + 4 * wi) →
      (v.gpr .ecx).toNat = (w32 s.mem base (lo len (.slot .wide j) + 4 * wi) &&& (2 ^ r - 1)) |||
        (if top then 2 ^ (r - 1) else 0) →
      WP isa (.block (.store (at_ .ebx 0) .ecx :: is)) v Q := by
    intro v Kv mv pv ev
    have hwv := h.ws.of_keeps Kv
    refine wp_storeS (ea_ptr hwv pv (d := 0) (by omega)) (ws_write hwv (y := _ + 0) (n := 4) (by omega))
      fun t M => ?_
    have mt : t.mem = s.mem.writeW (off base (lo len (.slot .wide j) + 4 * wi)) (v.gpr .ecx) := by
      rw [M.mem, mv, Nat.add_zero]
    have O : Outside base (lo len (.slot .wide j) + 4 * wi) 4 s.mem t.mem := by
      rw [mt]; exact writeW32_outside _ _ _ (by omega)
    have K : Keeps [.eax, .ebx, .ecx, .ebp] s t := Kv.trans (M.keeps _)
    refine k t (h.keep K (by decide) (by decide) (O.mono (Nat.zero_le _) (by omega))) O ?_ K
    rw [mt, w32_write_self, ev]
  cases top
  · refine fin u₃ K₃ m₃ p₃ ?_
    rw [ec₃, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pm]
    simp
  · refine wp_movS rfl fun u₄ U₄ _ => wp_shr (by decide) fun u₅ U₅ _ => ?_
    refine wp_logicS (.inr rfl) rfl fun u₆ U₆ => wp_orS rfl fun u₇ U₇ => ?_
    have K₇ : Keeps [.eax, .ebx, .ecx, .ebp] s u₇ :=
      K₃.trans ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans
        ((U₆.keeps.mono (by decide)).trans (U₇.keeps.mono (by decide)))))
    refine fin u₇ K₇ (by rw [U₇.mem, U₆.mem, U₅.mem, U₄.mem, m₃]) (by
      rw [PtrAt, U₇.other _ (by decide), U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide)]
      exact p₃) ?_
    rw [U₇.gpr, U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), ec₃, U₆.gpr]
    simp only [reduceCtorEq, ↓reduceIte]
    rw [U₅.gpr, U₄.gpr, U₅.other _ (by decide), U₄.other _ (by decide), ea₃]
    rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt pm, Nat.shiftRight_eq_div_pow]
    have half : (2 ^ r - 1) / 2 ^ 1 = 2 ^ (r - 1) - 1 := by
      obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
      rw [Nat.pow_succ, Nat.add_sub_cancel]
      have := Nat.one_le_two_pow (n := q)
      omega
    rw [half, xor_mask hr1]

/-- `cut`'s first block: `ecx = r = (k − 1) mod 32 + 1` and `edx = 4 ⌊(k − 1) / 32⌋` for `k` in the
header. -/
theorem cutHead_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {k : Nat}
    (hk : w32 s.mem base kOff = k) (hk1 : 1 ≤ k)
    (kk : ∀ t, t.mem = s.mem → Keeps [.ecx, .edx] s t → t.gpr .ecx = BitVec.ofNat 32 ((k - 1) % 32 + 1) →
      t.gpr .edx = BitVec.ofNat 32 (4 * ((k - 1) / 32)) → WP isa (.block is) t Q) :
    WP isa (.block (([.mov .ecx (.mem (sc kOff)), .alu .sub .ecx (.imm 1), .mov .edx (.reg .ecx), .shift .shr .edx 5,
      .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .and .ecx (.imm 31),
      .alu .add .ecx (.imm 1)] : List Instr) ++ is)) s Q := by
  have kl : k < 2 ^ 32 := by rw [← hk]; exact (s.mem.readW _ 32).isLt
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (hdr_read h (d := kOff) ⟨.inr ⟨by decide, by decide⟩, by decide⟩) fun u₁ U₁ _ => ?_
  refine wp_subS rfl fun u₂ U₂ _ => wp_mov fun u₃ U₃ => wp_shr (by decide) fun u₄ U₄ _ => ?_
  refine wp_addS rfl fun u₅ U₅ _ => wp_addS rfl fun u₆ U₆ _ => wp_logicS (.inl rfl) rfl fun u₇ U₇ => ?_
  refine wp_addS rfl fun u₈ U₈ _ => kk u₈ (by rw [U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem])
    ?_ ?_ ?_
  · exact ((U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans ((U₃.keeps.mono (by decide)).trans
      ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans ((U₆.keeps.mono (by decide)).trans
        ((U₇.keeps.mono (by decide)).trans (U₈.keeps.mono (by decide)))))))))
  · have e₂ : u₂.gpr .ecx = BitVec.ofNat 32 (k - 1) := by
      rw [U₂.gpr, U₁.gpr, hk, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hk1]
    rw [U₈.gpr, U₇.gpr]; simp only [↓reduceIte]
    rw [U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), e₂]
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    have h31 : (31 : BitVec 32).toNat = 31 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h1, h31,
      Nat.mod_eq_of_lt (a := k - 1) (by omega), show (31 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  · have e₂ : u₂.gpr .ecx = BitVec.ofNat 32 (k - 1) := by
      rw [U₂.gpr, U₁.gpr, hk, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat hk1]
    rw [U₈.other _ (by decide), U₇.other _ (by decide), U₆.gpr, U₅.gpr, U₄.gpr, U₃.gpr, e₂]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega

/-- A wide slot cut to its low `k` bits (`k` in the header), its bit `k − 1` set if `top`; the
words above the cut must be zero. -/
theorem cut_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) (top : Bool) {k : Nat}
    (hk : w32 s.mem base kOff = k) (hk1 : 1 ≤ k) (hkw : k ≤ 32 * cwc len .wide)
    (small : sv s.mem base len .wide j < 2 ^ (32 * ((k - 1) / 32 + 1))) :
    WP isa (cut (.slot .wide j) top) s fun t => In Ex base bytes len args t ∧
      Outside base (lo len (.slot .wide j)) (bc len .wide) s.mem t.mem ∧
      sv t.mem base len .wide j = sv s.mem base len .wide j % 2 ^ k ||| (if top then 2 ^ (k - 1) else 0) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have bl := h.bytes_lt
  have f := slot_fit1 h hj
  rw [cb1] at f
  have bw := bc_eq_cwc len .wide
  unfold cut
  refine WP.seq (cutHead_ok (is := []) h hk hk1 fun u mu Ku cu du => WP.block_nil ?_)
  refine WP.seq (WP.mono (VG.Proof.Ffdh.X86.Cand.maskLoop_ok (r := (k - 1) % 32 + 1) (by omega) (by omega) cu)
    fun v ⟨av, mv, Kv⟩ => ?_)
  have dv : v.gpr .edx = BitVec.ofNat 32 (4 * ((k - 1) / 32)) := by rw [Kv.1 _ (by decide), du]
  have hv : In Ex base bytes len args v :=
    h.regs ((Ku.mono (by decide)).trans (Kv.mono (by decide)) : Keeps [.eax, .ecx, .edx] s v) (by rw [mv, mu])
  rw [show ptrTo (.slot .wide j) .ebx .ecx ++ [.alu .add .ebx (.reg .edx), .mov .ecx (.mem (at_ .ebx 0)),
      .alu .and .ecx (.reg .eax)] ++
      (if top then [.mov .ebp (.reg .eax), .shift .shr .ebp 1, .alu .xor .eax (.reg .ebp), .alu .or .ecx (.reg .eax)]
        else []) ++ [.store (at_ .ebx 0) .ecx] = (ptrTo (.slot .wide j) .ebx .ecx ++ [.alu .add .ebx (.reg .edx),
      .mov .ecx (.mem (at_ .ebx 0)), .alu .and .ecx (.reg .eax)] ++
      (if top then [.mov .ebp (.reg .eax), .shift .shr .ebp 1, .alu .xor .eax (.reg .ebp), .alu .or .ecx (.reg .eax)]
        else []) ++ [.store (at_ .ebx 0) .ecx]) ++ [] from (List.append_nil _).symm]
  have wi : (k - 1) / 32 < cwc len .wide := by omega
  refine cutTail_ok hv hj (by omega) (by omega) wi top av dv fun t ht O W K => WP.block_nil ⟨ht, ?_, ?_, ?_⟩
  · have mvs : v.mem = s.mem := by rw [mv, mu]
    rw [mvs] at O; exact O.mono (by omega) (by omega)
  · have mvs : v.mem = s.mem := by rw [mv, mu]
    rw [mvs] at O W
    show val32 _ _ _ _ = _
    have e : 32 * ((k - 1) / 32) + ((k - 1) % 32 + 1) = k := by omega
    have e' : (k - 1) % 32 + 1 - 1 = (k - 1) % 32 := by omega
    have r := val32_cutTop (m := s.mem) (m' := t.mem) (d := lo len (.slot .wide j)) (w := cwc len .wide)
      (j := (k - 1) / 32) (r := (k - 1) % 32 + 1) top wi (by omega) (by omega) small W
      (fun i hi hne => O.w32 (by omega) (by omega))
    rw [e] at r
    rw [r]
  · exact ((Ku.mono (by decide)).trans (Kv.mono (by decide))).trans (K.mono (by decide))

/-- `and d, imm`, and ZF. -/
theorem wp_andZ {is : List Instr} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ t, Upd s t d (s.gpr d &&& v) → t.zf = some (s.gpr d &&& v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  cons (s' := (arithFlags s (s.gpr d &&& v) false false).setReg d (s.gpr d &&& v)) rfl
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem and_one_zero (x : Nat) (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x &&& 1 == 0) = decide (x % 2 = 0) := by
  have e : BitVec.ofNat 32 x &&& 1 = BitVec.ofNat 32 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx,
      show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.mod_eq_of_lt (a := x % 2) (by omega)]
  rw [e, ofNat_beq_zero (by omega)]

end VG.Proof.Ffdh.X86.Cand
