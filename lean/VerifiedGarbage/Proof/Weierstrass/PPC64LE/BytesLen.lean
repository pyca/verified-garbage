module

public import VerifiedGarbage.Impl.Weierstrass.PPC64LE
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Short Weierstrass curves on PPC64LE: numbers as big-endian bytes

`loadBytes len n o src` reads the `len` bytes at `src`, big-endian, into
`[o]` (`loadBytes_ok`), its whole words by `ldbrx` (which is `byteRev64` of
a load), a top word of fewer bytes the first eight reversed and shifted
right, and the words past `len` zero; `shrWords n o sh` shifts `[o]` right
by `sh` bits in place (`shrWords_ok`); and `storeBytes len n dst d a`
writes `[a]` masked with `r10` to the `len` bytes at `dst + d`
(`storeBytes_ok`), its whole words by `stdbrx`, a top word of fewer bytes a
byte at a time. As on AArch64 (`Proof/Weierstrass/AArch64/BytesLen.lean`),
from the same facts about the encodings (`Proof/Weierstrass/BytesLen.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE
  VG.Proof.Weierstrass

theorem rev64_eq (w : BitVec 64) : rev64 w = byteRev64 w := rfl

/-- `ldbrx r8, src, r9` from `r9 = e`. -/
theorem wp_ldRev {s : State} {src : Reg} (hsrc0 : src ≠ .r0) (hsrc9 : src ≠ .r9) {e : Nat} (he : e < 2 ^ 15)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 e) 8) {is : List Instr} {Q : State → Prop}
    (k : WP isa (.block is) ((s.write .r9 (BitVec.ofNat 64 e)).write .r8
      (byteRev64 (s.mem.readW (s.gpr src + BitVec.ofNat 64 e) 64))) Q) :
    WP isa (.block (.li .r9 e :: .loadRev .d .r8 src .r9 :: is)) s Q := by
  have ha : (s.write .r9 (BitVec.ofNat 64 e)).gpr src + (s.write .r9 (BitVec.ofNat 64 e)).gpr .r9 =
      s.gpr src + BitVec.ofNat 64 e := by simp only [write_gpr, hsrc9, ite_false, ite_true]
  refine wp_step (exec_li he) ?_
  refine wp_step (exec_loadRev_d hsrc0 (by rw [ha, write_rd, write_wr]; exact hr)) ?_
  rw [ha, write_mem]; exact k

/-- `stdbrx r4, dst, r6` from `r6 = e`. -/
theorem wp_stRev {s : State} {dst : Reg} (hdst0 : dst ≠ .r0) (hdst6 : dst ≠ .r6) {e : Nat} (he : e < 2 ^ 15)
    (hw : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 e) 8) {is : List Instr} {Q : State → Prop}
    (k : WP isa (.block is) { s.write .r6 (BitVec.ofNat 64 e) with
      mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 e) (byteRev64 (s.gpr .r4)) } Q) :
    WP isa (.block (.li .r6 e :: .storeRev .d .r4 dst .r6 :: is)) s Q := by
  have ha : (s.write .r6 (BitVec.ofNat 64 e)).gpr dst + (s.write .r6 (BitVec.ofNat 64 e)).gpr .r6 =
      s.gpr dst + BitVec.ofNat 64 e := by simp only [write_gpr, hdst6, ite_false, ite_true]
  refine wp_step (exec_li he) ?_
  refine wp_step (exec_storeRev_d hdst0 (by rw [ha, write_wr]; exact hw)) ?_
  rw [ha, write_mem]; exact k

/-! ## Loads -/

/-- One word of `loadBytes`. -/
def ldStepL (len o : Nat) (src : Reg) (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ len then
    [.li .r9 (len - 8 * (j + 1)), .loadRev .d .r8 src .r9, .store .d .r8 wb (o + 8 * j)]
  else if 8 * j < len then
    [.li .r9 0, .loadRev .d .r8 src .r9, .lsr .d .r8 .r8 (8 * (8 * (j + 1) - len)),
      .store .d .r8 wb (o + 8 * j)]
  else [.li .r8 0, .store .d .r8 wb (o + 8 * j)]

theorem loadBytes_eq (len n o : Nat) (src : Reg) :
    loadBytes len n o src = (List.range n).flatMap (ldStepL len o src) := rfl

/-- The word `j` that `loadBytes` reads from `p`. -/
def ldWord (m : Mem) (p : Addr) (len j : Nat) : BitVec 64 :=
  if 8 * (j + 1) ≤ len then byteRev64 (m.readW (p + BitVec.ofNat 64 (len - 8 * (j + 1))) 64)
  else byteRev64 (m.readW p 64) >>> (8 * (8 * (j + 1) - len))

/-- What the loads change. -/
abbrev ldClob : List Reg := [.r8, .r9]

/-- Word `k` of `loadBytes`. -/
theorem ldStepL_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {len o k : Nat} {src : Reg} (hsrc0 : src ≠ .r0) (hsrc9 : src ≠ .r9) (ho : o + 8 * k + 8 ≤ size)
    (ho4 : o % 4 = 0) (h8 : 8 ≤ len) (hl : len < 2 ^ 15)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8) :
    WP isa (.block (ldStepL len o src k)) s fun s' =>
      s'.mem = s.mem.writeW (off base (o + 8 * k)) (ldWord s.mem (s.gpr src) len k) ∧
      Kp ldClob s s' := by
  by_cases hc : 8 * (k + 1) ≤ len
  · rw [ldStepL, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    refine wp_ldRev hsrc0 hsrc9 (by omega) (hr _ (by omega)) ?_
    refine wp_step (std0_ok ((hs.write _ _).write _ _) ((h3.write _).write _) (by decide) (by omega)
      (by omega)) (WP.block_nil ⟨?_, ?_⟩)
    · simp only [write_mem, write_gpr, ite_true, ldWord, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    · exact ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _)
  · by_cases hz : 8 * k < len
    · rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_left_of_eq_true _ _ (eq_true hz)]
      refine wp_ldRev hsrc0 hsrc9 (by decide) (hr _ (by omega)) ?_
      refine wp_step (exec_lsr_d (by omega)) ?_
      refine wp_step (std0_ok (((hs.write _ _).write _ _).write _ _) (((h3.write _).write _).write _)
        (by decide) (by omega) (by omega)) (WP.block_nil ⟨?_, ?_⟩)
      · simp only [write_mem, write_gpr, ite_true, ldWord, ite_eq_right_of_eq_false _ _ (eq_false hc),
          BitVec.add_zero]
      · exact (((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
          (Kp.write _ _ (by decide))).trans (Kp.store _ _ _)
    · rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hz)]
      refine wp_step (exec_li (by decide)) ?_
      refine wp_step (std0_ok (hs.write _ _) (h3.write _) (by decide) (by omega) (by omega))
        (WP.block_nil ⟨?_, ?_⟩)
      · simp only [write_mem, write_gpr, ite_true, ldWord, ite_eq_right_of_eq_false _ _ (eq_false hc)]
        rw [BitVec.ushiftRight_eq_zero (by omega)]
      · exact (Kp.write _ _ (by decide)).trans (Kp.store _ _ _)

theorem ldStepsL_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {len n o : Nat} {src : Reg} (hsrc0 : src ≠ .r0) (hsrc8 : src ≠ .r8) (hsrc9 : src ≠ .r9)
    (ho : o + 8 * n ≤ size) (ho4 : o % 4 = 0) (h8 : 8 ≤ len) (hl : len < 2 ^ 15)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, len⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (ldStepL len o src))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = ldWord s.mem (s.gpr src) len j) ∧
      Kp ldClob s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine wp_append (WP.mono (ldStepsL_ok hs h3 hsrc0 hsrc8 hsrc9 ho ho4 h8 hl hr hd k (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simp [hsrc8, hsrc9])
    have hkeep : ∀ d, d + 8 ≤ len → s₁.mem.readW (s.gpr src + BitVec.ofNat 64 d) 64 =
        s.mem.readW (s.gpr src + BitVec.ofNat 64 d) 64 := fun d hd' =>
      readW_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine WP.mono (ldStepL_ok (k₁.ws hs) (k₁.at h3) (k := k) hsrc0 hsrc9 (by omega) ho4 h8 hl
      (fun d hd' => by rw [k₁.rd, k₁.wr, hp₁]; exact hr d hd')) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self, hp₁, ldWord, ldWord]
      split
      · rw [hkeep _ (by omega)]
      · rw [show s.gpr src = s.gpr src + BitVec.ofNat 64 0 from (BitVec.add_zero _).symm,
          hkeep _ (by omega)]

/-- `[o] = ` the `len` bytes at `src`, big-endian (`8 (n - 1) ≤ len ≤ 8 n`,
`8 ≤ len`). -/
theorem loadBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {len n o : Nat} {src : Reg} (hsrc0 : src ≠ .r0) (hsrc8 : src ≠ .r8) (hsrc9 : src ≠ .r9)
    (ho : o + 8 * n ≤ size) (ho4 : o % 4 = 0) (h8 : 8 ≤ len) (hlo : 8 * n ≤ len + 8) (hhi : len ≤ 8 * n)
    (hl : len < 2 ^ 15)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, len⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBytes len n o src)) s fun s' =>
      wordsVal s'.mem base o n = Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr src) len) ∧
      Kp ldClob s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBytes_eq]
  refine WP.mono (ldStepsL_ok hs h3 hsrc0 hsrc8 hsrc9 ho ho4 h8 hl hr hd n (Nat.le_refl _))
    fun s' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact wordsVal_eq_ofBytes_len _ _ _ _ o n' len (by omega) hhi fun j hj => e j hj

/-! ## Shifting right in place -/

/-- One word of `shrWords`. -/
def shrStep (n o sh j : Nat) : List Instr :=
  ([.load .d .r4 wb (o + 8 * j), .lsr .d .r4 .r4 sh] : List Instr) ++
  ((if j + 1 < n then
    [.load .d .r8 wb (o + 8 * (j + 1)), .lsl .r8 .r8 (64 - sh), .logic .or .r4 .r4 .r8]
  else []) : List Instr) ++
  ([.store .d .r4 wb (o + 8 * j)] : List Instr)

theorem shrWords_eq (n o sh : Nat) : shrWords n o sh = (List.range n).flatMap (shrStep n o sh) := rfl

/-- Word `j` of `[o]` shifted right by `sh`, from the words of `m`. -/
def shrWord (m : Mem) (base : Addr) (n o sh j : Nat) : BitVec 64 :=
  if j + 1 < n then (word m base (o + 8 * j) >>> sh) |||
    (word m base (o + 8 * (j + 1)) &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh
  else word m base (o + 8 * j) >>> sh

/-- The low `sh` bits of a word rotated to the top are it shifted left by
`64 - sh`. -/
theorem shl_eq_rotr (w : BitVec 64) {sh : Nat} (h0 : 0 < sh) (h64 : sh < 64) :
    w <<< (64 - sh) = (w &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_and,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.mod_eq_of_lt h64, hi, decide_true, Bool.true_and]
  by_cases h : i < 64 - sh
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, ite_true]
    simp only [show ¬ sh + i < sh by omega, decide_false, Bool.and_false]
  · simp only [h, decide_false, Bool.not_false, Bool.true_and, ite_false]
    rw [show i - (64 - sh) = i - (64 - sh) from rfl]
    simp only [show i - (64 - sh) < sh by omega, decide_true, Bool.and_true, show i - (64 - sh) < 64 by omega]

/-- What the shifts and the stores change. -/
abbrev shrClob : List Reg := [.r4, .r8]

/-- Word `k` of `shrWords`, from words `k` and `k + 1` of `m`. -/
theorem shrStep_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {n o sh k : Nat} (ho : o + 8 * n ≤ size) (ho4 : o % 4 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) (hk : k < n)
    {m : Mem} (hm : ∀ j, k ≤ j → j < n → word s.mem base (o + 8 * j) = word m base (o + 8 * j)) :
    WP isa (.block (shrStep n o sh k)) s fun s' =>
      s'.mem = s.mem.writeW (off base (o + 8 * k)) (shrWord m base n o sh k) ∧ Kp shrClob s s' := by
  rw [shrStep, List.append_assoc]
  refine wp_step (ld0_ok hs h3 (by decide) (by omega) (by omega)) ?_
  refine wp_step (exec_lsr_d hsh') ?_
  by_cases hc : k + 1 < n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    refine wp_step (ld0_ok ((hs.write _ _).write _ _) ((h3.write _).write _) (by decide) (by omega)
      (by omega)) ?_
    refine wp_step (exec_lsl (by omega)) ?_
    refine wp_step exec_logic ?_
    refine wp_step (std0_ok (((((hs.write _ _).write _ _).write _ _).write _ _).write _ _)
      (((((h3.write _).write _).write _).write _).write _) (by decide) (by omega) (by omega))
      (WP.block_nil ⟨?_, ?_⟩)
    · simp only [write_mem, write_gpr, ite_true, reduceCtorEq, ite_false, shrWord,
        ite_eq_left_of_eq_true _ _ (eq_true hc)]
      rw [hm k (Nat.le_refl _) hk, hm (k + 1) (by omega) hc, shl_eq_rotr _ (by omega) hsh']
    · exact (((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
        (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _)
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), List.nil_append]
    refine wp_step (std0_ok ((hs.write _ _).write _ _) ((h3.write _).write _) (by decide) (by omega)
      (by omega)) (WP.block_nil ⟨?_, ?_⟩)
    · simp only [write_mem, write_gpr, ite_true, shrWord, ite_eq_right_of_eq_false _ _ (eq_false hc)]
      rw [hm k (Nat.le_refl _) hk]
    · exact ((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans (Kp.store _ _ _)

theorem shrSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {n o sh : Nat} (ho : o + 8 * n ≤ size) (ho4 : o % 4 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (shrStep n o sh))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = shrWord s.mem base n o sh j) ∧
      Kp shrClob s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _, Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine wp_append (WP.mono (shrSteps_ok hs h3 ho ho4 hsh hsh' k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    refine WP.mono (shrStep_ok (k₁.ws hs) (k₁.at h3) ho ho4 hsh hsh' (k := k) (by omega) (m := s.mem)
      fun j hj _ => O₁.word (by omega) (by omega)) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self]

/-- `[o] = [o] >> sh`, `n` words, for `0 < sh < 64`. -/
theorem shrWords_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {n o sh : Nat} (ho : o + 8 * n ≤ size) (ho4 : o % 4 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) :
    WP isa (.block (shrWords n o sh)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base o n >>> sh ∧
      Kp shrClob s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [shrWords_eq]
  exact WP.mono (shrSteps_ok hs h3 ho ho4 hsh hsh' n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨wordsVal_shr _ _ _ _ _ _ (by omega) hsh' fun j hj => e j hj, k, O⟩

/-! ## Stores -/

/-- A whole word of `storeBytes`. -/
def stStepW (len : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.load .d .r4 wb (a + 8 * j), .logic .and .r4 .r4 .r10, .li .r6 (d + (len - 8 * (j + 1))),
    .storeRev .d .r4 dst .r6]

/-- Byte `i` of a top word of `t` bytes in `r4`. -/
def stByte (t : Nat) (dst : Reg) (d i : Nat) : List Instr :=
  if t - 1 - i = 0 then [.stb .r4 dst (d + i)]
  else [.lsr .d .r5 .r4 (8 * (t - 1 - i)), .stb .r5 dst (d + i)]

/-- A top word of `t` bytes. -/
def stTop (t : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.load .d .r4 wb (a + 8 * j), .logic .and .r4 .r4 .r10] ++ (List.range t).flatMap (stByte t dst d)

theorem storeBytes_eq (len n : Nat) (dst : Reg) (d a : Nat) :
    storeBytes len n dst d a = (List.range n).flatMap fun j =>
      if 8 * (j + 1) ≤ len then stStepW len dst d a j
      else if 8 * j < len then stTop (len - 8 * j) dst d a j else [] := rfl

/-- What the stores change. -/
abbrev stClob : List Reg := [.r4, .r5, .r6]

/-- One whole word: the byte reversal of the masked word `j` to
`dst + d + len - 8 (j + 1)`. -/
theorem stStepW_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {len d a j : Nat} {dst : Reg} (hdst0 : dst ≠ .r0) (hdst4 : dst ≠ .r4) (hdst6 : dst ≠ .r6)
    (ha : a + 8 * j + 8 ≤ size) (ha4 : a % 4 = 0) (hj : 8 * (j + 1) ≤ len) (hdl : d + len < 2 ^ 15)
    (hw : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1))) 8) :
    WP isa (.block (stStepW len dst d a j)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1)))
        (byteRev64 (word s.mem base (a + 8 * j) &&& s.gpr .r10)) ∧ Kp stClob s s' := by
  have hq : s.gpr dst + BitVec.ofNat 64 (d + (len - 8 * (j + 1))) =
      s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1)) := (Offset.add_add _ _ _).symm
  rw [stStepW]
  refine wp_step (ld0_ok hs h3 (by decide) (by omega) (by omega)) ?_
  refine wp_step exec_logic ?_
  have g : ((s.write .r4 (word s.mem base (a + 8 * j))).write .r4
      ((s.write .r4 (word s.mem base (a + 8 * j))).gpr .r4 &&&
        (s.write .r4 (word s.mem base (a + 8 * j))).gpr .r10)).gpr dst = s.gpr dst := by
    simp only [write_gpr, hdst4, ite_false]
  refine wp_stRev hdst0 hdst6 (by omega) (by rw [g, write_wr, write_wr, hq]; exact hw) (WP.block_nil ⟨?_, ?_⟩)
  · simp only [write_mem, write_gpr, ite_true, reduceCtorEq, ite_false, hdst4]
    rw [hq]
  · exact (((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.store _ _ _)

theorem stSteps_wordsL {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {len d a : Nat} {dst : Reg} (hdst0 : dst ≠ .r0) (hdst4 : dst ≠ .r4) (hdst5 : dst ≠ .r5) (hdst6 : dst ≠ .r6)
    {c : Bool} (hc : s.gpr .r10 = (if c then BitVec.allOnes 64 else 0))
    {k : Nat} (ha : a + 8 * k ≤ size) (ha4 : a % 4 = 0) (hlen : 8 * k ≤ len) (hdl : d + len < 2 ^ 15)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * k⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, len⟩) : ∀ k', k' ≤ k →
    WP isa (.block ((List.range k').flatMap (stStepW len dst d a))) s fun s' =>
      (∀ j < k', s'.mem.readW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1))) 64 =
        byteRev64 (word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0))) ∧
      Kp stClob s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) (len - 8 * k') (8 * k') s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _, Outside.refl _ _ _ _⟩
  | k' + 1, hk => by
    have hn := hs.nowrap
    have hl : len ≤ 2 ^ 64 := by omega
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine wp_append (WP.mono (stSteps_wordsL hs h3 hdst0 hdst4 hdst5 hdst6 hc ha ha4 hlen hdl hw hd k'
      (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simp [hdst4, hdst5, hdst6])
    have hc₁ : s₁.gpr .r10 = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.g, hc]
    have hword : word s₁.mem base (a + 8 * k') = word s.mem base (a + 8 * k') := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k')) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k')) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine WP.mono (stStepW_ok (k₁.ws hs) (k₁.at h3) hdst0 hdst4 hdst6 (j := k') (by omega) ha4 (by omega) hdl
      (by rw [k₁.wr, hq₁]; exact hw _ _ (by omega))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [hq₁, hc₁, hword] at m₂
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) (len - 8 * (k' + 1)) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k' with h | h
    · rw [m₂, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), e₁ j h]
    · obtain rfl : j = k' := by omega
      rw [m₂, Mem.readW_writeW_self64]

theorem setWidth8_shr (v : BitVec 64) (n : Nat) :
    ((v >>> n).setWidth 8 : BitVec 8) = BitVec.ofNat 8 (v.toNat >>> n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]

theorem stByte_ok {s : State} {v : BitVec 64} (ha : s.gpr .r4 = v) {dst : Reg} (hdst0 : dst ≠ .r0)
    (hdst5 : dst ≠ .r5) {t d i : Nat} (hi : i < t) (ht : t ≤ 8) (hd : d + i < 2 ^ 15)
    (hw : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stByte t dst d i)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧ Kp [.r5] s s' := by
  have hq : s.gpr dst + BitVec.ofNat 64 (d + i) = s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i :=
    (Offset.add_add _ _ _).symm
  by_cases h0 : t - 1 - i = 0
  · rw [stByte, ite_eq_left_of_eq_true _ _ (eq_true h0)]
    refine wp_step (exec_stb hdst0 hd (by rw [hq]; exact hw)) (WP.block_nil ⟨?_, Kp.store _ _ _⟩)
    rw [hq, ha, h0, Nat.mul_zero, ← setWidth8_shr, BitVec.ushiftRight_zero]; rfl
  · rw [stByte, ite_eq_right_of_eq_false _ _ (eq_false h0)]
    refine wp_step (exec_lsr_d (by omega)) ?_
    have g : (s.write .r5 (s.gpr .r4 >>> (8 * (t - 1 - i)))).gpr dst = s.gpr dst := by
      simp only [write_gpr, hdst5, ite_false]
    refine wp_step (exec_stb hdst0 hd (by rw [g, write_wr, hq]; exact hw))
      (WP.block_nil ⟨?_, (Kp.write _ _ (by decide)).trans (Kp.store _ _ _)⟩)
    simp only [write_mem, write_gpr, ite_true, hdst5, ite_false]
    rw [hq, ha, ← setWidth8_shr]; rfl

theorem stBytes_ok {s : State} {v : BitVec 64} (ha : s.gpr .r4 = v) {dst : Reg} (hdst0 : dst ≠ .r0)
    (hdst4 : dst ≠ .r4) (hdst5 : dst ≠ .r5)
    {t d : Nat} (ht : t ≤ 8) (hdt : d + t ≤ 2 ^ 15) (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + t ≤ 2 ^ 64)
    (hw : ∀ i < t, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) : ∀ i', i' ≤ t →
    WP isa (.block ((List.range i').flatMap (stByte t dst d))) s fun s' =>
      (∀ i < i', s'.mem (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧
      Kp [.r5] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 i' s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Kp.refl _ _, Outside.refl _ _ _ _⟩
  | i' + 1, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine wp_append (WP.mono (stBytes_ok ha hdst0 hdst4 hdst5 ht hdt hq hw i' (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst5)
    refine WP.mono (stByte_ok (s := s₁) (v := v) (by rw [k₁.g, ha]) hdst0 hdst5 (t := t) (d := d)
      (i := i') (by omega) ht (by omega) (by rw [k₁.wr, hq₁]; exact hw i' (by omega))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [hq₁] at m₂
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) i' 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega)
    refine ⟨fun i hi' => ?_, k₁.trans k₂, (O₁.mono (Nat.le_refl _) (by omega)).trans
      (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge i i' with h | h
    · rw [O₂ _ (by rw [ofs_off0 _ (by omega)]; omega), e₁ i h]
    · obtain rfl : i = i' := by omega
      rw [m₂, writeW8_self]

theorem stTop_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {dst : Reg} (hdst0 : dst ≠ .r0) (hdst4 : dst ≠ .r4) (hdst5 : dst ≠ .r5) {c : Bool}
    (hc : s.gpr .r10 = (if c then BitVec.allOnes 64 else 0))
    {t d a j : Nat} (ha : a + 8 * (j + 1) ≤ size) (ha4 : a % 4 = 0) (ht : t ≤ 8) (hdt : d + t ≤ 2 ^ 15)
    (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + t ≤ 2 ^ 64)
    (hw : ∀ i < t, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stTop t dst d a j)) s fun s' =>
      (∀ i < t, s'.mem (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 ((word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0)).toNat >>>
          (8 * (t - 1 - i)))) ∧
      Kp stClob s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 t s.mem s'.mem := by
  rw [stTop, List.cons_append, List.cons_append]
  refine wp_step (ld0_ok hs h3 (by decide) (by omega) (by omega)) ?_
  refine wp_step exec_logic ?_
  generalize hs₂ : (s.write .r4 (word s.mem base (a + 8 * j))).write .r4
    ((s.write .r4 (word s.mem base (a + 8 * j))).gpr .r4 &&& (s.write .r4 (word s.mem base (a + 8 * j))).gpr .r10)
    = s₂
  have K₂ : Kp [.r4] s s₂ := by rw [← hs₂]; exact (Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))
  have m₂ : s₂.mem = s.mem := by rw [← hs₂]; rfl
  have hq₂ : s₂.gpr dst = s.gpr dst := K₂.gpr _ (by simpa using hdst4)
  have ha₂ : s₂.gpr .r4 = word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0) := by
    rw [← hs₂]; simp only [write_gpr, ite_true, reduceCtorEq, ite_false, hc]
  refine WP.mono (stBytes_ok ha₂ hdst0 hdst4 hdst5 ht hdt (by rw [hq₂]; exact hq)
    (fun i hi => by rw [K₂.wr, hq₂]; exact hw i hi) t (Nat.le_refl _)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hq₂] at e₃ O₃
  rw [m₂] at O₃
  exact ⟨e₃, K₂.mono.trans k₃.mono, O₃⟩

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} : ∀ (k : Nat), (∀ j < k, f j = g j) →
    ((List.range k).flatMap f : List α) = (List.range k).flatMap g
  | 0, _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr k fun j hj => h j (by omega),
      List.flatMap_singleton, List.flatMap_singleton, h k (by omega)]

/-- The `len` bytes at `dst + d` (`8 (n - 1) ≤ len ≤ 8 n`) are `[a]`
big-endian if the mask `r10` is all ones (`c`), zeros if it is zero. -/
theorem storeBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {len n d a : Nat} {dst : Reg} (hdst0 : dst ≠ .r0) (hdst4 : dst ≠ .r4) (hdst5 : dst ≠ .r5)
    (hdst6 : dst ≠ .r6) (c : Bool)
    (hc : s.gpr .r10 = (if c then BitVec.allOnes 64 else 0)) (ha : a + 8 * n ≤ size) (ha4 : a % 4 = 0)
    (hpos : 0 < len) (hlo : 8 * n ≤ len + 8) (hhi : len ≤ 8 * n) (hdl : d + len < 2 ^ 15)
    (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + len ≤ 2 ^ 64)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, len⟩) :
    WP isa (.block (storeBytes len n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (s.gpr dst + BitVec.ofNat 64 d) len =
        (if c then Spec.Weierstrass.toBytes len (wordsVal s.mem base a n) else List.replicate len 0) ∧
      Kp stClob s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 len s.mem s'.mem := by
  have hn := hs.nowrap
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [storeBytes_eq]
  by_cases hf : 8 * (k + 1) ≤ len
  · rw [flatMap_range_congr (g := stStepW len dst d a) (k + 1) fun j hj =>
      ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    refine WP.mono (stSteps_wordsL hs h3 hdst0 hdst4 hdst5 hdst6 hc ha ha4 (by omega) hdl hw hd (k + 1)
      (Nat.le_refl _)) fun s' ⟨e, k', O⟩ => ⟨?_, k', ?_⟩
    · exact bytesAt_eq_toBytes_len _ _ _ _ c (k := k) (by omega) hhi (fun j hj _ => e j hj)
        fun h => absurd h (by omega)
    · rw [show len - 8 * (k + 1) = 0 by omega, show 8 * (k + 1) = len by omega] at O; exact O
  have hsub₀ : Region.Sub ⟨off base a, 8 * k⟩ ⟨off base a, 8 * (k + 1)⟩ := by
    have := Offset.sub_base (off base a) (d := 0) (n := 8 * k) (k := 8 * (k + 1)) (by omega)
    rwa [show off base a + BitVec.ofNat 64 0 = off base a from BitVec.add_zero _] at this
  by_cases ht : 8 * k < len
  swap
  · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      flatMap_range_congr (g := stStepW len dst d a) k fun j hj =>
        ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false hf), ite_eq_right_of_eq_false _ _ (eq_false ht),
      List.append_nil]
    refine WP.mono (stSteps_wordsL hs h3 hdst0 hdst4 hdst5 hdst6 hc (k := k) (by omega) ha4
      (by omega) hdl hw (hd.sub_left hsub₀) k (Nat.le_refl _)) fun s' ⟨e, k', O⟩ => ⟨?_, k', ?_⟩
    · exact bytesAt_eq_toBytes_len _ _ _ _ c (k := k) (by omega) hhi (fun j hj _ => e j (by omega))
        fun _ i hi => absurd hi (by omega)
    · rw [show len - 8 * k = 0 by omega, show 8 * k = len by omega] at O; exact O
  · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      flatMap_range_congr (g := stStepW len dst d a) k fun j hj =>
        ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false hf), ite_eq_left_of_eq_true _ _ (eq_true ht)]
    have hsub : Region.Sub ⟨off base a, 8 * k⟩ ⟨off base a, 8 * (k + 1)⟩ := by
      have := Offset.sub_base (off base a) (d := 0) (n := 8 * k) (k := 8 * (k + 1)) (by omega)
      rwa [show off base a + BitVec.ofNat 64 0 = off base a from BitVec.add_zero _] at this
    refine wp_append (WP.mono (stSteps_wordsL hs h3 hdst0 hdst4 hdst5 hdst6 hc (k := k) (by omega) ha4
      (by omega) hdl hw (hd.sub_left hsub) k (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simp [hdst4, hdst5, hdst6])
    have hc₁ : s₁.gpr .r10 = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.g, hc]
    have hword : word s₁.mem base (a + 8 * k) = word s.mem base (a + 8 * k) := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine WP.mono (stTop_ok (k₁.ws hs) (k₁.at h3) hdst0 hdst4 hdst5 hc₁ (t := len - 8 * k) (d := d) (a := a)
      (j := k) ha ha4 (by omega) (by omega) (by rw [hq₁]; omega)
      (fun i hi => by rw [k₁.wr, hq₁]; exact hw _ _ (by omega))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    rw [hq₁, hword] at e₂
    rw [hq₁] at O₂
    refine ⟨?_, k₁.trans k₂,
      (O₁.mono (Nat.zero_le _) (by omega)).trans (O₂.mono (Nat.le_refl _) (by omega))⟩
    refine bytesAt_eq_toBytes_len _ _ _ _ c (k := k) (by omega) hhi (fun j hj hj8 => ?_) fun _ => e₂
    refine Eq.trans ?_ (e₁ j (by omega))
    exact readW_keep fun i hi => O₂ _ (by rw [ofs_off0 _ (by omega)]; omega)

end VG.Proof.Weierstrass.PPC64LE
