import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.BytesLen

/-!
# Short Weierstrass curves on AArch64: numbers of `len` bytes

For encodings that are not whole words (P-521's 66 bytes in nine words):
`loadBytes len n o src` reads the `len` bytes at `src`, big-endian, into
`[o]` (`loadBytes_ok`), its whole words from `x6 = src + len % 8` (as `ldr`
takes offsets in words) and its top word from the first eight bytes shifted
right; `shrWords n o sh` shifts `[o]` right by `sh` bits in place
(`shrWords_ok`); and `storeBytes len n dst d a` writes `[a]` masked with `x3`
to the `len` bytes at `dst + d` (`storeBytes_ok`), its top word a byte at a
time. For `len = 8 n`, `loadBytes` and `storeBytes` are `loadBE` and
`storeBE`.
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

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

/-! ## Loads -/

/-- One word of `loadBytes` for `len ≠ 8 n`. -/
def ldStepL (len o : Nat) (src : Reg) (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ len then
    [.ldr .x .x5 .x6 (len - len % 8 - 8 * (j + 1)), .rev .x5 .x5, st .x5 (o + 8 * j)]
  else
    [.ldr .x .x5 src 0, .rev .x5 .x5, .lsr .x .x5 .x5 (8 * (8 * (j + 1) - len)), st .x5 (o + 8 * j)]

theorem loadBytes_eq {len n o : Nat} (src : Reg) (h : len ≠ 8 * n) :
    loadBytes len n o src = [.addImm .x .x6 src (len % 8)] ++ (List.range n).flatMap (ldStepL len o src) := by
  simp only [loadBytes, h, ite_false]; rfl

/-- The word `j` that `loadBytes` reads from `p`. -/
def ldWord (m : Mem) (p : Addr) (len j : Nat) : BitVec 64 :=
  if 8 * (j + 1) ≤ len then byteRev64 (m.readW (p + BitVec.ofNat 64 (len - 8 * (j + 1))) 64)
  else byteRev64 (m.readW p 64) >>> (8 * (8 * (j + 1) - len))

theorem ldStepsL_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .x5) (hsrc6 : src ≠ .x6) (h6 : s.gpr .x6 = s.gpr src + BitVec.ofNat 64 (len % 8))
    (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (h8 : 8 ≤ len) (hlo : 8 * n < len + 8) (hhi : len ≤ 8 * n)
    (hlen : len ≤ 32768)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, len⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (ldStepL len o src))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = ldWord s.mem (s.gpr src) len j) ∧
      KeepRegs [.x5] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ldStepsL_ok hs hsrc hsrc6 h6 ho ho8 h8 hlo hhi hlen hr hd k (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simpa using hsrc)
    have h6₁ : s₁.gpr .x6 = s.gpr src + BitVec.ofNat 64 (len % 8) := by rw [k₁.gpr _ (by decide), h6]
    have hkeep : ∀ d, d + 8 ≤ len → s₁.mem.readW (s.gpr src + BitVec.ofNat 64 d) 64 =
        s.mem.readW (s.gpr src + BitVec.ofNat 64 d) 64 := fun d hd' =>
      readW_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    have hst := st_out hs₁ (o := o + 8 * k) (by omega) (by omega) .x5
    by_cases hc : 8 * (k + 1) ≤ len
    · have ha : s₁.gpr .x6 + BitVec.ofNat 64 (len - len % 8 - 8 * (k + 1)) =
          s.gpr src + BitVec.ofNat 64 (len - 8 * (k + 1)) := by
        rw [h6₁, Offset.add_add, show len % 8 + (len - len % 8 - 8 * (k + 1)) = len - 8 * (k + 1) by omega]
      have hr₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x6 + BitVec.ofNat 64 (len - len % 8 - 8 * (k + 1))) 8 := by
        rw [k₁.rd, k₁.wr, ha]; exact hr _ (by omega)
      rw [ldStepL, ite_eq_left_of_eq_true _ _ (eq_true hc), show ([.ldr .x .x5 .x6 (len - len % 8 - 8 * (k + 1)), .rev .x5 .x5,
        st .x5 (o + 8 * k)] : List Instr) = [.ldr .x .x5 .x6 (len - len % 8 - 8 * (k + 1)), .rev .x5 .x5] ++
          [st .x5 (o + 8 * k)] from rfl, WP.block_append_iff]
      refine WP.mono (ldRev_ok s₁ (t := .x5) ⟨by omega, by omega⟩ hr₁) fun s₂ ⟨v₂, k₂⟩ => ?_
      have hs₂ := hs₁.of_keeps k₂ (by decide)
      refine WP.mono (st_out hs₂ (o := o + 8 * k) (by omega) (by omega) .x5) fun s₃ ⟨m₃, k₃, _⟩ => ?_
      rw [v₂, k₂.mem, ha] at m₃
      have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₃.mem := by
        rw [m₃]; exact writeW_outside _ _ _ (by omega)
      refine ⟨fun j hj => ?_, k₁.trans ((Keeps.regs k₂).trans (k₃.mono (by simp))),
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
      rcases Nat.lt_or_ge j k with h | h
      · rw [O₂.word (by omega) (by omega), e₁ j h]
      · obtain rfl : j = k := by omega
        rw [m₃, word_writeW_self, hkeep _ (by omega), ldWord, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    · have hr₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr src + BitVec.ofNat 64 0) 8 := by
        rw [k₁.rd, k₁.wr, hp₁]; exact hr _ (by omega)
      have hsh : 8 * (8 * (k + 1) - len) < 64 := by omega
      rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc), show ([.ldr .x .x5 src 0, .rev .x5 .x5, .lsr .x .x5 .x5 (8 * (8 * (k + 1) - len)),
        st .x5 (o + 8 * k)] : List Instr) = [.ldr .x .x5 src 0, .rev .x5 .x5] ++
          ([.lsr .x .x5 .x5 (8 * (8 * (k + 1) - len))] ++ [st .x5 (o + 8 * k)]) from rfl, WP.block_append_iff]
      refine WP.mono (ldRev_ok s₁ (t := .x5) ⟨by omega, by omega⟩ hr₁) fun s₂ ⟨v₂, k₂⟩ => ?_
      rw [WP.block_append_iff]
      refine WP.mono (show WP isa (.block [.lsr .x .x5 .x5 (8 * (8 * (k + 1) - len))]) s₂ (fun s₃ =>
          s₃.gpr .x5 = s₂.gpr .x5 >>> (8 * (8 * (k + 1) - len)) ∧ Keeps [.x5] s₂ s₃) by
        apply WP.of_runBlock
        simp only [runBlock_cons, exec_lsr_x hsh, runStep_some, runBlock_nil, read_x, RegUpd.gpr_write_self,
          BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
        refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
        simp only [List.mem_singleton] at hq
        rw [RegUpd.gpr_write_of_ne _ _ _ hq]) fun s₃ ⟨v₃, k₃⟩ => ?_
      have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
      refine WP.mono (st_out hs₃ (o := o + 8 * k) (by omega) (by omega) .x5) fun s₄ ⟨m₄, k₄, _⟩ => ?_
      rw [v₃, v₂, k₃.mem, k₂.mem, hp₁, BitVec.add_zero] at m₄
      have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₄.mem := by
        rw [m₄]; exact writeW_outside _ _ _ (by omega)
      refine ⟨fun j hj => ?_, k₁.trans (((Keeps.regs k₂).trans (Keeps.regs k₃)).trans (k₄.mono (by simp))),
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
      rcases Nat.lt_or_ge j k with h | h
      · rw [O₂.word (by omega) (by omega), e₁ j h]
      · obtain rfl : j = k := by omega
        have h0 := hkeep 0 (by omega)
        rw [BitVec.add_zero] at h0
        rw [m₄, word_writeW_self, h0, ldWord, ite_eq_right_of_eq_false _ _ (eq_false hc)]

/-- `[o] = ` the `len` bytes at `src`, big-endian (`8 (n - 1) < len ≤ 8 n`,
`8 ≤ len`). -/
theorem loadBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .x5) (hsrc6 : src ≠ .x6) (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0)
    (h8 : 8 ≤ len) (hlo : 8 * n < len + 8) (hhi : len ≤ 8 * n) (hlen : len ≤ 32768)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, len⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBytes len n o src)) s fun s' =>
      wordsVal s'.mem base o n = Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr src) len) ∧
      KeepRegs [.x5, .x6] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  by_cases hl : len = 8 * n
  · subst hl
    rw [loadBytes, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    exact WP.mono (loadBE_ok hs hsrc ho ho8 hlen hr hd) fun s' ⟨e, k, O⟩ => ⟨e, k.mono (by simp), O⟩
  rw [loadBytes_eq src hl, WP.block_append_iff]
  refine WP.mono (addImm_ok s (d := .x6) (n := src) (imm := len % 8) (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simpa using hsrc6)
  refine WP.mono (ldStepsL_ok hs₁ hsrc hsrc6 (by rw [v₁, hp₁]) ho ho8 h8 hlo hhi hlen
    (by rw [k₁.rd, k₁.wr, hp₁]; exact hr) (by rw [hp₁]; exact hd) n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ => ⟨?_, ?_, ?_⟩
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [k₁.mem, hp₁] at e
    exact wordsVal_eq_ofBytes_len _ _ _ _ o n' len (by omega) hhi fun j hj => e j hj
  · exact (Keeps.regs k₁).mono (by simp) |>.trans (k.mono (by simp))
  · rw [k₁.mem] at O; exact O

/-! ## One-register steps -/

theorem lsr_ok (s : State) {d n : Reg} {sh : Nat} (h : sh < 64) :
    WP isa (.block [.lsr .x d n sh]) s fun s' => s'.gpr d = s.gpr n >>> sh ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_lsr_x h, runStep_some, runBlock_nil, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq]

theorem lsl_ok (s : State) {d n : Reg} {sh : Nat} (h : sh < 64) :
    WP isa (.block [.lsl .x d n sh]) s fun s' => s'.gpr d = s.gpr n <<< sh ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, show exec (.lsl .x d n sh) s = some (s.write .x d (s.read .x n <<< sh)) by
      simp [exec, Size.bits, h],
    runStep_some, runBlock_nil, read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq]

theorem orr_ok (s : State) {d n m : Reg} :
    WP isa (.block [.logic .orr .x d n m]) s fun s' => s'.gpr d = (s.gpr n ||| s.gpr m) ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, runStep_some, runBlock_nil, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq]

theorem and_ok (s : State) {d n m : Reg} :
    WP isa (.block [.logic .and .x d n m]) s fun s' => s'.gpr d = (s.gpr n &&& s.gpr m) ∧ Keeps [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, exec, runStep_some, runBlock_nil, read_x, RegUpd.gpr_write_self,
    BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_singleton] at hq
  rw [RegUpd.gpr_write_of_ne _ _ _ hq]

/-! ## Shifting right in place -/

/-- Word `j + 1` shifted left by `64 - sh` is its low `sh` bits rotated to
the top. -/
theorem shl_eq_rotr (w : BitVec 64) {sh : Nat} (h0 : 0 < sh) (h : sh < 64) :
    w <<< (64 - sh) = (w &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and, Nat.mod_eq_of_lt h]
  by_cases hc : i < 64 - sh
  · simp only [hc, decide_true, Bool.not_true, Bool.false_and, ite_true]
    simp only [show ¬sh + i < sh by omega, decide_false, Bool.and_false]
  · simp only [hc, decide_false, Bool.not_false, Bool.true_and, ite_false]
    simp only [show i - (64 - sh) < sh by omega, decide_true, Bool.and_true, show i - (64 - sh) < 64 by omega]

/-- One word of `shrWords`. -/
def shrStep (n o sh j : Nat) : List Instr :=
  [ld .x1 (o + 8 * j), .lsr .x .x1 .x1 sh] ++
  (if j + 1 < n then [ld .x2 (o + 8 * (j + 1)), .lsl .x .x2 .x2 (64 - sh), .logic .orr .x .x1 .x1 .x2]
    else []) ++
  [st .x1 (o + 8 * j)]

theorem shrWords_eq (n o sh : Nat) : shrWords n o sh = (List.range n).flatMap (shrStep n o sh) := rfl

/-- Word `j` of `[o]` shifted right by `sh`, from the words of `m`. -/
def shrWord (m : Mem) (base : Addr) (n o sh j : Nat) : BitVec 64 :=
  if j + 1 < n then (word m base (o + 8 * j) >>> sh) |||
    (word m base (o + 8 * (j + 1)) &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh
  else word m base (o + 8 * j) >>> sh

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
    refine WP.mono (shrSteps_ok hs ho ho8 hsh hsh' k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hw : word s₁.mem base (o + 8 * k) = word s.mem base (o + 8 * k) := O₁.word (by omega) (by omega)
    rw [show shrStep n o sh k = [ld .x1 (o + 8 * k)] ++ ([.lsr .x .x1 .x1 sh] ++
      ((if k + 1 < n then [ld .x2 (o + 8 * (k + 1)), .lsl .x .x2 .x2 (64 - sh), .logic .orr .x .x1 .x1 .x2]
        else []) ++ [st .x1 (o + 8 * k)])) from rfl, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := o + 8 * k) (by omega) (by omega) .x1) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (lsr_ok s₂ (d := .x1) (n := .x1) hsh') fun s₃ ⟨v₃, k₃⟩ => ?_
    have hs₃ := (hs₁.of_keeps k₂ (by decide)).of_keeps k₃ (by decide)
    have hm₃ : s₃.mem = s₁.mem := by rw [k₃.mem, k₂.mem]
    have step : WP isa (.block ((if k + 1 < n then [ld .x2 (o + 8 * (k + 1)), .lsl .x .x2 .x2 (64 - sh),
        .logic .orr .x .x1 .x1 .x2] else []) ++ [st .x1 (o + 8 * k)])) s₃ (fun s₄ =>
        s₄.mem = s₁.mem.writeW (off base (o + 8 * k)) (shrWord s.mem base n o sh k) ∧
          KeepRegs [.x1, .x2] s₃ s₄) := by
      by_cases hc : k + 1 < n
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), List.cons_append, ← List.singleton_append,
          WP.block_append_iff]
        refine WP.mono (ld_ok hs₃ (d := o + 8 * (k + 1)) (by omega) (by omega) .x2) fun s₄ ⟨l₄, k₄, _⟩ => ?_
        rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
        refine WP.mono (lsl_ok s₄ (d := .x2) (n := .x2) (sh := 64 - sh) (by omega)) fun s₅ ⟨v₅, k₅⟩ => ?_
        rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
        refine WP.mono (orr_ok s₅ (d := .x1) (n := .x1) (m := .x2)) fun s₆ ⟨v₆, k₆⟩ => ?_
        have hs₆ := ((hs₃.of_keeps k₄ (by decide)).of_keeps k₅ (by decide)).of_keeps k₆ (by decide)
        refine WP.mono (st_out hs₆ (o := o + 8 * k) (by omega) (by omega) .x1) fun s₇ ⟨m₇, k₇, _⟩ => ?_
        have hw' : word s₁.mem base (o + 8 * (k + 1)) = word s.mem base (o + 8 * (k + 1)) :=
          O₁.word (by omega) (by omega)
        refine ⟨?_, ((Keeps.regs k₄).mono (by simp)).trans (((Keeps.regs k₅).mono (by simp)).trans
          (((Keeps.regs k₆).mono (by simp)).trans (k₇.mono (by simp))))⟩
        rw [m₇, k₆.mem, k₅.mem, k₄.mem, hm₃, v₆, v₅, k₅.gpr _ (by decide), l₄, k₄.gpr _ (by decide), v₃, l₂, hm₃, hw, hw',
          shl_eq_rotr _ (by omega) hsh', shrWord, ite_eq_left_of_eq_true _ _ (eq_true hc)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), List.nil_append]
        refine WP.mono (st_out hs₃ (o := o + 8 * k) (by omega) (by omega) .x1) fun s₄ ⟨m₄, k₄, _⟩ => ?_
        refine ⟨?_, k₄.mono (by simp)⟩
        rw [m₄, hm₃, v₃, l₂, hw, shrWord, ite_eq_right_of_eq_false _ _ (eq_false hc)]
    refine WP.mono step fun s₄ ⟨m₄, k₄⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₄.mem := by
      rw [m₄]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (((Keeps.regs k₂).mono (by simp)).trans (((Keeps.regs k₃).mono (by simp)).trans k₄)),
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₄, word_writeW_self]

/-- `[o] = [o] >> sh`, `n` words, for `0 < sh < 64`. -/
theorem shrWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (ho8 : o % 8 = 0) (hsh : 1 ≤ sh) (hsh' : sh < 64) :
    WP isa (.block (shrWords n o sh)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base o n >>> sh ∧
      KeepRegs [.x1, .x2] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [shrWords_eq]
  exact WP.mono (shrSteps_ok hs ho ho8 hsh hsh' n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨wordsVal_shr _ _ _ _ _ _ (by omega) hsh' fun j hj => e j hj, k, O⟩

/-! ## Stores -/

/-- A whole word of `storeBytes` for `len ≠ 8 n`. -/
def stStepW (len a j : Nat) : List Instr :=
  [ld .x1 (a + 8 * j), .logic .and .x .x1 .x1 .x3, .rev .x1 .x1, .str .x .x1 .x6 (len - len % 8 - 8 * (j + 1))]

/-- Byte `i` of a top word of `t` bytes in `x1`. -/
def stByte (t : Nat) (dst : Reg) (d i : Nat) : List Instr :=
  [.lsr .x .x2 .x1 (8 * (t - 1 - i)), .strb .x2 dst (d + i)]

/-- A top word of `t` bytes. -/
def stTop (t : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [ld .x1 (a + 8 * j), .logic .and .x .x1 .x1 .x3] ++ (List.range t).flatMap (stByte t dst d)

theorem storeBytes_eq {len n : Nat} (dst : Reg) (d a : Nat) (h : len ≠ 8 * n) :
    storeBytes len n dst d a = [.addImm .x .x6 dst (d + len % 8)] ++ (List.range n).flatMap fun j =>
      if 8 * (j + 1) ≤ len then stStepW len a j else stTop (len - 8 * j) dst d a j := by
  simp only [storeBytes, h, ite_false]; rfl

theorem stSteps_wordsL {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len d a : Nat}
    {dst : Reg} (hdst : dst ≠ .x1) (hdst6 : dst ≠ .x6) (h6 : s.gpr .x6 = s.gpr dst + BitVec.ofNat 64 (d + len % 8))
    {c : Bool} (hc : s.gpr .x3 = (if c then BitVec.allOnes 64 else 0))
    {k : Nat} (ha : a + 8 * k ≤ size) (ha8 : a % 8 = 0) (hlen : 8 * k ≤ len) (hl : len ≤ 32768)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * k⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, len⟩) : ∀ k', k' ≤ k →
    WP isa (.block ((List.range k').flatMap (stStepW len a))) s fun s' =>
      (∀ j < k', s'.mem.readW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1))) 64 =
        byteRev64 (word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0))) ∧
      KeepRegs [.x1] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) (len - 8 * k') (8 * k') s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k' + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stSteps_wordsL hs hdst hdst6 h6 hc ha ha8 hlen hl hw hd k' (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have h6₁ : s₁.gpr .x6 = s.gpr dst + BitVec.ofNat 64 (d + len % 8) := by rw [k₁.gpr _ (by decide), h6]
    have hc₁ : s₁.gpr .x3 = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hq : s.gpr dst + BitVec.ofNat 64 (d + len % 8) + BitVec.ofNat 64 (len - len % 8 - 8 * (k' + 1)) =
        s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (k' + 1)) := by
      rw [Offset.add_add, Offset.add_add, show d + len % 8 + (len - len % 8 - 8 * (k' + 1)) =
        d + (len - 8 * (k' + 1)) by omega]
    have hword : word s₁.mem base (a + 8 * k') = word s.mem base (a + 8 * k') := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k')) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k')) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    rw [stStepW, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (ld_ok hs₁ (d := a + 8 * k') (by omega) (by omega) .x1) fun s₂ ⟨l₂, k₂, _⟩ => ?_
    rw [show ([.logic .and .x .x1 .x1 .x3, .rev .x1 .x1, .str .x .x1 .x6 (len - len % 8 - 8 * (k' + 1))] :
      List Instr) = [.logic .and .x .x1 .x1 .x3, .rev .x1 .x1] ++ [.str .x .x1 .x6 (len - len % 8 - 8 * (k' + 1))]
      from rfl, WP.block_append_iff]
    refine WP.mono (andRev_ok s₂) fun s₃ ⟨v₃, k₃⟩ => ?_
    have h6₃ : s₃.gpr .x6 = s.gpr dst + BitVec.ofNat 64 (d + len % 8) := by
      rw [k₃.gpr _ (by decide), k₂.gpr _ (by decide), h6₁]
    have hw₃ : InRegions s₃.wr (s₃.gpr .x6 + BitVec.ofNat 64 (len - len % 8 - 8 * (k' + 1))) 8 := by
      rw [k₃.wr, k₂.wr, k₁.wr, h6₃, hq]; exact hw _ _ (by omega)
    refine WP.mono (strReg_ok s₃ ⟨by omega, by omega⟩ hw₃) fun s₄ e₄ => ?_
    subst e₄
    rw [v₃, l₂, k₂.gpr _ (by decide), hc₁, h6₃, hq, k₃.mem, k₂.mem]
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) (len - 8 * (k' + 1)) 8 s₁.mem
        (s₁.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (k' + 1)))
          (byteRev64 (word s₁.mem base (a + 8 * k') &&& if c = true then BitVec.allOnes 64 else 0))) :=
      writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (((Keeps.regs k₂).trans (Keeps.regs k₃)).trans
      ⟨fun _ _ => rfl, rfl, rfl, rfl⟩), (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k' with h | h
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), e₁ j h]
    · obtain rfl : j = k' := by omega
      rw [Mem.readW_writeW_self64, hword]

theorem exec_strb' {s : State} {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.read .w t).setWidth 8) } := by
  simp only [exec, addr, Nat.mod_one, show off < 4096 * 1 by omega, true_and, ite_true, Option.bind_some,
    State.store, h]

theorem write1_eq (m : Mem) (a : Addr) (v : BitVec 8) : m.write a 1 v = m.writeW a v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem byte_shift (v : BitVec 64) (k : Nat) :
    ((v >>> k).setWidth 32).setWidth 8 = BitVec.ofNat 8 (v.toNat >>> k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem stByte_ok {s : State} {v : BitVec 64} (ha : s.gpr .x1 = v) {dst : Reg} (hdst : dst ≠ .x2)
    {t d i : Nat} (hi : i < t) (ht : t ≤ 8) (hdi : d + i < 4096)
    (hw : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stByte t dst d i)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧ KeepRegs [.x2] s s' := by
  have hq : s.gpr dst + BitVec.ofNat 64 (d + i) = s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i :=
    (Offset.add_add _ _ _).symm
  rw [stByte, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (lsr_ok s (d := .x2) (n := .x1) (sh := 8 * (t - 1 - i)) (by omega)) fun s₁ ⟨v₁, k₁⟩ => ?_
  have hd₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
  have hw₁ : InRegions s₁.wr (s₁.gpr dst + BitVec.ofNat 64 (d + i)) 1 := by rw [k₁.wr, hd₁, hq]; exact hw
  apply WP.of_runBlock
  simp only [runBlock_cons, exec_strb' hdi hw₁, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => k₁.gpr r hr, k₁.rd, k₁.wr, k₁.sp⟩⟩
  rw [write1_eq, hd₁, hq, k₁.mem, State.read, v₁, ha, byte_shift]

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
    refine WP.mono (stBytes_ok ha hdst ht hdt hq hw i' (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    refine WP.mono (stByte_ok (s := s₁) (v := v) (by rw [k₁.gpr _ (by decide), ha]) hdst (t := t) (d := d)
      (i := i') (by omega) ht (by omega) (by rw [k₁.wr, hq₁]; exact hw i' (by omega))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [hq₁] at m₂
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) i' 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega)
    refine ⟨fun i hi' => ?_, k₁.trans k₂, (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge i i' with h | h
    · rw [O₂ _ (by rw [ofs_off0 _ (by omega)]; omega), e₁ i h]
    · obtain rfl : i = i' := by omega
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
  rw [stTop, List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := a + 8 * j) (by omega) (by omega) .x1) fun s₁ ⟨l₁, k₁, _⟩ => ?_
  rw [List.cons_append, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (and_ok s₁ (d := .x1) (n := .x1) (m := .x3)) fun s₂ ⟨v₂, k₂⟩ => ?_
  have hq₂ : s₂.gpr dst = s.gpr dst := by rw [k₂.gpr _ (by simpa using hdst), k₁.gpr _ (by simpa using hdst)]
  rw [l₁, k₁.gpr _ (by decide), hc] at v₂
  refine WP.mono (stBytes_ok v₂ hdst' ht hdt (by rw [hq₂]; exact hq)
    (fun i hi => by rw [k₂.wr, k₁.wr, hq₂]; exact hw i hi) t (Nat.le_refl _)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hq₂] at e₃ O₃
  rw [k₂.mem, k₁.mem] at O₃
  exact ⟨e₃, ((Keeps.regs k₁).mono (by simp)).trans (((Keeps.regs k₂).mono (by simp)).trans (k₃.mono (by simp))), O₃⟩

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} : ∀ (k : Nat), (∀ j < k, f j = g j) →
    ((List.range k).flatMap f : List α) = (List.range k).flatMap g
  | 0, _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr k fun j hj => h j (by omega),
      List.flatMap_singleton, List.flatMap_singleton, h k (by omega)]

/-- The `len` bytes at `dst + d` (`8 (n - 1) < len ≤ 8 n`) are `[a]`
big-endian if the mask `x3` is all ones (`c`), zeros if it is zero. -/
theorem storeBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n d a : Nat}
    {dst : Reg} (hdst : dst ≠ .x1) (hdst' : dst ≠ .x2) (hdst6 : dst ≠ .x6) (c : Bool)
    (hc : s.gpr .x3 = (if c then BitVec.allOnes 64 else 0)) (ha : a + 8 * n ≤ size) (ha8 : a % 8 = 0)
    (hpos : 0 < len) (hlo : 8 * n < len + 8) (hhi : len ≤ 8 * n) (hd8 : d % 8 = 0 ∨ len ≠ 8 * n)
    (hdl : d + len < 4096)
    (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + len ≤ 2 ^ 64)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, len⟩) :
    WP isa (.block (storeBytes len n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (s.gpr dst + BitVec.ofNat 64 d) len =
        (if c then Spec.Weierstrass.toBytes len (wordsVal s.mem base a n) else List.replicate len 0) ∧
      KeepRegs [.x1, .x2, .x6] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 len s.mem s'.mem := by
  have hn := hs.nowrap
  by_cases hl : len = 8 * n
  · subst hl
    rw [storeBytes, ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    exact WP.mono (storeBE_ok hs hdst c hc ha ha8 (by omega) (by omega)
      (fun e he => hw e 8 he) hd) fun s' ⟨e, k, O⟩ => ⟨e, k.mono (by simp), O⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [storeBytes_eq dst d a hl, WP.block_append_iff]
  refine WP.mono (addImm_ok s (d := .x6) (n := dst) (imm := d + len % 8) (by omega)) fun s₀ ⟨v₀, k₀⟩ => ?_
  have hs₀ := hs.of_keeps k₀ (by decide)
  have hp₀ : s₀.gpr dst = s.gpr dst := k₀.gpr _ (by simpa using hdst6)
  have hc₀ : s₀.gpr .x3 = (if c then BitVec.allOnes 64 else 0) := by rw [k₀.gpr _ (by decide), hc]
  have hw₀ : ∀ e m, e + m ≤ len → InRegions s₀.wr (s₀.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m := by
    rw [k₀.wr, hp₀]; exact hw
  have hd₀ : Region.Disjoint ⟨off base a, 8 * (k + 1)⟩ ⟨s₀.gpr dst + BitVec.ofNat 64 d, len⟩ := by rw [hp₀]; exact hd
  have hm₀ := k₀.mem
  have hf : ¬ 8 * (k + 1) ≤ len := by omega
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
    flatMap_range_congr (g := stStepW len a) k fun j hj => ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false hf), WP.block_append_iff]
  have hsub : Region.Sub ⟨off base a, 8 * k⟩ ⟨off base a, 8 * (k + 1)⟩ := by
    have := Offset.sub_base (off base a) (d := 0) (n := 8 * k) (k := 8 * (k + 1)) (by omega)
    rwa [show off base a + BitVec.ofNat 64 0 = off base a from BitVec.add_zero _] at this
  refine WP.mono (stSteps_wordsL hs₀ hdst hdst6 (by rw [v₀, hp₀]) hc₀ (k := k) (by omega) ha8 (by omega)
    (by omega) hw₀ (hd₀.sub_left hsub) k (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs₀.of_keepRegs k₁ (by decide)
  have hq₁ : s₁.gpr dst = s.gpr dst := by rw [k₁.gpr _ (by simpa using hdst), hp₀]
  have hc₁ : s₁.gpr .x3 = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.gpr _ (by decide), hc₀]
  have hword : word s₁.mem base (a + 8 * k) = word s.mem base (a + 8 * k) := by
    show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64
    rw [← Offset.add_add, ← hm₀]
    exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd₀ (by omega)
      (by omega) (by omega)
  refine WP.mono (stTop_ok hs₁ hdst hdst' hc₁ (t := len - 8 * k) (d := d) (a := a) (j := k) ha ha8 (by omega)
    (by omega) (by rw [hq₁]; omega) (fun i hi => by rw [k₁.wr, hq₁, ← hp₀]; exact hw₀ _ _ (by omega)))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hq₁, hword] at e₂
  rw [hq₁] at O₂
  rw [hp₀, hm₀] at e₁ O₁
  refine ⟨?_, ((Keeps.regs k₀).mono (by simp)).trans ((k₁.mono (by simp)).trans (k₂.mono (by simp))),
    (O₁.mono (Nat.zero_le _) (by omega)).trans (O₂.mono (Nat.le_refl _) (by omega))⟩
  refine bytesAt_eq_toBytes_len _ _ _ _ c (k := k) (by omega) hhi (fun j hj hj8 => ?_) fun _ => e₂
  refine Eq.trans ?_ (e₁ j (by omega))
  exact readW_keep fun i hi => O₂ _ (by rw [ofs_off0 _ (by omega)]; omega)

end VG.Proof.Weierstrass.AArch64
