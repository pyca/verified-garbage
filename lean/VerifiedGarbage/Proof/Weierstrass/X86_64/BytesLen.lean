import VerifiedGarbage.Proof.Weierstrass.X86_64.Bytes
import VerifiedGarbage.Proof.Weierstrass.BytesLen

/-!
# Short Weierstrass curves on x86-64: numbers of `len` bytes

For encodings that are not whole words (P-521's 66 bytes in nine words):
`loadBytes len n o src` reads the `len` bytes at `src`, big-endian, into
`[o]` (`loadBytes_ok`), its top word from the first eight bytes shifted
right; `shrWords n o sh` shifts `[o]` right by `sh` bits in place
(`shrWords_ok`); and `storeBytes len n dst d a` writes `[a]` masked with
`rcx` to the `len` bytes at `dst + d` (`storeBytes_ok`), its top word a byte
at a time.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont

/-! ## Loads -/

/-- One word of `loadBytes`. -/
def ldStepL (len o : Nat) (src : Reg) (j : Nat) : List Instr :=
  if 8 * (j + 1) ≤ len then
    [.mov .rax (.mem { base := src, disp := ((len - 8 * (j + 1) : Nat) : Int) }), .bswap .rax,
      .store (sc (o + 8 * j)) .rax]
  else
    [.mov .rax (.mem { base := src, disp := ((0 : Nat) : Int) }), .bswap .rax,
      .shift .shr .rax (8 * (8 * (j + 1) - len)), .store (sc (o + 8 * j)) .rax]

theorem loadBytes_eq (len n o : Nat) (src : Reg) :
    loadBytes len n o src = (List.range n).flatMap (ldStepL len o src) := rfl

/-- The word `j` that `loadBytes` reads from `p`. -/
def ldWord (m : Mem) (p : Addr) (len j : Nat) : BitVec 64 :=
  if 8 * (j + 1) ≤ len then byteRev64 (m.readW (p + BitVec.ofNat 64 (len - 8 * (j + 1))) 64)
  else byteRev64 (m.readW p 64) >>> (8 * (8 * (j + 1) - len))

theorem ldStepsL_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .rax) (ho : o + 8 * n ≤ size) (h8 : 8 ≤ len) (hlo : 8 * n < len + 8)
    (hhi : len ≤ 8 * n)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, len⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (ldStepL len o src))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = ldWord s.mem (s.gpr src) len j) ∧
      KeepRegs [.rax] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ldStepsL_ok hs hsrc ho h8 hlo hhi hr hd k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simpa using hsrc)
    have hkeep : ∀ d, d + 8 ≤ len → s₁.mem.readW (s.gpr src + BitVec.ofNat 64 d) 64 =
        s.mem.readW (s.gpr src + BitVec.ofNat 64 d) 64 := fun d hd' =>
      readW_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    have hst := st_sc hs₁ (d := o + 8 * k) (by omega)
    by_cases hc : 8 * (k + 1) ≤ len
    · have hr₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr src + BitVec.ofNat 64 (len - 8 * (k + 1))) 8 := by
        rw [k₁.rd, k₁.wr, hp₁]; exact hr _ (by omega)
      refine WP.mono (show WP isa (.block (ldStepL len o src k)) s₁ (fun s₂ =>
          s₂.mem = s₁.mem.writeW (off base (o + 8 * k))
            (bswap64 (s₁.mem.readW (s₁.gpr src + BitVec.ofNat 64 (len - 8 * (k + 1))) 64)) ∧
            KeepRegs [.rax] s₁ s₂) by
        apply WP.of_runBlock
        simp only [ldStepL, hc, ite_true, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
          Option.map_some, State.load64, State.store64, ea_disp, ea_sc, hr₁, RegUpd.gpr_setReg,
          RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false, hs₁.rdi, hst,
          Option.some.injEq, exists_eq_left']
        refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₂ ⟨m₂, k₂⟩ => ?_
      have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
        rw [m₂]; exact writeW_outside _ _ _ (by omega)
      refine ⟨fun j hj => ?_, k₁.trans k₂,
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
      rcases Nat.lt_or_ge j k with h | h
      · rw [O₂.word (by omega) (by omega), e₁ j h]
      · obtain rfl : j = k := by omega
        rw [m₂, word_writeW_self, hp₁, hkeep _ (by omega), ldWord, ite_eq_left_of_eq_true _ _ (eq_true hc)]
        rfl
    · have hr₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr src + BitVec.ofNat 64 0) 8 := by
        rw [k₁.rd, k₁.wr, hp₁]; exact hr _ (by omega)
      have hsh : 1 ≤ 8 * (8 * (k + 1) - len) ∧ 8 * (8 * (k + 1) - len) ≤ 63 := ⟨by omega, by omega⟩
      refine WP.mono (show WP isa (.block (ldStepL len o src k)) s₁ (fun s₂ =>
          s₂.mem = s₁.mem.writeW (off base (o + 8 * k))
            (bswap64 (s₁.mem.readW (s₁.gpr src + BitVec.ofNat 64 0) 64) >>> (8 * (8 * (k + 1) - len))) ∧
            KeepRegs [.rax] s₁ s₂) by
        apply WP.of_runBlock
        simp only [ldStepL, hc, ite_false, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
          execShift, hsh, ite_true, Option.map_some, State.load64, State.store64, ea_disp, ea_sc, hr₁,
          RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.mem_setReg,
          RegUpd.mem_setFlags, reduceCtorEq, hs₁.rdi, hst, and_self, Option.some.injEq, exists_eq_left']
        refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]) fun s₂ ⟨m₂, k₂⟩ => ?_
      have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
        rw [m₂]; exact writeW_outside _ _ _ (by omega)
      refine ⟨fun j hj => ?_, k₁.trans k₂,
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
      rcases Nat.lt_or_ge j k with h | h
      · rw [O₂.word (by omega) (by omega), e₁ j h]
      · obtain rfl : j = k := by omega
        rw [m₂, word_writeW_self, hp₁, hkeep _ (by omega), ldWord, ite_eq_right_of_eq_false _ _ (eq_false hc),
          BitVec.add_zero]
        rfl

/-- `[o] = ` the `len` bytes at `src`, big-endian (`8 (n - 1) < len ≤ 8 n`,
`8 ≤ len`). -/
theorem loadBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .rax) (ho : o + 8 * n ≤ size) (h8 : 8 ≤ len) (hlo : 8 * n < len + 8)
    (hhi : len ≤ 8 * n)
    (hr : ∀ d, d + 8 ≤ len → InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 d) 8)
    (hd : Region.Disjoint ⟨s.gpr src, len⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBytes len n o src)) s fun s' =>
      wordsVal s'.mem base o n = Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr src) len) ∧
      KeepRegs [.rax] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBytes_eq]
  refine WP.mono (ldStepsL_ok hs hsrc ho h8 hlo hhi hr hd n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact wordsVal_eq_ofBytes_len _ _ _ _ o n' len (by omega) hhi fun j hj => e j hj

/-! ## Shifting right in place -/

/-- One word of `shrWords`. -/
def shrStep (n o sh j : Nat) : List Instr :=
  [.mov .rax (.mem (sc (o + 8 * j))), .shift .shr .rax sh] ++
  (if j + 1 < n then
    [.mov .rdx (.mem (sc (o + 8 * (j + 1)))), .alu .and .rdx (.imm (BitVec.ofNat 32 (2 ^ sh - 1))),
      .shift .ror .rdx sh, .alu .or .rax (.reg .rdx)]
  else []) ++
  [.store (sc (o + 8 * j)) .rax]

theorem shrWords_eq (n o sh : Nat) : shrWords n o sh = (List.range n).flatMap (shrStep n o sh) := rfl

/-- The mask of the low `sh < 32` bits, as an immediate. -/
theorem imm_mask : ∀ sh < 32, (BitVec.ofNat 32 (2 ^ sh - 1)).signExtend 64 = BitVec.ofNat 64 (2 ^ sh - 1) := by
  decide +kernel

/-- Word `j` of `[o]` shifted right by `sh`, from the words of `m`. -/
def shrWord (m : Mem) (base : Addr) (n o sh j : Nat) : BitVec 64 :=
  if j + 1 < n then (word m base (o + 8 * j) >>> sh) |||
    (word m base (o + 8 * (j + 1)) &&& BitVec.ofNat 64 (2 ^ sh - 1)).rotateRight sh
  else word m base (o + 8 * j) >>> sh

theorem shrSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (hsh : 1 ≤ sh) (hsh' : sh < 32) : ∀ k, k ≤ n →
    WP isa (.block ((List.range k).flatMap (shrStep n o sh))) s fun s' =>
      (∀ j < k, word s'.mem base (o + 8 * j) = shrWord s.mem base n o sh j) ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside base o (8 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (shrSteps_ok hs ho hsh hsh' k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hst := st_sc hs₁ (d := o + 8 * k) (by omega)
    have hld := ld_sc hs₁ (d := o + 8 * k) (by omega)
    have hw : word s₁.mem base (o + 8 * k) = word s.mem base (o + 8 * k) := O₁.word (by omega) (by omega)
    have hsh₁ : 1 ≤ sh ∧ sh ≤ 63 := ⟨hsh, by omega⟩
    have step : WP isa (.block (shrStep n o sh k)) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (off base (o + 8 * k)) (shrWord s.mem base n o sh k) ∧
          KeepRegs [.rax, .rdx] s₁ s₂) := by
      apply WP.of_runBlock
      by_cases hc : k + 1 < n
      · have hld' := ld_sc hs₁ (d := o + 8 * (k + 1)) (by omega)
        have hw' : word s₁.mem base (o + 8 * (k + 1)) = word s.mem base (o + 8 * (k + 1)) :=
          O₁.word (by omega) (by omega)
        simp only [shrStep, hc, ite_true, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
          runBlock_nil, exec, readSrc, execAlu, execShift, hsh₁, and_self, Option.map_some, Option.bind_some,
          State.load64, State.store64, ea_sc, hld, hld', hst, hs₁.rdi, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
          RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
          RegUpd.wr_setFlags, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags,
          RegUpd.mem_arithFlags, reduceCtorEq, ite_false, imm_mask sh hsh',
          Option.some.injEq, exists_eq_left']
        refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
        · unfold shrWord; rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ← hw, ← hw']
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]
      · simp only [shrStep, hc, ite_false, List.cons_append, List.nil_append, List.append_nil, runBlock_cons,
          runStep_some, runBlock_nil, exec, readSrc, execShift, hsh₁, and_self, ite_true, Option.map_some,
          State.load64, State.store64, ea_sc, hld, hst, hs₁.rdi, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
          RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags, reduceCtorEq,
          Option.some.injEq, exists_eq_left']
        refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
        · unfold shrWord; rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ← hw]
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
          simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, ite_false]
    refine WP.mono step fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside base (o + 8 * k) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂.word (by omega) (by omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, word_writeW_self]

/-- `[o] = [o] >> sh`, `n` words, for `0 < sh < 32`. -/
theorem shrWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (hsh : 1 ≤ sh) (hsh' : sh < 32) :
    WP isa (.block (shrWords n o sh)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base o n >>> sh ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [shrWords_eq]
  exact WP.mono (shrSteps_ok hs ho hsh hsh' n (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨wordsVal_shr _ _ _ _ _ _ (by omega) (by omega) fun j hj => e j hj, k, O⟩

/-! ## Stores -/

/-- A whole word of `storeBytes`. -/
def stStepW (len : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.mov .rax (.mem (sc (a + 8 * j))), .alu .and .rax (.reg .rcx), .bswap .rax,
    .store { base := dst, disp := ((d + (len - 8 * (j + 1)) : Nat) : Int) } .rax]

/-- Byte `i` of a top word of `t` bytes in `rax`. -/
def stByte (t : Nat) (dst : Reg) (d i : Nat) : List Instr :=
  [.mov .rdx (.reg .rax)] ++ (if t - 1 - i = 0 then [] else [.shift .shr .rdx (8 * (t - 1 - i))]) ++
    [.store8 { base := dst, disp := ((d + i : Nat) : Int) } .rdx]

/-- A top word of `t` bytes. -/
def stTop (t : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.mov .rax (.mem (sc (a + 8 * j))), .alu .and .rax (.reg .rcx)] ++
    (List.range t).flatMap (stByte t dst d)

theorem storeBytes_eq (len n : Nat) (dst : Reg) (d a : Nat) :
    storeBytes len n dst d a = (List.range n).flatMap fun j =>
      if 8 * (j + 1) ≤ len then stStepW len dst d a j else stTop (len - 8 * j) dst d a j := rfl

/-- The masked byte `i` of `t` of a word, most significant first. -/
theorem byte_shift (v : BitVec 64) (k : Nat) : (v >>> k).setWidth 8 = BitVec.ofNat 8 (v.toNat >>> k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]

theorem stSteps_wordsL {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len d a : Nat}
    {dst : Reg} (hdst : dst ≠ .rax) {c : Bool} (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0))
    {k : Nat} (ha : a + 8 * k ≤ size) (hlen : 8 * k ≤ len) (hl : len ≤ 2 ^ 64)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * k⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, len⟩) : ∀ k', k' ≤ k →
    WP isa (.block ((List.range k').flatMap (stStepW len dst d a))) s fun s' =>
      (∀ j < k', s'.mem.readW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (j + 1))) 64 =
        bswap64 (word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0))) ∧
      KeepRegs [.rax] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) (len - 8 * k') (8 * k') s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | k' + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stSteps_wordsL hs hdst hc ha hlen hl hw hd k' (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    have hc₁ : s₁.gpr .rcx = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hq : s.gpr dst + BitVec.ofNat 64 (d + (len - 8 * (k' + 1))) =
        s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (k' + 1)) := (Offset.add_add _ _ _).symm
    have hw₁ : InRegions s₁.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (k' + 1))) 8 := by
      rw [k₁.wr]; exact hw _ _ (by omega)
    have hword : word s₁.mem base (a + 8 * k') = word s.mem base (a + 8 * k') := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k')) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k')) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine WP.mono (show WP isa (.block (stStepW len dst d a k')) s₁ (fun s₂ =>
        s₂.mem = s₁.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 8 * (k' + 1)))
          (bswap64 (word s₁.mem base (a + 8 * k') &&& (if c then BitVec.allOnes 64 else 0))) ∧
          KeepRegs [.rax] s₁ s₂) by
      apply WP.of_runBlock
      simp only [stStepW, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
        Option.bind_some, State.load64, State.store64, ea_disp, ea_sc, hs₁.rdi,
        ld_sc hs₁ (d := a + 8 * k') (by omega), RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
        RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, reduceCtorEq, ite_true, ite_false,
        hdst, hq₁, hc₁, hq, hw₁, Option.some.injEq, exists_eq_left']
      refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₂ ⟨m₂, k₂⟩ => ?_
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) (len - 8 * (k' + 1)) 8 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans k₂,
      (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k' with h | h
    · rw [m₂, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), e₁ j h]
    · obtain rfl : j = k' := by omega
      rw [m₂, Mem.readW_writeW_self64, hword]

theorem stByte_ok {s : State} {v : BitVec 64} (ha : s.gpr .rax = v) {dst : Reg} (hdst : dst ≠ .rdx)
    {t d i : Nat} (hi : i < t) (ht : t ≤ 8)
    (hw : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stByte t dst d i)) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧ KeepRegs [.rdx] s s' := by
  have hq : s.gpr dst + BitVec.ofNat 64 (d + i) = s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i :=
    (Offset.add_add _ _ _).symm
  apply WP.of_runBlock
  by_cases h0 : t - 1 - i = 0
  · simp only [stByte, h0, ite_true, List.nil_append, List.cons_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, Option.map_some, State.store8, ea_disp, RegUpd.gpr_setReg,
      RegUpd.wr_setReg, RegUpd.mem_setReg, hdst, ite_false, ha, hq, hw, Option.some.injEq,
      exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
    · rw [Nat.mul_zero, Nat.shiftRight_zero]
      exact congrArg _ (BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]
  · have hsh : 1 ≤ 8 * (t - 1 - i) ∧ 8 * (t - 1 - i) ≤ 63 := ⟨by omega, by omega⟩
    simp only [stByte, h0, ite_false, List.nil_append, List.cons_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execShift, hsh, and_self, ite_true, Option.map_some, State.store8, ea_disp,
      RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.wr_setReg, RegUpd.wr_setFlags, RegUpd.mem_setReg,
      RegUpd.mem_setFlags, hdst, ha, hq, hw, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl⟩⟩
    · rw [byte_shift]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

theorem stBytes_ok {s : State} {v : BitVec 64} (ha : s.gpr .rax = v) {dst : Reg} (hdst : dst ≠ .rdx)
    (hdst' : dst ≠ .rax) {t d : Nat} (ht : t ≤ 8) (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + t ≤ 2 ^ 64)
    (hw : ∀ i < t, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) : ∀ i', i' ≤ t →
    WP isa (.block ((List.range i').flatMap (stByte t dst d))) s fun s' =>
      (∀ i < i', s'.mem (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧
      KeepRegs [.rdx] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 i' s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), ⟨fun _ _ => rfl, rfl, rfl⟩,
      Outside.refl _ _ _ _⟩
  | i' + 1, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (stBytes_ok ha hdst hdst' ht hq hw i' (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    refine WP.mono (stByte_ok (s := s₁) (v := v) (by rw [k₁.gpr _ (by decide), ha]) hdst (t := t) (d := d)
      (i := i') (by omega) ht (by rw [k₁.wr, hq₁]; exact hw i' (by omega))) fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [hq₁] at m₂
    have O₂ : Outside (s.gpr dst + BitVec.ofNat 64 d) i' 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega)
    refine ⟨fun i hi' => ?_, k₁.trans k₂, (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge i i' with h | h
    · rw [O₂ _ (by rw [ofs_off0 _ (by omega)]; omega), e₁ i h]
    · obtain rfl : i = i' := by omega
      rw [m₂, writeW8_self]

theorem stTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst : Reg}
    (hdst : dst ≠ .rax) (hdst' : dst ≠ .rdx) {c : Bool} (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0))
    {t d a j : Nat} (ha : a + 8 * (j + 1) ≤ size) (ht : t ≤ 8)
    (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + t ≤ 2 ^ 64)
    (hw : ∀ i < t, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stTop t dst d a j)) s fun s' =>
      (∀ i < t, s'.mem (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 ((word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0)).toNat >>>
          (8 * (t - 1 - i)))) ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 t s.mem s'.mem := by
  rw [stTop, WP.block_append_iff]
  refine WP.mono (show WP isa (.block ([.mov .rax (.mem (sc (a + 8 * j))), .alu .and .rax (.reg .rcx)] :
      List Instr)) s (fun s₁ => s₁.gpr .rax = word s.mem base (a + 8 * j) &&& (if c then BitVec.allOnes 64 else 0) ∧
        KeepRegs [.rax] s s₁ ∧ s₁.mem = s.mem) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
      Option.bind_some, State.load64, ea_sc, hs.rdi, ld_sc hs (d := a + 8 * j) (by omega), RegUpd.gpr_setReg,
      RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags, reduceCtorEq, ite_true, ite_false, hc,
      Option.some.injEq, exists_eq_left']
    refine ⟨trivial, ⟨fun r hr => ?_, rfl, rfl⟩, trivial⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]) fun s₁ ⟨a₁, k₁, m₁⟩ => ?_
  have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
  refine WP.mono (stBytes_ok a₁ hdst' hdst ht (by rw [hq₁]; exact hq)
    (fun i hi => by rw [k₁.wr, hq₁]; exact hw i hi) t (Nat.le_refl _)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hq₁] at e₂ O₂
  rw [m₁] at O₂
  exact ⟨e₂, (k₁.mono (by decide)).trans (k₂.mono (by decide)), O₂⟩

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} : ∀ (k : Nat), (∀ j < k, f j = g j) →
    ((List.range k).flatMap f : List α) = (List.range k).flatMap g
  | 0, _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr k fun j hj => h j (by omega),
      List.flatMap_singleton, List.flatMap_singleton, h k (by omega)]

/-- The `len` bytes at `dst + d` (`8 (n - 1) < len ≤ 8 n`) are `[a]`
big-endian if the mask `rcx` is all ones (`c`), zeros if it is zero. -/
theorem storeBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n d a : Nat}
    {dst : Reg} (hdst : dst ≠ .rax) (hdst' : dst ≠ .rdx) (c : Bool)
    (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0)) (ha : a + 8 * n ≤ size) (hpos : 0 < len)
    (hlo : 8 * n < len + 8)
    (hhi : len ≤ 8 * n) (hq : (s.gpr dst + BitVec.ofNat 64 d).toNat + len ≤ 2 ^ 64)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (s.gpr dst + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨s.gpr dst + BitVec.ofNat 64 d, len⟩) :
    WP isa (.block (storeBytes len n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (s.gpr dst + BitVec.ofNat 64 d) len =
        (if c then Spec.Weierstrass.toBytes len (wordsVal s.mem base a n) else List.replicate len 0) ∧
      KeepRegs [.rax, .rdx] s s' ∧ Outside (s.gpr dst + BitVec.ofNat 64 d) 0 len s.mem s'.mem := by
  have hn := hs.nowrap
  have hl : len ≤ 2 ^ 64 := by omega
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [storeBytes_eq]
  by_cases hf : 8 * (k + 1) ≤ len
  · rw [flatMap_range_congr (g := stStepW len dst d a) (k + 1) fun j hj =>
      ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    refine WP.mono (stSteps_wordsL hs hdst hc ha (by omega) hl hw hd (k + 1) (Nat.le_refl _))
      fun s' ⟨e, k', O⟩ => ⟨?_, k'.mono (by decide), ?_⟩
    · exact bytesAt_eq_toBytes_len _ _ _ _ c (k := k) (by omega) hhi (fun j hj _ => e j hj)
        fun h => absurd h (by omega)
    · rw [show len - 8 * (k + 1) = 0 by omega, show 8 * (k + 1) = len by omega] at O; exact O
  · rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
      flatMap_range_congr (g := stStepW len dst d a) k fun j hj =>
        ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      ite_eq_right_of_eq_false _ _ (eq_false hf), WP.block_append_iff]
    have hsub : Region.Sub ⟨off base a, 8 * k⟩ ⟨off base a, 8 * (k + 1)⟩ := by
      have := Offset.sub_base (off base a) (d := 0) (n := 8 * k) (k := 8 * (k + 1)) (by omega)
      rwa [show off base a + BitVec.ofNat 64 0 = off base a from BitVec.add_zero _] at this
    refine WP.mono (stSteps_wordsL hs hdst hc (k := k) (by omega) (by omega) hl hw (hd.sub_left hsub) k
      (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    have hc₁ : s₁.gpr .rcx = (if c then BitVec.allOnes 64 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hword : word s₁.mem base (a + 8 * k) = word s.mem base (a + 8 * k) := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64 = s.mem.readW (base + BitVec.ofNat 64 (a + 8 * k)) 64
      rw [← Offset.add_add]
      exact readW_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine WP.mono (stTop_ok hs₁ hdst hdst' hc₁ (t := len - 8 * k) (d := d) (a := a) (j := k) ha (by omega)
      (by rw [hq₁]; omega) (fun i hi => by rw [k₁.wr, hq₁]; exact hw _ _ (by omega))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    rw [hq₁, hword] at e₂
    rw [hq₁] at O₂
    refine ⟨?_, (k₁.mono (by decide)).trans k₂,
      (O₁.mono (Nat.zero_le _) (by omega)).trans (O₂.mono (Nat.le_refl _) (by omega))⟩
    refine bytesAt_eq_toBytes_len _ _ _ _ c (k := k) (by omega) hhi (fun j hj hj8 => ?_) fun _ => e₂
    refine Eq.trans ?_ (e₁ j (by omega))
    exact readW_keep fun i hi => O₂ _ (by rw [ofs_off0 _ (by omega)]; omega)

end VG.Proof.Weierstrass.X86_64
