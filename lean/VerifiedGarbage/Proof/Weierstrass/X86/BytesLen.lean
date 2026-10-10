import VerifiedGarbage.Proof.Weierstrass.X86.Bytes
import VerifiedGarbage.Proof.Weierstrass.BytesLen32

/-!
# Short Weierstrass curves on x86 (32-bit): numbers of `len` bytes

For encodings that are not whole words (P-521's 66 bytes in the eighteen
32-bit words of nine 64-bit ones): `loadBytes len n o src` reads the `len`
bytes at `src`, big-endian, into `[o]` (`loadBytes_ok`), a word of fewer
bytes from the first four shifted right and the words past `len` zero;
`shrWords n o sh` shifts `[o]` right by `sh` bits in place (`shrWords_ok`);
and `storeBytes len n dst d a` writes `[a]` masked with `ecx` to the `len`
bytes at `dst + d` (`storeBytes_ok`), a word of fewer bytes a byte at a
time.
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

/-! ## Loads -/

/-- One word of `loadBytes`. -/
def ldStepL (len o : Nat) (src : Reg) (j : Nat) : List Instr :=
  if 4 * (j + 1) ≤ len then
    [.mov .eax (.mem (at_ src (len - 4 * (j + 1)))), .bswap .eax, .store (sc (o + 4 * j)) .eax]
  else if 4 * j < len then
    [.mov .eax (.mem (at_ src 0)), .bswap .eax, .shift .shr .eax (8 * (4 * (j + 1) - len)),
      .store (sc (o + 4 * j)) .eax]
  else [.mov .eax (.imm 0), .store (sc (o + 4 * j)) .eax]

theorem loadBytes_eq (len n o : Nat) (src : Reg) :
    loadBytes len n o src = (List.range (2 * n)).flatMap (ldStepL len o src) := rfl

theorem ldStepsL_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .eax) (ho : o + 8 * n ≤ size) (hp : (s.gpr src).toNat + len ≤ 2 ^ 32)
    (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (hr : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨(s.gpr src).setWidth 64, len⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ 2 * n →
    WP isa (.block ((List.range k).flatMap (ldStepL len o src))) s fun s' =>
      (∀ j < k, w32 s'.mem base (o + 4 * j) = ldWord32 s.mem ((s.gpr src).setWidth 64) len j) ∧
      Keeps [.eax] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ldStepsL_ok hs hsrc ho hp h4 hlen hr hd k (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.1 _ (by simpa using hsrc)
    have hkeep : ∀ d, d + 4 ≤ len → s₁.mem.readW ((s.gpr src).setWidth 64 + BitVec.ofNat 64 d) 32 =
        s.mem.readW ((s.gpr src).setWidth 64 + BitVec.ofNat 64 d) 32 := fun d hd' =>
      readW32_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega)) hd (by omega)
        (by omega) (by omega)
    by_cases hc1 : 4 * (k + 1) ≤ len
    · have ha₁ : s₁.ea (at_ src (len - 4 * (k + 1))) =
          (s.gpr src).setWidth 64 + BitVec.ofNat 64 (len - 4 * (k + 1)) := by
        rw [ea_ptr s₁ (by rw [hp₁]; omega), hp₁]
      have hr₁ : InRegions (s₁.rd ++ s₁.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 (len - 4 * (k + 1))) 4 := by
        rw [k₁.2.1, k₁.2.2]; exact hr _ (by omega)
      rw [ldStepL, ite_eq_left_of_eq_true _ _ (eq_true hc1)]
      refine wp_movS (show readSrc s₁ (.mem (at_ src (len - 4 * (k + 1)))) = some _ by
        show s₁.load32 _ = _; rw [ha₁, State.load32, ite_eq_left_iff.mpr fun h => absurd hr₁ h]) fun s₂ u₂ _ => ?_
      refine wp_bswap fun s₃ u₃ => ?_
      have k₃ : Keeps [.eax] s₁ s₃ := u₂.keeps.trans u₃.keeps
      have hs₃ := hs₁.of_keeps k₃ (by decide)
      refine wp_storeS (hs₃.ea (d := o + 4 * k) (by omega)) (hs₃.write (d := o + 4 * k) (n := 4) (by omega))
        fun s₄ m₄ => WP.block_nil ?_
      have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₄.mem := by
        rw [m₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
      refine ⟨fun j hj => ?_, k₁.trans (k₃.trans (m₄.keeps _)),
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
      rcases Nat.lt_or_ge j k with h | h
      · rw [O₂.w32 (by omega) (by omega), e₁ j h]
      · obtain rfl : j = k := by omega
        rw [m₄.mem, u₃.mem, u₂.mem, w32_write_self, u₃.gpr, u₂.gpr, hkeep _ (by omega), bswap_eq, ldWord32,
          ite_eq_left_of_eq_true _ _ (eq_true hc1)]
    · by_cases hc2 : 4 * k < len
      · have ha₁ : s₁.ea (at_ src 0) = (s.gpr src).setWidth 64 + BitVec.ofNat 64 0 := by
          rw [ea_ptr s₁ (by rw [hp₁]; omega), hp₁]
        have hr₁ : InRegions (s₁.rd ++ s₁.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 0) 4 := by
          rw [k₁.2.1, k₁.2.2]; exact hr _ (by omega)
        rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_left_of_eq_true _ _ (eq_true hc2)]
        refine wp_movS (show readSrc s₁ (.mem (at_ src 0)) = some _ by
          show s₁.load32 _ = _; rw [ha₁, State.load32, ite_eq_left_iff.mpr fun h => absurd hr₁ h]) fun s₂ u₂ _ => ?_
        refine wp_bswap fun s₃ u₃ => ?_
        refine wp_shr (n := 8 * (4 * (k + 1) - len)) ⟨by omega, by omega⟩ fun s₄ u₄ _ => ?_
        have k₄ : Keeps [.eax] s₁ s₄ := (u₂.keeps.trans u₃.keeps).trans u₄.keeps
        have hs₄ := hs₁.of_keeps k₄ (by decide)
        refine wp_storeS (hs₄.ea (d := o + 4 * k) (by omega)) (hs₄.write (d := o + 4 * k) (n := 4) (by omega))
          fun s₅ m₅ => WP.block_nil ?_
        have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₅.mem := by
          rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
        refine ⟨fun j hj => ?_, k₁.trans (k₄.trans (m₅.keeps _)),
          (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
        rcases Nat.lt_or_ge j k with h | h
        · rw [O₂.w32 (by omega) (by omega), e₁ j h]
        · obtain rfl : j = k := by omega
          have h0 := hkeep 0 (by omega)
          rw [BitVec.add_zero] at h0
          rw [m₅.mem, u₄.mem, u₃.mem, u₂.mem, w32_write_self, u₄.gpr, u₃.gpr, u₂.gpr, BitVec.add_zero, h0,
            bswap_eq, BitVec.toNat_ushiftRight, ldWord32, ite_eq_right_of_eq_false _ _ (eq_false hc1),
            ite_eq_left_of_eq_true _ _ (eq_true hc2)]
      · rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_right_of_eq_false _ _ (eq_false hc2)]
        refine wp_movS (v := 0) rfl fun s₂ u₂ _ => ?_
        have hs₂ := hs₁.of_keeps u₂.keeps (by decide)
        refine wp_storeS (hs₂.ea (d := o + 4 * k) (by omega)) (hs₂.write (d := o + 4 * k) (n := 4) (by omega))
          fun s₃ m₃ => WP.block_nil ?_
        have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₃.mem := by
          rw [m₃.mem, u₂.mem]; exact writeW32_outside _ _ _ (by omega)
        refine ⟨fun j hj => ?_, k₁.trans (u₂.keeps.trans (m₃.keeps _)),
          (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
        rcases Nat.lt_or_ge j k with h | h
        · rw [O₂.w32 (by omega) (by omega), e₁ j h]
        · obtain rfl : j = k := by omega
          rw [m₃.mem, u₂.mem, w32_write_self, u₂.gpr, ldWord32, ite_eq_right_of_eq_false _ _ (eq_false hc1),
            ite_eq_right_of_eq_false _ _ (eq_false hc2)]
          rfl

/-- `[o] = ` the `len` bytes at `src`, big-endian (`4 ≤ len ≤ 8 n`). -/
theorem loadBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .eax) (ho : o + 8 * n ≤ size) (hp : (s.gpr src).toNat + len ≤ 2 ^ 32)
    (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (hr : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) ((s.gpr src).setWidth 64 + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨(s.gpr src).setWidth 64, len⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBytes len n o src)) s fun s' =>
      wordsVal s'.mem base o n =
        Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem ((s.gpr src).setWidth 64) len) ∧
      Keeps [.eax] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBytes_eq]
  refine WP.mono (ldStepsL_ok hs hsrc ho hp h4 hlen hr hd (2 * n) (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, by rw [show 8 * n = 4 * (2 * n) by omega]; exact O⟩
  rw [wordsVal_eq_val32]
  exact val32_eq_ofBytes_len _ _ _ _ o (2 * n) len h4 (by omega) e

/-! ## Shifting right in place -/

/-- One word of `shrWords`. -/
def shrStep (n o sh j : Nat) : List Instr :=
  ([.mov .eax (.mem (sc (o + 4 * j))), .shift .shr .eax sh] : List Instr) ++
  ((if j + 1 < 2 * n then
    [.mov .edx (.mem (sc (o + 4 * (j + 1)))), .alu .and .edx (.imm (BitVec.ofNat 32 (2 ^ sh - 1))),
      .shift .ror .edx sh, .alu .or .eax (.reg .edx)]
  else []) : List Instr) ++
  ([.store (sc (o + 4 * j)) .eax] : List Instr)

theorem shrWords_eq (n o sh : Nat) : shrWords n o sh = (List.range (2 * n)).flatMap (shrStep n o sh) := rfl

/-- Word `j` of `[o]` shifted right by `sh`, from the words of `m`. -/
def shrWord32 (m : Mem) (base : Addr) (N o sh j : Nat) : BitVec 32 :=
  if j + 1 < N then (m.readW (off base (o + 4 * j)) 32 >>> sh) |||
    (m.readW (off base (o + 4 * (j + 1))) 32 &&& BitVec.ofNat 32 (2 ^ sh - 1)).rotateRight sh
  else m.readW (off base (o + 4 * j)) 32 >>> sh

theorem shrSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (hsh : 1 ≤ sh) (hsh' : sh < 32) : ∀ k, k ≤ 2 * n →
    WP isa (.block ((List.range k).flatMap (shrStep n o sh))) s fun s' =>
      (∀ j < k, s'.mem.readW (off base (o + 4 * j)) 32 = shrWord32 s.mem base (2 * n) o sh j) ∧
      Keeps [.eax, .edx] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (shrSteps_ok hs ho hsh hsh' k (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    have hw : s₁.mem.readW (off base (o + 4 * k)) 32 = s.mem.readW (off base (o + 4 * k)) 32 :=
      BitVec.eq_of_toNat_eq (O₁.w32 (by omega) (by omega))
    rw [shrStep, List.append_assoc, List.cons_append, List.cons_append]
    refine wp_movS (readSrc_sc hs₁ (d := o + 4 * k) (by omega)) fun s₂ u₂ _ => ?_
    refine wp_shr ⟨hsh, by omega⟩ fun s₃ u₃ _ => ?_
    have k₃ : Keeps [.eax, .edx] s₁ s₃ := (u₂.keeps.trans u₃.keeps).mono (by simp)
    have hs₃ := hs₁.of_keeps k₃ (by decide)
    have hm₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
    have v₃ : s₃.gpr .eax = s₁.mem.readW (off base (o + 4 * k)) 32 >>> sh := by rw [u₃.gpr, u₂.gpr]
    have step : ∀ (t : State), Keeps [.eax, .edx] s₃ t → t.mem = s₁.mem →
        t.gpr .eax = shrWord32 s.mem base (2 * n) o sh k →
        WP isa (.block [.store (sc (o + 4 * k)) .eax]) t (fun s' =>
          (∀ j < k + 1, s'.mem.readW (off base (o + 4 * j)) 32 = shrWord32 s.mem base (2 * n) o sh j) ∧
          Keeps [.eax, .edx] s s' ∧ Outside base o (4 * (k + 1)) s.mem s'.mem) := fun t kt mt vt => by
      have hst := hs₃.of_keeps kt (by decide)
      refine wp_storeS (hst.ea (d := o + 4 * k) (by omega)) (hst.write (d := o + 4 * k) (n := 4) (by omega))
        fun s₄ m₄ => WP.block_nil ?_
      have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₄.mem := by
        rw [m₄.mem, mt]; exact writeW32_outside _ _ _ (by omega)
      refine ⟨fun j hj => ?_, k₁.trans (k₃.trans (kt.trans (m₄.keeps [.eax, .edx]))),
        (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
      rcases Nat.lt_or_ge j k with h | h
      · exact (BitVec.eq_of_toNat_eq (O₂.w32 (by omega) (by omega))).trans (e₁ j h)
      · obtain rfl : j = k := by omega
        rw [m₄.mem, Mem.readW_writeW_self32, vt]
    by_cases hc : k + 1 < 2 * n
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), List.cons_append]
      have hw' : s₁.mem.readW (off base (o + 4 * (k + 1))) 32 = s.mem.readW (off base (o + 4 * (k + 1))) 32 :=
        BitVec.eq_of_toNat_eq (O₁.w32 (by omega) (by omega))
      refine wp_movS (readSrc_sc hs₃ (d := o + 4 * (k + 1)) (by omega)) fun s₄ u₄ _ => ?_
      refine wp_logicS (.inl rfl) rfl fun s₅ u₅ => ?_
      refine wp_ror ⟨hsh, by omega⟩ fun s₆ u₆ => ?_
      refine wp_orS rfl fun s₇ u₇ => ?_
      refine step s₇ ((u₄.keeps.mono (by simp)).trans ((u₅.keeps.mono (by simp)).trans
        ((u₆.keeps.mono (by simp)).trans (u₇.keeps.mono (by simp)))))
        (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, hm₃]) ?_
      rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), v₃, u₆.gpr, u₅.gpr,
        u₄.gpr, hm₃, hw, hw', shrWord32, ite_eq_left_of_eq_true _ _ (eq_true hc),
        ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), List.nil_append]
      refine step s₃ (Keeps.refl _ _) hm₃ ?_
      rw [v₃, hw, shrWord32, ite_eq_right_of_eq_false _ _ (eq_false hc)]

/-- `[o] = [o] >> sh`, `n` words, for `0 < sh < 32`. -/
theorem shrWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (hsh : 1 ≤ sh) (hsh' : sh < 32) :
    WP isa (.block (shrWords n o sh)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base o n >>> sh ∧
      Keeps [.eax, .edx] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [shrWords_eq]
  refine WP.mono (shrSteps_ok hs ho hsh hsh' (2 * n) (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, by rw [show 8 * n = 4 * (2 * n) by omega]; exact O⟩
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact val32_shr _ _ _ _ _ _ (by omega) hsh' fun j hj => e j hj

/-! ## Stores -/

/-- A whole word of `storeBytes`. -/
def stStepW (len : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (a + 4 * j))), .alu .and .eax (.reg .ecx), .bswap .eax,
    .store (at_ dst (d + (len - 4 * (j + 1)))) .eax]

/-- Byte `i` of a word of `t` bytes in `eax`. -/
def stByte (t : Nat) (dst : Reg) (d i : Nat) : List Instr :=
  ([.mov .edx (.reg .eax)] : List Instr) ++ ((if t - 1 - i = 0 then [] else [.shift .shr .edx (8 * (t - 1 - i))]) : List Instr) ++
    ([.store8 (at_ dst (d + i)) .dl] : List Instr)

/-- A word of `t` bytes. -/
def stTop (t : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.mov .eax (.mem (sc (a + 4 * j))), .alu .and .eax (.reg .ecx)] ++ (List.range t).flatMap (stByte t dst d)

theorem storeBytes_eq (len n : Nat) (dst : Reg) (d a : Nat) :
    storeBytes len n dst d a = (List.range (2 * n)).flatMap fun j =>
      if 4 * (j + 1) ≤ len then stStepW len dst d a j
      else if 4 * j < len then stTop (len - 4 * j) dst d a j else [] := rfl

theorem stSteps_wordsL {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len d a : Nat}
    {dst : Reg} (hdst : dst ≠ .eax) {c : Bool} (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0))
    {k : Nat} (ha : a + 4 * k ≤ size) (hlen : 4 * k ≤ len) (hq : (s.gpr dst).toNat + d + len ≤ 2 ^ 32)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 4 * k⟩ ⟨(s.gpr dst).setWidth 64 + BitVec.ofNat 64 d, len⟩) :
    ∀ k', k' ≤ k →
    WP isa (.block ((List.range k').flatMap (stStepW len dst d a))) s fun s' =>
      (∀ j < k', s'.mem.readW ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 =
        byteRev32 (s.mem.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0))) ∧
      Keeps [.eax] s s' ∧
      Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) (len - 4 * k') (4 * k') s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k' + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (stSteps_wordsL hs hdst hc ha hlen hq hw hd k' (by omega))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hs₁ := hs.of_keeps k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.1 _ (by simpa using hdst)
    have hc₁ : s₁.gpr .ecx = (if c then BitVec.allOnes 32 else 0) := by rw [k₁.1 _ (by decide), hc]
    have hqa : (s.gpr dst).setWidth 64 + BitVec.ofNat 64 (d + (len - 4 * (k' + 1))) =
        (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 4 * (k' + 1)) :=
      (Offset.add_add _ _ _).symm
    have hword : s₁.mem.readW (off base (a + 4 * k')) 32 = s.mem.readW (off base (a + 4 * k')) 32 := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 4 * k')) 32 = s.mem.readW (base + BitVec.ofNat 64 (a + 4 * k')) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    rw [stStepW]
    refine wp_movS (readSrc_sc hs₁ (d := a + 4 * k') (by omega)) fun s₂ u₂ _ => ?_
    refine wp_logicS (.inl rfl) rfl fun s₃ u₃ => ?_
    refine wp_bswap fun s₄ u₄ => ?_
    have k₄ : Keeps [.eax] s₁ s₄ := (u₂.keeps.trans u₃.keeps).trans u₄.keeps
    have hq₄ : s₄.gpr dst = s.gpr dst := by rw [k₄.1 _ (by simpa using hdst), hq₁]
    have ha₄ : s₄.ea (at_ dst (d + (len - 4 * (k' + 1)))) =
        (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 4 * (k' + 1)) := by
      rw [ea_ptr s₄ (by rw [hq₄]; omega), hq₄, hqa]
    have hw₄ : InRegions s₄.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d +
        BitVec.ofNat 64 (len - 4 * (k' + 1))) 4 := by
      rw [k₄.2.2, k₁.2.2]; exact hw _ _ (by omega)
    refine wp_storeS ha₄ hw₄ fun s₅ m₅ => WP.block_nil ?_
    have v₄ : s₄.gpr .eax = byteRev32 (s.mem.readW (off base (a + 4 * k')) 32 &&&
        (if c then BitVec.allOnes 32 else 0)) := by
      rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), hc₁, hword, bswap_eq]
      simp only [ite_true]
    have mem₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have O₂ : Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) (len - 4 * (k' + 1)) 4 s₁.mem s₅.mem := by
      rw [m₅.mem, mem₄]; exact writeW32_outside _ _ _ (by omega)
    refine ⟨fun j hj => ?_, k₁.trans (k₄.trans (m₅.keeps _)),
      (O₁.mono (by omega) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k' with h | h
    · rw [m₅.mem, mem₄, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
        e₁ j h]
    · obtain rfl : j = k' := by omega
      rw [m₅.mem, Mem.readW_writeW_self32, v₄]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov BYTE PTR [m], r`. -/
theorem wp_store8' {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) })
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

theorem byte_shift32 (v : BitVec 32) (k : Nat) : (v >>> k).setWidth 8 = BitVec.ofNat 8 (v.toNat >>> k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]

theorem stByte_ok {s : State} {v : BitVec 32} (ha : s.gpr .eax = v) {dst : Reg} (hdst : dst ≠ .edx)
    {t d i : Nat} (hi : i < t) (ht : t ≤ 4) (hq : (s.gpr dst).toNat + d + t ≤ 2 ^ 32)
    (hw : InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stByte t dst d i)) s fun s' =>
      s'.mem = s.mem.writeW ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧ Keeps [.edx] s s' := by
  have hqa : (s.gpr dst).setWidth 64 + BitVec.ofNat 64 (d + i) =
      (s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i := (Offset.add_add _ _ _).symm
  rw [stByte, List.cons_append]
  refine wp_mov fun s₁ u₁ => ?_
  have hd₁ : s₁.gpr dst = s.gpr dst := u₁.other _ hdst
  by_cases h0 : t - 1 - i = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), List.nil_append]
    refine wp_store8' (ea_ptr s₁ (by rw [hd₁]; omega)) (by rw [hd₁, hqa, u₁.wr]; exact hw) fun s₂ m₂ => WP.block_nil ?_
    refine ⟨?_, u₁.keeps.trans (m₂.keeps _)⟩
    rw [m₂.mem, u₁.mem, hd₁, hqa, show Reg8.dl.reg = .edx from rfl, u₁.gpr, ha, h0, Nat.mul_zero,
      Nat.shiftRight_zero]
    refine congrArg _ (BitVec.eq_of_toNat_eq ?_)
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), List.nil_append]
    show WP isa (.block (.shift .shr .edx (8 * (t - 1 - i)) :: [.store8 (at_ dst (d + i)) .dl])) s₁ _
    refine wp_shr ⟨by omega, by omega⟩ fun s₂ u₂ _ => ?_
    have hd₂ : s₂.gpr dst = s.gpr dst := by rw [u₂.other _ hdst, hd₁]
    refine wp_store8' (ea_ptr s₂ (by rw [hd₂]; omega)) (by rw [hd₂, hqa, u₂.wr, u₁.wr]; exact hw)
      fun s₃ m₃ => WP.block_nil ?_
    refine ⟨?_, (u₁.keeps.trans u₂.keeps).trans (m₃.keeps _)⟩
    rw [m₃.mem, u₂.mem, u₁.mem, hd₂, hqa, show Reg8.dl.reg = .edx from rfl, u₂.gpr, u₁.gpr, ha, byte_shift32]

theorem stBytes_ok {s : State} {v : BitVec 32} (ha : s.gpr .eax = v) {dst : Reg} (hdst : dst ≠ .edx)
    (hdst' : dst ≠ .eax) {t d : Nat} (ht : t ≤ 4) (hq : (s.gpr dst).toNat + d + t ≤ 2 ^ 32)
    (hw : ∀ i < t, InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    ∀ i', i' ≤ t →
    WP isa (.block ((List.range i').flatMap (stByte t dst d))) s fun s' =>
      (∀ i < i', s'.mem ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧
      Keeps [.edx] s s' ∧ Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) 0 i' s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Keeps.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | i' + 1, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (stBytes_ok ha hdst hdst' ht hq hw i' (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.1 _ (by simpa using hdst)
    refine WP.mono (stByte_ok (s := s₁) (v := v) (by rw [k₁.1 _ (by decide), ha]) hdst (t := t) (d := d)
      (i := i') (by omega) ht (by rw [hq₁]; exact hq) (by rw [k₁.2.2, hq₁]; exact hw i' (by omega)))
      fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [hq₁] at m₂
    have hb : ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d).toNat + t ≤ 2 ^ 64 := by
      rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := (s.gpr dst).isLt
      omega
    have O₂ : Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) i' 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega)
    refine ⟨fun i hi' => ?_, k₁.trans k₂, (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge i i' with h | h
    · rw [O₂ _ (by rw [ofs_off0 _ (by omega)]; omega), e₁ i h]
    · obtain rfl : i = i' := by omega
      rw [m₂, writeW8_self]

theorem stTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst : Reg}
    (hdst : dst ≠ .eax) (hdst' : dst ≠ .edx) {c : Bool} (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0))
    {t d a j : Nat} (ha : a + 4 * (j + 1) ≤ size) (ht : t ≤ 4) (hq : (s.gpr dst).toNat + d + t ≤ 2 ^ 32)
    (hw : ∀ i < t, InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stTop t dst d a j)) s fun s' =>
      (∀ i < t, s'.mem ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 ((s.mem.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0)).toNat >>>
          (8 * (t - 1 - i)))) ∧
      Keeps [.eax, .edx] s s' ∧ Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) 0 t s.mem s'.mem := by
  rw [stTop, List.cons_append, List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc hs (d := a + 4 * j) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  have k₂ : Keeps [.eax] s s₂ := u₁.keeps.trans u₂.keeps
  have hq₂ : s₂.gpr dst = s.gpr dst := k₂.1 _ (by simpa using hdst)
  have v₂ : s₂.gpr .eax = s.mem.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hc]; simp only [ite_true]
  refine WP.mono (stBytes_ok v₂ hdst' hdst ht (by rw [hq₂]; exact hq)
    (fun i hi => by rw [k₂.2.2, hq₂]; exact hw i hi) t (Nat.le_refl _)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hq₂] at e₃ O₃
  rw [u₂.mem, u₁.mem] at O₃
  exact ⟨e₃, (k₂.mono (by simp)).trans (k₃.mono (by simp)), O₃⟩

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} : ∀ (k : Nat), (∀ j < k, f j = g j) →
    ((List.range k).flatMap f : List α) = (List.range k).flatMap g
  | 0, _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr k fun j hj => h j (by omega),
      List.flatMap_singleton, List.flatMap_singleton, h k (by omega)]

/-- The `len` bytes at `dst + d` (`4 ≤ len ≤ 8 n`) are `[a]` big-endian if
the mask `ecx` is all ones (`c`), zeros if it is zero. -/
theorem storeBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n d a : Nat}
    {dst : Reg} (hdst : dst ≠ .eax) (hdst' : dst ≠ .edx) (c : Bool)
    (hc : s.gpr .ecx = (if c then BitVec.allOnes 32 else 0)) (ha : a + 8 * n ≤ size) (h4 : 4 ≤ len)
    (hlen : len ≤ 8 * n) (hq : (s.gpr dst).toNat + d + len ≤ 2 ^ 32)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨(s.gpr dst).setWidth 64 + BitVec.ofNat 64 d, len⟩) :
    WP isa (.block (storeBytes len n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) len =
        (if c then Spec.Weierstrass.toBytes len (wordsVal s.mem base a n) else List.replicate len 0) ∧
      Keeps [.eax, .edx] s s' ∧ Outside ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d) 0 len s.mem s'.mem := by
  have hn := hs.nowrap
  obtain ⟨K, hK⟩ : ∃ K, K = len / 4 := ⟨_, rfl⟩
  have hKn : K ≤ 2 * n := by omega
  rw [storeBytes_eq, show 2 * n = K + (2 * n - K) by omega, List.range_add, List.flatMap_append,
    flatMap_range_congr (g := stStepW len dst d a) K fun j hj => ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
    List.flatMap_map]
  have hsub : Region.Sub ⟨off base a, 4 * K⟩ ⟨off base a, 8 * n⟩ := by
    have := Offset.sub_base (off base a) (d := 0) (n := 4 * K) (k := 8 * n) (by omega)
    rwa [show off base a + BitVec.ofNat 64 0 = off base a from BitVec.add_zero _] at this
  refine WP.block_append (WP.mono (stSteps_wordsL hs hdst hc (k := K) (by omega) (by omega) hq hw
    (hd.sub_left hsub) K (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps k₁ (by decide)
  have hq₁ : s₁.gpr dst = s.gpr dst := k₁.1 _ (by simpa using hdst)
  have hc₁ : s₁.gpr .ecx = (if c then BitVec.allOnes 32 else 0) := by rw [k₁.1 _ (by decide), hc]
  have hb : ((s.gpr dst).setWidth 64 + BitVec.ofNat 64 d).toNat + len ≤ 2 ^ 64 := by
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := (s.gpr dst).isLt
    omega
  by_cases hr : len % 4 = 0
  · have hnil : (List.range (2 * n - K)).flatMap (fun i =>
        if 4 * (K + i + 1) ≤ len then stStepW len dst d a (K + i)
        else if 4 * (K + i) < len then stTop (len - 4 * (K + i)) dst d a (K + i) else []) = [] :=
      List.flatMap_eq_nil_iff.mpr fun i _ => by
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    rw [hnil]
    refine WP.block_nil ⟨?_, k₁.mono (by simp), ?_⟩
    · rw [wordsVal_eq_val32]
      refine bytesAt_eq_toBytes_len32 _ _ _ _ c (N := 2 * n) (by omega) (fun j hj hj4 => ?_)
        fun k _ hk1 hk2 => absurd hk2 (by omega)
      have hjK : j < K := by omega
      exact e₁ j hjK
    · rw [show len - 4 * K = 0 by omega, show 4 * K = len by omega] at O₁; exact O₁
  · have hm : 2 * n - K = (2 * n - K - 1) + 1 := by omega
    have htop : (List.range (2 * n - K)).flatMap (fun i =>
        if 4 * (K + i + 1) ≤ len then stStepW len dst d a (K + i)
        else if 4 * (K + i) < len then stTop (len - 4 * (K + i)) dst d a (K + i) else []) =
        stTop (len - 4 * K) dst d a K := by
      rw [hm, List.range_succ_eq_map, List.flatMap_cons, Nat.add_zero,
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
        List.flatMap_eq_nil_iff.mpr (fun i hi => by
          simp only [List.mem_map] at hi
          obtain ⟨i', _, rfl⟩ := hi
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]),
        List.append_nil, Nat.add_zero]
    rw [htop]
    have hword : s₁.mem.readW (off base (a + 4 * K)) 32 = s.mem.readW (off base (a + 4 * K)) 32 := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 4 * K)) 32 = s.mem.readW (base + BitVec.ofNat 64 (a + 4 * K)) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega)) hd (by omega)
        (by omega) (by omega)
    refine WP.mono (stTop_ok hs₁ hdst hdst' hc₁ (t := len - 4 * K) (d := d) (a := a) (j := K) (by omega) (by omega)
      (by rw [hq₁]; omega) (fun i hi => by rw [k₁.2.2, hq₁]; exact hw _ _ (by omega))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    rw [hq₁, hword] at e₂
    rw [hq₁] at O₂
    refine ⟨?_, (k₁.mono (by simp)).trans k₂,
      (O₁.mono (Nat.zero_le _) (by omega)).trans (O₂.mono (Nat.le_refl _) (by omega))⟩
    rw [wordsVal_eq_val32]
    refine bytesAt_eq_toBytes_len32 _ _ _ _ c (N := 2 * n) (by omega) (fun j hj hj4 => ?_) fun k _ hk1 hk2 => ?_
    · refine Eq.trans ?_ (e₁ j (by omega))
      exact readW32_keep fun i hi => O₂ _ (by rw [ofs_off0 _ (by omega)]; omega)
    · obtain rfl : k = K := by omega
      exact e₂

end VG.Proof.Weierstrass.X86
