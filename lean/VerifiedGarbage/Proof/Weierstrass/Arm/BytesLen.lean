import VerifiedGarbage.Proof.Weierstrass.Arm.Bytes
import VerifiedGarbage.Proof.Weierstrass.BytesLen32

/-!
# Short Weierstrass curves on 32-bit ARM: numbers of `len` bytes

For encodings that are not whole words (P-521's 66 bytes in the eighteen
32-bit words of nine 64-bit ones): `loadBytes len n o src` reads the `len`
bytes at `src`, big-endian, into `[o]` (`loadBytes_ok`), a word of fewer
bytes from the first four shifted right and the words past `len` zero;
`shrWords n o sh` shifts `[o]` right by `sh` bits in place (`shrWords_ok`);
and `storeBytes len n dst d a` writes `[a]` masked with `r10` to the `len`
bytes at `dst + d` (`storeBytes_ok`), a word of fewer bytes a byte at a
time, as on x86 (`Proof/Weierstrass/X86/BytesLen.lean`).
-/

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
  VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_strb wp_dp wp_mov op2_reg op2_imm op2_lsr op2_lsl
  dpVal)

/-! ## Loads -/

/-- One word of `loadBytes`. -/
def ldStepL (len o : Nat) (src : Reg) (j : Nat) : List Instr :=
  if 4 * (j + 1) ≤ len then
    [.ldr .r4 src (len - 4 * (j + 1)), .rev .r4 .r4, .str .r4 wb (o + 4 * j)]
  else if 4 * j < len then
    [.ldr .r4 src 0, .rev .r4 .r4, .mov .r4 (.shifted .r4 .lsr (8 * (4 * (j + 1) - len))),
      .str .r4 wb (o + 4 * j)]
  else [.mov .r4 (.imm 0), .str .r4 wb (o + 4 * j)]

theorem loadBytes_eq (len n o : Nat) (src : Reg) :
    loadBytes len n o src = (List.range (2 * n)).flatMap (ldStepL len o src) := rfl

theorem ldStepsL_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .r4) (ho : o + 8 * n ≤ size) (hp : (s.gpr src).toNat + len ≤ 2 ^ 32)
    (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (hr : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨State.addr (s.gpr src), len⟩ ⟨off base o, 8 * n⟩) : ∀ k, k ≤ 2 * n →
    WP isa (.block ((List.range k).flatMap (ldStepL len o src))) s fun s' =>
      (∀ j < k, w32 s'.mem base (o + 4 * j) = ldWord32 s.mem (State.addr (s.gpr src)) len j) ∧
      Rest [.r4] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    have hsm := hs.small
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (ldStepsL_ok hs hsrc ho hp h4 hlen hr hd k (by omega_arith))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    have hp₁ : s₁.gpr src = s.gpr src := k₁.gpr _ (by simpa using hsrc)
    have hkeep : ∀ d, d + 4 ≤ len → s₁.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 d) 32 =
        s.mem.readW (State.addr (s.gpr src) + BitVec.ofNat 64 d) 32 := fun d hd' =>
      readW32_keep fun i hi => keep_of_disjoint (O₁.mono (Nat.le_refl _) (by omega_arith)) hd (by omega_arith)
        (by omega_arith) (by omega_arith)
    -- The store of `r4` to word `k`, after the load.
    have fin : ∀ (t : State) (v : BitVec 32), Rest [.r4] s₁ t → t.mem = s₁.mem → t.gpr .r4 = v →
        v.toNat = ldWord32 s.mem (State.addr (s.gpr src)) len k →
        WP isa (.block [.str .r4 wb (o + 4 * k)]) t (fun s' =>
          (∀ j < k + 1, w32 s'.mem base (o + 4 * j) = ldWord32 s.mem (State.addr (s.gpr src)) len j) ∧
          Rest [.r4] s s' ∧ Outside base o (4 * (k + 1)) s.mem s'.mem) := fun t v kt mt vt ev => by
      have hst := hs₁.of_rest kt (by decide)
      refine wp_str (hs.off_lt (by omega_arith)) (hst.ea (d := o + 4 * k) (by omega_arith))
        (hst.write (d := o + 4 * k) (n := 4) (by omega_arith)) fun s₄ m₄ => WP.block_nil ?_
      have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₄.mem := by
        rw [m₄.mem, mt]; exact writeW32_outside _ _ _ (by omega_arith)
      refine ⟨fun j hj => ?_, k₁.trans (kt.trans (m₄.rest _)),
        (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
      rcases Nat.lt_or_ge j k with h | h
      · rw [O₂.w32 (by omega_arith) (by omega_arith), e₁ j h]
      · obtain rfl : j = k := by omega_arith
        rw [m₄.mem, mt, w32_write_self, vt, ev]
    by_cases hc1 : 4 * (k + 1) ≤ len
    · have ha₁ : State.addr (s₁.gpr src + BitVec.ofNat 32 (len - 4 * (k + 1))) =
          State.addr (s.gpr src) + BitVec.ofNat 64 (len - 4 * (k + 1)) := by
        rw [hp₁, addr_add (by omega_arith)]
      have hr₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 (len - 4 * (k + 1))) 4 := by
        rw [k₁.rd, k₁.wr]; exact hr _ (by omega_arith)
      rw [ldStepL, ite_eq_left_of_eq_true _ _ (eq_true hc1)]
      refine wp_ldr (by omega_arith) ha₁ hr₁ fun s₂ u₂ => ?_
      refine wp_rev fun s₃ u₃ => fin s₃ _ ((u₂.rest (by simp)).trans (u₃.rest (by simp)))
        (by rw [u₃.mem, u₂.mem]) rfl ?_
      rw [u₃.gpr, u₂.gpr, hkeep _ (by omega_arith), rev_eq, ldWord32, ite_eq_left_of_eq_true _ _ (eq_true hc1)]
    · by_cases hc2 : 4 * k < len
      · have ha₁ : State.addr (s₁.gpr src + BitVec.ofNat 32 0) = State.addr (s.gpr src) + BitVec.ofNat 64 0 := by
          rw [hp₁, addr_add (by omega_arith)]
        have hr₁ : InRegions (s₁.rd ++ s₁.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 0) 4 := by
          rw [k₁.rd, k₁.wr]; exact hr _ (by omega_arith)
        rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_left_of_eq_true _ _ (eq_true hc2)]
        refine wp_ldr (by omega_arith) ha₁ hr₁ fun s₂ u₂ => ?_
        refine wp_rev fun s₃ u₃ => ?_
        refine wp_mov (op2_lsr (n := 8 * (4 * (k + 1) - len)) ⟨by omega_arith, by omega_arith⟩) fun s₄ u₄ =>
          fin s₄ _ ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp))))
            (by rw [u₄.mem, u₃.mem, u₂.mem]) rfl ?_
        have h0 := hkeep 0 (by omega_arith)
        rw [BitVec.add_zero] at h0
        rw [u₄.gpr, u₃.gpr, u₂.gpr, BitVec.add_zero, h0, rev_eq, BitVec.toNat_ushiftRight, ldWord32,
          ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_left_of_eq_true _ _ (eq_true hc2)]
      · rw [ldStepL, ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_right_of_eq_false _ _ (eq_false hc2)]
        refine wp_mov (op2_imm (v := 0) (by decide)) fun s₂ u₂ =>
          fin s₂ 0 (u₂.rest (by simp)) u₂.mem u₂.gpr ?_
        rw [ldWord32, ite_eq_right_of_eq_false _ _ (eq_false hc1), ite_eq_right_of_eq_false _ _ (eq_false hc2)]
        rfl

/-- `[o] = ` the `len` bytes at `src`, big-endian (`4 ≤ len ≤ 8 n`). -/
theorem loadBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n o : Nat}
    {src : Reg} (hsrc : src ≠ .r4) (ho : o + 8 * n ≤ size) (hp : (s.gpr src).toNat + len ≤ 2 ^ 32)
    (h4 : 4 ≤ len) (hlen : len ≤ 8 * n)
    (hr : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) (State.addr (s.gpr src) + BitVec.ofNat 64 d) 4)
    (hd : Region.Disjoint ⟨State.addr (s.gpr src), len⟩ ⟨off base o, 8 * n⟩) :
    WP isa (.block (loadBytes len n o src)) s fun s' =>
      wordsVal s'.mem base o n =
        Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr src)) len) ∧
      Rest [.r4] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [loadBytes_eq]
  refine WP.mono (ldStepsL_ok hs hsrc ho hp h4 hlen hr hd (2 * n) (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, by rw [show 8 * n = 4 * (2 * n) by omega_arith]; exact O⟩
  rw [wordsVal_eq_val32]
  exact val32_eq_ofBytes_len _ _ _ _ o (2 * n) len h4 (by omega_arith) e

/-! ## Shifting right in place -/

/-- One word of `shrWords`. -/
def shrStep (n o sh j : Nat) : List Instr :=
  ([.ldr .r4 wb (o + 4 * j), .mov .r4 (.shifted .r4 .lsr sh)] : List Instr) ++
  ((if j + 1 < 2 * n then
    [.ldr .r5 wb (o + 4 * (j + 1)), .dp .orr .r4 .r4 (.shifted .r5 .lsl (32 - sh))]
  else []) : List Instr) ++
  ([.str .r4 wb (o + 4 * j)] : List Instr)

theorem shrWords_eq (n o sh : Nat) : shrWords n o sh = (List.range (2 * n)).flatMap (shrStep n o sh) := rfl

/-- A word shifted left by `32 - sh`: its low `sh` bits rotated to the top. -/
theorem shl_eq_rotateRight {sh : Nat} (h0 : 0 < sh) (h1 : sh < 32) (x : BitVec 32) :
    x <<< (32 - sh) = (x &&& BitVec.ofNat 32 (2 ^ sh - 1)).rotateRight sh := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt h1]
  by_cases hc : i < 32 - sh
  · simp only [hi, decide_true, hc, Bool.true_and, Bool.not_true, Bool.false_and,
      BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, ↓reduceIte]
    simp only [show ¬sh + i < sh by omega_arith, decide_false, Bool.and_false]
  · simp only [hi, decide_true, hc, decide_false, Bool.not_false, Bool.true_and,
      BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, ↓reduceIte]
    simp only [show i - (32 - sh) < 32 by omega_arith, show i - (32 - sh) < sh by omega_arith, decide_true,
      Bool.and_true]

/-- Word `j` of `[o]` shifted right by `sh`, from the words of `m`. -/
def shrWord32 (m : Mem) (base : Addr) (N o sh j : Nat) : BitVec 32 :=
  if j + 1 < N then (m.readW (off base (o + 4 * j)) 32 >>> sh) |||
    (m.readW (off base (o + 4 * (j + 1))) 32 &&& BitVec.ofNat 32 (2 ^ sh - 1)).rotateRight sh
  else m.readW (off base (o + 4 * j)) 32 >>> sh

theorem shrSteps_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (hsh : 1 ≤ sh) (hsh' : sh < 32) : ∀ k, k ≤ 2 * n →
    WP isa (.block ((List.range k).flatMap (shrStep n o sh))) s fun s' =>
      (∀ j < k, s'.mem.readW (off base (o + 4 * j)) 32 = shrWord32 s.mem base (2 * n) o sh j) ∧
      Rest [.r4, .r5] s s' ∧ Outside base o (4 * k) s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hnw := hs.nowrap
    have hsm := hs.small
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (shrSteps_ok hs ho hsh hsh' k (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    have hw : s₁.mem.readW (off base (o + 4 * k)) 32 = s.mem.readW (off base (o + 4 * k)) 32 :=
      BitVec.eq_of_toNat_eq (O₁.w32 (by omega_arith) (by omega_arith))
    rw [shrStep, List.append_assoc, List.cons_append, List.cons_append]
    refine wp_ldr (hs.off_lt (by omega_arith)) (hs₁.ea (d := o + 4 * k) (by omega_arith))
      (hs₁.read (d := o + 4 * k) (n := 4) (by omega_arith)) fun s₂ u₂ => ?_
    refine wp_mov (op2_lsr ⟨hsh, by omega_arith⟩) fun s₃ u₃ => ?_
    have k₃ : Rest [.r4, .r5] s₁ s₃ := (u₂.rest (by simp)).trans (u₃.rest (by simp))
    have hs₃ := hs₁.of_rest k₃ (by decide)
    have hm₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
    have v₃ : s₃.gpr .r4 = s₁.mem.readW (off base (o + 4 * k)) 32 >>> sh := by rw [u₃.gpr, u₂.gpr]
    have step : ∀ (t : State), Rest [.r4, .r5] s₃ t → t.mem = s₁.mem →
        t.gpr .r4 = shrWord32 s.mem base (2 * n) o sh k →
        WP isa (.block [.str .r4 wb (o + 4 * k)]) t (fun s' =>
          (∀ j < k + 1, s'.mem.readW (off base (o + 4 * j)) 32 = shrWord32 s.mem base (2 * n) o sh j) ∧
          Rest [.r4, .r5] s s' ∧ Outside base o (4 * (k + 1)) s.mem s'.mem) := fun t kt mt vt => by
      have hst := hs₃.of_rest kt (by decide)
      refine wp_str (hs.off_lt (by omega_arith)) (hst.ea (d := o + 4 * k) (by omega_arith))
        (hst.write (d := o + 4 * k) (n := 4) (by omega_arith)) fun s₄ m₄ => WP.block_nil ?_
      have O₂ : Outside base (o + 4 * k) 4 s₁.mem s₄.mem := by
        rw [m₄.mem, mt]; exact writeW32_outside _ _ _ (by omega_arith)
      refine ⟨fun j hj => ?_, k₁.trans (k₃.trans (kt.trans (m₄.rest _))),
        (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
      rcases Nat.lt_or_ge j k with h | h
      · exact (BitVec.eq_of_toNat_eq (O₂.w32 (by omega_arith) (by omega_arith))).trans (e₁ j h)
      · obtain rfl : j = k := by omega_arith
        rw [m₄.mem, Mem.readW_writeW_self32, vt]
    by_cases hc : k + 1 < 2 * n
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), List.cons_append]
      have hw' : s₁.mem.readW (off base (o + 4 * (k + 1))) 32 = s.mem.readW (off base (o + 4 * (k + 1))) 32 :=
        BitVec.eq_of_toNat_eq (O₁.w32 (by omega_arith) (by omega_arith))
      refine wp_ldr (hs.off_lt (by omega_arith)) (hs₃.ea (d := o + 4 * (k + 1)) (by omega_arith))
        (hs₃.read (d := o + 4 * (k + 1)) (n := 4) (by omega_arith)) fun s₄ u₄ => ?_
      refine wp_dp (op2_lsl (n := 32 - sh) ⟨by omega_arith, by omega_arith⟩) fun s₅ u₅ => ?_
      refine step s₅ ((u₄.rest (by simp)).trans (u₅.rest (by simp))) (by rw [u₅.mem, u₄.mem, hm₃]) ?_
      rw [u₅.gpr, dpVal, u₄.other _ (by decide), v₃, u₄.gpr, hm₃, hw, hw', shl_eq_rotateRight (by omega_arith) hsh',
        shrWord32, ite_eq_left_of_eq_true _ _ (eq_true hc)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), List.nil_append]
      refine step s₃ (Rest.refl _ _) hm₃ ?_
      rw [v₃, hw, shrWord32, ite_eq_right_of_eq_false _ _ (eq_false hc)]

/-- `[o] = [o] >> sh`, `n` words, for `0 < sh < 32`. -/
theorem shrWords_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n o sh : Nat}
    (ho : o + 8 * n ≤ size) (hsh : 1 ≤ sh) (hsh' : sh < 32) :
    WP isa (.block (shrWords n o sh)) s fun s' =>
      wordsVal s'.mem base o n = wordsVal s.mem base o n >>> sh ∧
      Rest [.r4, .r5] s s' ∧ Outside base o (8 * n) s.mem s'.mem := by
  rw [shrWords_eq]
  refine WP.mono (shrSteps_ok hs ho hsh hsh' (2 * n) (Nat.le_refl _)) fun s' ⟨e, k, O⟩ =>
    ⟨?_, k, by rw [show 8 * n = 4 * (2 * n) by omega_arith]; exact O⟩
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact val32_shr _ _ _ _ _ _ (by omega_arith) hsh' fun j hj => e j hj

/-! ## Stores -/

/-- A whole word of `storeBytes`. -/
def stStepW (len : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.ldr .r4 wb (a + 4 * j), .dp .and .r4 .r4 (.reg .r10), .rev .r4 .r4, .str .r4 dst (d + (len - 4 * (j + 1)))]

/-- Byte `i` of a word of `t` bytes in `r4`. -/
def stByte (t : Nat) (dst : Reg) (d i : Nat) : List Instr :=
  if t - 1 - i = 0 then [.strb .r4 dst (d + i)]
  else [.mov .r5 (.shifted .r4 .lsr (8 * (t - 1 - i))), .strb .r5 dst (d + i)]

/-- A word of `t` bytes. -/
def stTop (t : Nat) (dst : Reg) (d a j : Nat) : List Instr :=
  [.ldr .r4 wb (a + 4 * j), .dp .and .r4 .r4 (.reg .r10)] ++ (List.range t).flatMap (stByte t dst d)

theorem storeBytes_eq (len n : Nat) (dst : Reg) (d a : Nat) :
    storeBytes len n dst d a = (List.range (2 * n)).flatMap fun j =>
      if 4 * (j + 1) ≤ len then stStepW len dst d a j
      else if 4 * j < len then stTop (len - 4 * j) dst d a j else [] := rfl

theorem stSteps_wordsL {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len d a : Nat}
    {dst : Reg} (hdst : dst ≠ .r4) {c : Bool} (hc : s.gpr .r10 = (if c then BitVec.allOnes 32 else 0))
    {k : Nat} (ha : a + 4 * k ≤ size) (hlen : 4 * k ≤ len) (hq : (s.gpr dst).toNat + d + len ≤ 2 ^ 32)
    (hd4 : d + len ≤ 4096)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 4 * k⟩ ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 d, len⟩) :
    ∀ k', k' ≤ k →
    WP isa (.block ((List.range k').flatMap (stStepW len dst d a))) s fun s' =>
      (∀ j < k', s'.mem.readW (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 4 * (j + 1))) 32 =
        byteRev32 (s.mem.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0))) ∧
      Rest [.r4] s s' ∧
      Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) (len - 4 * k') (4 * k') s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k' + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (stSteps_wordsL hs hdst hc ha hlen hq hd4 hw hd k' (by omega_arith))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    have hc₁ : s₁.gpr .r10 = (if c then BitVec.allOnes 32 else 0) := by rw [k₁.gpr _ (by decide), hc]
    have hword : s₁.mem.readW (off base (a + 4 * k')) 32 = s.mem.readW (off base (a + 4 * k')) 32 := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 4 * k')) 32 = s.mem.readW (base + BitVec.ofNat 64 (a + 4 * k')) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega_arith)) hd (by omega_arith)
        (by omega_arith) (by omega_arith)
    rw [stStepW]
    refine wp_ldr (hs.off_lt (by omega_arith)) (hs₁.ea (d := a + 4 * k') (by omega_arith))
      (hs₁.read (d := a + 4 * k') (n := 4) (by omega_arith)) fun s₂ u₂ => ?_
    refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
    refine wp_rev fun s₄ u₄ => ?_
    have k₄ : Rest [.r4] s₁ s₄ := (u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))
    have hq₄ : s₄.gpr dst = s.gpr dst := by rw [k₄.gpr _ (by simpa using hdst), hq₁]
    have ha₄ : State.addr (s₄.gpr dst + BitVec.ofNat 32 (d + (len - 4 * (k' + 1)))) =
        State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 (len - 4 * (k' + 1)) := by
      rw [hq₄, addr_add (by omega_arith), Offset.add_add]
    have hw₄ : InRegions s₄.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d +
        BitVec.ofNat 64 (len - 4 * (k' + 1))) 4 := by
      rw [k₄.wr, k₁.wr]; exact hw _ _ (by omega_arith)
    refine wp_str (by omega_arith) ha₄ hw₄ fun s₅ m₅ => WP.block_nil ?_
    have v₄ : s₄.gpr .r4 = byteRev32 (s.mem.readW (off base (a + 4 * k')) 32 &&&
        (if c then BitVec.allOnes 32 else 0)) := by
      rw [u₄.gpr, u₃.gpr, dpVal, u₂.gpr, u₂.other _ (by decide), hc₁, hword, rev_eq]
    have mem₄ : s₄.mem = s₁.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have O₂ : Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) (len - 4 * (k' + 1)) 4 s₁.mem s₅.mem := by
      rw [m₅.mem, mem₄]; exact writeW32_outside _ _ _ (by omega_arith)
    refine ⟨fun j hj => ?_, k₁.trans (k₄.trans (m₅.rest _)),
      (O₁.mono (by omega_arith) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge j k' with h | h
    · rw [m₅.mem, mem₄, Mem.readW_writeW_sep (Offset.sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        e₁ j h]
    · obtain rfl : j = k' := by omega_arith
      rw [m₅.mem, Mem.readW_writeW_self32, v₄]

theorem byte_shift32 (v : BitVec 32) (k : Nat) : (v >>> k).setWidth 8 = BitVec.ofNat 8 (v.toNat >>> k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]

theorem stByte_ok {s : State} {v : BitVec 32} (ha : s.gpr .r4 = v) {dst : Reg} (hdst : dst ≠ .r5)
    {t d i : Nat} (hi : i < t) (ht : t ≤ 4) (hq : (s.gpr dst).toNat + d + t ≤ 2 ^ 32) (hd4 : d + t ≤ 4096)
    (hw : InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stByte t dst d i)) s fun s' =>
      s'.mem = s.mem.writeW (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 i)
        (BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧ Rest [.r5] s s' := by
  have hqa : State.addr (s.gpr dst + BitVec.ofNat 32 (d + i)) =
      State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 i := by
    rw [addr_add (by omega_arith), Offset.add_add]
  rw [stByte]
  by_cases h0 : t - 1 - i = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
    refine wp_strb (by omega_arith) hqa hw fun s₁ m₁ => WP.block_nil ⟨?_, m₁.rest _⟩
    rw [m₁.mem, ha, h0, Nat.mul_zero, Nat.shiftRight_zero]
    refine congrArg _ (BitVec.eq_of_toNat_eq ?_)
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    refine wp_mov (op2_lsr (n := 8 * (t - 1 - i)) ⟨by omega_arith, by omega_arith⟩) fun s₁ u₁ => ?_
    have hd₁ : s₁.gpr dst = s.gpr dst := u₁.other _ hdst
    refine wp_strb (a := State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 i) (by omega_arith)
      (by rw [hd₁, hqa]) (by rw [u₁.wr]; exact hw) fun s₂ m₂ =>
      WP.block_nil ⟨?_, (u₁.rest (by simp)).trans (m₂.rest _)⟩
    rw [m₂.mem, u₁.mem, u₁.gpr, ha, byte_shift32]

theorem stBytes_ok {s : State} {v : BitVec 32} (ha : s.gpr .r4 = v) {dst : Reg} (hdst : dst ≠ .r5)
    (hdst' : dst ≠ .r4) {t d : Nat} (ht : t ≤ 4) (hq : (s.gpr dst).toNat + d + t ≤ 2 ^ 32) (hd4 : d + t ≤ 4096)
    (hw : ∀ i < t, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    ∀ i', i' ≤ t →
    WP isa (.block ((List.range i').flatMap (stByte t dst d))) s fun s' =>
      (∀ i < i', s'.mem (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 (v.toNat >>> (8 * (t - 1 - i)))) ∧
      Rest [.r5] s s' ∧ Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) 0 i' s.mem s'.mem
  | 0, _ => WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _,
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | i' + 1, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (stBytes_ok ha hdst hdst' ht hq hd4 hw i' (by omega_arith))
      fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
    refine WP.mono (stByte_ok (s := s₁) (v := v) (by rw [k₁.gpr _ (by decide), ha]) hdst (t := t) (d := d)
      (i := i') (by omega_arith) ht (by rw [hq₁]; exact hq) hd4 (by rw [k₁.wr, hq₁]; exact hw i' (by omega_arith)))
      fun s₂ ⟨m₂, k₂⟩ => ?_
    rw [hq₁] at m₂
    have hb : (State.addr (s.gpr dst) + BitVec.ofNat 64 d).toNat + t ≤ 2 ^ 64 := by
      rw [BitVec.toNat_add, VG.Proof.X25519.Arm.addr_toNat, BitVec.toNat_ofNat]
      have := (s.gpr dst).isLt
      omega_arith
    have O₂ : Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) i' 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega_arith)
    refine ⟨fun i hi' => ?_, k₁.trans k₂, (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    rcases Nat.lt_or_ge i i' with h | h
    · rw [O₂ _ (by rw [ofs_off0 _ (by omega_arith)]; omega_arith), e₁ i h]
    · obtain rfl : i = i' := by omega_arith
      rw [m₂, writeW8_self]

theorem stTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {dst : Reg}
    (hdst : dst ≠ .r4) (hdst' : dst ≠ .r5) {c : Bool} (hc : s.gpr .r10 = (if c then BitVec.allOnes 32 else 0))
    {t d a j : Nat} (ha : a + 4 * (j + 1) ≤ size) (ht : t ≤ 4) (hq : (s.gpr dst).toNat + d + t ≤ 2 ^ 32)
    (hd4 : d + t ≤ 4096)
    (hw : ∀ i < t, InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 i) 1) :
    WP isa (.block (stTop t dst d a j)) s fun s' =>
      (∀ i < t, s'.mem (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 i) =
        BitVec.ofNat 8 ((s.mem.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0)).toNat >>>
          (8 * (t - 1 - i)))) ∧
      Rest [.r4, .r5] s s' ∧ Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) 0 t s.mem s'.mem := by
  have hsm := hs.small
  rw [stTop, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ldr (hs.off_lt (by omega_arith)) (hs.ea (d := a + 4 * j) (by omega_arith))
    (hs.read (d := a + 4 * j) (n := 4) (by omega_arith)) fun s₁ u₁ => ?_
  refine wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  have k₂ : Rest [.r4] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have hq₂ : s₂.gpr dst = s.gpr dst := k₂.gpr _ (by simpa using hdst)
  have v₂ : s₂.gpr .r4 = s.mem.readW (off base (a + 4 * j)) 32 &&& (if c then BitVec.allOnes 32 else 0) := by
    rw [u₂.gpr, dpVal, u₁.gpr, u₁.other _ (by decide), hc]
  refine WP.mono (stBytes_ok v₂ hdst' hdst ht (by rw [hq₂]; exact hq) hd4
    (fun i hi => by rw [k₂.wr, hq₂]; exact hw i hi) t (Nat.le_refl _)) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hq₂] at e₃ O₃
  rw [u₂.mem, u₁.mem] at O₃
  exact ⟨e₃, (k₂.mono (by simp)).trans (k₃.mono (by simp)), O₃⟩

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} : ∀ (k : Nat), (∀ j < k, f j = g j) →
    ((List.range k).flatMap f : List α) = (List.range k).flatMap g
  | 0, _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr k fun j hj => h j (by omega_arith),
      List.flatMap_singleton, List.flatMap_singleton, h k (by omega_arith)]

/-- The `len` bytes at `dst + d` (`4 ≤ len ≤ 8 n`) are `[a]` big-endian if
the mask `r10` is all ones (`c`), zeros if it is zero. -/
theorem storeBytes_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {len n d a : Nat}
    {dst : Reg} (hdst : dst ≠ .r4) (hdst' : dst ≠ .r5) (c : Bool)
    (hc : s.gpr .r10 = (if c then BitVec.allOnes 32 else 0)) (ha : a + 8 * n ≤ size) (h4 : 4 ≤ len)
    (hlen : len ≤ 8 * n) (hq : (s.gpr dst).toNat + d + len ≤ 2 ^ 32) (hd4 : d + len ≤ 4096)
    (hw : ∀ e m, e + m ≤ len → InRegions s.wr (State.addr (s.gpr dst) + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m)
    (hd : Region.Disjoint ⟨off base a, 8 * n⟩ ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 d, len⟩) :
    WP isa (.block (storeBytes len n dst d a)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr (s.gpr dst) + BitVec.ofNat 64 d) len =
        (if c then Spec.Weierstrass.toBytes len (wordsVal s.mem base a n) else List.replicate len 0) ∧
      Rest [.r4, .r5] s s' ∧ Outside (State.addr (s.gpr dst) + BitVec.ofNat 64 d) 0 len s.mem s'.mem := by
  have hn := hs.nowrap
  obtain ⟨K, hK⟩ : ∃ K, K = len / 4 := ⟨_, rfl⟩
  have hKn : K ≤ 2 * n := by omega_arith
  rw [storeBytes_eq, show 2 * n = K + (2 * n - K) by omega_arith, List.range_add, List.flatMap_append,
    flatMap_range_congr (g := stStepW len dst d a) K fun j hj => ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
    List.flatMap_map]
  have hsub : Region.Sub ⟨off base a, 4 * K⟩ ⟨off base a, 8 * n⟩ := by
    have := Offset.sub_base (off base a) (d := 0) (n := 4 * K) (k := 8 * n) (by omega_arith)
    rwa [show off base a + BitVec.ofNat 64 0 = off base a from BitVec.add_zero _] at this
  refine VG.Proof.X25519.Arm.WP.append (stSteps_wordsL hs hdst hc (k := K) (by omega_arith) (by omega_arith) hq hd4 hw
    (hd.sub_left hsub) K (Nat.le_refl _)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  have hq₁ : s₁.gpr dst = s.gpr dst := k₁.gpr _ (by simpa using hdst)
  have hc₁ : s₁.gpr .r10 = (if c then BitVec.allOnes 32 else 0) := by rw [k₁.gpr _ (by decide), hc]
  have hb : (State.addr (s.gpr dst) + BitVec.ofNat 64 d).toNat + len ≤ 2 ^ 64 := by
    rw [BitVec.toNat_add, VG.Proof.X25519.Arm.addr_toNat, BitVec.toNat_ofNat]
    have := (s.gpr dst).isLt
    omega_arith
  by_cases hr : len % 4 = 0
  · have hnil : (List.range (2 * n - K)).flatMap (fun i =>
        if 4 * (K + i + 1) ≤ len then stStepW len dst d a (K + i)
        else if 4 * (K + i) < len then stTop (len - 4 * (K + i)) dst d a (K + i) else []) = [] :=
      List.flatMap_eq_nil_iff.mpr fun i _ => by
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
    rw [hnil]
    refine WP.block_nil ⟨?_, k₁.mono (by simp), ?_⟩
    · rw [wordsVal_eq_val32]
      refine bytesAt_eq_toBytes_len32 _ _ _ _ c (N := 2 * n) (by omega_arith) (fun j hj hj4 => ?_)
        fun k _ hk1 hk2 => absurd hk2 (by omega_arith)
      have hjK : j < K := by omega_arith
      exact e₁ j hjK
    · rw [show len - 4 * K = 0 by omega_arith, show 4 * K = len by omega_arith] at O₁; exact O₁
  · have hm : 2 * n - K = (2 * n - K - 1) + 1 := by omega_arith
    have htop : (List.range (2 * n - K)).flatMap (fun i =>
        if 4 * (K + i + 1) ≤ len then stStepW len dst d a (K + i)
        else if 4 * (K + i) < len then stTop (len - 4 * (K + i)) dst d a (K + i) else []) =
        stTop (len - 4 * K) dst d a K := by
      rw [hm, List.range_succ_eq_map, List.flatMap_cons, Nat.add_zero,
        ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith)),
        List.flatMap_eq_nil_iff.mpr (fun i hi => by
          simp only [List.mem_map] at hi
          obtain ⟨i', _, rfl⟩ := hi
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith)), ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]),
        List.append_nil, Nat.add_zero]
    rw [htop]
    have hword : s₁.mem.readW (off base (a + 4 * K)) 32 = s.mem.readW (off base (a + 4 * K)) 32 := by
      show s₁.mem.readW (base + BitVec.ofNat 64 (a + 4 * K)) 32 = s.mem.readW (base + BitVec.ofNat 64 (a + 4 * K)) 32
      rw [← Offset.add_add]
      exact readW32_keep fun i hi => keep_of_disjoint' (O₁.mono (Nat.zero_le _) (by omega_arith)) hd (by omega_arith)
        (by omega_arith) (by omega_arith)
    refine WP.mono (stTop_ok hs₁ hdst hdst' hc₁ (t := len - 4 * K) (d := d) (a := a) (j := K) (by omega_arith) (by omega_arith)
      (by rw [hq₁]; omega_arith) (by omega_arith) (fun i hi => by rw [k₁.wr, hq₁]; exact hw _ _ (by omega_arith)))
      fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
    rw [hq₁, hword] at e₂
    rw [hq₁] at O₂
    refine ⟨?_, (k₁.mono (by simp)).trans k₂,
      (O₁.mono (Nat.zero_le _) (by omega_arith)).trans (O₂.mono (Nat.le_refl _) (by omega_arith))⟩
    rw [wordsVal_eq_val32]
    refine bytesAt_eq_toBytes_len32 _ _ _ _ c (N := 2 * n) (by omega_arith) (fun j hj hj4 => ?_) fun k _ hk1 hk2 => ?_
    · refine Eq.trans ?_ (e₁ j (by omega_arith))
      exact readW32_keep fun i hi => O₂ _ (by rw [ofs_off0 _ (by omega_arith)]; omega_arith)
    · obtain rfl : k = K := by omega_arith
      exact e₂

end VG.Proof.Weierstrass.Arm
