import VerifiedGarbage.Proof.AesOcb.AArch64.PadTo
import VerifiedGarbage.Proof.Ocb.Bytes

/-!
# AES-OCB on AArch64: checking the tag and masking the data (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` ORs the XORs of the
first `tag_len` bytes of the received tag (at `W`) and the computed one (at
`W + t2O`) and leaves 1 at `W` if the OR is 0, else 0 (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − ok`: the data stays if the tags were
equal, and is zeroed if not (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.AesGcm.AArch64 (read_one succ_ofNat bytesAt_succ in_of_covers eval_zero eval_nonzero)

/-! ## `cmp` -/

theorem zext8 (b : BitVec (8 * 1)) : BitVec.setWidth 64 (BitVec.setWidth 32 b) = BitVec.setWidth 64 (b : Byte) := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem setWidth_xor_eq_zero (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64 = 0#64) ↔ a = b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor (a b : Byte) : (a.setWidth 64 ^^^ b.setWidth 64).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt

/-- `(x − 1) >> 63` is 1 if `x` is 0 and 0 if `0 < x < 256`. -/
theorem okBit {x : BitVec 64} (h : x.toNat < 256) :
    (x - BitVec.ofNat 64 1) >>> 63 = if x = 0#64 then 1#64 else 0#64 := by
  by_cases hx : x = 0#64
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have hx' : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 64 - 1 % 2 ^ 64 + x.toNat = (x.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-- The registers `cmp` writes. -/
abbrev cmpRegs : List Reg := [.x9, .x10, .x11, .x12, .x13, .x24]

abbrev cmpBody : List Instr :=
  [.ldrb .x9 .x11 0, .ldrb .x10 .x12 0, .logic .eor .x .x9 .x9 .x10, .logic .orr .x .x13 .x13 .x9,
    Impl.AesGcm.AArch64.ptr .x11 .x11 1, Impl.AesGcm.AArch64.ptr .x12 .x12 1, .subImm .x .x24 .x24 1]

/-- One step of `cmp`. -/
theorem cmpStep_ok (s : State) {A B : Addr} (ha : s.gpr .x11 = A) (hb : s.gpr .x12 = B)
    (ra : InRegions (s.rd ++ s.wr) A 1) (rb : InRegions (s.rd ++ s.wr) B 1) :
    ∃ s', runBlock isa cmpBody s = some s' ∧ s'.mem = s.mem ∧
      s'.gpr .x13 = s.gpr .x13 ||| ((s.mem A).setWidth 64 ^^^ (s.mem B).setWidth 64) ∧
      s'.gpr .x11 = A + BitVec.ofNat 64 1 ∧ s'.gpr .x12 = B + BitVec.ofNat 64 1 ∧
      s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 1 ∧
      (∀ r, r ∉ cmpRegs → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by orun [ha, hb, ra, rb], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [gpr_write, read_one, zext8, ha, hb]
  · simp [gpr_write, ha]
  · simp [gpr_write, hb]
  · simp [gpr_write]
  · simp only [cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  all_goals rfl

/-- `cmp`'s first block: the tag length, and the two tags' addresses. -/
theorem cmpHead_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {tl : Nat}
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    ∃ s₁, runBlock isa
        [Impl.AesGcm.AArch64.imm .x13 0, Impl.AesGcm.AArch64.mov .x11 .x19, Impl.AesGcm.AArch64.ptr .x12 .x19 t2O,
          ld .x24 .x19 tlO] s = some s₁ ∧
      s₁.gpr .x13 = 0#64 ∧ s₁.gpr .x11 = W + BitVec.ofNat 64 0 ∧ s₁.gpr .x12 = W + BitVec.ofNat 64 t2O + BitVec.ofNat 64 0 ∧
      s₁.gpr .x24 = BitVec.ofNat 64 (tl - 0) ∧ s₁.mem = s.mem ∧
      (∀ r, r ∉ cmpRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have r₀ := E.perm.wR (show 248 + 8 ≤ 2560 by decide)
  simp only [tlO] at htl
  refine ⟨_, by orun [E.x19, r₀, htl], ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_write]
  · simp [gpr_write, E.x19]
  · simp [gpr_write, E.x19, t2O]
  · simp [gpr_write, htl]
  · rfl
  · simp only [cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
    simp [gpr_write, h₁, h₂, h₃, h₄, h₅, h₆]
  all_goals rfl

/-- `cmp`: 1 at `W` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) {tl : Nat} (h1 : 1 ≤ tl)
    (h16 : tl ≤ 16) (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (W + BitVec.ofNat 64 tagO)
        (if bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64) ∧
      (∀ r, r ∉ cmpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨s₁, run₁, x13₁, x11₁, x12₁, x24₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := cmpHead_ok E htl
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hR : ∀ {d j : Nat}, d + j < 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 :=
    fun h => by rw [Offset.add_add]; exact E.perm.wR (by omega)
  -- The loop: the OR of the XORs of the first `j` bytes in `x13`.
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .nonzero .x .x24)
    (Q := fun u => (u.gpr .x13).toNat < 256 ∧
      (u.gpr .x13 = 0#64 ↔ bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl) ∧
      u.mem = s.mem ∧ (∀ r, r ∉ cmpRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = tl - j ∧ j < tl ∧ u.gpr .x11 = W + BitVec.ofNat 64 j ∧
      u.gpr .x12 = W + BitVec.ofNat 64 t2O + BitVec.ofNat 64 j ∧ u.gpr .x24 = BitVec.ofNat 64 (tl - j) ∧
      (u.gpr .x13).toNat < 256 ∧
      (u.gpr .x13 = 0#64 ↔ bytesAt s.mem W j = bytesAt s.mem (W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ∉ cmpRegs → u.gpr r = s.gpr r) ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr) ?_ (tl - 0) _
    ⟨0, rfl, by omega, x11₁, x12₁, x24₁, by rw [x13₁]; decide, by rw [x13₁]; simp [bytesAt], m₁, g₁, sp₁, rd₁,
      wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, x11, x12, x24, lt, iff, mem, g, sp, rd, wr⟩
    obtain ⟨u', run', mem', x13', x11', x12', x24', g', sp', rd', wr'⟩ := cmpStep_ok u x11 x12
      (by rw [rd, wr, show W + BitVec.ofNat 64 j = W + BitVec.ofNat 64 0 + BitVec.ofNat 64 j by simp]
          exact hR (by omega))
      (by rw [rd, wr]; exact hR (by simp only [t2O]; omega))
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at x13'
    have lt' : (u'.gpr .x13).toNat < 256 := by
      rw [x13', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (toNat_setWidth_xor _ _)
    have iff' : u'.gpr .x13 = 0#64 ↔
        bytesAt s.mem W (j + 1) = bytesAt s.mem (W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [x13', BitVec.or_eq_zero_iff, iff, setWidth_xor_eq_zero, bytesAt_succ, bytesAt_succ]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [length_bytesAt, length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have x24'' : u'.gpr .x24 = BitVec.ofNat 64 (tl - (j + 1)) := by
      rw [x24', x24, Offset.ofNat_sub_ofNat (by omega)]; rfl
    have ev := eval_nonzero (r := .x24) (a := tl - (j + 1)) x24'' (by omega)
    have gg : ∀ r, r ∉ cmpRegs → u'.gpr r = s.gpr r := fun r hr => by rw [g' r hr, g r hr]
    by_cases he : j + 1 = tl
    · left
      exact ⟨by rw [ev]; simp [he], lt', by rw [iff', he], by rw [mem', mem], gg, by rw [sp', sp],
        by rw [rd', rd], by rw [wr', wr]⟩
    · right
      exact ⟨by rw [ev]; simp; omega, tl - (j + 1), by omega, j + 1, rfl, by omega,
        by rw [x11', Offset.add_add], by rw [x12', Offset.add_add], x24'', lt', iff', by rw [mem', mem], gg,
        by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, sp, rd, wr⟩ := hu
    have h19 : u.gpr .x19 = W := by rw [g _ (by decide), E.x19]
    have w₀ : InRegions u.wr W 8 := by rw [wr]; simpa using E.perm.wW (d := 0) (n := 8) (by decide)
    refine WP.of_runBlock ⟨_, by orun [h19, w₀], ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · simp only [mem_write, gpr_write, ite_true, mem, tagO, BitVec.add_zero]
      rw [okBit lt]
      by_cases he : bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl
      · simp only [iff.mpr he, he, ↓reduceIte]
      · simp only [mt iff.mp he, he, ↓reduceIte]
    · simp only [cmpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hr
      simp only [gpr_write, h₅, ite_false]
      exact g r (by simp [cmpRegs, h₁, h₂, h₃, h₄, h₅, h₆])
    all_goals simp only [sp, rd, wr, sp_write, rd_write, wr_write, mem_write]

/-! ## `mask` -/

theorem mask_byte (b : BitVec (8 * 1)) (c : Bool) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 b)) &&& BitVec.setWidth 32 (0#64 - (if c then 1#64 else 0#64))))) =
      if c then (b : Byte) else 0 := by
  cases c
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [show (if true = true then 1#64 else 0#64) = 1#64 from rfl,
      show (0#64 - 1#64 : BitVec 64) = BitVec.allOnes 64 by decide]
    simp [BitVec.getLsbD_setWidth, show i < 32 by omega, show i < 64 by omega, hi]
    intro _
    rw [BitVec.getElem_eq_testBit_toNat, show (255#8).toNat = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
    simp [hi]

/-- The registers `mask` writes. -/
abbrev maskRegs : List Reg := [.x9, .x10, .x23, .x24]

abbrev maskBody : List Instr :=
  [.ldrb .x9 .x23 0, .logic .and .w .x9 .x9 .x10, .strb .x9 .x23 0, Impl.AesGcm.AArch64.ptr .x23 .x23 1,
    .subImm .x .x24 .x24 1]

theorem maskStep_ok (s : State) {P : Addr} {c : Bool} (h23 : s.gpr .x23 = P)
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64))
    (rq : InRegions (s.rd ++ s.wr) P 1) (wq : InRegions s.wr P 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW P ((if c then s.mem P else 0 : Byte)) ∧
      s'.gpr .x23 = P + BitVec.ofNat 64 1 ∧ s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by orun [h23, rq, wq, write1], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, gpr_write, ite_true, ite_false, reduceCtorEq, h10, h23, read_one, mask_byte]
  · simp [gpr_write, h23]
  · simp [gpr_write]
  · simp [gpr_write, h₁, h₂, h₃]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

theorem maskVector_ok (s : State) {P : Addr} {c : Bool} (h23 : s.gpr .x23 = P)
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64))
    (rq : InRegions (s.rd ++ s.wr) P 16) (wq : InRegions s.wr P 16) :
    ∃ s', runBlock isa [.vop (.dup .d2 .v0 .x10), .ldrq .v1 .x23 0,
        .vop (.logic .and .v1 .v1 .v0), .strq .v1 .x23 0,
        Impl.AesGcm.AArch64.ptr .x23 .x23 16, .subImm .x .x24 .x24 16] s = some s' ∧
      s'.mem = writeBytes s.mem P (if c then bytesAt s.mem P 16 else zeros 16) ∧
      s'.gpr .x23 = P + BitVec.ofNat 64 16 ∧ s'.gpr .x24 = s.gpr .x24 - BitVec.ofNat 64 16 ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have hm (v : BitVec 128) : v &&& ofVDwords (0#64 - (if c then 1#64 else 0#64))
      (0#64 - (if c then 1#64 else 0#64)) = if c then v else 0 := by
    cases c
    · simp [ofVDwords]
    · change v &&& BitVec.allOnes 128 = v
      exact BitVec.and_allOnes
  refine ⟨_, by orun [h23, rq, wq, VOp.eval, v_setV, gpr_setV, mem_setV, rd_setV, wr_setV,
      sp_setV], ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  · simp only [mem_write, gpr_setV, mem_setV, v_setV, ↓reduceIte, reduceCtorEq, h10, h23,
      BitVec.add_zero, hm]
    rw [write_eq_writeBytes]
    congr 1
    cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · decide
    · apply List.map_congr_left
      intro j hj
      exact Mem.extractLsb'_read _ _ (List.mem_range.mp hj)
  · simp [gpr_write, gpr_setV, h23]
  · simp [gpr_write, gpr_setV]
  · simp [gpr_write, gpr_setV, h₂, h₃]
  all_goals rfl

/-- A vector if one remains, otherwise a single tail byte. The branch depends only on length. -/
theorem maskSmall_ok {K W D : Addr} {n j : Nat} {s : State} (hD : DBuf K W s D n)
    (hj : j < n) {c : Bool} (h23 : s.gpr .x23 = D + BitVec.ofNat 64 j)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 (n - j))
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64)) :
    WP isa maskSmall s fun t => ∃ b, 0 < b ∧ j + b ≤ n ∧
      t.mem = writeBytes s.mem (D + BitVec.ofNat 64 j)
        (if c then bytesAt s.mem (D + BitVec.ofNat 64 j) b else zeros b) ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (j + b) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - (j + b)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, x9, g, m, sp, rd, wr⟩ : ∃ s₁,
      runBlock isa [.lsr .x .x9 .x24 4] s = some s₁ ∧
      s₁.gpr .x9 = BitVec.ofNat 64 ((n-j) / 16) ∧
      (∀ r, r ≠ .x9 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, ↓reduceIte, h24, BitVec.setWidth_eq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Proof.Ocb.toNat_ofNat_of_lt (by omega),
        Proof.Ocb.toNat_ofNat_of_lt (by omega), Nat.shiftRight_eq_div_pow]
    · simp [gpr_write, hr]
    all_goals rfl
  unfold maskSmall
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide ((n-j)/16 = 0)) (eval_zero x9 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · obtain ⟨t, run, mem, xp, xc, gg, ss, rr, ww⟩ := maskStep_ok s₁ (P := D + BitVec.ofNat 64 j) (c := c)
      (by rw [g _ (by decide)]; exact h23) (by rw [g _ (by decide)]; exact h10)
      (by rw [rd, wr]; exact in_of_covers hD.rd hj hn)
      (by rw [wr]; exact in_of_covers hD.wr hj hn)
    refine WP.of_runBlock ⟨t, run, 1, by omega, by omega, ?_, ?_, ?_, ?_, ss.trans sp, rr.trans rd, ww.trans wr⟩
    · rw [mem, m, Proof.Ocb.writeW8_eq]; cases c <;> simp [bytesAt, zeros]
    · rw [xp, Offset.add_add]
    · rw [xc, g _ (by decide), h24, Offset.ofNat_sub_ofNat (by omega)]
      congr 1
    · exact fun r h₁ h₂ h₃ => (gg r h₁ h₂ h₃).trans (g r h₁)
  · have hb : 16 ≤ n-j := by have := of_decide_eq_false hb; omega
    obtain ⟨t, run, mem, xp, xc, gg, ss, rr, ww⟩ := maskVector_ok s₁ (P := D + BitVec.ofNat 64 j) (c := c)
      (by rw [g _ (by decide)]; exact h23) (by rw [g _ (by decide)]; exact h10)
      (by rw [rd, wr]; exact Proof.AesGcm.AArch64.in_off hD.rd (by omega) hn)
      (by rw [wr]; exact Proof.AesGcm.AArch64.in_off hD.wr (by omega) hn)
    refine WP.of_runBlock ⟨t, run, 16, by omega, by omega, by rw [mem, m], ?_, ?_, ?_,
      ss.trans sp, rr.trans rd, ww.trans wr⟩
    · rw [xp, Offset.add_add]
    · rw [xc, g _ (by decide), h24, Offset.ofNat_sub_ofNat (by omega)]
      congr 1
    · exact fun r h₁ h₂ h₃ => (gg r h₁ h₂ h₃).trans (g r h₁)


theorem maskVectors_ok {K W D : Addr} {n j : Nat} {s : State} (hD : DBuf K W s D n)
    (k : Nat) (hk : j + 16*k ≤ n) {c : Bool} (h23 : s.gpr .x23 = D + BitVec.ofNat 64 j)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 (n-j))
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64)) :
    WP isa (maskVectors k) s fun t =>
      t.mem = writeBytes s.mem (D + BitVec.ofNat 64 j)
        (if c then bytesAt s.mem (D + BitVec.ofNat 64 j) (16*k) else zeros (16*k)) ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (j+16*k) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n-(j+16*k)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  induction k generalizing s j with
  | zero =>
    refine WP.block_nil ⟨?_, by simpa using h23, by simpa using h24, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  | succ k ih =>
    have hn := hD.lt
    obtain ⟨u,run,mem,xp,xc,g,sp,rd,wr⟩ := maskVector_ok s h23 h10
      (Proof.AesGcm.AArch64.in_off hD.rd (by omega) hn)
      (Proof.AesGcm.AArch64.in_off hD.wr (by omega) hn)
    refine WP.seq (WP.of_runBlock ⟨u,run,?_⟩)
    have xp' : u.gpr .x23 = D + BitVec.ofNat 64 (j+16) := by rw [xp,Offset.add_add]
    have xc' : u.gpr .x24 = BitVec.ofNat 64 (n-(j+16)) := by
      rw [xc,h24,Offset.ofNat_sub_ofNat (by omega),Nat.sub_sub]
    refine WP.mono (ih (hD.of_eq rd wr) (by omega) xp' xc'
      (by rw [g _ (by decide) (by decide) (by decide),h10])) fun t ⟨mt,xt,ct,gt,st,rt,wt⟩ => ?_
    refine ⟨?_,by simpa only [show j+16+16*k = j+16*(k+1) by omega] using xt,
      by simpa only [show j+16+16*k = j+16*(k+1) by omega] using ct,
      fun r a b c => (gt r a b c).trans (g r a b c),st.trans sp,rt.trans rd,wt.trans wr⟩
    have hq : bytesAt u.mem (D+BitVec.ofNat 64 (j+16)) (16*k) =
        bytesAt s.mem (D+BitVec.ofNat 64 (j+16)) (16*k) := by
      apply List.map_congr_left
      intro i hi
      have hi : i < 16*k := List.mem_range.mp hi
      rw [mem, show D+BitVec.ofNat 64 (j+16) = (D+BitVec.ofNat 64 j)+16#64 from (Offset.add_add D j 16).symm,
        Offset.add_add]
      simp only [writeBytes,length_mask,Mem.sub_ofNat_toNat (D+BitVec.ofNat 64 j) (show 16+i < 2^64 by omega),
        show ¬16+i < 16 by omega,ite_false]
    rw [mt,hq,mem]
    have app := writeBytes_append s.mem (D+BitVec.ofNat 64 j)
      (if c then bytesAt s.mem (D+BitVec.ofNat 64 j) 16 else zeros 16)
      (if c then bytesAt s.mem (D+BitVec.ofNat 64 (j+16)) (16*k) else zeros (16*k))
      (by rw [length_mask,length_mask]; omega)
    rw [length_mask,Offset.add_add] at app
    rw [app]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, zeros, List.replicate_append_replicate,
        show 16*(k+1) = 16+16*k by omega]
    · simp [show 16*(k+1) = 16+16*k by omega,Proof.AesGcm.AArch64.bytesAt_add,Offset.add_add]

/-- Mask four complete vectors, one vector, or one byte depending only on length. -/
theorem maskChunk_ok {K W D : Addr} {n j : Nat} {s : State} (hD : DBuf K W s D n)
    (hj : j < n) {c : Bool} (h23 : s.gpr .x23 = D + BitVec.ofNat 64 j)
    (h24 : s.gpr .x24 = BitVec.ofNat 64 (n - j))
    (h10 : s.gpr .x10 = 0#64 - (if c then 1#64 else 0#64)) :
    WP isa maskChunk s fun t => ∃ b, 0 < b ∧ j + b ≤ n ∧
      t.mem = writeBytes s.mem (D + BitVec.ofNat 64 j)
        (if c then bytesAt s.mem (D + BitVec.ofNat 64 j) b else zeros b) ∧
      t.gpr .x23 = D + BitVec.ofNat 64 (j + b) ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - (j + b)) ∧
      (∀ r, r ≠ .x9 → r ≠ .x23 → r ≠ .x24 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let u := s.write .x .x9 (s.gpr .x24 >>> 6)
  have hu : runBlock isa [.lsr .x .x9 .x24 6] s = some u := by orun []
  have hg (r : Reg) (hr : r ≠ .x9) : u.gpr r = s.gpr r := by simp [u,gpr_write,hr]
  have h9 : u.gpr .x9 = BitVec.ofNat 64 ((n-j)/64) := by
    simp [u,gpr_write,h24,Proof.AesGcm.AArch64.lsr_ofNat _ _ (show n-j < 2^64 by have := hD.lt; omega)]
  unfold maskChunk
  refine WP.seq (WP.of_runBlock ⟨u,hu,?_⟩)
  refine WP.ite _ (eval_zero h9 (by have := hD.lt; omega)) (fun hz => ?_) (fun hn => ?_)
  · refine WP.mono (maskSmall_ok (s := u) (hD.of_eq rfl rfl) hj ((hg _ (by decide)).trans h23)
      ((hg _ (by decide)).trans h24) ((hg _ (by decide)).trans h10)) ?_
    rintro t ⟨b,hb,hjb,mem,xp,xc,g,sp,rd,wr⟩
    exact ⟨b,hb,hjb,mem,xp,xc,fun r a b c => (g r a b c).trans (hg r a),sp,rd,wr⟩
  · have hn : 64 ≤ n-j := by have := of_decide_eq_false hn; omega
    refine WP.mono (maskVectors_ok (s := u) (hD.of_eq rfl rfl) 4 (by omega) ((hg _ (by decide)).trans h23)
      ((hg _ (by decide)).trans h24) ((hg _ (by decide)).trans h10)) ?_
    rintro t ⟨mem,xp,xc,g,sp,rd,wr⟩
    exact ⟨64,by decide,by omega,mem,xp,xc,fun r a b c => (g r a b c).trans (hg r a),sp,rd,wr⟩

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State} (E : Env K W D R n SP s) (hD : DBuf K W s D n)
    {c : Bool} (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s fun t => (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have r₃ : InRegions (s.rd ++ s.wr) W 8 := by simpa using E.perm.wR (d := 0) (n := 8) (by decide)
  simp only [tagO, BitVec.add_zero] at hok
  have hok' : s.mem.readW W 64 = if c then 1#64 else 0#64 := by simpa using hok
  have hn := hD.lt
  obtain ⟨s₁, run₁, m₁, x23₁, x24₁, x10₁, g₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x28, ld .x9 .x19 tagO,
        Impl.AesGcm.AArch64.imm .x10 0, .sub .x .x10 .x10 .x9] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .x23 = D ∧ s₁.gpr .x24 = BitVec.ofNat 64 n ∧
      s₁.gpr .x10 = 0#64 - (if c then 1#64 else 0#64) ∧
      (∀ r, r ∉ maskRegs → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.x19, r₃, hok'], ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rfl
    · simp [gpr_write, E.x21]
    · simp [gpr_write, E.x28]
    · simp [gpr_write, hok']
    · simp only [maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hr
      simp [gpr_write, h₁, h₂, h₃, h₄]
    all_goals rfl
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_zero x24₁ hn) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨g₁, sp₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .nonzero .x .x24)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .x23 = D + BitVec.ofNat 64 j ∧
      t.gpr .x24 = BitVec.ofNat 64 (n - j) ∧ t.gpr .x10 = 0#64 - (if c then 1#64 else 0#64) ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
      (∀ r, r ∉ maskRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, by rw [x23₁]; simp, x24₁, x10₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil],
      g₁, sp₁, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, x23, x24, x10, mem, g, sp, rd, wr⟩
  refine WP.mono (maskChunk_ok (hD.of_eq rd wr) hj x23 x24 x10) ?_
  rintro t' ⟨b, hb, hjb, mem', x23', x24', g', sp', rd', wr'⟩
  have hq : bytesAt t.mem (D + BitVec.ofNat 64 j) b = bytesAt s.mem (D + BitVec.ofNat 64 j) b := by
    apply List.map_congr_left
    intro i hi
    have hi : i < b := List.mem_range.mp hi
    rw [Offset.add_add, mem]
    simp only [writeBytes, length_mask, Mem.sub_ofNat_toNat D (show j + i < 2 ^ 64 by omega),
      show ¬j + i < j by omega, ite_false]
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + b) else zeros (j + b)) := by
    rw [mem', hq, mem]
    have append := writeBytes_append s.mem D (if c then bytesAt s.mem D j else zeros j)
      (if c then bytesAt s.mem (D + BitVec.ofNat 64 j) b else zeros b)
      (by rw [length_mask, length_mask]; omega)
    rw [length_mask] at append
    rw [append]
    cases c <;> simp [zeros, Proof.AesGcm.AArch64.bytesAt_add]
  have x24'' : t'.gpr .x24 = BitVec.ofNat 64 (n - (j + b)) := by
    exact x24'
  have ev := eval_nonzero (r := .x24) (a := n - (j + b)) x24'' (by omega)
  have gg : ∀ r, r ∉ maskRegs → t'.gpr r = s.gpr r := fun r hr => by
    simp only [maskRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g' r hr.1 hr.2.2.1 hr.2.2.2, g r (by simp [maskRegs, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  by_cases he : j + b = n
  · left
    exact ⟨by rw [ev]; simp [he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    exact ⟨by rw [ev]; simp; omega, n - (j + b), by omega, j + b, rfl, by omega,
      x23', x24'', by rw [g' _ (by decide) (by decide) (by decide), x10], hmem, gg,
      by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.AArch64
