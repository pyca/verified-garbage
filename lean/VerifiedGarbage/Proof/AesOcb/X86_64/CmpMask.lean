import VerifiedGarbage.Proof.AesOcb.X86_64.XorPad

/-!
# AES-OCB on x86-64: checking the tag and masking the data (`cmp`, `mask`)

Untrusted: everything here is checked by Lean. `cmp` ORs the XORs of the
first `tag_len` bytes of the received tag (at `W`) and the computed one (at
`W + t2O`) and leaves 1 at `W` if the OR is 0, else 0 (`cmp_ok`); `mask`
ANDs every byte of the data with `0 − ok`: the data stays if the tags were
equal, and is zeroed if not (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt eval_e eval_ne length_bytesAt)
open VG.Proof.AesGcm.X86_64 (in_of_covers succ_ofNat bytesAt_succ)

/-! ## `cmp` -/

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
theorem okBit {x : BitVec 64} (h : x.toNat < 256) : (x - 1#64) >>> 63 = if x = 0#64 then 1#64 else 0#64 := by
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

/-- One step of `cmp`. -/
theorem cmpStep_ok (s : State) {W : Addr} {j T : Nat} (h15 : s.gpr .r15 = W)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (h12 : s.gpr .r12 = BitVec.ofNat 64 T)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 j) 1)
    (r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax { base := .r15, index := some .rcx },
        .movzx8 .r8 { base := .r15, index := some .rcx, disp := t2O }, .alu .xor .rax (.reg .r8),
        .alu .or .rdx (.reg .rax), addi .rcx 1, .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem ∧
      s'.gpr .rdx = s.gpr .rdx ||| ((s.mem (W + BitVec.ofNat 64 j)).setWidth 64 ^^^
        (s.mem (W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j)).setWidth 64) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 T == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea₁ := ea_index s h15 h1
  have ea₂ : s.gpr .r15 + s.gpr .rcx * BitVec.ofNat 64 1 + BitVec.ofNat 64 128 =
      W + BitVec.ofNat 64 128 + BitVec.ofNat 64 j := ea_index_disp s (d := 128) h15 h1
  refine ⟨_, by orun [ea₁, ea₂, r₀, r₁], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, h₄, ite_false]
  all_goals rfl

/-- `cmp`: 1 at `W` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {tl : Nat} (h1 : 1 ≤ tl) (h16 : tl ≤ 16)
    (htl : s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (W + BitVec.ofNat 64 tagO)
        (if bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl then 1#64 else 0#64) ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have r₀ := E.perm.wR (show 224 + 8 ≤ 2560 by decide)
  simp only [tlO] at htl
  obtain ⟨s₁, run₁, rdx₁, rcx₁, r12₁, m₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.alu .xor .rdx (.reg .rdx), .mov .rcx (.imm 0), ld .r12 .r15 tlO] s = some s₁ ∧
      s₁.gpr .rdx = 0#64 ∧ s₁.gpr .rcx = BitVec.ofNat 64 0 ∧ s₁.gpr .r12 = BitVec.ofNat 64 tl ∧ s₁.mem = s.mem ∧
      (∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [E.r15, r₀, htl], ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, htl]
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, ite_false]
    all_goals rfl
  have h15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hR : ∀ {d j : Nat}, d + j < 2560 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d + BitVec.ofNat 64 j) 1 :=
    fun h => by rw [Offset.add_add]; exact E.perm.wR (by omega)
  -- The loop: the OR of the XORs of the first `j` bytes in `rdx`.
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .ne)
    (Q := fun u => (u.gpr .rdx).toNat < 256 ∧
      (u.gpr .rdx = 0#64 ↔ bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = tl - j ∧ j < tl ∧ u.gpr .rcx = BitVec.ofNat 64 j ∧
      u.gpr .r12 = BitVec.ofNat 64 tl ∧ (u.gpr .rdx).toNat < 256 ∧
      (u.gpr .rdx = 0#64 ↔ bytesAt s.mem W j = bytesAt s.mem (W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ?_ (tl - 0) _
    ⟨0, rfl, by omega, rcx₁, r12₁, by rw [rdx₁]; decide, by rw [rdx₁]; simp [bytesAt], m₁,
      fun r _ h₂ h₃ _ h₅ => g₁ r h₂ h₃ h₅, rd₁, wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, rcx, r12, lt, iff, mem, g, rd, wr⟩
    have h15 : u.gpr .r15 = W := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
    obtain ⟨u', run', mem', rdx', rcx', zf', g', rd', wr'⟩ := cmpStep_ok u (W := W) (j := j) (T := tl) h15 rcx r12
      (by rw [rd, wr, show W + BitVec.ofNat 64 j = W + BitVec.ofNat 64 0 + BitVec.ofNat 64 j by simp]
          exact hR (by omega))
      (by rw [rd, wr]; exact hR (by omega))
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at rdx'
    have lt' : (u'.gpr .rdx).toNat < 256 := by
      rw [rdx', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (toNat_setWidth_xor _ _)
    have iff' : u'.gpr .rdx = 0#64 ↔
        bytesAt s.mem W (j + 1) = bytesAt s.mem (W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [rdx', BitVec.or_eq_zero_iff, iff, setWidth_xor_eq_zero, bytesAt_succ, bytesAt_succ]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]; rfl
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [length_bytesAt, length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have hz : u'.zf = some (decide (j + 1 = tl)) := by
      rw [zf', Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    have gg : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → r ≠ .r12 → u'.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄ h₅]
    by_cases he : j + 1 = tl
    · left
      exact ⟨(eval_ne hz).trans (by simp [he]), lt', by rw [iff', he], by rw [mem', mem], gg, by rw [rd', rd],
        by rw [wr', wr]⟩
    · right
      exact ⟨(eval_ne hz).trans (by simp [he]), tl - (j + 1), by omega, j + 1, rfl, by omega, rcx',
        by rw [g' _ (by decide) (by decide) (by decide) (by decide), r12], lt', iff', by rw [mem', mem], gg,
        by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, rd, wr⟩ := hu
    have h15 : u.gpr .r15 = W := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), E.r15]
    have w₀ : InRegions u.wr (W + BitVec.ofNat 64 0) 8 := by rw [wr]; exact E.perm.wW (by decide)
    refine WP.of_runBlock ⟨_, by orun [h15, w₀], ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_setFlags, mem_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags, ite_true,
        ite_false, reduceCtorEq, sext1, mem]
      rw [show BitVec.ofNat 64 1 = 1#64 from rfl, okBit lt]
      by_cases he : bytesAt s.mem W tl = bytesAt s.mem (W + BitVec.ofNat 64 t2O) tl
      · simp only [iff.mpr he, he, ↓reduceIte]; rfl
      · simp only [mt iff.mp he, he, ↓reduceIte]; rfl
    · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂, h₃, h₄, h₅, ite_false]
      exact g r h₁ h₂ h₃ h₄ h₅
    all_goals simp only [rd, wr]

/-! ## `mask` -/

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1#64 else 0#64))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then 1#64 else 0#64) = 1#64 from rfl,
      show (0 : BitVec 64) - 1#64 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

theorem maskStep_ok (s : State) {P : Addr} {j L : Nat} {c : Bool} (h3 : s.gpr .rbx = P)
    (h1 : s.gpr .rcx = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = 0 - (if c then 1#64 else 0#64))
    (h12 : s.gpr .r12 = BitVec.ofNat 64 L)
    (rq : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 j) 1) (wq : InRegions s.wr (P + BitVec.ofNat 64 j) 1) :
    ∃ s', runBlock isa [.movzx8 .rax { base := .rbx, index := some .rcx }, .alu .and .rax (.reg .rdx),
        .store8 { base := .rbx, index := some .rcx } .rax, addi .rcx 1, .alu .cmp .rcx (.reg .r12)] s = some s' ∧
      s'.mem = s.mem.writeW (P + BitVec.ofNat 64 j) ((if c then s.mem (P + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      s'.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 L == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea := ea_index s h3 h1
  refine ⟨_, by orun [ea, rq, wq], ?_, ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hdx,
      mask_byte]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, sext1, ← BitVec.ofNat_add]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h1, h12, sext1,
      ← BitVec.ofNat_add]
  · simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {D : Addr} {n : Nat}
    (hdata : s.mem.readW (W + BitVec.ofNat 64 208) 64 = D)
    (hlen : s.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 n) (hD : DBuf K W SP s D n) {c : Bool}
    (hok : s.mem.readW (W + BitVec.ofNat 64 tagO) 64 = if c then 1#64 else 0#64) :
    WP isa mask s fun t => Env K W SP t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D n else zeros n) := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 216 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 0 + 8 ≤ 2560 by decide)
  simp only [tagO] at hok
  have hn := hD.lt
  obtain ⟨s₁, run₁, m₁, h3₁, h12₁, hdx₁, h1₁, zf₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [ld .rbx .r15 dataO, ld .r12 .r15 lenO, .alu .xor .rdx (.reg .rdx),
        .alu .sub .rdx (.mem (at_ .r15 tagO)), .mov .rcx (.imm 0), .alu .test .r12 (.reg .r12)] s = some s₁ ∧
      s₁.mem = s.mem ∧ s₁.gpr .rbx = D ∧ s₁.gpr .r12 = BitVec.ofNat 64 n ∧
      s₁.gpr .rdx = 0 - (if c then 1#64 else 0#64) ∧ s₁.gpr .rcx = BitVec.ofNat 64 0 ∧
      s₁.zf = some (decide (n = 0)) ∧
      (∀ r ∈ [Reg.r14, .r15, .rsp], s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by orun [h15, r₁, r₂, r₃, hdata, hlen, hok], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0, hok]; rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, BitVec.xor_self, sext0]
    · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        Proof.AesCcm.X86_64.and_self_beq hn]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
    all_goals rfl
  have E₁ : Env K W SP s₁ := E.keep g₁ rd₁ wr₁
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .rcx = BitVec.ofNat 64 j ∧
      t.mem = writeBytes s.mem D (if c then bytesAt s.mem D j else zeros j) ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, h1₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil],
      fun r _ _ => rfl, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, h1, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', h1', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (j := j) (L := n) (c := c)
    (by rw [g _ (by decide) (by decide), h3₁]) h1 (by rw [g _ (by decide) (by decide), hdx₁])
    (by rw [g _ (by decide) (by decide), h12₁]) (by rw [rd, wr]; exact in_of_covers hD.rd hj hn)
    (by rw [wr]; exact in_of_covers hD.wr hj hn)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (D + BitVec.ofNat 64 j) = s.mem (D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat D (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem D (if c then bytesAt s.mem D (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by
    rw [zf', Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
  have gg : ∀ r, r ≠ .rax → r ≠ .rcx → t'.gpr r = s₁.gpr r := fun r h₁ h₂ => by rw [g' r h₁ h₂, g r h₁ h₂]
  have E' : Env K W SP t' := E₁.keep (fun r hr => gg r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    (by rw [rd', rd, rd₁]) (by rw [wr', wr, wr₁])
  by_cases he : j + 1 = n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), n - (j + 1), by omega, j + 1, rfl, by omega, h1', hmem, gg,
      by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.X86_64
