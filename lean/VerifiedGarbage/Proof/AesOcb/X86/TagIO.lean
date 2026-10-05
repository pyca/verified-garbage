import VerifiedGarbage.Proof.AesOcb.X86.Body

/-!
# AES-OCB on x86: the tag in and out, checking it and masking the data

Untrusted: everything here is checked by Lean. `tagOut` copies the first
`tag_len` bytes of the tag at `W` to `tag` (`tagOut_ok`); `recv` copies the
received tag to `W` (`recv_ok`); `cmp` ORs the XORs of the first `tag_len`
bytes at `W` and `W + t2O` and leaves 1 at `W + okO` if the OR is 0, else 0
(`cmp_ok`); `mask` ANDs every byte of the data with `0 − ok` (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (zeros)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop)
open VG.Proof.AesGcm.X86 (w64 w64_add slotv slotv_eq runBlock_app_of toNat_ofNat32 toNat_add32 covers_off in_off
  in_left covers_left length_bytesAt LoopPre CopyPost copyLoop_ok bytesAt_succ add_ofNat_assoc32)

/-! ## The tag out and in -/

theorem tagOut_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) (htw : Covers [⟨w64 p.T, p.tl⟩] s.wr) :
    WP isa tagOut s fun s' => s'.mem = writeBytes s.mem (w64 p.T) (bytesAt s.mem (w64 p.W) p.tl) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  obtain ⟨s₁, run₁, di₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (.reg .ebp), .mov .edx (slot tgO), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edi = p.W ∧ s₁.gpr .edx = p.T ∧ s₁.gpr .ecx = BitVec.ofNat 32 p.tl ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [E.ebp], by gregs [hT], by gregs [hv],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold tagOut
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ht := L.tl16
  have lp : LoopPre s₁ p.W p.T p.tl := ⟨di₁, dx₁, cx₁, L.tl1, by omega, by have := L.ww; omega, L.tw,
    by rw [rd₁, wr₁]; exact covers_prefix (covers_left E.perm.w) (by omega),
    by rw [wr₁]; exact htw, (L.t_w.sub_right (Region.sub_prefix (by omega))).symm⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, m₁], fun r h₁ h₂ h₃ h₄ => by
    rw [P.other r h₁ h₄ h₃ h₂, g₁ r h₂ h₃ h₄], by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩

theorem recv_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa recv s fun s' => s'.mem = writeBytes s.mem (w64 p.W) (bytesAt s.mem (w64 p.T) p.tl) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hT := E.slots.tg
  have hv := E.slots.tlen
  simp only [slotv_eq] at hT hv
  obtain ⟨s₁, run₁, di₁, dx₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edi (slot tgO), .mov .edx (.reg .ebp), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edi = p.T ∧ s₁.gpr .edx = p.W ∧ s₁.gpr .ecx = BitVec.ofNat 32 p.tl ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv, hT], by gregs [hT], by gregs [E.ebp], by gregs [hv],
      fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold recv
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have ht := L.tl16
  have lp : LoopPre s₁ p.T p.W p.tl := ⟨di₁, dx₁, cx₁, L.tl1, by omega, L.tw, by have := L.ww; omega,
    by rw [rd₁, wr₁]; exact E.perm.t, by rw [wr₁]; exact covers_prefix E.perm.w (by omega),
    L.t_w.sub_right (Region.sub_prefix (by omega))⟩
  refine WP.mono (copyLoop_ok s₁ lp) fun s' P => ⟨by rw [P.mem, m₁], fun r h₁ h₂ h₃ h₄ => by
    rw [P.other r h₁ h₄ h₃ h₂, g₁ r h₂ h₃ h₄], by rw [P.rd, rd₁], by rw [P.wr, wr₁]⟩

/-! ## `cmp` -/

theorem setWidth_xor_eq_zero32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32 = 0#32) ↔ a = b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth] at this
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega)]
  exact Nat.xor_lt_two_pow (n := 8) a.isLt b.isLt

/-- `(x − 1) >> 31` is 1 if `x` is 0 and 0 if `0 < x < 256`. -/
theorem okBit32 {x : BitVec 32} (h : x.toNat < 256) :
    (x - BitVec.ofNat 32 1) >>> 31 = if x = 0#32 then BitVec.ofNat 32 1 else BitVec.ofNat 32 0 := by
  by_cases hx : x = 0#32
  · subst hx; decide
  · simp only [hx, ↓reduceIte]
    have hx' : 0 < x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h0 | h0
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hx
      · exact h0
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 32 - 1 % 2 ^ 32 + x.toNat = (x.toNat - 1) + 2 ^ 32 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]

/-- One step of `cmp`. -/
theorem cmpStep_ok {p : Prm} (L : Lay p) {u : State} (E : Env p u) {j tl : Nat} (hj : j < tl) (ht : tl ≤ 16)
    (hdi : u.gpr .edi = p.W + BitVec.ofNat 32 j) (hcx : u.gpr .ecx = BitVec.ofNat 32 (tl - j)) :
    ∃ u', runBlock isa [.movzx8 .eax (at_ .edi 0), .movzx8 .ebx (at_ .edi t2O), .alu .xor .eax (.reg .ebx),
        .alu .or .edx (.reg .eax), .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)] u = some u' ∧
      u'.mem = u.mem ∧
      u'.gpr .edx = u.gpr .edx ||| ((u.mem (w64 p.W + BitVec.ofNat 64 j)).setWidth 32 ^^^
        (u.mem (w64 p.W + BitVec.ofNat 64 (t2O + j))).setWidth 32) ∧
      u'.gpr .edi = p.W + BitVec.ofNat 32 (j + 1) ∧ u'.gpr .ecx = BitVec.ofNat 32 (tl - (j + 1)) ∧
      u'.zf = some (decide (j + 1 = tl)) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧
      u'.wr = u.wr := by
  have a0 : w64 (p.W + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.W + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact L.aW (by omega)
  have a1 : w64 (p.W + BitVec.ofNat 32 j + BitVec.ofNat 32 t2O) = w64 p.W + BitVec.ofNat 64 (t2O + j) := by
    rw [add_ofNat_assoc32, Nat.add_comm]; exact L.aW (by simp only [t2O]; omega)
  have r0 : InRegions (u.rd ++ u.wr) (w64 p.W + BitVec.ofNat 64 j) 1 := E.perm.wR (by omega)
  have r1 : InRegions (u.rd ++ u.wr) (w64 p.W + BitVec.ofNat 64 (t2O + j)) 1 := E.perm.wR (by simp only [t2O]; omega)
  refine ⟨_, by grun [hdi, a0, a1, r0, r1], by gmems [], by gregs [], ?_, ?_, ?_,
    fun r h₁ h₂ h₃ h₄ h₅ => by gregs [h₁, h₂, h₃, h₄, h₅], by gmems [], by gmems []⟩
  · gregs [hdi]; rw [add_ofNat_assoc32]
  · gregs [hcx]; rw [sub1_32 (by omega) (by omega), show tl - j - 1 = tl - (j + 1) by omega]
  · gmems [hcx]
    rw [sub1_32 (by omega) (by omega), beq_zero32 (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- `cmp`: 1 at `W + okO` if the first `tl` bytes at `W` and `W + t2O` are equal, else 0. -/
theorem cmp_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    WP isa cmp s fun t => t.mem = s.mem.writeW (w64 p.W + BitVec.ofNat 64 okO)
        (if bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl then BitVec.ofNat 32 1
         else BitVec.ofNat 32 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have hv := E.slots.tlen
  simp only [slotv_eq] at hv
  have h1 := L.tl1
  have h16 := L.tl16
  obtain ⟨s₁, run₁, dx₁, di₁, cx₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .edx (imm 0), .mov .edi (.reg .ebp), .mov .ecx (slot tlO)] s = some s₁ ∧
      s₁.gpr .edx = 0#32 ∧ s₁.gpr .edi = p.W + BitVec.ofNat 32 0 ∧ s₁.gpr .ecx = BitVec.ofNat 32 (p.tl - 0) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hv], by gregs [], by gregs [E.ebp]; exact (BitVec.add_zero _).symm,
      by gregs [hv, Nat.sub_zero], fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [], by gmems []⟩
  unfold cmp
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (WP.loop (M := isa) (c := .ne)
    (Q := fun u => (u.gpr .edx).toNat < 256 ∧
      (u.gpr .edx = 0#32 ↔ bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr)
    (fun (k : Nat) (u : State) => ∃ j, k = p.tl - j ∧ j < p.tl ∧ u.gpr .edi = p.W + BitVec.ofNat 32 j ∧
      u.gpr .ecx = BitVec.ofNat 32 (p.tl - j) ∧ (u.gpr .edx).toNat < 256 ∧
      (u.gpr .edx = 0#32 ↔ bytesAt s.mem (w64 p.W) j = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) j) ∧
      u.mem = s.mem ∧ (∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ?_ (p.tl - 0) _
    ⟨0, rfl, by omega, di₁, cx₁, by rw [dx₁]; decide, by rw [dx₁]; simp [bytesAt], m₁,
      fun r _ _ h₃ h₄ h₅ => g₁ r h₃ h₄ h₅, rd₁, wr₁⟩) fun u hu => ?_)
  · rintro k u ⟨j, rfl, hj, di, cx, lt, iff, mem, g, rd, wr⟩
    have Eu : Env p u := E.keep (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]) rd wr mem
    obtain ⟨u', run', mem', dx', di', cx', zf', g', rd', wr'⟩ := cmpStep_ok L Eu hj h16 di cx
    refine WP.of_runBlock ⟨u', run', ?_⟩
    rw [mem] at dx'
    have lt' : (u'.gpr .edx).toNat < 256 := by
      rw [dx', BitVec.toNat_or]; exact Nat.or_lt_two_pow (n := 8) lt (toNat_setWidth_xor32 _ _)
    have iff' : u'.gpr .edx = 0#32 ↔
        bytesAt s.mem (w64 p.W) (j + 1) = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) (j + 1) := by
      rw [dx', BitVec.or_eq_zero_iff, iff, setWidth_xor_eq_zero32, bytesAt_succ, bytesAt_succ, add_ofNat_assoc]
      constructor
      · rintro ⟨h₁, h₂⟩; rw [h₁, h₂]
      · intro h
        obtain ⟨h₁, h₂⟩ := List.append_inj h (by rw [length_bytesAt, length_bytesAt])
        exact ⟨h₁, List.head_eq_of_cons_eq h₂⟩
    have gg : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → r ≠ .edi → u'.gpr r = s.gpr r :=
      fun r h₁ h₂ h₃ h₄ h₅ => by rw [g' r h₁ h₂ h₃ h₄ h₅, g r h₁ h₂ h₃ h₄ h₅]
    by_cases he : j + 1 = p.tl
    · left
      refine ⟨(eval_ne zf').trans (by simp [he]), lt', ?_, by rw [mem', mem], gg, by rw [rd', rd], by rw [wr', wr]⟩
      rw [← he]; exact iff'
    · right
      exact ⟨(eval_ne zf').trans (by simp [he]), p.tl - (j + 1), by omega, j + 1, rfl, by omega, di', cx', lt', iff',
        by rw [mem', mem], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · obtain ⟨lt, iff, mem, g, rd, wr⟩ := hu
    have Eu : Env p u := E.keep (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)])
      (by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide)]) rd wr mem
    have hb := okBit32 lt
    refine WP.of_runBlock ⟨_, by grun [Eu.ebp, L.aW, Eu.perm.wW], ?_, fun r h₁ h₂ h₃ h₄ h₅ => ?_, ?_, ?_⟩
    · gmems [mem, hb]
      by_cases h : u.gpr .edx = 0#32
      · simp only [h, ↓reduceIte, iff.mp h]
      · have h' : ¬ bytesAt s.mem (w64 p.W) p.tl = bytesAt s.mem (w64 p.W + BitVec.ofNat 64 t2O) p.tl :=
          fun e => h (iff.mpr e)
        simp only [h, h', ↓reduceIte]
    · gregs [h₄]; exact g r h₁ h₂ h₃ h₄ h₅
    · gmems []; exact rd
    · gmems []; exact wr

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- One step of `mask`. -/
theorem maskStep_ok {p : Prm} (L : Lay p) {u : State} {j : Nat} {c : Bool} (hj : j < p.n)
    (hdi : u.gpr .edi = p.D + BitVec.ofNat 32 j) (hcx : u.gpr .ecx = BitVec.ofNat 32 (p.n - j))
    (hdx : u.gpr .edx = 0 - (if c then 1 else 0))
    (r : InRegions (u.rd ++ u.wr) (w64 p.D + BitVec.ofNat 64 j) 1) (w : InRegions u.wr (w64 p.D + BitVec.ofNat 64 j) 1) :
    ∃ u', runBlock isa [.movzx8 .eax (at_ .edi 0), .alu .and .eax (.reg .edx), .store8 (at_ .edi 0) .al,
        .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)] u = some u' ∧
      u'.mem = u.mem.writeW (w64 p.D + BitVec.ofNat 64 j)
        ((if c then u.mem (w64 p.D + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      u'.gpr .edi = p.D + BitVec.ofNat 32 (j + 1) ∧ u'.gpr .ecx = BitVec.ofNat 32 (p.n - (j + 1)) ∧
      u'.zf = some (decide (j + 1 = p.n)) ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := L.n32
  have a0 : w64 (p.D + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.D + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact w64_add (by have := L.dw; omega)
  refine ⟨_, by grun [hdi, a0, r, w], by gmems [hdx, mask_byte32], ?_, ?_, ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  · gregs [hdi]; rw [add_ofNat_assoc32]
  · gregs [hcx]; rw [sub1_32 (by omega) (by omega), show p.n - j - 1 = p.n - (j + 1) by omega]
  · gmems [hcx]
    rw [sub1_32 (by omega) (by omega), beq_zero32 (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {c : Bool}
    (hok : slotv s.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) :
    WP isa mask s fun s' => s'.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) p.n else zeros p.n) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := L.n32
  have hd := L.dw
  have hD := E.slots.data
  have hl := E.slots.len
  simp only [slotv_eq] at hD hl hok
  obtain ⟨s₁, run₁, di₁, cx₁, dx₁, zf₁, g₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [.mov .edi (slot dataO),
      .mov .ecx (slot lenO), .mov .edx (imm 0), .alu .sub .edx (slot okO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧
      s₁.gpr .edi = p.D + BitVec.ofNat 32 0 ∧ s₁.gpr .ecx = BitVec.ofNat 32 (p.n - 0) ∧
      s₁.gpr .edx = 0 - (if c then 1 else 0) ∧ s₁.zf = some (decide (p.n = 0)) ∧
      (∀ r, r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hD, hl, hok], by gregs [hD]; exact (BitVec.add_zero _).symm,
      by gregs [hl, Nat.sub_zero], ?_, ?_, fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems [],
      by gmems []⟩
    · gregs [hok]; cases c <;> rfl
    · gmems [hl, BitVec.and_self, beq_zero32 hn]
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (p.n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : p.n = 0 := of_decide_eq_true hb
    refine ⟨?_, fun r h₁ h₂ h₃ h₄ => g₁ r h₂ h₃ h₄, rd₁, wr₁⟩
    rw [m₁, hn0]
    cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < p.n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = p.n - j ∧ j < p.n ∧ t.gpr .edi = p.D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (p.n - j) ∧ t.gpr .edx = 0 - (if c then 1 else 0) ∧
      t.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) j else zeros j) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_
    (p.n - 0) _ ⟨0, rfl, hn0, di₁, cx₁, dx₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil],
      fun r _ h₂ h₃ h₄ => g₁ r h₂ h₃ h₄, rd₁, wr₁⟩
  rintro k t ⟨j, rfl, hj, di, cx, dx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := maskStep_ok L (c := c) hj di cx dx
    (by rw [rd, wr]; exact in_left (in_off E.perm.d (by omega) (by omega)))
    (by rw [wr]; exact in_off E.perm.d (by omega) (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 p.D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 p.D + BitVec.ofNat 64 j) = s.mem (w64 p.D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 p.D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) (j + 1) else zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₄ h₂, g r h₁ h₂ h₃ h₄]
  by_cases he : j + 1 = p.n
  · left
    exact ⟨(eval_ne zf').trans (by simp [he]), by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
  · right
    exact ⟨(eval_ne zf').trans (by simp [he]), p.n - (j + 1), by omega, j + 1, rfl, by omega, di', cx',
      by rw [g' _ (by decide) (by decide) (by decide), dx], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesOcb.X86
