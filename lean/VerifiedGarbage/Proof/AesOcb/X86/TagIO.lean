module
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Proof.AesOcb.X86.Env
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Ocb

import VerifiedGarbage.Proof.AesOcb.X86.HashFill
import VerifiedGarbage.Proof.AesOcb.X86.Run
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# AES-OCB on x86: the tag in and out, checking it and masking the data

Untrusted: everything here is checked by Lean. `tagOut` copies the first
`tag_len` bytes of the tag at `W` to `tag` (`tagOut_ok`); `recv` copies the
received tag to `W` (`recv_ok`); `cmp` ORs the XORs of the first `tag_len`
bytes at `W` and `W + t2O` and leaves 1 at `W + okO` if the OR is 0, else 0
(`cmp_ok`); `mask` ANDs every byte of the data with `0 − ok` (`mask_ok`).
-/

@[expose] public section

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
  have lp : LoopPre s₁ p.W p.T p.tl := ⟨di₁, dx₁, cx₁, L.tl1, by omega_arith, by have := L.ww; omega_arith, L.tw,
    by rw [rd₁, wr₁]; exact covers_prefix (covers_left E.perm.w) (by omega_arith),
    by rw [wr₁]; exact htw, (L.t_w.sub_right (Region.sub_prefix (by omega_arith))).symm⟩
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
  have lp : LoopPre s₁ p.T p.W p.tl := ⟨di₁, dx₁, cx₁, L.tl1, by omega_arith, L.tw, by have := L.ww; omega_arith,
    by rw [rd₁, wr₁]; exact E.perm.t, by rw [wr₁]; exact covers_prefix E.perm.w (by omega_arith),
    L.t_w.sub_right (Region.sub_prefix (by omega_arith))⟩
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
    rwa [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega_arith),
      Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith)] at this
  · intro h; rw [h]

theorem toNat_setWidth_xor32 (a b : Byte) : (a.setWidth 32 ^^^ b.setWidth 32).toNat < 256 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by have := a.isLt; omega_arith), Nat.mod_eq_of_lt (a := b.toNat) (by have := b.isLt; omega_arith)]
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
    rw [show 2 ^ 32 - 1 % 2 ^ 32 + x.toNat = (x.toNat - 1) + 2 ^ 32 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith), Nat.div_eq_of_lt (by omega_arith)]

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
    rw [add_ofNat_assoc32, Nat.add_zero]; exact L.aW (by omega_arith)
  have a1 : w64 (p.W + BitVec.ofNat 32 j + BitVec.ofNat 32 t2O) = w64 p.W + BitVec.ofNat 64 (t2O + j) := by
    rw [add_ofNat_assoc32, Nat.add_comm]; exact L.aW (by simp only [t2O]; omega_arith)
  have r0 : InRegions (u.rd ++ u.wr) (w64 p.W + BitVec.ofNat 64 j) 1 := E.perm.wR (by omega_arith)
  have r1 : InRegions (u.rd ++ u.wr) (w64 p.W + BitVec.ofNat 64 (t2O + j)) 1 := E.perm.wR (by simp only [t2O]; omega_arith)
  refine ⟨_, by grun [hdi, a0, a1, r0, r1], by gmems [], by gregs [], ?_, ?_, ?_,
    fun r h₁ h₂ h₃ h₄ h₅ => by gregs [h₁, h₂, h₃, h₄, h₅], by gmems [], by gmems []⟩
  · gregs [hdi]; rw [add_ofNat_assoc32]
  · gregs [hcx]; rw [sub1_32 (by omega_arith) (by omega_arith), show tl - j - 1 = tl - (j + 1) by omega_arith]
  · gmems [hcx]
    rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

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
    ⟨0, rfl, by omega_arith, di₁, cx₁, by rw [dx₁]; decide, by rw [dx₁]; simp [bytesAt], m₁,
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
      exact ⟨(eval_ne zf').trans (by simp [he]), p.tl - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, di', cx', lt', iff',
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

/-- `0 − ok` in every word of an SSE register. -/
def maskX (c : Bool) : BitVec 128 := if c then BitVec.allOnes 128 else 0

theorem mask_xmm (c : Bool) :
    shufDwords ((0 : BitVec 96) ++ ((0 : BitVec 32) - (if c then 1 else 0))) 0 = maskX c := by
  cases c <;> decide

theorem mask_block (v : BitVec 128) (c : Bool) : v &&& maskX c = if c then v else 0 := by
  cases c
  · simp [maskX]
  · simp only [maskX, ite_true, BitVec.and_allOnes]

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

theorem mask_add (m : Mem) (P : Addr) (c : Bool) (a b : Nat) :
    (if c then bytesAt m P (a + b) else zeros (a + b)) =
      (if c then bytesAt m P a else zeros a) ++
        (if c then bytesAt m (P + BitVec.ofNat 64 a) b else zeros b) := by
  cases c <;> simp [zeros, Proof.Ocb.bytesAt_append, ← List.replicate_append_replicate]

/-- A block written is its 16 bytes written. -/
theorem writeW_eq_writeBytes (m : Mem) (a : Addr) (v : BitVec 128) :
    m.writeW a v = writeBytes m a ((List.range 16).map fun k => v.extractLsb' (8 * k) 8) :=
  write_eq_writeBytes m a 16 v

/-- The block at `a`, or zero, written back: the 16 bytes at `a` masked. -/
theorem writeW_mask (m m' : Mem) (a : Addr) (c : Bool) :
    m'.writeW a (if c then m.readW a 128 else (0 : BitVec 128)) =
      writeBytes m' a (if c then bytesAt m a 16 else zeros 16) := by
  rw [writeW_eq_writeBytes]
  refine congrArg (writeBytes m' a) ?_
  cases c
  · simp [zeros]; decide
  · simp only [ite_true, bytesAt]
    refine List.map_congr_left fun k hk => ?_
    rw [List.mem_range] at hk
    rw [← Mem.extractLsb'_read m a (n := 16) hk]
    rfl

/-- What both loops keep: `edi` after the first `j` bytes of the data, which
are masked, and the mask in `edx` and `xmm0`. -/
structure MInv (p : Prm) (s s₁ t : State) (c : Bool) (j : Nat) : Prop where
  edi : t.gpr .edi = p.D + BitVec.ofNat 32 j
  mem : t.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) j else zeros j)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → t.gpr r = s₁.gpr r
  xmm0 : t.xmm .xmm0 = s₁.xmm .xmm0
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem MInv.frame {p : Prm} {s s₁ t : State} {c : Bool} {j : Nat} (h : MInv p s s₁ t c j) :
    Frame [⟨w64 p.D, j⟩] s.mem t.mem := by
  rw [h.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)

/-- The bytes from `j` on are as they were. -/
theorem MInv.at {p : Prm} {s s₁ t : State} {c : Bool} {j i : Nat} (h : MInv p s s₁ t c j) (hi : j ≤ i)
    (hi' : i < 2 ^ 64) : t.mem (w64 p.D + BitVec.ofNat 64 i) = s.mem (w64 p.D + BitVec.ofNat 64 i) :=
  h.frame (w64 p.D + BitVec.ofNat 64 i) fun r hr hcon => by
    simp only [List.mem_singleton] at hr; subst hr
    simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 p.D) hi'] at hcon; omega_arith

theorem MInv.readW {p : Prm} {s s₁ t : State} {c : Bool} {j : Nat} (h : MInv p s s₁ t c j)
    (hj : j + 16 < 2 ^ 64) :
    t.mem.readW (w64 p.D + BitVec.ofNat 64 j) 128 = s.mem.readW (w64 p.D + BitVec.ofNat 64 j) 128 := by
  refine Mem.readW_congr fun k hk => ?_
  rw [add_ofNat_assoc]
  exact h.at (by omega_arith) (by omega_arith)

/-- One step of `maskBlocks`. -/
theorem maskBlock_ok {p : Prm} (L : Lay p) {u : State} {j w : Nat} {c : Bool} (hj : j + 16 ≤ p.n) (hw : 0 < w)
    (hw' : w < 2 ^ 32) (hdi : u.gpr .edi = p.D + BitVec.ofNat 32 j) (hax : u.gpr .eax = BitVec.ofNat 32 w)
    (hx0 : u.xmm .xmm0 = maskX c)
    (r : InRegions (u.rd ++ u.wr) (w64 p.D + BitVec.ofNat 64 j) 16)
    (w16 : InRegions u.wr (w64 p.D + BitVec.ofNat 64 j) 16) :
    ∃ u', runBlock isa [.movdquLoad .xmm1 (at_ .edi 0), .xop (.bin .pand .xmm1 .xmm0),
        .movdquStore (at_ .edi 0) .xmm1, .alu .add .edi (imm 16), .alu .sub .eax (imm 1)] u = some u' ∧
      u'.mem = u.mem.writeW (w64 p.D + BitVec.ofNat 64 j)
        (if c then u.mem.readW (w64 p.D + BitVec.ofNat 64 j) 128 else (0 : BitVec 128)) ∧
      u'.gpr .edi = p.D + BitVec.ofNat 32 (j + 16) ∧ u'.gpr .eax = BitVec.ofNat 32 (w - 1) ∧
      u'.zf = some (decide (w = 1)) ∧ u'.xmm .xmm0 = u.xmm .xmm0 ∧
      (∀ r, r ≠ .eax → r ≠ .edi → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := L.n32
  have a0 : w64 (p.D + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.D + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact w64_add (by have := L.dw; omega_arith)
  refine ⟨_, by srun [hdi, a0, r, w16], by smems [hdi, a0, hx0, eval_pand, mask_block], ?_, ?_, ?_, by smems [],
    fun r h₁ h₂ => by sregs [h₁, h₂], by smems [], by smems []⟩
  · sregs [hdi]; rw [add_ofNat_assoc32]
  · sregs [hax]; rw [sub1_32 (by omega_arith) (by omega_arith)]
  · smems [hax]
    rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- One step of `maskBytes`. -/
theorem maskStep_ok {p : Prm} (L : Lay p) {u : State} {j w : Nat} {c : Bool} (hj : j < p.n) (hw : 0 < w)
    (hw' : w < 2 ^ 32) (hdi : u.gpr .edi = p.D + BitVec.ofNat 32 j) (hcx : u.gpr .ecx = BitVec.ofNat 32 w)
    (hdx : u.gpr .edx = 0 - (if c then 1 else 0))
    (r : InRegions (u.rd ++ u.wr) (w64 p.D + BitVec.ofNat 64 j) 1) (w1 : InRegions u.wr (w64 p.D + BitVec.ofNat 64 j) 1) :
    ∃ u', runBlock isa [.movzx8 .eax (at_ .edi 0), .alu .and .eax (.reg .edx), .store8 (at_ .edi 0) .al,
        .alu .add .edi (imm 1), .alu .sub .ecx (imm 1)] u = some u' ∧
      u'.mem = u.mem.writeW (w64 p.D + BitVec.ofNat 64 j)
        ((if c then u.mem (w64 p.D + BitVec.ofNat 64 j) else 0 : Byte)) ∧
      u'.gpr .edi = p.D + BitVec.ofNat 32 (j + 1) ∧ u'.gpr .ecx = BitVec.ofNat 32 (w - 1) ∧
      u'.zf = some (decide (w = 1)) ∧ u'.xmm = u.xmm ∧
      (∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → u'.gpr r = u.gpr r) ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  have hn := L.n32
  have a0 : w64 (p.D + BitVec.ofNat 32 j + BitVec.ofNat 32 0) = w64 p.D + BitVec.ofNat 64 j := by
    rw [add_ofNat_assoc32, Nat.add_zero]; exact w64_add (by have := L.dw; omega_arith)
  refine ⟨_, by grun [hdi, a0, r, w1], by gmems [hdx, mask_byte32], ?_, ?_, ?_, by smems [],
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  · gregs [hdi]; rw [add_ofNat_assoc32]
  · gregs [hcx]; rw [sub1_32 (by omega_arith) (by omega_arith)]
  · gmems [hcx]
    rw [sub1_32 (by omega_arith) (by omega_arith), beq_zero32 (by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))

/-- The blocks: from `j = 16 i`, with `n / 16 − i` blocks left in `eax`, to
`16 (n / 16)`. -/
theorem maskBlocks_wp {p : Prm} (L : Lay p) {s s₁ t : State} {c : Bool} {i : Nat}
    (hD : Covers [⟨w64 p.D, p.n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨w64 p.D, p.n⟩] s.wr)
    (hx0 : s₁.xmm .xmm0 = maskX c) (hi : i < p.n / 16) (ht : MInv p s s₁ t c (16 * i))
    (hax : t.gpr .eax = BitVec.ofNat 32 (p.n / 16 - i)) (hcx : t.gpr .ecx = s₁.gpr .ecx) :
    WP isa maskBlocks t fun t' => MInv p s s₁ t' c (16 * (p.n / 16)) ∧ t'.gpr .ecx = s₁.gpr .ecx := by
  have hn := L.n32
  have hd := L.dw
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ i, k = p.n / 16 - i ∧ i < p.n / 16 ∧ MInv p s s₁ t c (16 * i) ∧
      t.gpr .eax = BitVec.ofNat 32 (p.n / 16 - i) ∧ t.gpr .ecx = s₁.gpr .ecx) ?_ (p.n / 16 - i) t
    ⟨i, rfl, hi, ht, hax, hcx⟩
  rintro k t ⟨i, rfl, hi, ht, hax, hcx⟩
  have hin : 16 * i + 16 ≤ p.n := by omega_arith
  obtain ⟨t', run', mem', di', ax', zf', x0', g', rd', wr'⟩ := maskBlock_ok L (c := c) hin
    (show 0 < p.n / 16 - i by omega_arith) (by omega_arith) ht.edi hax (by rw [ht.xmm0, hx0])
    (by rw [ht.rd, ht.wr]; exact in_off hD (by omega_arith) (by omega_arith))
    (by rw [ht.wr]; exact in_off hDw (by omega_arith) (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem (w64 p.D)
      (if c then bytesAt s.mem (w64 p.D) (16 * (i + 1)) else zeros (16 * (i + 1))) := by
    rw [mem', ht.readW (by omega_arith), ht.mem, writeW_mask, show 16 * (i + 1) = 16 * i + 16 by omega_arith, mask_add,
      ← writeBytes_append _ _ _ _ (by rw [length_mask, length_mask]; omega_arith), length_mask]
  have e1 : p.n / 16 - i - 1 = p.n / 16 - (i + 1) := by omega_arith
  have hz : t'.zf = some (decide (i + 1 = p.n / 16)) := by
    rw [zf']; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have ht' : MInv p s s₁ t' c (16 * (i + 1)) :=
    ⟨by rw [di', show 16 * (i + 1) = 16 * i + 16 by omega_arith], hmem,
      fun r h₁ h₂ h₃ => by rw [g' r h₁ h₃, ht.keep r h₁ h₂ h₃], by rw [x0', ht.xmm0], by rw [rd', ht.rd],
      by rw [wr', ht.wr]⟩
  have hcx' : t'.gpr .ecx = s₁.gpr .ecx := by rw [g' _ (by decide) (by decide), hcx]
  by_cases he : i + 1 = p.n / 16
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht', hcx'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), p.n / 16 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ht',
      by rw [ax', e1], hcx'⟩

/-- The last bytes: from `j < n` to `n`, with `n − j` left in `ecx`. -/
theorem maskBytes_wp {p : Prm} (L : Lay p) {s s₁ t : State} {c : Bool} {j : Nat}
    (hD : Covers [⟨w64 p.D, p.n⟩] (s.rd ++ s.wr)) (hDw : Covers [⟨w64 p.D, p.n⟩] s.wr)
    (hdx : s₁.gpr .edx = 0 - (if c then 1 else 0)) (hj : j < p.n) (ht : MInv p s s₁ t c j)
    (hcx : t.gpr .ecx = BitVec.ofNat 32 (p.n - j)) :
    WP isa maskBytes t fun t' => MInv p s s₁ t' c p.n := by
  have hn := L.n32
  have hd := L.dw
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = p.n - j ∧ j < p.n ∧ MInv p s s₁ t c j ∧
      t.gpr .ecx = BitVec.ofNat 32 (p.n - j)) ?_ (p.n - j) t ⟨j, rfl, hj, ht, hcx⟩
  rintro k t ⟨j, rfl, hj, ht, hcx⟩
  obtain ⟨t', run', mem', di', cx', zf', x', g', rd', wr'⟩ := maskStep_ok L (c := c) hj
    (show 0 < p.n - j by omega_arith) (by omega_arith) ht.edi hcx
    (by rw [ht.keep _ (by decide) (by decide) (by decide), hdx])
    (by rw [ht.rd, ht.wr]; exact in_off hD (by omega_arith) (by omega_arith))
    (by rw [ht.wr]; exact in_off hDw (by omega_arith) (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hmem : t'.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) (j + 1) else zeros (j + 1)) := by
    rw [mem', ht.at (Nat.le_refl _) (by omega_arith), ht.mem, mask_succ,
      writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  have hz : t'.zf = some (decide (j + 1 = p.n)) := by
    rw [zf']; exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have ht' : MInv p s s₁ t' c (j + 1) :=
    ⟨di', hmem, fun r h₁ h₂ h₃ => by rw [g' r h₁ h₃ h₂, ht.keep r h₁ h₂ h₃], by rw [x', ht.xmm0], by rw [rd', ht.rd],
      by rw [wr', ht.wr]⟩
  by_cases he : j + 1 = p.n
  · left
    exact ⟨(eval_ne hz).trans (by simp [he]), by rw [← he]; exact ht'⟩
  · right
    exact ⟨(eval_ne hz).trans (by simp [he]), p.n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, ht',
      by rw [cx', show p.n - j - 1 = p.n - (j + 1) by omega_arith]⟩

/-- The head of `mask`: the data in `edi`, `0 − ok` in `edx` and in every
word of `xmm0`, the whole blocks in `eax` and the bytes after them in `ecx`. -/
theorem maskHead_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {c : Bool}
    (hok : slotv s.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) :
    ∃ s₁, runBlock isa [.mov .edi (slot dataO), .mov .ecx (slot lenO), .mov .edx (imm 0),
        .alu .sub .edx (slot okO), .xop (.movd .xmm0 .edx), .xop (.pshufd .xmm0 .xmm0 0), .mov .eax (.reg .ecx),
        .shift .shr .eax 4, .alu .and .ecx (imm 15), .alu .test .eax (.reg .eax)] s = some s₁ ∧
      s₁.gpr .edi = p.D + BitVec.ofNat 32 0 ∧ s₁.gpr .ecx = BitVec.ofNat 32 (p.n % 16) ∧
      s₁.gpr .edx = 0 - (if c then 1 else 0) ∧ s₁.gpr .eax = BitVec.ofNat 32 (p.n / 16 - 0) ∧
      s₁.zf = some (decide (p.n / 16 = 0)) ∧ s₁.xmm .xmm0 = maskX c ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
  have hn := L.n32
  have hD := E.slots.data
  have hl := E.slots.len
  simp only [slotv_eq] at hD hl hok
  have hdx : (0 : BitVec 32) - (if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) = 0 - (if c then 1 else 0) := by
    cases c <;> rfl
  refine ⟨_, by srun [E.ebp, L.aW, E.perm.wR, hD, hl, hok], by sregs [hD]; exact (BitVec.add_zero _).symm,
    ?_, by sregs [hok]; exact hdx, by sregs [hl, Proof.AesGcm.X86.shr4 hn, Nat.sub_zero], ?_, ?_,
    fun r h₁ h₂ h₃ h₄ => by sregs [h₁, h₂, h₃, h₄], by smems [], by smems [], by smems []⟩
  · sregs [hl]
    exact (Proof.AesGcm.X86.and15 _).trans (by rw [toNat_ofNat32 hn])
  · smems [hl, Proof.AesGcm.X86.shr4 hn, BitVec.and_self, beq_zero32 (show p.n / 16 < 2 ^ 32 by omega_arith)]
  · smems [hok, hdx]; exact mask_xmm c

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or
0: its whole blocks, then the rest. -/
theorem mask_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {c : Bool}
    (hok : slotv s.mem p.W okO = if c then BitVec.ofNat 32 1 else BitVec.ofNat 32 0) :
    WP isa mask s fun s' => s'.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) p.n else zeros p.n) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := L.n32
  obtain ⟨s₁, run₁, di₁, cx₁, dx₁, ax₁, zf₁, x0₁, g₁, m₁, rd₁, wr₁⟩ := maskHead_ok L E hok
  have hD : Covers [⟨w64 p.D, p.n⟩] (s.rd ++ s.wr) := covers_left E.perm.d
  have inv₀ : MInv p s s₁ s₁ c (16 * 0) :=
    ⟨di₁, by rw [m₁]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], fun _ _ _ _ => rfl, rfl, rd₁, wr₁⟩
  have fin : ∀ {t : State}, MInv p s s₁ t c p.n →
      t.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) p.n else zeros p.n) ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr :=
    fun ht => ⟨ht.mem, fun r h₁ h₂ h₃ h₄ => by rw [ht.keep r h₁ h₂ h₄, g₁ r h₁ h₂ h₃ h₄], ht.rd, ht.wr⟩
  -- The blocks.
  have words : WP isa (.ite .e (.block []) maskBlocks) s₁ fun t =>
      MInv p s s₁ t c (16 * (p.n / 16)) ∧ t.gpr .ecx = s₁.gpr .ecx := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact ⟨inv₀, rfl⟩
    · exact maskBlocks_wp L hD E.perm.d x0₁ (Nat.pos_of_ne_zero (of_decide_eq_false hb)) inv₀ ax₁ rfl
  unfold mask
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono words fun t ⟨ht, hcx⟩ => ?_)
  -- The rest.
  have cx : t.gpr .ecx = BitVec.ofNat 32 (p.n - 16 * (p.n / 16)) := by
    rw [hcx, cx₁]; exact congrArg _ (by omega_arith)
  obtain ⟨t₁, run₂, zf₂, g₂, m₂, x₂, rd₂, wr₂⟩ : ∃ t₁, runBlock isa [.alu .test .ecx (.reg .ecx)] t = some t₁ ∧
      t₁.zf = some (decide (16 * (p.n / 16) = p.n)) ∧ t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.xmm = t.xmm ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by grun [], ?_, by gmems [], by gmems [], by smems [], by gmems [], by gmems []⟩
    gmems [cx, BitVec.and_self, beq_zero32 (show p.n - 16 * (p.n / 16) < 2 ^ 32 by omega_arith)]
    exact congrArg some (decide_eq_decide.mpr (by omega_arith))
  have ht₁ : MInv p s s₁ t₁ c (16 * (p.n / 16)) :=
    ⟨by rw [g₂, ht.edi], by rw [m₂, ht.mem], fun r h₁ h₂ h₃ => by rw [g₂, ht.keep r h₁ h₂ h₃],
      by rw [x₂, ht.xmm0], by rw [rd₂, ht.rd], by rw [wr₂, ht.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₂, ?_⟩)
  refine WP.ite (decide (16 * (p.n / 16) = p.n)) (eval_e zf₂) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have e := of_decide_eq_true hb
    rw [e] at ht₁; exact fin ht₁
  · exact WP.mono (maskBytes_wp L hD E.perm.d dx₁ (by have := of_decide_eq_false hb; omega_arith) ht₁
      (by rw [g₂, cx])) fun t' ht' => fin ht'

end VG.Proof.AesOcb.X86
