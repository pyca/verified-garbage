import VerifiedGarbage.Proof.AesGcmSiv.X86.Crypt

/-!
# AES-GCM-SIV on x86: comparing the tags and masking the data

Untrusted: everything here is checked by Lean. `cmp` sets `eax` to 1 if the
tags at `W` and `W + 240` are equal and 0 if not, without a branch, as
AES-GCM's `cmpTail` does (`cmp_ok`); `mask` ANDs every byte of the data with
`0 − eax`: it keeps the data if `eax` is 1 and zeroes it if `eax` is 0
(`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq bytes16_eq xor4_eq_zero w64_add in_of_covers succ_ofNat32 add_zero32
  pred_count pred_beq bytesAt_succ length_bytesAt and_self_beq32 readW_writeW_off covers_left)

/-- `cmp eax, 1` and `adc` of 0 after the OR of the XORs of two blocks' words:
1 if they are equal, else 0. -/
theorem cmpAdc (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    0#32 + 0#32 + BitVec.setWidth 32 (BitVec.ofBool (decide
      ((a₀ ^^^ b₀ ||| a₁ ^^^ b₁ ||| a₂ ^^^ b₂ ||| a₃ ^^^ b₃).toNat < (1#32).toNat))) =
      BitVec.ofNat 32 (if a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ then 1 else 0) := by
  have e := xor4_eq_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte, BitVec.xor_self, BitVec.or_self]
    decide
  · have h0 : (a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) ≠ 0 := fun h' => h (e.mp h')
    have hne : ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat ≠ 0 := fun h' =>
      h0 (BitVec.eq_of_toNat_eq (by simpa using h'))
    have hlt : ¬ ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat < (1#32).toNat := by
      rw [BitVec.toNat_ofNat]; omega
    simp only [h, ↓reduceIte, decide_eq_false hlt]
    rfl

/-- Whether the tags at `W` and `W + 240` are equal, as a word. -/
abbrev okVal (m : Mem) (W : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (if bytesAt m (w64 W) 16 = bytesAt m (w64 W + BitVec.ofNat 64 240) 16 then 1 else 0)

theorem cmp_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t', runBlock isa cmp t = some t' ∧ t'.gpr .eax = okVal t.mem p.W ∧ t'.mem = t.mem ∧
      t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [Impl.AesGcmSiv.X86.cmp, E.ebp, L.aW, E.perm.wR], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gregs []
    rw [cmpAdc]
    simp only [okVal, bytes16_eq, BitVec.add_zero, add_ofNat_assoc, Nat.reduceAdd]
  · gmems []
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals gmems []

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - BitVec.ofNat 32 (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show BitVec.ofNat 32 (if true = true then 1 else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - BitVec.ofNat 32 (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by grun [maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hb, mask_byte32]
  · gregs [hs, succ_ofNat32]
  · gregs [hc]
  · gmems [hc]
  · intro r h₁ h₂ h₃; gregs [h₁, h₂, h₃]
  all_goals gmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else Spec.GcmSiv.zeros j).length = j := by
  cases c <;> simp [Spec.GcmSiv.zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else Spec.GcmSiv.zeros (j + 1)) =
      (if c then bytesAt m P j else Spec.GcmSiv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.GcmSiv.zeros, bytesAt_succ, List.replicate_succ']

/-- What `mask` leaves, from `t`, for `eax` 1 (`c`) or 0. -/
structure MaskPost (p : Prm) (c : Bool) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  eax : t'.gpr .eax = t.gpr .eax
  mem : t'.mem = writeBytes t.mem (w64 p.D) (if c then bytesAt t.mem (w64 p.D) p.n else Spec.GcmSiv.zeros p.n)

/-- Every byte of the data ANDed with `0 − eax`, for `eax` 1 or 0. -/
theorem mask_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {c : Bool}
    (hok : s.gpr .eax = BitVec.ofNat 32 (if c then 1 else 0)) : WP isa mask s (MaskPost p c s) := by
  have hn32 := L.n32
  have hDp := E.slots.data
  have hlen := E.slots.len
  simp only [slotv_eq, dataO, lenO] at hDp hlen
  obtain ⟨s₁, run₁, m₁, bx₁, cx₁, zf₁, ax₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (.reg .eax), .mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s =
        some s₁ ∧ s₁.mem = s.mem ∧ s₁.gpr .ebx = 0 - BitVec.ofNat 32 (if c then 1 else 0) ∧
      s₁.gpr .ecx = BitVec.ofNat 32 p.n ∧ s₁.zf = some (decide (p.n = 0)) ∧ s₁.gpr .eax = s.gpr .eax ∧
      s₁.gpr .ebp = p.W ∧ s₁.gpr .esp = p.SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by grun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · gregs [hok]; rfl
    · gregs [hlen]
    · gmems [hlen]; rw [and_self_beq32 hn32]
    · gregs []
    · gregs [E.ebp]
    · gregs [E.esp]
    all_goals gmems []
  have E₁ : Env p s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁ m₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (p.n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : p.n = 0 := of_decide_eq_true hb
    refine ⟨E₁, rd₁, wr₁, ax₁, ?_⟩
    rw [m₁, hn0]
    cases c <;> simp [Spec.Aes.bytesAt, Spec.GcmSiv.zeros, writeBytes_nil]
  have hn0 : 0 < p.n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  have hd₁ : s₁.mem.readW (w64 p.W + BitVec.ofNat 64 164) 32 = p.D := by rw [m₁]; exact hDp
  obtain ⟨s₂, run₂, m₂, di₂, g₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa [.mov .edi (slot dataO)] s₁ = some s₂ ∧
      s₂.mem = s.mem ∧ s₂.gpr .edi = p.D ∧ (∀ r, r ≠ .edi → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr :=
    ⟨_, by grun [bp₁, L.aW, E₁.perm.wR, hd₁], by gmems [m₁], by gregs [hd₁], fun r h => by gregs [h],
      by gmems [rd₁], by gmems [wr₁]⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := L.dw
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = p.n - j ∧ j < p.n ∧ t.gpr .edi = p.D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (p.n - j) ∧
      t.mem = writeBytes s.mem (w64 p.D) (if c then bytesAt s.mem (w64 p.D) j else Spec.GcmSiv.zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (p.n - 0) _
    ⟨0, rfl, hn0, by rw [di₂, add_zero32], by rw [g₂ _ (by decide), cx₁, Nat.sub_zero], by
      rw [m₂]; cases c <;> simp [Spec.Aes.bytesAt, Spec.GcmSiv.zeros, writeBytes_nil], fun r _ _ _ => rfl, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := maskStep_ok t (P := p.D) (i := j) (n := p.n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), g₂ _ (by decide), bx₁]) (w64_add (by omega))
    (by rw [rd, wr]; exact in_of_covers (covers_left E.perm.d) hj (by omega))
    (by rw [wr]; exact in_of_covers E.perm.d hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 p.D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 p.D + BitVec.ofNat 64 j) = s.mem (w64 p.D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 p.D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem (w64 p.D)
      (if c then bytesAt s.mem (w64 p.D) (j + 1) else Spec.GcmSiv.zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = p.n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have fm : Frame (mutR p) s.mem t'.mem := by
    rw [hmem]
    have f0 : Frame [⟨w64 p.D, j + 1⟩] s.mem (writeBytes s.mem (w64 p.D)
        (if c then bytesAt s.mem (w64 p.D) (j + 1) else Spec.GcmSiv.zeros (j + 1))) :=
      writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
    exact frame_toMut f0 fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.D, p.n⟩, by simp, Region.sub_prefix (by omega)⟩
  have E' : Env p t' := E.mut L (by rw [gg _ (by decide) (by decide) (by decide), g₂ _ (by decide), bp₁])
    (by rw [gg _ (by decide) (by decide) (by decide), g₂ _ (by decide), sp₁]) (by rw [rd', rd]) (by rw [wr', wr]) fm
  have ax' : t'.gpr .eax = s.gpr .eax := by
    rw [gg _ (by decide) (by decide) (by decide), g₂ _ (by decide), ax₁]
  by_cases he : j + 1 = p.n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], ax', by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], p.n - (j + 1), by omega, j + 1, rfl, by omega, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.AesGcmSiv.X86
