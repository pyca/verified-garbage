module

import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Open
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Finish
public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Small
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Run
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch

/-! ### `AesGcm.X86_64.Short.Cond`, which this module and modules that import it used -/

section

/-!
# AES-GCM's short path on x86-64: the condition

Untrusted: everything here is checked by Lean. `cond` leaves ZF clear iff
the short path applies: a 12-byte nonce, fewer than 512 bytes of additional
data and of text, fewer than 32 blocks of them, and some text or more than 16
bytes of additional data (`cond_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64

/-- When the short path applies. -/
abbrev IsShort (nl al n : Nat) : Prop :=
  nl = 12 ∧ al < 512 ∧ n < 512 ∧ nb16 al + nb16 n < 32 ∧ (0 < n ∨ 16 < al)

/-- Both below `512` iff their OR is. -/
theorem or_lt_512 {a b : Nat} : a ||| b < 512 ↔ a < 512 ∧ b < 512 := by
  constructor
  · intro h
    exact ⟨Nat.lt_of_le_of_lt Nat.left_le_or h, Nat.lt_of_le_of_lt Nat.right_le_or h⟩
  · rintro ⟨ha, hb⟩
    exact Nat.or_lt_two_pow (n := 9) ha hb

/-- What `cond` keeps. -/
structure CondKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem CondKeep.trans {s₁ s₂ s₃ : State} (h₁ : CondKeep s₁ s₂) (h₂ : CondKeep s₂ s₃) : CondKeep s₁ s₃ :=
  ⟨fun r a b c => (h₂.gpr r a b c).trans (h₁.gpr r a b c), h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

/-- What `cond` reads: `W` in `r15`, the nonce's length in `rbp` and the
lengths of the additional data and the text in `W`. -/
structure CondS (W : Addr) (nl al n : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = W
  w : Covers [⟨W, 2560⟩] s.wr
  rbp : s.gpr .rbp = BitVec.ofNat 64 nl
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n

theorem CondS.keep {W : Addr} {nl al n : Nat} {s t : State} (h : CondS W nl al n s) (k : CondKeep s t) :
    CondS W nl al n t :=
  ⟨by rw [k.gpr _ (by decide) (by decide) (by decide), h.r15], by rw [k.wr]; exact h.w,
    by rw [k.gpr _ (by decide) (by decide) (by decide), h.rbp], by rw [k.mem]; exact h.alen,
    by rw [k.mem]; exact h.len⟩

/-- `cond`'s first block: `rax := 0`, and the nonce's length compared with 12. -/
theorem condB1_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) (hnl : nl < 2 ^ 64) :
    WP isa (.block [.mov32 .rax (imm 0), .alu .cmp .rbp (imm 12)]) s fun t =>
      t.zf = some (decide (nl = 12)) ∧ t.gpr .rax = 0 ∧ CondKeep s t := by
  obtain ⟨s₁, run₁, ax₁, k₁⟩ : ∃ s₁, runBlock isa [.mov32 .rax (imm 0)] s = some s₁ ∧
      s₁.gpr .rax = 0 ∧ CondKeep s s₁ := by
    refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r hr _ _; simp [gpr_setReg, hr]
    all_goals rfl
  obtain ⟨s₂, run₂, zf₂, -, g₂, m₂, rd₂, wr₂⟩ :=
    cmpImm_ok s₁ .rbp (by rw [k₁.gpr _ (by decide) (by decide) (by decide), h.rbp]) hnl (show 12 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, zf₂, by rw [g₂, ax₁],
    k₁.trans ⟨fun r _ _ _ => by rw [g₂], m₂, rd₂, wr₂⟩⟩⟩)

/-- `cond`'s second block: the OR of the lengths compared with 512. -/
theorem condB2_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) (hal : al < 2 ^ 64)
    (hn : n < 2 ^ 64) :
    WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .or .rcx (.mem (at_ .r15 lenO)),
        .alu .cmp .rcx (imm 512)]) s fun t =>
      t.cf = some (decide (al ||| n < 512)) ∧ t.gpr .rax = s.gpr .rax ∧ CondKeep s t := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := in_left (in_off h.w (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off h.w (by decide) (by decide))
  have hal' := h.alen
  have hn' := h.len
  have h15 := h.r15
  have hor : BitVec.ofNat 64 al ||| BitVec.ofNat 64 n = BitVec.ofNat 64 (al ||| n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal,
      Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (Nat.or_lt_two_pow hal hn)]
  obtain ⟨s₃, run₃, cx₃, ax₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .rcx (.mem (at_ .r15 alenO)),
      .alu .or .rcx (.mem (at_ .r15 lenO))] s = some s₃ ∧ s₃.gpr .rcx = BitVec.ofNat 64 (al ||| n) ∧
      s₃.gpr .rax = s.gpr .rax ∧ CondKeep s s₃ := by
    refine ⟨_, by xrun [h15, hal', hn', r₁, r₂, alenO, lenO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true]
      exact hor
    · simp [gpr_setReg, gpr_arithFlags]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, b]
    all_goals rfl
  obtain ⟨s₄, run₄, -, cf₄, g₄, m₄, rd₄, wr₄⟩ :=
    cmpImm_ok s₃ .rcx cx₃ (Nat.or_lt_two_pow hal hn) (show 512 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₃, run₃, WP.of_runBlock ⟨s₄, run₄, cf₄, by rw [g₄, ax₃],
    k₃.trans ⟨fun r _ _ _ => by rw [g₄], m₄, rd₄, wr₄⟩⟩⟩)

/-- `cond`'s third block: the blocks of both lengths compared with 32. -/
theorem condB3_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) (hal : al < 512) (hn : n < 512) :
    WP isa (.block [.mov .rcx (.mem (at_ .r15 alenO)), .alu .add .rcx (imm 15), .shift .shr .rcx 4,
        .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (imm 15), .shift .shr .rdx 4, .alu .add .rcx (.reg .rdx),
        .alu .cmp .rcx (imm 32)]) s fun t =>
      t.cf = some (decide (nb16 al + nb16 n < 32)) ∧ t.gpr .rax = s.gpr .rax ∧ CondKeep s t := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := in_left (in_off h.w (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off h.w (by decide) (by decide))
  have hal' := h.alen
  have hn' := h.len
  have h15 := h.r15
  have e₁ : BitVec.ofNat 64 (al + 15) >>> 4 = BitVec.ofNat 64 (nb16 al) := shr4 _ (by omega_using [hal])
  have e₂ : BitVec.ofNat 64 (n + 15) >>> 4 = BitVec.ofNat 64 (nb16 n) := shr4 _ (by omega_using [hn])
  obtain ⟨s₅, run₅, cx₅, ax₅, k₅⟩ : ∃ s₅, runBlock isa [.mov .rcx (.mem (at_ .r15 alenO)), .alu .add .rcx (imm 15),
      .shift .shr .rcx 4, .mov .rdx (.mem (at_ .r15 lenO)), .alu .add .rdx (imm 15), .shift .shr .rdx 4,
      .alu .add .rcx (.reg .rdx)] s = some s₅ ∧ s₅.gpr .rcx = BitVec.ofNat 64 (nb16 al + nb16 n) ∧
      s₅.gpr .rax = s.gpr .rax ∧ CondKeep s s₅ := by
    refine ⟨_, by xrun [execShift, h15, hal', hn', r₁, r₂, alenO, lenO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, hal', hn', ofNat_add_ofNat, e₁, e₂]
    · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, b, c]
    all_goals rfl
  obtain ⟨s₆, run₆, -, cf₆, g₆, m₆, rd₆, wr₆⟩ :=
    cmpImm_ok s₅ .rcx cx₅ (by simp only [nb16]; omega_using [hal, hn]) (show 32 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₅, run₅, WP.of_runBlock ⟨s₆, run₆, cf₆, by rw [g₆, ax₅],
    k₅.trans ⟨fun r _ _ _ => by rw [g₆], m₆, rd₆, wr₆⟩⟩⟩)

/-- `cond`'s fourth block: `al + 17 n` compared with 17, which it is below
iff there is no text and at most 16 bytes of additional data. -/
theorem condB4_ok {W : Addr} {nl al n : Nat} {s : State} (h : CondS W nl al n s) (hal : al < 512) (hn : n < 512) :
    WP isa (.block [.mov .rdx (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rdx), .shift .shl .rcx 4,
        .alu .add .rcx (.reg .rdx), .alu .add .rcx (.mem (at_ .r15 alenO)), .alu .cmp .rcx (imm 17)]) s fun t =>
      t.cf = some (decide (al + 17 * n < 17)) ∧ t.gpr .rax = s.gpr .rax ∧ CondKeep s t := by
  have r₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 184) 8 := in_left (in_off h.w (by decide) (by decide))
  have r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 208) 8 := in_left (in_off h.w (by decide) (by decide))
  have hal' := h.alen
  have hn' := h.len
  have h15 := h.r15
  have e₁ : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_using [hn]), Nat.mod_eq_of_lt (by omega_using [hn])]
    omega_using []
  obtain ⟨s₅, run₅, cx₅, ax₅, k₅⟩ : ∃ s₅, runBlock isa [.mov .rdx (.mem (at_ .r15 lenO)), .mov .rcx (.reg .rdx),
      .shift .shl .rcx 4, .alu .add .rcx (.reg .rdx), .alu .add .rcx (.mem (at_ .r15 alenO))] s = some s₅ ∧
      s₅.gpr .rcx = BitVec.ofNat 64 (al + 17 * n) ∧ s₅.gpr .rax = s.gpr .rax ∧ CondKeep s s₅ := by
    refine ⟨_, by xrun [execShift, h15, hal', hn', r₁, r₂, alenO, lenO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, reduceCtorEq, ite_false, hn', hal', e₁,
        ofNat_add_ofNat]
      congr 1
      omega_using []
    · simp [gpr_setReg, gpr_arithFlags, gpr_setFlags]
    · intro r a b c; simp [gpr_setReg, gpr_arithFlags, gpr_setFlags, b, c]
    all_goals rfl
  obtain ⟨s₆, run₆, -, cf₆, g₆, m₆, rd₆, wr₆⟩ :=
    cmpImm_ok s₅ .rcx cx₅ (by omega_using [hal, hn]) (show 17 < 2 ^ 31 by decide)
  exact WP.block_append_iff.mpr (WP.of_runBlock ⟨s₅, run₅, WP.of_runBlock ⟨s₆, run₆, cf₆, by rw [g₆, ax₅],
    k₅.trans ⟨fun r _ _ _ => by rw [g₆], m₆, rd₆, wr₆⟩⟩⟩)

theorem eval_ne {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .ne s = some !b := by
  show s.zf.map _ = _; rw [h]; rfl
theorem eval_ae {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .ae s = some !b := by
  show s.cf.map _ = _; rw [h]; rfl

/-- `cond`: ZF clear iff the short path applies, with `rbp` the nonce's length
and the lengths of the additional data and the text in `W`. -/
theorem cond_ok {s : State} {W : Addr} {nl al n : Nat} (h : CondS W nl al n s) (hnl : nl < 2 ^ 64)
    (hal : al < 2 ^ 64) (hn : n < 2 ^ 64) :
    WP isa cond s fun s' => s'.zf = some (decide ¬IsShort nl al n) ∧ CondKeep s s' := by
  refine WP.seq (WP.mono (condB1_ok h hnl) fun s₂ ⟨zf₂, ax₂, k₂⟩ => ?_)
  -- `rax := 1` iff the short path applies.
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .rax = BitVec.ofNat 64 (if IsShort nl al n then 1 else 0) ∧
      CondKeep s s₃) (WP.ite (!decide (nl = 12)) (eval_ne zf₂) (fun h12 => ?_) (fun h12 => ?_)) fun s₃ ⟨ax₃, k₃⟩ => ?_)
  · have h12 : nl ≠ 12 := by simpa using h12
    refine WP.block_nil ⟨?_, k₂⟩
    rw [ax₂]
    simp [IsShort, h12]
  · have h12 : nl = 12 := by simpa using h12
    refine WP.seq (WP.mono (condB2_ok (h.keep k₂) hal hn) fun s₄ ⟨cf₄, ax₄, k₄⟩ => ?_)
    rw [ax₂] at ax₄
    refine WP.ite (!decide (al ||| n < 512)) (eval_ae cf₄) (fun h5 => ?_) (fun h5 => ?_)
    · have h5 : ¬(al < 512 ∧ n < 512) := fun h => by simp [or_lt_512.mpr h] at h5
      refine WP.block_nil ⟨?_, k₂.trans k₄⟩
      have h5' : ¬IsShort nl al n := fun ⟨_, a, b, _⟩ => h5 ⟨a, b⟩
      rw [ax₄]
      simp only [h5', ↓reduceIte]
      rfl
    · have h5 : al < 512 ∧ n < 512 := or_lt_512.mp (by simpa using h5)
      refine WP.seq (WP.mono (condB3_ok ((h.keep k₂).keep k₄) h5.1 h5.2) fun s₆ ⟨cf₆, ax₆, k₆⟩ => ?_)
      rw [ax₄] at ax₆
      refine WP.ite (!decide (nb16 al + nb16 n < 32)) (eval_ae cf₆) (fun h32 => ?_) (fun h32 => ?_)
      · have h32 : ¬nb16 al + nb16 n < 32 := fun h => by simp [h] at h32
        exact WP.block_nil ⟨by simp [ax₆, IsShort, h32], k₂.trans (k₄.trans k₆)⟩
      · have h32 : nb16 al + nb16 n < 32 := by simpa using h32
        refine WP.seq (WP.mono (condB4_ok (((h.keep k₂).keep k₄).keep k₆) h5.1 h5.2) fun s₈ ⟨cf₈, ax₈, k₈⟩ => ?_)
        rw [ax₆] at ax₈
        refine WP.ite (decide (al + 17 * n < 17)) (eval_b cf₈) (fun h17 => ?_) (fun h17 => ?_)
        · have h17 : al + 17 * n < 17 := by simpa using h17
          have hs : ¬IsShort nl al n := fun ⟨_, _, _, _, z⟩ => by omega_arith
          exact WP.block_nil ⟨by simp [ax₈, hs], k₂.trans (k₄.trans (k₆.trans k₈))⟩
        · have h17 : ¬al + 17 * n < 17 := by simpa using h17
          have hs : IsShort nl al n := ⟨h12, h5.1, h5.2, h32, by omega_using [h17]⟩
          refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
          · have e : (if IsShort nl al n then 1 else 0) = 1 := ite_eq_left_iff.mpr fun h => absurd hs h
            rw [e]
            simp [gpr_setReg]
          · exact k₂.trans (k₄.trans (k₆.trans (k₈.trans ⟨fun r a _ _ => by simp [gpr_setReg, a], rfl, rfl, rfl⟩)))
  -- `test rax, rax`.
  refine WP.of_runBlock ⟨_, by xrun [], ?_, ?_⟩
  · rw [zf_arithFlags, ax₃]
    split <;> rename_i h <;> simp [h]
  · exact k₃.trans ⟨fun r _ _ _ => by simp [gpr_arithFlags], rfl, rfl, rfl⟩

end VG.Proof.AesGcm.X86_64.Short

end

end

/-!
# AES-GCM's short path on x86-64: `seal` and `open`

Untrusted: everything here is checked by Lean. After the entry, `cond`
chooses the short path (`IsShort`) or the other instances' body: `seal`
leaves what `sealRun_ok` does either way (`sealShort_ok`; the other
instances' body with `finish` at its end, `sealRunF_ok`), and `open`, for a
tag length it allows, what `openOk_ok` does (`openShort_ok`), so the rest of
`sealM_wp`'s and `openM_wp`'s proofs applies (`sealM_of`, `openM_of`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Proof.AesGcm.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxH ctxCiph gctr inc32)

/-- What `cond` reads, after the entry. -/
theorem condS_of {s₀ s₁ : State} {Ctx W SP A D : Addr} {nl al n : Nat} (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) : CondS W nl al n s₁ :=
  ⟨E.env.r15, E.env.perm.w, by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.len⟩

/-- `cond` after the entry: ZF clear iff the short path applies, and the
entry kept. -/
theorem condE_ok {k : Nat} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ k Ctx W SP Np A D nl al n) (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) :
    WP isa Impl.AesGcm.X86_64.Short.cond s₁ fun s₂ => s₂.zf = some (decide ¬IsShort nl al n) ∧
      OneEntry s₀ Ctx W SP A D n s₂ ∧ CondKeep s₁ s₂ := by
  have hlt := C.data.ok.lt
  refine WP.mono (cond_ok (condS_of E hnl hal) (by rw [← hnl]; exact BitVec.isLt _) (by rw [← hal]; exact BitVec.isLt _)
    (by omega_using [hlt])) fun s₂ ⟨hz, K⟩ => ⟨hz, ?_, K⟩
  exact E.keep C.lay (fun r hr => K.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) K.rd K.wr (by rw [K.mem]; exact Frame.refl _ _)

/-- After the entry, the long `seal` up to the tag at `W`: additional data
absorbed by `aadP`, which leaves what `oneAad` does, then `oneBlocks` and
`finishWith ks` leave what `sealRun_ok` does. -/
theorem sealRunW_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {aadP : Prog isa} {s₀ s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (hal : (s₀.gpr .r9).toNat = al)
    (ha : WP isa aadP s₁
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s₁.mem)) :
    WP isa (.seq aadP (.seq (oneBlocks B.enc) (Impl.AesGcm.X86_64.Short.finishWith ks))) s₁
      (SealRunPost s₀ Ctx W SP Np A D nl al n) := by
  have L := C.lay
  unfold SealRunPost
  generalize hR : (s₀.gpr .rsi).toNat = R
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  refine WP.seq (WP.mono ha fun s₂ M => ?_)
  generalize hH : ctxH s₀.mem Ctx = H at M ⊢
  generalize hiv : bytesAt s₀.mem Np nl = iv at M ⊢
  generalize ha : bytesAt s₀.mem A al = a at M ⊢
  have hRo : RoundsAt s₂.mem W R := hR ▸ M.rounds
  have hd₂ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₂ D n := C.data.of_eq M.rd M.wr
  have hal₂ : s₂.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have X₂ := X.keep M.rd M.wr M.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact X.cw
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm
  refine WP.mono (WP.with_rdwr (sealBodyF_ok L B hF hks (icb := inc32 (Spec.Gcm.j0 H iv)) (a := a)
    ⟨M.env, hRo, M.dat, M.len, hd₂, C.t_c, C.t_w, C.t_d, C.sp24, X₂⟩ M.hH M.cb hal₂ M.abs))
    fun s₄ ⟨⟨he₄, _, _, f₄, hC, hT₄⟩, hrd₄, hwr₄⟩ => ?_
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₂ : ciphOf s₂.mem Ctx R = ctxCiph s₀.mem Ctx R :=
    ciph_frame M.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR'
  have hp₂ : bytesAt s₂.mem D n = bytesAt s₀.mem D n :=
    bytesAt_frame M.frame (dM _ _ C.dE C.data.ok.stk) (by have := C.data.ok.lt; omega_using [this])
  rw [M.j0, hc₂] at hT₄
  refine ⟨he₄, hrd₄.trans M.rd, hwr₄.trans M.wr, M.saved.frame f₄ (saved_oneFrameB L C.dE C.t_w), ?_,
    by rw [hC, hc₂, hp₂, Proof.Gcm.gctr_eq], hT₄⟩
  refine (M.frame.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨below SP 24, by simp, below_sub (by decide) (by decide)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.wSub (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, fun _ h => h⟩
    · exact ⟨below SP 24, by simp, fun _ h => h⟩

/-- After the entry, the long `seal` up to the tag at `W`: `oneAad`,
`oneBlocks` and `finishWith ks` leave what `sealRun_ok` does. -/
theorem sealRunF_ok (hF : ShortFacts) {ks : Prog isa} (hks : KsOk ks) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s₀ s₁ : State}
    {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀)
    (E : OneEntry s₀ Ctx W SP A D n s₁)
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al) :
    WP isa (.seq (oneAad v.callees) (.seq (oneBlocks B.enc) (Impl.AesGcm.X86_64.Short.finishWith ks))) s₁
      (SealRunPost s₀ Ctx W SP Np A D nl al n) :=
  sealRunW_ok hF hks B C X hal (oneMid_ok v C E hNp hnl hal)

/-- What `seal` needs of the code `lng` it runs when the short path does not
apply, with a key context of kind `M`: what `sealRun_ok` leaves, after the
entry. -/
def SealLongOk (M : Gcm.X86_64.Stitch.CtxMode) (lng : Prog isa) : Prop :=
  ∀ {s s₁ : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}, OneCtx s 4 Ctx W SP Np A D nl al n →
    CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s → OneEntry s Ctx W SP A D n s₁ →
    s.gpr .rdx = Np → (s.gpr .rcx).toNat = nl → (s.gpr .r9).toNat = al →
    WP isa lng s₁ (SealRunPost s Ctx W SP Np A D nl al n)

theorem sealLongOk_sealLong (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    SealLongOk M (Impl.AesGcm.X86_64.Short.sealLong (v.withBlk B)) :=
  fun C X E hNp hnl hal => sealRunF_ok hF finKs_ksOk v B C X E hNp hnl hal

/-- What the short path needs of its table of powers' code `pw` and its
GHASH code `gh` with a key context of kind `M`: `PowFrom` from any entry
with the context, for some view of the table. -/
def PowOk (M : Gcm.X86_64.Stitch.CtxMode) (pw gh : Prog isa) : Prop :=
  ∀ {s₀ : State} {Ctx W SP D : Addr} {n : Nat}, CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀ →
    ∃ tm, PowFrom pw gh tm s₀ Ctx W SP D n

theorem powOk_powers (hF : ShortFacts) {M : Gcm.X86_64.Stitch.CtxMode} :
    PowOk M Impl.AesGcm.X86_64.Short.powers Impl.AesGcm.X86_64.Short.ghash :=
  fun _ => ⟨_, powFrom_powers hF⟩

/-- `seal` after the entry: `cond`, then the short path or the other
instances' body, which leave the same. -/
theorem sealMid_ok (hF : ShortFacts) {M : Gcm.X86_64.Stitch.CtxMode}
    {pw gh lng : Prog isa} (hpw : PowOk M pw gh) (hlng : SealLongOk M lng) {s s₁ : State}
    {Ctx W SP Np A D : Addr} {nl al n : Nat} (C : OneCtx s 4 Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s) (E : OneEntry s Ctx W SP A D n s₁)
    (hNp : s.gpr .rdx = Np) (hnl : (s.gpr .rcx).toNat = nl) (hal : (s.gpr .r9).toNat = al) :
    WP isa (.seq Impl.AesGcm.X86_64.Short.cond (.ite .e lng (Impl.AesGcm.X86_64.Short.sealShort pw gh))) s₁
      (SealRunPost s Ctx W SP Np A D nl al n) :=
  WP.seq (WP.mono (condE_ok C E hnl hal) fun _ ⟨hz, E₂, _⟩ =>
    WP.ite (decide ¬IsShort _ _ _) (eval_e hz) (fun _ => hlng C X E₂ hNp hnl hal) fun h => by
      have h' := Decidable.not_not.mp (of_decide_eq_false h)
      exact sealShort_ok hF C (hpw X).choose_spec E₂ hNp hnl hal h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1)

/-- `vg_aes_gcm_seal` with the short path, the table of powers from `pw`,
and `lng` when the short path does not apply, for a key context of kind
`M`. -/
theorem sealMW_wp (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {pw gh lng : Prog isa}
    (hpw : PowOk M pw gh) (hlng : SealLongOk M lng) {s : State} (hp : (Proof.AesGcm.sealX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B) pw gh lng) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' :=
  sealM_of hp (sealMid_ok hF hpw hlng)

/-- `vg_aes_gcm_seal` with the short path, for a key context of kind `M`. -/
theorem sealM_wp (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.sealX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.Short.«seal» (v.withBlk B)) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.sealX86_64.post s s' :=
  sealMW_wp hF v B (powOk_powers hF) (sealLongOk_sealLong hF v B) hp

/-- What `open` needs of the code `lng` it runs when the short path does not
apply, with a key context of kind `M`: what `openOk_ok` leaves, after the
entry. -/
def LongOk (M : Gcm.X86_64.Stitch.CtxMode) (lng : Prog isa) : Prop :=
  ∀ {s s₂ : State} {Ctx W SP Np A D T : Addr} {nl al n t : Nat}, OneCtx s 5 Ctx W SP Np A D nl al n →
    CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s → OneEntry s Ctx W SP A D n s₂ →
    s.gpr .rdx = Np → (s.gpr .rcx).toNat = nl → (s.gpr .r9).toNat = al →
    s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T → InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8 →
    Covers [⟨T, t⟩] (s.rd ++ s.wr) → OutWDS W D SP n ⟨T, t⟩ → OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩ →
    s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t → Spec.Gcm.tagLenOk t = true →
    WP isa lng s₂ (OpenOkPost s Ctx W SP Np A D T nl al n t)

theorem longOk_openLong (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) :
    LongOk M (Impl.AesGcm.X86_64.Short.openLong (v.withBlk B)) :=
  fun C X E hNp hnl hal hTa hTar hTr oT oA htl hok => openOk_ok v B C X E hNp hnl hal hTa hTar hTr oT oA htl hok

/-- `vg_aes_gcm_open` with the short path, the table of powers from `pw`,
and `lng` when the short path does not apply, for a key context of kind
`M`. -/
theorem openMW_wp (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M)
    {pw lng gh : Prog isa} (hpw : PowOk M pw gh) (hlng : LongOk M lng) {s : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B) pw lng gh) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' := by
  refine openM_of hp fun {Ctx W SP Np A D T nl al n t _ _} C X E hNp hnl hal _ hTa hTar hTr oT oA htl hok =>
    WP.seq (WP.mono (condE_ok C E hnl hal) fun s₂ ⟨hz, E₂, K⟩ => ?_)
  rw [← K.mem] at htl
  refine WP.ite (decide ¬IsShort _ _ _) (eval_e hz)
    (fun _ => hlng C X E₂ hNp hnl hal hTa hTar hTr oT oA htl hok) fun h => ?_
  have h' := Decidable.not_not.mp (of_decide_eq_false h)
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega_using [hok]
  refine WP.mono (openShort_ok hF C (hpw X).choose_spec E₂ hNp hnl hal h'.1 h'.2.1 h'.2.2.1 h'.2.2.2.1 htl hb.1 hb.2 hTa hTar hTr oT oA)
    fun s' ⟨he, hsv, f, hax, hD⟩ => ⟨he, hsv, ?_, ?_⟩
  · rw [ret_kept f fun r hr => ?_]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact C.rW
    · exact C.rD
    · exact Offset.base_disjoint_below _ (n := 24) (k := 8) (by decide)
  · obtain ⟨rfl, -⟩ := h'
    simp only [OpenRes, Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq,
      length_bytesAt]
    by_cases e : (VG.Spec.Gcm.toBytes (VG.Spec.Gcm.ghashFrom (ctxH s.mem Ctx) (VG.Spec.Gcm.ghash (ctxH s.mem Ctx)
        (VG.Spec.Gcm.blocks (Proof.Gcm.padded (bytesAt s.mem A al) (bytesAt s.mem D n))))
        [VG.Spec.Gcm.ofBytes (Proof.Gcm.lensBlock al n)] ^^^
        ctxCiph s.mem Ctx (s.gpr .rsi).toNat (Spec.Gcm.j0 (ctxH s.mem Ctx) (bytesAt s.mem Np 12)))).take t =
        bytesAt s.mem T t
    · simp only [e, ↓reduceIte] at hax hD ⊢
      exact ⟨hax, hD⟩
    · simp only [e, ↓reduceIte] at hax hD ⊢
      exact ⟨hax, hD⟩

/-- `vg_aes_gcm_open` with the short path, for a key context of kind `M`. -/
theorem openM_wp (hF : ShortFacts) (v : GcmImpl) {M : Gcm.X86_64.Stitch.CtxMode} (B : BlkFn M) {s : State}
    (hp : (Proof.AesGcm.openX86_64M M).pre s) :
    WP isa (Impl.AesGcm.X86_64.Short.«open» (v.withBlk B)) s fun s' =>
      gprPreserved s s' ∧ Proof.AesGcm.openX86_64.post s s' :=
  openMW_wp hF v B (powOk_powers hF) (longOk_openLong v B) hp

end VG.Proof.AesGcm.X86_64.Short
