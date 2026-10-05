import VerifiedGarbage.Proof.AesOcb.X86.NonceBlock
import VerifiedGarbage.Proof.Ocb.Stretch
import VerifiedGarbage.Proof.Ocb.Stretch32

/-!
# AES-OCB on x86: `Offset_0` (`offset0`)

Untrusted: everything here is checked by Lean. `offset0` stores `Ktop` as
four byte-reversed words at `W + stO`, and the two words of `Stretch`'s
tail after them (`stretch_ok`, `Proof.Ocb.stretch_words32`): `Stretch` as
six words (`stv`). Six masked stages shift them left by `bottom`
(`stage_ok`, `stage32_ok`, `Proof.Ocb.shl_stages`), and the top four,
byte-reversed, are stored to `W + ofsO` and `W + o0O` (`offset0_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesOcb.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem)
open VG.Proof.Ocb (shlIf cat6 shlW shl6 shl6_32 ror_mask32 sel_mask32 bit_bottom32 stretch_words32)
open VG.Impl.AesGcm.X86 (at_ imm slot)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq runBlock_app_of readW_writeW_off)

/-- The six words at `W + stO`, the most significant first. -/
def stv (m : Mem) (W : BitVec 32) : BitVec 192 :=
  cat6 (slotv m W 240) (slotv m W 244) (slotv m W 248) (slotv m W 252) (slotv m W 256) (slotv m W 260)

/-- Six words stored at `W + stO`. -/
def put6 (m : Mem) (W : BitVec 32) (y0 y1 y2 y3 y4 y5 : BitVec 32) : Mem :=
  (((((m.writeW (w64 W + BitVec.ofNat 64 240) y0).writeW (w64 W + BitVec.ofNat 64 244) y1).writeW
    (w64 W + BitVec.ofNat 64 248) y2).writeW (w64 W + BitVec.ofNat 64 252) y3).writeW
    (w64 W + BitVec.ofNat 64 256) y4).writeW (w64 W + BitVec.ofNat 64 260) y5

theorem stv_put6 (m : Mem) (W : BitVec 32) (y0 y1 y2 y3 y4 y5 : BitVec 32) :
    stv (put6 m W y0 y1 y2 y3 y4 y5) W = cat6 y0 y1 y2 y3 y4 y5 := by
  simp (disch := first | decide | omega) only [stv, put6, slotv_eq, Mem.readW_writeW_self32, readW_writeW_off]

theorem frame_put6 (m : Mem) (W : BitVec 32) (y0 y1 y2 y3 y4 y5 : BitVec 32) :
    Frame [⟨w64 W + BitVec.ofNat 64 stO, 24⟩] m (put6 m W y0 y1 y2 y3 y4 y5) := by
  have c : ∀ d, 240 ≤ d → d + 4 ≤ 264 →
      (⟨w64 W + BitVec.ofNat 64 stO, 24⟩ : Region).Contains (w64 W + BitVec.ofNat 64 d) (32 / 8) := fun d h₁ h₂ =>
    Offset.contains (w64 W) (e := 240) (k := 24) (d := d) (n := 4) (by omega) (by omega) (by decide)
  have hm := List.mem_singleton_self (⟨w64 W + BitVec.ofNat 64 stO, 24⟩ : Region)
  exact (((((((Frame.refl _ m).writeW hm _ (c 240 (by decide) (by decide))).writeW hm _ (c 244 (by decide)
    (by decide))).writeW hm _ (c 248 (by decide) (by decide))).writeW hm _ (c 252 (by decide)
    (by decide))).writeW hm _ (c 256 (by decide) (by decide))).writeW hm _ (c 260 (by decide) (by decide)))

/-- The mask of a stage: all ones if bit `k` of `bottom` is set. -/
theorem stageMask_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {k v : Nat} (hk : k < 6) (hv : v < 64)
    (hb : slotv s.mem p.W botO = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa (stageMask k) s = some s' ∧
      s'.gpr .ebx = (0 : BitVec 32) - (if v.testBit k then 1 else 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [slotv_eq] at hb
  by_cases hk0 : k = 0
  · subst hk0
    have := bit_bottom32 hv 0
    rw [BitVec.ushiftRight_zero] at this
    refine ⟨_, by grun [stageMask, E.ebp, L.aW, E.perm.wR, hb], ?_, fun r h₁ h₂ => by gregs [h₁, h₂], by gmems [],
      by gmems [], by gmems []⟩
    gregs [hb]
    rw [← this]; rfl
  · have := bit_bottom32 hv k
    have ck : 1 ≤ k ∧ k ≤ 31 := ⟨by omega, by omega⟩
    refine ⟨_, by grun [stageMask, hk0, ck, E.ebp, L.aW, E.perm.wR, hb], ?_, fun r h₁ h₂ => by gregs [h₁, h₂],
      by gmems [], by gmems [], by gmems []⟩
    gregs [hb]
    rw [← this]; rfl

/-- Word `j` of a stage: shifted if `b`. -/
abbrev selW' (b : Bool) (x x' : BitVec 32) : BitVec 32 := if b then x' else x

/-- Word `j < 5` of a stage, with the mask in `ebx`. -/
theorem stageW_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {a j : Nat} {b : Bool} (ha : 0 < a)
    (ha' : a < 32) (hj : j < 5) (hbx : t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ t', runBlock isa (stageW a j) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 (240 + 4 * j))
        (selW' b (slotv t.mem p.W (240 + 4 * j)) (shlW a (slotv t.mem p.W (240 + 4 * j))
          (slotv t.mem p.W (240 + 4 * j + 4)))) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have c1 : 1 ≤ 32 - a ∧ 32 - a ≤ 31 := ⟨by omega, by omega⟩
  refine ⟨_, by grun [stageW, shlEcx, selW, c1, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hbx, ror_mask32 _ ha ha', sel_mask32, slotv_eq]

/-- The last word of a stage: `x5 << a`. -/
theorem stageL_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {a : Nat} {b : Bool} (ha : 0 < a)
    (ha' : a < 32) (hbx : t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ t', runBlock isa ([.mov .eax (slot (stO + 20)), .mov .ecx (.reg .eax)] ++ shlEcx a ++ selW 5) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 260)
        (selW' b (slotv t.mem p.W 260) (slotv t.mem p.W 260 <<< a)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  have c1 : 1 ≤ 32 - a ∧ 32 - a ≤ 31 := ⟨by omega, by omega⟩
  refine ⟨_, by grun [shlEcx, selW, c1, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hbx, ror_mask32 _ ha ha', sel_mask32, slotv_eq]

/-- Word `j < 5` of the last stage: the next word. -/
theorem stage32W_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat} {b : Bool} (hj : j < 5)
    (hbx : t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ t', runBlock isa (stage32W j) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 (240 + 4 * j))
        (selW' b (slotv t.mem p.W (240 + 4 * j)) (slotv t.mem p.W (240 + 4 * j + 4))) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [stage32W, selW, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hbx, sel_mask32, slotv_eq]

/-- The last word of the last stage: zero. -/
theorem stage32L_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {b : Bool}
    (hbx : t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) :
    ∃ t', runBlock isa ([.mov .eax (slot (stO + 20)), .mov .ecx (imm 0)] ++ selW 5) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 260) (selW' b (slotv t.mem p.W 260) 0) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [selW, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [hbx, sel_mask32, slotv_eq]; rfl

/-- A word of `W + stO` written. -/
theorem frame_st {p : Prm} {m m' : Mem} (hf : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] m m') {d : Nat}
    (h₁ : 240 ≤ d) (h₂ : d + 4 ≤ 264) (v : BitVec 32) :
    Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] m (m'.writeW (w64 p.W + BitVec.ofNat 64 d) v) :=
  hf.writeW (List.mem_singleton_self _) v
    (Offset.contains (w64 p.W) (e := 240) (k := 24) (d := d) (n := 4) (by omega) (by omega) (by decide))

/-- A word of `W` after a word written: the value written, or the word before. -/
theorem slot_upd {m m' : Mem} {W : BitVec 32} {d : Nat} {v : BitVec 32}
    (h : m' = m.writeW (w64 W + BitVec.ofNat 64 d) v) (o : Nat) (hs : o = d ∨ o + 4 ≤ d ∨ d + 4 ≤ o)
    (ho : o < 2 ^ 32) (hd : d < 2 ^ 32) : slotv m' W o = if o = d then v else slotv m W o := by
  subst h
  rw [slotv_eq, slotv_eq]
  rcases hs with rfl | hs
  · simp only [↓reduceIte, Mem.readW_writeW_self32]
  · rw [ite_eq_right_of_eq_false _ _ (by simp only [eq_iff_iff, iff_false]; omega)]; exact readW_writeW_off _ _ _ hs ho hd

/-- What a stage leaves. -/
structure StagePost (p : Prm) (b : Bool) (f : BitVec 192 → BitVec 192) (s s' : State) : Prop where
  val : stv s'.mem p.W = (if b then f (stv s.mem p.W) else stv s.mem p.W)
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s'.mem
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The words of a stage, run one after another from the mask. -/
theorem stage_words {p : Prm} (L : Lay p) {s : State} (E : Env p s) {b : Bool}
    (hbx : s.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0)) (w : Nat → List Instr) (last : List Instr)
    (f : BitVec 32 → BitVec 32 → BitVec 32) (fl : BitVec 32 → BitVec 32)
    (hw : ∀ {t : State} {j : Nat}, Env p t → j < 5 → t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0) →
      ∃ t', runBlock isa (w j) t = some t' ∧
        t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 (240 + 4 * j))
          (selW' b (slotv t.mem p.W (240 + 4 * j)) (f (slotv t.mem p.W (240 + 4 * j))
            (slotv t.mem p.W (240 + 4 * j + 4)))) ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr)
    (hl : ∀ {t : State}, Env p t → t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0) →
      ∃ t', runBlock isa last t = some t' ∧
        t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 260) (selW' b (slotv t.mem p.W 260) (fl (slotv t.mem p.W 260))) ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr) :
    ∃ s', runBlock isa (w 0 ++ w 1 ++ w 2 ++ w 3 ++ w 4 ++ last) s = some s' ∧
      stv s'.mem p.W = (if b then
        cat6 (f (slotv s.mem p.W 240) (slotv s.mem p.W 244)) (f (slotv s.mem p.W 244) (slotv s.mem p.W 248))
          (f (slotv s.mem p.W 248) (slotv s.mem p.W 252)) (f (slotv s.mem p.W 252) (slotv s.mem p.W 256))
          (f (slotv s.mem p.W 256) (slotv s.mem p.W 260)) (fl (slotv s.mem p.W 260))
        else stv s.mem p.W) ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have step : ∀ {t t' : State}, Env p t → (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) →
      t'.rd = t.rd → t'.wr = t.wr → (∃ d, 240 ≤ d ∧ d + 4 ≤ 264 ∧ ∃ v : BitVec 32,
        t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 d) v) → Env p t' := fun Et g rd wr ⟨d, h₁, h₂, v, hm⟩ =>
    Et.mut L (by rw [g _ (by decide) (by decide) (by decide), Et.ebp])
      (by rw [g _ (by decide) (by decide) (by decide), Et.esp]) rd wr
      (frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩]) (by rw [hm]; exact frame_st (Frame.refl _ _) h₁ h₂ v)
        fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have bx : ∀ {t t' : State}, (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) →
      t.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0) → t'.gpr .ebx = (0 : BitVec 32) - (if b then 1 else 0) :=
    fun g h => by rw [g _ (by decide) (by decide) (by decide), h]
  obtain ⟨t₁, r₁, m₁, g₁, rd₁, wr₁⟩ := hw E (j := 0) (by decide) hbx
  have E₁ := step E g₁ rd₁ wr₁ ⟨_, by decide, by decide, _, m₁⟩
  obtain ⟨t₂, r₂, m₂, g₂, rd₂, wr₂⟩ := hw E₁ (j := 1) (by decide) (bx g₁ hbx)
  have E₂ := step E₁ g₂ rd₂ wr₂ ⟨_, by decide, by decide, _, m₂⟩
  obtain ⟨t₃, r₃, m₃, g₃, rd₃, wr₃⟩ := hw E₂ (j := 2) (by decide) (bx g₂ (bx g₁ hbx))
  have E₃ := step E₂ g₃ rd₃ wr₃ ⟨_, by decide, by decide, _, m₃⟩
  obtain ⟨t₄, r₄, m₄, g₄, rd₄, wr₄⟩ := hw E₃ (j := 3) (by decide) (bx g₃ (bx g₂ (bx g₁ hbx)))
  have E₄ := step E₃ g₄ rd₄ wr₄ ⟨_, by decide, by decide, _, m₄⟩
  obtain ⟨t₅, r₅, m₅, g₅, rd₅, wr₅⟩ := hw E₄ (j := 4) (by decide) (bx g₄ (bx g₃ (bx g₂ (bx g₁ hbx))))
  have E₅ := step E₄ g₅ rd₅ wr₅ ⟨_, by decide, by decide, _, m₅⟩
  obtain ⟨t₆, r₆, m₆, g₆, rd₆, wr₆⟩ := hl E₅ (bx g₅ (bx g₄ (bx g₃ (bx g₂ (bx g₁ hbx)))))
  refine ⟨t₆, runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of r₁ r₂) r₃) r₄) r₅) r₆,
    ?_, ?_, fun r h₁ h₂ h₃ => by rw [g₆ r h₁ h₂ h₃, g₅ r h₁ h₂ h₃, g₄ r h₁ h₂ h₃, g₃ r h₁ h₂ h₃, g₂ r h₁ h₂ h₃,
      g₁ r h₁ h₂ h₃], by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁], by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · simp only [Nat.reduceMul, Nat.reduceAdd] at m₁ m₂ m₃ m₄ m₅
    rw [stv]
    simp (disch := decide) only [slot_upd m₆, slot_upd m₅, slot_upd m₄, slot_upd m₃, slot_upd m₂,
      slot_upd m₁, Nat.reduceEqDiff, ↓reduceIte]
    cases b <;> rfl
  · simp only [Nat.reduceMul, Nat.reduceAdd] at m₁ m₂ m₃ m₄ m₅
    have f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₁.mem := by
      rw [m₁]; exact frame_st (Frame.refl _ _) (by decide) (by decide) _
    have f₂ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₂.mem := by
      rw [m₂]; exact frame_st f₁ (by decide) (by decide) _
    have f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₃.mem := by
      rw [m₃]; exact frame_st f₂ (by decide) (by decide) _
    have f₄ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₄.mem := by
      rw [m₄]; exact frame_st f₃ (by decide) (by decide) _
    have f₅ : Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem t₅.mem := by
      rw [m₅]; exact frame_st f₄ (by decide) (by decide) _
    rw [m₆]; exact frame_st f₅ (by decide) (by decide) _

/-- One stage: the six words shifted left by `a` if bit `k` of `bottom` is set. -/
theorem stage_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {k a v : Nat} (hk : k < 6) (ha : 0 < a)
    (ha' : a < 32) (hv : v < 64) (hb : slotv s.mem p.W botO = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa (stage k a) s = some s' ∧ StagePost p (v.testBit k) (· <<< a) s s' := by
  obtain ⟨s₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ := stageMask_ok L E hk hv hb
  have E₁ : Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide)]) (by rw [g₁ _ (by decide) (by decide)]) rd₁ wr₁ m₁
  obtain ⟨s', run', v', f', g', rd', wr'⟩ := stage_words L E₁ bx₁ (stageW a)
    ([.mov .eax (slot (stO + 20)), .mov .ecx (.reg .eax)] ++ shlEcx a ++ selW 5) (shlW a) (· <<< a)
    (fun Et hj hbx => stageW_ok L Et ha ha' hj hbx) (fun Et hbx => stageL_ok L Et ha ha' hbx)
  refine ⟨s', ?_, ⟨?_, by rw [← m₁]; exact f', fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₃ h₄, g₁ r h₁ h₂],
    by rw [rd', rd₁], by rw [wr', wr₁]⟩⟩
  · rw [show stage k a = stageMask k ++ (stageW a 0 ++ stageW a 1 ++ stageW a 2 ++ stageW a 3 ++ stageW a 4 ++
      ([.mov .eax (slot (stO + 20)), .mov .ecx (.reg .eax)] ++ shlEcx a ++ selW 5)) by simp [stage]]
    exact runBlock_app_of run₁ run'
  · rw [v', m₁]
    split
    · exact shl6 a ha ha' _ _ _ _ _ _
    · rfl

/-- The last stage: the six words shifted left by 32 if bit 5 of `bottom` is set. -/
theorem stage32_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {v : Nat} (hv : v < 64)
    (hb : slotv s.mem p.W botO = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa stage32 s = some s' ∧ StagePost p (v.testBit 5) (· <<< 32) s s' := by
  obtain ⟨s₁, run₁, bx₁, g₁, m₁, rd₁, wr₁⟩ := stageMask_ok L E (k := 5) (by decide) hv hb
  have E₁ : Env p s₁ := E.keep (by rw [g₁ _ (by decide) (by decide)]) (by rw [g₁ _ (by decide) (by decide)]) rd₁ wr₁ m₁
  obtain ⟨s', run', v', f', g', rd', wr'⟩ := stage_words L E₁ bx₁ stage32W
    ([.mov .eax (slot (stO + 20)), .mov .ecx (imm 0)] ++ selW 5) (fun _ y => y) (fun _ => 0)
    (fun Et hj hbx => stage32W_ok L Et hj hbx) (fun Et hbx => stage32L_ok L Et hbx)
  refine ⟨s', ?_, ⟨?_, by rw [← m₁]; exact f', fun r h₁ h₂ h₃ h₄ => by rw [g' r h₁ h₃ h₄, g₁ r h₁ h₂],
    by rw [rd', rd₁], by rw [wr', wr₁]⟩⟩
  · rw [show stage32 = stageMask 5 ++ (stage32W 0 ++ stage32W 1 ++ stage32W 2 ++ stage32W 3 ++ stage32W 4 ++
      ([.mov .eax (slot (stO + 20)), .mov .ecx (imm 0)] ++ selW 5)) by simp [stage32]]
    exact runBlock_app_of run₁ run'
  · rw [v', m₁]
    split
    · exact shl6_32 _ _ _ _ _ _
    · rfl

/-- `Stretch = Ktop ‖ (Ktop[1..64] ⊕ Ktop[9..72])`. -/
def stretchV (ktop : Block) : BitVec 192 := ktop ++ (ktop.extractLsb' 64 64 ^^^ ktop.extractLsb' 56 64)

/-- The block at `W + d` as its four byte-reversed words. -/
theorem blockAtMem_words (m : Mem) (W : BitVec 32) (d : Nat) :
    blockAtMem m (w64 W + BitVec.ofNat 64 d) = byteRev32 (slotv m W d) ++ byteRev32 (slotv m W (d + 4)) ++
      byteRev32 (slotv m W (d + 8)) ++ byteRev32 (slotv m W (d + 12)) := by
  rw [blockAtMem, Proof.Ocb.ofBytes_eq, Proof.Cmac.ofBytes_rev4, slotv_eq, slotv_eq, slotv_eq, slotv_eq,
    add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]

/-- Word `j < 2` of `Stretch`'s tail. -/
theorem tailW_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat} (hj : j < 2) :
    ∃ t', runBlock isa (tailW j) t = some t' ∧
      t'.mem = t.mem.writeW (w64 p.W + BitVec.ofNat 64 (256 + 4 * j))
        ((slotv t.mem p.W (240 + 4 * j) <<< 8 ||| slotv t.mem p.W (240 + 4 * j + 4) >>> 24) ^^^
          slotv t.mem p.W (240 + 4 * j)) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by grun [tailW, shlEcx, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
    fun r h₁ h₂ h₃ => by gregs [h₁, h₂, h₃], by gmems [], by gmems []⟩
  gmems [ror_mask32 _ (show 0 < 8 by decide) (show 8 < 32 by decide), slotv_eq]

/-- `Stretch` to `W + stO`, from `Ktop` at `W + tmpO`. -/
theorem stretch_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) :
    ∃ s', runBlock isa Impl.AesOcb.X86.stretch s = some s' ∧ stv s'.mem p.W = stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO)) ∧
      Frame [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, run₁, m₁, g₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa ([0, 1, 2, 3].flatMap (fun j =>
      [.mov .eax (slot (tmpO + 4 * j)), .bswap .eax, .store (at_ .ebp (stO + 4 * j)) .eax])) s = some s₁ ∧
      s₁.mem = (((s.mem.writeW (w64 p.W + BitVec.ofNat 64 240) (byteRev32 (slotv s.mem p.W 112))).writeW
        (w64 p.W + BitVec.ofNat 64 244) (byteRev32 (slotv s.mem p.W 116))).writeW
        (w64 p.W + BitVec.ofNat 64 248) (byteRev32 (slotv s.mem p.W 120))).writeW
        (w64 p.W + BitVec.ofNat 64 252) (byteRev32 (slotv s.mem p.W 124)) ∧
      (∀ r, r ≠ .eax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by grun [List.flatMap_cons, List.flatMap_nil, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_,
      fun r h₁ => by gregs [h₁], by gmems [], by gmems []⟩
    gmems [bswap_eq, slotv_eq]
  have E₁ : Env p s₁ := E.mut L (by rw [g₁ _ (by decide), E.ebp]) (by rw [g₁ _ (by decide), E.esp]) rd₁ wr₁
    (frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩]) (by
      rw [m₁]
      exact frame_st (frame_st (frame_st (frame_st (Frame.refl _ _) (by decide) (by decide) _) (by decide) (by decide) _)
        (by decide) (by decide) _) (by decide) (by decide) _)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := tailW_ok L E₁ (j := 0) (by decide)
  have E₂ : Env p s₂ := E₁.mut L (by rw [g₂ _ (by decide) (by decide) (by decide), E₁.ebp])
    (by rw [g₂ _ (by decide) (by decide) (by decide), E₁.esp]) rd₂ wr₂
    (frame_toMut (rs := [⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩]) (by
      rw [m₂]; exact frame_st (Frame.refl _ _) (by decide) (by decide) _)
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := tailW_ok L E₂ (j := 1) (by decide)
  refine ⟨s₃, runBlock_app_of (runBlock_app_of run₁ run₂) run₃, ?_, ?_,
    fun r h₁ h₂ h₃ => by rw [g₃ r h₁ h₂ h₃, g₂ r h₁ h₂ h₃, g₁ r h₁], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · simp only [Nat.reduceMul, Nat.reduceAdd] at m₂ m₃
    have m₁' := m₁
    rw [stv]
    simp (disch := decide) only [slot_upd m₃, slot_upd m₂, Nat.reduceEqDiff, ↓reduceIte]
    rw [stretchV, blockAtMem_words, stretch_words32]
    simp (disch := first | decide | omega) only [slotv_eq, m₁, Mem.readW_writeW_self32, readW_writeW_off,
      Nat.reduceAdd]
  · simp only [Nat.reduceMul, Nat.reduceAdd] at m₂ m₃
    rw [m₃, m₂, m₁]
    exact frame_st (frame_st (frame_st (frame_st (frame_st (frame_st (Frame.refl _ _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _

/-- The top four of six words. -/
theorem top4 (a b c d e f : BitVec 32) : (cat6 a b c d e f).extractLsb' 64 128 = a ++ b ++ c ++ d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and, Proof.Ocb.getLsbD_cat6,
    BitVec.getLsbD_append]
  simp only [Nat.sub_sub, Nat.reduceAdd]
  split_ifs <;> first | omega | exact congrArg _ (by omega)

/-- What `offset0` leaves. -/
structure Off0Post (p : Prm) (o : Block) (s s' : State) : Prop where
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s'.mem
  ofs : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 ofsO) = o
  o0 : blockAtMem s'.mem (w64 p.W + BitVec.ofNat 64 o0O) = o
  gpr : ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- A stage keeps the environment and `bottom`. -/
theorem StagePost.env {p : Prm} (L : Lay p) {b : Bool} {f : BitVec 192 → BitVec 192} {s s' : State}
    (P : StagePost p b f s s') (E : Env p s) : Env p s' :=
  E.mut L (by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide), E.ebp])
    (by rw [P.gpr _ (by decide) (by decide) (by decide) (by decide), E.esp]) P.rd P.wr
    (frame_toMut P.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))

theorem StagePost.bot {p : Prm} {b : Bool} {f : BitVec 192 → BitVec 192} {s s' : State}
    (P : StagePost p b f s s') : slotv s'.mem p.W botO = slotv s.mem p.W botO :=
  P.frame.readW (r := ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
    (by decide)

theorem offset0_ok {p : Prm} (L : Lay p) {s : State} (E : Env p s) {v : Nat} (hv : v < 64)
    (hbot : slotv s.mem p.W botO = BitVec.ofNat 32 v) :
    ∃ s', runBlock isa offset0 s = some s' ∧
      Off0Post p ((stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128) s s' := by
  obtain ⟨s₁, run₁, v₁, f₁, g₁, rd₁, wr₁⟩ := stretch_ok L E
  have E₁ : Env p s₁ := E.mut L (by rw [g₁ _ (by decide) (by decide) (by decide), E.ebp])
    (by rw [g₁ _ (by decide) (by decide) (by decide), E.esp]) rd₁ wr₁
    (frame_toMut f₁ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩))))
  have b₁ : slotv s₁.mem p.W botO = BitVec.ofNat 32 v := by
    rw [← hbot]
    exact f₁.readW (r := ⟨w64 p.W + BitVec.ofNat 64 botO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)
  obtain ⟨s₂, run₂, P₂⟩ := stage_ok L E₁ (k := 0) (a := 1) (by decide) (by decide) (by decide) hv b₁
  obtain ⟨s₃, run₃, P₃⟩ := stage_ok L (P₂.env L E₁) (k := 1) (a := 2) (by decide) (by decide) (by decide) hv
    (P₂.bot.trans b₁)
  obtain ⟨s₄, run₄, P₄⟩ := stage_ok L (P₃.env L (P₂.env L E₁)) (k := 2) (a := 4) (by decide) (by decide) (by decide) hv
    (P₃.bot.trans (P₂.bot.trans b₁))
  obtain ⟨s₅, run₅, P₅⟩ := stage_ok L (P₄.env L (P₃.env L (P₂.env L E₁))) (k := 3) (a := 8) (by decide) (by decide)
    (by decide) hv (P₄.bot.trans (P₃.bot.trans (P₂.bot.trans b₁)))
  obtain ⟨s₆, run₆, P₆⟩ := stage_ok L (P₅.env L (P₄.env L (P₃.env L (P₂.env L E₁)))) (k := 4) (a := 16) (by decide)
    (by decide) (by decide) hv (P₅.bot.trans (P₄.bot.trans (P₃.bot.trans (P₂.bot.trans b₁))))
  have E₆ := P₆.env L (P₅.env L (P₄.env L (P₃.env L (P₂.env L E₁))))
  obtain ⟨s₇, run₇, P₇⟩ := stage32_ok L E₆ hv
    (P₆.bot.trans (P₅.bot.trans (P₄.bot.trans (P₃.bot.trans (P₂.bot.trans b₁)))))
  have E₇ := P₇.env L E₆
  have hw : stv s₇.mem p.W = stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO)) <<< v := by
    rw [P₇.val, P₆.val, P₅.val, P₄.val, P₃.val, P₂.val, v₁, ← Proof.Ocb.shl_stages _ hv]; rfl
  have hO : (stv s₇.mem p.W).extractLsb' 64 128 =
      (stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    rw [hw, Proof.Ocb.offset_shl _ (by omega)]
  obtain ⟨s₈, run₈, m₈, g₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa ([0, 1, 2, 3].flatMap (fun j =>
      [.mov .eax (slot (stO + 4 * j)), .bswap .eax, .store (at_ .ebp (ofsO + 4 * j)) .eax,
        .store (at_ .ebp (o0O + 4 * j)) .eax])) s₇ = some s₈ ∧
      s₈.mem = (((((((s₇.mem.writeW (w64 p.W + BitVec.ofNat 64 16) (byteRev32 (slotv s₇.mem p.W 240))).writeW
        (w64 p.W + BitVec.ofNat 64 224) (byteRev32 (slotv s₇.mem p.W 240))).writeW
        (w64 p.W + BitVec.ofNat 64 20) (byteRev32 (slotv s₇.mem p.W 244))).writeW
        (w64 p.W + BitVec.ofNat 64 228) (byteRev32 (slotv s₇.mem p.W 244))).writeW
        (w64 p.W + BitVec.ofNat 64 24) (byteRev32 (slotv s₇.mem p.W 248))).writeW
        (w64 p.W + BitVec.ofNat 64 232) (byteRev32 (slotv s₇.mem p.W 248))).writeW
        (w64 p.W + BitVec.ofNat 64 28) (byteRev32 (slotv s₇.mem p.W 252))).writeW
        (w64 p.W + BitVec.ofNat 64 236) (byteRev32 (slotv s₇.mem p.W 252)) ∧
      (∀ r, r ≠ .eax → s₈.gpr r = s₇.gpr r) ∧ s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by grun [List.flatMap_cons, List.flatMap_nil, E₇.ebp, L.aW, E₇.perm.wR, E₇.perm.wW], ?_,
      fun r h₁ => by gregs [h₁], by gmems [], by gmems []⟩
    gmems [bswap_eq, slotv_eq]
  have blk : ∀ d, d = 16 ∨ d = 224 → blockAtMem s₈.mem (w64 p.W + BitVec.ofNat 64 d) =
      (stretchV (blockAtMem s.mem (w64 p.W + BitVec.ofNat 64 tmpO))).extractLsb' (64 - v) 128 := by
    intro d hd
    rw [← hO, stv, top4, blockAtMem_words]
    rcases hd with rfl | rfl <;>
      simp (disch := first | decide | omega) only [slotv_eq, m₈, Mem.readW_writeW_self32, readW_writeW_off,
        Nat.reduceAdd, Proof.Cmac.byteRev32_byteRev32]
  have fs : ∀ {t t' : State} {b : Bool} {f : BitVec 192 → BitVec 192}, StagePost p b f t t' →
      Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] t.mem t'.mem := fun P =>
    P.frame.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]
  have F₇ : Frame [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] s.mem s₇.mem :=
    ((((((f₁.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans (fs P₂)).trans (fs P₃)).trans
      (fs P₄)).trans (fs P₅)).trans (fs P₆)).trans (fs P₇)
  refine ⟨s₈, ?_, ⟨?_, blk 16 (.inl rfl), blk 224 (.inr rfl), fun r h₁ h₂ h₃ h₄ => ?_, ?_, ?_⟩⟩
  · unfold offset0
    exact runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of (runBlock_app_of
      (runBlock_app_of run₁ run₂) run₃) run₄) run₅) run₆) run₇) run₈
  · rw [m₈]
    have c : ∀ e d, (e = 16 ∨ e = 224) → e ≤ d → d + 4 ≤ e + 16 →
        (⟨w64 p.W + BitVec.ofNat 64 e, 16⟩ : Region).Contains (w64 p.W + BitVec.ofNat 64 d) (32 / 8) :=
      fun e d he h₁ h₂ => Offset.contains (w64 p.W) (by omega) (by rcases he with rfl | rfl <;> omega) (by omega)
    have m0 : (⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩ : Region) ∈ [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] := by simp
    have m1 : (⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩ : Region) ∈ [⟨w64 p.W + BitVec.ofNat 64 ofsO, 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 o0O, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 stO, 24⟩] := by simp
    exact (((((((F₇.writeW m0 _ (c 16 16 (.inl rfl) (by decide) (by decide))).writeW m1 _
      (c 224 224 (.inr rfl) (by decide) (by decide))).writeW m0 _ (c 16 20 (.inl rfl) (by decide) (by decide))).writeW
      m1 _ (c 224 228 (.inr rfl) (by decide) (by decide))).writeW m0 _ (c 16 24 (.inl rfl) (by decide) (by decide))).writeW
      m1 _ (c 224 232 (.inr rfl) (by decide) (by decide))).writeW m0 _ (c 16 28 (.inl rfl) (by decide) (by decide))).writeW
      m1 _ (c 224 236 (.inr rfl) (by decide) (by decide))
  · rw [g₈ r h₁, P₇.gpr r h₁ h₂ h₃ h₄, P₆.gpr r h₁ h₂ h₃ h₄, P₅.gpr r h₁ h₂ h₃ h₄, P₄.gpr r h₁ h₂ h₃ h₄,
      P₃.gpr r h₁ h₂ h₃ h₄, P₂.gpr r h₁ h₂ h₃ h₄, g₁ r h₁ h₃ h₄]
  · rw [rd₈, P₇.rd, P₆.rd, P₅.rd, P₄.rd, P₃.rd, P₂.rd, rd₁]
  · rw [wr₈, P₇.wr, P₆.wr, P₅.wr, P₄.wr, P₃.wr, P₂.wr, wr₁]

end VG.Proof.AesOcb.X86
