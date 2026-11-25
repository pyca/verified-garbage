module

public import VerifiedGarbage.Proof.Sha3.AArch64.Rounds
public import VerifiedGarbage.Proof.Sha3.AArch64.Permute
public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core
import VerifiedGarbage.Proof.Sha3.AArch64.RoundConstants
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64

/-!
# Keccak-f[1600] on AArch64, in general registers: the 24 rounds

`callCore_ok`: calling `vg_keccak_f1600_lanes` permutes the state in the
lanes' registers, and changes no other register but its free ones, `v27` and
`v28`, and memory only in the 24 bytes at `x28`.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar VG.Proof.Sha3.AArch64.Eval
open VG.Proof.Sha3.AArch64.Rounds
open VG.Proof.Sha3.Forms (core)
open VG.Spec.Sha3 (keccakF rnd RC)
open VG.Impl.Sha3.AArch64.Lanes (home)

/-- The lanes' registers hold `A`, between rounds of the same parity as the first. -/
abbrev Lanes (s : State) (A : Spec.Sha3.State) : Prop := Gen.Lanes conf.pd 0 s A

def mode : Mode := ⟨.x28, 0, 3⟩

/-- The registers the rounds write: all but `x28`. -/
def writes : Nat := 0x17ffffff

theorem rounds_ok : ∀ r < 2, Gen.ok conf.pd mode writes (conf.round r) r = true := by decide +kernel

/-- What the rounds keep. -/
structure Keep (s t : State) : Prop where
  x28 : t.gpr .x28 = s.gpr .x28
  v : t.v = s.v
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  syms : t.syms = s.syms
  frame : Frame [⟨s.gpr .x28, 24⟩] s.mem t.mem

theorem Keep.refl (s : State) : Keep s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keep.trans {s t u : State} (h : Keep s t) (g : Keep t u) : Keep s u :=
  ⟨g.x28.trans h.x28, g.v.trans h.v, g.rd.trans h.rd, g.wr.trans h.wr, g.sp.trans h.sp, g.syms.trans h.syms,
    h.frame.trans (h.x28 ▸ g.frame)⟩

/-- The working space. -/
def Space (s : State) : Prop := ∀ k < 3, InRegions s.wr (s.gpr .x28 + BitVec.ofNat 64 (8 * k)) 8

theorem Space.keep {s t : State} (h : Space s) (k : Keep s t) : Space t := fun i hi => by
  rw [k.x28, k.wr]; exact h i hi

theorem base_eq (s : State) : slotBase mode s = s.gpr .x28 := by
  simp [slotBase, mode]

theorem lanes_mod (r : Nat) (pd : Nat → Nat) (s : State) (A : Spec.Sha3.State) :
    Gen.Lanes pd (r % 2) s A ↔ Gen.Lanes pd r s A := by
  simp only [Gen.Lanes, reg, home_mod r, home_mod (r % 2), Nat.mod_mod]

theorem round_ok (r : Nat) {s : State} {A : Spec.Sha3.State} (hl : Gen.Lanes conf.pd r s A) (hs : Space s) :
    ∃ t, runBlock isa (conf.round (r % 2)) s = some t ∧ Gen.Lanes conf.pd (r + 1) t (core A) ∧ Keep s t := by
  obtain ⟨t, x, l, k⟩ := Gen.round_ok (Gen.pd_lt conf) (m := mode) (w := writes) (by decide)
    (Nat.mod_lt r (by decide)) (rounds_ok _ (Nat.mod_lt r (by decide))) (s := s)
    ⟨by decide, fun k hk => by rw [base_eq]; exact hs k hk⟩ ((lanes_mod r _ _ _).mpr hl)
  refine ⟨t, x, ?_, ⟨k.gpr _ (by decide), k.v, k.rd, k.wr, k.sp, k.syms, ?_⟩⟩
  · rw [← lanes_mod, show (r + 1) % 2 = (r % 2 + 1) % 2 by omega, lanes_mod]; exact l
  · have := k.frame
    rw [slotR, base_eq] at this
    exact this

theorem reg_ne : ∀ r < 2, ∀ i < 25, reg r i ≠ .x16 ∧ reg r i ≠ .x17 ∧ reg r i ≠ .x30 ∧ reg r i ≠ .x28 ∧ (reg r i = .x0 ↔ i = 0) := by
  decide

theorem reg_ne' (r : Nat) {i : Nat} (hi : i < 25) :
    reg r i ≠ .x16 ∧ reg r i ≠ .x17 ∧ reg r i ≠ .x30 ∧ reg r i ≠ .x28 ∧ (reg r i = .x0 ↔ i = 0) := by
  have := reg_ne (r % 2) (Nat.mod_lt _ (by decide)) i hi
  simpa only [reg, home_mod r, home_mod (r % 2), Nat.mod_mod] using this

theorem runBlock_append (a b : List Instr) {s t : State} (h : runBlock isa a s = some t) :
    runBlock isa (a ++ b) s = runBlock isa b t := by
  induction a generalizing s with
  | nil => cases h; rfl
  | cons i a ih =>
    rw [List.cons_append, runBlock_cons]
    rw [runBlock_cons] at h
    rcases hi : exec i s with _ | u
    · rw [hi] at h; cases h
    · rw [hi, runStep_some] at h
      rw [runStep_some]; exact ih h

/-- ι, in general registers: lane 0 XORed with a word that is `RC n`. -/
theorem iota_lanes {r n : Nat} {A : Spec.Sha3.State} {pd : Nat → Nat} (h0 : pd 0 = 0) {s t : State}
    (hl : Gen.Lanes pd (r + 1) s (core A)) (hx : t.gpr .x0 = s.gpr .x0 ^^^ RC n)
    (ho : ∀ q, q ≠ .x0 → q ≠ .x16 → t.gpr q = s.gpr q) : Gen.Lanes pd (r + 1) t (rnd A n) := by
  intro i hi
  have hn := reg_ne' (r + 1) hi
  rw [Forms.rnd_core A n hi]
  by_cases hi0 : i = 0
  · subst hi0
    have h := hl 0 hi
    rw [hn.2.2.2.2.mpr rfl] at h ⊢
    rw [hx, h, h0]
    simp only [ite_true]
    have e : ∀ x : BitVec 64, x.rotateRight 0 = x := fun x => by
      ext j hj; simp [BitVec.getElem_rotateRight, hj]
    rw [e, e]
  · rw [ite_eq_right hi0, ho _ (fun h => hi0 (hn.2.2.2.2.mp h)) hn.1]
    exact hl i hi

theorem iota_run (r : Nat) (hr : r < 24) {s : State} (hv : vdword (s.v .v28) 0 = s.syms VG.Impl.Sha3.AArch64.RoundConstants.sym) :
    ∃ t, runBlock isa (iota r) s = some t ∧ t.gpr .x0 = s.gpr .x0 ^^^ RC r ∧
      (∀ q, q ≠ .x0 → q ≠ .x16 → t.gpr q = s.gpr q) ∧ Keep s t := by
  let s₁ := s.write .x .x16 (vdword (s.v .v28) 0)
  let s₂ := s₁.write .x .x16 (RC r)
  let s₃ := s₂.write .x .x0 (s₂.gpr .x0 ^^^ s₂.gpr .x16)
  have e₁ : exec (.umov .x .x16 .v28 0) s = some s₁ := rfl
  have e₂ : exec (.ldrTbl .x .x16 .x16 (8 * r) VG.Impl.Sha3.AArch64.RoundConstants.sym VG.Impl.Sha3.AArch64.RoundConstants.rcs) s₁ = some s₂ := by
    simp only [exec]
    rw [ite_eq_left ⟨by
        rw [show s₁.gpr .x16 = vdword (s.v .v28) 0 from by simp only [s₁, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]]
        exact hv, by simp only [Size.bytes]; omega, by simp only [Size.bytes]; omega,
        by rw [VG.Proof.Sha3.AArch64.RoundConstants.rcs_length]; omega⟩]
    rw [show 8 * r / 8 = r by omega, show 8 * (8 * r % 8) = 0 by omega, VG.Proof.Sha3.AArch64.RoundConstants.rcs_eq r hr]
    have e : (RC r).extractLsb' 0 64 = RC r := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [BitVec.getLsbD_extractLsb', Nat.zero_add]
      simp only [hi, decide_true, Bool.true_and]
    show some (s₁.write .x .x16 ((RC r).extractLsb' 0 64)) = some s₂
    rw [e]
  have e₃ : exec (.logic .eor .x .x0 .x0 .x16) s₂ = some s₃ := by
    simp only [exec_logic, State.read, BitVec.setWidth_eq]; rfl
  have g16 : s₂.gpr .x16 = RC r := by simp only [s₂, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
  have g : ∀ q, q ≠ .x16 → s₂.gpr q = s.gpr q := fun q h => by
    simp only [s₂, s₁, RegUpd.gpr_write, ite_eq_right h]
  refine ⟨s₃, ?_, ?_, fun q h0 h16 => ?_, ⟨?_, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩⟩
  · rw [iota, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]
  · simp only [s₃, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
    rw [g16, g _ (by decide)]
  · simp only [s₃, RegUpd.gpr_write, ite_eq_right h0]
    exact g q h16
  · simp only [s₃, RegUpd.gpr_write]
    rw [ite_eq_right (by decide)]; exact g _ (by decide)

/-- `n` rounds from the first. -/
theorem rounds_run {s : State} {A : Spec.Sha3.State} (hl : Lanes s A) (hs : Space s)
    (hv : vdword (s.v .v28) 0 = s.syms VG.Impl.Sha3.AArch64.RoundConstants.sym) : ∀ n ≤ 24,
    ∃ t, runBlock isa ((List.range n).flatMap fullRound) s = some t ∧
      Gen.Lanes conf.pd n t ((List.range n).foldl rnd A) ∧ Keep s t
  | 0, _ => ⟨s, rfl, hl, .refl s⟩
  | n + 1, hn => by
    obtain ⟨t, x, l, k⟩ := rounds_run hl hs hv n (by omega)
    obtain ⟨u, y, l', k'⟩ := round_ok n l (hs.keep k)
    obtain ⟨w, z, h0, ho, k''⟩ := iota_run n (by omega) (s := u) (by rw [k'.v, k.v, k'.syms, k.syms]; exact hv)
    refine ⟨w, ?_, ?_, (k.trans k').trans k''⟩
    · rw [List.range_succ, List.flatMap_append, runBlock_append _ _ x, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, fullRound, runBlock_append _ _ y, z]
    · rw [foldl_succ]
      exact iota_lanes (by decide) l' h0 ho

/-- What a call of the core keeps. -/
structure CoreKeep (s t : State) : Prop where
  x28 : t.gpr .x28 = s.gpr .x28
  v : ∀ r, r ≠ .v27 → r ≠ .v28 → t.v r = s.v r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x28, 24⟩] s.mem t.mem

theorem callCore_ok {s : State} {A : Spec.Sha3.State} (hl : Lanes s A) (hs : Space s) {Q : State → Prop}
    (hQ : ∀ t, Lanes t (keccakF A) → CoreKeep s t → Q t) : WP isa callCore s Q := by
  let s₀ := s.callEntry
  let s₁ := s₀.setV .v27 (ofVDwords (s₀.gpr .x30) (s₀.gpr .x30))
  let s₂ := s₁.write .x .x16 (s₁.syms VG.Impl.Sha3.AArch64.RoundConstants.sym)
  let s₃ := s₂.setV .v28 (ofVDwords (s₂.gpr .x16) (s₂.gpr .x16))
  have g : ∀ q, q ≠ .x16 → s₃.gpr q = s₀.gpr q := fun q h => by
    simp only [s₃, s₂, s₁, RegUpd.gpr_setV, RegUpd.gpr_write, ite_eq_right h]
  have g0 : ∀ q, q ∉ linkRegs → s₃.gpr q = s.gpr q := fun q h => by
    rw [g q (by rintro rfl; exact h (by decide))]; exact State.callEntry_gpr s h
  have h28 : s₃.gpr .x28 = s.gpr .x28 := g0 _ (by decide)
  have hl₃ : Lanes s₃ A := fun i hi => by
    have hn := reg_ne 0 (by decide) i hi
    rw [g0 _ (by simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hn.1, hn.2.1, hn.2.2.1⟩)]
    exact hl i hi
  have hs₃ : Space s₃ := fun k hk => by rw [h28]; exact hs k hk
  have hv28 : vdword (s₃.v .v28) 0 = s₃.syms VG.Impl.Sha3.AArch64.RoundConstants.sym := by
    simp only [s₃, RegUpd.v_setV, ite_true, vdword_ofVDwords_0]
    simp only [s₂, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]; rfl
  obtain ⟨t, x, l, k⟩ := rounds_run hl₃ hs₃ hv28 24 (Nat.le_refl _)
  have hv27 : vdword (t.v .v27) 0 = s₀.gpr .x30 := by
    rw [k.v]
    simp only [s₃, s₂, RegUpd.v_setV, RegUpd.v_write, s₁]
    rw [ite_eq_right (by decide)]; simp only [ite_true, vdword_ofVDwords_0]
  let u := t.write .x .x30 (vdword (t.v .v27) 0)
  have hrun : runBlock isa coreCode s₀ = some u := by
    unfold coreCode
    have e : runBlock isa ([.vop (.dup .d2 .v27 .x30), .adrSym .x16 VG.Impl.Sha3.AArch64.RoundConstants.sym, .vop (.dup .d2 .v28 .x16)] : List Instr) s₀ = some s₃ := rfl
    rw [List.append_assoc, runBlock_append _ _ e, runBlock_append _ _ x]
    rfl
  obtain ⟨tr, s', he, hq⟩ := WP.of_runBlock (M := isa) (Q := (· = u)) ⟨u, hrun, rfl⟩
  subst hq
  have hret : isa.ret s₀ u = some u := by
    simp only [isa, ret]
    rw [ite_eq_left]
    simp only [u, RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, hv27]
  refine ⟨_, u, Exec.call (call_callEntry s) he hret, hQ u ?_ ?_⟩
  · intro i hi
    have hn := reg_ne 0 (by decide) i hi
    have := (lanes_mod 24 _ _ _).mpr l i hi
    simp only [u, RegUpd.gpr_write, ite_eq_right hn.2.2.1]
    exact this
  · refine ⟨?_, fun r h27 h28' => ?_, k.rd, k.wr, k.sp, ?_⟩
    · simp only [u, RegUpd.gpr_write]
      rw [ite_eq_right (by decide), k.x28, h28]
    · simp only [u, RegUpd.v_write]
      rw [k.v]
      simp only [s₃, s₂, s₁, RegUpd.v_setV, RegUpd.v_write, ite_eq_right h27, ite_eq_right h28']
      rfl
    · have := k.frame
      rw [h28] at this
      exact this

end VG.Proof.Sha3.AArch64.Scalar
