module

public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.Scalar
public import VerifiedGarbage.Proof.Framework.AArch64.Interleave
import VerifiedGarbage.Proof.Sha3.AArch64.RoundConstants
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64

/-! # Keccak-f[1600] on three states on AArch64: two rounds of all three -/

-- separate module: so that the proof of the loop does not check these again

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Hybrid.X3

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Hybrid.X3
open VG.Proof.Sha3.AArch64 VG.Proof.Sha3.AArch64.Neon VG.Proof.Sha3.AArch64.Rounds
open VG.Proof.Sha3.AArch64.Eval (OnlyV Mode slotR slotBase)
open VG.Proof.Sha3.AArch64.Sha3.Vector (runBlock_append iota_pairs pairs_two CoreKeep)
open VG.Proof.Sha3.Forms (core)
open VG.Spec.Sha3 (keccakF rnd RC stateAt)
open VG.Proof.MlKem.AArch64 (VUpd wp_ldrq wp_vop)

/-! ## The vector rounds -/

theorem trn1_d2 (x : BitVec 128) : VPermOp.eval .trn1 .d2 x x = ofVDwords (vdword x 0) (vdword x 0) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes]

theorem trn2_d2 (x : BitVec 128) : VPermOp.eval .trn2 .d2 x x = ofVDwords (vdword x 1) (vdword x 1) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes]

theorem vecIota_run {r n : Nat} (hr : r < 2) {s : State} {A B : Spec.Sha3.State}
    (h : Vec.Pairs (r + 1) s (core A) (core B)) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x30 + BitVec.ofNat 64 32) 16)
    (hrc : vdword (s.mem.read (s.gpr .x30 + BitVec.ofNat 64 32) 16) r = RC n) :
    ∃ t, runBlock isa (vecIota r) s = some t ∧ Vec.Pairs (r + 1) t (rnd A n) (rnd B n) ∧ OnlyV s t := by
  let w := s.mem.read (s.gpr .x30 + BitVec.ofNat 64 32) 16
  let s₁ := s.setV .v31 w
  let s₂ := s₁.setV .v31 (VPermOp.eval (if r = 0 then .trn1 else .trn2) .d2 (s₁.v .v31) (s₁.v .v31))
  let s₃ := s₂.setV .v0 (s₂.v .v0 ^^^ s₂.v .v31)
  have e₁ : exec (.ldrq .v31 .x30 32) s = some s₁ := by
    simp only [exec, addr]
    rw [ite_eq_left ⟨by decide, by decide⟩]
    simp only [Option.bind_some, State.load]
    rw [ite_eq_left hin]; rfl
  have e₂ : exec (.vop (.perm (if r = 0 then .trn1 else .trn2) .d2 .v31 .v31 .v31)) s₁ = some s₂ := rfl
  have e₃ : exec (.vop (.logic .eor .v0 .v0 .v31)) s₂ = some s₃ := rfl
  have e31 : s₂.v .v31 = ofVDwords (RC n) (RC n) := by
    simp only [s₂, s₁, RegUpd.v_setV, ite_true]
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · rw [ite_eq_left rfl, trn1_d2, hrc]
    · rw [ite_eq_right (by decide), trn2_d2, hrc]
  refine ⟨s₃, ?_, iota_pairs (by omega) h ?_ fun v h0 h31 => ?_,
    ((OnlyV.setV _ _ _).trans (.setV _ _ _)).trans (.setV _ _ _)⟩
  · rw [vecIota, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃, runStep_some, runBlock_nil]
  · simp only [s₃, RegUpd.v_setV, ite_true]
    rw [e31]
    simp only [s₂, s₁, RegUpd.v_setV]
    rw [ite_eq_right (by decide), ite_eq_right (by decide)]
  · simp only [s₃, s₂, s₁, RegUpd.v_setV]
    rw [ite_eq_right h0, ite_eq_right h31, ite_eq_right h31]

theorem vecPlain_run {n : Nat} {s : State} {A B : Spec.Sha3.State} (hp : Vec.Pairs 0 s A B)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x30 + BitVec.ofNat 64 32) 16)
    (hrc : ∀ r < 2, vdword (s.mem.read (s.gpr .x30 + BitVec.ofNat 64 32) 16) r = RC (n + r)) :
    ∃ t, runBlock isa vecPlain s = some t ∧ Vec.Pairs 0 t (rnd (rnd A n) (n + 1)) (rnd (rnd B n) (n + 1)) ∧ OnlyV s t := by
  have keep : ∀ {t : State}, OnlyV s t → t.gpr .x30 = s.gpr .x30 ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
    rintro t ⟨v, rfl⟩; exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₁, x₁, p₁, o₁⟩ := Vec.round_ok (by decide) (Neon.X2.mixed_ok 0 (by decide)) hp
  have k₁ := keep o₁
  obtain ⟨s₂, x₂, p₂, o₂⟩ := vecIota_run (n := n) (r := 0) (by decide) p₁
    (by rw [k₁.1, k₁.2.2.1, k₁.2.2.2]; exact hin) (by rw [k₁.1, k₁.2.1]; exact hrc 0 (by decide))
  obtain ⟨s₃, x₃, p₃, o₃⟩ := Vec.round_ok (r := 1) (by decide) (Neon.X2.mixed_ok 1 (by decide)) p₂
  have o := (o₁.trans o₂).trans o₃
  have k := keep o
  obtain ⟨s₄, x₄, p₄, o₄⟩ := vecIota_run (n := n + 1) (r := 1) (by decide) p₃
    (by rw [k.1, k.2.2.1, k.2.2.2]; exact hin) (by rw [k.1, k.2.1]; exact hrc 1 (by decide))
  refine ⟨s₄, ?_, pairs_two.mp p₄, o.trans o₄⟩
  rw [vecPlain, List.append_assoc, List.append_assoc, runBlock_append _ _ x₁, runBlock_append _ _ x₂,
    runBlock_append _ _ x₃, x₄]

theorem order_ok : Schedule.ok .x30 order vecPlain = true := by decide +kernel

theorem vecBody_run {n : Nat} {s : State} {A B : Spec.Sha3.State} (hp : Vec.Pairs 0 s A B)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x30 + BitVec.ofNat 64 32) 16)
    (hrc : ∀ r < 2, vdword (s.mem.read (s.gpr .x30 + BitVec.ofNat 64 32) 16) r = RC (n + r)) :
    ∃ t, runBlock isa vecBody s = some t ∧ Vec.Pairs 0 t (rnd (rnd A n) (n + 1)) (rnd (rnd B n) (n + 1)) ∧ OnlyV s t := by
  obtain ⟨t, x, h⟩ := vecPlain_run hp hin hrc
  exact ⟨t, (Schedule.run_eq order order_ok _).trans x, h⟩

/-! ## The general rounds -/

/-- The third state's lanes, before round `r`. -/
abbrev Third (r : Nat) (s : State) (A : Spec.Sha3.State) : Prop := Gen.Lanes conf.pd r s A

def mode : Mode := ⟨.x30, 0, 3⟩

/-- The registers the rounds write: all but `x30`. -/
def writes : Nat := 0xfffffff

theorem gen_rounds_ok : ∀ r < 2, Gen.ok conf.pd mode writes (conf.round r) r = true := by decide +kernel

/-- What the general rounds keep. -/
structure GKeep (s t : State) : Prop where
  x30 : t.gpr .x30 = s.gpr .x30
  v : t.v = s.v
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x30, 24⟩] s.mem t.mem

theorem GKeep.refl (s : State) : GKeep s s := ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem GKeep.trans {s t u : State} (h : GKeep s t) (g : GKeep t u) : GKeep s u :=
  ⟨g.x30.trans h.x30, g.v.trans h.v, g.rd.trans h.rd, g.wr.trans h.wr, g.sp.trans h.sp, h.frame.trans (h.x30 ▸ g.frame)⟩

/-- A word beyond the window's spilled lanes. -/
theorem GKeep.word {s t : State} (h : GKeep s t) {o : Nat} (h1 : 24 ≤ o) (h2 : o < 4096) :
    t.mem.readW (s.gpr .x30 + BitVec.ofNat 64 o) 64 = s.mem.readW (s.gpr .x30 + BitVec.ofNat 64 o) 64 :=
  h.frame.readW (r := ⟨s.gpr .x30 + BitVec.ofNat 64 o, 8⟩) (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ h1 (by omega)) (by decide)

theorem mode_base (s : State) : slotBase mode s = s.gpr .x30 := by simp [slotBase, mode]

theorem genRound_run {r : Nat} (hr : r < 2) {s : State} {A : Spec.Sha3.State} (hl : Third r s A)
    (hs : ∀ k < 3, InRegions s.wr (s.gpr .x30 + BitVec.ofNat 64 (8 * k)) 8) :
    ∃ t, runBlock isa (conf.round r) s = some t ∧ Third (r + 1) t (core A) ∧ GKeep s t := by
  obtain ⟨t, x, l, k⟩ := Gen.round_ok (Gen.pd_lt conf) (m := mode) (w := writes) (by decide) hr (gen_rounds_ok _ hr) (s := s)
    ⟨by decide, fun k hk => by rw [mode_base]; exact hs k hk⟩ hl
  refine ⟨t, x, l, ⟨k.gpr _ (by decide), k.v, k.rd, k.wr, k.sp, ?_⟩⟩
  have := k.frame
  rw [slotR, mode_base] at this
  exact this

theorem genIota_run {r n : Nat} {s : State} {A : Spec.Sha3.State} (hl : Third (r + 1) s (core A)) (hr : r < 2)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x30 + BitVec.ofNat 64 (32 + 8 * r)) 8)
    (hrc : s.mem.readW (s.gpr .x30 + BitVec.ofNat 64 (32 + 8 * r)) 64 = RC n) :
    ∃ t, runBlock isa (genIota r) s = some t ∧ Third (r + 1) t (rnd A n) ∧ GKeep s t := by
  refine Interleave.runBlock_of_WP (wp_ldr (a := s.gpr .x30 + BitVec.ofNat 64 (32 + 8 * r)) ⟨by omega, by omega⟩ rfl hin
    fun t d => wp_eor fun u e => wp_nil ⟨?_, ?_⟩)
  · refine Scalar.iota_lanes (pd := conf.pd) (by decide) hl ?_ fun q h0 h16 => ?_
    · rw [e.gpr, d.gpr, d.other _ (by decide), hrc]
    · rw [e.other _ h0, d.other _ h16]
  · exact ⟨by rw [e.other _ (by decide), d.other _ (by decide)], e.vec.trans d.vec, e.rd.trans d.rd, e.wr.trans d.wr,
      e.sp.trans d.sp, by rw [e.mem, d.mem]; exact Frame.refl _ _⟩

theorem third_two {s : State} {A : Spec.Sha3.State} : Third 2 s A ↔ Third 0 s A := by
  simp only [Third, Gen.Lanes, Impl.Sha3.AArch64.Scalar.reg, home_mod 2, home_mod 0]

theorem genBody_run {n : Nat} {s : State} {A : Spec.Sha3.State} (hl : Third 0 s A)
    (hs : ∀ k < 3, InRegions s.wr (s.gpr .x30 + BitVec.ofNat 64 (8 * k)) 8)
    (hin : ∀ r < 2, InRegions (s.rd ++ s.wr) (s.gpr .x30 + BitVec.ofNat 64 (32 + 8 * r)) 8)
    (hrc : ∀ r < 2, s.mem.readW (s.gpr .x30 + BitVec.ofNat 64 (32 + 8 * r)) 64 = RC (n + r)) :
    ∃ t, runBlock isa genBody s = some t ∧ Third 0 t (rnd (rnd A n) (n + 1)) ∧ GKeep s t := by
  have iota : ∀ {t : State} {r : Nat}, r < 2 → GKeep s t →
      InRegions (t.rd ++ t.wr) (t.gpr .x30 + BitVec.ofNat 64 (32 + 8 * r)) 8 ∧
        t.mem.readW (t.gpr .x30 + BitVec.ofNat 64 (32 + 8 * r)) 64 = RC (n + r) := fun {t r} hr k => by
    rw [k.x30, k.rd, k.wr, k.word (by omega) (by omega)]; exact ⟨hin r hr, hrc r hr⟩
  obtain ⟨s₁, x₁, l₁, k₁⟩ := genRound_run (r := 0) (by decide) hl hs
  obtain ⟨s₂, x₂, l₂, k₂⟩ := genIota_run (r := 0) (n := n) l₁ (by decide) (iota (by decide) k₁).1 (iota (by decide) k₁).2
  have k := k₁.trans k₂
  obtain ⟨s₃, x₃, l₃, k₃⟩ := genRound_run (r := 1) (by decide) l₂ fun j hj => by rw [k.x30, k.wr]; exact hs j hj
  have kk := k.trans k₃
  obtain ⟨s₄, x₄, l₄, k₄⟩ := genIota_run (r := 1) (n := n + 1) l₃ (by decide) (iota (by decide) kk).1 (iota (by decide) kk).2
  refine ⟨s₄, ?_, third_two.mp l₄, kk.trans k₄⟩
  rw [genBody, List.append_assoc, List.append_assoc, runBlock_append _ _ x₁, runBlock_append _ _ x₂,
    runBlock_append _ _ x₃, x₄]

/-! ## Both -/

theorem indeps : Interleave.Indeps .x30 vecBody genBody := Interleave.indeps_of_check (by decide +kernel)

/-- Two rounds of all three states. -/
theorem rounds_ok {n : Nat} {s : State} {A B C : Spec.Sha3.State} (hp : Vec.Pairs 0 s A B) (hl : Third 0 s C)
    (hs : ∀ k < 3, InRegions s.wr (s.gpr .x30 + BitVec.ofNat 64 (8 * k)) 8)
    (hin : ∀ m, m ≤ 16 → ∀ j, j + m ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .x30 + BitVec.ofNat 64 (32 + j)) m)
    (hrc : ∀ r < 2, s.mem.readW (s.gpr .x30 + BitVec.ofNat 64 (32 + 8 * r)) 64 = RC (n + r)) :
    WP isa (.block rounds) s fun t => Vec.Pairs 0 t (rnd (rnd A n) (n + 1)) (rnd (rnd B n) (n + 1)) ∧
      Third 0 t (rnd (rnd C n) (n + 1)) ∧ t.gpr .x30 = s.gpr .x30 ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      Frame [⟨s.gpr .x30, 24⟩] s.mem t.mem := by
  refine Interleave.WP.weave indeps ?_
  obtain ⟨t, x, pt, ot⟩ := vecBody_run (n := n) hp (hin 16 (by decide) 0 (by decide)) fun r hr => by
    rw [vdword_read16 _ _ hr, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hrc r hr
  refine WP.mono (WP.of_runBlock (M := isa) (Q := (· = t)) ⟨t, x, rfl⟩) fun _ e => ?_
  subst e
  obtain ⟨v, rfl⟩ := ot
  obtain ⟨u, y, lu, ku⟩ := genBody_run (n := n) (s := { s with v := v }) hl hs
    (fun r hr => hin 8 (by decide) (8 * r) (by omega)) hrc
  refine WP.mono (WP.of_runBlock (M := isa) (Q := (· = u)) ⟨u, y, rfl⟩) fun _ e => ?_
  subst e
  exact ⟨fun i hi => by rw [ku.v]; exact pt i hi, lu, ku.x30, ku.rd, ku.wr, ku.sp, ku.frame⟩

end VG.Proof.Sha3.AArch64.Hybrid.X3
