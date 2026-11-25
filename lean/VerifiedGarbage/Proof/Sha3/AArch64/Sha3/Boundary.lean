module

public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Rounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.StraightV

/-!
# Keccak-f[1600] on AArch64, in vector registers: entry and exit

Saving the vector registers the calling convention preserves, and one state
in the low doublewords of the lanes' registers.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64 VG.Proof.Sha3.AArch64.Neon
open VG.Spec.Sha3 (keccakF stateAt)
open VG.Proof.MlKem.AArch64 (VUpd VMem VChg wp_strq wp_ldrq wp_vop vupd_setV)

/-! ## The vector registers the calling convention preserves -/

/-- Those of `v` at `q`. -/
def SavedV (v : VReg → BitVec 128) (m : Mem) (q : Addr) : Prop :=
  ∀ i < 8, m.read (q + BitVec.ofNat 64 (16 * i)) 16 = v (vreg (8 + i))

theorem SavedV.frame {v : VReg → BitVec 128} {m m' : Mem} {q : Addr} (h : SavedV v m q) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (Region.mk q 128).Disjoint r) : SavedV v m' q := fun i hi => by
  rw [hf.read (r := ⟨q, 128⟩) (Offset.contains_base q (by omega) (by omega)) hd (by decide)]
  exact h i hi

theorem preservedV_idx : ∀ r ∈ preservedV, ∃ i < 8, r = vreg (8 + i) := by decide
theorem preservedV_idx' : ∀ i < 8, vreg (8 + i) ∈ preservedV := by decide

theorem save_ok {s : State} {b : Reg} {off : Nat} (ho : off % 16 = 0) (hlt : off ≤ 32768) {q : Addr}
    (hq : s.gpr b + BitVec.ofNat 64 off = q) (hw : ∀ i < 8, InRegions s.wr (q + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block (save b off)) s fun t => VMem s t t.mem ∧ SavedV s.v t.mem q ∧ Frame [⟨q, 128⟩] s.mem t.mem := by
  suffices h : ∀ k ≤ 8, WP isa (.block ((List.range k).map fun i => .strq (vreg (8 + i)) b (off + 16 * i))) s fun t =>
      VMem s t t.mem ∧ (∀ i < k, t.mem.read (q + BitVec.ofNat 64 (16 * i)) 16 = s.v (vreg (8 + i))) ∧
        Frame [⟨q, 128⟩] s.mem t.mem from h 8 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨c, h, f⟩ => wp_strq (a := q + BitVec.ofNat 64 (16 * k)) ⟨by omega, by omega⟩
      (by rw [c.gpr, BitVec.ofNat_add, ← BitVec.add_assoc, hq]) (by rw [c.wr]; exact hw k (by omega)) fun u d =>
      wp_nil ⟨⟨d.gpr.trans c.gpr, d.v.trans c.v, rfl, d.rd.trans c.rd, d.wr.trans c.wr, d.sp.trans c.sp⟩, fun i hi => ?_, ?_⟩
    · rw [d.mem, c.v]
      by_cases hik : i = k
      · subst hik; exact read_write16 _ _ _
      · rw [Mem.read_write_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)]
        exact h i (by omega)
    · rw [d.mem]
      exact f.write (List.mem_singleton_self _) _ (Offset.contains_base q (by omega) (by omega))

theorem restore_ok {v : VReg → BitVec 128} {s : State} {b : Reg} {off : Nat} (ho : off % 16 = 0) (hlt : off ≤ 32768) {q : Addr}
    (hq : s.gpr b + BitVec.ofNat 64 off = q) (hin : ∀ i < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16 * i)) 16)
    (hs : SavedV v s.mem q) : WP isa (.block (restore b off)) s fun t =>
      VChg preservedV s t ∧ ∀ r ∈ preservedV, t.v r = v r := by
  suffices h : ∀ k ≤ 8, WP isa (.block ((List.range k).map fun i => .ldrq (vreg (8 + i)) b (off + 16 * i))) s fun t =>
      VChg preservedV s t ∧ ∀ i < k, t.v (vreg (8 + i)) = v (vreg (8 + i)) from
    WP.mono (h 8 (Nat.le_refl _)) fun t ⟨c, h⟩ => ⟨c, fun r hr => by
      obtain ⟨i, hi, rfl⟩ := preservedV_idx r hr; exact h i hi⟩
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨.refl _ s, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨c, h⟩ => wp_ldrq (a := q + BitVec.ofNat 64 (16 * k)) ⟨by omega, by omega⟩
      (by rw [c.gpr, BitVec.ofNat_add, ← BitVec.add_assoc, hq]) (by rw [c.rd, c.wr]; exact hin k (by omega)) fun u d =>
      wp_nil ⟨(c.trans d.chg).mono fun r hr => ?_, fun i hi => ?_⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · rw [List.mem_singleton] at hr; subst hr; exact preservedV_idx' k (by omega)
    · by_cases hik : i = k
      · subst hik; rw [d.v, c.mem]; exact hs i (by omega)
      · rw [d.other _ fun e => hik (by have := (vreg_inj (8 + i) (by omega) (8 + k) (by omega)).mp e; omega)]
        exact h i (by omega)

/-! ## One state -/

/-- The low doublewords of the lanes' registers hold the state. -/
def One (s : State) (A : Spec.Sha3.State) : Prop := ∀ i < 25, vdword (s.v (vreg i)) 0 = A[i]!

/-- With what the high ones hold, two states. -/
theorem One.pairs {s : State} {A : Spec.Sha3.State} (h : One s A) : ∃ B, Pairs s A B :=
  ⟨Vector.ofFn fun i => vdword (s.v (vreg i.val)) 1, fun i hi => vec64_ext
    (by rw [vdword_ofVDwords_0]; exact h i hi)
    (by rw [vdword_ofVDwords_1, getElem!_eq _ hi]; simp only [Vector.getElem_ofFn])⟩

theorem one_of_pairs {s : State} {A B : Spec.Sha3.State} (h : Pairs s A B) : One s A := fun i hi => by
  rw [h i hi, vdword_ofVDwords_0]

theorem dwords (x : BitVec 128) : x = ofVDwords (vdword x 0) (vdword x 1) :=
  vec64_ext (vdword_ofVDwords_0 _ _).symm (vdword_ofVDwords_1 _ _).symm

theorem ext8_low (x : BitVec 128) : vdword (((x ++ x) >>> (8 * 8)).extractLsb' 0 128) 0 = vdword x 1 := by
  rw [dwords x, ext8_pair, vdword_ofVDwords_0, vdword_ofVDwords_1]

theorem zip1_d2 (x y : BitVec 128) : VPermOp.eval .zip1 .d2 x y = ofVDwords (vdword x 0) (vdword y 0) := by
  simp [VPermOp.eval, VArr.lanes, VArr.ofLanes]

/-- A read of a lane's 16 bytes' words. -/
theorem state_lane (m : Mem) (p : Addr) {i : Nat} (hi : i < 25) :
    (stateAt m p)[i]! = m.readW (p + BitVec.ofNat 64 (8 * i)) 64 := by
  rw [getElem!_eq _ hi]; simp only [stateAt, Vector.getElem_ofFn]

/-- The registers loading may change. -/
theorem load_ok {s : State} {b : Reg} {p : Addr} (hp : s.gpr b = p)
    (hin : ∀ i < 12, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (16 * i)) 16)
    (hlast : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 192) 8) :
    WP isa (.block (load b)) s fun t => One t (stateAt s.mem p) ∧ (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have half : ∀ k ≤ 12, WP isa (.block ((List.range k).flatMap fun i => [.ldrq (vreg (2 * i)) b (16 * i),
      .vop (.ext (vreg (2 * i + 1)) (vreg (2 * i)) (vreg (2 * i)) 8)])) s fun t =>
      (∀ i < 2 * k, vdword (t.v (vreg i)) 0 = s.mem.readW (p + BitVec.ofNat 64 (8 * i)) 64) ∧ VChg allV s t := by
    intro k hk
    induction k with
    | zero => exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), .refl _ s⟩
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
      refine WP.mono (ih (by omega)) fun t ⟨h, c⟩ => ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine wp_ldrq (a := p + BitVec.ofNat 64 (16 * k)) ⟨by omega, by omega⟩ (by rw [c.gpr, hp])
        (by rw [c.rd, c.wr]; exact hin k (by omega)) fun u d => ?_
      refine wp_vop rfl fun w e => wp_nil ⟨fun i hi => ?_, ((c.trans d.chg).trans e.chg).mono fun r _ => allV_mem r⟩
      rw [c.mem] at d
      have n01 : vreg (2 * k) ≠ vreg (2 * k + 1) := fun e => by
        have := (vreg_inj (2 * k) (by omega) (2 * k + 1) (by omega)).mp e; omega
      by_cases h1 : i = 2 * k + 1
      · subst h1
        rw [e.v, ext8_low, d.v, vdword_read16 _ _ (by decide), BitVec.add_assoc, ← BitVec.ofNat_add]
        congr 3; omega
      · rw [e.other _ fun e => h1 ((vreg_inj i (by omega) (2 * k + 1) (by omega)).mp e)]
        by_cases h0 : i = 2 * k
        · subst h0
          rw [d.v, vdword_read16 _ _ (by decide)]
          rw [show 16 * k = 8 * (2 * k) by omega]; simp
        · rw [d.other _ fun e => h0 ((vreg_inj i (by omega) (2 * k) (by omega)).mp e)]
          exact h i (by omega)
  unfold load
  rw [WP.block_append_iff]
  refine WP.mono (half 12 (Nat.le_refl _)) fun t ⟨h, c⟩ => ?_
  refine wp_ldr (a := p + BitVec.ofNat 64 192) ⟨by decide, by decide⟩ (by rw [c.gpr, hp]) (by rw [c.rd, c.wr]; exact hlast)
    fun u d => ?_
  refine WP.cons (s' := u.setV .v24 (ofVDwords (u.gpr .x16) (u.gpr .x16))) rfl (wp_nil ⟨fun i hi => ?_, fun g hg => ?_,
    d.mem.trans c.mem, d.rd.trans c.rd, d.wr.trans c.wr, d.sp.trans c.sp⟩)
  · rw [state_lane _ _ hi, RegUpd.v_setV]
    by_cases h24 : i = 24
    · subst h24
      rw [ite_eq_left (by decide), vdword_ofVDwords_0, d.gpr, c.mem]
    · rw [ite_eq_right (show ¬vreg i = VReg.v24 from fun e => h24 ((vreg_inj i (by omega) 24 (by omega)).mp e)), d.vec]
      exact h i (by omega)
  · rw [RegUpd.gpr_setV, d.other g hg, c.gpr]

theorem store_ok {s : State} {b : Reg} (hb : b ≠ .x16) {p : Addr} (hp : s.gpr b = p) {A : Spec.Sha3.State} (hA : One s A)
    (hw : ∀ i < 12, InRegions s.wr (p + BitVec.ofNat 64 (16 * i)) 16) (hlast : InRegions s.wr (p + BitVec.ofNat 64 192) 8) :
    WP isa (.block (store b)) s fun t => stateAt t.mem p = A ∧ Frame [⟨p, 200⟩] s.mem t.mem ∧
      (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have half : ∀ k ≤ 12, WP isa (.block ((List.range k).flatMap fun i =>
      [.vop (.perm .zip1 .d2 .v25 (vreg (2 * i)) (vreg (2 * i + 1))), .strq .v25 b (16 * i)])) s fun t =>
      (∀ i < 2 * k, t.mem.readW (p + BitVec.ofNat 64 (8 * i)) 64 = A[i]!) ∧ Frame [⟨p, 200⟩] s.mem t.mem ∧
        (∀ i < 25, t.v (vreg i) = s.v (vreg i)) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
    intro k hk
    induction k with
    | zero => exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
      refine WP.mono (ih (by omega)) fun t ⟨h, f, v, g, rd, wr, sp⟩ => ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      refine wp_vop rfl fun u d => ?_
      refine wp_strq (a := p + BitVec.ofNat 64 (16 * k)) ⟨by omega, by omega⟩ (by rw [d.gpr, g, hp])
        (by rw [d.wr, wr]; exact hw k (by omega)) fun w m => wp_nil ?_
      have mm : w.mem = (t.mem.writeW (p + BitVec.ofNat 64 (8 * (2 * k))) A[2 * k]!).writeW
          (p + BitVec.ofNat 64 (8 * (2 * k + 1))) A[2 * k + 1]! := by
        rw [m.mem, d.mem, d.v, zip1_d2, v _ (by omega), v _ (by omega), hA _ (by omega), hA _ (by omega), write16_dwords,
          BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * k = 8 * (2 * k) by omega,
          show 8 * (2 * k) + 8 = 8 * (2 * k + 1) by omega]
      refine ⟨fun i hi => ?_, ?_, fun i hi => ?_, m.gpr.trans (d.gpr.trans g), m.rd.trans (d.rd.trans rd),
        m.wr.trans (d.wr.trans wr), m.sp.trans (d.sp.trans sp)⟩
      · rw [mm]
        by_cases h1 : i = 2 * k + 1
        · subst h1; exact Mem.readW_writeW_self64 _ _ _
        · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
          by_cases h0 : i = 2 * k
          · subst h0; exact Mem.readW_writeW_self64 _ _ _
          · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
            exact h i (by omega)
      · rw [m.mem, d.mem]
        exact f.write (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))
      · rw [m.v, d.other _ fun e => by have := (vreg_inj i (by omega) 25 (by omega)).mp e; omega]
        exact v i hi
  unfold store
  rw [WP.block_append_iff]
  refine WP.mono (half 12 (Nat.le_refl _)) fun t ⟨h, f, v, g, rd, wr, sp⟩ => ?_
  refine WP.cons (s' := t.write .x .x16 (vdword (t.v .v24) 0)) rfl ?_
  refine wp_str (a := p + BitVec.ofNat 64 192) ⟨by decide, by decide⟩
    (by rw [RegUpd.gpr_write, ite_eq_right hb, g, hp]) (by rw [RegUpd.wr_write, wr]; exact hlast) fun u m => wp_nil ?_
  have mm : u.mem = t.mem.writeW (p + BitVec.ofNat 64 (8 * 24)) A[24]! := by
    rw [m.mem, RegUpd.gpr_write, ite_eq_left rfl, BitVec.setWidth_eq, show VReg.v24 = vreg 24 from rfl, v _ (by decide),
      hA _ (by decide)]; rfl
  refine ⟨Vector.ext fun i hi => ?_, ?_, fun r hr => ?_, m.rd.trans rd, m.wr.trans wr, m.sp.trans sp⟩
  · rw [← getElem!_eq _ hi, ← getElem!_eq _ hi, state_lane _ _ hi, mm]
    by_cases h24 : i = 24
    · subst h24; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
      exact h i (by omega)
  · rw [mm]; exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base p (by omega) (by omega))
  · rw [m.gpr, RegUpd.gpr_write, ite_eq_right hr, g]

/-! ## The functions on one state -/

/-- What holds between the entry from `o` and the exit, `T` the working space. -/
structure In (o s : State) (T : Addr) : Prop where
  table : RcTable s T
  saved : SavedV o.v s.mem (T + BitVec.ofNat 64 384)
  frame : Frame [⟨T, 512⟩] o.mem s.mem
  rd : s.rd = o.rd
  wr : s.wr = o.wr
  sp : s.sp = o.sp

theorem In.core {o s t : State} {T : Addr} (h : In o s T) (k : CoreKeep s t) : In o t T :=
  ⟨h.table.core k, by rw [k.mem]; exact h.saved, by rw [k.mem]; exact h.frame, k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp⟩

/-- The state and the working space are apart, and writable. -/
structure Space (o : State) (T : Addr) : Prop where
  state : ∀ k n, k + n ≤ 200 → InRegions o.wr (o.gpr .x0 + BitVec.ofNat 64 k) n
  work : ∀ k n, k + n ≤ 512 → InRegions o.wr (T + BitVec.ofNat 64 k) n
  apart : (Region.mk (o.gpr .x0) 200).Disjoint ⟨T, 512⟩

theorem table_saved (T : Addr) : (Region.mk (T + BitVec.ofNat 64 384) 128).Disjoint ⟨T, 384⟩ :=
  Offset.disjoint_base _ (by decide) (by decide)

private theorem readable {o t : State} (h1 : t.wr = o.wr) {a : Addr} {n : Nat} : InRegions o.wr a n → InRegions (t.rd ++ t.wr) a n :=
  fun ⟨R, hR, hc⟩ => ⟨R, List.mem_append_right _ (by rw [h1]; exact hR), hc⟩

theorem frame_work {T : Addr} {m m' : Mem} {k n : Nat} (h : Frame [⟨T + BitVec.ofNat 64 k, n⟩] m m') (hk : k + n ≤ 512) :
    Frame [⟨T, 512⟩] m m' :=
  h.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ hk⟩

theorem enter_ok {o : State} {b : Reg} (hb : b ≠ .x16) (hs : Space o (o.gpr b)) :
    WP isa (.block (save b 384 ++ rcStore b 0 ++ load .x0)) o fun t => In o t (o.gpr b) ∧
      One t (stateAt o.mem (o.gpr .x0)) ∧ ∀ g, g ≠ .x16 → t.gpr g = o.gpr g := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (save_ok (by decide) (by decide) rfl fun i hi => ?_) fun t₁ ⟨c₁, v₁, f₁⟩ => ?_
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add]; exact hs.work _ _ (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (rcStore_ok hb (T := o.gpr b) (by decide) (by decide) (by rw [c₁.gpr]; simp) fun r hr => ?_)
    fun t₂ ⟨g₂, _, rd₂, wr₂, sp₂, f₂, T₂⟩ => ?_
  · rw [c₁.wr]; exact hs.work _ _ (by omega)
  have f₁' := frame_work f₁ (by decide)
  have f₂' : Frame [⟨o.gpr b, 512⟩] t₁.mem t₂.mem :=
    frame_work (T := o.gpr b) (k := 0) (n := 384) (by simpa using f₂) (by decide)
  have f := f₁'.trans f₂'
  refine WP.mono (load_ok (p := o.gpr .x0) (by rw [g₂ _ (by decide), c₁.gpr]) (fun i hi => ?_) ?_)
    fun t₃ ⟨l₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ⟨⟨?_, ?_, by rw [m₃]; exact f, rd₃.trans (rd₂.trans c₁.rd), wr₃.trans (wr₂.trans c₁.wr),
      sp₃.trans (sp₂.trans c₁.sp)⟩, fun i hi => ?_, fun g hg => by rw [g₃ g hg, g₂ g hg, c₁.gpr]⟩
  · exact readable (wr₂.trans c₁.wr) (hs.state _ _ (by omega))
  · exact readable (wr₂.trans c₁.wr) (hs.state 192 8 (by decide))
  · exact T₂.frame (rs := []) (by rw [m₃]; exact Frame.refl _ _) (fun r hr => absurd hr (List.not_mem_nil)) rd₃ wr₃
  · rw [m₃]; exact v₁.frame f₂ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact table_saved _
  · rw [l₃ i hi, state_lane _ _ hi, state_lane _ _ hi]
    exact f.readW (r := ⟨o.gpr .x0, 200⟩) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hs.apart) (by decide)

theorem exit_ok {o s : State} {b : Reg} (hb : b ≠ .x16) (hs : Space o (o.gpr b)) {A : Spec.Sha3.State}
    (hi : In o s (o.gpr b)) (hA : One s A) (h0 : s.gpr .x0 = o.gpr .x0) (hb' : s.gpr b = o.gpr b) {is : List Instr} {Q : State → Prop}
    (hQ : ∀ t, stateAt t.mem (o.gpr .x0) = A → (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) → t.sp = o.sp →
      (∀ r ∈ preservedV, t.v r = o.v r) → WP isa (.block is) t Q) :
    WP isa (.block (store .x0 ++ (restore b 384 ++ is))) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (store_ok (by decide) (p := o.gpr .x0) h0 hA (fun i h => ?_) ?_) fun t₁ ⟨a₁, f₁, g₁, rd₁, wr₁, sp₁⟩ => ?_
  · rw [hi.wr]; exact hs.state _ _ (by omega)
  · rw [hi.wr]; exact hs.state _ _ (by decide)
  rw [WP.block_append_iff]
  have sv : SavedV o.v t₁.mem (o.gpr b + BitVec.ofNat 64 384) := hi.saved.frame f₁ fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact fun a h1 h2 => hs.apart a h2 (Offset.sub_base (k := 512) _ (by decide) a h1)
  refine WP.mono (restore_ok (by decide) (by decide) (by rw [g₁ _ hb, hb']) (fun i h => ?_) sv) fun t₂ ⟨c₂, v₂⟩ =>
    hQ t₂ (by rw [c₂.mem]; exact a₁) (fun g hg => by rw [c₂.gpr, g₁ g hg]) (c₂.sp.trans (sp₁.trans hi.sp)) v₂
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact readable (wr₁.trans hi.wr) (hs.work _ _ (by omega))

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .x16 ∧ r ≠ .x17 ∧ r ≠ .x0 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x9 ∧ r ≠ .x10 := by decide

theorem permute_ok (s : State) (hp : Proof.Sha3.permuteAArch64.pre s) :
    WP isa permute s fun t => abiPreserved s t ∧ Proof.Sha3.permuteAArch64.post s t := by
  obtain ⟨hrd, hwr, hdis⟩ := hp
  have hs : Space s (s.gpr .x1) := ⟨fun k n h => ⟨⟨s.gpr .x0, 200⟩, by simp [hwr], Offset.contains_base _ h (by omega)⟩,
    fun k n h => ⟨⟨s.gpr .x1, 512⟩, by simp [hwr], Offset.contains_base _ h (by omega)⟩, hdis⟩
  unfold permute
  refine WP.seq (WP.mono (enter_ok (by decide) hs) fun t₁ ⟨i₁, l₁, g₁⟩ => ?_)
  obtain ⟨B, hB⟩ := l₁.pairs
  refine WP.seq (WP.mono (rounds_ok hB (by rw [g₁ _ (by decide)]; exact i₁.table)) fun t₂ ⟨k₂, p₂⟩ => ?_)
  rw [← List.append_nil (restore .x1 384)]
  refine exit_ok (by decide) hs (i₁.core k₂) (one_of_pairs p₂) (by rw [k₂.gpr _ (by decide) (by decide), g₁ _ (by decide)])
    (by rw [k₂.gpr _ (by decide) (by decide), g₁ _ (by decide)]) fun t₃ a₃ g₃ sp₃ v₃ => wp_nil ⟨⟨fun r hr => ?_, sp₃,
      fun r hr => by rw [v₃ r hr]⟩, a₃⟩
  have hn := preserved_ne r hr
  rw [g₃ r hn.1, k₂.gpr r hn.1 hn.2.1, g₁ r hn.1]

end VG.Proof.Sha3.AArch64.Sha3.Vector
