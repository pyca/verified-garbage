module

import VerifiedGarbage.Proof.Rc2.CbcList
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Rc2.CbcMemory
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Mash
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Rc2.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Simd
public import VerifiedGarbage.Proof.Framework.Mem

/-! ### `Rc2.AArch64.Vec.Group`, which only this module used -/

section

/-! ### `Rc2.AArch64.Vec.Rounds`, which only this module used -/

section

/-!
# The sixteen reverse rounds on eight blocks

`rounds_ok`: on both sets, the reverse rounds of `Spec.Rc2.decryptBlock`.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- Word `i` of both sets reverse mashed. -/
theorem mashStep_ok {s : State} {m : Mem} {p : Addr} (hs : SchedV s m p)
    {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) {i : Nat} (hi : i < 4) :
    ∃ s', runBlock isa (rmash 0 i ++ rmash 1 i) s = some s' ∧
      Sets s' (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i (vs b)) ∧
      VKeep s s' := by
  obtain ⟨s₁, r₁, w₁, o₁, k₁, sp₁⟩ := rmash_ok hs (h := 0) (by decide) hi (hv 0 (by decide))
  have f₀ := regs_fixed 0 i (by decide) hi
  have sch₁ : ∀ r < 8, s₁.v (treg r) = s.v (treg r) := by
    intro r hr
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega_using [hr])
    exact o₁ _ (f₀.2.2.2.2.2.2.2.2 r hr).1 a0 a1 a2 a3 a4 a5
  have v₁ : VWords s₁ 1 (fun b => vs (4 * 1 + b)) := (hv 1 (by decide)).keep fun i' hi' => by
    have wn := wreg_ne 1 i' (by decide)
    exact o₁ _ (regs_cross 0 i i' (by decide) hi hi').1 wn.1 wn.2.1 wn.2.2.1 wn.2.2.2.1
      wn.2.2.2.2.1 wn.2.2.2.2.2.1
  obtain ⟨s₂, r₂, w₂, o₂, k₂, sp₂⟩ :=
    rmash_ok (fun r hr => (sch₁ r hr).trans (hs r hr)) (h := 1) (by decide) hi v₁
  have f₁ := regs_fixed 1 i (by decide) hi
  have w₂' : VWords s₂ 0 (fun b => Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i
      (vs (4 * 0 + b))) := w₁.keep fun i' hi' => by
    have wn := wreg_ne 0 i' (by decide)
    exact o₂ _ (regs_cross 1 i i' (by decide) hi hi').1 wn.1 wn.2.1 wn.2.2.1 wn.2.2.2.1
      wn.2.2.2.2.1 wn.2.2.2.2.2.1
  refine ⟨s₂, runBlock_cat_some r₁ r₂, fun h hh => ?_, ⟨k₁.trans k₂, by rw [sp₂, sp₁], ?_, ?_⟩⟩
  · match h, hh with
    | 0, _ => exact w₂'
    | 1, _ => exact w₂
  · intro r hr
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega_using [hr])
    rw [o₂ _ (f₁.2.2.2.2.2.2.2.2 r hr).1 a0 a1 a2 a3 a4 a5]
    exact sch₁ r hr
  · rw [o₂ _ f₁.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      o₁ _ f₀.2.1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem mashSteps_ok {m : Mem} {p : Addr} (is : List Nat) (his : ∀ i ∈ is, i < 4) {s : State}
    (hs : SchedV s m p) {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa (is.flatMap fun i => rmash 0 i ++ rmash 1 i) s = some s' ∧
      Sets s' (fun b => is.foldl (fun r i =>
        Spec.Rc2.reverseMash (Spec.Rc2.scheduleAt m p) i r) (vs b)) ∧
      VKeep s s' := by
  induction is generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons i is ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := mashStep_ok hs hv (his i (by simp))
    obtain ⟨s₂, r₂, v₂, k₂⟩ := ih (fun i hi => his i (by simp [hi])) (hs.keep k₁) v₁
    exact ⟨s₂, by rw [List.flatMap_cons]; exact runBlock_cat_some r₁ r₂, v₂, k₁.trans k₂⟩

theorem rmashRound_ok {m : Mem} {p : Addr} {s : State} (hs : SchedV s m p)
    {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa rmashRound s = some s' ∧
      Sets s' (fun b => Spec.Rc2.reverseMashRound (Spec.Rc2.scheduleAt m p) (vs b)) ∧
      VKeep s s' :=
  mashSteps_ok [3, 2, 1, 0] (by decide) hs hv

/-- A reverse round of `Spec.Rc2.decryptBlock`: the mixing round `15 - j`,
then the mashing round after the fifth and the eleventh. -/
def revRound (k : Spec.Rc2.Schedule) (r : Spec.Rc2.State) (j : Nat) : Spec.Rc2.State :=
  if j = 4 ∨ j = 10 then Spec.Rc2.reverseMashRound k (Spec.Rc2.reverseMixRound k (15 - j) r)
  else Spec.Rc2.reverseMixRound k (15 - j) r

theorem roundsList_ok {m : Mem} {p : Addr} (js : List Nat) {s : State} (hs : SchedV s m p)
    (hm : s.v m16 = mask16) {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa (js.flatMap fun j =>
        rmixRound (15 - j) ++ (if j = 4 ∨ j = 10 then rmashRound else [])) s = some s' ∧
      Sets s' (fun b => js.foldl (revRound (Spec.Rc2.scheduleAt m p)) (vs b)) ∧
      VKeep s s' := by
  induction js generalizing s vs with
  | nil => exact ⟨s, rfl, hv, ⟨⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl, fun _ _ => rfl, rfl⟩⟩
  | cons j js ih =>
    obtain ⟨s₁, r₁, v₁, k₁⟩ := rmixRound_ok (j := 15 - j) (by omega_using []) hs hm hv
    have step : ∃ s', runBlock isa
        (rmixRound (15 - j) ++ (if j = 4 ∨ j = 10 then rmashRound else [])) s = some s' ∧
        Sets s' (fun b => revRound (Spec.Rc2.scheduleAt m p) (vs b) j) ∧ VKeep s s' := by
      by_cases hc : j = 4 ∨ j = 10
      · obtain ⟨s₂, r₂, v₂, k₂⟩ := rmashRound_ok (hs.keep k₁) v₁
        refine ⟨s₂, ?_, fun h hh i hi b hb => ?_, k₁.trans k₂⟩
        · simp only [hc, ↓reduceIte]; exact runBlock_cat_some r₁ r₂
        · simp only [revRound, hc, ↓reduceIte]; exact v₂ h hh i hi b hb
      · refine ⟨s₁, ?_, fun h hh i hi b hb => ?_, k₁⟩
        · simp only [hc, ↓reduceIte, List.append_nil]; exact r₁
        · simp only [revRound, hc, ↓reduceIte]; exact v₁ h hh i hi b hb
    obtain ⟨s₂, r₂, v₂, k₂⟩ := step
    obtain ⟨s₃, r₃, v₃, k₃⟩ := ih (hs.keep k₂) (k₂.mask.trans hm) v₂
    exact ⟨s₃, by rw [List.flatMap_cons]; exact runBlock_cat_some r₂ r₃, v₃, k₂.trans k₃⟩

theorem revRounds_eq (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    Spec.Rc2.decryptBlock k b =
      Spec.Rc2.encodeBlock ((List.range 16).foldl (revRound k) (Spec.Rc2.decodeBlock b)) := by
  simp only [Spec.Rc2.decryptBlock]
  rfl

theorem rounds_ok {m : Mem} {p : Addr} {s : State} (hs : SchedV s m p)
    (hm : s.v m16 = mask16) {vs : Nat → Spec.Rc2.State} (hv : Sets s vs) :
    ∃ s', runBlock isa rounds s = some s' ∧
      Sets s' (fun b => (List.range 16).foldl (revRound (Spec.Rc2.scheduleAt m p)) (vs b)) ∧
      VKeep s s' :=
  roundsList_ok _ hs hm hv

end VG.Proof.Rc2.AArch64.Vec

end

end

/-! ### `Rc2.AArch64.Vec.Load`, which only this module used -/

section

/-!
# Loading a group of eight blocks

`loadGroup_ok`: the eight blocks at `x1`, loaded into `v0`–`v3` and their
words gathered into the sets by `tbl` (`inIndex`): block `b` of the eight is
`Spec.Rc2.decodeBlock` of the block at `x1 + 8 b`.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

theorem exec_tbl2 (s : State) (d n m : VReg) :
    exec (.vop (.tblN false 2 d n m)) s = some (s.setV d (ofVBytes fun e =>
      if (vbyte (s.v m) e).toNat < 16 * 2 then tableByte s.v n (vbyte (s.v m) e).toNat else 0)) :=
  rfl

/-- A byte of a two-register table loaded from consecutive memory. -/
theorem tableByte_pair {v : VReg → BitVec 128} {n : VReg} {m : Mem} {a : Addr}
    (h0 : v n = m.read a 16) (h1 : v (VReg.succ n) = m.read (a + BitVec.ofNat 64 16) 16)
    {idx : Nat} (hi : idx < 32) : tableByte v n idx = m (a + BitVec.ofNat 64 idx) := by
  rw [tableByte]
  by_cases hl : idx < 16
  · rw [show idx / 16 = 0 by omega_arith, show Nat.repeat VReg.succ 0 n = n from rfl, h0,
      vbyte_read _ _ (by omega_arith), Nat.mod_eq_of_lt hl]
  · rw [show idx / 16 = 1 by omega_arith, show Nat.repeat VReg.succ 1 n = VReg.succ n from rfl, h1,
      vbyte_read _ _ (by omega_arith), Offset.add_add, show 16 + idx % 16 = idx by omega_arith]

theorem inIndex_byte (i : Nat) (hi : i < 4) {e : Nat} (he : e < 16) :
    (vbyte (inIndex i) e).toNat = if e % 4 < 2 then 8 * (e / 4) + 2 * i + e % 4 else 255 := by
  rw [inIndex, vbyte_ofVBytes _ he]
  split
  · rw [BitVec.toNat_ofNat]; omega_arith
  · rfl

/-- The block's word `i`, from its bytes. -/
theorem decode_getD (m : Mem) (a : Addr) {i : Nat} (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m a)).getD i 0 =
      (m (a + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (a + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.decodeBlock, Spec.Rc2.blockAt, Vector.getD, hi, show 2 * i < 8 by omega_arith,
    show 2 * i + 1 < 8 by omega_arith]

/-- Word `i` of set `h`, gathered from the table at `n` (`v0` or `v2`). -/
theorem gather_lane {v : VReg → BitVec 128} {n : VReg} {m : Mem} {a : Addr}
    (h0 : v n = m.read a 16) (h1 : v (VReg.succ n) = m.read (a + BitVec.ofNat 64 16) 16)
    {i : Nat} (hix : v .v4 = inIndex i) (hi : i < 4) {b : Nat} (hb : b < 4) :
    lw (ofVBytes fun e =>
      if (vbyte (v .v4) e).toNat < 16 * 2 then tableByte v n (vbyte (v .v4) e).toNat else 0) b =
      (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m (a + BitVec.ofNat 64 (8 * b)))).getD i 0 := by
  rw [lw_bytes, vbyte_ofVBytes _ (by omega_arith), vbyte_ofVBytes _ (by omega_arith), hix,
    inIndex_byte i hi (by omega_arith), inIndex_byte i hi (by omega_arith), decode_getD _ _ hi,
    Offset.add_add, Offset.add_add]
  simp only [show 4 * b % 4 = 0 by omega_arith, show (4 * b + 1) % 4 = 1 by omega_arith,
    show 4 * b / 4 = b by omega_arith, show (4 * b + 1) / 4 = b by omega_arith, show 0 < 2 by decide,
    show 1 < 2 by decide, ite_true, Nat.add_zero, show 8 * b + 2 * i + 1 = 8 * b + (2 * i + 1) by omega_arith,
    eq_true (show 8 * b + 2 * i < 16 * 2 by omega_arith), eq_true (show 8 * b + (2 * i + 1) < 16 * 2 by omega_arith)]
  rw [tableByte_pair h0 h1 (by omega_arith), tableByte_pair h0 h1 (by omega_arith)]

theorem wreg_inj {h i h' i' : Nat} (hh : h < 2) (hi : i < 4) (hh' : h' < 2) (hi' : i' < 4)
    (e : wreg h i = wreg h' i') : h = h' ∧ i = i' := by
  have := treg_inj (8 + 4 * h + i % 4) (by omega_arith) (8 + 4 * h' + i' % 4) (by omega_arith) e
  omega_arith

/-- The words the gathers of `is` leave: block `b` of the eight at `q`. -/
def Gathered (t : State) (m : Mem) (q : Addr) (i : Nat) : Prop :=
  ∀ h < 2, ∀ b < 4, lw (t.v (wreg h i)) b =
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m (q + BitVec.ofNat 64 (8 * (4 * h + b))))).getD i 0

theorem gathers_ok {m : Mem} {q : Addr} (is : List Nat) (his : ∀ i ∈ is, i < 4) (t : State)
    (r0 : t.v .v0 = m.read q 16) (r1 : t.v .v1 = m.read (q + BitVec.ofNat 64 16) 16)
    (r2 : t.v .v2 = m.read (q + BitVec.ofNat 64 32) 16)
    (r3 : t.v .v3 = m.read (q + BitVec.ofNat 64 48) 16) :
    WP isa (.block (is.flatMap fun i => const128 .v4 (inIndex i) ++
        ([.vop (.tblN false 2 (wreg 0 i) .v0 .v4), .vop (.tblN false 2 (wreg 1 i) .v2 .v4)] :
          List Instr))) t
      fun t' => (∀ i ∈ is, Gathered t' m q i) ∧
        (∀ w, w ≠ .v4 → (∀ i ∈ is, ∀ h < 2, w ≠ wreg h i) → t'.v w = t.v w) ∧
        (∀ g, g ≠ .x6 → g ≠ .x7 → t'.gpr g = t.gpr g) ∧
        t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  induction is generalizing t with
  | nil =>
    exact WP.block_nil ⟨fun _ h => absurd h (by simp), fun _ _ _ => rfl, fun _ _ _ => rfl,
      rfl, rfl, rfl, rfl⟩
  | cons i is ih =>
    have hi := his i (by simp)
    rw [List.flatMap_cons, WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (const128_ok t .v4 (inIndex i)) fun a ⟨a4, av, ag, am, ard, awr, asp⟩ => ?_
    have w0 := wreg_ne 0 i (by decide)
    have w1 := wreg_ne 1 i (by decide)
    have n01 : wreg 1 i ≠ wreg 0 i := fun e => absurd (wreg_inj (by decide) hi (by decide) hi e).1 (by decide)
    let c₁ := a.setV (wreg 0 i) (ofVBytes fun e => if (vbyte (a.v .v4) e).toNat < 16 * 2 then
      tableByte a.v .v0 (vbyte (a.v .v4) e).toNat else 0)
    let c₂ := c₁.setV (wreg 1 i) (ofVBytes fun e => if (vbyte (c₁.v .v4) e).toNat < 16 * 2 then
      tableByte c₁.v .v2 (vbyte (c₁.v .v4) e).toNat else 0)
    refine WP.of_runBlock ⟨c₂, by
      rw [runBlock_cons, exec_tbl2, runStep_some, runBlock_cons, exec_tbl2, runStep_some,
        runBlock_nil], ?_⟩
    have cv : ∀ w, w ≠ wreg 0 i → w ≠ wreg 1 i → c₂.v w = a.v w := fun w h0 h1 => by
      simp only [c₂, c₁, v_setV_of_ne _ _ h0, v_setV_of_ne _ _ h1]
    have keepT : ∀ w, w ≠ .v4 → w ≠ wreg 0 i → w ≠ wreg 1 i → c₂.v w = t.v w := fun w h4 h0 h1 => by
      rw [cv w h0 h1, av w h4]
    have g : Gathered c₂ m q i := by
      intro h hh b hb
      match h, hh with
      | 0, _ =>
        rw [show c₂.v (wreg 0 i) = c₁.v (wreg 0 i) from v_setV_of_ne _ _ n01.symm,
          show c₁.v (wreg 0 i) = _ from v_setV_self _ _ _,
          gather_lane (a := q) (by rw [av _ (by decide), r0])
            (by rw [show VReg.succ .v0 = .v1 from rfl, av _ (by decide), r1]) a4 hi hb,
          show 4 * 0 + b = b by omega_arith]
      | 1, _ =>
        rw [show c₂.v (wreg 1 i) = _ from v_setV_self _ _ _]
        have e4 : c₁.v .v4 = a.v .v4 := v_setV_of_ne _ _ w0.2.2.2.2.1.symm
        rw [gather_lane (a := q + BitVec.ofNat 64 32)
          (by rw [v_setV_of_ne _ _ w0.2.2.1.symm, av _ (by decide), r2])
          (by rw [show VReg.succ .v2 = .v3 from rfl, v_setV_of_ne _ _ w0.2.2.2.1.symm,
            av _ (by decide), r3, Offset.add_add]) (e4.trans a4) hi hb, Offset.add_add,
          show 32 + 8 * b = 8 * (4 * 1 + b) by omega_arith]
    have hr : ∀ r < 4, c₂.v (VReg.v0) = t.v .v0 ∧ c₂.v .v1 = t.v .v1 ∧ c₂.v .v2 = t.v .v2 ∧
        c₂.v .v3 = t.v .v3 := fun _ _ =>
      ⟨keepT _ (by decide) w0.1.symm w1.1.symm, keepT _ (by decide) w0.2.1.symm w1.2.1.symm,
        keepT _ (by decide) w0.2.2.1.symm w1.2.2.1.symm,
        keepT _ (by decide) w0.2.2.2.1.symm w1.2.2.2.1.symm⟩
    obtain ⟨e0, e1, e2, e3⟩ := hr 0 (by decide)
    refine WP.mono (ih (fun i hi => his i (by simp [hi])) c₂ (e0.trans r0) (e1.trans r1)
      (e2.trans r2) (e3.trans r3)) fun t' ⟨tg, tv, tgp, tm, trd, twr, tsp⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i' hi'
      by_cases hin : i' ∈ is
      · exact tg i' hin
      · have he : i' = i := by simpa [hin] using hi'
        subst he
        intro h hh b hb
        rw [tv _ (by have := wreg_ne h i' hh; exact this.2.2.2.2.1)
          (fun i'' hi'' h' hh' e => by
            have := wreg_inj hh hi hh' (his i'' (by simp [hi''])) e
            exact hin (this.2 ▸ hi''))]
        exact g h hh b hb
    · intro w h4 hw
      rw [tv w h4 (fun i' hi' => hw i' (by simp [hi'])),
        keepT w h4 (hw i (by simp) 0 (by decide)) (hw i (by simp) 1 (by decide))]
    · intro r h6 h7
      rw [tgp r h6 h7]
      simp only [c₂, c₁, gpr_setV]
      exact ag r h6 h7
    · rw [tm]; simp only [c₂, c₁, mem_setV]; exact am
    · rw [trd]; simp only [c₂, c₁, rd_setV]; exact ard
    · rw [twr]; simp only [c₂, c₁, wr_setV]; exact awr
    · rw [tsp]; simp only [c₂, c₁, sp_setV]; exact asp

theorem loadGroup_ok (t : State)
    (hr : ∀ c < 4, InRegions (t.rd ++ t.wr) (t.gpr .x1 + BitVec.ofNat 64 (16 * c)) 16) :
    WP isa (.block loadGroup) t fun t' =>
      Sets t' (fun b => Spec.Rc2.decodeBlock
        (Spec.Rc2.blockAt t.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b)))) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → (∀ i < 4, ∀ h < 2, w ≠ wreg h i) →
        t'.v w = t.v w) ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → t'.gpr g = t.gpr g) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  let q := t.gpr .x1
  let s₁ := t.setV .v0 (t.mem.read (q + BitVec.ofNat 64 0) 16)
  let s₂ := s₁.setV .v1 (t.mem.read (q + BitVec.ofNat 64 16) 16)
  let s₃ := s₂.setV .v2 (t.mem.read (q + BitVec.ofNat 64 32) 16)
  let s₄ := s₃.setV .v3 (t.mem.read (q + BitVec.ofNat 64 48) 16)
  rw [loadGroup, WP.block_append_iff]
  have e₁ : exec (.ldrq .v0 .x1 0) t = some s₁ :=
    exec_ldrq' t _ _ 0 ⟨by decide, by decide⟩ (hr 0 (by decide))
  have e₂ : exec (.ldrq .v1 .x1 16) s₁ = some s₂ :=
    exec_ldrq' s₁ _ _ 16 ⟨by decide, by decide⟩ (hr 1 (by decide))
  have e₃ : exec (.ldrq .v2 .x1 32) s₂ = some s₃ :=
    exec_ldrq' s₂ _ _ 32 ⟨by decide, by decide⟩ (hr 2 (by decide))
  have e₄ : exec (.ldrq .v3 .x1 48) s₃ = some s₄ :=
    exec_ldrq' s₃ _ _ 48 ⟨by decide, by decide⟩ (hr 3 (by decide))
  refine WP.of_runBlock ⟨s₄, by
    rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil], ?_⟩
  have z : q + BitVec.ofNat 64 0 = q := BitVec.add_zero q
  refine WP.mono (gathers_ok (m := t.mem) (q := q) (List.range 4) (fun i hi => List.mem_range.mp hi) s₄
    (by simp only [s₄, s₃, s₂, s₁, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1),
      v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3), z])
    (by simp only [s₄, s₃, s₂, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v2),
      v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v3)])
    (by simp only [s₄, s₃, v_setV_self, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3)])
    (by simp only [s₄, v_setV_self])) fun t' ⟨tg, tv, tgp, tm, trd, twr, tsp⟩ =>
      ⟨fun h hh i hi b hb => tg i (List.mem_range.mpr hi) h hh b hb, fun w a0 a1 a2 a3 a4 hw => ?_,
        fun g h6 h7 => (tgp g h6 h7).trans rfl, ?_, ?_, ?_, ?_⟩
  rotate_left
  · rw [tm]; simp only [s₄, s₃, s₂, s₁, mem_setV]
  · rw [trd]; simp only [s₄, s₃, s₂, s₁, rd_setV]
  · rw [twr]; simp only [s₄, s₃, s₂, s₁, wr_setV]
  · rw [tsp]; simp only [s₄, s₃, s₂, s₁, sp_setV]
  rw [tv w a4 (fun i hi h hh => hw i (List.mem_range.mp hi) h hh)]
  simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ a0, v_setV_of_ne _ _ a1, v_setV_of_ne _ _ a2,
    v_setV_of_ne _ _ a3]

end VG.Proof.Rc2.AArch64.Vec

end

end

/-! ### `Rc2.AArch64.Vec.Store`, which only this module used -/

section

/-!
# Storing a group of eight blocks

`scatter_ok`: `tbl` scatters the sets' words back into blocks, blocks `4 h +
2 k` and `4 h + 2 k + 1` into `v(2 h + k)` (`outIndex`). `xorStore_ok`: each
XORed with the ciphertext block before it and stored in place.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec

/-- Byte `j` of a block with words `r` (`Spec.Rc2.encodeBlock`). -/
def encByte (r : Spec.Rc2.State) (j : Nat) : BitVec 8 :=
  ((r.getD (j / 2) 0) >>> (8 * (j % 2))).setWidth 8

theorem encodeBlock_getElem (r : Spec.Rc2.State) {j : Nat} (hj : j < 8) :
    (Spec.Rc2.encodeBlock r)[j] = encByte r j := by
  simp [Spec.Rc2.encodeBlock, encByte]

theorem exec_tbl4 (s : State) (d n m : VReg) :
    exec (.vop (.tblN false 4 d n m)) s = some (s.setV d (ofVBytes fun e =>
      if (vbyte (s.v m) e).toNat < 16 * 4 then tableByte s.v n (vbyte (s.v m) e).toNat else 0)) :=
  rfl

/-- The low two bytes of a lane, from its low 16 bits. -/
theorem vbyte_lw (x : BitVec 128) (b : Nat) {c : Nat} (hc : c < 2) :
    vbyte x (4 * b + c) = ((lw x b) >>> (8 * c)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vbyte, lw, vword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, ht, decide_true, Bool.true_and]
  simp [show 8 * c + t < 16 by omega_arith, show 8 * c + t < 32 by omega_arith,
    show 8 * (4 * b + c) + t = 32 * b + (8 * c + t) by omega_arith]

theorem outIndex_byte (k : Nat) (hk : k < 2) {e : Nat} (he : e < 16) :
    (vbyte (outIndex k) e).toNat = 16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2 := by
  rw [outIndex, vbyte_ofVBytes _ he, BitVec.toNat_ofNat]
  omega_arith

theorem repeat_wreg : ∀ h < 2, ∀ w < 4, Nat.repeat VReg.succ w (wreg h 0) = wreg h w := by
  decide

/-- Byte `e` of `tbl` of set `h` at `outIndex k`: byte `e % 8` of block `4 h + 2 k + e / 8`. -/
theorem scatter_byte {v : VReg → BitVec 128} {h k : Nat} (hh : h < 2) (hk : k < 2)
    (hix : v .v4 = outIndex k) {R : Nat → Spec.Rc2.State}
    (hw : ∀ i < 4, ∀ b < 4, lw (v (wreg h i)) b = (R (4 * h + b)).getD i 0) {e : Nat} (he : e < 16) :
    vbyte (ofVBytes fun e =>
      if (vbyte (v .v4) e).toNat < 16 * 4 then tableByte v (wreg h 0) (vbyte (v .v4) e).toNat else 0) e =
      encByte (R (4 * h + 2 * k + e / 8)) (e % 8) := by
  rw [vbyte_ofVBytes _ he, hix, outIndex_byte k hk he,
    ite_eq_left (show 16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2 < 16 * 4 by omega_arith), tableByte,
    show (16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2) / 16 = e % 8 / 2 by omega_arith,
    show (16 * (e % 8 / 2) + 4 * (2 * k + e / 8) + e % 2) % 16 = 4 * (2 * k + e / 8) + e % 2 by omega_arith,
    repeat_wreg h hh _ (by omega_arith), vbyte_lw _ _ (by omega_arith), hw _ (by omega_arith) _ (by omega_arith), encByte,
    show 4 * h + (2 * k + e / 8) = 4 * h + 2 * k + e / 8 by omega_arith,
    show e % 8 % 2 = e % 2 by omega_arith]

/-- The scattering: the blocks into `v0`–`v3`. -/
def scatterCode : List Instr :=
  const128 .v4 (outIndex 0) ++
  [.vop (.tblN false 4 .v0 (wreg 0 0) .v4), .vop (.tblN false 4 .v2 (wreg 1 0) .v4)] ++
  const128 .v4 (outIndex 1) ++
  [.vop (.tblN false 4 .v1 (wreg 0 0) .v4), .vop (.tblN false 4 .v3 (wreg 1 0) .v4)]

/-- The XOR with the ciphertext blocks, and the stores. -/
def xorCode : List Instr :=
  [.ldr .x .x9 .x1 0, .vop (.ins .d2 .v4 0 .x11), .vop (.ins .d2 .v4 1 .x9),
   .addImm .x .x12 .x1 8, .ldrq .v5 .x12 0,
   .vop (.logic .eor .v0 .v0 .v4), .vop (.logic .eor .v1 .v1 .v5),
   .ldrq .v4 .x12 16, .ldrq .v5 .x12 32,
   .vop (.logic .eor .v2 .v2 .v4), .vop (.logic .eor .v3 .v3 .v5),
   .ldr .x .x11 .x1 56,
   .strq .v0 .x1 0, .strq .v1 .x1 16, .strq .v2 .x1 32, .strq .v3 .x1 48]

theorem storeGroup_eq : storeGroup = scatterCode ++ xorCode := by
  simp only [storeGroup, scatterCode, xorCode, List.append_assoc, List.cons_append, List.nil_append]

/-- Byte `e` of `v0`–`v3` after the scattering: byte `16 c + e` of the eight blocks. -/
def Scattered (v : VReg → BitVec 128) (R : Nat → Spec.Rc2.State) : Prop :=
  ∀ e < 16, vbyte (v .v0) e = encByte (R (e / 8)) (e % 8) ∧
    vbyte (v .v1) e = encByte (R (2 + e / 8)) (e % 8) ∧
    vbyte (v .v2) e = encByte (R (4 + e / 8)) (e % 8) ∧
    vbyte (v .v3) e = encByte (R (6 + e / 8)) (e % 8)

theorem scatter_ok (t : State) {R : Nat → Spec.Rc2.State} (hS : Sets t R) :
    WP isa (.block scatterCode) t fun t' => Scattered t'.v R ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → t'.v w = t.v w) ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → t'.gpr g = t.gpr g) ∧
      t'.mem = t.mem ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  rw [scatterCode, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (const128_ok t .v4 (outIndex 0)) fun a ⟨a4, av, ag, am, ard, awr, asp⟩ => ?_
  let c₁ := a.setV .v0 (ofVBytes fun e => if (vbyte (a.v .v4) e).toNat < 16 * 4 then
    tableByte a.v (wreg 0 0) (vbyte (a.v .v4) e).toNat else 0)
  let c₂ := c₁.setV .v2 (ofVBytes fun e => if (vbyte (c₁.v .v4) e).toNat < 16 * 4 then
    tableByte c₁.v (wreg 1 0) (vbyte (c₁.v .v4) e).toNat else 0)
  refine WP.of_runBlock ⟨c₂, by
    rw [runBlock_cons, exec_tbl4, runStep_some, runBlock_cons, exec_tbl4, runStep_some,
      runBlock_nil], ?_⟩
  refine WP.mono (const128_ok c₂ .v4 (outIndex 1)) fun b ⟨b4, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  let d₁ := b.setV .v1 (ofVBytes fun e => if (vbyte (b.v .v4) e).toNat < 16 * 4 then
    tableByte b.v (wreg 0 0) (vbyte (b.v .v4) e).toNat else 0)
  let d₂ := d₁.setV .v3 (ofVBytes fun e => if (vbyte (d₁.v .v4) e).toNat < 16 * 4 then
    tableByte d₁.v (wreg 1 0) (vbyte (d₁.v .v4) e).toNat else 0)
  refine WP.of_runBlock ⟨d₂, by
    rw [runBlock_cons, exec_tbl4, runStep_some, runBlock_cons, exec_tbl4, runStep_some,
      runBlock_nil], ?_⟩
  -- The sets, kept until the end.
  obtain ws : ∀ h < 2, ∀ i < 4, a.v (wreg h i) = t.v (wreg h i) ∧ c₁.v (wreg h i) = t.v (wreg h i) ∧
      b.v (wreg h i) = t.v (wreg h i) ∧ d₁.v (wreg h i) = t.v (wreg h i) := by
    intro h hh i hi
    obtain wn := wreg_ne h i hh
    obtain e₁ : a.v (wreg h i) = t.v (wreg h i) := av _ wn.2.2.2.2.1
    obtain e₂ : c₁.v (wreg h i) = t.v (wreg h i) := by
      simp only [c₁, v_setV_of_ne _ _ wn.1]; exact e₁
    obtain e₃ : b.v (wreg h i) = t.v (wreg h i) := by
      rw [bv _ wn.2.2.2.2.1]; simp only [c₂, v_setV_of_ne _ _ wn.2.2.1]; exact e₂
    refine ⟨e₁, e₂, e₃, ?_⟩
    simp only [d₁, v_setV_of_ne _ _ wn.2.1]; exact e₃
  obtain hw : ∀ (f : VReg → BitVec 128), (∀ h < 2, ∀ i < 4, f (wreg h i) = t.v (wreg h i)) →
      ∀ h < 2, ∀ i < 4, ∀ b < 4, lw (f (wreg h i)) b = (R (4 * h + b)).getD i 0 :=
    fun f hf h hh i hi b hb => by rw [hf h hh i hi]; exact hS h hh i hi b hb
  obtain c4 : c₁.v .v4 = outIndex 0 := by simp only [c₁, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v0)]; exact a4
  obtain d4 : d₁.v .v4 = outIndex 1 := by simp only [d₁, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v1)]; exact b4
  refine ⟨fun e he => ⟨?_, ?_, ?_, ?_⟩, fun w h0 h1 h2 h3 h4 => ?_, fun g h6 h7 => ?_, ?_, ?_, ?_, ?_⟩
  · have : d₂.v .v0 = c₁.v .v0 := by
      simp only [d₂, d₁, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1)]
      rw [bv _ (by decide)]; simp only [c₂, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v2)]
    rw [this, show c₁.v .v0 = _ from v_setV_self _ _ _,
      scatter_byte (h := 0) (k := 0) (by decide) (by decide) a4
        (hw a.v (fun h hh i hi => (ws h hh i hi).1) 0 (by decide)) he,
      show 4 * 0 + 2 * 0 + e / 8 = e / 8 by omega_arith]
  · rw [show d₂.v .v1 = d₁.v .v1 from v_setV_of_ne _ _ (by decide),
      show d₁.v .v1 = _ from v_setV_self _ _ _,
      scatter_byte (h := 0) (k := 1) (by decide) (by decide) b4
        (hw b.v (fun h hh i hi => (ws h hh i hi).2.2.1) 0 (by decide)) he]
  · have : d₂.v .v2 = c₂.v .v2 := by
      simp only [d₂, d₁, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3),
        v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v1)]
      exact bv _ (by decide)
    rw [this, show c₂.v .v2 = _ from v_setV_self _ _ _,
      scatter_byte (h := 1) (k := 0) (by decide) (by decide) c4
        (hw c₁.v (fun h hh i hi => (ws h hh i hi).2.1) 1 (by decide)) he]
  · rw [show d₂.v .v3 = _ from v_setV_self _ _ _,
      scatter_byte (h := 1) (k := 1) (by decide) (by decide) d4
        (hw d₁.v (fun h hh i hi => (ws h hh i hi).2.2.2) 1 (by decide)) he]
  · simp only [d₂, d₁, v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h1]
    rw [bv _ h4]
    simp only [c₂, c₁, v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h0]
    exact av _ h4
  · simp only [d₂, d₁, gpr_setV]; rw [bg g h6 h7]; simp only [c₂, c₁, gpr_setV]; exact ag g h6 h7
  · simp only [d₂, d₁, mem_setV]; rw [bm]; simp only [c₂, c₁, mem_setV]; exact am
  · simp only [d₂, d₁, rd_setV]; rw [brd]; simp only [c₂, c₁, rd_setV]; exact ard
  · simp only [d₂, d₁, wr_setV]; rw [bwr]; simp only [c₂, c₁, wr_setV]; exact awr
  · simp only [d₂, d₁, sp_setV]; rw [bsp]; simp only [c₂, c₁, sp_setV]; exact asp

theorem exec_addImmx (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp [exec, State.read, h]

theorem exec_strq (s : State) (t : VReg) (n : Reg) (off : Nat) (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.store, h,
    Option.bind_some]

/-- A 16-byte write at offset `d`, read at offset `j`. -/
theorem write16_at (m : Mem) (q : Addr) {d j : Nat} (hd : d + 16 ≤ 64) (hj : j < 64)
    (v : BitVec (8 * 16)) :
    (m.write (q + BitVec.ofNat 64 d) 16 v) (q + BitVec.ofNat 64 j) =
      if d ≤ j ∧ j < d + 16 then vbyte v (j - d) else m (q + BitVec.ofNat 64 j) := by
  simp only [Mem.write, Offset.add_sub_add_left]
  by_cases h : d ≤ j ∧ j < d + 16
  · rw [Offset.ofNat_sub_ofNat h.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    simp only [show j - d < 16 by omega_arith, h, and_self, ite_true]
    rfl
  · have : ¬ (BitVec.ofNat 64 j - BitVec.ofNat 64 d).toNat < 16 := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    simp only [this, h, ite_false]

theorem write4_at (m : Mem) (q : Addr) (V0 V1 V2 V3 : BitVec (8 * 16)) {o : Nat} (ho : o < 64) :
    ((((m.write (q + BitVec.ofNat 64 0) 16 V0).write (q + BitVec.ofNat 64 16) 16 V1).write
      (q + BitVec.ofNat 64 32) 16 V2).write (q + BitVec.ofNat 64 48) 16 V3) (q + BitVec.ofNat 64 o) =
      vbyte (if o < 16 then V0 else if o < 32 then V1 else if o < 48 then V2 else V3) (o % 16) := by
  rw [write16_at _ _ (by decide) ho, write16_at _ _ (by decide) ho, write16_at _ _ (by decide) ho,
    write16_at _ _ (by decide) ho]
  rcases (by omega_arith : o < 16 ∨ (16 ≤ o ∧ o < 32) ∨ (32 ≤ o ∧ o < 48) ∨ 48 ≤ o) with h | h | h | h <;>
    simp (disch := omega_arith) only [↓ite_eq_left, ↓ite_eq_right] <;>
    exact congrArg _ (by omega_arith)

theorem vbyte_ofVDwords (a b : BitVec 64) {e : Nat} (he : e < 16) :
    vbyte (ofVDwords a b) e =
      if e < 8 then a.extractLsb' (8 * e) 8 else b.extractLsb' (8 * (e - 8)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro t ht
  simp only [vbyte, ofVDwords, BitVec.getLsbD_extractLsb', ht, decide_true, Bool.true_and,
    BitVec.getLsbD_append]
  by_cases h : e < 8
  · simp only [h, ite_true, show 8 * e + t < 64 by omega_arith, BitVec.getLsbD_extractLsb', ht,
      decide_true, Bool.true_and]
  · simp only [h, ite_false, show ¬ 8 * e + t < 64 by omega_arith, BitVec.getLsbD_extractLsb', ht,
      decide_true, Bool.true_and, show 8 * e + t - 64 = 8 * (e - 8) + t by omega_arith]

/-- The ciphertext byte before byte `o` of the group: the chaining value's
in the first block. -/
def prevByte (X : BitVec 64) (m : Mem) (q : Addr) (o : Nat) : BitVec 8 :=
  if o < 8 then X.extractLsb' (8 * o) 8 else m (q + BitVec.ofNat 64 (o - 8))

theorem xorStore_ok (t : State) {R : Nat → Spec.Rc2.State} (hsc : Scattered t.v R)
    (hrd : InRegions (t.rd ++ t.wr) (t.gpr .x1) 64) (hwr : InRegions t.wr (t.gpr .x1) 64) :
    ∃ t', runBlock isa xorCode t = some t' ∧
      (∀ o < 64, t'.mem (t.gpr .x1 + BitVec.ofNat 64 o) =
        encByte (R (o / 8)) (o % 8) ^^^ prevByte (t.gpr .x11) t.mem (t.gpr .x1) o) ∧
      Frame [⟨t.gpr .x1, 64⟩] t.mem t'.mem ∧
      t'.gpr .x11 = t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 56) 64 ∧
      (∀ g, g ≠ .x9 → g ≠ .x11 → g ≠ .x12 → t'.gpr g = t.gpr g) ∧
      (∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 → t'.v w = t.v w) ∧
      t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  let q := t.gpr .x1
  let M := t.mem
  let X := t.gpr .x11
  obtain rd : ∀ off, off + 16 ≤ 64 → InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 off) 16 :=
    fun off h => CallLay.inRegions_sub hrd h (by decide)
  let d₁ := t.write .x .x9 (t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 0) 64)
  let d₂ := d₁.setV .v4 (setLane (d₁.v .v4) 64 0 (d₁.gpr .x11))
  let d₃ := d₂.setV .v4 (setLane (d₂.v .v4) 64 1 (d₂.gpr .x9))
  let d₄ := d₃.write .x .x12 (d₃.gpr .x1 + BitVec.ofNat 64 8)
  let d₅ := d₄.setV .v5 (d₄.mem.read (d₄.gpr .x12 + BitVec.ofNat 64 0) 16)
  let d₆ := d₅.setV .v0 (d₅.v .v0 ^^^ d₅.v .v4)
  let d₇ := d₆.setV .v1 (d₆.v .v1 ^^^ d₆.v .v5)
  let d₈ := d₇.setV .v4 (d₇.mem.read (d₇.gpr .x12 + BitVec.ofNat 64 16) 16)
  let d₉ := d₈.setV .v5 (d₈.mem.read (d₈.gpr .x12 + BitVec.ofNat 64 32) 16)
  let d₁₀ := d₉.setV .v2 (d₉.v .v2 ^^^ d₉.v .v4)
  let d₁₁ := d₁₀.setV .v3 (d₁₀.v .v3 ^^^ d₁₀.v .v5)
  let d₁₂ := d₁₁.write .x .x11 (d₁₁.mem.readW (d₁₁.gpr .x1 + BitVec.ofNat 64 56) 64)
  let d₁₃ : State := { d₁₂ with mem := d₁₂.mem.write (d₁₂.gpr .x1 + BitVec.ofNat 64 0) 16 (d₁₂.v .v0) }
  let d₁₄ : State := { d₁₃ with mem := d₁₃.mem.write (d₁₃.gpr .x1 + BitVec.ofNat 64 16) 16 (d₁₃.v .v1) }
  let d₁₅ : State := { d₁₄ with mem := d₁₄.mem.write (d₁₄.gpr .x1 + BitVec.ofNat 64 32) 16 (d₁₄.v .v2) }
  let d₁₆ : State := { d₁₅ with mem := d₁₅.mem.write (d₁₅.gpr .x1 + BitVec.ofNat 64 48) 16 (d₁₅.v .v3) }
  -- The general registers along the way.
  obtain x1₄ : d₄.gpr .x1 = q := by
    simp only [d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x12), gpr_setV,
      gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x9)]; rfl
  obtain x12₄ : d₄.gpr .x12 = q + BitVec.ofNat 64 8 := by
    simp only [d₄, gpr_write_self, BitVec.setWidth_eq]
    rw [show d₃.gpr .x1 = d₄.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₄]
  obtain x1₁₂ : d₁₂.gpr .x1 = q := by
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x11),
      gpr_setV]; exact x1₄
  obtain x12₇ : d₇.gpr .x12 = q + BitVec.ofNat 64 8 := by
    simp only [d₇, d₆, d₅, gpr_setV]; exact x12₄
  obtain e₁ : exec (.ldr .x .x9 .x1 0) t = some d₁ :=
    exec_ldr_x ⟨by decide, by decide⟩ (CallLay.inRegions_sub hrd (by decide : 0 + 8 ≤ 64) (by decide))
  obtain e₄ : exec (.addImm .x .x12 .x1 8) d₃ = some d₄ := exec_addImmx _ _ _ (by decide)
  obtain e₅ : exec (.ldrq .v5 .x12 0) d₄ = some d₅ := exec_ldrq' d₄ _ _ 0 ⟨by decide, by decide⟩
    (by rw [x12₄, Offset.add_add]; exact rd _ (by decide))
  obtain e₈ : exec (.ldrq .v4 .x12 16) d₇ = some d₈ := exec_ldrq' d₇ _ _ 16 ⟨by decide, by decide⟩
    (by rw [x12₇, Offset.add_add]; exact rd _ (by decide))
  obtain e₉ : exec (.ldrq .v5 .x12 32) d₈ = some d₉ := exec_ldrq' d₈ _ _ 32 ⟨by decide, by decide⟩
    (by rw [show d₈.gpr .x12 = d₇.gpr .x12 from rfl, x12₇, Offset.add_add]; exact rd _ (by decide))
  obtain e₁₂ : exec (.ldr .x .x11 .x1 56) d₁₁ = some d₁₂ := exec_ldr_x ⟨by decide, by decide⟩
    (by
      rw [show d₁₁.gpr .x1 = d₁₂.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₁₂]
      exact CallLay.inRegions_sub hrd (by decide : 56 + 8 ≤ 64) (by decide))
  obtain wr : ∀ off, off + 16 ≤ 64 → InRegions d₁₂.wr (d₁₂.gpr .x1 + BitVec.ofNat 64 off) 16 :=
    fun off h => by rw [x1₁₂]; exact CallLay.inRegions_sub hwr h (by decide)
  obtain e₁₃ : exec (.strq .v0 .x1 0) d₁₂ = some d₁₃ := exec_strq _ _ _ 0 ⟨by decide, by decide⟩ (wr 0 (by decide))
  obtain e₁₄ : exec (.strq .v1 .x1 16) d₁₃ = some d₁₄ := exec_strq _ _ _ 16 ⟨by decide, by decide⟩ (wr 16 (by decide))
  obtain e₁₅ : exec (.strq .v2 .x1 32) d₁₄ = some d₁₅ := exec_strq _ _ _ 32 ⟨by decide, by decide⟩ (wr 32 (by decide))
  obtain e₁₆ : exec (.strq .v3 .x1 48) d₁₅ = some d₁₆ := exec_strq _ _ _ 48 ⟨by decide, by decide⟩ (wr 48 (by decide))
  obtain run : runBlock isa xorCode t = some d₁₆ := by
    rw [xorCode, runBlock_cons, e₁, runStep_some, runBlock_cons, exec_insd _ _ _ (by decide),
      runStep_some, runBlock_cons, exec_insd _ _ _ (by decide), runStep_some, runBlock_cons, e₄,
      runStep_some, runBlock_cons, e₅, runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, exec_eorv, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_cons, e₉,
      runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_cons, exec_eorv, runStep_some,
      runBlock_cons, e₁₂, runStep_some, runBlock_cons, e₁₃, runStep_some, runBlock_cons, e₁₄,
      runStep_some, runBlock_cons, e₁₅, runStep_some, runBlock_cons, e₁₆, runStep_some, runBlock_nil]
  -- The values stored.
  obtain V0 : d₁₂.v .v0 = t.v .v0 ^^^ ofVDwords X (M.readW (q + BitVec.ofNat 64 0) 64) := by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq,
      setLane_two] <;> rfl
  obtain V1 : d₁₂.v .v1 = t.v .v1 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 0) 16 := by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  obtain V2 : d₁₂.v .v2 = t.v .v2 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 16) 16 := by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  obtain V3 : d₁₂.v .v3 = t.v .v3 ^^^ M.read (q + BitVec.ofNat 64 8 + BitVec.ofNat 64 32) 16 := by
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_self, v_setV_of_ne, gpr_setV, gpr_write_self, gpr_write_of_ne, BitVec.setWidth_eq] <;> rfl
  obtain mem : d₁₆.mem = (((M.write (q + BitVec.ofNat 64 0) 16 (d₁₂.v .v0)).write
      (q + BitVec.ofNat 64 16) 16 (d₁₂.v .v1)).write (q + BitVec.ofNat 64 32) 16 (d₁₂.v .v2)).write
      (q + BitVec.ofNat 64 48) 16 (d₁₂.v .v3) := by
    simp only [d₁₆, d₁₅, d₁₄, d₁₃, x1₁₂]
    rfl
  refine ⟨d₁₆, run, fun o ho => ?_, ?_, ?_, fun g h9 h11 h12 => ?_, fun w h0 h1 h2 h3 h4 h5 => ?_,
    rfl, rfl, rfl⟩
  · rw [mem, write4_at _ _ _ _ _ _ ho, prevByte]
    rcases (by omega_arith : o < 16 ∨ (16 ≤ o ∧ o < 32) ∨ (32 ≤ o ∧ o < 48) ∨ 48 ≤ o) with h | h | h | h <;>
      simp (disch := omega_arith) only [↓ite_eq_left, ↓ite_eq_right]
    · rw [V0, vbyte_xor, (hsc _ (by omega_arith)).1, vbyte_ofVDwords _ _ (by omega_arith),
        show o % 16 = o by omega_arith]
      by_cases h8 : o < 8
      · simp only [h8, ite_true] <;> rfl
      · simp only [h8, ite_false]
        rw [read64_byte _ _ _ (by omega_arith), Offset.add_add, show 0 + (o - 8) = o - 8 by omega_arith]
    · rw [V1, vbyte_xor, (hsc _ (by omega_arith)).2.1, vbyte_read _ _ (by omega_arith), Offset.add_add,
        Offset.add_add, show o / 8 = 2 + o % 16 / 8 by omega_arith, show o % 8 = o % 16 % 8 by omega_arith,
        show 8 + (0 + o % 16) = o - 8 by omega_arith]
    · rw [V2, vbyte_xor, (hsc _ (by omega_arith)).2.2.1, vbyte_read _ _ (by omega_arith), Offset.add_add,
        Offset.add_add, show o / 8 = 4 + o % 16 / 8 by omega_arith, show o % 8 = o % 16 % 8 by omega_arith,
        show 8 + (16 + o % 16) = o - 8 by omega_arith]
    · rw [V3, vbyte_xor, (hsc _ (by omega_arith)).2.2.2, vbyte_read _ _ (by omega_arith), Offset.add_add,
        Offset.add_add, show o / 8 = 6 + o % 16 / 8 by omega_arith, show o % 8 = o % 16 % 8 by omega_arith,
        show 8 + (32 + o % 16) = o - 8 by omega_arith]
  · rw [mem]
    obtain c : ∀ d, d + 16 ≤ 64 → (⟨q, 64⟩ : Region).Contains (q + BitVec.ofNat 64 d) 16 :=
      fun d h => Offset.contains_base q h (by omega_arith)
    exact (((((Frame.refl _ M).write (List.mem_singleton_self _) _ (c 0 (by decide))).write
      (List.mem_singleton_self _) _ (c 16 (by decide))).write (List.mem_singleton_self _) _
      (c 32 (by decide))).write (List.mem_singleton_self _) _ (c 48 (by decide)))
  · show d₁₂.gpr .x11 = _
    simp only [d₁₂, gpr_write_self, BitVec.setWidth_eq]
    rw [show d₁₁.gpr .x1 = d₁₂.gpr .x1 from (gpr_write_of_ne _ _ _ (by decide)).symm, x1₁₂]
    rfl
  · show d₁₂.gpr g = t.gpr g
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, gpr_write_of_ne _ _ _ h11, gpr_setV,
      gpr_write_of_ne _ _ _ h12, gpr_write_of_ne _ _ _ h9]
  · show d₁₂.v w = t.v w
    simp only [d₁₂, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, v_write, v_setV_of_ne _ _ h0,
      v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h2, v_setV_of_ne _ _ h3, v_setV_of_ne _ _ h4,
      v_setV_of_ne _ _ h5]

end VG.Proof.Rc2.AArch64.Vec

end

end

/-!
# One group of eight blocks

`group_ok`: the eight blocks at `x1` decrypted, each XORed with the
ciphertext block before it (the chaining value in `x11` before the first),
in place; the last ciphertext block into `x11`, and `x1` and `x10` advanced.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec VG.Proof.Rc2

/-- The block before block `b` of the group at `q`: the chaining value `X` before the first. -/
def prevBlock (X : BitVec 64) (m : Mem) (q : Addr) (b : Nat) : Spec.Rc2.Block :=
  if b = 0 then wordBlock X else Spec.Rc2.blockAt m (q + BitVec.ofNat 64 (8 * (b - 1)))

structure GroupPost (m : Mem) (p : Addr) (t t' : State) : Prop where
  data : ∀ b < 8, Spec.Rc2.blockAt t'.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b)) =
    Proof.Rc2.xorBlock (Spec.Rc2.decryptBlock (Spec.Rc2.scheduleAt m p)
        (Spec.Rc2.blockAt t.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b))))
      (prevBlock (t.gpr .x11) t.mem (t.gpr .x1) b)
  frame : Frame [⟨t.gpr .x1, 64⟩] t.mem t'.mem
  chain : t'.gpr .x11 = t.mem.readW (t.gpr .x1 + BitVec.ofNat 64 56) 64
  ptr : t'.gpr .x1 = t.gpr .x1 + BitVec.ofNat 64 64
  count : t'.gpr .x10 = t.gpr .x10 - BitVec.ofNat 64 1
  reg : ∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
    t'.gpr g = t.gpr g
  sched : SchedV t' m p
  mask : t'.v m16 = mask16
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp

theorem exec_subImmx (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp [exec, State.read, h]

/-- The output byte, as a block. -/
theorem out_block {m m' : Mem} {q : Addr} {X : BitVec 64} {R : Nat → Spec.Rc2.State}
    (h : ∀ o < 64, m' (q + BitVec.ofNat 64 o) = encByte (R (o / 8)) (o % 8) ^^^ prevByte X m q o)
    {b : Nat} (hb : b < 8) :
    Spec.Rc2.blockAt m' (q + BitVec.ofNat 64 (8 * b)) =
      Proof.Rc2.xorBlock (Spec.Rc2.encodeBlock (R b)) (prevBlock X m q b) := by
  apply Vector.ext
  intro j hj
  simp only [Spec.Rc2.blockAt, Proof.Rc2.xorBlock, Vector.getElem_ofFn, Offset.add_add, Fin.getElem_fin]
  rw [h _ (by omega_using [hb, hj]), encodeBlock_getElem _ hj, show (8 * b + j) / 8 = b by omega_using [hj],
    show (8 * b + j) % 8 = j by omega_using [hj], prevByte, prevBlock]
  by_cases h0 : b = 0
  · subst h0
    simp only [ite_true, wordBlock, Vector.getElem_ofFn, show 8 * 0 + j = j by omega_using [], hj]
  · simp only [show ¬ 8 * b + j < 8 by omega_using [h0], h0, ite_false, Spec.Rc2.blockAt, Vector.getElem_ofFn,
      Offset.add_add, show 8 * (b - 1) + j = 8 * b + j - 8 by omega_using [h0]]

theorem group_ok {m : Mem} {p : Addr} (t : State) (hs : SchedV t m p) (hm : t.v m16 = mask16)
    (hrd : InRegions (t.rd ++ t.wr) (t.gpr .x1) 64) (hwr : InRegions t.wr (t.gpr .x1) 64) :
    WP isa (.block group) t (GroupPost m p t) := by
  rw [group, storeGroup_eq]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadGroup_ok t fun c hc => CallLay.inRegions_sub hrd (by omega_using [hc]) (by decide))
    fun a ⟨aS, av, ag, am, ard, awr, asp⟩ => ?_
  have aw : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 →
      (∀ i < 4, ∀ h < 2, w ≠ wreg h i) → a.v w = t.v w := fun w a0 a1 a2 a3 a4 _ hw =>
    av w a0 a1 a2 a3 a4 hw
  have hsA : SchedV a m p := fun r hr => by
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega_using [hr])
    rw [aw _ a0 a1 a2 a3 a4 a5 fun i hi h hh => ((regs_fixed h i hh hi).2.2.2.2.2.2.2.2 r hr).1]
    exact hs r hr
  have hmA : a.v m16 = mask16 := by
    rw [aw _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      fun i hi h hh => (regs_fixed h i hh hi).2.1]
    exact hm
  let R : Nat → Spec.Rc2.State := fun b => (List.range 16).foldl (revRound (Spec.Rc2.scheduleAt m p))
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt t.mem (t.gpr .x1 + BitVec.ofNat 64 (8 * b))))
  obtain ⟨b, runb, bS, bk⟩ := rounds_ok hsA hmA aS
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b, runb, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (scatter_ok b (R := R) bS) fun c ⟨cS, cv, cg, cm, crd, cwr, csp⟩ => ?_
  have cx : ∀ g, g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → c.gpr g = t.gpr g := fun g h6 h7 h9 => by
    rw [cg g h6 h7, bk.keep.reg g (by simp [h6, h9]), ag g h6 h7]
  have q₁ : c.gpr .x1 = t.gpr .x1 := cx _ (by decide) (by decide) (by decide)
  have mc : c.mem = t.mem := by rw [cm, bk.keep.mem, am]
  have rdc : c.rd = t.rd := by rw [crd, bk.keep.rd, ard]
  have wrc : c.wr = t.wr := by rw [cwr, bk.keep.wr, awr]
  obtain ⟨d, rund, dmem, dframe, d11, dg, dv, drd, dwr, dsp⟩ := xorStore_ok c (R := R) cS
    (by rw [rdc, wrc, q₁]; exact hrd) (by rw [wrc, q₁]; exact hwr)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨d, rund, ?_⟩
  let e := d.write .x .x1 (d.gpr .x1 + BitVec.ofNat 64 64)
  let f := e.write .x .x10 (e.gpr .x10 - BitVec.ofNat 64 1)
  refine WP.of_runBlock ⟨f, by
    rw [runBlock_cons, exec_addImmx _ _ _ (by decide), runStep_some, runBlock_cons,
      exec_subImmx _ _ _ (by decide), runStep_some, runBlock_nil], ?_⟩
  have fg : ∀ g, g ≠ .x1 → g ≠ .x10 → f.gpr g = d.gpr g := fun g h1 h10 => by
    simp only [f, e, gpr_write_of_ne _ _ _ h10, gpr_write_of_ne _ _ _ h1]
  have x11 : c.gpr .x11 = t.gpr .x11 := cx _ (by decide) (by decide) (by decide)
  refine ⟨fun b hb => ?_, ?_, ?_, ?_, ?_, fun g h1 h6 h7 h9 h10 h11 h12 => ?_, fun r hr => ?_, ?_,
    by simp only [f, e, rd_write]; rw [drd, rdc], by simp only [f, e, wr_write]; rw [dwr, wrc],
    by simp only [f, e, sp_write]; rw [dsp, csp, bk.sp, asp]⟩
  · have := out_block (R := R) dmem hb
    rw [q₁, x11, mc] at this
    simp only [f, e, mem_write]
    rw [this, revRounds_eq]
  · simp only [f, e, mem_write]; rw [← mc, ← q₁]; exact dframe
  · rw [fg _ (by decide) (by decide), d11, mc, q₁]
  · simp only [f, e, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x1 = .x10), gpr_write_self,
      BitVec.setWidth_eq]
    rw [dg _ (by decide) (by decide) (by decide), q₁]
  · simp only [f, gpr_write_self, BitVec.setWidth_eq, e, gpr_write_of_ne _ _ _ (by decide : ¬Reg.x10 = .x1)]
    rw [dg _ (by decide) (by decide) (by decide), cx _ (by decide) (by decide) (by decide)]
  · rw [fg g h1 h10, dg g h9 h11 h12, cx g h6 h7 h9]
  · simp only [f, e, v_write]
    obtain ⟨a0, a1, a2, a3, a4, a5, -, -⟩ := treg_ne8 r (by omega_using [hr])
    rw [dv _ a0 a1 a2 a3 a4 a5, cv _ a0 a1 a2 a3 a4, bk.sched r hr]
    exact hsA r hr
  · simp only [f, e, v_write]
    rw [dv _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      cv _ (by decide) (by decide) (by decide) (by decide) (by decide), bk.mask]
    exact hmA

end VG.Proof.Rc2.AArch64.Vec

end

end

/-!
# The loop over groups

`loopV_ok`: `j` groups of eight blocks at `x1`, decrypted in CBC mode from the
chaining value in `x11`, which is left the last ciphertext block.
-/

@[expose] public section

namespace VG.Proof.Rc2.AArch64.Vec

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64
  VG.Impl.Rc2.AArch64.Vec VG.Proof.Rc2

/-- A group, as CBC on its eight blocks. -/
theorem GroupPost.cbc {m : Mem} {p : Addr} {t t' : State} (h : GroupPost m p t t') :
    Spec.Rc2.blocksAt t'.mem (t.gpr .x1) 8 = (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m p) .decrypt
      (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) 8)).1 ∧
    wordBlock (t'.gpr .x11) = (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m p) .decrypt
      (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) 8)).2 := by
  rw [cbc_decrypt]
  constructor
  · apply List.ext_getElem (by simp [blocksAt_length])
    intro i h₁ h₂
    have hi : i < 8 := by simpa [blocksAt_length] using h₁
    rw [List.getElem_zipWith, blocksAt_getElem, blocksAt_getElem, h.data i hi, prevBlock]
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.getElem_cons_succ, blocksAt_getElem, Nat.add_sub_cancel, Nat.add_one_ne_zero,
        ite_false]
  · rw [h.chain, ← blockAt_read64, List.getLast_eq_getElem]
    simp only [List.length_cons, blocksAt_length, Nat.add_sub_cancel, List.getElem_cons_succ,
      blocksAt_getElem]

structure LoopVPost (m : Mem) (p : Addr) (t : State) (j : Nat) (t' : State) : Prop where
  ptr : t'.gpr .x1 = t.gpr .x1 + BitVec.ofNat 64 (64 * j)
  count : t'.gpr .x10 = 0
  reg : ∀ g, g ≠ .x1 → g ≠ .x6 → g ≠ .x7 → g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 →
    t'.gpr g = t.gpr g
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  sp : t'.sp = t.sp
  frame : Frame [⟨t.gpr .x1, 64 * j⟩] t.mem t'.mem
  data : Spec.Rc2.blocksAt t'.mem (t.gpr .x1) (8 * j) = (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m p)
    .decrypt (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) (8 * j))).1
  chain : wordBlock (t'.gpr .x11) = (Proof.Rc2.cbcBlocks (Spec.Rc2.scheduleAt m p)
    .decrypt (wordBlock (t.gpr .x11)) (Spec.Rc2.blocksAt t.mem (t.gpr .x1) (8 * j))).2

theorem ofNat_ne_zero {a : Nat} (h : 0 < a) (h' : a < 2 ^ 64) : BitVec.ofNat 64 a ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h', show (0 : BitVec 64).toNat = 0 from rfl] at this
  omega_using [h, this]

theorem loopV_ok (m : Mem) (p : Addr) (j : Nat) :
    ∀ t : State, 1 ≤ j → 64 * j < 2 ^ 64 → SchedV t m p → t.v m16 = mask16 →
      t.gpr .x10 = BitVec.ofNat 64 j →
      InRegions (t.rd ++ t.wr) (t.gpr .x1) (64 * j) → InRegions t.wr (t.gpr .x1) (64 * j) →
      WP isa (.loop (.block group) (.nonzero .x .x10)) t (LoopVPost m p t j) := by
  induction j with
  | zero => intro t h; omega
  | succ j ih =>
    intro t _ bound hs hm count hrd hwr
    have z : t.gpr .x1 + BitVec.ofNat 64 0 = t.gpr .x1 := BitVec.add_zero _
    obtain ⟨t₀, s₁, exec₁, h₁⟩ := group_ok (m := m) (p := p) t hs hm
      (by have := CallLay.inRegions_sub hrd (by omega_using [] : 0 + 64 ≤ 64 * (j + 1)) (by omega_using [bound])
          rwa [z] at this)
      (by have := CallLay.inRegions_sub hwr (by omega_using [] : 0 + 64 ≤ 64 * (j + 1)) (by omega_using [bound])
          rwa [z] at this)
    have c₁ : s₁.gpr .x10 = BitVec.ofNat 64 j := by
      rw [h₁.count, count, Offset.ofNat_sub_ofNat (by omega_using [])]; rfl
    have g8 := h₁.cbc
    by_cases hz : j = 0
    · subst hz
      refine ⟨_, s₁, Exec.loopExit exec₁ (by simp [eval, State.read, c₁]), ?_⟩
      refine ⟨by rw [h₁.ptr], c₁, fun g a b c d e f i => h₁.reg g a b c d e f i, h₁.rd, h₁.wr,
        h₁.sp, h₁.frame, g8.1, g8.2⟩
    · obtain ⟨t₂, s₂, exec₂, h₂⟩ := ih s₁ (by omega_using [hz]) (by omega_using [bound]) h₁.sched h₁.mask c₁
        (by rw [h₁.rd, h₁.wr, h₁.ptr]; exact CallLay.inRegions_sub hrd (by omega_using []) (by omega_using [bound]))
        (by rw [h₁.wr, h₁.ptr]; exact CallLay.inRegions_sub hwr (by omega_using []) (by omega_using [bound]))
      refine ⟨_, s₂, Exec.loopNext exec₁ (by
        simp [eval, State.read, c₁]; exact ofNat_ne_zero (by omega_using [hz]) (by omega_using [bound])) exec₂, ?_⟩
      let q := t.gpr .x1
      have q₁ : s₁.gpr .x1 = q + BitVec.ofNat 64 64 := h₁.ptr
      -- The first group's blocks, left by the rest; the rest's, by the first.
      have keepFirst : Spec.Rc2.blocksAt s₂.mem q 8 = Spec.Rc2.blocksAt s₁.mem q 8 :=
        blocksAt_frame h₂.frame q 8 (by
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          rw [q₁]
          exact Offset.base_disjoint q (by omega_using []) (by omega_using [bound]))
      have keepRest : Spec.Rc2.blocksAt s₁.mem (q + BitVec.ofNat 64 64) (8 * j) =
          Spec.Rc2.blocksAt t.mem (q + BitVec.ofNat 64 64) (8 * j) :=
        blocksAt_frame h₁.frame _ _ (by
          intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact Offset.disjoint_base q (by omega_using []) (by omega_using [bound]))
      have split : ∀ mm : Mem, Spec.Rc2.blocksAt mm q (8 * (j + 1)) =
          Spec.Rc2.blocksAt mm q 8 ++ Spec.Rc2.blocksAt mm (q + BitVec.ofNat 64 64) (8 * j) :=
        fun mm => by rw [show 8 * (j + 1) = 8 + 8 * j by omega_using [], blocksAt_add]
      have data₂ := h₂.data
      have chain₂ := h₂.chain
      rw [q₁, keepRest, g8.2] at data₂ chain₂
      refine ⟨?_, h₂.count, fun g a b c d e f i => (h₂.reg g a b c d e f i).trans
        (h₁.reg g a b c d e f i), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, ?_, ?_, ?_⟩
      · rw [h₂.ptr, q₁, Offset.add_add, show 64 + 64 * j = 64 * (j + 1) by omega_using []]
      · refine (h₁.frame.sub ?_).trans (h₂.frame.sub ?_)
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_using [])⟩
        · intro r hr
          simp only [List.mem_singleton] at hr
          subst hr
          rw [q₁]
          exact ⟨_, List.mem_singleton_self _, Offset.sub_base q (by omega_using [])⟩
      · rw [split, split, keepFirst, g8.1, cbc_append, data₂]
      · rw [chain₂, split, cbc_append]

end VG.Proof.Rc2.AArch64.Vec
