import VerifiedGarbage.Proof.Rc2.AArch64.Vec.Rounds

/-!
# Loading a group of eight blocks

`loadGroup_ok`: the eight blocks at `x1`, loaded into `v0`–`v3` and their
words gathered into the sets by `tbl` (`inIndex`): block `b` of the eight is
`Spec.Rc2.decodeBlock` of the block at `x1 + 8 b`.
-/

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
  · rw [show idx / 16 = 0 by omega, show Nat.repeat VReg.succ 0 n = n from rfl, h0,
      vbyte_read _ _ (by omega), Nat.mod_eq_of_lt hl]
  · rw [show idx / 16 = 1 by omega, show Nat.repeat VReg.succ 1 n = VReg.succ n from rfl, h1,
      vbyte_read _ _ (by omega), Offset.add_add, show 16 + idx % 16 = idx by omega]

theorem inIndex_byte (i : Nat) (hi : i < 4) {e : Nat} (he : e < 16) :
    (vbyte (inIndex i) e).toNat = if e % 4 < 2 then 8 * (e / 4) + 2 * i + e % 4 else 255 := by
  rw [inIndex, vbyte_ofVBytes _ he]
  split
  · rw [BitVec.toNat_ofNat]; omega
  · rfl

/-- The block's word `i`, from its bytes. -/
theorem decode_getD (m : Mem) (a : Addr) {i : Nat} (hi : i < 4) :
    (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m a)).getD i 0 =
      (m (a + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (a + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.decodeBlock, Spec.Rc2.blockAt, Vector.getD, hi, show 2 * i < 8 by omega,
    show 2 * i + 1 < 8 by omega]

/-- Word `i` of set `h`, gathered from the table at `n` (`v0` or `v2`). -/
theorem gather_lane {v : VReg → BitVec 128} {n : VReg} {m : Mem} {a : Addr}
    (h0 : v n = m.read a 16) (h1 : v (VReg.succ n) = m.read (a + BitVec.ofNat 64 16) 16)
    {i : Nat} (hix : v .v4 = inIndex i) (hi : i < 4) {b : Nat} (hb : b < 4) :
    lw (ofVBytes fun e =>
      if (vbyte (v .v4) e).toNat < 16 * 2 then tableByte v n (vbyte (v .v4) e).toNat else 0) b =
      (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt m (a + BitVec.ofNat 64 (8 * b)))).getD i 0 := by
  rw [lw_bytes, vbyte_ofVBytes _ (by omega), vbyte_ofVBytes _ (by omega), hix,
    inIndex_byte i hi (by omega), inIndex_byte i hi (by omega), decode_getD _ _ hi,
    Offset.add_add, Offset.add_add]
  simp only [show 4 * b % 4 = 0 by omega, show (4 * b + 1) % 4 = 1 by omega,
    show 4 * b / 4 = b by omega, show (4 * b + 1) / 4 = b by omega, show 0 < 2 by decide,
    show 1 < 2 by decide, ite_true, Nat.add_zero, show 8 * b + 2 * i + 1 = 8 * b + (2 * i + 1) by omega,
    eq_true (show 8 * b + 2 * i < 16 * 2 by omega), eq_true (show 8 * b + (2 * i + 1) < 16 * 2 by omega)]
  rw [tableByte_pair h0 h1 (by omega), tableByte_pair h0 h1 (by omega)]

theorem wreg_inj {h i h' i' : Nat} (hh : h < 2) (hi : i < 4) (hh' : h' < 2) (hi' : i' < 4)
    (e : wreg h i = wreg h' i') : h = h' ∧ i = i' := by
  have := treg_inj (8 + 4 * h + i % 4) (by omega) (8 + 4 * h' + i' % 4) (by omega) e
  omega

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
          show 4 * 0 + b = b by omega]
      | 1, _ =>
        rw [show c₂.v (wreg 1 i) = _ from v_setV_self _ _ _]
        have e4 : c₁.v .v4 = a.v .v4 := v_setV_of_ne _ _ w0.2.2.2.2.1.symm
        rw [gather_lane (a := q + BitVec.ofNat 64 32)
          (by rw [v_setV_of_ne _ _ w0.2.2.1.symm, av _ (by decide), r2])
          (by rw [show VReg.succ .v2 = .v3 from rfl, v_setV_of_ne _ _ w0.2.2.2.1.symm,
            av _ (by decide), r3, Offset.add_add]) (e4.trans a4) hi hb, Offset.add_add,
          show 32 + 8 * b = 8 * (4 * 1 + b) by omega]
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
        fun g h6 h7 => (tgp g h6 h7).trans rfl, tm, trd, twr, tsp⟩
  rw [tv w a4 (fun i hi h hh => hw i (List.mem_range.mp hi) h hh)]
  simp only [s₄, s₃, s₂, s₁, v_setV_of_ne _ _ a0, v_setV_of_ne _ _ a1, v_setV_of_ne _ _ a2,
    v_setV_of_ne _ _ a3]

end VG.Proof.Rc2.AArch64.Vec
