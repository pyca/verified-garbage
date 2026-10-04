import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Lanes

/-!
# Poly1305 on AArch64 in AdvSIMD: rows of products

Untrusted: everything here is checked by Lean. A row multiplies one operand
vector `iV i` by five multipliers `M k`, into the products `dV k`, with
`umull` (a fresh row) or `umlal`, on words 0–1 or (`hi`) 2–3.
-/

namespace VG.Proof.Poly1305.AArch64.Vector

open VG VG.AArch64
open VG.Impl.Poly1305.AArch64.Vector
open VG.Proof.Curve448.AArch64.Neon (umull_lane umlal_lane)

/-- The first word of a product's lanes. -/
abbrev hp (hi : Bool) : Nat := if hi then 2 else 0

/-- The term of lane `e`: word `hp hi + e` of the operand times that of the multiplier. -/
abbrev term (s : State) (hi : Bool) (i : Nat) (M : Nat → VReg) (k e : Nat) : Nat :=
  wd (s.v (iV i)) (hp hi + e) * wd (s.v (M k)) (hp hi + e)

theorem dV_ne_iV : ∀ k < 5, ∀ i < 5, dV k ≠ iV i := by decide
theorem dV_ne : ∀ k < 5, ∀ j < 5, k ≠ j → dV k ≠ dV j := by decide

/-- What a row keeps. -/
structure MKeep (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  v : ∀ r, (∀ k < 5, r ≠ dV k) → t.v r = s.v r

theorem mac_exec (s : State) (hi fresh : Bool) (i : Nat) (M : Nat → VReg) (k : Nat) :
    ∃ x, isa.exec (mac hi fresh i M k) s = some (s.setV (dV k) x) ∧ ∀ e < 2,
      ln x e = ((if fresh then 0 else ln (s.v (dV k)) e) + term s hi i M k e) % 2 ^ 64 := by
  cases fresh
  · refine ⟨_, exec_vo rfl, fun e he => ?_⟩
    simp only [ln, term, wd, Bool.false_eq_true, ite_false]
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · rw [vdword_ofVDwords_0]; exact umlal_lane _ _ _ _ _
    · rw [vdword_ofVDwords_1]; exact umlal_lane _ _ _ _ _
  · refine ⟨_, exec_vo rfl, fun e he => ?_⟩
    simp only [ln, term, wd, ite_true, Nat.zero_add]
    have hlt : ∀ a b : BitVec 32, a.toNat * b.toNat < 2 ^ 64 := fun a b =>
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' a.isLt b.isLt) (by decide)
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · rw [vdword_ofVDwords_0, umull_lane, Nat.mod_eq_of_lt (hlt _ _)]
    · rw [vdword_ofVDwords_1, umull_lane, Nat.mod_eq_of_lt (hlt _ _)]

/-- A row over the targets `ks`. -/
theorem row_aux (hi fresh : Bool) (i : Nat) (hi5 : i < 5) (M : Nat → VReg)
    (hM : ∀ k < 5, ∀ j < 5, M k ≠ dV j) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k < 5) → ks.Nodup → ∀ s : State,
      WP isa (.block (ks.map (mac hi fresh i M))) s fun t =>
        (∀ k ∈ ks, ∀ e < 2, ln (t.v (dV k)) e =
          ((if fresh then 0 else ln (s.v (dV k)) e) + term s hi i M k e) % 2 ^ 64) ∧
        (∀ k < 5, k ∉ ks → t.v (dV k) = s.v (dV k)) ∧ MKeep s t := by
  intro ks
  induction ks with
  | nil =>
    intro _ _ s
    exact WP.block_nil_iff.mpr ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ _ => rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩
  | cons k ks ih =>
    intro hks hnd s
    have hk : k < 5 := hks k List.mem_cons_self
    have hks' : ∀ j ∈ ks, j < 5 := fun j hj => hks j (List.mem_cons_of_mem _ hj)
    obtain ⟨hnk, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨x, hx, hl⟩ := mac_exec s hi fresh i M k
    refine WP.block_cons_iff.mpr ⟨_, hx, ?_⟩
    refine WP.mono (ih hks' hnd' _) fun t ⟨hr, hn, hkp⟩ => ⟨?_, ?_, ?_⟩
    · -- operands are unchanged by the write of `dV k`
      have hopnd : (s.setV (dV k) x).v (iV i) = s.v (iV i) :=
        RegUpd.v_setV_of_ne _ _ (dV_ne_iV k hk i hi5).symm
      have hmul : ∀ j < 5, (s.setV (dV k) x).v (M j) = s.v (M j) := fun j hj =>
        RegUpd.v_setV_of_ne _ _ (hM j hj k hk)
      intro j hj e he
      rcases List.mem_cons.mp hj with rfl | hj'
      · rw [hn j hk hnk, RegUpd.v_setV_self, hl e he]
      · have hjk : j ≠ k := fun h => hnk (h ▸ hj')
        rw [hr j hj' e he, RegUpd.v_setV_of_ne _ _ (dV_ne j (hks' j hj') k hk hjk), term, term,
          hopnd, hmul j (hks' j hj')]
    · intro j hj hjn
      have hjk : j ≠ k := fun h => hjn (h ▸ List.mem_cons_self)
      rw [hn j hj (fun h => hjn (List.mem_cons_of_mem _ h)), RegUpd.v_setV_of_ne _ _ (dV_ne j hj k hk hjk)]
    · exact ⟨hkp.gpr, hkp.mem, hkp.rd, hkp.wr, hkp.sp, fun r hr' => by
        rw [hkp.v r hr', RegUpd.v_setV_of_ne _ _ (hr' k hk)]⟩

/-- A row: the five targets. -/
theorem row_ok (hi fresh : Bool) {i : Nat} (hi5 : i < 5) {M : Nat → VReg}
    (hM : ∀ k < 5, ∀ j < 5, M k ≠ dV j) (s : State) :
    WP isa (.block ((List.range 5).map (mac hi fresh i M))) s fun t =>
      (∀ k < 5, ∀ e < 2, ln (t.v (dV k)) e =
        ((if fresh then 0 else ln (s.v (dV k)) e) + term s hi i M k e) % 2 ^ 64) ∧ MKeep s t :=
  WP.mono (row_aux hi fresh i hi5 M hM (List.range 5) (fun _ h => List.mem_range.mp h) List.nodup_range s)
    fun _ ⟨h, _, k⟩ => ⟨fun j hj => h j (List.mem_range.mpr hj), k⟩

theorem MKeep.trans {s t u : State} (h : MKeep s t) (k : MKeep t u) : MKeep s u :=
  ⟨k.gpr.trans h.gpr, k.mem.trans h.mem, k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp,
    fun r hr => (k.v r hr).trans (h.v r hr)⟩

end VG.Proof.Poly1305.AArch64.Vector
