module

public import VerifiedGarbage.Proof.Sha3.AArch64.Rounds
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.RoundConstants
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.StraightV

/-!
# Keccak-f[1600] on AArch64, in vector registers: the 24 rounds

The table of round constants (`RcTable`), the rounds' loop on both
doublewords (`loop_ok`), from what its body does (`BodyOk`), and `rounds_ok`.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3.AArch64 VG.Proof.Sha3.AArch64.Neon VG.Proof.Sha3.AArch64.Rounds
open VG.Proof.Sha3.AArch64.Eval (OnlyV)
open VG.Proof.Sha3.Forms (core)
open VG.Spec.Sha3 (keccakF rnd RC)
open VG.Impl.Sha3.AArch64.Lanes (home)
open VG.Proof.MlKem.AArch64 (VUpd VMem wp_strq wp_ldrq wp_vop vupd_setV)
open VG.Impl.Sha3.AArch64.RoundConstants (rcs2 sym2)

/-- Only `x16`, `x17` and vector registers may differ. -/
structure CoreKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x16 → r ≠ .x17 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem CoreKeep.refl (s : State) : CoreKeep s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem CoreKeep.trans {s t u : State} (h : CoreKeep s t) (g : CoreKeep t u) : CoreKeep s u :=
  ⟨fun r h6 h7 => (g.gpr r h6 h7).trans (h.gpr r h6 h7), g.mem.trans h.mem, g.rd.trans h.rd, g.wr.trans h.wr, g.sp.trans h.sp⟩
theorem CoreKeep.onlyV {s t : State} (h : OnlyV s t) : CoreKeep s t := by
  obtain ⟨v, rfl⟩ := h; exact ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem CoreKeep.upd {s t : State} {d : Reg} {x : BitVec 64} (h : Upd s t d x) (hd : d = .x16 ∨ d = .x17) : CoreKeep s t :=
  ⟨fun r h6 h7 => h.other r (by rintro rfl; rcases hd with rfl | rfl <;> contradiction), h.mem, h.rd, h.wr, h.sp⟩

/-! ## The table -/

/-- The table of the round constants, each twice, at `T`, readable. -/
structure RcTable (s : State) (T : Addr) : Prop where
  rd : ∀ r < 24, InRegions (s.rd ++ s.wr) (T + BitVec.ofNat 64 (16 * r)) 16
  entry : ∀ r < 24, s.mem.read (T + BitVec.ofNat 64 (16 * r)) 16 = ofVDwords (RC r) (RC r)

theorem RcTable.frame {s t : State} {T : Addr} (h : RcTable s T) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (Region.mk T 384).Disjoint r) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) : RcTable t T :=
  ⟨fun k hk => by rw [hrd, hwr]; exact h.rd k hk, fun k hk => by
    rw [hf.read (r := ⟨T, 384⟩) (Offset.contains_base T (by omega) (by omega)) hd (by decide)]
    exact h.entry k hk⟩

theorem RcTable.core {s t : State} {T : Addr} (h : RcTable s T) (k : CoreKeep s t) : RcTable t T :=
  ⟨fun r hr => by rw [k.rd, k.wr]; exact h.rd r hr, fun r hr => by rw [k.mem]; exact h.entry r hr⟩

theorem rcStore_ok {s : State} {b : Reg} (hb : b ≠ .x16) {off : Nat} (ho : off % 16 = 0) (hlt : off ≤ 32768) {T : Addr}
    (hT : s.gpr b + BitVec.ofNat 64 off = T) (hw : ∀ r < 24, InRegions s.wr (T + BitVec.ofNat 64 (16 * r)) 16) :
    WP isa (.block (rcStore b off)) s fun t => (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) ∧ (∀ v, v ≠ .v31 → t.v v = s.v v) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Frame [⟨T, 384⟩] s.mem t.mem ∧ RcTable t T := by
  suffices h : ∀ k ≤ 24, WP isa (.block (([.adrSym .x16 sym2] : List Instr) ++ (List.range k).flatMap fun r =>
      [.ldrqTbl .v31 .x16 (16 * r) sym2 rcs2, .strq .v31 b (off + 16 * r)])) s fun t =>
      (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) ∧ (∀ v, v ≠ .v31 → t.v v = s.v v) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ Frame [⟨T, 384⟩] s.mem t.mem ∧ t.gpr .x16 = t.syms sym2 ∧
      ∀ r < k, t.mem.read (T + BitVec.ofNat 64 (16 * r)) 16 = ofVDwords (RC r) (RC r) by
    refine WP.mono (h 24 (Nat.le_refl _)) fun t ⟨h1, h2, h3, h4, h5, h6, _, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, fun r hr => ?_, h8⟩
    obtain ⟨R, hR, hc⟩ := hw r hr
    exact ⟨R, List.mem_append_right _ (by rw [h4]; exact hR), hc⟩
  intro k hk
  induction k with
  | zero =>
    refine WP.cons (s' := s.write .x .x16 (s.syms sym2)) rfl (wp_nil ⟨fun g hg => ?_, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, ?_, fun r hr => absurd hr (Nat.not_lt_zero _)⟩)
    · rw [RegUpd.gpr_write, ite_eq_right hg]
    · rw [RegUpd.gpr_write, ite_eq_left rfl, BitVec.setWidth_eq]; rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ← List.append_assoc, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hrc := RoundConstants.rcs2_eq k (by omega)
    have hx : exec (.ldrqTbl .v31 .x16 (16 * k) sym2 rcs2) t = some (t.setV .v31 (ofVDwords (RC k) (RC k))) := by
      simp only [exec]
      rw [ite_eq_left ⟨h7, by omega, by omega, by rw [RoundConstants.rcs2_length]; omega⟩,
        show 16 * k / 8 = 2 * k by omega, hrc.1, hrc.2]
      rfl
    refine WP.cons hx ?_
    have ha : t.gpr b + BitVec.ofNat 64 (off + 16 * k) = T + BitVec.ofNat 64 (16 * k) := by
      rw [h1 b hb, BitVec.ofNat_add, ← BitVec.add_assoc, hT]
    have hin : InRegions (t.setV .v31 (ofVDwords (RC k) (RC k))).wr (T + BitVec.ofNat 64 (16 * k)) 16 := by
      rw [RegUpd.wr_setV, h4]; exact hw k (by omega)
    refine WP.cons (s' := { t.setV .v31 (ofVDwords (RC k) (RC k)) with
        mem := t.mem.write (T + BitVec.ofNat 64 (16 * k)) 16 (ofVDwords (RC k) (RC k)) }) ?_ (wp_nil ?_)
    · simp only [exec, addr, RegUpd.gpr_setV, ha]
      rw [ite_eq_left ⟨by omega, by omega⟩]
      simp only [Option.bind_some, State.store]
      rw [ite_eq_left hin, RegUpd.v_setV, ite_eq_left rfl]; rfl
    refine ⟨h1, fun v hv => ?_, h3, h4, h5, ?_, h7, fun r hr => ?_⟩
    · rw [RegUpd.v_setV, ite_eq_right hv]; exact h2 v hv
    · exact h6.write (List.mem_singleton_self _) _ (Offset.contains_base T (by omega) (by omega))
    · by_cases hrk : r = k
      · subst hrk; exact read_write16 _ _ _
      · rw [Mem.read_write_sep (Offset.sep T (by omega) (by omega) (by omega)) (by decide)]
        exact h8 r (by omega)

/-! ## Rounds -/

theorem pairs_iff {s : State} {A B : Spec.Sha3.State} : Pairs s A B ↔ Vec.Pairs 0 s A B := by
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · rw [show reg 0 i = vreg i from rfl, h i hi, vdword_ofVDwords_0, vdword_ofVDwords_1]; exact ⟨rfl, rfl⟩
  · have := h i hi
    rw [show reg 0 i = vreg i from rfl] at this
    apply vec64_ext
    · rw [this.1, vdword_ofVDwords_0]
    · rw [this.2, vdword_ofVDwords_1]

theorem pairs_two {s : State} {A B : Spec.Sha3.State} : Vec.Pairs 2 s A B ↔ Vec.Pairs 0 s A B := by
  simp only [Vec.Pairs, reg, home_mod 2, home_mod 0]

theorem reg_zero : ∀ r < 3, ∀ i < 25, reg r i ≠ .v31 ∧ (reg r i = .v0 ↔ i = 0) := by decide

/-- ι: lane 0 XORed with the round constant, in both states. -/
theorem iota_pairs {r n : Nat} (hr : r < 3) {A B : Spec.Sha3.State} {s t : State} (h : Vec.Pairs r s (core A) (core B))
    (h0 : t.v .v0 = s.v .v0 ^^^ ofVDwords (RC n) (RC n)) (ho : ∀ v, v ≠ .v0 → v ≠ .v31 → t.v v = s.v v) :
    Vec.Pairs r t (rnd A n) (rnd B n) := fun i hi => by
  have hn := reg_zero r hr i hi
  rw [Forms.rnd_core A n hi, Forms.rnd_core B n hi]
  by_cases hi0 : i = 0
  · subst hi0
    have := h 0 hi
    rw [hn.2.mpr rfl] at this ⊢
    rw [h0, StraightV.vdword_xor, StraightV.vdword_xor, vdword_ofVDwords_0, vdword_ofVDwords_1, this.1, this.2]
    simp only [ite_true, and_self]
  · rw [ite_eq_right hi0, ite_eq_right hi0, ho _ (fun e => hi0 (hn.2.mp e)) hn.1]
    exact h i hi

/-- Two rounds, `x16` pointing to their constants. -/
def BodyOk (bd : List Instr) : Prop :=
  ∀ {n : Nat} {s : State} {A B : Spec.Sha3.State}, Vec.Pairs 0 s A B →
    (∀ r < 2, InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * r)) 16 ∧
      s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * r)) 16 = ofVDwords (RC (n + r)) (RC (n + r))) →
    ∃ t, runBlock isa bd s = some t ∧ Vec.Pairs 0 t (rnd (rnd A n) (n + 1)) (rnd (rnd B n) (n + 1)) ∧ OnlyV s t

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

theorem iota_run {r n : Nat} (hr : r < 2) {s : State} {A B : Spec.Sha3.State}
    (h : Vec.Pairs (r + 1) s (core A) (core B))
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x16 + BitVec.ofNat 64 (16 * r)) 16)
    (hrc : s.mem.read (s.gpr .x16 + BitVec.ofNat 64 (16 * r)) 16 = ofVDwords (RC n) (RC n)) :
    ∃ t, runBlock isa (iota r) s = some t ∧ Vec.Pairs (r + 1) t (rnd A n) (rnd B n) ∧ OnlyV s t := by
  let s₁ := s.setV .v31 (ofVDwords (RC n) (RC n))
  let s₂ := s₁.setV .v0 (s₁.v .v0 ^^^ s₁.v .v31)
  have e₁ : exec (.ldrq .v31 .x16 (16 * r)) s = some s₁ := by
    simp only [exec, addr]
    rw [ite_eq_left ⟨by omega, by omega⟩]
    simp only [Option.bind_some, State.load]
    rw [ite_eq_left hin, hrc]; rfl
  have e₂ : exec (.vop (.logic .eor .v0 .v0 .v31)) s₁ = some s₂ := rfl
  refine ⟨s₂, ?_, iota_pairs (by omega) h ?_ fun v h0 h31 => ?_, (OnlyV.setV _ _ _).trans (.setV _ _ _)⟩
  · rw [iota, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_nil]
  · simp only [s₂, s₁, RegUpd.v_setV, ite_true]
    rw [ite_eq_right (by decide)]
  · simp only [s₂, s₁, RegUpd.v_setV]
    rw [ite_eq_right h0, ite_eq_right h31]

/-- A body of two rounds and their ι. -/
theorem body_run {es bs : Nat} (hk : ∀ r < 2, Vec.ok (round es bs r) r = true) :
    BodyOk (round es bs 0 ++ iota 0 ++ round es bs 1 ++ iota 1) := by
  intro n s A B hp hc
  obtain ⟨s₁, x₁, p₁, o₁⟩ := Vec.round_ok (by decide) (hk 0 (by decide)) hp
  have c₁ := CoreKeep.onlyV o₁
  have g₁ : s₁.gpr .x16 = s.gpr .x16 := by obtain ⟨v, rfl⟩ := o₁; rfl
  obtain ⟨s₂, x₂, p₂, o₂⟩ := iota_run (n := n) (r := 0) (by decide) p₁
    (by rw [g₁, c₁.rd, c₁.wr]; exact (hc 0 (by decide)).1) (by rw [g₁, c₁.mem]; exact (hc 0 (by decide)).2)
  obtain ⟨s₃, x₃, p₃, o₃⟩ := Vec.round_ok (r := 1) (by decide) (hk 1 (by decide)) p₂
  have o := (o₁.trans o₂).trans o₃
  have c := CoreKeep.onlyV o
  have g : s₃.gpr .x16 = s.gpr .x16 := by obtain ⟨v, rfl⟩ := o; rfl
  obtain ⟨s₄, x₄, p₄, o₄⟩ := iota_run (n := n + 1) (r := 1) (by decide) p₃
    (by rw [g, c.rd, c.wr]; exact (hc 1 (by decide)).1) (by rw [g, c.mem]; exact (hc 1 (by decide)).2)
  refine ⟨s₄, ?_, pairs_two.mp p₄, o.trans o₄⟩
  rw [List.append_assoc, List.append_assoc, runBlock_append _ _ x₁, runBlock_append _ _ x₂, runBlock_append _ _ x₃, x₄]

theorem pure_ok : ∀ r < 2, Vec.ok (round 0 0 r) r = true := by decide +kernel

theorem body_ok : BodyOk body := body_run pure_ok

theorem two_rounds (A : Spec.Sha3.State) (k : Nat) :
    (List.range (2 * (k + 1))).foldl rnd A = rnd (rnd ((List.range (2 * k)).foldl rnd A) (2 * k)) (2 * k + 1) := by
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, foldl_succ, foldl_succ]

/-- The loop of 12 bodies. -/
theorem loop_ok {bd : List Instr} (hb : BodyOk bd) {s : State} {T : Addr} {A B : Spec.Sha3.State} (hp : Pairs s A B)
    (hT : RcTable s T) (h16 : s.gpr .x16 = T) (h17 : s.gpr .x17 = 12) :
    WP isa (.loop (.block (bd ++ ([.addImm .x .x16 .x16 32, .subImm .x .x17 .x17 1] : List Instr))) (.nonzero .x .x17)) s
      fun t => CoreKeep s t ∧ Pairs t (keccakF A) (keccakF B) := by
  refine WP.loop (M := isa) (fun n t => ∃ k < 12, n = 12 - k ∧ CoreKeep s t ∧
      Vec.Pairs 0 t ((List.range (2 * k)).foldl rnd A) ((List.range (2 * k)).foldl rnd B) ∧
      t.gpr .x16 = T + BitVec.ofNat 64 (32 * k) ∧ t.gpr .x17 = BitVec.ofNat 64 (12 - k)) ?_ 12 s
    ⟨0, by decide, rfl, .refl s, pairs_iff.mp hp, by rw [h16]; simp, h17⟩
  rintro _ t ⟨k, hk, rfl, c, p, e16, e17⟩
  obtain ⟨u, x, pu, ou⟩ := hb (n := 2 * k) p fun r hr => by
    have e : t.gpr .x16 + BitVec.ofNat 64 (16 * r) = T + BitVec.ofNat 64 (16 * (2 * k + r)) := by
      rw [e16, BitVec.add_assoc, ← BitVec.ofNat_add, show 32 * k + 16 * r = 16 * (2 * k + r) by omega]
    rw [e]
    have hT' := hT.core c
    exact ⟨hT'.rd _ (by omega), hT'.entry _ (by omega)⟩
  rw [← two_rounds, ← two_rounds] at pu
  have cu := CoreKeep.onlyV ou
  have g : u.gpr = t.gpr := by obtain ⟨v, rfl⟩ := ou; rfl
  rw [WP.block_append_iff]
  refine WP.mono (WP.of_runBlock (M := isa) (Q := (· = u)) ⟨u, x, rfl⟩) fun _ e => ?_
  subst e
  refine wp_addImm (by decide) fun u₁ d₁ => wp_subImm (by decide) fun u₂ d₂ => wp_nil ?_
  have cc : CoreKeep s u₂ := ((c.trans cu).trans (.upd d₁ (.inl rfl))).trans (.upd d₂ (.inr rfl))
  have p₂ : Vec.Pairs 0 u₂ ((List.range (2 * (k + 1))).foldl rnd A) ((List.range (2 * (k + 1))).foldl rnd B) :=
    fun i hi => by rw [d₂.vec, d₁.vec]; exact pu i hi
  have f16 : u₂.gpr .x16 = T + BitVec.ofNat 64 (32 * (k + 1)) := by
    rw [d₂.other _ (by decide), d₁.gpr, g, e16, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [Nat.mul_add, Nat.mul_one]
  have f17 : u₂.gpr .x17 = BitVec.ofNat 64 (12 - (k + 1)) := by
    rw [d₂.gpr, d₁.other _ (by decide), g, e17]
    have : ∀ k < 12, BitVec.ofNat 64 (12 - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (12 - (k + 1)) := by decide
    exact this k hk
  have hz : isa.eval (.nonzero .x .x17) u₂ = some (decide (k + 1 ≠ 12)) := by
    show VG.AArch64.eval (.nonzero .x .x17) u₂ = _
    rw [eval_nonzero, f17]
    have : ∀ k < 12, (BitVec.ofNat 64 (12 - (k + 1)) != 0) = decide (k + 1 ≠ 12) := by decide
    rw [this k hk]
  by_cases h : k + 1 = 12
  · refine .inl ⟨by rw [hz, h]; rfl, cc, pairs_iff.mpr ?_⟩
    rw [h] at p₂; exact p₂
  · exact .inr ⟨by rw [hz, decide_eq_true h], 12 - (k + 1), by omega, k + 1, by omega, rfl, cc, p₂, f16, f17⟩

theorem rounds_ok {b : Reg} {s : State} {A B : Spec.Sha3.State} (hp : Pairs s A B) (hT : RcTable s (s.gpr b)) :
    WP isa (rounds b) s fun t => CoreKeep s t ∧ Pairs t (keccakF A) (keccakF B) := by
  refine WP.seq (wp_addImm (by decide) fun t d => wp_movz fun u e => wp_nil ?_)
  have c : CoreKeep s u := (CoreKeep.upd d (.inl rfl)).trans (.upd e (.inr rfl))
  refine WP.mono (loop_ok body_ok (A := A) (B := B) (fun i hi => by rw [e.vec, d.vec]; exact hp i hi) (hT.core c)
    (by rw [e.other _ (by decide), d.gpr]; simp) (by rw [e.gpr]; rfl)) fun w ⟨k, h⟩ => ⟨c.trans k, h⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector
