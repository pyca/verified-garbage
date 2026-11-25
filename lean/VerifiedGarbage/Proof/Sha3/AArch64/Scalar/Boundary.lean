module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Core
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Keccak-f[1600] on AArch64, in general registers: entry and exit

Saving the callee-saved registers in vector registers and restoring them,
and loading and storing the lanes, each pending its rotation.
-/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64

/-- The permissions and the stack pointer are kept. -/
structure Env (s t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Env.refl (s : State) : Env s s := ⟨rfl, rfl, rfl⟩
theorem Env.trans {s t u : State} (h : Env s t) (g : Env t u) : Env s u :=
  ⟨g.rd.trans h.rd, g.wr.trans h.wr, g.sp.trans h.sp⟩
theorem Env.upd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v) : Env s t := ⟨u.rd, u.wr, u.sp⟩

/-- `v` is `s` with the doublewords of `d` set to `x`. -/
structure Dup (s t : State) (d : VReg) (x : BitVec 64) : Prop where
  v : vdword (t.v d) 0 = x
  other : ∀ r, r ≠ d → t.v r = s.v r
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  env : Env s t

theorem wp_dup {d : VReg} {n : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ t, Dup s t d (s.gpr n) → WP isa (.block is) t Q) : WP isa (.block (.vop (.dup .d2 d n) :: is)) s Q := by
  refine WP.cons (s' := s.setV d (ofVDwords (s.gpr n) (s.gpr n))) rfl (k _ ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl, rfl⟩)
  · rw [RegUpd.v_setV, ite_eq_left rfl, vdword_ofVDwords_0]
  · rw [RegUpd.v_setV, ite_eq_right hr]

theorem wp_umov {d : Reg} {n : VReg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ t, Upd s t d (vdword (s.v n) 0) → WP isa (.block is) t Q) : WP isa (.block (.umov .x d n 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (vdword (s.v n) 0)) rfl (k _ (Upd.write64 _ _ _))

/-! ## The callee-saved registers -/

theorem savedVec_inj : ∀ i < 11, ∀ j < 11, savedVec i = savedVec j → i = j := by decide
theorem savedReg_inj : ∀ i < 11, ∀ j < 11, savedReg i = savedReg j → i = j := by decide
theorem savedReg_all : ∀ r ∈ preserved, ∃ i < 11, savedReg i = r := by decide

/-- The registers the code keeps are `o`'s, in vector registers. -/
def Saved (o s : State) : Prop := ∀ i < 11, vdword (s.v (savedVec i)) 0 = o.gpr (savedReg i)

theorem Saved.congr {o s t : State} (h : Saved o s) (hv : ∀ i < 11, t.v (savedVec i) = s.v (savedVec i)) : Saved o t :=
  fun i hi => by rw [hv i hi]; exact h i hi

theorem save_ok (s : State) : WP isa (.block save) s fun t =>
    Saved s t ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ Env s t ∧ ∀ r, (∀ i < 11, r ≠ savedVec i) → t.v r = s.v r := by
  suffices h : ∀ k ≤ 11, WP isa (.block ((List.range k).map fun i => .vop (.dup .d2 (savedVec i) (savedReg i)))) s fun t =>
      (∀ i < k, vdword (t.v (savedVec i)) 0 = s.gpr (savedReg i)) ∧ t.gpr = s.gpr ∧ t.mem = s.mem ∧ Env s t ∧
        ∀ r, (∀ i < 11, r ≠ savedVec i) → t.v r = s.v r from h 11 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), rfl, rfl, .refl s, fun _ _ => rfl⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h1, h2, h3, h4, h5⟩ => wp_dup fun u d => wp_nil ⟨fun i hi => ?_,
      d.gpr.trans h2, d.mem.trans h3, h4.trans d.env, fun r hr => (d.other r (hr k (by omega))).trans (h5 r hr)⟩
    by_cases hik : i = k
    · subst hik; rw [d.v, h2]
    · rw [d.other _ fun e => hik (savedVec_inj i (by omega) k (by omega) e)]
      exact h1 i (by omega)

theorem restore_ok {o s : State} (hs : Saved o s) : WP isa (.block restore) s fun t =>
    (∀ r ∈ preserved, t.gpr r = o.gpr r) ∧ (∀ r, r ∉ preserved → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.v = s.v ∧ Env s t := by
  suffices h : ∀ k ≤ 11, WP isa (.block ((List.range k).map fun i => .umov .x (savedReg i) (savedVec i) 0)) s fun t =>
      (∀ i < k, t.gpr (savedReg i) = o.gpr (savedReg i)) ∧ (∀ r, r ∉ preserved → t.gpr r = s.gpr r) ∧
        t.mem = s.mem ∧ t.v = s.v ∧ Env s t by
    refine WP.mono (h 11 (Nat.le_refl _)) fun t ⟨h1, h2⟩ => ⟨fun r hr => ?_, h2⟩
    obtain ⟨i, hi, rfl⟩ := savedReg_all r hr
    exact h1 i hi
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, .refl s⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h1, h2, h3, h4, h5⟩ => wp_umov fun u d => wp_nil ⟨fun i hi => ?_,
      fun r hr => ?_, d.mem.trans h3, d.vec.trans h4, h5.trans (.upd d)⟩
    · by_cases hik : i = k
      · subst hik; rw [d.gpr, h4]; exact hs i (by omega)
      · rw [d.other _ fun e => hik (savedReg_inj i (by omega) k (by omega) e)]
        exact h1 i (by omega)
    · have hm : ∀ i < 11, savedReg i ∈ preserved := by decide
      rw [d.other r fun e => hr (e ▸ hm k (by omega))]
      exact h2 r hr

/-! ## The lanes -/

theorem lreg_inj : ∀ i < 25, ∀ j < 25, lreg i = lreg j → i = j := by decide
theorem lreg_ne : ∀ i < 25, lreg i ≠ .x16 ∧ lreg i ≠ .x17 ∧ lreg i ≠ .x30 ∧ lreg i ≠ .x28 := by decide
theorem reg0 (i : Nat) : reg 0 i = lreg i := rfl
theorem pend_lt : ∀ i < 25, pend i < 64 := by decide
theorem pd_eq (i : Nat) : conf.pd i = pend i := rfl

theorem rotr_zero (x : BitVec 64) : x.rotateRight 0 = x := by
  ext j hj; simp [BitVec.getElem_rotateRight, hj]

theorem rotr_back (x : BitVec 64) {k : Nat} (hk : k < 64) (h0 : k ≠ 0) : (x.rotateRight k).rotateRight (64 - k) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (show 64 - k < 64 by omega)]
  split
  · split
    · rename_i h1 h2; omega
    · rename_i h1 h2
      rw [show 64 - k + i - (64 - k) = i by omega]
      simp [show 64 - k + i < 64 by omega]
  · rename_i h1
    simp only [hi, decide_true, Bool.true_and]
    split
    · congr 1; omega
    · omega

theorem lanes_upd {s t : State} {A : Spec.Sha3.State} (h : Lanes s A) {d : Reg} {x : BitVec 64} (u : Upd s t d x)
    (hd : d ∈ [Reg.x16, .x17, .x30, .x28] := by decide) : Lanes t A := fun i hi => by
  have hn := lreg_ne i hi
  rw [reg0, u.other _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    exacts [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2])]
  exact h i hi

/-- Only the lanes' registers differ. -/
structure Loaded (s t : State) : Prop where
  other : ∀ r, (∀ i < 25, r ≠ lreg i) → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  v : t.v = s.v
  env : Env s t

/-- Loading the lanes at `p + stride i + off`. -/
theorem load_ok {s : State} {b : Reg} (hb : ∀ i < 25, b ≠ lreg i) {stride off : Nat} (hd : stride % 8 = 0) (ho : off % 8 = 0)
    (hs : stride ≤ 16) (hoff : off < 16) {A : Spec.Sha3.State}
    (hin : ∀ i < 25, InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (stride * i + off)) 8)
    (hA : ∀ i < 25, s.mem.readW (s.gpr b + BitVec.ofNat 64 (stride * i + off)) 64 = A[i]!) :
    WP isa (.block (load b stride off)) s fun t => Lanes t A ∧ Loaded s t := by
  suffices h : ∀ k ≤ 25, WP isa (.block ((List.range k).flatMap fun i => loadLane b i (stride * i + off))) s fun t =>
      (∀ i < k, t.gpr (lreg i) = A[i]!.rotateRight (pend i)) ∧ Loaded s t from
    WP.mono (h 25 (Nat.le_refl _)) fun t ⟨h1, h2⟩ => ⟨fun i hi => h1 i hi, h2⟩
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, .refl s⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h1, h2⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, loadLane, List.cons_append, List.nil_append]
    have hbt : t.gpr b = s.gpr b := h2.other b hb
    have e8 : (stride * k + off) % 8 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod, hd, ho]; simp
    have eb : stride * k + off < 4096 * 8 := by
      have := Nat.mul_le_mul hs (show k ≤ 24 by omega)
      omega
    refine wp_ldr (a := s.gpr b + BitVec.ofNat 64 (stride * k + off)) ⟨e8, eb⟩ (by rw [hbt])
      (by rw [h2.env.rd, h2.env.wr]; exact hin k (by omega)) fun u d => ?_
    rw [h2.mem, hA k (by omega)] at d
    have fin : ∀ w, w.gpr (lreg k) = A[k]!.rotateRight (pend k) → (∀ r, r ≠ lreg k → w.gpr r = u.gpr r) →
        w.mem = u.mem → w.v = u.v → Env u w →
        (∀ i < k + 1, w.gpr (lreg i) = A[i]!.rotateRight (pend i)) ∧ Loaded s w := fun w e1 e2 e3 e4 e5 => by
      refine ⟨fun i hi => ?_, fun r hr => ?_, ?_, ?_, (h2.env.trans (.upd d)).trans e5⟩
      · by_cases hik : i = k
        · subst hik; exact e1
        · have hne : lreg i ≠ lreg k := fun e => hik (lreg_inj i (by omega) k (by omega) e)
          rw [e2 _ hne, d.other _ hne]; exact h1 i (by omega)
      · rw [e2 r (hr k (by omega)), d.other r (hr k (by omega))]; exact h2.other r hr
      · rw [e3, d.mem, h2.mem]
      · rw [e4, d.vec, h2.v]
    split
    · rename_i h0
      exact wp_nil (fin u (by rw [d.gpr, h0, rotr_zero]) (fun _ _ => rfl) rfl rfl (.refl u))
    · exact wp_ror (pend_lt k (by omega)) fun w d' => wp_nil
        (fin w (by rw [d'.gpr, d.gpr]) d'.other d'.mem d'.vec (.upd d'))

/-- Where the lanes are. -/
def laneRs (p : Addr) (stride off : Nat) : List Region :=
  (List.range 25).map fun i => ⟨p + BitVec.ofNat 64 (stride * i + off), 8⟩

/-- Storing the lanes at `p + stride i + off`. -/
theorem store_ok {s : State} {b : Reg} (hb : ∀ i < 25, b ≠ lreg i) {stride off : Nat} (hd : stride % 8 = 0) (ho : off % 8 = 0)
    (hs : stride ≤ 16) (h8 : 8 ≤ stride) (hoff : off < 16) {A : Spec.Sha3.State} (hl : Lanes s A)
    (hin : ∀ i < 25, InRegions s.wr (s.gpr b + BitVec.ofNat 64 (stride * i + off)) 8) :
    WP isa (.block (store b stride off)) s fun t =>
      (∀ i < 25, t.mem.readW (s.gpr b + BitVec.ofNat 64 (stride * i + off)) 64 = A[i]!) ∧
      Frame (laneRs (s.gpr b) stride off) s.mem t.mem ∧
      (∀ r, (∀ i < 25, r ≠ lreg i) → t.gpr r = s.gpr r) ∧ t.v = s.v ∧ Env s t := by
  suffices h : ∀ k ≤ 25, WP isa (.block ((List.range k).flatMap fun i => storeLane b i (stride * i + off))) s fun t =>
      (∀ i < k, t.mem.readW (s.gpr b + BitVec.ofNat 64 (stride * i + off)) 64 = A[i]!) ∧
      Frame (laneRs (s.gpr b) stride off) s.mem t.mem ∧ (∀ r, (∀ i < 25, r ≠ lreg i) → t.gpr r = s.gpr r) ∧
      t.v = s.v ∧ Env s t ∧ ∀ i < 25, k ≤ i → t.gpr (lreg i) = s.gpr (lreg i) from
    WP.mono (h 25 (Nat.le_refl _)) fun t ⟨h1, h2, h3, h4, h5, _⟩ => ⟨h1, h2, h3, h4, h5⟩
  intro k hk
  induction k with
  | zero =>
    exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ => rfl, rfl, .refl s, fun _ _ _ => rfl⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h1, h2, h3, h4, h5, h6⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, storeLane]
    have e8 : (stride * k + off) % 8 = 0 := by rw [Nat.add_mod, Nat.mul_mod, hd, ho]; simp
    have eb : stride * k + off < 4096 * 8 := by
      have := Nat.mul_le_mul hs (show k ≤ 24 by omega)
      omega
    have hk' : t.gpr (lreg k) = A[k]!.rotateRight (pend k) := by rw [h6 k (by omega) (Nat.le_refl _)]; exact hl k (by omega)
    have str : ∀ u, u.gpr (lreg k) = A[k]! → (∀ r, r ≠ lreg k → u.gpr r = t.gpr r) → u.mem = t.mem → u.v = t.v → Env t u →
        WP isa (.block [.str .x (lreg k) b (stride * k + off)]) u fun t =>
          (∀ i < k + 1, t.mem.readW (s.gpr b + BitVec.ofNat 64 (stride * i + off)) 64 = A[i]!) ∧
          Frame (laneRs (s.gpr b) stride off) s.mem t.mem ∧ (∀ r, (∀ i < 25, r ≠ lreg i) → t.gpr r = s.gpr r) ∧
          t.v = s.v ∧ Env s t ∧ ∀ i < 25, k + 1 ≤ i → t.gpr (lreg i) = s.gpr (lreg i) := fun u e1 e2 e3 e4 e5 => by
      refine wp_str (a := s.gpr b + BitVec.ofNat 64 (stride * k + off)) ⟨e8, eb⟩
        (by rw [e2 b (hb k (by omega)), h3 b hb]) (by rw [e5.wr, h5.wr]; exact hin k (by omega)) fun w d => wp_nil ?_
      have hm : w.mem = t.mem.writeW (s.gpr b + BitVec.ofNat 64 (stride * k + off)) A[k]! := by rw [d.mem, e1, e3]
      refine ⟨fun i hi => ?_, ?_, fun r hr => ?_, ?_, (h5.trans e5).trans ⟨d.rd, d.wr, d.sp⟩, fun i hi hki => ?_⟩
      · rw [hm]
        by_cases hik : i = k
        · subst hik; exact Mem.readW_writeW_self64 _ _ _
        · have hm' : stride * i + off + 8 ≤ stride * k + off := by
            have := Nat.mul_le_mul (Nat.le_refl stride) (show i + 1 ≤ k by omega)
            rw [Nat.mul_add, Nat.mul_one] at this
            omega
          rw [Mem.readW_writeW_sep (Offset.sep _ (.inl hm') (by omega) (by omega)) (by decide)]
          exact h1 i (by omega)
      · rw [hm]
        exact h2.writeW (r := ⟨s.gpr b + BitVec.ofNat 64 (stride * k + off), 8⟩)
          (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), rfl⟩) _ (Region.contains_self _ _)
      · rw [d.gpr, e2 r (hr k (by omega))]; exact h3 r hr
      · rw [d.vec, e4, h4]
      · rw [d.gpr, e2 _ fun e => by have := lreg_inj i hi k (by omega) e; omega]
        exact h6 i hi (by omega)
    split
    · rename_i h0
      exact str t (by rw [hk', h0, rotr_zero]) (fun _ _ => rfl) rfl rfl (.refl t)
    · rename_i h0
      simp only [List.cons_append, List.nil_append]
      have hp := pend_lt k (by omega)
      exact wp_ror (by omega) fun u d => str u (by rw [d.gpr, hk', rotr_back _ hp h0]) d.other d.mem d.vec (.upd d)

/-! ## Around the core -/

/-- What holds between the entry from `o` and the exit. -/
structure Ctx (o s : State) : Prop where
  saved : Saved o s
  vp : ∀ r ∈ preservedV, s.v r = o.v r
  env : Env o s

theorem savedVec_ne : ∀ i < 11, savedVec i ≠ .v27 ∧ savedVec i ≠ .v28 ∧ savedVec i ≠ .v29 ∧ savedVec i ≠ .v30 ∧
    savedVec i ≠ .v31 ∧ savedVec i ≠ .v0 ∧ savedVec i ≠ .v1 ∧ savedVec i ≠ .v2 ∧ savedVec i ∉ preservedV := by decide

/-- The vector registers that hold arguments. -/
def argVec : List VReg := [.v0, .v1, .v2, .v29, .v30, .v31]

theorem argVec_ne : ∀ r ∈ argVec, r ∉ preservedV ∧ ∀ i < 11, savedVec i ≠ r := by decide

theorem Ctx.ofV {o s t : State} (h : Ctx o s) (hv : t.v = s.v) (he : Env s t) : Ctx o t :=
  ⟨h.saved.congr fun _ _ => by rw [hv], fun r hr => by rw [hv]; exact h.vp r hr, h.env.trans he⟩

theorem Ctx.upd {o s t : State} (h : Ctx o s) {d : Reg} {x : BitVec 64} (u : Upd s t d x) : Ctx o t := h.ofV u.vec (.upd u)

theorem Ctx.dup {o s t : State} (h : Ctx o s) {d : VReg} (hd : d ∈ argVec) {x : BitVec 64} (u : Dup s t d x) : Ctx o t :=
  ⟨h.saved.congr fun i hi => u.other _ ((argVec_ne d hd).2 i hi),
    fun r hr => (u.other r fun e => (argVec_ne d hd).1 (e ▸ hr)).trans (h.vp r hr), h.env.trans u.env⟩

theorem Ctx.core {o s t : State} (h : Ctx o s) (k : CoreKeep s t) : Ctx o t :=
  ⟨h.saved.congr fun i hi => k.v _ (savedVec_ne i hi).1 (savedVec_ne i hi).2.1,
    fun r hr => (k.v r (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))).trans (h.vp r hr),
    h.env.trans ⟨k.rd, k.wr, k.sp⟩⟩

/-- Entry: the registers saved. -/
theorem enter_ok (s : State) : WP isa (.block save) s fun t => Ctx s t ∧ t.gpr = s.gpr ∧ t.mem = s.mem :=
  WP.mono (save_ok s) fun _ ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨⟨h1, fun r hr => h5 r fun i hi e => (savedVec_ne i hi).2.2.2.2.2.2.2.2 (e ▸ hr), h4⟩, h2, h3⟩

/-- Exit: the registers restored. -/
theorem exit_ok {o s : State} (h : Ctx o s) : WP isa (.block restore) s fun t =>
    abiPreserved o t ∧ t.mem = s.mem ∧ t.v = s.v ∧ Env s t ∧ ∀ r, r ∉ preserved → t.gpr r = s.gpr r :=
  WP.mono (restore_ok h.saved) fun t ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨⟨h1, h5.sp.trans h.env.sp, fun r hr => by rw [h4, h.vp r hr]⟩, h3, h4, h5, h2⟩

theorem b16 : ∀ i < 25, Reg.x16 ≠ lreg i := by decide

/-- The state whose lanes are at `p + stride i + off`. -/
def stateFrom (m : Mem) (p : Addr) (stride off : Nat) : Spec.Sha3.State :=
  Vector.ofFn fun i => m.readW (p + BitVec.ofNat 64 (stride * i.val + off)) 64

theorem stateFrom_get (m : Mem) (p : Addr) (stride off : Nat) {i : Nat} (hi : i < 25) :
    (stateFrom m p stride off)[i]! = m.readW (p + BitVec.ofNat 64 (stride * i + off)) 64 := by
  rw [getElem!_eq _ hi]; simp only [stateFrom, Vector.getElem_ofFn]

theorem eq_stateFrom {m : Mem} {p : Addr} {stride off : Nat} {A : Spec.Sha3.State}
    (h : ∀ i < 25, m.readW (p + BitVec.ofNat 64 (stride * i + off)) 64 = A[i]!) : stateFrom m p stride off = A := by
  apply Vector.ext
  intro i hi
  rw [← getElem!_eq _ hi, ← getElem!_eq _ hi, stateFrom_get _ _ _ _ hi, h i hi]

theorem stateFrom_congr {m m' : Mem} {p : Addr} {stride off : Nat}
    (h : ∀ i < 25, m'.readW (p + BitVec.ofNat 64 (stride * i + off)) 64 = m.readW (p + BitVec.ofNat 64 (stride * i + off)) 64) :
    stateFrom m' p stride off = stateFrom m p stride off :=
  eq_stateFrom fun i hi => by rw [h i hi, stateFrom_get _ _ _ _ hi]

theorem stateFrom_stateAt (m : Mem) (p : Addr) : stateFrom m p 8 0 = Spec.Sha3.stateAt m p := rfl

end VG.Proof.Sha3.AArch64.Scalar
