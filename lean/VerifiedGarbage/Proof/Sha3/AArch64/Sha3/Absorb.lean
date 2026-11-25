module

public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Boundary
public import VerifiedGarbage.Proof.Sha3.AArch64.Blocks
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.StraightV

/-! # Keccak-f[1600] on AArch64, in vector registers: absorbing blocks -/

-- separate module: a proof of its own function, which `Boundary.lean`'s callers do not need

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (laneAddr sub_beq sub_ofNat)
open VG.Proof.Sha3.AArch64 VG.Proof.Sha3.AArch64.Neon VG.Proof.Sha3.AArch64.Blocks
open VG.Spec.Sha3 (keccakF stateAt rates bytesAt)
open VG.Proof.MlKem.AArch64 (VUpd VMem VChg wp_strq wp_ldrq wp_vop vupd_setV)

/-- Only `x9`, `x10` and vector registers may differ. -/
structure WKeep (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem WKeep.refl (s : State) : WKeep s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
theorem WKeep.trans {s t u : State} (h : WKeep s t) (g : WKeep t u) : WKeep s u :=
  ⟨fun r h6 h7 => (g.gpr r h6 h7).trans (h.gpr r h6 h7), g.mem.trans h.mem, g.rd.trans h.rd, g.wr.trans h.wr, g.sp.trans h.sp⟩
theorem WKeep.vupd {s t : State} {d : VReg} {x : BitVec 128} (h : VUpd s t d x) : WKeep s t :=
  ⟨fun r _ _ => by rw [h.gpr], h.mem, h.rd, h.wr, h.sp⟩
theorem WKeep.upd {s t : State} {d : Reg} {x : BitVec 64} (h : Upd s t d x) (hd : d = .x9 ∨ d = .x10) : WKeep s t :=
  ⟨fun r h6 h7 => h.other r (by rintro rfl; rcases hd with rfl | rfl <;> contradiction), h.mem, h.rd, h.wr, h.sp⟩

/-- Lane `k` XORed with word `k` of the data. -/
theorem xor_lane {s t : State} {S : Spec.Sha3.State} {m : Mem} {p : Addr} {k : Nat} (hk : k < 25)
    (h : One s (xorWords S m p k)) (hx : vdword (t.v (vreg k)) 0 = vdword (s.v (vreg k)) 0 ^^^ m.readW (laneAddr p k) 64)
    (ho : ∀ i < 25, i ≠ k → t.v (vreg i) = s.v (vreg i)) : One t (xorWords S m p (k + 1)) := fun i hi => by
  have := h i hi
  rw [xorWords_get! _ _ _ _ hi] at this ⊢
  by_cases hik : i = k
  · subst hik
    rw [ite_eq_right (by omega), show S[i]! ^^^ (0 : BitVec 64) = S[i]! from BitVec.xor_zero] at this
    rw [hx, this, ite_eq_left (by omega)]
  · rw [ho i hi hik, this]
    by_cases hlt : i < k
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]

theorem ne25 {i : Nat} (hi : i < 25) : vreg i ≠ .v25 := fun e => by
  have := (vreg_inj i (by omega) 25 (by omega)).mp e; omega

theorem ne_lane {i j : Nat} (hi : i < 25) (hj : j < 25) (h : i ≠ j) : vreg i ≠ vreg j := fun e =>
  h ((vreg_inj i (by omega) j (by omega)).mp e)

theorem xorOne_ok {s : State} {S : Spec.Sha3.State} {m : Mem} {p : Addr} {k : Nat} (hk : k < 25)
    (h : One s (xorWords S m p k)) (hp : s.gpr .x2 = p) (hin : InRegions (s.rd ++ s.wr) (laneAddr p k) 8)
    (hm : s.mem.readW (laneAddr p k) 64 = m.readW (laneAddr p k) 64) :
    WP isa (.block (xorOne k)) s fun t => One t (xorWords S m p (k + 1)) ∧ WKeep s t := by
  refine wp_ldr (a := laneAddr p k) ⟨by omega, by omega⟩ (by rw [hp]) hin fun t d => ?_
  refine WP.cons (s' := t.setV .v25 (ofVDwords (t.gpr .x9) (t.gpr .x9))) rfl (wp_vop rfl fun u e => wp_nil
    ⟨xor_lane hk h ?_ fun i hi hik => ?_, (WKeep.upd d (.inl rfl)).trans ((WKeep.vupd (vupd_setV ..)).trans (.vupd e))⟩)
  · rw [e.v, StraightV.vdword_xor, RegUpd.v_setV, ite_eq_right (ne25 hk), RegUpd.v_setV, ite_eq_left rfl,
      vdword_ofVDwords_0, d.gpr, d.vec, hm]
  · rw [e.other _ (ne_lane hi hk hik), RegUpd.v_setV, ite_eq_right (ne25 hi), d.vec]

theorem xorPair_ok {s : State} {S : Spec.Sha3.State} {m : Mem} {p : Addr} {r : Reg} {k i : Nat} (hi : i + 1 < 25) (hk : k < 100)
    (h : One s (xorWords S m p i)) (hq : s.gpr r + BitVec.ofNat 64 (16 * k) = laneAddr p i)
    (hin : InRegions (s.rd ++ s.wr) (laneAddr p i) 16)
    (hm : ∀ j, j = i ∨ j = i + 1 → s.mem.readW (laneAddr p j) 64 = m.readW (laneAddr p j) 64) :
    WP isa (.block (xorPair r k i)) s fun t => One t (xorWords S m p (i + 2)) ∧ WKeep s t ∧ t.gpr = s.gpr := by
  refine wp_ldrq (a := laneAddr p i) ⟨by omega, by omega⟩ hq hin fun t₁ d₁ => wp_vop rfl fun t₂ d₂ => wp_vop rfl fun t₃ d₃ =>
    wp_vop rfl fun t₄ d₄ => wp_nil ?_
  have e1 : laneAddr p i + BitVec.ofNat 64 8 = laneAddr p (i + 1) := by
    simp only [laneAddr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add]
  have o₂ : One t₂ (xorWords S m p (i + 1)) := xor_lane (by omega) (s := s) h (by
    rw [d₂.v, StraightV.vdword_xor, d₁.other _ (ne25 (by omega)), d₁.v, vdword_read16 _ _ (by decide), ← hm i (.inl rfl)]
    simp) fun j hj hji => by rw [d₂.other _ (ne_lane hj (by omega) hji), d₁.other _ (ne25 hj)]
  refine ⟨xor_lane (k := i + 1) hi o₂ ?_ fun j hj hji => ?_, ((WKeep.vupd d₁).trans (.vupd d₂)).trans ((WKeep.vupd d₃).trans (.vupd d₄)), ?_⟩
  · rw [d₄.v, StraightV.vdword_xor, d₃.other _ (ne25 hi), d₃.v, ext8_low, d₂.other _ (ne25 (i := i) (by omega)).symm, d₁.v,
      vdword_read16 _ _ (by decide), Nat.mul_one, e1, hm _ (.inr rfl)]
  · rw [d₄.other _ (ne_lane hj hi hji), d₃.other _ (ne25 hj)]
  · rw [d₄.gpr, d₃.gpr, d₂.gpr, d₁.gpr]

theorem xorPairs_ok {s : State} {S : Spec.Sha3.State} {m : Mem} {p : Addr} {i n : Nat} (hn : i + 2 * n ≤ 25)
    (h : One s (xorWords S m p i)) (hp : s.gpr .x2 = p)
    (hin : ∀ j, i ≤ j → j + 2 ≤ i + 2 * n → InRegions (s.rd ++ s.wr) (laneAddr p j) 16)
    (hm : ∀ j < i + 2 * n, s.mem.readW (laneAddr p j) 64 = m.readW (laneAddr p j) 64) :
    WP isa (.block (xorPairs i n)) s fun t => One t (xorWords S m p (i + 2 * n)) ∧ WKeep s t := by
  suffices h : ∀ k ≤ n, WP isa (.block (([.addImm .x .x10 .x2 (8 * i)] : List Instr) ++
      (List.range k).flatMap fun k => xorPair .x10 k (i + 2 * k))) s fun t =>
      One t (xorWords S m p (i + 2 * k)) ∧ WKeep s t ∧ t.gpr .x10 = laneAddr p i from
    WP.mono (h n (Nat.le_refl _)) fun t h => ⟨h.1, h.2.1⟩
  intro k hk
  induction k with
  | zero =>
    exact wp_addImm (by omega) fun t d => wp_nil ⟨fun j hj => by rw [d.vec]; exact h j hj, .upd d (.inr rfl), by rw [d.gpr, hp, laneAddr]⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ← List.append_assoc, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h1, h2, h3⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (xorPair_ok (by omega) (by omega) h1 ?_ ?_ ?_) fun u ⟨g1, g2, g3⟩ => ⟨g1, h2.trans g2, by rw [g3, h3]⟩
    · rw [h3]; simp only [laneAddr]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * i + 16 * k = 8 * (i + 2 * k) by omega]
    · rw [h2.rd, h2.wr]; exact hin _ (by omega) (by omega)
    · intro j hj; rw [h2.mem]; exact hm j (by omega)

theorem unlessRate_ok {s : State} {r : BitVec 64} (hv : s.gpr .x1 = r) {R : Nat} (hR : R < 4096) {c : Prog isa}
    {Q : State → Prop} (he : ∀ t x, r.toNat = R → Upd s t .x9 x → Q t)
    (hn : ∀ t x, r.toNat ≠ R → Upd s t .x9 x → WP isa c t Q) : WP isa (unlessRate R c) s Q := by
  unfold unlessRate
  refine WP.seq (wp_subImm (by omega) fun t u => wp_nil ?_)
  refine WP.ite (decide (r.toNat = R)) ?_ (fun hb => wp_nil (he t _ (by simpa using hb) u)) (fun hb => hn t _ (by simpa using hb) u)
  show VG.AArch64.eval (.zero .x .x9) t = _
  rw [eval_zero, u.gpr, hv]
  have : r = BitVec.ofNat 64 r.toNat := by simp
  rw [this, sub_beq r.isLt (by omega), ← this]

theorem xorBlock_ok {s : State} {S : Spec.Sha3.State} {m : Mem} {p : Addr} {r : BitVec 64} (hr : r.toNat ∈ rates)
    (hv : s.gpr .x1 = r) (hl : One s S) (hp : s.gpr .x2 = p)
    (hin : ∀ i n, 8 * i + n ≤ r.toNat → InRegions (s.rd ++ s.wr) (laneAddr p i) n)
    (hm : ∀ i, 8 * i + 8 ≤ r.toNat → s.mem.readW (laneAddr p i) 64 = m.readW (laneAddr p i) 64) :
    WP isa xorBlock s fun t => One t (xorWords S m p (r.toNat / 8)) ∧ WKeep s t := by
  have pairs : ∀ {i : Nat} (n : Nat) {t : State}, i + 2 * n ≤ 25 → 8 * (i + 2 * n) ≤ r.toNat → One t (xorWords S m p i) ∧ WKeep s t →
      WP isa (.block (xorPairs i n)) t fun u => One u (xorWords S m p (i + 2 * n)) ∧ WKeep s u := fun {i} n {t} hn h8 ⟨h, k⟩ =>
    WP.mono (xorPairs_ok hn h ((k.gpr _ (by decide) (by decide)).trans hp)
      (fun j hj hj' => by rw [k.rd, k.wr]; exact hin j 16 (by omega)) (fun j hj => by rw [k.mem]; exact hm j (by omega)))
      fun u h => ⟨h.1, k.trans h.2⟩
  have one : ∀ {i : Nat} {t : State}, i < 25 → 8 * (i + 1) ≤ r.toNat → One t (xorWords S m p i) ∧ WKeep s t →
      WP isa (.block (xorOne i)) t fun u => One u (xorWords S m p (i + 1)) ∧ WKeep s u := fun {i} {t} hi h8 ⟨h, k⟩ =>
    WP.mono (xorOne_ok hi h ((k.gpr _ (by decide) (by decide)).trans hp)
      (by rw [k.rd, k.wr]; exact hin _ 8 (by omega)) (by rw [k.mem]; exact hm _ (by omega))) fun u h => ⟨h.1, k.trans h.2⟩
  have upd : ∀ {t u : State} {a : Nat} {x : BitVec 64}, One t (xorWords S m p a) ∧ WKeep s t → Upd t u .x9 x →
      One u (xorWords S m p a) ∧ WKeep s u := fun h d => ⟨fun i hi => by rw [d.vec]; exact h.1 i hi, h.2.trans (.upd d (.inl rfl))⟩
  have vt : ∀ {t : State}, WKeep s t → t.gpr .x1 = r := fun k => (k.gpr _ (by decide) (by decide)).trans hv
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hr
  unfold xorBlock
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairs (i := 0) 4 (by decide) (by omega) ⟨by rw [xorWords_zero]; exact hl, .refl s⟩) fun t₀ h₀ => ?_
  refine WP.mono (one (i := 8) (by decide) (by omega) h₀) fun t₁ h₁ => ?_
  refine unlessRate_ok (vt h₁.2) (by decide) (fun u x e d => by rw [e]; exact upd h₁ d) fun u₁ x₁ n₁ d₁ => ?_
  refine WP.seq (WP.mono (pairs 2 (by decide) (by omega) (upd h₁ d₁)) fun t₂ h₂ => ?_)
  refine unlessRate_ok (vt h₂.2) (by decide) (fun u x e d => by rw [e]; exact upd h₂ d) fun u₂ x₂ n₂ d₂ => ?_
  refine WP.seq (WP.mono (pairs 2 (by decide) (by omega) (upd h₂ d₂)) fun t₃ h₃ => ?_)
  refine unlessRate_ok (vt h₃.2) (by decide) (fun u x e d => by rw [e]; exact upd h₃ d) fun u₃ x₃ n₃ d₃ => ?_
  refine WP.seq (WP.mono (one (by decide) (by omega) (upd h₃ d₃)) fun t₄ h₄ => ?_)
  refine unlessRate_ok (vt h₄.2) (by decide) (fun u x e d => by rw [e]; exact upd h₄ d) fun u₄ x₄ n₄ d₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pairs 1 (by decide) (by omega) (upd h₄ d₄)) fun t₅ h₅ => ?_
  have e : r.toNat = 168 := by omega
  rw [e]
  exact one (i := 20) (by decide) (by omega) h₅

/-! ## The loop -/

/-- Before block `k`. -/
structure LInv (o : State) (k : Nat) (s : State) : Prop where
  ctx : In o s (o.gpr .x4)
  one : One s (absorbed (rt o) o.mem (o.gpr .x2) (stateAt o.mem (o.gpr .x0)) k)
  gpr : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x9 → r ≠ .x10 → r ≠ .x16 → r ≠ .x17 → s.gpr r = o.gpr r
  x2 : s.gpr .x2 = o.gpr .x2 + BitVec.ofNat 64 (rt o * k)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (ln o - rt o * k)

theorem step_ok {o : State} (hp : blocksK.pre o) {k : Nat} {s : State} (hI : LInv o k s) (hk : rt o * k + rt o ≤ ln o) :
    WP isa absorbStep s fun t => LInv o (k + 1) t ∧
      t.gpr .x9 = (BitVec.ofNat 64 (ln o - rt o * (k + 1)) - o.gpr .x1) >>> 63 := by
  have hb := rt_bounds hp
  obtain ⟨hrd, hwr, d1, d2, d3, hrt, -⟩ := hp
  have hln : ln o < 2 ^ 64 := (o.gpr .x3).isLt
  have hmul : rt o * (k + 1) = rt o * k + rt o := by rw [Nat.mul_add, Nat.mul_one]
  have hdata : ∀ i n, 8 * i + n ≤ rt o → (⟨o.gpr .x2, ln o⟩ : Region).Contains
      (laneAddr (o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) i) n := fun i n hi => by
    rw [laneAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  have hr1 : s.gpr .x1 = o.gpr .x1 := hI.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  unfold absorbStep
  refine WP.seq (WP.mono (xorBlock_ok hrt (m := o.mem) hr1 hI.one hI.x2
    (fun i n hi => ⟨⟨o.gpr .x2, ln o⟩, by simp [hI.ctx.rd, hrd], hdata i n hi⟩)
    fun i hi => hI.ctx.frame.readW (hdata i 8 hi) (by simpa using d3) (by decide)) fun s₁ ⟨l₁, w₁⟩ => ?_)
  have ctx₁ : In o s₁ (o.gpr .x4) := ⟨hI.ctx.table.frame (rs := []) (by rw [w₁.mem]; exact Frame.refl _ _)
      (fun r hr => absurd hr (List.not_mem_nil)) w₁.rd w₁.wr, by rw [w₁.mem]; exact hI.ctx.saved,
    by rw [w₁.mem]; exact hI.ctx.frame, w₁.rd.trans hI.ctx.rd, w₁.wr.trans hI.ctx.wr, w₁.sp.trans hI.ctx.sp⟩
  have g₁ : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x9 → r ≠ .x10 → r ≠ .x16 → r ≠ .x17 → s₁.gpr r = o.gpr r :=
    fun r a b c d e f => (w₁.gpr r c d).trans (hI.gpr r a b c d e f)
  obtain ⟨B, hB⟩ := l₁.pairs
  refine WP.seq (WP.mono (rounds_ok hB (by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ctx₁.table)) fun s₂ ⟨k₂, p₂⟩ => ?_)
  refine wp_add fun s₃ u₃ => wp_sub fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_lsr (by decide) fun s₆ u₆ => wp_nil ?_
  have ctx₂ := ctx₁.core k₂
  have g₂ : ∀ r, r ≠ .x2 → r ≠ .x3 → r ≠ .x9 → r ≠ .x10 → r ≠ .x16 → r ≠ .x17 → s₂.gpr r = o.gpr r :=
    fun r a b c d e f => (k₂.gpr r e f).trans (g₁ r a b c d e f)
  have x1 : s₂.gpr .x1 = BitVec.ofNat 64 (rt o) := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [rt]
  have x2 : s₂.gpr .x2 = o.gpr .x2 + BitVec.ofNat 64 (rt o * k) := by
    rw [k₂.gpr _ (by decide) (by decide), w₁.gpr _ (by decide) (by decide), hI.x2]
  have x3 : s₂.gpr .x3 = BitVec.ofNat 64 (ln o - rt o * k) := by
    rw [k₂.gpr _ (by decide) (by decide), w₁.gpr _ (by decide) (by decide), hI.x3]
  have v : s₆.v = s₂.v := by rw [u₆.vec, u₅.vec, u₄.vec, u₃.vec]
  have m : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have rd : s₆.rd = s₂.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd]
  have wr : s₆.wr = s₂.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr]
  have sp : s₆.sp = s₂.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp]
  have y3 : s₄.gpr .x3 = BitVec.ofNat 64 (ln o - rt o * (k + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), x3, x1, sub_ofNat (by omega)]
    congr 1; omega
  refine ⟨⟨⟨ctx₂.table.frame (rs := []) (by rw [m]; exact Frame.refl _ _) (fun r hr => absurd hr (List.not_mem_nil)) rd wr,
    by rw [m]; exact ctx₂.saved, by rw [m]; exact ctx₂.frame, rd.trans ctx₂.rd, wr.trans ctx₂.wr, sp.trans ctx₂.sp⟩,
    fun i hi => ?_, fun r a b c d e f => ?_, ?_, ?_⟩, ?_⟩
  · rw [v, absorbed_succ, show bytesAt o.mem (o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) (rt o) =
        bytesAt o.mem (o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) (8 * (rt o / 8)) by rw [show 8 * (rt o / 8) = rt o by omega],
      ← xorWords_eq]
    exact one_of_pairs p₂ i hi
  · rw [u₆.other _ c, u₅.other _ c, u₄.other _ b, u₃.other _ a]; exact g₂ r a b c d e f
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, x2, x1, hmul, BitVec.ofNat_add,
      ← BitVec.add_assoc]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), y3]
  · rw [u₆.gpr, u₅.gpr, y3, u₄.other _ (by decide), u₃.other _ (by decide),
      g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

theorem absorbBlocks_ok (o : State) (hp : blocksK.pre o) :
    WP isa absorbBlocks o fun t => abiPreserved o t ∧ blocksK.post o t := by
  have hb := rt_bounds hp
  have hpre := hp
  obtain ⟨hrd, hwr, d1, d2, d3, hrt, hle⟩ := hp
  have hs : Space o (o.gpr .x4) := ⟨fun k n h => ⟨⟨o.gpr .x0, 200⟩, by simp [hwr], Offset.contains_base _ h (by omega)⟩,
    fun k n h => ⟨⟨o.gpr .x4, 512⟩, by simp [hwr], Offset.contains_base _ h (by omega)⟩, d1⟩
  unfold absorbBlocks
  refine WP.seq (WP.mono (enter_ok (by decide) hs) fun t₁ ⟨i₁, l₁, g₁⟩ => ?_)
  have hI : LInv o 0 t₁ := ⟨i₁, l₁, fun r _ _ _ _ h _ => g₁ r h, by rw [g₁ _ (by decide)]; simp, by
    rw [g₁ _ (by decide)]; simp [ln]⟩
  let Q : State → Prop := fun s => ∃ k, 0 < k ∧ rt o * k ≤ ln o ∧ LInv o k s
  refine WP.seq (WP.mono (Q := Q) ?_ fun t₂ ⟨k, hk0, hk, hL⟩ => ?_)
  · refine WP.loop (M := isa) (fun n s => ∃ k, n = ln o - rt o * k ∧ rt o * k + rt o ≤ ln o ∧ LInv o k s) ?_ (ln o) t₁
      ⟨0, by simp, by simpa using hle, hI⟩
    rintro n s ⟨k, rfl, hk, hL⟩
    have hmul : rt o * (k + 1) = rt o * k + rt o := by rw [Nat.mul_add, Nat.mul_one]
    refine WP.mono (step_ok hpre hL hk) fun t ⟨hL', hx⟩ => ?_
    have hz : isa.eval (.zero .x .x9) t = some ((BitVec.ofNat 64 (ln o - rt o * (k + 1)) - o.gpr .x1) >>> 63 == 0) := by
      show VG.AArch64.eval (.zero .x .x9) t = _
      rw [eval_zero, hx]
    by_cases h0 : (BitVec.ofNat 64 (ln o - rt o * (k + 1)) - o.gpr .x1) >>> 63 = 0
    · have hln : ln o < 2 ^ 64 := (o.gpr .x3).isLt
      have : rt o ≤ (BitVec.ofNat 64 (ln o - rt o * (k + 1))).toNat := sign_sub _ _ hb.2.1 h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact .inr ⟨by rw [hz, h0]; rfl, ln o - rt o * (k + 1), by omega, k + 1, rfl, by omega, hL'⟩
    · exact .inl ⟨by rw [hz, beq_eq_false_iff_ne.mpr h0], k + 1, by omega, by omega, hL'⟩
  · rw [List.append_assoc]
    refine exit_ok (by decide) hs hL.ctx hL.one (hL.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hL.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) fun t₃ a₃ g₃ sp₃ v₃ =>
      wp_addImm (by decide) fun t₄ u₄ => wp_nil ⟨⟨fun r hr => ?_, u₄.sp.trans sp₃, fun r hr => by rw [u₄.vec, v₃ r hr]⟩,
        k, hk0, hk, ?_, by rw [u₄.mem, a₃]⟩
    · have hn := preserved_ne r hr
      rw [u₄.other r hn.2.2.1, g₃ r hn.1]
      exact hL.gpr r hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2.1 hn.2.2.2.2.2.2 hn.1 hn.2.1
    · rw [u₄.gpr, g₃ _ (by decide), hL.x3]; simp

end VG.Proof.Sha3.AArch64.Sha3.Vector
