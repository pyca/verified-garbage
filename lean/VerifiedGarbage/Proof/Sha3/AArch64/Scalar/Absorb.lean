module

public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Permute
public import VerifiedGarbage.Proof.Sha3.AArch64.Blocks
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce

/-! # Keccak-f[1600] on AArch64, in general registers: absorbing blocks -/

-- separate module: a proof of its own function, which `Permute.lean`'s callers do not need

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Scalar

open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar
open VG.Proof.Sha3.AArch64 VG.Proof.Sha3.AArch64.Blocks
open VG.Spec.Sha3 (keccakF stateAt bytesAt xorBytes rates)
open VG.Proof.Sha3 (laneAddr)

theorem wp_eorRor {d n m : Reg} {k : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (h : ∀ t, Upd s t d (s.gpr n ^^^ (s.gpr m).rotateRight (k % 64)) → WP isa (.block is) t Q) :
    WP isa (.block (eor d n m k :: is)) s Q := by
  unfold eor
  split
  · rename_i h0
    exact wp_eor fun t u => h t (by rw [h0, rotr_zero]; exact u)
  · refine WP.cons (s' := s.write .x d (s.gpr n ^^^ (s.gpr m).rotateRight (k % 64))) ?_ (h _ (Upd.write64 _ _ _))
    simp only [reduceExec, Size.bits, Nat.mod_lt k (show 64 > 0 by decide), ite_true, State.read, BitVec.setWidth_eq]

theorem rotr_xor (a b : BitVec 64) {k : Nat} (hk : k < 64) : (a ^^^ b).rotateRight k = a.rotateRight k ^^^ b.rotateRight k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hk]
  split
  · rfl
  · simp [hi]

/-- What absorbing a block's words keeps. -/
structure WKeep (s t : State) : Prop where
  x16 : t.gpr .x16 = s.gpr .x16
  mem : t.mem = s.mem
  v : t.v = s.v
  env : Env s t

theorem WKeep.refl (s : State) : WKeep s s := ⟨rfl, rfl, rfl, .refl s⟩
theorem WKeep.trans {s t u : State} (h : WKeep s t) (g : WKeep t u) : WKeep s u :=
  ⟨g.x16.trans h.x16, g.mem.trans h.mem, g.v.trans h.v, h.env.trans g.env⟩

theorem xorLanes_ok {s : State} {S : Spec.Sha3.State} {m : Mem} {p : Addr} {a b : Nat} (hab : a ≤ b) (hb : b ≤ 25)
    (hl : Lanes s (xorWords S m p a)) (h16 : s.gpr .x16 = p)
    (hin : ∀ i < b, InRegions (s.rd ++ s.wr) (laneAddr p i) 8)
    (hm : ∀ i < b, s.mem.readW (laneAddr p i) 64 = m.readW (laneAddr p i) 64) :
    WP isa (.block (xorLanes a b)) s fun t => Lanes t (xorWords S m p b) ∧ WKeep s t := by
  suffices h : ∀ k ≤ b - a, WP isa (.block ((List.range k).flatMap fun k => xorLane (a + k))) s fun t =>
      Lanes t (xorWords S m p (a + k)) ∧ WKeep s t by
    have := h (b - a) (Nat.le_refl _)
    rw [show a + (b - a) = b by omega] at this
    exact this
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨hl, .refl s⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h1, h2⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, xorLane]
    refine wp_ldr (a := laneAddr p (a + k)) ⟨by omega, by omega⟩ (by rw [h2.x16, h16])
      (by rw [h2.env.rd, h2.env.wr]; exact hin _ (by omega)) fun u d => wp_eorRor fun w e => wp_nil ⟨fun i hi => ?_, ?_⟩
    · have hn := lreg_ne (a + k) (by omega)
      by_cases hik : i = a + k
      · subst hik
        rw [reg0, e.gpr, d.gpr, d.other _ hn.2.1, h2.mem, hm _ (by omega), xorWords_get! _ _ _ _ hi,
          Nat.mod_eq_of_lt (pend_lt _ hi), pd_eq, ite_eq_left (by omega), rotr_xor _ _ (pend_lt _ hi)]
        have := h1 (a + k) hi
        rw [reg0, pd_eq, xorWords_get! _ _ _ _ hi, ite_eq_right (by omega), show S[a + k]! ^^^ (0 : BitVec 64) = S[a + k]! from BitVec.xor_zero] at this
        rw [this]
      · rw [reg0, e.other _ fun x => hik (lreg_inj i hi _ (by omega) x), d.other _ (lreg_ne i hi).2.1]
        have := h1 i hi
        rw [reg0] at this
        rw [this, xorWords_get! _ _ _ _ hi, xorWords_get! _ _ _ _ hi]
        by_cases hlt : i < a + k
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]
    · have hn := lreg_ne (a + k) (by omega)
      refine ⟨?_, ?_, ?_, (h2.env.trans (.upd d)).trans (.upd e)⟩
      · rw [e.other _ (Ne.symm hn.1), d.other _ (by decide), h2.x16]
      · rw [e.mem, d.mem, h2.mem]
      · rw [e.vec, d.vec, h2.v]

theorem unlessRate_ok {s : State} {r : BitVec 64} (hv : vdword (s.v .v0) 0 = r) {R : Nat} (hR : R < 4096) {c : Prog isa}
    {Q : State → Prop} (he : ∀ t x, r.toNat = R → Upd s t .x17 x → Q t)
    (hn : ∀ t x, r.toNat ≠ R → Upd s t .x17 x → WP isa c t Q) : WP isa (unlessRate R c) s Q := by
  unfold unlessRate
  refine WP.seq (wp_umov fun t₁ u₁ => wp_subImm (by omega) fun t₂ u₂ => wp_nil ?_)
  have u := u₁.trans u₂
  refine WP.ite (decide (r.toNat = R)) ?_ (fun hb => wp_nil (he t₂ _ (by simpa using hb) u)) (fun hb => hn t₂ _ (by simpa using hb) u)
  show VG.AArch64.eval (.zero .x .x17) t₂ = _
  rw [eval_zero, u₂.gpr, u₁.gpr, hv]
  have : r = BitVec.ofNat 64 r.toNat := by simp
  rw [this, sub_beq r.isLt (by omega), ← this]

theorem xorBlock_ok {s : State} {S : Spec.Sha3.State} {m : Mem} {p : Addr} {r : BitVec 64} (hr : r.toNat ∈ rates)
    (hv : vdword (s.v .v0) 0 = r) (hl : Lanes s S) (h16 : s.gpr .x16 = p)
    (hin : ∀ i, 8 * i + 8 ≤ r.toNat → InRegions (s.rd ++ s.wr) (laneAddr p i) 8)
    (hm : ∀ i, 8 * i + 8 ≤ r.toNat → s.mem.readW (laneAddr p i) 64 = m.readW (laneAddr p i) 64) :
    WP isa xorBlock s fun t => Lanes t (xorWords S m p (r.toNat / 8)) ∧ WKeep s t := by
  have step : ∀ {a b : Nat} {t : State}, a ≤ b → 8 * b ≤ r.toNat → b ≤ 25 → WKeep s t → Lanes t (xorWords S m p a) →
      WP isa (.block (xorLanes a b)) t fun u => Lanes u (xorWords S m p b) ∧ WKeep s u := fun hab h8 hb k h =>
    WP.mono (xorLanes_ok hab hb h (k.x16.trans h16) (fun i hi => by rw [k.env.rd, k.env.wr]; exact hin i (by omega))
      (fun i hi => by rw [k.mem]; exact hm i (by omega))) fun u h => ⟨h.1, k.trans h.2⟩
  have upd : ∀ {t u : State} {a : Nat} {x : BitVec 64}, Lanes t (xorWords S m p a) ∧ WKeep s t → Upd t u .x17 x →
      Lanes u (xorWords S m p a) ∧ WKeep s u := fun h d =>
    ⟨lanes_upd h.1 d, h.2.trans ⟨d.other _ (by decide), d.mem, d.vec, .upd d⟩⟩
  have vt : ∀ {t : State}, WKeep s t → vdword (t.v .v0) 0 = r := fun k => by rw [k.v]; exact hv
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hr
  unfold xorBlock
  refine WP.seq (WP.mono (step (a := 0) (by decide) (by omega) (by decide) (.refl s) (by rw [xorWords_zero]; exact hl)) fun t₁ h₁ => ?_)
  refine unlessRate_ok (vt h₁.2) (by decide) (fun u x e d => by rw [e]; exact upd h₁ d) fun u₁ x₁ n₁ d₁ => ?_
  have k₁ := upd h₁ d₁
  refine WP.seq (WP.mono (step (by decide) (by omega) (by decide) k₁.2 k₁.1) fun t₂ h₂ => ?_)
  refine unlessRate_ok (vt h₂.2) (by decide) (fun u x e d => by rw [e]; exact upd h₂ d) fun u₂ x₂ n₂ d₂ => ?_
  have k₂ := upd h₂ d₂
  refine WP.seq (WP.mono (step (by decide) (by omega) (by decide) k₂.2 k₂.1) fun t₃ h₃ => ?_)
  refine unlessRate_ok (vt h₃.2) (by decide) (fun u x e d => by rw [e]; exact upd h₃ d) fun u₃ x₃ n₃ d₃ => ?_
  have k₃ := upd h₃ d₃
  refine WP.seq (WP.mono (step (by decide) (by omega) (by decide) k₃.2 k₃.1) fun t₄ h₄ => ?_)
  refine unlessRate_ok (vt h₄.2) (by decide) (fun u x e d => by rw [e]; exact upd h₄ d) fun u₄ x₄ n₄ d₄ => ?_
  have k₄ := upd h₄ d₄
  have e : r.toNat = 168 := by omega
  rw [e]
  exact step (b := 21) (by decide) (by omega) (by decide) k₄.2 k₄.1

/-! ## The loop -/

/-- Before block `k`. -/
structure LInv (o : State) (k : Nat) (s : State) : Prop where
  ctx : Ctx o s
  lanes : Lanes s (absorbed (rt o) o.mem (o.gpr .x2) (stateAt o.mem (o.gpr .x0)) k)
  v29 : vdword (s.v .v29) 0 = o.gpr .x0
  v30 : vdword (s.v .v30) 0 = o.gpr .x4
  v0 : vdword (s.v .v0) 0 = o.gpr .x1
  v1 : vdword (s.v .v1) 0 = o.gpr .x2 + BitVec.ofNat 64 (rt o * k)
  v2 : vdword (s.v .v2) 0 = BitVec.ofNat 64 (ln o - rt o * k)
  frame : Frame [⟨o.gpr .x4, 512⟩] o.mem s.mem

theorem step_ok {o : State} (hp : blocksK.pre o) {k : Nat} {s : State} (hI : LInv o k s) (hk : rt o * k + rt o ≤ ln o) :
    WP isa absorbStep s fun t => LInv o (k + 1) t ∧
      t.gpr .x17 = (BitVec.ofNat 64 (ln o - rt o * (k + 1)) - o.gpr .x1) >>> 63 := by
  have hb := rt_bounds hp
  obtain ⟨hrd, hwr, d1, d2, d3, hrt, -⟩ := hp
  have hln : ln o < 2 ^ 64 := (o.gpr .x3).isLt
  have hmul : rt o * (k + 1) = rt o * k + rt o := by rw [Nat.mul_add, Nat.mul_one]
  unfold absorbStep
  refine WP.seq (wp_umov fun s₁ u₁ => wp_nil ?_)
  have hdata : ∀ i, 8 * i + 8 ≤ rt o → (⟨o.gpr .x2, ln o⟩ : Region).Contains
      (laneAddr (o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) i) 8 := fun i hi => by
    rw [laneAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega) (by omega)
  have hmem : ∀ i, 8 * i + 8 ≤ rt o → s₁.mem.readW (laneAddr (o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) i) 64 =
      o.mem.readW (laneAddr (o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) i) 64 := fun i hi => by
    rw [u₁.mem]
    exact hI.frame.readW (hdata i hi) (by simpa using d3) (by decide)
  refine WP.seq (WP.mono (xorBlock_ok hrt (m := o.mem) (by rw [u₁.vec]; exact hI.v0) (lanes_upd hI.lanes u₁)
    (p := o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) (by rw [u₁.gpr, hI.v1])
    (fun i hi => ⟨⟨o.gpr .x2, ln o⟩, by simp [u₁.rd, hI.ctx.env.rd, hrd], hdata i hi⟩) hmem) fun s₂ ⟨l₂, w₂⟩ => ?_)
  have v₂ : s₂.v = s.v := by rw [w₂.v, u₁.vec]
  have c₂ : Ctx o s₂ := (hI.ctx.upd u₁).ofV w₂.v w₂.env
  refine WP.seq (wp_umov fun s₃ u₃ => wp_umov fun s₄ u₄ => wp_add fun s₅ u₅ => wp_dup fun s₆ u₆ => wp_umov fun s₇ u₇ => wp_nil ?_)
  have l₇ : Lanes s₇ _ := lanes_upd (fun i hi => by
    rw [u₆.gpr]; exact (lanes_upd (lanes_upd (lanes_upd l₂ u₃) u₄) u₅ : Lanes s₅ _) i hi) u₇
  have c₇ : Ctx o s₇ := (((((c₂.upd u₃).upd u₄).upd u₅).dup (by decide) u₆).upd u₇)
  have v₅ : s₅.v = s.v := by rw [u₅.vec, u₄.vec, u₃.vec, v₂]
  have hv7 : ∀ r, r ≠ .v1 → s₇.v r = s.v r := fun r hr => by rw [u₇.vec, u₆.other r hr, v₅]
  have hv1 : vdword (s₇.v .v1) 0 = o.gpr .x2 + BitVec.ofNat 64 (rt o * (k + 1)) := by
    rw [u₇.vec, u₆.v, u₅.gpr, u₄.other _ (by decide), u₃.gpr, v₂, hI.v1, u₄.gpr, u₃.vec, v₂, hI.v0, hmul, BitVec.ofNat_add,
      ← BitVec.add_assoc]
    congr 1
    simp [rt]
  have h28 : s₇.gpr .x28 = o.gpr .x4 := by rw [u₇.gpr, u₆.other _ (by decide), v₅, hI.v30]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, w₂.mem, u₁.mem]
  have hsc : ∀ j < 3, InRegions s₇.wr (s₇.gpr .x28 + BitVec.ofNat 64 (8 * j)) 8 := fun j hj => by
    rw [h28, c₇.env.wr, hwr]
    exact ⟨⟨o.gpr .x4, 512⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.seq (callCore_ok l₇ hsc fun s₈ l₈ k₈ => ?_)
  refine wp_umov fun s₉ u₉ => wp_umov fun s₁₀ u₁₀ => wp_sub fun s₁₁ u₁₁ => wp_dup fun s₁₂ u₁₂ => wp_sub fun s₁₃ u₁₃ =>
    wp_lsr (by decide) fun s₁₄ u₁₄ => wp_nil ?_
  have hv8 : ∀ r, r ≠ .v1 → r ≠ .v27 → r ≠ .v28 → s₈.v r = s.v r := fun r h1 h2 h3 => by rw [k₈.v r h2 h3, hv7 r h1]
  have hx16 : s₁₁.gpr .x16 = BitVec.ofNat 64 (ln o - rt o * (k + 1)) := by
    rw [u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, u₁₀.gpr, u₉.vec, hv8 _ (by decide) (by decide) (by decide),
      hv8 _ (by decide) (by decide) (by decide), hI.v2, hI.v0]
    have : o.gpr .x1 = BitVec.ofNat 64 (rt o) := by simp [rt]
    rw [this, sub_ofNat (by omega)]
    congr 1; omega
  have vf : ∀ r, r ≠ .v2 → s₁₄.v r = s₈.v r := fun r hr => by
    rw [u₁₄.vec, u₁₃.vec, u₁₂.other r hr, u₁₁.vec, u₁₀.vec, u₉.vec]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact ((((((c₇.core k₈).upd u₉).upd u₁₀).upd u₁₁).dup (by decide) u₁₂).upd u₁₃).upd u₁₄
  · rw [absorbed_succ, show bytesAt o.mem (o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) (rt o) =
        bytesAt o.mem (o.gpr .x2 + BitVec.ofNat 64 (rt o * k)) (8 * (rt o / 8)) by rw [show 8 * (rt o / 8) = rt o by omega],
      ← xorWords_eq]
    exact lanes_upd (lanes_upd (fun i hi => by
      rw [u₁₂.gpr]; exact (lanes_upd (lanes_upd (lanes_upd l₈ u₉) u₁₀) u₁₁ : Lanes s₁₁ _) i hi) u₁₃) u₁₄
  · rw [vf _ (by decide), hv8 _ (by decide) (by decide) (by decide), hI.v29]
  · rw [vf _ (by decide), hv8 _ (by decide) (by decide) (by decide), hI.v30]
  · rw [vf _ (by decide), hv8 _ (by decide) (by decide) (by decide), hI.v0]
  · rw [vf _ (by decide), k₈.v _ (by decide) (by decide), hv1]
  · rw [u₁₄.vec, u₁₃.vec, u₁₂.v, hx16]
  · have e : s₁₄.mem = s₈.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
    have f := k₈.frame
    rw [h28, m₇] at f
    rw [e]
    exact hI.frame.trans (f.sub fun r hr => ⟨⟨o.gpr .x4, 512⟩, by simp, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩)
  · rw [u₁₄.gpr, u₁₃.gpr, u₁₂.gpr, hx16, u₁₁.other _ (by decide), u₁₀.gpr, u₉.vec, hv8 _ (by decide) (by decide) (by decide), hI.v0]

theorem absorbBlocks_ok (o : State) (hp : blocksK.pre o) :
    WP isa absorbBlocks o fun t => abiPreserved o t ∧ blocksK.post o t := by
  have hb := rt_bounds hp
  have hpre := hp
  obtain ⟨hrd, hwr, d1, d2, d3, hrt, hle⟩ := hp
  have inS : ∀ i < 25, InRegions o.wr (o.gpr .x0 + BitVec.ofNat 64 (8 * i + 0)) 8 := fun i hi =>
    ⟨⟨o.gpr .x0, 200⟩, by simp [hwr], Offset.contains_base _ (by omega) (by omega)⟩
  unfold absorbBlocks
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (enter_ok o) fun t₁ ⟨c₁, g₁, m₁⟩ => ?_
  refine wp_dup fun t₂ d₂ => wp_dup fun t₃ d₃ => wp_dup fun t₄ d₄ => wp_dup fun t₅ d₅ => wp_dup fun t₆ d₆ => wp_umov fun t₇ d₇ => ?_
  have c₇ : Ctx o t₇ := (((((c₁.dup (by decide) d₂).dup (by decide) d₃).dup (by decide) d₄).dup (by decide) d₅).dup (by decide) d₆).upd d₇
  have m₇ : t₇.mem = o.mem := by rw [d₇.mem, d₆.mem, d₅.mem, d₄.mem, d₃.mem, d₂.mem, m₁]
  have x16 : t₇.gpr .x16 = o.gpr .x0 := by
    rw [d₇.gpr, d₆.other _ (by decide), d₅.other _ (by decide), d₄.other _ (by decide), d₃.other _ (by decide), d₂.v, g₁]
  refine WP.mono (load_ok (s := t₇) (stride := 8) (off := 0) (A := stateAt o.mem (o.gpr .x0)) b16 rfl rfl (by decide) (by decide)
    (fun i hi => ?_) (fun i hi => ?_)) fun t₈ ⟨l₈, h₈⟩ => ?_
  · obtain ⟨R, hR, hc⟩ := inS i hi
    rw [x16]
    exact ⟨R, List.mem_append_right _ (by rw [c₇.env.wr]; exact hR), hc⟩
  · rw [x16, m₇, ← stateFrom_stateAt, stateFrom_get _ _ _ _ hi]
  have hI : LInv o 0 t₈ := by
    refine ⟨c₇.ofV h₈.v h₈.env, l₈, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h₈.v, d₇.vec, d₆.other _ (by decide), d₅.other _ (by decide), d₄.other _ (by decide), d₃.other _ (by decide), d₂.v, g₁]
    · rw [h₈.v, d₇.vec, d₆.other _ (by decide), d₅.other _ (by decide), d₄.other _ (by decide), d₃.v, d₂.gpr, g₁]
    · rw [h₈.v, d₇.vec, d₆.other _ (by decide), d₅.other _ (by decide), d₄.v, d₃.gpr, d₂.gpr, g₁]
    · rw [h₈.v, d₇.vec, d₆.other _ (by decide), d₅.v, d₄.gpr, d₃.gpr, d₂.gpr, g₁]; simp
    · rw [h₈.v, d₇.vec, d₆.v, d₅.gpr, d₄.gpr, d₃.gpr, d₂.gpr, g₁]; simp [ln]
    · rw [h₈.mem, m₇]; exact Frame.refl _ _
  let Q : State → Prop := fun s => ∃ k, 0 < k ∧ rt o * k ≤ ln o ∧ LInv o k s
  refine WP.seq (WP.mono (Q := Q) ?_ fun t₉ ⟨k, hk0, hk, hL⟩ => ?_)
  · refine WP.loop (M := isa) (fun n s => ∃ k, n = ln o - rt o * k ∧ rt o * k + rt o ≤ ln o ∧ LInv o k s) ?_ (ln o) t₈
      ⟨0, by simp, by simpa using hle, hI⟩
    rintro n s ⟨k, rfl, hk, hL⟩
    have hmul : rt o * (k + 1) = rt o * k + rt o := by rw [Nat.mul_add, Nat.mul_one]
    refine WP.mono (step_ok hpre hL hk) fun t ⟨hL', hx⟩ => ?_
    have hz : isa.eval (.zero .x .x17) t = some ((BitVec.ofNat 64 (ln o - rt o * (k + 1)) - o.gpr .x1) >>> 63 == 0) := by
      show VG.AArch64.eval (.zero .x .x17) t = _
      rw [eval_zero, hx]
    by_cases h0 : (BitVec.ofNat 64 (ln o - rt o * (k + 1)) - o.gpr .x1) >>> 63 = 0
    · have hln : ln o < 2 ^ 64 := (o.gpr .x3).isLt
      have : rt o ≤ (BitVec.ofNat 64 (ln o - rt o * (k + 1))).toNat := sign_sub _ _ hb.2.1 h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact .inr ⟨by rw [hz, h0]; rfl, ln o - rt o * (k + 1), by omega, k + 1, rfl, by omega, hL'⟩
    · exact .inl ⟨by rw [hz, beq_eq_false_iff_ne.mpr h0], k + 1, by omega, by omega, hL'⟩
  · simp only [List.cons_append, List.nil_append]
    refine wp_umov fun t₁₀ u₁₀ => ?_
    rw [WP.block_append_iff]
    have x16' : t₁₀.gpr .x16 = o.gpr .x0 := by rw [u₁₀.gpr, hL.v29]
    have c₁₀ := hL.ctx.upd u₁₀
    have hlt := lanes_upd hL.lanes u₁₀
    have hin : ∀ i < 25, InRegions t₁₀.wr (t₁₀.gpr .x16 + BitVec.ofNat 64 (8 * i + 0)) 8 := fun i hi => by
      rw [x16', c₁₀.env.wr]; exact inS i hi
    have st := store_ok (s := t₁₀) b16 (stride := 8) (off := 0) rfl rfl (by decide) (by decide) (by decide) hlt hin
    refine WP.mono st fun t₁₁ ⟨r₁₁, f₁₁, g₁₁, v₁₁, e₁₁⟩ => ?_
    rw [x16'] at r₁₁
    have hA := eq_stateFrom r₁₁
    rw [stateFrom_stateAt] at hA
    rw [WP.block_append_iff]
    refine WP.mono (exit_ok (c₁₀.ofV v₁₁ e₁₁)) fun t₁₂ h₁₂ => wp_umov fun t₁₃ u₁₃ => wp_nil ?_
    obtain ⟨⟨a1, a2, a3⟩, m₁₂, v₁₂, e₁₂, _⟩ := h₁₂
    refine ⟨⟨fun r hr => ?_, u₁₃.sp.trans a2, fun r hr => by rw [u₁₃.vec]; exact a3 r hr⟩, k, hk0, hk, ?_, ?_⟩
    · rw [u₁₃.other r (by rintro rfl; exact absurd hr (by decide))]; exact a1 r hr
    · rw [u₁₃.gpr, v₁₂, v₁₁, u₁₀.vec, hL.v2]
    · rw [u₁₃.mem, m₁₂, hA]

end VG.Proof.Sha3.AArch64.Scalar
