module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.LevelsBase
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.SlhDsa.Lemmas

-- separate module: the groups, built in parallel with the scan (`LevelsScan`).

/-!
# SLH-DSA on AArch64: `levels`, the groups of four nodes

As on x86-64 (`Proof/SlhDsa/X86_64/LevelsLane.lean`, `LevelsLevel.lean`,
`LevelsGroup.lean`): lane `k` of the lanes `A` set up for node `j + k` of
height `z + 1` (`lane_ok`): its address's type, key pair, height and index,
and its message, the two nodes below it; the four lanes (`lanes_ok`), the
call of `thash4` on them and the copy of its outputs to the nodes
(`group_ok`), and the loop of the groups of a height (`level_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Levels

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks VG.Proof.SlhDsa.AArch64.Wots4
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64

variable {p : Params} {σ : State} {S AU : Addr} {idx c h z₀ : Nat} {pkSeed a16 : List Byte}

/-! ## A lane -/

/-- The fields and message of lane `k` of `A`. -/
abbrev lR (p : Params) (S : Addr) (k : Nat) : Region := ⟨at' S (Layout.laneA k + p.n + 16), 16 + 2 * p.n⟩

theorem lR_mem (S AU : Addr) (c h : Nat) {k : Nat} (hk : k < 4) : lR p S k ∈ lch p S AU c h := by
  simp only [lch, levelsChanges, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inl (Or.inl ⟨k, hk, rfl⟩)

/-- Lane `k` of `A`: the type `ty`, key pair `κ`, height `z`, index `x`, message `M`. -/
structure LaneL (p : Params) (m : Mem) (S : Addr) (k ty κ z x : Nat) (M : List Byte) : Prop where
  f16 : la p m S k 16 4 = toByte ty 4
  f20 : la p m S k 20 4 = toByte κ 4
  f24 : la p m S k 24 4 = toByte z 4
  f28 : la p m S k 28 4 = toByte x 4
  msg : la p m S k 32 (2 * p.n) = M

theorem lR_sub (_hz : Sz p) {S : Addr} {k o l : Nat} (h₁ : 16 ≤ o) (h₂ : o + l ≤ 2 * p.n + 32) :
    Region.Sub ⟨at' S (Layout.laneA k + p.n + o), l⟩ (lR p S k) := by
  have e : at' S (Layout.laneA k + p.n + o) = at' S (Layout.laneA k + p.n + 16) + BitVec.ofNat 64 (o - 16) := by
    rw [ofNat_add', show Layout.laneA k + p.n + 16 + (o - 16) = Layout.laneA k + p.n + o by omega_using [h₁]]
  rw [e]; exact Offset.sub_base _ (by omega_using [h₁, h₂])

theorem lR_frame (S : Addr) {k : Nat} (hk : k < 4) (hz : Sz p) : Region.Disjoint (frameR S) (lR p S k) := by
  have hn := hz.n32
  exact Entry.dscr (Or.inl (by rw [laneA_eq]; omega_using [])) (by decide) (by rw [laneA_eq]; omega_using [hk, hn])

/-- A range of lane `k₂` that a change of a range of lane `k₁` leaves. -/
theorem ll_keep (hz : Sz p) {m m' : Mem} {S : Addr} {k₁ o₁ l₁ k₂ o₂ l₂ : Nat}
    (hf : Frame [⟨at' S (Layout.laneA k₁ + p.n + o₁), l₁⟩] m m') (hk₁ : k₁ < 4) (hk₂ : k₂ < 4)
    (h₁ : 16 ≤ o₁) (h₁' : o₁ + l₁ ≤ 2 * p.n + 32) (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ 2 * p.n + 32)
    (h : k₁ ≠ k₂ ∨ o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) : la p m' S k₂ o₂ l₂ = la p m S k₂ o₂ l₂ := by
  have hn := hz.n32
  exact keepScr hf (by rw [laneA_eq, laneA_eq]; omega_using [h, hk₁, hk₂, h₁, h₁', h₂, h₂', hn])
    (by rw [laneA_eq]; omega_using [hk₁, h₁', hn]) (by rw [laneA_eq]; omega_using [hk₂, h₂', hn])

theorem readW32_toNat {m : Mem} {a : Addr} (h : (m.readW a 64).toNat < 2 ^ 32) :
    ((m.readW a 32).setWidth 64).toNat = (m.readW a 64).toNat := by
  rw [← readW64_lo, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.mod_eq_of_lt (by omega_using [h]), Nat.mod_eq_of_lt (by omega_using [h])]

theorem nodeLane_eq (L : Layout) (k : Nat) : Tree.nodeLane L k =
    ([.ldr .w .x13 .x19 (Tree.var 2)] : List Instr) ++ setFieldR .x19 (Layout.laneA k + L.n + 16) .x13 ++
    ([.ldr .w .x13 .x19 (Tree.var 3)] : List Instr) ++ setFieldR .x19 (Layout.laneA k + L.n + 20) .x13 ++
    setFieldR .x19 (Layout.laneA k + L.n + 24) .x10 ++
    ([.addImm .x .x13 .x11 k] : List Instr) ++ setFieldR .x19 (Layout.laneA k + L.n + 28) .x13 ++
    copyWords .x19 (Layout.laneA k + L.n + 32) .x12 (2 * L.n * k) (2 * L.n / 8) := by
  simp only [Tree.nodeLane, Layout.adrsOff, Layout.msgOff, Nat.add_assoc]

/-- A field of lane `k` set from a register below `2³²`, with `Base`. -/
theorem fieldL_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {t : State} (hb : Base hE t)
    {k o : Nat} (hk : k < 4) (ho : o = 16 ∨ o = 20 ∨ o = 24 ∨ o = 28) {r : Reg} (hr : (t.gpr r).toNat < 2 ^ 32)
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ t', Base hE t' → (∀ g, g ≠ .x9 → t'.gpr g = t.gpr g) →
      la p t'.mem S k o 4 = toByte (t.gpr r).toNat 4 → Frame [⟨at' S (Layout.laneA k + p.n + o), 4⟩] t.mem t'.mem →
      WP isa (.block is) t' Q) :
    WP isa (.block (setFieldR .x19 (Layout.laneA k + p.n + o) r ++ is)) t Q := by
  have hn := hz.n32
  have h8 := hz.n8
  have hoo : 16 ≤ o ∧ o ≤ 28 ∧ o % 4 = 0 := by rcases ho with rfl | rfl | rfl | rfl <;> decide
  have hlt : Layout.laneA k + p.n + o + 4 ≤ 16384 := by rw [laneA_eq]; omega_using [hk, hn, hoo]
  refine setFieldR_ok (by decide) ⟨by rw [laneA_eq]; omega_using [h8, hoo], by omega_using [hlt]⟩ hr
    (by rw [hb.x19]; exact hE.inScr hb.wr (by omega_using [hlt])) fun t' f => ?_
  rw [hb.x19] at f
  exact kk t' (hb.ofFrame f.rd f.wr f.sp (fun g hg => f.gpr g (by rcases lr_mem hg with rfl | rfl | rfl <;> decide))
      f.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, lR_mem S AU c h hk, lR_sub hz hoo.1 (by omega_using [hoo, hn])⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (lR_frame S hk hz).sub_right (lR_sub hz hoo.1 (by omega_using [hoo, hn]))))
    f.gpr f.bytes f.frame

/-- Lane `k` for the node `x + k` of height `z` (`x10`; `x` in `x11`), its
message the `2n` bytes at `x12 + 2nk`, `x12 = S + b` among the nodes. -/
theorem lane_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {k z x b : Nat} {t : State}
    (hk : k < 4) (hb : Base hE t) (h10 : t.gpr .x10 = BitVec.ofNat 64 z) (hz32 : z < 2 ^ 32)
    (h11 : t.gpr .x11 = BitVec.ofNat 64 x) (hx : x + k < 2 ^ 32) (h12 : t.gpr .x12 = at' S b)
    (hb₁ : Layout.oN ≤ b) (hb₂ : b + 2 * p.n * k + 2 * p.n ≤ 65536) :
    WP isa (.block (Tree.nodeLane ⟨p.n, p.len⟩ k)) t fun t' => Base hE t' ∧
      (∀ g, g ≠ .x9 → g ≠ .x13 → g ≠ .x14 → t'.gpr g = t.gpr g) ∧
      LaneL p t'.mem S k (tyA σ S) (kpA σ S) z (x + k) (bytesAt t.mem (at' S (b + 2 * p.n * k)) (2 * p.n)) ∧
      Frame [lR p S k] t.mem t'.mem := by
  have hn := hz.n32
  have h8 := hz.n8
  rw [nodeLane_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have v2 : t.mem.readW (at' S (Layout.oVar 3 2)) 64 = varAt σ.mem S 3 2 := hb.vars 2 (by decide)
  have v3 : t.mem.readW (at' S (Layout.oVar 3 3)) 64 = varAt σ.mem S 3 3 := hb.vars 3 (by decide)
  refine wp_ldrw (a := at' S (Layout.oVar 3 2)) ⟨by decide, by decide⟩ (by rw [hb.x19]; rfl)
    (hE.inScr' hb.wr (by rw [oVar3_eq]; omega_using [])) fun t₁ u₁ => ?_
  have hb₁' : Base hE t₁ := hb.regs u₁.mem u₁.rd u₁.wr u₁.sp fun r hr => u₁.other _ (by
    rcases lr_mem hr with rfl | rfl | rfl <;> decide)
  have hty : (t₁.gpr .x13).toNat = tyA σ S := by rw [u₁.gpr, readW32_toNat (by rw [v2]; exact hE.v2), v2]
  refine fieldL_ok hE hz hb₁' hk (o := 16) (by decide) (by rw [hty]; exact hE.v2) fun t₂ b₂ g₂ y₂ f₂ => ?_
  rw [hty] at y₂
  refine wp_ldrw (a := at' S (Layout.oVar 3 3)) ⟨by decide, by decide⟩ (by rw [b₂.x19]; rfl)
    (hE.inScr' b₂.wr (by rw [oVar3_eq]; omega_using [])) fun t₃ u₃ => ?_
  have hb₃ : Base hE t₃ := b₂.regs u₃.mem u₃.rd u₃.wr u₃.sp fun r hr => u₃.other _ (by
    rcases lr_mem hr with rfl | rfl | rfl <;> decide)
  have hkp : (t₃.gpr .x13).toNat = kpA σ S := by
    rw [u₃.gpr, readW32_toNat (by rw [b₂.vars 3 (by decide)]; exact hE.v3), b₂.vars 3 (by decide)]; rfl
  refine fieldL_ok hE hz hb₃ hk (o := 20) (by decide) (by rw [hkp]; exact hE.v3) fun t₄ b₄ g₄ y₄ f₄ => ?_
  rw [hkp] at y₄
  have h10₄ : t₄.gpr .x10 = BitVec.ofNat 64 z := by
    rw [g₄ _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), u₁.other _ (by decide), h10]
  have hzv : (t₄.gpr .x10).toNat = z := by rw [h10₄, BitVec.toNat_ofNat]; omega_using [hz32]
  refine fieldL_ok hE hz b₄ hk (o := 24) (by decide) (by rw [hzv]; exact hz32) fun t₅ b₅ g₅ y₅ f₅ => ?_
  rw [hzv] at y₅
  refine wp_addImm (by omega_using [hk]) fun t₆ u₆ => ?_
  have hb₆ : Base hE t₆ := b₅.regs u₆.mem u₆.rd u₆.wr u₆.sp fun r hr => u₆.other _ (by
    rcases lr_mem hr with rfl | rfl | rfl <;> decide)
  have hxv : (t₆.gpr .x13).toNat = x + k := by
    rw [u₆.gpr, g₅ _ (by decide), g₄ _ (by decide), u₃.other _ (by decide), g₂ _ (by decide), u₁.other _ (by decide),
      h11, ← BitVec.ofNat_add, BitVec.toNat_ofNat]; omega_using [hx]
  refine fieldL_ok hE hz hb₆ hk (o := 28) (by decide) (by rw [hxv]; exact hx) fun t₇ b₇ g₇ y₇ f₇ => ?_
  rw [hxv] at y₇
  have h12₇ : t₇.gpr .x12 = at' S b := by
    rw [g₇ _ (by decide), u₆.other _ (by decide), g₅ _ (by decide), g₄ _ (by decide), u₃.other _ (by decide),
      g₂ _ (by decide), u₁.other _ (by decide), h12]
  have hw8 : 8 * (2 * p.n / 8) = 2 * p.n := by omega_using [h8]
  have hd8 : (2 * p.n * k) % 8 = 0 := by
    rw [Nat.mul_assoc, Nat.mul_comm 2, Nat.mul_assoc, Nat.mul_mod, h8, Nat.zero_mul, Nat.zero_mod]
  have hnk : 2 * p.n * k ≤ 2 * 32 * 3 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) (by omega_using [hk])
  have hdst : at' S (Layout.laneA k + p.n + 32) + BitVec.ofNat 64 0 = at' S (Layout.laneA k + p.n + 32) := add0 _
  refine WP.mono (copyWords_ok (s := t₇) (by decide) (by decide) hd8
    (by rw [laneA_eq]; omega_using [h8]) ?_ ?_ ?_ (by omega_using [hw8, hnk, hn]) (by rw [laneA_eq]; omega_using [hw8, hk, hn]))
    fun t' cp => ?_
  · rw [h12₇, hw8, ofNat_add']; exact hE.inScr' b₇.wr (by omega_using [hb₂])
  · rw [b₇.x19, hw8]; exact hE.inScr b₇.wr (by rw [laneA_eq]; omega_using [hk, hn])
  · rw [b₇.x19, h12₇, hw8, ofNat_add']
    exact Entry.dscr (Or.inl (by rw [laneA_eq]; rw [oN_eq] at hb₁; omega_using [hk, hn, hb₁]))
      (by rw [laneA_eq]; omega_using [hk, hn]) (by omega_using [hb₂])
  rw [b₇.x19, h12₇, hw8, ofNat_add'] at cp
  have fm : Frame [⟨at' S (Layout.laneA k + p.n + 32), 2 * p.n⟩] t₇.mem t'.mem := cp.frame
  have hb' : Base hE t' := b₇.ofFrame cp.rd cp.wr cp.sp (fun g hg => cp.gpr g (by rcases lr_mem hg with rfl | rfl | rfl <;> decide))
    fm (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, lR_mem S AU c h hk, lR_sub hz (by decide) (by omega_using [])⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (lR_frame S hk hz).sub_right (lR_sub hz (by decide) (by omega_using [])))
  -- the source bytes, as at `t`
  have hsrc : bytesAt t₇.mem (at' S (b + 2 * p.n * k)) (2 * p.n) = bytesAt t.mem (at' S (b + 2 * p.n * k)) (2 * p.n) := by
    have far : ∀ {m m' : Mem} {o : Nat}, 16 ≤ o → o ≤ 28 → Frame [⟨at' S (Layout.laneA k + p.n + o), 4⟩] m m' →
        bytesAt m' (at' S (b + 2 * p.n * k)) (2 * p.n) = bytesAt m (at' S (b + 2 * p.n * k)) (2 * p.n) :=
      fun h₁ h₂ hf => keepScr hf (Or.inl (by rw [laneA_eq]; rw [oN_eq] at hb₁; omega_using [hk, hn, hb₁, h₂]))
        (by rw [laneA_eq]; omega_using [hk, hn, h₂]) (by omega_using [hb₂])
    rw [far (by decide) (by decide) f₇, u₆.mem, far (by decide) (by decide) f₅, far (by decide) (by decide) f₄, u₃.mem,
      far (by decide) (by decide) f₂, u₁.mem]
  -- the fields, through the later writes
  have K := fun {m m' : Mem} {o₁ l₁ o₂ l₂ : Nat} (hf : Frame [⟨at' S (Layout.laneA k + p.n + o₁), l₁⟩] m m')
    (h₁ : 16 ≤ o₁) (h₁' : o₁ + l₁ ≤ 2 * p.n + 32) (h₂ : 16 ≤ o₂) (h₂' : o₂ + l₂ ≤ 2 * p.n + 32)
    (h : o₁ + l₁ ≤ o₂ ∨ o₂ + l₂ ≤ o₁) => ll_keep hz hf hk hk h₁ h₁' h₂ h₂' (Or.inr h)
  refine ⟨hb', fun g h₁ h₂ h₃ => ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [cp.gpr _ h₃, g₇ _ h₁, u₆.other _ h₂, g₅ _ h₁, g₄ _ h₁, u₃.other _ h₂, g₂ _ h₁, u₁.other _ h₂]
  · rw [K fm (by decide) (by omega_using []) (by decide) (by omega_using [hn]) (by omega_using []),
      K f₇ (by decide) (by omega_using [hn]) (by decide) (by omega_using [hn]) (by omega_using []), u₆.mem,
      K f₅ (by decide) (by omega_using [hn]) (by decide) (by omega_using [hn]) (by omega_using []),
      K f₄ (by decide) (by omega_using [hn]) (by decide) (by omega_using [hn]) (by omega_using []), u₃.mem]
    exact y₂
  · rw [K fm (by decide) (by omega_using []) (by decide) (by omega_using [hn]) (by omega_using []),
      K f₇ (by decide) (by omega_using [hn]) (by decide) (by omega_using [hn]) (by omega_using []), u₆.mem,
      K f₅ (by decide) (by omega_using [hn]) (by decide) (by omega_using [hn]) (by omega_using [])]
    exact y₄
  · rw [K fm (by decide) (by omega_using []) (by decide) (by omega_using [hn]) (by omega_using []),
      K f₇ (by decide) (by omega_using [hn]) (by decide) (by omega_using [hn]) (by omega_using []), u₆.mem]
    exact y₅
  · rw [K fm (by decide) (by omega_using []) (by decide) (by omega_using [hn]) (by omega_using [])]
    exact y₇
  · rw [← hsrc]; exact bytesAt_ext fun q hq => cp.bytes q hq
  · have s : ∀ {o l : Nat}, 16 ≤ o → o + l ≤ 2 * p.n + 32 → ∀ r ∈ [(⟨at' S (Layout.laneA k + p.n + o), l⟩ : Region)],
        ∃ R ∈ [lR p S k], Region.Sub r R := fun h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, lR_sub hz h₁ h₂⟩
    rw [u₁.mem] at f₂
    rw [u₃.mem] at f₄
    rw [u₆.mem] at f₇
    exact ((((f₂.sub (s (by decide) (by omega_using [hn]))).trans (f₄.sub (s (by decide) (by omega_using [hn])))).trans
      (f₅.sub (s (by decide) (by omega_using [hn])))).trans (f₇.sub (s (by decide) (by omega_using [hn])))).trans
      (fm.sub (s (by decide) (by omega_using [])))

/-! ## What `levels` never changes -/

/-- The `PK.seed` and `a16` of lane `k`, and the region of a change. -/
theorem head_disj (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {a l : Nat}
    (h₁ : Layout.oA ≤ a) (h₂ : a + l ≤ Layout.oN) (h₃ : ∀ k < 4, a + l ≤ Layout.laneA k + p.n + 16 ∨
      Layout.laneA k + p.n + 16 + (16 + 2 * p.n) ≤ a) :
    ∀ R ∈ lch p S AU c h, Region.Disjoint ⟨at' S a, l⟩ R := by
  have hn := hz.n32
  have hfit := hE.nodes_fit
  intro R hR
  simp only [lch, levelsChanges, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hR
  have ha : 3136 ≤ a := h₁
  have ha' : a + l ≤ 12480 := h₂
  rcases hR with (⟨k, hk, rfl⟩ | rfl | rfl | rfl) | rfl
  · exact Entry.dscr (h₃ k hk) (by omega_using [ha']) (by rw [laneA_eq]; omega_using [hk, hn])
  · exact Offset.disjoint_base S (by simp only [workUsed]; omega_using [ha]) (by omega_using [ha'])
  · exact Entry.dscr (Or.inr (by rw [oFrame3_eq, frameLen_eq]; omega_using [ha])) (by omega_using [ha']) (by decide)
  · exact Entry.dscr (Or.inl (by rw [oN_eq]; omega_using [ha'])) (by omega_using [ha']) (by omega_using [hfit])
  · exact (hE.reg.out_scr.sub_right (Offset.sub_base S (by rw [oSigTmp_eq]; omega_using [ha']))).symm

theorem Base.env {hE : Entry p σ S AU idx c h z₀ pkSeed a16} (hz : Sz p) {t : State} (hb : Base hE t) :
    Env p t.mem S pkSeed a16 := by
  have hn := hz.n32
  have hA : ∀ {k o l : Nat}, k < 4 → o + l ≤ p.n + 16 → bytesAt t.mem (at' S (Layout.laneA k + o)) l =
      bytesAt σ.mem (at' S (Layout.laneA k + o)) l := @fun k o l hk ho =>
    bytesAt_frame hb.frame (head_disj hE hz (by rw [laneA_eq]; simp only [Layout.oA]; omega_using [])
      (by rw [laneA_eq, oN_eq]; omega_using [hk, ho, hn]) fun k' hk' => by
        rw [laneA_eq, laneA_eq]
        rcases Nat.lt_or_ge k' k with h' | h'
        · exact Or.inr (by omega_using [h', ho, hn, hk, hk'])
        · exact Or.inl (by omega_using [h', ho, hn, hk, hk']))
      (by omega_using [ho, hn])
  have hB : ∀ {k o l : Nat}, k < 4 → o + l ≤ p.n + 16 → bytesAt t.mem (at' S (Layout.laneB k + o)) l =
      bytesAt σ.mem (at' S (Layout.laneB k + o)) l := fun hk ho =>
    bytesAt_frame hb.frame (head_disj hE hz (by rw [laneB_eq]; simp only [Layout.oA]; omega_using [])
      (by rw [laneB_eq, oN_eq]; omega_using [hk, ho, hn]) fun k' hk' => by
        rw [laneA_eq, laneB_eq]; exact Or.inr (by omega_using [hk', hn]))
      (by omega_using [ho, hn])
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have := hA (o := 0) (l := p.n) hk (by omega_using [])
    rw [Nat.add_zero] at this; rw [this]; exact hE.env.seedA k hk
  · have := hB (o := 0) (l := p.n) hk (by omega_using [])
    rw [Nat.add_zero] at this; rw [this]; exact hE.env.seedB k hk
  · rw [hA hk (by omega_using [])]; exact hE.env.adrsA k hk
  · rw [hB hk (by omega_using [])]; exact hE.env.adrsB k hk

/-! ## The four lanes -/

theorem levelLanes_eq (L : Layout) : Tree.levelLanes L =
    ([.addImm .x .x10 .x22 1, .add .x .x11 .x27 .x24, .addImm .x .x12 .x24 0] : List Instr) ++ mulN L.n .x12 .x13 ++
      ([.add .x .x12 .x12 .x12, .add .x .x12 .x12 .x20] : List Instr) ++ (List.range 4).flatMap (Tree.nodeLane L) := rfl

/-- The temporaries of the groups. -/
abbrev GT : List Reg := [.x9, .x10, .x11, .x12, .x13, .x14]

theorem gt_ne {g : Reg} (hg : g ∉ GT) (r : Reg) (hr : r ∈ GT := by decide) : g ≠ r := fun e => hg (e ▸ hr)

/-- The lanes of nodes `j` to `j + 3` of height `z + 1`. -/
theorem lanes_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {z B j : Nat} {t : State}
    (hb : Base hE t) (h22 : t.gpr .x22 = BitVec.ofNat 64 z) (hz14 : z < 14)
    (h27 : t.gpr .x27 = BitVec.ofNat 64 B) (h24 : t.gpr .x24 = BitVec.ofNat 64 j) (hB : B + j + 3 < 2 ^ 32)
    (hj : Layout.oN + 2 * j * p.n + 8 * p.n ≤ 65536) :
    WP isa (.block (Tree.levelLanes ⟨p.n, p.len⟩)) t fun t' => Base hE t' ∧ (∀ g ∉ GT, t'.gpr g = t.gpr g) ∧
      (∀ k < 4, LaneL p t'.mem S k (tyA σ S) (kpA σ S) (z + 1) (B + j + k)
        (bytesAt t.mem (at' S (Layout.oN + 2 * j * p.n + 2 * p.n * k)) (2 * p.n))) ∧
      Frame ((List.range 4).map (lR p S)) t.mem t'.mem := by
  have hn := hz.n32
  rw [levelLanes_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addImm (by decide) fun t₁ u₁ => wp_add fun t₂ u₂ => wp_addImm (by decide) fun t₃ u₃ =>
    mulN_ok hz.nv (r := .x12) (tmp := .x13) (x := j) (by decide) (by
      rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h24, add0]) fun t₄ h₄ g₄ sp₄ m₄ rd₄ wr₄ => ?_
  refine wp_add fun t₅ u₅ => wp_add fun t₆ u₆ => ?_
  have hm₆ : t₆.mem = t.mem := by rw [u₆.mem, u₅.mem, m₄, u₃.mem, u₂.mem, u₁.mem]
  have hg₆ : ∀ g ∉ GT, t₆.gpr g = t.gpr g := fun g hg => by
    rw [u₆.other _ (gt_ne hg .x12), u₅.other _ (gt_ne hg .x12), g₄ _ (gt_ne hg .x12) (gt_ne hg .x13),
      u₃.other _ (gt_ne hg .x12), u₂.other _ (gt_ne hg .x11), u₁.other _ (gt_ne hg .x10)]
  have hb₆ : Base hE t₆ := hb.regs hm₆ (by rw [u₆.rd, u₅.rd, rd₄, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, wr₄, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₆.sp, u₅.sp, sp₄, u₃.sp, u₂.sp, u₁.sp])
    fun g hg => hg₆ g (by rcases lr_mem hg with rfl | rfl | rfl <;> decide)
  have h10 : t₆.gpr .x10 = BitVec.ofNat 64 (z + 1) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide) (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, h22, ← BitVec.ofNat_add]
  have h11 : t₆.gpr .x11 = BitVec.ofNat 64 (B + j) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), g₄ _ (by decide) (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h27, h24, ← BitVec.ofNat_add]
  have h12 : t₆.gpr .x12 = at' S (Layout.oN + 2 * j * p.n) := by
    rw [u₆.gpr, u₅.gpr, h₄, u₅.other _ (by decide), g₄ _ (by decide) (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hb.x20, ← BitVec.ofNat_add, BitVec.add_comm, ofNat_add']
    congr 2; rw [Nat.mul_assoc, Nat.two_mul]
  refine WP.mono (wp_range_flatMap 4 (P := fun K u => Base hE u ∧ (∀ g, g ≠ .x9 → g ≠ .x13 → g ≠ .x14 → u.gpr g = t₆.gpr g) ∧
      (∀ k < K, LaneL p u.mem S k (tyA σ S) (kpA σ S) (z + 1) (B + j + k)
        (bytesAt t.mem (at' S (Layout.oN + 2 * j * p.n + 2 * p.n * k)) (2 * p.n))) ∧
      Frame ((List.range K).map (lR p S)) t₆.mem u.mem)
    ⟨hb₆, fun _ _ _ _ => rfl, fun _ h => absurd h (by omega_using []), by simpa using Frame.refl [] t₆.mem⟩
    fun K hK u hu => ?_) fun u hu => ?_
  · obtain ⟨hbu, hgu, hlu, hfu⟩ := hu
    refine WP.mono (lane_ok hE hz (k := K) (z := z + 1) (x := B + j) (b := Layout.oN + 2 * j * p.n) hK hbu
      (by rw [hgu _ (by decide) (by decide) (by decide), h10]) (by omega_using [hz14])
      (by rw [hgu _ (by decide) (by decide) (by decide), h11]) (by omega_using [hB, hK])
      (by rw [hgu _ (by decide) (by decide) (by decide), h12]) (by omega_using [])
      (by have : 2 * p.n * K ≤ 2 * p.n * 3 := Nat.mul_le_mul_left _ (by omega_using [hK]); omega_using [hj, this]))
      fun u' ⟨hb', hg', hl', hf'⟩ => ?_
    have hsrc : bytesAt u.mem (at' S (Layout.oN + 2 * j * p.n + 2 * p.n * K)) (2 * p.n) =
        bytesAt t.mem (at' S (Layout.oN + 2 * j * p.n + 2 * p.n * K)) (2 * p.n) := by
      have hnK : 2 * p.n * K ≤ 2 * p.n * 3 := Nat.mul_le_mul_left _ (by omega_using [hK])
      rw [← hm₆]
      exact bytesAt_frame hfu (fun r hr => by
        obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
        have := List.mem_range.mp hk'
        exact Entry.dscr (Or.inr (by rw [laneA_eq, oN_eq]; omega_using [this, hK, hn]))
          (by omega_using [hj, hnK]) (by rw [laneA_eq]; omega_using [this, hK, hn])) (by omega_using [hn])
    rw [hsrc] at hl'
    refine ⟨hb', fun g h₁ h₂ h₃ => by rw [hg' g h₁ h₂ h₃, hgu g h₁ h₂ h₃], fun k hk => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · have l := hlu k hk'
        have K' := fun {o l : Nat} (h₁ : 16 ≤ o) (h₂ : o + l ≤ 2 * p.n + 32) =>
          ll_keep hz (o₁ := 16) (l₁ := 16 + 2 * p.n) (k₁ := K) (k₂ := k) (o₂ := o) (l₂ := l) hf' hK
            (by omega_using [hk', hK]) (by decide) (by omega_using []) h₁ h₂ (Or.inl (by omega_using [hk']))
        exact ⟨by rw [K' (by decide) (by omega_using [hn])]; exact l.f16, by rw [K' (by decide) (by omega_using [hn])]; exact l.f20,
          by rw [K' (by decide) (by omega_using [hn])]; exact l.f24, by rw [K' (by decide) (by omega_using [hn])]; exact l.f28,
          by rw [K' (by decide) (by omega_using [])]; exact l.msg⟩
      · rw [show B + j + k = B + j + k from rfl]; exact hl'
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact frame_cat hfu hf'
  · obtain ⟨hbu, hgu, hlu, hfu⟩ := hu
    refine ⟨hbu, fun g hg => by rw [hgu g (gt_ne hg .x9) (gt_ne hg .x13) (gt_ne hg .x14), hg₆ g hg], hlu, ?_⟩
    rw [← hm₆]; exact hfu

/-! ## The outputs to the nodes -/

theorem levelOut_eq (L : Layout) : Tree.levelOut L =
    ([.addImm .x .x10 .x24 0] : List Instr) ++ mulN L.n .x10 .x11 ++ ([.add .x .x10 .x10 .x20] : List Instr) ++
      (List.range 4).flatMap (fun k => copyWords .x10 (L.n * k) .x19 (Layout.laneA k + L.n + 32) (L.n / 8)) ++
      ([.addImm .x .x24 .x24 4, .sub .x .x9 .x24 .x23, .lsr .x .x9 .x9 63] : List Instr) := by
  simp only [Tree.levelOut, Thash4.mov, Layout.msgOff, Nat.add_assoc]

/-- Node `j + k`'s place. -/
abbrev oR (p : Params) (S : Addr) (j k : Nat) : Region := ⟨at' S (Layout.oN + j * p.n + p.n * k), p.n⟩

theorem oR_off (n j k : Nat) : Layout.oN + j * n + n * k = Layout.oN + (j + k) * n := by
  rw [Nat.add_mul, Nat.mul_comm n k]; omega_using []

theorem node_fit (hE : Entry p σ S AU idx c h z₀ pkSeed a16) {i : Nat} (hi : i + 1 ≤ c + 8) :
    Layout.oN + i * p.n + p.n ≤ 29120 := by
  have hcap := hE.nodes_fit
  have := Nat.mul_le_mul_right p.n hi
  rw [Nat.succ_mul] at this
  omega_using [this, hcap]

/-- The outputs of the four lanes to nodes `j` to `j + 3`, and `j + 4`. -/
theorem out_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) {j P : Nat} {t : State}
    (hb : Base hE t) (h24 : t.gpr .x24 = BitVec.ofNat 64 j) (h23 : t.gpr .x23 = BitVec.ofNat 64 P)
    (hj : j + 4 ≤ c + 8) :
    WP isa (.block (Tree.levelOut ⟨p.n, p.len⟩)) t fun t' => Base hE t' ∧ (∀ g ∉ GT, g ≠ .x24 → t'.gpr g = t.gpr g) ∧
      t'.gpr .x24 = BitVec.ofNat 64 (j + 4) ∧ t'.gpr .x9 = (BitVec.ofNat 64 (j + 4) - BitVec.ofNat 64 P) >>> 63 ∧
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.oN + (j + k) * p.n)) p.n = la p t.mem S k 32 p.n) ∧
      Frame ((List.range 4).map (oR p S j)) t.mem t'.mem := by
  have hn := hz.n32
  have h8 := hz.n8
  have hcap := hE.nodes_fit
  have hjn : j * p.n + 4 * p.n ≤ (c + 8) * p.n := by rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hj
  rw [levelOut_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addImm (by decide) fun t₁ u₁ => mulN_ok hz.nv (r := .x10) (tmp := .x11) (x := j) (by decide)
    (by rw [u₁.gpr, h24, add0]) fun t₂ h₂ g₂ sp₂ m₂ rd₂ wr₂ => ?_
  refine wp_add fun t₃ u₃ => ?_
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, m₂, u₁.mem]
  have hg₃ : ∀ g, g ≠ .x10 → g ≠ .x11 → t₃.gpr g = t.gpr g := fun g h₁ h₂ => by
    rw [u₃.other _ h₁, g₂ _ h₁ h₂, u₁.other _ h₁]
  have hb₃ : Base hE t₃ := hb.regs hm₃ (by rw [u₃.rd, rd₂, u₁.rd]) (by rw [u₃.wr, wr₂, u₁.wr])
    (by rw [u₃.sp, sp₂, u₁.sp]) fun g hg => hg₃ g (by rcases lr_mem hg with rfl | rfl | rfl <;> decide)
      (by rcases lr_mem hg with rfl | rfl | rfl <;> decide)
  have h10 : t₃.gpr .x10 = at' S (Layout.oN + j * p.n) := by
    rw [u₃.gpr, h₂, u₃.other _ (by decide) |>.symm.trans (u₃.other _ (by decide)), g₂ _ (by decide) (by decide),
      u₁.other _ (by decide), hb.x20, BitVec.add_comm, ofNat_add']
  refine WP.block_append (WP.mono (wp_range_flatMap 4 (P := fun K u => Base hE u ∧
      (∀ g, g ≠ .x14 → u.gpr g = t₃.gpr g) ∧
      (∀ k < K, bytesAt u.mem (at' S (Layout.oN + (j + k) * p.n)) p.n = la p t.mem S k 32 p.n) ∧
      Frame ((List.range K).map (oR p S j)) t₃.mem u.mem)
    ⟨hb₃, fun _ _ => rfl, fun _ h => absurd h (by omega_using []), by simpa using Frame.refl [] t₃.mem⟩
    fun K hK u hu => ?_) fun u hu => ?_)
  · obtain ⟨hbu, hgu, hnu, hfu⟩ := hu
    have hw8 : 8 * (p.n / 8) = p.n := by omega_using [h8]
    have hnK : p.n * K ≤ p.n * 3 := Nat.mul_le_mul_left _ (by omega_using [hK])
    have hK8 : (p.n * K) % 8 = 0 := by rw [Nat.mul_mod, h8, Nat.zero_mul, Nat.zero_mod]
    have h10u : u.gpr .x10 = at' S (Layout.oN + j * p.n) := by rw [hgu _ (by decide), h10]
    have hdst : at' S (Layout.oN + j * p.n) + BitVec.ofNat 64 (p.n * K) = at' S (Layout.oN + (j + K) * p.n) := by
      rw [ofNat_add']; congr 2; rw [Nat.add_mul, Nat.mul_comm p.n K]; omega_using []
    have hfit : Layout.oN + (j + K) * p.n + p.n ≤ 29120 := by
      have : (j + K) * p.n + p.n ≤ j * p.n + 4 * p.n := by
        rw [Nat.add_mul]; have := Nat.mul_le_mul_right p.n (show K + 1 ≤ 4 by omega_using [hK])
        rw [Nat.add_mul, Nat.one_mul] at this; omega_using [this]
      omega_using [this, hjn, hcap]
    refine WP.mono (copyWords_ok (by decide) (by decide) (by rw [laneA_eq]; omega_using [h8]) hK8 ?_ ?_ ?_
      (by rw [laneA_eq]; omega_using [hK, hn, hw8]) (by omega_using [hnK, hn, hw8])) fun u' cp => ?_
    · rw [hbu.x19, hw8]; exact hE.inScr' hbu.wr (by rw [laneA_eq]; omega_using [hK, hn])
    · rw [h10u, hdst, hw8]; exact hE.inScr hbu.wr (by omega_using [hfit])
    · rw [h10u, hdst, hbu.x19, hw8]
      exact Entry.dscr (Or.inr (by rw [laneA_eq, oN_eq]; omega_using [hK, hn])) (by omega_using [hfit])
        (by rw [laneA_eq]; omega_using [hK, hn])
    rw [h10u, hdst, hbu.x19, hw8] at cp
    have hf' : Frame [oR p S j K] u.mem u'.mem := by
      have := cp.frame
      rwa [show Layout.oN + (j + K) * p.n = Layout.oN + j * p.n + p.n * K by
        rw [Nat.add_mul, Nat.mul_comm K]; omega_using []] at this
    refine ⟨hbu.ofFrame cp.rd cp.wr cp.sp (fun g hg => cp.gpr g (by rcases lr_mem hg with rfl | rfl | rfl <;> decide)) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine ⟨⟨at' S Layout.oN, (c + 8) * p.n⟩, by simp [lch, levelsChanges], Offset.sub S (by omega_using []) ?_⟩
        rw [show Layout.oN + j * p.n + p.n * K = Layout.oN + (j + K) * p.n by rw [Nat.add_mul, Nat.mul_comm K]; omega_using []]
        have : (j + K) * p.n + p.n ≤ (c + 8) * p.n := by
          have := Nat.mul_le_mul_right p.n (show j + K + 1 ≤ c + 8 by omega_using [hK, hj])
          rwa [Nat.add_mul, Nat.one_mul] at this
        omega_using [this])
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Entry.dscr (Or.inl (by rw [oN_eq]; omega_using [])) (by decide)
          (by rw [show Layout.oN + j * p.n + p.n * K = Layout.oN + (j + K) * p.n by
            rw [Nat.add_mul, Nat.mul_comm K]; omega_using []]; omega_using [hfit])),
      fun g hg => by rw [cp.gpr g hg, hgu g hg], fun k hk => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · rw [bytesAt_frame hf' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            dsimp only [oR]; rw [oR_off]
            have hf₁ := node_fit hE (i := j + k) (by omega_using [hk', hK, hj])
            refine Entry.dscr (Or.inl ?_) (by omega_using [hf₁]) (by omega_using [hfit])
            have := Nat.mul_le_mul_right p.n (show j + k + 1 ≤ j + K by omega_using [hk'])
            rw [Nat.succ_mul] at this; omega_using [this]) (by omega_using [hn]),
          hnu k hk']
      · have e₁ : bytesAt u'.mem (at' S (Layout.oN + (j + k) * p.n)) p.n =
            bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) p.n := bytesAt_ext fun q hq => cp.bytes q hq
        rw [e₁, ← hm₃]
        exact bytesAt_frame hfu (fun r hr => by
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
          have := List.mem_range.mp hk'
          dsimp only [oR]; rw [oR_off]
          have hf₁ := node_fit hE (i := j + k') (by omega_using [this, hK, hj])
          exact Entry.dscr (Or.inl (by rw [laneA_eq, oN_eq]; omega_using [hK, hn])) (by rw [laneA_eq]; omega_using [hK, hn])
            (by omega_using [hf₁])) (by omega_using [hn])
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact frame_cat hfu hf'
  · obtain ⟨hbu, hgu, hnu, hfu⟩ := hu
    refine wp_addImm (by decide) fun v₁ w₁ => wp_sub fun v₂ w₂ => wp_lsr (by decide) fun v₃ w₃ => WP.block_nil ?_
    have h24' : v₁.gpr .x24 = BitVec.ofNat 64 (j + 4) := by
      rw [w₁.gpr, hgu _ (by decide), hg₃ _ (by decide) (by decide), h24, ← BitVec.ofNat_add]
    refine ⟨hbu.regs (by rw [w₃.mem, w₂.mem, w₁.mem]) (by rw [w₃.rd, w₂.rd, w₁.rd]) (by rw [w₃.wr, w₂.wr, w₁.wr])
        (by rw [w₃.sp, w₂.sp, w₁.sp]) (fun g hg => by
          rcases lr_mem hg with rfl | rfl | rfl <;>
            rw [w₃.other _ (by decide), w₂.other _ (by decide), w₁.other _ (by decide)]),
      fun g hg h24n => ?_, by rw [w₃.other _ (by decide), w₂.other _ (by decide), h24'], ?_,
      fun k hk => by rw [w₃.mem, w₂.mem, w₁.mem]; exact hnu k hk, by rw [w₃.mem, w₂.mem, w₁.mem, ← hm₃]; exact hfu⟩
    · rw [w₃.other _ (gt_ne hg .x9), w₂.other _ (gt_ne hg .x9), w₁.other _ h24n, hgu _ (gt_ne hg .x14),
        hg₃ _ (gt_ne hg .x10) (gt_ne hg .x11)]
    · rw [w₃.gpr, w₂.gpr, h24', w₁.other _ (by decide), hgu _ (by decide), hg₃ _ (by decide) (by decide), h23]

/-! ## The call of `thash4` on the lanes `A` -/

theorem pres_args' : ∀ r ∈ preserved, r ∉ [Reg.x0, .x1, .x2, .x3, .x4] := by decide

/-- What a call of `thash4` on `A` changes is in `lch`, away from frame 3. -/
theorem t4ch_ok (hz : Sz p) (S AU : Addr) (c h : Nat) :
    ∀ r ∈ t4ch p.n S 3136 128, (∃ R ∈ lch p S AU c h, Region.Sub r R) ∧ Region.Disjoint (frameR S) r := by
  have hn := hz.n32
  intro r hr
  simp only [t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨j, hj, rfl⟩ | rfl
  · have e : 3136 + j * 128 + p.n + 32 = Layout.laneA j + p.n + 32 := by rw [laneA_eq]; omega_using []
    rw [e]
    exact ⟨⟨_, lR_mem S AU c h hj, lR_sub hz (by decide) (by omega_using [])⟩,
      (lR_frame S hj hz).sub_right (lR_sub hz (by decide) (by omega_using []))⟩
  · exact ⟨⟨_, by simp [lch, levelsChanges], fun _ h => h⟩, Offset.disjoint_base S (by decide) (by decide)⟩

/-- A call of `thash4` on the lanes `A`, messages of `3n + 32` bytes, from a state with `Base`. -/
theorem lcall_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {t : State} (hb : Base hE t) {Q : State → Prop}
    (k : ∀ t', Base hE t' → (∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) → VK t' t →
      (∀ j < 4, bytesAt t'.mem (at' S (3136 + j * 128 + p.n + 32)) p.n =
        shake256 (bytesAt t.mem (at' S (3136 + j * 128)) (3 * p.n + 32)) p.n) →
      Frame (t4ch p.n S 3136 128) t.mem t'.mem → Q t') :
    WP isa (thashCall ⟨p.n, p.len⟩ name T.code Layout.oA Layout.strideA (3 * p.n + 32)) t Q := by
  have hn := hz.n32
  have h8 := hz.n8
  refine WP.seq ?_
  rw [thashArgs_eq _ (show Layout.oA < 4096 by decide)]
  refine wp_vk rfl ?_
  refine wp_addImm (by decide) fun t₁ u₁ => wp_movz fun t₂ u₂ => wp_movz fun t₃ u₃ =>
    wp_addImm (by simp only [Layout.msgOff]; omega_using [hn]) fun t₄ u₄ => wp_addImm (by decide) fun t₅ u₅ =>
      WP.block_nil fun hvk => ?_
  have hm : t₅.mem = t.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hg : ∀ g ∉ [Reg.x0, .x1, .x2, .x3, .x4], t₅.gpr g = t.gpr g := fun g h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    rw [u₅.other _ h.2.2.2.2, u₄.other _ h.2.2.2.1, u₃.other _ h.2.2.1, u₂.other _ h.2.1, u₁.other _ h.1]
  have hb₅ : Base hE t₅ := hb.regs hm (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) fun g hg' => hg g (by rcases lr_mem hg' with rfl | rfl | rfl <;> decide)
  have h0 : t₁.gpr .x0 = at' S 3136 := by rw [u₁.gpr, hb.x19]; rfl
  refine t4call_ok T name (s := t₅) (S := S) (o := 3136) (st := 128) (len := 3 * p.n + 32)
    (hE.scr_mem hb₅.wr) hE.scr_fit (by decide) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h0])
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, movz_ofNat (by decide)]; rfl)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, movz_ofNat (by omega_using [hn])])
    (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), h0]
        simp only [Layout.msgOff]; rw [ofNat_add', Nat.add_assoc])
    (by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hb.x19, add0])
    (by omega_using []) (by omega_using [h8]) (by omega_using [hn]) (by omega_using [hn])
    fun t' h₁ h₂ h₃ h₄ h₅ h₆ h₇ => ?_
  rw [hm] at h₆ h₇
  have hc := t4ch_ok hz S AU c h
  exact k t' (hb₅.ofFrame h₁ h₂ h₃ (fun g hg' => h₄ g (by rcases lr_mem hg' with rfl | rfl | rfl <;> decide)
      (by rcases lr_mem hg' with rfl | rfl | rfl <;> decide))
      (by rw [hm]; exact h₇) (fun r hr => (hc r hr).1) fun r hr => (hc r hr).2)
    (fun r hr h30 => by rw [h₄ r hr h30]; exact hg _ (pres_args' r hr)) (VK.trans h₅ hvk) h₆ h₇

/-! ## A group of four nodes -/

theorem nodeAdrs_fld (h16 : a16.length = 16) (ty kp z j : Nat) :
    nodeAdrs a16 ty kp z j = VG.Proof.SlhDsa.fld a16 ty kp z j := by
  rw [nodeAdrs, VG.Proof.SlhDsa.treeAdrs_eq, VG.Proof.SlhDsa.setTypeAndClear_fld h16,
    VG.Proof.SlhDsa.setKeyPairAddress_fld h16, VG.Proof.SlhDsa.setTreeHeight_fld h16,
    VG.Proof.SlhDsa.setTreeIndex_fld h16]

/-- The message of lane `k` of `A` to `thash4`. -/
theorem laneL_msg {m : Mem} (henv : Env p m S pkSeed a16) {k ty κ z x : Nat} {M : List Byte} (hk : k < 4)
    (hl : LaneL p m S k ty κ z x M) :
    bytesAt m (at' S (Layout.laneA k)) (3 * p.n + 32) = pkSeed ++ VG.Proof.SlhDsa.fld a16 ty κ z x ++ M := by
  rw [show 3 * p.n + 32 = p.n + 32 + 2 * p.n by omega_using [], lane_msg, henv.seedA k hk, henv.adrsA k hk]
  obtain ⟨f16, f20, f24, f28, fm⟩ := hl
  simp only [la] at f16 f20 f24 f28 fm
  rw [f16, f20, f24, f28, fm]
  simp only [VG.Proof.SlhDsa.fld, List.append_assoc]

/-- What a group does. -/
structure GroupPost (p : Params) (S : Addr) (pkSeed a16 : List Byte) (t t' : State) (z B j P ty κ : Nat) : Prop where
  keep : ∀ g ∈ [Reg.x21, .x22, .x23, .x25, .x26, .x27], t'.gpr g = t.gpr g
  x24 : t'.gpr .x24 = BitVec.ofNat 64 (j + 4)
  x9 : t'.gpr .x9 = (BitVec.ofNat 64 (j + 4) - BitVec.ofNat 64 P) >>> 63
  vk : VK t' t
  nodes : ∀ k < 4, bytesAt t'.mem (at' S (Layout.oN + (j + k) * p.n)) p.n =
    shake256 (pkSeed ++ VG.Proof.SlhDsa.fld a16 ty κ (z + 1) (B + j + k) ++
      bytesAt t.mem (at' S (Layout.oN + 2 * j * p.n + 2 * p.n * k)) (2 * p.n)) p.n
  frame : Frame ((List.range 4).map (lR p S) ++ [⟨S, workUsed⟩] ++ (List.range 4).map (oR p S j)) t.mem t'.mem

theorem kv_levelLanes (L : Layout) : (Tree.levelLanes L).all keepsV = true := by
  have hl : ∀ k, (Tree.nodeLane L k).all keepsV = true := fun k => by
    rw [nodeLane_eq]; simp only [List.all_append, kv_setFieldR, kv_copyWords]; rfl
  rw [levelLanes_eq]; simp only [List.all_append, kv_mulN, kv_flatMap 4 hl]; rfl

theorem kv_levelOut (L : Layout) : (Tree.levelOut L).all keepsV = true := by
  rw [levelOut_eq]; simp only [List.all_append, kv_mulN, kv_flatMap 4 fun k => kv_copyWords _ _ _ _ _]; rfl

theorem group_ok (hE : Entry p σ S AU idx c h z₀ pkSeed a16) (hz : Sz p) (T : Thash4Impl p.n) (name : String)
    {z B j P : Nat} {t : State} (hb : Base hE t) (h22 : t.gpr .x22 = BitVec.ofNat 64 z) (hz14 : z < 14)
    (h27 : t.gpr .x27 = BitVec.ofNat 64 B) (h24 : t.gpr .x24 = BitVec.ofNat 64 j)
    (h23 : t.gpr .x23 = BitVec.ofNat 64 P) (hB : B + j + 3 < 2 ^ 32) (hj : 2 * j + 8 ≤ c + 8) :
    WP isa (Tree.levelBody ⟨p.n, p.len⟩ name T.code) t fun t' => Base hE t' ∧
      GroupPost p S pkSeed a16 t t' z B j P (tyA σ S) (kpA σ S) := by
  have hn := hz.n32
  have h16 := a16_length hE.env
  have hroom : Layout.oN + 2 * j * p.n + 8 * p.n ≤ 65536 := by
    have := node_fit hE (i := 2 * j + 7) (by omega_using [hj])
    rw [show (2 * j + 7) * p.n = 2 * j * p.n + 7 * p.n by rw [Nat.add_mul]] at this; omega_using [this]
  refine WP.seq (wp_vk (kv_levelLanes _) (WP.mono (lanes_ok hE hz hb h22 hz14 h27 h24 hB hroom)
    fun t₁ ⟨hb₁, hg₁, hl₁, hf₁⟩ hvk₁ => ?_))
  refine WP.seq (lcall_ok hE hz T name hb₁ fun t₂ hb₂ hg₂ hvk₂ hout₂ hf₂ => ?_)
  refine wp_vk (kv_levelOut _) (WP.mono (out_ok hE hz hb₂ (j := j) (P := P)
    (by rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide), h24])
    (by rw [hg₂ _ (by decide) (by decide), hg₁ _ (by decide), h23]) (by omega_using [hj]))
    fun t₃ ⟨hb₃, hg₃, h24₃, h9₃, hn₃, hf₃⟩ hvk₃ => ⟨hb₃, ?_⟩)
  refine ⟨fun g hg => ?_, h24₃, h9₃, VK.trans hvk₃ (VK.trans hvk₂ hvk₁), fun k hk => ?_, ?_⟩
  · have hg' : g ∉ GT ∧ g ≠ .x24 ∧ g ∈ preserved ∧ g ≠ .x30 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hg₃ g hg'.1 hg'.2.1, hg₂ g hg'.2.2.1 hg'.2.2.2, hg₁ g hg'.1]
  · rw [hn₃ k hk]
    have e := hout₂ k hk
    rw [show 3136 + k * 128 = Layout.laneA k by rw [laneA_eq]; omega_using [],
      laneL_msg (hb₁.env hz) hk (hl₁ k hk)] at e
    exact e
  · refine ((frame_cat (frame_cat hf₁ hf₂) hf₃).sub fun r hr => ?_)
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact ⟨r, by simp only [List.mem_append]; exact Or.inl (Or.inl hr), fun _ h => h⟩
    · simp only [t4ch, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨k, hk, rfl⟩ | rfl
      · refine ⟨lR p S k, by simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inl (Or.inl ⟨k, hk, rfl⟩), ?_⟩
        rw [show 3136 + k * 128 + p.n + 32 = Layout.laneA k + p.n + 32 by rw [laneA_eq]; omega_using []]
        exact lR_sub hz (by decide) (by omega_using [])
      · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨r, by simp only [List.mem_append]; exact Or.inr hr, fun _ h => h⟩

end VG.Proof.SlhDsa.AArch64.Levels
