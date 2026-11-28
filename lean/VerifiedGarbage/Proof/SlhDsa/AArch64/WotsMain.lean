module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.WotsChain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.SlhDsa.Lemmas

-- separate module: `WotsCT` runs the taint analysis, which needs a `meta import` of each of its imports;
-- keeping the correctness proofs here keeps them out of that.

/-!
# SLH-DSA on AArch64: `wotsLeaves4` meets its contract

As on x86-64 (`Proof/SlhDsa/X86_64/WotsMain.lean`): the ends of chain `i`
of the four lanes to their messages in `B` (`toB_ok`), what holds before
each chain (`ChainInv`), a whole chain (`chainBody_ok`), the loop of the
`len` chains, the public keys (`leaves_ok`: `T_len` of the chain ends in the
lanes of `B`, to the nodes), the restore of the caller's registers, and the
whole function (`wots4_correct`): from a state satisfying `wots4Contract`'s
precondition, it returns in a state satisfying its postcondition, keeping
what the calling convention keeps.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Wots4

open VG VG.AArch64 VG.AArch64.Steps VG.Proof.SlhDsa.AArch64.Blocks
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64
open VG.Proof.SlhDsa (fld)

variable {p : Params} {σ : State} {S sig : Addr} {kp idx : Nat} {pkSeed a16 skSeed : List Byte}

/-! ## The ends of the chains to `B` -/

/-- Chain `i` of lane `k`'s message in `B`. -/
abbrev bm (p : Params) (m : Mem) (S : Addr) (k i : Nat) : List Byte :=
  bytesAt m (at' S (Layout.laneB k + p.n + 32 + i * p.n)) p.n

theorem bm_fit (hz : Sz p) {k i : Nat} (_hk : k < 4) (hi : i < p.len) :
    Layout.laneB k + p.n + 32 + i * p.n + p.n ≤ Layout.laneB k + Layout.strideB := by
  have hl := lenN hi
  rw [hz.len] at hl
  rw [strideB_eq]
  rcases hz.nv with e | e | e <;> rw [e] at hl ⊢ <;> omega_using [hl]

/-- Where chain `i` of lane `k` goes in `B`. -/
abbrev bR (p : Params) (S : Addr) (k i : Nat) : Region := ⟨at' S (Layout.laneB k + p.n + 32 + i * p.n), p.n⟩

theorem bR_wch (hz : Sz p) {k i : Nat} (hk : k < 4) (hi : i < p.len) (S sig : Addr) (kp : Nat) :
    ∃ R ∈ wch p S sig kp, Region.Sub (bR p S k i) R := by
  refine ⟨_, tailB_mem k hk S sig kp, ?_⟩
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  have e := sub_tailB (p := p) (S := S) (k := k) (a := p.n + 32 + i * p.n) (l := p.n) (by omega_using [])
    (by rw [strideB_eq]; omega_using [hf])
  rwa [show Layout.laneB k + (p.n + 32 + i * p.n) = Layout.laneB k + p.n + 32 + i * p.n by omega_using []] at e

theorem bR_save (hz : Sz p) {k i : Nat} (hk : k < 4) (hi : i < p.len) (S : Addr) :
    Region.Disjoint (saveR S) (bR p S k i) := by
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  exact Entry.dscr (Or.inl (by rw [laneB_eq]; omega_using [])) (by decide)
    (by rw [laneB_eq]; omega_using [hf, hk])

/-- Two places of chain ends in `B`. -/
theorem bR_disj (hz : Sz p) {k i k' i' : Nat} (hk : k < 4) (hi : i < p.len) (hk' : k' < 4) (hi' : i' < p.len)
    (h : k ≠ k' ∨ i ≠ i') (S : Addr) : Region.Disjoint (bR p S k i) (bR p S k' i') := by
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  have hf' := bm_fit hz hk' hi'
  rw [laneB_eq, strideB_eq] at hf'
  have hc : Layout.laneB k + p.n + 32 + i * p.n + p.n ≤ Layout.laneB k' + p.n + 32 + i' * p.n ∨
      Layout.laneB k' + p.n + 32 + i' * p.n + p.n ≤ Layout.laneB k + p.n + 32 + i * p.n := by
    rw [laneB_eq, laneB_eq]
    rcases h with h | h
    · rcases Nat.lt_or_gt_of_ne h with h | h <;> omega_using [h, hf, hf']
    · rcases Nat.lt_or_gt_of_ne h with h | h
      · by_cases e : k = k'
        · subst e; left
          have := Nat.mul_le_mul_right p.n (show i + 1 ≤ i' by omega_using [h]); rw [Nat.add_mul, Nat.one_mul] at this
          omega_using [this]
        · rcases Nat.lt_or_gt_of_ne e with e | e <;> omega_using [e, hf, hf']
      · by_cases e : k = k'
        · subst e; right
          have := Nat.mul_le_mul_right p.n (show i' + 1 ≤ i by omega_using [h]); rw [Nat.add_mul, Nat.one_mul] at this
          omega_using [this]
        · rcases Nat.lt_or_gt_of_ne e with e | e <;> omega_using [e, hf, hf']
  exact Entry.dscr hc (by rw [laneB_eq]; omega_using [hf, hk]) (by rw [laneB_eq]; omega_using [hf', hk'])

/-- A place of a chain end in `B` and a range of a lane of `A`. -/
theorem bR_la (hz : Sz p) {k i k' o l : Nat} (hk : k < 4) (hi : i < p.len) (hk' : k' < 4) (ho : o + l ≤ p.n + 32)
    (S : Addr) : Region.Disjoint (bR p S k i) ⟨at' S (Layout.laneA k' + p.n + o), l⟩ := by
  have hn := hz.n32
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  exact Entry.dscr (Or.inr (by rw [laneA_eq, laneB_eq]; omega_using [hk', ho, hn]))
    (by rw [laneB_eq]; omega_using [hf, hk]) (by rw [laneA_eq]; omega_using [hk', ho, hn])

/-- A chain end in `B` and a fields' range of a lane of `B`. -/
theorem bR_fB (hz : Sz p) {k i k' o : Nat} (hk : k < 4) (hi : i < p.len) (hk' : k' < 4) (ho₁ : 16 ≤ o)
    (ho : o + 4 ≤ 32) (S : Addr) : Region.Disjoint (bR p S k i) ⟨at' S (Layout.laneB k' + p.n + o), 4⟩ := by
  have hn := hz.n32
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  have hc : Layout.laneB k' + p.n + o + 4 ≤ Layout.laneB k + p.n + 32 + i * p.n ∨
      Layout.laneB k + p.n + 32 + i * p.n + p.n ≤ Layout.laneB k' + p.n + o := by
    rw [laneB_eq, laneB_eq]
    by_cases e : k = k'
    · subst e; left; omega_using [ho]
    · rcases Nat.lt_or_gt_of_ne e with e | e <;> omega_using [e, hf, ho, ho₁]
  exact Entry.dscr hc.symm (by rw [laneB_eq]; omega_using [hf, hk])
    (by rw [laneB_eq]; omega_using [hk', ho, hn])

/-- A chain end in `B` and a chain of the signature. -/
theorem bR_sig (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k i i' : Nat} (hk : k < 4) (hi : i < p.len)
    (hi' : i' < p.len) : Region.Disjoint (bR p S k i) ⟨sig + BitVec.ofNat 64 (i' * p.n), p.n⟩ := by
  have hf := bm_fit hz hk hi
  rw [laneB_eq, strideB_eq] at hf
  exact (hE.dsig (lenN hi') (by rw [oSigTmp_eq, laneB_eq]; omega_using [hf, hk])).symm

theorem at_add (S : Addr) (a b : Nat) : BitVec.ofNat 64 a + S + BitVec.ofNat 64 b = at' S (b + a) := by
  rw [BitVec.add_comm (BitVec.ofNat 64 a) S, ofNat_add', Nat.add_comm]

theorem kv_toB (L : Layout) : (Wots.toB L).all keepsV = true := by
  simp only [Wots.toB, List.all_append, kv_mulN, kv_flatMap 4 fun k => kv_copyWords _ _ _ _ _]; rfl

/-- `toB`: the end of chain `i` of each lane to its message in `B`. -/
theorem toB_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {i : Nat} (hi : i < p.len) {t : State}
    (hb : Base hE t) (hr21 : t.gpr .x21 = BitVec.ofNat 64 i) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t', Base hE t' → (∀ g ∉ TMP, t'.gpr g = t.gpr g) →
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.laneB k + p.n + 32 + i * p.n)) p.n = la p t.mem S k 32 p.n) →
      Frame ((List.range 4).map fun k => bR p S k i) t.mem t'.mem → WP isa (.block is) t' Q) :
    WP isa (.block (Wots.toB (L p) ++ is)) t Q := by
  have hn := hz.n32
  have h8 := hz.n8
  simp only [Wots.toB, Thash4.mov, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addImm (by decide) fun t₁ u₁ => mulN_ok hz.nv (r := .x10) (tmp := .x11) (x := i) (by decide)
    (by rw [u₁.gpr, hr21, add0]) fun t₂ h₂ g₂ sp₂ m₂ rd₂ wr₂ => ?_
  refine wp_add fun t₃ u₃ => ?_
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, m₂, u₁.mem]
  have hg₃ : ∀ g ∉ TMP, t₃.gpr g = t.gpr g := fun g hg => by
    rw [u₃.other _ (nt hg .x10), g₂ _ (nt hg .x10) (nt hg .x11), u₁.other _ (nt hg .x10)]
  have hb₃ : Base hE t₃ := hb.regs hm₃ (by rw [u₃.rd, rd₂, u₁.rd]) (by rw [u₃.wr, wr₂, u₁.wr])
    (by rw [u₃.sp, sp₂, u₁.sp]) fun g h' => hg₃ g (br_tmp h')
  have hdx : t₃.gpr .x10 = BitVec.ofNat 64 (i * p.n) + S := by
    rw [u₃.gpr, h₂, g₂ _ (by decide) (by decide), u₁.other _ (by decide), hb.x19]
  refine WP.block_append (WP.mono (wp_range_flatMap 4 (P := fun K u => Base hE u ∧
      (∀ g, g ≠ .x14 → u.gpr g = t₃.gpr g) ∧
      (∀ k < K, bytesAt u.mem (at' S (Layout.laneB k + p.n + 32 + i * p.n)) p.n = la p t.mem S k 32 p.n) ∧
      Frame ((List.range K).map fun k => bR p S k i) t₃.mem u.mem)
    ⟨hb₃, fun _ _ => rfl, fun _ h => absurd h (by omega_using []), by simpa using Frame.refl [] t₃.mem⟩
    fun K hK u hu => ?_) fun u hu => ?_)
  · have hdxu : u.gpr .x10 = BitVec.ofNat 64 (i * p.n) + S := by rw [hu.2.1 _ (by decide), hdx]
    have hfit := bm_fit hz hK hi
    have hw8 : 8 * (p.n / 8) = p.n := by omega_using [h8]
    have hbr : at' S (Layout.laneB K + (L p).msgOff + i * p.n) = at' S (Layout.laneB K + p.n + 32 + i * p.n) := by
      simp only [Layout.msgOff, Nat.add_assoc]
    refine WP.mono (copyWords_ok (by decide) (by decide)
      (by simp only [Layout.msgOff]; rw [laneA_eq]; omega_using [h8])
      (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [h8]) ?_ ?_ ?_
      (by simp only [Layout.msgOff]; rw [laneA_eq]; omega_using [hK, hn, hw8])
      (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [hK, hn, hw8])) fun u' c => ?_
    · rw [hu.1.x19, hw8]
      exact hE.inScr' hu.1.wr (by simp only [Layout.msgOff]; rw [laneA_eq]; omega_using [hK, h8, hn])
    · rw [hdxu, at_add, hw8, hbr]
      exact hE.inScr hu.1.wr (by rw [laneB_eq, strideB_eq] at hfit; rw [laneB_eq]; omega_using [hfit, hK])
    · rw [hdxu, at_add, hu.1.x19, hw8, hbr]
      have := bR_la hz hK hi hK (o := 32) (l := p.n) (by omega_using []) S
      simp only [Layout.msgOff, ← Nat.add_assoc] at this ⊢
      exact this
    rw [hdxu, at_add, hu.1.x19, hw8, hbr] at c
    have hf' : Frame [bR p S K i] u.mem u'.mem := c.frame
    refine ⟨hu.1.ofFrame c.rd c.wr c.sp (fun g hg => c.gpr g (ne_of_mem hg (by decide))) hf'
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact bR_wch hz hK hi S sig kp)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact bR_save hz hK hi S),
      fun g hg => by rw [c.gpr g hg, hu.2.1 g hg], fun k hk => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · rw [bytesAt_frame hf' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact bR_disj hz (by omega_using [hk', hK]) hi hK hi (Or.inl (by omega_using [hk'])) S) (by omega_using [hn]),
          hu.2.2.1 k hk']
      · have e₁ : bytesAt u'.mem (at' S (Layout.laneB k + p.n + 32 + i * p.n)) p.n =
            bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) p.n := by
          refine bytesAt_ext fun q hq => ?_
          have := c.bytes q (by omega_using [hq, hw8])
          simpa only [Layout.msgOff, Nat.add_assoc] using this
        rw [e₁]
        have e₂ := bytesAt_frame (a := at' S (Layout.laneA k + p.n + 32)) (n := p.n) hu.2.2.2 (fun r hr => by
          obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
          exact (bR_la hz (by have := List.mem_range.mp hk'; omega_using [this, hK]) hi hK (o := 32) (l := p.n)
            (by omega_using []) S).symm)
          (by omega_using [hn])
        rw [e₂, hm₃]
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact frame_cat hu.2.2.2 hf'
  · exact kk u hu.1 (fun g hg => by rw [hu.2.1 g (nt hg .x14), hg₃ g hg]) hu.2.2.1 (by rw [← hm₃]; exact hu.2.2.2)

/-! ## A chain of the four lanes -/

/-- Before chain `i`: the ends of the chains before it in `B`, the
signature's chains before it captured. -/
structure ChainInv (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (i : Nat) (t : State) : Prop where
  base : Base hE t
  vk : VK t σ
  x21 : t.gpr .x21 = BitVec.ofNat 64 i
  lanes : ∀ k < 4, LaneSet p t.mem S kp k
  ends : ∀ k < 4, ∀ i' < i, bm p t.mem S k i' = cv p skSeed pkSeed a16 kp k i' 15
  sigs : ∀ i' < p.len, sigC p t.mem sig i' = if InR kp idx ∧ i' < i then
    wotsChainAt p skSeed pkSeed a16 idx i' (digitAt σ.mem S i') else sigC p σ.mem sig i'

theorem bR_AZ (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k i' i : Nat} (hk : k < 4)
    (hi' : i' < p.len) (hi : i < p.len) : ∀ r ∈ AZ p S sig i, Region.Disjoint (bR p S k i') r := by
  have hf := bm_fit hz hk hi'
  rw [laneB_eq, strideB_eq] at hf
  exact B_AZ hE hz (a := Layout.laneB k + p.n + 32 + i' * p.n) (l := p.n) (by rw [laneB_eq]; omega_using [])
    (by rw [laneB_eq]; omega_using [hf, hk]) hi

theorem fB_AZ (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) {k o i : Nat} (hk : k < 4) (ho : o ≤ 28)
    (hi : i < p.len) : ∀ r ∈ AZ p S sig i, Region.Disjoint ⟨at' S (Layout.laneB k + p.n + o), 4⟩ r := by
  have hn := hz.n32
  exact B_AZ hE hz (a := Layout.laneB k + p.n + o) (l := 4) (by rw [laneB_eq]; omega_using [])
    (by rw [laneB_eq]; omega_using [hn, hk, ho]) hi

/-- A range of `scratch` before the signature's copy and a chain of the signature. -/
theorem scr_sig (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) {i a l : Nat} (hi : i < p.len)
    (ha : a + l ≤ Layout.oSigTmp) : Region.Disjoint ⟨at' S a, l⟩ ⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ :=
  (hE.dsig (lenN hi) ha).symm

theorem LaneSet.frame {m m' : Mem} {k : Nat} {rs : List Region} (hl : LaneSet p m S kp k) (hf : Frame rs m m')
    (hA : ∀ r ∈ rs, Region.Disjoint ⟨at' S (Layout.laneA k + p.n + 20), 4⟩ r)
    (hB : ∀ o, 16 ≤ o → o ≤ 28 → ∀ r ∈ rs, Region.Disjoint ⟨at' S (Layout.laneB k + p.n + o), 4⟩ r) :
    LaneSet p m' S kp k :=
  ⟨(bytesAt_frame hf hA (by decide)).trans hl.a20,
    (bytesAt_frame hf (hB 16 (by decide) (by decide)) (by decide)).trans hl.b16,
    (bytesAt_frame hf (hB 20 (by decide) (by decide)) (by decide)).trans hl.b20,
    (bytesAt_frame hf (hB 24 (by decide) (by decide)) (by decide)).trans hl.b24,
    (bytesAt_frame hf (hB 28 (by decide) (by decide)) (by decide)).trans hl.b28⟩

theorem kv_final (L : Layout) : (Wots.capture L ++ Wots.toB L ++
    [Instr.addImm .x .x21 .x21 1, Instr.subImm .x .x9 .x21 L.len]).all keepsV = true := by
  simp only [List.all_append, kv_capture, kv_toB]; rfl

/-- Chain `i` of the four lanes. -/
theorem chainBody_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) {i : Nat} (hi : i < p.len) {t₀ : State} (h : ChainInv hE i t₀) :
    WP isa (Wots.chainBody (L p) name T.code) t₀ (fun t' => ChainInv hE (i + 1) t' ∧
      t'.gpr .x9 = BitVec.ofNat 64 (i + 1) - BitVec.ofNat 64 p.len) := by
  have hn := hz.n32
  have hlen : p.len < 4096 := by have := hz.len; omega_using [this, hn]
  refine chainHead_ok hE hz T name hi h.base h.vk h.x21 (fun k hk => (h.lanes k hk).a20) fun t ht => ?_
  refine WP.seq (WP.mono (steps_ok hE hz T name hi ht) fun u hu => ?_)
  refine wp_vk (kv_final _) ?_
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (capture_ok hE hz hi (by decide) hu.base hu.x21 hu.x22 fun k hk => by
      obtain ⟨_, l⟩ := hu.lanes k hk; exact l.msg) fun u₁ ⟨hb₁, hg₁, hs₁, hf₁⟩ => ?_)
  have hr₁ : u₁.gpr .x21 = BitVec.ofNat 64 i := by rw [hg₁ _ (by decide), hu.x21]
  refine toB_ok hE hz hi hb₁ hr₁ fun u₂ hb₂ hg₂ he₂ hf₂ => ?_
  refine wp_addImm (by decide) fun u₃ v₃ => wp_subImm hlen fun u₄ v₄ => WP.block_nil fun hvk₄ => ?_
  have hm : u₄.mem = u₂.mem := by rw [v₄.mem, v₃.mem]
  have hr₃ : u₃.gpr .x21 = BitVec.ofNat 64 (i + 1) := by
    rw [v₃.gpr, hg₂ _ (by decide), hr₁, ← BitVec.ofNat_add]
  have hfB : ∀ {R : Region}, (∀ k < 4, Region.Disjoint R (bR p S k i)) → ∀ r ∈ (List.range 4).map fun k => bR p S k i,
      Region.Disjoint R r := fun hR r hr => by
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
    exact hR k' (List.mem_range.mp hk')
  have hfS : ∀ {R : Region}, Region.Disjoint R ⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ →
      ∀ r ∈ [(⟨sig + BitVec.ofNat 64 (i * p.n), p.n⟩ : Region)], Region.Disjoint R r := fun hR r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR
  refine ⟨⟨hb₂.regs hm (by rw [v₄.rd, v₃.rd]) (by rw [v₄.wr, v₃.wr]) (by rw [v₄.sp, v₃.sp]) fun g hg => by
      rw [v₄.other g (ne_of_mem hg (by decide)), v₃.other g (ne_of_mem hg (by decide))],
    VK.trans hvk₄ hu.vk, by rw [v₄.other _ (by decide), hr₃], fun k hk => ?_, fun k hk i' hi' => ?_, fun i' hi' => ?_⟩, ?_⟩
  · obtain ⟨_, la₀⟩ := hu.lanes k hk
    have l₀ : LaneSet p u.mem S kp k :=
      ⟨la₀.f20, (bytesAt_frame hu.fr (fB_AZ hE hz hk (o := 16) (by decide) hi) (by decide)).trans (h.lanes k hk).b16,
        (bytesAt_frame hu.fr (fB_AZ hE hz hk (o := 20) (by decide) hi) (by decide)).trans (h.lanes k hk).b20,
        (bytesAt_frame hu.fr (fB_AZ hE hz hk (o := 24) (by decide) hi) (by decide)).trans (h.lanes k hk).b24,
        (bytesAt_frame hu.fr (fB_AZ hE hz hk (o := 28) (by decide) hi) (by decide)).trans (h.lanes k hk).b28⟩
    have l₁ := l₀.frame hf₁ (hfS (scr_sig hE hi (a := Layout.laneA k + p.n + 20) (l := 4) (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn])))
      fun o _ ho => hfS (scr_sig hE hi (a := Layout.laneB k + p.n + o) (l := 4) (by rw [laneB_eq, oSigTmp_eq]; omega_using [hk, hn, ho]))
    rw [hm]
    exact l₁.frame hf₂ (hfB fun k' hk' => (bR_la hz hk' hi hk (o := 20) (l := 4) (by omega_using [hn]) S).symm)
      fun o ho₁ ho => hfB fun k' hk' => (bR_fB hz hk' hi hk ho₁ (by omega_using [ho]) S).symm
  · have hi'l : i' < p.len := by omega_using [hi', hi]
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hlt | rfl
    · show bytesAt _ _ _ = _
      rw [bytesAt_frame hf₂ (hfB fun k' hk' => bR_disj hz hk hi'l hk' hi (Or.inr (by omega_using [hlt])) S)
          (by omega_using [hn]),
        bytesAt_frame hf₁ (hfS (bR_sig hE hz hk hi'l hi)) (by omega_using [hn]),
        bytesAt_frame hu.fr (bR_AZ hE hz hk hi'l hi) (by omega_using [hn])]
      exact h.ends k hk i' hlt
    · show bytesAt _ _ _ = _
      rw [he₂ k hk]
      obtain ⟨_, la₀⟩ := hu.lanes k hk
      show bytesAt _ _ _ = _
      rw [bytesAt_frame hf₁ (hfS (scr_sig hE hi (a := Layout.laneA k + p.n + 32) (l := p.n)
        (by rw [laneA_eq, oSigTmp_eq]; omega_using [hk, hn]))) (by omega_using [hn])]
      exact la₀.msg
  · rw [hm]
    show bytesAt _ _ _ = _
    rw [bytesAt_frame hf₂ (hfB fun k' hk' => (bR_sig hE hz hk' hi hi').symm) (by omega_using [hn])]
    by_cases e : i' = i
    · subst e
      show sigC p u₁.mem sig i' = _
      rw [hs₁, hu.sigc]
      refine (sig_step (InR kp idx) (fun x => wotsChainAt p skSeed pkSeed a16 idx i' x) _).trans ?_
      have hd := hE.dig i' hi'
      by_cases hP : InR kp idx
      · rw [ite_eq_left (⟨hP, by omega_using [hd]⟩ : InR kp idx ∧ digitAt σ.mem S i' < 15 + 1),
          ite_eq_left (⟨hP, Nat.lt_succ_self i'⟩ : InR kp idx ∧ i' < i' + 1)]
      · rw [ite_eq_right (fun h' => hP h'.1), ite_eq_right (fun h' => hP h'.1), h.sigs i' hi', ite_eq_right (fun h' => hP h'.1)]
    · rw [bytesAt_frame hf₁ (hfS (sig_AZ hE hz hi hi' e _ (by simp [AZ]))) (by omega_using [hn]),
        bytesAt_frame hu.fr (sig_AZ hE hz hi hi' e) (by omega_using [hn])]
      show sigC p t₀.mem sig i' = _
      rw [h.sigs i' hi']
      by_cases hc : InR kp idx ∧ i' < i
      · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, by omega_using [hc.2]⟩]
      · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ⟨h'.1, by omega_using [h'.2, e]⟩)]
  · rw [v₄.gpr, hr₃]

/-- The `len` chains. -/
theorem chains_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) {t : State} (h : ChainInv hE 0 t) :
    WP isa (.loop (Wots.chainBody (L p) name T.code) (.nonzero .x .x9)) t (ChainInv hE p.len) := by
  have hl : 1 ≤ p.len := by have := hz.len; omega_using [this]
  have hl64 : p.len < 2 ^ 63 := by have h1 := hz.len; have h2 := hz.n32; omega_using [h1, h2]
  refine WP.loop (M := isa) (Inv := fun (n : Nat) (u : State) => 1 ≤ n ∧ n ≤ p.len ∧ ChainInv hE (p.len - n) u)
    (fun n u hu => ?_) p.len t ⟨hl, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  obtain ⟨h₁, h₂, hu⟩ := hu
  refine WP.mono (chainBody_ok hE hz T name (by omega_using [h₁, h₂]) hu) fun u' ⟨hu', h9⟩ => ?_
  have ev := eval_nz h9 (by omega_using [h₂, hl64]) (by omega_using [hl64])
  by_cases e : p.len - n + 1 = p.len
  · rw [e] at hu'
    exact Or.inl ⟨by rw [ev, decide_eq_true e]; rfl, hu'⟩
  · refine Or.inr ⟨by rw [ev, decide_eq_false e]; rfl, n - 1, by omega_using [h₁],
      ⟨by omega_using [e, h₁, h₂], by omega_using [h₂], ?_⟩⟩
    rw [show p.len - (n - 1) = p.len - n + 1 by omega_using [h₁, h₂, e]]; exact hu'

/-! ## The public keys -/

theorem bytesAt_flat (m : Mem) (S : Addr) (b n : Nat) :
    ∀ L, bytesAt m (at' S b) (L * n) = (List.range L).flatMap fun i => bytesAt m (at' S (b + i * n)) n
  | 0 => by simp [bytesAt]
  | L + 1 => by
    rw [Nat.add_mul, Nat.one_mul, bytesAt_split, bytesAt_flat m S b n L, List.range_succ, List.flatMap_append,
      List.flatMap_singleton]

theorem w_eq (hz : Sz p) : p.w - 1 = 15 := by simp [Params.w, hz.lgw]

/-- `wots_pkGen`, as `T_len` of the chain ends. -/
theorem pkGen_eq (hz : Sz p) (h16 : a16.length = 16) {κ : Nat} (hκ : κ < 2 ^ 32) :
    wotsPkGen p skSeed pkSeed (wotsAdrs a16 κ) = shake256 (pkSeed ++ fld a16 WOTS_PK κ 0 0 ++
      (List.range p.len).flatMap fun i => wotsChainAt p skSeed pkSeed a16 κ i 15) p.n := by
  have e : wotsPkGen p skSeed pkSeed (wotsAdrs a16 κ) = T p pkSeed (wotsPkAdrs (wotsAdrs a16 κ))
      ((List.range p.len).flatMap fun i => wotsChainAt p skSeed pkSeed a16 κ i (p.w - 1)) := rfl
  rw [e, w_eq hz, VG.Proof.SlhDsa.wotsAdrs_fld h16, VG.Proof.SlhDsa.wotsPkAdrs_fld h16 _ _ _ _ hκ]
  simp only [T, hz.shake, shakeAdrs]

theorem flatMap_range_congr {f g : Nat → List Byte} : ∀ {K : Nat}, (∀ i < K, f i = g i) →
    (List.range K).flatMap f = (List.range K).flatMap g
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_congr fun i hi => h i (by omega_using [hi]),
      List.flatMap_singleton, List.flatMap_singleton, h K (by omega_using [])]

/-- The node of key pair `kp + k`. -/
abbrev nR (p : Params) (S : Addr) (kp k : Nat) : Region := ⟨at' S (Layout.oN + kp * p.n + p.n * k), p.n⟩

theorem nR_fit (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) {k : Nat} (hk : k < 4) :
    Layout.oN + kp * p.n + p.n * k + p.n ≤ 29120 := by
  have hkp := hE.kpN
  rw [nodeSlots_eq, Nat.add_mul] at hkp
  have : p.n * k + p.n ≤ 4 * p.n := by
    have := Nat.mul_le_mul_left p.n (show k + 1 ≤ 4 by omega_using [hk]); rw [Nat.mul_add, Nat.mul_one] at this
    omega_using [this]
  rw [oN_eq]; omega_using [hkp, this]

theorem kv_leaves (L : Layout) : (Wots.leafPtr L ++ (List.range 4).flatMap fun k =>
    copyWords .x10 (Layout.oN + L.n * k) .x19 (Layout.laneB k + L.msgOff) (L.n / 8)).all keepsV = true := by
  simp only [Wots.leafPtr, List.all_append, kv_mulN, kv_flatMap 4 fun k => kv_copyWords _ _ _ _ _]; rfl

/-- The public keys: `T_len` of the lanes of `B`, copied to the nodes. -/
theorem leaves_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) {t : State} (h : ChainInv hE p.len t) :
    WP isa (Wots.leaves (L p) name T.code) t (fun t' => Base hE t' ∧ VK t' σ ∧
      (∀ k < 4, bytesAt t'.mem (at' S (Layout.oN + (kp + k) * p.n)) p.n =
        wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k))) ∧
      ∀ i' < p.len, sigC p t'.mem sig i' = sigC p t.mem sig i') := by
  have hn := hz.n32
  have h8 := hz.n8
  have hl := hz.len
  have h16 := a16_length hE.env
  have hkp := hE.kp_lt hz
  have hlm : (p.n + 32 + p.len * p.n) % 8 = 0 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e]
  have hll : p.n + 32 + p.len * p.n ≤ 2208 := by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide
  refine WP.seq (tcall_ok hE hz T name (o := 3648) (st := 2208) (len := p.n + 32 + p.len * p.n) (Or.inr ⟨rfl, rfl⟩)
    (by omega_using []) hlm hll h.base fun t₁ hb₁ hcs₁ hvk₁ hout₁ hf₁ => ?_)
  have hmsg : ∀ k < 4, bytesAt t.mem (at' S (3648 + k * 2208)) (p.n + 32 + p.len * p.n) =
      pkSeed ++ fld a16 WOTS_PK (kp + k) 0 0 ++
        (List.range p.len).flatMap fun i => wotsChainAt p skSeed pkSeed a16 (kp + k) i 15 := by
    intro k hk
    have henv := h.base.env hz
    obtain ⟨_, b16, b20, b24, b28⟩ := h.lanes k hk
    simp only [fB] at b16 b20 b24 b28
    rw [show 3648 + k * 2208 = Layout.laneB k by rw [laneB_eq]; omega_using [], lane_msg, henv.seedB k hk,
      henv.adrsB k hk, b16, b20, b24, b28, bytesAt_flat]
    rw [flatMap_range_congr fun i hi => h.ends k hk i hi]
    simp only [fld, List.append_assoc, WOTS_PK]
  have hpk : ∀ k < 4, bytesAt t₁.mem (at' S (Layout.laneB k + p.n + 32)) p.n =
      wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k)) := fun k hk => by
    have e := hout₁ k hk
    rw [hmsg k hk, show 3648 + k * 2208 + p.n + 32 = Layout.laneB k + p.n + 32 by rw [laneB_eq]; omega_using []] at e
    rw [e, pkGen_eq hz h16 (by omega_using [hkp, hk])]
  have hsig₁ : ∀ i' < p.len, sigC p t₁.mem sig i' = sigC p t.mem sig i' := fun i' hi' =>
    sig_t4 hE hz (Or.inr ⟨rfl, rfl⟩) hi' hf₁
  refine wp_vk (kv_leaves _) ?_
  simp only [Wots.leafPtr, Thash4.mov, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addImm (by decide) fun t₂ u₂ => mulN_ok hz.nv (r := .x10) (tmp := .x11) (x := kp) (by decide)
    (by rw [u₂.gpr, hb₁.x20, add0]) fun t₃ h₃ g₃ sp₃ m₃ rd₃ wr₃ => ?_
  refine wp_add fun t₄ u₄ => ?_
  have hm₄ : t₄.mem = t₁.mem := by rw [u₄.mem, m₃, u₂.mem]
  have hg₄ : ∀ g ∉ TMP, t₄.gpr g = t₁.gpr g := fun g hg => by
    rw [u₄.other _ (nt hg .x10), g₃ _ (nt hg .x10) (nt hg .x11), u₂.other _ (nt hg .x10)]
  have hb₄ : Base hE t₄ := hb₁.regs hm₄ (by rw [u₄.rd, rd₃, u₂.rd]) (by rw [u₄.wr, wr₃, u₂.wr])
    (by rw [u₄.sp, sp₃, u₂.sp]) fun g h' => hg₄ g (br_tmp h')
  have hdx : t₄.gpr .x10 = at' S (kp * p.n) := by
    rw [u₄.gpr, h₃, g₃ _ (by decide) (by decide), u₂.other _ (by decide), hb₁.x19, BitVec.add_comm]
  refine WP.mono (wp_range_flatMap 4 (P := fun K u => Base hE u ∧ (∀ g, g ≠ .x14 → u.gpr g = t₄.gpr g) ∧
      (∀ k < K, bytesAt u.mem (at' S (Layout.oN + kp * p.n + p.n * k)) p.n =
        wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k))) ∧
      Frame ((List.range K).map fun k => nR p S kp k) t₄.mem u.mem)
    ⟨hb₄, fun _ _ => rfl, fun _ h => absurd h (by omega_using []), by simpa using Frame.refl [] t₄.mem⟩
    fun K hK u hu => ?_) fun u hu => ?_
  · have hdxu : u.gpr .x10 = at' S (kp * p.n) := by rw [hu.2.1 _ (by decide), hdx]
    have hfit := nR_fit hE hK
    have hw8 : 8 * (p.n / 8) = p.n := by omega_using [h8]
    have hnK : p.n * K ≤ 32 * 4 := Nat.mul_le_mul hn (Nat.le_of_lt hK)
    have hdst : at' S (kp * p.n) + BitVec.ofNat 64 (Layout.oN + p.n * K) = at' S (Layout.oN + kp * p.n + p.n * K) := by
      rw [ofNat_add']; congr 2; omega_using []
    refine WP.mono (copyWords_ok (by decide) (by decide)
      (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [h8])
      (by rw [oN_eq, Nat.add_mod, Nat.mul_mod, h8]; simp) ?_ ?_ ?_
      (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [hK, hn, hw8])
      (by rw [oN_eq]; omega_using [hnK, hn, hw8])) fun u' c => ?_
    · rw [hu.1.x19, hw8]
      exact hE.inScr' hu.1.wr (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [hK, h8, hn])
    · rw [hdxu, hdst, hw8]
      exact hE.inScr hu.1.wr (by omega_using [hfit])
    · rw [hdxu, hdst, hu.1.x19, hw8]
      exact Entry.dscr (Or.inr (by simp only [Layout.msgOff]; rw [laneB_eq, oN_eq]; omega_using [hK, hn]))
        (by omega_using [hfit]) (by simp only [Layout.msgOff]; rw [laneB_eq]; omega_using [hK, hn])
    rw [hdxu, hdst, hu.1.x19, hw8] at c
    have hf' : Frame [nR p S kp K] u.mem u'.mem := c.frame
    have hfar : ∀ {a l : Nat}, a + l ≤ Layout.oN → Region.Disjoint ⟨at' S a, l⟩ (nR p S kp K) := fun ha =>
      Entry.dscr (Or.inl (by omega_using [ha])) (by rw [oN_eq] at ha; omega_using [ha]) (by omega_using [hfit])
    refine ⟨hu.1.ofFrame c.rd c.wr c.sp (fun g hg => c.gpr g (ne_of_mem hg (by decide))) hf'
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        refine ⟨⟨at' S (Layout.oN + kp * p.n), 4 * p.n⟩, nodes_mem S sig kp, Offset.sub S (by omega_using []) ?_⟩
        have := Nat.mul_le_mul_left p.n (show K + 1 ≤ 4 by omega_using [hK]); rw [Nat.mul_add, Nat.mul_one] at this
        omega_using [this])
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hfar (by rw [oN_eq]; decide)),
      fun g hg => by rw [c.gpr g hg, hu.2.1 g hg], fun k hk => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · rw [bytesAt_frame hf' (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            have hf₂ := nR_fit hE (show k < 4 by omega_using [hk', hK])
            refine Entry.dscr (Or.inl ?_) (by omega_using [hf₂]) (by omega_using [hfit])
            have := Nat.mul_le_mul_left p.n (show k + 1 ≤ K by omega_using [hk']); rw [Nat.mul_add, Nat.mul_one] at this
            omega_using [this]) (by omega_using [hn]),
          hu.2.2.1 k hk']
      · have e₁ : bytesAt u'.mem (at' S (Layout.oN + kp * p.n + p.n * k)) p.n =
            bytesAt u.mem (at' S (Layout.laneB k + p.n + 32)) p.n := by
          refine bytesAt_ext fun q hq => ?_
          have := c.bytes q (by omega_using [hq])
          simpa only [Layout.msgOff, Nat.add_assoc] using this
        rw [e₁, bytesAt_frame hu.2.2.2 (fun r hr => by
            obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
            have hf₂ := nR_fit hE (show k' < 4 by have := List.mem_range.mp hk'; omega_using [this, hK])
            exact Entry.dscr (Or.inl (by rw [laneB_eq, oN_eq]; omega_using [hK, hn]))
              (by rw [laneB_eq]; omega_using [hK, hn]) (by omega_using [hf₂])) (by omega_using [hn]),
          hm₄, hpk k hK]
    · rw [List.range_succ, List.map_append, List.map_singleton]
      exact frame_cat hu.2.2.2 hf'
  · obtain ⟨hb, _, hn', hf⟩ := hu
    refine fun hvk => ⟨hb, VK.trans hvk (VK.trans hvk₁ h.vk), fun k hk => ?_, fun i' hi' => ?_⟩
    · rw [show Layout.oN + (kp + k) * p.n = Layout.oN + kp * p.n + p.n * k by rw [Nat.add_mul, Nat.mul_comm k]; omega_using []]
      exact hn' k hk
    · rw [← hsig₁ i' hi', ← hm₄]
      exact bytesAt_frame hf (fun r hr => by
        obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
        have hf₂ := nR_fit hE (show k' < 4 from List.mem_range.mp hk')
        exact hE.dsig (lenN hi') (by rw [oSigTmp_eq]; omega_using [hf₂])) (by omega_using [hn])

/-! ## The epilogue, and the whole function -/

theorem ne_of_mem' {l : List Reg} {a b : Reg} (ha : a ∉ l) (hb : b ∈ l) : a ≠ b := fun e => ha (e ▸ hb)

theorem restore_eq : restoreRegs 0 Wots.saved = [.ldr .x .x20 .x19 1032, .ldr .x .x21 .x19 1040,
    .ldr .x .x22 .x19 1048, .ldr .x .x23 .x19 1056, .ldr .x .x24 .x19 1064, .ldr .x .x30 .x19 1072,
    .ldr .x .x19 .x19 1024] := rfl

theorem restore_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) {t : State} (hb : Base hE t) {Q : State → Prop}
    (k : ∀ t', t'.mem = t.mem → t'.sp = t.sp → VK t' t → (∀ r ∈ preserved, t'.gpr r = σ.gpr r) → Q t') :
    WP isa (.block (restoreRegs 0 Wots.saved)) t Q := by
  have hin : ∀ i < 7, InRegions (t.rd ++ t.wr) (at' S (Layout.oSave 0 i)) 8 := fun i hi =>
    hE.inScr' hb.wr (by rw [oSave_eq]; omega_using [hi])
  rw [restore_eq]
  refine wp_vk rfl ?_
  refine wp_ldr (a := at' S (Layout.oSave 0 1)) ⟨by decide, by decide⟩ (by rw [hb.x19]; rfl) (hin 1 (by decide))
    fun t₁ u₁ => ?_
  refine wp_ldr (a := at' S (Layout.oSave 0 2)) ⟨by decide, by decide⟩ (by rw [u₁.other _ (by decide), hb.x19]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact hin 2 (by decide)) fun t₂ u₂ => ?_
  refine wp_ldr (a := at' S (Layout.oSave 0 3)) ⟨by decide, by decide⟩
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hb.x19]; rfl)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 3 (by decide)) fun t₃ u₃ => ?_
  refine wp_ldr (a := at' S (Layout.oSave 0 4)) ⟨by decide, by decide⟩
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb.x19]; rfl)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 4 (by decide)) fun t₄ u₄ => ?_
  refine wp_ldr (a := at' S (Layout.oSave 0 5)) ⟨by decide, by decide⟩
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb.x19]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 5 (by decide)) fun t₅ u₅ => ?_
  refine wp_ldr (a := at' S (Layout.oSave 0 6)) ⟨by decide, by decide⟩
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hb.x19]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 6 (by decide))
    fun t₆ u₆ => ?_
  refine wp_ldr (a := at' S (Layout.oSave 0 0)) ⟨by decide, by decide⟩
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hb.x19]; rfl)
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 0 (by decide))
    fun t₇ u₇ => WP.block_nil fun hvk => ?_
  have hm₁ : t₁.mem = t.mem := u₁.mem
  have hm₂ : t₂.mem = t.mem := by rw [u₂.mem, hm₁]
  have hm₃ : t₃.mem = t.mem := by rw [u₃.mem, hm₂]
  have hm₄ : t₄.mem = t.mem := by rw [u₄.mem, hm₃]
  have hm₅ : t₅.mem = t.mem := by rw [u₅.mem, hm₄]
  have hm₆ : t₆.mem = t.mem := by rw [u₆.mem, hm₅]
  refine k t₇ (by rw [u₇.mem, hm₆]) (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]) hvk fun r hr => ?_
  have hk : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t₇.gpr r = σ.gpr r := fun r hr' => by
    have h₀ : r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x30] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' ⊢
      rcases hr' with rfl | rfl | rfl | rfl <;> decide
    rw [u₇.other _ (ne_of_mem' h₀ (by decide)), u₆.other _ (ne_of_mem' h₀ (by decide)),
      u₅.other _ (ne_of_mem' h₀ (by decide)), u₄.other _ (ne_of_mem' h₀ (by decide)),
      u₃.other _ (ne_of_mem' h₀ (by decide)), u₂.other _ (ne_of_mem' h₀ (by decide)),
      u₁.other _ (ne_of_mem' h₀ (by decide)), hb.keep r hr']
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [u₇.gpr, hm₆]; exact hb.saved 0 (by decide)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; exact hb.saved 1 (by decide)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, hm₁]; exact hb.saved 2 (by decide)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, hm₂]; exact hb.saved 3 (by decide)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, hm₃]
    exact hb.saved 4 (by decide)
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, hm₄]; exact hb.saved 5 (by decide)
  · exact hk _ (by decide)
  · exact hk _ (by decide)
  · exact hk _ (by decide)
  · exact hk _ (by decide)
  · rw [u₇.other _ (by decide), u₆.gpr, hm₅]; exact hb.saved 6 (by decide)

/-- What `wotsLeaves4` does, from the entry state `σ`. -/
structure Wots4Post (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (t : State) : Prop where
  cs : ∀ r ∈ preserved, t.gpr r = σ.gpr r
  sp : t.sp = σ.sp
  vk : VK t σ
  frame : Frame (wch p S sig kp) σ.mem t.mem
  env : Env p t.mem S pkSeed a16
  nodes : ∀ k < 4, bytesAt t.mem (at' S (Layout.oN + (kp + k) * p.n)) p.n =
    wotsPkGen p skSeed pkSeed (wotsAdrs a16 (kp + k))
  sigs : ∀ i < p.len, sigC p t.mem sig i = if InR kp idx then
    wotsChainAt p skSeed pkSeed a16 idx i (digitAt σ.mem S i) else sigC p σ.mem sig i

theorem kv_setup (L : Layout) : (Wots.pro ++ Wots.setup L).all keepsV = true := by
  have hl : ∀ k, (([.addImm .x .x10 .x20 k] : List Instr) ++
      setFieldR .x19 (Layout.laneA k + L.adrsOff + 20) .x10 ++ setFieldR .x19 (Layout.laneB k + L.adrsOff + 20) .x10 ++
      setField .x19 (Layout.laneB k + L.adrsOff + 16) 1 ++ setField .x19 (Layout.laneB k + L.adrsOff + 24) 0 ++
      setField .x19 (Layout.laneB k + L.adrsOff + 28) 0).all keepsV = true := fun k => by
    simp only [List.all_append, kv_setFieldR, kv_setField _ _ (show (1 : Nat) < 65536 by decide),
      kv_setField _ _ (show (0 : Nat) < 65536 by decide)]; rfl
  simp only [Wots.pro, Wots.setup, List.all_append, kv_flatMap 4 hl]
  rfl

/-- The prologue and the setup: the invariant of the chains, before the first. -/
theorem start_ok (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) :
    WP isa (.block (Wots.pro ++ Wots.setup (L p))) σ (ChainInv hE 0) := by
  have hn := hz.n32
  refine wp_vk (kv_setup _) (WP.mono (setup_ok hE hz) fun t ht hvk => ?_)
  refine ⟨ht.base, hvk, by rw [ht.x21]; rfl, ht.lanes, fun _ _ _ h => absurd h (Nat.not_lt_zero _),
    fun i' hi' => ?_⟩
  rw [ite_eq_right (fun h => Nat.not_lt_zero _ h.2)]
  exact bytesAt_frame ht.scr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hE.reg.out_scr.sub_left (Offset.sub_base sig (lenN hi'))) (by omega_using [hn])

theorem wots4_wp (hE : Entry p σ S sig kp idx pkSeed a16 skSeed) (hz : Sz p) (T : Thash4Impl p.n)
    (name : String) : WP isa (Wots.wotsLeaves4 (L p) name T.code) σ (Wots4Post hE) := by
  refine WP.seq (WP.mono (start_ok hE hz) fun t h0 => ?_)
  refine WP.seq (WP.mono (chains_ok hE hz T name h0) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (leaves_ok hE hz T name h₁) fun t₂ h₂ => ?_)
  refine restore_ok hE h₂.1 fun t₃ m₃ sp₃ vk₃ cs₃ => ⟨cs₃, by rw [sp₃]; exact h₂.1.sp, VK.trans vk₃ h₂.2.1,
    by rw [m₃]; exact h₂.1.frame, by rw [m₃]; exact h₂.1.env hz, by rw [m₃]; exact h₂.2.2.1, fun i hi => ?_⟩
  show bytesAt _ _ _ = _
  rw [m₃]
  show sigC p t₂.mem sig i = _
  rw [h₂.2.2.2 i hi, h₁.sigs i hi]
  by_cases hP : InR kp idx
  · rw [ite_eq_left (⟨hP, hi⟩ : InR kp idx ∧ i < p.len), ite_eq_left hP]
  · rw [ite_eq_right (fun h => hP h.1), ite_eq_right hP]

theorem sig_flat (m : Mem) (sig : Addr) (n L : Nat) :
    bytesAt m sig (L * n) = (List.range L).flatMap fun i => bytesAt m (sig + BitVec.ofNat 64 (i * n)) n := by
  have := bytesAt_flat m sig 0 n L
  simp only [at', Nat.zero_add] at this
  rwa [show sig + BitVec.ofNat 64 0 = sig from BitVec.add_zero sig] at this

/-- The first part of `Verified`: from every state of the precondition,
`wotsLeaves4` returns, keeping what the calling convention keeps, in a state
of the postcondition. -/
theorem wots4_correct (hz : Sz p) (T : Thash4Impl p.n) (name : String) :
    ∀ s, (wots4Contract p).pre s → ∃ t s', Exec isa (Wots.wotsLeaves4 (L p) name T.code) s t s' ∧
      abiPreserved s s' ∧ (wots4Contract p).post s s' := by
  intro s ⟨hreg, ⟨pkSeed, a16, henv⟩, hkp4, hkpN, hidx, hdig⟩
  have hE : Entry p s (s.gpr .x0) (s.gpr .x3) (s.gpr .x1).toNat (s.gpr .x2).toNat pkSeed a16
      (bytesAt s.mem (at' (s.gpr .x0) Layout.oSkSeed) p.n) :=
    ⟨rfl, by simp, by simp, rfl, hreg, henv, rfl, hkp4, hkpN, hidx, hdig⟩
  obtain ⟨t, s', he, q⟩ := wots4_wp hE hz T name
  refine ⟨t, s', he, ⟨q.cs, q.sp, q.vk⟩, ?_⟩
  intro pkSeed' a16' skSeed' henv' hsk'
  have e₁ : pkSeed' = pkSeed := by rw [← henv'.seedA 0 (by decide), henv.seedA 0 (by decide)]
  have e₂ : a16' = a16 := by rw [← henv'.adrsA 0 (by decide), henv.adrsA 0 (by decide)]
  have e₃ : skSeed' = bytesAt s.mem (at' (s.gpr .x0) Layout.oSkSeed) p.n := hsk'.symm
  subst e₁ e₂ e₃
  refine ⟨q.env, q.nodes, fun hP i hi => by
      have := q.sigs i hi; rw [ite_eq_left hP] at this; exact this,
    fun hP => ?_, q.frame⟩
  rw [sig_flat, sig_flat]
  exact flatMap_range_congr fun i hi => by have := q.sigs i hi; rw [ite_eq_right hP] at this; exact this

end VG.Proof.SlhDsa.AArch64.Wots4
