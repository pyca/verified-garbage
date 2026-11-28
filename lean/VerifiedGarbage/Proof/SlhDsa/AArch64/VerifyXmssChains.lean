module

-- separate module: the groups and their loop, which the proofs of the WOTS+ key and the path do not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssStep
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopLanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `xmssPk`: the chains

A group of four chains (`chainGroup_ok`): the lanes, the steps from the
least digit to 14, each lane's end, `chain(sig_c, d_c, 15 - d_c)`
(`chain_restore`), copied to chain `c`'s place in lane 0 of `B`; and the
loop over the groups (`chains_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.SlhDsa (adrsOf)
open VG.Proof.SlhDsa.AArch64.TreeBase (Up in_scr in_scr' wp_subr wp_lsr wp_movz wp_mov wp_addi wp_subi wp_addr)

variable {p : Params}

/-- Where chain `c`'s end goes: lane 0 of `B`'s message, at `c·n`. -/
abbrev endAt (p : Params) (c : Nat) : Nat := Layout.laneB 0 + p.n + 32 + c * p.n

/-- Lane `k`'s end to chain `c`'s place in lane 0 of `B`. -/
theorem endCopy_ok (hz : Sz p) {g k : Nat} (hg : 4 * g < p.len) (hk : k < 4) {t : State} {S : Addr}
    (h19 : t.gpr .x19 = S) (h22 : t.gpr .x22 = BitVec.ofNat 64 (4 * g)) (hw : (⟨S, 65536⟩ : Region) ∈ t.wr)
    {is : List Instr} {Q : State → Prop}
    (K : ∀ t', Keep [.x10, .x11, .x12, .x13, .x14, .x15] t t' → Frame [⟨at' S (endAt p (cOf p g k)), p.n⟩] t.mem t'.mem →
      bytesAt t'.mem (at' S (endAt p (cOf p g k))) p.n = bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n →
      WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.chainOf p k ++ [Impl.SlhDsa.AArch64.Thash4.mov .x12 .x10] ++
      Impl.SlhDsa.AArch64.mulN p.n .x12 .x13 ++ ([.add .x .x12 .x12 .x19] : List Instr) ++
      Impl.SlhDsa.AArch64.copyWords .x12 (Layout.laneB 0 + (p.n + 32)) .x19 (Layout.laneA k + (p.n + 32)) (p.n / 8) ++
      is)) t Q := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have hl := hz.len
  have hcl : cOf p g k < p.len := by simp only [cOf]; omega_using [hl, hn32]
  have hcn : cOf p g k * p.n + p.n ≤ p.len * p.n := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [hcl])
  have hln : p.len * p.n ≤ 67 * 32 := Nat.mul_le_mul (by omega_using [hl, hn32]) hn32
  have eA : Layout.laneA k = 3136 + 128 * k := rfl
  have eB : Layout.laneB 0 = 3648 := rfl
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine chainOf_ok hz hg hk h19 h22 hw fun t₁ o₁ c₁ _ => wp_mov fun t₂ u₂ =>
    mulN_ok hz.nv (r := .x12) (tmp := .x13) (by decide) fun t₃ o₃ e₃ => wp_addr fun t₄ u₄ => ?_
  have g19 : t₄.gpr .x19 = S := by rw [u₄.other _ (by decide), o₃.get .x19, u₂.other _ (by decide), o₁.get .x19, h19]
  have e12 : t₄.gpr .x12 = S + BitVec.ofNat 64 (cOf p g k * p.n) := by
    rw [u₄.gpr, e₃, u₂.gpr, c₁, o₃.get .x19, u₂.other _ (by decide), o₁.get .x19, h19, ← BitVec.ofNat_mul,
      BitVec.add_comm]
  have w4 : t₄.wr = t.wr := by rw [u₄.wr, o₃.wr, u₂.wr, o₁.wr]
  have r4 : t₄.rd = t.rd := by rw [u₄.rd, o₃.rd, u₂.rd, o₁.rd]
  have m4 : t₄.mem = t.mem := by rw [u₄.mem, o₃.mem, u₂.mem, o₁.mem]
  have h8n : 8 * (p.n / 8) = p.n := by omega_using [hn8]
  have ed : S + BitVec.ofNat 64 (cOf p g k * p.n) + BitVec.ofNat 64 (Layout.laneB 0 + (p.n + 32)) =
      at' S (endAt p (cOf p g k)) := by
    rw [addr_add]; congr 2; simp only [endAt]; omega
  refine copyWords_ok (t := .x12) (sr := .x19) (d₂ := Layout.laneB 0 + (p.n + 32)) (d₁ := Layout.laneA k + (p.n + 32))
    (w := p.n / 8) ⟨by decide, by decide, ⟨by rw [eA]; omega, by rw [eA]; omega⟩, ⟨by rw [eB]; omega, by rw [eB]; omega⟩,
      (by rw [g19, r4, w4, h8n]; exact in_scr' hw (by rw [eA]; omega)),
      (by rw [e12, ed, w4, h8n]; exact in_scr hw (by simp only [endAt, Layout.laneB, Layout.oB, Layout.strideB]; omega)),
      (by rw [e12, ed, g19, h8n]
          exact Offset.disjoint S (by simp only [endAt, Layout.laneB, Layout.oB, Layout.strideB]; rw [eA]; omega)
            (by simp only [endAt, Layout.laneB, Layout.oB, Layout.strideB]; omega) (by rw [eA]; omega))⟩
    fun t₅ k₅ f₅ b₅ => ?_
  rw [e12, ed, h8n, m4] at f₅
  rw [e12, ed, h8n, g19, m4, show Layout.laneA k + (p.n + 32) = Layout.laneA k + p.n + 32 by omega] at b₅
  exact K t₅ ((((o₁.keep.trans (upOnly u₂).keep).trans o₃.keep).trans ((upOnly u₄).keep.trans k₅)).mono (by simp)) f₅ b₅

/-- Chain `c`'s value from the signature. -/
abbrev Xc (p : Params) (σ : State) (sig : Addr) (c : Nat) : List Byte :=
  bytesAt σ.mem (sig + BitVec.ofNat 64 (c * p.n)) p.n

/-- Chain `c`'s end, `chain(sig_c, d_c, 15 - d_c)`. -/
def chainEnd (p : Params) (σ : State) (sig : Addr) (pk a : List Byte) (D : List Nat) (c : Nat) : List Byte :=
  chain p (Xc p σ sig c) (D.getD c 0) (15 - D.getD c 0) pk (adrsOf a 0 (σ.gpr .x1).toNat c 0)

theorem V_end {pk a : List Byte} (ha : a.length = 16) {idx c d t₀ : Nat} {X : List Byte} (h₀ : t₀ ≤ d) (hd : d ≤ 15) :
    V p pk a idx c d X t₀ 15 = chain p X d (15 - d) pk (adrsOf a 0 idx c 0) := by
  rw [← chain_restore p pk (adrsOf a 0 idx c 0) X h₀ hd]
  simp only [V, restoreRun, setHashAddress_adrsOf ha]

theorem mnOf_le (p : Params) (m : Mem) (S : Addr) (g : Nat) :
    ∀ j, ∀ k < j, mnOf p m S g j ≤ digitAt m S (cOf p g k)
  | 0, k, hk => absurd hk (by omega)
  | j + 1, k, hk => by
    simp only [mnOf]
    by_cases e : k = j
    · subst e; omega
    · have := mnOf_le p m S g j k (by omega); omega

theorem mnOf_le15 (p : Params) (m : Mem) (S : Addr) (g : Nat) : ∀ j, mnOf p m S g j ≤ 15
  | 0 => by simp [mnOf]
  | j + 1 => by simp only [mnOf]; have := mnOf_le15 p m S g j; omega

/-- Before group `g`: the ends of the chains below `4g`. -/
structure GI (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (g : Nat) (t : State) :
    Prop where
  xk : XK p σ S sig pk a D t
  x22 : t.gpr .x22 = BitVec.ofNat 64 (4 * g)
  ends : ∀ c < min (4 * g) p.len, bytesAt t.mem (at' S (endAt p c)) p.n = chainEnd p σ sig pk a D c

theorem endAt_safe (hz : Sz p) {c : Nat} (hc : c < p.len) : Safe p (endAt p c) p.n := by
  have hn32 := hz.n32
  have hl := hz.len
  have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [hc])
  have hln : p.len * p.n = 2 * p.n * p.n + 3 * p.n := by rw [hl, Nat.add_mul]
  have hnn : 2 * p.n * p.n + 3 * p.n ≤ 2 * 32 * 32 + 3 * 32 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn32) hn32; omega
  exact .inr (.inr ⟨0, by decide, .inr ⟨by simp only [endAt]; omega, by
    simp only [endAt, Layout.laneB, Layout.oB, Layout.strideB] at *; omega⟩⟩)

theorem cOf_ge {g k : Nat} (hg : 4 * g < p.len) : 4 * g ≤ cOf p g k := by simp only [cOf]; omega

theorem endAt_disj {c c' : Nat} (h : c ≠ c') :
    endAt p c + p.n ≤ endAt p c' ∨ endAt p c' + p.n ≤ endAt p c := by
  simp only [endAt]
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left; have := Nat.mul_le_mul_right p.n (show c + 1 ≤ c' by omega); rw [Nat.succ_mul] at this; omega
  · right; have := Nat.mul_le_mul_right p.n (show c' + 1 ≤ c by omega); rw [Nat.succ_mul] at this; omega

theorem endAt_lt (hz : Sz p) {c : Nat} (hc : c < p.len) : endAt p c + p.n ≤ Layout.laneB 0 + Layout.strideB := by
  have hn32 := hz.n32
  have hl := hz.len
  have hcn : c * p.n + p.n ≤ p.len * p.n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega_using [hc])
  have hln : p.len * p.n = 2 * p.n * p.n + 3 * p.n := by rw [hl, Nat.add_mul]
  have hnn : 2 * p.n * p.n + 3 * p.n ≤ 2 * 32 * 32 + 3 * 32 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn32) hn32; omega
  simp only [endAt, Layout.laneB, Layout.oB, Layout.strideB]; omega

/-- The ends of group `g`, and its counter. -/
theorem ends_ok (hz : Sz p) {g : Nat} (hg : 4 * g < p.len) {σ t : State} {S sig : Addr} {pk a : List Byte}
    {D : List Nat} (hx : XK p σ S sig pk a D t) (h22 : t.gpr .x22 = BitVec.ofNat 64 (4 * g))
    (hA : ∀ k < 4, bytesAt t.mem (at' S (Layout.laneA k + p.n + 32)) p.n = chainEnd p σ sig pk a D (cOf p g k))
    (hE : ∀ c < min (4 * g) p.len, bytesAt t.mem (at' S (endAt p c)) p.n = chainEnd p σ sig pk a D c)
    (hfit : (⟨S, 65536⟩ : Region) ∈ t.wr) {Q : State → Prop}
    (K : ∀ t', GI p σ S sig pk a D (g + 1) t' →
      t'.gpr .x9 = (BitVec.ofNat 64 (4 * g + 4) - BitVec.ofNat 64 p.len) >>> 63 → Q t') :
    WP isa (.block ((List.range 4).flatMap (fun k => Impl.SlhDsa.AArch64.Verify.chainOf p k ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x12 .x10] : List Instr) ++ Impl.SlhDsa.AArch64.mulN p.n .x12 .x13 ++ ([.add .x .x12 .x12 .x19] : List Instr) ++
      Impl.SlhDsa.AArch64.copyWords .x12 (Layout.laneB 0 + (p.n + 32)) .x19 (Layout.laneA k + (p.n + 32)) (p.n / 8)) ++
      ([.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 p.len, .lsr .x .x9 .x9 63] : List Instr))) t Q := by
  have hn32 := hz.n32
  have hl := hz.len
  have eA : ∀ i, Layout.laneA i = 3136 + 128 * i := fun _ => rfl
  have hcl : ∀ k, cOf p g k < p.len := fun k => by simp only [cOf]; omega_using [hl, hn32]
  refine wp_rangeFlatMap (P := fun i u => XK p σ S sig pk a D u ∧ u.gpr .x22 = BitVec.ofNat 64 (4 * g) ∧
      (∀ k < 4, bytesAt u.mem (at' S (Layout.laneA k + p.n + 32)) p.n = chainEnd p σ sig pk a D (cOf p g k)) ∧
      (∀ c < min (4 * g) p.len, bytesAt u.mem (at' S (endAt p c)) p.n = chainEnd p σ sig pk a D c) ∧
      ∀ k < i, bytesAt u.mem (at' S (endAt p (cOf p g k))) p.n = chainEnd p σ sig pk a D (cOf p g k)) 4
    ⟨hx, h22, hA, hE, fun k hk => absurd hk (by omega)⟩ (fun i hi u is' ⟨xu, u22, uA, uE, uD⟩ k' => ?_) ?_
  · refine endCopy_ok hz hg hi xu.x19 u22 (by rw [xu.wr, ← hx.wr]; exact hfit) fun u' k₁ f₁ b₁ => k' u' ?_
    have hW : ∀ r ∈ [(⟨at' S (endAt p (cOf p g i)), p.n⟩ : Region)], ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l :=
      fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, _, rfl, endAt_safe hz (hcl i)⟩
    have dj : ∀ {o l : Nat}, (o + l ≤ endAt p (cOf p g i) ∨ endAt p (cOf p g i) + p.n ≤ o) → o + l ≤ 65536 →
        bytesAt u'.mem (at' S o) l = bytesAt u.mem (at' S o) l := fun h₁ h₂ =>
      TreeBase.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := endAt_lt hz (hcl i)
        simp only [Layout.laneB, Layout.oB, Layout.strideB] at this
        exact Offset.disjoint S h₁ (by omega) (by omega)) (by omega)
    have hB : ∀ c, c < p.len → endAt p c + p.n ≤ 65536 := fun c hc => by
      have := endAt_lt hz hc; simp only [Layout.laneB, Layout.oB, Layout.strideB] at this; omega
    have eB : Layout.laneB 0 = 3648 := rfl
    have hB0 : 3648 + p.n + 32 ≤ endAt p (cOf p g i) := by simp only [endAt]; rw [eB]; omega
    refine ⟨XK.step hz xu (by decide) k₁ f₁ hW, by rw [k₁.get .x22, u22], fun k hk => ?_, fun c hc => ?_, fun k hk => ?_⟩
    · rw [dj (.inl (by rw [eA]; omega)) (by rw [eA]; omega)]
      exact uA k hk
    · rw [dj (endAt_disj (show c ≠ cOf p g i by have := cOf_ge (p := p) (k := i) hg; omega)) (hB c (by omega))]
      exact uE c hc
    · by_cases e : cOf p g k = cOf p g i
      · rw [e, b₁, uA i hi]
      · have hki : k < i := by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
          · exact h
          · exact absurd (h ▸ rfl) e
        rw [dj (endAt_disj e) (hB _ (hcl k))]; exact uD k hki
  · intro u ⟨xu, u22, uA, uE, uD⟩
    refine wp_addi (by decide) fun u₁ v₁ => wp_subi (by omega) fun u₂ v₂ => wp_lsr (by decide) fun u₃ v₃ =>
      MlKem.AArch64.wp_nil (K u₃ ⟨XK.step hz xu (by decide) (((upOnly v₁).keep.trans (upOnly v₂).keep).trans
        (upOnly v₃).keep) (by rw [v₃.mem, v₂.mem, v₁.mem]; exact Frame.refl _ _) (fun r hr => absurd hr List.not_mem_nil),
        by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, u22, show 4 * (g + 1) = 4 * g + 4 by omega,
          BitVec.ofNat_add], fun c hc => ?_⟩ ?_)
    · rw [v₃.mem, v₂.mem, v₁.mem]
      by_cases h : c < 4 * g
      · exact uE c (by omega)
      · have hk : c - 4 * g < 4 := by omega
        have e : cOf p g (c - 4 * g) = c := by simp only [cOf]; omega
        have := uD (c - 4 * g) hk
        rw [e] at this; exact this
    · rw [v₃.gpr, v₂.gpr, v₁.gpr, u22, BitVec.ofNat_add]

theorem sub15_eq : ∀ j < 16, (BitVec.ofNat 64 j - BitVec.ofNat 64 15 == 0) = decide (j = 15) := by decide

theorem sub15_ne : ∀ j < 16, (BitVec.ofNat 64 j - BitVec.ofNat 64 15 != 0) = decide (j ≠ 15) := by decide

theorem endAt_aW (hz : Sz p) {c : Nat} (hc : c < p.len) {S : Addr} :
    ∀ r ∈ aW p S, Region.Disjoint ⟨at' S (endAt p c), p.n⟩ r := by
  have hn32 := hz.n32
  have h₁ := endAt_lt hz hc
  have eA : ∀ i, Layout.laneA i = 3136 + 128 * i := fun _ => rfl
  have eB : Layout.laneB 0 = 3648 := rfl
  have eS : Layout.strideB = 2208 := rfl
  have eW : workUsed = 1008 := rfl
  have h₀ : 3648 ≤ endAt p c := by simp only [endAt]; rw [eB]; omega
  rw [eB, eS] at h₁
  intro r hr
  simp only [aW, List.mem_cons, List.mem_map, List.mem_range] at hr
  rcases hr with rfl | ⟨k, hk, rfl⟩
  · exact Offset.disjoint_base S (by rw [eW]; omega) (by omega)
  · have e₂ : Layout.strideA = 128 := rfl
    rw [e₂]
    exact Offset.disjoint S (.inr (by rw [eA]; omega)) (by omega) (by rw [eA]; omega)

theorem endAt_allW (hz : Sz p) {c : Nat} (hc : c < p.len) {S : Addr} :
    ∀ r ∈ allW p S, Region.Disjoint ⟨at' S (endAt p c), p.n⟩ r := by
  have hn32 := hz.n32
  have h₁ := endAt_lt hz hc
  have eA : ∀ i, Layout.laneA i = 3136 + 128 * i := fun _ => rfl
  have eB : Layout.laneB 0 = 3648 := rfl
  have eS : Layout.strideB = 2208 := rfl
  have h₀ : 3648 ≤ endAt p c := by simp only [endAt]; rw [eB]; omega
  rw [eB, eS] at h₁
  intro r hr
  obtain ⟨k, hk, hr⟩ := List.mem_flatMap.mp hr
  rw [List.mem_range] at hk
  simp only [laneW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  all_goals exact Offset.disjoint S (.inr (by rw [eA]; omega)) (by omega) (by rw [eA]; omega)

/-- A pass of the steps' loop, at measure `m`, from step `15 - m`. -/
theorem steps_step (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) {g t₀ : Nat}
    (hg : 4 * g < p.len) {tg : State} (m : Nat) (u : State)
    (hI : 1 ≤ m ∧ m + t₀ ≤ 15 ∧ SI p σ tg S sig pk a D g t₀ (15 - m) u) :
    WP isa (Impl.SlhDsa.AArch64.Verify.stepBody p f) u fun u' =>
      isa.eval (.nonzero .x .x9) u' = some (decide (m ≠ 1)) ∧
      (decide (m ≠ 1) = false → SI p σ tg S sig pk a D g t₀ 15 u') ∧
      (decide (m ≠ 1) = true → m - 1 < m ∧
        (1 ≤ m - 1 ∧ m - 1 + t₀ ≤ 15 ∧ SI p σ tg S sig pk a D g t₀ (15 - (m - 1)) u')) := by
  obtain ⟨h1, h2, hu⟩ := hI
  refine WP.mono (step_ok hz T ht hR hidx hg (by omega : t₀ ≤ 15 - m) (by omega : 15 - m < 15) hu)
    fun u' ⟨hs, h9⟩ => ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · rw [MlKem.AArch64.eval_nonzero, h9, sub15_ne (15 - m + 1) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · have : m = 1 := by simpa using hc
    rwa [show 15 - m + 1 = 15 by omega] at hs
  · have : m ≠ 1 := by simpa using hc
    exact ⟨by omega, by omega, by omega, by rwa [show 15 - (m - 1) = 15 - m + 1 by omega]⟩

/-- The steps of group `g`, from its least digit `t₀`. -/
theorem groupIte_ok (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) {g t₀ : Nat}
    (hg : 4 * g < p.len) (h15 : t₀ ≤ 15) {t₃ : State}
    (v9 : t₃.gpr .x9 = BitVec.ofNat 64 t₀ - BitVec.ofNat 64 15) (S₀ : SI p σ t₃ S sig pk a D g t₀ t₀ t₃) :
    WP isa (.ite (.zero .x .x9) (.block [])
      (.loop (Impl.SlhDsa.AArch64.Verify.stepBody p f) (.nonzero .x .x9))) t₃
      (SI p σ t₃ S sig pk a D g t₀ 15) := by
  refine WP.ite _ (MlKem.AArch64.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have e : t₀ = 15 := by rw [v9, sub15_eq t₀ (by omega)] at hb; exact of_decide_eq_true hb
    subst e; exact WP.block_nil S₀
  · have e : t₀ ≠ 15 := by rw [v9, sub15_eq t₀ (by omega)] at hb; exact of_decide_eq_false hb
    exact TreeBase.wpLoop (I := fun m u => 1 ≤ m ∧ m + t₀ ≤ 15 ∧ SI p σ t₃ S sig pk a D g t₀ (15 - m) u)
      (fun m => decide (m ≠ 1)) (fun m => m - 1) (steps_step hz T ht hR hidx hg) (15 - t₀)
      ⟨by omega, by omega, by rw [show 15 - (15 - t₀) = t₀ by omega]; exact S₀⟩

/-- The least of group `g`'s first `j` digits, from the digits `D`. -/
def mnD (p : Params) (D : List Nat) (g : Nat) : Nat → Nat
  | 0 => 15
  | j + 1 => min (mnD p D g j) (D.getD (cOf p g j) 0)

theorem mnOf_eq (hz : Sz p) {m : Mem} {S : Addr} {D : List Nat} {g : Nat} (hg : 4 * g < p.len)
    (hd : ∀ i < p.len, digitAt m S i = D.getD i 0) : ∀ j, mnOf p m S g j = mnD p D g j
  | 0 => rfl
  | j + 1 => by
    have hc : cOf p g j < p.len := by simp only [cOf]; have := hz.len; have := hz.n32; omega
    simp only [mnOf, mnD, mnOf_eq hz hg hd j, hd _ hc]

/-- After the lanes of group `g` and `x23 ← x24`: the steps from the least digit. -/
structure PM (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (g : Nat) (t₃ : State) :
    Prop where
  h15 : mnD p D g 4 ≤ 15
  x9 : t₃.gpr .x9 = BitVec.ofNat 64 (mnD p D g 4) - BitVec.ofNat 64 15
  si : SI p σ t₃ S sig pk a D g (mnD p D g 4) (mnD p D g 4) t₃
  le : ∀ k < 4, mnD p D g 4 ≤ D.getD (cOf p g k) 0
  ends : ∀ c < min (4 * g) p.len, bytesAt t₃.mem (at' S (endAt p c)) p.n = chainEnd p σ sig pk a D c

/-- `x23 ← x24` and `x9 ← x24 - 15`, after the lanes. -/
theorem lanesMid_ok (hz : Sz p) {σ t t₁ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) {g : Nat} (hg : 4 * g < p.len)
    (hG : GI p σ S sig pk a D g t) (c₁ : CLI p t S sig g 4 t₁) :
    WP isa (.block [Impl.SlhDsa.AArch64.Thash4.mov .x23 .x24, .subImm .x .x9 .x24 15]) t₁
      (PM p σ S sig pk a D g) := by
  have hn32 := hz.n32
  have hl := hz.len
  have hcl : ∀ k, cOf p g k < p.len := fun k => by simp only [cOf]; omega_using [hl, hn32]
  have et₀ := mnOf_eq hz hg hG.xk.dig 4
  have X₁ : XK p σ S sig pk a D t₁ := XK.step hz hG.xk (by decide) c₁.keep c₁.frame (allW_safe hz)
  refine wp_mov fun t₂ u₂ => wp_subi (by decide) fun t₃ u₃ => MlKem.AArch64.wp_nil ?_
  have K3 : Keep [.x23, .x9] t₁ t₃ := (upOnly u₂).keep.trans (upOnly u₃).keep
  have v23 : t₃.gpr .x23 = BitVec.ofNat 64 (mnD p D g 4) := by rw [u₃.other _ (by decide), u₂.gpr, c₁.x24, et₀]
  have v24 : t₃.gpr .x24 = BitVec.ofNat 64 (mnD p D g 4) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), c₁.x24, et₀]
  have m3 : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
  have X₃ : XK p σ S sig pk a D t₃ := XK.step hz X₁ (by decide) K3 (by rw [m3]; exact Frame.refl _ _)
    (fun r hr => absurd hr List.not_mem_nil)
  refine ⟨et₀ ▸ mnOf_le15 p t.mem S g 4, by rw [u₃.gpr, u₂.other _ (by decide), c₁.x24, et₀], ?_,
    fun k hk => ?_, fun c hc => ?_⟩
  · refine ⟨X₃, by rw [K3.get .x22, c₁.keep.get .x22, hG.x22], v23, v24, fun k hk => ?_, fun k hk => ?_,
      Frame.refl _ _⟩
    · have L := c₁.lanes k hk
      rw [hG.xk.x20] at L
      rw [m3]; exact ⟨L.ty, L.kp, L.ch⟩
    · have hcn : cOf p g k * p.n + p.n ≤ p.xmssSigLen := by
        rw [xmssSigLen_eq', ← Nat.succ_mul]
        exact Nat.le_add_right_of_le (Nat.mul_le_mul_right _ (by have := hcl k; omega))
      rw [m3, (c₁.lanes k hk).msg, hG.xk.sigB hz hR hcn]
      simp only [V, Nat.sub_self, List.range_zero, List.foldl_nil]
  · have hle := mnOf_le p t.mem S g 4 k hk
    rw [et₀, hG.xk.dig _ (hcl k)] at hle
    exact hle
  · have hc' : c < p.len := by omega
    rw [m3, TreeBase.bytesAt_frame c₁.frame (endAt_allW hz hc') (by omega)]
    exact hG.ends c hc

/-- The ends of group `g`, after its steps. -/
theorem groupEnd_ok (hz : Sz p) {σ t₃ u : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (ha : a.length = 16)
    (hD : ∀ i < p.len, D.getD i 0 < 16) {g : Nat} (hg : 4 * g < p.len) (hP : PM p σ S sig pk a D g t₃)
    (hu : SI p σ t₃ S sig pk a D g (mnD p D g 4) 15 u) :
    WP isa (.block ((List.range 4).flatMap (fun k => Impl.SlhDsa.AArch64.Verify.chainOf p k ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x12 .x10] : List Instr) ++ Impl.SlhDsa.AArch64.mulN p.n .x12 .x13 ++ ([.add .x .x12 .x12 .x19] : List Instr) ++
      Impl.SlhDsa.AArch64.copyWords .x12 (Layout.laneB 0 + (p.n + 32)) .x19 (Layout.laneA k + (p.n + 32)) (p.n / 8)) ++
      ([.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 p.len, .lsr .x .x9 .x9 63] : List Instr))) u fun t' =>
      GI p σ S sig pk a D (g + 1) t' ∧
        t'.gpr .x9 = (BitVec.ofNat 64 (4 * g + 4) - BitVec.ofNat 64 p.len) >>> 63 := by
  have hn32 := hz.n32
  have hl := hz.len
  have hcl : ∀ k, cOf p g k < p.len := fun k => by simp only [cOf]; omega_using [hl, hn32]
  have hfit : (⟨S, 65536⟩ : Region) ∈ u.wr := by rw [hu.xk.wr]; exact TreeBase.regions_scr hR
  refine ends_ok hz hg hu.xk hu.x22 (fun k hk => ?_) (fun c hc => ?_) hfit fun t' h₁ h₂ => ⟨h₁, h₂⟩
  · rw [hu.msg k hk]
    exact V_end ha (hP.le k hk) (by have := hD _ (hcl k); omega)
  · have hc' : c < p.len := by omega
    rw [TreeBase.bytesAt_frame hu.frame (endAt_aW hz hc') (by omega)]
    exact hP.ends c hc

/-- Group `g` of four chains. -/
theorem chainGroup_ok (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ t : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) (ha : a.length = 16)
    (hD : ∀ i < p.len, D.getD i 0 < 16) {g : Nat} (hg : 4 * g < p.len) (hG : GI p σ S sig pk a D g t) :
    WP isa (Impl.SlhDsa.AArch64.Verify.chainGroup p f) t fun t' => GI p σ S sig pk a D (g + 1) t' ∧
      t'.gpr .x9 = (BitVec.ofNat 64 (4 * g + 4) - BitVec.ofNat 64 p.len) >>> 63 := by
  unfold Impl.SlhDsa.AArch64.Verify.chainGroup
  refine WP.seq ?_
  rw [← List.append_nil (Impl.SlhDsa.AArch64.Verify.chainLanes p)]
  refine chainLanes_ok hz hg (hG.xk.laneIn hR hidx) hG.x22 fun t₁ c₁ => MlKem.AArch64.wp_nil ?_
  refine WP.seq (WP.mono (lanesMid_ok hz hR hg hG c₁) fun t₃ hP => ?_)
  exact WP.seq (WP.mono (groupIte_ok hz T ht hR hidx hg hP.h15 hP.x9 hP.si) fun u hu =>
    groupEnd_ok hz hR ha hD hg hP hu)

theorem more_tab : ∀ g < 17, ∀ l ∈ ([35, 51, 67] : List Nat),
    ((BitVec.ofNat 64 (4 * g + 4) - BitVec.ofNat 64 l) >>> 63 != 0) = decide (4 * g + 4 < l) := by decide

theorem more_eq (hz : Sz p) {g : Nat} (hg : 4 * g < p.len) :
    ((BitVec.ofNat 64 (4 * g + 4) - BitVec.ofNat 64 p.len) >>> 63 != 0) = decide (4 * g + 4 < p.len) := by
  have hl := hz.len
  have hg' : g < 17 := by have := hz.n32; omega
  exact more_tab g hg' _ (by rw [hl]; rcases hz.nv with e | e | e <;> rw [e] <;> decide)

/-- The number of groups. -/
abbrev nG (p : Params) : Nat := (p.len + 3) / 4

/-- A pass of the groups' loop, at measure `m`, from group `nG - m`. -/
theorem groups_step (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) (ha : a.length = 16)
    (hD : ∀ i < p.len, D.getD i 0 < 16) (m : Nat) (u : State)
    (hI : 1 ≤ m ∧ m ≤ nG p ∧ GI p σ S sig pk a D (nG p - m) u) :
    WP isa (Impl.SlhDsa.AArch64.Verify.chainGroup p f) u fun u' =>
      isa.eval (.nonzero .x .x9) u' = some (decide (m ≠ 1)) ∧
      (decide (m ≠ 1) = false → XK p σ S sig pk a D u' ∧
        ∀ c < p.len, bytesAt u'.mem (at' S (endAt p c)) p.n = chainEnd p σ sig pk a D c) ∧
      (decide (m ≠ 1) = true → m - 1 < m ∧ (1 ≤ m - 1 ∧ m - 1 ≤ nG p ∧ GI p σ S sig pk a D (nG p - (m - 1)) u')) := by
  have hl := hz.len
  have hn16 := hz.n16
  obtain ⟨h1, h2, hu⟩ := hI
  have hg : 4 * (nG p - m) < p.len := by simp only [nG]; omega
  refine WP.mono (chainGroup_ok hz T ht hR hidx ha hD hg hu) fun u' ⟨hs, h9⟩ => ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · rw [MlKem.AArch64.eval_nonzero, h9, more_eq hz hg]
    exact congrArg some (decide_eq_decide.mpr (by simp only [nG]; omega))
  · have : m = 1 := by simpa using hc
    subst this
    rw [show nG p - 1 + 1 = nG p by omega] at hs
    exact ⟨hs.xk, fun c hc => hs.ends c (by simp only [nG]; omega)⟩
  · have : m ≠ 1 := by simpa using hc
    exact ⟨by omega, by omega, by omega, by rwa [show nG p - (m - 1) = nG p - m + 1 by omega]⟩

/-- The loop over the groups: every chain's end in lane 0 of `B`. -/
theorem chains_ok (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    {σ t : State} {S sig : Addr} {pk a : List Byte} {D : List Nat}
    (hR : Regions σ S [⟨sig, p.xmssSigLen⟩] ⟨S, 0⟩) (hidx : (σ.gpr .x1).toNat < 2 ^ 32) (ha : a.length = 16)
    (hD : ∀ i < p.len, D.getD i 0 < 16) (hx : XK p σ S sig pk a D t) (h22 : t.gpr .x22 = BitVec.ofNat 64 0) :
    WP isa (.loop (Impl.SlhDsa.AArch64.Verify.chainGroup p f) (.nonzero .x .x9)) t fun u =>
      XK p σ S sig pk a D u ∧ ∀ c < p.len, bytesAt u.mem (at' S (endAt p c)) p.n = chainEnd p σ sig pk a D c := by
  have hl := hz.len
  have hn16 := hz.n16
  exact TreeBase.wpLoop _ _ (groups_step hz T ht hR hidx ha hD) (nG p)
    ⟨by simp only [nG]; omega, Nat.le_refl _, by rw [Nat.sub_self]; exact ⟨hx, h22, fun c hc => absurd hc (by omega)⟩⟩

end VG.Proof.SlhDsa.AArch64.XmssPk
