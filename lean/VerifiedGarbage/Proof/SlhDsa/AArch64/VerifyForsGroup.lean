module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyForsHeight
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `forsPk`: a group of four trees

A tree's node at a height (`rootZ`, the path from its leaf); the heights of
a group (`heights_step`, a pass of their loop); each lane's root to lane 0 of
`B` (`rootLane_ok`, `roots_ok`); and a group (`forsGroup_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.ForsPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (in_scr in_scr' disj_scr bytesAt_frame readW_frame)
open VG.Proof.MlKem.AArch64 (Only Keep)

variable {p : Params}

/-- String `z` of the `c` strings of `n` bytes at `a`. -/
theorem chunk_bytes (m : Mem) (a : Addr) {n z c : Nat} (hz : z < c) :
    chunk (bytesAt m a (c * n)) n z = bytesAt m (a + BitVec.ofNat 64 (n * z)) n := by
  have hl : (chunk (bytesAt m a (c * n)) n z).length = n := by
    simp only [chunk, List.length_take, List.length_drop, bytesAt, List.length_map, List.length_range]
    have : n ≤ c * n - n * z := by
      rw [Nat.mul_comm n z, ← Nat.sub_mul]
      exact Nat.le_mul_of_pos_left n (by omega)
    omega
  apply List.ext_getElem (by rw [hl]; simp [bytesAt])
  intro i h₁ h₂
  have hi : i < n := by rw [hl] at h₁; exact h₁
  have hzn : n * z + i < c * n := by
    have : n * z + n ≤ c * n := by rw [Nat.mul_comm c n, ← Nat.mul_succ]; exact Nat.mul_le_mul_left n hz
    omega
  simp only [chunk, List.getElem_take, List.getElem_drop, bytesAt, List.getElem_map, List.getElem_range]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Tree `T`'s node at height `z` on the path from its leaf, from the signature at `sig`. -/
def rootZ (p : Params) (m : Mem) (sig : Addr) (pk a : List Byte) (kp : Nat) (I : Nat → Nat) (T z : Nat) :
    List Byte :=
  path p pk a 3 kp (T * 2 ^ p.a + I T) (bytesAt m (sig + BitVec.ofNat 64 (sigOff p T + p.n)) (p.a * p.n)) z
    (F p pk (adrsOf a 3 kp 0 (T * 2 ^ p.a + I T)) (bytesAt m (sig + BitVec.ofNat 64 (sigOff p T)) p.n))

theorem rootZ_succ {m : Mem} {sig : Addr} {pk a : List Byte} {kp : Nat} {I : Nat → Nat} {t₀ z : Nat} (k' : Nat)
    (hz : z < p.a) :
    H p pk (adrsOf a 3 kp (z + 1) (lOf p I t₀ k' / 2 ^ (z + 1)))
        (yOf p m sig I t₀ z k' (rootZ p m sig pk a kp I (tOf p t₀ k') z)) =
      rootZ p m sig pk a kp I (tOf p t₀ k') (z + 1) := by
  simp only [rootZ, path, yOf, authOf, lOf]
  rw [chunk_bytes _ _ hz, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_comm p.n z]

/-- `x - y`, for small `x ≤ y`, is zero iff `x = y`. -/
theorem sub_ne {x y : Nat} (hx : x ≤ y) (hy : y < 2 ^ 63) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 y != 0) = decide (x ≠ y) := by
  rw [MlKem.AArch64.ne_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]
  by_cases h : x = y
  · subst h; rw [Nat.sub_add_cancel (by omega), Nat.mod_self]; simp
  · rw [Nat.mod_eq_of_lt (show 2 ^ 64 - y + x < 2 ^ 64 by omega)]
    exact decide_eq_decide.mpr ⟨fun _ => h, fun _ => by omega⟩

/-! ## The heights -/

/-- The heights' loop at measure `m`: height `a - m`. -/
def HI (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (I : Nat → Nat) (t₀ : Nat) (u₀ : State)
    (m : Nat) (u : State) : Prop :=
  1 ≤ m ∧ m ≤ p.a ∧ GS p σ S sig pk a I t₀ (p.a - m)
    (fun k' => rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I (tOf p t₀ k') (p.a - m)) u₀ u ∧
    u.gpr .x23 = BitVec.ofNat 64 (p.a - m)

/-- A pass of the heights' loop. -/
theorem heights_step (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (ht : f.t4 = T.code) {t₀ : Nat} (ht₀ : t₀ < 2 ^ 32) {u₀ : State} (m : Nat) (u : State)
    (hu : HI p σ S sig pk a I t₀ u₀ m u) :
    WP isa (Impl.SlhDsa.AArch64.Verify.forsUp p f) u fun u' =>
      isa.eval (.nonzero .x .x9) u' = some (decide (m ≠ 1)) ∧
      (decide (m ≠ 1) = false → GS p σ S sig pk a I t₀ p.a
        (fun k' => rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I (tOf p t₀ k') p.a) u₀ u') ∧
      (decide (m ≠ 1) = true → m - 1 < m ∧ HI p σ S sig pk a I t₀ u₀ (m - 1) u') := by
  obtain ⟨hm1, hma, hg, h23⟩ := hu
  have ha := hF.a
  refine WP.mono (forsUp_ok hF c hIa T ht ht₀ (by omega) hg h23) fun u' ⟨hg', h23', h9'⟩ => ?_
  have e : ∀ k', H p pk (adrsOf a 3 (σ.gpr .x2).toNat (p.a - m + 1) (lOf p I t₀ k' / 2 ^ (p.a - m + 1)))
      (yOf p σ.mem sig I t₀ (p.a - m) k' (rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I (tOf p t₀ k') (p.a - m))) =
      rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I (tOf p t₀ k') (p.a - m + 1) := fun k' => rootZ_succ k' (by omega)
  simp only [e] at hg'
  have hev : isa.eval (.nonzero .x .x9) u' = some (decide (m ≠ 1)) := by
    rw [MlKem.AArch64.eval_nonzero, h9', sub_ne (x := p.a - m + 1) (y := p.a) (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr ⟨fun h h' => h (by omega), fun h h' => h (by omega)⟩)
  refine ⟨hev,
    fun hd => ?_, fun hd => ?_⟩
  · have : m = 1 := by simpa using hd
    subst this
    rwa [show p.a - 1 + 1 = p.a by omega] at hg'
  · have : m ≠ 1 := by simpa using hd
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rwa [show p.a - m + 1 = p.a - (m - 1) by omega] at hg'
    · rw [h23']; congr 1; omega

/-! ## The roots -/

/-- Tree `c`'s root's place in lane 0 of `B`. -/
abbrev rootAt (p : Params) (S : Addr) (c : Nat) : Addr := at' S (Layout.laneB 0 + p.n + 32 + c * p.n)

/-- The roots of the trees below `N`. -/
def RT (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (I : Nat → Nat) (N : Nat) (m : Mem) : Prop :=
  ∀ c < p.k, c < N → bytesAt m (rootAt p S c) p.n = rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I c p.a

theorem root_sep {c T n : Nat} (h : c ≠ T) : c * n + n ≤ T * n ∨ T * n + n ≤ c * n := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h)
  · exact .inr (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h)

theorem root_le {c : Nat} (hc : c < p.k) : c * p.n + p.n ≤ p.k * p.n := by
  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc

/-- The block of lane `k`'s root. -/
abbrev rootL (p : Params) (k' : Nat) : List Instr :=
  Impl.SlhDsa.AArch64.Verify.treeT p k' ++ [Impl.SlhDsa.AArch64.Thash4.mov .x11 .x10] ++ Impl.SlhDsa.AArch64.mulN p.n .x11 .x13 ++
    [.add .x .x11 .x11 .x19] ++
    Impl.SlhDsa.AArch64.copyWords .x11 (Layout.laneB 0 + (Impl.SlhDsa.AArch64.Shake.layout p).msgOff) .x19
      (Layout.laneA k' + (Impl.SlhDsa.AArch64.Shake.layout p).msgOff) (p.n / 8)

theorem rootLane_ok (hF : FP p) {k' t₀ : Nat} (hk' : k' < 4) (ht₀ : t₀ < 2 ^ 32) {S : Addr} {u : State}
    (h19 : u.gpr .x19 = S) (h22 : u.gpr .x22 = BitVec.ofNat 64 t₀) (hw : (⟨S, 65536⟩ : Region) ∈ u.wr)
    {is : List Instr} {Q : State → Prop}
    (K : ∀ u', Keep [.x10, .x11, .x13, .x14, .x15] u u' → Frame [⟨rootAt p S (tOf p t₀ k'), p.n⟩] u.mem u'.mem →
      bytesAt u'.mem (rootAt p S (tOf p t₀ k')) p.n = bytesAt u.mem (at' S (Layout.laneA k' + p.n + 32)) p.n →
      WP isa (.block is) u' Q) :
    WP isa (.block (rootL p k' ++ is)) u Q := by
  have hn32 := hF.n32
  have hn8 := hF.n8
  have hL := ForsPk.laneA_eq k'
  have hB := laneB0_eq
  have hT := tOf_lt hF t₀ k'
  have hTn := root_le hT
  have hkn := hF.kn
  have e8 : 8 * (p.n / 8) = p.n := by omega
  simp only [rootL, Impl.SlhDsa.AArch64.Shake.layout, Layout.msgOff, List.append_assoc, List.cons_append,
    List.nil_append]
  refine treeT_ok hF hk' ht₀ h22 fun u₁ o₁ e₁ => MlKem.AArch64.wp_addImm (by decide) fun u₂ o₂ e₂ =>
    mulN_ok hF.nv (r := .x11) (tmp := .x13) (by decide) fun u₃ o₃ e₃ => MlKem.AArch64.wp_add fun u₄ o₄ e₄ => ?_
  have o₁₄ : Only [.x10, .x13, .x14, .x15, .x11] u u₄ := ((o₁.trans o₂).trans (o₃.trans o₄)).mono (by decide)
  have hb₄ : u₄.gpr .x19 = S := by rw [o₁₄.get .x19, h19]
  have hd₄ : u₄.gpr .x11 + BitVec.ofNat 64 (Layout.laneB 0 + (p.n + 32)) = rootAt p S (tOf p t₀ k') := by
    rw [e₄, e₃, e₂, e₁, o₃.get .x19, o₂.get .x19, o₁.get .x19, h19, BitVec.add_zero, BitVec.ofNat_mul_ofNat,
      BitVec.add_comm _ S, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    show S + _ = S + _
    congr 2; omega
  have hw₄ : (⟨S, 65536⟩ : Region) ∈ u₄.wr := by rw [o₁₄.wr]; exact hw
  refine copyWords_ok (t := .x11) (sr := .x19) (d₂ := Layout.laneB 0 + (p.n + 32)) (d₁ := Layout.laneA k' + (p.n + 32))
    (w := p.n / 8) ⟨by decide, by decide, by omega, by omega, by rw [hb₄]; exact in_scr' hw₄ (by omega),
      by rw [hd₄, e8]; exact in_scr hw₄ (by omega),
      by rw [hd₄, hb₄, e8]; exact disj_scr S (by omega) (by omega) (by omega)⟩ fun u' k₁ f₁ c₁ => ?_
  rw [hd₄, e8] at f₁ c₁
  rw [hb₄, show Layout.laneA k' + (p.n + 32) = Layout.laneA k' + p.n + 32 by omega, o₁₄.mem] at c₁
  rw [o₁₄.mem] at f₁
  exact K u' ((o₁₄.keep.trans k₁).mono (by decide)) f₁ c₁

theorem gwL_roots (hF : FP p) (S : Addr) : ∀ r ∈ gwL p S,
    Region.Disjoint ⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩ r := by
  have hn := hF.n32
  have hkn := hF.kn
  intro r hr
  simp only [gwL, List.mem_cons, List.mem_map, List.mem_range] at hr
  rcases hr with rfl | ⟨k, hk, rfl⟩
  · have := disj_scr (o := Layout.laneB 0 + p.n + 32) (l := p.k * p.n) (o' := 0) (l' := workUsed) S
      (by rw [laneB0_eq]; simp only [workUsed]; omega) (by rw [laneB0_eq]; omega) (by simp only [workUsed]; omega)
    simpa using this
  · simp only [tailA, laneA_eq, Layout.strideA, laneB0_eq]
    exact disj_scr S (by omega) (by omega) (by omega)

/-- The roots past a frame in `gwL`. -/
theorem RT.keep {σ : State} {S sig : Addr} {pk a : List Byte} {I : Nat → Nat} {N : Nat} {m m' : Mem} (hF : FP p)
    (h : RT p σ S sig pk a I N m) (hf : Frame (gwL p S) m m') : RT p σ S sig pk a I N m' := fun c hc hN => by
  have := root_le hc
  have hn := hF.n32
  have e : bytesAt m' (rootAt p S c) p.n = bytesAt m (rootAt p S c) p.n :=
    bytesAt_frame hf (fun r hr => (gwL_roots hF S r hr).sub_left (Offset.sub S (by omega) (by omega))) (by omega)
  rw [e]; exact h c hc hN


/-- The roots' block: each lane's root to its place, then the next group's first tree. -/
theorem roots_ok (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte} {I : Nat → Nat}
    {t₀ : Nat} (ht₀ : t₀ < p.k) {u : State} (hK : FK p σ S sig pk a I u) (h22 : u.gpr .x22 = BitVec.ofNat 64 t₀)
    (hl : ∀ k' < 4, bytesAt u.mem (at' S (Layout.laneA k' + p.n + 32)) p.n =
      rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I (tOf p t₀ k') p.a)
    (hR : RT p σ S sig pk a I t₀ u.mem) :
    WP isa (.block ((List.range 4).flatMap (rootL p) ++
      ([.addImm .x .x22 .x22 4, .subImm .x .x9 .x22 p.k, .lsr .x .x9 .x9 63] : List Instr))) u fun u' =>
      FK p σ S sig pk a I u' ∧ u'.gpr .x22 = BitVec.ofNat 64 (t₀ + 4) ∧
      u'.gpr .x9 = BitVec.ofNat 64 (if t₀ + 4 < p.k then 1 else 0) ∧ RT p σ S sig pk a I (t₀ + 4) u'.mem := by
  have hn32 := hF.n32
  have hkn := hF.kn
  have hk := hF.k
  have hB := laneB0_eq
  let P : Nat → State → Prop := fun j v => FK p σ S sig pk a I v ∧ Keep [.x10, .x11, .x13, .x14, .x15] u v ∧
    Frame [(⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩ : Region)] u.mem v.mem ∧ ∀ c' < p.k, (c' < t₀ ∨ ∃ k' < j, c' = tOf p t₀ k') →
      bytesAt v.mem (rootAt p S c') p.n = rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I c' p.a
  have hsubR : ∀ {T : Nat}, T < p.k → ∀ r ∈ [(⟨rootAt p S T, p.n⟩ : Region)], ∃ R ∈ [(⟨at' S (Layout.laneB 0 + p.n + 32), p.k * p.n⟩ : Region)], Region.Sub r R :=
    fun hT => by have := root_le hT; exact sub1 S (by omega) (by omega)
  refine Fors.wp_flatRange (P := P) 4 ⟨hK, Keep.refl _ _, Frame.refl _ _, fun c' hc h => ?_⟩
    (fun j hj v is' ⟨hv, kv, fv, rv⟩ k' => ?_) fun v ⟨hv, kv, fv, rv⟩ => ?_
  · rcases h with h | ⟨k', hk', _⟩
    · exact hR c' hc h
    · exact absurd hk' (by omega)
  · have hT := tOf_lt hF t₀ j
    refine rootLane_ok hF hj (by omega) hv.x19 (by rw [kv.get .x22, h22]) (by rw [hv.wr]; exact c.scr)
      fun v' k₁ f₁ c₁ => k' v' ⟨hv.keep hF k₁ (by decide) (by decide) (by decide) (by decide)
        ((f₁.sub (hsubR hT)).mono fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact roots_gw S),
        (kv.trans k₁).mono (by decide), fv.trans (f₁.sub (hsubR hT)), fun c' hc h => ?_⟩
    by_cases e : c' = tOf p t₀ j
    · rw [e, c₁, k1 fv (by rw [laneA_eq, hB]; omega) (by rw [laneA_eq]; omega) (by rw [hB]; omega), hl j hj]
    · have := root_le hc
      have := root_le hT
      have hs := root_sep (n := p.n) e
      show bytesAt v'.mem (at' S (Layout.laneB 0 + p.n + 32 + c' * p.n)) p.n = _
      rw [k1 (o := Layout.laneB 0 + p.n + 32 + tOf p t₀ j * p.n) f₁ (by omega) (by omega) (by omega)]
      refine rv c' hc (h.imp_right fun ⟨k'', hk'', h'⟩ => ⟨k'', ?_, h'⟩)
      by_contra hne
      exact e (by rw [h', show k'' = j by omega])
  · refine MlKem.AArch64.wp_addImm (by decide) fun v₁ o₁ e₁ => MlKem.AArch64.wp_subImm (by omega) fun v₂ o₂ e₂ =>
      MlKem.AArch64.wp_lsr (by decide) fun v₃ o₃ e₃ => WP.block_nil ?_
    have o₁₃ : Only [.x22, .x9] v v₃ := ((o₁.trans o₂).trans o₃).mono (by decide)
    have h22' : v₁.gpr .x22 = BitVec.ofNat 64 (t₀ + 4) := by rw [e₁, kv.get .x22, h22, BitVec.ofNat_add_ofNat]
    refine ⟨hv.keep hF o₁₃.keep (by decide) (by decide) (by decide) (by decide) (by rw [o₁₃.mem]; exact Frame.refl _ _),
      by rw [o₃.get .x22, o₂.get .x22, h22'], by rw [e₃, e₂, h22', lt_bit (by omega) (by omega)], fun c' hc h => ?_⟩
    rw [o₁₃.mem]
    refine rv c' hc ?_
    by_cases h' : c' < t₀
    · exact .inl h'
    · exact .inr ⟨c' - t₀, by omega, by simp only [tOf]; omega⟩

/-- What a group from `t₀` needs. -/
structure GP (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (I : Nat → Nat) (t₀ : Nat) (u : State) : Prop where
  fk : FK p σ S sig pk a I u
  x22 : u.gpr .x22 = BitVec.ofNat 64 t₀
  lt : t₀ < p.k
  roots : RT p σ S sig pk a I t₀ u.mem

/-- A group: the roots of its trees, and the next group's first tree. -/
theorem forsGroup_ok (hF : FP p) {σ : State} {S sig : Addr} (c : Ctx p σ S sig) {pk a : List Byte}
    {I : Nat → Nat} (hIa : ∀ i < p.k, I i < 2 ^ p.a) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    (ht : f.t4 = T.code) {t₀ : Nat} {u : State} (hg : GP p σ S sig pk a I t₀ u) :
    WP isa (Impl.SlhDsa.AArch64.Verify.forsGroup p f) u fun u' =>
      FK p σ S sig pk a I u' ∧ u'.gpr .x22 = BitVec.ofNat 64 (t₀ + 4) ∧
      u'.gpr .x9 = BitVec.ofNat 64 (if t₀ + 4 < p.k then 1 else 0) ∧ RT p σ S sig pk a I (t₀ + 4) u'.mem := by
  have hk := hF.k
  have ht₀ : t₀ < 2 ^ 32 := by have := hg.lt; omega
  unfold Impl.SlhDsa.AArch64.Verify.forsGroup
  refine WP.seq (WP.mono (forsLeaves_ok hF c hIa T ht ht₀ hg.fk hg.x22) fun t₁ ⟨g₁, _⟩ => ?_)
  refine WP.seq (MlKem.AArch64.wp_movz fun t₂ o₂ e₂ => WP.block_nil ?_)
  have hu : HI p σ S sig pk a I t₀ u p.a t₂ := by
    refine ⟨hF.a1, Nat.le_refl _, ?_, ?_⟩
    · rw [Nat.sub_self]
      exact ⟨g₁.fk.keep hF o₂.keep (by decide) (by decide) (by decide) (by decide) (by rw [o₂.mem]; exact Frame.refl _ _),
        by rw [o₂.get .x22, g₁.x22], fun k' hk' => ⟨by rw [o₂.get _ (fun h => idx_ne' k' hk' .x23 (by decide) (List.mem_singleton.mpr (List.mem_singleton.mp h).symm)), (g₁.lanes k' hk').idx],
          by rw [o₂.mem, (g₁.lanes k' hk').fld], by rw [o₂.mem, (g₁.lanes k' hk').msg]; rfl⟩, by rw [o₂.mem]; exact g₁.frame⟩
    · rw [e₂, Nat.sub_self]; rfl
  refine WP.seq (TreeBase.wpLoop (Q := fun v => GS p σ S sig pk a I t₀ p.a
      (fun k' => rootZ p σ.mem sig pk a (σ.gpr .x2).toNat I (tOf p t₀ k') p.a) u v) (fun m => decide (m ≠ 1)) (· - 1)
    (heights_step hF c hIa T ht ht₀) p.a hu |> fun h => WP.mono h fun v hv => ?_)
  have hr : RT p σ S sig pk a I t₀ v.mem := hg.roots.keep hF hv.frame
  exact roots_ok hF c hg.lt hv.fk hv.x22 (fun k' hk' => (hv.lanes k' hk').msg) hr

end VG.Proof.SlhDsa.AArch64.ForsPk
