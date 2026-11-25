module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block

/-! # Keccak-f[1600] on three states on AArch64: the contract, and the code in general registers -/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Hybrid.X3

open VG VG.AArch64
open VG.Proof.Sha3.AArch64 VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Neon.X2 (stateFrom_x2 pairAt_stateX2 stateX2_of_pairAt)
open VG.Spec.Sha3 (keccakF stateAt)
open VG.Proof.Sha3 (stateX2At)

/-- The third state's memory. -/
def stR (p : Addr) : Region := ⟨p, 200⟩

/-- The frame the code may allocate. -/
def frR (sp : Addr) : Region := ⟨sp - BitVec.ofNat 64 128, 128⟩

/-- The contract, in registers: two states at `x0`, one at `x1`, working space at `x2`. -/
def K : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [pairR (s.gpr .x0), stR (s.gpr .x1), Neon.X2.scrR (s.gpr .x2)] ∧
    (pairR (s.gpr .x0)).Disjoint (stR (s.gpr .x1)) ∧ (pairR (s.gpr .x0)).Disjoint (Neon.X2.scrR (s.gpr .x2)) ∧
    (stR (s.gpr .x1)).Disjoint (Neon.X2.scrR (s.gpr .x2)) ∧ 128 ≤ s.sp.toNat ∧
    (frR s.sp).Disjoint (pairR (s.gpr .x0)) ∧ (frR s.sp).Disjoint (stR (s.gpr .x1)) ∧
    (frR s.sp).Disjoint (Neon.X2.scrR (s.gpr .x2))
  post s s' := stateX2At s'.mem (s.gpr .x0) 0 = keccakF (stateX2At s.mem (s.gpr .x0) 0) ∧
    stateX2At s'.mem (s.gpr .x0) 1 = keccakF (stateX2At s.mem (s.gpr .x0) 1) ∧
    stateAt s'.mem (s.gpr .x1) = keccakF (stateAt s.mem (s.gpr .x1))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp

theorem pairAt_frame {m m' : Mem} {p : Addr} {A B : Spec.Sha3.State} {rs : List Region} (h : PairAt m p A B)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (pairR p).Disjoint r) : PairAt m' p A B := fun i hi => by
  rw [hf.read (pair_contains p hi) hd (by decide)]; exact h i hi

theorem stateAt_frame {m m' : Mem} {p : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (stR p).Disjoint r) : stateAt m' p = stateAt m p := by
  rw [← Scalar.stateFrom_stateAt, ← Scalar.stateFrom_stateAt]
  exact Scalar.stateFrom_congr fun i hi => hf.readW (r := stR p) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

theorem stateX2At_frame {m m' : Mem} {p : Addr} {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (pairR p).Disjoint r) {k : Nat} (hk : k < 2) : stateX2At m' p k = stateX2At m p k := by
  rw [← stateFrom_x2, ← stateFrom_x2]
  exact Scalar.stateFrom_congr fun i hi => hf.readW (r := pairR p) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

/-! ## In general registers -/

theorem scalar_ok (s : State) (hp : K.pre s) :
    WP isa Impl.Sha3.AArch64.Hybrid.X3.scalar s fun t => abiPreserved s t ∧ K.post s t := by
  obtain ⟨hrd, hwr, d01, d02, d12, -⟩ := hp
  have inS : ∀ i < 25, ∀ k < 2, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k)) 8 := fun i hi k hk =>
    ⟨pairR (s.gpr .x0), by simp [hwr], Offset.contains_base _ (by omega) (by omega)⟩
  have inT : ∀ i < 25, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (8 * i + 0)) 8 := fun i hi =>
    ⟨stR (s.gpr .x1), by simp [hwr], Offset.contains_base _ (by omega) (by omega)⟩
  have inW : ∀ k < 3, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * k)) 8 := fun k hk =>
    ⟨Neon.X2.scrR (s.gpr .x2), by simp [hwr], Offset.contains_base _ (by omega) (by omega)⟩
  have hw : ∀ {m m' : Mem}, Frame [⟨s.gpr .x2, 24⟩] m m' → Frame [Neon.X2.scrR (s.gpr .x2)] m m' := fun h =>
    h.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  have hl : ∀ {m m' : Mem} {k : Nat}, k < 2 → Frame (Scalar.laneRs (s.gpr .x0) 16 (8 * k)) m m' → Frame [pairR (s.gpr .x0)] m m' :=
    fun hk h => h.sub fun r hr => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have := List.mem_range.mp hj
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
  have hl' : ∀ {m m' : Mem}, Frame (Scalar.laneRs (s.gpr .x1) 8 0) m m' → Frame [stR (s.gpr .x1)] m m' :=
    fun h => h.sub fun r hr => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
      have := List.mem_range.mp hj
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
  have keep : ∀ {m m' : Mem} {k : Nat}, k < 2 → Frame (Scalar.laneRs (s.gpr .x0) 16 (8 * (1 - k))) m m' →
      stateX2At m' (s.gpr .x0) k = stateX2At m (s.gpr .x0) k := fun {m m' k} hk f => by
    rw [← stateFrom_x2, ← stateFrom_x2]
    exact Scalar.stateFrom_congr fun i hi => f.readW (r := ⟨s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k), 8⟩)
      (Region.contains_self _ _) (fun r hr => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
        have := List.mem_range.mp hj
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  have one : ∀ {m m' : Mem} {R : Region} {k : Nat}, k < 2 → (pairR (s.gpr .x0)).Disjoint R → Frame [R] m m' →
      stateX2At m' (s.gpr .x0) k = stateX2At m (s.gpr .x0) k := fun hk hd f =>
    stateX2At_frame f (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd) hk
  have two : ∀ {m m' : Mem} {R : Region}, (stR (s.gpr .x1)).Disjoint R → Frame [R] m m' →
      stateAt m' (s.gpr .x1) = stateAt m (s.gpr .x1) := fun hd f =>
    stateAt_frame f fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd
  have rd : ∀ {t : State} {a : Addr} {n : Nat}, InRegions t.wr a n → InRegions (t.rd ++ t.wr) a n :=
    fun ⟨R, hR, hc⟩ => ⟨R, List.mem_append_right _ hR, hc⟩
  have iW : ∀ {t : State}, Scalar.Ctx s t → ∀ k < 3, InRegions t.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * k)) 8 := fun c k hk => by
    rw [c.env.wr]; exact inW k hk
  have iS : ∀ {t : State}, Scalar.Ctx s t → ∀ i < 25, ∀ k < 2,
      InRegions t.wr (s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k)) 8 := fun c i hi k hk => by rw [c.env.wr]; exact inS i hi k hk
  have iT : ∀ {t : State}, Scalar.Ctx s t → ∀ i < 25,
      InRegions t.wr (s.gpr .x1 + BitVec.ofNat 64 (8 * i + 0)) 8 := fun c i hi => by rw [c.env.wr]; exact inT i hi
  unfold Impl.Sha3.AArch64.Hybrid.X3.scalar
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Scalar.enter_ok s) fun t₁ ⟨c₁, g₁, m₁⟩ => ?_
  refine Scalar.wp_dup fun t₂ d₂ => Scalar.wp_dup fun t₃ d₃ => Scalar.wp_dup fun t₃' d₃' => Scalar.wp_umov fun t₄ d₄ => ?_
  have c₄ : Scalar.Ctx s t₄ := (((c₁.dup (by decide) d₂).dup (by decide) d₃).dup (by decide) d₃').upd d₄
  have v29 : vdword (t₄.v .v29) 0 = s.gpr .x0 := by rw [d₄.vec, d₃'.other _ (by decide), d₃.other _ (by decide), d₂.v, g₁]
  have v30 : vdword (t₄.v .v30) 0 = s.gpr .x2 := by rw [d₄.vec, d₃'.other _ (by decide), d₃.v, d₂.gpr, g₁]
  have v31 : vdword (t₄.v .v31) 0 = s.gpr .x1 := by rw [d₄.vec, d₃'.v, d₃.gpr, d₂.gpr, g₁]
  have x16 : t₄.gpr .x16 = s.gpr .x0 := by rw [d₄.gpr, d₃'.other _ (by decide), d₃.other _ (by decide), d₂.v, g₁]
  have m₄ : t₄.mem = s.mem := by rw [d₄.mem, d₃'.mem, d₃.mem, d₂.mem, m₁]
  -- The first state.
  refine WP.mono (Scalar.run_ok c₄ (stride := 16) (off := 8 * 0) (by decide) (by decide) (by decide) (by decide) v30
    (fun i hi => by rw [x16]; exact rd (iS c₄ i hi 0 (by decide))) (iW c₄) fun t₅ c₅ l₅ a₅ e₅ f₅ => ?_) fun _ h => WP.seq h
  rw [x16, m₄, stateFrom_x2] at l₅
  rw [m₄] at f₅
  have w₅ := hw f₅
  refine WP.seq (Scalar.put_ok c₅ l₅ (p := s.gpr .x0) (by rw [a₅ _ (by decide), v29]) (stride := 16) (off := 8 * 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (fun i hi => iS c₅ i hi 0 (by decide))
    fun t₆ c₆ v₆ x₆ r₆ f₆ => ?_)
  -- The second.
  refine WP.mono (Scalar.run_ok c₆ (stride := 16) (off := 8 * 1) (by decide) (by decide) (by decide) (by decide)
    (by rw [v₆, a₅ _ (by decide), v30]) (fun i hi => by rw [x₆]; exact rd (iS c₆ i hi 1 (by decide))) (iW c₆)
    fun t₇ c₇ l₇ a₇ e₇ f₇ => ?_) fun _ h => WP.seq h
  rw [x₆, stateFrom_x2, keep (k := 1) (by decide) f₆, one (by decide) d02 w₅] at l₇
  have w₇ := hw f₇
  refine WP.seq (Scalar.put_ok c₇ l₇ (p := s.gpr .x0) (by rw [a₇ _ (by decide), v₆, a₅ _ (by decide), v29]) (stride := 16)
    (off := 8 * 1) (by decide) (by decide) (by decide) (by decide) (by decide) (fun i hi => iS c₇ i hi 1 (by decide))
    fun t₈ c₈ v₈ x₈ r₈ f₈ => ?_)
  -- The third.
  refine Scalar.wp_umov fun t₉ d₉ => ?_
  have c₉ := c₈.upd d₉
  have x₉ : t₉.gpr .x16 = s.gpr .x1 := by rw [d₉.gpr, v₈, a₇ _ (by decide), v₆, a₅ _ (by decide), v31]
  refine WP.mono (Scalar.run_ok c₉ (stride := 8) (off := 0) (by decide) (by decide) (by decide) (by decide)
    (by rw [d₉.vec, v₈, a₇ _ (by decide), v₆, a₅ _ (by decide), v30])
    (fun i hi => by rw [x₉]; exact rd (iT c₉ i hi)) (iW c₉) fun t₁₀ c₁₀ l₁₀ a₁₀ e₁₀ f₁₀ => ?_) fun _ h => WP.seq h
  have d10 := d01.symm
  rw [x₉, Scalar.stateFrom_stateAt, d₉.mem, two d10 (hl (k := 1) (by decide) f₈), two d12 w₇,
    two d10 (hl (k := 0) (by decide) f₆), two d12 w₅] at l₁₀
  rw [d₉.mem] at f₁₀
  have w₁₀ := hw f₁₀
  refine Scalar.put_ok c₁₀ l₁₀ (p := s.gpr .x1) (by rw [a₁₀ _ (by decide), d₉.vec, v₈, a₇ _ (by decide), v₆, a₅ _ (by decide), v31])
    (stride := 8) (off := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (iT c₁₀) fun t₁₁ c₁₁ v₁₁ x₁₁ r₁₁ f₁₁ => ?_
  refine WP.mono (Scalar.exit_ok c₁₁) fun t₁₂ h => ⟨h.1, ?_⟩
  have e₀ : stateX2At t₆.mem (s.gpr .x0) 0 = keccakF (stateX2At s.mem (s.gpr .x0) 0) := by rw [← stateFrom_x2]; exact Scalar.eq_stateFrom r₆
  have e₁ : stateX2At t₈.mem (s.gpr .x0) 1 = keccakF (stateX2At s.mem (s.gpr .x0) 1) := by rw [← stateFrom_x2]; exact Scalar.eq_stateFrom r₈
  have w₁₁ := hl' f₁₁
  simp only [K]
  rw [h.2.1]
  refine ⟨?_, ?_, ?_⟩
  · rw [one (by decide) d01 w₁₁, one (by decide) d02 w₁₀, keep (k := 0) (by decide) f₈, one (by decide) d02 w₇, e₀]
  · rw [one (by decide) d01 w₁₁, one (by decide) d02 w₁₀, e₁]
  · rw [← Scalar.stateFrom_stateAt]; exact Scalar.eq_stateFrom r₁₁

end VG.Proof.Sha3.AArch64.Hybrid.X3
