module

public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2
public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.Rounds
public import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.Lit
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Sha3.AArch64.RoundConstants
import VerifiedGarbage.Proof.Sha3.Lanes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Sha3.AArch64.Hybrid.Lit

/-! # Keccak-f[1600] on three states on AArch64 -/

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

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Hybrid.X3
open VG.Impl.Sha3.AArch64.Scalar (lreg savedReg)
open VG.Proof.Sha3.AArch64 VG.Proof.Sha3.AArch64.Neon VG.Proof.Sha3.AArch64.Rounds
open VG.Proof.Sha3.AArch64.Sha3.Vector (SavedV pairs_iff two_rounds)
open VG.Spec.Sha3 (keccakF rnd RC stateAt)
open VG.Proof.Sha3 (stateX2At)
open VG.Proof.MlKem.AArch64 (VUpd VMem VChg wp_ldrq wp_strq wp_vop)
open VG.Impl.Sha3.AArch64.RoundConstants (rcs sym)

/-! ## The stack -/

theorem wp_strSp {t : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off % 8 = 0 ∧ off < 32768)
    (hout : InRegions s.wr (s.sp + BitVec.ofNat 64 off) 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW (s.sp + BitVec.ofNat 64 off) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strSp t off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW (s.sp + BitVec.ofNat 64 off) (s.gpr t) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, State.store, State.read, BitVec.setWidth_eq]
  rw [ite_eq_left ho, ite_eq_left hout]; rfl

theorem wp_ldrSp {t : Reg} {off : Nat} {is : List Instr} {s : State} {Q : State → Prop} (ho : off % 8 = 0 ∧ off < 32768)
    (hin : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8)
    (k : ∀ s', Upd s s' t (s.mem.readW (s.sp + BitVec.ofNat 64 off) 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW (s.sp + BitVec.ofNat 64 off) 64)) ?_ (k _ (Upd.write64 _ _ _))
  simp only [exec, State.load]
  rw [ite_eq_left ho, ite_eq_left hin]; rfl

/-! ## What holds in the frame

`e` is the state on entry to it. -/

/-- The frame. -/
def fr (e : State) : Region := ⟨e.sp, 128⟩

structure Pre (e : State) : Prop where
  wr : e.wr = [fr e, pairR (e.gpr .x0), stR (e.gpr .x1), Neon.X2.scrR (e.gpr .x2)]
  d01 : (pairR (e.gpr .x0)).Disjoint (stR (e.gpr .x1))
  d02 : (pairR (e.gpr .x0)).Disjoint (Neon.X2.scrR (e.gpr .x2))
  d12 : (stR (e.gpr .x1)).Disjoint (Neon.X2.scrR (e.gpr .x2))
  f0 : (fr e).Disjoint (pairR (e.gpr .x0))
  f1 : (fr e).Disjoint (stR (e.gpr .x1))
  f2 : (fr e).Disjoint (Neon.X2.scrR (e.gpr .x2))

namespace Pre
variable {e : State} (h : Pre e)
include h

theorem inF {k n : Nat} (hk : k + n ≤ 128) : InRegions e.wr (e.sp + BitVec.ofNat 64 k) n :=
  ⟨fr e, by rw [h.wr]; simp, Offset.contains_base _ hk (by omega)⟩
theorem inP {k n : Nat} (hk : k + n ≤ 400) : InRegions e.wr (e.gpr .x0 + BitVec.ofNat 64 k) n :=
  ⟨pairR (e.gpr .x0), by rw [h.wr]; simp, Offset.contains_base _ hk (by omega)⟩
theorem inS {k n : Nat} (hk : k + n ≤ 200) : InRegions e.wr (e.gpr .x1 + BitVec.ofNat 64 k) n :=
  ⟨stR (e.gpr .x1), by rw [h.wr]; simp, Offset.contains_base _ hk (by omega)⟩
theorem inW {k n : Nat} (hk : k + n ≤ 128) : InRegions e.wr (e.gpr .x2 + BitVec.ofNat 64 k) n :=
  ⟨Neon.X2.scrR (e.gpr .x2), by rw [h.wr]; simp, Offset.contains_base _ hk (by omega)⟩

end Pre

theorem readable {t : State} {a : Addr} {n : Nat} : InRegions t.wr a n → InRegions (t.rd ++ t.wr) a n :=
  fun ⟨R, hR, hc⟩ => ⟨R, List.mem_append_right _ hR, hc⟩

/-- What the frame and the working space hold. -/
structure Held (e s : State) : Prop where
  sp : s.sp = e.sp
  wr : s.wr = e.wr
  slot : ∀ i < 11, s.mem.readW (e.sp + BitVec.ofNat 64 (8 * i)) 64 = e.gpr (savedReg i)
  x0 : s.mem.readW (e.sp + BitVec.ofNat 64 88) 64 = e.gpr .x0
  x1 : s.mem.readW (e.sp + BitVec.ofNat 64 96) 64 = e.gpr .x1
  x2 : s.mem.readW (e.sp + BitVec.ofNat 64 104) 64 = e.gpr .x2
  saved : SavedV e.v s.mem (e.gpr .x2)

/-- The slots. -/
def slots (e : State) : Region := ⟨e.sp, 112⟩

theorem Held.frame {e s t : State} (h : Held e s) {rs : List Region} (hf : Frame rs s.mem t.mem)
    (hd : ∀ r ∈ rs, (slots e).Disjoint r ∧ (Neon.X2.scrR (e.gpr .x2)).Disjoint r) (hsp : t.sp = s.sp) (hwr : t.wr = s.wr) :
    Held e t := by
  have rd : ∀ {k : Nat}, k + 8 ≤ 112 → t.mem.readW (e.sp + BitVec.ofNat 64 k) 64 = s.mem.readW (e.sp + BitVec.ofNat 64 k) 64 :=
    fun hk => hf.readW (r := slots e) (Offset.contains_base _ hk (by omega)) (fun r hr => (hd r hr).1) (by decide)
  exact ⟨hsp.trans h.sp, hwr.trans h.wr, fun i hi => by rw [rd (by omega)]; exact h.slot i hi, by rw [rd (by decide)]; exact h.x0,
    by rw [rd (by decide)]; exact h.x1, by rw [rd (by decide)]; exact h.x2, h.saved.frame hf fun r hr => (hd r hr).2⟩

theorem Held.same {e s t : State} (h : Held e s) (hm : t.mem = s.mem) (hsp : t.sp = s.sp) (hwr : t.wr = s.wr) : Held e t :=
  h.frame (rs := []) (by rw [hm]; exact Frame.refl _ _) (fun _ hr => absurd hr List.not_mem_nil) hsp hwr

theorem pair_apart {e : State} (h : Pre e) : (slots e).Disjoint (pairR (e.gpr .x0)) ∧
    (Neon.X2.scrR (e.gpr .x2)).Disjoint (pairR (e.gpr .x0)) :=
  ⟨fun a h1 h2 => h.f0 a (Region.sub_prefix (by decide) a h1) h2, h.d02.symm⟩

theorem state_apart {e : State} (h : Pre e) : (slots e).Disjoint (stR (e.gpr .x1)) ∧
    (Neon.X2.scrR (e.gpr .x2)).Disjoint (stR (e.gpr .x1)) :=
  ⟨fun a h1 h2 => h.f1 a (Region.sub_prefix (by decide) a h1) h2, h.d12.symm⟩

/-- The count's slot. -/
def cnt (e : State) : Region := ⟨e.sp + BitVec.ofNat 64 112, 8⟩

theorem cnt_sub (e : State) : ∀ a, (cnt e).Contains a 1 → (fr e).Contains a 1 := Offset.sub_base _ (by decide)

theorem cnt_apart {e : State} (h : Pre e) : (slots e).Disjoint (cnt e) ∧ (Neon.X2.scrR (e.gpr .x2)).Disjoint (cnt e) :=
  ⟨Offset.base_disjoint _ (by decide) (by decide), fun a h1 h2 => h.f2 a (cnt_sub e a h2) h1⟩

theorem cnt_pair {e : State} (h : Pre e) : (cnt e).Disjoint (pairR (e.gpr .x0)) := fun a h1 h2 => h.f0 a (cnt_sub e a h1) h2

/-! ## The loop -/

/-- The states on entry. -/
abbrev A0 (e : State) (k : Nat) : Spec.Sha3.State := stateX2At e.mem (e.gpr .x0) k
abbrev C0 (e : State) : Spec.Sha3.State := stateAt e.mem (e.gpr .x1)

/-- `n` rounds. -/
abbrev go (n : Nat) (A : Spec.Sha3.State) : Spec.Sha3.State := (List.range n).foldl rnd A

/-- Before iteration `k`. -/
structure LInv (e : State) (k : Nat) (s : State) : Prop where
  held : Held e s
  pairs : Vec.Pairs 0 s (go (2 * k) (A0 e 0)) (go (2 * k) (A0 e 1))
  third : Third 0 s (go (2 * k) (C0 e))
  x30 : s.gpr .x30 = e.gpr .x0 + BitVec.ofNat 64 (16 * k)
  count : s.mem.readW (e.sp + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 (12 - k)
  table : ∀ r, 2 * k ≤ r → r < 24 → s.mem.readW (e.gpr .x0 + BitVec.ofNat 64 (32 + 8 * r)) 64 = RC r

theorem step_ok {e s : State} (hp : Pre e) {k : Nat} (hk : k < 12) (h : LInv e k s) :
    WP isa (.seq (.block rounds) (.block next)) s fun t => LInv e (k + 1) t ∧ t.gpr .x16 = BitVec.ofNat 64 (12 - (k + 1)) := by
  have wr := h.held.wr
  have at' : ∀ o, s.gpr .x30 + BitVec.ofNat 64 o = e.gpr .x0 + BitVec.ofNat 64 (16 * k + o) := fun o => by
    rw [h.x30, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine WP.seq (WP.mono (rounds_ok (n := 2 * k) h.pairs h.third ?_ ?_ ?_) fun t ⟨p, l, x, rd, wr', sp, f⟩ => ?_)
  · intro j hj; rw [at', wr]; exact hp.inP (by omega)
  · intro m hm j hj; rw [at']; exact readable (by rw [wr]; exact hp.inP (by omega))
  · intro r hr
    rw [at', show 16 * k + (32 + 8 * r) = 32 + 8 * (2 * k + r) by omega]
    exact h.table _ (by omega) (by omega)
  rw [← two_rounds, ← two_rounds] at p
  rw [← two_rounds] at l
  rw [h.x30] at f
  have fp : Frame [pairR (e.gpr .x0)] s.mem t.mem := f.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩
  have ht : Held e t := h.held.frame fp (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact pair_apart hp) sp wr'
  have hcnt : t.mem.readW (e.sp + BitVec.ofNat 64 112) 64 = BitVec.ofNat 64 (12 - k) := by
    rw [fp.readW (r := cnt e) (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact cnt_pair hp)
      (by decide), h.count]
  have inC : InRegions t.wr (t.sp + BitVec.ofNat 64 112) 8 := by rw [ht.wr, ht.sp]; exact hp.inF (by decide)
  unfold next
  refine wp_addImm (by decide) fun t₁ d₁ => wp_ldrSp ⟨by decide, by decide⟩ (by rw [d₁.rd, d₁.wr, d₁.sp]; exact readable inC)
    fun t₂ d₂ => wp_subImm (by decide) fun t₃ d₃ => wp_strSp ⟨by decide, by decide⟩
      (by rw [d₃.wr, d₂.wr, d₁.wr, d₃.sp, d₂.sp, d₁.sp]; exact inC) fun t₄ d₄ => wp_nil ?_
  have x16 : t₃.gpr .x16 = BitVec.ofNat 64 (12 - (k + 1)) := by
    rw [d₃.gpr, d₂.gpr, d₁.mem, d₁.sp, ht.sp, hcnt]
    have : ∀ k < 12, BitVec.ofNat 64 (12 - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (12 - (k + 1)) := by decide
    exact this k hk
  have m₄ : t₄.mem = t.mem.writeW (e.sp + BitVec.ofNat 64 112) (BitVec.ofNat 64 (12 - (k + 1))) := by
    rw [d₄.mem, x16, d₃.mem, d₂.mem, d₁.mem, d₃.sp, d₂.sp, d₁.sp, ht.sp]
  have f₄ : Frame [cnt e] t.mem t₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have v₄ : t₄.v = t.v := by rw [d₄.vec, d₃.vec, d₂.vec, d₁.vec]
  have g₄ : ∀ r, r ≠ .x16 → r ≠ .x30 → t₄.gpr r = t.gpr r := fun r h1 h2 => by
    rw [d₄.gpr, d₃.other r h1, d₂.other r h1, d₁.other r h2]
  refine ⟨⟨?_, fun i hi => by rw [v₄]; exact p i hi, fun i hi => ?_, ?_, ?_, fun r h1 h2 => ?_⟩, by rw [d₄.gpr, x16]⟩
  · exact ht.frame f₄ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact cnt_apart hp)
      (by rw [d₄.sp, d₃.sp, d₂.sp, d₁.sp]) (by rw [d₄.wr, d₃.wr, d₂.wr, d₁.wr])
  · have hn := Scalar.reg_ne' 0 hi
    rw [g₄ _ hn.1 hn.2.2.1]; exact l i hi
  · rw [d₄.gpr, d₃.other _ (by decide), d₂.other _ (by decide), d₁.gpr, x, h.x30, BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.mul_add, Nat.mul_one]
  · rw [m₄]; exact Mem.readW_writeW_self64 _ _ _
  · rw [f₄.readW (r := pairR (e.gpr .x0)) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact (cnt_pair hp).symm) (by decide),
      f.readW (r := ⟨e.gpr .x0 + BitVec.ofNat 64 (32 + 8 * r), 8⟩) (Region.contains_self _ _)
        (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)]
    exact h.table r (by omega) h2

theorem count_eval {s : State} {k : Nat} (hk : k < 12) (h : s.gpr .x16 = BitVec.ofNat 64 (12 - (k + 1))) :
    isa.eval (.nonzero .x .x16) s = some (decide (k + 1 ≠ 12)) := by
  show VG.AArch64.eval (.nonzero .x .x16) s = _
  rw [eval_nonzero, h]
  have : ∀ k < 12, (BitVec.ofNat 64 (12 - (k + 1)) != 0) = decide (k + 1 ≠ 12) := by decide
  rw [this k hk]

theorem loop_ok {e s : State} (hp : Pre e) (h : LInv e 0 s) :
    WP isa (.loop (.seq (.block rounds) (.block next)) (.nonzero .x .x16)) s (LInv e 12) := by
  refine WP.loop (M := isa) (fun n t => ∃ k < 12, n = 12 - k ∧ LInv e k t) ?_ 12 s ⟨0, by decide, rfl, h⟩
  rintro _ t ⟨k, hk, rfl, h⟩
  refine WP.mono (step_ok hp hk h) fun u ⟨hu, x16⟩ => ?_
  rw [count_eval hk x16]
  by_cases h12 : k + 1 = 12
  · refine .inl ⟨by rw [h12]; rfl, ?_⟩
    rw [h12] at hu; exact hu
  · exact .inr ⟨by rw [decide_eq_true h12], 12 - (k + 1), by omega, k + 1, by omega, rfl, hu⟩

/-! ## The entry -/

/-- The saved registers. -/
theorem saveG_ok {e s : State} (hp : Pre e) (hsp : s.sp = e.sp) (hwr : s.wr = e.wr) :
    WP isa (.block saveG) s fun t => (∀ i < 11, t.mem.readW (e.sp + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (savedReg i)) ∧
      Frame [fr e] s.mem t.mem ∧ Mupd s t t.mem := by
  suffices h : ∀ k ≤ 11, WP isa (.block ((List.range k).map fun i => .strSp (savedReg i) (8 * i))) s fun t =>
      (∀ i < k, t.mem.readW (e.sp + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (savedReg i)) ∧ Frame [fr e] s.mem t.mem ∧
        Mupd s t t.mem from h 11 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h, f, c⟩ => wp_strSp ⟨by omega, by omega⟩
      (by rw [c.wr, c.sp, hsp, hwr]; exact hp.inF (by omega)) fun u d => wp_nil ⟨fun i hi => ?_, ?_,
        ⟨d.gpr.trans c.gpr, rfl, d.rd.trans c.rd, d.wr.trans c.wr, d.sp.trans c.sp, d.vec.trans c.vec⟩⟩
    · rw [d.mem, c.sp, hsp, c.gpr]
      by_cases hik : i = k
      · subst hik; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact h i (by omega)
    · rw [d.mem, c.sp, hsp]
      exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem rcStore_ok {e s : State} (hp : Pre e) (h0 : s.gpr .x0 = e.gpr .x0) (hwr : s.wr = e.wr) :
    WP isa (.block rcStore) s fun t => (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) ∧ (∀ v, v ≠ .v31 → t.v v = s.v v) ∧
      t.wr = s.wr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ Frame [pairR (e.gpr .x0)] s.mem t.mem ∧
      ∀ r < 24, t.mem.readW (e.gpr .x0 + BitVec.ofNat 64 (32 + 8 * r)) 64 = RC r := by
  suffices h : ∀ k ≤ 12, WP isa (.block (([.adrSym .x16 sym] : List Instr) ++ (List.range k).flatMap fun k =>
      [.ldrqTbl .v31 .x16 (16 * k) sym rcs, .strq .v31 .x0 (32 + 16 * k)])) s fun t =>
      (∀ g, g ≠ .x16 → t.gpr g = s.gpr g) ∧ (∀ v, v ≠ .v31 → t.v v = s.v v) ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.rd = s.rd ∧
      Frame [pairR (e.gpr .x0)] s.mem t.mem ∧ t.gpr .x16 = t.syms sym ∧
      ∀ r < 2 * k, t.mem.readW (e.gpr .x0 + BitVec.ofNat 64 (32 + 8 * r)) 64 = RC r from
    WP.mono (h 12 (Nat.le_refl _)) fun t ⟨h1, h2, h3, h4, h5, h6, _, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h8⟩
  intro k hk
  induction k with
  | zero =>
    refine WP.cons (s' := s.write .x .x16 (s.syms sym)) rfl (wp_nil ⟨fun g hg => ?_, fun _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _, ?_, fun r hr => absurd hr (Nat.not_lt_zero _)⟩)
    · rw [RegUpd.gpr_write, ite_eq_right hg]
    · rw [RegUpd.gpr_write, ite_eq_left rfl, BitVec.setWidth_eq]; rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, ← List.append_assoc, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hr0 := RoundConstants.rcs_eq (2 * k) (by omega)
    have hr1 := RoundConstants.rcs_eq (2 * k + 1) (by omega)
    have hx : exec (.ldrqTbl .v31 .x16 (16 * k) sym rcs) t = some (t.setV .v31 (ofVDwords (RC (2 * k)) (RC (2 * k + 1)))) := by
      simp only [exec]
      rw [ite_eq_left ⟨h7, by omega, by omega, by rw [RoundConstants.rcs_length]; omega⟩,
        show 16 * k / 8 = 2 * k by omega, hr0, hr1]
      rfl
    refine WP.cons hx ?_
    let m' := t.mem.write (e.gpr .x0 + BitVec.ofNat 64 (32 + 16 * k)) 16 (ofVDwords (RC (2 * k)) (RC (2 * k + 1)))
    have hin : InRegions (t.setV .v31 (ofVDwords (RC (2 * k)) (RC (2 * k + 1)))).wr
        (e.gpr .x0 + BitVec.ofNat 64 (32 + 16 * k)) 16 := by
      rw [RegUpd.wr_setV, h3, hwr]; exact hp.inP (by omega)
    refine WP.cons (s' := { t.setV .v31 (ofVDwords (RC (2 * k)) (RC (2 * k + 1))) with mem := m' }) ?_ (wp_nil ?_)
    · simp only [exec, addr, RegUpd.gpr_setV]
      rw [ite_eq_left ⟨by omega, by omega⟩, h1 _ (by decide), h0]
      simp only [Option.bind_some, State.store]
      rw [ite_eq_left hin, RegUpd.v_setV, ite_eq_left rfl]; rfl
    have mm : m' = (t.mem.writeW (e.gpr .x0 + BitVec.ofNat 64 (32 + 8 * (2 * k))) (RC (2 * k))).writeW
        (e.gpr .x0 + BitVec.ofNat 64 (32 + 8 * (2 * k + 1))) (RC (2 * k + 1)) := by
      simp only [m']
      rw [write16_dwords, BitVec.add_assoc, ← BitVec.ofNat_add, show 32 + 16 * k = 32 + 8 * (2 * k) by omega,
        show 32 + 8 * (2 * k) + 8 = 32 + 8 * (2 * k + 1) by omega]
    refine ⟨h1, fun v hv => ?_, h3, h4, h5, ?_, h7, fun r hr => ?_⟩
    · rw [RegUpd.v_setV, ite_eq_right hv]; exact h2 v hv
    · exact h6.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · show m'.readW _ 64 = _
      rw [mm]
      by_cases r1 : r = 2 * k + 1
      · subst r1; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        by_cases r0 : r = 2 * k
        · subst r0; exact Mem.readW_writeW_self64 _ _ _
        · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
          exact h8 r (by omega)

theorem reg0' (i : Nat) : Impl.Sha3.AArch64.Scalar.reg 0 i = lreg i := rfl
theorem lreg1 : ∀ i < 25, lreg i = .x1 ↔ i = 1 := by decide

/-- Loading the third state. -/
theorem loadThird_ok {e s : State} (hp : Pre e) (h1 : s.gpr .x1 = e.gpr .x1) (hwr : s.wr = e.wr)
    (hs : stateAt s.mem (e.gpr .x1) = C0 e) :
    WP isa (.block loadThird) s fun t => Third 0 t (C0 e) ∧ (∀ r, (∀ i < 25, r ≠ lreg i) → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.v = s.v ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have lane : ∀ i < 25, s.mem.readW (e.gpr .x1 + BitVec.ofNat 64 (8 * i)) 64 = (C0 e)[i]! := fun i hi => by
    rw [← hs, Sha3.Vector.state_lane _ _ hi]
  have hin : ∀ i < 25, ∀ t : State, t.rd = s.rd → t.wr = s.wr → InRegions (t.rd ++ t.wr) (e.gpr .x1 + BitVec.ofNat 64 (8 * i)) 8 :=
    fun i hi t _ h => readable (by rw [h, hwr]; exact hp.inS (by omega))
  have part : ∀ l : List Nat, l.Nodup → (∀ i ∈ l, i < 25 ∧ i ≠ 1) → ∀ s' : State, s'.gpr .x1 = e.gpr .x1 → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr →
      WP isa (.block (l.map fun i => .ldr .x (lreg i) .x1 (8 * i))) s' fun t => (∀ i ∈ l, t.gpr (lreg i) = (C0 e)[i]!) ∧
        (∀ r, (∀ i ∈ l, r ≠ lreg i) → t.gpr r = s'.gpr r) ∧ t.mem = s'.mem ∧ t.v = s'.v ∧ t.rd = s'.rd ∧ t.wr = s'.wr ∧ t.sp = s'.sp := by
    intro l
    induction l with
    | nil => exact fun _ _ s' _ _ _ _ => wp_nil ⟨fun i hi => absurd hi List.not_mem_nil, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
    | cons j l ih =>
      intro hn hl s' hx hm hrd hwr'
      have hj := hl j List.mem_cons_self
      have nj : lreg j ≠ .x1 := fun e => hj.2 ((lreg1 j hj.1).mp e)
      rw [List.map_cons]
      refine wp_ldr (a := e.gpr .x1 + BitVec.ofNat 64 (8 * j)) ⟨by omega, by omega⟩ (by rw [hx]) (hin j hj.1 s' hrd hwr') fun u d => ?_
      refine WP.mono (ih (List.nodup_cons.mp hn).2 (fun i hi => hl i (List.mem_cons_of_mem _ hi)) u
        (by rw [d.other _ nj.symm, hx]) (d.mem.trans hm) (d.rd.trans hrd) (d.wr.trans hwr')) fun t ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
        ⟨fun i hi => ?_, fun r hr => ?_, h3.trans d.mem, h4.trans d.vec, h5.trans d.rd, h6.trans d.wr, h7.trans d.sp⟩
      · rcases List.mem_cons.mp hi with rfl | hi
        · rw [h2 _ fun k hk e' => ?_, d.gpr, hm, lane _ hj.1]
          have := Scalar.lreg_inj i hj.1 k (hl k (List.mem_cons_of_mem _ hk)).1 e'
          subst this
          exact (List.nodup_cons.mp hn).1 hk
        · exact h1 i hi
      · rw [h2 r fun i hi => hr i (List.mem_cons_of_mem _ hi), d.other r (hr j List.mem_cons_self)]
  unfold loadThird
  rw [WP.block_append_iff]
  refine WP.mono (part ((List.range 25).filter (· != 1)) (by decide) (by decide) s h1 rfl rfl rfl)
    fun t ⟨h1', h2, h3, h4, h5, h6, h7⟩ => ?_
  have x1 : t.gpr .x1 = e.gpr .x1 := by rw [h2 _ (by decide), h1]
  refine wp_ldr (a := e.gpr .x1 + BitVec.ofNat 64 8) ⟨by decide, by decide⟩ (by rw [x1]) (hin 1 (by decide) t h5 h6)
    fun u d => wp_nil ⟨fun i hi => ?_, fun r hr => ?_, d.mem.trans h3, d.vec.trans h4, d.wr.trans h6, d.sp.trans h7⟩
  · rw [reg0', show conf.pd i = 0 from rfl, Scalar.rotr_zero]
    by_cases hi1 : i = 1
    · subst hi1
      rw [show lreg 1 = .x1 from rfl, d.gpr, h3]
      exact lane 1 (by decide)
    · rw [d.other _ fun e => hi1 ((lreg1 i hi).mp e)]
      exact h1' i (by simp [hi, hi1])
  · rw [d.other r (hr 1 (by decide)), h2 r fun i hi => hr i (by simp at hi; exact hi.1)]

theorem enter_ok {e : State} (hp : Pre e) : WP isa (.block enter) e (LInv e 0) := by
  unfold enter
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Sha3.Vector.save_ok (by decide) (by decide) (q := e.gpr .x2) (by simp) fun i hi => hp.inW (by omega))
    fun t₁ ⟨c₁, v₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saveG_ok hp c₁.sp c₁.wr) fun t₂ ⟨s₂, f₂, c₂⟩ => ?_
  have sp₂ : t₂.sp = e.sp := c₂.sp.trans c₁.sp
  have wr₂ : t₂.wr = e.wr := c₂.wr.trans c₁.wr
  have g₂ : t₂.gpr = e.gpr := c₂.gpr.trans c₁.gpr
  rw [WP.block_append_iff]
  refine WP.mono (?_ : WP isa (.block ptrs) t₂ fun t₃ => Held e t₃ ∧ t₃.gpr = e.gpr ∧ Frame [fr e] t₂.mem t₃.mem ∧ t₃.v = e.v) ?_
  · unfold ptrs
    refine wp_strSp ⟨by decide, by decide⟩ (by rw [wr₂, sp₂]; exact hp.inF (by decide)) fun a da =>
      wp_strSp ⟨by decide, by decide⟩ (by rw [da.wr, da.sp, wr₂, sp₂]; exact hp.inF (by decide)) fun b db =>
      wp_strSp ⟨by decide, by decide⟩ (by rw [db.wr, db.sp, da.wr, da.sp, wr₂, sp₂]; exact hp.inF (by decide)) fun c dc => wp_nil ?_
    have mm : c.mem = ((t₂.mem.writeW (e.sp + BitVec.ofNat 64 88) (e.gpr .x0)).writeW (e.sp + BitVec.ofNat 64 96) (e.gpr .x1)).writeW
        (e.sp + BitVec.ofNat 64 104) (e.gpr .x2) := by
      rw [dc.mem, db.mem, da.mem, db.gpr, da.gpr, g₂, db.sp, da.sp, sp₂]
    have fc : Frame [fr e] t₂.mem c.mem := by
      rw [mm]
      exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
    refine ⟨⟨?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩, ?_, fc, ?_⟩
    · rw [dc.sp, db.sp, da.sp, sp₂]
    · rw [dc.wr, db.wr, da.wr, wr₂]
    · rw [mm, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), s₂ i hi, c₁.gpr]
    · rw [mm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
      exact Mem.readW_writeW_self64 _ _ _
    · rw [mm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide)]
      exact Mem.readW_writeW_self64 _ _ _
    · rw [mm]; exact Mem.readW_writeW_self64 _ _ _
    · exact (v₁.frame f₂ fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.f2.symm).frame fc
        fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.f2.symm
    · rw [dc.gpr, db.gpr, da.gpr, g₂]
    · rw [dc.vec, db.vec, da.vec, c₂.vec, c₁.v]
  rintro t₃ ⟨h₃, g₃, f₃, v₃⟩
  -- The states are as on entry.
  have s1 : ∀ r ∈ [Neon.X2.scrR (e.gpr .x2)], (pairR (e.gpr .x0)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.d02
  have s2 : ∀ r ∈ [fr e], (pairR (e.gpr .x0)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.f0.symm
  have q1 : ∀ r ∈ [Neon.X2.scrR (e.gpr .x2)], (stR (e.gpr .x1)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.d12
  have q2 : ∀ r ∈ [fr e], (stR (e.gpr .x1)).Disjoint r := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hp.f1.symm
  have P₃ : PairAt t₃.mem (e.gpr .x0) (A0 e 0) (A0 e 1) :=
    pairAt_frame (pairAt_frame (pairAt_frame (Neon.X2.pairAt_stateX2 _ _) f₁ s1) f₂ s2) f₃ s2
  have S₃ : stateAt t₃.mem (e.gpr .x1) = C0 e := by
    rw [stateAt_frame f₃ q2, stateAt_frame f₂ q2, stateAt_frame f₁ q1]
  rw [WP.block_append_iff]
  refine WP.mono (Neon.load_ok (p := e.gpr .x0) (by rw [g₃]) P₃ fun i hi => readable (by rw [h₃.wr]; exact hp.inP (by omega)))
    fun t₄ ⟨c₄, p₄⟩ => ?_
  have h₄ := h₃.same c₄.mem c₄.sp c₄.wr
  rw [WP.block_append_iff]
  refine WP.mono (rcStore_ok hp (by rw [c₄.gpr, g₃]) h₄.wr) fun t₅ ⟨g₅, v₅, wr₅, sp₅, rd₅, f₅, tb₅⟩ => ?_
  have h₅ := h₄.frame f₅ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact pair_apart hp) sp₅ wr₅
  have S₅ : stateAt t₅.mem (e.gpr .x1) = C0 e := by
    rw [stateAt_frame f₅ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hp.d01.symm), c₄.mem, S₃]
  simp only [List.cons_append, List.nil_append]
  refine wp_movz fun t₆ d₆ => wp_strSp ⟨by decide, by decide⟩ (by rw [d₆.wr, d₆.sp, h₅.wr, h₅.sp]; exact hp.inF (by decide))
    fun t₇ d₇ => wp_addImm (by decide) fun t₈ d₈ => ?_
  have m₈ : t₈.mem = t₅.mem.writeW (e.sp + BitVec.ofNat 64 112) (12 : BitVec 64) := by
    rw [d₈.mem, d₇.mem, d₆.mem, d₆.sp, h₅.sp, d₆.gpr]; rfl
  have f₈ : Frame [cnt e] t₅.mem t₈.mem := by
    rw [m₈]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have h₈ := h₅.frame f₈ (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact cnt_apart hp)
    (by rw [d₈.sp, d₇.sp, d₆.sp]) (by rw [d₈.wr, d₇.wr, d₆.wr])
  have g₈ : ∀ r, r ≠ .x16 → r ≠ .x30 → t₈.gpr r = e.gpr r := fun r h1 h2 => by
    rw [d₈.other r h2, d₇.gpr, d₆.other r h1, g₅ r h1, c₄.gpr, g₃]
  have S₈ : stateAt t₈.mem (e.gpr .x1) = C0 e := by
    rw [stateAt_frame f₈ (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact fun a h1 h2 => hp.f1 a (cnt_sub e a h2) h1), S₅]
  refine WP.mono (loadThird_ok hp (g₈ _ (by decide) (by decide)) h₈.wr S₈) fun t₉ ⟨l₉, g₉, m₉, v₉, wr₉, sp₉⟩ => ?_
  have hv : ∀ i < 25, t₉.v (Impl.Sha3.AArch64.Sha3.Vector.vreg i) = t₄.v (Impl.Sha3.AArch64.Sha3.Vector.vreg i) := fun i hi => by
    rw [v₉, d₈.vec, d₇.vec, d₆.vec, v₅ _ fun e => by have := (vreg_inj i (by omega) 31 (by omega)).mp e; omega]
  refine ⟨h₈.same m₉ sp₉ wr₉, pairs_iff.mp fun i hi => by rw [hv i hi]; exact p₄ i hi, l₉, ?_, ?_, fun r _ hr => ?_⟩
  · rw [g₉ _ (by decide), d₈.gpr, d₇.gpr, d₆.other _ (by decide), g₅ _ (by decide), c₄.gpr, g₃]
  · rw [m₉, m₈]; exact Mem.readW_writeW_self64 _ _ _
  · rw [m₉, f₈.readW (r := pairR (e.gpr .x0)) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact (cnt_pair hp).symm) (by decide)]
    exact tb₅ r hr

/-! ## The exit -/

/-- The stores of the third state. -/
def storeLanes : List Instr := (List.range 25).map fun i => .str .x (lreg i) .x16 (8 * i)

/-- After the loop. -/
structure P1 (e s : State) : Prop where
  held : Held e s
  pairs : Pairs s (keccakF (A0 e 0)) (keccakF (A0 e 1))
  third : Third 0 s (keccakF (C0 e))

/-- With the third state stored. -/
structure P2 (e s : State) : Prop where
  held : Held e s
  pairs : Pairs s (keccakF (A0 e 0)) (keccakF (A0 e 1))
  st : stateAt s.mem (e.gpr .x1) = keccakF (C0 e)

/-- With all three stored. -/
structure P3 (e s : State) : Prop where
  held : Held e s
  pair : PairAt s.mem (e.gpr .x0) (keccakF (A0 e 0)) (keccakF (A0 e 1))
  st : stateAt s.mem (e.gpr .x1) = keccakF (C0 e)

theorem LInv.p1 {e s : State} (h : LInv e 12 s) : P1 e s := ⟨h.held, pairs_iff.mpr h.pairs, h.third⟩

theorem slot_in {e s : State} (hp : Pre e) (h : Held e s) {k : Nat} (hk : k + 8 ≤ 128) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8 := readable (by rw [h.wr, h.sp]; exact hp.inF hk)

theorem l1_ok {e s : State} (hp : Pre e) (h : P1 e s) :
    WP isa (.block [.ldrSp .x16 96]) s fun t => P1 e t ∧ t.gpr .x16 = e.gpr .x1 :=
  wp_ldrSp ⟨by decide, by decide⟩ (slot_in hp h.held (by decide)) fun t d => wp_nil
    ⟨⟨h.held.same d.mem d.sp d.wr, fun i hi => by rw [d.vec]; exact h.pairs i hi, fun i hi => by
      rw [d.other _ (Scalar.reg_ne' 0 hi).1]; exact h.third i hi⟩, by rw [d.gpr, h.held.sp]; exact h.held.x1⟩

theorem s1_ok {e s : State} (hp : Pre e) (h : P1 e s ∧ s.gpr .x16 = e.gpr .x1) : WP isa (.block storeLanes) s (P2 e) := by
  obtain ⟨h, h16⟩ := h
  refine WP.mono (?_ : WP isa (.block storeLanes) s fun t => (∀ i < 25, t.mem.readW (e.gpr .x1 + BitVec.ofNat 64 (8 * i)) 64 =
      (keccakF (C0 e))[i]!) ∧ Frame [stR (e.gpr .x1)] s.mem t.mem ∧ Mupd s t t.mem) fun t ⟨r, f, c⟩ =>
      ⟨h.held.frame f (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact state_apart hp) c.sp c.wr,
        fun i hi => by rw [c.vec]; exact h.pairs i hi, Vector.ext fun i hi => by
          rw [← getElem!_eq _ hi, ← getElem!_eq _ hi, Sha3.Vector.state_lane _ _ hi, r i hi]⟩
  suffices g : ∀ k ≤ 25, WP isa (.block ((List.range k).map fun i => .str .x (lreg i) .x16 (8 * i))) s fun t =>
      (∀ i < k, t.mem.readW (e.gpr .x1 + BitVec.ofNat 64 (8 * i)) 64 = (keccakF (C0 e))[i]!) ∧
        Frame [stR (e.gpr .x1)] s.mem t.mem ∧ Mupd s t t.mem from g 25 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), Frame.refl _ _, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  | succ k ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨r, f, c⟩ => wp_str (a := e.gpr .x1 + BitVec.ofNat 64 (8 * k)) ⟨by omega, by omega⟩
      (by rw [c.gpr, h16]) (by rw [c.wr, h.held.wr]; exact hp.inS (by omega)) fun u d => wp_nil ⟨fun i hi => ?_, ?_,
        ⟨d.gpr.trans c.gpr, rfl, d.rd.trans c.rd, d.wr.trans c.wr, d.sp.trans c.sp, d.vec.trans c.vec⟩⟩
    · rw [d.mem]
      by_cases hik : i = k
      · subst hik
        have := h.third i (by omega)
        rw [reg0', show conf.pd i = 0 from rfl, Scalar.rotr_zero] at this
        rw [c.gpr, this]; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
        exact r i (by omega)
    · rw [d.mem]; exact f.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem l2_ok {e s : State} (hp : Pre e) (h : P2 e s) :
    WP isa (.block [.ldrSp .x0 88]) s fun t => P2 e t ∧ t.gpr .x0 = e.gpr .x0 :=
  wp_ldrSp ⟨by decide, by decide⟩ (slot_in hp h.held (by decide)) fun t d => wp_nil
    ⟨⟨h.held.same d.mem d.sp d.wr, fun i hi => by rw [d.vec]; exact h.pairs i hi, by rw [d.mem]; exact h.st⟩, by
      rw [d.gpr, h.held.sp]; exact h.held.x0⟩

theorem s2_ok {e s : State} (hp : Pre e) (h : P2 e s ∧ s.gpr .x0 = e.gpr .x0) :
    WP isa (.block (Impl.Sha3.AArch64.Neon.Pair.store .x0)) s (P3 e) :=
  WP.mono (Neon.store_ok h.2 h.1.pairs fun i hi => by rw [h.1.held.wr]; exact hp.inP (by omega)) fun t ⟨c, p, f⟩ =>
    ⟨h.1.held.frame f (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact pair_apart hp) c.sp c.wr, p, by
      rw [stateAt_frame f fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact hp.d01.symm]; exact h.1.st⟩

theorem l3_ok {e s : State} (hp : Pre e) (h : P3 e s) :
    WP isa (.block [.ldrSp .x2 104]) s fun t => P3 e t ∧ t.gpr .x2 = e.gpr .x2 :=
  wp_ldrSp ⟨by decide, by decide⟩ (slot_in hp h.held (by decide)) fun t d => wp_nil
    ⟨⟨h.held.same d.mem d.sp d.wr, by rw [d.mem]; exact h.pair, by rw [d.mem]; exact h.st⟩, by
      rw [d.gpr, h.held.sp]; exact h.held.x2⟩

/-- On exit from the frame. -/
structure Done (e s : State) : Prop where
  sp : s.sp = e.sp
  gpr : ∀ r ∈ preserved, s.gpr r = e.gpr r
  v : ∀ r ∈ preservedV, s.v r = e.v r
  pair : PairAt s.mem (e.gpr .x0) (keccakF (A0 e 0)) (keccakF (A0 e 1))
  st : stateAt s.mem (e.gpr .x1) = keccakF (C0 e)

theorem s3_ok {e s : State} (hp : Pre e) (h : P3 e s ∧ s.gpr .x2 = e.gpr .x2) :
    WP isa (.block (Impl.Sha3.AArch64.Sha3.Vector.restore .x2 0 ++ restoreG)) s (Done e) := by
  obtain ⟨h, h2⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (Sha3.Vector.restore_ok (q := e.gpr .x2) (by decide) (by decide) (by rw [h2]; simp)
    (fun i hi => readable (by rw [h.held.wr]; exact hp.inW (by omega))) h.held.saved) fun t ⟨c, v⟩ => ?_
  have ht := h.held.same c.mem c.sp c.wr
  refine WP.mono (?_ : WP isa (.block restoreG) t fun u => (∀ i < 11, u.gpr (savedReg i) = e.gpr (savedReg i)) ∧
      u.mem = t.mem ∧ u.sp = t.sp ∧ u.v = t.v) fun u ⟨g, m, sp, vu⟩ => ⟨sp.trans ht.sp, fun r hr => ?_,
      fun r hr => by rw [vu]; exact v r hr, by rw [m, c.mem]; exact h.pair, by rw [m, c.mem]; exact h.st⟩
  · suffices g : ∀ k ≤ 11, WP isa (.block ((List.range k).map fun i => .ldrSp (savedReg i) (8 * i))) t fun u =>
        (∀ i < k, u.gpr (savedReg i) = e.gpr (savedReg i)) ∧ u.mem = t.mem ∧ u.sp = t.sp ∧ u.v = t.v ∧ u.wr = t.wr from
      WP.mono (g 11 (Nat.le_refl _)) fun u ⟨a, b, c, d, _⟩ => ⟨a, b, c, d⟩
    intro k hk
    induction k with
    | zero => exact wp_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩
    | succ k ih =>
      rw [List.range_succ, List.map_append, WP.block_append_iff]
      refine WP.mono (ih (by omega)) fun u ⟨g, m, sp, vu, wr⟩ => wp_ldrSp ⟨by omega, by omega⟩
        (slot_in hp (ht.same m sp wr) (by omega)) fun w d => wp_nil ⟨fun i hi => ?_, d.mem.trans m, d.sp.trans sp,
          d.vec.trans vu, d.wr.trans wr⟩
      by_cases hik : i = k
      · subst hik; rw [d.gpr, m, sp, ht.sp]; exact ht.slot i (by omega)
      · rw [d.other _ fun x => hik (Scalar.savedReg_inj i (by omega) k (by omega) x)]
        exact g i (by omega)
  · obtain ⟨i, hi, rfl⟩ := Scalar.savedReg_all r hr
    exact g i hi

theorem leave_eq : leave = ([.ldrSp .x16 96] : List Instr) ++ (storeLanes ++ (([.ldrSp .x0 88] : List Instr) ++
    (Impl.Sha3.AArch64.Neon.Pair.store .x0 ++ (([.ldrSp .x2 104] : List Instr) ++
      (Impl.Sha3.AArch64.Sha3.Vector.restore .x2 0 ++ restoreG))))) := by
  simp only [leave, storeThird, storeLanes, List.append_assoc]

theorem leave_ok {e s : State} (hp : Pre e) (h : P1 e s) : WP isa (.block leave) s (Done e) := by
  rw [leave_eq, WP.block_append_iff]
  refine WP.mono (l1_ok hp h) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (s1_ok hp h₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (l2_ok hp h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (s2_ok hp h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  exact WP.mono (l3_ok hp h₄) fun s₅ h₅ => s3_ok hp h₅

theorem body_ok {e : State} (hp : Pre e) :
    WP isa (.seq (.block enter) (.seq (.loop (.seq (.block rounds) (.block next)) (.nonzero .x .x16)) (.block leave))) e (Done e) :=
  WP.seq (WP.mono (enter_ok hp) fun _ h => WP.seq (WP.mono (loop_ok hp h) fun _ h => leave_ok hp h.p1))

theorem pre_of {s : State} (h : K.pre s) : Pre (allocated 128 s) := by
  obtain ⟨_, hwr, d01, d02, d12, _, f0, f1, f2⟩ := h
  exact ⟨by simp only [allocated, hwr]; rfl, d01, d02, d12, f0, f1, f2⟩

theorem vector_ok (s : State) (hp : K.pre s) : WP isa vector s fun t => abiPreserved s t ∧ K.post s t := by
  have hP := pre_of hp
  refine WP.alloc ⟨by decide, by decide, by decide⟩ hp.2.2.2.2.2.1 (WP.mono (body_ok hP) fun t h m u f => ?_)
  have f' : Frame [fr (allocated 128 s)] t.mem m := f
  have hA := Neon.X2.stateX2_of_pairAt (pairAt_frame h.pair f' fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hP.f0.symm)
  have hC := (stateAt_frame f' fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hP.f1.symm).trans h.st
  refine ⟨⟨fun r hr => h.gpr r hr, ?_, fun r hr => by
    show (t.v r).extractLsb' 0 64 = _; rw [h.v r hr]; rfl⟩, hA.1, hA.2, hC⟩
  show t.sp + BitVec.ofNat 64 128 = s.sp
  rw [h.sp]
  exact BitVec.sub_add_cancel _ _

theorem correct (sha3 : Bool) (s : State) (hp : K.pre s) :
    ∃ tr t, Exec isa (code sha3) s tr t ∧ abiPreserved s t ∧ K.post s t := by
  cases sha3
  · exact scalar_ok s hp
  · exact vector_ok s hp

/-! ## Constant time -/

theorem scalar_ct : ConstantTime isa K.pre K.pub scalar :=
  Taint.constantTime_of_exists (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1, .x2]) (fun _ _ _ _ h => ⟨⟨h.2.2.2, fun r hr => by
    simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1⟩, fun v hv => by simp [VectorTaint.ofRegs] at hv⟩) ⟨_, by taint_decide⟩

/-- A block whose addresses are in public registers. -/
theorem relBlock {P : State → State → Prop} {c : Prog isa} (rs : List Reg) (hp : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    (h : ∃ hc, (AArch64.taint.check (Taint.ofRegs rs) c hc).isSome = true) {F₁ F₂ : State → Prop}
    (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) : RelCT isa P c fun a b => F₁ a ∧ F₂ b := by
  obtain ⟨hc, h⟩ := h
  refine RelCT.mono (RelCT.wp (RelCT.taint (A := AArch64.taint) (Taint.ofRegs rs) (fun a b hab => ⟨(hp a b hab).1, fun r hr =>
    (hp a b hab).2 r (Taint.mem_ofRegs.mp hr)⟩) h) hw) (fun _ _ h => h) fun _ _ h => h.2

theorem body_rel {e₁ e₂ : State} (hp₁ : Pre e₁) (hp₂ : Pre e₂) (h0 : e₁.gpr .x0 = e₂.gpr .x0) (h1 : e₁.gpr .x1 = e₂.gpr .x1)
    (h2 : e₁.gpr .x2 = e₂.gpr .x2) (hsp : e₁.sp = e₂.sp) :
    RelCT isa (fun a b => a = e₁ ∧ b = e₂)
      (.seq (.block enter) (.seq (.loop (.seq (.block rounds) (.block next)) (.nonzero .x .x16)) (.block leave)))
      fun _ _ => True := by
  have sps : ∀ {a b}, Held e₁ a → Held e₂ b → a.sp = b.sp := fun ha hb => by rw [ha.sp, hb.sp, hsp]
  refine RelCT.seq (relBlock (F₁ := LInv e₁ 0) (F₂ := LInv e₂ 0) [.x0, .x1, .x2] ?_ ⟨_, by taint_decide⟩ ?_)
    (RelCT.seq (R := fun a b => LInv e₁ 12 a ∧ LInv e₂ 12 b) ?_ ?_)
  · rintro a b ⟨rfl, rfl⟩
    exact ⟨hsp, by simp [h0, h1, h2]⟩
  · rintro a b ⟨rfl, rfl⟩
    exact ⟨enter_ok hp₁, enter_ok hp₂⟩
  · refine RelCT.mono (RelCT.loop (M := isa) (Q := fun a b => LInv e₁ 12 a ∧ LInv e₂ 12 b)
      (fun n a b => ∃ k, n = 12 - k ∧ k < 12 ∧ LInv e₁ k a ∧ LInv e₂ k b) (fun n => RelCT.exists_ fun k => ?_) 12)
      (fun a b h => ⟨0, rfl, by decide, h.1, h.2⟩) fun _ _ h => h
    refine RelCT.mono (relBlock (P := fun a b => n = 12 - k ∧ k < 12 ∧ LInv e₁ k a ∧ LInv e₂ k b)
      (F₁ := fun t => k < 12 ∧ n = 12 - k ∧ LInv e₁ (k + 1) t ∧ t.gpr .x16 = BitVec.ofNat 64 (12 - (k + 1)))
      (F₂ := fun t => LInv e₂ (k + 1) t ∧ t.gpr .x16 = BitVec.ofNat 64 (12 - (k + 1))) [.x30] ?_ ⟨_, by taint_decide⟩ ?_)
      (fun _ _ h => h) ?_
    · rintro a b ⟨_, _, ha, hb⟩
      exact ⟨sps ha.held hb.held, by simp [ha.x30, hb.x30, h0]⟩
    · rintro a b ⟨hn, hk, ha, hb⟩
      exact ⟨WP.mono (step_ok hp₁ hk ha) fun t h => ⟨hk, hn, h⟩, step_ok hp₂ hk hb⟩
    · rintro a b ⟨⟨hk, hn, ha, xa⟩, hb, xb⟩
      rw [count_eval hk xa, count_eval hk xb]
      refine ⟨rfl, fun h => ?_, fun h => ⟨12 - (k + 1), by omega, k + 1, rfl, ?_, ha, hb⟩⟩
      · have h12 : k + 1 = 12 := by simpa using h
        rw [h12] at ha hb
        exact ⟨ha, hb⟩
      · have : ¬ k + 1 = 12 := by simpa using h
        omega
  · rw [leave_eq]
    refine RelCT.block_append (RelCT.seq (relBlock (F₁ := fun t => P1 e₁ t ∧ t.gpr .x16 = e₁.gpr .x1)
      (F₂ := fun t => P1 e₂ t ∧ t.gpr .x16 = e₂.gpr .x1) [] (fun a b h => ⟨sps h.1.held h.2.held, by simp⟩)
      ⟨_, by taint_decide⟩ fun a b h => ⟨l1_ok hp₁ h.1.p1, l1_ok hp₂ h.2.p1⟩) ?_)
    refine RelCT.block_append (RelCT.seq (relBlock (F₁ := P2 e₁) (F₂ := P2 e₂) [.x16] (fun a b h => ⟨sps h.1.1.held h.2.1.held, by
      simp [h.1.2, h.2.2, h1]⟩) ⟨_, by taint_decide⟩ fun a b h => ⟨s1_ok hp₁ h.1, s1_ok hp₂ h.2⟩) ?_)
    refine RelCT.block_append (RelCT.seq (relBlock (F₁ := fun t => P2 e₁ t ∧ t.gpr .x0 = e₁.gpr .x0)
      (F₂ := fun t => P2 e₂ t ∧ t.gpr .x0 = e₂.gpr .x0) [] (fun a b h => ⟨sps h.1.held h.2.held, by simp⟩)
      ⟨_, by taint_decide⟩ fun a b h => ⟨l2_ok hp₁ h.1, l2_ok hp₂ h.2⟩) ?_)
    refine RelCT.block_append (RelCT.seq (relBlock (F₁ := P3 e₁) (F₂ := P3 e₂) [.x0] (fun a b h => ⟨sps h.1.1.held h.2.1.held, by
      simp [h.1.2, h.2.2, h0]⟩) ⟨_, by taint_decide⟩ fun a b h => ⟨s2_ok hp₁ h.1, s2_ok hp₂ h.2⟩) ?_)
    refine RelCT.block_append (RelCT.seq (relBlock (F₁ := fun t => P3 e₁ t ∧ t.gpr .x2 = e₁.gpr .x2)
      (F₂ := fun t => P3 e₂ t ∧ t.gpr .x2 = e₂.gpr .x2) [] (fun a b h => ⟨sps h.1.held h.2.held, by simp⟩)
      ⟨_, by taint_decide⟩ fun a b h => ⟨l3_ok hp₁ h.1, l3_ok hp₂ h.2⟩) ?_)
    exact RelCT.mono (relBlock (F₁ := Done e₁) (F₂ := Done e₂) [.x2] (fun a b h => ⟨sps h.1.1.held h.2.1.held, by
      simp [h.1.2, h.2.2, h2]⟩) ⟨_, by taint_decide⟩ fun a b h => ⟨s3_ok hp₁ h.1, s3_ok hp₂ h.2⟩) (fun _ _ h => h) fun _ _ _ => trivial

theorem vector_ct : ConstantTime isa K.pre K.pub vector :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) (RelCT.mono
    (RelCT.exists_ (α := {x : State × State // Pre x.1 ∧ Pre x.2 ∧ x.1.gpr .x0 = x.2.gpr .x0 ∧ x.1.gpr .x1 = x.2.gpr .x1 ∧
      x.1.gpr .x2 = x.2.gpr .x2 ∧ x.1.sp = x.2.sp}) fun x => body_rel x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2)
    (fun a b ⟨s, t, ⟨ps, pt, q⟩, ha, hb⟩ => ⟨⟨(allocated 128 s, allocated 128 t), pre_of ps, pre_of pt, q.1, q.2.1, q.2.2.1, by
      simp only [allocated, q.2.2.2]⟩, ha, hb⟩) fun _ _ _ => trivial))

theorem ct (sha3 : Bool) : ConstantTime isa K.pre K.pub (code sha3) := by
  cases sha3
  · exact scalar_ct
  · exact vector_ct

end VG.Proof.Sha3.AArch64.Hybrid.X3
