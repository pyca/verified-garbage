module

public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Boundary
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Permute
public import VerifiedGarbage.Proof.Framework.AArch64.Schedule
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
meta import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2

/-! # Keccak-f[1600] on two interleaved states on AArch64 -/

@[expose] public section

namespace VG.Proof.Sha3.AArch64.Neon.X2

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Neon.X2
open VG.Proof.Sha3.AArch64 VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3.AArch64.Rounds (Vec.ok Vec.Pairs)
open VG.Spec.Sha3 (keccakF)
open VG.Proof.Sha3 (stateX2At)

/-- The working space. -/
def scrR (q : Addr) : Region := ⟨q, 128⟩

/-- The contract, in registers. -/
def x2K : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [pairR (s.gpr .x0), scrR (s.gpr .x1)] ∧ (pairR (s.gpr .x0)).Disjoint (scrR (s.gpr .x1))
  post s s' := stateX2At s'.mem (s.gpr .x0) 0 = keccakF (stateX2At s.mem (s.gpr .x0) 0) ∧
    stateX2At s'.mem (s.gpr .x0) 1 = keccakF (stateX2At s.mem (s.gpr .x0) 1)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

/-! ## With FEAT_SHA3 -/

theorem mixed_ok : ∀ r < 2, Vec.ok (Impl.Sha3.AArch64.Sha3.Vector.round 2 8 r) r = true := by decide +kernel

theorem order_ok : Schedule.ok .x16 order plain = true := by decide +kernel

theorem body_ok : Sha3.Vector.BodyOk body := fun hp hc => by
  obtain ⟨t, x, h⟩ := Sha3.Vector.body_run mixed_ok hp hc
  exact ⟨t, (Schedule.run_eq order order_ok _).trans x, h⟩

private theorem readable {o t : State} (h1 : t.wr = o.wr) {a : Addr} {n : Nat} : InRegions o.wr a n → InRegions (t.rd ++ t.wr) a n :=
  fun ⟨R, hR, hc⟩ => ⟨R, List.mem_append_right _ (by rw [h1]; exact hR), hc⟩

theorem vector_ok (s : State) (hp : x2K.pre s) : WP isa vector s fun t => abiPreserved s t ∧ x2K.post s t := by
  obtain ⟨hrd, hwr, hdis⟩ := hp
  have inS : ∀ k n, k + n ≤ 400 → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 k) n := fun k n h =>
    ⟨pairR (s.gpr .x0), by simp [hwr], Offset.contains_base _ h (by omega)⟩
  have inW : ∀ k n, k + n ≤ 128 → InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 k) n := fun k n h =>
    ⟨scrR (s.gpr .x1), by simp [hwr], Offset.contains_base _ h (by omega)⟩
  unfold vector
  refine WP.seq ?_
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Sha3.Vector.save_ok (by decide) (by decide) (q := s.gpr .x1) (by simp) fun i hi => inW _ _ (by omega))
    fun t₁ ⟨c₁, v₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  have hP : PairAt t₁.mem (s.gpr .x0) (stateX2At s.mem (s.gpr .x0) 0) (stateX2At s.mem (s.gpr .x0) 1) := fun i hi => by
    rw [f₁.read (pair_contains _ hi) (fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hdis) (by decide)]
    exact pairAt_stateX2 _ _ i hi
  refine WP.mono (load_ok (p := s.gpr .x0) (by rw [c₁.gpr]) hP fun i hi => readable c₁.wr (inS _ _ (by omega)))
    fun t₂ ⟨c₂, p₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Sha3.Vector.rcStore_ok (b := .x0) (by decide) (by decide) (by decide) (T := s.gpr .x0)
    (by rw [c₂.gpr, c₁.gpr]; simp) fun r hr => by rw [c₂.wr, c₁.wr]; exact inS _ _ (by omega))
    fun t₃ ⟨g₃, w₃, rd₃, wr₃, sp₃, f₃, T₃⟩ => ?_
  refine wp_addImm (by decide) fun t₄ d₄ => wp_movz fun t₅ d₅ => wp_nil ?_
  have k : Sha3.Vector.CoreKeep t₃ t₅ := (Sha3.Vector.CoreKeep.upd d₄ (.inl rfl)).trans (.upd d₅ (.inr rfl))
  have p₅ : Pairs t₅ _ _ := fun i hi => by
    rw [d₅.vec, d₄.vec, w₃ _ fun e => by have := (vreg_inj i (by omega) 31 (by omega)).mp e; omega]; exact p₂ i hi
  refine WP.seq (WP.mono (Sha3.Vector.loop_ok body_ok p₅ (T₃.core k)
    (by rw [d₅.other _ (by decide), d₄.gpr, g₃ _ (by decide), c₂.gpr, c₁.gpr]; simp) (by rw [d₅.gpr]; rfl)) fun t₆ ⟨k₆, p₆⟩ => ?_)
  have kk := k.trans k₆
  have wr₆ : t₆.wr = s.wr := kk.wr.trans (wr₃.trans (c₂.wr.trans c₁.wr))
  have g₆ : ∀ r, r ≠ .x16 → r ≠ .x17 → t₆.gpr r = s.gpr r := fun r h6 h7 => by rw [kk.gpr r h6 h7, g₃ r h6, c₂.gpr, c₁.gpr]
  rw [WP.block_append_iff]
  refine WP.mono (store_ok (p := s.gpr .x0) (g₆ _ (by decide) (by decide)) p₆ fun i hi => by rw [wr₆]; exact inS _ _ (by omega))
    fun t₇ ⟨c₇, p₇, f₇⟩ => ?_
  have dq : (scrR (s.gpr .x1)).Disjoint ⟨s.gpr .x0, 384⟩ := fun a h1 h2 =>
    hdis a (Region.sub_prefix (base := s.gpr .x0) (len := 384) (len' := 400) (by decide) a h2) h1
  have sv : Sha3.Vector.SavedV s.v t₇.mem (s.gpr .x1) := by
    refine (v₁.frame (m' := t₆.mem) (rs := [⟨s.gpr .x0, 384⟩]) ?_ fun r hr => ?_).frame f₇ fun r hr => ?_
    · rw [kk.mem, ← c₂.mem]; exact f₃
    · rw [List.mem_singleton] at hr; subst hr
      exact dq
    · rw [List.mem_singleton] at hr; subst hr; exact hdis.symm
  refine WP.mono (Sha3.Vector.restore_ok (q := s.gpr .x1) (by decide) (by decide)
    (by rw [c₇.gpr, g₆ _ (by decide) (by decide)]; simp) (fun i hi => readable (c₇.wr.trans wr₆) (inW _ _ (by omega))) sv)
    fun t₈ ⟨c₈, v₈⟩ => ⟨⟨fun r hr => ?_, ?_, fun r hr => by rw [v₈ r hr]⟩, ?_⟩
  · have hn := Sha3.Vector.preserved_ne r hr
    rw [c₈.gpr, c₇.gpr, g₆ r hn.1 hn.2.1]
  · rw [c₈.sp, c₇.sp, kk.sp, sp₃, c₂.sp, c₁.sp]
  · simp only [x2K]
    rw [c₈.mem]
    exact stateX2_of_pairAt p₇

/-! ## In general registers -/

theorem word_addr (p : Addr) (i k : Nat) : p + BitVec.ofNat 64 (16 * i + 8 * k) = p + BitVec.ofNat 64 (8 * (2 * i + k)) := by
  rw [show 16 * i + 8 * k = 8 * (2 * i + k) by omega]

theorem stateFrom_x2 (m : Mem) (p : Addr) (k : Nat) : Scalar.stateFrom m p 16 (8 * k) = stateX2At m p k := by
  refine Scalar.eq_stateFrom fun i hi => ?_
  rw [stateX2_get m p hi]

theorem scalar_ok (s : State) (hp : x2K.pre s) : WP isa scalar s fun t => abiPreserved s t ∧ x2K.post s t := by
  obtain ⟨hrd, hwr, hdis⟩ := hp
  have inS : ∀ i < 25, ∀ k < 2, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k)) 8 := fun i hi k hk =>
    ⟨pairR (s.gpr .x0), by simp [hwr], Offset.contains_base _ (by omega) (by omega)⟩
  have inW : ∀ k < 3, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := fun k hk =>
    ⟨scrR (s.gpr .x1), by simp [hwr], Offset.contains_base _ (by omega) (by omega)⟩
  unfold scalar
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Scalar.enter_ok s) fun t₁ ⟨c₁, g₁, m₁⟩ => ?_
  refine Scalar.wp_dup fun t₂ d₂ => Scalar.wp_dup fun t₃ d₃ => Scalar.wp_umov fun t₄ d₄ => ?_
  have c₄ : Scalar.Ctx s t₄ := ((c₁.dup (by decide) d₂).dup (by decide) d₃).upd d₄
  have v29 : vdword (t₄.v .v29) 0 = s.gpr .x0 := by rw [d₄.vec, d₃.other _ (by decide), d₂.v, g₁]
  have v30 : vdword (t₄.v .v30) 0 = s.gpr .x1 := by rw [d₄.vec, d₃.v, d₂.gpr, g₁]
  have x16 : t₄.gpr .x16 = s.gpr .x0 := by rw [d₄.gpr, d₃.other _ (by decide), d₂.v, g₁]
  have m₄ : t₄.mem = s.mem := by rw [d₄.mem, d₃.mem, d₂.mem, m₁]
  have iS : ∀ {t : State}, Scalar.Ctx s t → t.gpr .x16 = s.gpr .x0 → ∀ i < 25, ∀ k < 2,
      InRegions t.wr (t.gpr .x16 + BitVec.ofNat 64 (16 * i + 8 * k)) 8 := fun c h i hi k hk => by
    rw [h, c.env.wr]; exact inS i hi k hk
  have iW : ∀ {t : State}, Scalar.Ctx s t → ∀ k < 3, InRegions t.wr (s.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := fun c k hk => by
    rw [c.env.wr]; exact inW k hk
  have rd : ∀ {t : State} {a : Addr} {n : Nat}, InRegions t.wr a n → InRegions (t.rd ++ t.wr) a n :=
    fun ⟨R, hR, hc⟩ => ⟨R, List.mem_append_right _ hR, hc⟩
  -- Storing what the rounds leave.
  have st : ∀ {t : State} {A : Spec.Sha3.State} {k : Nat} {is : List Instr} {Q : State → Prop}, k < 2 → Scalar.Ctx s t →
      Scalar.Lanes t A → vdword (t.v .v29) 0 = s.gpr .x0 →
      (∀ u, Scalar.Ctx s u → u.v = t.v → u.gpr .x16 = s.gpr .x0 →
        (∀ i < 25, u.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k)) 64 = A[i]!) →
        Frame (Scalar.laneRs (s.gpr .x0) 16 (8 * k)) t.mem u.mem → WP isa (.block is) u Q) →
      WP isa (.block (.umov .x .x16 .v29 0 :: (Impl.Sha3.AArch64.Scalar.store .x16 16 (8 * k) ++ is))) t Q :=
    fun {t A k is Q} hk c l v h => by
      refine Scalar.wp_umov fun u d => ?_
      have hx : u.gpr .x16 = s.gpr .x0 := by rw [d.gpr, v]
      have cu := c.upd d
      rw [WP.block_append_iff]
      refine WP.mono (Scalar.store_ok Scalar.b16 (stride := 16) (off := 8 * k) (by decide) (by omega) (by decide) (by decide)
        (by omega) (Scalar.lanes_upd l d) fun i hi => iS cu hx i hi k hk) fun w ⟨r, f, g, vw, e⟩ => ?_
      rw [hx] at r f
      refine h w (cu.ofV vw e) (vw.trans d.vec) ?_ r (by rw [← d.mem]; exact f)
      rw [g _ Scalar.b16]; exact hx
  have keep : ∀ {m m' : Mem} {k : Nat}, k < 2 → Frame (Scalar.laneRs (s.gpr .x0) 16 (8 * (1 - k))) m m' → ∀ i < 25,
      m'.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k)) 64 = m.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k)) 64 :=
    fun {m m' k} hk f i hi => f.readW (r := ⟨s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k), 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
        have := List.mem_range.mp hj
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  have work : ∀ {m m' : Mem}, Frame [⟨s.gpr .x1, 24⟩] m m' → ∀ i < 25, ∀ k < 2,
      m'.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k)) 64 = m.readW (s.gpr .x0 + BitVec.ofNat 64 (16 * i + 8 * k)) 64 :=
    fun f i hi k hk => f.readW (r := pairR (s.gpr .x0)) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact fun a h1 h2 => hdis a h1 (Region.sub_prefix (base := s.gpr .x1) (len := 24) (len' := 128) (by decide) a h2)) (by decide)
  refine WP.mono (Scalar.run_ok c₄ (stride := 16) (off := 0) (by decide) (by decide) (by decide) (by decide) v30
    (fun i hi => rd (iS c₄ x16 i hi 0 (by decide))) (iW c₄) fun t₅ c₅ l₅ a₅ e₅ f₅ => ?_) fun _ h => WP.seq h
  rw [x16, m₄] at l₅
  rw [m₄] at f₅
  refine WP.seq ?_
  simp only [List.cons_append, List.nil_append]
  refine st (k := 0) (by decide) c₅ l₅ (by rw [a₅ _ (by decide), v29]) fun t₆ c₆ v₆ x₆ r₆ f₆ => ?_
  have e₆ : Scalar.stateFrom t₆.mem (s.gpr .x0) 16 8 = Scalar.stateFrom s.mem (s.gpr .x0) 16 8 :=
    Scalar.stateFrom_congr fun i hi => by
      have h1 := keep (k := 1) (by decide) f₆ i hi
      have h2 := work f₅ i hi 1 (by decide)
      rw [Nat.mul_one] at h1 h2
      rw [h1, h2]
  refine WP.mono (Scalar.run_ok c₆ (stride := 16) (off := 8) (by decide) (by decide) (by decide) (by decide)
    (by rw [v₆, a₅ _ (by decide), v30]) (fun i hi => rd (iS c₆ x₆ i hi 1 (by decide))) (iW c₆)
    fun t₇ c₇ l₇ a₇ e₇ f₇ => ?_) fun _ h => WP.seq h
  rw [x₆, e₆] at l₇
  refine st (k := 1) (by decide) c₇ l₇ (by rw [a₇ _ (by decide), v₆, a₅ _ (by decide), v29]) fun t₈ c₈ v₈ x₈ r₈ f₈ => ?_
  refine WP.mono (Scalar.exit_ok c₈) fun t₉ h => ⟨h.1, ?_⟩
  simp only [x2K]
  rw [h.2.1, ← stateFrom_x2, ← stateFrom_x2, ← stateFrom_x2, ← stateFrom_x2]
  refine ⟨Scalar.eq_stateFrom fun i hi => ?_, Scalar.eq_stateFrom r₈⟩
  rw [keep (k := 0) (by decide) f₈ i hi, work f₇ i hi 0 (by decide)]
  exact r₆ i hi

/-! ## Both -/

theorem code_ok (sha3 : Bool) (s : State) (hp : x2K.pre s) :
    WP isa (code sha3) s fun t => abiPreserved s t ∧ x2K.post s t := by
  cases sha3
  · exact scalar_ok s hp
  · exact vector_ok s hp

theorem code_taint (sha3 : Bool) :
    ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1]) (code sha3) h).isSome = true := by
  cases sha3
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem code_ct (sha3 : Bool) : ConstantTime isa x2K.pre x2K.pub (code sha3) :=
  Taint.constantTime_of_exists (A := VectorTaint.taint) (VectorTaint.ofRegs [.x0, .x1]) (fun _ _ _ _ h => ⟨⟨h.2.2, fun r hr => by
    simp only [VectorTaint.ofRegs, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1
    · exact h.2.1⟩, fun v hv => by simp [VectorTaint.ofRegs] at hv⟩) (code_taint sha3)

/-- A state the contract allows. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 400⟩, ⟨0x2000, 128⟩]

theorem verified (sha3 : Bool) : Verified AArch64.target (code sha3) (Proof.Sha3.permuteX2Contract AArch64.abi) :=
  Verified.of_correct (T := AArch64.target) (k := x2K) (code_ok sha3) (code_ct sha3) (by
    contract_implies [Proof.Sha3.permuteX2Contract, Proof.Sha3.permuteX2Sig, x2K, pairR, scrR, AArch64.abi, AArch64.argRegs]
      [sat] using sat)

end VG.Proof.Sha3.AArch64.Neon.X2
