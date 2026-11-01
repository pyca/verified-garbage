module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Mont1
public import VerifiedGarbage.Proof.Rsa.Arm.RvVP
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Arm.RvMont

/-! # A candidate on ARMv7: steps that keep Montgomery multiplication ready

`MS.of_read`: the same header, arrays 0 and 4 and frame word 0 keep `MS`;
`MS.of_keep`: so does a step of the key working space that writes none of
the key arrays 15–21 and 25; `VP.withMS`: a piece with such a step keeps
`MS` alongside its stages.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {P : CP} {σ : State}

/-- The bytes of the header and of the number in array 0. -/
abbrev mHd (P : CP) : Nat := arrAt P.w 0 + 8 * P.w

/-- The bytes `MSp` reads: the header's first 16 words and the number in array 0. -/
abbrev MRd (P : CP) (d n : Nat) : Prop := d + n ≤ 128 ∨ (arrAt P.w 0 ≤ d ∧ d + n ≤ mHd P)

/-- The same first header words, arrays 0 and 4, and frame word 0. -/
theorem MSp.of_read {s t : State} (h : MSp P σ s)
    (e : ∀ d n, MRd P d n → t.mem.read (off (State.addr P.M0) d) n = s.mem.read (off (State.addr P.M0) d) n)
    (e4 : numAt t.mem (State.addr P.M0) P.w 4 = numAt s.mem (State.addr P.M0) P.w 4)
    (sv : t.mem.readW (State.addr t.sp) 32 = s.mem.readW (State.addr s.sp) 32)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MSp P σ t := by
  have hw : 2 ≤ P.w := h.width ▸ h.layout.1
  have ew : ∀ d, MRd P d 8 → t.mem.readW (off (State.addr P.M0) d) 64 = s.mem.readW (off (State.addr P.M0) d) 64 :=
    fun d hd => by simp only [Mem.readW, e d 8 hd]
  have width : wOf t.mem (State.addr P.M0) = wOf s.mem (State.addr P.M0) :=
    congrArg BitVec.toNat (ew 48 (.inl (by decide)))
  refine ⟨h.workspace.congr wr, ?_, width.trans h.width, ?_, ?_, e4.trans h.r2, ?_, ?_, ?_⟩
  · have layout := h.layout
    unfold Layout at layout ⊢
    rw [width]
    refine ⟨layout.1, layout.2.1, layout.2.2.1, fun j hj => ?_⟩
    unfold wordAt
    rw [ew _ (.inl (by simp only [Proof.Rsa.Mont.arrWord]; omega_arith))]
    exact layout.2.2.2 j hj
  · change ((t.mem.readW (off (State.addr P.M0) (arrAt P.w 0)) 64).toNat *
      (t.mem.readW (off (State.addr P.M0) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [ew _ (.inr ⟨Nat.le_refl _, by simp only [mHd]; omega_arith⟩), ew 56 (.inl (by decide))]
    exact h.inverse
  · unfold numAt
    rw [show State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w 0) = off (State.addr P.M0) (arrAt P.w 0) from rfl,
      e _ _ (.inr ⟨Nat.le_refl _, Nat.le_refl _⟩)]
    exact h.n0
  · rw [rd, wr, sp]; exact h.stackRead
  · rw [sp]; exact h.stackSep
  · rw [sv]; exact h.saved

/-- The same first header words, arrays 0 and 4, frame word 0, and header word 28. -/
theorem MS.of_read {s t : State} (h : MS P σ s)
    (e : ∀ d n, MRd P d n ∨ (224 ≤ d ∧ d + n ≤ 232) →
      t.mem.read (off (State.addr P.M0) d) n = s.mem.read (off (State.addr P.M0) d) n)
    (e4 : numAt t.mem (State.addr P.M0) P.w 4 = numAt s.mem (State.addr P.M0) P.w 4)
    (sv : t.mem.readW (State.addr t.sp) 32 = s.mem.readW (State.addr s.sp) 32)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MS P σ t := by
  refine ⟨h.toMSp.of_read (fun d n hd => e d n (.inl hd)) e4 sv sp rd wr, ?_⟩
  unfold wordAt
  rw [show State.addr P.M0 + BitVec.ofNat 64 (8 * 28) = off (State.addr P.M0) (8 * 28) from rfl]
  simp only [Mem.readW]
  rw [e (8 * 28) 8 (.inr ⟨by decide, by decide⟩)]
  exact h.stride

/-- Memory that changed only within the working space. -/
theorem Keep.frameS {v : Nat} {js ds : List Nat} {m m' : Mem} (k : Keep P.B v js ds m m')
    (hj : ∀ j ∈ js, arr v j + S v ≤ P.Z) (hd : ∀ d ∈ ds, d + 4 ≤ P.Z) : Frame [P.rS] m m' := by
  intro x hx
  have hz' : ¬ P.rS.Contains x 1 := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hz'
  exact k.out (Z := P.Z) hj hd (by simp only [ofs]; omega_arith)

/-- The key arrays a step may write and keep `MS`. -/
abbrev MOk (j : Nat) : Prop := j < 15 ∨ (mBase < j ∧ j ≠ mBase + 4 ∧ j < nArr)

/-- A step of the key working space that writes none of the key arrays 15–21
and 25 keeps `MS`. -/
theorem MS.of_keep (pre : In P σ) {s t : State} (h : MS P σ s) {js ds : List Nat}
    (k : Keep P.B P.W js ds s.mem t.mem) (hjs : ∀ j ∈ js, MOk j) (hds : ∀ d ∈ ds, d + 4 ≤ hdr)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (spw : s.sp = P.sp) : MS P σ t := by
  have hf := pre.fS
  have e1 := pre.oM_arrAt 1
  have e4 := pre.oM_arrAt 4
  have l := pre.oM_le
  have hfit := Nat.le_trans (arr_mono (w := P.W) (show mBase + 8 ≤ nArr by decide)) pre.fits
  have zl := pre.Z_le
  have hS := pre.S_eq
  -- A byte at an offset of the header, array 0 or array 4 is kept.
  have kb : ∀ e i, (P.oM ≤ e + i ∧ e + i < arr P.W (mBase + 1)) ∨
      (arr P.W (mBase + 4) ≤ e + i ∧ e + i < arr P.W (mBase + 5)) →
      t.mem (off (State.addr P.B) e + BitVec.ofNat 64 i) = s.mem (off (State.addr P.B) e + BitVec.ofNat 64 i) :=
      fun e i hi => by
    have : arr P.W (mBase + 1) ≤ arr P.W (mBase + 5) := arr_mono (by decide)
    have : arr P.W (mBase + 5) ≤ arr P.W (mBase + 8) := arr_mono (by decide)
    refine k _ fun r hr => ?_
    rw [ofs_off _ (by omega_arith)]
    simp only [ranges, List.mem_append, List.mem_map] at hr
    rcases hr with ⟨j, hj, rfl⟩ | ⟨d', hd', rfl⟩
    · have hjo := hjs j hj
      dsimp only
      rcases hjo with c | ⟨c1, c2, c3⟩
      · have := arr_end (w := P.W) (show j < 15 by omega_arith); omega_arith
      · rcases Nat.lt_or_gt_of_ne c2 with c4 | c4
        · have := arr_end (w := P.W) c4
          have := arr_mono (w := P.W) (show mBase + 1 ≤ j by omega_arith)
          omega_arith
        · have := arr_mono (w := P.W) (show mBase + 5 ≤ j by omega_arith)
          have : arr P.W (mBase + 1) ≤ arr P.W (mBase + 4) := arr_mono (by decide)
          omega_arith
    · have := hds d' hd'
      have : hdr ≤ arr P.W 15 := Nat.le_add_right _ _
      dsimp only; omega_arith
  refine h.of_read (fun d n hdn => ?_) ?_ ?_ sp rd wr
  · rw [pre.M0_off]
    have hdn : d + n ≤ mHd P := by
      have : 232 ≤ arrAt P.w 0 := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith
      rcases hdn with (h1 | ⟨_, h1⟩) | ⟨_, h1⟩ <;> simp only [mHd] at * <;> omega_arith
    simp only [mHd] at hdn
    refine Mem.read_congr fun i hi => ?_
    have c1 : P.oM ≤ P.oM + d + i := by rw [Nat.add_assoc]; exact Nat.le_add_right _ _
    have a01 : arrAt P.w 0 + 8 * P.w ≤ arrAt P.w 1 := by simp only [arrAt]; omega_arith
    have c2 : P.oM + d + i < arr P.W (mBase + 1) := by omega_using [hdn, hi, e1, a01]
    exact kb (P.oM + d) i (.inl ⟨c1, c2⟩)
  · unfold numAt
    rw [show State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w 4) = off (State.addr P.M0) (arrAt P.w 4) from rfl,
      pre.M0_off]
    have e5 := pre.oM_arrAt 5
    have d45 : arrAt P.w 5 = arrAt P.w 4 + 8 * (P.w + 2) := by
      simp only [arrAt, show 5 = 4 + 1 from rfl, Nat.add_mul, Nat.one_mul]; omega_arith
    refine congrArg BitVec.toNat (Mem.read_congr fun i hi => ?_)
    have c1 : arr P.W (mBase + 4) ≤ P.oM + arrAt P.w 4 + i := by omega_using [e4]
    have c2 : P.oM + arrAt P.w 4 + i < arr P.W (mBase + 5) := by omega_using [hi, e5, d45]
    exact kb (P.oM + arrAt P.w 4) i (.inr ⟨c1, c2⟩)
  · rw [sp, spw]
    have hfr := Keep.frameS (P := P) k (fun j hj => by
      rcases hjs j hj with c | ⟨_, _, c⟩
      · exact pre.fitZ (by simp only [nArr]; omega_arith)
      · exact pre.fitZ c) (fun d hd => Nat.le_trans (hds d hd) pre.hdr_Z)
    exact hfr.readW (r := P.rW0) (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact pre.sF.symm.sub_left (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 88) (by decide) |>
          fun h => by simpa using h)) (by decide)

end

/-- A piece keeps an invariant `X` that its code keeps from its stages. -/
theorem VP.withX {F G X : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (hx : ∀ σ s, F σ s → X σ s → WP isa c s (X σ)) :
    VP (fun σ s => F σ s ∧ X σ s) c (fun σ s => G σ s ∧ X σ s) :=
  VP.of_ct (fun _ _ => h.ct.mono (fun _ _ ⟨⟨f₁, _⟩, ⟨f₂, _⟩⟩ => ⟨_, _, f₁, f₂⟩) fun _ _ _ => trivial)
    fun σ s ⟨f, x⟩ => WP.and (h.wp σ s f) (hx σ s f x)

/-- A piece whose code writes none of the key arrays 15–21 and 25 keeps `MS`. -/
theorem VP.withMS {P : CP} {F G : State → State → Prop} {c : Prog isa} (h : VP F c G)
    (hpre : ∀ σ s, F σ s → In P σ ∧ s.sp = P.sp)
    (hk : ∀ σ s, F σ s → WP isa c s fun t => ∃ js ds, Keep P.B P.W js ds s.mem t.mem ∧ (∀ j ∈ js, MOk j) ∧
      (∀ d ∈ ds, d + 4 ≤ hdr) ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) :
    VP (fun σ s => F σ s ∧ MS P σ s) c (fun σ s => G σ s ∧ MS P σ s) :=
  VP.withX h fun σ s f m => WP.mono (hk σ s f) fun _ ⟨_, _, k, hjs, hds, sp, rd, wr⟩ =>
    m.of_keep (hpre σ s f).1 k hjs hds sp rd wr (hpre σ s f).2

end VG.Proof.Dsa.Arm.Prime
