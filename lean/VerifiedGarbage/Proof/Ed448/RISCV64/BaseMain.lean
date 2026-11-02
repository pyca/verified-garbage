module

public import VerifiedGarbage.Proof.Ed25519.Contract
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
import VerifiedGarbage.Proof.Ed448.RISCV64.Comb
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Comb
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# Ed448's base-point multiplication on RISCV64: the whole function

`vg_ed448_scalar_base` writes the encoding of `[s]B` to `out`
(`scalarBase_correct`): `R = (0 : 1 : 1)` and `d` (`combInit_ok`), the comb's
table (`Comb.tabBuild_ok`), the scalar's bits, the 114 rows of the comb, after
which `R` represents `[s]B` (`Comb.loop_ok`, `Proof.Ed448.Comb.accScalar_total`),
and the encoding of `R`. (The hypothesis `BaseLadder2Ok` of the earlier
ladder is kept for the registration, unused.)
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (BITS X2 Z2 ACC)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point basePoint identity)

/-- `scalarBaseContract` by register: `out = a0`, `scalar = a1`,
`scratch = a2`. -/
def baseRISCV64 : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let sc : Region := ⟨s.gpr .a1, 57⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .a0) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

section
variable {b : Addr}

/-- An element below `BITS` or above its 456 bytes stays through a write of them. -/
theorem fs_bits {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 BITS, 456⟩] m m') {q : Nat}
    (hq : q + 56 ≤ BITS ∨ BITS + 456 ≤ q) (hq' : q + 56 ≤ 2048) : FS m' b q = FS m b q := by
  have hB : BITS = 1064 := rfl
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega_using [hq, hk]) (by omega_using [hq', hk]) (by omega_using [hB])
  rw [FS, V, val32_congr e]; rfl

/-- The scalar, outside the working space, stays. -/
theorem bytesAt_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : Region.Disjoint ⟨p, 57⟩ ⟨b, 2048⟩) (hrs : ∀ r ∈ rs, Region.Sub r ⟨b, 2048⟩) :
    Spec.Ed448.bytesAt m' p 57 = Spec.Ed448.bytesAt m p 57 := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega) (by omega)) (hrs r hr _ hc)

end

section
variable {b : Addr}

/-- The elements of `combInit`. -/
def cVal (q : Nat) : Fe :=
  if q = RX then Spec.Ed448.identity.X else if q = RY then Spec.Ed448.identity.Y
  else if q = RZ then Spec.Ed448.identity.Z else Spec.Ed448.d

theorem combInit_ok {s : State} (hc : Ctx b s) :
    WP isa (.block combInit) s fun t => Rest [.a4] s t ∧ Frame [FA b] s.mem t.mem ∧
      ∀ q ∈ [RX, RY, RZ, DK], FS t.mem b q = cVal q := by
  have hX : RX = 56 := rfl
  have hY : RY = 0 := rfl
  have hZ : RZ = 112 := rfl
  have hD : DK = 336 := rfl
  have hA : ACC = 952 := rfl
  have fa : ∀ o, o + 56 ≤ ACC + 112 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 o, 56⟩ : Region)], ∃ r' ∈ [FA b],
      Region.Sub r r' := fun o ho r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ ho⟩
  unfold combInit
  simp only [List.append_assoc]
  refine WP.append (constField_ok hc (o := RX) (by omega) (by omega) (fe_lt _)) fun t1 ⟨r1, f1, v1⟩ => ?_
  have c1 := hc.of_rest r1 (by decide)
  refine WP.append (constField_ok c1 (o := RY) (by omega) (by omega) (fe_lt _)) fun t2 ⟨r2, f2, v2⟩ => ?_
  have c2 := c1.of_rest r2 (by decide)
  refine WP.append (constField_ok c2 (o := RZ) (by omega) (by omega) (fe_lt _)) fun t3 ⟨r3, f3, v3⟩ => ?_
  have c3 := c2.of_rest r3 (by decide)
  refine WP.mono (constField_ok c3 (o := DK) (by omega) (by omega) (fe_lt _)) fun t4 ⟨r4, f4, v4⟩ =>
    ⟨r1.trans (r2.trans (r3.trans r4)), (f1.sub (fa _ (by omega))).trans ((f2.sub (fa _ (by omega))).trans
      ((f3.sub (fa _ (by omega))).trans (f4.sub (fa _ (by omega))))), fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · rw [FS, slot_keep f4 (by omega) (by omega) (by omega), slot_keep f3 (by omega) (by omega) (by omega),
      slot_keep f2 (by omega) (by omega) (by omega), v1, Proof.X448.toFe_self]; rfl
  · rw [FS, slot_keep f4 (by omega) (by omega) (by omega), slot_keep f3 (by omega) (by omega) (by omega),
      v2, Proof.X448.toFe_self]; rfl
  · rw [FS, slot_keep f4 (by omega) (by omega) (by omega), v3, Proof.X448.toFe_self]; rfl
  · rw [FS, v4, Proof.X448.toFe_self]; rfl

/-- A slot stays through a write past the field slots. -/
theorem fs_below_region {m m' : Mem} {e n : Nat} (hf : Frame [⟨b + BitVec.ofNat 64 e, n⟩] m m') {q : Nat}
    (hq : q + 56 ≤ e) (he : e + n ≤ 2 ^ 64) : FS m' b q = FS m b q := by
  have e' : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) he
  rw [FS, V, val32_congr e']; rfl

end

theorem scalarBase_correct (_hl : Proof.Ed448.BaseLadder2Ok) {s : State} (hp : baseRISCV64.pre s) :
    WP isa scalarBase s fun s' => baseRISCV64.post s s' := by
  obtain ⟨hrd, hwr, hos, how, hsw⟩ := hp
  have hB : BITS = 1064 := rfl
  obtain ⟨b, hb⟩ : ∃ b, b = Proof.Ed25519.RISCV64.base (s.gpr .a2) := ⟨_, rfl⟩
  have hsub : Region.Sub ⟨b, 2048⟩ ⟨s.gpr .a2, 8192⟩ := by
    have := Proof.Ed25519.RISCV64.base_sub (s.gpr .a2) (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero, ← hb] at this
  have hws : Region.Disjoint ⟨s.gpr .a1, 57⟩ ⟨b, 2048⟩ := hsw.sub_right hsub
  have hwo : Region.Disjoint ⟨b, 2048⟩ ⟨s.gpr .a0, 57⟩ := (how.sub_right hsub).symm
  have hwsr : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  -- The table's region, in the working space.
  have htsub : Region.Sub ⟨Comb.tb b, 1792⟩ ⟨s.gpr .a2, 8192⟩ := by
    have := Align.pad_lt (s.gpr .a2)
    rw [Comb.tb, hb, Proof.Ed25519.RISCV64.base, Offset.add_add]
    exact Offset.sub_base _ (by simp only [CTAB]; omega)
  have hts : Region.Disjoint ⟨s.gpr .a1, 57⟩ ⟨Comb.tb b, 1792⟩ := hsw.sub_right htsub
  unfold scalarBase
  rw [show Impl.X448.RISCV64.align = Impl.X25519.RISCV64.align from rfl]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_mv fun s1 u1 => WP.append (Proof.Ed25519.RISCV64.align_ok (q := s.gpr .a2) u1.gpr
    (by rw [u1.wr]; exact hwsr)) fun s1' ⟨hc1, hr1, hm1⟩ => WP.append (combInit_ok (b := b) (hb ▸ hc1))
    fun s2 ⟨hr2, hf2, hv2⟩ => ?_)
  have hr2' : Rest [.a3, .a4] s s2 :=
    (u1.rest (by decide)).trans ((hr1.mono (by decide)).trans (hr2.mono (by decide)))
  have hc2 : Ctx b s2 := (hb ▸ hc1).of_rest hr2 (by decide)
  have tw2 : Comb.TabW b s2 := fun d n hdn => by
    have := Align.pad_lt (s.gpr .a2)
    rw [hr2'.wr, Comb.tb, hb, Proof.Ed25519.RISCV64.base, Offset.add_add, Offset.add_add]
    exact in_base hwsr (by simp only [CTAB]; omega) (by simp only [CTAB]; omega)
  refine WP.mono (Comb.tabBuild_ok hc2 tw2) fun s2' ⟨hc2', hr2'', hf2', htab2⟩ => ?_
  have hr3' : Rest [.a3, .a4] s s2' := hr2'.trans hr2''
  -- The scalar stays through the stores so far.
  have hk2 : Spec.Ed448.bytesAt s2'.mem (s.gpr .a1) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57 := by
    have e1 : Spec.Ed448.bytesAt s2'.mem (s.gpr .a1) 57 = Spec.Ed448.bytesAt s2.mem (s.gpr .a1) 57 := by
      simp only [Spec.Ed448.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      exact hf2' _ fun r hr hc => hts _ (Offset.contains_base (s.gpr .a1) (show i + 1 ≤ 57 by omega)
        (by omega)) (by rw [List.mem_singleton.mp hr] at hc; exact hc)
    rw [e1, bytesAt_ws hf2 hws fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by simp only [ACC]; omega), hm1, u1.mem]
  -- The scalar's bits.
  refine WP.seq (WP.mono (baseBits_ok hc2' (by rw [hr3'.gpr _ (by decide)])
    (by rw [hr3'.rd, hr3'.wr, hrd]; simp) hws) fun s3 ⟨hc3, hr3, hf3, hb3⟩ => ?_)
  rw [hk2] at hb3
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57) = K at hb3
  -- The elements of `R` and `d`, and the table, at the loop.
  have fs3 : ∀ q ∈ [RX, RY, RZ, DK], FS s3.mem b q = cVal q := fun q hq => by
    have hq' : q + 56 ≤ BITS ∧ q + 56 ≤ 2048 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> decide
    rw [fs_bits hf3 (.inl hq'.1) hq'.2, fs_below_region hf2' (e := CTAB) (by simp only [CTAB]; omega)
      (by simp only [CTAB]; omega), hv2 q hq]
  have tab3 : Comb.TabOk b s3.mem := fun i hi => by
    obtain ⟨e1, e2⟩ := htab2 i hi
    have keep : ∀ o, o + 56 ≤ 2048 → V s3.mem (Comb.tb b) o = V s2'.mem (Comb.tb b) o := fun o ho => by
      unfold V
      refine val32_congr (limb_frame hf3 fun r hr k hk => ?_)
      rw [List.mem_singleton.mp hr, Comb.tb, Offset.add_add]
      exact Offset.disjoint _ (.inr (by simp only [CTAB]; omega)) (by simp only [CTAB]; omega) (by omega)
    exact ⟨by rw [keep _ (by omega), e1], by rw [keep _ (by omega), e2]⟩
  -- The loop.
  unfold combLoop
  refine WP.seq (WP.seq (wp_li (by decide) fun s4 u4 => WP.block_nil ?_))
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.t1]) (by decide)) (by decide)
  have m4 : s4.mem = s3.mem := u4.mem
  have fx : Comb.Fixed b K s4 :=
    ⟨fun d n hdn => by rw [u4.wr, hr3.wr, hr2''.wr]; exact tw2 d n hdn, by rw [m4]; exact tab3,
      by rw [m4]; exact hb3⟩
  have L0 : Comb.LInv b K s4 114 s4 := by
    refine ⟨hc4, R64.Stp.refl _ _, by rw [u4.gpr], ?_, ?_⟩
    · rw [m4, fs3 DK (by decide)]; rfl
    · have e : Comb.ptOf (FS s4.mem b) = Spec.Ed448.identity := by
        simp only [Comb.ptOf]
        rw [m4, fs3 RX (by decide), fs3 RY (by decide), fs3 RZ (by decide)]
        rfl
      rw [e, Proof.Ed448.Comb.accScalar_start, zero_smul]
      exact Proof.Ed448.identity_rep
  refine WP.mono (Comb.loop_ok fx 114 s4 (by decide) (Nat.le_refl _) L0) fun s5 h5 => ?_
  -- The encoding.
  have h05 : s5.gpr .a0 = s.gpr .a0 := by
    rw [h5.stp.rest.gpr _ (by decide), u4.other _ (by decide), hr3.gpr _ (by decide), hr3'.gpr _ (by decide)]
  refine WP.mono (baseEncode_ok h5.ctx h05 (by
      rw [h5.stp.rest.wr, u4.wr, hr3.wr, hr3'.wr, hwr]; simp) hwo
    (p := Comb.ptOf (FS s5.mem b)) fun q hq => ?_) fun s6 h6 => ?_
  · simp only [RQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · exact h5.d
  · show Spec.Ed448.bytesAt s6.mem (s.gpr .a0) 57 = _
    have hlen : (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57).length = 57 := by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]
    have hk := Proof.Ed448.decodeLE_below hlen
    rw [hK] at hk
    unfold Proof.Ed448.Below456 at hk
    have r5 := h5.rep
    -- `Proof/Ed448/Comb.lean` states the bound with `Monoid.npow`: the same, without evaluating it.
    have lt_npow : ∀ {k a n : Nat},
        k < @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) a n →
        k < @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) a n :=
      fun h => h
    have eK : Proof.Ed448.Comb.accScalar K 0 = K := Proof.Ed448.Comb.accScalar_total K (lt_npow hk)
    rw [eK] at r5
    rw [h6, Proof.Ed448.encodePoint_rep r5, Spec.Ed448.scalarBase, hK,
      Proof.Ed448.encodePoint_rep (Proof.Ed448.pointMul_rep K Proof.Ed448.basePoint_rep)]

end VG.Proof.Ed448.RISCV64
