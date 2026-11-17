module

public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.X448.RISCV64.Freeze
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Ed448.Binary
public import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.X448.RISCV64.Field
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Ed448.RISCV64.Scalar
public import VerifiedGarbage.Proof.Ed448.RISCV64.VVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.Ed448.RISCV64.ScalarBit
public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Impl.X448.RISCV64
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.X25519.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
import VerifiedGarbage.Proof.Ed448.RISCV64.Comb
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Comb
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseInit
import VerifiedGarbage.Proof.Ed448.RISCV64.BaseEncode
import VerifiedGarbage.Proof.X448.Field
public import VerifiedGarbage.Proof.Ed448.Ref
public import VerifiedGarbage.Proof.X448.RISCV64.Ladder
public import VerifiedGarbage.TCB.Artifact

/-! ### `Ed448.RISCV64.BaseMain`, which only this module used -/

section

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
  obtain e : ∀ k < 14, limb m' b q k = limb m b q k :=
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
  obtain hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (hrs r hr _ hc)

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
  obtain fa : ∀ o, o + 56 ≤ ACC + 112 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 o, 56⟩ : Region)], ∃ r' ∈ [FA b],
      Region.Sub r r' := fun o ho r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ ho⟩
  unfold combInit
  simp only [List.append_assoc]
  refine WP.append (constField_ok hc (o := RX) (by omega_using [hX]) (by omega_using [hX]) (fe_lt _)) fun t1 ⟨r1, f1, v1⟩ => ?_
  obtain c1 := hc.of_rest r1 (by decide)
  refine WP.append (constField_ok c1 (o := RY) (by omega_using [hY]) (by omega_using [hY]) (fe_lt _)) fun t2 ⟨r2, f2, v2⟩ => ?_
  obtain c2 := c1.of_rest r2 (by decide)
  refine WP.append (constField_ok c2 (o := RZ) (by omega_using [hZ]) (by omega_using [hZ]) (fe_lt _)) fun t3 ⟨r3, f3, v3⟩ => ?_
  obtain c3 := c2.of_rest r3 (by decide)
  refine WP.mono (constField_ok c3 (o := DK) (by omega_using [hD]) (by omega_using [hD]) (fe_lt _)) fun t4 ⟨r4, f4, v4⟩ =>
    ⟨r1.trans (r2.trans (r3.trans r4)), (f1.sub (fa _ (by omega_using [hX]))).trans ((f2.sub (fa _ (by omega_using [hY]))).trans
      ((f3.sub (fa _ (by omega_using [hZ, hA]))).trans (f4.sub (fa _ (by omega_using [hD, hA]))))), fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · rw [FS, slot_keep f4 (by omega_using [hX, hD]) (by omega_using [hD]) (by omega_using [hX]), slot_keep f3 (by omega_using [hX, hZ]) (by omega_using [hZ]) (by omega_using [hX]),
      slot_keep f2 (by omega_using [hX, hY]) (by omega_using [hY]) (by omega_using [hX]), v1, Proof.X448.toFe_self]; rfl
  · rw [FS, slot_keep f4 (by omega_using [hY, hD]) (by omega_using [hD]) (by omega_using [hY]), slot_keep f3 (by omega_using [hY, hZ]) (by omega_using [hZ]) (by omega_using [hY]),
      v2, Proof.X448.toFe_self]; rfl
  · rw [FS, slot_keep f4 (by omega_using [hZ, hD]) (by omega_using [hD]) (by omega_using [hZ]), v3, Proof.X448.toFe_self]; rfl
  · rw [FS, v4, Proof.X448.toFe_self]; rfl

/-- A slot stays through a write past the field slots. -/
theorem fs_below_region {m m' : Mem} {e n : Nat} (hf : Frame [⟨b + BitVec.ofNat 64 e, n⟩] m m') {q : Nat}
    (hq : q + 56 ≤ e) (he : e + n ≤ 2 ^ 64) : FS m' b q = FS m b q := by
  obtain e' : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hq, hk])) (by omega_using [hq, he, hk]) he
  rw [FS, V, val32_congr e']; rfl

end

theorem scalarBase_correct (_hl : Proof.Ed448.BaseLadder2Ok) {s : State} (hp : baseRISCV64.pre s) :
    WP isa scalarBase s fun s' => baseRISCV64.post s s' ∧
      Rest [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t1, .t2, .t3, .t4, .t5, .t6] s s' := by
  obtain ⟨hrd, hwr, hos, how, hsw⟩ := hp
  have hB : BITS = 1064 := rfl
  obtain ⟨b, hb⟩ : ∃ b, b = Proof.Ed25519.RISCV64.base (s.gpr .a2) := ⟨_, rfl⟩
  obtain hsub : Region.Sub ⟨b, 2048⟩ ⟨s.gpr .a2, 8192⟩ := by
    have := Proof.Ed25519.RISCV64.base_sub (s.gpr .a2) (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero, ← hb] at this
  obtain hws : Region.Disjoint ⟨s.gpr .a1, 57⟩ ⟨b, 2048⟩ := hsw.sub_right hsub
  obtain hwo : Region.Disjoint ⟨b, 2048⟩ ⟨s.gpr .a0, 57⟩ := (how.sub_right hsub).symm
  obtain hwsr : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  -- The table's region, in the working space.
  obtain htsub : Region.Sub ⟨Comb.tb b, 1792⟩ ⟨s.gpr .a2, 8192⟩ := by
    have := Align.pad_lt (s.gpr .a2)
    rw [Comb.tb, hb, Proof.Ed25519.RISCV64.base, Offset.add_add]
    exact Offset.sub_base _ (by simp only [CTAB]; omega_using [this])
  obtain hts : Region.Disjoint ⟨s.gpr .a1, 57⟩ ⟨Comb.tb b, 1792⟩ := hsw.sub_right htsub
  unfold scalarBase
  rw [show Impl.X448.RISCV64.align = Impl.X25519.RISCV64.align from rfl]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine WP.seq (wp_mv fun s1 u1 => WP.append (Proof.Ed25519.RISCV64.align_ok (q := s.gpr .a2) u1.gpr
    (by rw [u1.wr]; exact hwsr)) fun s1' ⟨hc1, hr1, hm1⟩ => WP.append (combInit_ok (b := b) (hb ▸ hc1))
    fun s2 ⟨hr2, hf2, hv2⟩ => ?_)
  obtain hr2' : Rest [.a3, .a4] s s2 :=
    (u1.rest (by decide)).trans ((hr1.mono (by decide)).trans (hr2.mono (by decide)))
  obtain hc2 : Ctx b s2 := (hb ▸ hc1).of_rest hr2 (by decide)
  obtain tw2 : Comb.TabW b s2 := fun d n hdn => by
    have := Align.pad_lt (s.gpr .a2)
    rw [hr2'.wr, Comb.tb, hb, Proof.Ed25519.RISCV64.base, Offset.add_add, Offset.add_add]
    exact in_base hwsr (by simp only [CTAB]; omega_using [hdn, this]) (by simp only [CTAB]; omega_using [hdn, this])
  refine WP.mono (Comb.tabBuild_ok hc2 tw2) fun s2' ⟨hc2', hr2'', hf2', htab2⟩ => ?_
  obtain hr3' : Rest [.a3, .a4] s s2' := hr2'.trans hr2''
  -- The scalar stays through the stores so far.
  obtain hk2 : Spec.Ed448.bytesAt s2'.mem (s.gpr .a1) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57 := by
    obtain e1 : Spec.Ed448.bytesAt s2'.mem (s.gpr .a1) 57 = Spec.Ed448.bytesAt s2.mem (s.gpr .a1) 57 := by
      simp only [Spec.Ed448.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      obtain hi := List.mem_range.mp hi
      exact hf2' _ fun r hr hc => hts _ (Offset.contains_base (s.gpr .a1) (show i + 1 ≤ 57 by omega_using [hi])
        (by omega_using [hi])) (by rw [List.mem_singleton.mp hr] at hc; exact hc)
    rw [e1, bytesAt_ws hf2 hws fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by simp only [ACC]; omega_using []), hm1, u1.mem]
  -- The scalar's bits.
  refine WP.seq (WP.mono (baseBits_ok hc2' (by rw [hr3'.gpr _ (by decide)])
    (by rw [hr3'.rd, hr3'.wr, hrd]; simp) hws) fun s3 ⟨hc3, hr3, hf3, hb3⟩ => ?_)
  rw [hk2] at hb3
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57) = K at hb3
  -- The elements of `R` and `d`, and the table, at the loop.
  obtain fs3 : ∀ q ∈ [RX, RY, RZ, DK], FS s3.mem b q = cVal q := fun q hq => by
    obtain hq' : q + 56 ≤ BITS ∧ q + 56 ≤ 2048 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> decide
    rw [fs_bits hf3 (.inl hq'.1) hq'.2, fs_below_region hf2' (e := CTAB) (by simp only [CTAB]; omega_using [hq'])
      (by simp only [CTAB]; omega_using []), hv2 q hq]
  obtain tab3 : Comb.TabOk b s3.mem := fun i hi => by
    obtain ⟨e1, e2⟩ := htab2 i hi
    obtain keep : ∀ o, o + 56 ≤ 2048 → V s3.mem (Comb.tb b) o = V s2'.mem (Comb.tb b) o := fun o ho => by
      unfold V
      refine val32_congr (limb_frame hf3 fun r hr k hk => ?_)
      rw [List.mem_singleton.mp hr, Comb.tb, Offset.add_add]
      exact Offset.disjoint _ (.inr (by simp only [CTAB]; omega_using [hB])) (by simp only [CTAB]; omega_using [ho, hk]) (by omega_using [hB])
    exact ⟨by rw [keep _ (by omega_using [hi]), e1], by rw [keep _ (by omega_using [hi]), e2]⟩
  -- The loop.
  unfold combLoop
  refine WP.seq (WP.seq (wp_li (by decide) fun s4 u4 => WP.block_nil ?_))
  obtain hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.t1]) (by decide)) (by decide)
  have m4 : s4.mem = s3.mem := u4.mem
  obtain fx : Comb.Fixed b K s4 :=
    ⟨fun d n hdn => by rw [u4.wr, hr3.wr, hr2''.wr]; exact tw2 d n hdn, by rw [m4]; exact tab3,
      by rw [m4]; exact hb3⟩
  obtain L0 : Comb.LInv b K s4 114 s4 := by
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
  obtain h05 : s5.gpr .a0 = s.gpr .a0 := by
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
  · refine ⟨?_, (hr3'.mono (by decide)).trans ((hr3.mono (by decide)).trans
      (((u4.rest (ws := [.t1]) (by decide)).mono (by decide)).trans
      ((h5.stp.rest.mono (by decide)).trans (h6.2.mono (by decide)))))⟩
    show Spec.Ed448.bytesAt s6.mem (s.gpr .a0) 57 = _
    obtain hlen : (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57).length = 57 := by
      simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]
    obtain hk := Proof.Ed448.decodeLE_below hlen
    rw [hK] at hk
    unfold Proof.Ed448.Below456 at hk
    have r5 := h5.rep
    -- `Proof/Ed448/Comb.lean` states the bound with `Monoid.npow`: the same, without evaluating it.
    obtain lt_npow : ∀ {k a n : Nat},
        k < @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) a n →
        k < @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) a n :=
      fun h => h
    obtain eK : Proof.Ed448.Comb.accScalar K 0 = K := Proof.Ed448.Comb.accScalar_total K (lt_npow hk)
    rw [eK] at r5
    rw [h6.1, Proof.Ed448.encodePoint_rep r5, Spec.Ed448.scalarBase, hK,
      Proof.Ed448.encodePoint_rep (Proof.Ed448.pointMul_rep K Proof.Ed448.basePoint_rep)]

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.ScalarReduce`, which only this module used -/

section

/-! ### `Ed448.RISCV64.Pack`, which this module and modules that import it used -/

section

/-!
# Ed448 on RISCV64: remainders to memory outside the working space

`packWords a n` copies the `n` words at `a` of the working space to the
aligned words at `t3` (`packWords_ok`), and `scalarFinish` the remainder at
`SR` to the 57 bytes at `out` (`a0`), a byte at a time: its fourteen words and
a zero byte, the encoding of a number below `2⁴⁴⁸` (`finish_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519

/-- After `k` words of `packWords a n` from `s0`. -/
structure PackInv (b q : Addr) (a : Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a4] s0 s
  frame : Frame [⟨q, 4 * k⟩] s0.mem s.mem
  outs : ∀ j < k, wd s.mem q (4 * j) = limb s0.mem b a j

theorem packWords_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h14 : s0.gpr .t3 = q) {a n : Nat}
    (ha : a + 4 * n ≤ 2048) (hn : 4 * n < 2048) (ha4 : a % 4 = 0)
    (hq4 : ∀ k < n, (q + BitVec.ofNat 64 (4 * k)).toNat % 4 = 0)
    (hw : ∀ k < n, InRegions s0.wr (q + BitVec.ofNat 64 (4 * k)) 4)
    (hd : (⟨q, 4 * n⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 4 * n⟩) :
    WP isa (.block (packWords a n)) s0 (PackInv b q a s0 n) := by
  refine wp_range_flatMap (M := isa) (PackInv b q a s0) (fun k s hk h => ?_)
    n (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  unfold packStep
  refine lw0_ok hcs (d := a + 4 * k) (by omega_using [ha, hk]) (by omega_using [ha4]) fun t1 v1 => ?_
  refine wp_stw (a := q + BitVec.ofNat 64 (4 * k)) (by omega_using [ha, hk])
    (by rw [v1.other _ (by decide), h.rest.gpr _ (by decide), h14]) (hq4 k hk)
    (by rw [v1.wr, h.rest.wr]; exact hw k hk) fun t2 v2 => WP.block_nil ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [v2.mem, v1.mem]
  have hsrc : wd s.mem b (a + 4 * k) = limb s0.mem b a k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega_using [hk]) x hx'
    · exact Offset.sub b (d := a + 4 * k) (n := 4) (e := a) (k := 4 * n) (by omega_using []) (by omega_using [hk]) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans (v2.rest _)), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [ha, hk]))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega_using [])
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [ha, hk])]
      exact h.outs j hj
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

theorem pow448_256 : (256 : Nat) ^ 56 = 2 ^ 224 * 2 ^ 224 := by decide +kernel

/-- The 57 bytes of a number below `2⁴⁴⁸`: its 56 bytes and a zero byte. -/
theorem encodeLE_57_zero {x : Nat} (hx : x < 2 ^ 224 * 2 ^ 224) :
    Spec.Ed448.encodeLE 57 x = Proof.X25519.leBytes 56 x ++ [0] := by
  rw [Proof.Ed448.encodeLE_eq, show 57 = 56 + 1 from rfl, Proof.X25519.leBytes_add, Proof.Ed448.leBytes_one,
    Nat.div_eq_of_lt (by rw [pow448_256]; exact hx)]
  rfl

/-- The output of `scalarFinish` from `s0`, after `j` words. -/
structure FinInv (q : Addr) (r : Nat → Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨q, 4 * j⟩] s0.mem s.mem
  words : ∀ i < j, wd s.mem q (4 * i) = r i

theorem outWords_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h3 : s0.gpr .a0 = q)
    (hw : (⟨q, 57⟩ : Region) ∈ s0.wr) (hd : (⟨q, 57⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 SR, 56⟩) :
    WP isa (.block ((List.range 14).flatMap outStep)) s0 (FinInv q (limb s0.mem b SR) s0 14) := by
  have hS : SR = 0 := rfl
  refine wp_range_flatMap (M := isa) (FinInv q (limb s0.mem b SR) s0) (fun k s hk h => ?_)
    14 (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  unfold outStep
  refine lw0_ok hcs (d := SR + 4 * k) (by omega_using [hS, hk]) (by omega_using [hS]) fun t1 v1 => ?_
  have e3 : t1.gpr .a0 = q := by rw [v1.other _ (by decide), h.rest.gpr _ (by decide), h3]
  have hwr : t1.wr = s0.wr := by rw [v1.wr, h.rest.wr]
  refine WP.mono (ByteLoad.storeLE32_ok (by decide) (by decide) (by omega_using [hk])
    (by rw [e3, hwr]; exact in_base hw (by omega_using [hk]) (by omega_using [hk]))) fun t2 e2 => ?_
  have v2 : Rest [.a5] t1 t2 := by
    rw [e2]
    exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (by simpa using hr), rfl, rfl, rfl⟩
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (4 * k)) ((t1.gpr .a4).setWidth 32) := by
    rw [e2, RegUpd.mem_write, e3]
    show t1.mem.writeW _ _ = _
    rw [v1.mem]
  have hsrc : wd s.mem b (SR + 4 * k) = limb s0.mem b SR k := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega_using [hk]) x hx'
    · exact Offset.sub b (d := SR + 4 * k) (n := 4) (e := SR) (k := 56) (by omega_using []) (by omega_using [hk]) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans (v2.mono (by decide))), ?_, fun j hj => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using []) (by omega_using [hk]))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega_using [])
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_using [hk])]
      exact h.words j hj
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

/-- **The remainder at `SR`** as the 57 bytes at `out` (`a0`). -/
theorem finish_ok {b q : Addr} {s0 : State} (hc : Ctx b s0) (h3 : s0.gpr .a0 = q)
    (hw : (⟨q, 57⟩ : Region) ∈ s0.wr)
    (hd : (⟨q, 57⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 SR, 56⟩) :
    WP isa (.block scalarFinish) s0 fun t =>
      Rest [.a4, .a5] s0 t ∧ Frame [⟨q, 57⟩] s0.mem t.mem ∧
      Spec.Ed448.bytesAt t.mem q 57 = Spec.Ed448.encodeLE 57 (V s0.mem b SR) := by
  unfold scalarFinish
  refine WP.append (outWords_ok hc h3 hw hd) fun s1 h1 => ?_
  refine wp_li (by decide) fun s2 u2 => ?_
  refine wp_sb (a := q + BitVec.ofNat 64 56) (by decide)
    (by rw [u2.other _ (by decide), h1.rest.gpr _ (by decide), h3])
    (by rw [u2.wr, h1.rest.wr]; exact in_base hw (by decide) (by decide)) fun s3 u3 => WP.block_nil ?_
  have hm3 : s3.mem = s1.mem.writeW (q + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [u3.mem, u2.gpr, u2.mem]; rfl
  refine ⟨h1.rest.trans ((u2.rest (by decide)).trans (u3.rest _)), ?_, ?_⟩
  · rw [hm3]
    exact (h1.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (n := 8 / 8) (by decide) (by decide))
  · have hlt := V_lt s0.mem b SR
    rw [encodeLE_57_zero hlt, show (57 : Nat) = 56 + 1 from rfl, Proof.Ed448.bytesAt_eq,
      Proof.X25519.bytesAt_add, ← Proof.Ed448.bytesAt_eq]
    congr 1
    · have f3 : Frame [⟨q + BitVec.ofNat 64 56, 1⟩] s1.mem s3.mem := by
        rw [hm3]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
          (Region.contains_self _ (8 / 8))
      have e : ∀ j < 14, wd s3.mem q (4 * j) = limb s0.mem b SR j := fun j hj => by
        rw [wd_frame f3 fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint q (d := 4 * j) (n := 4) (e := 56) (k := 1) (.inl (by omega_using [hj])) (by omega_using [hj]) (by omega_using [])]
        exact h1.words j hj
      exact bytesAt_words14 _ _ e
    · show [s3.mem (q + BitVec.ofNat 64 56 + BitVec.ofNat 64 0)] = [0]
      rw [hm3, VG.WriteBytes.writeW8_apply]
      exact congrArg (· :: []) (ite_eq_left (by simp))

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.ScalarLoop`, which this module and modules that import it used -/

section

/-!
# Ed448 on RISCV64: an integer of `N` bytes modulo `L`

`scalarEngine o N` reads the `N` bytes at `t3` from the top, each into the
remainder at `o` bit by bit (`scalarByte_ok`), and leaves the integer modulo
`L` there (`engine_ok`), for bytes that the remainder and its candidate at
`SD` do not overlap.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Proof.X25519
open VG.Spec.Ed448 (L decodeLE bytesAt)

/-- Bit `j` of a byte, as `consumeBits` takes it. -/
theorem bit_toNat {w : Nat} (hw : w < 256) (j : Nat) :
    ((BitVec.ofNat 64 w).getLsbD j).toNat = w / 2 ^ j % 2 := by
  rw [BitVec.getLsbD_ofNat]
  by_cases hj : j < 64
  · simp only [hj, decide_true, Bool.true_and, Nat.testBit, Nat.shiftRight_eq_div_pow]
    cases h : w / 2 ^ j % 2 == 1 <;> simp_all <;> omega
  · simp only [hj, decide_false, Bool.false_and, Bool.toNat_false]
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide : 2 > 0) (by omega_using [hj] : 8 ≤ j)))]

/-- What the scalar code writes: the remainder at `o` and its candidate. -/
abbrev RD (b : Addr) (o : Nat) : List Region := [⟨b + BitVec.ofNat 64 o, 56⟩, ⟨b + BitVec.ofNat 64 SD, 56⟩]

section
variable {b : Addr}

/-- The bits `js` of the byte in `t5`, in turn. -/
theorem scalarBits_ok {o : Nat} (ho : Rem o) {w : Nat} (hw : w < 256) :
    ∀ (js : List Nat), (∀ j ∈ js, j < 8) → ∀ {s : State}, Ctx b s → (s.gpr .t5).toNat = w →
      V s.mem b o < L →
      WP isa (.block (js.flatMap (scalarBit o))) s fun t =>
        Rest [.a2, .a4, .a5, .t0] s t ∧ Frame (RD b o) s.mem t.mem ∧
        V t.mem b o = js.foldl (fun v j => (2 * v + w / 2 ^ j % 2) % L) (V s.mem b o)
  | [], _, _, _, _, _ => WP.block_nil ⟨Rest.refl _ _, Frame.refl _ _, List.foldl_nil.symm⟩
  | j :: js, hj, s, hc, h16, hr => by
    rw [List.flatMap_cons]
    refine WP.append (scalarBit_ok ho hc hw (hj j List.mem_cons_self) h16 hr) fun t ⟨rt, ft, vt⟩ => ?_
    refine WP.mono (scalarBits_ok ho hw js (fun j h => hj j (List.mem_cons_of_mem _ h))
      (hc.of_rest rt (by decide)) (by rw [rt.gpr _ (by decide), h16])
      (by rw [vt]; exact Nat.mod_lt _ Proof.Ed448.order_pos))
      fun u ⟨ru, fu, vu⟩ => ⟨rt.trans ru, ft.trans fu, by rw [vu, vt]; rfl⟩

/-- One byte: `t4` counted down, the byte at `t3 + t4` into the remainder. -/
theorem scalarByte_ok {o : Nat} (ho : Rem o) {s : State} (hc : Ctx b s) {p : Addr} (h14 : s.gpr .t3 = p)
    {n : Nat} (hn : n + 1 < 2 ^ 15) (h15 : s.gpr .t4 = BitVec.ofNat 64 (n + 1))
    (hin : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 n) 1) (hr : V s.mem b o < L) :
    WP isa (.block (scalarByte o)) s fun t =>
      Rest [.a2, .a4, .a5, .t0, .t4, .t5] s t ∧ Frame (RD b o) s.mem t.mem ∧
      t.gpr .t4 = BitVec.ofNat 64 n ∧
      V t.mem b o = (256 * V s.mem b o + (s.mem (p + BitVec.ofNat 64 n)).toNat) % L := by
  unfold scalarByte scalarRead
  simp only [List.cons_append, List.nil_append]
  refine wp_subi (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e15 : s1.gpr .t4 = BitVec.ofNat 64 n := by
    rw [u1.gpr, h15, ofNat_sub_one (by omega_using []) (by omega_using [hn]), Nat.add_sub_cancel]
  refine wp_lbz (a := p + BitVec.ofNat 64 n) (by decide)
    (by rw [BitVec.add_zero, u2.gpr, u1.other .t3 (by decide), h14, e15])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact hin) fun s3 u3 => ?_
  have hr3 : Rest [.a4, .t4, .t5] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hw := (s.mem (p + BitVec.ofNat 64 n)).isLt
  have h16 : (s3.gpr .t5).toNat = (s.mem (p + BitVec.ofNat 64 n)).toNat := by
    rw [u3.gpr, u2.mem, u1.mem, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [])]
  refine WP.mono (scalarBits_ok ho hw _ (fun j hj => by simpa using hj) (hc.of_rest hr3 (by decide)) h16
    (by rw [hm3]; exact hr)) fun t ⟨rt, ft, vt⟩ => ⟨(hr3.mono (by decide)).trans (rt.mono (by decide)),
      by rw [hm3] at ft; exact ft, by rw [rt.gpr _ (by decide), u3.other _ (by decide), u2.other _ (by decide), e15], ?_⟩
  rw [vt, hm3]
  obtain ⟨w, hw'⟩ : ∃ w, w = (s.mem (p + BitVec.ofNat 64 n)).toNat := ⟨_, rfl⟩
  rw [← hw'] at hw ⊢
  have e : (fun v j => (2 * v + w / 2 ^ j % 2) % L) =
      fun v j => (2 * v + ((BitVec.ofNat 64 w).getLsbD j).toNat) % L :=
    funext fun v => funext fun j => by rw [bit_toNat hw j]
  rw [e]
  have hc8 := Proof.Ed448.consumeBits_eq (BitVec.ofNat 64 w) 8 (V s.mem b o) hr
  have hw64 : (BitVec.ofNat 64 w).toNat = w := by rw [BitVec.toNat_ofNat]; omega_using [hw]
  rw [hw64, Nat.mod_eq_of_lt (show w < 2 ^ 8 by omega_using [hw]), show (2 : Nat) ^ 8 = 256 from rfl] at hc8
  unfold Proof.Ed448.consumeBits at hc8
  exact hc8

theorem bytesAt_drop (m : Mem) (p : Addr) {N n : Nat} (hn : n < N) :
    (bytesAt m p N).drop n = m (p + BitVec.ofNat 64 n) :: (bytesAt m p N).drop (n + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [bytesAt]; omega_using [hn])]
  simp [bytesAt]

/-- After the bytes from `n` up: the remainder of the integer they make. -/
structure EngInv (b p : Addr) (o N : Nat) (s0 : State) (n : Nat) (t : State) : Prop where
  le : n ≤ N
  pos : 1 ≤ n
  rest : Rest [.a2, .a4, .a5, .t0, .t4, .t5] s0 t
  frame : Frame (RD b o) s0.mem t.mem
  t4 : t.gpr .t4 = BitVec.ofNat 64 n
  val : V t.mem b o = decodeLE ((bytesAt s0.mem p N).drop n) % L

/-- **The `N` bytes at `t3`**, modulo `L`, into the remainder at `o`. -/
theorem engine_ok {o : Nat} (ho : Rem o) {N : Nat} (hN : 1 ≤ N) (hN' : N < 2048) {s : State} (hc : Ctx b s)
    {p : Addr} (h14 : s.gpr .t3 = p)
    (hin : ∀ i < N, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hd : ∀ i < N, ∀ r ∈ RD b o, ¬ r.Contains (p + BitVec.ofNat 64 i) 1) :
    WP isa (scalarEngine o N) s fun t =>
      Rest [.a2, .a4, .a5, .t0, .t4, .t5] s t ∧ Frame (RD b o) s.mem t.mem ∧
      V t.mem b o = decodeLE (bytesAt s.mem p N) % L := by
  have hf := ho.fits
  unfold scalarEngine
  rw [List.cons_append]
  refine WP.seq (wp_li (by decide) fun s0 u0 => ?_)
  have hc0 : Ctx b s0 := hc.of_rest (u0.rest (ws := [.a4]) (by decide)) (by decide)
  refine WP.append (stores_ok (r := .a4) (o := o) (n := 14) (by omega_using [hf]) ho.al hc0) fun s1 ⟨hz, hf1, hg1, hr1⟩ =>
    wp_li (by omega_using [hN']) fun s2 u2 => WP.block_nil ?_
  have iN : EngInv b p o N s N s2 := by
    refine ⟨Nat.le_refl _, hN, (u0.rest (by decide)).trans ((hr1.mono (by decide)).trans (u2.rest (by decide))),
      ?_, u2.gpr, ?_⟩
    · rw [u2.mem, ← u0.mem]; exact hf1.mono fun r hr => by simp [List.mem_singleton.mp hr]
    · have : (bytesAt s.mem p N).drop N = [] := by simp [bytesAt]
      rw [this, u2.mem, V, val32_congr (f := limb s1.mem b o) (g := fun _ => 0) (fun k hk => by
        rw [limb, hz k hk, u0.gpr]; rfl), val32_zero_fn]
      rw [show decodeLE [] = 0 from rfl, Nat.zero_mod]
  refine WP.loop (M := isa) (EngInv b p o N s) ?_ N s2 iN
  intro n t h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := h.pos; omega_using [this]⟩
  have hk : k < N := by have := h.le; omega_using [this]
  have hct : Ctx b t := hc.of_rest h.rest (by decide)
  refine WP.mono (scalarByte_ok ho hct (p := p) (by rw [h.rest.gpr _ (by decide), h14]) (by omega_using [hN', hk]) h.t4
    (by rw [h.rest.rd, h.rest.wr]; exact hin k hk)
    (by rw [h.val]; exact Nat.mod_lt _ Proof.Ed448.order_pos)) fun t' ⟨rt, ft, r15, vt⟩ => ?_
  have hb : t.mem (p + BitVec.ofNat 64 k) = s.mem (p + BitVec.ofNat 64 k) :=
    h.frame _ fun r hr => hd k hk r hr
  have hv : V t'.mem b o = decodeLE ((bytesAt s.mem p N).drop k) % L := by
    rw [vt, h.val, hb, bytesAt_drop _ _ hk, Proof.Ed448.reduce_cons]
  have hz : (t'.gpr .t4 != 0) = decide (k ≠ 0) := by rw [r15, ofNat_ne_zero (by omega_using [hN', hk])]
  rw [eval_nonzero, hz]
  by_cases hk0 : k = 0
  · subst hk0
    refine .inl ⟨by simp, h.rest.trans rt, h.frame.trans ft, ?_⟩
    rw [hv, List.drop_zero]
  · exact .inr ⟨by simp [hk0], k, by omega_using [], ⟨by omega_using [hk], by omega_using [hk0], h.rest.trans rt, h.frame.trans ft, r15, hv⟩⟩

end

end VG.Proof.Ed448.RISCV64

end

end

/-!
# Ed448 on RISCV64: `vg_ed448_scalar_reduce`

The function rounds `scratch` up to a multiple of 8 (Ed25519's `align_ok`,
the same two instructions), reduces the 114 bytes of `wide` into `SR`
(`engine_ok`), and writes `SR` to `out` as 57 bytes (`finish_ok`). It uses
only caller-saved registers.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame
open VG.Spec.Ed448 (L decodeLE bytesAt)
open VG.Proof.Ed25519.RISCV64 (base base_sub)

theorem align_eq : Impl.X448.RISCV64.align = Impl.X25519.RISCV64.align := rfl

theorem SR_eq : SR = 0 := rfl

theorem rem_SR : Rem SR := ⟨by decide, by decide, by decide⟩

/-- A byte apart from `scratch` is in none of the rounded working space's parts. -/
theorem not_in_base {x q : Addr} {d n : Nat} (hd : d + n ≤ 2048)
    (h : ¬ (⟨q, 8192⟩ : Region).Contains x 1) : ¬ (⟨base q + BitVec.ofNat 64 d, n⟩ : Region).Contains x 1 :=
  fun hc => h (base_sub q hd x hc)

/-- The precondition, by register: `out` in `a0`, `wide` in `a1`, `scratch` in `a2`. -/
structure ReducePre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 114⟩]
  wr : s.wr = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a2, 8192⟩]
  out_wide : (⟨s.gpr .a0, 57⟩ : Region).Disjoint ⟨s.gpr .a1, 114⟩
  out_ws : (⟨s.gpr .a0, 57⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩
  wide_ws : (⟨s.gpr .a1, 114⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩

theorem reduce_ok {s : State} (hp : ReducePre s) :
    WP isa scalarReduce s fun t =>
      bytesAt t.mem (s.gpr .a0) 57 = Spec.Ed448.scalarReduce (bytesAt s.mem (s.gpr .a1) 114) := by
  have hS := SR_eq
  have hD := SD_eq
  have hws : (⟨s.gpr .a2, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hout : (⟨s.gpr .a0, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  have hwide : (⟨s.gpr .a1, 114⟩ : Region) ∈ s.rd := by rw [hp.rd]; simp
  unfold scalarReduce scalarReduceSetup
  rw [align_eq]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s1 u1 => WP.append
    (Proof.Ed25519.RISCV64.align_ok (q := s.gpr .a2) u1.gpr (by rw [u1.wr]; exact hws))
    fun s2 ⟨hc2, hr2, hm2⟩ => wp_mv fun s3 u3 => WP.block_nil ?_)
  have hr3 : Rest [.a3, .t3] s s3 := (u1.rest (by decide)).trans ((hr2.mono (by decide)).trans (u3.rest (by decide)))
  have hm3 : s3.mem = s.mem := by rw [u3.mem, hm2, u1.mem]
  have hc3 : Ctx (base (s.gpr .a2)) s3 := hc2.of_rest (u3.rest (ws := [.t3]) (by decide)) (by decide)
  have e14 : s3.gpr .t3 = s.gpr .a1 := by
    rw [u3.gpr, hr2.gpr _ (by decide), u1.other _ (by decide)]
  have hwb : ∀ i < 114, ¬ (⟨s.gpr .a2, 8192⟩ : Region).Contains (s.gpr .a1 + BitVec.ofNat 64 i) 1 :=
    fun i hi => hp.wide_ws _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  refine WP.seq (WP.mono (engine_ok rem_SR (N := 114) (by decide) (by decide) hc3 e14
    (fun i hi => by rw [hr3.rd, hr3.wr]; exact in_base (List.mem_append_left _ hwide) (by omega_using [hi]) (by omega_using [hi]))
    (fun i hi r hr => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact not_in_base (by omega_arith) (hwb i hi))) fun s4 ⟨hr4, _, hv4⟩ => ?_)
  rw [hm3] at hv4
  refine WP.mono (finish_ok (hc3.of_rest hr4 (by decide)) (by rw [hr4.gpr _ (by decide), hr3.gpr _ (by decide)])
    (by rw [hr4.wr, hr3.wr]; exact hout) (hp.out_ws.sub_right (base_sub _ (by omega_using [hS]))))
    fun t ⟨_, _, hb⟩ => by rw [hb, hv4]; rfl

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.BaseVerified`, which only this module used -/

section

/-!
# `vg_ed448_scalar_base` on RISC-V, verified

The function meets its contract of `Spec/Ed448/Contract.lean`, with no
stack: the proof against `baseRISCV64`, which it implies, and a state satisfying
it. The correctness proof carries register preservation through the shared
addition-chain call, establishing the ABI obligations.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64

theorem scalarBase_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : baseRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Ed448.RISCV64.scalarBase s t s' ∧ abiPreserved s s' ∧ baseRISCV64.post s s' := by
  obtain ⟨t, s', he, h, hr⟩ := scalarBase_correct hl hs
  exact ⟨t, s', he, ⟨fun r hm => hr.gpr r (by cases r <;> simp_all [preserved]),
    hr.sp, hr.gpr .ra (by decide)⟩, h⟩

end VG.Proof.Ed448.RISCV64

end

end

/-! ### `Ed448.RISCV64.ScalarVerified`, which only this module used -/

section

/-! ### `Ed448.RISCV64.ScalarMulAdd`, which only this module used -/

section

/-!
# `vg_ed448_scalar_mul_add` on RISCV64: correctness

The function rounds `scratch` up to a multiple of 8, reduces `k`, `s` and
`r` modulo `L` into `SK`, `SS` and `SA` (`inputs_ok`, by `engine_ok`),
computes their product row by row at `ACC` (X448's rows, `product_ok`), adds
`SA` (`sum_ok`), stores the sum's 112 bytes at `WIDE`, reduces them modulo
`L` into `SR` (`engine_ok`) and writes `SR` to `out` (`finish_ok`). It writes
only the rounded working space's first 1064 bytes (`LOW`).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Impl.X448.RISCV64 (pass ldSrc addSrc zeroAcc row ACC)
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq RowInv mulPre_ok row_ok
  zeroAcc_ok
open VG.Proof.X25519
open VG.Spec.Ed448 (L decodeLE bytesAt)
open VG.Proof.Ed25519.RISCV64 (base base_sub)

theorem SK_eq : SK = 112 := rfl
theorem SS_eq : SS = 168 := rfl
theorem SA_eq : SA = 224 := rfl
theorem WIDE_eq : WIDE = 280 := rfl

theorem rem_SK : Rem SK := ⟨by decide, by decide, by decide⟩
theorem rem_SS : Rem SS := ⟨by decide, by decide, by decide⟩
theorem rem_SA : Rem SA := ⟨by decide, by decide, by decide⟩

/-- What the function writes of the working space. -/
abbrev LOW (b : Addr) : Region := ⟨b, 1064⟩

theorem sub_low (b : Addr) {d n : Nat} (h : d + n ≤ 1064) : Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (LOW b) :=
  Offset.sub_base b h

theorem frame_low {b : Addr} {m m' : Mem} {rs : List Region} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r (LOW b)) : Frame [LOW b] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem RD_low {b : Addr} {o : Nat} (ho : o + 56 ≤ 1064) : ∀ r ∈ RD b o, Region.Sub r (LOW b) := by
  intro r hr
  have hD := SD_eq
  simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact sub_low b (by omega_arith)

theorem low_ws (b : Addr) : Region.Sub (LOW b) ⟨b, 2048⟩ := Region.sub_prefix (by decide)

/-- The bytes of a buffer apart from the working space are in none of its parts. -/
theorem out_RD {q b : Addr} {N : Nat} (hN : N < 2 ^ 64) (hd : (⟨q, N⟩ : Region).Disjoint ⟨b, 2048⟩) {o : Nat} (ho : o + 56 ≤ 1064) :
    ∀ i < N, ∀ r ∈ RD b o, ¬ r.Contains (q + BitVec.ofNat 64 i) 1 := fun i hi r hr hc =>
  hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (low_ws b _ (RD_low ho r hr _ hc))

/-- The bytes of a buffer apart from the working space, through a frame in it. -/
theorem bytesAt_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p b : Addr} {n : Nat}
    (hd : (⟨p, n⟩ : Region).Disjoint ⟨b, 2048⟩) (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 2048⟩)
    (hn : n < 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt, List.map_inj_left]
  intro i hi
  obtain hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (hs r hr _ hc)

section
variable {b : Addr}

/-- `k`, `s` and `r` (at `t3`, `t6` and `t2`) modulo `L` into `SK`, `SS` and `SA`. -/
theorem inputs_ok {s : State} (hc : Ctx b s) {pk ps pr : Addr} (h14 : s.gpr .t3 = pk)
    (h17 : s.gpr .t6 = ps) (h26 : s.gpr .t2 = pr)
    (hk : (⟨pk, 57⟩ : Region) ∈ s.rd) (hs : (⟨ps, 57⟩ : Region) ∈ s.rd) (hr : (⟨pr, 57⟩ : Region) ∈ s.rd)
    (dk : (⟨pk, 57⟩ : Region).Disjoint ⟨b, 2048⟩) (ds : (⟨ps, 57⟩ : Region).Disjoint ⟨b, 2048⟩)
    (dr : (⟨pr, 57⟩ : Region).Disjoint ⟨b, 2048⟩) :
    WP isa scalarInputs s fun t =>
      Rest [.a2, .a4, .a5, .t0, .t3, .t4, .t5] s t ∧ Frame [LOW b] s.mem t.mem ∧
      V t.mem b SK = decodeLE (bytesAt s.mem pk 57) % L ∧ V t.mem b SS = decodeLE (bytesAt s.mem ps 57) % L ∧
      V t.mem b SA = decodeLE (bytesAt s.mem pr 57) % L := by
  have hK := SK_eq
  have hS := SS_eq
  have hA := SA_eq
  have hD := SD_eq
  obtain inr : ∀ (t : State) (q : Addr), t.rd = s.rd → t.wr = s.wr → (⟨q, 57⟩ : Region) ∈ s.rd →
      ∀ i < 57, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 i) 1 := fun t q h1 h2 hq i hi => by
    rw [h1, h2]; exact in_base (List.mem_append_left _ hq) (by omega_arith) (by omega_arith)
  obtain keep : ∀ {m m' : Mem} {o : Nat}, o + 56 ≤ 1064 → Frame (RD b o) m m' → ∀ (q : Addr),
      (⟨q, 57⟩ : Region).Disjoint ⟨b, 2048⟩ → bytesAt m' q 57 = bytesAt m q 57 := fun ho hf q hq =>
    bytesAt_keep hf hq (fun r hr x hx => low_ws b x (RD_low ho r hr x hx)) (by decide)
  obtain vkeep : ∀ {m m' : Mem} {o a : Nat}, Rem o → (o + 56 ≤ a ∨ a + 56 ≤ o) → Rem a → Frame (RD b a) m m' →
      V m' b o = V m b o := fun ho hoa ha hf => by
    have := ha.fits; have := ha.sep; have := ho.fits; have := ho.sep
    unfold V
    exact val32_congr (limb_frame hf fun r hr k hk => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
  unfold scalarInputs
  refine WP.seq (WP.mono (engine_ok rem_SK (N := 57) (by decide) (by decide) hc h14
    (inr s pk rfl rfl hk) (out_RD (by decide) dk (by omega_arith))) fun s1 ⟨r1, f1, v1⟩ => ?_)
  obtain hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  refine WP.seq (wp_addi (by decide) fun s2 u2 => WP.block_nil ?_)
  obtain hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.t3]) (by decide)) (by decide)
  obtain e14 : s2.gpr .t3 = ps := by rw [u2.gpr, r1.gpr _ (by decide), h17, BitVec.add_zero]
  refine WP.seq (WP.mono (engine_ok rem_SS (N := 57) (by decide) (by decide) hc2 e14
    (inr s2 ps (by rw [u2.rd, r1.rd]) (by rw [u2.wr, r1.wr]) hs) (out_RD (by decide) ds (by omega_arith)))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  obtain hc3 : Ctx b s3 := hc2.of_rest r3 (by decide)
  refine WP.seq (wp_addi (by decide) fun s4 u4 => WP.block_nil ?_)
  obtain hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.t3]) (by decide)) (by decide)
  obtain e14' : s4.gpr .t3 = pr := by
    rw [u4.gpr, r3.gpr _ (by decide), u2.other _ (by decide), r1.gpr _ (by decide), h26, BitVec.add_zero]
  refine WP.mono (engine_ok rem_SA (N := 57) (by decide) (by decide) hc4 e14'
    (inr s4 pr (by rw [u4.rd, r3.rd, u2.rd, r1.rd]) (by rw [u4.wr, r3.wr, u2.wr, r1.wr]) hr) (out_RD (by decide) dr (by omega_arith)))
    fun t ⟨rt, ft, vt⟩ => ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans (rt.mono (by decide)))))
  · rw [u4.mem] at ft
    rw [u2.mem] at f3
    exact (frame_low f1 (RD_low (by omega_arith))).trans ((frame_low f3 (RD_low (by omega_arith))).trans
      (frame_low ft (RD_low (by omega_arith))))
  · rw [vkeep rem_SK (by omega_arith) rem_SA ft, u4.mem, vkeep rem_SK (by omega_arith) rem_SS f3, u2.mem, v1]
  · rw [vkeep rem_SS (by omega_arith) rem_SA ft, u4.mem, v3, u2.mem, keep (by omega_arith) f1 ps ds]
  · rw [vt, u4.mem, keep (by omega_arith) f3 pr dr, u2.mem, keep (by omega_arith) f1 pr dr]

/-- The 28 limbs of the product of `SK` and `SS` at `ACC`. -/
theorem product_ok {s : State} (hc : Ctx b s) :
    WP isa scalarProduct s (RowInv b SK SS s 14) := by
  have hA := ACC_eq
  unfold scalarProduct
  refine WP.seq (WP.mono (mulPre_ok (x := SK) (y := SS) hc) fun s1 h1 => ?_)
  refine WP.loop (M := isa) (fun n s' => ∃ i, n = 14 - i ∧ i < 14 ∧ RowInv b SK SS s i s') ?_ 14 s1
    ⟨0, rfl, by decide, h1⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (row_ok (by decide) (by decide) (by decide) (by decide) hi hr) fun s'' ⟨hr', hz⟩ => ?_
  by_cases h14 : i + 1 = 14
  · refine .inl ⟨by rw [eval_nonzero, hz]; simp [h14], ?_⟩
    rw [h14] at hr'; exact hr'
  · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_arith, 14 - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, hr'⟩

/-- The sum's limbs: the product plus `SA`, at `ACC`. -/
theorem wideAdd_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 28 + V s.mem b SA < 2 ^ 224 * 2 ^ 224 * (2 ^ 224 * 2 ^ 224)) :
    WP isa (.block (([.li .a5 0] : List Instr) ++ pass .a3 ACC (addSrc ACC SA) ++ pass .a3 (ACC + 56) (ldSrc (ACC + 56)))) s
      fun t => Rest [.a2, .a4, .a5] s t ∧ Frame [⟨b + BitVec.ofNat 64 ACC, 112⟩] s.mem t.mem ∧
        val32 (accw ACC t.mem b) 28 = val32 (accw ACC s.mem b) 28 + V s.mem b SA := by
  have hA := ACC_eq
  have hSA := SA_eq
  obtain hl : ∀ k < 28, accw ACC s.mem b k < 2 ^ 32 := fun k _ => wd_lt _ _ _
  obtain hr : ∀ k < 14, limb s.mem b SA k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.a5]) (by decide)) (by decide)
  let c1 : Nat → Nat := fun k => accw ACC s.mem b k + limb s.mem b SA k
  refine WP.append (pass_ok (s0 := s1) (c := c1) (cin := 0) (by decide) (by omega_arith)
    (fun k hk => by rw [hc1.a3]; exact hc1.inW (by omega_arith))
    (fun k hk => by rw [hc1.a3]; exact al4 hc1.al (by omega_arith)) (by rw [u1.gpr]; rfl)
    (fun k hk => by have := hl k (by omega_arith); have := hr k hk; simp only [c1]; omega_arith) (by decide) ?_)
    fun s2 hp => ?_
  · intro k hk s' hp
    obtain hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
    simp only [Impl.X448.RISCV64.addSrc]
    refine lw0_ok hc' (d := ACC + 4 * k) (by omega_arith) (by omega_arith) fun t1 v1 => ?_
    refine lw0_ok (hc'.of_rest (v1.rest (ws := [.a4]) (by decide)) (by decide)) (d := SA + 4 * k) (by omega_arith) (by omega_arith)
      fun t2 v2 => wp_add fun t3 v3 => WP.block_nil ⟨?_, ?_, by rw [v3.mem, v2.mem, v1.mem]⟩
    · have ea : wd s'.mem b (ACC + 4 * k) = accw ACC s.mem b k := by
        rw [wd_pass hc1 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u1.mem]; rfl
      obtain er : wd t1.mem b (SA + 4 * k) = limb s.mem b SA k := by
        rw [v1.mem, wd_pass hc1 hp.frame (by omega_arith) (by omega_arith) (by omega_arith), u1.mem]; rfl
      have := hl k (by omega_arith); have := hr k hk
      rw [v3.gpr, v2.other .a4 (by decide), v1.gpr, v2.gpr]
      unfold wd at ea er
      rw [toNat_add_lt (by rw [toNat_ext32, toNat_ext32, ea, er]; omega_arith), toNat_ext32, toNat_ext32, ea, er]
    · exact (v1.rest (by decide)).trans ((v2.rest (by decide)).trans (v3.rest (by decide)))
  -- The high half, with the carry.
  obtain hr2 : Rest [.a2, .a4, .a5] s s2 := (u1.rest (by decide)).trans hp.rest
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  obtain hf2 : Frame [⟨b + BitVec.ofNat 64 ACC, 56⟩] s.mem s2.mem := by
    have := hp.frame; rw [hc1.a3] at this; rw [← u1.mem]; exact this
  obtain hlo : ∀ j < 14, accw ACC s2.mem b j = out c1 0 j := fun j hj => by
    have := hp.outs j hj; rwa [hc1.a3] at this
  obtain hhi : ∀ j < 14, accw ACC s2.mem b (14 + j) = accw ACC s.mem b (14 + j) := fun j hj => by
    unfold accw
    refine wd_frame hf2 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  let c2 : Nat → Nat := fun k => accw ACC s.mem b (14 + k)
  obtain hc1v : val32 c1 14 = val32 (accw ACC s.mem b) 14 + V s.mem b SA := by
    simp only [c1]; rw [val32_add]; rfl
  obtain v1 := chain_val c1 0 14
  rw [pow448] at v1
  obtain hch1 : chain c1 0 14 ≤ 1 := by
    obtain h1 := val32_lt (f := accw ACC s.mem b) (n := 14) fun k hk => hl k (by omega_arith)
    obtain h2 := V_lt s.mem b SA
    rw [pow448] at h1
    omega_arith
  refine WP.mono (pass_ok (s0 := s2) (c := c2) (cin := chain c1 0 14) (by decide) (by omega_arith)
    (fun k hk => by rw [hc2.a3]; exact hc2.inW (by omega_arith))
    (fun k hk => by rw [hc2.a3]; exact al4 hc2.al (by omega_arith)) hp.a5
    (fun k hk => by have := hl (14 + k) (by omega_arith); simp only [c2]; omega_arith) (by omega_arith) ?_) fun t hq => ?_
  · intro k hk s' hq
    obtain hc' : Ctx b s' := hc2.of_rest hq.rest (by decide)
    refine WP.mono (ldSrc_ok hc' (o := ACC + 56) (k := k) (by omega_arith) (by omega_arith)) fun t1 ⟨e1, r1, m1⟩ =>
      ⟨?_, r1.mono (by decide), m1⟩
    rw [e1, wd_pass hc2 hq.frame (by omega_arith) (by omega_arith) (by omega_arith), show ACC + 56 + 4 * k = ACC + 4 * (14 + k) by omega_arith]
    exact hhi k hk
  · have hfq : Frame [⟨b + BitVec.ofNat 64 (ACC + 56), 56⟩] s2.mem t.mem := by
      have := hq.frame; rwa [hc2.a3] at this
    refine ⟨hr2.trans hq.rest, ?_, ?_⟩
    · refine (hf2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hfq.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      · rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)
      · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · have hlo' : ∀ j < 14, accw ACC t.mem b j = out c1 0 j := fun j hj => by
        rw [← hlo j hj]
        unfold accw
        refine wd_frame hfq fun r hr => ?_
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
      obtain hhi' : ∀ j < 14, accw ACC t.mem b (14 + j) = out c2 (chain c1 0 14) j := fun j hj => by
        have := hq.outs j hj
        rw [hc2.a3] at this
        unfold accw
        rw [show ACC + 4 * (14 + j) = ACC + 56 + 4 * j by omega_arith]; exact this
      obtain v2 := chain_val c2 (chain c1 0 14) 14
      rw [pow448] at v2
      obtain hsum : val32 (accw ACC t.mem b) 28 =
          val32 (out c1 0) 14 + 2 ^ 224 * 2 ^ 224 * val32 (out c2 (chain c1 0 14)) 14 := by
        rw [show (28 : Nat) = 14 + 14 from rfl, val32_append, val32_congr hlo', val32_congr hhi', pow448]
      obtain hs28 : val32 (accw ACC s.mem b) 28 = val32 (accw ACC s.mem b) 14 + 2 ^ 224 * 2 ^ 224 * val32 c2 14 := by
        rw [show (28 : Nat) = 14 + 14 from rfl, val32_append, pow448]
      obtain ho2 := val32_lt (f := out c2 (chain c1 0 14)) (n := 14) fun k _ => out_lt _ _ _
      rw [pow448] at ho2
      -- The final carry is zero: the sum is below `2⁸⁹⁶`.
      obtain hch2 : chain c2 (chain c1 0 14) 14 = 0 := by
        rw [hs28] at hb
        have : val32 c2 14 + chain c1 0 14 < 2 ^ 224 * 2 ^ 224 := by
          rcases Nat.lt_or_ge (val32 c2 14 + chain c1 0 14) (2 ^ 224 * 2 ^ 224) with h' | h'
          · exact h'
          · exfalso
            have := Nat.mul_le_mul_left (2 ^ 224 * 2 ^ 224) h'
            omega_arith
        omega_arith
      rw [hch2, Nat.mul_zero, Nat.add_zero] at v2
      rw [hsum, v2]
      omega_arith

/-- `4n` bytes in memory, as the number of their words. -/
theorem decode_words (m : Mem) (q : Addr) (n : Nat) :
    decodeLE (bytesAt m q (4 * n)) = val32 (fun j => wd m q (4 * j)) n := by
  rw [Proof.Ed448.decodeLE_eq]
  exact leNum_bytesAt4 m q n

/-- `SA` added to the product, and the sum's 112 bytes to `WIDE`. -/
theorem sum_ok {s : State} (hc : Ctx b s)
    (hb : val32 (accw ACC s.mem b) 28 + V s.mem b SA < 2 ^ 224 * 2 ^ 224 * (2 ^ 224 * 2 ^ 224)) :
    WP isa (.block scalarSum) s fun t =>
      Rest [.a2, .a4, .a5, .t3] s t ∧ Frame [LOW b] s.mem t.mem ∧ t.gpr .t3 = b + BitVec.ofNat 64 WIDE ∧
      decodeLE (bytesAt t.mem (b + BitVec.ofNat 64 WIDE) 112) = val32 (accw ACC s.mem b) 28 + V s.mem b SA := by
  have hA := ACC_eq
  have hW := WIDE_eq
  unfold scalarSum
  rw [List.append_assoc (([.li .a5 0] : List Instr) ++ pass .a3 ACC (addSrc ACC SA) ++
    pass .a3 (ACC + 56) (ldSrc (ACC + 56))) ([.addi .t3 .a3 WIDE] : List Instr) (packWords ACC 28)]
  refine WP.append (wideAdd_ok hc hb) fun s1 ⟨r1, f1, v1⟩ => ?_
  obtain hc1 : Ctx b s1 := hc.of_rest r1 (by decide)
  rw [List.cons_append]
  refine wp_addi (by decide) fun s2 u2 => ?_
  obtain e14 : s2.gpr .t3 = b + BitVec.ofNat 64 WIDE := by rw [u2.gpr, hc1.a3]
  obtain hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.t3]) (by decide)) (by decide)
  refine WP.mono (packWords_ok hc2 e14 (a := ACC) (n := 28) (by omega_arith) (by decide) (by decide)
    (fun k hk => by rw [Offset.add_add]; exact al4 hc2.al (by omega_arith))
    (fun k hk => by rw [Offset.add_add]; exact hc2.inW (by omega_arith))
    (Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))) fun t ht => ⟨?_, ?_, ?_, ?_⟩
  · exact (r1.mono (by decide)).trans ((u2.rest (by decide)).trans (ht.rest.mono (by decide)))
  · have f2 := ht.frame
    rw [u2.mem] at f2
    exact (frame_low f1 fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega_arith)).trans
      (frame_low f2 fun r hr => by rw [List.mem_singleton.mp hr]; exact sub_low b (by omega_arith))
  · rw [ht.rest.gpr _ (by decide), e14]
  · rw [show (112 : Nat) = 4 * 28 from rfl, decode_words, ← v1]
    exact val32_congr fun j hj => (ht.outs j hj).trans (by rw [limb, u2.mem]; rfl)

end

theorem mulAdd_mod (a b c n : Nat) : (a % n * (b % n) + c % n) % n = (c + a * b) % n := by
  rw [Nat.add_comm c, Nat.add_mod (a * b), Nat.mul_mod a b, Nat.mod_add_mod]

/-- The precondition, by register: `out` in `a0`, `r`, `k` and `s` in `a1`–`a3`, `scratch` in `a4`. -/
structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a1, 57⟩, ⟨s.gpr .a2, 57⟩, ⟨s.gpr .a3, 57⟩]
  wr : s.wr = [⟨s.gpr .a0, 57⟩, ⟨s.gpr .a4, 8192⟩]
  out_ws : (⟨s.gpr .a0, 57⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  r_ws : (⟨s.gpr .a1, 57⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  k_ws : (⟨s.gpr .a2, 57⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩
  s_ws : (⟨s.gpr .a3, 57⟩ : Region).Disjoint ⟨s.gpr .a4, 8192⟩

theorem mulAdd_ok {s : State} (hp : MulAddPre s) :
    WP isa scalarMulAdd s fun t =>
      bytesAt t.mem (s.gpr .a0) 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem (s.gpr .a1) 57)
        (bytesAt s.mem (s.gpr .a2) 57) (bytesAt s.mem (s.gpr .a3) 57) := by
  have hA := ACC_eq
  have hS := SR_eq
  have hW := WIDE_eq
  have hD := SD_eq
  obtain hws : (⟨s.gpr .a4, 8192⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain hout : (⟨s.gpr .a0, 57⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  obtain ⟨b, hb⟩ : ∃ b, b = base (s.gpr .a4) := ⟨_, rfl⟩
  obtain hsub : Region.Sub ⟨b, 2048⟩ ⟨s.gpr .a4, 8192⟩ := by
    have := base_sub (s.gpr .a4) (o := 0) (n := 2048) (by decide)
    rwa [BitVec.add_zero, ← hb] at this
  unfold scalarMulAdd scalarMulAddArgs
  rw [align_eq]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_mv fun s1 u1 => wp_mv fun s2 u2 => wp_mv fun s3 u3 => wp_mv fun s4 u4 => ?_)
  obtain hr4 : Rest [.t6, .t2, .t3, .a3] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest (by decide))))
  refine WP.append (Proof.Ed25519.RISCV64.align_ok (q := s.gpr .a4)
    (by rw [u4.gpr, u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]) (by rw [hr4.wr]; exact hws))
    fun s5 ⟨hc5, hr5, hm5⟩ => WP.block_nil ?_
  rw [← hb] at hc5
  obtain hr45 : Rest [.t6, .t2, .t3, .a3] s s5 := hr4.trans (hr5.mono (by decide))
  obtain hm45 : s5.mem = s.mem := by rw [hm5, u4.mem, u3.mem, u2.mem, u1.mem]
  obtain e14 : s5.gpr .t3 = s.gpr .a2 := by
    rw [hr5.gpr _ (by decide), u4.other _ (by decide), u3.gpr, u2.other _ (by decide), u1.other _ (by decide)]
  obtain e17 : s5.gpr .t6 = s.gpr .a3 := by
    rw [hr5.gpr _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.gpr]
  obtain e26 : s5.gpr .t2 = s.gpr .a1 := by
    rw [hr5.gpr _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.other _ (by decide)]
  obtain e27 : s5.gpr .a0 = s.gpr .a0 := hr45.gpr _ (by decide)
  obtain hin : ∀ r : Reg, r = .a1 ∨ r = .a2 ∨ r = .a3 → (⟨s.gpr r, 57⟩ : Region) ∈ s5.rd := by
    rintro r (rfl | rfl | rfl) <;> (rw [hr45.rd, hp.rd]; simp)
  refine WP.seq (WP.mono (inputs_ok hc5 e14 e17 e26 (hin _ (.inr (.inl rfl))) (hin _ (.inr (.inr rfl)))
    (hin _ (.inl rfl)) (hp.k_ws.sub_right hsub) (hp.s_ws.sub_right hsub) (hp.r_ws.sub_right hsub))
    fun s7 ⟨r7, f7, vk, vs, vr⟩ => ?_)
  rw [hm45] at vk vs vr
  obtain hc7 : Ctx b s7 := hc5.of_rest r7 (by decide)
  refine WP.seq (WP.mono (product_ok hc7) fun s8 h8 => ?_)
  have hc8 := h8.ctx
  obtain hvA : V s8.mem b SA = V s7.mem b SA := by
    unfold V
    exact val32_congr (limb_frame h8.frame fun r hr j hj => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by rw [SA_eq]; omega_arith)) (by rw [SA_eq]; omega_arith)
        (by omega_arith))
  obtain hKL : V s7.mem b SK < L := by rw [vk]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  obtain hSL : V s7.mem b SS < L := by rw [vs]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  obtain hAL : V s7.mem b SA < L := by rw [vr]; exact Nat.mod_lt _ Proof.Ed448.order_pos
  have hLt := L_lt
  obtain hprod : V s7.mem b SK * V s7.mem b SS ≤ (2 ^ 224 * 2 ^ 222) * (2 ^ 224 * 2 ^ 222) :=
    Nat.mul_le_mul (by omega_arith) (by omega_arith)
  have hv8 : val32 (accw ACC s8.mem b) 28 = V s7.mem b SK * V s7.mem b SS := h8.val
  refine WP.seq (WP.mono (sum_ok hc8 (by rw [hv8, hvA]; omega_arith)) fun s9 ⟨r9, f9, e9, v9⟩ => ?_)
  obtain hc9 : Ctx b s9 := hc8.of_rest r9 (by decide)
  refine WP.seq (WP.mono (engine_ok rem_SR (N := 112) (by decide) (by decide) hc9 e9
    (fun i hi => by rw [Offset.add_add]; exact hc9.inR (by omega_arith))
    (fun i hi r hr => by
      simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Offset.add_add]
      rcases hr with rfl | rfl <;>
        exact fun hc => Offset.disjoint b (d := WIDE + i) (n := 1) (k := 56) (.inr (by omega_arith))
          (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) hc)) fun s10 ⟨r10, f10, v10⟩ => ?_)
  obtain hc10 : Ctx b s10 := hc9.of_rest r10 (by decide)
  obtain hr10 : Rest [.a1, .a2, .a4, .a5, .a6, .a7, .t0, .t3, .t4, .t5] s5 s10 :=
    (r7.mono (by decide)).trans ((h8.rest.mono (by decide)).trans ((r9.mono (by decide)).trans (r10.mono (by decide))))
  refine WP.mono (finish_ok hc10 (q := s.gpr .a0) (by rw [hr10.gpr _ (by decide), e27])
    (by rw [hr10.wr, hr45.wr]; exact hout)
    ((hp.out_ws.sub_right hsub).sub_right (Offset.sub_base _ (by omega_arith))))
    fun t ⟨_, _, h3⟩ => ?_
  rw [h3, v10, v9, hv8, hvA, vk, vs, vr]
  unfold Spec.Ed448.scalarMulAdd
  exact congrArg (Spec.Ed448.encodeLE 57) (mulAdd_mod _ _ _ _)

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's scalar functions on RISC-V, verified

Each function meets its shared contract of `Spec/Ed448/Contract.lean`: the
proof against a contract by register (`reduceRISCV64`, `mulAddRISCV64`),
which the shared one implies, and a state satisfying it. The functions call
no function and write only caller-saved registers (`WP.keep`), so the ABI's
obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64

/-- `scalarReduceContract` by register. -/
def reduceRISCV64 : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let wide : Region := ⟨s.gpr .a1, 114⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [wide] ∧ s.wr = [out, ws] ∧ out.Disjoint wide ∧ out.Disjoint ws ∧ wide.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .a0) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 114)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.sp = s₂.sp

theorem reduce_ok' (s : State) (hs : reduceRISCV64.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed448.RISCV64.scalarReduce s t s' ∧ abiPreserved s s' ∧
      reduceRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hs
  obtain ⟨t, s', he, hb, hk⟩ := WP.keep [.a2, .a3, .a4, .a5, .a6, .a7, .t0, .t3, .t4, .t5]
    (reduce_ok ⟨h1, h2, h3, h4, h5⟩) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hb⟩

/-- `scalarMulAddContract` by register. -/
def mulAddRISCV64 : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 57⟩
    let r : Region := ⟨s.gpr .a1, 57⟩
    let k : Region := ⟨s.gpr .a2, 57⟩
    let a : Region := ⟨s.gpr .a3, 57⟩
    let ws : Region := ⟨s.gpr .a4, 8192⟩
    s.rd = [r, k, a] ∧ s.wr = [out, ws] ∧ out.Disjoint ws ∧ r.Disjoint ws ∧ k.Disjoint ws ∧ a.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .a0) 57 =
    Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt s.mem (s.gpr .a1) 57)
      (Spec.Ed448.bytesAt s.mem (s.gpr .a2) 57) (Spec.Ed448.bytesAt s.mem (s.gpr .a3) 57)
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

theorem mulAdd_ok' (s : State) (hs : mulAddRISCV64.pre s) :
    ∃ t s', VG.Exec isa Impl.Ed448.RISCV64.scalarMulAdd s t s' ∧ abiPreserved s s' ∧
      mulAddRISCV64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
  obtain ⟨t, s', he, hb, hk⟩ := WP.keep [.a1, .a2, .a3, .a4, .a5, .a6, .a7, .t0, .t2, .t3, .t4, .t5, .t6]
    (mulAdd_ok ⟨h1, h2, h3, h4, h5, h6⟩) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_keep he hk (by decide) (by decide), hb⟩

end VG.Proof.Ed448.RISCV64

end

end


/-!
# Ed448's whole functions on RISCV64: the calls of the Ed448 functions

`base_call`, `reduce_call`, `mulAdd_call` and `veq_call`: a call of
`vg_ed448_scalar_base`, `vg_ed448_scalar_reduce`, `vg_ed448_scalar_mul_add`
or `vg_ed448_verify_equation` with its arguments in `a0`–`a4`, by its
contract by register (`baseRISCV64`, …): what it writes, that it keeps the
callee-saved registers, and its result. None of them has a frame
(`*_noFrames`, checked once here).
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64.Whole

open VG VG.RISCV64
open VG.Spec.Ed448 (bytesAt)

theorem base_noFrames : Impl.Ed448.RISCV64.scalarBase.noFrames = true := by decide +kernel
theorem reduce_noFrames : Impl.Ed448.RISCV64.scalarReduce.noFrames = true := by decide +kernel
theorem mulAdd_noFrames : Impl.Ed448.RISCV64.scalarMulAdd.noFrames = true := by decide +kernel
theorem veq_noFrames : Impl.Ed448.RISCV64.verifyEquation.noFrames = true := by decide +kernel

theorem ce_gpr (s : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

section
variable {s : State} {Q : State → Prop}

theorem base_call (hl : Proof.Ed448.BaseLadder2Ok) {out sc ws : Addr} (h0 : s.gpr .a0 = out)
    (h1 : s.gpr .a1 = sc) (h2 : s.gpr .a2 = ws) (d₀ : Region.Disjoint ⟨out, 57⟩ ⟨sc, 57⟩)
    (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₂ : Region.Disjoint ⟨sc, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨sc, 57⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr)) (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarBase (bytesAt s.mem sc 57) → Q s') :
    WP isa (.call "vg_ed448_scalar_base" Impl.Ed448.RISCV64.scalarBase) s Q := by
  refine WP.call (k := baseRISCV64) (scalarBase_ok hl) (rd := [⟨sc, 57⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), h1],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h2],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h1]; exact d₀,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h2]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h1, h2]; exact d₂⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) base_noFrames
  simp only [baseRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    h0, h1] at hp
  exact hp

theorem reduce_call {out wide ws : Addr} (h0 : s.gpr .a0 = out) (h1 : s.gpr .a1 = wide) (h2 : s.gpr .a2 = ws)
    (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨wide, 114⟩) (d₂ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₃ : Region.Disjoint ⟨wide, 114⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨wide, 114⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarReduce (bytesAt s.mem wide 114) → Q s') :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.RISCV64.scalarReduce) s Q := by
  refine WP.call (k := reduceRISCV64) reduce_ok' (rd := [⟨wide, 114⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), h1],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h2],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h1]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h2]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h1, h2]; exact d₃⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) reduce_noFrames
  simp only [reduceRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    h0, h1] at hp
  exact hp

theorem mulAdd_call {out r k a ws : Addr} (h0 : s.gpr .a0 = out) (h1 : s.gpr .a1 = r) (h2 : s.gpr .a2 = k)
    (h3 : s.gpr .a3 = a) (h4 : s.gpr .a4 = ws) (d₁ : Region.Disjoint ⟨out, 57⟩ ⟨ws, 8192⟩)
    (d₂ : Region.Disjoint ⟨r, 57⟩ ⟨ws, 8192⟩) (d₃ : Region.Disjoint ⟨k, 57⟩ ⟨ws, 8192⟩)
    (d₄ : Region.Disjoint ⟨a, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨r, 57⟩, ⟨k, 57⟩, ⟨a, 57⟩] ++ [⟨out, 57⟩, ⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨out, 57⟩, ⟨ws, 8192⟩] s.wr)
    (K : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨out, 57⟩, ⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      bytesAt s'.mem out 57 = Spec.Ed448.scalarMulAdd (bytesAt s.mem r 57) (bytesAt s.mem k 57)
        (bytesAt s.mem a 57) → Q s') :
    WP isa (.call "vg_ed448_scalar_mul_add" Impl.Ed448.RISCV64.scalarMulAdd) s Q := by
  refine WP.call (k := mulAddRISCV64) mulAdd_ok' (rd := [⟨r, 57⟩, ⟨k, 57⟩, ⟨a, 57⟩]) (wr := [⟨out, 57⟩, ⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
        h1, h2, h3],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h4],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h4]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h1, h4]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h2, h4]; exact d₃,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h3, h4]; exact d₄⟩ hc hw
    (fun s' a b c f g _ hp => K s' a b c f g ?_) mulAdd_noFrames
  simp only [mulAddRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide),
    h0, h1, h2, h3] at hp
  exact hp

theorem veq_call (hR : Proof.Ed448.RecoverOk) {pk sig ch ws : Addr}
    (h0 : s.gpr .a0 = pk) (h1 : s.gpr .a1 = sig) (h2 : s.gpr .a2 = ch) (h3 : s.gpr .a3 = ws)
    (d₁ : Region.Disjoint ⟨pk, 57⟩ ⟨ws, 8192⟩) (d₂ : Region.Disjoint ⟨sig, 114⟩ ⟨ws, 8192⟩)
    (d₃ : Region.Disjoint ⟨ch, 57⟩ ⟨ws, 8192⟩)
    (hc : Covers ([⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩] ++ [⟨ws, 8192⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨ws, 8192⟩] s.wr)
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame [⟨ws, 8192⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      (s'.gpr .a0).setWidth 32 = (if Spec.Ed448.verifyEquation (bytesAt s.mem pk 57) (bytesAt s.mem sig 114)
        (bytesAt s.mem ch 57) then 1 else 0) → Q s') :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.RISCV64.verifyEquation) s Q := by
  refine WP.call (k := verifyRISCV64) (verifyEquation_ok hR) (rd := [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩])
    (wr := [⟨ws, 8192⟩])
    ⟨by rw [State.withRegions_rd, ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide),
        h0, h1, h2],
      by rw [State.withRegions_wr, ce_gpr _ _ _ (by decide), h3],
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h0, h3]; exact d₁,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h1, h3]; exact d₂,
      by rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), h2, h3]; exact d₃⟩ hc hw
    (fun s' a b c f g _ hp => k s' a b c f g ?_) veq_noFrames
  simp only [verifyRISCV64, State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), h0, h1, h2] at hp
  exact hp

end

end VG.Proof.Ed448.RISCV64.Whole
