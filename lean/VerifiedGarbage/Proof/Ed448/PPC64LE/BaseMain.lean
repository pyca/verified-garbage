module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseStep
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ed448.PPC64LE.Comb
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseInit
import VerifiedGarbage.Proof.Ed448.PPC64LE.BaseEncode
import VerifiedGarbage.Proof.Ed448.Comb
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.Field
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass

/-!
# Ed448's base-point multiplication on PPC64LE: the whole function

`vg_ed448_scalar_base` writes the encoding of `[s]B` to `out`, and returns
with the link register it was called with (`scalarBase_correct`): the
return address and the caller's `r14` kept at `LRS` and `R14S`, and `out` in `r14`, `R = (0 : 1 : 1)` and
`d` (`combInit_ok`), the comb's table (`Comb.tabBuild_ok`), the scalar's
bits, the 114 rows of the comb, after which `R` represents `[s]B`
(`Comb.loop_ok`, `Proof.Ed448.Comb.accScalar_total`), the return address and
`r14` loaded back (and `out` into `r3`), and the encoding of `R`. (The hypothesis `BaseLadder2Ok`
of the earlier ladder is kept for the registration, unused.)
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Impl.X448.PPC64LE (BITS X2 Z2 ACC)
open VG.Spec.X448 (Fe)
open VG.Spec.Ed448 (Point basePoint identity)

/-- `scalarBaseContract` by register: `out = r3`, `scalar = r4`,
`scratch = r5`. -/
def basePPC : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 57⟩
    let sc : Region := ⟨s.gpr .r4, 57⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := Spec.Ed448.bytesAt s'.mem (s.gpr .r3) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 57)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

section
variable {b : Addr}

/-- An element below `BITS` or above its 456 bytes stays through a write of them. -/
theorem fs_bits {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 BITS, 456⟩] m m') {q : Nat}
    (hq : q + 56 ≤ BITS ∨ BITS + 456 ≤ q) (hq' : q + 56 ≤ 4096) : FS m' b q = FS m b q := by
  have hB : BITS = 1064 := rfl
  have e : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (by omega_using [hq, hk]) (by omega_using [hq', hk]) (by omega_using [hB])
  rw [FS, V, val32_congr e]; rfl

/-- The scalar, outside the working space, stays. -/
theorem bytesAt_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : Region.Disjoint ⟨p, 57⟩ ⟨b, 4096⟩) (hrs : ∀ r ∈ rs, Region.Sub r ⟨b, 4096⟩) :
    Spec.Ed448.bytesAt m' p 57 = Spec.Ed448.bytesAt m p 57 := by
  simp only [Spec.Ed448.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega) (by omega)) (hrs r hr _ hc)

end

section
variable {b : Addr} {s : State} {is : List Instr} {Q : State → Prop}

/-- `addi`, keeping the link register. -/
theorem wp_addiL {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _) rfl)

/-- `ld`, keeping the link register. -/
theorem wp_ldL {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_load_d hn ho hin) (k _ (Upd.write _ _ _) rfl)

theorem wp_mflr {d : Reg} (k : ∀ s', Upd s s' d s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.mflr d :: is)) s Q :=
  WP.cons exec_mflr (k _ (Upd.write _ _ _))

theorem wp_mtlr {r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.lr = s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.mtlr r :: is)) s Q :=
  WP.cons exec_mtlr (k _ rfl rfl rfl rfl rfl rfl)

/-- Code without calls that writes neither the link register nor `r14` keeps them. -/
theorem wp_keep_lr {c : Prog isa} (h : WP isa c s Q) (hc : c.noCalls = true)
    (hl : (instrs c).all (fun i => !i.writesLr) = true)
    (h14 : (instrs c).all (fun i => dstOf i != some Reg.r14) = true) :
    WP isa c s fun t => Q t ∧ t.lr = s.lr ∧ t.gpr .r14 = s.gpr .r14 := by
  obtain ⟨tr, t, he, hq⟩ := h
  refine ⟨tr, t, he, hq, Exec.lr he hc hl, Exec.gpr (fun i hi => ?_) he (.inl hc)⟩
  have := List.all_eq_true.mp h14 i hi
  simpa using this

/-- The elements of `combInit`. -/
def cVal (q : Nat) : Fe :=
  if q = RX then identity.X else if q = RY then identity.Y
  else if q = RZ then identity.Z else Spec.Ed448.d

theorem combInit_ok (hc : Ctx b s) :
    WP isa (.block combInit) s fun t => Rest [.r7] s t ∧ Frame [FA b] s.mem t.mem ∧
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
  refine WP.append (constField_ok hc (o := RX) (by omega) (fe_lt _)) fun t1 ⟨r1, f1, v1⟩ => ?_
  have c1 := hc.of_rest r1 (by decide)
  refine WP.append (constField_ok c1 (o := RY) (by omega) (fe_lt _)) fun t2 ⟨r2, f2, v2⟩ => ?_
  have c2 := c1.of_rest r2 (by decide)
  refine WP.append (constField_ok c2 (o := RZ) (by omega) (fe_lt _)) fun t3 ⟨r3, f3, v3⟩ => ?_
  have c3 := c2.of_rest r3 (by decide)
  refine WP.mono (constField_ok c3 (o := DK) (by omega) (fe_lt _)) fun t4 ⟨r4, f4, v4⟩ =>
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

/-- A slot below `BITS` stays through writes past the field slots. -/
theorem fs_below_region {m m' : Mem} {e n : Nat} (hf : Frame [⟨b + BitVec.ofNat 64 e, n⟩] m m') {q : Nat}
    (hq : q + 56 ≤ e) (he : e + n ≤ 2 ^ 64) : FS m' b q = FS m b q := by
  have e' : ∀ k < 14, limb m' b q k = limb m b q k :=
    limb_frame hf fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) he
  rw [FS, V, val32_congr e']; rfl

/-- A doubleword at `o`, past the table, stays through a write of the field area, the
bits or the table. -/
theorem dw_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {o : Nat}
    (ho : 3840 ≤ o) (ho' : o + 8 ≤ 4096)
    (hrs : ∀ r ∈ rs, ∃ e n, r = ⟨b + BitVec.ofNat 64 e, n⟩ ∧ e + n ≤ 3840) :
    m'.readW (b + BitVec.ofNat 64 o) 64 = m.readW (b + BitVec.ofNat 64 o) 64 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  obtain ⟨e, n, rfl, hen⟩ := hrs r hr
  exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

/-- And through a write of the field area. -/
theorem dw_keep_fa {m m' : Mem} (hf : Frame [FA b] m m') {o : Nat} (ho : ACC + 112 ≤ o)
    (ho' : o + 8 ≤ 4096) :
    m'.readW (b + BitVec.ofNat 64 o) 64 = m.readW (b + BitVec.ofNat 64 o) 64 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [List.mem_singleton.mp hr]
  exact Offset.disjoint_base _ ho (by omega)

end

theorem scalarBase_correct (_hl : Proof.Ed448.BaseLadder2Ok) {s : State} (hp : basePPC.pre s) :
    WP isa scalarBase s fun s' => basePPC.post s s' ∧ s'.lr = s.lr ∧ s'.gpr .r14 = s.gpr .r14 := by
  obtain ⟨hrd, hwr, hos, how, hsw⟩ := hp
  have hB : BITS = 1064 := rfl
  have hA : ACC = 952 := rfl
  have hT : CTAB = 2048 := rfl
  have hL : LRS = 3840 := rfl
  have hO : R14S = 3848 := rfl
  obtain ⟨b, hb⟩ : ∃ b, s.gpr .r5 = b := ⟨_, rfl⟩
  have hws : Region.Disjoint ⟨s.gpr .r4, 57⟩ ⟨b, 4096⟩ := hb ▸ hsw.sub_right (Region.sub_prefix (by decide))
  have hwo : Region.Disjoint ⟨b, 4096⟩ ⟨s.gpr .r3, 57⟩ :=
    hb ▸ (how.sub_right (Region.sub_prefix (by decide))).symm
  unfold scalarBase
  simp only [combSave, List.cons_append, List.nil_append]
  refine WP.seq (wp_addiL (by decide) (by decide) fun s1 u1 l1 => wp_mflr fun s2 u2 => ?_)
  have hc1 : Ctx b s1 := ⟨by rw [u1.gpr, BitVec.add_zero, hb], ⟨8192, by decide, by rw [u1.wr, hwr, hb]; simp⟩⟩
  have hc2 : Ctx b s2 := hc1.of_rest (u2.rest (ws := [.r7]) (by decide)) (by decide)
  refine Comb.wp_std (by decide) ⟨by omega, by omega⟩ (by rw [hc2.r6]) (hc2.inW (by omega)) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc2.of_rest (u3.rest []) (by decide)
  refine Comb.wp_std (by decide) ⟨by omega, by omega⟩ (by rw [hc3.r6]) (hc3.inW (by omega)) fun s4a u4a =>
    wp_addi (by decide) (by decide) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := (hc3.of_rest (u4a.rest []) (by decide)).of_rest (u4.rest (ws := [.r14]) (by decide))
    (by decide)
  have hr4 : Rest [.r6, .r7, .r14] s s4 := (u1.rest (by decide)).trans ((u2.rest (by decide)).trans
    ((u3.rest _).trans ((u4a.rest _).trans (u4.rest (by decide)))))
  have h14 : s4.gpr .r14 = s.gpr .r3 := by
    rw [u4.gpr, u4a.gpr, u3.gpr, u2.other _ (by decide), u1.other _ (by decide), BitVec.add_zero]
  have hm4 : s4.mem = (s.mem.writeW (b + BitVec.ofNat 64 LRS) s.lr).writeW (b + BitVec.ofNat 64 R14S)
      (s.gpr .r14) := by
    rw [u4.mem, u4a.mem, u3.mem, u3.gpr, u2.gpr, u2.other Reg.r14 (by decide), u2.mem, u1.mem, l1,
      u1.other _ (by decide)]
  have lr4 : s4.mem.readW (b + BitVec.ofNat 64 LRS) 64 = s.lr := by
    rw [hm4, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  have out4 : s4.mem.readW (b + BitVec.ofNat 64 R14S) 64 = s.gpr .r14 := by
    rw [hm4, Mem.readW_writeW_self64]
  have hk4 : Spec.Ed448.bytesAt s4.mem (s.gpr .r4) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r4) 57 := by
    have fw : Frame [⟨b + BitVec.ofNat 64 LRS, 16⟩] s.mem s4.mem := by
      rw [hm4]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega) (by omega) (by omega))
    exact bytesAt_ws fw hws fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega)
  -- `R`, `d` and the table.
  refine WP.append (combInit_ok hc4) fun s5 ⟨hr5, hf5, hv5⟩ => ?_
  have hc5 : Ctx b s5 := hc4.of_rest hr5 (by decide)
  refine WP.mono (Comb.tabBuild_ok hc5) fun s6 ⟨hr6, hf6, htab6⟩ => ?_
  have hc6 : Ctx b s6 := hc5.of_rest hr6 (by decide)
  have hr6' : Rest [.r6, .r7, .r14] s s6 := hr4.trans ((hr5.mono (by decide)).trans (hr6.mono (by decide)))
  have h14' : s6.gpr .r14 = s.gpr .r3 := by rw [hr6.gpr _ (by decide), hr5.gpr _ (by decide), h14]
  have hk6 : Spec.Ed448.bytesAt s6.mem (s.gpr .r4) 57 = Spec.Ed448.bytesAt s.mem (s.gpr .r4) 57 := by
    rw [bytesAt_ws hf6 hws fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega),
      bytesAt_ws hf5 hws fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega), hk4]
  -- The scalar's bits.
  refine WP.seq (WP.mono (baseBits_ok hc6 (by rw [hr6'.gpr _ (by decide)])
    (by rw [hr6'.rd, hr6'.wr, hrd]; simp) hws) fun s7 ⟨hc7, hr7, hf7, hb7⟩ => ?_)
  rw [hk6] at hb7
  generalize hK : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 57) = K at hb7
  -- The elements of `R` and `d`, and the table, at the loop.
  have fs7 : ∀ q ∈ [RX, RY, RZ, DK], FS s7.mem b q = cVal q := fun q hq => by
    have hq' : q + 56 ≤ BITS ∧ q + 56 ≤ 4096 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> decide
    rw [fs_bits hf7 (.inl hq'.1) hq'.2, fs_below_region hf6 (e := CTAB) (by omega) (by omega), hv5 q hq]
  have tab7 : Comb.TabOk b s7.mem := fun i hi => by
    obtain ⟨e1, e2⟩ := htab6 i hi
    have keep : ∀ o, BITS + 456 ≤ o → o + 56 ≤ 4096 → V s7.mem b o = V s6.mem b o := fun o ho ho' => by
      unfold V
      refine val32_congr (limb_frame hf7 fun r hr k hk => ?_)
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    exact ⟨by rw [keep _ (by omega) (by omega), e1], by rw [keep _ (by omega) (by omega), e2]⟩
  have lr7 : s7.mem.readW (b + BitVec.ofNat 64 LRS) 64 = s.lr := by
    rw [dw_keep hf7 (by omega) (by omega) fun r hr => ⟨_, _, List.mem_singleton.mp hr, by omega⟩,
      dw_keep hf6 (by omega) (by omega) fun r hr => ⟨_, _, List.mem_singleton.mp hr, by omega⟩,
      dw_keep_fa hf5 (by omega) (by omega), lr4]
  have out7 : s7.mem.readW (b + BitVec.ofNat 64 R14S) 64 = s.gpr .r14 := by
    rw [dw_keep hf7 (by omega) (by omega) fun r hr => ⟨_, _, List.mem_singleton.mp hr, by omega⟩,
      dw_keep hf6 (by omega) (by omega) fun r hr => ⟨_, _, List.mem_singleton.mp hr, by omega⟩,
      dw_keep_fa hf5 (by omega) (by omega), out4]
  -- The loop.
  unfold combLoop
  refine WP.seq (WP.seq (wp_li (by decide) fun s8 u8 => WP.block_nil ?_))
  have hc8 : Ctx b s8 := hc7.of_rest (u8.rest (ws := [.r3]) (by decide)) (by decide)
  have m8 : s8.mem = s7.mem := u8.mem
  have fx : Comb.Fixed b K s8 := ⟨by rw [m8]; exact tab7, by rw [m8]; exact hb7⟩
  have L0 : Comb.LInv b K s8 114 s8 := by
    refine ⟨hc8, ⟨Rest.refl _ _, Frame.refl _ _⟩, by rw [u8.gpr], ?_, ?_⟩
    · rw [m8, fs7 DK (by decide)]; rfl
    · have e : Comb.ptOf (FS s8.mem b) = identity := by
        simp only [Comb.ptOf]
        rw [m8, fs7 RX (by decide), fs7 RY (by decide), fs7 RZ (by decide)]
        rfl
      rw [e, Proof.Ed448.Comb.accScalar_start, zero_smul]
      exact Proof.Ed448.identity_rep
  refine WP.mono (Comb.loop_ok fx 114 s8 (by decide) (Nat.le_refl _) L0) fun s9 h9 => ?_
  -- The return address and `out`, loaded back.
  have hc9 := h9.ctx
  have keep9 : ∀ o, 3840 ≤ o → o + 8 ≤ 4096 →
      s9.mem.readW (b + BitVec.ofNat 64 o) 64 = s7.mem.readW (b + BitVec.ofNat 64 o) 64 := fun o ho ho' => by
    rw [dw_keep_fa h9.stp.frame (by omega) ho', m8]
  have h14_9 : s9.gpr .r14 = s.gpr .r3 := by
    rw [h9.stp.rest.gpr _ (by decide), u8.other _ (by decide), hr7.gpr _ (by decide), h14']
  refine WP.seq (Comb.wp_ld (by decide) ⟨by omega, by omega⟩ (by rw [hc9.r6]) (hc9.inR (by omega))
    fun s10 u10 => wp_mtlr fun s11 g11 m11 rd11 wr11 sp11 l11 =>
    wp_addiL (by decide) (by decide) fun s11b u11b l11b =>
    wp_ldL (by decide) ⟨by omega, by omega⟩ (by rw [u11b.other _ (by decide), g11, u10.other _ (by decide), hc9.r6])
      (by rw [u11b.rd, u11b.wr, rd11, wr11, u10.rd, u10.wr]; exact hc9.inR (by omega)) fun s12 u12 l12 =>
    WP.block_nil ?_)
  have lr12 : s12.lr = s.lr := by
    rw [l12, l11b, l11, u10.gpr, keep9 _ (by omega) (by omega), lr7]
  have m12 : s12.mem = s9.mem := by rw [u12.mem, u11b.mem, m11, u10.mem]
  have e12 : s12.gpr .r3 = s.gpr .r3 := by
    rw [u12.other _ (by decide), u11b.gpr, g11, u10.other _ (by decide), h14_9, BitVec.add_zero]
  have r14_12 : s12.gpr .r14 = s.gpr .r14 := by
    rw [u12.gpr, u11b.mem, m11, u10.mem, keep9 _ (by omega) (by omega), out7]
  have hr12 : Rest [.r7, .r3, .r14] s9 s12 :=
    ⟨fun r hr => by
      rw [u12.other r (by intro h; exact hr (by simp [h])), u11b.other r (by intro h; exact hr (by simp [h])),
        g11, u10.other r (by intro h; exact hr (by simp [h]))],
      by rw [u12.rd, u11b.rd, rd11, u10.rd], by rw [u12.wr, u11b.wr, wr11, u10.wr],
      by rw [u12.sp, u11b.sp, sp11, u10.sp]⟩
  have hc12 : Ctx b s12 := hc9.of_rest hr12 (by decide)
  -- The encoding.
  have hS : SlotsOk s12.mem b RQ (ptV (Comb.ptOf (FS s9.mem b)) (Comb.ptOf (FS s9.mem b))) := by
    intro q hq
    rw [m12]
    simp only [RQ, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · rfl
    · exact h9.d
  refine WP.mono (wp_keep_lr (baseEncode_ok hc12 e12 (by
      rw [hr12.wr, h9.stp.rest.wr, u8.wr, hr7.wr, hr6'.wr, hwr]; simp) (hb ▸ hwo) hS)
    (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel))
    fun s13 ⟨h13, l13, r13⟩ => ⟨?_, by rw [l13, lr12], by rw [r13, r14_12]⟩
  show Spec.Ed448.bytesAt s13.mem (s.gpr .r3) 57 = _
  have hlen : (Spec.Ed448.bytesAt s.mem (s.gpr .r4) 57).length = 57 := by
    simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]
  have hk := Proof.Ed448.decodeLE_below hlen
  rw [hK] at hk
  unfold Proof.Ed448.Below456 at hk
  have r9 := h9.rep
  -- `Proof/Ed448/Comb.lean` states the bound with `Monoid.npow`: the same, without evaluating it.
  have lt_npow : ∀ {k a n : Nat},
      k < @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@instPowNat Nat instNatPowNat)) a n →
      k < @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) a n :=
    fun h => h
  have eK : Proof.Ed448.Comb.accScalar K 0 = K := Proof.Ed448.Comb.accScalar_total K (lt_npow hk)
  rw [eK] at r9
  rw [h13, Proof.Ed448.encodePoint_rep r9, Spec.Ed448.scalarBase, hK,
    Proof.Ed448.encodePoint_rep (Proof.Ed448.pointMul_rep K Proof.Ed448.basePoint_rep)]

end VG.Proof.Ed448.PPC64LE
