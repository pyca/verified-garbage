module

import VerifiedGarbage.Proof.X448.PPC64LE.Bits
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.X448.PPC64LE.Setup
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.PPC64LE.Mul
import VerifiedGarbage.Proof.X448.PPC64LE.Freeze
import VerifiedGarbage.Proof.X448.PPC64LE.Invert
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Spill

/-!
# X448 on PPC64LE: the whole function

`vg_x448` writes `X448(k, u)` to `out`, and restores `r15`–`r31`, which it
saves at `NV` for `mul` (`x448_correct`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)
open VG.Proof.X448 (toFe ladderAfter ladderAfter_swap_le)
open VG.PPC64LE.Spill (saveMem Saved saveMem_saved saveMem_frame_base)

/-- `vg_x448(out = r3, scalar = r4, point = r5, scratch = r6)`. -/
def x448PPC64LE : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 56⟩
    let sc : Region := ⟨s.gpr .r4, 56⟩
    let pt : Region := ⟨s.gpr .r5, 56⟩
    let ws : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [sc, pt] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint pt ∧ out.Disjoint ws ∧
      sc.Disjoint ws ∧ pt.Disjoint ws
  post s s' := bytesAt s'.mem (s.gpr .r3) 56 =
    VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .r4) 56) (bytesAt s.mem (s.gpr .r5) 56)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- `vg_x448_base(out = r3, scalar = r4, scratch = r5)`. -/
def x448BasePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 56⟩
    let sc : Region := ⟨s.gpr .r4, 56⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := bytesAt s'.mem (s.gpr .r3) 56 =
    VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .r4) 56) VG.Spec.X448.basePoint
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem XPre.of {s : State} (h : x448PPC64LE.pre s) : XPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

section
variable {b : Addr}

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h0 : s.gpr .r0 = BitVec.ofNat 64 sw) {v : Nat → Fe} (hS : SlotsOk s.mem b LQ v) :
    WP isa (.block lastSwap) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  simp only [lastSwap, mask, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_sub fun s2 u2 => ?_
  have hr2 : Rest [.r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  have e11 : s2.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), h0]; rfl
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (cswapS (v := v) (qs := LQ) (by decide) (by decide) (by decide) (by decide) (by decide) hc2
    hsw e11 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  have hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (cswapS (by decide) (by decide) (by decide) (by decide) (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e11]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

/-- The slots stay through a write above `BITS`. -/
theorem SlotsOk.above {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m b qs v)
    (hq : (qs.all fun q => q + 56 ≤ BITS) = true) {d n : Nat} (hd : BITS ≤ d) (hdn : d + n ≤ 4096)
    (hf : Frame [⟨b + BitVec.ofNat 64 d, n⟩] m m') : SlotsOk m' b qs v := by
  intro q hq'
  have h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hB : BITS = 1064 := rfl
  have e := limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hd, h, hk])) (by omega_using [h, hB, hk]) (by omega_using [hdn])
  rw [FS, V, val32_congr e]; exact hS q hq'

/-- The slots stay through a write of `BITS`. -/
theorem SlotsOk.bits {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m b qs v)
    (hq : (qs.all fun q => q + 56 ≤ BITS) = true)
    (hf : Frame [⟨b + BitVec.ofNat 64 BITS, 448⟩] m m') : SlotsOk m' b qs v := by
  intro q hq'
  have h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hB : BITS = 1064 := rfl
  have e := limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [h, hk])) (by omega_using [h, hB, hk]) (by omega_using [hB])
  rw [FS, V, val32_congr e]; exact hS q hq'

end

theorem bytesAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 56⟩ r) : bytesAt m' p 56 = bytesAt m p 56 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc

/-- The code after the setup, from the ladder's initial state for the
u-coordinate `pb` in the working space at `r6` of `s`: it saves `r15`–`r31`
at `NV`, and restores them before the final reduction. -/
theorem afterSetup_correct {s s1 : State} {pb : List Byte}
    (hsc_in : (⟨s.gpr .r4, 56⟩ : Region) ∈ s.rd ++ s.wr) (hout : (⟨s.gpr .r3, 56⟩ : Region) ∈ s.wr)
    (sc_ws : Region.Disjoint ⟨s.gpr .r4, 56⟩ ⟨s.gpr .r6, 8192⟩)
    (out_ws : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r6, 8192⟩)
    (hc1 : Ctx (s.gpr .r6) s1) (hf1 : Frame [⟨s.gpr .r6, 8192⟩] s.mem s1.mem)
    (hS1 : SlotsOk s1.mem (s.gpr .r6) LQ (ladV (toFe (VG.Spec.X448.decodeUCoordinate pb))
      (VG.Proof.X448.init (toFe (VG.Spec.X448.decodeUCoordinate pb)))))
    (hr1 : Rest [.r5, .r7, .r8] s s1) :
    WP isa afterSetup s1 fun s' =>
      bytesAt s'.mem (s.gpr .r3) 56 = VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .r4) 56) pb ∧
      ∀ i < 17, s'.gpr (nvR i) = s1.gpr (nvR i) := by
  have hB : BITS = 1064 := rfl
  have hNV : NV = 1512 := rfl
  have hA := ACC_eq
  unfold afterSetup
  -- `r14`–`r31` saved at `NV`.
  rw [← List.append_nil (stdsAt NV (slotsOf nvR 17))]
  refine WP.seq (stdsAt_ok (l := slotsOf nvR 17) (by decide) (slotsOf_fit (by decide) (by decide)) hc1
    fun s1' g1' rd1' wr1' sp1' mem1' => WP.block_nil ?_)
  have hc1' : Ctx (s.gpr .r6) s1' := ⟨by rw [g1']; exact hc1.r6, by rw [wr1']; exact hc1.wr⟩
  have hfNV : Frame [⟨s.gpr .r6 + BitVec.ofNat 64 NV, 136⟩] s1.mem s1'.mem := by
    rw [mem1']; exact saveMem_frame_base (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega)
      (by decide) _ _ _
  have hsv1 : Saved (s.gpr .r6 + BitVec.ofNat 64 NV) s1.gpr (slotsOf nvR 17) s1'.mem := by
    rw [mem1']; exact saveMem_saved (by decide) _ _ _
  have hS1' := hS1.above (by decide) (by rw [hB]; decide) (by omega_using [hNV]) hfNV
  have hf1' : Frame [⟨s.gpr .r6, 8192⟩] s.mem s1'.mem := hf1.trans (hfNV.sub fun r hr =>
    ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [hNV])⟩)
  have hr1' : Rest [.r5, .r7, .r8] s s1' := ⟨fun r hr => by rw [congrFun g1']; exact hr1.gpr r hr,
    by rw [rd1', hr1.rd], by rw [wr1', hr1.wr], by rw [sp1', hr1.sp]⟩
  refine WP.seq (WP.mono (bits_ok hc1' (hr1'.gpr .r4 (by decide)) (by rw [hr1'.rd, hr1'.wr]; exact hsc_in)
    (disj4096 sc_ws)) fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  have hS2 := hS1'.bits (by decide) hf2
  refine WP.seq (WP.mono (ladder_ok hc2 hb2 hS2) fun s3 ⟨hst3, hc3, h0, hS3⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc3 (ladderAfter_swap_le _ _ (by decide)) h0 hS3)
    fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok hc4 (hS4.mono (by decide)) rfl) fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (mulS (o := X2) (x := X2) (y := R) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc5 hS5) fun s6 ⟨hr6, hf6, hS6⟩ => ?_)
  -- The registers and regions along the way.
  have hst6 : StpW work (s.gpr .r6) s2 s6 :=
    hst3.trans ((hst4.mono (by decide)).trans (hst5.trans ⟨hr6.mono (by decide), hf6⟩))
  have hc6 : Ctx (s.gpr .r6) s6 := hc5.of_rest hr6 (by decide)
  -- `r14`–`r31` restored.
  have hsv6 : Saved (s.gpr .r6 + BitVec.ofNat 64 NV) s1.gpr (slotsOf nvR 17) s6.mem := by
    have h2 := hsv1.frame_in (lo := 0) (n := 136) (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega)
      hf2 (fun r hr => by
        rw [List.mem_singleton.mp hr]; simpa using Offset.disjoint (s.gpr .r6) (d := NV) (n := 136)
          (e := BITS) (k := 448) (.inr (by omega_using [hB, hNV])) (by omega_using [hNV]) (by omega_using [hB]))
    exact h2.frame_in (lo := 0) (n := 136) (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega)
      hst6.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; simpa using Offset.disjoint_base (s.gpr .r6) (d := NV) (n := 136)
          (k := ACC + 112) (by omega_using [hNV, hA]) (by omega_using [hNV]))
  refine ldsAt_ok (l := slotsOf nvR 17) (by decide) (slotsOf_fit (by decide) (by decide)) (by decide)
    (by decide) hc6 fun s7 hc7 r7 m7 _ v7 => ?_
  have nv7 : ∀ i < 17, s7.gpr (nvR i) = s1.gpr (nvR i) := fun i hi => by
    rw [v7 (nvR i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)]
    exact hsv6 (nvR i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have h3' : s7.gpr .r3 = s.gpr .r3 := by
    rw [r7.gpr _ (by decide), hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide), hr1'.gpr _ (by decide)]
  have hwr7 : s7.wr = s.wr := by rw [r7.wr, hst6.rest.wr, hr2.wr, hr1'.wr]
  refine WP.mono (freeze_ok hc7 h3'
    (fun k hk => in_base (len := 56) (by rw [hwr7]; exact hout) (by omega_using [hk]) (by omega_using [hk])) (disj4096 out_ws).symm)
    fun s8 ⟨hbytes, hr8, _⟩ => ⟨?_, fun i hi => by
      rw [hr8.gpr _ (by revert i; decide), nv7 i hi]⟩
  -- The result.
  rw [hbytes, m7, VG.Proof.X448.x448_eq]
  -- The scalar, as read by `bits`.
  have hk : bytesAt s1'.mem (s.gpr .r4) 56 = bytesAt s.mem (s.gpr .r4) 56 :=
    bytesAt_frame hf1' fun r hr => by rw [List.mem_singleton.mp hr]; exact sc_ws
  rw [hk] at hS3 h0 hS4 hS5 hS6
  have e6 : FS s6.mem (s.gpr .r6) X2 = _ := hS6 X2 (by decide)
  rw [← VG.Proof.X448.toFe_val, ← VG.Proof.X448.encodeUCoordinate_eq]
  change VG.Spec.X448.encodeUCoordinate (FS s6.mem (s.gpr .r6) X2) = _
  rw [e6]
  simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X448.invert_eq, VG.Proof.X448.pow_pw, cswap_fst,
    X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

theorem x448_correct {s : State} (hp : XPre s) :
    WP isa x448 s fun s' => x448PPC64LE.post s s' ∧ ∀ i < 17, s'.gpr (nvR i) = s.gpr (nvR i) := by
  unfold x448
  exact WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, hf1, hS1, hr1⟩ =>
    WP.mono (afterSetup_correct (by rw [hp.rd]; simp) (by rw [hp.wr]; simp) hp.sc_ws hp.out_ws hc1 hf1 hS1 hr1)
      fun s' ⟨h1, h2⟩ => ⟨h1, fun i hi => by rw [h2 i hi, hr1.gpr _ (by revert i; decide)]⟩)

/-- `vg_x448_base`'s precondition, by field. -/
structure BPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 56⟩]
  wr : s.wr = [⟨s.gpr .r3, 56⟩, ⟨s.gpr .r5, 8192⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r4, 56⟩
  out_ws : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r5, 8192⟩
  sc_ws : Region.Disjoint ⟨s.gpr .r4, 56⟩ ⟨s.gpr .r5, 8192⟩

theorem BPre.of {s : State} (h : x448BasePPC64LE.pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem x448Base_correct {s : State} (hp : BPre s) :
    WP isa x448Base s fun s' => x448BasePPC64LE.post s s' ∧ ∀ i < 17, s'.gpr (nvR i) = s.gpr (nvR i) := by
  unfold x448Base
  refine WP.seq ?_
  rw [List.singleton_append]
  refine wp_addi (imm := 0) (by decide) (by decide) fun s0 u0 => ?_
  have e0 : s0.gpr .r6 = s.gpr .r5 := by rw [u0.gpr]; exact BitVec.add_zero _
  have a3 : s0.gpr .r3 = s.gpr .r3 := u0.other _ (by decide)
  have a4 : s0.gpr .r4 = s.gpr .r4 := u0.other _ (by decide)
  refine WP.mono (setupBase_ok (by rw [e0, u0.wr, hp.wr]; simp)) fun s1 ⟨hc1, hf1, hS1, hr1⟩ => ?_
  refine WP.mono (afterSetup_correct (s := s0) (by rw [a4, u0.rd, hp.rd]; simp) (by rw [a3, u0.wr, hp.wr]; simp)
    (by rw [a4, e0]; exact hp.sc_ws) (by rw [a3, e0]; exact hp.out_ws) hc1 hf1 hS1 hr1) fun s' ⟨h, hnv⟩ =>
      ⟨?_, fun i hi => by rw [hnv i hi, hr1.gpr _ (by revert i; decide), u0.other _ (by revert i; decide)]⟩
  show bytesAt s'.mem (s.gpr .r3) 56 = _
  rw [← a3, h, a4, u0.mem]

end VG.Proof.X448.PPC64LE
