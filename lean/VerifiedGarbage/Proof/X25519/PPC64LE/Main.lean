module

import VerifiedGarbage.Proof.X25519.PPC64LE.Bits
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.X25519.PPC64LE.Setup
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
import VerifiedGarbage.Proof.X25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.X25519.PPC64LE.Invert
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill

/-!
# X25519 on PPC64LE: the whole function

`vg_x25519` writes `X25519(k, u)` to `out` (`x25519_correct`).
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes toFe ladderAfter ladderAfter_swap_le)

/-- `vg_x25519(out = r3, scalar = r4, point = r5, scratch = r6)`. -/
def x25519PPC64LE : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 32⟩
    let sc : Region := ⟨s.gpr .r4, 32⟩
    let pt : Region := ⟨s.gpr .r5, 32⟩
    let ws : Region := ⟨s.gpr .r6, 4096⟩
    s.rd = [sc, pt] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint pt ∧ out.Disjoint ws ∧
      sc.Disjoint ws ∧ pt.Disjoint ws
  post s s' := bytesAt s'.mem (s.gpr .r3) 32 =
    VG.Spec.X25519.x25519 (bytesAt s.mem (s.gpr .r4) 32) (bytesAt s.mem (s.gpr .r5) 32)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

theorem XPre.of {s : State} (h : x25519PPC64LE.pre s) : XPre s := by
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

/-- The slots stay through a write above them, `[lo, lo + n)`. -/
theorem SlotsOk.above {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m b qs v) {lo n : Nat}
    (hq : (qs.all fun q => q + 32 ≤ lo) = true) (hn : lo + n ≤ 4096)
    (hf : Frame [⟨b + BitVec.ofNat 64 lo, n⟩] m m') : SlotsOk m' b qs v := by
  intro q hq'
  have h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have e := limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  rw [FS, V, val32_congr e]; exact hS q hq'

/-- The bits stay through a write of the saved registers. -/
theorem Bits.save {m m' : Mem} {k : Nat} (h : Bits b k m)
    (hf : Frame [⟨b + BitVec.ofNat 64 SAVE, 136⟩] m m') : Bits b k m' := fun t ht => by
  have hB : BITS = 608 := rfl
  have hS : SAVE = 896 := rfl
  rw [hf _ fun r hr hc => (Offset.disjoint b (d := BITS + t) (n := 1) (e := SAVE) (k := 136)
    (.inl (by omega)) (by omega) (by omega)) _ (Region.contains_self _ _)
    (by rw [List.mem_singleton.mp hr] at hc; exact hc)]
  exact h t ht

end

/-! ## The registers `x25519` saves -/

/-- The nonvolatile registers the multiplication uses, and their slots. -/
def nvL : List (Reg × Nat) := (List.range 17).map fun k => (nvR k, SAVE + 8 * k)

theorem saveNV_eq : saveNV = Spill.saveCode .r6 nvL := rfl

theorem restoreNV_eq : restoreNV = Spill.restoreCode .r6 nvL := rfl

theorem nvL_ok : ∀ p ∈ nvL, p.2 % 8 = 0 ∧ p.2 < 32768 := by decide

theorem nvL_in : ∀ p ∈ nvL, SAVE ≤ p.2 ∧ p.2 + 8 ≤ SAVE + 136 := by decide

theorem nvL_fits : Spill.Fits nvL := by decide

theorem nvL_restorable : Spill.Restorable .r6 nvL := by decide

theorem nvL_regs : ∀ p ∈ nvL, p.1 ∉ clob ∧ p.1 ∉ [Reg.r4, .r7, .r8, .r9, .r11] ∧ p.1 ∉ [Reg.r5, .r7, .r8] ∧
    p.1 ≠ .r3 ∧ p.1 ≠ .r6 := by decide

theorem nvL_le {p : Reg × Nat} (hp : p ∈ nvL) : p.2 + 8 ≤ 4096 := by
  have := nvL_in p hp; have hS : SAVE = 896 := rfl; omega

theorem bytesAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 32⟩ r) : bytesAt m' p 32 = bytesAt m p 32 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega) (by omega)) hc

theorem x25519_correct {s : State} (hp : XPre s) :
    WP isa x25519 s fun s' => x25519PPC64LE.post s s' ∧ ∀ p ∈ nvL, s'.gpr p.1 = s.gpr p.1 := by
  have hB : BITS = 608 := rfl
  have hSV : SAVE = 896 := rfl
  have hA : ACC = 544 := rfl
  have hsc_in : (⟨s.gpr .r4, 32⟩ : Region) ∈ s.rd ++ s.wr := by rw [hp.rd]; simp
  unfold x25519
  rw [saveNV_eq, restoreNV_eq]
  refine WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, hf1, hS1, hr1⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok hc1 (hr1.gpr .r4 (by decide)) (by rw [hr1.rd, hr1.wr]; exact hsc_in)
    hp.sc_ws) fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  have hS2 := hS1.above (lo := BITS) (by decide) (by decide) hf2
  -- The saves.
  refine WP.seq (WP.mono (Spill.save_wp (l := nvL) (by decide) nvL_ok
    (fun p hp => by rw [hc2.r6]; exact hc2.inW (nvL_le hp))) fun s3 hst => ?_)
  have hc3 : Ctx (s.gpr .r6) s3 := ⟨by rw [hst.gpr]; exact hc2.r6, by rw [hst.wr]; exact hc2.wr⟩
  have hfs : Frame [⟨s.gpr .r6 + BitVec.ofNat 64 SAVE, 136⟩] s2.mem s3.mem := by
    rw [hst.mem, hc2.r6]; exact Spill.saveMem_frame nvL_in (by decide) _ _ _
  have hsv : Spill.Saved (s.gpr .r6) s2.gpr nvL s3.mem := by
    rw [hst.mem, hc2.r6]; exact Spill.saveMem_saved nvL_fits _ _ _
  have hS3 := hS2.above (lo := SAVE) (by decide) (by decide) hfs
  refine WP.seq (WP.mono (ladder_ok hc3 (hb2.save hfs) hS3) fun s4 ⟨hst4, hc4, h0, hS4⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc4 (ladderAfter_swap_le _ _ (by decide)) h0 hS4)
    fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok hc5 (hS5.mono (by decide)) rfl) fun s6 ⟨hst6, hc6, hS6⟩ => ?_)
  refine WP.seq (WP.mono (mulS (o := X2) (x := X2) (y := R) (by decide) (by decide) (by decide) (by decide)
    (by decide) hc6 hS6) fun s7 ⟨hr7, hf7, hS7⟩ => ?_)
  -- The registers and regions along the way.
  have hst7 : Stp (s.gpr .r6) s3 s7 := hst4.trans (hst5.trans (hst6.trans ⟨hr7.mono (by decide), hf7⟩))
  have h3' : s7.gpr .r3 = s.gpr .r3 := by
    rw [hst7.rest.gpr _ (by decide), hst.gpr, hr2.gpr _ (by decide), hr1.gpr _ (by decide)]
  have hwr7 : s7.wr = s.wr := by rw [hst7.rest.wr, hst.wr, hr2.wr, hr1.wr]
  have hc7 : Ctx (s.gpr .r6) s7 := hc6.of_rest hr7 (by decide)
  have hsv7 : Spill.Saved (s.gpr .r6) s2.gpr nvL s7.mem :=
    hsv.frame_in nvL_in hst7.frame fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by omega) (by omega)
  -- The restores.
  refine Spill.restore_ok (by decide) hc7.r6 nvL_ok nvL_restorable (fun p hp => hc7.inR (nvL_le hp)) hsv7
    fun s8 hR => ?_
  have hc8 : Ctx (s.gpr .r6) s8 := ⟨by rw [hR.other _ (by decide)]; exact hc7.r6, by rw [hR.wr]; exact hc7.wr⟩
  have h3'' : s8.gpr .r3 = s.gpr .r3 := by rw [hR.other _ (by decide), h3']
  refine WP.mono (freeze_ok hc8 h3'' (by rw [hR.wr, hwr7, hp.wr]; simp) hp.out_ws.symm)
    fun s9 ⟨hbytes, hr9, _⟩ => ⟨?_, fun p hp => ?_⟩
  -- The result.
  · show bytesAt s9.mem _ 32 = _
    rw [hbytes, hR.mem, VG.Proof.X25519.x25519_eq]
    -- The scalar, as read by `bits`.
    have hk : bytesAt s1.mem (s.gpr .r4) 32 = bytesAt s.mem (s.gpr .r4) 32 :=
      bytesAt_frame hf1 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.sc_ws
    rw [hk] at hS4 h0 hS5 hS6 hS7
    have e7 : FS s7.mem (s.gpr .r6) X2 = _ := hS7 X2 (by decide)
    rw [← VG.Proof.X25519.toFe_val, ← VG.Proof.X25519.encodeUCoordinate_eq]
    change VG.Spec.X25519.encodeUCoordinate (FS s7.mem (s.gpr .r6) X2) = _
    rw [e7]
    simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X25519.invert_eq, VG.Proof.X25519.pow_pw, cswap_fst,
      uOf, X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]
  -- The saved registers.
  · obtain ⟨n1, n2, n3, -, -⟩ := nvL_regs p hp
    rw [hr9.gpr _ n1, hR.gpr p hp, hr2.gpr _ n2, hr1.gpr _ n3]

end VG.Proof.X25519.PPC64LE
