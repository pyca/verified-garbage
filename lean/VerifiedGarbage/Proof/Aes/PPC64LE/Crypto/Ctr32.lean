module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Loops
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.CtrSetup
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.CtrFinish
public import VerifiedGarbage.Proof.Aes.PPC64LE.Base
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: CTR's contract permits a final counter store after the shared data loops.
/-! # POWER8 AES CTR correctness

`ctrWith to` is CTR in place (`ctr32`, `to = false`) and from `r6` to `r8`
(`ctr32To`, `to = true`), with one proof (`ctrWith_ok`): the two differ
only in the setup (`setupWith_ok`, which leaves the stores' offset register
`ctrOff to` at `dst - src`) and in `r11` before the counter's final store. -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.Memory
open VG.Impl.Aes.PPC64LE.Crypto (counterBase counterMask counterControl mask byteMask ctrPre ctrPost ctrOff ctrFin
  ctrWith)

def ctrGprs : List Reg := [.r0, .r8, .r6, .r7, .r9, .r10, .r11, .r12]

/-- Where `ctrWith to` writes the blocks: at `r6` in place, at `r8` out of place. -/
def dstOf (to : Bool) (s : State) : Addr := if to then s.gpr .r8 else s.gpr .r6

/-- `r9 := r8 - r6`. -/
theorem sub_ok (s : State) : WP isa (.block [.sub .r9 .r8 .r6]) s fun t =>
    t.gpr .r9 = s.gpr .r8 - s.gpr .r6 ∧ Local [.r9] [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, reduceExec, runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  exact ⟨RegUpd.gpr_write_self .., Local.write s .r9 _⟩

/-- `r11 := r9`. -/
theorem mov11_ok (s : State) : WP isa (.block [Impl.Aes.PPC64LE.Crypto.mov .r11 .r9]) s fun t =>
    t.gpr .r11 = s.gpr .r9 ∧ Local [.r11] [] s t := by
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.mov, runBlock_cons, reduceExec, runStep_some, runBlock_nil,
    Option.some.injEq, exists_eq_left']
  exact ⟨by rw [RegUpd.gpr_write_self, BitVec.or_self], Local.write s .r11 _⟩

/-- After the setup of `ctrWith to`: `CtrSetup`, with the stores' offset
register at `dst - src`, and `r11` at 12 in place. -/
structure SetupWith (to : Bool) (s t : State) : Prop where
  effects : Local [.r0, .r8, .r9, .r11, .r12] [.v0, .v1, mask, counterMask, counterBase] s t
  zero : t.gpr .r0 = 0
  mask : t.vpr mask = byteMask
  control : t.vpr counterMask = counterControl
  baseValue : t.vpr counterBase = Spec.Gcm.blockAt s.mem (s.gpr .r5)
  word : (t.gpr .r8).setWidth 32 = (Spec.Gcm.blockAt s.mem (s.gpr .r5)).extractLsb' 0 32
  off : t.gpr (ctrOff to) = dstOf to s - s.gpr .r6
  r11 : to = false → t.gpr .r11 = 12

theorem setupWith_ok (to : Bool) (s : State) (hcr : (⟨s.gpr .r5, 16⟩ : Region) ∈ s.rd ++ s.wr) :
    WP isa (.block (ctrPre to ++ Impl.Aes.PPC64LE.Crypto.ctrSetup ++ ctrPost to)) s (SetupWith to s) := by
  cases to
  · simp only [ctrPre, ctrPost, Bool.false_eq_true, ite_false, List.nil_append, List.append_nil]
    refine WP.mono (ctr_setup_ok s hcr) fun t hb => ⟨hb.effects.weaken (by decide) (by decide), hb.zero,
      hb.mask, hb.control, hb.baseValue, hb.word, ?_, fun _ => hb.offset⟩
    simp only [ctrOff, dstOf, Bool.false_eq_true, ite_false, BitVec.sub_self]
    exact hb.zero
  · simp only [ctrPre, ctrPost, ite_true]
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (sub_ok s) fun s₁ ⟨h9, e₁⟩ => ?_
    have hcr₁ : (⟨s₁.gpr .r5, 16⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
      rw [e₁.keep.gpr (by decide), e₁.keep.2.1, e₁.keep.2.2]; exact hcr
    refine WP.mono (ctr_setup_ok s₁ hcr₁) fun b₁ hb => ?_
    refine WP.mono (mov11_ok b₁) fun t ⟨h11, e₂⟩ => ?_
    have h15 : s₁.gpr .r5 = s.gpr .r5 := e₁.keep.gpr (by decide)
    have hm₁ : s₁.mem = s.mem := e₁.mem
    refine ⟨((e₁.trans hb.effects).trans e₂).weaken (by decide) (by decide),
      (e₂.keep.gpr (by decide)).trans hb.zero, (e₂.v _ (by decide)).trans hb.mask,
      (e₂.v _ (by decide)).trans hb.control, ?_, ?_, ?_, fun h => nomatch h⟩
    · rw [e₂.v _ (by decide), hb.baseValue, h15, hm₁]
    · rw [e₂.keep.gpr (by decide), hb.word, h15, hm₁]
    · simp only [ctrOff, dstOf, ite_true]
      rw [h11, hb.effects.keep.gpr (by decide), h9]

/-- `ctrWith to`: the `n = r7` blocks at `D = r6` XORed with the keystream,
written to `dstOf to s`, which is `D` or apart from it, and the counter block
advanced by `n`. -/
theorem ctrWith_ok (to : Bool) (s : State) (hK : (⟨s.gpr .r3, 240⟩ : Region) ∈ s.rd ++ s.wr)
    (hC : (⟨s.gpr .r5, 16⟩ : Region) ∈ s.wr)
    (hw : (⟨dstOf to s, 16 * (s.gpr .r7).toNat⟩ : Region) ∈ s.wr)
    (hr : (⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : (⟨s.gpr .r3, 240⟩ : Region).Disjoint ⟨dstOf to s, 16 * (s.gpr .r7).toNat⟩)
    (hcd : (⟨s.gpr .r5, 16⟩ : Region).Disjoint ⟨dstOf to s, 16 * (s.gpr .r7).toNat⟩)
    (halias : dstOf to s = s.gpr .r6 ∨
      (⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩ : Region).Disjoint ⟨dstOf to s, 16 * (s.gpr .r7).toNat⟩)
    (hsize : 16 * (s.gpr .r7).toNat ≤ 2 ^ 64)
    (hnr : (s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14) :
    WP isa (ctrWith to) s fun t => Keep ctrGprs s t ∧
      Spec.Gcm.blocksAt t.mem (dstOf to s) (s.gpr .r7).toNat =
        Spec.Gcm.ctr32 (Spec.Gcm.aesWith (s.gpr .r4).toNat
          (Spec.Aes.bytesAt s.mem (s.gpr .r3) (16 * ((s.gpr .r4).toNat + 1))))
          (Spec.Gcm.blockAt s.mem (s.gpr .r5)) (Spec.Gcm.blocksAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) ∧
      Spec.Gcm.blockAt t.mem (s.gpr .r5) =
        Nat.repeat Spec.Gcm.inc32 (s.gpr .r7).toNat (Spec.Gcm.blockAt s.mem (s.gpr .r5)) := by
  let n := (s.gpr .r7).toNat
  let nr := (s.gpr .r4).toNat
  let D := s.gpr .r6
  let E := dstOf to s
  let C := s.gpr .r5
  let icb := Spec.Gcm.blockAt s.mem C
  have hnrlt : nr < 15 := by rcases hnr with h | h | h <;> omega
  have hnrmin : 1 < nr := by rcases hnr with h | h | h <;> omega
  rw [ctrWith]
  by_cases hz : s.gpr .r7 = 0
  · refine WP.ite true (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hz]; rfl)
      (fun _ => WP.block_nil ?_) (by simp)
    refine ⟨Keep.refl _ _, ?_⟩
    simp only [hz, show (0 : BitVec 64).toNat = 0 from rfl, Spec.Gcm.blocksAt, List.range_zero, List.map_nil,
      Spec.Gcm.ctr32, Spec.Gcm.keystream, List.length_nil, List.zipWith_nil_left, Nat.repeat, and_self]
  · refine WP.ite false (by simpa only [eval, State.read, Size.bits, BitVec.setWidth_eq,
        Option.some.injEq, beq_eq_false_iff_ne] using hz) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (setupWith_ok to s (List.mem_append_right _ hC)) fun base hb => ?_)
    have e := hb.effects
    have hc : LoopConfig false true (ctrOff to) base nr n D E := by
      refine ⟨⟨hb.zero, hb.mask, ?_, hnrmin, hnrlt, ?_⟩, hsize, ?_, ?_, fun _ => rfl, ?_, hb.off, ?_, halias⟩
      · rw [e.keep.gpr (by decide)]
        simp only [nr, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · intro j hj
        rw [e.keep.2.1, e.keep.2.2, e.keep.gpr (by decide)]
        exact ⟨_, hK, Offset.contains_base _ (d := 16*j) (n := 16) (k := 240) (by omega) (by omega)⟩
      · rw [e.keep.2.2]; exact hw
      · rw [e.keep.gpr (by decide)]; exact hsep
      · rw [e.keep.2.1, e.keep.2.2]; exact hr
      · cases to <;> decide
    have hi : LoopInv false true base nr n D E icb 0 base := by
      refine ⟨by omega, Keep.refl _ _, ?_, ?_, Processed.refl _ _ _ _, Frame.refl _ _, hb.mask,
        fun _ => hb.control, ?_, ?_⟩
      · rw [e.keep.gpr (by decide)]
        simp only [Nat.mul_zero, BitVec.add_zero]; rfl
      · rw [e.keep.gpr (by decide)]
        simp only [Nat.sub_zero, n, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · intro _; rw [hb.baseValue]
      · intro _; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hb.word
    refine WP.seq (WP.mono (batches_ok hc hi) fun u hu => ?_)
    have hC5 : u.gpr .r5 = C := (hu.keep.gpr (by decide)).trans (e.keep.gpr (by decide))
    -- `r11` back to 12, then the counter's last word
    have hfin : WP isa (.block (ctrFin to)) u fun v => v.gpr .r11 = 12 ∧ Local [.r11] [] u v := by
      cases to
      · simp only [ctrFin, Bool.false_eq_true, ite_false]
        exact WP.block_nil ⟨(hu.keep.gpr (by decide)).trans (hb.r11 rfl), Local.refl _ _ _⟩
      · simp only [ctrFin, ite_true]
        apply WP.of_runBlock
        rw [runBlock_cons, show exec (.li .r11 12) u = some (u.write .r11 12) from rfl, runStep_some,
          runBlock_nil]
        simp only [Option.some.injEq, exists_eq_left']
        exact ⟨RegUpd.gpr_write_self .., Local.write u .r11 _⟩
    rw [WP.block_append_iff]
    refine WP.mono hfin fun v ⟨h11, ev⟩ => ?_
    have hCv : v.gpr .r5 = C := (ev.keep.gpr (by decide)).trans hC5
    have hwv : InRegions v.wr (v.gpr .r5 + v.gpr .r11) 4 := by
      rw [ev.keep.2.2, hu.keep.2.2, e.keep.2.2, hCv, h11]
      exact ⟨⟨C, 16⟩, hC, Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide)⟩
    have hstore : WP isa (.block [.storeRev .w .r8 .r5 .r11]) v
        (· = {v with mem := v.mem.writeW (C + 12) (rev32 ((v.gpr .r8).setWidth 32))}) := by
      apply WP.of_runBlock
      rw [runBlock_cons, exec_storeRev_w (by decide) hwv, runStep_some, runBlock_nil, hCv, h11]
      simp only [Option.some.injEq, exists_eq_left']
    refine WP.mono hstore fun t ht => ?_
    subst t
    have hvm : v.mem = u.mem := ev.mem
    have hv8 : v.gpr .r8 = u.gpr .r8 := ev.keep.gpr (by decide)
    have hf : Frame [⟨C, 16⟩] u.mem (u.mem.writeW (C+12) (rev32 ((u.gpr .r8).setWidth 32))) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (d := 12) (n := 4) (k := 16) (by decide) (by decide))
    have hp := hu.processed.frame hf (by simpa only [List.mem_singleton, forall_eq] using hcd.symm) hsize
    have hbm : base.mem = s.mem := e.mem
    have hsched : schedule nr base = schedule nr s := by
      rw [schedule, hbm, e.keep.gpr (by decide)]
    rw [hsched, hbm] at hp
    refine ⟨((e.keep.trans hu.keep).trans ev.keep).mono (by simp [ctrGprs, loopGprs]), ?_, ?_⟩
    · show Spec.Gcm.blocksAt (v.mem.writeW (C + 12) (rev32 ((v.gpr .r8).setWidth 32))) E n = _
      rw [hvm, hv8]
      exact ctr_processed hp
    · have hframe := hu.frame
      rw [hbm] at hframe
      show Spec.Gcm.blockAt (v.mem.writeW (C + 12) (rev32 ((v.gpr .r8).setWidth 32))) C = _
      rw [hvm, hv8]
      apply counter_after (word := (u.gpr .r8).setWidth 32) (hu.counter rfl)
      intro i hi
      change (u.mem.write (C+12) 4 (rev32 ((u.gpr .r8).setWidth 32))) (C + BitVec.ofNat 64 i) = _
      rw [Mem.write, show (12 : BitVec 64) = BitVec.ofNat 64 12 from rfl,
        Offset.sub_toNat' C (by omega) (by omega)]
      by_cases hil : i < 12
      · rw [ite_eq_right (show ¬12 ≤ i by omega), ite_eq_right (show ¬2^64+i-12 < 4 by omega), ite_eq_left hil]
        exact hframe.bytes (R := ⟨C, 16⟩) (by simpa only [List.mem_singleton, forall_eq] using hcd)
          (by change 16 ≤ 2^64; decide) hi
      · rw [ite_eq_left (show 12 ≤ i by omega), ite_eq_left (show i-12 < 4 by omega), ite_eq_right hil]

theorem ctr32_ok (s : State) (hs : Proof.Aes.ctr32PPC64LE.pre s) :
    WP isa Impl.Aes.PPC64LE.Crypto.ctr32 s fun t => Keep ctrGprs s t ∧ Proof.Aes.ctr32PPC64LE.post s t := by
  obtain ⟨hrd, hwr, _, hsep, _, hcd, _, _, hbound, hnr⟩ := hs
  exact ctrWith_ok false s (by rw [hrd]; simp) (by rw [hwr]; simp) (by rw [hwr]; simp [dstOf])
    (by rw [hrd, hwr]; simp) hsep hcd (.inl rfl) (by omega) hnr

theorem ctr32To_ok (s : State) (hs : Proof.Aes.ctr32ToPPC64LE.pre s) :
    WP isa Impl.Aes.PPC64LE.Crypto.ctr32To s fun t => Keep ctrGprs s t ∧ Proof.Aes.ctr32ToPPC64LE.post s t := by
  obtain ⟨hrd, hwr, hsep, hcd, hsd, _, hbE, hnr⟩ := hs
  exact ctrWith_ok true s (by rw [hrd]; simp) (by rw [hwr]; simp) (by rw [hwr]; simp [dstOf])
    (by rw [hrd]; simp) hsep hcd (.inr hsd) (by omega) hnr

end VG.Proof.Aes.PPC64LE.Crypto
