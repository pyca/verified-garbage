import VerifiedGarbage.Proof.Ed448.AArch64.BaseBits
import VerifiedGarbage.Proof.X448.AArch64.Base.Setup

/-!
# Ed448 base-point multiplication on AArch64: the setup

Untrusted: everything here is checked by Lean. X448's comb's `entry` (the
registers saved, every slot zeroed), the bits of all 57 bytes of the scalar
(`bits_ok`), and both accumulators at `[G] B` for `G = 8 Σ_{j < 57} 256^j`
(`baseG57`): `StepInv` of the comb of 57 tables, for step 0.
-/

namespace VG.Proof.Ed448.AArch64.Base

open VG VG.AArch64 VG.Impl.X448.AArch64 VG.Impl.X448.AArch64.Base
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Outside2 Saved bitRegs ofs)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast
open VG.Proof.X448.AArch64.Base (StepInv pt block1_ok consts_ok bnd_of_words F_of_words)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.Ed448 (Rep baseAff)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- What the setup leaves, from the function's entry state `sE`. -/
structure CombReady (sE : State) (base : Addr) (k : Nat) (t : State) : Prop where
  inv : StepInv 57 t base k 0 t
  saved : Saved base sE.gpr t.mem
  out : t.gpr .x20 = sE.gpr .x0
  savedX : SavedX base sE.gpr t.mem
  savedV : SavedV base sE.v t.mem
  lr : t.gpr .x30 = sE.gpr .x30
  rd : t.rd = sE.rd
  wr : t.wr = sE.wr
  mem : Outside base 0 8192 sE.mem t.mem

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    bytesAt m' p 57 = bytesAt m p 57 := by
  rw [VG.Proof.Ed448.bytesAt_eq, VG.Proof.Ed448.bytesAt_eq]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem setup_ok {s : State} {base kp : Addr} (hb : s.gpr .x2 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) (hk : s.gpr .x1 = kp)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (kp + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (kp + BitVec.ofNat 64 q))
    (htb : VG.Proof.X448.AArch64.Base.TblAt s base (s.syms VG.Impl.X448.AArch64.Base.combSym)) :
    WP isa VG.Impl.Ed448.AArch64.baseSetup s (CombReady s base (decodeLE (bytesAt s.mem kp 57))) := by
  unfold VG.Impl.Ed448.AArch64.baseSetup
  refine WP.seq (WP.mono_syms (block1_ok hb hw hn) fun a ⟨ha, sa, oa, xa, va, ka, za, outa⟩ sya => ?_)
  refine WP.seq (WP.mono_syms (VG.Proof.Ed448.AArch64.bits_ok ha (by rw [ka.1 _ (by decide)]; exact hk)
    (by rw [ka.2.1, ka.2.2]; exact hkr) hkd) fun b ⟨_, gb, rdb, wrb, ob, bitsb⟩ syb => ?_)
  have kb : Keeps (.x1 :: bitRegs) a b := ⟨gb, rdb, wrb⟩
  have hsb : Scr b base := ha.of_keeps kb (by decide)
  rw [bytesAt_outside outa hkd] at bitsb
  refine WP.mono_syms (consts_ok hsb _) fun t ⟨tv, tOut, kt, tc⟩ syt => ?_
  have hst : Scr t base := hsb.of_keeps kt (by decide)
  have mt : Outside base 0 8192 s.mem t.mem :=
    (outa.trans (ob.mono (by omega) (by simp only [BITS]; omega))).trans (tOut.mono (by omega) (by omega))
  have htt : VG.Proof.X448.AArch64.Base.TblAt t base (t.syms VG.Impl.X448.AArch64.Base.combSym) := by
    rw [syt, syb, sya]
    exact htb.of_far (by rw [kt.2.1, kb.2.1, ka.2.1, kt.2.2, kb.2.2, ka.2.2]) fun x hx => mt x (Or.inr hx)
  -- Every word outside the constant slots and the bits is as `block1` left it.
  have wt : ∀ {d : Nat}, d + 8 ≤ 64 ∨ 832 ≤ d → d + 8 ≤ BITS ∨ BITS + 456 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := fun h1 h2 h3 => by
    rw [tOut.word (by omega) h3, ob.word h2 h3]
  -- The slots `block1` zeroed.
  have zs : ∀ i : Index, ∀ w < 8, word a.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := za (16 * i.val + w) (by omega)
    have e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega
    rw [show VG.Proof.X448.AArch64.limbs a.mem base (slot 0) (16 * i.val + w) =
      (word a.mem base (slot i.val + 8 * w)).toNat by
        simp only [VG.Proof.X448.AArch64.limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  have zt : ∀ i : Index, 6 ≤ i.val → ∀ w < 8, word t.mem base (slot i.val + 8 * w) = 0 := fun i hi w hw => by
    have := i.isLt
    rw [wt (by simp only [slot]; omega) (by simp only [slot, BITS]; omega) (by simp only [slot]; omega)]
    exact zs i w hw
  have ev : ∀ (i : Index) (v : Spec.X448.Fe), (∀ w < 8, word t.mem base (slot i.val + 8 * w) = limb v w) →
      VG.Proof.X448.AArch64.Weak.E t.mem base i = v := fun i v h => F_of_words h
  have pA : pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 0 1 2 = VG.Proof.X448.basePt Impl.X448.baseG57 := by
    simp only [pt, VG.Proof.X448.basePt]
    rw [ev 0 _ fun w hw => (tv w hw).1, ev 1 _ fun w hw => (tv w hw).2.1, ev 2 _ fun w hw => (tv w hw).2.2.1]
  have pB : pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 3 4 5 = VG.Proof.X448.basePt Impl.X448.baseG57 := by
    simp only [pt, VG.Proof.X448.basePt]
    rw [ev 3 _ fun w hw => (tv w hw).2.2.2.1, ev 4 _ fun w hw => (tv w hw).2.2.2.2.1,
      ev 5 _ fun w hw => (tv w hw).2.2.2.2.2]
  have hG : Rep (VG.Proof.X448.basePt Impl.X448.baseG57) (((VG.Proof.X448.combG 57 : ℤ) + 0) • baseAff) := by
    rw [VG.Proof.X448.combG_57, add_zero, natCast_zsmul]; exact VG.Proof.X448.baseG57_ok
  refine ⟨⟨by decide, hst, fun i w hw => ?_, fun w hw => ?_, by rw [tc]; rfl, fun q hq => ?_,
      by rw [pA]; exact hG, by rw [pB]; exact hG, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _, htt⟩,
    ⟨by rw [wt (by decide) (by decide) (by decide)]; exact sa.1,
      by rw [wt (by decide) (by decide) (by decide)]; exact sa.2⟩,
    by rw [kt.1 _ (by decide), kb.1 _ (by decide)]; exact oa,
    fun k hk => by
      rw [wt (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)
        (by simp only [Impl.X448.AArch64.Fast.SAVE, BITS]; omega) (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)]
      exact xa k hk,
    (va.outside ob (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega)).outside tOut
      (by simp only [Impl.X448.AArch64.Fast.VSAVE]; omega),
    by rw [kt.1 _ (by decide), kb.1 _ (by decide), ka.1 _ (by decide)],
    by rw [kt.2.1, kb.2.1, ka.2.1], by rw [kt.2.2, kb.2.2, ka.2.2], mt⟩
  · -- Every slot's limbs are below `Ib`.
    by_cases hi : i.val < 6
    · have hi6 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
        rcases i with ⟨i, hlt⟩; simp only [Fin.ext_iff] at hi ⊢; omega
      rcases hi6 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact bnd_of_words (fun w hw => (tv w hw).1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.1) w hw
      · exact bnd_of_words (fun w hw => (tv w hw).2.2.2.2.2) w hw
    · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
      rw [zt i (by omega) w hw]; decide
  · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [zt 19 (by decide) w hw]; rfl
  · have hn' := hn
    rw [tOut _ (by rw [VG.Proof.X448.AArch64.Base.ofs_off0 base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact bitsb q hq

end VG.Proof.Ed448.AArch64.Base
