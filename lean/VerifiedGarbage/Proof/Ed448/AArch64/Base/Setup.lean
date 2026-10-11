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
open VG.Proof.X448.AArch64.Base (CombPre block1_ok)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.Ed448 (Rep baseAff)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- What the setup leaves, from the function's entry state `sE`. -/
structure CombReady (sE : State) (base : Addr) (k : Nat) (t : State) : Prop where
  pre : CombPre 57 base k t
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
  refine WP.mono_syms (VG.Proof.Ed448.AArch64.bits_ok ha (by rw [ka.1 _ (by decide)]; exact hk)
    (by rw [ka.2.1, ka.2.2]; exact hkr) hkd) fun t ⟨_, gb, rdb, wrb, ob, bitsb⟩ syb => ?_
  have kb : Keeps (.x1 :: bitRegs) a t := ⟨gb, rdb, wrb⟩
  have hsb : Scr t base := ha.of_keeps kb (by decide)
  rw [bytesAt_outside outa hkd] at bitsb
  have mt : Outside base 0 8192 s.mem t.mem := outa.trans (ob.mono (by omega) (by simp only [BITS]; omega))
  have htt : VG.Proof.X448.AArch64.Base.TblAt t base (t.syms VG.Impl.X448.AArch64.Base.combSym) := by
    rw [syb, sya]
    exact htb.of_far (by rw [kb.2.1, ka.2.1, kb.2.2, ka.2.2]) fun x hx => mt x (Or.inr hx)
  -- Every word outside the bits is as `block1` left it.
  have wt : ∀ {d : Nat}, d + 8 ≤ BITS ∨ BITS + 456 ≤ d → d + 8 ≤ 8192 →
      word t.mem base d = word a.mem base d := fun h2 h3 => ob.word h2 h3
  -- The slots `block1` zeroed.
  have zs : ∀ i : Index, ∀ w < 8, word a.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := za (16 * i.val + w) (by omega)
    have e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega
    rw [show VG.Proof.X448.AArch64.limbs a.mem base (slot 0) (16 * i.val + w) =
      (word a.mem base (slot i.val + 8 * w)).toNat by
        simp only [VG.Proof.X448.AArch64.limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  have zt : ∀ i : Index, ∀ w < 8, word t.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    rw [wt (by simp only [slot, BITS]; omega) (by simp only [slot]; omega)]
    exact zs i w hw
  refine ⟨⟨hsb, fun i w hw => ?_, fun w hw => ?_, fun q hq => bitsb q hq, htt⟩,
    ⟨by rw [wt (by decide) (by decide)]; exact sa.1,
      by rw [wt (by decide) (by decide)]; exact sa.2⟩,
    by rw [kb.1 _ (by decide)]; exact oa,
    fun k hk => by
      rw [wt (by simp only [Impl.X448.AArch64.Fast.SAVE, BITS]; omega)
        (by simp only [Impl.X448.AArch64.Fast.SAVE]; omega)]
      exact xa k hk,
    va.outside ob (by simp only [BITS, Impl.X448.AArch64.Fast.VSAVE]; omega),
    by rw [kb.1 _ (by decide), ka.1 _ (by decide)],
    by rw [kb.2.1, ka.2.1], by rw [kb.2.2, ka.2.2], mt⟩
  · show (word t.mem base (slot i.val + 8 * w)).toNat < Ib
    rw [zt i w hw]; decide
  · show (word t.mem base (slot (19 : Index).val + 8 * w)).toNat = 0
    rw [zt 19 w hw]; rfl

end VG.Proof.Ed448.AArch64.Base
