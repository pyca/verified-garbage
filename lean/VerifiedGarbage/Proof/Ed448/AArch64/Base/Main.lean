module

public import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
public import VerifiedGarbage.Proof.Ed448.AArch64.CombSum
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Lit
public import VerifiedGarbage.Proof.X448.AArch64.Mem
public import Mathlib.Tactic.NormNum.Prime

import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Combine
import VerifiedGarbage.Proof.Ed448.AArch64.Base.Encode
import VerifiedGarbage.Proof.Ed448.AArch64.CombBase
import Mathlib.FieldTheory.Finite.Basic
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.X448.AArch64.Base.Step
import VerifiedGarbage.Proof.X448.AArch64.Fast.Setup
import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.AArch64.BaseBits
import VerifiedGarbage.Proof.X448.AArch64.Base.Setup
import VerifiedGarbage.Proof.Framework.AArch64.Syms
/-!
# Ed448 base-point multiplication on AArch64: the whole function

Untrusted: everything here is checked by Lean. The correctness of
`vg_ed448_scalar_base` against `scalarBaseLocal` (`BaseContract.lean`): the
comb of 57 tables, by a call of `vg_ed448_r56_comb_base` (`CombBase.call_ok`), and `16 A + C`
(`Point56.combineCall_frame`) leave `R` representing `[k]B`, whose
encoding is `encodePoint (pointMul k B)` since both represent the same affine
point (`encodePoint_rep`); every write but the result's is in the working
space, so the scalar is read unchanged, and the callee-saved registers are
restored from it.
-/

-- Formerly `VerifiedGarbage/Proof/Ed448/AArch64/Base/Setup.lean`, which only this module imported.
section

/-!
# Ed448 base-point multiplication on AArch64: the setup

Untrusted: everything here is checked by Lean. X448's comb's `entry` (the
registers saved, every slot zeroed), the bits of all 57 bytes of the scalar
(`bits_ok`), and both accumulators at `[G] B` for `G = 8 Σ_{j < 57} 256^j`
(`baseG57`): `StepInv` of the comb of 57 tables, for step 0.
-/

section

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
end

end

@[expose] public section

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside Outside2 Saved ofs far)
open VG.Proof.Ed448.AArch64.Base (setup_ok encode_ok)
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- A byte of the working space is beyond the output. -/
theorem far_out {base p : Addr} (hd : (⟨p, 57⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 57 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 57
  omega

theorem decodeLE_57_lt (kb : List Byte) (hk : kb.length = 57) : decodeLE kb < 256 ^ 57 := by
  have h := VG.Proof.Ed448.decodeLE_lt' kb
  rwa [hk] at h

theorem scalarBase_correct {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa scalarBase s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧
      scalarBaseLocal.post s t := by
  have htb := hp.2.2.2.2.2.tblAt (base := s.gpr .x2)
    (by rw [hp.1]; exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    (by simp)
  obtain ⟨hr, hw, hdo, hds, hn, -⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x2 = b := ⟨_, rfl⟩
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  rw [hbase] at hn hdo hds htb
  have hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 q) 1 := fun q hq =>
    ⟨⟨s.gpr .x1, 57⟩, by rw [hr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hkd : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 q) := fun q hq => far hds hq (by decide)
  have hod : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 q) := fun q hq => far hdo hq (by decide)
  set kb := bytesAt s.mem (s.gpr .x1) 57
  set k := decodeLE kb
  unfold scalarBase
  refine WP.seq (WP.mono (setup_ok hbase hws hn rfl hkr hkd htb) fun s1 R => ?_)
  have f1 : VG.Proof.X448.AArch64.Base.Frame s1 base s1 :=
    ⟨R.pre.scr, R.pre.env, R.pre.zero, rfl, rfl, rfl, rfl, Outside2.refl _ _ _ _ _ _⟩
  refine WP.seq (WP.mono (CombBase.call_ok (Or.inr rfl) f1 R.pre) fun s2 ⟨f2, a2, c2⟩ => ?_)
  refine WP.seq (WP.mono (Point56.combineCall_frame f2 a2 c2) fun s3 ⟨f3, r3⟩ => ?_)
  rw [VG.Proof.X448.comb_total (decodeLE_57_lt kb (by simp [kb, VG.Proof.Ed448.bytesAt_eq,
    Spec.X25519.bytesAt]))] at r3
  -- The encoding.
  have out3 : s3.gpr .x20 = s.gpr .x0 := by rw [f3.out, R.out]
  have wr3 : s3.wr = s.wr := by rw [f3.wr, R.wr]
  have o13 : Outside2 base 64 2816 ACC 1152 s1.mem s3.mem := f3.mem
  refine WP.mono (encode_ok f3.scr f3.env out3
    (fun j hj => ⟨⟨s.gpr .x0, 57⟩, by rw [wr3, hw]; simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (fun j hj => hod j hj) (fun j hj => far_out hdo hj)
    (R.saved.outside2 o13 (by decide) (by decide)) (R.savedX.outside2 o13 (by decide) (by decide))
    (R.savedV.outside2 o13 (by decide) (by decide)))
    fun t ⟨t19, t20, tx, tv, t30, _, vt⟩ => ⟨?_, ?_, ?_⟩
  · intro r hr
    have lr : t.gpr .x30 = s.gpr .x30 := by rw [t30, f3.lr, R.lr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t19
    · exact t20
    · exact tx 0 (by decide)
    · exact tx 1 (by decide)
    · exact tx 2 (by decide)
    · exact tx 3 (by decide)
    · exact tx 4 (by decide)
    · exact tx 5 (by decide)
    · exact tx 6 (by decide)
    · exact tx 7 (by decide)
    · exact lr
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv 0 (by decide)
    · exact tv 1 (by decide)
    · exact tv 2 (by decide)
    · exact tv 3 (by decide)
    · exact tv 4 (by decide)
    · exact tv 5 (by decide)
    · exact tv 6 (by decide)
    · exact tv 7 (by decide)
  · show bytesAt t.mem (s.gpr .x0) 57 = Spec.Ed448.scalarBase kb
    rw [vt, Spec.Ed448.scalarBase]
    change Spec.Ed448.encodePoint (VG.Proof.X448.AArch64.Base.pt _ 0 1 2) = _
    rw [VG.Proof.Ed448.encodePoint_rep r3,
      VG.Proof.Ed448.encodePoint_rep (VG.Proof.Ed448.pointMul_rep k VG.Proof.Ed448.basePoint_rep),
      natCast_zsmul]

end VG.Proof.Ed448.AArch64
