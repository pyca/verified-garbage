import VerifiedGarbage.Proof.Ed448.AArch64.Base.Setup
import VerifiedGarbage.Proof.Ed448.AArch64.Base.Encode
import VerifiedGarbage.Proof.X448.AArch64.Base.Loop
import VerifiedGarbage.Proof.Ed448.Group.Projective
import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract

/-!
# Ed448 base-point multiplication on AArch64: the whole function

Untrusted: everything here is checked by Lean. The correctness of
`vg_ed448_scalar_base` against `scalarBaseLocal` (`BaseContract.lean`): the
comb of 57 tables leaves `R` representing `[k]B` (`combine_ok`), whose
encoding is `encodePoint (pointMul k B)` since both represent the same affine
point (`encodePoint_rep`); every write but the result's is in the working
space, so the scalar is read unchanged, and the callee-saved registers are
restored from it.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside Outside2 Saved ofs far)
open VG.Proof.X448.AArch64.Base (loop_ok combine_ok)
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
  obtain ⟨hr, hw, hdo, hds, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x2 = b := ⟨_, rfl⟩
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  rw [hbase] at hn hdo hds
  have hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 q) 1 := fun q hq =>
    ⟨⟨s.gpr .x1, 57⟩, by rw [hr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hkd : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 q) := fun q hq => far hds hq (by decide)
  have hod : ∀ q < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 q) := fun q hq => far hdo hq (by decide)
  set kb := bytesAt s.mem (s.gpr .x1) 57
  set k := decodeLE kb
  unfold scalarBase
  refine WP.seq (WP.mono (setup_ok hbase hws hn rfl hkr hkd) fun s1 R => ?_)
  refine WP.seq (WP.mono (loop_ok (by decide) (s₀ := s1) 57 s1 (by decide) le_rfl
    (by rw [Nat.sub_self]; exact R.inv)) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (combine_ok (decodeLE_57_lt kb (by simp [kb, VG.Proof.Ed448.bytesAt_eq, Spec.X25519.bytesAt])) h2)
    fun s3 ⟨f3, r3⟩ => ?_)
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
