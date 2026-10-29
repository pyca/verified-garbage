module

import VerifiedGarbage.Proof.CmacTripleDes.Stream.PPC64LE.Common
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Key.Verified
import VerifiedGarbage.Proof.TripleDes.PPC64LE.Ecb.Call
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Streaming TDEA-CMAC on PPC64LE: the calls

`keyCall_wp` and `encCall_wp`: the calls of the verified key expansion and
block function, from their contracts (`Key.correct`, `Ecb.call_ok`), as the
streaming functions make them: the key expansion writes the schedule at the
start of the state, and the block function enciphers the block at `B + 512`
with the working space at `B`, the scratch buffer's 640 bytes.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.PPC64LE

open VG VG.PPC64LE VG.Impl.CmacTripleDes.Stream.PPC64LE

/-- The key expansion's call, with the key at `r3` (`len` bytes, in `r4`)
and the schedule at `r5`, within the 416 bytes at `S`. -/
theorem keyCall_wp {s : State} {K S : Addr} {len : Nat} (h3 : s.gpr .r3 = K) (h4 : s.gpr .r4 = BitVec.ofNat 64 len)
    (h5 : s.gpr .r5 = S) (hlen : len < 2 ^ 64) (hkey : (⟨K, len⟩ : Region) ∈ s.rd)
    (hS : (⟨S, 416⟩ : Region) ∈ s.wr) (hd : Region.Disjoint ⟨K, len⟩ ⟨S, 416⟩)
    (hv : Spec.TripleDes.validKey len) {Q : State → Prop}
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → Frame [⟨S, 384⟩] s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Spec.TripleDes.scheduleAt s'.mem S = Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem K len) → Q s') :
    WP isa keyCall s Q := by
  have c3 := State.callEntry_gpr s (r := .r3) (by decide)
  have c4 := State.callEntry_gpr s (r := .r4) (by decide)
  have c5 := State.callEntry_gpr s (r := .r5) (by decide)
  have hlt : (s.gpr .r4).toNat = len := by rw [h4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  have sub : Region.Sub ⟨S, 384⟩ ⟨S, 416⟩ := Region.sub_prefix (by decide)
  refine WP.call (k := Proof.TripleDes.PPC64LE.Key.contract) Proof.TripleDes.PPC64LE.Key.correct
    (rd := [⟨K, len⟩]) (wr := [⟨S, 384⟩]) ?_ ?_ ?_ ?_
  · simp only [Proof.TripleDes.PPC64LE.Key.contract, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c3, c4, c5, h3, hlt, h5]
    exact ⟨trivial, trivial, hd.sub_right sub, hv⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_left _ hkey, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ hS, 0, by simp, by show 0 + 384 ≤ 416; decide⟩
  · refine VG.Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, hS, 0, by simp, by show 0 + 384 ≤ 416; decide⟩
  · intro s' rd wr _ frame callee _ out
    simp only [Proof.TripleDes.PPC64LE.Key.contract, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c3, c4, c5, h3, hlt, h5] at out
    exact k s' rd wr frame callee out

/-- The block function's call, with the schedule at `r3 = S`, the block at
`r4 = B + 512` and the working space at `r5 = B`. -/
theorem encCall_wp {s : State} {S B : Addr} (h3 : s.gpr .r3 = S) (h4 : s.gpr .r4 = B + BitVec.ofNat 64 512)
    (h5 : s.gpr .r5 = B) (hkey : InRegions (s.rd ++ s.wr) S 384) {L : Nat} (hB : (⟨B, L⟩ : Region) ∈ s.wr)
    (hL : 640 ≤ L) (hd : Region.Disjoint ⟨S, 384⟩ ⟨B, 640⟩) {Q : State → Prop}
    (k : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      s'.gpr .r3 = S → s'.gpr .r4 = B + BitVec.ofNat 64 512 → s'.gpr .r5 = B →
      Frame [⟨B, 520⟩] s.mem s'.mem →
      Spec.TripleDes.blockAt s'.mem (B + BitVec.ofNat 64 512) =
        Spec.TripleDes.encryptBlock (Spec.TripleDes.scheduleAt s.mem S)
          (Spec.TripleDes.blockAt s.mem (B + BitVec.ofNat 64 512)) → Q s') :
    WP isa encCall s Q := by
  have bufIn : Region.Sub ⟨B + BitVec.ofNat 64 512, 8⟩ ⟨B, 640⟩ := VG.Offset.sub_base _ (by decide)
  have scrIn : Region.Sub ⟨B, 512⟩ ⟨B, 640⟩ := Region.sub_prefix (by decide)
  have cw : VG.Covers [⟨s.gpr .r4, 8⟩, ⟨s.gpr .r5, 512⟩] s.wr := VG.Covers.of_sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨B, L⟩, hB, 512, h4, by show 512 + 8 ≤ L; omega⟩
    · exact ⟨⟨B, L⟩, hB, 0, by simp [h5], by show 0 + 512 ≤ L; omega⟩
  have hp : Proof.TripleDes.PPC64LE.Ecb.CallPre s :=
    ⟨VG.Covers.cons (by rw [h3]; exact VG.Covers.one hkey) (VG.Covers.right cw), cw,
      by rw [h3, h5]; exact hd.sub_right scrIn,
      by rw [h4, h5]; exact VG.Offset.disjoint_base _ (by decide) (by omega)⟩
  refine WP.mono (Proof.TripleDes.PPC64LE.Ecb.call_ok .encrypt s hp) fun s' h' => ?_
  have sub : ∀ r ∈ [(⟨s.gpr .r4, 8⟩ : Region), ⟨s.gpr .r5, 512⟩], ∃ r' ∈ [(⟨B, 520⟩ : Region)], Region.Sub r r' :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, by rw [h4]; exact VG.Offset.sub_base _ (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, by rw [h5]; exact Region.sub_prefix (by decide)⟩
  have out := h'.output
  rw [h3, h4] at out
  exact k s' h'.rd h'.wr h'.callee (by rw [h'.reg _ (by decide), h3]) (by rw [h'.reg _ (by decide), h4])
    (by rw [h'.reg _ (by decide), h5]) (h'.mem.sub sub) out

end VG.Proof.CmacTripleDes.Stream.PPC64LE
