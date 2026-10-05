import VerifiedGarbage.Proof.Ed448.AArch64.PublicKey.Hash
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Prune

/-!
# Ed448 public-key derivation on AArch64: pruning and the base point

The first 57 bytes of the hash, pruned, are stored as the scalar at the
bottom of the frame (`prune_ok`), `[s]B` is encoded into `out` by
`vg_ed448_scalar_base` (`base_step`, given that it meets its contract, `BaseOk`), and the scalar and
the hash in the frame are cleared (`wipe_step`).
-/

namespace VG.Proof.Ed448.AArch64.PublicKey

open VG VG.AArch64 VG.Impl.Ed448.AArch64.PublicKey
open VG.Impl.Ed25519.AArch64.Whole (setup callWith Value zeroWord)
open VG.Proof.Ed25519.AArch64.Whole (call_ok Within)
open VG.Proof.Ed448.AArch64.Whole (prune_run)

/-! ## In the frame's body -/

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem prune_step (hc : Ctx L g vec m₀ t) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.E + BitVec.ofNat 64 hashAt) 114 = h) :
    WP isa (.block prune) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem L.E 57) = Spec.Ed448.prune h := by
  have hwrite : (⟨t.sp, 256⟩ : Region) ∈ t.wr := by rw [hc.sp, hc.wr]; exact List.mem_cons_self
  have hh' : Spec.Sha3.bytesAt t.mem (t.sp + BitVec.ofNat 64 hashAt) 114 = h := by rw [hc.sp]; exact hh
  refine WP.mono (prune_run (d := 0) hwrite (by decide) (by decide) (by decide) (by decide) (by decide) hh')
    fun u ⟨hu, hf, hp⟩ => ⟨?_, ?_⟩
  · refine hc.of_frame hu.rd hu.wr hu.sp ?_ ?_ hf ?_
    · intro r hr _
      apply hu.regs r <;> intro h <;> subst r <;> simp [preserved] at hr
    · intro r _; rw [hu.v]
    · rintro r hr
      rw [List.mem_singleton.mp hr, hc.sp, BitVec.add_zero]
      exact .inl (Region.sub_prefix (by decide))
  · rw [hc.sp, BitVec.add_zero] at hp
    exact hp

theorem base_noFrames : Impl.Ed448.AArch64.scalarBase.noFrames = true :=
  Proof.Ed448.AArch64.scalarBase_noFrames

def baseValues : List (Reg × Value) := [(.x0, .caller 0 0), (.x1, .frame 0), (.x2, .caller 2 0)]

theorem base_pre (hL : L.Ok) {u : State} (hs : ∀ p ∈ baseValues, u.gpr p.1 = argValue L p.2) :
    Proof.Ed448.AArch64.scalarBaseLocal.pre (u.callEntry.withRegions [⟨L.E, 57⟩] L.outputs) := by
  have h0 := hs (.x0, .caller 0 0) (List.mem_of_getElem? (i := 0) rfl)
  have h1 := hs (.x1, .frame 0) (List.mem_of_getElem? (i := 1) rfl)
  have h2 := hs (.x2, .caller 2 0) (List.mem_of_getElem? (i := 2) rfl)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  simp only [Proof.Ed448.AArch64.scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨trivial, rfl, hL.oc, hL.kc.sub_left (Region.sub_prefix (by decide)), hL.nc⟩

theorem base_covers (L : Lay) : Covers ([⟨L.E, 57⟩] ++ L.outputs) (L.inputs ++ L.FR :: L.outputs) := by
  refine Covers.of_sub fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    exact ⟨L.FR, List.mem_append_right _ List.mem_cons_self, 0, (BitVec.add_zero _).symm,
      by change 0 + 57 ≤ 256; decide⟩
  · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_writes (L : Lay) : ∀ r ∈ L.outputs, Within r L.FR ∨ ∃ R ∈ L.outputs, Within r R :=
  fun r hr => .inr ⟨r, hr, 0, (BitVec.add_zero _).symm, by simp⟩

theorem base_step (hb : Proof.Ed448.AArch64.BaseOk) (hc : Ctx L g vec m₀ t) (hL : L.Ok)
    (ha : Arguments L m₀) {n : Nat}
    (hs : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem L.E 57) = n) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) t fun u =>
      Ctx L g vec m₀ u ∧ Spec.Ed448.bytesAt u.mem L.out 57 =
        Spec.Ed448.encodePoint (Spec.Ed448.pointMul n Spec.Ed448.basePoint) := by
  refine WP.seq (WP.mono (setup_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 0), (.x2, .caller 2 0)])
    (by decide) (by simp [VG.Proof.Ed25519.AArch64.Whole.valid]) (by simp) (by decide))
    fun u ⟨hu, hm, hav⟩ => ?_)
  have h0 := hav (.x0, .caller 0 0) (by simp)
  have h1 := hav (.x1, .frame 0) (by simp)
  have h2 := hav (.x2, .caller 2 0) (by simp)
  simp only [argValue, Lay.value, BitVec.add_zero] at h0 h1 h2
  have hpre := base_pre hL (u := u) (fun p hp => hav p hp)
  refine call_ok hu hb.ok base_noFrames hpre (base_covers L)
    (base_writes L) fun w hw _ hp => ⟨hw, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm] at hp
  rw [hp, Spec.Ed448.scalarBase, hs]

theorem wipe_step (hc : Ctx L g vec m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed448.bytesAt u.mem L.out 57 = Spec.Ed448.bytesAt t.mem L.out 57 := by
  refine WP.mono (VG.Proof.Ed25519.AArch64.Whole.Ctx.zeroWords hc (start := 0) (count := 32) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes (R := L.OUT) ?_
    (by change 57 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 8 * 0 + 8 * 32 ≤ 336))).symm

end VG.Proof.Ed448.AArch64.PublicKey
