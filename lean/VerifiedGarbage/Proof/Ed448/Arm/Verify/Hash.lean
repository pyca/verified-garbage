import VerifiedGarbage.Proof.Ed448.Arm.Verify.Header
import VerifiedGarbage.Proof.Ed448.Arm.Shake.Sponge

/-!
# Ed448 verification on ARMv7: the hash

`hash_ok`: `H(dom4(0, context) ‖ R ‖ A ‖ M)` in the frame at `HASH`, from
the header the frame holds (`hdr_ok`), with the calls of
`Proof/Ed448/Arm/Shake/Sponge.lean`: the Keccak state zeroed, the header,
the context, `R`, `A` and the message absorbed each from where the previous
absorption stopped, the padding absorbed, and 114 bytes squeezed.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit argVal kWr kArgs ScrAt DataOk valid_const valid_frame
  frame_within frame_bytes hdr_len dom4_eq)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem scr_at (L : Lay) : ScrAt 11 L.value SC L.scr := ⟨by decide, rfl⟩

/-- An input's `N` bytes at `P`, which the absorptions may read. -/
theorem input_data (hL : L.Ok) {R : Region} (hR : R ∈ L.inputs) {P : BitVec 32} {N : Nat}
    (hw : Whole.Within ⟨State.addr P, N⟩ R) :
    DataOk L.E L.inputs L.outputs ⟨State.addr P, N⟩ ∧ (∀ r ∈ kWr L.scr, Region.Disjoint ⟨State.addr P, N⟩ r) ∧
      (kArgs L.E 8).Disjoint ⟨State.addr P, N⟩ :=
  let h := hL.kit.data_input hR hw
  ⟨.inr ⟨R, List.mem_append_left _ hR, hw⟩, h.1, h.2⟩

theorem whole (r : Region) : Whole.Within r r := ⟨0, (BitVec.add_zero _).symm, by simp⟩

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` in the frame at `HASH`, with the
header of `dom4` in the frame. -/
theorem hash_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L) :
    WP isa Impl.Ed448.Arm.Verify.hash t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt m₀ (State.addr L.sig) 57 ++ Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 ++
            Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have hk := hL.kit
  have rx : L.CTX ∈ L.inputs := by simp [Lay.inputs]
  have rs : L.SIG ∈ L.inputs := by simp [Lay.inputs]
  have rp : L.PK ∈ L.inputs := by simp [Lay.inputs]
  have rm : L.MSG ∈ L.inputs := by simp [Lay.inputs]
  have ws : Whole.Within ⟨State.addr L.sig, 57⟩ L.SIG := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  obtain ⟨cx, dx, ax⟩ := input_data hL rx (whole _)
  obtain ⟨cs, ds, as⟩ := input_data hL rs ws
  obtain ⟨cp, dp, ap⟩ := input_data hL rp (whole _)
  obtain ⟨cm, dm, am⟩ := input_data hL rm (whole _)
  unfold Impl.Ed448.Arm.Verify.hash
  -- Zero the state.
  refine WP.seq (WP.mono (hk.zero_ok hc ha (scr_at L)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 := frame_bytes hf1 (D := ⟨State.addr L.E + BitVec.ofNat 64 HDR, 10⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hk.frame_kWr (by decide) _ (by simp [kWr]))
    (by change 10 ≤ 2 ^ 64; decide)
  simp only at hh1
  -- The header.
  refine WP.seq (WP.mono (hk.firstAt hc1 ha (scr_at L) (src := .frame HDR) (len := .const 10)
    (P := L.E + BitVec.ofNat 32 HDR) (N := 10) (valid_frame (by decide)) (valid_const (by decide)) rfl rfl
    (by rw [hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hk.frame_addr (by decide)]; exact hk.frame_kWr (by decide))
    (by rw [hk.frame_addr (by decide)]; exact Offset.base_disjoint _ (by decide) (by decide))
    (hk.frame_fit (by decide)) (PublicKey.repr_nil hz)) fun t2 ⟨hc2, _, hr2, hp2⟩ => ?_)
  rw [hk.frame_addr (by decide), hh1, hh] at hr2
  have hp2' : t2.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (hk.nextAt hc2 ha (scr_at L) (src := .caller 1 0) (len := .caller 2 0) (P := L.ctx)
    (N := L.ctxLen.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value]) cx dx ax hL.nx hr2 hp2') fun t3 ⟨hc3, _, hr3, hp3⟩ => ?_)
  have ex := hk.input_bytes hc2 rx (whole _) (by change L.ctxLen.toNat ≤ 2 ^ 64; have := L.ctxLen.isLt; omega)
  simp only at ex
  rw [ex] at hr3 hp3
  -- `R`.
  refine WP.seq (WP.mono (hk.nextAt hc3 ha (scr_at L) (src := .caller 5 0) (len := .const 57) (P := L.sig)
    (N := 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl cs ds as
    (by have := hL.ns; omega) hr3 hp3) fun t4 ⟨hc4, _, hr4, hp4⟩ => ?_)
  have es := hk.input_bytes hc3 rs ws (by change 57 ≤ 2 ^ 64; decide)
  simp only at es
  rw [es] at hr4 hp4
  -- `A`.
  refine WP.seq (WP.mono (hk.nextAt hc4 ha (scr_at L) (src := .caller 0 0) (len := .const 57) (P := L.pk)
    (N := 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl cp dp ap
    hL.np hr4 hp4) fun t5 ⟨hc5, _, hr5, hp5⟩ => ?_)
  have ep := hk.input_bytes hc4 rp (whole _) (by change 57 ≤ 2 ^ 64; decide)
  simp only at ep
  rw [ep] at hr5 hp5
  -- The message.
  refine WP.seq (WP.mono (hk.nextAt hc5 ha (scr_at L) (src := .caller 3 0) (len := .caller 4 0) (P := L.msg)
    (N := L.len.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value]) cm dm am hL.nm hr5 hp5) fun t6 ⟨hc6, _, hr6, hp6⟩ => ?_)
  have em := hk.input_bytes hc5 rm (whole _) (by change L.len.toNat ≤ 2 ^ 64; have := L.len.isLt; omega)
  simp only at em
  rw [em] at hr6 hp6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc6 ha (scr_at L) hr6 hp6) fun t7 ⟨hc7, _, hs7⟩ => ?_)
  refine WP.mono (hk.sqz_step hc7 ha (scr_at L) (d := HASH) (by decide) (by decide)) fun u ⟨hu, _, hb⟩ =>
    ⟨hu, ?_⟩
  rw [hb, hs7, ← PublicKey.shake256_eq, Spec.Ed448.hash,
    dom4_eq L.ctxLen _ _ (by simp [Spec.Ed448.bytesAt])]
  simp only [List.append_assoc]

end VG.Proof.Ed448.Arm.Verify
