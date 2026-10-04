import VerifiedGarbage.Proof.Ed448.Arm.Verify.Sponge

/-!
# Ed448 verification on ARMv7: the hash

`hash_ok`: `H(dom4(0, context) ‖ R ‖ A ‖ M)` in the frame at `HASH`, from
the header the frame holds (`hdr_ok`): the Keccak state zeroed
(`zero_ok`), the header, the context, `R`, `A` and the message absorbed
each from where the previous absorption stopped, the padding absorbed, and
114 bytes squeezed.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR)

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-! ## The state, zeroed -/

/-- The stores, from `scratch` in `r0` and `0` in `r1`. -/
theorem zeroStores_step (hu : Ctx L g m₀ t) (hL : L.Ok) (h0 : t.gpr .r0 = L.scr) (h1 : t.gpr .r1 = 0) :
    WP isa (.block Impl.Ed448.Arm.PublicKey.zeroStores) t fun v => Ctx L g m₀ v ∧
      stateAt v.mem (State.addr L.scr) = Spec.Sha3.zero ∧ Frame [⟨State.addr L.scr, 200⟩] t.mem v.mem := by
  have hw : ∀ k < 50, InRegions t.wr (State.addr (t.gpr .r0) + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k hk
    rw [hu.wr, h0]
    exact ⟨L.SCR, by simp [Lay.outputs], Offset.contains_base _ (by omega) (by omega)⟩
  refine WP.mono (PublicKey.zeroStores_ok h1 (by rw [h0]; have := hL.nc; omega) hw) fun v hv => ⟨?_, ?_, ?_⟩
  · refine hu.of_frame hv.rd hv.wr hv.sp (fun r _ _ => by rw [hv.gpr]) hv.frame ?_
    intro r hr
    rw [List.mem_singleton.mp hr, h0]
    exact .inr ⟨L.SCR, by simp [Lay.outputs], Region.sub_prefix (by decide)⟩
  · have := hv.zero
    rw [h0] at this
    exact PublicKey.stateAt_zero this
  · have f2 := hv.frame
    rw [h0] at f2
    exact f2

def zeroValues : List (Reg × Value) := [(.r0, scr 0), (.r1, .const 0)]

theorem zero_slots {s : State} (hs : ∀ p ∈ zeroValues, s.gpr p.1 = argValue L p.2) :
    s.gpr .r0 = L.scr ∧ s.gpr .r1 = 0 := by
  have h0 := hs (.r0, scr 0) (by simp [zeroValues])
  have h1 := hs (.r1, .const 0) (by simp [zeroValues])
  simp only [argValue, scr, Lay.value, BitVec.add_zero] at h0 h1
  exact ⟨h0, h1⟩

theorem zero_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa zeroState t fun u => Ctx L g m₀ u ∧ stateAt u.mem (State.addr L.scr) = Spec.Sha3.zero ∧
      Frame [⟨State.addr L.E, 24⟩, ⟨State.addr L.scr, 200⟩] t.mem u.mem := by
  unfold zeroState
  refine WP.seq (WP.mono (setup_ok hc hL ha (args := zeroValues) (stk := [])
    (by decide) (by simp [zeroValues, valid, scr, Slot]) (by simp [zeroValues, preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  obtain ⟨h0, h1⟩ := zero_slots hs
  refine WP.mono (zeroStores_step hu hL h0 h1) fun v ⟨hv, hz, f2⟩ => ⟨hv, hz, ?_⟩
  refine (Frame.sub hm fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩).trans
    (Frame.sub f2 fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)

/-! ## The hash -/

theorem len_append (msg : List Byte) (m : Mem) (p : Addr) (n : Nat) :
    (msg ++ Spec.Ed448.bytesAt m p n).length = msg.length + n := by
  simp [Spec.Ed448.bytesAt]

theorem hdr_len (L : Lay) : (hdrBytes L).length = 10 := by simp [hdrBytes]

/-- The input of the hash, as the specification puts it together. -/
theorem dom4_eq (L : Lay) (m : Mem) (x : List Byte) :
    Spec.Ed448.dom4 0 (Spec.Ed448.bytesAt m (State.addr L.ctx) L.ctxLen.toNat) ++ x =
      hdrBytes L ++ Spec.Ed448.bytesAt m (State.addr L.ctx) L.ctxLen.toNat ++ x := by
  simp [Spec.Ed448.dom4, hdrBytes, Spec.Ed448.bytesAt]

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` in the frame at `HASH`, with the
header of `dom4` in the frame. -/
theorem hash_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    (hh : Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L) :
    WP isa hash t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt m₀ (State.addr L.sig) 57 ++ Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 ++
            Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  -- Zero the state.
  refine WP.seq (WP.mono (zero_ok hc hL ha) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 : Spec.Ed448.bytesAt t1.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L := by
    rw [← hh]
    unfold Spec.Ed448.bytesAt
    refine List.map_congr_left fun i hi => hf1.bytes (R := ⟨State.addr L.E + BitVec.ofNat 64 HDR, 10⟩) ?_
      (by change 10 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact Offset.disjoint_base _ (by decide) (by decide)
    · exact (data_frame hL (d := HDR) (n := 10) (by decide) (by decide)).1 _ (by simp [kWr])
  -- The header.
  refine WP.seq (WP.mono (hdr_abs hc1 hL ha (PublicKey.repr_nil hz) hh1) fun t2 ⟨hc2, hr2, hp2⟩ => ?_)
  have hp2' : t2.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (next_abs hc2 hL ha (src := .caller 1 0) (len := .caller 2 0) ⟨.inl (by decide), by decide⟩
    ⟨.inl (by decide), by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact hL.nx) hr2 hp2') fun t3 ⟨hc3, hr3, hp3⟩ => ?_)
  simp only [argValue, Lay.value, BitVec.add_zero] at hr3 hp3
  have hp3' : t3.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L ++
      Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat).length % 136) := by rw [hp3]; simp only [len_append]
  -- `R`.
  refine WP.seq (WP.mono (next_abs hc3 hL ha (src := .caller 5 0) (len := .const 57) ⟨.inl (by decide), by decide⟩
    (show 57 < 65536 by decide) (R := L.SIG) (by simp [Lay.inputs])
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argValue, Lay.value, BitVec.add_zero]; have := hL.ns; simp; omega) hr3 hp3')
    fun t4 ⟨hc4, hr4, hp4⟩ => ?_)
  simp only [argValue, Lay.value, BitVec.add_zero, show (BitVec.ofNat 32 57).toNat = 57 from rfl] at hr4 hp4
  have hp4' : t4.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L ++ Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat ++
      Spec.Ed448.bytesAt m₀ (State.addr L.sig) 57).length % 136) := by rw [hp4]; simp only [len_append]
  -- `A`.
  refine WP.seq (WP.mono (next_abs hc4 hL ha (src := .caller 0 0) (len := .const 57) ⟨.inl (by decide), by decide⟩
    (show 57 < 65536 by decide) (R := L.PK) (by simp [Lay.inputs])
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argValue, Lay.value, BitVec.add_zero]; have := hL.np; simp; omega) hr4 hp4')
    fun t5 ⟨hc5, hr5, hp5⟩ => ?_)
  simp only [argValue, Lay.value, BitVec.add_zero, show (BitVec.ofNat 32 57).toNat = 57 from rfl] at hr5 hp5
  have hp5' : t5.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L ++ Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat ++
      Spec.Ed448.bytesAt m₀ (State.addr L.sig) 57 ++ Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57).length % 136) := by
    rw [hp5]; simp only [len_append]
  -- The message.
  refine WP.seq (WP.mono (next_abs hc5 hL ha (src := .caller 3 0) (len := .caller 4 0) ⟨.inl (by decide), by decide⟩
    ⟨.inl (by decide), by decide⟩ (R := L.MSG) (by simp [Lay.inputs])
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argValue, Lay.value, BitVec.add_zero]; exact hL.nm) hr5 hp5') fun t6 ⟨hc6, hr6, hp6⟩ => ?_)
  simp only [argValue, Lay.value, BitVec.add_zero] at hr6 hp6
  have hp6' : t6.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L ++ Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat ++
      Spec.Ed448.bytesAt m₀ (State.addr L.sig) 57 ++ Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 ++
      Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat).length % 136) := by
    rw [hp6]; simp only [len_append]
  -- Pad and squeeze.
  refine WP.seq (WP.mono (pad_step hc6 hL ha hr6 hp6') fun t7 ⟨hc7, hs7⟩ => ?_)
  refine WP.mono (sqz_step hc7 hL ha) fun t8 ⟨hc8, hm8⟩ => ⟨hc8, ?_⟩
  rw [hm8, hs7, ← PublicKey.shake256_eq, Spec.Ed448.hash, dom4_eq]
  simp only [List.append_assoc]

end VG.Proof.Ed448.Arm.Verify
