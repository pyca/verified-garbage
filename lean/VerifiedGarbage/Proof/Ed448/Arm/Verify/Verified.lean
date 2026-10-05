import VerifiedGarbage.Impl.Ed448.Arm.Verify
import VerifiedGarbage.Proof.Ed448.Arm.Shake.CT
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed448.Arm.VerifyVerified
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Arm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Verify.Entry`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Verify.Layout`. -/
section

/-!
# Ed448 verification on ARMv7: the layout

The frame is Ed25519's on this target (`Proof/Ed25519/Arm/Whole`): `Ctx`
holds between the frame's entry and its exit. `Lay` names the arguments and
the frame's base `E`; the inputs are the buffers, the caller's stack
arguments (`ORIG`, which hold `scratch`) and the saved arguments, and the
only output is `scratch`. `setup_ok` sets a call's arguments from them.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.ARGS Whole.value)
open VG.Proof.Ed448.Arm.Shake (Slot valid Fits Ctx.setup Kit)

structure Lay where
  pk : BitVec 32
  ctx : BitVec 32
  ctxLen : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  sig : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : VG.Proof.Ed448.Arm.Verify.Lay)
abbrev PK : Region := ⟨State.addr L.pk, 57⟩
abbrev CTX : Region := ⟨State.addr L.ctx, L.ctxLen.toNat⟩
abbrev MSG : Region := ⟨State.addr L.msg, L.len.toNat⟩
abbrev SIG : Region := ⟨State.addr L.sig, 114⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev ORIG : Region := ⟨State.addr L.E + BitVec.ofNat 64 280, 12⟩
abbrev FR : Region := Whole.FR L.E
abbrev STK : Region := ⟨State.addr L.E, 280⟩
def inputs : List Region := [L.PK, L.CTX, L.MSG, L.SIG, L.ORIG, L.ARGS]
def outputs : List Region := [L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with | 0 => L.pk | 1 => L.ctx | 2 => L.ctxLen | 3 => L.msg | 4 => L.len | 5 => L.sig | _ => L.scr
structure Ok : Prop where
  top : L.E.toNat + 292 ≤ 2 ^ 32
  cl : L.ctxLen.toNat < 256
  ps : L.PK.Disjoint L.SCR
  xs : L.CTX.Disjoint L.SCR
  ms : L.MSG.Disjoint L.SCR
  ss : L.SIG.Disjoint L.SCR
  os : L.ORIG.Disjoint L.SCR
  kp : L.STK.Disjoint L.PK
  kx : L.STK.Disjoint L.CTX
  km : L.STK.Disjoint L.MSG
  ks : L.STK.Disjoint L.SIG
  kc : L.STK.Disjoint L.SCR
  np : L.pk.toNat + 57 ≤ 2 ^ 32
  nx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  ns : L.sig.toNat + 114 ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : VG.Proof.Ed448.Arm.Verify.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

/-- The saved words, and `scratch` where the caller put it. -/
def Arguments (L : VG.Proof.Ed448.Arm.Verify.Lay) (m : Mem) : Prop :=
  ∀ j, VG.Proof.Ed448.Arm.Shake.Slot 11 j → m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def argValue (L : VG.Proof.Ed448.Arm.Verify.Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

variable {L : VG.Proof.Ed448.Arm.Verify.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem frame_sub (L : VG.Proof.Ed448.Arm.Verify.Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : VG.Proof.Ed448.Arm.Verify.Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

/-- The inputs are outside what the body may write. -/
theorem Lay.Ok.inputs_out (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) :
    ∀ R ∈ L.outputs ++ [L.FR], r.Disjoint R := by
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rintro R (rfl | rfl)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.ps
    · exact hL.xs
    · exact hL.ms
    · exact hL.ss
    · exact hL.os
    · exact hL.kc.sub_left (VG.Proof.Ed448.Arm.Verify.args_sub L)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hL.kp.sub_left (VG.Proof.Ed448.Arm.Verify.frame_sub L)).symm
    · exact (hL.kx.sub_left (VG.Proof.Ed448.Arm.Verify.frame_sub L)).symm
    · exact (hL.km.sub_left (VG.Proof.Ed448.Arm.Verify.frame_sub L)).symm
    · exact (hL.ks.sub_left (VG.Proof.Ed448.Arm.Verify.frame_sub L)).symm
    · exact Offset.disjoint_base _ (by decide : 248 ≤ 280) (by decide)
    · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

theorem Ctx.input_bytes (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs)
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.mem r.base r.len = Spec.Ed448.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed448.bytesAt
  exact List.map_congr_left fun i hi =>
    hc.frame.bytes (R := r) (hL.inputs_out hr) hn (List.mem_range.mp hi)

theorem slot_mem (L : VG.Proof.Ed448.Arm.Verify.Lay) {j : Nat} (hj : VG.Proof.Ed448.Arm.Shake.Slot 11 j) :
    ∃ R ∈ L.inputs, R.Contains (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
  obtain ⟨hj11, hj | hj⟩ := hj
  · exact ⟨L.ARGS, by simp [Lay.inputs],
      Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)⟩
  · exact ⟨L.ORIG, by simp [Lay.inputs],
      Offset.contains _ (e := 280) (k := 12) (by omega) (by omega) (by decide)⟩

theorem Ctx.arg_word (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : VG.Proof.Ed448.Arm.Shake.Slot 11 j) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  obtain ⟨R, hR, hcon⟩ := VG.Proof.Ed448.Arm.Verify.slot_mem L hj
  exact hc.frame.readW (r := R) hcon (hL.inputs_out hR) (by decide)

theorem value_eq (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₀)
    {v : Value} (hv : VG.Proof.Ed448.Arm.Shake.valid 11 v) : Whole.value L.E t.mem v = VG.Proof.Ed448.Arm.Verify.argValue L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, VG.Proof.Ed448.Arm.Verify.argValue]
    rw [hc.arg_word hL hv.1, ha j hv.1]

theorem setup_ok (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, VG.Proof.Ed448.Arm.Shake.valid 11 p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, VG.Proof.Ed448.Arm.Shake.valid 11 v) :
    WP isa (.block (setup args stk)) t fun u => VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ u ∧
      Frame [⟨State.addr L.E, 24⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = VG.Proof.Ed448.Arm.Verify.argValue L p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = VG.Proof.Ed448.Arm.Verify.argValue L (stk[j]'hj)) ∧
      (∀ r, r ∉ args.map Prod.fst → r ≠ .r0 → r ≠ .r12 → u.gpr r = t.gpr r) := by
  have hE : Fits L.E 11 := ⟨by decide, by decide, by have := hL.top; omega⟩
  refine WP.mono (Ctx.setup hc hE hn hv hs hvs
    (fun j hj => let ⟨R, hR, hcon⟩ := VG.Proof.Ed448.Arm.Verify.slot_mem L hj; ⟨R, hR, hcon⟩) hr)
    fun u ⟨hu, hm, hregs, hstk, hk⟩ => ⟨hu, Frame.sub hm fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩, ?_, ?_, hk⟩
  · intro p hp
    rw [hregs p hp, VG.Proof.Ed448.Arm.Verify.value_eq hc hL ha (hv p hp)]
  · intro j hj
    rw [hstk j hj, VG.Proof.Ed448.Arm.Verify.value_eq hc hL ha (hvs _ (List.getElem_mem hj))]

/-- What the calls need of the layout (`Proof/Ed448/Arm/Shake/Layout.lean`). -/
theorem Lay.Ok.kit (hL : L.Ok) : Kit L.E L.scr 11 L.inputs L.outputs :=
  ⟨⟨by decide, by decide, by have := hL.top; omega⟩, hL.nc, by simp [Lay.outputs], hL.kc,
    fun _ hr R hR => hL.inputs_out hr R hR, fun _ hj => VG.Proof.Ed448.Arm.Verify.slot_mem L hj⟩

end VG.Proof.Ed448.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Verify.Header`. -/
section

/-!
# Ed448 verification on ARMv7: the header of `dom4`

`hdr_ok`: the block `hdr` leaves `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten
bytes of `dom4(0, context)`, in the frame at `HDR` (`Shake.Kit.hdr_ok`).
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole

variable {L : VG.Proof.Ed448.Arm.Verify.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : VG.Proof.Ed448.Arm.Verify.Lay) : List Byte :=
  "SigEd448".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem hdr_ok (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₀) :
    WP isa (.block hdr) t fun u => VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = VG.Proof.Ed448.Arm.Verify.hdrBytes L :=
  WP.mono (hL.kit.hdr_ok hc ha (j := 2) (by decide) hL.cl (by decide)) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩

end VG.Proof.Ed448.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Verify.Hash`. -/
section

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

variable {L : VG.Proof.Ed448.Arm.Verify.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem scr_at (L : VG.Proof.Ed448.Arm.Verify.Lay) : ScrAt 11 L.value SC L.scr := ⟨by decide, rfl⟩

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
theorem hash_ok (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₀)
    (hh : Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = VG.Proof.Ed448.Arm.Verify.hdrBytes L) :
    WP isa Impl.Ed448.Arm.Verify.hash t fun u => VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ u ∧
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
  obtain ⟨cx, dx, ax⟩ := VG.Proof.Ed448.Arm.Verify.input_data hL rx (VG.Proof.Ed448.Arm.Verify.whole _)
  obtain ⟨cs, ds, as⟩ := VG.Proof.Ed448.Arm.Verify.input_data hL rs ws
  obtain ⟨cp, dp, ap⟩ := VG.Proof.Ed448.Arm.Verify.input_data hL rp (VG.Proof.Ed448.Arm.Verify.whole _)
  obtain ⟨cm, dm, am⟩ := VG.Proof.Ed448.Arm.Verify.input_data hL rm (VG.Proof.Ed448.Arm.Verify.whole _)
  unfold Impl.Ed448.Arm.Verify.hash
  -- Zero the state.
  refine WP.seq (WP.mono (hk.zero_ok hc ha (VG.Proof.Ed448.Arm.Verify.scr_at L)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  have hh1 := frame_bytes hf1 (D := ⟨State.addr L.E + BitVec.ofNat 64 HDR, 10⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hk.frame_kWr (by decide) _ (by simp [kWr]))
    (by change 10 ≤ 2 ^ 64; decide)
  simp only at hh1
  -- The header.
  refine WP.seq (WP.mono (hk.firstAt hc1 ha (VG.Proof.Ed448.Arm.Verify.scr_at L) (src := .frame HDR) (len := .const 10)
    (P := L.E + BitVec.ofNat 32 HDR) (N := 10) (valid_frame (by decide)) (valid_const (by decide)) rfl rfl
    (by rw [hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hk.frame_addr (by decide)]; exact hk.frame_kWr (by decide))
    (by rw [hk.frame_addr (by decide)]; exact Offset.base_disjoint _ (by decide) (by decide))
    (hk.frame_fit (by decide)) (PublicKey.repr_nil hz)) fun t2 ⟨hc2, _, hr2, hp2⟩ => ?_)
  rw [hk.frame_addr (by decide), hh1, hh] at hr2
  have hp2' : t2.gpr .r0 = BitVec.ofNat 32 ((VG.Proof.Ed448.Arm.Verify.hdrBytes L).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (hk.nextAt hc2 ha (VG.Proof.Ed448.Arm.Verify.scr_at L) (src := .caller 1 0) (len := .caller 2 0) (P := L.ctx)
    (N := L.ctxLen.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value]) cx dx ax hL.nx hr2 hp2') fun t3 ⟨hc3, _, hr3, hp3⟩ => ?_)
  have ex := hk.input_bytes hc2 rx (VG.Proof.Ed448.Arm.Verify.whole _) (by change L.ctxLen.toNat ≤ 2 ^ 64; have := L.ctxLen.isLt; omega)
  simp only at ex
  rw [ex] at hr3 hp3
  -- `R`.
  refine WP.seq (WP.mono (hk.nextAt hc3 ha (VG.Proof.Ed448.Arm.Verify.scr_at L) (src := .caller 5 0) (len := .const 57) (P := L.sig)
    (N := 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl cs ds as
    (by have := hL.ns; omega) hr3 hp3) fun t4 ⟨hc4, _, hr4, hp4⟩ => ?_)
  have es := hk.input_bytes hc3 rs ws (by change 57 ≤ 2 ^ 64; decide)
  simp only at es
  rw [es] at hr4 hp4
  -- `A`.
  refine WP.seq (WP.mono (hk.nextAt hc4 ha (VG.Proof.Ed448.Arm.Verify.scr_at L) (src := .caller 0 0) (len := .const 57) (P := L.pk)
    (N := 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl cp dp ap
    hL.np hr4 hp4) fun t5 ⟨hc5, _, hr5, hp5⟩ => ?_)
  have ep := hk.input_bytes hc4 rp (VG.Proof.Ed448.Arm.Verify.whole _) (by change 57 ≤ 2 ^ 64; decide)
  simp only at ep
  rw [ep] at hr5 hp5
  -- The message.
  refine WP.seq (WP.mono (hk.nextAt hc5 ha (VG.Proof.Ed448.Arm.Verify.scr_at L) (src := .caller 3 0) (len := .caller 4 0) (P := L.msg)
    (N := L.len.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value]) cm dm am hL.nm hr5 hp5) fun t6 ⟨hc6, _, hr6, hp6⟩ => ?_)
  have em := hk.input_bytes hc5 rm (VG.Proof.Ed448.Arm.Verify.whole _) (by change L.len.toNat ≤ 2 ^ 64; have := L.len.isLt; omega)
  simp only at em
  rw [em] at hr6 hp6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc6 ha (VG.Proof.Ed448.Arm.Verify.scr_at L) hr6 hp6) fun t7 ⟨hc7, _, hs7⟩ => ?_)
  refine WP.mono (hk.sqz_step hc7 ha (VG.Proof.Ed448.Arm.Verify.scr_at L) (d := HASH) (by decide) (by decide)) fun u ⟨hu, _, hb⟩ =>
    ⟨hu, ?_⟩
  rw [hb, hs7, ← PublicKey.shake256_eq, Spec.Ed448.hash,
    dom4_eq L.ctxLen _ _ (by simp [Spec.Ed448.bytesAt])]
  simp only [List.append_assoc]

end VG.Proof.Ed448.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Verify.Body`. -/
section

/-!
# Ed448 verification on ARMv7: the challenge, the equation, and the body

`reduce_step`: `k`, the hash reduced modulo `L` by `vg_ed448_scalar_reduce`,
in the frame at `K`. `equation_step`: `vg_ed448_verify_equation`'s result,
for any code meeting its contract (`EqOk`, a hypothesis: only the
registration file imports the proof). `body_ok`: the whole body.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG.Proof.Ed448.Arm.Shake (Slot valid)

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Within Whole.FR Whole.call_ok)
open VG.Proof.Ed448.Arm (verifyEquationLocal scalarReduceLocal scalarReduce_ok)

/-- `vg_ed448_verify_equation` meets its contract. -/
abbrev EqOk : Prop := ∀ s, verifyEquationLocal.pre s →
  ∃ tr s', Exec isa Impl.Ed448.Arm.verifyEquation s tr s' ∧ abiPreserved s s' ∧ verifyEquationLocal.post s s'

/-- `vg_ed448_verify_equation` is constant time under its contract. -/
abbrev EqCT : Prop :=
  ConstantTime isa verifyEquationLocal.pre verifyEquationLocal.pub Impl.Ed448.Arm.verifyEquation

variable {L : VG.Proof.Ed448.Arm.Verify.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-! ## `vg_ed448_scalar_reduce` -/

theorem reduce_noFrames : Impl.Ed448.Arm.scalarReduce.noFrames = true := by lit_decide
theorem equation_noFrames : Impl.Ed448.Arm.verifyEquation.noFrames = true := by lit_decide

def kReg (L : VG.Proof.Ed448.Arm.Verify.Lay) : Region := ⟨State.addr L.E + BitVec.ofNat 64 K, 57⟩
def hReg (L : VG.Proof.Ed448.Arm.Verify.Lay) : Region := ⟨State.addr L.E + BitVec.ofNat 64 HASH, 114⟩

theorem kWithin (L : VG.Proof.Ed448.Arm.Verify.Lay) : Whole.Within (VG.Proof.Ed448.Arm.Verify.kReg L) L.FR := ⟨K, rfl, by change 160 + 57 ≤ 248; decide⟩
theorem hWithin (L : VG.Proof.Ed448.Arm.Verify.Lay) : Whole.Within (VG.Proof.Ed448.Arm.Verify.hReg L) L.FR := ⟨HASH, rfl, by change 40 + 114 ≤ 248; decide⟩

def ReduceArgs (L : VG.Proof.Ed448.Arm.Verify.Lay) (t : State) : Prop :=
  t.gpr .r0 = L.E + BitVec.ofNat 32 K ∧ t.gpr .r1 = L.E + BitVec.ofNat 32 HASH ∧ t.gpr .r2 = L.scr

theorem reduce_pre (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.ReduceArgs L t) :
    scalarReduceLocal.pre (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Verify.hReg L] [VG.Proof.Ed448.Arm.Verify.kReg L, L.SCR]) := by
  obtain ⟨h0, h1, h2⟩ := ha
  have e0 : (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Verify.hReg L] [VG.Proof.Ed448.Arm.Verify.kReg L, L.SCR]).gpr .r0 = L.E + BitVec.ofNat 32 K := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), h0]
  have e1 : (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Verify.hReg L] [VG.Proof.Ed448.Arm.Verify.kReg L, L.SCR]).gpr .r1 = L.E + BitVec.ofNat 32 HASH := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h1]
  have e2 : (t.callEntry.withRegions [VG.Proof.Ed448.Arm.Verify.hReg L] [VG.Proof.Ed448.Arm.Verify.kReg L, L.SCR]).gpr .r2 = L.scr := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h2]
  simp only [scalarReduceLocal]
  rw [e0, e1, e2, State.withRegions_rd, State.withRegions_wr, hL.kit.frame_addr (by decide), hL.kit.frame_addr (by decide)]
  refine ⟨rfl, rfl, Offset.disjoint _ (by decide) (by decide) (by decide),
    hL.kc.sub_left (Offset.sub_base _ (by decide : K + 57 ≤ 280)),
    hL.kc.sub_left (Offset.sub_base _ (by decide : HASH + 114 ≤ 280)),
    hL.kit.frame_fit (by decide), hL.kit.frame_fit (by decide), hL.nc⟩

theorem reduce_covers (L : VG.Proof.Ed448.Arm.Verify.Lay) : Covers ([VG.Proof.Ed448.Arm.Verify.hReg L] ++ [VG.Proof.Ed448.Arm.Verify.kReg L, L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inl (VG.Proof.Ed448.Arm.Verify.hWithin L)
  · exact .inl (VG.Proof.Ed448.Arm.Verify.kWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by simp⟩

theorem reduce_writes (L : VG.Proof.Ed448.Arm.Verify.Lay) : ∀ r ∈ [VG.Proof.Ed448.Arm.Verify.kReg L, L.SCR],
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inl (VG.Proof.Ed448.Arm.Verify.kWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by simp⟩

theorem reduce_step (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₀) :
    WP isa (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) t fun u =>
      VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ u ∧ Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.Verify.setup_ok hc hL ha
    (args := [(.r0, .frame K), (.r1, .frame HASH), (.r2, VG.Impl.Ed448.Arm.Verify.scr 0)]) (stk := [])
    (by decide) (by simp [valid, VG.Impl.Ed448.Arm.Verify.scr, SC, Slot, K, HASH]) (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .frame K) (by simp)
  have h1 := hs (.r1, .frame HASH) (by simp)
  have h2 := hs (.r2, VG.Impl.Ed448.Arm.Verify.scr 0) (by simp)
  simp only [VG.Proof.Ed448.Arm.Verify.argValue, VG.Impl.Ed448.Arm.Verify.scr, Lay.value, BitVec.add_zero] at h0 h1 h2
  have he : Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
      Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 :=
    Shake.bytes_setup hm (D := VG.Proof.Ed448.Arm.Verify.hReg L) (Offset.base_disjoint _ (by decide) (by decide)) (by change 114 ≤ 2 ^ 64; decide)
  refine Whole.call_ok hu scalarReduce_ok VG.Proof.Ed448.Arm.Verify.reduce_noFrames (VG.Proof.Ed448.Arm.Verify.reduce_pre hL ⟨h0, h1, h2⟩) (VG.Proof.Ed448.Arm.Verify.reduce_covers L)
    (VG.Proof.Ed448.Arm.Verify.reduce_writes L) fun v hv _ hp => ⟨hv, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (u.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 114) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h0, h1, hL.kit.frame_addr (by decide),
    hL.kit.frame_addr (by decide), he] at hp
  exact hp

/-! ## `vg_ed448_verify_equation` -/

def EqArgs (L : VG.Proof.Ed448.Arm.Verify.Lay) (t : State) : Prop :=
  t.gpr .r0 = L.pk ∧ t.gpr .r1 = L.sig ∧ t.gpr .r2 = L.E + BitVec.ofNat 32 K ∧ t.gpr .r3 = L.scr

theorem equation_pre (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.EqArgs L t) :
    verifyEquationLocal.pre (t.callEntry.withRegions [L.PK, L.SIG, VG.Proof.Ed448.Arm.Verify.kReg L] [L.SCR]) := by
  obtain ⟨h0, h1, h2, h3⟩ := ha
  have e : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [L.PK, L.SIG, VG.Proof.Ed448.Arm.Verify.kReg L] [L.SCR]).gpr r = t.gpr r :=
    fun r hr => by rw [State.withRegions_gpr, State.callEntry_gpr _ hr]
  simp only [verifyEquationLocal]
  rw [e .r0 (by decide), e .r1 (by decide), e .r2 (by decide), e .r3 (by decide), h0, h1, h2, h3,
    State.withRegions_rd, State.withRegions_wr, hL.kit.frame_addr (by decide)]
  exact ⟨rfl, rfl, hL.ps, hL.ss, hL.kc.sub_left (Offset.sub_base _ (by decide : K + 57 ≤ 280)), hL.np, hL.ns, hL.kit.frame_fit (by decide), hL.nc⟩

theorem equation_covers (L : VG.Proof.Ed448.Arm.Verify.Lay) :
    Covers ([L.PK, L.SIG, VG.Proof.Ed448.Arm.Verify.kReg L] ++ [L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr ⟨L.PK, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by simp⟩
  · exact .inr ⟨L.SIG, by simp [Lay.inputs], 0, (BitVec.add_zero _).symm, by simp⟩
  · exact .inl (VG.Proof.Ed448.Arm.Verify.kWithin L)
  · exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by simp⟩

theorem equation_writes (L : VG.Proof.Ed448.Arm.Verify.Lay) : ∀ r ∈ [L.SCR],
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨L.SCR, by simp [Lay.outputs], 0, (BitVec.add_zero _).symm, by simp⟩

/-- `1` if `b`, else `0`. -/
def signWord (b : Bool) : BitVec 32 := if b then 1 else 0

theorem equation_step (hv : VG.Proof.Ed448.Arm.Verify.EqOk) (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₀) :
    WP isa (callWith equationArgs "vg_ed448_verify_equation" Impl.Ed448.Arm.verifyEquation) t fun u =>
      VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ u ∧ u.gpr .r0 = VG.Proof.Ed448.Arm.Verify.signWord (Spec.Ed448.verifyEquation
        (Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57) (Spec.Ed448.bytesAt m₀ (State.addr L.sig) 114)
        (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.Verify.setup_ok hc hL ha
    (args := [(.r0, .caller 0 0), (.r1, .caller 5 0), (.r2, .frame K), (.r3, VG.Impl.Ed448.Arm.Verify.scr 0)]) (stk := [])
    (by decide) (by simp [valid, VG.Impl.Ed448.Arm.Verify.scr, SC, Slot, K]) (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 0 0) (by simp)
  have h1 := hs (.r1, .caller 5 0) (by simp)
  have h2 := hs (.r2, .frame K) (by simp)
  have h3 := hs (.r3, VG.Impl.Ed448.Arm.Verify.scr 0) (by simp)
  simp only [VG.Proof.Ed448.Arm.Verify.argValue, VG.Impl.Ed448.Arm.Verify.scr, Lay.value, BitVec.add_zero] at h0 h1 h2 h3
  have hk : Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
      Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57 :=
    Shake.bytes_setup hm (D := VG.Proof.Ed448.Arm.Verify.kReg L) (Offset.base_disjoint _ (by decide) (by decide)) (by change 57 ≤ 2 ^ 64; decide)
  have hpk : Spec.Ed448.bytesAt u.mem (State.addr L.pk) 57 = Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 :=
    hu.input_bytes hL (r := L.PK) (by simp [Lay.inputs]) (by change 57 ≤ 2 ^ 64; decide)
  have hsg : Spec.Ed448.bytesAt u.mem (State.addr L.sig) 114 = Spec.Ed448.bytesAt m₀ (State.addr L.sig) 114 :=
    hu.input_bytes hL (r := L.SIG) (by simp [Lay.inputs]) (by change 114 ≤ 2 ^ 64; decide)
  refine Whole.call_ok hu hv VG.Proof.Ed448.Arm.Verify.equation_noFrames (VG.Proof.Ed448.Arm.Verify.equation_pre hL ⟨h0, h1, h2, h3⟩) (VG.Proof.Ed448.Arm.Verify.equation_covers L)
    (VG.Proof.Ed448.Arm.Verify.equation_writes L) fun v hv' _ hp => ⟨hv', ?_⟩
  change v.gpr .r0 = if Spec.Ed448.verifyEquation
    (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r0)) 57)
    (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 114)
    (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r2)) 57) then 1 else 0 at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, hL.kit.frame_addr (by decide), hk] at hp
  rw [hp, hpk, hsg]
  rfl

/-! ## The body -/

theorem take57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem verify_of_len {pk ctx msg sig : List Byte} (h : ctx.length ≤ 255) :
    Spec.Ed448.verify pk ctx msg sig = Spec.Ed448.verifyEquation pk sig
      (Spec.Ed448.scalarReduce (Spec.Ed448.hash ctx (sig.take 57 ++ pk ++ msg))) := by
  unfold Spec.Ed448.verify
  simp only [h, decide_true, Bool.true_and]

/-- The result of verification with a context of fewer than 256 bytes. -/
theorem body_ok (hv : VG.Proof.Ed448.Arm.Verify.EqOk) (hc : VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₀) :
    WP isa body t fun u => VG.Proof.Ed448.Arm.Verify.Ctx L g m₀ u ∧ u.gpr .r0 = VG.Proof.Ed448.Arm.Verify.signWord (Spec.Ed448.verify
      (Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57)
      (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
      (Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat)
      (Spec.Ed448.bytesAt m₀ (State.addr L.sig) 114)) := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.Verify.hdr_ok hc hL ha) fun t1 ⟨hc1, hh⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.Verify.hash_ok hc1 hL ha hh) fun t2 ⟨hc2, hh2⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.Verify.reduce_step hc2 hL ha) fun t3 ⟨hc3, hk⟩ => ?_)
  refine WP.mono (VG.Proof.Ed448.Arm.Verify.equation_step hv hc3 hL ha) fun u ⟨hu, hr⟩ => ⟨hu, ?_⟩
  have hl : (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat).length ≤ 255 := by
    simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]; have := hL.cl; omega
  rw [hr, hk, hh2, VG.Proof.Ed448.Arm.Verify.verify_of_len hl, VG.Proof.Ed448.Arm.Verify.take57]

theorem body_noFrames : body.noFrames = true := by
  simp only [Impl.Ed448.Arm.Verify.body, Impl.Ed448.Arm.Verify.hash, Impl.Ed448.Arm.Shake.zeroState,
    Impl.Ed448.Arm.Shake.absorb, Impl.Ed448.Arm.Shake.pad, Impl.Ed448.Arm.Shake.squeeze, callWith,
    Code.noFrames, Bool.and_self]
  rw [PublicKey.absorb_noFrames, PublicKey.pad_noFrames, PublicKey.squeeze_noFrames, VG.Proof.Ed448.Arm.Verify.reduce_noFrames,
    VG.Proof.Ed448.Arm.Verify.equation_noFrames]
  rfl

end VG.Proof.Ed448.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Verify.CT`. -/
section

/-!
# Ed448 verification on ARMv7: constant time

As Ed25519's complete operations on this target, with the blocks and calls
of `Proof/Ed448/Arm/Shake/CT.lean`: two runs from the same pointers, lengths
and `sp` set up the same arguments for every call, each callee is constant
time under its own contract, and the blocks between the calls address
memory only through `sp`, `r12` and `scratch`. The positions the
absorptions return, which the next ones start from, depend only on the
lengths.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Impl.Ed448.Arm.Shake (firstArgs nextArgs absorb)
open VG.Proof.Ed25519.Arm (Whole.FR Whole.Within Whole.call_ok)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit argVal Two Slots valid_const valid_frame frame_within)
open VG.Proof.Ed448.Arm (verifyEquationLocal scalarReduceLocal scalarReduce_ok scalarReduce_ct)

variable {L : VG.Proof.Ed448.Arm.Verify.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

abbrev T2 (L : VG.Proof.Ed448.Arm.Verify.Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) :=
  Two L.E L.inputs L.outputs g₁ g₂ m₁ m₂ P

/-! ## The hash -/

/-- An absorption of input data at the position the previous one returned. -/
theorem input_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.Verify.Arguments L m₂) (P : Nat) (hP : P < 136)
    {src len : Value} (vs : valid 11 src) (vl : valid 11 len) {R : Region} (hR : R ∈ L.inputs)
    (hw : Whole.Within ⟨State.addr (argVal L.E L.value src), (argVal L.E L.value len).toNat⟩ R)
    (hfit : (argVal L.E L.value src).toNat + (argVal L.E L.value len).toNat ≤ 2 ^ 32) :
    RelCT isa (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs SC src len))
      (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argVal L.E L.value len).toNat) % 136)) :=
  hL.kit.next_ct ha hb (VG.Proof.Ed448.Arm.Verify.scr_at L) P hP vs vl (.inr ⟨R, List.mem_append_left _ hR, hw⟩)
    (hL.kit.data_input hR hw).1 hfit

theorem hash_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.Verify.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True) Impl.Ed448.Arm.Verify.hash (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  have hd' : argVal L.E L.value (.frame HDR) = L.E + BitVec.ofNat 32 HDR := rfl
  have hkn : (argVal L.E L.value (.const 10)).toNat = 10 := rfl
  have a1 := hk.first_ct (g₁ := g₁) (g₂ := g₂) ha hb (VG.Proof.Ed448.Arm.Verify.scr_at L) (src := .frame HDR) (len := .const 10)
    (valid_frame (by decide)) (valid_const (by decide))
    (by rw [hd', hkn, hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hd', hkn, hk.frame_addr (by decide)]; exact hk.frame_kWr (by decide))
    (by rw [hd', hkn]; exact hk.frame_fit (by decide))
  let P1 : Nat := (0 + (argVal L.E L.value (.const 10)).toNat) % 136
  have x2 := VG.Proof.Ed448.Arm.Verify.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 1 0)
    (len := .caller 2 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 2 0)).toNat) % 136
  have x3 := VG.Proof.Ed448.Arm.Verify.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P2 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.SIG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.ns; simp; omega)
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x4 := VG.Proof.Ed448.Arm.Verify.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 0 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.PK) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.np; simp; omega)
  let P4 : Nat := (P3 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x5 := VG.Proof.Ed448.Arm.Verify.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P4 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.MSG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nm)
  let P5 : Nat := (P4 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  exact (hk.zeroState_ct ha hb (VG.Proof.Ed448.Arm.Verify.scr_at L)).seq (a1.seq (x2.seq (x3.seq (x4.seq (x5.seq
    ((hk.padStep_ct ha hb (VG.Proof.Ed448.Arm.Verify.scr_at L) P5 (Nat.mod_lt _ (by decide))).seq
      (hk.sqzStep_ct ha hb (VG.Proof.Ed448.Arm.Verify.scr_at L) (by decide) (by decide))))))))

/-! ## The challenge and the equation -/

theorem reduce_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.Verify.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
      (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  let args : List (Reg × Value) := [(.r0, .frame K), (.r1, .frame HASH), (.r2, VG.Impl.Ed448.Arm.Verify.scr 0)]
  have get : ∀ t, Slots L.E L.value args [] t → VG.Proof.Ed448.Arm.Verify.ReduceArgs L t := by
    intro t hs
    have h0 := hs.1 (.r0, .frame K) (by simp [args])
    have h1 := hs.1 (.r1, .frame HASH) (by simp [args])
    have h2 := hs.1 (.r2, VG.Impl.Ed448.Arm.Verify.scr 0) (by simp [args])
    simp only [argVal, VG.Impl.Ed448.Arm.Verify.scr, SC, Lay.value, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  refine (hL.kit.setup_ct ha hb args [] (by decide) (by simp [args, valid, VG.Impl.Ed448.Arm.Verify.scr, SC, Slot, K, HASH])
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct scalarReduce_ok scalarReduce_ct
    (fun t _ h => ⟨[VG.Proof.Ed448.Arm.Verify.hReg L], [VG.Proof.Ed448.Arm.Verify.kReg L, L.SCR], VG.Proof.Ed448.Arm.Verify.reduce_pre hL (get t h), VG.Proof.Ed448.Arm.Verify.reduce_covers L, VG.Proof.Ed448.Arm.Verify.reduce_writes L⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hsp, hg (.r0, .frame K) (by simp [args]), hg (.r1, .frame HASH) (by simp [args]),
      hg (.r2, VG.Impl.Ed448.Arm.Verify.scr 0) (by simp [args])⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc scalarReduce_ok VG.Proof.Ed448.Arm.Verify.reduce_noFrames (VG.Proof.Ed448.Arm.Verify.reduce_pre hL (get t hs)) (VG.Proof.Ed448.Arm.Verify.reduce_covers L)
      (VG.Proof.Ed448.Arm.Verify.reduce_writes L) fun v hv _ _ => ⟨hv, trivial⟩

theorem equation_ct (hv : VG.Proof.Ed448.Arm.Verify.EqOk) (hct : VG.Proof.Ed448.Arm.Verify.EqCT) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.Verify.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith equationArgs "vg_ed448_verify_equation" Impl.Ed448.Arm.verifyEquation)
      (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  let args : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .caller 5 0), (.r2, .frame K), (.r3, VG.Impl.Ed448.Arm.Verify.scr 0)]
  have get : ∀ t, Slots L.E L.value args [] t → VG.Proof.Ed448.Arm.Verify.EqArgs L t := by
    intro t hs
    have h0 := hs.1 (.r0, .caller 0 0) (by simp [args])
    have h1 := hs.1 (.r1, .caller 5 0) (by simp [args])
    have h2 := hs.1 (.r2, .frame K) (by simp [args])
    have h3 := hs.1 (.r3, VG.Impl.Ed448.Arm.Verify.scr 0) (by simp [args])
    simp only [argVal, VG.Impl.Ed448.Arm.Verify.scr, SC, Lay.value, BitVec.add_zero] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩
  refine (hL.kit.setup_ct ha hb args [] (by decide) (by simp [args, valid, VG.Impl.Ed448.Arm.Verify.scr, SC, Slot, K])
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct hv hct
    (fun t _ h => ⟨[L.PK, L.SIG, VG.Proof.Ed448.Arm.Verify.kReg L], [L.SCR], VG.Proof.Ed448.Arm.Verify.equation_pre hL (get t h), VG.Proof.Ed448.Arm.Verify.equation_covers L,
      VG.Proof.Ed448.Arm.Verify.equation_writes L⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hg (.r0, .caller 0 0) (by simp [args]), hg (.r1, .caller 5 0) (by simp [args]),
      hg (.r2, .frame K) (by simp [args]), hg (.r3, VG.Impl.Ed448.Arm.Verify.scr 0) (by simp [args]), hsp⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc hv VG.Proof.Ed448.Arm.Verify.equation_noFrames (VG.Proof.Ed448.Arm.Verify.equation_pre hL (get t hs)) (VG.Proof.Ed448.Arm.Verify.equation_covers L)
      (VG.Proof.Ed448.Arm.Verify.equation_writes L) fun v hv' _ _ => ⟨hv', trivial⟩

/-! ## The body -/

theorem body_ct (hv : VG.Proof.Ed448.Arm.Verify.EqOk) (hct : VG.Proof.Ed448.Arm.Verify.EqCT) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.Verify.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.Verify.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True) body (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have h : RelCT isa (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True) (.block hdr) (VG.Proof.Ed448.Arm.Verify.T2 L g₁ g₂ m₁ m₂ fun _ => True) :=
    (hL.kit.hdr_ct (g₁ := g₁) (g₂ := g₂) ha hb (j := 2) (off := HDR) (by decide) hL.cl (by decide)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩)
  exact h.seq ((VG.Proof.Ed448.Arm.Verify.hash_ct hL ha hb).seq ((VG.Proof.Ed448.Arm.Verify.reduce_ct hL ha hb).seq (VG.Proof.Ed448.Arm.Verify.equation_ct hv hct hL ha hb)))

end VG.Proof.Ed448.Arm.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Verify.Entry`. -/
section

/-!
# Ed448 verification on ARMv7: the contract, and the frame

`verifyLocal`, the contract the proof is written against; `inner_ok`, the
frame (`Whole.wrap_ok`) around the body for a context of fewer than 256
bytes; `verify_ok`, the whole function, with the check of the context's
length before it.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.base_addr Whole.base_top Whole.stack Whole.Saved Whole.entered
  Whole.saved_ctx Whole.saved_words Whole.saved_frame Whole.bodyRd Whole.bodyWr Whole.wrap_ok
  Whole.originalWord Whole.Ctx)
open VG.Proof.X25519.Arm (op2_lsr op2_imm)

/-- `vg_ed448_verify(pk = r0, context = r1, ctxlen = r2, message = r3, len = [sp],
signature = [sp, #4], scratch = [sp, #8]) -> r0`, with 280 bytes of stack. -/
def verifyLocal : Contract isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 57⟩
    let ctx : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let msg : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let sig : Region := ⟨State.addr (stackArg s 1), 114⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 8192⟩
    let args : Region := ⟨State.addr s.sp, 12⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [pk, ctx, msg, sig, args] ∧ s.wr = [scr] ∧
      pk.Disjoint scr ∧ ctx.Disjoint scr ∧ msg.Disjoint scr ∧ sig.Disjoint scr ∧ args.Disjoint scr ∧
      stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 114 ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s t := t.gpr .r0 = VG.Proof.Ed448.Arm.Verify.signWord (Spec.Ed448.verify
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r0)) 57)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (stackArg s 1)) 114))
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧
    stackArg s 2 = stackArg t 2

def lay (s : State) : VG.Proof.Ed448.Arm.Verify.Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, stackArg s 2, Whole.base s⟩

section
variable {s : State} (h : verifyLocal.pre s)
include h

theorem entry_below : 280 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem entry_top : s.sp.toNat + 12 ≤ 2 ^ 32 := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem original_args : (VG.Proof.Ed448.Arm.Verify.lay s).ORIG = ⟨State.addr s.sp, 12⟩ := by
  unfold Lay.ORIG VG.Proof.Ed448.Arm.Verify.lay
  rw [Whole.base_addr (VG.Proof.Ed448.Arm.Verify.entry_below h)]
  congr 1
  rw [show (280 : Addr) = BitVec.ofNat 64 280 from rfl, BitVec.sub_add_cancel]

theorem stack_eq : Whole.stack s = ⟨State.addr s.sp - 280, 280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr (VG.Proof.Ed448.Arm.Verify.entry_below h)]

theorem entry_writes : ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  intro r hr
  rw [h.2.1, List.mem_singleton] at hr
  subst r
  rw [VG.Proof.Ed448.Arm.Verify.stack_eq h]
  exact h.2.2.2.2.2.2.2.2.2.2.2.1

theorem lay_ok (hl : (s.gpr .r2).toNat < 256) : (VG.Proof.Ed448.Arm.Verify.lay s).Ok := by
  have hb := VG.Proof.Ed448.Arm.Verify.entry_below h
  have ht := VG.Proof.Ed448.Arm.Verify.entry_top h
  have ho := VG.Proof.Ed448.Arm.Verify.original_args h
  have hs : (VG.Proof.Ed448.Arm.Verify.lay s).STK = ⟨State.addr s.sp - 280, 280⟩ := by
    unfold Lay.STK; rw [show State.addr (VG.Proof.Ed448.Arm.Verify.lay s).E = State.addr (Whole.base s) from rfl, Whole.base_addr hb]
  obtain ⟨_, _, ps, xs, ms, ss, os, kp, kx, km, ks, kc, np, nx, nm, ns, nc, _, _⟩ := h
  refine ⟨?_, hl, ps, xs, ms, ss, by rw [ho]; exact os, by rw [hs]; exact kp, by rw [hs]; exact kx,
    by rw [hs]; exact km, by rw [hs]; exact ks, by rw [hs]; exact kc, np, nx, nm, ns, nc⟩
  have := Whole.base_top hb
  change (Whole.base s).toNat + 292 ≤ 2 ^ 32
  omega

theorem entry_regions : (VG.Proof.Ed448.Arm.Verify.lay s).inputs = Whole.bodyRd s ∧ (VG.Proof.Ed448.Arm.Verify.lay s).outputs = s.wr := by
  simp only [Lay.inputs, VG.Proof.Ed448.Arm.Verify.original_args h]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1, Lay.PK, Lay.CTX, Lay.MSG, Lay.SIG, Lay.SCR, Lay.ARGS,
    VG.Proof.Ed448.Arm.Verify.lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_ctx {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    VG.Proof.Ed448.Arm.Verify.Ctx (VG.Proof.Ed448.Arm.Verify.lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (VG.Proof.Ed448.Arm.Verify.lay s).inputs (VG.Proof.Ed448.Arm.Verify.lay s).outputs _
  rw [(VG.Proof.Ed448.Arm.Verify.entry_regions h).1, (VG.Proof.Ed448.Arm.Verify.entry_regions h).2]
  exact hc

theorem entry_args {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : VG.Proof.Ed448.Arm.Verify.Arguments (VG.Proof.Ed448.Arm.Verify.lay s) p.mem := by
  have hb := VG.Proof.Ed448.Arm.Verify.entry_below h
  have ht := VG.Proof.Ed448.Arm.Verify.entry_top h
  intro j hj
  obtain ⟨hj11, hj | hj⟩ := hj
  · have hw := Whole.saved_words hb (by decide : 6 ≤ 6) (by omega) hp hj
    have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
        Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, BitVec.add_zero, Lay.value, VG.Proof.Ed448.Arm.Verify.lay, stackArg, stackArgAddr] using hw
  · obtain rfl : j = 10 := by omega
    have hf := Whole.saved_frame hb hp
    have hbt := Whole.base_top hb
    have ea : State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10) = State.addr (s.sp + BitVec.ofNat 32 8) := by
      rw [addr_add (by omega), Whole.base_addr hb, show (248 + 4 * 10 : Nat) = 280 + 8 from rfl,
        ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, show (280 : Addr) = BitVec.ofNat 64 280 from rfl,
        BitVec.sub_add_cancel]
    change p.mem.readW (State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10)) 32 = stackArg s 2
    rw [hf.readW (r := ⟨State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * 10), 4⟩) (Region.contains_self _ _)
      (by
        rintro r hr
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint_base _ (by omega) (by omega)) (by decide), ea]
    rfl

theorem entry_read : ∀ j < 6, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4 := by
  have ht := VG.Proof.Ed448.Arm.Verify.entry_top h
  intro j hj h4
  have hj' : j = 4 ∨ j = 5 := by omega
  refine ⟨⟨State.addr s.sp, 12⟩, List.mem_append_left _ (by rw [h.1]; simp), ?_⟩
  rw [addr_add (by have := s.sp.isLt; omega)]
  exact Offset.contains_base _ (d := 4 * (j - 4)) (by omega) (by omega)

theorem entry_input {m : Mem} (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd)
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m r.base r.len = Spec.Ed448.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR, VG.Proof.Ed448.Arm.Verify.stack_eq h]
  obtain ⟨hrd, _, _, _, _, _, _, kp, kx, km, ks, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact kp.symm
  · exact kx.symm
  · exact km.symm
  · exact ks.symm
  · exact Offset.base_disjoint_below _ (n := 280) (k := 12) (by decide)

end

/-- The frame around the body, for a context of fewer than 256 bytes. -/
theorem inner_ok (hv : VG.Proof.Ed448.Arm.Verify.EqOk) {s : State} (h : verifyLocal.pre s) (hl : (s.gpr .r2).toNat < 256) :
    WP isa (wrap 6 body) s fun u => abiPreserved s u ∧ verifyLocal.post s u := by
  have hw := Whole.wrap_ok VG.Proof.Ed448.Arm.Verify.body_noFrames (by decide : 6 ≤ 6) (VG.Proof.Ed448.Arm.Verify.entry_below h)
    (by have := VG.Proof.Ed448.Arm.Verify.entry_top h; omega) (VG.Proof.Ed448.Arm.Verify.entry_read h) (VG.Proof.Ed448.Arm.Verify.entry_writes h)
    (P := fun m _ r => r = VG.Proof.Ed448.Arm.Verify.signWord (Spec.Ed448.verify
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r0)) 57)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
      (Spec.Ed448.bytesAt m (State.addr (stackArg s 1)) 114)))
    (fun p hp => WP.mono (VG.Proof.Ed448.Arm.Verify.body_ok hv (VG.Proof.Ed448.Arm.Verify.entry_ctx h hp) (VG.Proof.Ed448.Arm.Verify.lay_ok h hl) (VG.Proof.Ed448.Arm.Verify.entry_args h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (VG.Proof.Ed448.Arm.Verify.lay s).inputs (VG.Proof.Ed448.Arm.Verify.lay s).outputs u at hu
        rw [(VG.Proof.Ed448.Arm.Verify.entry_regions h).1, (VG.Proof.Ed448.Arm.Verify.entry_regions h).2] at hu
        exact hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have e0 := VG.Proof.Ed448.Arm.Verify.entry_input h hf (r := ⟨State.addr (s.gpr .r0), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  have e1 := VG.Proof.Ed448.Arm.Verify.entry_input h hf (r := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩) (by rw [h.1]; simp)
    (by change (s.gpr .r2).toNat ≤ 2 ^ 64; have := (s.gpr .r2).isLt; omega)
  have e3 := VG.Proof.Ed448.Arm.Verify.entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 0).toNat ≤ 2 ^ 64; have := (stackArg s 0).isLt; omega)
  have e5 := VG.Proof.Ed448.Arm.Verify.entry_input h hf (r := ⟨State.addr (stackArg s 1), 114⟩) (by rw [h.1]; simp)
    (by change 114 ≤ 2 ^ 64; decide)
  change u.gpr .r0 = _
  rw [hp]
  simp only at e0 e1 e3 e5
  rw [e0, e1, e3, e5]

/-- The check of the context's length: `r12 = ctxlen >> 8`, and Z set exactly when it is 0. -/
def checked (s : State) : State :=
  subFlags (s.setReg .r12 (s.gpr .r2 >>> 8)) (s.gpr .r2 >>> 8) 0

theorem check_exec (s : State) : WP isa (.block check) s fun u => u = VG.Proof.Ed448.Arm.Verify.checked s :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg .r12 (s.gpr .r2 >>> 8))
    (by simp only [exec]; rw [op2_lsr (by decide)]; rfl)
    (VG.Proof.X25519.Arm.WP.cons (s' := VG.Proof.Ed448.Arm.Verify.checked s)
      (by simp only [exec]; rw [op2_imm (v := 0) (by decide)]; rfl)
      (WP.block_nil rfl))

theorem checked_pre {s : State} (h : verifyLocal.pre s) : verifyLocal.pre (VG.Proof.Ed448.Arm.Verify.checked s) := h
theorem checked_post {s u : State} (h : verifyLocal.post (VG.Proof.Ed448.Arm.Verify.checked s) u) : verifyLocal.post s u := h
theorem checked_abi {s u : State} (h : abiPreserved (VG.Proof.Ed448.Arm.Verify.checked s) u) : abiPreserved s u := by
  refine ⟨fun r hr => (h.1 r hr).trans ?_, h.2⟩
  have : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
  exact RegUpd.gpr_setReg_of_ne _ _ this

theorem checked_z (s : State) : (VG.Proof.Ed448.Arm.Verify.checked s).z = (s.gpr .r2 >>> 8 - 0 == 0) := rfl

theorem shr8_eq_zero {x : BitVec 32} : (x >>> 8 - 0 == 0) = decide (x.toNat < 256) := by
  show (x >>> 8 - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  by_cases h : x.toNat < 256
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.X25519.Arm.toNat_shr]; simp; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    have := congrArg BitVec.toNat e
    rw [VG.Proof.X25519.Arm.toNat_shr] at this; simp at this; omega

theorem verify_ok (hv : VG.Proof.Ed448.Arm.Verify.EqOk) {s : State} (h : verifyLocal.pre s) :
    WP isa VG.Impl.Ed448.Arm.Verify.code s fun u => abiPreserved s u ∧ verifyLocal.post s u := by
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.Verify.check_exec s) fun u hu => ?_)
  subst hu
  refine WP.ite (decide ((s.gpr .r2).toNat < 256))
    (by rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.Ed448.Arm.Verify.checked_z, VG.Proof.Ed448.Arm.Verify.shr8_eq_zero]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.mono (VG.Proof.Ed448.Arm.Verify.inner_ok hv (VG.Proof.Ed448.Arm.Verify.checked_pre h) (of_decide_eq_true hb)) fun u ⟨ha, hp⟩ =>
      ⟨VG.Proof.Ed448.Arm.Verify.checked_abi ha, VG.Proof.Ed448.Arm.Verify.checked_post hp⟩
  · refine VG.Proof.X25519.Arm.wp_movw fun u vu => WP.block_nil ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
      have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
      rw [vu.other r h0]
      exact RegUpd.gpr_setReg_of_ne _ _ h12
    · rw [vu.sp]; rfl
    · change u.gpr .r0 = _
      rw [vu.gpr]
      have hl : ¬ (s.gpr .r2).toNat < 256 := by simpa using hb
      have hlen : ¬ (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat).length ≤ 255 := by
        simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range]; omega
      simp only [Spec.Ed448.verify, hlen, decide_false, Bool.false_and, VG.Proof.Ed448.Arm.Verify.signWord]
      rfl

end VG.Proof.Ed448.Arm.Verify

end

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.Verify.Verified`. -/
section

/-!
# Ed448 verification on ARMv7: constant time, and `Verified`

`verify_ct`: the check of the context's length leaks nothing and branches
on a length; the frame around the body is constant time (`inner_ct`, from
`body_ct`). `verify_verified`: against `Spec.Ed448.verifyContract Arm.abi
280`, for any code of `vg_ed448_verify_equation` meeting its contract
(`EqOk`, `EqCT`): the registration file passes its own.
-/

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.wrap_ct Whole.bodyRd Whole.bodyWr Whole.quiet_block_ct)

theorem lay_eq {s t : State} (hp : verifyLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, a0, a1, a2⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, a0, a1, a2]

/-- The frame around the body is constant time, for a context of fewer than 256 bytes. -/
theorem inner_ct (hv : EqOk) (hct : EqCT) :
    ConstantTime isa (fun s => verifyLocal.pre s ∧ (s.gpr .r2).toNat < 256) verifyLocal.pub (wrap 6 body) := by
  refine Whole.wrap_ct (by decide : 6 ≤ 6) (fun _ _ hp => hp.1) (fun _ hs => entry_below hs.1)
    (fun _ hs => by have := entry_top hs.1; omega) (fun _ hs => entry_read hs.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed448.Arm.Verify.body_ok hv (entry_ctx hs.1 hp) (lay_ok hs.1 hs.2) (entry_args hs.1 hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht.1 hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht.1 hqb
    exact ⟨(body_ct hv hct (lay_ok hs.1 hs.2) (entry_args hs.1 hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs.1 hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

theorem checked_pub {s t : State} (h : verifyLocal.pub s t) : verifyLocal.pub (checked s) (checked t) := h

theorem checked_lt {s : State} (h : isa.eval .eq (checked s) = some true) : (s.gpr .r2).toNat < 256 := by
  rw [VG.Proof.X25519.Arm.eval_eq, checked_z, shr8_eq_zero] at h
  exact of_decide_eq_true (Option.some.inj h)

theorem verify_ct (hv : EqOk) (hct : EqCT) : ConstantTime isa verifyLocal.pre verifyLocal.pub VG.Impl.Ed448.Arm.Verify.code := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  unfold VG.Impl.Ed448.Arm.Verify.code
  have hblk := ((Whole.quiet_block_ct check (by
      intro i hi s
      simp only [check, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> rfl)).mono
    (P' := fun s₁ s₂ => verifyLocal.pre s₁ ∧ verifyLocal.pre s₂ ∧ verifyLocal.pub s₁ s₂)
    (fun _ _ h => h.2.2.1) (fun _ _ _ => trivial)).wpDep (F := fun σ s' => s' = checked σ)
      (fun s₁ s₂ _ => ⟨check_exec s₁, check_exec s₂⟩)
  refine RelCT.seq hblk (RelCT.ite ?_ ?_ ?_)
  · rintro _ _ ⟨_, σ₁, σ₂, hp, rfl, rfl⟩
    rw [VG.Proof.X25519.Arm.eval_eq, VG.Proof.X25519.Arm.eval_eq, checked_z, checked_z, hp.2.2.2.2.2.1]
  · rintro _ _ t₁ t₂ s₁' s₂' ⟨⟨_, σ₁, σ₂, hp, rfl, rfl⟩, hev⟩ e₁ e₂
    have l₁ := checked_lt hev
    have l₂ : (σ₂.gpr .r2).toNat < 256 := hp.2.2.2.2.2.1 ▸ l₁
    exact ⟨inner_ct hv hct _ _ _ _ _ _ ⟨checked_pre hp.1, l₁⟩ ⟨checked_pre hp.2.1, l₂⟩
      (checked_pub hp.2.2) e₁ e₂, trivial⟩
  · refine ((Whole.quiet_block_ct [.movw .r0 0] (by
      intro i hi s
      rw [List.mem_singleton.mp hi]; rfl)).mono ?_ (fun _ _ _ => trivial))
    rintro _ _ ⟨⟨_, σ₁, σ₂, hp, rfl, rfl⟩, _⟩
    exact hp.2.2.1

/-! ## The contract -/

def verifySatState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0 | .r3 => 0x3000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9005 then 0x50 else if a = 0x900A then 0x01 else 0
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x5000, 114⟩, ⟨0x9000, 12⟩]
  wr := [⟨0x10000, 8192⟩]

private theorem argAddr_zero (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

private theorem pre_bridge (s : State) (h : (Spec.Ed448.verifyContract Arm.abi 280).pre s) :
    verifyLocal.pre s := by
  sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
    Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
  sig_split h
  sig_reduce [verifyLocal, Arm.State.addr]
  sig_simp [argAddr_zero, Arm.State.addr] [] at *
  simp only [Arm.State.addr, show (280#64) = (280 : Addr) from rfl] at *
  sig_and_intros
  all_goals first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›

theorem verify_implies : verifyLocal.Implies (Spec.Ed448.verifyContract Arm.abi 280) where
  pre := pre_bridge
  post s t _ h := by
    sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    rw [BitVec.setWidth_append_eq_right]
    exact h
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at h
    obtain ⟨sp, _, h0, h1, h2, h3, a0, a1, a2⟩ := h
    exact ⟨sp, h0, h1, h2, h3, a0, a1, a2⟩
  sat := by
    refine ⟨verifySatState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
        Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, verifySatState]
      decide +kernel

/-- `vg_ed448_verify` on ARMv7, for any code of `vg_ed448_verify_equation`
meeting its contract. -/
theorem verify_verified (hv : EqOk) (hct : EqCT) :
    Verified Arm.target VG.Impl.Ed448.Arm.Verify.code (Spec.Ed448.verifyContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verify_ok hv h) (verify_ct hv hct) (.refl verify_implies.sat_left))
    verify_implies

end VG.Proof.Ed448.Arm.Verify

end
