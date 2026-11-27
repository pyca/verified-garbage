module

public import VerifiedGarbage.Impl.Ed448.Arm.Verify
import VerifiedGarbage.Proof.Ed448.Arm.Shake.Header
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Ed448.Arm.Shake.Sponge
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Hash
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ed448.Arm.Shake.Layout

/-! ### `Ed448.Arm.Verify.Layout`, which this module and modules that import it used -/

section

/-!
# Ed448 verification on ARMv7: the layout

The frame is Ed25519's on this target (`Proof/Ed25519/Arm/Whole`): `Ctx`
holds between the frame's entry and its exit. `Lay` names the arguments and
the frame's base `E`; the inputs are the buffers, the caller's stack
arguments (`ORIG`, which hold `scratch`) and the saved arguments, and the
only output is `scratch`. `setup_ok` sets a call's arguments from them.
-/

@[expose] public section

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
variable (L : Lay)
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

abbrev Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

/-- The saved words, and `scratch` where the caller put it. -/
def Arguments (L : Lay) (m : Mem) : Prop :=
  ∀ j, Slot 11 j → m.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 = L.value j

def argValue (L : Lay) : Value → BitVec 32
  | .const n => BitVec.ofNat 32 n
  | .frame d => L.E + BitVec.ofNat 32 d
  | .caller j d => L.value j + BitVec.ofNat 32 d

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem frame_sub (L : Lay) : Region.Sub L.FR L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

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
    · exact hL.kc.sub_left (args_sub L)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hL.kp.sub_left (frame_sub L)).symm
    · exact (hL.kx.sub_left (frame_sub L)).symm
    · exact (hL.km.sub_left (frame_sub L)).symm
    · exact (hL.ks.sub_left (frame_sub L)).symm
    · exact Offset.disjoint_base _ (by decide : 248 ≤ 280) (by decide)
    · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

theorem Ctx.input_bytes (hc : Ctx L g m₀ t) (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs)
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt t.mem r.base r.len = Spec.Ed448.bytesAt m₀ r.base r.len := by
  unfold Spec.Ed448.bytesAt
  exact List.map_congr_left fun i hi =>
    hc.frame.bytes (R := r) (hL.inputs_out hr) hn (List.mem_range.mp hi)

theorem slot_mem (L : Lay) {j : Nat} (hj : Slot 11 j) :
    ∃ R ∈ L.inputs, R.Contains (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
  obtain ⟨hj11, hj | hj⟩ := hj
  · exact ⟨L.ARGS, by simp [Lay.inputs],
      Offset.contains _ (e := 248) (k := 24) (by omega_using []) (by omega_using [hj]) (by decide)⟩
  · exact ⟨L.ORIG, by simp [Lay.inputs],
      Offset.contains _ (e := 280) (k := 12) (by omega_using [hj]) (by omega_using [hj11]) (by decide)⟩

theorem Ctx.arg_word (hc : Ctx L g m₀ t) (hL : L.Ok) {j : Nat} (hj : Slot 11 j) :
    t.mem.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 =
      m₀.readW (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 32 := by
  obtain ⟨R, hR, hcon⟩ := slot_mem L hj
  exact hc.frame.readW (r := R) hcon (hL.inputs_out hR) (by decide)

theorem value_eq (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {v : Value} (hv : valid 11 v) : Whole.value L.E t.mem v = argValue L v := by
  cases v with
  | const => rfl
  | frame => rfl
  | caller j d =>
    simp only [Whole.value, argValue]
    rw [hc.arg_word hL hv.1, ha j hv.1]

theorem setup_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀)
    {args : List (Reg × Value)} {stk : List Value} (hn : (args.map Prod.fst).Nodup)
    (hv : ∀ p ∈ args, valid 11 p.2) (hr : ∀ p ∈ args, p.1 ∉ preserved)
    (hs : stk.length ≤ 6) (hvs : ∀ v ∈ stk, valid 11 v) :
    WP isa (.block (setup args stk)) t fun u => Ctx L g m₀ u ∧
      Frame [⟨State.addr L.E, 24⟩] t.mem u.mem ∧
      (∀ p ∈ args, u.gpr p.1 = argValue L p.2) ∧
      (∀ j (hj : j < stk.length), stackArg u j = argValue L (stk[j]'hj)) ∧
      (∀ r, r ∉ args.map Prod.fst → r ≠ .r0 → r ≠ .r12 → u.gpr r = t.gpr r) := by
  have hE : Fits L.E 11 := ⟨by decide, by decide, by have := hL.top; omega_using [this]⟩
  refine WP.mono (Ctx.setup hc hE hn hv hs hvs
    (fun j hj => let ⟨R, hR, hcon⟩ := slot_mem L hj; ⟨R, hR, hcon⟩) hr)
    fun u ⟨hu, hm, hregs, hstk, hk⟩ => ⟨hu, Frame.sub hm fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [hs])⟩, ?_, ?_, hk⟩
  · intro p hp
    rw [hregs p hp, value_eq hc hL ha (hv p hp)]
  · intro j hj
    rw [hstk j hj, value_eq hc hL ha (hvs _ (List.getElem_mem hj))]

/-- What the calls need of the layout (`Proof/Ed448/Arm/Shake/Layout.lean`). -/
theorem Lay.Ok.kit (hL : L.Ok) : Kit L.E L.scr 11 L.inputs L.outputs :=
  ⟨⟨by decide, by decide, by have := hL.top; omega_using [this]⟩, hL.nc, by simp [Lay.outputs], hL.kc,
    fun _ hr R hR => hL.inputs_out hr R hR, fun _ hj => slot_mem L hj⟩

end VG.Proof.Ed448.Arm.Verify

end

end

/-! ### `Ed448.Arm.Verify.Header`, which only this module used -/

section

/-!
# Ed448 verification on ARMv7: the header of `dom4`

`hdr_ok`: the block `hdr` leaves `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten
bytes of `dom4(0, context)`, in the frame at `HDR` (`Shake.Kit.hdr_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.Arm.Verify

open VG VG.Arm VG.Impl.Ed448.Arm.Verify VG.Impl.Ed25519.Arm.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctxlen`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : Lay) : List Byte :=
  "SigEd448".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem hdr_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (.block hdr) t fun u => Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L :=
  WP.mono (hL.kit.hdr_ok hc ha (j := 2) (by decide) hL.cl (by decide)) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩

end VG.Proof.Ed448.Arm.Verify

end

end


/-!
# Ed448 verification on ARMv7: the hash

`hash_ok`: `H(dom4(0, context) ‖ R ‖ A ‖ M)` in the frame at `HASH`, from
the header the frame holds (`hdr_ok`), with the calls of
`Proof/Ed448/Arm/Shake/Sponge.lean`: the Keccak state zeroed, the header,
the context, `R`, `A` and the message absorbed each from where the previous
absorption stopped, the padding absorbed, and 114 bytes squeezed.
-/

@[expose] public section

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
  have ex := hk.input_bytes hc2 rx (whole _) (by change L.ctxLen.toNat ≤ 2 ^ 64; have := L.ctxLen.isLt; omega_using [])
  simp only at ex
  rw [ex] at hr3 hp3
  -- `R`.
  refine WP.seq (WP.mono (hk.nextAt hc3 ha (scr_at L) (src := .caller 5 0) (len := .const 57) (P := L.sig)
    (N := 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl cs ds as
    (by have := hL.ns; omega_using [this]) hr3 hp3) fun t4 ⟨hc4, _, hr4, hp4⟩ => ?_)
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
  have em := hk.input_bytes hc5 rm (whole _) (by change L.len.toNat ≤ 2 ^ 64; have := L.len.isLt; omega_using [])
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
