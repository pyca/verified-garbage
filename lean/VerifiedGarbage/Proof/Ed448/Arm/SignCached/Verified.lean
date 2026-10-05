import VerifiedGarbage.Impl.Ed448.Arm.SignCached
import VerifiedGarbage.Proof.Ed448.Arm.Shake.CT
import VerifiedGarbage.Proof.Ed448.Arm.PublicKey.Verified
import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed448.Arm.BaseVerified
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Arm.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.SignCached.Layout`. -/
section

/-!
# Ed448 signing with a cached public key on ARMv7: the layout

The frame is Ed25519's on this target (`Proof/Ed25519/Arm/Whole`): `Ctx`
holds between the frame's entry and its exit. `Lay` names the arguments and
the frame's base `E`; the inputs are the private key, the public key, the
context, the message, the caller's stack arguments (`ORIG`, which hold
`len` and `scratch`) and the saved arguments, and the outputs are `out` and
`scratch`. `Lay.Ok.kit` gives the calls what they need of it
(`Proof/Ed448/Arm/Shake`), with the eight arguments' words (`Slot 12`).

`fr d l` is the region of `l` bytes of the frame at `d`, and `ob o l` that
of `out` at `o`; `Away` regions are outside everything a call of a sponge
function writes.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.ARGS Whole.Within)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit Args argVal kWr kArgs kWr_sub sqzWr)

structure Lay where
  out : BitVec 32
  seed : BitVec 32
  pk : BitVec 32
  ctx : BitVec 32
  ctxLen : BitVec 32
  msg : BitVec 32
  len : BitVec 32
  scr : BitVec 32
  E : BitVec 32

namespace Lay
variable (L : VG.Proof.Ed448.Arm.SignCached.Lay)
abbrev OUT : Region := ⟨State.addr L.out, 114⟩
abbrev SEED : Region := ⟨State.addr L.seed, 57⟩
abbrev PK : Region := ⟨State.addr L.pk, 57⟩
abbrev CTX : Region := ⟨State.addr L.ctx, L.ctxLen.toNat⟩
abbrev MSG : Region := ⟨State.addr L.msg, L.len.toNat⟩
abbrev SCR : Region := ⟨State.addr L.scr, 8192⟩
abbrev ARGS : Region := Whole.ARGS L.E
abbrev ORIG : Region := ⟨State.addr L.E + BitVec.ofNat 64 280, 16⟩
abbrev STK : Region := ⟨State.addr L.E, 280⟩
def inputs : List Region := [L.SEED, L.PK, L.CTX, L.MSG, L.ORIG, L.ARGS]
def outputs : List Region := [L.OUT, L.SCR]
def value (j : Nat) : BitVec 32 :=
  match j with
  | 0 => L.out | 1 => L.seed | 2 => L.pk | 3 => L.ctx | 4 => L.ctxLen | 5 => L.msg | 10 => L.len
  | _ => L.scr
/-- The frame's bytes at `d`, and `out`'s at `o`. -/
abbrev fr (d l : Nat) : Region := ⟨State.addr L.E + BitVec.ofNat 64 d, l⟩
abbrev ob (o l : Nat) : Region := ⟨State.addr L.out + BitVec.ofNat 64 o, l⟩
structure Ok : Prop where
  top : L.E.toNat + 296 ≤ 2 ^ 32
  cl : L.ctxLen.toNat < 256
  oc : L.OUT.Disjoint L.SCR
  eo : L.SEED.Disjoint L.OUT
  ec : L.SEED.Disjoint L.SCR
  po : L.PK.Disjoint L.OUT
  pc : L.PK.Disjoint L.SCR
  xo : L.CTX.Disjoint L.OUT
  xc : L.CTX.Disjoint L.SCR
  mo : L.MSG.Disjoint L.OUT
  mc : L.MSG.Disjoint L.SCR
  ao : L.ORIG.Disjoint L.OUT
  ac : L.ORIG.Disjoint L.SCR
  ko : L.STK.Disjoint L.OUT
  ke : L.STK.Disjoint L.SEED
  kp : L.STK.Disjoint L.PK
  kx : L.STK.Disjoint L.CTX
  km : L.STK.Disjoint L.MSG
  kc : L.STK.Disjoint L.SCR
  no : L.out.toNat + 114 ≤ 2 ^ 32
  ne : L.seed.toNat + 57 ≤ 2 ^ 32
  np : L.pk.toNat + 57 ≤ 2 ^ 32
  nx : L.ctx.toNat + L.ctxLen.toNat ≤ 2 ^ 32
  nm : L.msg.toNat + L.len.toNat ≤ 2 ^ 32
  nc : L.scr.toNat + 8192 ≤ 2 ^ 32
end Lay

abbrev Ctx (L : VG.Proof.Ed448.Arm.SignCached.Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

/-- The saved words, and `len` and `scratch` where the caller put them. -/
abbrev Arguments (L : VG.Proof.Ed448.Arm.SignCached.Lay) (m : Mem) : Prop := VG.Proof.Ed448.Arm.Shake.Args L.E 12 L.value m

variable {L : VG.Proof.Ed448.Arm.SignCached.Lay}

theorem frame_sub (L : VG.Proof.Ed448.Arm.SignCached.Lay) : Region.Sub (Whole.FR L.E) L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : VG.Proof.Ed448.Arm.SignCached.Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

theorem slot_mem (L : VG.Proof.Ed448.Arm.SignCached.Lay) {j : Nat} (hj : VG.Proof.Ed448.Arm.Shake.Slot 12 j) :
    ∃ R ∈ L.inputs, R.Contains (State.addr L.E + BitVec.ofNat 64 (248 + 4 * j)) 4 := by
  obtain ⟨hj12, hj | hj⟩ := hj
  · exact ⟨L.ARGS, by simp [Lay.inputs],
      Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)⟩
  · exact ⟨L.ORIG, by simp [Lay.inputs],
      Offset.contains _ (e := 280) (k := 16) (by omega) (by omega) (by decide)⟩

namespace Lay.Ok

theorem ob_sub {o l : Nat} (ho : o + l ≤ 114) : Region.Sub (L.ob o l) L.OUT :=
  Offset.sub_base _ ho

theorem ob_within {o l : Nat} (ho : o + l ≤ 114) : Whole.Within (L.ob o l) L.OUT := ⟨o, rfl, ho⟩

/-- Two regions of `out`. -/
theorem ob_ob {o l p k : Nat} (h : o + l ≤ p ∨ p + k ≤ o) (ho : o + l ≤ 114) (hp : p + k ≤ 114) :
    (L.ob o l).Disjoint (L.ob p k) := Offset.disjoint _ h (by omega) (by omega)

variable (hL : L.Ok)
include hL


/-- The inputs are outside what the body may write. -/
theorem inputs_out {r : Region} (hr : r ∈ L.inputs) : ∀ R ∈ L.outputs ++ [Whole.FR L.E], r.Disjoint R := by
  simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  simp only [Lay.inputs, List.mem_cons, List.not_mem_nil, or_false] at hr
  have orig_fr : L.ORIG.Disjoint (Whole.FR L.E) := Offset.disjoint_base _ (by decide : 248 ≤ 280) (by decide)
  rintro R (rfl | rfl | rfl)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.eo
    · exact hL.po
    · exact hL.xo
    · exact hL.mo
    · exact hL.ao
    · exact hL.ko.sub_left (VG.Proof.Ed448.Arm.SignCached.args_sub L)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.ec
    · exact hL.pc
    · exact hL.xc
    · exact hL.mc
    · exact hL.ac
    · exact hL.kc.sub_left (VG.Proof.Ed448.Arm.SignCached.args_sub L)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hL.ke.sub_left (VG.Proof.Ed448.Arm.SignCached.frame_sub L)).symm
    · exact (hL.kp.sub_left (VG.Proof.Ed448.Arm.SignCached.frame_sub L)).symm
    · exact (hL.kx.sub_left (VG.Proof.Ed448.Arm.SignCached.frame_sub L)).symm
    · exact (hL.km.sub_left (VG.Proof.Ed448.Arm.SignCached.frame_sub L)).symm
    · exact orig_fr
    · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

/-- What the calls need of the layout. -/
theorem kit : Kit L.E L.scr 12 L.inputs L.outputs :=
  ⟨⟨by decide, by decide, by have := hL.top; omega⟩, hL.nc, by simp [Lay.outputs], hL.kc,
    fun _ hr R hR => hL.inputs_out hr R hR, fun _ hj => VG.Proof.Ed448.Arm.SignCached.slot_mem L hj⟩

/-- `out` at `o`. -/
theorem ob_addr {o : Nat} (ho : o < 114) :
    State.addr (L.out + BitVec.ofNat 32 o) = State.addr L.out + BitVec.ofNat 64 o :=
  addr_add (by have := hL.no; omega)

theorem ob_fit {o l : Nat} (ho' : o < 114) (ho : o + l ≤ 114) : (L.out + BitVec.ofNat 32 o).toNat + l ≤ 2 ^ 32 := by
  have := hL.no
  rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- `out` is outside the stack, the state and the working space. -/
theorem ob_stk {o l d k : Nat} (ho : o + l ≤ 114) (hd : d + k ≤ 280) : (L.ob o l).Disjoint (L.fr d k) :=
  (hL.ko.sub_left (Offset.sub_base _ hd)).symm.sub_left (Lay.Ok.ob_sub ho)

theorem ob_kWr {o l : Nat} (ho : o + l ≤ 114) : ∀ r ∈ kWr L.scr, (L.ob o l).Disjoint r :=
  fun r hr => (hL.oc.sub_left (Lay.Ok.ob_sub ho)).sub_right (kWr_sub L.scr r hr).sub

theorem ob_scr {o l : Nat} (ho : o + l ≤ 114) : (L.ob o l).Disjoint L.SCR := hL.oc.sub_left (Lay.Ok.ob_sub ho)

end Lay.Ok

/-- The first half of `out`, where `R` goes. -/
abbrev Lay.R0 (L : VG.Proof.Ed448.Arm.SignCached.Lay) : Region := ⟨State.addr L.out, 57⟩

theorem r0_sub (L : VG.Proof.Ed448.Arm.SignCached.Lay) : Region.Sub L.R0 L.OUT := Region.sub_prefix (by decide)
theorem r0_within (L : VG.Proof.Ed448.Arm.SignCached.Lay) : Whole.Within L.R0 L.OUT := ⟨0, (BitVec.add_zero _).symm, by change 0 + 57 ≤ 114; decide⟩
theorem scr_within (L : VG.Proof.Ed448.Arm.SignCached.Lay) : Whole.Within L.SCR L.SCR := ⟨0, (BitVec.add_zero _).symm, by simp⟩

theorem out_in (L : VG.Proof.Ed448.Arm.SignCached.Lay) : L.OUT ∈ L.outputs := by simp [Lay.outputs]
theorem scr_in (L : VG.Proof.Ed448.Arm.SignCached.Lay) : L.SCR ∈ L.outputs := by simp [Lay.outputs]

/-- Two regions of the frame. -/
theorem fr_fr {d l e k : Nat} (h : d + l ≤ e ∨ e + k ≤ d) (hd : d + l ≤ 280) (he : e + k ≤ 280) :
    (L.fr d l).Disjoint (L.fr e k) := Offset.disjoint _ h (by omega) (by omega)

/-- Outside what a call of a sponge function writes but its squeezed output:
the outgoing stack arguments, the state and the working space. -/
structure Away (L : VG.Proof.Ed448.Arm.SignCached.Lay) (D : Region) : Prop where
  args : (kArgs L.E 8).Disjoint D
  kwr : ∀ r ∈ kWr L.scr, D.Disjoint r

theorem Away.zero {D : Region} (h : VG.Proof.Ed448.Arm.SignCached.Away L D) : ∀ r ∈ [(⟨State.addr L.scr, 200⟩ : Region)], D.Disjoint r :=
  fun r hr => h.kwr r (by rw [List.mem_singleton.mp hr]; simp [kWr])

theorem Away.abs {D : Region} (h : VG.Proof.Ed448.Arm.SignCached.Away L D) : ∀ r ∈ kArgs L.E 8 :: kWr L.scr, D.Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.args.symm
  · exact h.kwr r hr

theorem Away.sqz {D : Region} (h : VG.Proof.Ed448.Arm.SignCached.Away L D) {d : Nat} (hd : D.Disjoint (L.fr d 114)) :
    ∀ r ∈ kArgs L.E 8 :: sqzWr L.E L.scr d, D.Disjoint r := by
  intro r hr
  simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.args.symm
  · exact h.kwr _ (by simp [kWr])
  · exact hd
  · exact h.kwr _ (by simp [kWr])

theorem Lay.Ok.away_fr (hL : L.Ok) {d l : Nat} (h8 : 8 ≤ d) (hd : d + l ≤ 248) : VG.Proof.Ed448.Arm.SignCached.Away L (L.fr d l) :=
  ⟨Offset.base_disjoint _ h8 (by omega), hL.kit.frame_kWr (by omega)⟩

theorem Lay.Ok.away_ob (hL : L.Ok) {o l : Nat} (ho : o + l ≤ 114) : VG.Proof.Ed448.Arm.SignCached.Away L (L.ob o l) :=
  ⟨(hL.ko.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.Ok.ob_sub ho), hL.ob_kWr ho⟩

theorem Lay.Ok.away_r0 (hL : L.Ok) : VG.Proof.Ed448.Arm.SignCached.Away L L.R0 :=
  ⟨(hL.ko.sub_left (Region.sub_prefix (by decide))).sub_right (VG.Proof.Ed448.Arm.SignCached.r0_sub L),
    fun r hr => (hL.oc.sub_left (VG.Proof.Ed448.Arm.SignCached.r0_sub L)).sub_right (kWr_sub L.scr r hr).sub⟩

end VG.Proof.Ed448.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.SignCached.Hash`. -/
section

/-!
# Ed448 signing with a cached public key on ARMv7: the hashes

`hdr_step`: the first ten bytes of `dom4(0, C)` at `HDR`. `seed_step`:
`SHAKE256(seed, 114)` at `S`, and `prune_step`: its first half pruned in
place. `nonce_step` and `chal_step`: `SHAKE256(dom4(0, C) ‖ prefix ‖ M)` and
`SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M)` at `HASH`, the prefix at `K` and `R` the
first half of `out`. Each states what it may write (`W ex`: the outgoing
stack arguments, the regions `ex`, the state and the working space).
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Spec.Sha3 (stateAt)
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.Within)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit Args argVal kWr kArgs sqzWr ScrAt DataOk hdrBytes valid_const
  valid_frame frame_bytes frame_within hdr_len dom4_eq)

variable {L : VG.Proof.Ed448.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem scr_at (L : VG.Proof.Ed448.Arm.SignCached.Lay) : ScrAt 12 L.value SC L.scr := ⟨by decide, rfl⟩

/-! ## What the steps write -/

/-- The outgoing stack arguments, `ex`, the state and the working space. -/
abbrev W (L : VG.Proof.Ed448.Arm.SignCached.Lay) (ex : List Region) : List Region := kArgs L.E 8 :: ex ++ kWr L.scr

theorem Away.bytes {D : Region} (h : VG.Proof.Ed448.Arm.SignCached.Away L D) {ex : List Region} (hx : ∀ r ∈ ex, D.Disjoint r)
    {m m' : Mem} (hf : Frame (VG.Proof.Ed448.Arm.SignCached.W L ex) m m') (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := by
  refine frame_bytes hf (fun r hr => ?_) hn
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.args.symm
  rcases List.mem_append.mp hr with hr | hr
  · exact hx r hr
  · exact h.kwr r hr

theorem W.zero {ex : List Region} {m m' : Mem} (h : Frame [⟨State.addr L.scr, 200⟩] m m') : Frame (VG.Proof.Ed448.Arm.SignCached.W L ex) m m' :=
  h.mono fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [kWr]))

theorem W.abs {ex : List Region} {m m' : Mem} (h : Frame (kArgs L.E 8 :: kWr L.scr) m m') : Frame (VG.Proof.Ed448.Arm.SignCached.W L ex) m m' :=
  h.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hr)

theorem W.sqz {ex : List Region} {d : Nat} (hd : L.fr d 114 ∈ ex) {m m' : Mem}
    (h : Frame (kArgs L.E 8 :: sqzWr L.E L.scr d) m m') : Frame (VG.Proof.Ed448.Arm.SignCached.W L ex) m m' :=
  h.mono fun r hr => by
    simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [kWr]))
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hd)
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (by simp [kWr]))

/-! ## Absorptions, in this layout -/

/-- Data in an input. -/
theorem Lay.Ok.input_data (hL : L.Ok) {R D : Region} (hR : R ∈ L.inputs) (hw : Whole.Within D R) :
    DataOk L.E L.inputs L.outputs D ∧ VG.Proof.Ed448.Arm.SignCached.Away L D :=
  let h := hL.kit.data_input hR hw
  ⟨.inr ⟨R, List.mem_append_left _ hR, hw⟩, h.2, h.1⟩

theorem first_abs (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀) {src len : Value}
    (vs : valid 12 src) (vl : valid 12 len) {P : BitVec 32} {N : Nat} (hP : argVal L.E L.value src = P)
    (hN : (argVal L.E L.value len).toNat = N) (hcov : DataOk L.E L.inputs L.outputs ⟨State.addr P, N⟩)
    (hd : VG.Proof.Ed448.Arm.SignCached.Away L ⟨State.addr P, N⟩) (hfit : P.toNat + N ≤ 2 ^ 32)
    (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 []) :
    WP isa (absorb (firstArgs SC src len)) t fun v => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ v ∧
      Frame (kArgs L.E 8 :: kWr L.scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr L.scr) 136 (Spec.Ed448.bytesAt t.mem (State.addr P) N) ∧
      v.gpr .r0 = BitVec.ofNat 32 (N % 136) :=
  hL.kit.firstAt hc ha (VG.Proof.Ed448.Arm.SignCached.scr_at L) vs vl hP hN hcov hd.kwr hd.args hfit hr

theorem next_abs (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀) {src len : Value}
    (vs : valid 12 src) (vl : valid 12 len) {P : BitVec 32} {N : Nat} (hP : argVal L.E L.value src = P)
    (hN : (argVal L.E L.value len).toNat = N) (hcov : DataOk L.E L.inputs L.outputs ⟨State.addr P, N⟩)
    (hd : VG.Proof.Ed448.Arm.SignCached.Away L ⟨State.addr P, N⟩) (hfit : P.toNat + N ≤ 2 ^ 32)
    {msg : List Byte} (hr : Spec.Sha3.Repr t.mem (State.addr L.scr) 136 msg)
    (hpos : t.gpr .r0 = BitVec.ofNat 32 (msg.length % 136)) :
    WP isa (absorb (nextArgs SC src len)) t fun v => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ v ∧
      Frame (kArgs L.E 8 :: kWr L.scr) t.mem v.mem ∧
      Spec.Sha3.Repr v.mem (State.addr L.scr) 136 (msg ++ Spec.Ed448.bytesAt t.mem (State.addr P) N) ∧
      v.gpr .r0 = BitVec.ofNat 32 ((msg ++ Spec.Ed448.bytesAt t.mem (State.addr P) N).length % 136) :=
  hL.kit.nextAt hc ha (VG.Proof.Ed448.Arm.SignCached.scr_at L) vs vl hP hN hcov hd.kwr hd.args hfit hr hpos

/-! ## The header -/

theorem hdr_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀) :
    WP isa (.block (hdrAt 4 HDR)) t fun u => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L.ctxLen :=
  WP.mono (hL.kit.hdr_ok hc ha (j := 4) (by decide) hL.cl (by decide)) fun _ ⟨hu, _, hb⟩ => ⟨hu, hb⟩

/-! ## `SHAKE256(seed, 114)`, and `s` -/

theorem seed_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀) :
    WP isa seedHash t fun u => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧ Frame (VG.Proof.Ed448.Arm.SignCached.W L [L.fr S 114]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 S) 114 =
        Spec.Sha3.shake256 (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) 114 := by
  have hk := hL.kit
  have hw : Whole.Within ⟨State.addr L.seed, 57⟩ L.SEED := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have hR : L.SEED ∈ L.inputs := by simp [Lay.inputs]
  obtain ⟨hcov, hd⟩ := hL.input_data hR hw
  unfold seedHash
  refine WP.seq (WP.mono (hk.zero_ok hc ha (VG.Proof.Ed448.Arm.SignCached.scr_at L)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.first_abs hc1 hL ha (src := .caller 1 0) (len := .const 57) (P := L.seed) (N := 57)
    ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl hcov hd hL.ne
    (PublicKey.repr_nil hz))
    fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  refine WP.seq (WP.mono (hk.pad_step hc2 ha (VG.Proof.Ed448.Arm.SignCached.scr_at L) hr2 (by rw [hp2]; simp [Spec.Ed448.bytesAt]))
    fun t3 ⟨hc3, hf3, hs3⟩ => ?_)
  refine WP.mono (hk.sqz_step hc3 ha (VG.Proof.Ed448.Arm.SignCached.scr_at L) (d := S) (by decide) (by decide)) fun u ⟨hu, hf4, hb⟩ =>
    ⟨hu, ((W.zero hf1).trans (W.abs hf2)).trans ((W.abs hf3).trans (W.sqz (by simp) hf4)), ?_⟩
  have e := hk.input_bytes hc1 hR hw (by change 57 ≤ 2 ^ 64; decide)
  simp only at e
  rw [hb, hs3, ← PublicKey.shake256_eq, e]

theorem prune_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) :
    WP isa prune t fun u => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧ Frame [L.fr S 57] t.mem u.mem ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 S) 57) =
        Spec.Ed448.prune (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 S) 114) := by
  unfold prune
  refine WP.seq (VG.Proof.X25519.Arm.WP.cons (s' := t.setReg .r12 (t.sp + BitVec.ofNat 32 S))
    (by simp [exec, S]) (WP.block_nil ?_))
  have hsp := hc.sp
  have ht := hL.top
  have e12 : (t.setReg .r12 (t.sp + BitVec.ofNat 32 S)).gpr .r12 = L.E + BitVec.ofNat 32 S := by
    simp [State.setReg, hsp]
  refine WP.mono (PublicKey.pruneOps_ok (q := State.addr L.E + BitVec.ofNat 64 S)
    (by rw [e12]; exact hL.kit.frame_addr (by decide))
    (by rw [e12]; exact hL.kit.frame_fit (by decide))
    (fun j hj => by
      have h := hc.writable_frame (Offset.contains_base (State.addr L.E) (d := S + j) (n := 1)
        (k := 248) (by simp only [S]; omega) (by simp only [S]; omega))
      rw [← Offset.add_add] at h
      exact h))
    fun u ⟨um, usp, urd, uwr, ug⟩ => ?_
  have hf : Frame [L.fr S 57] t.mem u.mem := by
    rw [um]
    refine (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      ?_).writeW (List.mem_singleton_self _) _ ?_
    · have h := Offset.contains_base (State.addr L.E + BitVec.ofNat 64 S) (d := 0) (n := 1) (k := 57) (by omega) (by omega)
      rw [show State.addr L.E + BitVec.ofNat 64 S + BitVec.ofNat 64 0 = State.addr L.E + BitVec.ofNat 64 S from
        BitVec.add_zero _] at h
      exact h
    · exact Offset.contains_base _ (by omega) (by omega)
    · exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨?_, hf, ?_⟩
  · refine hc.of_frame urd uwr usp ?_ hf ?_
    · intro r hr _
      rw [ug r (by rintro rfl; simp [preserved] at hr)]
      exact RegUpd.gpr_setReg_of_ne _ _ (by rintro rfl; simp [preserved] at hr)
    · intro r hr
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by simp only [S]; omega))
  · rw [um, PublicKey.pruned_value]
    unfold Spec.Ed448.prune
    rw [PublicKey.bytesAt_take57]
    rfl

/-! ## The nonce's and the challenge's hashes -/

theorem len_append (msg : List Byte) (m : Mem) (p : Addr) (n : Nat) :
    (msg ++ Spec.Ed448.bytesAt m p n).length = msg.length + n := by
  simp [Spec.Ed448.bytesAt]

theorem Lay.Ok.away_hdr (hL : L.Ok) : VG.Proof.Ed448.Arm.SignCached.Away L (L.fr HDR 10) := hL.away_fr (by decide) (by decide)
theorem Lay.Ok.away_k (hL : L.Ok) : VG.Proof.Ed448.Arm.SignCached.Away L (L.fr K 57) := hL.away_fr (by decide) (by decide)
theorem Lay.Ok.away_s (hL : L.Ok) : VG.Proof.Ed448.Arm.SignCached.Away L (L.fr S 57) := hL.away_fr (by decide) (by decide)

/-- `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` in the frame at `HASH`, the
header of `dom4` at `HDR` and the prefix at `K`. -/
theorem nonce_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀)
    (hh : Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L.ctxLen) :
    WP isa nonceHash t fun u => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧ Frame (VG.Proof.Ed448.Arm.SignCached.W L [L.fr HASH 114]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57 ++
            Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have hk := hL.kit
  have wx : Whole.Within ⟨State.addr L.ctx, L.ctxLen.toNat⟩ L.CTX := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have wm : Whole.Within ⟨State.addr L.msg, L.len.toNat⟩ L.MSG := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have rx : L.CTX ∈ L.inputs := by simp [Lay.inputs]
  have rm : L.MSG ∈ L.inputs := by simp [Lay.inputs]
  obtain ⟨cx, dx⟩ := hL.input_data rx wx
  obtain ⟨cm, dm⟩ := hL.input_data rm wm
  unfold nonceHash
  -- Zero the state.
  refine WP.seq (WP.mono (hk.zero_ok hc ha (VG.Proof.Ed448.Arm.SignCached.scr_at L)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  -- The header.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.first_abs hc1 hL ha (src := .frame HDR) (len := .const 10)
    (P := L.E + BitVec.ofNat 32 HDR) (N := 10) (valid_frame (by decide)) (valid_const (by decide)) rfl rfl
    (by rw [hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hk.frame_addr (by decide)]; exact hL.away_hdr) (hk.frame_fit (by decide)) (PublicKey.repr_nil hz))
    fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  have hh1 := hL.away_hdr.bytes (ex := []) (fun _ h => nomatch h) (W.zero hf1) (by change 10 ≤ 2 ^ 64; decide)
  simp only at hh1
  rw [hk.frame_addr (by decide), hh1, hh] at hr2
  have hp2' : t2.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L.ctxLen).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.next_abs hc2 hL ha (src := .caller 3 0) (len := .caller 4 0) (P := L.ctx)
    (N := L.ctxLen.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value]) cx dx hL.nx hr2 hp2') fun t3 ⟨hc3, hf3, hr3, hp3⟩ => ?_)
  have ex := hk.input_bytes hc2 rx wx (by change L.ctxLen.toNat ≤ 2 ^ 64; have := L.ctxLen.isLt; omega)
  simp only at ex
  rw [ex] at hr3 hp3
  -- The prefix.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.next_abs hc3 hL ha (src := .frame K) (len := .const 57)
    (P := L.E + BitVec.ofNat 32 K) (N := 57) (valid_frame (by decide)) (valid_const (by decide)) rfl rfl
    (by rw [hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hk.frame_addr (by decide)]; exact hL.away_k) (hk.frame_fit (by decide)) hr3 hp3)
    fun t4 ⟨hc4, hf4, hr4, hp4⟩ => ?_)
  have hk3 := hL.away_k.bytes (ex := []) (fun _ h => nomatch h)
    (((W.zero hf1).trans (W.abs hf2)).trans (W.abs hf3)) (by change 57 ≤ 2 ^ 64; decide)
  simp only at hk3
  rw [hk.frame_addr (by decide), hk3] at hr4 hp4
  -- The message.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.next_abs hc4 hL ha (src := .caller 5 0) (len := LEN) (P := L.msg)
    (N := L.len.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value, LEN]) cm dm hL.nm hr4 hp4) fun t5 ⟨hc5, hf5, hr5, hp5⟩ => ?_)
  have em := hk.input_bytes hc4 rm wm (by change L.len.toNat ≤ 2 ^ 64; have := L.len.isLt; omega)
  simp only at em
  rw [em] at hr5 hp5
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc5 ha (VG.Proof.Ed448.Arm.SignCached.scr_at L) hr5 hp5) fun t6 ⟨hc6, hf6, hs6⟩ => ?_)
  refine WP.mono (hk.sqz_step hc6 ha (VG.Proof.Ed448.Arm.SignCached.scr_at L) (d := HASH) (by decide) (by decide)) fun u ⟨hu, hf7, hb⟩ =>
    ⟨hu, ((((W.zero hf1).trans (W.abs hf2)).trans ((W.abs hf3).trans (W.abs hf4))).trans
      ((W.abs hf5).trans ((W.abs hf6).trans (W.sqz (by simp) hf7)))), ?_⟩
  rw [hb, hs6, ← PublicKey.shake256_eq, Spec.Ed448.hash,
    dom4_eq L.ctxLen _ _ (by simp [Spec.Ed448.bytesAt])]
  simp only [List.append_assoc]

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` in the frame at `HASH`, the header
of `dom4` at `HDR` and `R` the first half of `out`. -/
theorem chal_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀)
    (hh : Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HDR) 10 = hdrBytes L.ctxLen) :
    WP isa chalHash t fun u => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧ Frame (VG.Proof.Ed448.Arm.SignCached.W L [L.fr HASH 114]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114 =
        Spec.Ed448.hash (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt t.mem (State.addr L.out) 57 ++ Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 ++
            Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have hk := hL.kit
  have wx : Whole.Within ⟨State.addr L.ctx, L.ctxLen.toNat⟩ L.CTX := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have wp : Whole.Within ⟨State.addr L.pk, 57⟩ L.PK := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have wm : Whole.Within ⟨State.addr L.msg, L.len.toNat⟩ L.MSG := ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have rx : L.CTX ∈ L.inputs := by simp [Lay.inputs]
  have rp : L.PK ∈ L.inputs := by simp [Lay.inputs]
  have rm : L.MSG ∈ L.inputs := by simp [Lay.inputs]
  obtain ⟨cx, dx⟩ := hL.input_data rx wx
  obtain ⟨cp, dp⟩ := hL.input_data rp wp
  obtain ⟨cm, dm⟩ := hL.input_data rm wm
  unfold chalHash
  -- Zero the state.
  refine WP.seq (WP.mono (hk.zero_ok hc ha (VG.Proof.Ed448.Arm.SignCached.scr_at L)) fun t1 ⟨hc1, hz, hf1⟩ => ?_)
  -- The header.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.first_abs hc1 hL ha (src := .frame HDR) (len := .const 10)
    (P := L.E + BitVec.ofNat 32 HDR) (N := 10) (valid_frame (by decide)) (valid_const (by decide)) rfl rfl
    (by rw [hk.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hk.frame_addr (by decide)]; exact hL.away_hdr) (hk.frame_fit (by decide)) (PublicKey.repr_nil hz))
    fun t2 ⟨hc2, hf2, hr2, hp2⟩ => ?_)
  have hh1 := hL.away_hdr.bytes (ex := []) (fun _ h => nomatch h) (W.zero hf1) (by change 10 ≤ 2 ^ 64; decide)
  simp only at hh1
  rw [hk.frame_addr (by decide), hh1, hh] at hr2
  have hp2' : t2.gpr .r0 = BitVec.ofNat 32 ((hdrBytes L.ctxLen).length % 136) := by rw [hp2, hdr_len]
  -- The context.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.next_abs hc2 hL ha (src := .caller 3 0) (len := .caller 4 0) (P := L.ctx)
    (N := L.ctxLen.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value]) cx dx hL.nx hr2 hp2') fun t3 ⟨hc3, hf3, hr3, hp3⟩ => ?_)
  have ex := hk.input_bytes hc2 rx wx (by change L.ctxLen.toNat ≤ 2 ^ 64; have := L.ctxLen.isLt; omega)
  simp only at ex
  rw [ex] at hr3 hp3
  -- `R`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.next_abs hc3 hL ha (src := .caller 0 0) (len := .const 57) (P := L.out) (N := 57)
    ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl
    (.inr ⟨L.OUT, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.out_in L), VG.Proof.Ed448.Arm.SignCached.r0_within L⟩) hL.away_r0 (by have := hL.no; omega) hr3 hp3)
    fun t4 ⟨hc4, hf4, hr4, hp4⟩ => ?_)
  have hr3' := hL.away_r0.bytes (ex := []) (fun _ h => nomatch h)
    (((W.zero hf1).trans (W.abs hf2)).trans (W.abs hf3)) (by change 57 ≤ 2 ^ 64; decide)
  simp only at hr3'
  rw [hr3'] at hr4 hp4
  -- `A`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.next_abs hc4 hL ha (src := .caller 2 0) (len := .const 57) (P := L.pk) (N := 57)
    ⟨by decide, by decide⟩ (valid_const (by decide)) (by simp [argVal, Lay.value]) rfl cp dp hL.np hr4 hp4)
    fun t5 ⟨hc5, hf5, hr5, hp5⟩ => ?_)
  have ep := hk.input_bytes hc4 rp wp (by change 57 ≤ 2 ^ 64; decide)
  simp only at ep
  rw [ep] at hr5 hp5
  -- The message.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.next_abs hc5 hL ha (src := .caller 5 0) (len := LEN) (P := L.msg)
    (N := L.len.toNat) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (by simp [argVal, Lay.value])
    (by simp [argVal, Lay.value, LEN]) cm dm hL.nm hr5 hp5) fun t6 ⟨hc6, hf6, hr6, hp6⟩ => ?_)
  have em := hk.input_bytes hc5 rm wm (by change L.len.toNat ≤ 2 ^ 64; have := L.len.isLt; omega)
  simp only at em
  rw [em] at hr6 hp6
  -- Pad and squeeze.
  refine WP.seq (WP.mono (hk.pad_step hc6 ha (VG.Proof.Ed448.Arm.SignCached.scr_at L) hr6 hp6) fun t7 ⟨hc7, hf7, hs7⟩ => ?_)
  refine WP.mono (hk.sqz_step hc7 ha (VG.Proof.Ed448.Arm.SignCached.scr_at L) (d := HASH) (by decide) (by decide)) fun u ⟨hu, hf8, hb⟩ =>
    ⟨hu, ((((W.zero hf1).trans (W.abs hf2)).trans ((W.abs hf3).trans (W.abs hf4))).trans
      (((W.abs hf5).trans (W.abs hf6)).trans ((W.abs hf7).trans (W.sqz (by simp) hf8)))), ?_⟩
  rw [hb, hs7, ← PublicKey.shake256_eq, Spec.Ed448.hash,
    dom4_eq L.ctxLen _ _ (by simp [Spec.Ed448.bytesAt])]
  simp only [List.append_assoc]

end VG.Proof.Ed448.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.SignCached.Calls`. -/
section

/-!
# Ed448 signing with a cached public key on ARMv7: the scalar calls

`reduceR_step`: `r`, the nonce's hash reduced modulo `L`, into the second
half of `out`; `base_step`: `R = [r]B` into its first half, given the
reference ladder's agreement with the specification (`BaseLadderOk`, a
hypothesis); `reduceK_step`: `k` at `K`; `mulAdd_step`:
`S = (r + k s) mod L` over `r` (`vg_ed448_scalar_mul_add`'s output may be
one of its inputs); `wipe_step`: the locals cleared. Each through
`Whole.call_ok` with the callee's contract on this target, and stating what
it may write.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.Within Whole.call_ok Whole.Ctx.zeroWords)
open VG.Proof.Ed448.Arm.Shake (Slot valid Kit Args argVal kWr kArgs valid_const valid_frame frame_within
  frame_bytes bytes_setup)
open VG.Proof.Ed448.Arm (scalarReduceLocal scalarReduce_ok scalarBaseLocal scalarBase_ok scalarMulAddLocal
  scalarMulAdd_ok)
open VG.Proof.Ed448 (BaseLadderOk)

variable {L : VG.Proof.Ed448.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem W.call {ex : List Region} {k : Nat} (hk : k ≤ 8) {m1 m2 m3 : Mem}
    (h1 : Frame [⟨State.addr L.E, k⟩] m1 m2) (h2 : Frame ex m2 m3) : Frame (VG.Proof.Ed448.Arm.SignCached.W L ex) m1 m3 := by
  refine (Frame.sub h1 fun r hr => ⟨kArgs L.E 8, List.mem_cons_self, ?_⟩).trans
    (h2.mono fun r hr => List.mem_cons_of_mem _ (List.mem_append_left _ hr))
  rw [List.mem_singleton.mp hr]
  exact Region.sub_prefix hk

theorem gpr_entry {s : State} {rd wr : List Region} {r : Reg} (hr : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

/-! ## `r` -/

theorem reduce_noFrames : Impl.Ed448.Arm.scalarReduce.noFrames = true := by lit_decide

def ReduceArgs (L : VG.Proof.Ed448.Arm.SignCached.Lay) (out wide : BitVec 32) (t : State) : Prop :=
  t.gpr .r0 = out ∧ t.gpr .r1 = wide ∧ t.gpr .r2 = L.scr

/-- `vg_ed448_scalar_reduce` from 114 bytes of the frame at `HASH` into `O`. -/
theorem reduce_pre (hL : L.Ok) {o : BitVec 32} {O : Region} (hO : O = ⟨State.addr o, 57⟩)
    (hof : o.toNat + 57 ≤ 2 ^ 32) (hoh : O.Disjoint (L.fr HASH 114)) (hos : O.Disjoint L.SCR)
    (ha : VG.Proof.Ed448.Arm.SignCached.ReduceArgs L o (L.E + BitVec.ofNat 32 HASH) t) :
    scalarReduceLocal.pre (t.callEntry.withRegions [L.fr HASH 114] [O, L.SCR]) := by
  obtain ⟨h0, h1, h2⟩ := ha
  subst hO
  simp only [scalarReduceLocal]
  rw [VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r0 ∉ linkRegs), VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r1 ∉ linkRegs),
    VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, State.withRegions_rd, State.withRegions_wr,
    hL.kit.frame_addr (by decide)]
  exact ⟨rfl, rfl, hoh, hos, hL.kit.stack_scr (by decide), hof, hL.kit.frame_fit (by decide), hL.nc⟩

theorem reduce_covers {O : Region} (hO : Whole.Within O (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within O R) :
    Covers ([L.fr HASH 114] ++ [O, L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inl (frame_within _ (by decide))
  · rcases hO with h | ⟨R, hR, h⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, h⟩
  · exact .inr ⟨L.SCR, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.scr_in L), VG.Proof.Ed448.Arm.SignCached.scr_within L⟩

theorem reduce_writes {O : Region} (hO : Whole.Within O (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within O R) :
    ∀ r ∈ [O, L.SCR], Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hO
  · exact .inr ⟨L.SCR, VG.Proof.Ed448.Arm.SignCached.scr_in L, VG.Proof.Ed448.Arm.SignCached.scr_within L⟩

/-- The call, from its arguments in registers. -/
theorem reduce_call (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) {o : BitVec 32} {O : Region} (hO : O = ⟨State.addr o, 57⟩)
    (hof : o.toNat + 57 ≤ 2 ^ 32) (hoh : O.Disjoint (L.fr HASH 114)) (hos : O.Disjoint L.SCR)
    (hw : Whole.Within O (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within O R)
    (ha : VG.Proof.Ed448.Arm.SignCached.ReduceArgs L o (L.E + BitVec.ofNat 32 HASH) t) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) t fun u => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧
      Frame [O, L.SCR] t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr o) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114) := by
  refine Whole.call_ok hc scalarReduce_ok VG.Proof.Ed448.Arm.SignCached.reduce_noFrames (VG.Proof.Ed448.Arm.SignCached.reduce_pre hL hO hof hoh hos ha) (VG.Proof.Ed448.Arm.SignCached.reduce_covers hw)
    (VG.Proof.Ed448.Arm.SignCached.reduce_writes hw) fun v hv hf hp => ⟨hv, hf, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (t.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr (t.callEntry.gpr .r1)) 114) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1, hL.kit.frame_addr (by decide)] at hp
  exact hp

/-- `r` into the second half of `out`. -/
theorem reduceR_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀) :
    WP isa (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) t fun u =>
      VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧ Frame (VG.Proof.Ed448.Arm.SignCached.W L [L.ob 57 57, L.SCR]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (hL.kit.setup_ok hc ha
    (args := [(.r0, .caller 0 57), (.r1, .frame HASH), (.r2, .caller SC 0)]) (stk := [])
    (by decide) (by simp only [List.forall_mem_cons]
                    exact ⟨⟨by decide, by decide⟩, valid_frame (by decide), ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 0 57) (by simp)
  have h1 := hs (.r1, .frame HASH) (by simp)
  have h2 := hs (.r2, .caller SC 0) (by simp)
  simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
  have he := bytes_setup hm (D := L.fr HASH 114) (Shake.frame_out (by decide) (by decide)) (by change 114 ≤ 2 ^ 64; decide)
  simp only at he
  refine WP.mono (VG.Proof.Ed448.Arm.SignCached.reduce_call hu hL (o := L.out + BitVec.ofNat 32 57) (O := L.ob 57 57)
    (by rw [hL.ob_addr (by decide)]) (hL.ob_fit (by decide) (by decide)) (hL.ob_stk (by decide) (by decide))
    (hL.ob_scr (by decide)) (.inr ⟨L.OUT, VG.Proof.Ed448.Arm.SignCached.out_in L, Lay.Ok.ob_within (by decide)⟩) ⟨h0, h1, h2⟩)
    fun v ⟨hv, hf, hp⟩ => ⟨hv, W.call (by simp) hm hf, ?_⟩
  rw [← hL.ob_addr (by decide), hp, he]

/-! ## `R` -/

theorem base_noFrames : Impl.Ed448.Arm.scalarBase.noFrames = true := PublicKey.base_noFrames

def BaseArgs (L : VG.Proof.Ed448.Arm.SignCached.Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out ∧ t.gpr .r1 = L.out + BitVec.ofNat 32 57 ∧ t.gpr .r2 = L.scr

theorem base_pre (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.BaseArgs L t) :
    scalarBaseLocal.pre (t.callEntry.withRegions [L.ob 57 57] [L.R0, L.SCR]) := by
  obtain ⟨h0, h1, h2⟩ := ha
  simp only [scalarBaseLocal]
  rw [VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r0 ∉ linkRegs), VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r1 ∉ linkRegs),
    VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r2 ∉ linkRegs), h0, h1, h2, State.withRegions_rd, State.withRegions_wr,
    hL.ob_addr (by decide)]
  exact ⟨rfl, rfl, hL.oc.sub_left (VG.Proof.Ed448.Arm.SignCached.r0_sub L), hL.ob_scr (by decide), by have := hL.no; omega,
    hL.ob_fit (by decide) (by decide), hL.nc⟩

theorem base_covers (L : VG.Proof.Ed448.Arm.SignCached.Lay) : Covers ([L.ob 57 57] ++ [L.R0, L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨L.OUT, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.out_in L), Lay.Ok.ob_within (by decide)⟩
  · exact .inr ⟨L.OUT, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.out_in L), VG.Proof.Ed448.Arm.SignCached.r0_within L⟩
  · exact .inr ⟨L.SCR, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.scr_in L), VG.Proof.Ed448.Arm.SignCached.scr_within L⟩

theorem base_writes (L : VG.Proof.Ed448.Arm.SignCached.Lay) : ∀ r ∈ [L.R0, L.SCR],
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨L.OUT, VG.Proof.Ed448.Arm.SignCached.out_in L, VG.Proof.Ed448.Arm.SignCached.r0_within L⟩
  · exact .inr ⟨L.SCR, VG.Proof.Ed448.Arm.SignCached.scr_in L, VG.Proof.Ed448.Arm.SignCached.scr_within L⟩

theorem base_step (hl : BaseLadderOk) (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀) :
    WP isa (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase) t fun u =>
      VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧ Frame (VG.Proof.Ed448.Arm.SignCached.W L [L.R0, L.SCR]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 57 =
        Spec.Ed448.scalarBase (Spec.Ed448.bytesAt t.mem (State.addr L.out + BitVec.ofNat 64 57) 57) := by
  refine WP.seq (WP.mono (hL.kit.setup_ok hc ha
    (args := [(.r0, .caller 0 0), (.r1, .caller 0 57), (.r2, .caller SC 0)]) (stk := [])
    (by decide) (by simp only [List.forall_mem_cons]
                    exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .caller 0 0) (by simp)
  have h1 := hs (.r1, .caller 0 57) (by simp)
  have h2 := hs (.r2, .caller SC 0) (by simp)
  simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
  have he := frame_bytes hm (D := L.ob 57 57) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hL.ko.sub_left (Region.sub_prefix (by decide))).symm.sub_left
      (Lay.Ok.ob_sub (by decide))) (by change 57 ≤ 2 ^ 64; decide)
  simp only at he
  refine Whole.call_ok hu (scalarBase_ok hl) VG.Proof.Ed448.Arm.SignCached.base_noFrames (VG.Proof.Ed448.Arm.SignCached.base_pre hL ⟨h0, h1, h2⟩) (VG.Proof.Ed448.Arm.SignCached.base_covers L)
    (VG.Proof.Ed448.Arm.SignCached.base_writes L) fun v hv hf hp => ⟨hv, W.call (by simp) hm hf, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (u.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), h0, h1, hL.ob_addr (by decide), he] at hp
  exact hp

/-! ## `k` -/

theorem reduceK_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀) :
    WP isa (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce) t fun u =>
      VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧ Frame (VG.Proof.Ed448.Arm.SignCached.W L [L.fr K 57, L.SCR]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 HASH) 114) := by
  refine WP.seq (WP.mono (hL.kit.setup_ok hc ha
    (args := [(.r0, .frame K), (.r1, .frame HASH), (.r2, .caller SC 0)]) (stk := [])
    (by decide) (by simp only [List.forall_mem_cons]
                    exact ⟨valid_frame (by decide), valid_frame (by decide), ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide) (by simp))
    fun u ⟨hu, hm, hs, _⟩ => ?_)
  have h0 := hs (.r0, .frame K) (by simp)
  have h1 := hs (.r1, .frame HASH) (by simp)
  have h2 := hs (.r2, .caller SC 0) (by simp)
  simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
  have he := bytes_setup hm (D := L.fr HASH 114) (Shake.frame_out (by decide) (by decide)) (by change 114 ≤ 2 ^ 64; decide)
  simp only at he
  refine WP.mono (VG.Proof.Ed448.Arm.SignCached.reduce_call hu hL (o := L.E + BitVec.ofNat 32 K) (O := L.fr K 57)
    (by rw [hL.kit.frame_addr (by decide)]) (hL.kit.frame_fit (by decide)) (VG.Proof.Ed448.Arm.SignCached.fr_fr (by decide) (by decide) (by decide))
    (hL.kit.stack_scr (by decide)) (.inl (frame_within _ (by decide))) ⟨h0, h1, h2⟩)
    fun v ⟨hv, hf, hp⟩ => ⟨hv, W.call (by simp) hm hf, ?_⟩
  rw [← hL.kit.frame_addr (by decide), hp, he]

/-! ## `S` -/

theorem mulAdd_noFrames : Impl.Ed448.Arm.scalarMulAdd.noFrames = true := by lit_decide

def MulArgs (L : VG.Proof.Ed448.Arm.SignCached.Lay) (t : State) : Prop :=
  t.gpr .r0 = L.out + BitVec.ofNat 32 57 ∧ t.gpr .r1 = L.out + BitVec.ofNat 32 57 ∧
    t.gpr .r2 = L.E + BitVec.ofNat 32 K ∧ t.gpr .r3 = L.E + BitVec.ofNat 32 S ∧ stackArg t 0 = L.scr

def mulRd (L : VG.Proof.Ed448.Arm.SignCached.Lay) : List Region := [L.ob 57 57, L.fr K 57, L.fr S 57, kArgs L.E 4]

theorem mul_pre (hL : L.Ok) (he : t.sp = L.E) (ha : VG.Proof.Ed448.Arm.SignCached.MulArgs L t) :
    scalarMulAddLocal.pre (t.callEntry.withRegions (VG.Proof.Ed448.Arm.SignCached.mulRd L) [L.ob 57 57, L.SCR]) := by
  obtain ⟨h0, h1, h2, h3, a0⟩ := ha
  have sa : stackArg (t.callEntry.withRegions (VG.Proof.Ed448.Arm.SignCached.mulRd L) [L.ob 57 57, L.SCR]) 0 = stackArg t 0 := rfl
  have spa : State.addr (t.callEntry.withRegions (VG.Proof.Ed448.Arm.SignCached.mulRd L) [L.ob 57 57, L.SCR]).sp = State.addr L.E := by
    simp [State.withRegions_sp, State.callEntry_sp, he]
  simp only [scalarMulAddLocal]
  rw [VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r0 ∉ linkRegs), VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r1 ∉ linkRegs),
    VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r2 ∉ linkRegs), VG.Proof.Ed448.Arm.SignCached.gpr_entry (by decide : Reg.r3 ∉ linkRegs), h0, h1, h2, h3,
    sa, a0, spa, State.withRegions_rd, State.withRegions_wr, hL.ob_addr (by decide),
    hL.kit.frame_addr (by decide), hL.kit.frame_addr (by decide)]
  have ht := hL.kit.top
  have hsp : (t.callEntry.withRegions (VG.Proof.Ed448.Arm.SignCached.mulRd L) [L.ob 57 57, L.SCR]).sp = L.E := by
    simp [State.withRegions_sp, State.callEntry_sp, he]
  refine ⟨rfl, rfl, hL.ob_scr (by decide), hL.ob_scr (by decide), hL.kit.stack_scr (by decide),
    hL.kit.stack_scr (by decide),
    (hL.ko.sub_left (Region.sub_prefix (by decide : 4 ≤ 280))).symm.sub_left (Lay.Ok.ob_sub (by decide)),
    (hL.kc.sub_left (Region.sub_prefix (by decide : 4 ≤ 280))).symm,
    hL.ob_fit (by decide) (by decide), hL.ob_fit (by decide) (by decide), hL.kit.frame_fit (by decide),
    hL.kit.frame_fit (by decide), hL.nc, by rw [hsp]; omega⟩

theorem mul_covers (L : VG.Proof.Ed448.Arm.SignCached.Lay) : Covers (VG.Proof.Ed448.Arm.SignCached.mulRd L ++ [L.ob 57 57, L.SCR]) (L.inputs ++ Whole.FR L.E :: L.outputs) := by
  refine Shake.covers_of fun r hr => ?_
  simp only [VG.Proof.Ed448.Arm.SignCached.mulRd, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨L.OUT, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.out_in L), Lay.Ok.ob_within (by decide)⟩
  · exact .inl (frame_within _ (by decide))
  · exact .inl (frame_within _ (by decide))
  · exact .inl (Shake.args_within _ (by decide))
  · exact .inr ⟨L.OUT, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.out_in L), Lay.Ok.ob_within (by decide)⟩
  · exact .inr ⟨L.SCR, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.scr_in L), VG.Proof.Ed448.Arm.SignCached.scr_within L⟩

theorem mul_writes (L : VG.Proof.Ed448.Arm.SignCached.Lay) : ∀ r ∈ [L.ob 57 57, L.SCR],
    Whole.Within r (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨L.OUT, VG.Proof.Ed448.Arm.SignCached.out_in L, Lay.Ok.ob_within (by decide)⟩
  · exact .inr ⟨L.SCR, VG.Proof.Ed448.Arm.SignCached.scr_in L, VG.Proof.Ed448.Arm.SignCached.scr_within L⟩

theorem mulAdd_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀) :
    WP isa (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.Arm.scalarMulAdd) t fun u =>
      VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧ Frame (VG.Proof.Ed448.Arm.SignCached.W L [L.ob 57 57, L.SCR]) t.mem u.mem ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out + BitVec.ofNat 64 57) 57 =
        Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt t.mem (State.addr L.out + BitVec.ofNat 64 57) 57)
          (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 K) 57)
          (Spec.Ed448.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 S) 57) := by
  refine WP.seq (WP.mono (hL.kit.setup_ok hc ha
    (args := [(.r0, .caller 0 57), (.r1, .caller 0 57), (.r2, .frame K), (.r3, .frame S)]) (stk := [.caller SC 0])
    (by decide) (by simp only [List.forall_mem_cons]; exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
      valid_frame (by decide), valid_frame (by decide), fun _ h => nomatch h⟩)
    (by simp [preserved]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨⟨by decide, by decide⟩, fun _ h => nomatch h⟩))
    fun u ⟨hu, hm, hs, st, _⟩ => ?_)
  have h0 := hs (.r0, .caller 0 57) (by simp)
  have h1 := hs (.r1, .caller 0 57) (by simp)
  have h2 := hs (.r2, .frame K) (by simp)
  have h3 := hs (.r3, .frame S) (by simp)
  have a0 := st 0 (by simp)
  simp only [argVal, Lay.value, SC, BitVec.add_zero, List.getElem_cons_zero] at h0 h1 h2 h3 a0
  have eo := frame_bytes hm (D := L.ob 57 57) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hL.ko.sub_left (Region.sub_prefix (by decide))).symm.sub_left
      (Lay.Ok.ob_sub (by decide))) (by change 57 ≤ 2 ^ 64; decide)
  have ek := bytes_setup hm (D := L.fr K 57) (Shake.frame_out (by decide) (by decide)) (by change 57 ≤ 2 ^ 64; decide)
  have es := bytes_setup hm (D := L.fr S 57) (Shake.frame_out (by decide) (by decide)) (by change 57 ≤ 2 ^ 64; decide)
  simp only at eo ek es
  refine Whole.call_ok hu scalarMulAdd_ok VG.Proof.Ed448.Arm.SignCached.mulAdd_noFrames (VG.Proof.Ed448.Arm.SignCached.mul_pre hL hu.sp ⟨h0, h1, h2, h3, a0⟩) (VG.Proof.Ed448.Arm.SignCached.mul_covers L)
    (VG.Proof.Ed448.Arm.SignCached.mul_writes L) fun v hv hf hp => ⟨hv, W.call (by decide) hm hf, ?_⟩
  change Spec.Ed448.bytesAt v.mem (State.addr (u.callEntry.gpr .r0)) 57 =
    Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r1)) 57)
      (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r2)) 57)
      (Spec.Ed448.bytesAt u.mem (State.addr (u.callEntry.gpr .r3)) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs),
    h0, h1, h2, h3, hL.ob_addr (by decide), hL.kit.frame_addr (by decide), hL.kit.frame_addr (by decide),
    eo, ek, es] at hp
  exact hp

/-! ## The locals, cleared -/

theorem wipe_step (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) :
    WP isa (.block wipe) t fun u => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 114 = Spec.Ed448.bytesAt t.mem (State.addr L.out) 114 := by
  refine WP.mono (Whole.Ctx.zeroWords hc (by have := hL.top; omega) (start := 2) (count := 60) (by decide))
    fun u ⟨hu, hf, _⟩ => ⟨hu, ?_⟩
  refine frame_bytes hf (D := L.OUT) (fun r hr => ?_) (by change 114 ≤ 2 ^ 64; decide)
  rw [List.mem_singleton.mp hr]
  exact (hL.ko.sub_left (Offset.sub_base _ (by decide : 4 * 2 + 4 * 60 ≤ 280))).symm

end VG.Proof.Ed448.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.SignCached.Body`. -/
section

/-!
# Ed448 signing with a cached public key on ARMv7: the body

`body_ok`: the steps (`Hash.lean`, `Calls.lean`) in order, each keeping
what the later ones read (the header of `dom4`, `s`, the prefix, `r` and
`R`), leave `Spec.Ed448.sign` in `out` (`Proof.Ed448.sign_pipeline`), given
the public key of the private key.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.Ctx Whole.FR Whole.Within)
open VG.Proof.Ed448.Arm.Shake (Kit Args argVal kWr kArgs hdrBytes frame_bytes)
open VG.Proof.Ed448 (BaseLadderOk)

variable {L : VG.Proof.Ed448.Arm.SignCached.Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

/-- The two halves of a 114-byte region. -/
theorem bytes_halves (m : Mem) (p : Addr) :
    Spec.Ed448.bytesAt m p 114 = Spec.Ed448.bytesAt m p 57 ++ Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  simp only [Proof.Ed448.bytesAt_eq]
  exact Proof.X25519.bytesAt_add m p 57 57

theorem drop57 (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 114).drop 57 = Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  rw [VG.Proof.Ed448.Arm.SignCached.bytes_halves]
  exact List.drop_left' (by simp [Spec.Ed448.bytesAt])

theorem disj1 {D r₀ : Region} (h : D.Disjoint r₀) : ∀ r ∈ [r₀], D.Disjoint r := fun r hr => by
  rw [List.mem_singleton.mp hr]; exact h

theorem disj2 {D r₀ r₁ : Region} (h₀ : D.Disjoint r₀) (h₁ : D.Disjoint r₁) : ∀ r ∈ [r₀, r₁], D.Disjoint r :=
  fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h₀
    · rw [List.mem_singleton.mp hr]; exact h₁

/-- Regions of the frame and of `out` that a step keeps. -/
theorem keep {D : Region} (h : VG.Proof.Ed448.Arm.SignCached.Away L D) {ex : List Region} (hx : ∀ r ∈ ex, D.Disjoint r)
    {m m' : Mem} (hf : Frame (VG.Proof.Ed448.Arm.SignCached.W L ex) m m') (hn : D.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m' D.base D.len = Spec.Ed448.bytesAt m D.base D.len := h.bytes hx hf hn

theorem body_ok (hl : BaseLadderOk) (hc : VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ t) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₀)
    (hpk : Spec.Ed448.bytesAt m₀ (State.addr L.pk) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57)) :
    WP isa body t fun u => VG.Proof.Ed448.Arm.SignCached.Ctx L g m₀ u ∧
      Spec.Ed448.bytesAt u.mem (State.addr L.out) 114 =
        Spec.Ed448.sign (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57)
          (Spec.Ed448.bytesAt m₀ (State.addr L.ctx) L.ctxLen.toNat)
          (Spec.Ed448.bytesAt m₀ (State.addr L.msg) L.len.toNat) := by
  have hk := hL.kit
  have n10 : (10 : Nat) ≤ 2 ^ 64 := by decide
  have n57 : (57 : Nat) ≤ 2 ^ 64 := by decide
  -- Regions kept, and the disjointness of each from what the steps write.
  have dHS : (L.fr HDR 10).Disjoint (L.fr S 114) := VG.Proof.Ed448.Arm.SignCached.fr_fr (by decide) (by decide) (by decide)
  have dHS' : (L.fr HDR 10).Disjoint (L.fr S 57) := VG.Proof.Ed448.Arm.SignCached.fr_fr (by decide) (by decide) (by decide)
  have dHH : (L.fr HDR 10).Disjoint (L.fr HASH 114) := VG.Proof.Ed448.Arm.SignCached.fr_fr (by decide) (by decide) (by decide)
  have dHr : (L.fr HDR 10).Disjoint (L.ob 57 57) := (hL.ob_stk (by decide) (by decide)).symm
  have dHc : (L.fr HDR 10).Disjoint L.SCR := hk.stack_scr (by decide)
  have dHR : (L.fr HDR 10).Disjoint L.R0 :=
    (hL.ko.sub_left (Offset.sub_base _ (by decide : 236 + 10 ≤ 280))).sub_right (VG.Proof.Ed448.Arm.SignCached.r0_sub L)
  have dKS : (L.fr K 57).Disjoint (L.fr S 57) := VG.Proof.Ed448.Arm.SignCached.fr_fr (by decide) (by decide) (by decide)
  have dSH : (L.fr S 57).Disjoint (L.fr HASH 114) := VG.Proof.Ed448.Arm.SignCached.fr_fr (by decide) (by decide) (by decide)
  have dSr : (L.fr S 57).Disjoint (L.ob 57 57) := (hL.ob_stk (by decide) (by decide)).symm
  have dSc : (L.fr S 57).Disjoint L.SCR := hk.stack_scr (by decide)
  have dSR : (L.fr S 57).Disjoint L.R0 :=
    (hL.ko.sub_left (Offset.sub_base _ (by decide : 122 + 57 ≤ 280))).sub_right (VG.Proof.Ed448.Arm.SignCached.r0_sub L)
  have dSK : (L.fr S 57).Disjoint (L.fr K 57) := dKS.symm
  have drR : (L.ob 57 57).Disjoint L.R0 := Offset.disjoint_base _ (by decide) (by decide)
  have drc : (L.ob 57 57).Disjoint L.SCR := hL.ob_scr (by decide)
  have drH : (L.ob 57 57).Disjoint (L.fr HASH 114) := hL.ob_stk (by decide) (by decide)
  have drK : (L.ob 57 57).Disjoint (L.fr K 57) := hL.ob_stk (by decide) (by decide)
  have dRH : L.R0.Disjoint (L.fr HASH 114) :=
    ((hL.ko.sub_left (Offset.sub_base _ (by decide : 8 + 114 ≤ 280))).sub_right (VG.Proof.Ed448.Arm.SignCached.r0_sub L)).symm
  have dRK : L.R0.Disjoint (L.fr K 57) :=
    ((hL.ko.sub_left (Offset.sub_base _ (by decide : 179 + 57 ≤ 280))).sub_right (VG.Proof.Ed448.Arm.SignCached.r0_sub L)).symm
  have dRc : L.R0.Disjoint L.SCR := hL.oc.sub_left (VG.Proof.Ed448.Arm.SignCached.r0_sub L)
  have dRr : L.R0.Disjoint (L.ob 57 57) := drR.symm
  have aH := hL.away_hdr
  have aS := hL.away_s
  have ar := hL.away_ob (o := 57) (l := 57) (by decide)
  have aR := hL.away_r0
  -- The header.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.hdr_step hc hL ha) fun t1 ⟨hc1, hh1⟩ => ?_)
  -- `SHAKE256(seed)`, pruned.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.seed_step hc1 hL ha) fun t2 ⟨hc2, hf2, hb2⟩ => ?_)
  have hh2 := VG.Proof.Ed448.Arm.SignCached.keep aH (VG.Proof.Ed448.Arm.SignCached.disj1 dHS) hf2 n10
  simp only at hh2
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.prune_step hc2 hL) fun t3 ⟨hc3, hf3, hs3⟩ => ?_)
  have hh3 := frame_bytes hf3 (D := L.fr HDR 10) (VG.Proof.Ed448.Arm.SignCached.disj1 dHS') n10
  have hp3 := frame_bytes hf3 (D := L.fr K 57) (VG.Proof.Ed448.Arm.SignCached.disj1 dKS) n57
  simp only at hh3 hp3
  have hpfx : Spec.Ed448.bytesAt t3.mem (State.addr L.E + BitVec.ofNat 64 K) 57 =
      (Spec.Sha3.shake256 (Spec.Ed448.bytesAt m₀ (State.addr L.seed) 57) 114).drop 57 := by
    rw [hp3, ← hb2, VG.Proof.Ed448.Arm.SignCached.drop57, Offset.add_add]; rfl
  rw [hb2] at hs3
  -- The nonce's hash, and `r`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.nonce_step hc3 hL ha (by rw [hh3, hh2, hh1])) fun t4 ⟨hc4, hf4, hb4⟩ => ?_)
  have hh4 := VG.Proof.Ed448.Arm.SignCached.keep aH (VG.Proof.Ed448.Arm.SignCached.disj1 dHH) hf4 n10
  have hs4 := VG.Proof.Ed448.Arm.SignCached.keep aS (VG.Proof.Ed448.Arm.SignCached.disj1 dSH) hf4 n57
  simp only at hh4 hs4
  rw [hpfx] at hb4
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.reduceR_step hc4 hL ha) fun t5 ⟨hc5, hf5, hr5⟩ => ?_)
  have hh5 := VG.Proof.Ed448.Arm.SignCached.keep aH (VG.Proof.Ed448.Arm.SignCached.disj2 dHr dHc) hf5 n10
  have hs5 := VG.Proof.Ed448.Arm.SignCached.keep aS (VG.Proof.Ed448.Arm.SignCached.disj2 dSr dSc) hf5 n57
  simp only at hh5 hs5
  rw [hb4] at hr5
  -- `R`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.base_step hl hc5 hL ha) fun t6 ⟨hc6, hf6, hR6⟩ => ?_)
  have hh6 := VG.Proof.Ed448.Arm.SignCached.keep aH (VG.Proof.Ed448.Arm.SignCached.disj2 dHR dHc) hf6 n10
  have hs6 := VG.Proof.Ed448.Arm.SignCached.keep aS (VG.Proof.Ed448.Arm.SignCached.disj2 dSR dSc) hf6 n57
  have hr6 := VG.Proof.Ed448.Arm.SignCached.keep ar (VG.Proof.Ed448.Arm.SignCached.disj2 drR drc) hf6 n57
  simp only at hh6 hs6 hr6
  rw [hr5] at hR6 hr6
  -- The challenge's hash, and `k`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.chal_step hc6 hL ha (by rw [hh6, hh5, hh4, hh3, hh2, hh1]))
    fun t7 ⟨hc7, hf7, hb7⟩ => ?_)
  have hs7 := VG.Proof.Ed448.Arm.SignCached.keep aS (VG.Proof.Ed448.Arm.SignCached.disj1 dSH) hf7 n57
  have hr7 := VG.Proof.Ed448.Arm.SignCached.keep ar (VG.Proof.Ed448.Arm.SignCached.disj1 drH) hf7 n57
  have hR7 := VG.Proof.Ed448.Arm.SignCached.keep aR (VG.Proof.Ed448.Arm.SignCached.disj1 dRH) hf7 n57
  simp only at hs7 hr7 hR7
  rw [hR6] at hb7
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.reduceK_step hc7 hL ha) fun t8 ⟨hc8, hf8, hk8⟩ => ?_)
  have hs8 := VG.Proof.Ed448.Arm.SignCached.keep aS (VG.Proof.Ed448.Arm.SignCached.disj2 dSK dSc) hf8 n57
  have hr8 := VG.Proof.Ed448.Arm.SignCached.keep ar (VG.Proof.Ed448.Arm.SignCached.disj2 drK drc) hf8 n57
  have hR8 := VG.Proof.Ed448.Arm.SignCached.keep aR (VG.Proof.Ed448.Arm.SignCached.disj2 dRK dRc) hf8 n57
  simp only at hs8 hr8 hR8
  rw [hb7] at hk8
  -- `S`.
  refine WP.seq (WP.mono (VG.Proof.Ed448.Arm.SignCached.mulAdd_step hc8 hL ha) fun t9 ⟨hc9, hf9, hS9⟩ => ?_)
  have hR9 := VG.Proof.Ed448.Arm.SignCached.keep aR (VG.Proof.Ed448.Arm.SignCached.disj2 dRr dRc) hf9 n57
  simp only at hR9
  -- The locals, cleared.
  refine WP.mono (VG.Proof.Ed448.Arm.SignCached.wipe_step hc9 hL) fun u ⟨hu, hw⟩ => ⟨hu, ?_⟩
  rw [hw, VG.Proof.Ed448.Arm.SignCached.bytes_halves, hR9, hR8, hR7, hR6, hS9, hr8, hr7, hr6, hk8, hs8, hs7, hs6, hs5, hs4]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ hpk hs3

end VG.Proof.Ed448.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.SignCached.CT`. -/
section

/-!
# Ed448 signing with a cached public key on ARMv7: constant time

As `vg_ed448_verify`'s on this target: two runs from the same pointers,
lengths and `sp` set up the same arguments for every call, each callee is
constant time under its own contract, and the blocks between the calls
address memory only through `sp`, `r12` and `scratch`
(`Proof/Ed448/Arm/Shake/CT.lean`); the positions the absorptions return
depend only on the lengths.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed448.Arm.Shake VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.FR Whole.rel_wp Whole.CallReady Whole.block_cons_ct Whole.block_nil_ct Whole.Within
  Whole.call_ok Whole.zeroWords_ct)
open VG.Proof.Ed448.Arm.Shake (Kit Args argVal kWr kArgs Two Slots valid_const valid_frame frame_within DataOk
  hdr_len)
open VG.Proof.Ed448.Arm (scalarReduceLocal scalarReduce_ok scalarReduce_ct scalarBaseLocal scalarBase_ok
  scalarBase_ct scalarMulAddLocal scalarMulAdd_ok scalarMulAdd_ct)
open VG.Proof.Ed448 (BaseLadderOk)

variable {L : VG.Proof.Ed448.Arm.SignCached.Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

abbrev T2 (L : VG.Proof.Ed448.Arm.SignCached.Lay) (g₁ g₂ : Reg → BitVec 32) (m₁ m₂ : Mem) (P : State → Prop) :=
  Two L.E L.inputs L.outputs g₁ g₂ m₁ m₂ P

/-! ## The hashes -/

theorem seed_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) seedHash (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  obtain ⟨cs, ds⟩ := hL.input_data (R := L.SEED) (D := ⟨State.addr L.seed, 57⟩) (by simp [Lay.inputs])
    ⟨0, (BitVec.add_zero _).symm, by simp⟩
  have e1 : argVal L.E L.value (.caller 1 0) = L.seed := by simp [argVal, Lay.value]
  have e57 : (argVal L.E L.value (.const 57)).toNat = 57 := rfl
  have a := hk.first_ct (g₁ := g₁) (g₂ := g₂) ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) (src := .caller 1 0) (len := .const 57)
    ⟨by decide, by decide⟩ (valid_const (by decide)) (by rw [e1, e57]; exact cs) (by rw [e1, e57]; exact ds.kwr)
    (by rw [e1, e57]; exact hL.ne)
  exact (hk.zeroState_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L)).seq (a.seq ((hk.padStep_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) _
    (Nat.mod_lt _ (by decide))).seq (hk.sqzStep_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) (by decide) (by decide))))

theorem prune_sp_ct : RelCT isa (fun a b => a.sp = b.sp) prune (fun a b => a.sp = b.sp) := by
  unfold prune
  refine RelCT.seq (M := isa) (R := fun a b => a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12) ?_
    ((Shake.r12_ct Impl.Ed448.Arm.PublicKey.pruneOps (by decide) ?_).mono (fun _ _ h => h) (fun _ _ h => h.1))
  · refine Whole.block_cons_ct (fun a b a' b' hp ea eb => ?_) Whole.block_nil_ct
    simp only [exec, S, show 122 < 256 from by decide, ite_true, Option.some.injEq] at ea eb
    subst a' b'
    exact ⟨rfl, hp, congrArg (· + BitVec.ofNat 32 122) hp⟩
  · intro i hi a b h
    simp only [Impl.Ed448.Arm.PublicKey.pruneOps, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [addrs, h]

theorem prune_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) prune (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp (prune_sp_ct.mono (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm)
    (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.Arm.SignCached.prune_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩
    exact WP.mono (VG.Proof.Ed448.Arm.SignCached.prune_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-- An absorption of input data. -/
theorem input_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) (P : Nat) (hP : P < 136)
    {src len : Value} (vs : Shake.valid 12 src) (vl : Shake.valid 12 len) {R : Region} (hR : R ∈ L.inputs)
    (hw : Whole.Within ⟨State.addr (argVal L.E L.value src), (argVal L.E L.value len).toNat⟩ R)
    (hfit : (argVal L.E L.value src).toNat + (argVal L.E L.value len).toNat ≤ 2 ^ 32) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs SC src len))
      (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argVal L.E L.value len).toNat) % 136)) :=
  let h := hL.input_data hR hw
  hL.kit.next_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) P hP vs vl h.1 h.2.kwr hfit

/-- An absorption of the frame's bytes at `d`. -/
theorem local_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) (P : Nat) (hP : P < 136)
    {d k : Nat} (h8 : 8 ≤ d) (hd : d + k ≤ 248) (hk : k < 65536) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 P) (absorb (nextArgs SC (.frame d) (.const k)))
      (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((P + (argVal L.E L.value (.const k)).toNat) % 136)) := by
  have hkn : (argVal L.E L.value (.const k)).toNat = k := by
    simp only [argVal, BitVec.toNat_ofNat]; omega
  have hd' : argVal L.E L.value (.frame d) = L.E + BitVec.ofNat 32 d := rfl
  exact hL.kit.next_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) P hP (valid_frame (by omega)) (valid_const hk)
    (by rw [hd', hkn, hL.kit.frame_addr (by omega)]; exact .inl (frame_within _ hd))
    (by rw [hd', hkn, hL.kit.frame_addr (by omega)]; exact (hL.away_fr h8 hd).kwr)
    (by rw [hd', hkn]; exact hL.kit.frame_fit hd)

theorem hdrAbs_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) (absorb (firstArgs SC (.frame HDR) (.const 10)))
      (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun s => s.gpr .r0 = BitVec.ofNat 32 ((0 + (argVal L.E L.value (.const 10)).toNat) % 136)) := by
  have hd' : argVal L.E L.value (.frame HDR) = L.E + BitVec.ofNat 32 HDR := rfl
  have hkn : (argVal L.E L.value (.const 10)).toNat = 10 := rfl
  exact hL.kit.first_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) (valid_frame (by decide)) (valid_const (by decide))
    (by rw [hd', hkn, hL.kit.frame_addr (by decide)]; exact .inl (frame_within _ (by decide)))
    (by rw [hd', hkn, hL.kit.frame_addr (by decide)]; exact hL.away_hdr.kwr)
    (by rw [hd', hkn]; exact hL.kit.frame_fit (by decide))

theorem nonce_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) nonceHash (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let P1 : Nat := (0 + (argVal L.E L.value (.const 10)).toNat) % 136
  have x2 := VG.Proof.Ed448.Arm.SignCached.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  have x3 := VG.Proof.Ed448.Arm.SignCached.local_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P2 (Nat.mod_lt _ (by decide)) (d := K) (k := 57)
    (by decide) (by decide) (by decide)
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x4 := VG.Proof.Ed448.Arm.SignCached.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
    (len := LEN) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.MSG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, LEN, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, LEN, BitVec.add_zero]; exact hL.nm)
  let P4 : Nat := (P3 + (argVal L.E L.value LEN).toNat) % 136
  exact (hk.zeroState_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L)).seq ((VG.Proof.Ed448.Arm.SignCached.hdrAbs_ct hL ha hb).seq (x2.seq (x3.seq (x4.seq
    ((hk.padStep_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) P4 (Nat.mod_lt _ (by decide))).seq
      (hk.sqzStep_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) (by decide) (by decide)))))))

theorem chal_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) chalHash (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let P1 : Nat := (0 + (argVal L.E L.value (.const 10)).toNat) % 136
  have x2 := VG.Proof.Ed448.Arm.SignCached.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P1 (Nat.mod_lt _ (by decide)) (src := .caller 3 0)
    (len := .caller 4 0) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.CTX) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact hL.nx)
  let P2 : Nat := (P1 + (argVal L.E L.value (.caller 4 0)).toNat) % 136
  have e0 : argVal L.E L.value (.caller 0 0) = L.out := by simp [argVal, Lay.value]
  have e57 : (argVal L.E L.value (.const 57)).toNat = 57 := rfl
  have x3 := hk.next_ct (g₁ := g₁) (g₂ := g₂) ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) P2 (Nat.mod_lt _ (by decide))
    (src := .caller 0 0) (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide))
    (by rw [e0, e57]; exact .inr ⟨L.OUT, List.mem_append_right _ (VG.Proof.Ed448.Arm.SignCached.out_in L), VG.Proof.Ed448.Arm.SignCached.r0_within L⟩)
    (by rw [e0, e57]; exact hL.away_r0.kwr) (by rw [e0, e57]; have := hL.no; omega)
  let P3 : Nat := (P2 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x4 := VG.Proof.Ed448.Arm.SignCached.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P3 (Nat.mod_lt _ (by decide)) (src := .caller 2 0)
    (len := .const 57) ⟨by decide, by decide⟩ (valid_const (by decide)) (R := L.PK) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, BitVec.add_zero]; have := hL.np; simp; omega)
  let P4 : Nat := (P3 + (argVal L.E L.value (.const 57)).toNat) % 136
  have x5 := VG.Proof.Ed448.Arm.SignCached.input_ct (g₁ := g₁) (g₂ := g₂) hL ha hb P4 (Nat.mod_lt _ (by decide)) (src := .caller 5 0)
    (len := LEN) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ (R := L.MSG) (by simp [Lay.inputs])
    (by simp only [argVal, Lay.value, LEN, BitVec.add_zero]; exact ⟨0, (BitVec.add_zero _).symm, by simp⟩)
    (by simp only [argVal, Lay.value, LEN, BitVec.add_zero]; exact hL.nm)
  let P5 : Nat := (P4 + (argVal L.E L.value LEN).toNat) % 136
  exact (hk.zeroState_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L)).seq ((VG.Proof.Ed448.Arm.SignCached.hdrAbs_ct hL ha hb).seq (x2.seq (x3.seq (x4.seq (x5.seq
    ((hk.padStep_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) P5 (Nat.mod_lt _ (by decide))).seq
      (hk.sqzStep_ct ha hb (VG.Proof.Ed448.Arm.SignCached.scr_at L) (by decide) (by decide))))))))

/-! ## The scalar calls -/

/-- A call's arguments, from the slots the set-up gives them. -/
theorem slot_reg {args : List (Reg × Value)} {stk : List Value} {s : State} (h : Slots L.E L.value args stk s)
    {r : Reg} {v : Value} (hm : (r, v) ∈ args) : s.gpr r = argVal L.E L.value v := h.1 _ hm

theorem reduceR_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith reduceRArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
      (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .caller 0 57), (.r1, .frame HASH), (.r2, .caller SC 0)]
  have get : ∀ t, Slots L.E L.value args [] t → VG.Proof.Ed448.Arm.SignCached.ReduceArgs L (L.out + BitVec.ofNat 32 57) (L.E + BitVec.ofNat 32 HASH) t := by
    intro t hs
    have h0 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r0) (v := .caller 0 57) (by simp [args])
    have h1 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r1) (v := .frame HASH) (by simp [args])
    have h2 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
    simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hO : Whole.Within (L.ob 57 57) (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within (L.ob 57 57) R :=
    .inr ⟨L.OUT, VG.Proof.Ed448.Arm.SignCached.out_in L, Lay.Ok.ob_within (by decide)⟩
  refine (hk.setup_ct ha hb args [] (by decide)
    (by simp only [args, List.forall_mem_cons]
        exact ⟨⟨by decide, by decide⟩, valid_frame (by decide), ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct scalarReduce_ok scalarReduce_ct
    (fun t _ h => ⟨[L.fr HASH 114], [L.ob 57 57, L.SCR],
      VG.Proof.Ed448.Arm.SignCached.reduce_pre hL (by rw [hL.ob_addr (by decide)]) (hL.ob_fit (by decide) (by decide))
        (hL.ob_stk (by decide) (by decide)) (hL.ob_scr (by decide)) (get t h),
      VG.Proof.Ed448.Arm.SignCached.reduce_covers hO, VG.Proof.Ed448.Arm.SignCached.reduce_writes hO⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hsp, hg (.r0, .caller 0 57) (by simp [args]), hg (.r1, .frame HASH) (by simp [args]),
      hg (.r2, .caller SC 0) (by simp [args])⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact WP.mono (VG.Proof.Ed448.Arm.SignCached.reduce_call hc hL (by rw [hL.ob_addr (by decide)]) (hL.ob_fit (by decide) (by decide))
      (hL.ob_stk (by decide) (by decide)) (hL.ob_scr (by decide)) hO (get t hs)) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem reduceK_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith reduceKArgs "vg_ed448_scalar_reduce" Impl.Ed448.Arm.scalarReduce)
      (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .frame K), (.r1, .frame HASH), (.r2, .caller SC 0)]
  have get : ∀ t, Slots L.E L.value args [] t → VG.Proof.Ed448.Arm.SignCached.ReduceArgs L (L.E + BitVec.ofNat 32 K) (L.E + BitVec.ofNat 32 HASH) t := by
    intro t hs
    have h0 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r0) (v := .frame K) (by simp [args])
    have h1 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r1) (v := .frame HASH) (by simp [args])
    have h2 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
    simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  have hO : Whole.Within (L.fr K 57) (Whole.FR L.E) ∨ ∃ R ∈ L.outputs, Whole.Within (L.fr K 57) R :=
    .inl (frame_within _ (by decide))
  refine (hk.setup_ct ha hb args [] (by decide)
    (by simp only [args, List.forall_mem_cons]
        exact ⟨valid_frame (by decide), valid_frame (by decide), ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct scalarReduce_ok scalarReduce_ct
    (fun t _ h => ⟨[L.fr HASH 114], [L.fr K 57, L.SCR],
      VG.Proof.Ed448.Arm.SignCached.reduce_pre hL (by rw [hk.frame_addr (by decide)]) (hk.frame_fit (by decide))
        (VG.Proof.Ed448.Arm.SignCached.fr_fr (by decide) (by decide) (by decide)) (hk.stack_scr (by decide)) (get t h),
      VG.Proof.Ed448.Arm.SignCached.reduce_covers hO, VG.Proof.Ed448.Arm.SignCached.reduce_writes hO⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hsp, hg (.r0, .frame K) (by simp [args]), hg (.r1, .frame HASH) (by simp [args]),
      hg (.r2, .caller SC 0) (by simp [args])⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact WP.mono (VG.Proof.Ed448.Arm.SignCached.reduce_call hc hL (by rw [hk.frame_addr (by decide)]) (hk.frame_fit (by decide))
      (VG.Proof.Ed448.Arm.SignCached.fr_fr (by decide) (by decide) (by decide)) (hk.stack_scr (by decide)) hO (get t hs))
      fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

theorem base_ct (hl : BaseLadderOk) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith baseArgs "vg_ed448_scalar_base" Impl.Ed448.Arm.scalarBase)
      (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .caller 0 0), (.r1, .caller 0 57), (.r2, .caller SC 0)]
  have get : ∀ t, Slots L.E L.value args [] t → VG.Proof.Ed448.Arm.SignCached.BaseArgs L t := by
    intro t hs
    have h0 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r0) (v := .caller 0 0) (by simp [args])
    have h1 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r1) (v := .caller 0 57) (by simp [args])
    have h2 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r2) (v := .caller SC 0) (by simp [args])
    simp only [argVal, Lay.value, SC, BitVec.add_zero] at h0 h1 h2
    exact ⟨h0, h1, h2⟩
  refine (hk.setup_ct ha hb args [] (by decide)
    (by simp only [args, List.forall_mem_cons]
        exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, fun _ h => nomatch h⟩)
    (by simp [args, preserved]) (by decide) (by simp)).seq ?_
  apply Shake.Kit.call_ct (scalarBase_ok hl) scalarBase_ct
    (fun t _ h => ⟨[L.ob 57 57], [L.R0, L.SCR], VG.Proof.Ed448.Arm.SignCached.base_pre hL (get t h), VG.Proof.Ed448.Arm.SignCached.base_covers L, VG.Proof.Ed448.Arm.SignCached.base_writes L⟩)
  · intro a b ar aw br bw hsp hg _
    exact ⟨hg (.r0, .caller 0 0) (by simp [args]), hg (.r1, .caller 0 57) (by simp [args]),
      hg (.r2, .caller SC 0) (by simp [args]), hsp⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc (scalarBase_ok hl) VG.Proof.Ed448.Arm.SignCached.base_noFrames (VG.Proof.Ed448.Arm.SignCached.base_pre hL (get t hs)) (VG.Proof.Ed448.Arm.SignCached.base_covers L)
      (VG.Proof.Ed448.Arm.SignCached.base_writes L) fun v hv _ _ => ⟨hv, trivial⟩

theorem mulAdd_ct (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True)
      (callWith mulAddArgs "vg_ed448_scalar_mul_add" Impl.Ed448.Arm.scalarMulAdd)
      (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have hk := hL.kit
  let args : List (Reg × Value) := [(.r0, .caller 0 57), (.r1, .caller 0 57), (.r2, .frame K), (.r3, .frame S)]
  have get : ∀ t, Slots L.E L.value args [.caller SC 0] t → VG.Proof.Ed448.Arm.SignCached.MulArgs L t := by
    intro t hs
    have h0 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r0) (v := .caller 0 57) (by simp [args])
    have h1 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r1) (v := .caller 0 57) (by simp [args])
    have h2 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r2) (v := .frame K) (by simp [args])
    have h3 := VG.Proof.Ed448.Arm.SignCached.slot_reg hs (r := .r3) (v := .frame S) (by simp [args])
    have a0 := hs.2 0 (by simp)
    simp only [argVal, Lay.value, SC, BitVec.add_zero, List.getElem_cons_zero] at h0 h1 h2 h3 a0
    exact ⟨h0, h1, h2, h3, a0⟩
  refine (hk.setup_ct ha hb args [.caller SC 0] (by decide)
    (by simp only [args, List.forall_mem_cons]
        exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, valid_frame (by decide), valid_frame (by decide),
          fun _ h => nomatch h⟩)
    (by simp [args, preserved]) (by decide)
    (by simp only [List.forall_mem_cons]; exact ⟨⟨by decide, by decide⟩, fun _ h => nomatch h⟩)).seq ?_
  apply Shake.Kit.call_ct scalarMulAdd_ok scalarMulAdd_ct
    (fun t he h => ⟨VG.Proof.Ed448.Arm.SignCached.mulRd L, [L.ob 57 57, L.SCR], VG.Proof.Ed448.Arm.SignCached.mul_pre hL he (get t h), VG.Proof.Ed448.Arm.SignCached.mul_covers L, VG.Proof.Ed448.Arm.SignCached.mul_writes L⟩)
  · intro a b ar aw br bw hsp hg ht
    exact ⟨hsp, hg (.r0, .caller 0 57) (by simp [args]), hg (.r1, .caller 0 57) (by simp [args]),
      hg (.r2, .frame K) (by simp [args]), hg (.r3, .frame S) (by simp [args]), ht 0 (by simp)⟩
  · simp [args, linkRegs]
  · intro g m t hc hs
    exact Whole.call_ok hc scalarMulAdd_ok VG.Proof.Ed448.Arm.SignCached.mulAdd_noFrames (VG.Proof.Ed448.Arm.SignCached.mul_pre hL hc.sp (get t hs)) (VG.Proof.Ed448.Arm.SignCached.mul_covers L)
      (VG.Proof.Ed448.Arm.SignCached.mul_writes L) fun v hv _ _ => ⟨hv, trivial⟩

theorem wipe_ct (hL : L.Ok) : RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
    (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine Whole.rel_wp ((Whole.zeroWords_ct 2 60).mono
    (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (fun _ _ _ => trivial)) ?_ ?_
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed448.Arm.SignCached.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩
  · intro t ⟨hc, _⟩; exact WP.mono (VG.Proof.Ed448.Arm.SignCached.wipe_step hc hL) fun _ ⟨hu, _⟩ => ⟨hu, trivial⟩

/-! ## The body -/

theorem body_ct (hl : BaseLadderOk) (hL : L.Ok) (ha : VG.Proof.Ed448.Arm.SignCached.Arguments L m₁) (hb : VG.Proof.Ed448.Arm.SignCached.Arguments L m₂) :
    RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) body (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) := by
  have h : RelCT isa (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) (.block (hdrAt 4 HDR)) (VG.Proof.Ed448.Arm.SignCached.T2 L g₁ g₂ m₁ m₂ fun _ => True) :=
    (hL.kit.hdr_ct (g₁ := g₁) (g₂ := g₂) ha hb (j := 4) (off := HDR) (by decide) hL.cl (by decide)).mono
      (fun _ _ h => h) (fun _ _ h => ⟨⟨h.1.1, trivial⟩, ⟨h.2.1, trivial⟩⟩)
  exact h.seq ((VG.Proof.Ed448.Arm.SignCached.seed_ct hL ha hb).seq ((VG.Proof.Ed448.Arm.SignCached.prune_ct hL).seq ((VG.Proof.Ed448.Arm.SignCached.nonce_ct hL ha hb).seq ((VG.Proof.Ed448.Arm.SignCached.reduceR_ct hL ha hb).seq
    ((VG.Proof.Ed448.Arm.SignCached.base_ct hl hL ha hb).seq ((VG.Proof.Ed448.Arm.SignCached.chal_ct hL ha hb).seq ((VG.Proof.Ed448.Arm.SignCached.reduceK_ct hL ha hb).seq
      ((VG.Proof.Ed448.Arm.SignCached.mulAdd_ct hL ha hb).seq (VG.Proof.Ed448.Arm.SignCached.wipe_ct hL)))))))))

end VG.Proof.Ed448.Arm.SignCached

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.Arm.SignCached.Verified`. -/
section

/-!
# Ed448 signing with a cached public key on ARMv7: the whole function

`signLocal`, the contract the proof is written against; `signCached_ok`, the
frame (`Whole.wrap_ok`) around the body; `signCached_ct`, constant time
(`Whole.wrap_ct`, from `body_ct`); and `signCached_verified`, against
`Spec.Ed448.signCachedContract Arm.abi 280`, given the reference ladder's
agreement with the specification (`BaseLadderOk`), which only the
registration file supplies.
-/

namespace VG.Proof.Ed448.Arm.SignCached

open VG VG.Arm VG.Impl.Ed448.Arm.SignCached VG.Impl.Ed25519.Arm.Whole
open VG.Proof.Ed25519.Arm (Whole.base Whole.base_addr Whole.base_top Whole.stack Whole.Saved Whole.entered
  Whole.saved_ctx Whole.saved_words Whole.saved_frame Whole.bodyRd Whole.bodyWr Whole.wrap_ok Whole.wrap_ct
  Whole.originalWord Whole.Ctx)
open VG.Proof.Ed448 (BaseLadderOk)

/-- `vg_ed448_sign_cached(out = r0, seed = r1, pk = r2, context = r3,
ctxlen = [sp], message = [sp, #4], len = [sp, #8], scratch = [sp, #12])`, with
280 bytes of stack. -/
def signLocal : Contract isa where
  pre s :=
    let out : Region := ⟨State.addr (s.gpr .r0), 114⟩
    let seed : Region := ⟨State.addr (s.gpr .r1), 57⟩
    let pk : Region := ⟨State.addr (s.gpr .r2), 57⟩
    let ctx : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let msg : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 3), 8192⟩
    let args : Region := ⟨State.addr s.sp, 16⟩
    let stk : Region := ⟨State.addr s.sp - 280, 280⟩
    s.rd = [seed, pk, ctx, msg, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint scr ∧ seed.Disjoint out ∧ seed.Disjoint scr ∧ pk.Disjoint out ∧ pk.Disjoint scr ∧
      ctx.Disjoint out ∧ ctx.Disjoint scr ∧ msg.Disjoint out ∧ msg.Disjoint scr ∧
      args.Disjoint out ∧ args.Disjoint scr ∧
      stk.Disjoint out ∧ stk.Disjoint seed ∧ stk.Disjoint pk ∧ stk.Disjoint ctx ∧ stk.Disjoint msg ∧
      stk.Disjoint scr ∧
      (s.gpr .r0).toNat + 114 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 57 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 57 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 32 ∧
      (stackArg s 3).toNat + 8192 ≤ 2 ^ 32 ∧ 280 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat ≤ 255 ∧
      Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57 =
        Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
  post s t := Spec.Ed448.bytesAt t.mem (State.addr (s.gpr .r0)) 114 = Spec.Ed448.sign
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57)
    (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
    (Spec.Ed448.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat)
  pub s t := s.sp = t.sp ∧ s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧
    s.gpr .r3 = t.gpr .r3 ∧ stackArg s 0 = stackArg t 0 ∧ stackArg s 1 = stackArg t 1 ∧
    stackArg s 2 = stackArg t 2 ∧ stackArg s 3 = stackArg t 3

def lay (s : State) : VG.Proof.Ed448.Arm.SignCached.Lay :=
  ⟨s.gpr .r0, s.gpr .r1, s.gpr .r2, s.gpr .r3, stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
    Whole.base s⟩

section
variable {s : State} (h : signLocal.pre s)
include h

theorem entry_below : 280 ≤ s.sp.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hb, _⟩ := h
  exact hb

theorem entry_top : s.sp.toNat + 16 ≤ 2 ^ 32 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _⟩ := h
  exact ht

theorem original_args : (VG.Proof.Ed448.Arm.SignCached.lay s).ORIG = ⟨State.addr s.sp, 16⟩ := by
  unfold Lay.ORIG VG.Proof.Ed448.Arm.SignCached.lay
  rw [Whole.base_addr (VG.Proof.Ed448.Arm.SignCached.entry_below h)]
  congr 1
  rw [show (280 : Addr) = BitVec.ofNat 64 280 from rfl, BitVec.sub_add_cancel]

theorem stack_eq : Whole.stack s = ⟨State.addr s.sp - 280, 280⟩ := by
  unfold Whole.stack
  rw [Whole.base_addr (VG.Proof.Ed448.Arm.SignCached.entry_below h)]

theorem entry_writes : ∀ r ∈ s.wr, (Whole.stack s).Disjoint r := by
  have hs := VG.Proof.Ed448.Arm.SignCached.stack_eq h
  obtain ⟨_, hw, _, _, _, _, _, _, _, _, _, _, _, ko, _, _, _, _, kc, _⟩ := h
  intro r hr
  rw [hw] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hs]
  rcases hr with rfl | rfl
  · exact ko
  · exact kc

theorem lay_ok : (VG.Proof.Ed448.Arm.SignCached.lay s).Ok := by
  have hb := VG.Proof.Ed448.Arm.SignCached.entry_below h
  have ht := VG.Proof.Ed448.Arm.SignCached.entry_top h
  have ho := VG.Proof.Ed448.Arm.SignCached.original_args h
  have hs : (VG.Proof.Ed448.Arm.SignCached.lay s).STK = ⟨State.addr s.sp - 280, 280⟩ := by
    unfold Lay.STK; rw [show State.addr (VG.Proof.Ed448.Arm.SignCached.lay s).E = State.addr (Whole.base s) from rfl, Whole.base_addr hb]
  obtain ⟨_, _, oc, eo, ec, po, pc, xo, xc, mo, mc, ao, ac, ko, ke, kp, kx, km, kc, no, ne, np, nx, nm, nc,
    _, _, cl, _⟩ := h
  refine ⟨?_, by change (stackArg s 0).toNat < 256; omega, oc, eo, ec, po, pc, xo, xc, mo, mc,
    by rw [ho]; exact ao, by rw [ho]; exact ac, by rw [hs]; exact ko, by rw [hs]; exact ke,
    by rw [hs]; exact kp, by rw [hs]; exact kx, by rw [hs]; exact km, by rw [hs]; exact kc,
    no, ne, np, nx, nm, nc⟩
  have := Whole.base_top hb
  change (Whole.base s).toNat + 296 ≤ 2 ^ 32
  omega

theorem entry_regions : (VG.Proof.Ed448.Arm.SignCached.lay s).inputs = Whole.bodyRd s ∧ (VG.Proof.Ed448.Arm.SignCached.lay s).outputs = s.wr := by
  simp only [Lay.inputs, VG.Proof.Ed448.Arm.SignCached.original_args h]
  simp only [Whole.bodyRd, h.1, Lay.outputs, h.2.1, Lay.SEED, Lay.PK, Lay.CTX, Lay.MSG, Lay.OUT, Lay.SCR,
    Lay.ARGS, VG.Proof.Ed448.Arm.SignCached.lay, List.cons_append, List.nil_append]
  exact ⟨trivial, trivial⟩

theorem entry_ctx {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    VG.Proof.Ed448.Arm.SignCached.Ctx (VG.Proof.Ed448.Arm.SignCached.lay s) s.gpr p.mem (p.withRegions (Whole.bodyRd s) (Whole.bodyWr s)) := by
  have hc := Whole.saved_ctx hp
  change Whole.Ctx (Whole.base s) s.gpr p.mem (VG.Proof.Ed448.Arm.SignCached.lay s).inputs (VG.Proof.Ed448.Arm.SignCached.lay s).outputs _
  rw [(VG.Proof.Ed448.Arm.SignCached.entry_regions h).1, (VG.Proof.Ed448.Arm.SignCached.entry_regions h).2]
  exact hc

/-- The caller's stack argument `j - 6`, at `E + 248 + 4 j`, where the caller put it. -/
theorem caller_word {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) {j : Nat} (hj : 10 ≤ j) (hj' : j < 12) :
    p.mem.readW (State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j)) 32 = stackArg s (j - 8) := by
  have hb := VG.Proof.Ed448.Arm.SignCached.entry_below h
  have ht := VG.Proof.Ed448.Arm.SignCached.entry_top h
  have hf := Whole.saved_frame hb hp
  have hbt := Whole.base_top hb
  have ea : State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j) =
      State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 8))) := by
    rw [addr_add (by omega), Whole.base_addr hb, show 248 + 4 * j = 280 + 4 * (j - 8) by omega,
      ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, show (280 : Addr) = BitVec.ofNat 64 280 from rfl,
      BitVec.sub_add_cancel]
  rw [hf.readW (r := ⟨State.addr (Whole.base s) + BitVec.ofNat 64 (248 + 4 * j), 4⟩) (Region.contains_self _ _)
    (by
      rintro r hr
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint_base _ (by omega) (by omega)) (by decide), ea]
  rfl

theorem entry_args {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) : VG.Proof.Ed448.Arm.SignCached.Arguments (VG.Proof.Ed448.Arm.SignCached.lay s) p.mem := by
  have hb := VG.Proof.Ed448.Arm.SignCached.entry_below h
  have ht := VG.Proof.Ed448.Arm.SignCached.entry_top h
  intro j hj
  obtain ⟨hj12, hj | hj⟩ := hj
  · have hw := Whole.saved_words hb (by decide : 6 ≤ 6) (by omega) hp hj
    have he : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa only [Whole.originalWord, Impl.Ed25519.Arm.Whole.argReg, Nat.reduceLT, ite_true, ite_false,
        Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, BitVec.add_zero, Lay.value, VG.Proof.Ed448.Arm.SignCached.lay, stackArg, stackArgAddr] using hw
  · have he : j = 10 ∨ j = 11 := by omega
    rcases he with rfl | rfl
    · exact VG.Proof.Ed448.Arm.SignCached.caller_word h hp (by decide) (by decide)
    · exact VG.Proof.Ed448.Arm.SignCached.caller_word h hp (by decide) (by decide)

theorem entry_read : ∀ j < 6, 4 ≤ j →
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * (j - 4)))) 4 := by
  have ht := VG.Proof.Ed448.Arm.SignCached.entry_top h
  intro j hj h4
  refine ⟨⟨State.addr s.sp, 16⟩, List.mem_append_left _ (by rw [h.1]; simp), ?_⟩
  rw [addr_add (by have := s.sp.isLt; omega)]
  exact Offset.contains_base _ (d := 4 * (j - 4)) (by omega) (by omega)

theorem entry_input {m : Mem} (hf : Frame [Whole.stack s] s.mem m) {r : Region} (hr : r ∈ s.rd)
    (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed448.bytesAt m r.base r.len = Spec.Ed448.bytesAt s.mem r.base r.len := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => hf.bytes ?_ hn (List.mem_range.mp hi)
  rintro R hR
  rw [List.mem_singleton.mp hR, VG.Proof.Ed448.Arm.SignCached.stack_eq h]
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, ke, kp, kx, km, _⟩ := h
  rw [hrd] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ke.symm
  · exact kp.symm
  · exact kx.symm
  · exact km.symm
  · exact Offset.base_disjoint_below _ (n := 280) (k := 16) (by decide)

theorem entry_key {p : State} (hp : Whole.Saved (Whole.entered s) 6 p) :
    Spec.Ed448.bytesAt p.mem (State.addr (VG.Proof.Ed448.Arm.SignCached.lay s).pk) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (State.addr (VG.Proof.Ed448.Arm.SignCached.lay s).seed) 57) := by
  have hk : Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r2)) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (State.addr (s.gpr .r1)) 57) := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hk⟩ := h
    exact hk
  have hf := Whole.saved_frame (VG.Proof.Ed448.Arm.SignCached.entry_below h) hp
  have hp' := VG.Proof.Ed448.Arm.SignCached.entry_input h hf (r := ⟨State.addr (s.gpr .r2), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  have hs' := VG.Proof.Ed448.Arm.SignCached.entry_input h hf (r := ⟨State.addr (s.gpr .r1), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  change Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r2)) 57 =
    Spec.Ed448.publicKey (Spec.Ed448.bytesAt p.mem (State.addr (s.gpr .r1)) 57)
  simp only at hp' hs'
  rw [hp', hs']
  exact hk

end

theorem body_noFrames : body.noFrames = true := by
  simp only [body, seedHash, prune, nonceHash, chalHash, Impl.Ed448.Arm.Shake.zeroState,
    Impl.Ed448.Arm.Shake.absorb, Impl.Ed448.Arm.Shake.pad, Impl.Ed448.Arm.Shake.squeeze, callWith,
    Code.noFrames, Bool.and_self]
  rw [PublicKey.absorb_noFrames, PublicKey.pad_noFrames, PublicKey.squeeze_noFrames, VG.Proof.Ed448.Arm.SignCached.reduce_noFrames,
    VG.Proof.Ed448.Arm.SignCached.base_noFrames, VG.Proof.Ed448.Arm.SignCached.mulAdd_noFrames]
  rfl

theorem signCached_ok (hl : BaseLadderOk) {s : State} (h : signLocal.pre s) :
    WP isa VG.Impl.Ed448.Arm.SignCached.code s fun u => abiPreserved s u ∧ signLocal.post s u := by
  have hw := Whole.wrap_ok VG.Proof.Ed448.Arm.SignCached.body_noFrames (by decide : 6 ≤ 6) (VG.Proof.Ed448.Arm.SignCached.entry_below h)
    (by have := VG.Proof.Ed448.Arm.SignCached.entry_top h; omega) (VG.Proof.Ed448.Arm.SignCached.entry_read h) (VG.Proof.Ed448.Arm.SignCached.entry_writes h)
    (P := fun m m' _ => Spec.Ed448.bytesAt m' (State.addr (s.gpr .r0)) 114 = Spec.Ed448.sign
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r1)) 57)
      (Spec.Ed448.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
      (Spec.Ed448.bytesAt m (State.addr (stackArg s 1)) (stackArg s 2).toNat))
    (fun p hp => WP.mono (VG.Proof.Ed448.Arm.SignCached.body_ok hl (VG.Proof.Ed448.Arm.SignCached.entry_ctx h hp) (VG.Proof.Ed448.Arm.SignCached.lay_ok h) (VG.Proof.Ed448.Arm.SignCached.entry_args h hp) (VG.Proof.Ed448.Arm.SignCached.entry_key h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (VG.Proof.Ed448.Arm.SignCached.lay s).inputs (VG.Proof.Ed448.Arm.SignCached.lay s).outputs u at hu
        rw [(VG.Proof.Ed448.Arm.SignCached.entry_regions h).1, (VG.Proof.Ed448.Arm.SignCached.entry_regions h).2] at hu
        exact hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have e1 := VG.Proof.Ed448.Arm.SignCached.entry_input h hf (r := ⟨State.addr (s.gpr .r1), 57⟩) (by rw [h.1]; simp) (by change 57 ≤ 2 ^ 64; decide)
  have e3 := VG.Proof.Ed448.Arm.SignCached.entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 0).toNat ≤ 2 ^ 64; have := (stackArg s 0).isLt; omega)
  have e5 := VG.Proof.Ed448.Arm.SignCached.entry_input h hf (r := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩) (by rw [h.1]; simp)
    (by change (stackArg s 2).toNat ≤ 2 ^ 64; have := (stackArg s 2).isLt; omega)
  change Spec.Ed448.bytesAt u.mem (State.addr (s.gpr .r0)) 114 = _
  simp only at e1 e3 e5
  rw [hp, e1, e3, e5]

theorem lay_eq {s t : State} (hp : signLocal.pub s t) : VG.Proof.Ed448.Arm.SignCached.lay s = VG.Proof.Ed448.Arm.SignCached.lay t := by
  obtain ⟨sp, h0, h1, h2, h3, a0, a1, a2, a3⟩ := hp
  simp only [VG.Proof.Ed448.Arm.SignCached.lay, Whole.base, sp, h0, h1, h2, h3, a0, a1, a2, a3]

theorem signCached_ct (hl : BaseLadderOk) : ConstantTime isa signLocal.pre signLocal.pub VG.Impl.Ed448.Arm.SignCached.code := by
  refine Whole.wrap_ct (by decide : 6 ≤ 6) (fun _ _ hp => hp.1) (fun _ hs => VG.Proof.Ed448.Arm.SignCached.entry_below hs)
    (fun _ hs => by have := VG.Proof.Ed448.Arm.SignCached.entry_top hs; omega) (fun _ hs => VG.Proof.Ed448.Arm.SignCached.entry_read hs) ?_ ?_
  · intro s hs p hp
    exact WP.mono (VG.Proof.Ed448.Arm.SignCached.body_ok hl (VG.Proof.Ed448.Arm.SignCached.entry_ctx hs hp) (VG.Proof.Ed448.Arm.SignCached.lay_ok hs) (VG.Proof.Ed448.Arm.SignCached.entry_args hs hp) (VG.Proof.Ed448.Arm.SignCached.entry_key hs hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := VG.Proof.Ed448.Arm.SignCached.lay_eq hp
    have hq : VG.Proof.Ed448.Arm.SignCached.Ctx (VG.Proof.Ed448.Arm.SignCached.lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ VG.Proof.Ed448.Arm.SignCached.entry_ctx ht hqb
    have hqa : VG.Proof.Ed448.Arm.SignCached.Arguments (VG.Proof.Ed448.Arm.SignCached.lay s) q.mem := he ▸ VG.Proof.Ed448.Arm.SignCached.entry_args ht hqb
    exact ⟨(VG.Proof.Ed448.Arm.SignCached.body_ct hl (VG.Proof.Ed448.Arm.SignCached.lay_ok hs) (VG.Proof.Ed448.Arm.SignCached.entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨⟨VG.Proof.Ed448.Arm.SignCached.entry_ctx hs hpa, trivial⟩, ⟨hq, trivial⟩⟩ ea eb).1, trivial⟩

/-! ## The contract -/

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey VG.Proof.Ed448.Arm.SignCached.satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [VG.Proof.Ed448.Arm.SignCached.satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, `scratch`'s address `0x10000` as the fourth
argument on the stack, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a = 0x900E then 1 else if a.toNat < 0x3000 ∨ 0x3039 ≤ a.toNat then 0 else VG.Proof.Ed448.Arm.SignCached.satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed448.bytesAt VG.Proof.Ed448.Arm.SignCached.satMem 0x2000 57 = VG.Proof.Ed448.Arm.SignCached.satSeed := by
  unfold VG.Proof.Ed448.Arm.SignCached.satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  have hne : (0x2000 : Addr) + BitVec.ofNat 64 i ≠ 0x900E := fun h => by
    have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
  simp only [VG.Proof.Ed448.Arm.SignCached.satMem, hne, ↓reduceIte, ha, show 0x2000 + i < 0x3000 from by omega, true_or]

theorem sat_key : Spec.Ed448.bytesAt VG.Proof.Ed448.Arm.SignCached.satMem 0x3000 57 = VG.Proof.Ed448.Arm.SignCached.satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, VG.Proof.Ed448.Arm.SignCached.satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    have hne : (0x3000 : Addr) + BitVec.ofNat 64 i ≠ 0x900E := fun h => by
      have := congrArg BitVec.toNat h; rw [ha] at this; simp at this; omega
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, VG.Proof.Ed448.Arm.SignCached.satMem, hne, ↓reduceIte, ha,
      show ¬ (0x3000 + i < 0x3000 ∨ 0x3039 ≤ 0x3000 + i) from by omega, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

theorem sat_pk : Spec.Ed448.bytesAt VG.Proof.Ed448.Arm.SignCached.satMem 0x3000 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt VG.Proof.Ed448.Arm.SignCached.satMem 0x2000 57) := by
  rw [VG.Proof.Ed448.Arm.SignCached.sat_seed, VG.Proof.Ed448.Arm.SignCached.sat_key]
  rfl

def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | .r3 => 0x4000 | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem := VG.Proof.Ed448.Arm.SignCached.satMem
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0, 0⟩, ⟨0x9000, 16⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩]

theorem sat : ∃ s, (Spec.Ed448.signCachedContract Arm.abi 280).pre s := by
  refine ⟨VG.Proof.Ed448.Arm.SignCached.satState, ?_⟩
  sig_apply_check
  · decide +kernel
  · sig_reduce [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, VG.Proof.Ed448.Arm.SignCached.satState]
    sig_and_intros
    all_goals try exact VG.Proof.Ed448.Arm.SignCached.sat_pk
    all_goals decide +kernel

theorem sign_implies : signLocal.Implies (Spec.Ed448.signCachedContract Arm.abi 280) where
  pre := by
    intro s h
    sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.SignCached.signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr] at h
    sig_split h
    sig_reduce [VG.Proof.Ed448.Arm.SignCached.signLocal, Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
    sig_simp [] []
    simp only [BitVec.add_zero, show (280#64) = (280 : Addr) from rfl] at *
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.SignCached.signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  pub := by
    sig_implies_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, VG.Proof.Ed448.Arm.SignCached.signLocal, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, Arm.stackArg, Arm.stackArgAddr]
  sat := VG.Proof.Ed448.Arm.SignCached.sat

/-- `vg_ed448_sign_cached` on ARMv7, given the reference ladder's agreement
with the specification. -/
theorem signCached_verified (hl : BaseLadderOk) :
    Verified Arm.target VG.Impl.Ed448.Arm.SignCached.code (Spec.Ed448.signCachedContract Arm.abi 280) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => VG.Proof.Ed448.Arm.SignCached.signCached_ok hl h) (VG.Proof.Ed448.Arm.SignCached.signCached_ct hl) (.refl sign_implies.sat_left))
    VG.Proof.Ed448.Arm.SignCached.sign_implies

end VG.Proof.Ed448.Arm.SignCached

end
