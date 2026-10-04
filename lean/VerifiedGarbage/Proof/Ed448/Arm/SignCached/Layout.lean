import VerifiedGarbage.Impl.Ed448.Arm.SignCached
import VerifiedGarbage.Proof.Ed448.Arm.Shake.Sponge

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
variable (L : Lay)
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

abbrev Ctx (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) :=
  Whole.Ctx L.E g m₀ L.inputs L.outputs t

/-- The saved words, and `len` and `scratch` where the caller put them. -/
abbrev Arguments (L : Lay) (m : Mem) : Prop := Args L.E 12 L.value m

variable {L : Lay}

theorem frame_sub (L : Lay) : Region.Sub (Whole.FR L.E) L.STK := Region.sub_prefix (by decide : 248 ≤ 280)
theorem args_sub (L : Lay) : Region.Sub L.ARGS L.STK := Offset.sub_base _ (by decide : 248 + 24 ≤ 280)

theorem slot_mem (L : Lay) {j : Nat} (hj : Slot 12 j) :
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
    · exact hL.ko.sub_left (args_sub L)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.ec
    · exact hL.pc
    · exact hL.xc
    · exact hL.mc
    · exact hL.ac
    · exact hL.kc.sub_left (args_sub L)
  · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hL.ke.sub_left (frame_sub L)).symm
    · exact (hL.kp.sub_left (frame_sub L)).symm
    · exact (hL.kx.sub_left (frame_sub L)).symm
    · exact (hL.km.sub_left (frame_sub L)).symm
    · exact orig_fr
    · exact Offset.disjoint_base _ (by decide : 248 ≤ 248) (by decide : 248 + 24 ≤ 2 ^ 64)

/-- What the calls need of the layout. -/
theorem kit : Kit L.E L.scr 12 L.inputs L.outputs :=
  ⟨⟨by decide, by decide, by have := hL.top; omega⟩, hL.nc, by simp [Lay.outputs], hL.kc,
    fun _ hr R hR => hL.inputs_out hr R hR, fun _ hj => slot_mem L hj⟩

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
abbrev Lay.R0 (L : Lay) : Region := ⟨State.addr L.out, 57⟩

theorem r0_sub (L : Lay) : Region.Sub L.R0 L.OUT := Region.sub_prefix (by decide)
theorem r0_within (L : Lay) : Whole.Within L.R0 L.OUT := ⟨0, (BitVec.add_zero _).symm, by change 0 + 57 ≤ 114; decide⟩
theorem scr_within (L : Lay) : Whole.Within L.SCR L.SCR := ⟨0, (BitVec.add_zero _).symm, by simp⟩

theorem out_in (L : Lay) : L.OUT ∈ L.outputs := by simp [Lay.outputs]
theorem scr_in (L : Lay) : L.SCR ∈ L.outputs := by simp [Lay.outputs]

/-- Two regions of the frame. -/
theorem fr_fr {d l e k : Nat} (h : d + l ≤ e ∨ e + k ≤ d) (hd : d + l ≤ 280) (he : e + k ≤ 280) :
    (L.fr d l).Disjoint (L.fr e k) := Offset.disjoint _ h (by omega) (by omega)

/-- Outside what a call of a sponge function writes but its squeezed output:
the outgoing stack arguments, the state and the working space. -/
structure Away (L : Lay) (D : Region) : Prop where
  args : (kArgs L.E 8).Disjoint D
  kwr : ∀ r ∈ kWr L.scr, D.Disjoint r

theorem Away.zero {D : Region} (h : Away L D) : ∀ r ∈ [(⟨State.addr L.scr, 200⟩ : Region)], D.Disjoint r :=
  fun r hr => h.kwr r (by rw [List.mem_singleton.mp hr]; simp [kWr])

theorem Away.abs {D : Region} (h : Away L D) : ∀ r ∈ kArgs L.E 8 :: kWr L.scr, D.Disjoint r := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.args.symm
  · exact h.kwr r hr

theorem Away.sqz {D : Region} (h : Away L D) {d : Nat} (hd : D.Disjoint (L.fr d 114)) :
    ∀ r ∈ kArgs L.E 8 :: sqzWr L.E L.scr d, D.Disjoint r := by
  intro r hr
  simp only [sqzWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.args.symm
  · exact h.kwr _ (by simp [kWr])
  · exact hd
  · exact h.kwr _ (by simp [kWr])

theorem Lay.Ok.away_fr (hL : L.Ok) {d l : Nat} (h8 : 8 ≤ d) (hd : d + l ≤ 248) : Away L (L.fr d l) :=
  ⟨Offset.base_disjoint _ h8 (by omega), hL.kit.frame_kWr (by omega)⟩

theorem Lay.Ok.away_ob (hL : L.Ok) {o l : Nat} (ho : o + l ≤ 114) : Away L (L.ob o l) :=
  ⟨(hL.ko.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.Ok.ob_sub ho), hL.ob_kWr ho⟩

theorem Lay.Ok.away_r0 (hL : L.Ok) : Away L L.R0 :=
  ⟨(hL.ko.sub_left (Region.sub_prefix (by decide))).sub_right (r0_sub L),
    fun r hr => (hL.oc.sub_left (r0_sub L)).sub_right (kWr_sub L.scr r hr).sub⟩

end VG.Proof.Ed448.Arm.SignCached
