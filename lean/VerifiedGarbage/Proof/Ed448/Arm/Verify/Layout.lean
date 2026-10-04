import VerifiedGarbage.Impl.Ed448.Arm.Verify
import VerifiedGarbage.Proof.Ed448.Arm.Shake.Layout
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Layout
import VerifiedGarbage.Spec.Ed448.Contract

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
      Offset.contains _ (e := 248) (k := 24) (by omega) (by omega) (by decide)⟩
  · exact ⟨L.ORIG, by simp [Lay.inputs],
      Offset.contains _ (e := 280) (k := 12) (by omega) (by omega) (by decide)⟩

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
  have hE : Fits L.E 11 := ⟨by decide, by decide, by have := hL.top; omega⟩
  refine WP.mono (Ctx.setup hc hE hn hv hs hvs
    (fun j hj => let ⟨R, hR, hcon⟩ := slot_mem L hj; ⟨R, hR, hcon⟩) hr)
    fun u ⟨hu, hm, hregs, hstk, hk⟩ => ⟨hu, Frame.sub hm fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩, ?_, ?_, hk⟩
  · intro p hp
    rw [hregs p hp, value_eq hc hL ha (hv p hp)]
  · intro j hj
    rw [hstk j hj, value_eq hc hL ha (hvs _ (List.getElem_mem hj))]

/-- What the calls need of the layout (`Proof/Ed448/Arm/Shake/Layout.lean`). -/
theorem Lay.Ok.kit (hL : L.Ok) : Kit L.E L.scr 11 L.inputs L.outputs :=
  ⟨⟨by decide, by decide, by have := hL.top; omega⟩, hL.nc, by simp [Lay.outputs], hL.kc,
    fun _ hr R hR => hL.inputs_out hr R hR, fun _ hj => slot_mem L hj⟩

end VG.Proof.Ed448.Arm.Verify
