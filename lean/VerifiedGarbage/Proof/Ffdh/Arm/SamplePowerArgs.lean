module

import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyPower
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! # Load the selected public scalar layout from saved arguments -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem samplePowerArgs_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    (h : SampleContext p l slots s) (_stable : stableSlots slots = true)
    (h56 : 56 ∈ slots) (h32 : 32 ∈ slots) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs 56 16 20)) s fun t =>
      (t.gpr .r4 = p.g ∧ t.gpr .r6 = BitVec.ofNat 32 p.k ∧
        t.gpr .r1 = l.start ∧ t.gpr .r2 = BitVec.ofNat 32 l.width ∧ t.mem = s.mem) ∧
      Rest [.r1, .r2, .r4, .r6] s t := by
  have bounds (d : Nat) (hd : d ≤ 68) : d + 4 ≤ 72 := by omega
  have addr (d : Nat) (hd : d ≤ 68) :
      State.addr (s.sp + BitVec.ofNat 32 d) = off (State.addr s.sp) d :=
    VG.Arm.addr_add (by have := h.locals.space.nowrap; omega)
  have rb := h.locals.read (bounds 56 (by decide))
  have re := h.locals.read (bounds 16 (by decide))
  have rc := h.locals.read (bounds 20 (by decide))
  have rk := h.locals.read (bounds 32 (by decide))
  have vb := h.saved 56 h56
  have ve := h.scalarStart
  have vc := h.scalarWidth
  have vk := h.saved 32 h32
  change s.mem.readW (off (State.addr s.sp) 56) 32 = p.g at vb
  change s.mem.readW (off (State.addr s.sp) 32) 32 = BitVec.ofNat 32 p.k at vk
  refine withRest_all [.r1, .r2, .r4, .r6] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.Domain.powerArgs
  ffrun [addr 56 (by decide), addr 16 (by decide), addr 20 (by decide), addr 32 (by decide),
    rb, re, rc, rk, vb, ve, vc, vk, off]

theorem samplePowerArgs_input (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    {P : State → Prop} {regions : List Region} {eb : List Byte}
    (A : TwoExp.Montgomery p.base p.len p.w P regions)
    (stable : stableSlots slots = true) (h56 : 56 ∈ slots) (h32 : 32 ∈ slots)
    (context : SampleContext p l slots s) (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P) (odd : p.P % 2 = 1)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (exponent : Octets p.base l.start p.len eb s) (size : eb.length = l.width)
    (hp : P s) (separate : ∀ r ∈ regions, Region.Disjoint ⟨State.addr l.start, eb.length⟩ r) :
    WP isa (.block (VG.Impl.Ffdh.Arm.Domain.powerArgs 56 16 20)) s fun t =>
      KeyPower.Input p.base p.g l.start p.len p.w p.P P regions ((p.dom.drop p.k).take p.k) eb t ∧
        t.mem = s.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (samplePowerArgs_ok s context stable h56 h32) ?_
  rintro t ⟨⟨source, count, pointer, exponentCount, mem⟩, rest⟩
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  have readyT := ready.of_mem mem rest ((rest.gpr .r0 (by simp)).trans ready.ptr)
  refine ⟨⟨⟨readyT, ?_, odd, ?_, context.gBytes.after_workspace frame rest,
    exponent.after_workspace frame rest, ?_, ?_, ?_, ?_, source, ?_, pointer, ?_⟩,
    A.stable frame (rest.mono (by simp [roundClobbers])) hp, separate⟩, mem,
    rest.mono (by simp [roundClobbers])⟩
  · rw [mem]; exact modulus
  · rw [mem]; exact r2
  · rw [p.gLength]; have := p.minLength; omega
  · rw [p.gLength]; exact p.width.2.2.2.1
  · rw [size]; exact l.width_bounds.1
  · rw [size]; have := l.width_bounds; have := p.maxLength; omega
  · rw [p.gLength]; exact count
  · rw [size]; exact exponentCount

end VG.Proof.Ffdh.Arm
