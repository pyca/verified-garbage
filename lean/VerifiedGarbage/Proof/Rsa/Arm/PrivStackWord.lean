module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
import VerifiedGarbage.Proof.Bignum.Arm.Stack
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Copy an incoming stack argument into the outgoing call area -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

theorem PrivContext.readArg {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) {j : Nat} (hj : j < 16) :
    InRegions (s.rd ++ s.wr) (off (State.addr g.stack) (arg j)) 4 := by
  have read := CallLay.inRegions_sub (off := 4 * j) h.argumentsRead (l := 4) (by omega) (by decide)
  have address : g.argumentsRegion.base + BitVec.ofNat 64 (4 * j) = off (State.addr g.stack) (arg j) :=
    Offset.add_add _ (frameBytes + 56) (4 * j)
  rw [address] at read
  exact read

theorem copyArg_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    {j : Nat} (hj : j < 14) (ptr : s.gpr .r12 = g.stack) :
    WP isa (.block (copyArg j)) s fun t =>
      t.mem = s.mem.writeW (off (State.addr g.stack) (4 * j)) (g.argument (j + 2)) ∧
      Rest [.r0] s t := by
  have fit := h.valid.stackHigh
  unfold copyArg
  refine wp_loadStack (a := off (State.addr g.stack) (arg (j + 2)))
    (by simp only [arg, frameBytes]; omega)
    (by rw [h.sp]; exact addr_add (by simp only [arg, frameBytes] at *; omega))
    (h.readArg (by omega)) fun u a => ?_
  refine wp_str (a := off (State.addr g.stack) (4 * j)) (by omega)
    (by rw [a.other .r12 (by decide), ptr]; exact addr_add (by simp only [frameBytes] at *; omega))
    (by rw [a.wr]; exact h.inner.write (by simp only [frameBytes]; omega)) fun t b => WP.block_nil ?_
  exact ⟨by rw [b.mem, a.gpr, a.mem, h.arguments (j + 2) (by omega)], (a.rest (by simp)).trans (b.rest _)⟩

theorem outgoing_frame {g : PrivGeometry} {m : Mem} {j : Nat} {v : BitVec 32} (hj : j < 14) :
    Frame [⟨State.addr g.stack, 56⟩] m (m.writeW (off (State.addr g.stack) (4 * j)) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem copyArg_context (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte} (h : PrivContext g bs s)
    (slots : PrivSlots g s.mem) {j : Nat} (hj : j < 14) (ptr : s.gpr .r12 = g.stack) :
    WP isa (.block (copyArg j)) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      t.mem = s.mem.writeW (off (State.addr g.stack) (4 * j)) (g.argument (j + 2)) ∧ Rest [.r0] s t := by
  refine WP.mono (copyArg_ok s h hj ptr) ?_
  rintro t ⟨mem, rest⟩
  have frame : Frame [⟨State.addr g.stack, 56⟩] s.mem t.mem := by rw [mem]; exact outgoing_frame hj
  refine ⟨h.after (frame.sub ?_) rest, slots.after frame ?_, mem, rest⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 56 ≤ frameBytes)⟩
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint_base _ (by decide : 56 ≤ 64) (by decide : 64 + 24 ≤ 2 ^ 64)
end VG.Proof.Rsa.Arm
