module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Field
import VerifiedGarbage.Proof.Ed25519.AArch64.Sub

/-!
# Field operations with one fold, on small slots

Untrusted: everything here is checked by Lean. `fieldAdd1` and `fieldSub1` on
slots that `Small` bounds, for code that uses them outside `fieldCode`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.X25519

/-- `fieldAdd1` on small slots. -/
theorem add1Slot_ok {s : State} {base : Addr} (hs : Scr s base large) (o a b : Slot) {S : Slot → Bool}
    (hS : Small s.mem base S) (ha : S a = true) (hb : S b = true) :
    WP isa (.block (fieldAdd1 (offset o) (offset a) (offset b))) s fun t =>
      Keep base s t ∧ env t.mem base = evalOp (.add o a b) (env s.mem base) ∧
      Small t.mem base (fun i => if i = o then false else S i) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have := hS a ha
  have := hS b hb
  refine WP.mono (add1_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
    (slot_rangeWith (large := large) b) (by omega)) fun t ⟨h, e⟩ => ?_
  exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun⟩

/-- `fieldSub1` from a small slot. -/
theorem sub1Slot_ok {s : State} {base : Addr} (hs : Scr s base large) (o a b : Slot) {S : Slot → Bool}
    (hS : Small s.mem base S) (hb : S b = true) :
    WP isa (.block (fieldSub1 (offset o) (offset a) (offset b))) s fun t =>
      Keep base s t ∧ env t.mem base = evalOp (.sub o a b) (env s.mem base) ∧
      Small t.mem base (fun i => if i = o then false else S i) := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  have := hS b hb
  refine WP.mono (sub1_ok hs (slot_rangeWith (large := large) o) (slot_rangeWith (large := large) a)
    (slot_rangeWith (large := large) b) (by omega)) fun t ⟨h, e⟩ => ?_
  exact ⟨op_keep h, by rw [env_update o h.mem, e]; rfl, hS.update h.mem false nofun⟩

end VG.Proof.Ed25519.AArch64
