module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontGeometry
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Rsa.X86.KeyBits
import VerifiedGarbage.Proof.Rsa.KeyWorkspace

/-! # The negative Montgomery inverse of the public recovery modulus -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem setupInverse_ok {g : Geo} {s : State} {m : Nat} (h : Ws s g.B g.Z g.w nArr)
    (positive : 0 < g.n) (value : num s.mem g.B g.w mBase = m)
    (bound : m < 2 ^ (64 * g.n)) (odd : m % 2 = 1) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.setupInverse (arr g.w mBase) sInv)) s fun t =>
      MR g m t ∧ Keep g.B g.w [] [sInv] s.mem t.mem ∧ Keeps opRegs s t := by
  have fit := h.arr_fit (by decide : mBase < nArr)
  have header := h.hdr_le
  have wordOdd : w32 s.mem g.B (arr g.w mBase) % 2 = 1 := by
    rw [← Keys.num_mod2 s.mem g.B h.wpos, value, odd]
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.setupInverse_ok h.workspace
    (by simp only [S] at fit; omega) (by unfold sInv hdr at *; omega) wordOdd)
    fun t ⟨inv, frame, r⟩ => ?_
  have keep : Keep g.B g.w [] [sInv] s.mem t.mem := Keep.of_slot frame (by simp)
  have rest : Keeps opRegs s t := r.mono (by decide)
  refine ⟨⟨h.rest rest, positive, ?_, bound, ?_⟩, keep, rest⟩
  · rw [keep.num (by simp) (by decide) (h.fit64 (by decide)), value]
  · have low : m % 2 ^ 32 = w32 s.mem g.B (arr g.w mBase) := by
      rw [← value]
      exact VG.Proof.Rsa.KeyWorkspace.num_mod32 s.mem g.B h.wpos
    have lowBound : w32 s.mem g.B (arr g.w mBase) < 2 ^ 32 :=
      (s.mem.readW (off g.B (arr g.w mBase)) 32).isLt
    have product : m * w32 t.mem g.B sInv % 2 ^ 32 =
        w32 s.mem g.B (arr g.w mBase) * w32 t.mem g.B sInv % 2 ^ 32 := by
      rw [Nat.mul_mod m, Nat.mul_mod (w32 s.mem g.B (arr g.w mBase)), low,
        Nat.mod_eq_of_lt lowBound]
    rw [Nat.add_mod, product, ← Nat.add_mod]
    exact inv

end VG.Proof.Rsa.X86.Recover
