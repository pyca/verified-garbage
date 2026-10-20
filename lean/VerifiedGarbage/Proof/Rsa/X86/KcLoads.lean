module

public import VerifiedGarbage.Proof.Rsa.X86.KcLoadList
public import VerifiedGarbage.Proof.Rsa.X86.KcStart
import VerifiedGarbage.Proof.Rsa.X86.KcZero
import VerifiedGarbage.Proof.Rsa.KeyWorkspace

/-! # Initialized RSA key workspace from the caller's byte arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys

def geometry (g : CallGeometry) : Geo := ⟨g.base, g.size, 2 * g.n⟩

def numbers (g : CallGeometry) (m : Mem) : Vals :=
  let v := fun i => Spec.Rsa.os2ip (inputBytes g m i)
  ⟨v 0, v 1, v (if g.full then 3 else 2), v (if g.full then 4 else 3),
    v (if g.full then 5 else 4), v (if g.full then 6 else 5), v (if g.full then 7 else 6),
    if g.full then v 2 else 0⟩

theorem inputs_fit (full : Bool) : ∀ p ∈ inputs full,
    2 * p.1 < scratchArg full ∧ p.2 < nArr ∧ p.2 ≠ aVD := by cases full <;> decide

theorem loaded_values (g : CallGeometry) (m : Mem) :
    loadValues g m (fun _ => 0) (inputs g.full) = vals (numbers g m) := by
  funext j
  cases e : g.full <;>
    simp only [inputs, e, Bool.false_eq_true, ite_false, ite_true,
      List.cons_append, List.nil_append, loadValues, numbers, vals, upd,
      aN, aE, aD, aP, aQ, aDP, aDQ, aQI]
  all_goals repeat' first | split | rfl | omega

theorem loads_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (loads g.full g.n) s fun t => Inputs g t ∧ BodyIn (geometry g) (numbers g s.mem) t ∧
      Outside g.base 16 (g.size - 16) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have header := h.ws.hdr_le
  have fits := h.ws.fits
  unfold loads
  rw [WP.seq_iff]
  refine WP.mono (zeroArrays_ok h) fun z ⟨hz, oz, zeros, rz⟩ => ?_
  have Oz : Outside g.base 0 g.size s.mem z.mem := oz.mono (by omega) (by
    change hdr + nArr * (4 * (2 * g.n + 2)) ≤ g.size at fits
    unfold nArr at fits ⊢; omega)
  have Bz : Outside g.base 16 (g.size - 16) s.mem z.mem := oz.mono (by unfold hdr; omega) (by
    change hdr + nArr * (4 * (2 * g.n + 2)) ≤ g.size at fits
    unfold nArr at fits ⊢; unfold hdr at header; omega)
  have az : Arrs z.mem g.base (2 * g.n) (fun _ => 0) (List.range nArr) := by
    intro j hj
    have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zeros j (List.mem_range.mp hj))
      (a := 0) (c := 2 * g.n) (by omega)
    simpa only [Nat.mul_zero, Nat.add_zero] using part
  have tz : w32 z.mem g.base (arr (2 * g.n) aVD + 4 * (2 * g.n)) = 0 := by
    have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zeros aVD (by decide))
      (a := 2 * g.n) (c := 1) (by omega)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using part
  refine WP.mono (loadInputs_ok hz _ az tz (inputs g.full) (inputs_fit _))
    fun t ⟨ht, kt, vt, tt, rt⟩ => ?_
  rw [loadValues_frame h Oz _ _ (fun p hp => (inputs_fit _ p hp).1), loaded_values] at vt
  exact ⟨ht, ⟨ht.ws, vt, tt⟩,
    Bz.trans (hz.keepBody kt (fun j hj => List.mem_range.mp hj) (by simp)),
    (rz.mono (by decide)).trans rt⟩
end VG.Proof.Rsa.X86.KeyCheck
