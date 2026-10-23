module

public import VerifiedGarbage.Proof.Rsa.X86.KcLoadList
public import VerifiedGarbage.Proof.Rsa.X86.KcStart
import VerifiedGarbage.Proof.Rsa.X86.KcLoad
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Initialized RSA key workspace from the caller's byte arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.KeyCheck
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.KeyCheck
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.KeyRt (kw zeroArrays_ok)

def geometry (g : CallGeometry) : Geo := ⟨g.base, g.size, (g.args 1).toNat, g.full⟩

def numbers (g : CallGeometry) (m : Mem) : Vals :=
  let v := fun i => Spec.Rsa.os2ip (inputBytes g m i)
  ⟨v 0, v 1, v (if g.full then 3 else 2), v (if g.full then 4 else 3),
    v (if g.full then 5 else 4), v (if g.full then 6 else 5), v (if g.full then 7 else 6),
    if g.full then v 2 else 0⟩

theorem inputs_fit (full : Bool) : ∀ p ∈ inputs full,
    2 * p.1 < scratchArg full ∧ p.2 < nArr ∧ p.2 ≠ aVD ∧ (fun _ => 0 : Nat → Nat) p.2 = 0 := by
  cases full <;> decide

theorem inputs_nodup (full : Bool) : ((inputs full).map Prod.snd).Nodup := by cases full <;> decide

theorem loaded_values (g : CallGeometry) (m : Mem) :
    loadValues g m (fun _ => 0) (inputs g.full) = vals (numbers g m) := by
  funext j
  cases e : g.full <;>
    simp only [inputs, e, Bool.false_eq_true, ite_false, ite_true,
      List.cons_append, List.nil_append, loadValues, numbers, vals, upd,
      aN, aE, aD, aP, aQ, aDP, aDQ, aQI]
  all_goals repeat' first | split | rfl | omega

/-- `q`'s length argument bounds `q`. -/
theorem qLen_ok {g : CallGeometry} {t : State} (h : Inputs g t) (m : Mem) :
    ∃ a, 1 ≤ a ∧ a ≤ 1024 ∧ (numbers g m).q < 2 ^ (8 * a) ∧
      VG.Proof.Bignum.X86.CallArgument t g.base g.size (qLenArg g.full) (BitVec.ofNat 32 a) := by
  have qi : 2 * (if g.full then 4 else 3) < scratchArg g.full := by cases g.full <;> decide
  have qa : 2 * (if g.full then 4 else 3) + 1 = qLenArg g.full := by cases g.full <;> rfl
  have pos := h.inputPositive _ qi
  have bound := h.inputBound _ qi
  have up := h.upper
  simp only [CallGeometry.buffer, qa] at pos bound
  refine ⟨(g.args (qLenArg g.full)).toNat, pos, by omega, ?_, ?_⟩
  · have lt := VG.Proof.Bignum.os2ip_lt (inputBytes g m (if g.full then 4 else 3))
    have ln : (inputBytes g m (if g.full then 4 else 3)).length = (g.args (qLenArg g.full)).toNat := by
      rw [inputBytes, VG.Proof.Bignum.bytesAt_length]; simp only [CallGeometry.buffer, qa]
    rw [ln, VG.Proof.Bignum.pow256_eq] at lt
    exact lt
  · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact h.arguments _ (by cases g.full <;> decide)

theorem loads_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa (VG.Impl.Rsa.X86.KeyCheckRt.loads g.full) s fun t => Inputs g t ∧
      BodyIn (geometry g) (numbers g s.mem) t ∧
      Outside g.base 16 (g.size - 16) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have r := inputsRt h len
  have header := r.ws.hdr_le
  have fits := r.ws.fits
  have nw := r.ws.workspace.nowrap
  have kwEq : kw (g.args 1).toNat = 2 * g.n := by rw [len.width]
  unfold VG.Impl.Rsa.X86.KeyCheckRt.loads
  rw [WP.seq_iff]
  refine WP.mono (zeroArrays_ok r (n := nArr) (by decide) (by decide)) fun z ⟨rz, oz, zeros, kz⟩ => ?_
  have a0 : arr (kw (g.args 1).toNat) 0 = hdr := by simp [arr]
  have fitsN : hdr + 4 * (nArr * (kw (g.args 1).toNat + 2)) ≤ g.size := by
    simp only [arr, S] at fits; rw [Nat.mul_left_comm] at fits; exact fits
  rw [a0] at oz
  have Oz : Outside g.base 0 g.size s.mem z.mem := oz.mono (Nat.zero_le _) (by omega)
  have Bz : Outside g.base 16 (g.size - 16) s.mem z.mem := oz.mono (by unfold hdr; omega) (by unfold hdr at *; omega)
  have hz := h.after (kz.mono (rs' := [.eax, .ecx, .edx, .ebp]) (by decide)) (by decide) (by decide) (h.scratchFrame Oz)
  have az : Arrs z.mem g.base (kw (g.args 1).toNat) (fun _ => 0) (List.range nArr) := by
    intro j hj
    have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zeros j (List.mem_range.mp hj))
      (a := 0) (c := kw (g.args 1).toNat) (by omega)
    simpa only [Nat.mul_zero, Nat.add_zero] using part
  have tz : w32 z.mem g.base (arr (kw (g.args 1).toNat) aVD + 4 * kw (g.args 1).toNat) = 0 := by
    have part := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (zeros aVD (by decide))
      (a := kw (g.args 1).toNat) (c := 1) (by omega)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using part
  refine WP.mono (loadInputs_ok hz len _ az tz (inputs g.full) (inputs_fit _) (inputs_nodup _))
    fun t ⟨ht, kt, vt, tt, rt⟩ => ?_
  rw [loadValues_frame h Oz _ _ (fun p hp => (inputs_fit _ p hp).1), loaded_values] at vt
  have kt' : Keep g.base (2 * g.n) (List.range nArr) [] z.mem t.mem := by rw [← kwEq]; exact kt
  exact ⟨ht, ⟨inputsRt ht len, vt, tt, qLen_ok ht s.mem⟩,
    Bz.trans (hz.keepBody kt' (fun j hj => List.mem_range.mp hj) (by simp)),
    (kz.mono (by decide)).trans rt⟩
end VG.Proof.Rsa.X86.KeyCheck
