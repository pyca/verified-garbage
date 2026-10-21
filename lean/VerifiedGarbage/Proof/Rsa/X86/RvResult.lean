module

public import VerifiedGarbage.Proof.Rsa.X86.RvRest
import VerifiedGarbage.Proof.Bignum.Octets
public import Init.Data.Fin.Basic
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.TCB.X86.State

/-! # The arithmetic recovery outputs satisfy the RSA byte-string result -/

@[expose] public section
variable [rsaBatchLaw : VG.Proof.Rsa.X86.BatchLaw]
include rsaBatchLaw
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa (sub32 pqOf)

def outputBuffers (g : CallGeometry) : List (Addr × Nat) :=
  [((g.buffer 0).base, (g.buffer 0).len), ((g.buffer 2).base, (g.buffer 2).len)]
def calculated (g : CallGeometry) (m : Mem) :=
  Spec.Rsa.primesKey (inputBytes g m 0) (inputBytes g m 1) (inputBytes g m 2)
def Written (g : CallGeometry) (m : Mem) (t : State) : Prop :=
  Spec.Rsa.writtenAll t.mem (outputBuffers g) (t.gpr .eax)
    ((calculated g m).1.map fun v => [v.1, v.2])

omit rsaBatchLaw in
theorem written_rest {g : CallGeometry} {s0 t : State} (h : RestResult g s0 t)
    (valid : Spec.Rsa.modulusValid (inputValue g s0.mem 0) (inputBytes g s0.mem 0).length = true)
    (pLen : (g.buffer 0).len = (inputBytes g s0.mem 0).length)
    (qLen : (g.buffer 2).len = (inputBytes g s0.mem 0).length) : Written g s0.mem t := by
  obtain ⟨y, ok, tries, ⟨inputs, p, q, status, _, _⟩, yl, yp, result⟩ := h
  have key : (calculated g s0.mem).1 = if ok then
      some (Spec.Rsa.i2osp (pqOf (inputValue g s0.mem 0) y).1 (inputBytes g s0.mem 0).length,
        Spec.Rsa.i2osp (pqOf (inputValue g s0.mem 0) y).2 (inputBytes g s0.mem 0).length) else none := by
    unfold calculated Spec.Rsa.primesKey
    dsimp only
    rw [show Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s0.mem 0))
      (inputBytes g s0.mem 0).length = true from valid]
    simp only [ite_true]
    have result' := result
    unfold inputValue at result'
    rw [← result']
    cases ok <;> rfl
  unfold Written
  rw [key]
  cases ok with
  | false =>
    simp only [encoded, Bool.false_eq_true, ite_false, Nat.zero_mod, i2osp_zero'] at p q
    simp only [Bool.false_eq_true, ite_false, Option.map_none]
    refine ⟨status, ?_⟩
    simp only [outputBuffers, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨p, q⟩
  | true =>
    have mpos : 0 < inputValue g s0.mem 0 := by omega
    have msmall := inputValue_lt g s0.mem 0
    have ysmall : y < 2 ^ (32 * g.toGeo.w) := by
      apply Nat.lt_trans yl
      apply Nat.lt_of_lt_of_le msmall
      apply Nat.pow_le_pow_right (by decide)
      have len := inputs.inputBound 0
      change 8 * (g.buffer (4 + 2 * (0 : Fin 3).val)).len ≤ 32 * (2 * g.n + 2)
      omega
    have sub := VG.Proof.Rsa.sub32_one (yp rfl) ysmall
    have pb := Nat.gcd_le_right (y - 1) mpos
    have qb := Nat.div_le_self (inputValue g s0.mem 0) (Nat.gcd (y - 1) (inputValue g s0.mem 0))
    have plen : (inputBytes g s0.mem 0).length = (g.buffer 4).len := by simp [inputBytes, Spec.Rsa.bytesAt]
    change inputValue g s0.mem 0 < 2 ^ (8 * (g.buffer 4).len) at msmall
    simp only [encoded, ite_true, sub] at p q
    have bp : max (Nat.gcd (y - 1) (inputValue g s0.mem 0))
        (inputValue g s0.mem 0 / Nat.gcd (y - 1) (inputValue g s0.mem 0)) < 2 ^ (8 * (g.buffer 0).len) := by
      rw [pLen, plen]; omega
    have bq : min (Nat.gcd (y - 1) (inputValue g s0.mem 0))
        (inputValue g s0.mem 0 / Nat.gcd (y - 1) (inputValue g s0.mem 0)) < 2 ^ (8 * (g.buffer 2).len) := by
      rw [qLen, plen]; omega
    change _ = Spec.Rsa.i2osp (_ % 2 ^ (8 * (g.buffer 0).len)) (g.buffer 0).len at p
    change _ = Spec.Rsa.i2osp (_ % 2 ^ (8 * (g.buffer 2).len)) (g.buffer 2).len at q
    rw [Nat.mod_eq_of_lt bp] at p
    rw [Nat.mod_eq_of_lt bq] at q
    simp only [ite_true, Option.map_some]
    refine ⟨status, ?_⟩
    simp only [outputBuffers, List.map_cons, List.map_nil]
    rw [p, q]
    change [Spec.Rsa.i2osp _ (g.buffer 0).len, Spec.Rsa.i2osp _ (g.buffer 2).len] = _
    rw [pLen, qLen]
    rfl

end VG.Proof.Rsa.X86.Recover
