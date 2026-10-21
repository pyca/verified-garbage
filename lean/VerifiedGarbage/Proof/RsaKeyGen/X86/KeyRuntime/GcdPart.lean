module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGcdPart
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddSecond
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.GcdFrom
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.OddModulus
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace

/-! # Complete native GCD stage for the RSA LCM -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key (aU aV aDen aOne kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (gcdPartRanges gcdPartArrays canonU canonV)

theorem gcdPart_ok {s : State} {B : Addr} {Z n k : Nat}
    (h : Ws s B Z n 32) (width : n = 2 * k) (positive : 0 < k)
    (boundU : num s.mem B n aU < 2 ^ (32 * k)) (boundV : num s.mem B n aV < 2 ^ (32 * k))
    (odd : 2 ≤ canonV (num s.mem B n aU) (num s.mem B n aV) →
      canonV (num s.mem B n aU) (num s.mem B n aV) % 2 = 1)
    (one : num s.mem B n aOne = 1) :
    WP isa gcdPart s fun t =>
      Ws t B Z n 32 ∧ Outs B (gcdPartRanges n k) s.mem t.mem ∧
      num t.mem B n aDen =
        (if canonV (num s.mem B n aU) (num s.mem B n aV) ≤ 1 then 1 else
          Nat.gcd (canonU (num s.mem B n aU) (num s.mem B n aV))
            (canonV (num s.mem B n aU) (num s.mem B n aV))) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  let A := num s.mem B n aU
  let C := num s.mem B n aV
  have cbU : canonU A C < 2 ^ (32 * k) := by
    unfold canonU
    split
    · exact boundV
    · exact boundU
  have cbV : canonV A C < 2 ^ (32 * k) := by
    unfold canonV
    split
    · exact boundU
    · exact boundV
  have bound3 : 3 < 2 ^ (32 * k) := by
    have P : 2 ^ 32 ≤ 2 ^ (32 * k) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have oddLocal : 2 ≤ canonV A C → canonV A C % 2 = 1 := odd
  have valid : canonV A C % 2 = 1 ∧ 3 ≤ canonV A C ↔ ¬canonV A C ≤ 1 := by
    constructor
    · intro H
      omega
    · intro H
      have O := oddLocal (by omega)
      exact ⟨O, by omega⟩
  unfold gcdPart VG.Impl.Rsa.X86.Keys.seqs
  refine WP.seq (WP.mono (oddSecond_ok h) fun u ⟨hu, Ou, U, V, Ku⟩ => ?_)
  change num u.mem B n aU = canonU A C at U
  change num u.mem B n aV = canonV A C at V
  have oneU : num u.mem B n aOne = 1 := by
    rw [Ou.num (by decide) (by decide) (h.fit64 (by decide)), one]
  refine WP.seq (WP.mono (oddModulus_ok hu (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, flag, modulus, Kv⟩ => ?_)
  rw [V] at flag modulus
  have Uv : num v.mem B n aU = canonU A C := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), U]
  have oneV : num v.mem B n aOne = 1 := by
    rw [Ov.num (by decide) (by decide) (h.fit64 (by decide)), oneU]
  have inputBound : num v.mem B n aU < 2 ^ (32 * k) := by rw [Uv]; exact cbU
  have modulusBound : num v.mem B n aDen < 2 ^ (32 * k) := by
    rw [modulus]
    split
    · exact cbV
    · exact bound3
  have modulusOdd : num v.mem B n aDen % 2 = 1 := by
    rw [modulus]
    split
    · next H => exact H.1
    · decide
  have modulusLarge : 1 < num v.mem B n aDen := by rw [modulus]; split <;> omega
  have bit : slot v.mem B kFlag ≤ 1 := by rw [flag]; split <;> omega
  refine WP.mono (gcdFrom_ok hv width positive inputBound modulusBound modulusOdd modulusLarge oneV bit)
    fun t ⟨ht, Ot, computed, Kt⟩ => ?_
  refine ⟨ht, ?_, ?_, (Ku.mono (by decide)).trans ((Kv.mono (by decide)).trans Kt)⟩
  · have first : Outs B (gcdPartRanges n k) s.mem u.mem :=
      VG.Proof.Mont.Outs.mono (Ou.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    have middle : Outs B (gcdPartRanges n k) u.mem v.mem :=
      VG.Proof.Mont.Outs.mono (Ov.mono (js' := gcdPartArrays) (by decide) (by simp))
        (fun r hr => List.mem_append_right _ hr)
    exact (first.trans middle).trans (Ot.mono (fun r hr => List.mem_append_left _ hr))
  · change num t.mem B n aDen = if canonV A C ≤ 1 then 1 else Nat.gcd (canonU A C) (canonV A C)
    rw [computed, flag, Uv, modulus]
    by_cases H : canonV A C ≤ 1
    · have inactive : ¬(canonV A C % 2 = 1 ∧ 3 ≤ canonV A C) := fun P => valid.mp P H
      simp [H, inactive]
    · have active := valid.mpr H
      simp [H, active]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
