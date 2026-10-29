module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePort
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome

import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.IntervalCases
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePorts
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.Octets
/-! # The masked native export returns the specified key or all zeros -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyFields.lean`, which only this module imported.
section

/-! # The native output order is the shared RSA key's field order -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.Proof.Mont VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def keyField (key : Spec.RsaKeyGen.Key) : Nat → Nat
  | 0 => key.n
  | 1 => key.d
  | 2 => key.p
  | 3 => key.q
  | 4 => key.dP
  | 5 => key.dQ
  | _ => key.qInv

theorem assembled_field (B : Addr) (n : Nat) (m : Mem) {i : Nat} (hi : i < 7) :
    num m B n (outputIndex i) = keyField (assembledKey B n m) i := by
  interval_cases i <;> rfl

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyWriteOutputs.lean`, which only this module imported.
section

/-! # Complete masked key export, including an independent retry status -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem writeOutputs_ok {g : OutputGeometry} {s : State} (h : OutputInput g s) (accept : Bool)
    (mask : slot s.mem g.base kOk = if accept then 1 else 0) :
    WP isa (writeOutputs g.n) s fun t =>
      Ws t g.base g.size g.n 32 ∧ (t.gpr .eax).toNat = slot s.mem g.base kStatus ∧
      (∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = portResult g s.mem accept i) ∧
      Frame g.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have fits := h.ws.arr_fit (j := aZero) (by decide)
  have fit64 := h.ws.fit64 (j := aZero) (by decide)
  unfold writeOutputs seqs
  refine WP.seq (WP.mono (zerosW_ok h.ws.workspace (by omega)
    (by change arr g.n aZero + 4 * (g.n + 2) ≤ g.size; exact fits))
    fun u ⟨Ou, zero, Ku⟩ => ?_)
  change Outside g.base (arr g.n aZero) (S g.n) s.mem u.mem at Ou
  change val32 u.mem g.base (arr g.n aZero) (g.n + 2) = 0 at zero
  have hu := h.ws.rest Ku
  have clear : Keep g.base g.n [aZero] [] s.mem u.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou) (by unfold S; omega) (by simp)
  have header : ∀ d, d + 4 ≤ hdr → slot u.mem g.base d = slot s.mem g.base d :=
    fun d hd => clear.slot hd (by simp)
  have Pu : ExportProgress g s.mem accept 0 u := by
    refine ⟨h.after hu Ku header, ?_, (header kOk (by decide)).trans mask, header, ?_, ?_⟩
    · change val32 u.mem g.base (arr g.n aZero) g.n = 0
      have H := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := g.n) (by omega)
      simpa only [Nat.mul_zero, Nat.add_zero] using H
    · intro i _ hi
      exact clear.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact outputIndex_zero hi)
        (by simp) (h.ws.fit64 (outputIndex_bound hi))
    · intro i hi
      omega
  have Fu : Frame g.writes s.mem u.mem := by
    apply (VG.Proof.Bignum.outside_frame Ou fit64).sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.scratch, List.mem_cons_self, Offset.sub_base g.base fits⟩
  refine WP.seq (WP.mono (writePorts_ok Pu (by decide : 0 + 7 ≤ 7))
    fun v ⟨Pv, Fv, Kv⟩ => ?_)
  have head := Pv.input.ws.hdr_le
  refine wp_movS (readSrc_sc Pv.input.ws.workspace (by unfold kStatus hdr at *; omega))
    fun t T _ => WP.block_nil ?_
  refine ⟨Pv.input.ws.rest T.keeps, ?_, ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans (T.keeps.mono (by decide)))⟩
  · rw [T.gpr]
    exact Pv.header kStatus (by decide)
  · intro i hi
    rw [T.mem]
    exact Pv.done i hi hi
  · rw [T.mem]
    exact Fu.trans Fv

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/TruncatedOctets.lean`, which only this module imported.
section

/-! # Truncating an integer before I2OSP keeps the same output octets -/

section
namespace VG.Proof.RsaKeyGen

theorem i2osp_mod (x len : Nat) :
    Spec.Rsa.i2osp (x % 2 ^ (8 * len)) len = Spec.Rsa.i2osp x len := by
  have power : 2 ^ (8 * len) = 256 ^ len := by rw [Nat.pow_mul]
  rw [power, ← VG.Proof.Rsa.os2ip_i2osp]
  have H := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.i2osp x len)
  rw [VG.Proof.Rsa.i2osp_length] at H
  exact H

end VG.Proof.RsaKeyGen
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

def WrittenCore (g : OutputGeometry) (e p q : Nat) (t : State) : Prop :=
  match Spec.RsaKeyGen.keyFromPrimes (32 * g.n) e p q with
  | .inl (.ok key) => (t.gpr .eax).toNat = 1 ∧
      ∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len =
        Spec.Rsa.i2osp (keyField key i) (g.length i)
  | .inr () => (t.gpr .eax).toNat = 2 ∧
      ∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = List.replicate (g.length i) 0
  | .inl (.error _) => (t.gpr .eax).toNat = 0 ∧
      ∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = List.replicate (g.length i) 0

/-- Any code that writes the masked outputs and returns the status writes the specified key. -/
theorem writeCore_of {g : OutputGeometry} {c : Prog isa} {s : State} {e p q : Nat} {R : State → Prop}
    (run : ∀ accept, slot s.mem g.base kOk = (if accept then 1 else 0) → WP isa c s fun t =>
      R t ∧ (t.gpr .eax).toNat = slot s.mem g.base kStatus ∧
      (∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len = portResult g s.mem accept i) ∧
      Frame g.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t)
    (result : CoreOutcome g.base g.n e p q s.mem) :
    WP isa c s fun t =>
      R t ∧ WrittenCore g e p q t ∧ Frame g.writes s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  unfold CoreOutcome at result
  cases code : Spec.RsaKeyGen.keyFromPrimes (32 * g.n) e p q with
  | inr u =>
    cases u
    rw [code] at result
    obtain ⟨status, mask⟩ := result
    refine WP.mono (run false mask) fun t ⟨ht, ret, values, F, K⟩ => ?_
    refine ⟨ht, ?_, F, K⟩
    unfold WrittenCore
    rw [code]
    refine ⟨ret.trans status, ?_⟩
    intro i hi
    simpa only [portResult, Bool.false_eq_true, ite_false, Nat.zero_mod, VG.Proof.Bignum.i2osp_zero'] using values i hi
  | inl value =>
    cases value with
    | error failure =>
      rw [code] at result
      obtain ⟨status, mask⟩ := result
      refine WP.mono (run false mask) fun t ⟨ht, ret, values, F, K⟩ => ?_
      refine ⟨ht, ?_, F, K⟩
      unfold WrittenCore
      rw [code]
      refine ⟨ret.trans status, ?_⟩
      intro i hi
      simpa only [portResult, Bool.false_eq_true, ite_false, Nat.zero_mod, VG.Proof.Bignum.i2osp_zero'] using values i hi
    | ok key =>
      rw [code] at result
      obtain ⟨status, mask, assembled⟩ := result
      refine WP.mono (run true mask) fun t ⟨ht, ret, values, F, K⟩ => ?_
      refine ⟨ht, ?_, F, K⟩
      unfold WrittenCore
      rw [code]
      refine ⟨ret.trans status, ?_⟩
      intro i hi
      have value := values i hi
      change Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len =
        Spec.Rsa.i2osp (num s.mem g.base g.n (outputIndex i) % 2 ^ (8 * g.length i)) (g.length i) at value
      rw [VG.Proof.RsaKeyGen.i2osp_mod] at value
      rw [assembled_field _ _ _ hi, assembled] at value
      exact value

theorem writeCore_ok {g : OutputGeometry} {s : State} {e p q : Nat} (h : OutputInput g s)
    (result : CoreOutcome g.base g.n e p q s.mem) :
    WP isa (writeOutputs g.n) s fun t =>
      Ws t g.base g.size g.n 32 ∧ WrittenCore g e p q t ∧ Frame g.writes s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  writeCore_of (fun accept mask => writeOutputs_ok h accept mask) result

end VG.Proof.RsaKeyGen.X86.Key
