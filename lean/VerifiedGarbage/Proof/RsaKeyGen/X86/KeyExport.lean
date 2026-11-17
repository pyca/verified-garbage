module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.X86.KeySelect
import VerifiedGarbage.Impl.Bignum.X86.StoreBE
import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `RsaKeyGen.X86.KeyWritePort`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyWriteArray`, which this module and modules that import it used -/

section

/-! # Masked native key output preserves every other array and header word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key
open VG.Proof.Bignum.X86 (byteAddr)

theorem output_word {s : State} {B : Addr} {Z n d : Nat} {m m' : Mem} {p : BitVec 32} {len : Nat}
    (h : Ws s B Z n 32) (separate : Region.Disjoint ⟨B, Z⟩ ⟨p.setWidth 64, len⟩)
    (F : Frame [⟨p.setWidth 64, len⟩] m m') (bound : d + 4 ≤ Z) : w32 m' B d = w32 m B d := by
  unfold w32
  rw [F.readW (r := ⟨B, Z⟩) (a := off B d) (w := 32)
    (Scr.contains h.workspace.nowrap bound)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide)]

theorem output_num {s : State} {B : Addr} {Z n j : Nat} {m m' : Mem} {p : BitVec 32} {len : Nat}
    (h : Ws s B Z n 32) (separate : Region.Disjoint ⟨B, Z⟩ ⟨p.setWidth 64, len⟩)
    (F : Frame [⟨p.setWidth 64, len⟩] m m') (index : j < 32) : num m' B n j = num m B n j := by
  apply val32_congr
  intro k hk
  have fits := h.arr_fit index
  unfold S at fits
  exact output_word h separate F (by omega_using [hk, fits])

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Output one key component while retaining the remaining output context -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def portResult (g : OutputGeometry) (m : Mem) (accept : Bool) (i : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then num m g.base g.n (outputIndex i) else 0) %
    2 ^ (8 * g.length i)) (g.length i)

def portWrites (g : OutputGeometry) (i : Nat) : List Region :=
  [⟨off g.base (arr g.n (outputIndex i)), S g.n⟩, g.region i]

theorem portFrame_global {g : OutputGeometry} {s : State} {m m' : Mem} {i : Nat}
    (h : OutputInput g s) (hi : i < 7) (F : Frame (portWrites g i) m m') : Frame g.writes m m' := by
  apply F.sub
  intro r hr
  simp only [portWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨g.scratch, List.mem_cons_self,
      Offset.sub_base g.base (h.ws.arr_fit (outputIndex_bound hi))⟩
  · exact ⟨g.region i, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩),
      fun _ H => H⟩

theorem portFrame_other {g : OutputGeometry} {s : State} {m m' : Mem} {i j : Nat}
    (h : OutputInput g s) (hi : i < 7) (hj : j < 7) (ne : j ≠ i)
    (F : Frame (portWrites g i) m m') :
    Spec.Rsa.bytesAt m' (g.region j).base (g.region j).len =
      Spec.Rsa.bytesAt m (g.region j).base (g.region j).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame F (by change g.length j < 2 ^ 64; have H := h.valid.fit j hj; omega_using [H])
  intro r hr
  simp only [portWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.valid.scratchApart j hj).symm.sub_right
      (Offset.sub_base g.base (h.ws.arr_fit (outputIndex_bound hi)))
  · exact h.valid.separate j hj i hi ne

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyWritePorts`, which this module and modules that import it used -/

section

/-! # Export all seven key components without losing earlier outputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure ExportProgress (g : OutputGeometry) (m : Mem) (accept : Bool) (i : Nat) (s : State) : Prop where
  input : OutputInput g s
  zero : num s.mem g.base g.n aZero = 0
  mask : slot s.mem g.base kOk = if accept then 1 else 0
  header : ∀ d, d + 4 ≤ hdr → slot s.mem g.base d = slot m g.base d
  pending : ∀ j, i ≤ j → j < 7 → num s.mem g.base g.n (outputIndex j) = num m g.base g.n (outputIndex j)
  done : ∀ j, j < i → j < 7 → Spec.Rsa.bytesAt s.mem (g.region j).base (g.region j).len = portResult g m accept j

end VG.Proof.RsaKeyGen.X86.Key

end

end

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

/-- What the outputs hold, whatever the bytes apart from them are. -/
theorem WrittenCore.frame {g : OutputGeometry} {e p q : Nat} {s t : State} (R : WrittenCore g e p q s)
    (eax : t.gpr .eax = s.gpr .eax) {rs : List Region} (F : Frame rs s.mem t.mem)
    (sep : ∀ i < 7, ∀ r ∈ rs, (g.region i).Disjoint r) (fit : ∀ i < 7, (g.region i).len < 2 ^ 64) :
    WrittenCore g e p q t := by
  have hb : ∀ i < 7, Spec.Rsa.bytesAt t.mem (g.region i).base (g.region i).len =
      Spec.Rsa.bytesAt s.mem (g.region i).base (g.region i).len := fun i hi =>
    VG.Proof.Rsa.rsa_bytes_frame F (fit i hi) (sep i hi)
  unfold WrittenCore at R ⊢
  revert R
  generalize Spec.RsaKeyGen.keyFromPrimes (32 * g.n) e p q = k
  rcases k with (_ | _) | _ <;> dsimp only <;> rintro ⟨r₁, r₂⟩ <;>
    exact ⟨by rw [eax]; exact r₁, fun i hi => by rw [hb i hi]; exact r₂ i hi⟩

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

end VG.Proof.RsaKeyGen.X86.Key
