module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyArgContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputMap
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.ContextArgument
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.Bignum.X86.ReverseBuffer
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ByteWords
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyNoSpBase
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Key
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.Mont.X86.Compact.EntryArgs
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateWidthTiming
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.MillerRabin.X86.Caller
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutputContext
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Tactic.IntervalCases
import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Impl.Bignum.X86.StoreBE
import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.X86.ExportBE
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `RsaKeyGen.X86.KeyBody`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyExport`, which this module and modules that import it used -/

section

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

end

end

/-! ### `RsaKeyGen.X86.KeySized`, which this module and modules that import it used -/

section

/-! # Complete native import, derivation and masked export at every supported width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

def BodyOutcome (E : Environment) (m : Mem) (t : State) : Prop :=
  WrittenCore E.outputs
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) t

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyEntry`, which this module and modules that import it used -/

section

/-! # Establish the native key workspace from cdecl argument sixteen -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyArgs.lean`, which only this module imported.
section

/-! # Key argument copying retains all eighteen cdecl inputs -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

theorem copy_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {i : Nat} (index : i < 18) :
    WP isa (.block (copy i)) s fun t =>
      Context base size p inputs t ∧ t.mem.readW (off base (4 * i)) 32 = inputs i ∧
      Outside base (4 * i) 4 s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold copy
  refine wp_movS (C.read i index) fun a A _ => ?_
  have Sa := C.scratch.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (by have := C.header; omega)) (Sa.write (by have := C.header; omega)) fun t T => WP.block_nil ?_
  have O : Outside base (4 * i) 4 s.mem t.mem := by
    rw [T.mem, A.mem]
    exact writeW32_outside _ _ _ (by omega)
  have K := A.keeps.widen (T.keeps [])
  have F : Frame [⟨base, size⟩] s.mem t.mem := VG.Proof.MillerRabin.X86.workspaceGlobalFrame (g := ⟨base, size, 0⟩) (rs := [(4 * i, 4)])
    (Outs.of_outside O (List.mem_singleton_self _))
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; change 4 * i + 4 ≤ size; have := C.header; omega)
  exact ⟨C.keep K F, by rw [T.mem, Mem.readW_writeW_self32, A.gpr], O, K⟩

theorem copies_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (C : Context base size p inputs s) {n : Nat} (bound : n ≤ 18) :
    WP isa (copies n) s fun t =>
      Context base size p inputs t ∧ (∀ i < n, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      Outside base 0 (4 * n) s.mem t.mem ∧ Keeps [.eax] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨C, by intro i index; omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | succ n ih =>
    change WP isa (.seq (copies n) (.block (copy n))) s _
    refine WP.seq (WP.mono (ih C (by omega)) fun a ⟨A, valuesA, Oa, Ka⟩ => ?_)
    refine WP.mono (copy_ok A (by omega)) fun t ⟨T, valueT, Ot, Kt⟩ => ?_
    refine ⟨T, ?_, ?_, Ka.trans Kt⟩
    · intro i index
      by_cases last : i = n
      · subst i; exact valueT
      · have same := BitVec.eq_of_toNat_eq (Ot.w32 (d := 4 * i) (by omega) (by omega))
        exact same.trans (valuesA i (by omega))
    · exact (Oa.mono (by decide) (by omega)).trans (Ot.mono (by omega) (by omega))

end VG.Proof.RsaKeyGen.X86.KeyArgs
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.RsaKeyGen.X86.CandidateArgs

structure Entry (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s : State) : Prop where
  workspace : Ws s base size
  header : 72 ≤ size
  pointer : (inputs 16).setWidth 64 = base
  stack : StkOk p base size
  sp : s.gpr .esp = p
  fit : p.toNat + 92 ≤ 2 ^ 32
  separate : (argsRegion p).Disjoint ⟨base, size⟩
  read : ∀ i < 18, readSrc s (.mem (arg i)) = some (inputs i)
  deep : DeepStk p base size

theorem enter_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (E : Entry base size p inputs s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.enter s fun t =>
      Context base size p inputs t ∧ (∀ i < 18, t.mem.readW (off base (4 * i)) 32 = inputs i) ∧
      Outside base 0 72 s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  unfold VG.Impl.RsaKeyGen.X86.Key.enter
  refine WP.seq (wp_movS (E.read 16 (by decide)) fun a A _ => WP.block_nil ?_)
  have Sa : Scr a base size := by
    refine ⟨?_, ?_, E.workspace.nowrap, ?_⟩
    · rw [A.gpr]
      exact E.pointer
    · rw [A.keeps.2.2]
      exact E.workspace.wr
    · rw [A.other .esp (by decide), E.sp]
      exact E.stack
  have C : Context base size p inputs a := by
    refine ⟨Sa, E.header, (A.other .esp (by decide)).trans E.sp, E.fit, E.separate, ?_, E.deep⟩
    intro i index
    have address : a.ea (arg i) = s.ea (arg i) := by
      change addr (a.gpr .esp) _ = addr (s.gpr .esp) _
      rw [A.other .esp (by decide)]
    have same : readSrc a (.mem (arg i)) = readSrc s (.mem (arg i)) := by
      show a.load32 (a.ea (arg i)) = s.load32 (s.ea (arg i))
      simp only [State.load32, address, A.keeps.2.1, A.keeps.2.2, A.mem]
    exact same.trans (E.read i index)
  refine WP.mono (copies_ok C (by decide : 18 ≤ 18)) fun t ⟨T, values, O, K⟩ => ?_
  rw [A.mem] at O
  exact ⟨T, values, O, (A.keeps.mono (by decide)).widen K⟩

end VG.Proof.RsaKeyGen.X86.KeyArgs

end

end

/-! # Native cdecl argument entry composes with the complete key body -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys

structure EntryInput (E : Environment) (p : BitVec 32) (s : State) : Prop where
  arguments : KeyArgs.Entry E.base E.size p E.argument s
  outWrite : ∀ i < 7, InRegions s.wr (E.outputRegion i).base (E.outputRegion i).len
  exponentRead : InRegions (s.rd ++ s.wr) E.exponentRegion.base E.exponentRegion.len
  argsOutput : ∀ i < 7, (KeyArgs.argsRegion p).Disjoint (E.outputRegion i)

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem enter_input_ok {E : Environment} {p : BitVec 32} {s : State} (v : E.Valid) (I : EntryInput E p s) :
    WP isa VG.Impl.RsaKeyGen.X86.Key.enter s fun t =>
      Input E t ∧ Frame [E.workspaceRegion] s.mem t.mem ∧ Keeps [.eax, .edi] s t := by
  refine WP.mono (KeyArgs.enter_ok I.arguments) fun t ⟨C, header, O, K⟩ => ?_
  have dimensions := v.widths
  have ws : Ws t E.base E.size E.n 32 :=
    ⟨C.scratch, v.bankFit, by omega_using [dimensions], by omega_using [dimensions]⟩
  have input : Input E t := by
    refine ⟨v, ws, header, ?_, ?_⟩
    · intro i hi
      rw [K.2.2]
      exact I.outWrite i hi
    · rw [K.2.1, K.2.2]
      exact I.exponentRead
  have frame : Frame [E.workspaceRegion] s.mem t.mem :=
    outs_scratch_frame (by have := C.scratch.nowrap; omega_using [this])
      (Outs.of_outside (rs := [(0, 72)]) O (List.mem_singleton_self _))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; change 0 + 72 ≤ E.size; exact I.arguments.header)
  exact ⟨input, frame, K⟩

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.Safety`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86.KeyFrameResult`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86.KeyBodyTiming`, which the modules that import this one used -/

section

/-! ### `RsaKeyGen.X86.KeyExportState`, which this module and modules that import it used -/

section

/-! # Each masked output retains the header, zero array and validity bit for the next port -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

structure ExportState (E : Environment) (s : State) : Prop where
  input : Input E s
  zero : num s.mem E.base E.n aZero = 0
  bit : slot s.mem E.base kOk ≤ 1

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The complete native key body obeys the shared public exponent and retry leak -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyEntryTiming.lean`, which only this module imported.
section

/-! # Copying the eighteen native key arguments has a public address trace -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.CandidateArgs

def EntryPair (base : Addr) (size : Nat) (p : BitVec 32) (inputs : Nat → BitVec 32) (s t : State) : Prop :=
  Entry base size p inputs s ∧ Entry base size p inputs t

theorem pointer_ok {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s : State}
    (S : Entry base size p inputs s) :
    WP isa (.block [.mov .edi (.mem (arg 16))]) s fun t => t.gpr .edi = inputs 16 ∧ Keeps [.edi] s t := by
  refine wp_movS (S.read 16 (by decide)) fun t T _ => WP.block_nil ⟨T.gpr, T.keeps⟩

theorem pointer_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) (.block [.mov .edi (.mem (arg 16))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  intro s t tr ur u v ⟨S, T⟩ A C
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (arg 16))])
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  have start : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact S.sp.trans T.sp.symm)
  obtain ⟨leftValue, leftKeeps⟩ := wp_result (pointer_ok S) A
  obtain ⟨rightValue, rightKeeps⟩ := wp_result (pointer_ok T) C
  refine ⟨(raw _ _ _ _ _ _ start A C).1, agree_regs ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact S.sp.trans T.sp.symm
  · exact leftValue.trans rightValue.symm

theorem enter_trace {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} :
    RelCT isa (EntryPair base size p inputs) VG.Impl.RsaKeyGen.X86.Key.enter (fun _ _ => True) := by
  have copied : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (copies 18) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.esp, .edi]) (fun _ _ H => H)
      (hc := VG.Taint.hintOf taint (τr [.esp, .edi]) (copies 18))
    kernel_rfl
  exact RelCT.seq pointer_trace copied

end VG.Proof.RsaKeyGen.X86.KeyArgs
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure BodyPair (E : Environment) (sp : BitVec 32) (e p q p' q' : Nat) (s t : State) : Prop where
  left : EntryInput E sp s
  right : EntryInput E sp t
  leftExponent : inputExponent E s.mem = e
  rightExponent : inputExponent E t.mem = e
  leftP : inputPrime E s.mem 2 = p
  leftQ : inputPrime E s.mem 3 = q
  rightP : inputPrime E t.mem 2 = p'
  rightQ : inputPrime E t.mem 3 = q'

theorem enterInput_trace (E : Environment) (v : E.Valid) (sp : BitVec 32) (e p q p' q' : Nat) :
    RelCT isa (BodyPair E sp e p q p' q') VG.Impl.RsaKeyGen.X86.Key.enter (SizedStart E e p q p' q') := by
  intro s t tr ur u z P A C
  have trace := (KeyArgs.enter_trace _ _ _ _ _ _ ⟨P.left.arguments, P.right.arguments⟩ A C).1
  obtain ⟨leftInput, leftFrame, leftKeeps⟩ := wp_result (enter_input_ok v P.left) A
  obtain ⟨rightInput, rightFrame, rightKeeps⟩ := wp_result (enter_input_ok v P.right) C
  refine ⟨trace, ⟨⟨leftInput, rightInput, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
    exact P.left.arguments.sp.trans P.right.arguments.sp.symm
  · unfold inputExponent
    rw [leftInput.exponent_preserved leftFrame]
    exact P.leftExponent
  · unfold inputExponent
    rw [rightInput.exponent_preserved rightFrame]
    exact P.rightExponent
  · unfold inputPrime
    rw [leftInput.output_preserved (by decide : 2 < 7) leftFrame]
    exact P.leftP
  · unfold inputPrime
    rw [leftInput.output_preserved (by decide : 3 < 7) leftFrame]
    exact P.leftQ
  · unfold inputPrime
    rw [rightInput.output_preserved (by decide : 2 < 7) rightFrame]
    exact P.rightP
  · unfold inputPrime
    rw [rightInput.output_preserved (by decide : 3 < 7) rightFrame]
    exact P.rightQ

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyEncodedResult`, which this module and modules that import it used -/

section

/-! # The native seven-port result is the shared encoded key operation -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86

def encodedOperation (E : Environment) (m : Mem) : Except Spec.RsaKeyGen.Failure (List (List Byte)) ⊕ Unit :=
  Proof.RsaKeyGen.keyOp E.primeLength
    (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len)
    (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len)
    (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)

def EncodedResult (E : Environment) (m : Mem) (t : State) : Prop :=
  let result := encodedOperation E m
  let outs := (List.range 7).map E.outputRegion
  (t.gpr .eax).toNat = Proof.RsaKeyGen.keyStatus result ∧
    match result with
    | .inl (.ok ys) => outs.map (fun r => Spec.Rsa.bytesAt t.mem r.base r.len) = ys
    | _ => ∀ r ∈ outs, Spec.Rsa.bytesAt t.mem r.base r.len = List.replicate r.len 0

theorem BodyOutcome.encoded {E : Environment} {m : Mem} {t : State} (v : E.Valid) (R : BodyOutcome E m t) :
    EncodedResult E m t := by
  have widths := v.widths
  have bits : 16 * E.primeLength = 32 * E.n := by omega_using [widths]
  unfold BodyOutcome WrittenCore at R
  rw [show E.outputs.n = E.n from rfl] at R
  unfold EncodedResult encodedOperation Proof.RsaKeyGen.keyOp
  rw [bits]
  cases code : Spec.RsaKeyGen.keyFromPrimes (32 * E.n)
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m E.exponentRegion.base E.exponentRegion.len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 2).base (E.outputRegion 2).len))
    (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (E.outputRegion 3).base (E.outputRegion 3).len)) with
  | inr u =>
    cases u
    rw [code] at R
    refine ⟨R.1, ?_⟩
    intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have bound := List.mem_range.mp hi
    simpa only [v.outputRegion bound, v.outputLength bound, Environment.outputRegion] using R.2 i bound
  | inl result =>
    cases result with
    | error failure =>
      rw [code] at R
      refine ⟨R.1, ?_⟩
      intro r hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      have bound := List.mem_range.mp hi
      simpa only [v.outputRegion bound, v.outputLength bound, Environment.outputRegion] using R.2 i bound
    | ok key =>
      rw [code] at R
      refine ⟨R.1, ?_⟩
      have values : ∀ i < 7, Spec.Rsa.bytesAt t.mem (E.outputRegion i).base (E.outputRegion i).len =
          Spec.Rsa.i2osp (keyField key i) (E.outputLength i) := by
        intro i hi
        simpa only [v.outputRegion hi, v.outputLength hi] using R.2 i hi
      have joined : ((List.range 7).map E.outputRegion).map (fun r => Spec.Rsa.bytesAt t.mem r.base r.len) =
          (List.range 7).map (fun i => Spec.Rsa.i2osp (keyField key i) (E.outputLength i)) := by
        rw [List.map_map]
        exact List.map_congr_left fun i hi => values i (List.mem_range.mp hi)
      exact joined

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! ### `RsaKeyGen.X86.KeyFramed`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeySaved`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyCallArgs`, which this module and modules that import it used -/

section

/-! # The native register push retains all eighteen cdecl key arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem CallLayout.workspaceMember {s : State} (A : CallLayout s) : callWorkspace s ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_right _ List.mem_cons_self

theorem CallLayout.argumentMember {s : State} (A : CallLayout s) : callArguments s ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem CallLayout.outputMember {s : State} (A : CallLayout s) {i : Nat} (hi : i < 7) : callOutput s i ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem CallLayout.argumentOffset {s : State} (A : CallLayout s) {i : Nat} (hi : i < 18) :
    argAddr s i = off (argAddr s 0) (4 * i) := by
  have fit := A.argsFit
  change addr (s.gpr .esp) (4 + 4 * i) = off (addr (s.gpr .esp) 4) (4 * i)
  rw [addr_eq (by omega_using [hi, fit]), addr_eq (by omega_using [fit])]
  simp only [off, BitVec.ofNat_add, BitVec.add_assoc]

theorem CallLayout.pushedArgument {s : State} (A : CallLayout s) {i : Nat} (hi : i < 18) :
    readSrc (Compact.entered s) (.mem (VG.Impl.RsaKeyGen.X86.CandidateArgs.arg i)) = some (arg s i) := by
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  have separate : (callArguments s).Disjoint (below (s.gpr .esp) 16) := by
    change (⟨addr (s.gpr .esp) 4, 72⟩ : Region).Disjoint (below (s.gpr .esp) 16)
    rw [addr_eq (by have := A.argsFit; omega_using [this])]
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.disjoint_below _ (by decide)
  have contains : (callArguments s).Contains (argAddr s i) 4 := by
    rw [A.argumentOffset hi]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  have word := F.readW contains (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate) (by decide : 32 / 8 < 2 ^ 64)
  change (Compact.entered s).load32 ((Compact.entered s).ea (VG.Impl.Mont.X86.Compact.arg i)) = _
  rw [Compact.argument_address]
  have access : InRegions ((Compact.entered s).rd ++ (Compact.entered s).wr) (argAddr s i) 4 := by
    refine ⟨callArguments s, List.mem_append_right _ (List.mem_cons_of_mem _ A.argumentMember), contains⟩
  rw [State.load32, ite_eq_left access]
  exact congrArg some word

theorem call_args_region (s : State) : KeyArgs.argsRegion (callSp s) = callArguments s := by
  unfold KeyArgs.argsRegion callArguments
  congr 1
  change ((s.gpr .esp - 16#32 + 20#32).setWidth 64) = ((s.gpr .esp + 4#32).setWidth 64)
  congr 1
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem entry_arguments {s : State} (h : contract.pre s) :
    KeyArgs.Entry (callEnvironment s).base (callEnvironment s).size (callSp s)
      (callEnvironment s).argument (Compact.entered s) := by
  have A := call_layout h
  have D := call_separation h
  have Z := call_sizes h
  have v := call_valid h
  have bank := v.bankFit
  have head : 72 ≤ (callEnvironment s).size := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at bank
    omega_using [bank]
  refine ⟨⟨?_, ?_⟩, head, rfl, workspace_stack h, ?_, ?_, ?_, ?_, workspace_deep h⟩
  · exact List.mem_cons_of_mem _ A.workspaceMember
  · change ((arg s 16).setWidth 64).toNat + 8 * (arg s 17).toNat ≤ 2 ^ 32
    rw [VG.BitVec.toNat_setWidth_32_64]
    exact A.workspaceFit
  · rw [Compact.entered, pushed_esp]
    rfl
  · rw [A.privateNat]
    have := A.low
    have := A.argsFit
    omega_using [this]
  · rw [call_args_region]
    exact D.argsWorkspace
  · intro i hi
    rw [Z.argument hi]
    exact A.pushedArgument hi

theorem entry_input {s : State} (h : contract.pre s) :
    EntryInput (callEnvironment s) (callSp s) (Compact.entered s) := by
  have A := call_layout h
  have Z := call_sizes h
  refine ⟨entry_arguments h, ?_, ?_, ?_⟩
  · intro i hi
    rw [Z.outputRegion hi]
    exact ⟨callOutput s i, List.mem_cons_of_mem _ (A.outputMember hi), Region.contains_self _ _⟩
  · refine ⟨callExponent s, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    change callExponent s ∈ s.rd
    rw [A.rd]
    exact List.mem_singleton_self _
  · intro i hi
    rw [call_args_region, Z.outputRegion hi]
    exact (call_separation h).argsOutput i hi

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Native key writes preserve the saved cdecl registers and return address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem call_writes {s : State} (h : contract.pre s) :
    (callEnvironment s).outputs.writes = callWorkspace s :: callOutputs s := by
  have v := call_valid h
  have Z := call_sizes h
  change callWorkspace s :: (List.range 7).map (callEnvironment s).outputs.region =
    callWorkspace s :: (List.range 7).map (callOutput s)
  congr 1
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  rw [v.outputRegion bound, Z.outputRegion bound]

theorem writes_reserved {s : State} (h : contract.pre s) :
    ∀ r ∈ (callEnvironment s).outputs.writes, r.Disjoint (reservedRegion s) := by
  have D := call_separation h
  rw [call_writes h]
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.stackWorkspace
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact D.stackOutput i (List.mem_range.mp hi)

theorem writes_return {s : State} (h : contract.pre s) :
    ∀ r ∈ (callEnvironment s).outputs.writes, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
  have D := call_separation h
  rw [call_writes h]
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact D.returnWorkspace
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact D.returnOutput i (List.mem_range.mp hi)

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Callable native key assembly restores all cdecl registers and the return address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86

theorem BodyOutcome.keep {E : Environment} {m : Mem} {s t : State} (R : BodyOutcome E m s)
    (eax : t.gpr .eax = s.gpr .eax) (memory : t.mem = s.mem) : BodyOutcome E m t := by
  simpa only [BodyOutcome, WrittenCore, eax, memory] using R

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The callable key operation uses the caller's original encoded inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem pushed_bytes {s : State} (h : contract.pre s) {r : Region}
    (far : r.Disjoint (reservedRegion s)) (size : r.len < 2 ^ 64) :
    Spec.Rsa.bytesAt (Compact.entered s).mem r.base r.len = Spec.Rsa.bytesAt s.mem r.base r.len := by
  have A := call_layout h
  have fit : 16 ≤ (s.gpr .esp).toNat := by have := A.low; omega_using [this]
  have F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) fit
  apply VG.Proof.Rsa.rsa_bytes_frame F size
  intro R hr
  obtain rfl := List.mem_singleton.mp hr
  exact far.sub_right A.savedSub

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # The shared native key implementation preserves ESP between its ABI frame operations -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86

theorem body_noSp : NoSp VG.Impl.RsaKeyGen.X86.KeyRuntime.body := NoSp.of_all (by decide +kernel)

theorem code_sp : (VG.Impl.RsaKeyGen.X86.KeyRuntime.code).all (fun i => !isa.writesSp i) = true := by
  apply Code.all_of_allInstrs
  have equal : (fun i => !isa.writesSp i) = (fun i => !VG.X86.Taint.clobbers i .esp) := by
    funext i
    cases i <;> rfl
  rw [equal]
  simp only [VG.Impl.RsaKeyGen.X86.KeyRuntime.code, Code.allInstrs]
  rw [VG.Proof.RsaKeyGen.X86.KeyNoSp.checked body_noSp]
  rfl

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.WriteArray`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.ContextWorkspace`, which this module and modules that import it used -/

section

/-! # Establish the three runtime widths from the retained cdecl arguments -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Rsa.X86.KeyRt (kw RtWs)
open VG.Proof.Bignum.X86 (CallArgument)
open VG.Proof.RsaKeyGen.X86.Key (Environment)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context)

theorem context_workspace {E : Environment} {p : BitVec 32} {s : State}
    (v : E.Valid) (C : Context E.base E.size p E.argument s)
    (old : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32) : Ws s E.base E.size E.n 32 := by
  obtain ⟨lo, hi, nk, kp, ke, plen⟩ := v.widths
  have width : E.n % 4 = 0 := by omega_using [nk, ke]
  have resize (k : Nat) (positive : 0 < k) (small : k ≤ E.n) :
      VG.Proof.Rsa.X86.Keys.Ws s E.base E.size k 32 := by
    refine ⟨old.workspace, Nat.le_trans ?_ old.fits, positive, Nat.le_trans small old.wle⟩
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Proof.Rsa.X86.Keys.S
    omega_using [small]
  have wsValue : BitVec.ofNat 32 E.base.toNat = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    simp only [Environment.base, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
    have bound := E.workspace.isLt
    omega_using []
  have wsArg : CallArgument s E.base E.size 20 (BitVec.ofNat 32 E.base.toNat) := by
    rw [wsValue]
    exact context_argument C (i := 16) (by decide)
  refine ⟨?_, ?_, ?_, width, ⟨lo, hi⟩, by rw [C.sp]; exact C.deep⟩
  · refine ⟨?_, ⟨2 * E.primeLength, by omega_using [hi, plen], ?_, context_argument C (i := 3) (by decide)⟩,
      wsArg, by omega_using [hi], by decide⟩
    · simpa only [kw_full width] using old
    · change kw (2 * E.primeLength) = kw (4 * E.n)
      rw [plen]
      congr 1
      omega_using []
  · refine ⟨?_, ⟨E.primeLength, by omega_using [hi, plen], ?_, context_argument C (i := 5) (by decide)⟩,
      wsArg, by omega_using [hi], by decide⟩
    · simpa only [kw_prime width] using resize (E.n / 2) (by omega_using [lo]) (by omega_using [])
    · change kw E.primeLength = kw (2 * E.n)
      rw [plen]
  · have kw8 : kw 8 = 2 := by decide
    refine ⟨?_, ⟨E.exponentLength, by have := v.exponentLength; omega_using [this], ?_,
      context_argument C (i := 15) (by decide)⟩, wsArg, by decide, by decide⟩
    · simpa only [kw8] using resize 2 (by decide) (by omega_using [lo])
    · have bounds := v.exponentLength
      change kw E.exponentLength = kw 8
      simp only [kw, Spec.Rsa.modulusWords]
      omega_using [bounds]

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyRuntime.ContextFar`, which this module and modules that import it used -/

section

/-! # The cdecl arguments survive writes away from them, such as the key outputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyArgs
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.CandidateArgs

/-- `Context.keep` for writes to any regions apart from the arguments. -/
theorem Context.keepFar {base : Addr} {size : Nat} {p : BitVec 32} {inputs : Nat → BitVec 32} {s t : State}
    {rs : List Reg} (C : Context base size p inputs s) (K : Keeps rs s t) {writes : List Region}
    (F : Frame writes s.mem t.mem) (far : ∀ r ∈ writes, (argsRegion p).Disjoint r)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) :
    Context base size p inputs t := by
  have spT : t.gpr .esp = p := (K.1 .esp esp).trans C.sp
  refine ⟨C.scratch.of_keeps K edi esp, C.header, spT, C.fit, C.separate, ?_, C.deep⟩
  intro i index
  have eaT : t.ea (arg i) = s.ea (arg i) := by
    change addr (t.gpr .esp) _ = addr (s.gpr .esp) _
    rw [K.1 .esp esp]
  have memory : t.mem.readW (s.ea (arg i)) 32 = s.mem.readW (s.ea (arg i)) 32 := by
    rw [C.address index]
    exact F.readW (r := argsRegion p)
      (Offset.contains_base _ (by change 4 * i + 4 ≤ 72; omega_using [index]) (by omega_using [index] : 4 * i < 2 ^ 64))
      far (by decide)
  have same : readSrc t (.mem (arg i)) = readSrc s (.mem (arg i)) := by
    show t.load32 (t.ea (arg i)) = s.load32 (s.ea (arg i))
    simp only [State.load32, eaT, K.2.1, K.2.2, memory]
  exact same.trans (C.read i index)

end VG.Proof.RsaKeyGen.X86.KeyArgs

end

end

/-! # One masked key output, through the pointer and length arguments, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kOk)
open VG.Proof.RsaKeyGen.X86.Key (Environment)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)
open VG.Proof.Bignum.X86 (byteAddr)

/-- `writeArray j pointer length`, with the pointer and length from arguments `pointer` and `length`. -/
theorem writeArray_ok {E : Environment} {sp : BitVec 32} {s : State} {j pointer length len : Nat}
    {p : BitVec 32} (valid : E.Valid) (h : VG.Proof.Rsa.X86.Keys.Ws s E.base E.size E.n 32)
    (C : Context E.base E.size sp E.argument s) (hj : j < 32) (nonzero : j ≠ aZero)
    (hp : pointer < 18) (hl : length < 18)
    (pointerEq : E.argument pointer = p) (lengthEq : E.argument length = BitVec.ofNat 32 len)
    (positive : 0 < len) (bound : len ≤ 4 * E.n)
    (fit : p.toNat + len ≤ 2 ^ 32) (write : InRegions s.wr (p.setWidth 64) len)
    (separate : Region.Disjoint ⟨E.base, E.size⟩ ⟨p.setWidth 64, len⟩)
    (far : (argsRegion sp).Disjoint ⟨p.setWidth 64, len⟩)
    (zero : num s.mem E.base E.n aZero = 0) (accept : Bool)
    (mask : slot s.mem E.base kOk = if accept then 1 else 0) :
    WP isa (writeArray j pointer length) s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ Context E.base E.size sp E.argument t ∧
      Spec.Rsa.bytesAt t.mem (p.setWidth 64) len =
        Spec.Rsa.i2osp ((if accept then num s.mem E.base E.n j else 0) % 2 ^ (8 * len)) len ∧
      Frame [⟨off E.base (arr E.n j), S E.n⟩, ⟨p.setWidth 64, len⟩] s.mem t.mem ∧
      (∀ d, d + 4 ≤ hdr → slot t.mem E.base d = slot s.mem E.base d) ∧
      (∀ k, k < 32 → k ≠ j → num t.mem E.base E.n k = num s.mem E.base E.n k) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  obtain H := context_workspace valid C h
  obtain fits := h.arr_fit hj
  obtain fit64 := h.fit64 hj
  have head := h.hdr_le
  have nowrap := h.workspace.nowrap
  unfold S at fits fit64
  unfold writeArray arraySetup
  refine WP.seq (WP.seq (WP.mono (sel_ok H hj (by decide) hj (by decide)
    (by rw [mask]; cases accept <;> decide) (Or.inl nonzero)) fun u ⟨Hu, Ou, selected, Ku⟩ => ?_))
  obtain raw : Outside E.base (arr E.n j) (S E.n) s.mem u.mem := by
    intro a ha
    apply Ou a
    intro r hr
    change r ∈ [(arr E.n j, S E.n)] at hr
    obtain rfl := List.mem_singleton.mp hr
    exact ha
  obtain ownFrame := VG.Proof.Bignum.outside_frame raw (by unfold S; exact fit64)
  obtain ownFar : (argsRegion sp).Disjoint ⟨off E.base (arr E.n j), S E.n⟩ :=
    C.separate.sub_right (Offset.sub_base E.base (by unfold S; exact fits))
  obtain Cu := C.keepFar Ku ownFrame (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact ownFar)
  obtain chosen : num u.mem E.base E.n j = if accept then num s.mem E.base E.n j else 0 := by
    rw [selected, mask, zero]
    cases accept <;> rfl
  obtain Pu := context_argument Cu (i := pointer) hp
  obtain Lu := context_argument Cu (i := length) hl
  simp only [List.cons_append, List.nil_append]
  refine wp_movS Pu.readSrc fun a A _ => ?_
  refine wp_movS (Lu.keep A.keeps (by decide) (by rw [A.mem]; exact Outside.refl _ _ _ _)).readSrc
    fun b Bb _ => ?_
  obtain Kab : Keeps [.ebx, .ecx] u b := (A.keeps.mono (by decide)).trans (Bb.keeps.mono (by decide))
  obtain mb : b.mem = u.mem := Bb.mem.trans A.mem
  obtain Hb := Hu.keep Kab (by rw [mb]; exact Outside.refl _ _ _ _)
  obtain ebx_b : b.gpr .ebx = p := by rw [Bb.other _ (by decide), A.gpr, pointerEq]
  obtain ecx_b : b.gpr .ecx = BitVec.ofNat 32 len := by rw [Bb.gpr, lengthEq]
  refine Hb.ptr_ok (arr j) (r := .esi) (t := .edx) (by decide) (by decide)
    (by change arr E.n j < _; omega_using [fits, nowrap]) fun c Kc mc Pc => ?_
  refine wp_addS rfl fun d D _ => wp_subS rfl fun e Ee _ => WP.block_nil ?_
  obtain Kce : Keeps [.esi] c e := (D.keeps.mono (by decide)).trans (Ee.keeps.mono (by decide))
  obtain me : e.mem = u.mem := by rw [Ee.mem, D.mem, mc, mb]
  obtain Kue : Keeps [.ebx, .ecx, .esi, .edx] u e :=
    ((Kab.mono (by decide)).trans (Kc.mono (by decide))).trans (Kce.mono (by decide))
  obtain Kse : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s e := (Ku.mono (by decide)).trans (Kue.mono (by decide))
  obtain ebx_e : e.gpr .ebx = p := by
    rw [Ee.other _ (by decide), D.other _ (by decide), Kc.1 _ (by decide), ebx_b]
  obtain ecx_e : e.gpr .ecx = BitVec.ofNat 32 len := by
    rw [Ee.other _ (by decide), D.other _ (by decide), Kc.1 _ (by decide), ecx_b]
  obtain ecx_c : c.gpr .ecx = BitVec.ofNat 32 len := by rw [Kc.1 _ (by decide), ecx_b]
  obtain srcNat : (c.gpr .esi).toNat = E.base.toNat + arr E.n j := by
    have P : (c.gpr .esi).toNat = (E.base.toNat + arr E.n j) % 2 ^ 32 := Pc
    rw [P, Nat.mod_eq_of_lt (by omega_using [fits, nowrap])]
  obtain lenSmall : len < 2 ^ 32 := by omega_using [bound, fits, nowrap]
  obtain esi_e : e.gpr .esi = c.gpr .esi + BitVec.ofNat 32 (len - 1) := by
    rw [Ee.gpr, D.gpr, ecx_c]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (1 : BitVec 32).toNat = 1 from rfl]
    have := (c.gpr .esi).isLt
    omega_using [positive]
  obtain source : byteAddr (c.gpr .esi) = off E.base (arr E.n j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, srcNat]
    omega_using []
  obtain rd : e.rd ++ e.wr = s.rd ++ s.wr := by rw [Kse.2.1, Kse.2.2]
  refine WP.mono (VG.Proof.Bignum.X86.reverseBuffer_ok e (src := c.gpr .esi) (dst := p) positive
    (by omega_using [bound, fits, nowrap, srcNat]) fit lenSmall
    (by rw [rd, source]; exact h.workspace.read (by omega_using [bound, fits]))
    (by rw [Kse.2.2]; exact write)
    (by rw [source]; exact separate.sub_left (Offset.sub_base E.base (by omega_using [bound, fits])))
    ebx_e esi_e ecx_e)
    fun t ⟨V, F, _, Kt⟩ => ?_
  rw [source, me] at V
  rw [me] at F
  change Frame [⟨p.setWidth 64, len⟩] u.mem t.mem at F
  obtain all : Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := Kse.trans (Kt.mono (by decide))
  obtain prefixValue : (u.mem.read (off E.base (arr E.n j)) len).toNat =
      num u.mem E.base E.n j % 2 ^ (8 * len) := by
    rw [VG.Proof.Bignum.read_prefix u.mem _ bound, BitVec.toNat_setWidth, VG.Proof.Bignum.read_eq_val32]
  refine ⟨h.rest all, Cu.keepFar ((Kue.mono (rs' := [.eax, .ebx, .ecx, .esi, .edx]) (by decide)).trans (Kt.mono (by decide))) F
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact far), ?_, ?_, ?_, ?_, all⟩
  · change Spec.Rsa.bytesAt t.mem (p.setWidth 64) len = _ at V
    rw [V, prefixValue, chosen]
  · exact (ownFrame.mono (by simp)).trans (F.mono (by simp))
  · intro d hd
    change w32 t.mem E.base d = w32 s.mem E.base d
    rw [VG.Proof.RsaKeyGen.X86.Key.output_word h separate F (by omega_using [head, hd])]
    exact Ou.slot hd (by simp)
  · intro k hk different
    rw [VG.Proof.RsaKeyGen.X86.Key.output_num h separate F hk]
    exact Ou.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact Ne.symm different)
      (by simp) (h.fit64 hk)

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # The seven masked key outputs and the status, at the run-time width -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Impl.RsaKeyGen.X86.Key (kOk kStatus outputIndex)
open VG.Proof.RsaKeyGen.X86.Key (Environment ExportProgress OutputInput portResult portFrame_global
  portFrame_other outputIndex_bound outputIndex_zero outputIndex_injective WrittenCore CoreOutcome)
open VG.Proof.RsaKeyGen.X86.KeyArgs (Context argsRegion)

/-- What the outputs need beyond `ExportProgress`: the arguments, and outputs apart from them. -/
structure OutputArgs (E : Environment) (sp : BitVec 32) (s : State) : Prop where
  valid : E.Valid
  context : Context E.base E.size sp E.argument s
  apart : ∀ i < 7, (argsRegion sp).Disjoint (E.outputs.region i)

theorem port_ok {E : Environment} {sp : BitVec 32} {m : Mem} {accept : Bool} {i : Nat} {s : State}
    (P : ExportProgress E.outputs m accept i s) (A : OutputArgs E sp s) (hi : i < 7) :
    WP isa (writePort i) s fun t =>
      ExportProgress E.outputs m accept (i + 1) t ∧ OutputArgs E sp t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have h := P.input
  refine WP.mono (writeArray_ok (p := E.outputs.pointer i) (len := E.outputs.length i) A.valid h.ws A.context
    (outputIndex_bound hi) (Ne.symm (outputIndex_zero hi)) (by omega_using [hi]) (by omega_using [hi]) rfl
    (by simp only [VG.Proof.RsaKeyGen.X86.Key.OutputGeometry.length, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl)
    (h.valid.lengthPositive i hi) (h.valid.lengthBound i hi) (h.valid.fit i hi)
    (h.writable i hi) (h.valid.scratchApart i hi) (A.apart i hi) P.zero accept P.mask)
    fun t ⟨ht, Ct, value, F, header, other, K⟩ => ?_
  refine ⟨⟨h.after ht K header, (other aZero (by decide) (outputIndex_zero hi)).trans P.zero,
    (header kOk (by decide)).trans P.mask, ?_, ?_, ?_⟩, ⟨A.valid, Ct, A.apart⟩,
    portFrame_global h hi F, K⟩
  · intro d hd
    exact (header d hd).trans (P.header d hd)
  · intro j lower upper
    exact (other (outputIndex j) (outputIndex_bound upper)
      (outputIndex_injective upper hi (by omega_using [lower]))).trans (P.pending j (by omega_using [lower]) upper)
  · intro j lower upper
    by_cases last : j = i
    · subst j
      unfold portResult
      rw [← P.pending i (Nat.le_refl _) hi]
      exact value
    · exact (portFrame_other h hi upper (by omega_using [last]) F).trans (P.done j (by omega_using [lower, last]) upper)

theorem ports_ok {E : Environment} {sp : BitVec 32} {m : Mem} {accept : Bool} {i count : Nat} {s : State}
    (P : ExportProgress E.outputs m accept i s) (A : OutputArgs E sp s) (bound : i + count ≤ 7) :
    WP isa (writePorts i count) s fun t =>
      ExportProgress E.outputs m accept (i + count) t ∧ OutputArgs E sp t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  induction count generalizing i s with
  | zero => exact WP.block_nil ⟨P, A, Frame.refl _ _, Keeps.refl _ _⟩
  | succ count ih =>
    unfold writePorts
    refine WP.seq (WP.mono (port_ok P A (by omega_using [bound])) fun u ⟨Pu, Au, Fu, Ku⟩ => ?_)
    refine WP.mono (ih Pu Au (by omega_using [bound])) fun t ⟨Pt, At, Ft, Kt⟩ => ?_
    have index : i + 1 + count = i + (count + 1) := by omega_using []
    rw [index] at Pt
    exact ⟨Pt, At, Fu.trans Ft, Ku.trans Kt⟩

theorem writeOutputs_ok {E : Environment} {sp : BitVec 32} {s : State} (h : OutputInput E.outputs s)
    (A : OutputArgs E sp s) (accept : Bool) (mask : slot s.mem E.base kOk = if accept then 1 else 0) :
    WP isa writeOutputs s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ (t.gpr .eax).toNat = slot s.mem E.base kStatus ∧
      (∀ i, i < 7 → Spec.Rsa.bytesAt t.mem (E.outputs.region i).base (E.outputs.region i).len =
        portResult E.outputs s.mem accept i) ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have H := context_workspace A.valid A.context h.ws
  have fits := h.ws.arr_fit (j := aZero) (by decide)
  have fit64 := h.ws.fit64 (j := aZero) (by decide)
  unfold writeOutputs seqs
  refine WP.seq (WP.mono (zero_ok H .modulus (arr aZero) (by change arr E.n aZero + _ ≤ E.size; exact fits))
    fun u ⟨Hu, Ou, zero, Ku⟩ => ?_)
  change Outside E.base (arr E.n aZero) (S E.n) s.mem u.mem at Ou
  change val32 u.mem E.base (arr E.n aZero) (E.n + 2) = 0 at zero
  have clear : Keep E.base E.n [aZero] [] s.mem u.mem :=
    Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using Ou) (by unfold S; omega_using []) (by simp)
  have header : ∀ d, d + 4 ≤ hdr → slot u.mem E.base d = slot s.mem E.base d :=
    fun d hd => clear.slot hd (by simp)
  have Pu : ExportProgress E.outputs s.mem accept 0 u := by
    refine ⟨h.after Hu.old Ku header, ?_, (header kOk (by decide)).trans mask, header, ?_, ?_⟩
    · change val32 u.mem E.base (arr E.n aZero) E.n = 0
      have Z := VG.Proof.Rsa.KeyWorkspace.val32_zero_part zero (a := 0) (c := E.n) (by omega_using [])
      simpa only [Nat.mul_zero, Nat.add_zero] using Z
    · intro i _ hi
      exact clear.num (by intro a ha; obtain rfl := List.mem_singleton.mp ha; exact outputIndex_zero hi)
        (by simp) (h.ws.fit64 (outputIndex_bound hi))
    · intro i hi
      omega_using [hi]
  have ownFrame := VG.Proof.Bignum.outside_frame Ou fit64
  have Fu : Frame E.outputs.writes s.mem u.mem := by
    apply ownFrame.sub
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨E.outputs.scratch, List.mem_cons_self, Offset.sub_base E.base fits⟩
  have Au : OutputArgs E sp u := ⟨A.valid, A.context.keepFar Ku ownFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact A.context.separate.sub_right (Offset.sub_base E.base fits)), A.apart⟩
  refine WP.seq (WP.mono (ports_ok Pu Au (by decide : 0 + 7 ≤ 7)) fun v ⟨Pv, _, Fv, Kv⟩ => ?_)
  have head := Pv.input.ws.hdr_le
  refine wp_movS (readSrc_sc Pv.input.ws.workspace (by unfold kStatus hdr at *; omega_using [head]))
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

theorem writeCore_ok {E : Environment} {sp : BitVec 32} {s : State} {e p q : Nat}
    (h : OutputInput E.outputs s) (A : OutputArgs E sp s) (result : CoreOutcome E.base E.n e p q s.mem) :
    WP isa writeOutputs s fun t =>
      VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32 ∧ WrittenCore E.outputs e p q t ∧
      Frame E.outputs.writes s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t :=
  VG.Proof.RsaKeyGen.X86.Key.writeCore_of (g := E.outputs) (fun accept mask => writeOutputs_ok h A accept mask) result

end VG.Proof.RsaKeyGen.X86.KeyRuntime
