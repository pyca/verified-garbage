module

public import VerifiedGarbage.Proof.Dsa.Arm.ValidateOps
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on 32-bit ARM: values across operations

The caller's operands (`Input`: a `Ready` operand apart from the whole
working space, with its value) and the computed values in the working space
past the arithmetic (`localVal`) are kept by every operation that does not
store over them (`Input.stage`, `Stage.localVal`), and the flag word by
every operation that stores elsewhere (`Stage.maskW`). A schedule of
operations changes only the working space's arithmetic, its computed values
and the flag word (`Run`): not the saved pointers, nor the saved registers.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)
open VG.Proof.X25519.Arm (Rest)

/-- An operand of the caller, apart from the working space, with value `v`. -/
structure Input (s : State) (base : Addr) (size : Nat) (p : Pointer) (len v : Nat) : Prop
    extends Ready s base p len where
  outside : Region.Disjoint ⟨State.addr (pointerValue base s p), len⟩ ⟨base, size⟩
  value : operand base s p len = v

/-- The working space's memory a schedule may change: the arithmetic's, the
flag word and the computed values. -/
def runRanges : List (Nat × Nat) := [(0, 64), (116, 4), (168, 36), (256, 15456)]

/-- What a schedule keeps. -/
structure Run (base : Addr) (s t : State) : Prop where
  rest : Rest coreClob s t
  mem : Outs base runRanges s.mem t.mem

theorem Run.refl (base : Addr) (s : State) : Run base s s := ⟨Rest.refl _ _, Outs.refl _ _ _⟩

theorem Run.trans {base : Addr} {s t u : State} (h₁ : Run base s t) (h₂ : Run base t u) : Run base s u :=
  ⟨h₁.rest.trans h₂.rest, h₁.mem.trans h₂.mem⟩

theorem Stage.run {base : Addr} {s t : State} {output len : Nat} (St : Stage base s t output len)
    (ho : output = 116 ∧ len = 4 ∨ 4960 ≤ output ∧ output + len ≤ 15712) : Run base s t :=
  ⟨St.rest, fun x hx => St.mem x fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h₁ := hx (0, 64) (by simp [runRanges])
    have h₂ := hx (116, 4) (by simp [runRanges])
    have h₃ := hx (256, 15456) (by simp [runRanges])
    simp only at h₁ h₂ h₃
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega⟩

theorem Stage.ws {base : Addr} {s t : State} {size output len : Nat} (St : Stage base s t output len)
    (hs : Ws s base size) : Ws t base size :=
  hs.of_rest St.rest (by decide)

theorem Stage.maskW {base : Addr} {s t : State} {output len : Nat} (St : Stage base s t output len)
    (ho : 120 ≤ output) : maskW base t = maskW base s :=
  maskW_keep St.mem fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega

theorem Input.stage {base : Addr} {s t : State} {size output l : Nat} {p : Pointer} {len v : Nat}
    (I : Input s base size p len v) (St : Stage base s t output l) (hout : 116 ≤ output)
    (hz : 4960 ≤ size) (hz2 : size ≤ 2 ^ 32) (ho : output + l ≤ size) : Input t base size p len v := by
  have hO : ∀ r ∈ arithRanges ++ [(output, l)], r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have hz' : ∀ r ∈ arithRanges ++ [(output, l)], r.1 + r.2 ≤ size := fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  have P := pointerValue_keep (St.rest.gpr .r12 (by decide)) St.mem hO I.ok
  refine ⟨I.toReady.keep_rest St.rest (O := St.mem) (hO := hO), by rw [P]; exact I.outside, ?_⟩
  rw [operand, P, outs_bytes St.mem (by have := I.fits; omega) (fun r hr => by have := hz' r hr; omega)
    (fun r hr => I.outside.sub_right (Offset.sub_base base (hz' r hr)))]
  exact I.value

theorem Input.run {base : Addr} {s t : State} {size : Nat} {p : Pointer} {len v : Nat}
    (I : Input s base size p len v) (Rn : Run base s t) (hz : 15712 ≤ size) (hz2 : size ≤ 2 ^ 32) :
    Input t base size p len v := by
  have hO : ∀ r ∈ runRanges, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide
  have hz' : ∀ r ∈ runRanges, r.1 + r.2 ≤ size := fun r hr => by
    simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega
  have P := pointerValue_keep (Rn.rest.gpr .r12 (by decide)) Rn.mem hO I.ok
  refine ⟨I.toReady.keep_rest Rn.rest (O := Rn.mem) (hO := hO), by rw [P]; exact I.outside, ?_⟩
  rw [operand, P, outs_bytes Rn.mem (by have := I.fits; omega) (fun r hr => by have := hz' r hr; omega)
    (fun r hr => I.outside.sub_right (Offset.sub_base base (hz' r hr)))]
  exact I.value

theorem Run.ws {base : Addr} {s t : State} {size : Nat} (Rn : Run base s t) (hs : Ws s base size) :
    Ws t base size :=
  hs.of_rest Rn.rest (by decide)

/-! ## Computed values -/

/-- The value of the `len` bytes at offset `o`. -/
abbrev localVal (base : Addr) (s : State) (o len : Nat) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base o) len)

theorem local_addr {s : State} {base : Addr} {size o : Nat} (hs : Ws s base size) (ho : o < size) :
    State.addr (pointerValue base s (.local o)) = off base o := by
  have := hs.ea (r := .r12) (K := 0) (d := o) (BitVec.add_zero _).symm (by omega)
  rwa [Nat.zero_add] at this

theorem local_operand {s : State} {base : Addr} {size o len : Nat} (hs : Ws s base size) (ho : o < size) :
    operand base s (.local o) len = localVal base s o len := by
  rw [operand, local_addr hs ho]

theorem localReady {s : State} {base : Addr} {size o len : Nat} (hs : Ws s base size) (ho : 4960 ≤ o)
    (hol : o + len < size) (h16 : o < 2 ^ 16) : Ready s base (.local o) len := by
  have nw := hs.nowrap
  have A := local_addr hs (o := o) (by omega)
  refine ⟨h16, ?_, ?_, ?_⟩
  · rw [pointerValue, BitVec.toNat_add, BitVec.toNat_ofNat, hs.wb_toNat, Nat.mod_eq_of_lt (by omega : o < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega)]
    omega
  · intro e k hek
    rw [A, off, Offset.add_add]
    exact hs.read (by omega)
  · rw [A]
    exact Offset.disjoint_base base ho (by omega)

theorem Stage.localVal_eq {base : Addr} {s t : State} {output l o len : Nat} (St : Stage base s t output l)
    (ho : 4960 ≤ o) (hb : o + len ≤ 2 ^ 32) (hol : output + l ≤ 2 ^ 32)
    (hsep : o + len ≤ output ∨ output + l ≤ o) : localVal base t o len = localVal base s o len := by
  rw [Arm.localVal, Arm.localVal, outs_bytes St.mem (by omega)]
  · intro r hr
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega
  · intro r hr
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint base (.inr (by omega)) (by omega) (by omega)
    · exact Offset.disjoint base (.inr (by omega)) (by omega) (by omega)
    · exact Offset.disjoint base hsep (by omega) (by omega)

/-- A stored result's value. -/
theorem localVal_of_bytes {base : Addr} {s : State} {o len v : Nat}
    (h : Spec.Rsa.bytesAt s.mem (off base o) len = Spec.Dsa.encodeBE len v) (hv : v < 256 ^ len) :
    localVal base s o len = v := by
  rw [localVal, h, decodeBE_encodeBE hv]

/-- The computed values in `[lo, hi)` are kept. -/
def KeepsLocals (base : Addr) (s t : State) (lo hi : Nat) : Prop :=
  ∀ o len, lo ≤ o → o + len ≤ hi → localVal base t o len = localVal base s o len

theorem KeepsLocals.refl (base : Addr) (s : State) (lo hi : Nat) : KeepsLocals base s s lo hi := fun _ _ _ _ => rfl

theorem KeepsLocals.trans {base : Addr} {s t u : State} {lo hi : Nat} (h₁ : KeepsLocals base s t lo hi)
    (h₂ : KeepsLocals base t u lo hi) : KeepsLocals base s u lo hi :=
  fun o len h h' => (h₂ o len h h').trans (h₁ o len h h')

theorem Stage.keeps {base : Addr} {s t : State} {output l lo hi : Nat} (St : Stage base s t output l)
    (hlo : 4960 ≤ lo) (hhi : hi ≤ 2 ^ 32) (hol : output + l ≤ 2 ^ 32) (hsep : hi ≤ output ∨ output + l ≤ lo) :
    KeepsLocals base s t lo hi :=
  fun _ _ h h' => St.localVal_eq (by omega) (by omega) hol (by omega)

end VG.Proof.Dsa.Arm
