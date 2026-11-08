module

public import VerifiedGarbage.Spec.MlKem.Contract1024
public import VerifiedGarbage.Spec.MlKem.EncapsH
public import VerifiedGarbage.Spec.Zeroize
import VerifiedGarbage.Proof.Framework.Mem

/-!
# ML-KEM leaving `scratch` scrubbed, on every target

Each of ML-KEM-768's and ML-KEM-1024's functions taking `scratch` (key
generation, encapsulation, with `H(ek)` given or not, and decapsulation)
meets its contract and leaves each byte of `scratch` unchanged or zero
(`Spec.Zeroize.scrubbed`): the contracts `keyGenContract`, … here, which are
those of `Spec/MlKem/` (`keyGen_eq`, …), written as the postconditions
without that clause (`keyGenPost`, …) with it added (`scrub4`, `scrub5`,
`scrub6`: `scratch` is the last argument of each). Every target's
implementation is proven against them.

Each target's `callWipe` zeroes all of `scratch` once the function's code
returns (but x86-64's, which zeroes only what that code may write), so the
clause follows from the bytes it zeroes (`keyGen_wiped`, …:
`scrubbed_of_zeros`).
-/

@[expose] public section

namespace VG.Proof.MlKem.Scrubbed

open VG.Spec.MlKem (Outcome leakRho)
open VG.Spec.Sha3 (bytesAt)

/-! ## Buffers left scrubbed -/

/-- A buffer whose bytes are all zero holds nothing written. -/
theorem scrubbed_of_zeros {m m' : Mem} {p : Addr} {len : Nat}
    (h : Spec.Zeroize.bytesAt m' p len = Spec.Zeroize.zeros len) : Spec.Zeroize.scrubbed m m' p len := by
  intro a ha
  right
  have hi : (a - p).toNat < len := by simp only [Region.Contains] at ha; omega
  have he := congrArg (·[(a - p).toNat]?) h
  simp only [Spec.Zeroize.bytesAt, Spec.Zeroize.zeros, List.getElem?_map, List.getElem?_range hi,
    List.getElem?_replicate, hi, ite_true, Option.map_some, Option.some.injEq,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at he
  rwa [BitVec.add_comm, BitVec.sub_add_cancel] at he

/-- A buffer whose first `w` bytes are zero and whose others are unchanged
holds nothing written. -/
theorem scrubbed_of_prefix {m m' : Mem} {p : Addr} {w len : Nat}
    (hz : Spec.Zeroize.bytesAt m' p w = Spec.Zeroize.zeros w)
    (ht : ∀ i, w ≤ i → i < len → m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Zeroize.scrubbed m m' p len := by
  intro a ha
  have hi : (a - p).toNat < len := by simp only [Region.Contains] at ha; omega
  have ea : p + BitVec.ofNat 64 (a - p).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  by_cases hw : (a - p).toNat < w
  · right
    have he := congrArg (·[(a - p).toNat]?) hz
    simp only [Spec.Zeroize.bytesAt, Spec.Zeroize.zeros, List.getElem?_map, List.getElem?_range hw,
      List.getElem?_replicate, hw, ite_true, Option.map_some, Option.some.injEq] at he
    rwa [ea] at he
  · left
    have he := ht _ (Nat.le_of_not_lt hw) hi
    rwa [ea] at he

/-! ## Postconditions with `scratch`, the last argument, scrubbed -/

/-- A postcondition of four pointers. -/
abbrev Post4 : Type := Addr → Addr → Addr → Addr → Mem → Mem → BitVec 32 → Prop

/-- A postcondition of five pointers. -/
abbrev Post5 : Type := Addr → Addr → Addr → Addr → Addr → Mem → Mem → BitVec 32 → Prop

/-- A postcondition of six pointers. -/
abbrev Post6 : Type := Addr → Addr → Addr → Addr → Addr → Addr → Mem → Mem → BitVec 32 → Prop

/-- `P`, and the `len` bytes at the last argument scrubbed. -/
def scrub4 (len : Nat) (P : Post4) : Post4 := fun a b c d m m' r =>
  P a b c d m m' r ∧ Spec.Zeroize.scrubbed m m' d len

/-- `P`, and the `len` bytes at the last argument scrubbed. -/
def scrub5 (len : Nat) (P : Post5) : Post5 := fun a b c d e m m' r =>
  P a b c d e m m' r ∧ Spec.Zeroize.scrubbed m m' e len

/-- `P`, and the `len` bytes at the last argument scrubbed. -/
def scrub6 (len : Nat) (P : Post6) : Post6 := fun a b c d e f m m' r =>
  P a b c d e f m m' r ∧ Spec.Zeroize.scrubbed m m' f len

theorem vs4 {vs : List (BitVec 64)} (h : vs.length = 4) : ∃ a b c d, vs = [a, b, c, d] :=
  match vs, h with | [a, b, c, d], _ => ⟨a, b, c, d, rfl⟩

theorem vs5 {vs : List (BitVec 64)} (h : vs.length = 5) : ∃ a b c d e, vs = [a, b, c, d, e] :=
  match vs, h with | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩

theorem vs6 {vs : List (BitVec 64)} (h : vs.length = 6) : ∃ a b c d e f, vs = [a, b, c, d, e, f] :=
  match vs, h with | [a, b, c, d, e, f], _ => ⟨a, b, c, d, e, f, rfl⟩

/-- With the `len` bytes at the last argument zero, `scrub4`. -/
theorem wiped4 (len : Nat) (P : Post4) : ∀ vs m m' x, vs.length = 4 →
    Curry.apply [.addr, .addr, .addr, .addr] P vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) len = Spec.Zeroize.zeros len →
      Curry.apply [.addr, .addr, .addr, .addr] (scrub4 len P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, rfl⟩ := vs4 hlen
  exact ⟨h, scrubbed_of_zeros hz⟩

/-- With the `len` bytes at the last argument zero, `scrub5`. -/
theorem wiped5 (len : Nat) (P : Post5) : ∀ vs m m' x, vs.length = 5 →
    Curry.apply [.addr, .addr, .addr, .addr, .addr] P vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) len = Spec.Zeroize.zeros len →
      Curry.apply [.addr, .addr, .addr, .addr, .addr] (scrub5 len P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, rfl⟩ := vs5 hlen
  exact ⟨h, scrubbed_of_zeros hz⟩

/-- With the `len` bytes at the last argument zero, `scrub6`. -/
theorem wiped6 (len : Nat) (P : Post6) : ∀ vs m m' x, vs.length = 6 →
    Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] P vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) len = Spec.Zeroize.zeros len →
      Curry.apply [.addr, .addr, .addr, .addr, .addr, .addr] (scrub6 len P) vs m m' x := by
  intro vs m m' x hlen h hz
  obtain ⟨a, b, c, d, e, f, rfl⟩ := vs6 hlen
  exact ⟨h, scrubbed_of_zeros hz⟩

/-! ## The contracts of the functions' bodies

Each function is its body, `vg_mlkem*_<function>_body`, an internal
function, followed by `callWipe`. Every target's implementation of a body
is proven against its contract here (`keyGenBodyContract`, …), which is
that of `Spec/MlKem/` without its clause on `scratch`: the body does not
leave `scratch` scrubbed. -/

/-- The contract of `vg_mlkem768_keygen_body`: `Spec.MlKem.keyGenContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def keyGenBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.keyGenSig.contract A
    (post := fun seed ek dk _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.keyGenInternal Spec.MlKem.mlKem768 iters (bytesAt m seed 32)
          (bytesAt m (seed + 32) 32)) r
        (bytesAt m' ek 1184, bytesAt m' dk 2400))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ek _dk _scratch m =>
      leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem768 (bytesAt m seed 32)))

/-- The contract of `vg_mlkem768_encaps_h_body`: `Spec.MlKem.encapsHContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def encapsHBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = Spec.MlKem.H (bytesAt m ek 1184))
    (post := fun ek _h msg key ct _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem768 iters (bytesAt m ek 1184)
          (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1088))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem768 (bytesAt m ek 1184)))

/-- The contract of `vg_mlkem768_encaps_body`: `Spec.MlKem.encapsContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def encapsBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.encapsSig.contract A
    (post := fun ek msg key ct _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem768 iters (bytesAt m ek 1184)
          (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1088))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem768 (bytesAt m ek 1184)))

/-- The contract of `vg_mlkem768_decaps_body`: `Spec.MlKem.decapsContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def decapsBodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.decapsSig.contract A
    (post := fun dk ct key _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.decapsInternal Spec.MlKem.mlKem768 iters (bytesAt m dk 2400)
          (bytesAt m ct 1088)) r (bytesAt m' key 32))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun dk _ct _key _scratch m =>
      leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem768 (bytesAt m dk 2400)))

/-- The contract of `vg_mlkem1024_keygen_body`: `Spec.MlKem1024.keyGenContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def keyGen1024BodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.keyGenSig.contract A
    (post := fun seed ek dk _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.keyGenInternal Spec.MlKem.mlKem1024 iters (bytesAt m seed 32)
          (bytesAt m (seed + 32) 32)) r
        (bytesAt m' ek 1568, bytesAt m' dk 3168))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun seed _ek _dk _scratch m =>
      leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem1024 (bytesAt m seed 32)))

/-- The contract of `vg_mlkem1024_encaps_h_body`: `Spec.MlKem1024.encapsHContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def encapsH1024BodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = Spec.MlKem.H (bytesAt m ek 1568))
    (post := fun ek _h msg key ct _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m ek 1568)
          (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1568))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (bytesAt m ek 1568)))

/-- The contract of `vg_mlkem1024_encaps_body`: `Spec.MlKem1024.encapsContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def encaps1024BodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.encapsSig.contract A
    (post := fun ek msg key ct _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m ek 1568)
          (bytesAt m msg 32)) r
        (bytesAt m' key 32, bytesAt m' ct 1568))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (bytesAt m ek 1568)))

/-- The contract of `vg_mlkem1024_decaps_body`: `Spec.MlKem1024.decapsContract`'s
precondition and leak, and its postcondition without a clause on `scratch`. -/
def decaps1024BodyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.decapsSig.contract A
    (post := fun dk ct key _scratch m m' r =>
      Outcome (fun iters => Spec.MlKem.decapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m dk 3168)
          (bytesAt m ct 1568)) r (bytesAt m' key 32))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun dk _ct _key _scratch m =>
      leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem1024 (bytesAt m dk 3168)))

/-! ## ML-KEM-768 -/

/-- `Spec.MlKem.keyGenContract`'s postcondition without its clause on
`scratch`. -/
def keyGenPost (pb : Nat) : Spec.MlKem.keyGenSig.Post pb := fun seed ek dk _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.keyGenInternal Spec.MlKem.mlKem768 iters (bytesAt m seed 32)
      (bytesAt m (seed + 32) 32)) r
    (bytesAt m' ek 1184, bytesAt m' dk 2400)

/-- `keyGenPost`, and each byte of `scratch` unchanged or zero on return. -/
def keyGenContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.keyGenSig.contract A
    (post := scrub4 32768 (keyGenPost A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun seed _ek _dk _scratch m =>
      leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem768 (bytesAt m seed 32)))

/-- `Spec.MlKem.keyGenContract` is `keyGenContract`. -/
theorem keyGen_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.MlKem.keyGenContract A stack = keyGenContract A stack :=
  rfl

/-- `Spec.MlKem.encapsHContract`'s postcondition without its clause on
`scratch`. -/
def encapsHPost (pb : Nat) : Spec.MlKem.encapsHSig.Post pb := fun ek _h msg key ct _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem768 iters (bytesAt m ek 1184)
      (bytesAt m msg 32)) r
    (bytesAt m' key 32, bytesAt m' ct 1088)

/-- `encapsHPost`, and each byte of `scratch` unchanged or zero on return. -/
def encapsHContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = Spec.MlKem.H (bytesAt m ek 1184))
    (post := scrub6 32768 (encapsHPost A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem768 (bytesAt m ek 1184)))

/-- `Spec.MlKem.encapsHContract` is `encapsHContract`. -/
theorem encapsH_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.MlKem.encapsHContract A stack = encapsHContract A stack :=
  rfl

/-- `Spec.MlKem.encapsContract`'s postcondition without its clause on
`scratch`. -/
def encapsPost (pb : Nat) : Spec.MlKem.encapsSig.Post pb := fun ek msg key ct _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem768 iters (bytesAt m ek 1184)
      (bytesAt m msg 32)) r
    (bytesAt m' key 32, bytesAt m' ct 1088)

/-- `encapsPost`, and each byte of `scratch` unchanged or zero on return. -/
def encapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.encapsSig.contract A
    (post := scrub5 32768 (encapsPost A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem768 (bytesAt m ek 1184)))

/-- `Spec.MlKem.encapsContract` is `encapsContract`. -/
theorem encaps_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.MlKem.encapsContract A stack = encapsContract A stack :=
  rfl

/-- `Spec.MlKem.decapsContract`'s postcondition without its clause on
`scratch`. -/
def decapsPost (pb : Nat) : Spec.MlKem.decapsSig.Post pb := fun dk ct key _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.decapsInternal Spec.MlKem.mlKem768 iters (bytesAt m dk 2400)
      (bytesAt m ct 1088)) r (bytesAt m' key 32)

/-- `decapsPost`, and each byte of `scratch` unchanged or zero on return. -/
def decapsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem.decapsSig.contract A
    (post := scrub4 32768 (decapsPost A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun dk _ct _key _scratch m =>
      leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem768 (bytesAt m dk 2400)))

/-- `Spec.MlKem.decapsContract` is `decapsContract`. -/
theorem decaps_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.MlKem.decapsContract A stack = decapsContract A stack :=
  rfl

/-! ## ML-KEM-1024 -/

/-- `Spec.MlKem1024.keyGenContract`'s postcondition without its clause on
`scratch`. -/
def keyGen1024Post (pb : Nat) : Spec.MlKem1024.keyGenSig.Post pb := fun seed ek dk _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.keyGenInternal Spec.MlKem.mlKem1024 iters (bytesAt m seed 32)
      (bytesAt m (seed + 32) 32)) r
    (bytesAt m' ek 1568, bytesAt m' dk 3168)

/-- `keyGen1024Post`, and each byte of `scratch` unchanged or zero on return. -/
def keyGen1024Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.keyGenSig.contract A
    (post := scrub4 49152 (keyGen1024Post A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun seed _ek _dk _scratch m =>
      leakRho (Spec.MlKem.keyGenRho Spec.MlKem.mlKem1024 (bytesAt m seed 32)))

/-- `Spec.MlKem1024.keyGenContract` is `keyGen1024Contract`. -/
theorem keyGen1024_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.MlKem1024.keyGenContract A stack = keyGen1024Contract A stack :=
  rfl

/-- `Spec.MlKem1024.encapsHContract`'s postcondition without its clause on
`scratch`. -/
def encapsH1024Post (pb : Nat) : Spec.MlKem1024.encapsHSig.Post pb := fun ek _h msg key ct _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m ek 1568)
      (bytesAt m msg 32)) r
    (bytesAt m' key 32, bytesAt m' ct 1568)

/-- `encapsH1024Post`, and each byte of `scratch` unchanged or zero on return. -/
def encapsH1024Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.encapsHSig.contract A
    (pre := fun ek h _msg _key _ct _scratch m => bytesAt m h 32 = Spec.MlKem.H (bytesAt m ek 1568))
    (post := scrub6 49152 (encapsH1024Post A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun ek _h _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (bytesAt m ek 1568)))

/-- `Spec.MlKem1024.encapsHContract` is `encapsH1024Contract`. -/
theorem encapsH1024_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.MlKem1024.encapsHContract A stack = encapsH1024Contract A stack :=
  rfl

/-- `Spec.MlKem1024.encapsContract`'s postcondition without its clause on
`scratch`. -/
def encaps1024Post (pb : Nat) : Spec.MlKem1024.encapsSig.Post pb := fun ek msg key ct _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.encapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m ek 1568)
      (bytesAt m msg 32)) r
    (bytesAt m' key 32, bytesAt m' ct 1568)

/-- `encaps1024Post`, and each byte of `scratch` unchanged or zero on return. -/
def encaps1024Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.encapsSig.contract A
    (post := scrub5 49152 (encaps1024Post A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun ek _msg _key _ct _scratch m =>
      leakRho (Spec.MlKem.ekRho Spec.MlKem.mlKem1024 (bytesAt m ek 1568)))

/-- `Spec.MlKem1024.encapsContract` is `encaps1024Contract`. -/
theorem encaps1024_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.MlKem1024.encapsContract A stack = encaps1024Contract A stack :=
  rfl

/-- `Spec.MlKem1024.decapsContract`'s postcondition without its clause on
`scratch`. -/
def decaps1024Post (pb : Nat) : Spec.MlKem1024.decapsSig.Post pb := fun dk ct key _scratch m m' r =>
  Outcome (fun iters => Spec.MlKem.decapsInternal Spec.MlKem.mlKem1024 iters (bytesAt m dk 3168)
      (bytesAt m ct 1568)) r (bytesAt m' key 32)

/-- `decaps1024Post`, and each byte of `scratch` unchanged or zero on return. -/
def decaps1024Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  Spec.MlKem1024.decapsSig.contract A
    (post := scrub4 49152 (decaps1024Post A.ptrBits)) (writeArgs := true) (stack := stack)
    (leak := some fun dk _ct _key _scratch m =>
      leakRho (Spec.MlKem.dkRho Spec.MlKem.mlKem1024 (bytesAt m dk 3168)))

/-- `Spec.MlKem1024.decapsContract` is `decaps1024Contract`. -/
theorem decaps1024_eq {M : ISA} (A : Abi M) (stack : Nat) :
    Spec.MlKem1024.decapsContract A stack = decaps1024Contract A stack :=
  rfl

/-! ## From the bytes `callWipe` zeroes

Each in the form `Verified.callWipe'` takes (`hwiped`), with all of
`scratch` zeroed. -/

theorem keyGen_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem.keyGenSig.words pb).length →
    Curry.apply (Spec.MlKem.keyGenSig.words pb) (keyGenPost pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) 32768 = Spec.Zeroize.zeros 32768 →
      Curry.apply (Spec.MlKem.keyGenSig.words pb) (scrub4 32768 (keyGenPost pb)) vs m m' x :=
  wiped4 32768 (keyGenPost pb)

theorem encapsH_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem.encapsHSig.words pb).length →
    Curry.apply (Spec.MlKem.encapsHSig.words pb) (encapsHPost pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) 32768 = Spec.Zeroize.zeros 32768 →
      Curry.apply (Spec.MlKem.encapsHSig.words pb) (scrub6 32768 (encapsHPost pb)) vs m m' x :=
  wiped6 32768 (encapsHPost pb)

theorem encaps_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem.encapsSig.words pb).length →
    Curry.apply (Spec.MlKem.encapsSig.words pb) (encapsPost pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) 32768 = Spec.Zeroize.zeros 32768 →
      Curry.apply (Spec.MlKem.encapsSig.words pb) (scrub5 32768 (encapsPost pb)) vs m m' x :=
  wiped5 32768 (encapsPost pb)

theorem decaps_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem.decapsSig.words pb).length →
    Curry.apply (Spec.MlKem.decapsSig.words pb) (decapsPost pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) 32768 = Spec.Zeroize.zeros 32768 →
      Curry.apply (Spec.MlKem.decapsSig.words pb) (scrub4 32768 (decapsPost pb)) vs m m' x :=
  wiped4 32768 (decapsPost pb)

theorem keyGen1024_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem1024.keyGenSig.words pb).length →
    Curry.apply (Spec.MlKem1024.keyGenSig.words pb) (keyGen1024Post pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) 49152 = Spec.Zeroize.zeros 49152 →
      Curry.apply (Spec.MlKem1024.keyGenSig.words pb) (scrub4 49152 (keyGen1024Post pb)) vs m m' x :=
  wiped4 49152 (keyGen1024Post pb)

theorem encapsH1024_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem1024.encapsHSig.words pb).length →
    Curry.apply (Spec.MlKem1024.encapsHSig.words pb) (encapsH1024Post pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 5 0) 49152 = Spec.Zeroize.zeros 49152 →
      Curry.apply (Spec.MlKem1024.encapsHSig.words pb) (scrub6 49152 (encapsH1024Post pb)) vs m m' x :=
  wiped6 49152 (encapsH1024Post pb)

theorem encaps1024_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem1024.encapsSig.words pb).length →
    Curry.apply (Spec.MlKem1024.encapsSig.words pb) (encaps1024Post pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 4 0) 49152 = Spec.Zeroize.zeros 49152 →
      Curry.apply (Spec.MlKem1024.encapsSig.words pb) (scrub5 49152 (encaps1024Post pb)) vs m m' x :=
  wiped5 49152 (encaps1024Post pb)

theorem decaps1024_wiped (pb : Nat) : ∀ vs m m' x, vs.length = (Spec.MlKem1024.decapsSig.words pb).length →
    Curry.apply (Spec.MlKem1024.decapsSig.words pb) (decaps1024Post pb) vs m m' x →
    Spec.Zeroize.bytesAt m' (vs.getD 3 0) 49152 = Spec.Zeroize.zeros 49152 →
      Curry.apply (Spec.MlKem1024.decapsSig.words pb) (scrub4 49152 (decaps1024Post pb)) vs m m' x :=
  wiped4 49152 (decaps1024Post pb)

end VG.Proof.MlKem.Scrubbed
