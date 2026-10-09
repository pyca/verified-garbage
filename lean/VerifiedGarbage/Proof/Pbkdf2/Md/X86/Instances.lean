import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Lit
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.IterateCT
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFinCT
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacInitCT
import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# HMAC's `init` and `finalize` and PBKDF2's `iterate` on x86 (32-bit): the instances

The generic proofs (`IterateCT.lean`, `HmacInitCT.lean`, `HmacFinCT.lean`) at
each hash function of `Hashes.lean`, with the taint checks of their blocks,
which the kernel evaluates for each hash function, moved to the shared
contracts of `Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`
(`sig_implies`), which the artifacts are emitted with: here, the states
that satisfy the shared contracts and the checks of the hash functions with a
backend for each implementation of their compression function; the
instances themselves are in a file per hash function (`Md5.lean`,
`Sha384.lean`, `Sha512.lean`, `Sha512_224.lean`, `Sha512_256.lean`), which
build in parallel.
-/

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.X86
open VG.Proof.Pbkdf2.Md.X86
open VG.Proof.Pbkdf2.Stream.X86 (initW initG finW finG iterW iterG countF)

/-- Memory holding the arguments `0x1000, 0x1400, 0, 0x1800, 0x2000` of
`iterate` at `0x6004`. -/
def iterMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x6011 then 0x18 else
  if a = 0x6015 then 0x20 else 0

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 sc` bytes of scratch space, with the arguments
writable. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := iterMem
  rd := [⟨0x1000, 2 * S⟩, ⟨0x1400, D⟩]
  wr := [⟨0x1800, D⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 20⟩]

theorem iterSat_args (S D sc : Nat) :
    arg (iterSat S D sc) 0 = 0x1000 ∧ arg (iterSat S D sc) 1 = 0x1400 ∧ arg (iterSat S D sc) 2 = 0 ∧
      arg (iterSat S D sc) 3 = 0x1800 ∧ arg (iterSat S D sc) 4 = 0x2000 ∧ argAddr (iterSat S D sc) 0 = 0x6004 ∧
      (iterSat S D sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (iterSat S D sc) i = arg (iterSat 0 0 0) i := fun _ => rfl
  have e' : argAddr (iterSat S D sc) 0 = argAddr (iterSat 0 0 0) 0 := rfl
  rw [e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-- Memory holding the arguments `0x1000, 0x1400, 0, 0, 0x1800, 0x2000` of
`finalize` at `0x6004`. -/
def finMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x6015 then 0x18 else
  if a = 0x6019 then 0x20 else 0

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space, with the arguments
writable. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := finMem
  rd := [⟨0x1400, S⟩]
  wr := [⟨0x1000, S⟩, ⟨0x1800, D⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 24⟩]

theorem finSat_args (S D sc : Nat) :
    arg (finSat S D sc) 0 = 0x1000 ∧ arg (finSat S D sc) 1 = 0x1400 ∧ arg (finSat S D sc) 2 = 0 ∧
      arg (finSat S D sc) 3 = 0 ∧ arg (finSat S D sc) 4 = 0x1800 ∧ arg (finSat S D sc) 5 = 0x2000 ∧
      argAddr (finSat S D sc) 0 = 0x6004 ∧ (finSat S D sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (finSat S D sc) i = arg (finSat 0 0 0) i := fun _ => rfl
  have e' : argAddr (finSat S D sc) 0 = argAddr (finSat 0 0 0) 0 := rfl
  rw [e, e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

/-- Memory holding the arguments `0x1000, 0x1400, 0x1800, 0, 0x2000` of
`init` at `0x6004`. -/
def initMem : Mem := fun a =>
  if a = 0x6005 then 0x10 else if a = 0x6009 then 0x14 else if a = 0x600D then 0x18 else
  if a = 0x6015 then 0x20 else 0

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and an empty key), with the arguments writable. -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .esp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := initMem
  rd := [⟨0x1800, 0⟩]
  wr := [⟨0x1000, S⟩, ⟨0x1400, S⟩, ⟨0x2000, 8 * sc⟩, ⟨0x6004, 20⟩]

theorem initSat_args (S sc : Nat) :
    arg (initSat S sc) 0 = 0x1000 ∧ arg (initSat S sc) 1 = 0x1400 ∧ arg (initSat S sc) 2 = 0x1800 ∧
      arg (initSat S sc) 3 = 0 ∧ arg (initSat S sc) 4 = 0x2000 ∧ argAddr (initSat S sc) 0 = 0x6004 ∧
      (initSat S sc).gpr .esp = 0x6000 := by
  have e : ∀ i, arg (initSat S sc) i = arg (initSat 0 0) i := fun _ => rfl
  have e' : argAddr (initSat S sc) 0 = argAddr (initSat 0 0) 0 := rfl
  rw [e, e, e, e, e, e']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> decide

end VG.Proof.Pbkdf2.Md.X86.Instances

/-! ## Hash functions with a backend for each implementation of their compression function

Their code differs between backends only in the functions it calls, so its
taint checks are evaluated once, on the code without them (`shapeOf`), for
every backend (`Sha256.lean`, `Sha1.lean`). -/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.Impl.Pbkdf2.Md.X86 (Hash)

/-- `H` without the names and code of the functions it calls: the code
between the calls depends on nothing else. -/
def shapeOf (H : Hash) : Hash :=
  ⟨⟨H.st.B, H.st.S, H.st.D, H.st.F, H.st.W, "", .block [], "", .block [], "", .block []⟩, H.N, H.L, H.be, H.so,
    "", .block [], H.out⟩

end VG.Proof.Pbkdf2.Md.X86

namespace VG.Proof.Pbkdf2.Md.X86.Instances

open VG.Proof.Pbkdf2.Md.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)

theorem iterChecks_of_shape {H : Hash} (h : Iterate.Checks (shapeOf H)) : Iterate.Checks H :=
  ⟨h.pro, h.load, h.mid, h.tail, h.restore⟩

theorem initChecks_of_shape {H : Hash} (h : HmacInit.Checks (shapeOf H)) : HmacInit.Checks H :=
  ⟨h.pro, h.blocks, h.toOuter, h.restore⟩

theorem finChecks_of_shape {H : Hash} (h : HmacFin.Checks (shapeOf H)) : HmacFin.Checks H :=
  ⟨h.pro, h.fin1, h.mid, h.out⟩

end VG.Proof.Pbkdf2.Md.X86.Instances
