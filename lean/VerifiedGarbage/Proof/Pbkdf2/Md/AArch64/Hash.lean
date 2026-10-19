module

public import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
public import VerifiedGarbage.Spec.Mgf1
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Pbkdf2.AArch64.IterateCT

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the hash function

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/Hash.lean`), `HashOK H` is what the
proofs know of the hash function whose code `H` describes: it is a
Merkle–Damgård hash function `md` (`Md`) whose length field and digest code do
what they should (`Shape`), with a verified compression function (`CompOk`);
its streaming functions are verified against the contracts HMAC's and
PBKDF2's proofs call them with (`stream`, `Calls.lean`); its specification is `md` from the initial
hash value `iv`, with the digest the first `D` bytes of `md`'s; and its sizes
fit.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64 VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.AArch64 (Shape CompOk Sizes)
open VG.Proof.Hmac.Generic.Common (bytesAt_reloc)
open Spec.Hmac (StreamingHash)

/-- What the proofs need of a Merkle–Damgård hash function's code. -/
structure HashOK (H : Hash) where
  /-- The hash function, as the proofs of `iterate` see it. -/
  md : Md H.P.B H.P.N H.P.L
  shape : Shape md
  /-- The compression function is verified. -/
  comp : CompOk md H.P.so H.compC
  /-- The hash value is determined by its bytes, wherever they are. -/
  reloc : md.Reloc
  /-- The length field is right for every message shorter than 2⁶⁴ bytes. -/
  lenOk : ∀ n, n < 2 ^ 64 → md.lenOk n
  /-- The streaming functions, verified. -/
  stream : Calls.StreamOK H.stream
  /-- Checked no-clobber facts for the MD wrapper call graph. -/
  initKeepsV : H.initC.allInstrs keepsV = true
  updKeepsV : H.updC.allInstrs keepsV = true
  finKeepsV : H.finC.allInstrs keepsV = true
  /-- The specification is `md` from `iv`, with a `D`-byte digest. -/
  iv : md.HV
  repr : ∀ mem p m, stream.SH.Repr mem p m ↔ md.Repr iv mem p m
  hash : ∀ m, stream.SH.H.hash m = (md.hash iv m).take H.D
  /-- The sizes. -/
  sizes : Sizes H.P H.D H.W
  L : 0 < H.P.L ∧ H.P.L ≤ 16
  W : H.W ≤ 256
  /-- HMAC's outer block has room for `padW`'s 16-byte stores: from the
  first multiple of 16 after the digest, 16 bytes before its end. -/
  hPad : 16 * (H.D / 16 + 1) + 16 ≤ H.P.B
  /-- The length field, whose zeros `padW` stores, is 8 or 16 bytes. -/
  L816 : H.P.L = 8 ∨ H.P.L = 16

namespace HashOK

variable {H : Hash} (hH : HashOK H)

/-- The specification. -/
abbrev SH : StreamingHash := hH.stream.SH

theorem hB : hH.SH.H.blockSize = H.P.B := hH.stream.hB
theorem hS : hH.SH.stateBytes = H.P.N + H.P.B := hH.stream.hS
theorem hD : hH.SH.digestBytes = H.D := hH.stream.hD

include hH in
theorem B_le : H.P.B ≤ 128 := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem B_pos : 0 < H.P.B := by rcases hH.sizes.B with h | h <;> omega

include hH in
theorem N_le : H.P.N ≤ 64 := hH.sizes.dims.N.2

/-! Bounds the proofs use many times, proved once by `Nat` lemmas rather than
by `omega` at each use. -/

include hH in
theorem B4 : H.P.B % 4 = 0 := by rcases hH.sizes.B with h | h <;> rw [h]
include hH in
theorem N_lt4096 : H.P.N < 4096 := Nat.lt_of_le_of_lt hH.N_le (by decide)
include hH in
theorem N_le64 : H.P.N ≤ 2 ^ 64 := Nat.le_of_lt hH.sizes.N_lt64
include hH in
theorem NB_le64 : H.P.N + H.P.B ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.add_le_add hH.N_le hH.B_le) (by decide)
include hH in
theorem D4' : 4 * (H.D / 4) = H.D := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hH.sizes.D4)

/-- What the proof of `iterate` (`Proof/Pbkdf2/AArch64/Iterate.lean`) needs
of the hash function. -/
theorem iterOk : Pbkdf2.AArch64.HashOk H.P H.D H.W hH.SH hH.md hH.iv where
  sizes := hH.sizes
  shape := hH.shape
  reloc := hH.reloc
  lenOk := hH.lenOk _ (by have := hH.B_le; have := hH.sizes.DN; have := hH.N_le; omega)
  link := ⟨hH.hB, hH.hS, hH.hD, fun m p x h => (hH.repr m p x).1 h, hH.hash, hH.sizes.DN,
    by have := hH.sizes.pad; have := hH.sizes.NL; omega⟩

/-- `copyW` writes no SIMD register. -/
theorem copyW_keepsV (wide : Bool) (src : Reg) (so : Nat) (dst : Reg) (d n : Nat) :
    (Hash.copyW wide src so dst d n).all keepsV = true := by
  have h2 : ∀ (c : Prop) [Decidable c] (a b : List Instr), a.all keepsV = true → b.all keepsV = true →
      (if c then a else b).all keepsV = true := fun c _ a b ha hb => by
    split
    · exact ha
    · exact hb
  unfold Hash.copyW
  refine h2 _ _ _ ?_ ?_
  · simp only [List.all_append, List.all_flatMap, Hash.cp128]
    refine Bool.and_eq_true_iff.mpr ⟨List.all_eq_true.mpr fun k _ => ?_,
      Bool.and_eq_true_iff.mpr ⟨h2 _ _ _ rfl rfl, h2 _ _ _ rfl rfl⟩⟩
    exact Bool.and_eq_true_iff.mpr ⟨h2 _ _ _ rfl rfl, h2 _ _ _ rfl rfl⟩
  · simp [Hash.copy32, Impl.Pbkdf2.AArch64.cp32, keepsV, vdstOf]

include hH in
/-- The pieces of HMAC's `finalize` after the inner digest write no SIMD
register. -/
theorem finMid_keepsV : H.finMid.all keepsV = true := by
  have hl := hH.shape.lenKeepsV
  have hw : H.padW.all keepsV = true := by
    simp only [Hash.padW, List.all_append, List.all_cons, hl, Bool.and_true]
    refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
    · split
      · rfl
      · simp [Impl.Pbkdf2.AArch64.padFrom, keepsV, vdstOf]
    · simp [keepsV, vdstOf]
    · split <;> rfl
  have hsel : H.padSel.all keepsV = true := by
    unfold Hash.padSel
    split
    · exact hw
    · exact Pbkdf2.AArch64.padLen_keepsV hH.shape
  simp only [Hash.finMid, List.all_append, copyW_keepsV, hsel, Bool.and_true, Bool.true_and]
  simp [Impl.MdStream.AArch64.mov, keepsV, vdstOf]

include hH in
theorem cmp_keepsV : (instrs (Impl.MdStream.AArch64.compressAt H.compN H.compC)).all keepsV = true := by
  have hc := hH.comp.keepsV
  rw [Code.allInstrs_eq] at hc
  simp only [Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, instrs, List.all_append, hc,
    Bool.and_true]
  rfl

include hH in
theorem finOut_keepsV : H.finOut.all keepsV = true := by
  have ho := hH.shape.outKeepsV
  by_cases hDN : H.D < H.P.N <;>
  simp only [Hash.finOut, hDN, ↓reduceIte, List.all_append, List.all_cons, ho, copyW_keepsV, Bool.and_true,
    Bool.true_and] <;>
  simp [Impl.Pbkdf2.Md.AArch64.Stream.restore,
    Impl.Pbkdf2.Md.AArch64.Stream.saved, Impl.MdStream.AArch64.mov, keepsV, vdstOf]

include hH in
/-- HMAC's `init` writes no SIMD register but in the functions it calls,
which write none either. -/
theorem hmacInit_keepsV : H.hmacInit.allInstrs keepsV = true := by
  have hi := hH.initKeepsV
  have hc := hH.comp.keepsV
  have h1 : H.ipadFill.all keepsV = true := by
    rw [List.all_eq_true]; intro i hi
    simp only [Hash.ipadFill, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | ⟨k, -, rfl⟩) | rfl <;> rfl
  have h2 : H.opadFill.all keepsV = true := by
    rw [List.all_eq_true]; intro i hi
    simp only [Hash.opadFill, Hash.opadW, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_range,
      List.not_mem_nil, or_false] at hi
    rcases hi with ((rfl | rfl) | ⟨k, -, rfl | rfl | rfl⟩) | rfl <;> rfl
  rw [Code.allInstrs_eq] at hi hc ⊢
  simp only [Hash.hmacInit, Hash.initKeys, Hash.keyLoop, Impl.Pbkdf2.Md.AArch64.Stream.callInit,
    Impl.MdStream.AArch64.compressAt, Impl.MdStream.AArch64.compressWith, Hash.stream, instrs,
    List.all_append, hi, hc, h1, h2, Bool.and_true, Bool.true_and]
  simp [Hash.initPrologue, Hash.initOuter, Hash.stream, Impl.Pbkdf2.Md.AArch64.Stream.save,
    Impl.Pbkdf2.Md.AArch64.Stream.saved, Impl.Pbkdf2.Md.AArch64.Stream.restore, Impl.MdStream.AArch64.mov,
    keepsV, vdstOf]

include hH in
/-- HMAC's `finalize` writes no SIMD register but in the functions it calls,
which write none either. -/
theorem hmacFin_keepsV : H.hmacFin.allInstrs keepsV = true := by
  have hf := hH.finKeepsV
  rw [Code.allInstrs_eq] at hf ⊢
  simp only [Hash.hmacFin, Impl.Pbkdf2.Md.AArch64.Stream.callFin, instrs, List.all_append,
    hH.finMid_keepsV, hH.cmp_keepsV, hH.finOut_keepsV, Bool.and_true]
  simp [Hash.stream, hf, Impl.Pbkdf2.Md.AArch64.Stream.finPrologue, Impl.Pbkdf2.Md.AArch64.Stream.save,
    Impl.Pbkdf2.Md.AArch64.Stream.saved, Impl.MdStream.AArch64.mov, Impl.MdStream.AArch64.mov, keepsV,
    vdstOf]

include hH in
/-- The MD PBKDF2 wrapper uses only scalar instructions around its certified callees. -/
theorem pbkdf2_keepsV : H.pbkdf2.allInstrs keepsV = true := by
  have hi := hH.initKeepsV
  have hu := hH.updKeepsV
  have hf := hH.finKeepsV
  have ht : H.iterate.allInstrs keepsV = true :=
    Pbkdf2.AArch64.iterate_keepsV hH.shape hH.comp.keepsV
  have hinit : H.hmacInit.allInstrs keepsV = true := hH.hmacInit_keepsV
  have hfin : H.hmacFin.allInstrs keepsV = true := hH.hmacFin_keepsV
  have hk : H.key.allInstrs keepsV = true := by
    simp [Hash.key, Hash.keyShr, Hash.keySub, Hash.short, Hash.hashKey, Hash.hkInit,
      Hash.hkUpd, Hash.hkFin, Hash.hkKey, Impl.MdStream.AArch64.mov,
      Code.allInstrs, keepsV, vdstOf, hi, hu, hf]
  have hs : H.setup.allInstrs keepsV = true := by
    rw [Code.allInstrs_eq] at hinit hu ⊢
    simp [Hash.setup, Hash.initArgs, Hash.saltArgs, Hash.copy32, Impl.Pbkdf2.AArch64.cp32,
      Impl.MdStream.AArch64.mov, instrs, keepsV, vdstOf, hinit, hu]
  have hb : H.block.allInstrs keepsV = true := by
    rw [Code.allInstrs_eq] at hu hfin ht ⊢
    simp [Hash.block, Hash.intArgs, Hash.finArgs, Hash.iterArgs, Hash.outLen,
      Hash.outLoop, Hash.advance, Hash.copy32, Impl.Pbkdf2.AArch64.cp32,
      Impl.MdStream.AArch64.mov, instrs, keepsV, vdstOf, hu, hfin, ht]
  simp [Hash.pbkdf2, Hash.entry, Hash.entryPre, Hash.entryPost, Hash.loopRegs,
    Hash.exit, Impl.Pbkdf2.Md.AArch64.Stream.save, Impl.Pbkdf2.Md.AArch64.Stream.saved,
    Impl.Pbkdf2.Md.AArch64.Stream.restore, Impl.MdStream.AArch64.mov,
    Code.allInstrs, keepsV, vdstOf, hk, hs, hb]

end HashOK

/-- The hash functions RSA's padding takes (`Spec.Mgf1.Hash`). -/
def mdHashes : List Spec.Mgf1.Hash :=
  [Spec.Mgf1.md5, Spec.Mgf1.sha1, Spec.Mgf1.sha224, Spec.Mgf1.sha256, Spec.Mgf1.sha384, Spec.Mgf1.sha512,
    Spec.Mgf1.sha512_224, Spec.Mgf1.sha512_256]

/-- The hash function `H` as RSA's padding takes it (`Spec.Mgf1.Hash`). -/
structure MgfLink (H : Hash) (hH : HashOK H) where
  G : Spec.Mgf1.Hash
  mem : G ∈ mdHashes
  hash : ∀ x, G.hash x = hH.SH.H.hash x
  len : G.len = H.D

end VG.Proof.Pbkdf2.Md.AArch64
