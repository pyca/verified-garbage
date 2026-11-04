module

public import VerifiedGarbage.Proof.MdHashTable.RISCV64
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha1
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha384
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_224
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.MdStream.RISCV64.Common
import VerifiedGarbage.Proof.Md5.RISCV64.Stream
import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.Sha1.RISCV64.Compress
import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common

/-!
# RSASSA-PSS on RISC-V: the hash functions as Merkle–Damgård hash functions

Untrusted: everything here is checked by Lean. What hashing a message of a
public length by its compression function needs of a hash function `H`
beyond its streaming functions (`MdL`, for the `HashOK` of those): the
`Md` instance of its family, with its initial hash value, which the
streaming `init` sets (`init`); its hash function, the first `hLen` bytes of
that instance's (`hash`); its length field, for a message shorter than
`2⁶¹` bytes, the 64-bit bit count, big-endian or not, after zeros (`len`);
its compression function, correct and constant time for `compK` with `cs`
bytes of working space; and its digest of a hash value
(`Impl/MdHashTable/RISCV64.lean`), what it writes (`OutOK`) and that the
taint analysis accepts it. One for each hash function (`md5M`, …).
-/

@[expose] public section

namespace VG.Proof.RsaPss.RISCV64

open VG VG.RISCV64 VG.Proof.MdStream
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.MdHashTable.RISCV64 (OutOK digestK)
open VG.Impl.MdHashTable.RISCV64 (digest outMd5 outSha1 outSha256 outSha512)

/-- The contract of a compression function: updates the hash value at `a0`
with the `a2` blocks at `a1`, with `cs` bytes of working space at `a3`,
8-byte aligned. -/
def compK {B N L : Nat} (H : Md B N L) (cs : Nat) : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, N⟩
    let blocks : Region := ⟨s.gpr .a1, B * (s.gpr .a2).toNat⟩
    let scratch : Region := ⟨s.gpr .a3, cs⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    (s.gpr .a3).toNat % 8 = 0
  post s s' :=
    H.stateAt s'.mem (s.gpr .a0) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .a0)) s.mem (s.gpr .a1) (s.gpr .a2).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.sp = s₂.sp

/-- What hashing a message of a public length with the compression function
needs of the hash function `H`, whose streaming functions are `hH`. -/
structure MdL (H : Hash) (hH : HashOK H) where
  L : Nat
  md : Md H.B H.N L
  iv : md.HV
  be : Bool
  hL : L = H.B / 8 ∧ 8 ≤ L
  hDN : H.D ≤ H.N
  init : ∀ m p, hH.SH.Repr m p [] → md.stateAt m p = iv
  hash : ∀ x, hH.SH.H.hash x = (md.hash iv x).take H.D
  len : ∀ n, n < 2 ^ 61 → md.lenBytes n = List.replicate (L - 8) 0 ++ bytes64 be (BitVec.ofNat 64 (8 * n))
  cs : Nat
  hcs : cs ≤ 144
  compN : String
  compC : Prog isa
  comp : ∀ s, (compK md cs).pre s → ∃ t s', Exec isa compC s t s' ∧ abiPreserved s s' ∧ (compK md cs).post s s'
  compCT : ConstantTime isa (compK md cs).pre (compK md cs).pub compC
  compNF : compC.noFrames = true
  out : List Instr
  outOk : OutOK md out
  outCT : ∃ hc, (taint.check (Taint.ofRegs [.a0, .a1]) (digest out) hc).isSome = true

/-! ## The compression functions -/

/-- A compression function correct and constant time for `compK H cs`. -/
def CompOk {B N L : Nat} (H : Md B N L) (cs : Nat) (c : Prog isa) : Prop :=
  (∀ s, (compK H cs).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (compK H cs).post s s') ∧
    ConstantTime isa (compK H cs).pre (compK H cs).pub c

/-- The compression function of a contract whose precondition `compK`'s
implies, and whose `post` and `pub` are `compK`'s. -/
theorem comp_of {B N L : Nat} {H : Md B N L} {cs : Nat} {c : Prog isa} {k : Contract isa}
    (hv : Verified RISCV64.target c k) (hp : ∀ s, (compK H cs).pre s → k.pre s)
    (hq : ∀ s s', k.post s s' → (compK H cs).post s s') (hpub : ∀ s₁ s₂, (compK H cs).pub s₁ s₂ → k.pub s₁ s₂) :
    CompOk H cs c :=
  ⟨fun s hs => let ⟨t, s', he, ha, h⟩ := hv.1 s (hp s hs); ⟨t, s', he, ha, hq s s' h⟩,
    fun _ _ _ _ _ _ h₁ h₂ hpub' e₁ e₂ => hv.2.1 _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (hpub _ _ hpub') e₁ e₂⟩

theorem md5C : CompOk Proof.Md5.md 80 Impl.Md5.RISCV64.compress :=
  comp_of Proof.Md5.RISCV64.Stream.compress80 (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h)

theorem sha1C : CompOk Proof.Sha1.md 80 Impl.Sha1.RISCV64.compress :=
  comp_of Proof.Sha1.RISCV64.compress_verified
    (fun _ ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩) (fun _ _ h => h) (fun _ _ h => h)

theorem sha256C : CompOk Proof.Sha256.md 80 Impl.Sha256.RISCV64.compress :=
  comp_of Proof.Sha256.RISCV64.compress_verified
    (fun _ ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩) (fun _ _ h => h) (fun _ _ h => h)

theorem sha512C : CompOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  comp_of Proof.Sha512.RISCV64.compress_verified
    (fun _ ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩) (fun _ _ h => h) (fun _ _ h => h)

/-! ## The length fields -/

theorem ext_ofNat {n i : Nat} (hn : n < 2 ^ 64) :
    (BitVec.ofNat 128 n).extractLsb' (8 * i) 8 = (BitVec.ofNat 64 n).extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show n < 2 ^ 128 by omega), Nat.mod_eq_of_lt hn]

theorem ext_zero {n i : Nat} (hn : n < 2 ^ 64) (hi : 8 ≤ i) :
    (BitVec.ofNat 128 n).extractLsb' (8 * i) 8 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 128 by omega),
    Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega)))]
  rfl

/-- The SHA-512 family's 128-bit length field of a message shorter than
`2⁶¹` bytes: eight zeros, then the 64-bit bit count. -/
theorem sha512_len (n : Nat) (hn : n < 2 ^ 61) :
    Proof.Sha512.md.lenBytes n = List.replicate 8 0 ++ bytes64 true (BitVec.ofNat 64 (8 * n)) := by
  have h : 8 * n < 2 ^ 64 := by omega
  show Proof.Sha512.lenField (BitVec.ofNat 128 (8 * n)) = _
  simp only [Proof.Sha512.lenField, bytes64, ite_true]
  rw [show List.range 16 = List.range (8 + 8) from rfl, List.range_add,
    List.reverse_append, List.map_append, List.map_reverse, List.map_map]
  congr 1
  · refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_range, List.getElem_replicate,
      Function.comp_apply]
    exact ext_zero h (by omega)
  · exact List.map_congr_left fun _ _ => ext_ofNat h

/-! ## The hash functions -/

open VG.Proof.Hmac.Stream.RISCV64 in
def md5M : MdL Md5.hash Md5.ok where
  L := 8
  md := Proof.Md5.md
  iv := Spec.Md5.H0
  be := false
  hL := by decide
  hDN := by decide
  init _ _ h := h.1
  hash x := (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm
  len _ _ := rfl
  cs := 80
  hcs := by decide
  compN := "vg_md5_compress"
  compC := Impl.Md5.RISCV64.compress
  comp := md5C.1
  compCT := md5C.2
  compNF := Proof.Md5.RISCV64.Stream.callee.noFrames
  out := outMd5
  outOk := MdHashTable.RISCV64.out_md5
  outCT := MdHashTable.RISCV64.ct_md5

open VG.Proof.Hmac.Stream.RISCV64 in
def sha1M : MdL Sha1.hash Sha1.ok where
  L := 8
  md := Proof.Sha1.md
  iv := Spec.Sha1.H0
  be := true
  hL := by decide
  hDN := by decide
  init _ _ h := h.1
  hash x := (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm
  len _ _ := rfl
  cs := 80
  hcs := by decide
  compN := "vg_sha1_compress"
  compC := Impl.Sha1.RISCV64.compress
  comp := sha1C.1
  compCT := sha1C.2
  compNF := Proof.Sha1.RISCV64.Stream.callee.noFrames
  out := outSha1
  outOk := MdHashTable.RISCV64.out_sha1
  outCT := MdHashTable.RISCV64.ct_sha1

open VG.Proof.Hmac.Stream.RISCV64 in
def sha256M : MdL Sha256Family.hash256 Sha256Family.ok256 where
  L := 8
  md := Proof.Sha256.md
  iv := Spec.Sha256.H0
  be := true
  hL := by decide
  hDN := by decide
  init _ _ h := h.1
  hash x := (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm
  len _ _ := rfl
  cs := 80
  hcs := by decide
  compN := "vg_sha256_compress"
  compC := Impl.Sha256.RISCV64.compress
  comp := sha256C.1
  compCT := sha256C.2
  compNF := Proof.Sha256.RISCV64.Stream.compress_noFrames
  out := outSha256
  outOk := MdHashTable.RISCV64.out_sha256
  outCT := MdHashTable.RISCV64.ct_sha256

open VG.Proof.Hmac.Stream.RISCV64 in
def sha224M : MdL Sha256Family.hash224 Sha256Family.ok224 where
  L := 8
  md := Proof.Sha256.md
  iv := Spec.Sha256.H0_224
  be := true
  hL := by decide
  hDN := by decide
  init _ _ h := h.1
  hash _ := rfl
  len _ _ := rfl
  cs := 80
  hcs := by decide
  compN := "vg_sha256_compress"
  compC := Impl.Sha256.RISCV64.compress
  comp := sha256C.1
  compCT := sha256C.2
  compNF := Proof.Sha256.RISCV64.Stream.compress_noFrames
  out := outSha256
  outOk := MdHashTable.RISCV64.out_sha256
  outCT := MdHashTable.RISCV64.ct_sha256

/-- The SHA-512 family's, from the initial hash value `iv`, for the streaming
functions `Sha512Family.hash iv D …`. -/
def sha512FamM (iv : Spec.Sha512.HashValue) (D : Nat) (initN finN : String) (finC : Prog isa)
    (hH : HashOK (Hmac.Stream.RISCV64.Sha512Family.hash iv D initN finN finC)) (hD : D ≤ 64)
    (init : ∀ m p, hH.SH.Repr m p [] → Spec.Sha512.stateAt m p = iv)
    (hash : ∀ x, hH.SH.H.hash x = (Proof.Sha512.md.hash iv x).take D) :
    MdL (Hmac.Stream.RISCV64.Sha512Family.hash iv D initN finN finC) hH where
  L := 16
  md := Proof.Sha512.md
  iv := iv
  be := true
  hL := ⟨by simp [Hmac.Stream.RISCV64.Sha512Family.hash, Hash.B], by decide⟩
  hDN := hD
  init := init
  hash := hash
  len := sha512_len
  cs := 144
  hcs := by decide
  compN := "vg_sha512_compress"
  compC := Impl.Sha512.RISCV64.compress
  comp := sha512C.1
  compCT := sha512C.2
  compNF := Proof.Sha512.RISCV64.Stream.compress_noFrames
  out := outSha512
  outOk := MdHashTable.RISCV64.out_sha512
  outCT := MdHashTable.RISCV64.ct_sha512

open VG.Proof.Hmac.Stream.RISCV64 in
def sha384M : MdL Sha384.hash Sha384.ok :=
  sha512FamM _ _ _ _ _ Sha384.ok (by decide) (fun _ _ h => h.1) fun _ => rfl
open VG.Proof.Hmac.Stream.RISCV64 in
def sha512M : MdL Sha512.hash Sha512.ok :=
  sha512FamM _ _ _ _ _ Sha512.ok (by decide) (fun _ _ h => h.1)
    fun _ => (List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))).symm
open VG.Proof.Hmac.Stream.RISCV64 in
def sha512_224M : MdL Sha512_224.hash Sha512_224.ok :=
  sha512FamM _ _ _ _ _ Sha512_224.ok (by decide) (fun _ _ h => h.1) fun _ => rfl
open VG.Proof.Hmac.Stream.RISCV64 in
def sha512_256M : MdL Sha512_256.hash Sha512_256.ok :=
  sha512FamM _ _ _ _ _ Sha512_256.ok (by decide) (fun _ _ h => h.1) fun _ => rfl

end VG.Proof.RsaPss.RISCV64
