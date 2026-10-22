module

public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Ocb.Spec
public import VerifiedGarbage.Proof.Modes.Counter
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Counter mode with GCM's `inc₃₂`, for any block cipher and target

The modes' `ctr32` keeps its running counter block as the number `V` that
its 16 big-endian bytes are (as CTR does, `Ctr.lean`), and steps it by
`inc₃₂` (NIST SP 800-38D §6.2): `j` steps from `V` give `ctr32Val V j`, the
high 96 bits of `V` and its low 32 bits plus `j`, modulo 2³²
(`toNat_repeat_inc32`). On 64-bit targets the running counter is the two
halves `hiOf`, `loOf` (`Counter.lean`): the high half is unchanged
(`hiOf_ctr32Val`), and the low half is its high 32 bits and its low 32 bits
plus `j` (`loOf_ctr32Val`).

`ctr32_of_dinv`: when a mode's data loop has replaced each block `j` with its
XOR with the encryption of the counter block `ctr32Val V j` (`ctr32Out`),
the blocks are `Spec.Gcm.ctr32`'s, for the cipher on blocks as lists of
bytes made a cipher on GCM's blocks (`onBlocks`); `ctr32_next`: the counter
block it leaves is `inc₃₂ⁿ(CB₁)`. Nothing here depends on a cipher or a
target.
-/

@[expose] public section

namespace VG.Proof.Modes

open VG
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ctr (ofNat toNat)

/-- The counter block `j` steps of `inc₃₂` from the counter block `V`: the
high 96 bits of `V`, and its low 32 bits plus `j`, modulo 2³². -/
def ctr32Val (V j : Nat) : Nat := V / 2 ^ 32 * 2 ^ 32 + (V + j) % 2 ^ 32

theorem ctr32Val_zero (V : Nat) : ctr32Val V 0 = V := by
  unfold ctr32Val; omega

theorem ctr32Val_add (V a b : Nat) : ctr32Val (ctr32Val V a) b = ctr32Val V (a + b) := by
  unfold ctr32Val; omega

theorem ctr32Val_lt {V : Nat} (hV : V < 2 ^ 128) (j : Nat) : ctr32Val V j < 2 ^ 128 := by
  unfold ctr32Val; omega

/-- The high half is unchanged. -/
theorem hiOf_ctr32Val (V j : Nat) : hiOf (ctr32Val V j) = hiOf V := by
  simp only [hiOf, ctr32Val]
  congr 1
  omega

/-- The low half: its high 32 bits, and its low 32 bits plus `j` modulo
2³² (as a 32-bit addition computes them, zero-extended). -/
theorem loOf_ctr32Val (V j : Nat) :
    loOf (ctr32Val V j) =
      ((loOf V >>> 32) <<< 32) + (((loOf V).setWidth 32 + BitVec.ofNat 32 j).setWidth 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [loOf, ctr32Val, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- `inc₃₂` on numbers. -/
theorem toNat_repeat_inc32 (x : Spec.Gcm.Block) : ∀ j,
    (Nat.repeat Spec.Gcm.inc32 j x).toNat = ctr32Val x.toNat j
  | 0 => (ctr32Val_zero _).symm
  | j + 1 => by
    rw [Nat.repeat, AesCcm.toNat_inc32, toNat_repeat_inc32 x j]
    unfold ctr32Val; omega

/-- A block as 16 big-endian bytes. -/
theorem toBytes_eq_ofNat (x : Spec.Gcm.Block) : Spec.Gcm.toBytes x = ofNat x.toNat 16 := by
  have h := AesSiv.toBytes_be128 x.toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

/-- 16 bytes as a block, and its number. -/
theorem toNat_ofBytes {t : List Byte} (ht : t.length = 16) : (Spec.Gcm.ofBytes t).toNat = toNat t :=
  AesCcm.toNat_ofBytes ht

/-- A cipher on blocks as lists of bytes, on GCM's blocks. -/
def onBlocks (cipher : Spec.Cbc.Cipher) (x : Spec.Gcm.Block) : Spec.Gcm.Block :=
  Spec.Gcm.ofBytes (cipher (Spec.Gcm.toBytes x))

/-- The output block `j` of counter mode with `inc₃₂`, from the data at `D`
in `m₀` and the counter block `V`: data block `j` XORed with the encryption
of the counter block `ctr32Val V j`. -/
def ctr32Out (cipher : Spec.Cbc.Cipher) (m₀ : Mem) (D : Addr) (V j : Nat) : List Byte :=
  Spec.Cbc.xor (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16) (cipher (ofNat (ctr32Val V j) 16))

theorem ctr32Out_getD {cipher : Spec.Cbc.Cipher} (hc : ∀ b, (cipher b).length = 16) (m₀ : Mem) (D : Addr)
    (V j : Nat) {u : Nat} (hu : u < 16) :
    (ctr32Out cipher m₀ D V j).getD u 0 =
      m₀ (D + BitVec.ofNat 64 (16 * j + u)) ^^^ (cipher (ofNat (ctr32Val V j) 16)).getD u 0 := by
  have h1 : u < (bytesAt m₀ (D + BitVec.ofNat 64 (16 * j)) 16).length := by simp [bytesAt, hu]
  have h2 : u < (cipher (ofNat (ctr32Val V j) 16)).length := by rw [hc]; exact hu
  have h3 : u < (ctr32Out cipher m₀ D V j).length := by
    simp only [ctr32Out, Spec.Cbc.xor, List.length_zipWith]; omega
  rw [← List.getElem_eq_getD (h := h3) 0, ← List.getElem_eq_getD (h := h2) 0]
  simp only [ctr32Out, Spec.Cbc.xor, List.getElem_zipWith]
  simp [bytesAt, VG.Offset.add_add]

/-- The bytes at `D + 16 j` after the data loop: `ctr32Out`'s block `j`. -/
theorem bytes_of_dinv {cipher : Spec.Cbc.Cipher} (hc : ∀ b, (cipher b).length = 16) {m₀ m : Mem} {D : Addr}
    {n V : Nat} (h : DInv 16 m₀ m D n n (ctr32Out cipher m₀ D V)) {j : Nat} (hj : j < n) :
    bytesAt m (D + BitVec.ofNat 64 (16 * j)) 16 = ctr32Out cipher m₀ D V j := by
  apply List.ext_getElem (by simp [bytesAt, ctr32Out, Spec.Cbc.xor, hc])
  intro u h1 h2
  have hu : u < 16 := by simpa [bytesAt] using h1
  rw [show (ctr32Out cipher m₀ D V j)[u] = (ctr32Out cipher m₀ D V j).getD u 0 from
    List.getElem_eq_getD 0, ctr32Out_getD hc _ _ _ _ hu]
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [VG.Offset.add_add, h _ (by omega), ite_eq_left (by omega), show (16 * j + u) / 16 = j by omega,
    show (16 * j + u) % 16 = u by omega, ctr32Out_getD hc _ _ _ _ hu]

/-- The data after the data loop, from the counter block `t`, as
`Spec.Gcm.ctr32`'s. -/
theorem ctr32_of_dinv {cipher : Spec.Cbc.Cipher} (hc : ∀ b, (cipher b).length = 16) {m₀ m : Mem} {D : Addr}
    {n : Nat} {t : List Byte} (ht : t.length = 16) (h : DInv 16 m₀ m D n n (ctr32Out cipher m₀ D (toNat t))) :
    Spec.Gcm.blocksAt m D n =
      Spec.Gcm.ctr32 (onBlocks cipher) (Spec.Gcm.ofBytes t) (Spec.Gcm.blocksAt m₀ D n) := by
  have hl : (Spec.Gcm.blocksAt m₀ D n).length = n := by simp [Spec.Gcm.blocksAt]
  rw [Spec.Gcm.ctr32, hl, Spec.Gcm.keystream, Spec.Gcm.blocksAt, Spec.Gcm.blocksAt, List.zipWith_map,
    List.zipWith_self]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  have hctr : Spec.Gcm.toBytes (Nat.repeat Spec.Gcm.inc32 j (Spec.Gcm.ofBytes t)) =
      ofNat (ctr32Val (toNat t) j) 16 := by
    rw [toBytes_eq_ofNat, toNat_repeat_inc32, toNat_ofBytes ht]
  rw [onBlocks, hctr, Spec.Gcm.blockAt, Spec.Gcm.blockAt, bytes_of_dinv hc h hj, ctr32Out]
  exact Ocb.ofBytes_xor (Cmac.bytesAt_length _ _ _) (hc _)

/-- GCM's blocks are CTR's, as blocks. -/
theorem gcmBlocks_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Gcm.blocksAt m p n = (Spec.Cbc.blocksAt m p n).map Spec.Gcm.ofBytes := by
  simp only [Spec.Gcm.blocksAt, Spec.Cbc.blocksAt, List.map_map]
  rfl

/-- The counter block a mode leaves after `n` blocks, from the counter block
at `P` in `m`: `inc₃₂ⁿ` of it. -/
theorem ctr32_next {m m' : Mem} {P : Addr} {n : Nat}
    (h : bytesAt m' P 16 = ofNat (ctr32Val (toNat (bytesAt m P 16)) n) 16) :
    Spec.Gcm.blockAt m' P = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m P) := by
  have ht : (bytesAt m P 16).length = 16 := Cmac.bytesAt_length _ _ _
  apply Ocb.toBytes_inj
  rw [Ocb.toBytes_eq, ← Cmac.bytesAt_blockAt, h, toBytes_eq_ofNat, toNat_repeat_inc32, Spec.Gcm.blockAt, toNat_ofBytes ht]

end VG.Proof.Modes
