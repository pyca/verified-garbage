import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Sha256.Scratch
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Bswap

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Hmac`. -/
section

/-!
# PBKDF2-HMAC-SHA-256: one step as two compressions

For a 64-byte key `K₀`, both hashes of HMAC-SHA-256 of a 32-byte `U` are of
96-byte messages: a block (`K₀ ⊕ ipad` or `K₀ ⊕ opad`) whose compression is
the state `vg_hmac_sha256_init` leaves, then 32 bytes, which the padding
completes to a second block (`block96`). So a step of PBKDF2's iteration is
two compressions, whatever the target.
-/

namespace VG.Proof.Pbkdf2

open VG.Spec.Sha256 (HashValue Block compress compressList parseBlock wordBytes H0)
open VG.Spec.Hmac (xorPad ipad opad hmacBlockKey sha256)
open VG.Proof.Sha256.Stream (lenBytes hash_one compressList_append)

/-- The padding of a 96-byte message after its first 64 + 32 bytes: `0x80`,
zeros, and the length in bits (768), big-endian. -/
def pad96 : List Byte := [0x80] ++ List.replicate 23 0 ++ [0, 0, 0, 0, 0, 0, 3, 0]

/-- The last block of a 96-byte message whose last 32 bytes are `x`. -/
def block96 (x : List Byte) : Block := parseBlock fun t => (x ++ pad96).getD t 0

/-- A hash value as 32 big-endian bytes. -/
def digest (H : HashValue) : List Byte := H.toList.flatMap wordBytes

theorem digest_length (H : HashValue) : (digest H).length = 32 := by
  simp [digest, wordBytes, List.length_flatMap, List.map_const']

theorem lenBytes96 {m : List Byte} (h : m.length = 96) : lenBytes m = [0, 0, 0, 0, 0, 0, 3, 0] := by
  simp only [lenBytes, h]; decide

/-- SHA-256 of a 96-byte message. -/
theorem hash96 {p x : List Byte} (hp : p.length = 64) (hx : x.length = 32) :
    Spec.Sha256.hash (p ++ x) = digest (compress (compressList H0 p 1) (block96 x)) := by
  have hl : (p ++ x).length = 96 := by simp [hp, hx]
  rw [hash_one (by omega), hl]
  simp only [digest, block96, pad96]
  have e₁ : compressList H0 (p ++ x) (96 / 64) = compressList H0 p 1 := by
    rw [show 96 / 64 = 1 by rfl, compressList_append (by omega)]
  have e₂ : Sha256.Stream.rest (p ++ x) = x := by
    simp only [Sha256.Stream.rest, hl]
    rw [show 64 * (96 / 64) = p.length by omega, List.drop_left]
  rw [e₁, e₂, lenBytes96 hl, show 55 - 96 % 64 = 23 by rfl]
  simp only [List.append_assoc]

/-- One step of the iteration: HMAC-SHA-256 of a 32-byte message, from the
hash values of the key's two blocks. -/
theorem hmac_step {k0 u : List Byte} (hk : k0.length = 64) (hu : u.length = 32) :
    hmacBlockKey sha256 k0 u =
      digest (compress (compressList H0 (xorPad k0 opad) 1)
        (block96 (digest (compress (compressList H0 (xorPad k0 ipad) 1) (block96 u))))) := by
  have hi : (xorPad k0 ipad).length = 64 := by simp [xorPad, hk]
  have ho : (xorPad k0 opad).length = 64 := by simp [xorPad, hk]
  simp only [hmacBlockKey, sha256]
  rw [hash96 hi hu, hash96 ho (digest_length _)]

end VG.Proof.Pbkdf2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.Memory`. -/
section

/-!
# PBKDF2-HMAC-SHA-256's iteration: memory lemmas

Facts about bytes of memory, regions, the exclusive-or of words and the
iteration itself that the proofs of every target share, so that none imports
another target's proof.
-/

namespace VG.Proof.Pbkdf2.Memory

open VG.Proof.Sha256.Stream (writeBytes writeBytes_append write_eq_writeBytes)
open VG.Spec.Sha256 (bytesAt stateAt blockAt HashValue)
open VG.Proof.Hmac.Common (bytesAt_add read_congr₂ stateAt_eq_of_bytes writeBytes_at bytesAt_getD'
  bytesAt_length bytesAt_writeBytes_self)

/-! ## Helpers

Copies of lemmas of the x86-64 SHA-256 proofs, which this module does not
import; the lemmas about bytes are the target-independent HMAC ones
(`Proof/Hmac/Common.lean`). -/

private theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

private theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt ho]
    exact Nat.mod_le _ _
  omega

/-! ## Memory -/

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem contains_base {a : Addr} {n len : Nat} (h : n ≤ len) : (⟨a, len⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem off_contains {a x : Addr} {o n len : Nat} (h : (x - (a + BitVec.ofNat 64 o)).toNat < n)
    (hl : o + n ≤ len) (ho : o < 2 ^ 64) : (⟨a, len⟩ : Region).Contains x 1 :=
  sub_offset (off := o) (len := n) hl ho x (by simp only [Region.Contains]; omega)

/-- Bytes from `p + a` are not among the first `a` from `p`. -/
theorem sep_after {p x : Addr} {a n : Nat} (h₁ : (x - (p + BitVec.ofNat 64 a)).toNat < n) (h₂ : (x - p).toNat < a)
    (ha : a + n < 2 ^ 64) : False := by
  rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega, BitVec.toNat_add,
    toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h₂
  omega

/-- A block of 32 bytes followed by the padding. -/
theorem blockAt_eq {m : Mem} {p : Addr} (h : bytesAt m (p + 32) 32 = pad96) :
    blockAt m p = block96 (bytesAt m p 32) := by
  simp only [Spec.Sha256.blockAt, block96]
  apply Proof.Sha256.Stream.parseBlock_congr
  intro k hk
  have e := bytesAt_add m p 32 32
  rw [show BitVec.ofNat 64 32 = (32 : Addr) from rfl, h] at e
  rw [← e, bytesAt_getD' _ _ (by omega : k < 32 + 32)]

theorem writeW_xor (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 64 ^^^ m'.readW b 64) =
      writeBytes m d (Spec.Pbkdf2.xorBytes (bytesAt m' b 8) (bytesAt m' a 8)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (64 : Nat) / 8 = 8 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [Spec.Pbkdf2.xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [Spec.Pbkdf2.xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁, Mem.extractLsb'_read _ _ h₁, BitVec.xor_comm]

theorem xorBytes_length (a b : List Byte) (h : a.length = b.length) :
    (Spec.Pbkdf2.xorBytes a b).length = a.length := by
  simp [Spec.Pbkdf2.xorBytes, h]

/-- A copied hash value. -/
theorem stateAt_copy (m m' : Mem) (q p : Addr) :
    stateAt (writeBytes m q (bytesAt m' p 32)) q = stateAt m' p := by
  apply stateAt_eq_of_bytes
  intro i hi
  rw [writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi]

theorem digest_self (m : Mem) (q : Addr) (H : HashValue) :
    bytesAt (writeBytes m q (Pbkdf2.digest H)) q 32 = Pbkdf2.digest H := by
  have := bytesAt_writeBytes_self m q (Pbkdf2.digest H) (by rw [Pbkdf2.digest_length]; omega)
  rwa [Pbkdf2.digest_length] at this

theorem writeW_bytes (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (xs : List Byte)
    (h : ((List.range (w / 8)).map fun j => (v.setWidth (8 * (w / 8))).extractLsb' (8 * j) 8) = xs) :
    m.writeW a v = writeBytes m a xs := by
  rw [Mem.writeW, write_eq_writeBytes, h]

theorem writeBytes_append' (m : Mem) {q q' : Addr} (xs ys : List Byte) (hq : q' = q + BitVec.ofNat 64 xs.length)
    (h : xs.length + ys.length < 2 ^ 64) : writeBytes (writeBytes m q xs) q' ys = writeBytes m q (xs ++ ys) := by
  subst hq; exact writeBytes_append m q xs ys h

/-! ## Regions -/

theorem add_ofNat (a : Addr) (o j : Nat) : a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The result -/

theorem iterate_congr {f g : List Byte → List Byte} (hfg : ∀ u, u.length = 32 → f u = g u)
    (hg : ∀ u, (g u).length = 32) :
    ∀ n u t, u.length = 32 → Spec.Pbkdf2.iterate f n u t = Spec.Pbkdf2.iterate g n u t := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro u t hu
    simp only [Spec.Pbkdf2.iterate]
    rw [hfg u hu]
    exact ih _ _ (hg u)

end VG.Proof.Pbkdf2.Memory

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.MdKeys`. -/
section

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.MdStep`. -/
section

/-!
# PBKDF2-HMAC over a Merkle–Damgård hash function: one step as two compressions

For a key `K₀` of one block, both hashes of HMAC of a `D`-byte `U` are of `B +
D`-byte messages: a block (`K₀ ⊕ ipad` or `K₀ ⊕ opad`) whose compression is
the hash value of the streaming state `init` leaves, then `D` bytes, which the
padding (`pad`) completes to a second block (`block`). So a step of PBKDF2's
iteration is two compressions (`step`), for any hash function the streaming
proofs describe (`Md`), whatever the target. `Link` is what ties a hash
function of the specification (`StreamingHash`) to its `Md`. HMAC's outer
hash, of a key's outer block and an inner digest, is likewise one compression
(`Link.hash_block`), which HMAC's `finalize` computes.
-/

namespace VG.Proof.MdStream.Md

open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)

variable {B N L : Nat} (H : Md B N L)

/-- The padding of a `B + D`-byte message after its last `D` bytes: `0x80`,
zeros, and the length field. -/
def tailPad (D : Nat) : List Byte := [0x80] ++ List.replicate (B - L - 1 - D) 0 ++ H.lenBytes (B + D)

theorem tailPad_length {D : Nat} (h : D + L < B) : (H.tailPad D).length = B - D := by
  simp only [VG.Proof.MdStream.Md.tailPad, List.length_append, List.length_singleton, List.length_replicate, H.lenBytes_length]
  omega

/-- The start of the padding. -/
theorem tailPad_take {D n : Nat} (h₁ : 0 < n) (h₂ : D + n + L ≤ B) :
    (H.tailPad D).take n = [0x80] ++ List.replicate (n - 1) 0 := by
  have hr : (List.replicate (B - L - 1 - D) (0 : Byte)).take (n - 1) = List.replicate (n - 1) 0 := by
    rw [List.take_replicate, Nat.min_eq_left (by omega)]
  rw [VG.Proof.MdStream.Md.tailPad, List.take_append_of_le_length (by simp; omega), List.take_append, List.length_singleton, hr,
    List.take_of_length_le (by simp; omega)]

/-- The last block of a `B + D`-byte message whose last `D` bytes are `x`. -/
def tailBlock (D : Nat) (x : List Byte) : H.Blk := H.parse fun t => (x ++ H.tailPad D).getD t 0

/-- The block in memory at `p`, of `D` bytes of message and the padding after
them. -/
theorem blockAt_eq {D : Nat} {m : Mem} {p : Addr} (hD : D ≤ B)
    (h : Spec.Sha256.bytesAt m (p + BitVec.ofNat 64 D) (B - D) = H.tailPad D) :
    H.blockAt m p = H.tailBlock D (Spec.Sha256.bytesAt m p D) := by
  simp only [blockAt, VG.Proof.MdStream.Md.tailBlock]
  refine H.parse_congr fun k hk => ?_
  have e := Hmac.Common.bytesAt_add m p D (B - D)
  rw [h, show D + (B - D) = B by omega] at e
  rw [← e, Hmac.Common.bytesAt_getD' _ _ hk]

/-- A `B + D`-byte message is hashed with one more compression. -/
theorem hash_block (iv : H.HV) {p x : List Byte} {D : Nat} (hp : p.length = B) (hx : x.length = D)
    (h : D + L < B) :
    H.hash iv (p ++ x) = H.digest (H.compress (H.compressList iv p 1) (H.tailBlock D x)) := by
  have hB : 0 < B := by omega
  have hl : (p ++ x).length = B + D := by simp [hp, hx]
  have hmod : (p ++ x).length % B = D := by
    rw [hl, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (p ++ x).length / B = 1 := by
    rw [hl, show B + D = D + B * 1 by omega, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (by omega)]
  rw [hash_one H hB (by rw [hmod]; omega), hdiv, compressList_append H (by rw [hp]; omega), hmod, hl]
  have hr : rest B (p ++ x) = x := by
    simp only [rest, hdiv, Nat.mul_one]
    rw [← hp, List.drop_left]
  rw [hr]
  simp only [VG.Proof.MdStream.Md.tailBlock, VG.Proof.MdStream.Md.tailPad, List.append_assoc]

/-- A step of the iteration, from the hash values `hi` and `ho` of the key's
inner and outer blocks: two compressions, each of the digest (of `D` bytes)
of the previous one padded. -/
def step (D : Nat) (hi ho : H.HV) (u : List Byte) : List Byte :=
  (H.digest (H.compress ho (H.tailBlock D ((H.digest (H.compress hi (H.tailBlock D u))).take D)))).take D

theorem step_length {D : Nat} (h : D ≤ N) (hi ho : H.HV) (u : List Byte) : (H.step D hi ho u).length = D := by
  simp only [VG.Proof.MdStream.Md.step, List.length_take, H.digest_length]; omega

/-- A hash function of the specification (`S`, with a `D`-byte digest) is the
`Md` hash function `H` from the initial hash value `iv`, with its digest
truncated to `D` bytes, and its streaming state is `H`'s: the hash value
(`N` bytes) followed by a block (`B` bytes). -/
structure Link (S : StreamingHash) (iv : H.HV) (D : Nat) : Prop where
  hB : S.H.blockSize = B
  hS : S.stateBytes = N + B
  hD : S.digestBytes = D
  repr : ∀ m p x, S.Repr m p x → H.Repr iv m p x
  hash : ∀ x, S.H.hash x = (H.hash iv x).take D
  DN : D ≤ N
  DL : D + L < B

variable {H}

/-- The hash of a block `p` and `D` bytes `x` (HMAC's outer hash, of the
key's outer block and the inner digest) is one compression, of the hash
value of `p` with the block of `x` and the padding. -/
theorem Link.hash_block {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {p x : List Byte}
    (hp : p.length = B) (hx : x.length = D) :
    S.H.hash (p ++ x) = (H.digest (H.compress (H.compressList iv p 1) (H.tailBlock D x))).take D := by
  rw [hl.hash, Md.hash_block H iv hp hx hl.DL]

/-- One step of the iteration is HMAC, for a key whose blocks' hash values
are `hi` and `ho`. -/
theorem hmac_step {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {k0 u : List Byte}
    (hk : k0.length = B) (hu : u.length = D) :
    hmacBlockKey S.H k0 u =
      H.step D (H.compressList iv (xorPad k0 ipad) 1) (H.compressList iv (xorPad k0 opad) 1) u := by
  have li : (xorPad k0 ipad).length = B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = B := by simp [xorPad, hk]
  simp only [hmacBlockKey, VG.Proof.MdStream.Md.step]
  rw [hl.hash_block li hu, hl.hash_block lo (x := List.take D _)
    (by simp only [List.length_take, H.digest_length]; exact Nat.min_eq_left hl.DN)]

/-- The hash value stored at an address depends only on the bytes there, not
on the address. -/
def Reloc : Prop := ∀ (m m' : Mem) (p q : Addr),
  (∀ i < N, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) → H.stateAt m' q = H.stateAt m p

/-- The hash value of a streaming state that represents one block. -/
theorem stateAt_of_repr {iv : H.HV} {m : Mem} {p : Addr} {x : List Byte} (hB : 0 < B) (hx : x.length = B)
    (h : H.Repr iv m p x) : H.stateAt m p = H.compressList iv x 1 := by
  rw [h.1, hx, Nat.div_self hB]

/-- Steps that agree on `D`-byte inputs give the same iteration. -/
theorem iterate_congr {D : Nat} {f g : List Byte → List Byte} (hfg : ∀ u, u.length = D → f u = g u)
    (hg : ∀ u, (g u).length = D) :
    ∀ n u t, u.length = D → Spec.Pbkdf2.iterate f n u t = Spec.Pbkdf2.iterate g n u t := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro u t hu
    simp only [Spec.Pbkdf2.iterate]
    rw [hfg u hu]
    exact ih _ _ (hg u)

/-- PBKDF2's iteration with HMAC as its pseudorandom function is the
iteration of `step`, from the hash values of a key's streaming states. -/
theorem iterate_hmac {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {k0 : List Byte}
    (hk : k0.length = S.H.blockSize) {mem : Mem} {p q : Addr} (hi : S.Repr mem p (xorPad k0 ipad))
    (ho : S.Repr mem q (xorPad k0 opad)) (n : Nat) {u t : List Byte} (hu : u.length = D) :
    Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) n u t =
      Spec.Pbkdf2.iterate (H.step D (H.stateAt mem p) (H.stateAt mem q)) n u t := by
  have hB : 0 < B := by have := hl.DL; omega
  rw [hl.hB] at hk
  have li : (xorPad k0 ipad).length = B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = B := by simp [xorPad, hk]
  rw [VG.Proof.MdStream.Md.stateAt_of_repr hB li (hl.repr _ _ _ hi), VG.Proof.MdStream.Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)]
  exact VG.Proof.MdStream.Md.iterate_congr (fun u hu => VG.Proof.MdStream.Md.hmac_step hl hk hu) (fun u => VG.Proof.MdStream.Md.step_length H hl.DN _ _ u) n u t hu

/-- HMAC's outer hash, for a key whose outer block's hash value is `ho`, of
the inner digest `x`: one compression of the block `x ‖ pad`. -/
theorem hmac_outer {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {k0 text : List Byte}
    (hk : k0.length = S.H.blockSize) {mem : Mem} {p : Addr} (ho : S.Repr mem p (xorPad k0 opad)) :
    hmacBlockKey S.H k0 text =
      (H.digest (H.compress (H.stateAt mem p) (H.tailBlock D (S.H.hash (xorPad k0 ipad ++ text))))).take D := by
  have hB : 0 < B := by have := hl.DL; omega
  rw [hl.hB] at hk
  have lo : (xorPad k0 opad).length = B := by simp [xorPad, hk]
  have hx : (S.H.hash (xorPad k0 ipad ++ text)).length = D := by
    rw [hl.hash, List.length_take, Md.hash, H.digest_length]; exact Nat.min_eq_left hl.DN
  rw [hmacBlockKey, hl.hash, VG.Proof.MdStream.Md.hash_block H iv lo hx hl.DL, VG.Proof.MdStream.Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)]

end VG.Proof.MdStream.Md

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.MdHmac`. -/
section

/-!
# HMAC over a Merkle–Damgård hash function: the outer hash as one compression

HMAC's outer hash, of a key's outer block (`K₀ ⊕ opad`, one block) and an
inner digest of `D` bytes, is one compression, of the hash value of the outer
block with the block of the digest and the padding of a `B + D`-byte message
(`Link.hmac_outer`), for any hash function the streaming proofs describe
(`Md`), whatever the target. A block in memory made of `D` bytes followed by
that padding is the padded block of those bytes (`blockAt_tailPad`).
-/

namespace VG.Proof.MdStream.Md

open VG.Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)
open VG.Spec.Sha256 (bytesAt)

variable {B N L : Nat} {H : Md B N L}

/-- The block in memory at `p`, of `D` bytes of message and the padding after
them. -/
theorem blockAt_tailPad {D : Nat} {m : Mem} {p : Addr} (hD : D ≤ B)
    (h : bytesAt m (p + BitVec.ofNat 64 D) (B - D) = H.tailPad D) :
    H.blockAt m p = H.tailBlock D (bytesAt m p D) := by
  simp only [blockAt, VG.Proof.MdStream.Md.tailBlock]
  refine H.parse_congr fun k hk => ?_
  have e := Hmac.Common.bytesAt_add m p D (B - D)
  rw [h, show D + (B - D) = B by omega] at e
  rw [← e, Hmac.Common.bytesAt_getD' _ _ hk]

/-- The hash of a block `p` and `D` bytes `x` is one compression, of the hash
value of `p` with the block of `x` and the padding. -/
theorem Link.hash_outer {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {p x : List Byte}
    (hp : p.length = B) (hx : x.length = D) :
    S.H.hash (p ++ x) = (H.digest (H.compress (H.compressList iv p 1) (H.tailBlock D x))).take D := by
  rw [hl.hash, Md.hash_block H iv hp hx hl.DL]

/-- A digest has `D` bytes. -/
theorem Link.hash_length {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) (x : List Byte) :
    (S.H.hash x).length = D := by
  rw [hl.hash, List.length_take, Md.hash, H.digest_length]; exact Nat.min_eq_left hl.DN

/-- HMAC's outer hash, for a key of one block, is one compression of the hash
value of its outer block, with the inner digest padded. -/
theorem Link.hmac_outer {S : StreamingHash} {iv : H.HV} {D : Nat} (hl : H.Link S iv D) {k0 : List Byte}
    (hk : k0.length = B) (text : List Byte) :
    hmacBlockKey S.H k0 text = (H.digest (H.compress (H.compressList iv (xorPad k0 opad) 1)
      (H.tailBlock D (S.H.hash (xorPad k0 ipad ++ text))))).take D :=
  hl.hash_outer (by simp [xorPad, hk]) (hl.hash_length _)

end VG.Proof.MdStream.Md

end

/- Proofs formerly in `VerifiedGarbage.Proof.Pbkdf2.MdKeys`. -/
section

/-!
# HMAC's `init` over a Merkle–Damgård hash function: the padded keys

HMAC's `init` (`Impl/Pbkdf2/Md/`), for a key of at most a block, writes
`K₀ ⊕ ipad` into the inner state's buffer and `K₀ ⊕ opad` into the outer
one's, then compresses each state's buffer into the initial hash value `init`
set. What it writes, and what the states then represent, are facts about
memory alone, shared by every target:

* words of a byte repeated (`writeW_rep`), and words read from memory XORed
  with a byte repeated (`writeW_xorRep`), are the bytes they hold;
* the inner buffer is first `ipad` in every byte, written a word at a time
  (`fill_mem`), then the key's bytes are written over the first ones: all at
  once (`bytes_over`), or XORed in one at a time, after `j` of them it holds
  `ipadBlk … j` (`ipadBlk_succ`), and after all of them `K₀ ⊕ ipad`
  (`ipadBlk_eq`); the key of at most a block is padded with zeros
  (`blockKey_short`, `xorPad_short`);
* the outer buffer is the inner one XORed with `ipad ⊕ opad = 0x6a` in every
  byte, a word at a time (`xorOpad_mem`), which is `K₀ ⊕ opad`
  (`xorOpad_ipad`);
* a state whose hash value is the initial one, compressed with the block in
  its buffer, represents that block (`Md.repr_block`), for any hash function
  the streaming proofs describe (`Md`).
-/

namespace VG.Proof.Pbkdf2.MdKeys

open VG.WriteBytes (writeBytes writeBytes_append writeW8_apply write_eq_writeBytes)
open VG.Proof.Hmac.Common (bytesAt_add bytesAt_length bytesAt_writeBytes_sep bytesAt_writeBytes_self
  extractLsb'_read)
open VG.Proof.Hmac.Generic.Common (K0 K0_length K0_lt K0_ge)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-! ## Words of bytes -/

/-- A word whose four bytes are `b`. -/
theorem writeW_rep (m : Mem) (a : Addr) (b : Byte) :
    m.writeW a (b ++ b ++ b ++ b) = VG.WriteBytes.writeBytes m a (List.replicate 4 b) :=
  Memory.writeW_bytes _ _ _ _ (by
    show [_, _, _, _] = [b, b, b, b]
    simp (disch := decide) only [BitVec.setWidth_eq, Nat.mul_zero, Nat.reduceMul, VG.extractLsb'_append_byte_lo,
      VG.extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self])

/-- A word read from memory, XORed with `c` repeated, is its bytes XORed with `c`. -/
theorem writeW_xorRep (m m' : Mem) (d a : Addr) (c : Byte) :
    m.writeW d (m'.readW a 32 ^^^ (c ++ c ++ c ++ c)) = VG.WriteBytes.writeBytes m d ((bytesAt m' a 4).map (· ^^^ c)) := by
  refine Memory.writeW_bytes _ _ _ _ ?_
  simp only [bytesAt, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  simp only [Function.comp, Mem.readW, BitVec.setWidth_eq]
  rw [BitVec.extractLsb'_xor, extractLsb'_read _ _ hj]
  congr 1
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp (disch := decide) only [Nat.mul_zero, Nat.reduceMul, VG.extractLsb'_append_byte_lo,
      VG.extractLsb'_append_byte_hi, Nat.reduceSub, BitVec.extractLsb'_eq_self]

/-- `0x6a` in every byte. -/
theorem c6a : (0x6a6a6a6a : BitVec 32) = (0x6a : Byte) ++ (0x6a : Byte) ++ (0x6a : Byte) ++ (0x6a : Byte) := by
  decide

/-- A byte, widened to `w` bits and XORed with `v`, then narrowed back: the
byte XORed with the low byte of `v`. -/
theorem xor_byte {w : Nat} (b : Byte) (v : BitVec w) (hw : 8 ≤ w := by decide) :
    ((b.setWidth w) ^^^ v).setWidth 8 = b ^^^ v.setWidth 8 := by
  rw [BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ hw, BitVec.setWidth_eq]

/-- A byte written into bytes written before. -/
theorem writeBytes_set (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < xs.length)
    (hl : xs.length < 2 ^ 64) (b : Byte) :
    (VG.WriteBytes.writeBytes m q xs).writeW (q + BitVec.ofNat 64 i) b = VG.WriteBytes.writeBytes m q (xs.set i b) := by
  funext a
  rw [VG.WriteBytes.writeW8_apply]
  simp only [VG.WriteBytes.writeBytes, List.length_set]
  by_cases ha : a = q + BitVec.ofNat 64 i
  · subst ha
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hi, List.getD_eq_getElem?_getD]
  · have hne : (a - q).toNat ≠ i := by
      intro h'
      apply ha
      have : a - q = BitVec.ofNat 64 i :=
        BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      rw [← BitVec.sub_add_cancel a q, this, BitVec.add_comm]
    simp only [ha, ↓reduceIte]
    split
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
    · rfl

/-- Bytes all `b`, with the first ones overwritten. -/
theorem bytes_over {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} {b : Byte} (hl : xs.length ≤ n) (hn : n < 2 ^ 64)
    (hm : bytesAt m q n = List.replicate n b) :
    bytesAt (VG.WriteBytes.writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) b := by
  have hs : Mem.Sep (q + BitVec.ofNat 64 xs.length) (n - xs.length) q xs.length := by
    have := Offset.sep q (d := xs.length) (n := n - xs.length) (e := 0) (k := xs.length) (.inr (by omega))
      (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  have e := bytesAt_add (VG.WriteBytes.writeBytes m q xs) q xs.length (n - xs.length)
  have e' := bytesAt_add m q xs.length (n - xs.length)
  rw [show xs.length + (n - xs.length) = n by omega] at e e'
  rw [e, bytesAt_writeBytes_self _ _ _ (by omega), bytesAt_writeBytes_sep _ _ hs (by omega)]
  rw [hm] at e'
  rw [show bytesAt m (q + BitVec.ofNat 64 xs.length) (n - xs.length) = (List.replicate n b).drop xs.length by
    rw [e', List.drop_left' (bytesAt_length _ _ _)], List.drop_replicate]

/-! ## The inner buffer -/

/-- One more word of `ipad`, after `4 n` bytes of it. -/
theorem fill_mem (m : Mem) (q : Addr) (n : Nat) (h : 4 * n + 4 < 2 ^ 64) :
    (VG.WriteBytes.writeBytes m q (List.replicate (4 * n) ipad)).writeW (q + BitVec.ofNat 64 (4 * n)) (0x36363636 : BitVec 32) =
      VG.WriteBytes.writeBytes m q (List.replicate (4 * n + 4) ipad) := by
  have e : ∀ m' : Mem, m'.writeW (q + BitVec.ofNat 64 (4 * n)) (0x36363636 : BitVec 32) =
      VG.WriteBytes.writeBytes m' (q + BitVec.ofNat 64 (4 * n)) [ipad, ipad, ipad, ipad] := fun m' => by
    rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes]; rfl
  have a := VG.WriteBytes.writeBytes_append m q (List.replicate (4 * n) ipad) [ipad, ipad, ipad, ipad] (by simp; omega)
  rw [List.length_replicate] at a
  rw [e, a, show [ipad, ipad, ipad, ipad] = List.replicate 4 ipad from rfl, List.replicate_append_replicate]

/-- The inner buffer after the first `j` bytes of the key at `K` (in memory
`m`): those bytes, then zeros, XORed with `ipad`. -/
def ipadBlk (m : Mem) (K : Addr) (B j : Nat) : List Byte :=
  (List.range B).map fun i => (if i < j then m (K + BitVec.ofNat 64 i) else 0) ^^^ ipad

theorem ipadBlk_length (m : Mem) (K : Addr) (B j : Nat) : (VG.Proof.Pbkdf2.MdKeys.ipadBlk m K B j).length = B := by
  simp [VG.Proof.Pbkdf2.MdKeys.ipadBlk]

/-- Before the key: `ipad` in every byte. -/
theorem ipadBlk_zero (m : Mem) (K : Addr) (B : Nat) : VG.Proof.Pbkdf2.MdKeys.ipadBlk m K B 0 = List.replicate B ipad := by
  apply List.ext_getElem (by simp [VG.Proof.Pbkdf2.MdKeys.ipadBlk])
  intro i h₁ h₂
  simp [VG.Proof.Pbkdf2.MdKeys.ipadBlk]

/-- One more byte of the key. -/
theorem ipadBlk_succ (m : Mem) (K : Addr) {B j : Nat} :
    (VG.Proof.Pbkdf2.MdKeys.ipadBlk m K B j).set j (m (K + BitVec.ofNat 64 j) ^^^ ipad) = VG.Proof.Pbkdf2.MdKeys.ipadBlk m K B (j + 1) := by
  apply List.ext_getElem (by simp [VG.Proof.Pbkdf2.MdKeys.ipadBlk])
  intro i h₁ h₂
  simp only [List.getElem_set, VG.Proof.Pbkdf2.MdKeys.ipadBlk, List.getElem_map, List.getElem_range]
  by_cases hij : j = i
  · subst hij; simp
  · by_cases hi : i < j
    · simp only [hij, hi, show i < j + 1 by omega, ↓reduceIte]
    · simp only [hij, hi, show ¬ i < j + 1 by omega, ↓reduceIte]

/-- After the whole key: `K₀ ⊕ ipad`. -/
theorem ipadBlk_eq (m : Mem) (K : Addr) {kl B : Nat} (h : kl ≤ B) :
    VG.Proof.Pbkdf2.MdKeys.ipadBlk m K B kl = xorPad (K0 m K kl B) ipad := by
  apply List.ext_getElem (by simp [VG.Proof.Pbkdf2.MdKeys.ipadBlk, xorPad, K0_length _ _ h])
  intro i h₁ h₂
  simp only [VG.Proof.Pbkdf2.MdKeys.ipadBlk, xorPad, List.getElem_map, List.getElem_range]
  by_cases hi : i < kl
  · simp only [hi, ↓reduceIte, K0_lt hi]
  · simp only [hi, ↓reduceIte, K0_ge (Nat.le_of_not_lt hi)]

/-- A key of at most a block, padded with zeros. -/
theorem blockKey_short (H : Spec.Hmac.HashFunction) {key : List Byte} (h : key.length ≤ H.blockSize) :
    blockKey H key = key ++ List.replicate (H.blockSize - key.length) 0 := by
  simp only [blockKey, show ¬ (H.blockSize < key.length) by omega, ↓reduceIte]

/-- The bytes of `K₀ ⊕ ipad`, for a key of `kl ≤ B` bytes: the key's
bytes XORed with `ipad`, then `ipad`. -/
theorem xorPad_short (key : List Byte) (B : Nat) :
    xorPad (key ++ List.replicate (B - key.length) 0) ipad =
      key.map (· ^^^ ipad) ++ List.replicate (B - key.length) ipad := by
  simp only [xorPad, List.map_append, List.map_replicate]
  rfl

/-! ## The outer buffer -/

/-- One more word of the outer buffer, after `4 n` bytes, from the inner
buffer at `A` to the outer one at `Q`. -/
theorem xorOpad_mem (m : Mem) (A Q : Addr) (n : Nat) (hsep : Mem.Sep A (4 * n + 4) Q (4 * n + 4))
    (hlt : 4 * n + 4 < 2 ^ 64) :
    (VG.WriteBytes.writeBytes m Q ((bytesAt m A (4 * n)).map (· ^^^ 0x6a))).writeW (Q + BitVec.ofNat 64 (4 * n))
      ((VG.WriteBytes.writeBytes m Q ((bytesAt m A (4 * n)).map (· ^^^ 0x6a))).readW (A + BitVec.ofNat 64 (4 * n)) 32 ^^^
        0x6a6a6a6a) =
      VG.WriteBytes.writeBytes m Q ((bytesAt m A (4 * n + 4)).map (· ^^^ 0x6a)) := by
  have hl : ((bytesAt m A (4 * n)).map (· ^^^ (0x6a : Byte))).length = 4 * n := by simp [bytesAt]
  rw [VG.Proof.Pbkdf2.MdKeys.c6a, VG.Proof.Pbkdf2.MdKeys.writeW_xorRep, bytesAt_writeBytes_sep]
  · rw [bytesAt_add, List.map_append]
    have := VG.WriteBytes.writeBytes_append m Q ((bytesAt m A (4 * n)).map (· ^^^ (0x6a : Byte)))
      ((bytesAt m (A + BitVec.ofNat 64 (4 * n)) 4).map (· ^^^ 0x6a)) (by simp [bytesAt]; omega)
    rw [hl] at this
    exact this
  · intro x hx hy
    rw [hl] at hy
    apply hsep x _ (by omega)
    rw [show x - A = (x - (A + BitVec.ofNat 64 (4 * n))) + BitVec.ofNat 64 (4 * n) by
        rw [← BitVec.sub_sub, BitVec.sub_add_cancel],
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * n) (by omega)]
    have := Nat.mod_le ((x - (A + BitVec.ofNat 64 (4 * n))).toNat + 4 * n) (2 ^ 64)
    omega
  · omega

/-- `K₀ ⊕ ipad` XORed with `ipad ⊕ opad = 0x6a` is `K₀ ⊕ opad`. -/
theorem xorOpad_ipad (k : List Byte) : (xorPad k ipad).map (· ^^^ 0x6a) = xorPad k opad := by
  simp only [xorPad, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp, BitVec.xor_assoc]
  rfl

end VG.Proof.Pbkdf2.MdKeys

namespace VG.Proof.MdStream.Md

open VG.Proof.Hmac.Common (bytesAt_getD')
open Spec.Sha256 (bytesAt)

variable {B N L : Nat} {H : Md B N L}

/-- The streaming state at `p`, whose hash value is `iv` compressed with the
block in its buffer when that held `x`, represents `x`. -/
theorem repr_block {iv : H.HV} {m m' : Mem} {p : Addr} {x : List Byte} (hB : 0 < B) (hx : x.length = B)
    (hb : bytesAt m (p + BitVec.ofNat 64 N) B = x)
    (hs : H.stateAt m' p = H.compress iv (H.blockAt m (p + BitVec.ofNat 64 N))) : H.Repr iv m' p x := by
  refine ⟨?_, ?_⟩
  · rw [hs, hx, Nat.div_self hB, compressList_one]
    refine congrArg (H.compress iv) (H.parse_congr fun k hk => ?_)
    rw [← hb, bytesAt_getD' _ _ hk]
  · rw [hx, Nat.mod_self, Nat.div_self hB, Nat.mul_one, ← hx, List.drop_length]
    rfl

end VG.Proof.MdStream.Md

end

end
