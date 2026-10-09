import VerifiedGarbage.Proof.RsaOaep.AArch64.EncVerified
import VerifiedGarbage.Proof.RsaOaep.AArch64.DecVerified
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callees
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant

/-!
# RSAES-OAEP on AArch64: the instances emitted

Which pairs of `MdHash` variants encryption and decryption are emitted for,
and their names and CPU features, as on x86-64 (`Proof/RsaOaep/X86_64/Sp.lean`);
that the hash function of a variant is a valid one for MGF1 (`mgf_valid`);
and states meeting both contracts, for the registration files.
-/

namespace VG.Proof.RsaOaep.AArch64

open VG VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK MgfLink MdHash mdHashes)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- MGF1's hash function, as a hash function of `MdHash` takes it, is valid. -/
theorem mgf_valid {H : Hash} {hH : HashOK H} (lk : MgfLink H hH) : Proof.Mgf1.Valid lk.G := by
  have hD := hH.sizes.D0
  refine ⟨by rw [lk.len]; exact hD, fun x => ?_⟩
  rw [lk.hash, hH.hash, List.length_take, MdStream.Md.hash, hH.md.digest_length, lk.len]
  have := hH.sizes.DN
  omega

namespace Inst

/-- Whether `vg_rsa_oaep_<H>_mgf1_<G>_*` is emitted for `H`'s variant `v` and
`G`'s variant `v2`: for `G = H`, with the same variant for both (`v2 = v`);
and for MGF1 with SHA-1 and `H` another hash function, for every pair. MD5
is not used. These are the pairs x86-64 emits. -/
def emitted (v v2 : MdHash) : Bool :=
  v.mgf.G.rust != "md5" &&
    if v.mgf.G.rust == v2.mgf.G.rust then v.suffix == v2.suffix else v2.mgf.G.rust == "sha1"

/-- The tags and suffixes of an instance's name (`Emit.qualifiedName`): `H`'s
variant tagged with `H`, then, if `G` is another hash function, `G`'s tagged
with `mgf1`. -/
def parts (v v2 : MdHash) : List (String × String) :=
  (v.mgf.G.rust, v.suffix) ::
    if v.mgf.G.rust == v2.mgf.G.rust then [] else [("mgf1", v2.suffix)]

/-- The CPU features of both variants, each once. -/
def features (v v2 : MdHash) : List String := v.features ++ v2.features.filter (!v.features.contains ·)

end Inst

/-! ## States meeting the contracts -/

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

/-- A state meeting encryption's contract for `H`: a 512-bit modulus, a
one-byte `e`, an empty label and message, `H`'s seed, a working space of
2048 words, and the stack arguments at `0x10000`. -/
def encSatState (H : Spec.Mgf1.Hash) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1 | .x6 => 0x4000
    | _ => 0
  sp := 0x10000
  mem a := if a = 0x10001 then 0x41 else if a = 0x10011 then 0x42 else if a = 0x1001A then 0x02
    else if a = 0x10021 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 0⟩, ⟨0x4100, 0⟩, ⟨0x4200, H.len⟩, ⟨0x10000, 40⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 16384⟩]

theorem enc_sat {H : Spec.Mgf1.Hash} (G : Spec.Mgf1.Hash) (hH : H ∈ mdHashes) :
    ∃ s, (Spec.RsaOaep.encryptContract H G AArch64.abi (Enc.encStack RsaPkcs1Enc.AArch64.pubImpl)).pre s := by
  simp only [mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hH
  rcases hH with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
      Enc.encStack, Enc.encP, RsaPkcs1Enc.AArch64.pubImpl, stackArgs_five, List.append_eq, Spec.Rsa.lenValid,
      Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.md5
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
      Enc.encStack, Enc.encP, RsaPkcs1Enc.AArch64.pubImpl, stackArgs_five, List.append_eq, Spec.Rsa.lenValid,
      Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha1
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
      Enc.encStack, Enc.encP, RsaPkcs1Enc.AArch64.pubImpl, stackArgs_five, List.append_eq, Spec.Rsa.lenValid,
      Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha224
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
      Enc.encStack, Enc.encP, RsaPkcs1Enc.AArch64.pubImpl, stackArgs_five, List.append_eq, Spec.Rsa.lenValid,
      Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha256
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
      Enc.encStack, Enc.encP, RsaPkcs1Enc.AArch64.pubImpl, stackArgs_five, List.append_eq, Spec.Rsa.lenValid,
      Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha384
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
      Enc.encStack, Enc.encP, RsaPkcs1Enc.AArch64.pubImpl, stackArgs_five, List.append_eq, Spec.Rsa.lenValid,
      Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha512
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
      Enc.encStack, Enc.encP, RsaPkcs1Enc.AArch64.pubImpl, stackArgs_five, List.append_eq, Spec.Rsa.lenValid,
      Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha512_224
  · sig_implies_sat [Spec.RsaOaep.encryptContract, Spec.RsaOaep.encryptSig, AArch64.abi, AArch64.argRegs,
      Enc.encStack, Enc.encP, RsaPkcs1Enc.AArch64.pubImpl, stackArgs_five, List.append_eq, Spec.Rsa.lenValid,
      Spec.RsaPss.scratchWords, Spec.Rsa.scratchWords] [encSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using encSatState Spec.Mgf1.sha512_256

/-- A state meeting decryption's contract: a 512-bit modulus, one-byte `e`,
primes, exponents and `qInv`, an empty label, a working space of 2048 words,
and the stack arguments at `0x10000`. -/
def decSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x1800 | .x3 => 0x2000 | .x4 => 64 | .x5 => 0x3000 | .x6 => 1
    | .x7 => 0x4200 | _ => 0
  sp := 0x10000
  mem a := if a = 0x10000 then 1 else if a = 0x10009 then 0x43 else if a = 0x10010 then 1
    else if a = 0x10019 then 0x44 else if a = 0x10020 then 1 else if a = 0x10029 then 0x45
    else if a = 0x10030 then 1 else if a = 0x10039 then 0x46 else if a = 0x10040 then 1
    else if a = 0x10049 then 0x47 else if a = 0x10059 then 0x41 else if a = 0x10060 then 64
    else if a = 0x1006A then 0x02 else if a = 0x10071 then 0x08 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x4600, 1⟩,
    ⟨0x4700, 0⟩, ⟨0x4100, 64⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1800, 8⟩, ⟨0x20000, 16384⟩]

theorem dec_sat (H G : Spec.Mgf1.Hash) (c : Proof.Rsa.AArch64.CrtImpl) :
    ∃ s, (Spec.RsaOaep.decryptContract H G AArch64.abi (Dec.decStack (RsaPkcs1Enc.AArch64.privOf c))).pre s := by
  refine ⟨decSatState, ?_⟩
  -- The precondition does not depend on the hash functions: with them and the
  -- stack literal, `sig_sat_check` decides it in the kernel.
  change (Spec.RsaOaep.decryptContract Spec.Mgf1.md5 Spec.Mgf1.md5 AArch64.abi 3536).pre decSatState
  sig_sat_check [Spec.RsaOaep.decryptContract, Spec.RsaOaep.decryptSig, AArch64.abi, AArch64.argRegs,
    RsaPkcs1Enc.AArch64.stackArgs_fifteen, List.append_eq, Spec.Rsa.lenValid, Spec.RsaPss.scratchWords,
    Spec.Rsa.scratchWords]

end VG.Proof.RsaOaep.AArch64
