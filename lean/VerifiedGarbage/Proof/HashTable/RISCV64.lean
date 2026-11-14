module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Hashes
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.MgfT
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Pre
public import VerifiedGarbage.Spec.HashTable

/-!
# The hash functions RSAES-OAEP and RSASSA-PSS take on RISC-V

Each hash function as RSAES-OAEP on RISC-V has it (`Link`), with its place
in `Spec.Mgf1.hashes` (`TVar`): what its table of `MdHash`
(`Proof/MdHashTable/RISCV64/Tables.lean`) and of `Hmac`
(`Proof/HmacTable/RISCV64.lean`) are built from.
-/

@[expose] public section

namespace VG.Proof.HashTable.RISCV64

open VG VG.RISCV64
open VG.Proof.RsaOaep.RISCV64 (Link)

/-- A hash function, with its place in `Spec.Mgf1.hashes`. -/
structure TVar where
  H : Impl.Hmac.Stream.RISCV64.Hash
  l : Link H
  idx : Spec.Mgf1.hashes[Spec.HashTable.index l.G]? = some l.G

def md5V : TVar := ⟨_, Proof.RsaOaep.RISCV64.md5L, rfl⟩
def sha1V : TVar := ⟨_, Proof.RsaOaep.RISCV64.sha1L, rfl⟩
def sha224V : TVar := ⟨_, Proof.RsaOaep.RISCV64.sha224L, rfl⟩
def sha256V : TVar := ⟨_, Proof.RsaOaep.RISCV64.sha256L, rfl⟩
def sha384V : TVar := ⟨_, Proof.RsaOaep.RISCV64.sha384L, rfl⟩
def sha512V : TVar := ⟨_, Proof.RsaOaep.RISCV64.sha512L, rfl⟩
def sha512_224V : TVar := ⟨_, Proof.RsaOaep.RISCV64.sha512_224L, rfl⟩
def sha512_256V : TVar := ⟨_, Proof.RsaOaep.RISCV64.sha512_256L, rfl⟩

end VG.Proof.HashTable.RISCV64
