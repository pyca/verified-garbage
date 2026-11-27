module

public import VerifiedGarbage.Proof.HmacTable.RISCV64

/-! # The implementations of `MdHash` on RISC-V (RV64) -/

@[expose] public section

namespace VG.Proof.Variants.MdHash.RISCV64

def md5 : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.md5W

def sha1 : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha1W

def sha224 : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha224W

def sha256 : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha256W

def sha384 : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha384W

def sha512 : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha512W

def sha512_224 : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha512_224W

def sha512_256 : Proof.HmacTable.RISCV64.HVar := Proof.HmacTable.RISCV64.sha512_256W

/-- Every implementation, best first: each function generic over them is
emitted with each (the registration files that import this), and its
dispatcher tries them in this order. -/
def variants := [md5, sha1, sha224, sha256, sha384, sha512, sha512_224, sha512_256]

/-- For each of the HMAC functions a function calls through its table, that
function of each of `variants`: what the code that calls them through tables
is given (`Impl.Ecdsa.Rfc6979.RISCV64.Fn`). -/
def fns : Impl.Ecdsa.Rfc6979.RISCV64.Fns := Proof.HmacTable.RISCV64.fnsOf variants

end VG.Proof.Variants.MdHash.RISCV64
