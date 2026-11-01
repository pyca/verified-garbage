module

import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.Artifacts.Rc2.AArch64
meta import VerifiedGarbage.Artifacts.Rc2.AArch64

/-!
# Internal functions (`Rust.Internal`)

RC2's AArch64 artifacts, the streaming functions: they call
`vg_rc2_expand_key`, `vg_rc2_cbc_encrypt` and `vg_rc2_cbc_decrypt`, which
call `vg_rc2_encrypt_block` and `vg_rc2_decrypt_block`, none of them an
artifact. The emitter emits each as an internal function, from the code the
calls run: a file of its own, `internal/<name>.rs`, its text in
`assembly/internal/<name>.s`, which `rc2.rs` (the module of the artifacts
calling them, and of the algorithm their names start with) declares as
modules private to the crate, and the callers naming them there.
-/

namespace VG.Test.Internal
open VG

def arts : List Artifact := Artifacts.Rc2.AArch64.artifacts

def out : List (String × String) := match Rust.files arts with
  | .ok fs => fs
  | .error e => [("error", e)]

def file (n : String) : String := ((out.find? (·.1 == s!"verified-garbage-asm-aarch64/{n}")).map (·.2)).getD ""

def has (text part : String) : Bool := (text.splitOn part).length > 1

def internal : List String := ["vg_rc2_cbc_decrypt", "vg_rc2_cbc_encrypt", "vg_rc2_decrypt_block",
  "vg_rc2_encrypt_block", "vg_rc2_expand_key"]

#guard out.map (·.1) == ["verified-garbage-asm-aarch64/src/lib.rs"] ++
  internal.flatMap (fun n => [s!"verified-garbage-asm-aarch64/src/internal/{n}.rs",
    s!"verified-garbage-asm-aarch64/assembly/internal/{n}.s"]) ++
  ["verified-garbage-asm-aarch64/src/rc2.rs", "verified-garbage-asm-aarch64/assembly/rc2.s"]

-- `rc2.rs` declares their modules, private to the crate; `lib.rs` names
-- none of them.
#guard internal.all fun n => has (file "src/rc2.rs")
  s!"\n#[rustfmt::skip]\n#[path = \"internal/{n}.rs\"]\npub(crate) mod {n};\n"
#guard !has (file "src/lib.rs") "internal"

-- Where an internal function's module is declared: the target's module named
-- in its name, the longest if several are, whether or not it calls it, or
-- else the first module calling it.
#guard Rust.internalOwner "vg_sha256_compress" ["ecdsa_p256", "hmac_sha256", "sha256"]
  ["hmac_sha256", "ecdsa_p256"] == "sha256"
#guard Rust.internalOwner "vg_aes_gcm_ghash" ["aes", "aes_gcm", "chacha20"] ["aes_gcm"] == "aes_gcm"
#guard Rust.internalOwner "vg_keccak_f1600" ["mlkem768", "sha3"] ["sha3", "mlkem768"] == "mlkem768"

-- Callers name them in their modules, from the crate's modules and from
-- another internal function's.
#guard has (file "src/rc2.rs")
  "vg_rc2_cbc_encrypt = sym super::rc2::vg_rc2_cbc_encrypt::vg_rc2_cbc_encrypt,\n"
#guard has (file "src/internal/vg_rc2_cbc_encrypt.rs")
  "vg_rc2_encrypt_block = sym crate::rc2::vg_rc2_encrypt_block::vg_rc2_encrypt_block,\n"
#guard has (file "src/internal/vg_rc2_encrypt_block.rs")
  "#[unsafe(naked)]\npub(crate) unsafe extern \"C\" fn vg_rc2_encrypt_block() {\n"
#guard !has (file "src/rc2.rs") "fn vg_rc2_encrypt_block"

/-- The lines of `vg_rc2_encrypt_block`'s function, from its code. -/
def blockLines : List Line :=
  Rust.bodyLines AArch64.target [] (AArch64.printer.function Impl.Rc2.AArch64.encryptBlock)

-- The internal function's code is the block function's, and so is its text.
#guard has (file "src/internal/vg_rc2_encrypt_block.rs")
  (Rust.asmOf AArch64.target blockLines (fun _ => "") "crate")
#guard has (file "assembly/internal/vg_rc2_encrypt_block.s")
  (Rust.moduleAssembly.functionAssembly AArch64.target "vg_rc2_encrypt_block" blockLines)

-- An internal function's name is a Rust function's.
#guard Rust.internalName "vg_rc2_encrypt_block" && Rust.internalName "vg_x25519_2"
#guard ["", "vg_", "rc2_encrypt", "vg_Rc2", "vg_a-b", "vg_a()", "vg_a b", "vg_é"].all
  (!Rust.internalName ·)

end VG.Test.Internal
