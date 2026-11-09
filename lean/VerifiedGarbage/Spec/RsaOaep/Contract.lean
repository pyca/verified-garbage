module

public import VerifiedGarbage.Spec.RsaOaep
public import VerifiedGarbage.Spec.RsaPss.Contract

/-!
# RSAES-OAEP: the signatures its contracts share

**Trusted** (as every file in `Spec/`). The parameters of decryption
(`decryptSig`), what it writes and returns (`writtenDecrypt`), and the
`# Safety` items of encryption but for what the signature gives
(`encryptSafety`), which the contracts of `Spec/RsaOaep/Tables.lean` share.
-/

@[expose] public section

namespace VG.Spec.RsaOaep

open Mgf1 (Hash)
open Rsa (bytesAt Outcome)
open RsaPss (publicScratchSafety)

variable (H : Hash)

/-- The `# Safety` items of `encrypt` but for what the signature gives. -/
def encryptSafety : List String :=
  ["`n_len` must be in 64..=1024.", "`out_len` must be `n_len`.",
    "`e_len` must be in 1..=`n_len`."] ++ publicScratchSafety

/-! ## Decryption -/

/-- What decryption with the outcome `o` writes to the `nLen` octets at `out`
and the length at `len`, and returns: 1, the message padded with zeros to
`nLen` octets and its length; or 0 (the single error) or 2 (the internal
error), zeros and the length 0. -/
def writtenDecrypt (m' : Mem) (out len : Addr) (nLen : Nat) (r : BitVec 32) : Outcome → Prop
  | .ok msg => r = 1 ∧ bytesAt m' out nLen = msg ++ zeros (nLen - msg.length) ∧
      m'.readW len 64 = BitVec.ofNat 64 msg.length
  | .invalid => r = 0 ∧ bytesAt m' out nLen = zeros nLen ∧ m'.readW len 64 = 0
  | .fault => r = 2 ∧ bytesAt m' out nLen = zeros nLen ∧ m'.readW len 64 = 0

/-- The parameters of decryption: `(out: *mut u8, out_len: usize,
msg_len: *mut [u64; 1], n: *const u8, n_len: usize, e: *const u8,
e_len: usize, p: *const u8, p_len: usize, q: *const u8, q_len: usize,
dp: *const u8, dp_len: usize, dq: *const u8, dq_len: usize,
qinv: *const u8, qinv_len: usize, label: *const u8, label_len: usize,
ct: *const u8, ct_len: usize, scratch: *mut u64, scratch_len: usize)
-> u32`. -/
def decryptSig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("msg_len", .array true .u64 1),
    ("n", .slice false .u8 "n_len"), ("e", .slice false .u8 "e_len"),
    ("p", .slice false .u8 "p_len"), ("q", .slice false .u8 "q_len"),
    ("dp", .slice false .u8 "dp_len"), ("dq", .slice false .u8 "dq_len"),
    ("qinv", .slice false .u8 "qinv_len"), ("label", .slice false .u8 "label_len"),
    ("ct", .slice false .u8 "ct_len"), ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

end VG.Spec.RsaOaep
