module

public import VerifiedGarbage.Proof.AesXts.X86_64.Verified
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Verified
public import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Verified
public import VerifiedGarbage.Impl.AesXts.X86_64Unit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.AesXts.X86_64.CT

/-!
# Implementations of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` on x86-64

An `XtsImpl` is what a function that calls the whole-block functions needs
of them, so that its proof holds for every implementation: each is a
variant of the interface `AesXts` on x86-64 (`Variants/AesXts/X86_64/`), and
each caller (in `Generic/AesXts/X86_64/`) is emitted once for each of them
(see `TCB/Emit.lean`). Every implementation is proven against the contracts
`modeX86_64 (xtsMode true)` and `modeX86_64 (xtsMode false)` (whose return
address and stack below it no buffer overlaps), never writes the stack
pointer, and makes at most one level of calls.

There are two kinds: the functions calling an implementation of the block
functions (`XtsImpl.blocks`, e.g. `vg_aes_xts_encrypt_aesni`, emitted by
`Generic/AesBlocks/X86_64/AesXts.lean`), and the one-pass functions, which
call nothing (`XtsImpl.vaesVpclmul`, `XtsImpl.aesniPclmul`, emitted by
`Artifacts/AesXts/X86_64.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64

open VG VG.X86_64
open VG.Proof.AesCbc.X86_64 (modeX86_64)
open VG.Proof.Aes.X86_64 (BlocksImpl)

/-- An implementation of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` on x86-64. -/
structure XtsImpl where
  /-- `vg_aes_xts_encrypt`: its symbol and code. -/
  enc : Impl.Aes.X86_64.Blocks
  encDepth : enc.code.depth ≤ 1
  encOk : ∀ s, (modeX86_64 (AesXts.xtsMode true)).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode true)).post s s'
  encCt : ConstantTime isa (modeX86_64 (AesXts.xtsMode true)).pre (modeX86_64 (AesXts.xtsMode true)).pub enc.code
  encNosp : NoSp enc.code
  encMxcsr : enc.code.allInstrs (fun i => !loadsMxcsr i) = true
  encSpSafe : enc.code.all (fun i => !isa.writesSp i) = true
  /-- `vg_aes_xts_decrypt`: its symbol and code. -/
  dec : Impl.Aes.X86_64.Blocks
  decDepth : dec.code.depth ≤ 1
  decOk : ∀ s, (modeX86_64 (AesXts.xtsMode false)).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode false)).post s s'
  decCt : ConstantTime isa (modeX86_64 (AesXts.xtsMode false)).pre (modeX86_64 (AesXts.xtsMode false)).pub dec.code
  decNosp : NoSp dec.code
  decMxcsr : dec.code.allInstrs (fun i => !loadsMxcsr i) = true
  decSpSafe : dec.code.all (fun i => !isa.writesSp i) = true
  /-- What the names of its callers' instances end with (e.g. `_aesni`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace XtsImpl

/-- The pair the code of a caller calls. -/
abbrev xts (v : XtsImpl) : Impl.AesXts.X86_64Unit.Xts := ⟨v.enc, v.dec⟩

theorem nosp_of {c : Prog isa}
    (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem crypt_nosp {b : Impl.Aes.X86_64.Blocks} (hb : NoSp b.code) : NoSp (Impl.AesXts.X86_64.crypt b) := by
  have hv : b.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    rw [Code.allInstrs_eq, List.all_eq_true]
    exact fun i hi => by simp [hb i hi]
  have h : (Impl.AesXts.X86_64.crypt b).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    simp only [Impl.AesXts.X86_64.crypt, Impl.AesXts.X86_64.batch, Impl.AesXts.X86_64.pass, Code.allInstrs, hv]
    decide +kernel
  rw [Code.allInstrs_eq] at h
  exact nosp_of h

theorem crypt_depth {b : Impl.Aes.X86_64.Blocks} (hb : b.code.depth = 0) :
    (Impl.AesXts.X86_64.crypt b).depth ≤ 1 := by
  simp [Impl.AesXts.X86_64.crypt, Impl.AesXts.X86_64.batch, Impl.AesXts.X86_64.pass, Code.depth, hb]

/-- The functions calling the block functions of `v`, `vg_aes_xts_encrypt`
and `vg_aes_xts_decrypt` with `v`'s suffix. -/
def blocks (v : BlocksImpl) : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ v.suffix, Impl.AesXts.X86_64.encrypt v.enc⟩
  encDepth := crypt_depth v.encDepth
  encOk := encrypt_correct v
  encCt := crypt_ct true v.encOk v.encCt v.encNosp v.encDepth fun R w m p => (AesCbc.aesWith_state R w m p).symm
  encNosp := crypt_nosp v.encNosp
  encMxcsr := encrypt_mx v
  encSpSafe := encrypt_spSafe v
  dec := ⟨"vg_aes_xts_decrypt" ++ v.suffix, Impl.AesXts.X86_64.decrypt v.dec⟩
  decDepth := crypt_depth v.decDepth
  decOk := decrypt_correct v
  decCt := crypt_ct false v.decOk v.decCt v.decNosp v.decDepth fun R w m p => (AesCbc.aesInvWith_state R w m p).symm
  decNosp := crypt_nosp v.decNosp
  decMxcsr := decrypt_mx v
  decSpSafe := decrypt_spSafe v
  suffix := v.suffix
  features := v.features

theorem vaes_enc_nosp : NoSp Impl.AesXts.X86_64Vaes.encrypt :=
  nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem vaes_dec_nosp : NoSp Impl.AesXts.X86_64Vaes.decrypt :=
  nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem aesni_enc_nosp : NoSp Impl.AesXts.X86_64AesNi.encrypt :=
  nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem aesni_dec_nosp : NoSp Impl.AesXts.X86_64AesNi.decrypt :=
  nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)

/-- The one-pass functions with VAES and VPCLMULQDQ,
`vg_aes_xts_encrypt_vaes_vpclmul` and `vg_aes_xts_decrypt_vaes_vpclmul`. -/
def vaesVpclmul : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ "_vaes_vpclmul", Impl.AesXts.X86_64Vaes.encrypt⟩
  encDepth := by decide +kernel
  encOk := Vaes.encrypt_correct
  encCt := Vaes.encrypt_ct
  encNosp := vaes_enc_nosp
  encMxcsr := Vaes.encrypt_mx
  encSpSafe := Vaes.encrypt_spSafe
  dec := ⟨"vg_aes_xts_decrypt" ++ "_vaes_vpclmul", Impl.AesXts.X86_64Vaes.decrypt⟩
  decDepth := by decide +kernel
  decOk := Vaes.decrypt_correct
  decCt := Vaes.decrypt_ct
  decNosp := vaes_dec_nosp
  decMxcsr := Vaes.decrypt_mx
  decSpSafe := Vaes.decrypt_spSafe
  suffix := "_vaes_vpclmul"
  features := ["aes", "avx", "avx2", "vaes", "vpclmulqdq"]

/-- The one-pass functions with AES-NI and PCLMULQDQ,
`vg_aes_xts_encrypt_aesni_pclmul` and `vg_aes_xts_decrypt_aesni_pclmul`. -/
def aesniPclmul : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ "_aesni_pclmul", Impl.AesXts.X86_64AesNi.encrypt⟩
  encDepth := by decide +kernel
  encOk := OnePassNi.encrypt_correct
  encCt := OnePassNi.encrypt_ct
  encNosp := aesni_enc_nosp
  encMxcsr := OnePassNi.encrypt_mx
  encSpSafe := OnePassNi.encrypt_spSafe
  dec := ⟨"vg_aes_xts_decrypt" ++ "_aesni_pclmul", Impl.AesXts.X86_64AesNi.decrypt⟩
  decDepth := by decide +kernel
  decOk := OnePassNi.decrypt_correct
  decCt := OnePassNi.decrypt_ct
  decNosp := aesni_dec_nosp
  decMxcsr := OnePassNi.decrypt_mx
  decSpSafe := OnePassNi.decrypt_spSafe
  suffix := "_aesni_pclmul"
  features := ["aes", "avx", "pclmulqdq"]

end XtsImpl

end VG.Proof.AesXts.X86_64
