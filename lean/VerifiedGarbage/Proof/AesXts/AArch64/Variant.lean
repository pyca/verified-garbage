module

public import VerifiedGarbage.Proof.AesXts.AArch64.CT
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Top
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.AesXts.AArch64.Aes.Top
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Impl.AesXts.AArch64
public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
meta import VerifiedGarbage.Impl.AesXts.AArch64
meta import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Block
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
meta import VerifiedGarbage.Proof.AesXts.AArch64.CT

/-! ### `AesXts.AArch64.Aes.Verified`, which only this module used -/

section

/-! ### `AesXts.AArch64.Verified`, which this module and modules that import it used -/

section

/-!
# XTS-AES on AArch64: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from `crypt_wp` and `crypt_ct`, a state satisfying the
precondition, and the shared contracts of `Spec/Xts/Contract.lean` (with no
stack: the call keeps the return address in `x30`, which the functions save
in the scratch buffer).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64 VG.Impl.AesXts.AArch64
open VG.Proof.AesCbc (ciphOf aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)

theorem encrypt_keepsV (v : BlocksImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, crypt, batch, pass, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem encrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s' :=
  WP.withPreservedV (crypt_wp true v.encOk v.encNoFrames (fun R w m p => (aesWith_state R w m p).symm) hs)
    (encrypt_keepsV v)

theorem decrypt_keepsV (v : BlocksImpl) : (decrypt v.dec).allInstrs keepsV = true := by
  simp only [decrypt, crypt, batch, pass, Code.allInstrs, v.decKeepsV]; decide +kernel

theorem decrypt_correct (v : BlocksImpl) (s : State) (hs : (modeAArch64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa (decrypt v.dec) s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s' :=
  WP.withPreservedV (crypt_wp false v.decOk v.decNoFrames (fun R w m p => (aesInvWith_state R w m p).symm) hs)
    (decrypt_keepsV v)

end VG.Proof.AesXts.AArch64

end

end

/-!
# One-pass XTS-AES on AArch64: `Verified`

Correctness (`crypt_wp` with `encFn` or `decFn`, whose setups load the round
keys, `encSetup_ok'` and `decSetup_ok'`), the registers preserved (no
instruction writes a callee-saved one), constant time (`taint_decide`: only
the pointers, `rounds` and `n` reach a branch or an address), and the shared
contracts of `Spec/Xts/Contract.lean`, from the same contracts
`modeAArch64 (xtsMode enc)` as the functions calling a block function
(`AArch64/Verified.lean`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Aes

open VG VG.AArch64
open VG.Impl.AesXts.AArch64Aes (encrypt decrypt)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.Aes.AArch64.Aese (encFn decFn)

theorem encFn_F : encFn.F = stF true := rfl

theorem decFn_F : decFn.F = stF false := rfl

theorem encrypt_keepsV : encrypt.allInstrs keepsV = true := by lit_decide

theorem decrypt_keepsV : decrypt.allInstrs keepsV = true := by lit_decide

theorem encrypt_noFrames : encrypt.noFrames = true := by lit_decide

theorem decrypt_noFrames : decrypt.noFrames = true := by lit_decide

theorem encrypt_correct (s : State) (hs : (modeAArch64 (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved)
    (crypt_wp encFn true encFn_F (fun _ hp => encSetup_ok' hp) hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he encrypt_keepsV⟩, h₂⟩

theorem decrypt_correct (s : State) (hs : (modeAArch64 (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, h₂, h₁⟩ := WP.gprs (rs := preserved)
    (crypt_wp decFn false decFn_F (fun _ hp => decSetup_ok' hp) hs) (by lit_decide) (by lit_decide)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he decrypt_keepsV⟩, h₂⟩

theorem encrypt_ct (enc : Bool) : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre
    (modeAArch64 (AesXts.xtsMode enc)).pub encrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem decrypt_ct (enc : Bool) : ConstantTime isa (modeAArch64 (AesXts.xtsMode enc)).pre
    (modeAArch64 (AesXts.xtsMode enc)).pub decrypt := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.AesXts.AArch64.Aes

end

end

/-!
# Implementations of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` on AArch64

An `XtsImpl` is what a function that calls the whole-block functions needs
of them, so that its proof holds for every implementation: each is a
variant of the interface `AesXts` on AArch64 (`Variants/AesXts/AArch64/`),
and each caller (in `Generic/AesXts/AArch64/`) is emitted once for each of
them (see `TCB/Emit.lean`). Both functions are proven against the contracts
`modeAArch64 (xtsMode true)` and `modeAArch64 (xtsMode false)`, have no
frames and write no callee-saved vector register.

There are two: the functions calling the bitsliced block functions
(`XtsImpl.blocks .scalar`, `vg_aes_xts_encrypt`), and the one-pass functions
with the AES instructions, which call nothing (`XtsImpl.aes`,
`vg_aes_xts_encrypt_aes`); both are emitted by
`Artifacts/AesXts/AArch64.lean`.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64

open VG VG.AArch64
open VG.Proof.AesCbc (aesWith_state aesInvWith_state)
open VG.Proof.AesCbc.AArch64 (modeAArch64)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- An implementation of `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt` on AArch64. -/
structure XtsImpl where
  /-- `vg_aes_xts_encrypt`: its symbol and code. -/
  enc : Impl.Aes.AArch64.Blocks
  encNoFrames : enc.code.noFrames = true
  encOk : ∀ s, (modeAArch64 (AesXts.xtsMode true)).pre s →
    ∃ t s', Exec isa enc.code s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode true)).post s s'
  encCt : ConstantTime isa (modeAArch64 (AesXts.xtsMode true)).pre (modeAArch64 (AesXts.xtsMode true)).pub
    enc.code
  encKeepsV : enc.code.allInstrs keepsV = true
  /-- `vg_aes_xts_decrypt`: its symbol and code. -/
  dec : Impl.Aes.AArch64.Blocks
  decNoFrames : dec.code.noFrames = true
  decOk : ∀ s, (modeAArch64 (AesXts.xtsMode false)).pre s →
    ∃ t s', Exec isa dec.code s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode false)).post s s'
  decCt : ConstantTime isa (modeAArch64 (AesXts.xtsMode false)).pre (modeAArch64 (AesXts.xtsMode false)).pub
    dec.code
  decKeepsV : dec.code.allInstrs keepsV = true
  /-- What the names of its callers' instances end with (e.g. `_aes`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String

namespace XtsImpl

theorem crypt_noFrames {b : Impl.Aes.AArch64.Blocks} (h : b.code.noFrames = true) :
    (Impl.AesXts.AArch64.crypt b).noFrames = true := by
  simp [Impl.AesXts.AArch64.crypt, Impl.AesXts.AArch64.batch, Impl.AesXts.AArch64.pass, Code.noFrames, h]

/-- The functions calling the block functions of `v`, `vg_aes_xts_encrypt`
and `vg_aes_xts_decrypt` with `v`'s suffix. -/
def blocks (v : BlocksImpl) : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ v.suffix, Impl.AesXts.AArch64.encrypt v.enc⟩
  encNoFrames := crypt_noFrames v.encNoFrames
  encOk := encrypt_correct v
  encCt := crypt_ct true v.encOk v.encCt v.encNoFrames fun R w m p => (aesWith_state R w m p).symm
  encKeepsV := encrypt_keepsV v
  dec := ⟨"vg_aes_xts_decrypt" ++ v.suffix, Impl.AesXts.AArch64.decrypt v.dec⟩
  decNoFrames := crypt_noFrames v.decNoFrames
  decOk := decrypt_correct v
  decCt := crypt_ct false v.decOk v.decCt v.decNoFrames fun R w m p => (aesInvWith_state R w m p).symm
  decKeepsV := decrypt_keepsV v
  suffix := v.suffix
  features := v.features

/-- The one-pass functions with the AES instructions,
`vg_aes_xts_encrypt_aes` and `vg_aes_xts_decrypt_aes`. -/
def aes : XtsImpl where
  enc := ⟨"vg_aes_xts_encrypt" ++ "_aes", Impl.AesXts.AArch64Aes.encrypt⟩
  encNoFrames := Aes.encrypt_noFrames
  encOk := Aes.encrypt_correct
  encCt := Aes.encrypt_ct true
  encKeepsV := Aes.encrypt_keepsV
  dec := ⟨"vg_aes_xts_decrypt" ++ "_aes", Impl.AesXts.AArch64Aes.decrypt⟩
  decNoFrames := Aes.decrypt_noFrames
  decOk := Aes.decrypt_correct
  decCt := Aes.decrypt_ct false
  decKeepsV := Aes.decrypt_keepsV
  suffix := "_aes"
  features := ["aes"]

end XtsImpl

end VG.Proof.AesXts.AArch64
