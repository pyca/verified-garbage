import VerifiedGarbage.Proof.AesOcb.X86.SealCT
import VerifiedGarbage.Proof.AesOcb.X86.Init
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesOcb.Scratch

/-!
# AES-OCB on x86: `Verified`

Untrusted: everything here is checked by Lean. Correctness (`seal_wp`,
`open_wp`, `init_correct`) and constant time (`seal_ct`, `open_ct`,
`init_ct`) for any implementations `v` of `vg_aes_encrypt_blocks`,
`vg_aes_decrypt_blocks` and `vg_aes_expand_key`, a state satisfying each
precondition, and the shared contracts with the working space as a last
argument (`Proof/AesOcb/Scratch.lean`), with 24 bytes of stack: the
arguments and return address of the calls, whose callees use no stack.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86 VG.Impl.AesOcb.X86
open VG.Proof.Aes.X86 (BlocksImpl)

theorem seal_correct (v : BlocksImpl) (s : State) (hs : sealX86.pre s) :
    ∃ t s', Exec isa («seal» (callees v)) s t s' ∧ abiPreserved s s' ∧ sealX86.post s s' :=
  seal_wp v hs

theorem open_correct (v : BlocksImpl) (s : State) (hs : openX86.pre s) :
    ∃ t s', Exec isa («open» (callees v)) s t s' ∧ abiPreserved s s' ∧ openX86.post s s' :=
  open_wp v hs

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: the key
context at `0x1000`, 10 rounds, a 7-byte nonce at `0x2000`, no associated
data (at `0x2100`), no data (at `0x3000`), a 4-byte tag at `0x4000` and
`work` at `0x5000`, as stack arguments at `0x8004`. -/
def sealSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 10 else if a = 0x800d then 0x20
    else if a = 0x8010 then 7 else if a = 0x8015 then 0x21 else if a = 0x801d then 0x30
    else if a = 0x8025 then 0x40 else if a = 0x8028 then 4 else if a = 0x802d then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 4⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩]

/-- As `sealSat`, with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 7⟩, ⟨0x2100, 0⟩, ⟨0x4000, 4⟩],
                 wr := [⟨0x3000, 0⟩, ⟨0x5000, 2560⟩, ⟨0x8004, 44⟩] }

theorem sealSat_args : arg sealSat 0 = 0x1000 ∧ arg sealSat 1 = 10 ∧ arg sealSat 2 = 0x2000 ∧ arg sealSat 3 = 7 ∧
    arg sealSat 4 = 0x2100 ∧ arg sealSat 5 = 0 ∧ arg sealSat 6 = 0x3000 ∧ arg sealSat 7 = 0 ∧
    arg sealSat 8 = 0x4000 ∧ arg sealSat 9 = 4 ∧ arg sealSat 10 = 0x5000 ∧ argAddr sealSat 0 = 0x8004 := by
  decide

theorem openSat_args : arg openSat 0 = 0x1000 ∧ arg openSat 1 = 10 ∧ arg openSat 2 = 0x2000 ∧ arg openSat 3 = 7 ∧
    arg openSat 4 = 0x2100 ∧ arg openSat 5 = 0 ∧ arg openSat 6 = 0x3000 ∧ arg openSat 7 = 0 ∧
    arg openSat 8 = 0x4000 ∧ arg openSat 9 = 4 ∧ arg openSat 10 = 0x5000 ∧ argAddr openSat 0 = 0x8004 :=
  sealSat_args

theorem seal_verified (v : BlocksImpl) :
    Verified X86.target («seal» (callees v)) (Proof.AesOcb.sealScratchContract X86.abi 24) :=
  Verified.of_correct (seal_correct v) (seal_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := sealSat_args
    have esp : sealSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Spec.Ocb.sealPost, sealX86, sealPre, oneLay, onePub, ctxR, nonceR, aadR, dataR, tagR, workR, argsR', retR,
      stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using sealSat)

theorem open_verified (v : BlocksImpl) :
    Verified X86.target («open» (callees v)) (Proof.AesOcb.openScratchContract X86.abi 24) :=
  Verified.of_correct (open_correct v) (open_ct v) (by
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e⟩ := openSat_args
    have esp : openSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
      Spec.Ocb.openPost, Spec.Ocb.openLeak, openX86, openPost, openResult, openPre, oneLay, onePub, ctxR, nonceR,
      aadR, dataR, tagR, workR, argsR', retR, stackR, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, e, esp] using openSat)

/-- A state satisfying `vg_aes_ocb_init`'s precondition: a key of 16 bytes
at `0x1000`, the context at `0x2000` and the scratch buffer at `0x4000`, as
stack arguments at `0x8004`. -/
def initSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20
    else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 256⟩, ⟨0x4000, 2560⟩, ⟨0x8004, 16⟩]

theorem init_verified (v : BlocksImpl) :
    Verified X86.target (init (callees v)) (Proof.AesOcb.initScratchContract X86.abi 24) :=
  Verified.of_correct (init_correct v) (init_ct v) (by
    have a0 : arg initSat 0 = 0x1000 := by decide
    have a1 : arg initSat 1 = 16 := by decide
    have a2 : arg initSat 2 = 0x2000 := by decide
    have a3 : arg initSat 3 = 0x4000 := by decide
    have e : argAddr initSat 0 = 0x8004 := by decide
    have esp : initSat.gpr .esp = 0x8000 := rfl
    sig_implies [Proof.AesOcb.initScratchContract, Proof.AesOcb.initScratchSig, Spec.Ocb.initPre,
      Spec.Ocb.initPost, initX86, initPre, keyR, ictxR, scrR, iargsR, retR, stackR, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes] [a0, a1, a2, a3, e, esp] using initSat)

end VG.Proof.AesOcb.X86
