module

import VerifiedGarbage.Proof.AesXts.AArch64.Unit.CT
public import VerifiedGarbage.Proof.AesXts.AArch64.Variant
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Enc
public import VerifiedGarbage.Proof.AesXts.Spec
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Dec
import VerifiedGarbage.Proof.AesXts.AArch64.CT
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.AesXts.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# XTS-AES of data units on AArch64: `Verified`

Correctness (`encrypt_wp`, `decrypt_wp`) and constant time (`encrypt_ct`,
`decrypt_ct`) for any implementation `v` of the whole-block functions
(`XtsImpl`), a state satisfying the precondition (`unitSat`), and the shared
contracts of `Spec/Xts/Contract.lean`, with no stack: the calls keep the
return address in `x30`, which the functions save in the scratch buffer.
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesXts.AArch64 (XtsImpl)

theorem encrypt_keepsV (v : XtsImpl) : (encrypt v.enc).allInstrs keepsV = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.allInstrs, v.encKeepsV]; decide +kernel

theorem decrypt_keepsV (v : XtsImpl) : (decrypt v.enc v.dec).allInstrs keepsV = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.allInstrs, v.encKeepsV, v.decKeepsV]; decide +kernel

theorem encrypt_correct (v : XtsImpl) (s : State) (hs : (unitAArch64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.enc) s t s' ∧ abiPreserved s s' ∧ (unitAArch64 true).post s s' :=
  WP.withPreservedV (encrypt_wp (UPre.of hs) v.encOk v.encNoFrames) (encrypt_keepsV v)

theorem decrypt_correct (v : XtsImpl) (s : State) (hs : (unitAArch64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.enc v.dec) s t s' ∧ abiPreserved s s' ∧ (unitAArch64 false).post s s' :=
  WP.withPreservedV (decrypt_wp (UPre.of hs) v.encOk v.encNoFrames v.decOk v.decNoFrames) (decrypt_keepsV v)

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at `0x5000`. -/
def unitSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 10 | .x3 => 0x3000 | .x4 => 0x4000 | .x5 => 16 | .x6 => 0x5000
    | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩]
  wr := [⟨0x4000, 16⟩, ⟨0x5000, 2432⟩]

theorem encrypt_verified (v : XtsImpl) :
    Verified AArch64.target (encrypt v.enc) (Spec.Xts.aesEncryptUnitContract AArch64.abi) :=
  Verified.of_correct (encrypt_correct v) (encrypt_ct v.encOk v.encNoFrames v.encCt) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitAArch64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, AArch64.abi, AArch64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified (v : XtsImpl) :
    Verified AArch64.target (decrypt v.enc v.dec) (Spec.Xts.aesDecryptUnitContract AArch64.abi) :=
  Verified.of_correct (decrypt_correct v)
    (decrypt_ct v.encOk v.encNoFrames v.encCt v.decOk v.decNoFrames v.decCt) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitAArch64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, AArch64.abi, AArch64.argRegs] [unitSat] using unitSat)

/-! ## The functions, as emitted

`vg_aes_xts_encrypt_unit` and `vg_aes_xts_decrypt_unit` with their cleanup
(`Impl.AesXts.AArch64Unit.Fn`), around an implementation `v` of
`vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`: each meets its contract in
constant time and returns without secret residue (`VerifiedScrubbed`), which
is what its registration binds. What the cleanup needs of the code
(`ScrubAll.scrubSide`) is proved of each function's own instructions here,
once, with code that does nothing in the place of the functions it calls,
and of each implementation where it is defined (`XtsImpl.encScrub`,
`XtsImpl.decScrub`). -/

open VG.AArch64.ScrubAll

private theorem encrypt_all {p : Instr → Bool} (f : Impl.Aes.AArch64.Blocks)
    (h0 : sideAll p (encrypt ⟨"", .block [], ⟨[], [], []⟩⟩) = true) (hc : sideAll p f.code = true) :
    sideAll p (encrypt f) = true := by
  simp only [encrypt, tweak, encSteal, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, hc, and_self]

private theorem decrypt_all {p : Instr → Bool} (e d : Impl.Aes.AArch64.Blocks)
    (h0 : sideAll p (decrypt ⟨"", .block [], ⟨[], [], []⟩⟩ ⟨"", .block [], ⟨[], [], []⟩⟩) = true) (he : sideAll p e.code = true)
    (hd : sideAll p d.code = true) : sideAll p (decrypt e d) = true := by
  simp only [decrypt, tweak, decSteal, sideAll, Bool.and_eq_true] at h0 ⊢
  simp only [h0, he, hd, and_self]

private theorem encrypt_own :
    calleeSide (encrypt ⟨"", .block [], ⟨[], [], []⟩⟩) Impl.AesXts.AArch64Unit.Fn.encryptOwn = true := by
  kernel_rfl

private theorem decrypt_own :
    calleeSide (decrypt ⟨"", .block [], ⟨[], [], []⟩⟩ ⟨"", .block [], ⟨[], [], []⟩⟩) Impl.AesXts.AArch64Unit.Fn.decryptOwn = true := by
  kernel_rfl

theorem encrypt_side (v : XtsImpl) :
    scrubSide (encrypt v.enc) 0 0 (Impl.AesXts.AArch64Unit.Fn.encryptOwn.union v.enc.clear) [] = true := by
  refine scrubSide_union0 ?_ (by decide)
    (encrypt_all v.enc (sideAll_union_left encrypt_own) (sideAll_union_right v.encScrub)) (by decide)
  simp only [encrypt, tweak, encSteal, swap, Code.aarch64Depth, Proof.Aes.AArch64.depth_of_noFrames v.encNoFrames]
  decide

theorem decrypt_side (v : XtsImpl) :
    scrubSide (decrypt v.enc v.dec) 0 0
      ((Impl.AesXts.AArch64Unit.Fn.decryptOwn.union v.enc.clear).union v.dec.clear) [] = true := by
  refine scrubSide_union0 ?_ (by decide)
    (decrypt_all v.enc v.dec (sideAll_union_left (sideAll_union_left decrypt_own))
      (sideAll_union_left (sideAll_union_right v.encScrub)) (sideAll_union_right v.decScrub))
    (linkRegs_union (by decide))
  simp only [decrypt, tweak, decSteal, swap, Code.aarch64Depth, Proof.Aes.AArch64.depth_of_noFrames v.encNoFrames,
    Proof.Aes.AArch64.depth_of_noFrames v.decNoFrames]
  decide

/-- `vg_aes_xts_encrypt_unit` as emitted, cleanup included. -/
theorem encrypt_scrubbed (v : XtsImpl) :
    VerifiedScrubbed AArch64.target (Impl.AesXts.AArch64Unit.Fn.encrypt v.enc)
      (Spec.Xts.aesEncryptUnitContract AArch64.abi) 0 :=
  verifiedScrubbed (api := Spec.Xts.aesEncryptUnitApi)
    { code := encrypt v.enc, verified := encrypt_verified v } _
    Proof.AesXts.AArch64.Scrub.encryptOk (encrypt_side v)

/-- `vg_aes_xts_decrypt_unit` as emitted, cleanup included. -/
theorem decrypt_scrubbed (v : XtsImpl) :
    VerifiedScrubbed AArch64.target (Impl.AesXts.AArch64Unit.Fn.decrypt v.enc v.dec)
      (Spec.Xts.aesDecryptUnitContract AArch64.abi) 0 :=
  verifiedScrubbed (api := Spec.Xts.aesDecryptUnitApi)
    { code := decrypt v.enc v.dec, verified := decrypt_verified v } _
    Proof.AesXts.AArch64.Scrub.decryptOk (decrypt_side v)

end VG.Proof.AesXts.AArch64.Unit
