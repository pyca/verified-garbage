module
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.AesGcm.AArch64.Verified
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.OpenPw
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.SealPw

/-!
# AES-GCM on AArch64: the code of each function, with or without the interleaved loops

Untrusted: everything here is checked by Lean. For the implementations `v`,
the code of `seal`, `open` and the functions with the powers (`open_to`'s
in one pass): with the loops that interleave counter mode and GHASH
(`Impl/AesGcm/AArch64/Stitch.lean`) if `v.stitch`, and otherwise as before,
each `Verified` against its contract, for
`Generic/AesGcm/AArch64/AesGcm.lean`.
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64 VG.Impl.AesGcm.AArch64
open VG.Proof.Gcm.AArch64.Pmull (MulKey PrepPow)
open VG.Proof.Gcm.AArch64.Stitch (Gh8Ok)

/-- The CPU features of the functions that may run the interleaved loops:
`v`'s, and `FEAT_SHA3` for `eor3` with them. -/
def GcmImpl.stitchFeatures (v : GcmImpl) : List String := v.features ++ if v.stitch then ["sha3"] else []

/-- The working space of the functions with the powers: 1024 bytes for the
interleaved loops over an implementation of counter mode that needs no
working space, else `gcmWn v`. -/
def gcmPwWn (v : GcmImpl) : Nat := if v.stitch = true ∧ v.ctr.scratch = 0 then 1024 else gcmWn v

/-- `vg_aes_gcm_seal_with_powers`, calling `g`. -/
def sealPwCode (v : GcmImpl) (g : GhashWithImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn else Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn

/-- `vg_aes_gcm_open_with_powers`, calling `g`. -/
def openPwCode (v : GcmImpl) (g : GhashWithImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn else Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn

/-- `vg_aes_gcm_open_to_with_powers`, calling `g`, in one pass: with the
interleaved loops if `v.stitch`, as `openPwCode`, else the path for TLS
records (`Fast.openToWithPw`). -/
def openToPwCode (v : GcmImpl) (g : GhashWithImpl) : Prog isa :=
  if v.stitch then Impl.AesGcm.AArch64.Stitch.openToWithPw v.callees g.fn
  else Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn

section
variable (v : GcmImpl) (hMK : MulKey) (hP : PrepPow) (gh : Gh8Ok)
include hMK hP gh

omit hP in
theorem sealPwCode_framed (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 2 (sealPwCode v g))
      (Proof.AesGcm.sealWithPowersRoundsContract AArch64.abi 2592) := by
  unfold sealPwCode
  split
  · exact Fast.sealPwS_framed v g hMK gh
  · exact Fast.sealPw_framed v g hMK

omit hP in
theorem openPwCode_framed (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2592 3 (openPwCode v g))
      (Proof.AesGcm.openWithPowersRoundsContract AArch64.abi 2592) := by
  unfold openPwCode
  split
  · exact Fast.openPwS_framed v g hMK gh
  · exact Fast.openPw_framed v g hMK

omit hP in
theorem openToPwCode_framed (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch 2608 5 (openToPwCode v g))
      (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi 2608) := by
  unfold openToPwCode
  split
  · exact Fast.openToPwS_framed v g hMK gh
  · exact Fast.openToPw_framed v g hMK


omit hP in
theorem sealPwCode_framedW (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn v + 32) 2 (sealPwCode v g))
      (Proof.AesGcm.sealWithPowersRoundsContract AArch64.abi (gcmPwWn v + 32)) := by
  by_cases hs : v.stitch = true
  · have ec : sealPwCode v g = Impl.AesGcm.AArch64.Stitch.sealWithPw v.callees g.fn := by simp [sealPwCode, hs]
    rw [ec]
    by_cases h0 : v.ctr.scratch = 0
    · rw [show gcmPwWn v = 1024 by simp [gcmPwWn, hs, h0]]
      exact Fast.sealPwS_framedW v g hMK gh (.inl rfl) (by omega)
    · rw [show gcmPwWn v = 2560 by simp [gcmPwWn, gcmWn, hs, h0]]
      exact Fast.sealPwS_framedW v g hMK gh (.inr rfl) (by rcases v.ctr.scratch_ok with h | h <;> omega)
  · have ec : sealPwCode v g = Impl.AesGcm.AArch64.Fast.sealWithPw v.callees g.fn := by simp [sealPwCode, hs]
    rw [ec, show gcmPwWn v = gcmWn v by simp [gcmPwWn, hs]]
    exact Fast.sealPw_framedW v g hMK (by rcases gcmWn_cases v with h | h <;> simp [h]) (gcmWn_hv v)

omit hP in
theorem openPwCode_framedW (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn v + 32) 3 (openPwCode v g))
      (Proof.AesGcm.openWithPowersRoundsContract AArch64.abi (gcmPwWn v + 32)) := by
  by_cases hs : v.stitch = true
  · have ec : openPwCode v g = Impl.AesGcm.AArch64.Stitch.openWithPw v.callees g.fn := by simp [openPwCode, hs]
    rw [ec]
    by_cases h0 : v.ctr.scratch = 0
    · rw [show gcmPwWn v = 1024 by simp [gcmPwWn, hs, h0]]
      exact Fast.openPwS_framedW v g hMK gh (.inl rfl) (by omega)
    · rw [show gcmPwWn v = 2560 by simp [gcmPwWn, gcmWn, hs, h0]]
      exact Fast.openPwS_framedW v g hMK gh (.inr rfl) (by rcases v.ctr.scratch_ok with h | h <;> omega)
  · have ec : openPwCode v g = Impl.AesGcm.AArch64.Fast.openWithPw v.callees g.fn := by simp [openPwCode, hs]
    rw [ec, show gcmPwWn v = gcmWn v by simp [gcmPwWn, hs]]
    exact Fast.openPw_framedW v g hMK (by rcases gcmWn_cases v with h | h <;> simp [h]) (gcmWn_hv v)

omit hP in
theorem openToPwCode_framedW (g : GhashWithImpl) :
    Verified AArch64.target (Impl.StackScratch.AArch64.withStackArgScratch (gcmPwWn v + 48) 5 (openToPwCode v g))
      (Proof.AesGcm.openToWithPowersRoundsContract AArch64.abi (gcmPwWn v + 48)) := by
  by_cases hs : v.stitch = true
  · have ec : openToPwCode v g = Impl.AesGcm.AArch64.Stitch.openToWithPw v.callees g.fn := by simp [openToPwCode, hs]
    rw [ec]
    by_cases h0 : v.ctr.scratch = 0
    · rw [show gcmPwWn v = 1024 by simp [gcmPwWn, hs, h0]]
      exact Fast.openToPwS_framedW v g hMK gh (.inl rfl) (by omega)
    · rw [show gcmPwWn v = 2560 by simp [gcmPwWn, gcmWn, hs, h0]]
      exact Fast.openToPwS_framedW v g hMK gh (.inr rfl) (by rcases v.ctr.scratch_ok with h | h <;> omega)
  · have ec : openToPwCode v g = Impl.AesGcm.AArch64.Fast.openToWithPw v.callees g.fn := by simp [openToPwCode, hs]
    rw [ec, show gcmPwWn v = gcmWn v by simp [gcmPwWn, hs]]
    exact Fast.openToPw_framedW v g hMK (by rcases gcmWn_cases v with h | h <;> simp [h]) (gcmWn_hv v)

end

end VG.Proof.AesGcm.AArch64
