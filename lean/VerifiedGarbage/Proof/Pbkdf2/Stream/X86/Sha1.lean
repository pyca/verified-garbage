import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes
import VerifiedGarbage.Proof.Sha1.X86.Stream.Init
import VerifiedGarbage.Proof.Sha1.X86.Variants.Code

/-!
# SHA-1's streaming functions on x86 (32-bit), for every backend

SHA-1 has an implementation of its compression function for each variant of
its interface on x86 (`Variants/Sha1/X86/`), and its streaming `update` and
`finalize` made with each (`Sha1Stream`): `sha1OK` is `HashOK` for any of
them, with `vg_sha1_init`.
-/

namespace VG.Proof.Pbkdf2.Stream.X86

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Sha1.X86.Variants (hmacHash)

/-- SHA-1's streaming `update` and `finalize` made with one implementation of
its compression function, named with its suffix (e.g. `_shani`; nothing for
the baseline implementation), verified against their per-target contracts;
they keep `esp` and use at most 20 bytes of stack. -/
structure Sha1Stream where
  suffix : String
  upd : Prog isa
  fin : Prog isa
  updOK : Verified X86.target upd Proof.Sha1.updateX86
  finOK : Verified X86.target fin Proof.Sha1.finalizeX86
  updSp : NoSp upd
  finSp : NoSp fin
  updSU : stackUse upd ≤ 20
  finSU : stackUse fin ≤ 20

/-- SHA-1's streaming functions with `v`'s `update` and `finalize`. -/
abbrev sha1H (v : Sha1Stream) : Hash := hmacHash v.suffix v.upd v.fin

theorem sha1_initSp : NoSp Impl.Sha1.X86.Stream.init := nosp_of (by lit_decide)
theorem sha1_initSU : stackUse Impl.Sha1.X86.Stream.init ≤ 20 := by lit_decide

/-- SHA-1's streaming functions with `v`'s `update` and `finalize`, verified. -/
def sha1OK (v : Sha1Stream) : HashOK (sha1H v) where
  SH := Spec.Hmac.sha1S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 20 ≤ 20 by decide
  hF := show 20 ≤ 64 by decide
  hD0 := show 0 < 20 by decide
  hS0 := show 0 < 84 by decide
  hSB := show 84 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := Hmac.Generic.Common.sha1_repr
  init := Proof.Sha1.X86.Stream.init_verified
  upd := v.updOK
  fin := v.finOK.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finOK.2.2 }
  initSp := sha1_initSp
  updSp := v.updSp
  finSp := v.finSp
  initSU := sha1_initSU
  updSU := v.updSU
  finSU := v.finSU

end VG.Proof.Pbkdf2.Stream.X86
