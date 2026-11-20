module

public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.AesGcm.X86_64.Short
public import VerifiedGarbage.Impl.AesGcm.X86_64.SealFin
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastSeal
public import VerifiedGarbage.Impl.AesGcm.X86_64.FastOpen
public import VerifiedGarbage.Impl.Gcm.X86_64.Flag
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenToSplit
public import VerifiedGarbage.Impl.AesGcm.X86_64.OpenTo
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-GCM on x86-64: the functions as emitted

Each function, over the callees `c`, in a frame whose size its
implementations decide (`n` bytes of stack in all), then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`): every vector register at the level
`v` and every caller-saved register but the `rb` bits of the result
cleared, and the `n` bytes of stack its frames and calls use wiped.
-/

@[expose] public section

namespace VG.Impl.AesGcm.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.StackScratch.X86_64 (withStackScratch withStackArgScratch)

/-- `Spec.Gcm.initApi`'s function as emitted, in `n` bytes of stack. -/
def init (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 0 n (withStackScratch (n - 8) .rcx (Impl.AesGcm.X86_64.init c))

/-- `Spec.Gcm.streamInitApi`'s function as emitted, in `n` bytes of stack. -/
def streamInit (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 0 n (withStackScratch (n - 8) .r8 (Impl.AesGcm.X86_64.streamInit c))

/-- `Spec.Gcm.streamAadApi`'s function as emitted, in `n` bytes of stack. -/
def streamAad (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 0 n (withStackScratch (n - 8) .r9 (Impl.AesGcm.X86_64.streamAad c))

/-- `Spec.Gcm.streamFinishApi`'s function as emitted, in `n` bytes of stack. -/
def streamFinish (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 0 n (withStackArgScratch (n - 8) 0 (Impl.AesGcm.X86_64.streamFinish c))

/-- `Spec.Gcm.streamVerifyApi`'s function as emitted, in `n` bytes of stack. -/
def streamVerify (v : VecLevel) (n : Nat) (c : Callees) : Prog isa :=
  scrubAll v 32 n (withStackArgScratch (n - 8) 1 (Impl.AesGcm.X86_64.streamVerify c))

/-! ## On a prepared key context

`short` and `fin` are the variant's (`GcmImpl.short`, `GcmImpl.fin`); `cp`
are the callees with the whole-blocks functions on prepared powers, and `t`
the count of powers that chooses them (`Impl.Gcm.X86_64.Flag.onFlag`). -/

/-- `vg_aes_gcm_seal`'s code calling `c` (`GcmImpl.sealCode`). -/
def sealCode (short fin : Bool) (c : Callees) : Prog isa :=
  if short then Impl.AesGcm.X86_64.Short.«seal» c
  else if fin then Impl.AesGcm.X86_64.SealFin.«seal» c else Impl.AesGcm.X86_64.«seal» c

/-- `vg_aes_gcm_open`'s code calling `c` (`GcmImpl.openCode`). -/
def openCode (short : Bool) (c : Callees) : Prog isa :=
  if short then Impl.AesGcm.X86_64.Short.«open» c else Impl.AesGcm.X86_64.«open» c

/-- `seal`'s code on prepared powers calling `c` (`GcmImpl.sealCodeP`). -/
def sealCodeP (short fin : Bool) (c : Callees) : Prog isa :=
  if short then
    Impl.AesGcm.X86_64.Short.«seal» c Impl.AesGcm.X86_64.Short.powersP Impl.AesGcm.X86_64.Short.ghashP
      (Impl.AesGcm.X86_64.FastSeal.sel c (Impl.AesGcm.X86_64.Short.sealLong c))
  else if fin then
    Impl.AesGcm.X86_64.SealFin.«seal» c
      (Impl.AesGcm.X86_64.FastSeal.sel c (Impl.AesGcm.X86_64.SealFin.mid c) Impl.AesGcm.X86_64.Short.finKsA true)
  else Impl.AesGcm.X86_64.«seal» c

/-- `open`'s code on prepared powers calling `c` (`GcmImpl.openCodeP`). -/
def openCodeP (short : Bool) (c : Callees) : Prog isa :=
  if short then
    Impl.AesGcm.X86_64.Short.«open» c Impl.AesGcm.X86_64.Short.powersP
      (Impl.AesGcm.X86_64.FastOpen.sel c (Impl.AesGcm.X86_64.Short.openLong c)) Impl.AesGcm.X86_64.Short.ghashP
  else
    Impl.AesGcm.X86_64.FastOpen.openFin
      (Impl.AesGcm.X86_64.FastOpen.sel c (Impl.AesGcm.X86_64.Short.openLong c) Impl.AesGcm.X86_64.Short.finKsA true)

/-- `Spec.Gcm.sealPreparedApi`'s function on the key context alone, as emitted. -/
def sealW (v : VecLevel) (short fin : Bool) (c : Callees) : Prog isa :=
  scrubAll v 0 2624 (withStackArgScratch 2600 3 (sealCode short fin c))

/-- `Spec.Gcm.openPreparedApi`'s function on the key context alone, as emitted. -/
def openW (v : VecLevel) (short : Bool) (c : Callees) : Prog isa :=
  scrubAll v 32 2632 (withStackArgScratch 2608 4 (openCode short c))

/-- `Spec.Gcm.streamEncryptPreparedApi`'s function on the key context alone, as emitted. -/
def streamEncryptW (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 0 2608 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt c))

/-- `Spec.Gcm.streamDecryptPreparedApi`'s function on the key context alone, as emitted. -/
def streamDecryptW (v : VecLevel) (c : Callees) : Prog isa :=
  scrubAll v 0 2608 (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt c))

/-- `Spec.Gcm.sealPreparedApi`'s function, by the count `t` on the prepared
powers (calling `cp`) or on the key context, as emitted. -/
def sealP (v : VecLevel) (t : Nat) (short fin : Bool) (cp c : Callees) : Prog isa :=
  scrubAll v 0 2624 (Impl.Gcm.X86_64.Flag.onFlag t (withStackArgScratch 2600 3 (sealCodeP short fin cp))
    (withStackArgScratch 2600 3 (sealCode short fin c)))

/-- `Spec.Gcm.openPreparedApi`'s function, as `sealP`. -/
def openP (v : VecLevel) (t : Nat) (short : Bool) (cp c : Callees) : Prog isa :=
  scrubAll v 32 2632 (Impl.Gcm.X86_64.Flag.onFlag t (withStackArgScratch 2608 4 (openCodeP short cp))
    (withStackArgScratch 2608 4 (openCode short c)))

/-- `Spec.Gcm.streamEncryptPreparedApi`'s function, as `sealP`. -/
def streamEncryptP (v : VecLevel) (t : Nat) (cp c : Callees) : Prog isa :=
  scrubAll v 0 2608 (Impl.Gcm.X86_64.Flag.onFlag t
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt cp))
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamEncrypt c)))

/-- `Spec.Gcm.streamDecryptPreparedApi`'s function, as `sealP`. -/
def streamDecryptP (v : VecLevel) (t : Nat) (cp c : Callees) : Prog isa :=
  scrubAll v 0 2608 (Impl.Gcm.X86_64.Flag.onFlag t
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt cp))
    (withStackArgScratch 2584 1 (Impl.AesGcm.X86_64.streamDecrypt c)))

/-- `Spec.Gcm.openToPreparedApi`'s function on the key context alone, calling
`S` (`vg_aes_gcm_open_split`), as emitted. -/
def openToW (v : VecLevel) (S : Fn) : Prog isa :=
  scrubAll v 32 2776 (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit S))

/-- `vg_aes_gcm_open_to`'s code on prepared powers: in one pass from `thr`
bytes on by `fS` if `sel`, else by a copy and `fO`. -/
def openToCodeP (sel : Bool) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width) (fO fS : Fn) : Prog isa :=
  if sel then Impl.AesGcm.X86_64.OpenToSplit.openToSel Impl.AesGcm.X86_64.OpenToSplit.thr w fO fS
  else Impl.AesGcm.X86_64.OpenTo.openTo w fO

/-- `Spec.Gcm.openToPreparedApi`'s function, by the count `t` on the
prepared powers (`openToCodeP`) or on the key context (`openToW`'s), as
emitted. -/
def openToP (v : VecLevel) (t : Nat) (sel : Bool) (w : Impl.ChaCha20Poly1305.X86_64.SealGather.Width)
    (fO fS S : Fn) : Prog isa :=
  scrubAll v 32 2776 (Impl.Gcm.X86_64.Flag.onFlag t (openToCodeP sel w fO fS)
    (withStackArgScratch 2624 6 (Impl.AesGcm.X86_64.OpenToSplit.openToSplit S)))

end VG.Impl.AesGcm.X86_64.Fn
