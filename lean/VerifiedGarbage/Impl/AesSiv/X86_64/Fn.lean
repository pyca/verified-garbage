module

public import VerifiedGarbage.Impl.AesSiv.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Impl.Scrub.X86_64.Fn

/-! # AES-SIV on x86-64: the functions as emitted

`vg_aes_siv_init`, `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` over the
functions they call, each in a frame of the working space those need (none
for `…F`, 1480 bytes for `…S`, else all of it), then its cleanup
(`Impl.Scrub.X86_64.scrubAll v rb n`): every vector register at the level
`v` and every caller-saved register but the result's cleared, and its whole
frame wiped.
-/

@[expose] public section

namespace VG.Impl.AesSiv.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (VecLevel scrubAll)
open VG.Impl.Aes.X86_64 (Ctr32 ExpandKey)
open VG.Impl.StackScratch.X86_64 (withStackScratch withStackArgScratch)

def initF (v : VecLevel) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 0 104 (withStackScratch 88 .rcx (X86_64.initF .aesni c sfx))

def initS (v : VecLevel) (e : ExpandKey) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 0 1944 (withStackScratch 1928 .rcx (X86_64.initS e c sfx))

def init (v : VecLevel) (e : ExpandKey) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 0 2584 (withStackScratch 2568 .rcx (X86_64.init e c sfx))

def encryptF (v : VecLevel) (u : Impl.CmacAes.X86_64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 0 328 (withStackArgScratch 312 1 (X86_64.encrypt csImmF dOffF u c sfx))

def encryptS (v : VecLevel) (u : Impl.CmacAes.X86_64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 0 1976 (withStackArgScratch 1960 1 (X86_64.encrypt csImmS dOffS u c sfx))

def encrypt (v : VecLevel) (u : Impl.CmacAes.X86_64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 0 2616 (withStackArgScratch 2600 1 (X86_64.encrypt csImm dOff u c sfx))

def decryptF (v : VecLevel) (u : Impl.CmacAes.X86_64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 32 328 (withStackArgScratch 312 1 (X86_64.decrypt csImmF dOffF u c sfx))

def decryptS (v : VecLevel) (u : Impl.CmacAes.X86_64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 32 1976 (withStackArgScratch 1960 1 (X86_64.decrypt csImmS dOffS u c sfx))

def decrypt (v : VecLevel) (u : Impl.CmacAes.X86_64.Update) (c : Ctr32) (sfx : String) : Prog isa :=
  scrubAll v 32 2616 (withStackArgScratch 2600 1 (X86_64.decrypt csImm dOff u c sfx))

end VG.Impl.AesSiv.X86_64.Fn
