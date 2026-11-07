module

public import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loops
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Loops
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ok
meta import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Stitch.Ctr

/-!
# AES-GCM-SIV's loops with VAES and VPCLMULQDQ meet `LoopsOk`

Untrusted: everything here is checked by Lean. `Impl.AesGcmSiv.X86_64Stitch.vaesLoops`:
their contracts (`dec_ok`, `hash_ok`, `ctr_ok`), the taint analysis of each,
and what the artifacts' frame needs of their code.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64.Stitch

open VG VG.X86_64
open VG.Impl.AesGcmSiv.X86_64Stitch
open VG.Impl.Gcm.X86_64.Stitch (aregs storesK pregs ordE)
open VG.Impl.Gcm.X86_64.Vpclmul (powers powers16 zero acc reduce combine)
open VG.Impl.Aes.X86_64.Vaes (aesK xorDataK)

theorem vaesLoops_ok : LoopsOk vaesLoops where
  dec hp hm := dec_ok hp hm
  hash hp := hash_ok hp
  ctr hp hm := ctr_ok hp hm
  decT := ⟨_, by taint_decide⟩
  hashT := ⟨_, by taint_decide⟩
  ctrT := ⟨_, by taint_decide⟩

theorem vaesLoops_code : LoopsCode vaesLoops := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [vaesLoops, Impl.AesGcmSiv.X86_64Stitch.dec, setup, setupG, setupC, first, batch, body, gA, gB, gq, ghLoad, ldR,
    lastG, storeCtr, storeY, ctrsR, Impl.AesGcmSiv.X86_64Stitch.hash, loadY, hbody, Impl.AesGcmSiv.X86_64Stitch.ctr, setupK, cbody,
    Impl.Gcm.X86_64.Pclmul.const, Code.allInstrs, Code.all, Code.x86_64Depth] <;>
  decide +kernel

end VG.Proof.AesGcmSiv.X86_64.Stitch
