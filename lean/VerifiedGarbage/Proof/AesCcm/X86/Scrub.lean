module

public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesCcm.X86.Frame
public import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
public import VerifiedGarbage.Spec.Ccm.Contract
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.AesCcm.X86
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesCcm.X86.Frame
meta import VerifiedGarbage.Proof.CmacAes.Stream.X86.Frame
meta import VerifiedGarbage.Spec.Ccm.Contract
meta import VerifiedGarbage.Proof.Aes.ScrubLocal
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.ScrubProved
meta import VerifiedGarbage.Impl.AesCcm.X86

/-!
# AES-CCM on x86 (32-bit), without secret residue

`vg_aes_ccm_seal` and `vg_aes_ccm_open` read the memory on return only
within the data and the tag (`sealOut`, `openOut`), as on PPC64LE
(`Proof/AesCcm/PPC64LE/Scrub.lean`): what the scrub of their frames and
calls needs (`X86.Scrub.PostOut`).

Each as emitted (`Impl.AesCcm.X86.Fn`) zeroes its 2668 bytes of stack below
`esp`, the working space among them, and clears the registers, and returns
without secret residue (`X86.Scrub.verifiedScrubbedAll`: `seal_scrubbed`,
`open_scrubbed`). What that needs of the code (`scrubFSide`) holds
whatever the implementation of AES (`seal_scrub`, `open_scrub`): from CCM's
code with a stub, whose code is `.block []`, which the kernel evaluates once
for each way `vg_cmac_aes_update` chains (`Impl.CmacAes.X86.hardware`:
`seal_side`, `sealNi_side`, …), the implementation's own facts
(`Ctr32Impl.scrub`, its stack), and `Fill`, which `fill_calls` proves by
walking only CCM's code.
-/

@[expose] public section

namespace VG.Proof.AesCcm.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

/-- A length argument, which the contract reads as its low 32 bits, is at
most the bytes of the buffer `Sig.bufs` gives it. -/
private theorem len_le1 (x : BitVec 64) : (x.setWidth 32).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_le _ _

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ccm.sealContract abi stack) (Spec.Ccm.sealSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ccm.sealPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ccm.sealPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of0 hb.2.2.2.1 (len_le1 _), bytesAt_of0 hb.2.2.2.2 (len_le1 _)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ccm.openContract abi stack) (Spec.Ccm.openSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ccm.openPost 32) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr,
        ArgWord.int 32, ArgWord.addr, ArgWord.int 32, ArgWord.addr, ArgWord.int 32]
        (Spec.Ccm.openPost 32) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 _)]
      exact h key hk

/-! ## What the scrub needs of the code -/

open Impl.StackScratch.X86 (withStackScratch)
open Proof.Aes.X86 (Ctr32Impl)

/-- AES in counter mode with no code, by a name that chooses the chaining
of `vg_cmac_aes_update` by calls (`Impl.CmacAes.X86.hardware`). -/
def stubCtr : Impl.Aes.X86.Ctr32 := ⟨"", .block []⟩

/-- `stubCtr` by the name that chooses the chaining with AES-NI. -/
def stubCtrNi : Impl.Aes.X86.Ctr32 := ⟨"vg_aes_ctr32_to_aesni", .block []⟩

-- CCM's own code, with the stubs, as literals for the kernel's evaluation.
materialize_code sealStub := withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» stubCtr "")
materialize_code sealStubNi := withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» stubCtrNi "")
materialize_code openStub := withStackScratch 2608 10 (Impl.AesCcm.X86.«open» stubCtr "")
materialize_code openStubNi := withStackScratch 2608 10 (Impl.AesCcm.X86.«open» stubCtrNi "")

theorem seal_side : scrubFSide (withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» stubCtr "")) [] 2668 = true := by
  lit_decide

theorem sealNi_side :
    scrubFSide (withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» stubCtrNi "")) [] 2668 = true := by
  lit_decide

theorem open_side : scrubFSide (withStackScratch 2608 10 (Impl.AesCcm.X86.«open» stubCtr "")) [] 2668 = true := by
  lit_decide

theorem openNi_side :
    scrubFSide (withStackScratch 2608 10 (Impl.AesCcm.X86.«open» stubCtrNi "")) [] 2668 = true := by
  lit_decide

theorem seal_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : ¬Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» stubCtr ""))
      (withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» c sfx)) := by
  fill_calls

theorem sealNi_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» stubCtrNi ""))
      (withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» c sfx)) := by
  fill_calls

theorem open_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : ¬Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2608 10 (Impl.AesCcm.X86.«open» stubCtr ""))
      (withStackScratch 2608 10 (Impl.AesCcm.X86.«open» c sfx)) := by
  fill_calls

theorem openNi_fill (c : Impl.Aes.X86.Ctr32) (sfx : String) (hc : calleeSide c.code 0 = true)
    (h : Impl.CmacAes.X86.hardware c = true) :
    Fill 0 (withStackScratch 2608 10 (Impl.AesCcm.X86.«open» stubCtrNi ""))
      (withStackScratch 2608 10 (Impl.AesCcm.X86.«open» c sfx)) := by
  fill_calls

/-- `scrubFSide` of `vg_aes_ccm_seal`, whatever the implementation of AES. -/
theorem seal_scrub (v : Ctr32Impl) :
    scrubFSide (withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» v.callee v.suffix)) [] 2668 = true := by
  by_cases h : Impl.CmacAes.X86.hardware v.callee = true
  · exact scrubFSide_of_fill (sealNi_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) sealNi_side
  · exact scrubFSide_of_fill (seal_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) seal_side

/-- `scrubFSide` of `vg_aes_ccm_open`, whatever the implementation of AES. -/
theorem open_scrub (v : Ctr32Impl) :
    scrubFSide (withStackScratch 2608 10 (Impl.AesCcm.X86.«open» v.callee v.suffix)) [] 2668 = true := by
  by_cases h : Impl.CmacAes.X86.hardware v.callee = true
  · exact scrubFSide_of_fill (openNi_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) openNi_side
  · exact scrubFSide_of_fill (open_fill _ _ (calleeSide_of_eq v.stack v.scrub) h) open_side

/-! ## The functions as emitted -/

/-- `vg_aes_ccm_seal` over `v` as emitted (`Impl.AesCcm.X86.Fn.«seal»`)
meets its contract in constant time and returns without secret residue. -/
theorem seal_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.AesCcm.X86.Fn.«seal» v.callee v.suffix)
      (Spec.Ccm.sealContract X86.abi 2668) 0 :=
  verifiedScrubbedAll (api := Spec.Ccm.sealApi) {
      suffix := v.suffix
      code := withStackScratch 2608 10 (Impl.AesCcm.X86.«seal» v.callee v.suffix)
      verified := Proof.AesCcm.seal_keyed (seal_framed v)
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (seal_spSafe v) }
    (sealOut _) (W := 2668) (hs := seal_scrub v)

/-- `vg_aes_ccm_open` over `v` as emitted (`Impl.AesCcm.X86.Fn.«open»`)
meets its contract in constant time and returns without secret residue. -/
theorem open_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed X86.target (Impl.AesCcm.X86.Fn.«open» v.callee v.suffix)
      (Spec.Ccm.openContract X86.abi 2668) 32 :=
  verifiedScrubbedAll (api := Spec.Ccm.openApi) {
      suffix := v.suffix
      code := withStackScratch 2608 10 (Impl.AesCcm.X86.«open» v.callee v.suffix)
      verified := Proof.AesCcm.open_keyed (open_framed v)
      spSafe := Proof.CmacAes.Stream.X86.withStackScratch_spSafe (open_spSafe v) }
    (openOut _) (W := 2668) (hs := open_scrub v)

/-- `Impl.AesCcm.X86.Fn.«seal»` writes `esp` only in its frames and calls. -/
theorem seal_fnSpSafe (v : Ctr32Impl) :
    (Impl.AesCcm.X86.Fn.«seal» v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (seal_spSafe v))

/-- `Impl.AesCcm.X86.Fn.«open»` writes `esp` only in its frames and calls. -/
theorem open_fnSpSafe (v : Ctr32Impl) :
    (Impl.AesCcm.X86.Fn.«open» v.callee v.suffix).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.CmacAes.Stream.X86.withStackScratch_spSafe (open_spSafe v))

end VG.Proof.AesCcm.X86.Scrub
