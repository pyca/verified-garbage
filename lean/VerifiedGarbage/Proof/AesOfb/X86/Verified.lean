module
public import VerifiedGarbage.Impl.AesOfb.X86
public import VerifiedGarbage.Proof.AesOfb.Rounds
public import VerifiedGarbage.Proof.Aes.X86.BlocksVariant
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Proof.AesCbc.X86.Wiped

import VerifiedGarbage.Proof.AesCbc.X86.Verified
public import VerifiedGarbage.Proof.AesOfb.X86.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# AES-OFB on x86: `Verified`

Correctness and constant time (for any implementation `v` of the block
functions), from the loop AES-CBC's proofs share, a state satisfying the
precondition, and the shared contract of `Spec/Ofb/Contract.lean`, with 24
bytes of stack: each call of a block function pushes its five arguments and
the return address.

The whole-block code of `v` is `cryptCode v`: around its chain if it has one
(`Chain.of`), the loop that keeps the output block in a register and calls
nothing (`Impl.AesOfb.X86.cryptChain`, `Chained` in `Body.lean`), which needs
none of those 24 bytes; for any other implementation, `crypt` around its block
function. Both meet the same contract (`cryptCode_verified`).
-/

@[expose] public section

namespace VG.Proof.AesOfb.X86

open VG VG.X86 VG.Impl.AesOfb.X86
open VG.Impl.AesCbc.X86 (whole blkCall)
open VG.Proof.AesCbc.X86
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Impl.Aes.X86 (Chain)

theorem crypt_spSafe (v : BlocksImpl) : (crypt v.enc).all (fun i => !isa.writesSp i) = true := by
  simp only [crypt, whole, body, blkCall, Code.all, v.encSpSafe]
  decide +kernel

/-- The shared contract, from the code's own (`modeX86 ofbMode`). -/
theorem ofb_implies : (modeX86 ofbMode).Implies (Proof.AesOfb.roundsContract X86.abi 24) :=
    { pre := by sig_implies_pre [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, modeX86]
      -- `ofbMode.chain` counts the blocks, which are `n`.
      post := by
        intro s s' _ h
        sig_post [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, ofbMode]
        sig_reduce [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, ofbMode] at h
        sig_simp [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes, modeX86, ofbMode] [] at h
        rwa [VG.Proof.AesCbc.length_blocksAt] at h
      pub := by sig_implies_pub [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, modeX86]
      sat := by
        have a0 : arg sat 0 = 0x1000 := by decide
        have a1 : arg sat 1 = 10 := by decide
        have a2 : arg sat 2 = 0x2000 := by decide
        have a3 : arg sat 3 = 0x3000 := by decide
        have a4 : arg sat 4 = 0 := by decide
        have a5 : arg sat 5 = 0x4000 := by decide
        have e : argAddr sat 0 = 0x8004 := by decide
        have esp : sat.gpr .esp = 0x8000 := rfl
        sig_implies_sat [Proof.AesOfb.roundsContract, Spec.Ofb.aesSig, Spec.Cbc.aesSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes, modeX86] [a0, a1, a2, a3, a4, a5, e, esp] using sat }

theorem crypt_verified (v : BlocksImpl) :
    Verified X86.target (crypt v.enc) (Proof.AesOfb.roundsContract X86.abi 24) :=
  Verified.of_correct (fun _ hs => whole_wp (body_ok v) hs) (whole_ct (body_ok v) (body_ct v)) ofb_implies

/-! ## The code of each implementation -/

/-- The whole-block code for `v`: around its chain if it has one (`Chain.of`),
which keeps the output block in a register with no call; otherwise `crypt`
around its block function. -/
def cryptCode (v : BlocksImpl) : Prog isa :=
  Chain.choose v.enc.name cryptChain (crypt v.enc)

theorem cryptCode_some {v : BlocksImpl} {c : Chain} (h : Chain.of v.enc.name = some c) :
    cryptCode v = cryptChain c := Proof.Aes.X86.Chain.choose_some h _ _

theorem cryptCode_none {v : BlocksImpl} (h : Chain.of v.enc.name = none) : cryptCode v = crypt v.enc :=
  Proof.Aes.X86.Chain.choose_none h _ _

theorem cryptCode_cases (v : BlocksImpl) :
    (∃ c, Chain.of v.enc.name = some c ∧ cryptCode v = cryptChain c) ∨ cryptCode v = crypt v.enc :=
  Proof.Aes.X86.Chain.choose_cases _ _ _

/-- `cryptCode v` runs to the code's own contract. -/
theorem cryptCode_correct (v : BlocksImpl) (s : State) (hs : (modeX86 ofbMode).pre s) :
    ∃ t s', Exec isa (cryptCode v) s t s' ∧ abiPreserved s s' ∧ (modeX86 ofbMode).post s s' := by
  rcases cryptCode_cases v with ⟨c, h, e⟩ | e <;> rw [e]
  · exact Chained.correct h s hs
  · exact whole_wp (body_ok v) hs

theorem cryptCode_ct (v : BlocksImpl) :
    ConstantTime isa (modeX86 ofbMode).pre (modeX86 ofbMode).pub (cryptCode v) := by
  rcases cryptCode_cases v with ⟨c, h, e⟩ | e <;> rw [e]
  · exact Chained.ct h
  · exact whole_ct (body_ok v) (body_ct v)

theorem cryptCode_verified (v : BlocksImpl) :
    Verified X86.target (cryptCode v) (Proof.AesOfb.roundsContract X86.abi 24) :=
  Verified.of_correct (cryptCode_correct v) (cryptCode_ct v) ofb_implies

theorem cryptCode_spSafe (v : BlocksImpl) : (cryptCode v).all (fun i => !isa.writesSp i) = true := by
  rcases cryptCode_cases v with ⟨c, h, e⟩ | e <;> rw [e]
  · exact Chained.spSafe h
  · exact crypt_spSafe v

end VG.Proof.AesOfb.X86
