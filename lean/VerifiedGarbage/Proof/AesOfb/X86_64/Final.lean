module

public import VerifiedGarbage.Impl.AesOfb.X86_64.Final
public import VerifiedGarbage.Proof.AesOfb.Final
public import VerifiedGarbage.Proof.AesOfb.X86_64.Verified
public import VerifiedGarbage.Proof.AesCfb.X86_64.Final
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesOfb.X86_64.Body
import VerifiedGarbage.Proof.AesOfb.Spec
import VerifiedGarbage.Proof.AesCbc.Spec
import VerifiedGarbage.Proof.AesCbc.X86_64.CT
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipe

/-!
# AES-OFB of a message's last piece on x86-64

`cryptFinal_framed`: `vg_aes_ofb_final` (`Impl/AesOfb/X86_64/Final.lean`), for
any implementation `v` of the block functions (`BlocksImpl`), meets
`Proof.AesOfb.finalRoundsContract`, from which the shared contract follows
(`Proof.AesOfb.final_keyed`).

Its code is AES-CFB's final function around a call of the whole-block
AES-OFB function, so its proof is AES-CFB's (`Proof/AesCfb/X86_64/Final.lean`),
for OFB as a `Mode` (`ofbMode`): `final_wp` runs it, for any mode, to what it
leaves before restoring the registers (`Done`); `final_rel` gives its
constant time. `ofbFinalX86_64` is AES-CFB's code contract with OFB's
postcondition, which `final_post` gives from `Done` by
`Proof.AesOfb.cryptFinal_of`.
-/

@[expose] public section

namespace VG.Proof.AesOfb.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCfb.X86_64 (finalX86_64 FPre Done fW fR fIv fD fL fN fU fT fWk fIv0 fBlks final_wp final_ct
  finalSatState args_getD stackArgs_one noSp_of_all all_of_noSp finalFrameSat)
open VG.Proof.AesCbc.X86_64 (modeX86_64)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Impl.AesOfb.X86_64
open VG.Impl.AesCfb.X86_64 (final finalTail)

/-- The code's contract, with the arguments `(schedule = rdi, rounds = rsi,
iv = rdx, data = rcx, len = r8, scratch = r9, save = [rsp + 8])`: AES-CFB's
final functions' (`finalX86_64`), with the data and the block at `iv` as
`Spec.Ofb.CryptFinal` says, by AES with the key schedule it is given. -/
def ofbFinalX86_64 : Contract isa :=
  { finalX86_64 true with
    post := fun s s' => Spec.Ofb.CryptFinal (ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 16 s.mem s'.mem
      (s.gpr .rdx) (s.gpr .rcx) (s.gpr .r8).toNat }

/-- The contract the frame needs: the shared one, with `save`, 48 bytes, as
a seventh argument, and 16 bytes of stack (the return addresses of the
whole-block function and of the block function it calls). -/
abbrev finalScratchContract : Contract isa :=
  Sig.scratchContract X86_64.abi Spec.Ofb.aesFinalSig "save" .u64 6 (finalPre X86_64.abi.ptrBits)
    (finalPost X86_64.abi.ptrBits) false 16

theorem final_implies : ofbFinalX86_64.Implies finalScratchContract where
  pre := by
    intro s h
    sig_pre [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ofb.aesFinalSig, finalPre, finalPost, abi, argRegs, ofbFinalX86_64, finalX86_64, args_getD,
      stackArgs_one, List.append_eq] at h
    sig_pre [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ofb.aesFinalSig, finalPre, finalPost, abi, argRegs, ofbFinalX86_64, finalX86_64, args_getD,
      stackArgs_one, List.append_eq] at h
    sig_split h
    sig_reduce [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ofb.aesFinalSig, finalPre, finalPost, abi, argRegs, ofbFinalX86_64, finalX86_64, args_getD,
      stackArgs_one, List.append_eq]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
  post := by
    sig_implies_post [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ofb.aesFinalSig, finalPre, finalPost, abi, argRegs, ofbFinalX86_64, finalX86_64, args_getD,
      stackArgs_one, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ofb.aesFinalSig, finalPre, finalPost, abi, argRegs, ofbFinalX86_64, finalX86_64, args_getD,
      stackArgs_one, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    sig_split h
    rename_i h1 h2 h3 h4 h5 h6 h7
    exact ⟨h2, h3, h4, h5, h6, h7, h1, h⟩
  sat := by
    sig_implies_sat [finalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
      Spec.Ofb.aesFinalSig, finalPre, finalPost, abi, argRegs, ofbFinalX86_64, finalX86_64, args_getD,
      stackArgs_one, List.append_eq] [finalSatState, stackArg, stackArgAddr, Mem.readW, Mem.read]
      using finalSatState

/-- `Spec.Ofb.CryptFinal`, from what the function leaves. -/
theorem final_post {s₀ s₁ s' : State} (h : Done ofbMode s₀ s₁) (hm : s'.mem = s₁.mem) :
    ofbFinalX86_64.post s₀ s' := by
  show Spec.Ofb.CryptFinal (ciphAt s₀.mem (fW s₀) (fR s₀)) 16 s₀.mem s'.mem (fIv s₀) (fD s₀) (fL s₀)
  have e := AesCbc.length_blocksAt s₀.mem (fD s₀) (fN s₀)
  have hb := h.blocks
  have ht := h.tail
  have hi := h.iv
  rw [ofbMode_out] at hb
  rw [ofbMode_chain, e] at ht hi
  exact cryptFinal_of (aesWith_length _ _) (by rw [hm]; exact hb) (fun q hq => by rw [hm]; exact ht q hq)
    (by rw [hm]; exact hi)

theorem final_correct (v : BlocksImpl) (hmx : (cryptFinal v.enc v.suffix).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsp : NoSp (crypt v.enc)) (hd : (crypt v.enc).depth = 1) (s : State) (hs : ofbFinalX86_64.pre s) :
    ∃ t s', Exec isa (cryptFinal v.enc v.suffix) s t s' ∧ abiPreserved s s' ∧ ofbFinalX86_64.post s s' := by
  obtain ⟨t, s', he, hg, s₁, h₁, hm⟩ := final_wp (M := ofbMode) (crypt_correct v) hsp hd v (FPre.of (enc := true) hs)
  exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, final_post h₁ hm⟩

/-! ## The code's properties -/

theorem crypt_noSp (v : BlocksImpl) : NoSp (crypt v.enc) :=
  noSp_of_all (by
    simp only [crypt, Impl.AesCbc.X86_64.whole, body, Code.allInstrs, all_of_noSp v.encNosp]
    decide +kernel)

theorem crypt_depth (v : BlocksImpl) : (crypt v.enc).depth = 1 := by
  simp only [crypt, Impl.AesCbc.X86_64.whole, body, Code.depth, v.encDepth]
  decide

theorem cryptFinal_mx (v : BlocksImpl) :
    (cryptFinal v.enc v.suffix).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [cryptFinal, final, finalTail, Code.allInstrs, crypt_mx v, v.encMxcsr]
  decide +kernel

theorem cryptFinal_spSafe (v : BlocksImpl) :
    (cryptFinal v.enc v.suffix).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [cryptFinal, final, finalTail, Code.all, crypt_spSafe v, v.encSpSafe]
  decide +kernel

theorem cryptFinal_xdepth (v : BlocksImpl) : (cryptFinal v.enc v.suffix).x86_64Depth ≤ 16 := by
  simp only [cryptFinal, final, finalTail, crypt, Impl.AesCbc.X86_64.whole, body, Code.x86_64Depth,
    v.encNoStack]
  decide

/-! ## Verified -/

theorem cryptFinal_verified (v : BlocksImpl) :
    Verified X86_64.target (cryptFinal v.enc v.suffix) finalScratchContract :=
  Verified.of_correct (final_correct v (cryptFinal_mx v) (crypt_noSp v) (crypt_depth v))
    (final_ct (enc := true) (crypt_correct v) (AesCbc.X86_64.whole_ct (body_ok v) (body_ct v)) (crypt_noSp v)
      (crypt_depth v) v)
    final_implies

/-! ## With `save` on the stack

As AES-CFB's final functions, the code runs in a frame of 64 bytes
(`withStackArgScratchWiped`): the quadword standing for the return address,
`save`'s address, and `save`'s 48 bytes, which it zeroes before returning.
Its calls use 16 bytes below it, so 80 in all. -/

theorem frameSat_pre : ∃ s, (finalRoundsContract X86_64.abi 80).pre s := by
  implies_sat [finalRoundsContract, Spec.Ofb.aesFinalSig, finalPre, finalPost, X86_64.abi,
    X86_64.argRegs] [finalFrameSat, finalSatState] using finalFrameSat

theorem cryptFinal_framed (v : BlocksImpl) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackArgScratchWiped 64 0 6 (cryptFinal v.enc v.suffix))
      (finalRoundsContract X86_64.abi 80) :=
  X86_64.Verified.stackArgScratchWiped (sig := Spec.Ofb.aesFinalSig) (nm := "save") (e := .u64) (n := 6)
    (pre := finalPre X86_64.abi.ptrBits) (post := finalPost X86_64.abi.ptrBits) (wa := false)
    (stack := 16) (bytes := 64) (words := 6) (cryptFinal_verified v) (by decide) (by decide) (by decide)
    (cryptFinal_spSafe v) (cryptFinal_xdepth v) (by decide) (finalPre_local _) (finalPost_local _)
    (finalPost_localOut _) frameSat_pre

theorem cryptFinal_framed_spSafe (v : BlocksImpl) :
    (Impl.StackScratch.X86_64.withStackArgScratchWiped 64 0 6 (cryptFinal v.enc v.suffix)).all
      (fun i => !X86_64.isa.writesSp i) = true :=
  X86_64.withStackArgScratch_spSafe (by
    simp only [Code.all, cryptFinal_spSafe v, X86_64.wipeAt_spSafe, Bool.and_self])

end VG.Proof.AesOfb.X86_64
