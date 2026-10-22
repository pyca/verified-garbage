module

public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Sm4Gcm.Scratch

/-!
# SM4-GCM on ARMv7: the functions with their working space as an argument

The ARMv7 SM4-GCM functions keep their 768-byte working space in a frame of
their own (`Verified.stackScratch`, `Verified.regScratch`), around code
proved with the working space as a last argument: `initScratchContract`, …,
`openScratchContract` are the shared contracts with a 768-byte `scratch` (or
`work`) buffer appended, whatever it holds (`Proof/Sm4Gcm/Scratch.lean` has
x86-64's, with 2560 bytes).

The frames also hold a copy of the arguments passed on the stack, which needs
the postconditions to read the memory on entry only within the function's
buffers: `Proof/Sm4Gcm/Scratch.lean` proves it of all but
`vg_sm4_gcm_stream_finish`'s (`streamFinishPost_local`), and
`Proof/AesGcm/Scratch.lean` of `vg_sm4_gcm_stream_init`'s and
`vg_sm4_gcm_stream_aad`'s, which are AES-GCM's.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.Arm

open VG.Spec.Sm4.Gcm
open VG.Proof.AesGcm (bytesAt_congr ctxH_congr streamRepr_congr agree_of)
open VG.Proof.Sm4Gcm (ctxCiph_congr)

/-- `vg_sm4_gcm_init` with `scratch: *mut [u64; 96]`. -/
def initScratchSig : Sig where
  params := initSig.params ++ [("scratch", .array true .u64 96)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (post := fun key ctx _scratch => initPost A.ptrBits key ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_init` with `scratch: *mut [u64; 96]`. -/
def streamInitScratchSig : Sig where
  params := Spec.Gcm.streamInitSig.params ++ [("scratch", .array true .u64 96)]

/-- `Spec.Gcm.streamInitContract`, whatever `scratch` is. -/
def streamInitScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamInitScratchSig.contract A
    (post := fun ctx nonce nonceLen state _scratch =>
      Spec.Gcm.streamInitPost A.ptrBits ctx nonce nonceLen state)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_aad` with `scratch: *mut [u64; 96]`. -/
def streamAadScratchSig : Sig where
  params := Spec.Gcm.streamAadSig.params ++ [("scratch", .array true .u64 96)]

/-- `Spec.Gcm.streamAadContract`, whatever `scratch` is. -/
def streamAadScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamAadScratchSig.contract A
    (post := fun ctx state aadLen data len _scratch =>
      Spec.Gcm.streamAadPost A.ptrBits ctx state aadLen data len)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_encrypt` and `vg_sm4_gcm_stream_decrypt` with
`scratch: *mut [u64; 96]`. -/
def streamCryptScratchSig : Sig where
  params := streamCryptSig.params ++ [("scratch", .array true .u64 96)]

/-- `streamEncryptContract`, whatever `scratch` is. -/
def streamEncryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (post := fun ctx state aadLen textLen data len _scratch =>
      streamEncryptPost A.ptrBits ctx state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `streamDecryptContract`, whatever `scratch` is. -/
def streamDecryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamCryptScratchSig.contract A
    (post := fun ctx state aadLen textLen data len _scratch =>
      streamDecryptPost A.ptrBits ctx state aadLen textLen data len)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_finish` with `work: *mut [u64; 96]`. -/
def streamFinishScratchSig : Sig where
  params := streamFinishSig.params ++ [("work", .array true .u64 96)]

/-- `streamFinishContract`, whatever `work` is. -/
def streamFinishScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamFinishScratchSig.contract A
    (post := fun ctx state aadLen textLen tag _work =>
      streamFinishPost A.ptrBits ctx state aadLen textLen tag)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_stream_verify` with `work: *mut [u64; 96]`. -/
def streamVerifyScratchSig : Sig where
  params := streamVerifySig.params ++ [("work", .array true .u64 96)]
  ret := some .u32

/-- `streamVerifyContract`, whatever `work` is. -/
def streamVerifyScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  streamVerifyScratchSig.contract A
    (post := fun ctx state aadLen textLen tag tagLen _work =>
      streamVerifyPost A.ptrBits ctx state aadLen textLen tag tagLen)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_seal` with `work: *mut [u64; 96]`. -/
def sealScratchSig : Sig where
  params := sealSig.params ++ [("work", .array true .u64 96)]

/-- `sealContract`, whatever `work` is. -/
def sealScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealScratchSig.contract A
    (post := fun ctx nonce nonceLen aad aadLen data len tag _work =>
      sealPost A.ptrBits ctx nonce nonceLen aad aadLen data len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_sm4_gcm_open` with `work: *mut [u64; 96]`. -/
def openScratchSig : Sig where
  params := openSig.params ++ [("work", .array true .u64 96)]
  ret := some .u32

/-- `openContract`, whatever `work` is. -/
def openScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  openScratchSig.contract A
    (post := fun ctx nonce nonceLen aad aadLen data len tag tagLen _work =>
      openPost A.ptrBits ctx nonce nonceLen aad aadLen data len tag tagLen)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx nonce nonceLen aad aadLen data len tag tagLen _work =>
      openLeak A.ptrBits ctx nonce nonceLen aad aadLen data len tag tagLen)

/-! ## Locality -/

variable (pb : Nat)

theorem streamFinishPost_local : ∀ vs m₁ m₂ m' r, vs.length = (streamFinishSig.words pb).length →
    (∀ b ∈ Sig.bufs streamFinishSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (streamFinishSig.words pb) (streamFinishPost pb) vs m₁ m' r →
      Curry.apply (streamFinishSig.words pb) (streamFinishPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  obtain ⟨ctx, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 4) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  iterate 3
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  have hc := agree_of hb.1
  have hs := agree_of hb.2.1
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr] (streamFinishPost pb) _ m₁ m' r at h
  change Curry.apply [ArgWord.addr, ArgWord.addr, ArgWord.int 64, ArgWord.int 64,
    ArgWord.addr] (streamFinishPost pb) _ m₂ m' r
  dsimp only [Curry.apply, streamFinishPost, ArgWord.ofRaw] at h ⊢
  intro iv a c hr hl ht
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)]
  rw [ctxCiph_congr fun i hi => hc i (by omega), ctxH_congr fun i hi => hc i (by omega)] at hr
  exact h iv a c (streamRepr_congr (fun i hi => (hs i (by omega)).symm) hr) hl ht

end VG.Proof.Sm4Gcm.Arm
