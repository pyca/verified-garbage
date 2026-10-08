import VerifiedGarbage.Proof.AesGcm.X86_64.StreamTo.Contract

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86-64: the contracts

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather`
keeps its working space in a frame of its own (`Verified.stackArgScratchL`),
around code proved with the working space as its last argument:
`sealGatherScratchContract` is the shared contract with a 184-byte `scratch`
buffer appended, whatever it holds, which the contract the proof is written
against, `sealGatherX86_64M`, implies (`Gather/Verified.lean`):
`(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, src = [rsp + 8], src_count = [rsp + 16], dst = [rsp + 24],
len = [rsp + 32], tag = [rsp + 40], work = [rsp + 48])`, for a key context
of kind `M` (`Stitch.CtxMode`). The code calls the streaming functions, the
deepest of which, `vg_aes_gcm_stream_encrypt_to`, uses 4856 bytes of stack,
with three arguments on the stack, so it uses the 4888 bytes below the stack
pointer (`stkG`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `vg_aes_gcm_seal_gather` with `scratch: *mut [u64; 23]`. -/
def sealGatherScratchSig : Sig where
  params := [("ctx", .array false .u64 32), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16), ("scratch", .array true .u64 23)]

/-- `sealGatherContract`, whatever `scratch` is. -/
def sealGatherScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      Spec.Gcm.sealGatherPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      Spec.Gcm.sealGatherPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_gcm_seal_gather_precomputed` with `scratch: *mut [u64; 23]`. -/
def sealGatherPrecomputedScratchSig : Sig where
  params := [("ctx", .array false .u64 128), ("rounds", .int .usize true),
    ("nonce", .slice false .u8 "nonce_len"), ("aad", .slice false .u8 "aad_len"),
    ("src", .slices .u8 "src_count"), ("dst", .slice true .u8 "len"),
    ("tag", .array true .u8 16), ("scratch", .array true .u64 23)]

/-- `sealGatherPrecomputedContract`, whatever `scratch` is. -/
def sealGatherPrecomputedScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherPrecomputedScratchSig.contract A
    (pre := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      Spec.Gcm.sealGatherPrecomputedPre A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (post := fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _scratch =>
      Spec.Gcm.sealGatherPost A.ptrBits ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag)
    (writeArgs := true) (stack := stack)

/-- The stack the code uses: the frame of the three arguments of
`vg_aes_gcm_stream_encrypt_to`, its return address and its 4856 bytes. -/
abbrev stkG (s : State) : Region := below (s.gpr .rsp) 4888

/-- The slices `src` lists. -/
abbrev slicesG (s : State) : List Region := Sig.listed 64 s.mem .u8 (arg s 0) (arg s 1).toNat

/-- What the code of `vg_aes_gcm_seal_gather` needs, for a key context of
kind `M`. -/
def sealGatherPreM (M : CtxMode) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, M.len⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let desc : Region := ⟨arg s 0, (arg s 1).toNat * 16⟩
  let dst : Region := ⟨arg s 2, (arg s 3).toNat⟩
  let tag : Region := ⟨arg s 4, 16⟩
  let scr : Region := ⟨arg s 5, 184⟩
  s.rd = [ctx, nonce, aad, desc] ++ slicesG s ++ [args s 6] ∧ s.wr = [dst, tag, scr] ∧
    ctx.Disjoint dst ∧ ctx.Disjoint tag ∧ ctx.Disjoint scr ∧
    nonce.Disjoint dst ∧ nonce.Disjoint tag ∧ nonce.Disjoint scr ∧
    aad.Disjoint dst ∧ aad.Disjoint tag ∧ aad.Disjoint scr ∧
    desc.Disjoint dst ∧ desc.Disjoint tag ∧ desc.Disjoint scr ∧
    (∀ r ∈ slicesG s, r.Disjoint dst ∧ r.Disjoint tag ∧ r.Disjoint scr) ∧
    dst.Disjoint tag ∧ dst.Disjoint scr ∧ tag.Disjoint scr ∧
    dst.Disjoint (args s 6) ∧ tag.Disjoint (args s 6) ∧ scr.Disjoint (args s 6) ∧
    (ret s).Disjoint dst ∧ (ret s).Disjoint tag ∧ (ret s).Disjoint scr ∧
    (stkG s).Disjoint ctx ∧ (stkG s).Disjoint nonce ∧ (stkG s).Disjoint aad ∧ (stkG s).Disjoint desc ∧
    (∀ r ∈ slicesG s, (stkG s).Disjoint r) ∧
    (stkG s).Disjoint dst ∧ (stkG s).Disjoint tag ∧ (stkG s).Disjoint scr ∧
    (s.gpr .rdi).toNat + M.len ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat * 16 ≤ 2 ^ 64 ∧
    (∀ r ∈ slicesG s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 64 ∧ (arg s 4).toNat + 16 ≤ 2 ^ 64 ∧
    (arg s 5).toNat + 184 ≤ 2 ^ 64 ∧
    4888 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64 ∧ rounds s ∧
    gatheredLen 64 s.mem (arg s 0) (arg s 1).toNat = (arg s 3).toNat ∧ M.ok s.mem (s.gpr .rdi)

/-- What two runs agree on: the arguments but the scratch's contents, and the
descriptors. -/
def sealGatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧
    arg s₁ 3 = arg s₂ 3 ∧ arg s₁ 4 = arg s₂ 4 ∧ arg s₁ 5 = arg s₂ 5 ∧
    ∀ i < (arg s₁ 1).toNat * 16, s₁.mem (arg s₁ 0 + BitVec.ofNat 64 i) = s₂.mem (arg s₁ 0 + BitVec.ofNat 64 i)

/-- What `vg_aes_gcm_seal_gather` leaves: `sealGatherPost`. -/
def sealGatherPostG (s s' : State) : Prop :=
  encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) 16
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (gathered 64 s.mem (arg s 0) (arg s 1).toNat)
      (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
    (bytesAt s'.mem (arg s 2) (arg s 3).toNat, bytesAt s'.mem (arg s 4) 16)

/-- `vg_aes_gcm_seal_gather`, for a key context of kind `M`. -/
def sealGatherX86_64M (M : CtxMode) : Contract isa where
  pre := sealGatherPreM M
  post := sealGatherPostG
  pub := sealGatherPub

end VG.Proof.AesGcm
