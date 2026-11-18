module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Gather.Fn
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.AesGcm.RISCV64.SealGather
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
import VerifiedGarbage.Proof.AesGcm.RISCV64.Gather.CT
import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubPre
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Verified
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.AesGcm.Scratch
import VerifiedGarbage.Proof.Framework.Omega

/-!
# AES-GCM encryption out of place, from a list of slices, RISC-V: `Verified`

Untrusted: everything here is checked by Lean. The shared contract of
`vg_aes_gcm_seal_gather`, with the 4640 bytes of stack below the stack
pointer that its frame and its call use (`Proof.AesGcm.sealGatherRoundsContract`),
implies the one the proof is written against (`gatherRISCV64`,
`gather_implies`), and so the code, calling `vg_aes_gcm_seal` by its shared
contract (`seal_framed`), is `Verified` against it (`sealGather_verified`).
As on PPC64LE (`Proof/AesGcm/PPC64LE/GatherSplit/Contract.lean`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.RISCV64.Gather

open VG VG.RISCV64 VG.Impl.AesGcm.RISCV64.SealGather
open VG.Proof.ChaCha20Poly1305.RISCV64.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem stackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] := rfl

theorem gatherPre_of_spec {s : State} (h : (Proof.AesGcm.sealGatherRoundsContract RISCV64.abi 4640).pre s) :
    gatherPre s := by
  sig_pre [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, RISCV64.abi,
    RISCV64.argRegs, stackArgs_three, List.append_eq] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or,
    List.cons_append, Sig.pairFacts, Bool.or_self] at h
  rw [pairFacts_ro _ (by simp)] at h
  obtain ⟨al, w₁, w₂, rd, wr, ⟨cd, ct, nd, nt, ad, at_, dt, dds, ⟨dl, da⟩, tds, ⟨tl, ta⟩, -⟩,
    bc, bn, ba, bd, bt, ⟨bds, bl, barg⟩, oc, on, oa, od, ot, ⟨ods, ol⟩, hR, hg, ca⟩ := h
  exact ⟨by rw [rd]; simp, wr, cd, ct, nd, nt, ad, at_, dds.symm, tds.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩, dt, da, ta, bc, bn, ba, bds, bl, barg, bd, bt, oc, on, oa,
    ods, ol, od, ot, al, w₁, w₂, hR, hg, ca⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Proof.AesGcm.sealGatherRoundsContract RISCV64.abi 4640).post s s' := by
  sig_post [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Proof.AesGcm.sealGatherRoundsPost, RISCV64.abi,
    RISCV64.argRegs, stackArgs_three, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State} (hp : (Proof.AesGcm.sealGatherRoundsContract RISCV64.abi 4640).pub s₁ s₂) :
    gatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, RISCV64.abi,
    RISCV64.argRegs, stackArgs_three, List.append_eq] at hp
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, q9, q10, a0, a1, a2, hd⟩ := hp
  exact ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, a1, a2, hd⟩

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather`: no
slices, nonce, additional data or text; the tag at `0x5000`, its address
the third stack argument, at `sp + 16`. -/
def gatherSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9011 then 0x50 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherSat_pre : ∃ s, (Proof.AesGcm.sealGatherRoundsContract RISCV64.abi 4640).pre s := by
  sig_implies_sat [Proof.AesGcm.sealGatherRoundsContract, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, RISCV64.abi,
    RISCV64.argRegs, stackArgs_three, List.append_eq]
    [gatherSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using gatherSat

theorem gather_implies : gatherRISCV64.Implies (Proof.AesGcm.sealGatherRoundsContract RISCV64.abi 4640) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherSat_pre⟩

theorem sealGather_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : gatherRISCV64.pre s) :
    ∃ t s', Exec isa sealGather s t s' ∧ abiPreserved s s' ∧ gatherRISCV64.post s s' :=
  sealGather_wp seal_framed.1 hs

theorem sealGather_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target sealGather (Proof.AesGcm.sealGatherRoundsContract RISCV64.abi 4640) :=
  Verified.of_correct (k := gatherRISCV64) sealGather_correct (sealGather_ct seal_framed.1 seal_framed.2.1)
    gather_implies

end VG.Proof.AesGcm.RISCV64.Gather

/-! ## AES-GCM on RISC-V, without secret residue

`vg_aes_gcm_init`, its streaming functions, `vg_aes_gcm_seal`,
`vg_aes_gcm_open`, `vg_aes_gcm_seal_gather` and `vg_aes_gcm_open_to`, each
followed by `Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.withScrub`),
which clears the caller-saved registers and the stack its frames used, the
working space of its AES and GHASH with it. Their postconditions read the
memory on return only within their buffers (`RISCV64.Scrub.PostOut`), as on
x86-64 (`Proof/AesGcm/X86_64/Scrub.lean`, `Proof/AesGcm/X86_64/Leaves.lean`).
`vg_aes_gcm_seal_gather` calls `vg_aes_gcm_seal`'s code as an internal
function of its own, `vg_aes_gcm_seal_core`.
-/

namespace VG.Proof.AesGcm.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.AesGcm.RISCV64

/-! ## Postconditions -/

theorem initOut (stack : Nat) :
    PostOut (Spec.Gcm.initContract RISCV64.abi stack) (Spec.Gcm.initSig.retBits 64) :=
  postOut_of_local_pre fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [k, ln, ctx], _ =>
      simp only [Spec.Gcm.initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      change Spec.Gcm.KeyRepr m₁ ctx _ at h
      change Spec.Gcm.KeyRepr m₂ ctx _
      change _ ∨ _ at hpre
      obtain ⟨h1, h2⟩ := h
      refine ⟨?_, ?_⟩
      · rw [bytesAt_of0 hb.2 ?_]
        · exact h1
        · simp only [Spec.Aes.bytesAt, List.length_map, List.length_range, Spec.Aes.rounds, Elem.size]
          rcases hpre with h | h | h <;> rw [h] <;> decide
      · simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt] at h2 ⊢
        rw [show (240 : BitVec 64) = BitVec.ofNat 64 240 from rfl] at h2 ⊢
        rw [bytesAt_of hb.2 (by decide)]
        exact h2

theorem streamInitOut (stack : Nat) :
    PostOut (Spec.Gcm.streamInitContract RISCV64.abi stack) (Spec.Gcm.streamInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, np, nl, st], _ =>
      simp only [Spec.Gcm.streamInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size] at hb
      change ∀ ciph, Spec.Gcm.StreamRepr m₁ st ciph _ _ [] [] at h
      change ∀ ciph, Spec.Gcm.StreamRepr m₂ st ciph _ _ [] []
      exact fun ciph => Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.2) (h ciph)

theorem streamAadOut (stack : Nat) :
    PostOut (Spec.Gcm.streamAadContract RISCV64.abi stack) (Spec.Gcm.streamAadSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, st, al, d, ln], _ =>
      simp only [Spec.Gcm.streamAadSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size] at hb
      change ∀ ciph iv a, Spec.Gcm.StreamRepr m st ciph _ iv a [] → _ → Spec.Gcm.StreamRepr m₁ st ciph _ iv _ [] at h
      change ∀ ciph iv a, Spec.Gcm.StreamRepr m st ciph _ iv a [] → _ → Spec.Gcm.StreamRepr m₂ st ciph _ iv _ []
      exact fun ciph iv a hr hl => Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) (h ciph iv a hr hl)

theorem streamFinishOut (stack : Nat) :
    PostOut (Spec.Gcm.streamFinishContract RISCV64.abi stack) (Spec.Gcm.streamFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag], _ =>
      simp only [Spec.Gcm.streamFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, Elem.size] at hb
      intro key hk _ _ iv a c hr hA hT
      show Spec.Aes.bytesAt m₂ tag 16 = _
      rw [bytesAt_of0 hb.2.2 (by decide)]
      exact h key hk iv a c hr hA hT

theorem streamVerifyOut (stack : Nat) :
    PostOut (Spec.Gcm.streamVerifyContract RISCV64.abi stack) (Spec.Gcm.streamVerifySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen _ h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, tag, tagLen], _ => exact h

theorem sealOut (stack : Nat) :
    PostOut (Spec.Gcm.sealContract RISCV64.abi stack) (Spec.Gcm.sealSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag], _ =>
      simp only [Spec.Gcm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      show _ = (Spec.Aes.bytesAt m₂ data len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [bytesAt_of0 hb.2.2.2.1 (by omega_arith), bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h key hk

theorem openOut (stack : Nat) :
    PostOut (Spec.Gcm.openContract RISCV64.abi stack) (Spec.Gcm.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, data, len, tag, tl], _ =>
      simp only [Spec.Gcm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      show (match Spec.Gcm.openResult (Spec.Gcm.aes key) (Spec.Gcm.aes key 0) tl.toNat
          (Spec.Aes.bytesAt m nonce nl.toNat) (Spec.Aes.bytesAt m data len.toNat)
          (Spec.Aes.bytesAt m aad al.toNat) (Spec.Aes.bytesAt m tag tl.toNat) with
        | some pt => r = 1 ∧ Spec.Aes.bytesAt m₂ data len.toNat = pt
        | none => r = 0 ∧ Spec.Aes.bytesAt m₂ data len.toNat = Spec.Aes.bytesAt m data len.toNat)
      rw [bytesAt_of0 hb.2.2.2.1 (by omega_arith)]
      exact h key hk

theorem streamEncryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamEncryptContract RISCV64.abi stack) (Spec.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      dsimp only
      intro iv a p hr hA hT
      obtain ⟨h1, h2⟩ := h key hk iv a p hr hA hT
      refine ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h1, ?_⟩
      show Spec.Aes.bytesAt m₂ data len.toNat = _
      rw [bytesAt_of0 hb.2.2 (by omega_arith)]
      exact h2

theorem streamDecryptOut (stack : Nat) :
    PostOut (Spec.Gcm.streamDecryptContract RISCV64.abi stack) (Spec.Gcm.streamCryptSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, st, al, tl, data, len], _ =>
      simp only [Spec.Gcm.streamCryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk
      dsimp only
      intro iv a c hr hA hT
      obtain ⟨h1, h2⟩ := h key hk iv a c hr hA hT
      refine ⟨Proof.AesGcm.streamRepr_congr (Proof.AesGcm.agree_of hb.2.1) h1, ?_⟩
      show Spec.Aes.bytesAt m₂ data len.toNat = _
      rw [bytesAt_of0 hb.2.2 (by omega_arith)]
      exact h2

theorem openToOut (stack : Nat) :
    PostOut (Spec.Gcm.openToContract RISCV64.abi stack) (Spec.Gcm.openToSig.retBits 64) :=
  postOut_of_local_pre fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, len, dst, dl, tag, tl], _ =>
      simp only [Spec.Gcm.openToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      have hdl : dl.toNat = len.toNat := hpre.2
      intro key hk
      show (match Spec.Gcm.openResult (Spec.Gcm.aes key) (Spec.Gcm.aes key 0) tl.toNat
          (Spec.Aes.bytesAt m nonce nl.toNat) (Spec.Aes.bytesAt m src len.toNat)
          (Spec.Aes.bytesAt m aad al.toNat) (Spec.Aes.bytesAt m tag tl.toNat) with
        | some pt => r = 1 ∧ Spec.Aes.bytesAt m₂ dst len.toNat = pt
        | none => r = 0 ∧ Spec.Aes.bytesAt m₂ dst len.toNat = List.replicate len.toNat 0)
      rw [bytesAt_of0 hb.2.2.2.2.1 (by omega_arith)]
      exact h key hk

theorem sealGatherOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherContract RISCV64.abi stack)
      (Spec.Gcm.sealGatherSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [ctx, rounds, nonce, nl, aad, al, src, sc, dst, len, tag], _ =>
      simp only [Spec.Gcm.sealGatherSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size] at hb
      intro key hk hg
      show _ = (Spec.Aes.bytesAt m₂ dst len.toNat, Spec.Aes.bytesAt m₂ tag 16)
      rw [bytesAt_of0 hb.2.2.2.1 (by omega_arith), bytesAt_of0 hb.2.2.2.2 (by decide)]
      exact h key hk hg

/-! ## The registrations -/

variable [Gcm.RISCV64.GhashLaw]

/-- `Spec.Gcm.initApi`. -/
def initReg : Registration Spec.Gcm.initApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init
      verified := init_framed }
    (initOut _)

/-- `Spec.Gcm.streamInitApi`. -/
def streamInitReg : Registration Spec.Gcm.streamInitApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a4 Impl.AesGcm.RISCV64.streamInit
      verified := streamInit_framed }
    (streamInitOut _)

/-- `Spec.Gcm.streamAadApi`. -/
def streamAadReg : Registration Spec.Gcm.streamAadApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a5 Impl.AesGcm.RISCV64.streamAad
      verified := streamAad_framed }
    (streamAadOut _)

/-- `Spec.Gcm.streamEncryptApi`. -/
def streamEncryptReg : Registration Spec.Gcm.streamEncryptApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 Impl.AesGcm.RISCV64.streamEncrypt
      verified := Proof.AesGcm.streamEncrypt_keyed streamEncrypt_framed }
    (streamEncryptOut _)

/-- `Spec.Gcm.streamDecryptApi`. -/
def streamDecryptReg : Registration Spec.Gcm.streamDecryptApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 Impl.AesGcm.RISCV64.streamDecrypt
      verified := Proof.AesGcm.streamDecrypt_keyed streamDecrypt_framed }
    (streamDecryptOut _)

/-- `Spec.Gcm.streamFinishApi`. -/
def streamFinishReg : Registration Spec.Gcm.streamFinishApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a6 Impl.AesGcm.RISCV64.streamFinish
      verified := Proof.AesGcm.streamFinish_keyed streamFinish_framed }
    (streamFinishOut _)

/-- `Spec.Gcm.streamVerifyApi`. -/
def streamVerifyReg : Registration Spec.Gcm.streamVerifyApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a7 Impl.AesGcm.RISCV64.streamVerify
      verified := Proof.AesGcm.streamVerify_keyed streamVerify_framed }
    (streamVerifyOut _)

/-- `Spec.Gcm.sealApi`. -/
def sealReg : Registration Spec.Gcm.sealApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2576 1 Impl.AesGcm.RISCV64.«seal»
      verified := Proof.AesGcm.seal_keyed seal_framed }
    (sealOut _)

/-- `Spec.Gcm.openApi`. -/
def openReg : Registration Spec.Gcm.openApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesGcm.RISCV64.«open»
      verified := Proof.AesGcm.open_keyed open_framed }
    (openOut _)

/-- `Spec.Gcm.sealGatherApi`. -/
def sealGatherReg : Registration Spec.Gcm.sealGatherApi RISCV64.target :=
  withScrub {
      code := Impl.AesGcm.RISCV64.SealGather.sealGather
      verified := Proof.AesGcm.sealGather_keyed Gather.sealGather_verified }
    (sealGatherOut _)

/-- `Spec.Gcm.openToApi`. -/
def openToReg : Registration Spec.Gcm.openToApi RISCV64.target :=
  withScrub {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2608 4 Impl.AesGcm.RISCV64.OpenTo.openTo
      verified := Proof.AesGcm.openTo_keyed OpenTo.openTo_framed }
    (openToOut _)

end VG.Proof.AesGcm.RISCV64.Scrub
