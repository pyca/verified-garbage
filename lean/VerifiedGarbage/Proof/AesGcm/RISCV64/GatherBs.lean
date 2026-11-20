module

public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.Bitsliced
public import VerifiedGarbage.Proof.Gather.RISCV64.Loop
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Gcm.Bitsliced
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Impl.AesGcm.RISCV64.SealGather
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.AesGcm.RISCV64.Fn
import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
import VerifiedGarbage.Proof.AesGcm.CtxFrame
import VerifiedGarbage.Proof.AesGcm.ScratchGather
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
meta import VerifiedGarbage.Proof.AesGcm.Rounds
meta import VerifiedGarbage.Proof.AesGcm.Bitsliced
meta import VerifiedGarbage.Proof.Gather.RISCV64.Loop
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Spec.Gcm.Bitsliced
meta import VerifiedGarbage.Spec.Gcm.OutOfPlace
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Impl.AesGcm.RISCV64.SealGather
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Ghash
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubSel
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
meta import VerifiedGarbage.Proof.AesGcm.CtxFrame
meta import VerifiedGarbage.Proof.AesGcm.ScratchGather
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Gcm.SealGather
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Gather.Verified
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.CallWipe
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Call
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-!
# AES-GCM encryption out of place, from a list of slices, reading the key's bitsliced form: RISC-V

Untrusted: everything here is checked by Lean. `vg_aes_gcm_seal_gather_bitsliced`
(`Impl/AesGcm/RISCV64/SealGather.lean`, `sealGatherBs`) is
`vg_aes_gcm_seal_gather` of the other targets, with the buffer `bk` of the
key context's bitsliced form as its fourth stack argument, and a call
of `vg_aes_gcm_seal_bitsliced`'s code (`OneBs.lean`), without the clearing
its registration ends with, as the internal function
`vg_aes_gcm_seal_bitsliced_core`, by its shared contract
(`Proof.AesGcm.sealBitslicedRoundsContract`, with 4640 bytes of stack).

With `Bs` the base of the 4672 bytes of stack below the stack pointer
(`sp = Bs + 4672`), it allocates its frame of 32 bytes at `Bs + 4640`
(`allocd`): our return address at `Bs + 4656`, and the call's stack
arguments `tag` and `bk`, from our stack arguments above the frame, at
`Bs + 4640` and `Bs + 4648` (`entered_wp`); gathers the slices to `dst`
(`gathered_wp`); calls `vg_aes_gcm_seal_bitsliced` on them in place
(`called_wp`), whose frame is in the 4640 bytes below ours, so that the
return address and `bk`'s bytes and the key context come back from it, and
`bk` still holds the context's bitsliced form when it is called
(`ctxSlicedRepr_congr`); and loads the return address back (`restored_ok`).

* **Correctness** (`sealGatherBs_wp`), **constant time** (`sealGatherBs_ct`,
  as `Gather/CT.lean`'s, `RelCT.alloc` for the frame), and `Verified`
  against the shared contract with 4672 bytes of stack
  (`sealGatherBs_verified`).
* **No secret residue:** `sealGatherBs_scrubbed`, by
  `verifiedScrubbedSelT`, as ChaCha20-Poly1305's `seal_gather`
  (`Proof/ChaCha20Poly1305/RISCV64/Scrub.lean`).
-/

@[expose] public section

/-! ## The contract the proof is written against -/

namespace VG.Proof.AesGcm

open VG.Spec.Gcm

/-- `sealGatherBitslicedPost` for `rounds` of 10, 12 or 14, in terms of the
key context: `sealGatherRoundsPost`. -/
def sealGatherBitslicedRoundsPost (pb : Nat) : sealGatherBitslicedSig.Post pb :=
  fun ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag _bk =>
    sealGatherRoundsPost pb ctx rounds nonce nonceLen aad aadLen src srcCount dst len tag

/-- `sealGatherBitslicedPre` and `sealGatherBitslicedRoundsPost`. -/
def sealGatherBitslicedRoundsContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  sealGatherBitslicedSig.contract A (pre := sealGatherBitslicedPre A.ptrBits)
    (post := sealGatherBitslicedRoundsPost A.ptrBits) (writeArgs := true) (stack := stack)

/-- `Spec.Gcm.sealGatherBitslicedContract` from `sealGatherBitslicedRoundsContract`. -/
theorem sealGatherBitsliced_keyed {T : Target} {c : Prog T.isa} {A : Abi T.isa} {stack : Nat}
    (h : Verified T c (sealGatherBitslicedRoundsContract A stack)) :
    Verified T c (Spec.Gcm.sealGatherBitslicedContract A stack) :=
  h.post_mono fun ctx rounds n nl a al s sc d l t _ => sealGatherPost_imp _ ctx rounds n nl a al s sc d l t

/-- `seal_gather_bitsliced`'s postcondition reads the memory on return only
within `dst` and `tag`. -/
theorem sealGatherBitslicedPost_out (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (sealGatherBitslicedSig.words pb).length →
    (∀ b ∈ Sig.bufs sealGatherBitslicedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (sealGatherBitslicedSig.words pb) (sealGatherBitslicedPost pb) vs m m₁ r →
      Curry.apply (sealGatherBitslicedSig.words pb) (sealGatherBitslicedPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hlen
  replace hlen := Nat.succ.inj hlen
  iterate 7
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
  obtain ⟨dst, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨tag, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [sealGatherBitslicedSig, sealGatherSig, bitslicedParam, List.cons_append, List.nil_append, Sig.bufs,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr]
    (sealGatherBitslicedPost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb,
    ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr]
    (sealGatherBitslicedPost pb) _ m m₂ r
  dsimp only [Curry.apply, sealGatherBitslicedPost, sealGatherPost, ArgWord.ofRaw] at h ⊢
  intro key hk hg
  have := Nat.mod_le len.toNat (2 ^ pb)
  rw [h key hk hg, bytesAt_congr (m₁ := m₁) (m₂ := m₂) (p := dst) (n := (len.setWidth pb).toNat) fun i hi =>
      agree_of hb.2.2.2.1 i (by rw [BitVec.toNat_setWidth] at hi; omega_using [this, hi]),
    bytesAt_congr (m₁ := m₁) (m₂ := m₂) (p := tag) (n := 16) fun i hi =>
      agree_of hb.2.2.2.2.1 i (by omega_using [hi])]

end VG.Proof.AesGcm

namespace VG.Proof.AesGcm.RISCV64.GatherBs

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesGcm.RISCV64.SealGather VG.WriteBytes
open VG.Impl.AesGcm.RISCV64 (mov)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen CtxSlicedRepr)
open VG.Proof.Gather.RISCV64 (GatherPre gather_wp gatherRegs)

/-! ## The arguments and the layout -/

theorem covers_mem {rs rs' : List Region} (h : ∀ r ∈ rs, r ∈ rs') : Covers rs rs' :=
  Covers.of_sub fun r hr => ⟨r, h r hr, 0, (BitVec.add_zero _).symm, by omega_arith⟩

section
variable (s : State)

/-- The arguments. -/
abbrev C : Addr := s.gpr .a0
abbrev Rn : Nat := (s.gpr .a1).toNat
abbrev Nn : Addr := s.gpr .a2
abbrev NL : Nat := (s.gpr .a3).toNat
abbrev Ad : Addr := s.gpr .a4
abbrev AL : Nat := (s.gpr .a5).toNat
abbrev Src : Addr := s.gpr .a6
abbrev Cnt : Nat := (s.gpr .a7).toNat
abbrev Dst : Addr := stackArg s 0
abbrev L : Nat := (stackArg s 1).toNat
abbrev Tg : Addr := stackArg s 2
abbrev Bk : Addr := stackArg s 3

/-- The regions: the key context, the nonce, the additional data, the
descriptors, the slices they list, the output, the tag, the buffer, the
stack arguments and the stack below the stack pointer. -/
abbrev cR : Region := ⟨C s, 256⟩
abbrev nR : Region := ⟨Nn s, NL s⟩
abbrev aR : Region := ⟨Ad s, AL s⟩
abbrev dsR : Region := ⟨Src s, Cnt s * 16⟩
abbrev lsR : List Region := Sig.listed 64 s.mem .u8 (Src s) (Cnt s)
abbrev dR : Region := ⟨Dst s, L s⟩
abbrev tgR : Region := ⟨Tg s, 16⟩
abbrev bkR : Region := ⟨Bk s, 1248⟩
abbrev argR : Region := ⟨stackArgAddr s 0, 32⟩
abbrev stkR : Region := ⟨s.sp - BitVec.ofNat 64 4672, 4672⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 64 s.mem (Src s) i
abbrev pt (i : Nat) : List Byte := gathered 64 s.mem (Src s) i

/-- The base of the 4672 bytes of stack below the stack pointer. -/
abbrev Bs : Addr := s.sp - BitVec.ofNat 64 4672

/-- Our frame; the call's stack arguments and the return address in it. -/
abbrev FA : Region := ⟨Bs s + BitVec.ofNat 64 4640, 32⟩
abbrev aOut : Addr := Bs s + BitVec.ofNat 64 4640
abbrev bkA : Addr := Bs s + BitVec.ofNat 64 4648
abbrev raA : Addr := Bs s + BitVec.ofNat 64 4656

/-- Our stack argument `i`. -/
abbrev sa (i : Nat) : Addr := Bs s + BitVec.ofNat 64 (4672 + 8 * i)

/-- The memory after each store of the entry. -/
abbrev eMem1 : Mem := s.mem.writeW (raA s) (s.gpr .ra)
abbrev eMem2 : Mem := (eMem1 s).writeW (aOut s) (Tg s)
abbrev eMem : Mem := (eMem2 s).writeW (bkA s) (Bk s)

/-- The memory once the slices are gathered at `dst`. -/
abbrev gMem : Mem := writeBytes (eMem s) (Dst s) (pt s (Cnt s))

/-- The regions the call of `vg_aes_gcm_seal_bitsliced` reads and writes. -/
abbrev rdC : List Region := [cR s, nR s, aR s, bkR s, ⟨aOut s, 16⟩]
abbrev wrC : List Region := [dR s, tgR s]

end

/-- What the code of `vg_aes_gcm_seal_gather_bitsliced` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [cR s, nR s, aR s, bkR s, dsR s] ++ lsR s ++ [argR s] ∧ s.wr = [dR s, tgR s] ∧
    (cR s).Disjoint (dR s) ∧ (cR s).Disjoint (tgR s) ∧ (nR s).Disjoint (dR s) ∧
    (nR s).Disjoint (tgR s) ∧ (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧
    (dsR s).Disjoint (dR s) ∧ (dsR s).Disjoint (tgR s) ∧ (bkR s).Disjoint (dR s) ∧ (bkR s).Disjoint (tgR s) ∧
    (∀ r ∈ lsR s, r.Disjoint (dR s) ∧ r.Disjoint (tgR s)) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (cR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dsR s) ∧ (stkR s).Disjoint (bkR s) ∧ (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧
    (stkR s).Disjoint (argR s) ∧ (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧
    (C s).toNat + 256 ≤ 2 ^ 64 ∧ (Nn s).toNat + NL s ≤ 2 ^ 64 ∧ (Ad s).toNat + AL s ≤ 2 ^ 64 ∧
    (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 64) ∧
    (Dst s).toNat + L s ≤ 2 ^ 64 ∧ (Tg s).toNat + 16 ≤ 2 ^ 64 ∧ (Bk s).toNat + 1248 ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 4672 ≤ s.sp.toNat ∧ s.sp.toNat + 32 ≤ 2 ^ 64 ∧
    (Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14) ∧ gl s (Cnt s) = L s ∧ (C s).toNat % 8 = 0 ∧
    (Bk s).toNat % 8 = 0 ∧ CtxSlicedRepr s.mem (Bk s) (C s)

/-- What two runs agree on: the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3 ∧
    ∀ i < Cnt s₁ * 16, s₁.mem (Src s₁ + BitVec.ofNat 64 i) = s₂.mem (Src s₁ + BitVec.ofNat 64 i)

/-- What `vg_aes_gcm_seal_gather_bitsliced` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encryptWith (ctxCiph s.mem (C s) (Rn s)) (ctxH s.mem (C s)) 16 (bytesAt s.mem (Nn s) (NL s)) (pt s (Cnt s))
      (bytesAt s.mem (Ad s) (AL s)) =
    (bytesAt s'.mem (Dst s) (L s), bytesAt s'.mem (Tg s) 16)

/-- `vg_aes_gcm_seal_gather_bitsliced`. -/
def gatherBsRISCV64 : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

/-! ## The function called -/

/-- The frame of `vg_aes_gcm_seal_bitsliced` uses the 4640 bytes of stack
its contract reserves. -/
theorem sealBs_sdepth : sdepth sealBsCode = 4640 := by
  decide +kernel

/-- The correctness of `vg_aes_gcm_seal_bitsliced`, in its frame, by its shared contract. -/
abbrev SealBsOk : Prop :=
  ∀ s, (Proof.AesGcm.sealBitslicedRoundsContract RISCV64.abi 4640).pre s →
    ∃ t s', Exec isa sealBsCode s t s' ∧ abiPreserved s s' ∧
      (Proof.AesGcm.sealBitslicedRoundsContract RISCV64.abi 4640).post s s'

/-- What a call of `vg_aes_gcm_seal_bitsliced(ctx = a0, rounds = a1,
nonce = a2, nonce_len = a3, aad = a4, aad_len = a5, data = a6, len = a7,
tag, bk)` needs, `tag` and `bk` its stack arguments. -/
def callPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .a0, 256⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, 16⟩
  let bk : Region := ⟨stackArg s 1, 1248⟩
  let arg : Region := ⟨stackArgAddr s 0, 16⟩
  let stk : Region := ⟨s.sp - BitVec.ofNat 64 4640, 4640⟩
  s.rd = [ctx, nonce, aad, bk, arg] ∧ s.wr = [data, tag] ∧
    ctx.Disjoint data ∧ ctx.Disjoint tag ∧ nonce.Disjoint data ∧ nonce.Disjoint tag ∧
    aad.Disjoint data ∧ aad.Disjoint tag ∧ bk.Disjoint data ∧ bk.Disjoint tag ∧
    data.Disjoint tag ∧ data.Disjoint arg ∧ tag.Disjoint arg ∧
    stk.Disjoint ctx ∧ stk.Disjoint nonce ∧ stk.Disjoint aad ∧ stk.Disjoint bk ∧ stk.Disjoint data ∧
    stk.Disjoint tag ∧ stk.Disjoint arg ∧
    (s.gpr .a0).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + 16 ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + 1248 ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 4640 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) ∧ (s.gpr .a0).toNat % 8 = 0 ∧
    (stackArg s 1).toNat % 8 = 0 ∧ CtxSlicedRepr s.mem (stackArg s 1) (s.gpr .a0)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem sealSpec_pre {s : State} (h : callPre s) :
    (Proof.AesGcm.sealBitslicedRoundsContract RISCV64.abi 4640).pre s := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃, a₁₄, a₁₅, a₁₆, a₁₇, a₁₈, a₁₉, a₂₀, a₂₁, a₂₂,
    a₂₃, a₂₄, a₂₅, a₂₆, a₂₇, a₂₈, a₂₉, a₃₀, a₃₁, a₃₂, a₃₃⟩ := h
  sig_pre [Proof.AesGcm.sealBitslicedRoundsContract, Spec.Gcm.sealBitslicedSig, Spec.Gcm.sealBitslicedPre,
    Spec.Gcm.sealSig, Spec.Gcm.sealPre, Spec.Gcm.bitslicedParam, RISCV64.abi, RISCV64.argRegs, stackArgs_two,
    List.range, List.range.loop]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | exact a₃₃
    | exact a₉.symm
    | exact a₁₀.symm

theorem sealSpec_post {s s' : State} (h : (Proof.AesGcm.sealBitslicedRoundsContract RISCV64.abi 4640).post s s')
    (hR : (s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) :
    encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (ctxH s.mem (s.gpr .a0)) 16
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
        (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat, bytesAt s'.mem (stackArg s 0) 16) := by
  sig_post [Proof.AesGcm.sealBitslicedRoundsContract, Spec.Gcm.sealBitslicedSig, Spec.Gcm.sealSig,
    Spec.Gcm.bitslicedParam, Proof.AesGcm.sealBitslicedRoundsPost, Proof.AesGcm.sealRoundsPost, RISCV64.abi,
    RISCV64.argRegs, stackArgs_two, List.range, List.range.loop] at h
  exact h hR

theorem sealSpec_pub {s₁ s₂ : State} (h : s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧
    s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
    s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1) :
    (Proof.AesGcm.sealBitslicedRoundsContract RISCV64.abi 4640).pub s₁ s₂ := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁⟩ := h
  sig_pub [Proof.AesGcm.sealBitslicedRoundsContract, Spec.Gcm.sealBitslicedSig, Spec.Gcm.sealSig,
    Spec.Gcm.bitslicedParam, RISCV64.abi, RISCV64.argRegs, stackArgs_two, List.range, List.range.loop]
  sig_reduce [Proof.AesGcm.sealBitslicedRoundsContract, Spec.Gcm.sealBitslicedSig, Spec.Gcm.sealSig,
    Spec.Gcm.bitslicedParam, RISCV64.abi, RISCV64.argRegs, stackArgs_two, List.range, List.range.loop]
  sig_and_intros
  all_goals first | with_reducible assumption | trivial

/-! ## The layout -/

/-- Parts of the stack below the stack pointer. -/
theorem stk_sub (s : State) (d n : Nat) (h' : d + n ≤ 4672) :
    (⟨Bs s + BitVec.ofNat 64 d, n⟩ : Region).Sub ⟨Bs s, 4672⟩ :=
  Offset.sub_base _ h'

theorem stk_sub0 (s : State) (n : Nat) (h' : n ≤ 4672) : (⟨Bs s, n⟩ : Region).Sub ⟨Bs s, 4672⟩ :=
  Region.sub_prefix h'

/-- A doubleword of our frame. -/
theorem fa_contains (s : State) {d : Nat} (h₁ : 4640 ≤ d) (h₂ : d + 8 ≤ 4672) :
    (FA s).Contains (Bs s + BitVec.ofNat 64 d) 8 :=
  Offset.contains (Bs s) h₁ h₂ (by decide)

theorem frame_e1 (s : State) : Frame [FA s] s.mem (eMem1 s) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (fa_contains s (d := 4656) (by decide) (by decide))

theorem frame_e2 (s : State) : Frame [FA s] s.mem (eMem2 s) :=
  (frame_e1 s).writeW (List.mem_singleton_self _) _ (fa_contains s (d := 4640) (by decide) (by decide))

theorem frame_eMem (s : State) : Frame [FA s] s.mem (eMem s) :=
  (frame_e2 s).writeW (List.mem_singleton_self _) _ (fa_contains s (d := 4648) (by decide) (by decide))

/-- What `gatherPre` gives, with the stack below the stack pointer at `Bs s`. -/
structure Lay (s : State) : Prop where
  pre : gatherPre s
  hB : s.sp = Bs s + BitVec.ofNat 64 4672
  hBn : (Bs s).toNat + 4704 ≤ 2 ^ 64
  bc : (⟨Bs s, 4672⟩ : Region).Disjoint (cR s)
  bn : (⟨Bs s, 4672⟩ : Region).Disjoint (nR s)
  ba : (⟨Bs s, 4672⟩ : Region).Disjoint (aR s)
  bds : (⟨Bs s, 4672⟩ : Region).Disjoint (dsR s)
  bbk : (⟨Bs s, 4672⟩ : Region).Disjoint (bkR s)
  bl : ∀ r ∈ lsR s, (⟨Bs s, 4672⟩ : Region).Disjoint r
  bd : (⟨Bs s, 4672⟩ : Region).Disjoint (dR s)
  bt : (⟨Bs s, 4672⟩ : Region).Disjoint (tgR s)
  hargR : argR s = ⟨Bs s + BitVec.ofNat 64 4672, 32⟩
  al : s.sp.toNat % 16 = 0
  w₁ : 4672 ≤ s.sp.toNat
  hgl : gl s (Cnt s) = L s
  ods : (Src s).toNat + Cnt s * 16 ≤ 2 ^ 64
  hR : Rn s = 10 ∨ Rn s = 12 ∨ Rn s = 14

theorem lay {s : State} (hs : gatherPre s) : Lay s := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, bkd, bkt, lsdt, dt, darg, targ, bc, bn, ba, bds, bbk, bl,
    barg, bd, bt, oc, on, oa, ods, ol, od, ot, ob, al, w₁, w₂, hR, hgl, ca, bal, hbk⟩ := hs
  obtain hB : s.sp = Bs s + BitVec.ofNat 64 4672 := (BitVec.sub_add_cancel s.sp _).symm
  obtain hBn : (Bs s).toNat + 4704 ≤ 2 ^ 64 := by
    obtain e := congrArg BitVec.toNat hB
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
    have := (Bs s).isLt
    omega_arith
  refine ⟨⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, bkd, bkt, lsdt, dt, darg, targ, bc, bn, ba, bds, bbk, bl,
    barg, bd, bt, oc, on, oa, ods, ol, od, ot, ob, al, w₁, w₂, hR, hgl, ca, bal, hbk⟩, hB, hBn, bc, bn, ba, bds,
    bbk, bl, bd, bt, ?_, al, w₁, hgl, ods, hR⟩
  show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 32⟩ : Region) = ⟨Bs s + BitVec.ofNat 64 4672, 32⟩
  rw [← hB]; simp

namespace Lay

variable {s : State} (h : Lay s)
include h

theorem bs_toNat : (Bs s).toNat = s.sp.toNat - 4672 := by
  obtain e := congrArg BitVec.toNat h.hB
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at e
  have := h.hBn
  omega_using [e, this]

theorem off_toNat {k : Nat} (hk : k < 4704) : (Bs s + BitVec.ofNat 64 k).toNat = (Bs s).toNat + k := by
  have := h.hBn
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (by omega_arith)]

theorem al8 {k : Nat} (hk : k < 4704) (h8 : k % 8 = 0) : (Bs s + BitVec.ofNat 64 k).toNat % 8 = 0 := by
  rw [h.off_toNat hk, h.bs_toNat]; have := h.al; have := h.w₁; omega_arith

theorem fsp : s.sp - BitVec.ofNat 64 32 = Bs s + BitVec.ofNat 64 4640 := by
  rw [h.hB, Offset.add_ofNat_sub _ (by decide)]

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

/-- Our stack argument `i`, from its address in our frame's terms. -/
theorem sa_eq {i : Nat} : stackArg s i = s.mem.readW (sa s i) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (8 * i)) 64 = _
  rw [h.hB, Offset.add_add]

theorem sa_in {i : Nat} (hi : i < 4) (u : State) (hrd : u.rd = s.rd) :
    InRegions (u.rd ++ u.wr) (sa s i) 8 :=
  ⟨_, List.mem_append_left _ (by rw [hrd]; exact h.argIn), by
    rw [h.hargR]
    exact Offset.contains (Bs s) (by omega_arith) (by omega_arith) (by have := h.hBn; omega_arith)⟩

omit h in
/-- The memory the entry left outside the frame. -/
theorem keepE {r : Region} (hr : r.Disjoint ⟨Bs s, 4672⟩) {x : Addr} (hx : r.Contains x 1) :
    eMem s x = s.mem x :=
  frame_eMem s x fun r' hr' hc => by
    simp only [List.mem_singleton] at hr'; subst hr'
    exact hr x hx (stk_sub s 4640 32 (by decide) x hc)

/-- Our stack arguments are apart from the frame. -/
theorem sa_fa {i : Nat} (hi : i < 4) : ∀ r ∈ [FA s], (⟨sa s i, 8⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ (.inr (by omega_arith)) (by have := h.hBn; omega_arith)
    (by have := h.hBn; omega_arith)

/-- Our stack arguments, in a memory that differs only in the frame. -/
theorem argOf {m : Mem} (hf : Frame [FA s] s.mem m) {i : Nat} (hi : i < 4) :
    m.readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW hf (Region.contains_self _ _) (h.sa_fa hi) (by decide), h.sa_eq]

theorem eArg {i : Nat} (hi : i < 4) : (eMem s).readW (sa s i) 64 = stackArg s i := h.argOf (frame_eMem s) hi

/-- The descriptors and the slices, after the entry. -/
theorem hag : ∀ r ∈ Sig.descRegion 64 (Src s) (Cnt s) :: lsR s, ∀ x, r.Contains x 1 → s.mem x = eMem s x := by
  intro r hr x hx
  refine (keepE ?_ hx).symm
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h.bds.symm
  · exact (h.bl r hr).symm

theorem hpt : gathered 64 (eMem s) (Src s) (Cnt s) = pt s (Cnt s) :=
  Proof.AesGcm.gathered_congr_le (Nat.le_refl _) h.hag

theorem hlen : (pt s (Cnt s)).length = L s := (Proof.Gcm.length_gathered _ _ _ _).trans h.hgl

theorem frame_gMem : Frame [dR s] (eMem s) (gMem s) := by
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, h.hlen, Nat.le_refl]

/-- The memory once the slices are gathered differs from the one on entry
only in the frame and the output. -/
theorem frame_g : Frame [FA s, dR s] s.mem (gMem s) :=
  ((frame_eMem s).mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp)).trans
    (h.frame_gMem.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; simp))

omit h in
/-- A region apart from the stack and the output is apart from what the
entry and the gathering write. -/
theorem apart {r : Region} (h₁ : (⟨Bs s, 4672⟩ : Region).Disjoint r) (h₂ : r.Disjoint (dR s)) :
    ∀ r' ∈ [FA s, dR s], r.Disjoint r' := by
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · exact h₁.symm.sub_right (stk_sub s 4640 32 (by decide))
  · exact h₂

/-- The buffer still holds the key context's bitsliced form once the slices
are gathered. -/
theorem gRepr : CtxSlicedRepr (gMem s) (Bk s) (C s) := by
  obtain ⟨-, -, cd, -, -, -, -, -, -, -, bkd, -⟩ := h.pre
  have hbk := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact Proof.AesGcm.ctxSlicedRepr_congr (fun i hi => h.frame_g.bytes (R := bkR s) (apart h.bbk bkd)
      (show 1248 ≤ 2 ^ 64 by decide) hi)
    (fun i hi => h.frame_g.bytes (R := cR s) (apart h.bc cd) (show 256 ≤ 2 ^ 64 by decide) hi) hbk

/-- A doubleword of the frame, once the slices are gathered. -/
theorem gFr {a : Nat} (ha : a + 8 ≤ 32) :
    (gMem s).readW (Bs s + BitVec.ofNat 64 (4640 + a)) 64 = (eMem s).readW (Bs s + BitVec.ofNat 64 (4640 + a)) 64 :=
  Frame.readW h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.bd.sub_left (stk_sub s _ _ (by omega_arith))) (by decide)

/-- The return address and the call's `tag` and `bk`, once the slices are gathered. -/
theorem gRa : (gMem s).readW (raA s) 64 = s.gpr .ra := by
  rw [show raA s = Bs s + BitVec.ofNat 64 (4640 + 16) from rfl, h.gFr (by decide), eMem, eMem2,
    Mem.readW_writeW_sep (Offset.sep _ (.inr (by decide)) (by have := h.hBn; omega_arith)
      (by have := h.hBn; omega_arith)) (by decide),
    Mem.readW_writeW_sep (Offset.sep _ (.inr (by decide)) (by have := h.hBn; omega_arith)
      (by have := h.hBn; omega_arith)) (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem gTag : (gMem s).readW (aOut s) 64 = Tg s := by
  rw [show aOut s = Bs s + BitVec.ofNat 64 (4640 + 0) from rfl, h.gFr (by decide), eMem,
    Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by have := h.hBn; omega_arith)
      (by have := h.hBn; omega_arith)) (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem gBk : (gMem s).readW (bkA s) 64 = Bk s := by
  rw [show bkA s = Bs s + BitVec.ofNat 64 (4640 + 8) from rfl, h.gFr (by decide), eMem]
  exact Mem.readW_writeW_self64 _ _ _

/-- Our stack arguments, once the slices are gathered. -/
theorem gArg {i : Nat} (hi : i < 4) : (gMem s).readW (sa s i) 64 = stackArg s i := by
  rw [Frame.readW h.frame_gMem (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have darg := h.pre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    rw [h.hargR] at darg
    refine darg.symm.sub_left ?_
    exact Offset.sub _ (by omega_arith) (by omega_arith)) (by decide), h.eArg hi]

end Lay

/-! ## The phases -/

/-- After the entry. -/
structure Entered (s e : State) : Prop where
  mem : e.mem = eMem s
  a0 : e.gpr .a0 = s.gpr .a0
  a1 : e.gpr .a1 = s.gpr .a1
  a2 : e.gpr .a2 = s.gpr .a2
  a3 : e.gpr .a3 = s.gpr .a3
  a4 : e.gpr .a4 = Src s
  a5 : e.gpr .a5 = s.gpr .a7
  a6 : e.gpr .a6 = Dst s
  a7 : e.gpr .a7 = stackArg s 1
  t5 : e.gpr .t5 = Ad s
  t6 : e.gpr .t6 = s.gpr .a5
  pres : ∀ r ∈ preserved, e.gpr r = s.gpr r
  sp : e.sp = Bs s + BitVec.ofNat 64 4640
  rd : e.rd = s.rd
  wr : e.wr = FA s :: s.wr

theorem entered_wp {s : State} (h : Lay s) : WP isa (.block entryBs) (allocd 32 s) (Entered s) := by
  have asp : (allocd 32 s).sp = Bs s + BitVec.ofNat 64 4640 := h.fsp
  obtain awr : (allocd 32 s).wr = FA s :: s.wr := by
    show ⟨s.sp - BitVec.ofNat 64 32, 32⟩ :: s.wr = _; rw [h.fsp]
  have ag (r : Reg) : (allocd 32 s).gpr r = s.gpr r := rfl
  have ard : (allocd 32 s).rd = s.rd := rfl
  have amem : (allocd 32 s).mem = s.mem := rfl
  have hw (u : State) (hu : u.wr = FA s :: s.wr) {d : Nat} (h₁ : 4640 ≤ d) (h₂ : d + 8 ≤ 4672) :
      InRegions u.wr (Bs s + BitVec.ofNat 64 d) 8 :=
    ⟨_, by rw [hu]; exact List.mem_cons_self .., fa_contains s h₁ h₂⟩
  unfold entryBs
  simp only [mov]
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  obtain p₁ : u₁.gpr .t0 = Bs s + BitVec.ofNat 64 4640 := by rw [v₁.gpr, asp, BitVec.add_zero]
  -- The return address.
  refine wp_sd (a := raA s) (by decide) (by rw [p₁, Offset.add_add]) (h.al8 (by decide) (by decide))
    (hw u₁ (by rw [v₁.wr, awr]) (d := 4656) (by decide) (by decide)) fun u₂ v₂ => ?_
  obtain p₂ : u₂.gpr .t0 = Bs s + BitVec.ofNat 64 4640 := by rw [v₂.gpr, p₁]
  obtain m₂ : u₂.mem = eMem1 s := by rw [v₂.mem, v₁.mem, amem, v₁.other _ (by decide), ag]
  -- `tag`.
  refine wp_ld (a := sa s 2) (by decide) (by rw [p₂, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ (by rw [v₂.rd, v₁.rd, ard])) fun u₃ v₃ => ?_
  obtain p₃ : u₃.gpr .t0 = Bs s + BitVec.ofNat 64 4640 := by rw [v₃.other _ (by decide), p₂]
  obtain t₃ : u₃.gpr .t1 = Tg s := by rw [v₃.gpr, m₂, h.argOf (frame_e1 s) (by decide)]
  refine wp_sd (a := aOut s) (by decide) (by rw [p₃, BitVec.add_zero]) (h.al8 (by decide) (by decide))
    (hw u₃ (by rw [v₃.wr, v₂.wr, v₁.wr, awr]) (d := 4640) (by decide) (by decide)) fun u₄ v₄ => ?_
  obtain m₄ : u₄.mem = eMem2 s := by rw [v₄.mem, t₃, v₃.mem, m₂]
  -- `bk`.
  refine wp_ld (a := sa s 3) (by decide) (by rw [v₄.gpr, p₃, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ (by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, ard])) fun u₅ v₅ => ?_
  obtain p₅ : u₅.gpr .t0 = Bs s + BitVec.ofNat 64 4640 := by rw [v₅.other _ (by decide), v₄.gpr, p₃]
  obtain t₅ : u₅.gpr .t1 = Bk s := by rw [v₅.gpr, m₄, h.argOf (frame_e2 s) (by decide)]
  refine wp_sd (a := bkA s) (by decide) (by rw [p₅, Offset.add_add]) (h.al8 (by decide) (by decide))
    (hw u₅ (by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, awr]) (d := 4648) (by decide) (by decide))
    fun u₆ v₆ => ?_
  obtain m₆ : u₆.mem = eMem s := by rw [v₆.mem, t₅, v₅.mem, m₄]
  have h6 (r : Reg) (h0 : r ≠ .t0) (h1 : r ≠ .t1) : u₆.gpr r = s.gpr r := by
    rw [v₆.gpr, v₅.other r h1, v₄.gpr, v₃.other r h1, v₂.gpr, v₁.other r h0, ag]
  -- The registers.
  refine wp_mv fun u₇ v₇ => wp_mv fun u₈ v₈ => wp_mv fun u₉ v₉ => wp_mv fun u₁₀ v₁₀ => ?_
  obtain p₁₀ : u₁₀.gpr .t0 = Bs s + BitVec.ofNat 64 4640 := by
    rw [v₁₀.other _ (by decide), v₉.other _ (by decide), v₈.other _ (by decide), v₇.other _ (by decide), v₆.gpr,
      p₅]
  obtain hm₁₀ : u₁₀.mem = eMem s := by rw [v₁₀.mem, v₉.mem, v₈.mem, v₇.mem, m₆]
  obtain hr₁₀ : u₁₀.rd = s.rd := by
    rw [v₁₀.rd, v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, ard]
  refine wp_ld (a := sa s 0) (by decide) (by rw [p₁₀, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ hr₁₀) fun u₁₁ v₁₁ => ?_
  refine wp_ld (a := sa s 1) (by decide) (by rw [v₁₁.other _ (by decide), p₁₀, Offset.add_add])
    (h.al8 (by decide) (by decide)) (h.sa_in (by decide) _ (by rw [v₁₁.rd, hr₁₀])) fun u₁₂ v₁₂ => WP.block_nil ?_
  have g (r : Reg) (h0 : r ≠ .t0) (h1 : r ≠ .t1) (h5 : r ≠ .t5) (h6' : r ≠ .t6) (h4 : r ≠ .a4) (h5' : r ≠ .a5)
      (h6'' : r ≠ .a6) (h7 : r ≠ .a7) : u₁₂.gpr r = s.gpr r := by
    rw [v₁₂.other r h7, v₁₁.other r h6'', v₁₀.other r h5', v₉.other r h4, v₈.other r h6', v₇.other r h5,
      h6 r h0 h1]
  obtain hpres : ∀ r ∈ preserved, r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t5 ∧ r ≠ .t6 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .a6 ∧
      r ≠ .a7 := by decide
  exact ⟨by rw [v₁₂.mem, v₁₁.mem, hm₁₀],
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    by rw [v₁₂.other _ (by decide), v₁₁.other _ (by decide), v₁₀.other _ (by decide), v₉.gpr,
      v₈.other _ (by decide), v₇.other _ (by decide), h6 _ (by decide) (by decide)],
    by rw [v₁₂.other _ (by decide), v₁₁.other _ (by decide), v₁₀.gpr, v₉.other _ (by decide),
      v₈.other _ (by decide), v₇.other _ (by decide), h6 _ (by decide) (by decide)],
    by rw [v₁₂.other _ (by decide), v₁₁.gpr, hm₁₀, h.eArg (by decide)],
    by rw [v₁₂.gpr, v₁₁.mem, hm₁₀, h.eArg (by decide)],
    by rw [v₁₂.other _ (by decide), v₁₁.other _ (by decide), v₁₀.other _ (by decide), v₉.other _ (by decide),
      v₈.other _ (by decide), v₇.gpr, h6 _ (by decide) (by decide)],
    by rw [v₁₂.other _ (by decide), v₁₁.other _ (by decide), v₁₀.other _ (by decide), v₉.other _ (by decide),
      v₈.gpr, v₇.other _ (by decide), h6 _ (by decide) (by decide)],
    fun r hr => have q := hpres r hr; g r q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1
      q.2.2.2.2.2.2.1 q.2.2.2.2.2.2.2,
    by rw [v₁₂.sp, v₁₁.sp, v₁₀.sp, v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, asp],
    by rw [v₁₂.rd, v₁₁.rd, hr₁₀],
    by rw [v₁₂.wr, v₁₁.wr, v₁₀.wr, v₉.wr, v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, awr]⟩

/-- `gather`'s precondition after the entry. -/
theorem gatherPre_of {s e : State} (h : Lay s) (he : Entered s e) : GatherPre e (Src s) (Dst s) (Cnt s) (L s) := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, bkd, bkt, lsdt, dt, darg, targ, bc, bn, ba, bds, bbk, bl,
    barg, bd, bt, oc, on, oa, ods, ol, od, ot, ob, al, w₁, w₂, hR, hgl, ca, bal, hbk⟩ := h.pre
  obtain ⟨hls, -⟩ := Proof.AesGcm.listed_congr_le (Nat.le_refl _) h.hag
  rw [← he.mem] at hls
  exact { a4 := he.a4
          a5 := by rw [he.a5, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          a6 := he.a6
          hcnt := (s.gpr .a7).isLt
          dw := ods
          lt := (stackArg s 1).isLt
          len := by rw [he.mem, Proof.AesGcm.gatheredLen_congr_le (Nat.le_refl _) h.hag]; exact hgl
          dsr := covers_mem fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact List.mem_append_left _ (by rw [he.rd, rd]; simp)
          lsr := fun r hr => covers_mem fun r' hr' => by
            simp only [List.mem_singleton] at hr'; subst hr'
            rw [hls] at hr
            exact List.mem_append_left _ (by rw [he.rd, rd]; simp [hr])
          dw' := covers_mem fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            rw [he.wr, wr]; simp
          dsd := dsd
          lsd := fun r hr => (lsdt r (by rw [hls] at hr; exact hr)).1 }

/-- After the gathering. -/
structure Gathered (s g : State) : Prop where
  mem : g.mem = gMem s
  a0 : g.gpr .a0 = s.gpr .a0
  a1 : g.gpr .a1 = s.gpr .a1
  a2 : g.gpr .a2 = s.gpr .a2
  a3 : g.gpr .a3 = s.gpr .a3
  a7 : g.gpr .a7 = stackArg s 1
  t5 : g.gpr .t5 = Ad s
  t6 : g.gpr .t6 = s.gpr .a5
  pres : ∀ r ∈ preserved, g.gpr r = s.gpr r
  sp : g.sp = Bs s + BitVec.ofNat 64 4640
  rd : g.rd = s.rd
  wr : g.wr = FA s :: s.wr

theorem gathered_wp {s e : State} (h : Lay s) (he : Entered s e) :
    WP isa Impl.Gather.RISCV64.gather e (Gathered s) := by
  refine WP.mono (gather_wp e (gatherPre_of h he)) fun g ⟨mg, kg⟩ => ?_
  rw [he.mem, h.hpt] at mg
  have hn : ∀ r, r ∉ gatherRegs → g.gpr r = e.gpr r := kg.gpr
  obtain hpres : ∀ r ∈ preserved, r ∉ gatherRegs := by decide
  exact ⟨mg, (hn _ (by decide)).trans he.a0, (hn _ (by decide)).trans he.a1, (hn _ (by decide)).trans he.a2,
    (hn _ (by decide)).trans he.a3, (hn _ (by decide)).trans he.a7, (hn _ (by decide)).trans he.t5,
    (hn _ (by decide)).trans he.t6, fun r hr => (hn r (hpres r hr)).trans (he.pres r hr),
    kg.sp.trans he.sp, kg.rd.trans he.rd, kg.wr.trans he.wr⟩

/-- Ready for the call. -/
structure Ready (s c : State) : Prop where
  mem : c.mem = gMem s
  a0 : c.gpr .a0 = C s
  a1 : c.gpr .a1 = s.gpr .a1
  a2 : c.gpr .a2 = Nn s
  a3 : c.gpr .a3 = s.gpr .a3
  a4 : c.gpr .a4 = Ad s
  a5 : c.gpr .a5 = s.gpr .a5
  a6 : c.gpr .a6 = Dst s
  a7 : c.gpr .a7 = stackArg s 1
  pres : ∀ r ∈ preserved, c.gpr r = s.gpr r
  sp : c.sp = Bs s + BitVec.ofNat 64 4640
  rd : c.rd = s.rd
  wr : c.wr = FA s :: s.wr

theorem ready_wp {s g : State} (h : Lay s) (hg : Gathered s g) : WP isa (.block callArgsBs) g (Ready s) := by
  unfold callArgsBs
  simp only [mov]
  refine wp_mv fun u₁ v₁ => wp_mv fun u₂ v₂ => wp_addSp (imm := 0) (by decide) fun u₃ v₃ => ?_
  obtain p₃ : u₃.gpr .t0 = Bs s + BitVec.ofNat 64 4640 := by rw [v₃.gpr, v₂.sp, v₁.sp, hg.sp, BitVec.add_zero]
  refine wp_ld (a := sa s 0) (by decide) (by rw [p₃, Offset.add_add]) (h.al8 (by decide) (by decide))
    (h.sa_in (by decide) _ (by rw [v₃.rd, v₂.rd, v₁.rd, hg.rd])) fun u₄ v₄ => WP.block_nil ?_
  have g (r : Reg) (h4 : r ≠ .a4) (h5 : r ≠ .a5) (h0 : r ≠ .t0) (h6 : r ≠ .a6) : u₄.gpr r = g.gpr r := by
    rw [v₄.other r h6, v₃.other r h0, v₂.other r h5, v₁.other r h4]
  obtain hpres : ∀ r ∈ preserved, r ≠ .a4 ∧ r ≠ .a5 ∧ r ≠ .t0 ∧ r ≠ .a6 := by decide
  exact ⟨by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, hg.mem],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a0],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a1],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a2],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a3],
    by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, hg.t5],
    by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), hg.t6],
    by rw [v₄.gpr, v₃.mem, v₂.mem, v₁.mem, hg.mem, h.gArg (by decide)],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hg.a7],
    fun r hr => have q := hpres r hr; by rw [g r q.1 q.2.1 q.2.2.1 q.2.2.2, hg.pres r hr],
    by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, hg.sp], by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, hg.rd],
    by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, hg.wr]⟩

/-- The registers at the call. -/
theorem Ready.callGpr {s c : State} (hc : Ready s c) :
    c.callEntry.gpr .a0 = C s ∧ c.callEntry.gpr .a1 = s.gpr .a1 ∧ c.callEntry.gpr .a2 = Nn s ∧
      c.callEntry.gpr .a3 = s.gpr .a3 ∧ c.callEntry.gpr .a4 = Ad s ∧ c.callEntry.gpr .a5 = s.gpr .a5 ∧
      c.callEntry.gpr .a6 = Dst s ∧ c.callEntry.gpr .a7 = stackArg s 1 :=
  ⟨by rw [c.callEntry_gpr (by decide), hc.a0], by rw [c.callEntry_gpr (by decide), hc.a1],
    by rw [c.callEntry_gpr (by decide), hc.a2], by rw [c.callEntry_gpr (by decide), hc.a3],
    by rw [c.callEntry_gpr (by decide), hc.a4], by rw [c.callEntry_gpr (by decide), hc.a5],
    by rw [c.callEntry_gpr (by decide), hc.a6], by rw [c.callEntry_gpr (by decide), hc.a7]⟩

theorem cs_sub (s : State) : Bs s + BitVec.ofNat 64 4640 - BitVec.ofNat 64 4640 = Bs s :=
  BitVec.add_sub_cancel _ _

theorem Ready.argAddr {s c : State} (hc : Ready s c) (rd wr : List Region) :
    stackArgAddr ((c.callEntry).withRegions rd wr) 0 = aOut s := by
  show c.sp + BitVec.ofNat 64 (8 * 0) = _
  rw [hc.sp, Nat.mul_zero, BitVec.add_zero]

theorem Ready.argAddr1 {s c : State} (hc : Ready s c) (rd wr : List Region) :
    stackArgAddr ((c.callEntry).withRegions rd wr) 1 = bkA s := by
  show c.sp + BitVec.ofNat 64 (8 * 1) = _
  rw [hc.sp, Offset.add_add]

theorem Ready.arg {s c : State} (h : Lay s) (hc : Ready s c) (rd wr : List Region) :
    stackArg ((c.callEntry).withRegions rd wr) 0 = Tg s := by
  show c.mem.readW (stackArgAddr ((c.callEntry).withRegions rd wr) 0) 64 = _
  rw [hc.argAddr, hc.mem, h.gTag]

theorem Ready.arg1 {s c : State} (h : Lay s) (hc : Ready s c) (rd wr : List Region) :
    stackArg ((c.callEntry).withRegions rd wr) 1 = Bk s := by
  show c.mem.readW (stackArgAddr ((c.callEntry).withRegions rd wr) 1) 64 = _
  rw [hc.argAddr1, hc.mem, h.gBk]

/-- What the call needs. -/
theorem Ready.call {s c : State} (h : Lay s) (hc : Ready s c) :
    callPre ((c.callEntry).withRegions (rdC s) (wrC s)) ∧ Covers (rdC s ++ wrC s) (c.rd ++ c.wr) ∧
      Covers (wrC s) c.wr := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, bkd, bkt, lsdt, dt, darg, targ, -, -, -, -, -, -,
    -, -, -, oc, on, oa, ods, ol, od, ot, ob, al, w₁, w₂, hR, hgl, ca, bal, hbk⟩ := h.pre
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr
  have hBn := h.hBn
  have hb := h.bs_toNat
  obtain h24 := h.off_toNat (k := 4640) (by decide)
  obtain aS : (⟨aOut s, 16⟩ : Region).Sub ⟨Bs s, 4672⟩ := stk_sub s 4640 16 (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [callPre, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.withRegions_sp,
      State.withRegions_mem, State.callEntry_sp, State.callEntry_mem, c3, c4, c5, c6, c7, c8, c9, c10, hc.sp,
      cs_sub, hc.argAddr, hc.arg h, hc.arg1 h, hc.mem]
    refine ⟨trivial, trivial, cd, ct, nd, nt, ad, at_, bkd, bkt, dt, h.bd.symm.sub_right aS,
      h.bt.symm.sub_right aS, h.bc.sub_left (stk_sub0 s _ (by decide)), h.bn.sub_left (stk_sub0 s _ (by decide)),
      h.ba.sub_left (stk_sub0 s _ (by decide)), h.bbk.sub_left (stk_sub0 s _ (by decide)),
      h.bd.sub_left (stk_sub0 s _ (by decide)), h.bt.sub_left (stk_sub0 s _ (by decide)),
      (Offset.disjoint_base _ (by decide) (by omega_arith)).symm, oc, on, oa, od, ot, ob,
      by rw [h24]; omega_arith, by rw [h24]; omega_arith, by rw [h24]; omega_arith, hR, ca, bal, h.gRepr⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [rdC, wrC, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_left _ (by rw [hc.rd, rd]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨FA s, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), 0,
        (BitVec.add_zero _).symm, by show 0 + 16 ≤ 32; omega_arith⟩
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
    · exact ⟨_, List.mem_append_right _ (by rw [hc.wr, wr]; simp), 0, (BitVec.add_zero _).symm, by omega_arith⟩
  · refine covers_mem fun r hr => ?_
    rw [hc.wr, wr]
    exact List.mem_cons_of_mem _ hr

/-- After the call. -/
structure Called (s z : State) : Prop where
  ra : z.mem.readW (raA s) 64 = s.gpr .ra
  out : encryptWith (ctxCiph (gMem s) (C s) (Rn s)) (ctxH (gMem s) (C s)) 16 (bytesAt (gMem s) (Nn s) (NL s))
      (bytesAt (gMem s) (Dst s) (L s)) (bytesAt (gMem s) (Ad s) (AL s)) =
    (bytesAt z.mem (Dst s) (L s), bytesAt z.mem (Tg s) 16)
  pres : ∀ r ∈ preserved, z.gpr r = s.gpr r
  sp : z.sp = Bs s + BitVec.ofNat 64 4640
  rd : z.rd = s.rd
  wr : z.wr = FA s :: s.wr

theorem called_wp (hv : SealBsOk) {s c : State} (h : Lay s) (hc : Ready s c) :
    WP isa (.call "vg_aes_gcm_seal_bitsliced_core" sealBsCode) c (Called s) := by
  obtain ⟨hcp, hcov, hw⟩ := hc.call h
  obtain ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩ := hc.callGpr
  refine WP.callAny (k := Proof.AesGcm.sealBitslicedRoundsContract RISCV64.abi 4640) hv (sealSpec_pre hcp) hcov hw
    (fun z rd' wr' sp' fr' pres' post' => ?_) (by rw [sealBs_sdepth]; decide)
  obtain hpost := sealSpec_post post' (by simp only [State.withRegions_gpr, c4]; exact h.hR)
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, c3, c4, c5, c6, c7, c8, c9, c10,
    hc.mem, hc.arg h] at hpost
  -- The return address, from the frame, which the call kept.
  obtain ra : z.mem.readW (raA s) 64 = s.gpr .ra := by
    rw [← h.gRa, ← hc.mem]
    refine Frame.readW fr' (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · exact h.bd.sub_left (stk_sub s 4656 8 (by decide))
    · exact h.bt.sub_left (stk_sub s 4656 8 (by decide))
    · simp only [below, hc.sp, sealBs_sdepth, cs_sub]
      exact Offset.disjoint_base _ (by decide) (by have := h.hBn; omega_arith)
  exact ⟨ra, hpost, fun r hr => by rw [pres' r hr, hc.pres r hr], sp'.trans hc.sp, rd'.trans hc.rd,
    wr'.trans hc.wr⟩

/-- After the return address is loaded back. -/
structure Restored (s y : State) : Prop where
  ra : y.gpr .ra = s.gpr .ra
  out : encryptWith (ctxCiph (gMem s) (C s) (Rn s)) (ctxH (gMem s) (C s)) 16 (bytesAt (gMem s) (Nn s) (NL s))
      (bytesAt (gMem s) (Dst s) (L s)) (bytesAt (gMem s) (Ad s) (AL s)) =
    (bytesAt y.mem (Dst s) (L s), bytesAt y.mem (Tg s) 16)
  pres : ∀ r ∈ preserved, y.gpr r = s.gpr r
  sp : y.sp = Bs s + BitVec.ofNat 64 4640
  wr : y.wr = FA s :: s.wr

theorem restored_wp {s z : State} (h : Lay s) (hz : Called s z) : WP isa (.block restoreBs) z (Restored s) := by
  unfold restoreBs
  refine wp_addSp (imm := 0) (by decide) fun u₁ v₁ => ?_
  obtain p₁ : u₁.gpr .t0 = Bs s + BitVec.ofNat 64 4640 := by rw [v₁.gpr, hz.sp, BitVec.add_zero]
  refine wp_ld (a := raA s) (by decide) (by rw [p₁, Offset.add_add]) (h.al8 (by decide) (by decide))
    ⟨FA s, List.mem_append_right _ (by rw [v₁.wr, hz.wr]; exact List.mem_cons_self ..),
      fa_contains s (d := 4656) (by decide) (by decide)⟩ fun u₂ v₂ => WP.block_nil ?_
  obtain hpres : ∀ r ∈ preserved, r ≠ .ra ∧ r ≠ .t0 := by decide
  exact ⟨by rw [v₂.gpr, v₁.mem, hz.ra], by rw [v₂.mem, v₁.mem]; exact hz.out,
    fun r hr => by rw [v₂.other r (hpres r hr).1, v₁.other r (hpres r hr).2, hz.pres r hr],
    by rw [v₂.sp, v₁.sp, hz.sp], by rw [v₂.wr, v₁.wr, hz.wr]⟩

/-- The frame freed: what the function leaves. -/
theorem freed_ok {s y : State} (h : Lay s) (hy : Restored s y) (m : Mem) (u : Nat → BitVec 64)
    (fl : Frame [⟨s.sp - BitVec.ofNat 64 32, 32⟩] y.mem m) :
    abiPreserved s { freed 32 y with mem := m, unknowns := u } ∧
      gatherPost s { freed 32 y with mem := m, unknowns := u } := by
  obtain ⟨rd, wr, cd, ct, nd, nt, ad, at_, dsd, dst, bkd, bkt, lsdt, dt, darg, targ, -, -, -, -, -, -,
    -, -, -, oc, on, oa, ods, ol, od, ot, ob, al, w₁, w₂, hR, hgl, ca, bal, hbk⟩ := h.pre
  refine ⟨⟨fun r hr => hy.pres r hr, ?_, hy.ra⟩, ?_⟩
  · show y.sp + BitVec.ofNat 64 32 = s.sp
    rw [hy.sp, Offset.add_add, h.hB]
  · show encryptWith _ _ _ _ _ _ = (bytesAt m (Dst s) (L s), bytesAt m (Tg s) 16)
    -- The frame's bytes are lost, which lie apart from the data and the tag.
    rw [h.fsp] at fl
    have hD : bytesAt m (Dst s) (L s) = bytesAt y.mem (Dst s) (L s) :=
      List.map_congr_left fun i hi =>
        lost_byte fl (R := dR s) (h.bd.symm.sub_right (stk_sub s 4640 32 (by decide))) (List.mem_range.mp hi)
    have hT : bytesAt m (Tg s) 16 = bytesAt y.mem (Tg s) 16 :=
      List.map_congr_left fun i hi =>
        lost_byte fl (R := tgR s) (h.bt.symm.sub_right (stk_sub s 4640 32 (by decide))) (List.mem_range.mp hi)
    rw [hD, hT]
    obtain ⟨hc₁, hh₁⟩ := Proof.AesGcm.ctx_frame h.frame_g (Lay.apart h.bc cd) h.hR
    obtain hn : bytesAt (gMem s) (Nn s) (NL s) = bytesAt s.mem (Nn s) (NL s) :=
      Proof.Cmac.bytesAt_frame h.frame_g (Lay.apart h.bn nd) (by omega_arith)
    obtain ha : bytesAt (gMem s) (Ad s) (AL s) = bytesAt s.mem (Ad s) (AL s) :=
      Proof.Cmac.bytesAt_frame h.frame_g (Lay.apart h.ba ad) (by omega_arith)
    obtain hd : bytesAt (gMem s) (Dst s) (L s) = pt s (Cnt s) := by
      rw [← h.hlen]
      exact Proof.AesGcm.bytesAt_writeBytes_self _ _ _ (by rw [h.hlen]; exact (stackArg s 1).isLt)
    have := hy.out
    rw [hc₁, hh₁, hn, ha, hd] at this
    exact this

theorem sealGatherBs_wp (hv : SealBsOk) {s : State} (hs : gatherPre s) :
    WP isa sealGatherBs s fun z => abiPreserved s z ∧ gatherPost s z := by
  obtain h := lay hs
  refine WP.alloc (by decide) (by have := h.w₁; omega_arith) ?_
  refine WP.seq (WP.mono (entered_wp h) fun e he => ?_)
  refine WP.seq (WP.mono (gathered_wp h he) fun g hg => ?_)
  refine WP.seq (WP.mono (ready_wp h hg) fun c hc => ?_)
  refine WP.seq (WP.mono (called_wp hv h hc) fun z hz => ?_)
  exact WP.mono (restored_wp h hz) fun y hy m u fl => freed_ok h hy m u fl

/-! ## Constant time -/

open VG.Proof.Gather.RISCV64 (Eq2 TT rel_seq rel_taint ct_of gather_rel)

theorem sealGatherBs_ct (hv : SealBsOk)
    (hct : ConstantTime isa (Proof.AesGcm.sealBitslicedRoundsContract RISCV64.abi 4640).pre
      (Proof.AesGcm.sealBitslicedRoundsContract RISCV64.abi 4640).pub sealBsCode) :
    ConstantTime isa gatherPre gatherPub sealGatherBs := by
  refine VG.Proof.Gather.RISCV64.ct_of fun σ₁ σ₂ p₁ p₂ hq => ?_
  have h₁ := lay p₁
  have h₂ := lay p₂
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, a1, a2, a3, hdesc⟩ := hq
  have hB : Bs σ₁ = Bs σ₂ := by simp only [Bs, qsp]
  refine (RelCT.alloc (bytes := 32) (P := Eq2 σ₁ σ₂) (R := TT)
    ((?_ : RelCT isa (Eq2 (allocd 32 σ₁) (allocd 32 σ₂)) _ TT).mono
      (fun a b ⟨s, t, ⟨hs, ht⟩, ha, hb⟩ => by subst hs ht; exact ⟨ha, hb⟩) fun _ _ h => h)).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  -- The entry.
  refine rel_seq (rel_taint [] (show σ₁.sp - BitVec.ofNat 64 32 = σ₂.sp - BitVec.ofNat 64 32 by rw [qsp])
    (by simp) (by taint_decide)) (entered_wp h₁) (entered_wp h₂) fun e₁ e₂ he₁ he₂ => ?_
  -- The gathering.
  have g₁ := gatherPre_of h₁ he₁
  have g₂ := gatherPre_of h₂ he₂
  simp only [Src, Dst, Cnt, L, ← q9, ← q10, ← a0, ← a1] at g₂
  have hd : ∀ j < Cnt σ₁ * 16, e₁.mem (Src σ₁ + BitVec.ofNat 64 j) = e₂.mem (Src σ₁ + BitVec.ofNat 64 j) := by
    intro j hj
    have hx : (dsR σ₁).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ hj (by have := h₁.ods; omega_using [hj, this])
    have hx₂ : (dsR σ₂).Contains (Src σ₁ + BitVec.ofNat 64 j) 1 := by
      simp only [dsR, Src, Cnt, ← q9, ← q10]; exact hx
    rw [he₁.mem, he₂.mem, Lay.keepE h₁.bds.symm hx, Lay.keepE h₂.bds.symm hx₂]
    exact hdesc j hj
  refine rel_seq (gather_rel hd g₁ g₂ (by rw [he₁.sp, he₂.sp, hB])) (gathered_wp h₁ he₁) (gathered_wp h₂ he₂)
    fun u₁ u₂ hg₁ hg₂ => ?_
  -- The call's arguments.
  refine rel_seq (rel_taint [] (by rw [hg₁.sp, hg₂.sp, hB]) (by simp) (by taint_decide))
    (ready_wp h₁ hg₁) (ready_wp h₂ hg₂) fun c₁ c₂ hc₁ hc₂ => ?_
  -- The call, by its callee's contract.
  have hrd : rdC σ₂ = rdC σ₁ := by
    simp only [rdC, cR, nR, aR, bkR, C, Nn, NL, Ad, AL, Bk, aOut, Bs, q3, q5, q6, q7, q8, a3, qsp]
  have hwr : wrC σ₂ = wrC σ₁ := by simp only [wrC, dR, tgR, Dst, L, Tg, a0, a1, a2]
  obtain ⟨cp₁, cv₁, cw₁⟩ := hc₁.call h₁
  obtain ⟨cp₂, cv₂, cw₂⟩ := hc₂.call h₂
  rw [hrd, hwr] at cp₂ cv₂
  rw [hwr] at cw₂
  obtain ⟨r3₁, r4₁, r5₁, r6₁, r7₁, r8₁, r9₁, r10₁⟩ := hc₁.callGpr
  obtain ⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, r10₂⟩ := hc₂.callGpr
  refine rel_seq (RelCT.call hv hct (rdC σ₁) (wrC σ₁) fun a b ⟨ha, hb⟩ => by
    subst ha hb
    refine ⟨sealSpec_pre cp₁, sealSpec_pre cp₂, sealSpec_pub ?_, cv₁, cw₁, cv₂, cw₂⟩
    simp only [State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, r3₁, r4₁, r5₁, r6₁, r7₁,
      r8₁, r9₁, r10₁, r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, r9₂, r10₂, hc₁.sp, hc₂.sp, hB, hc₁.arg h₁, hc₂.arg h₂,
      hc₁.arg1 h₁, hc₂.arg1 h₂, C, Nn, Ad, Dst, Tg, Bk, q3, q4, q5, q6, q7, q8, a0, a1, a2, a3, and_self])
    (called_wp hv h₁ hc₁) (called_wp hv h₂ hc₂) fun z₁ z₂ hz₁ hz₂ => ?_
  -- The return address back.
  exact rel_taint [] (by rw [hz₁.sp, hz₂.sp, hB]) (by simp) (by taint_decide)

/-! ## `Verified` -/

open VG.Proof.ChaCha20Poly1305.RISCV64.Gather (filter_true' filter_false' filterMap_some' filterMap_none' pairFacts_ro)

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

theorem gatherPre_of_spec {s : State}
    (h : (Proof.AesGcm.sealGatherBitslicedRoundsContract RISCV64.abi 4672).pre s) : gatherPre s := by
  sig_pre [Proof.AesGcm.sealGatherBitslicedRoundsContract, Spec.Gcm.sealGatherBitslicedSig,
    Spec.Gcm.sealGatherBitslicedPre, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, Spec.Gcm.bitslicedParam,
    RISCV64.abi, RISCV64.argRegs, stackArgs_four, List.append_eq] at h
  simp only [List.map_append, List.filter_append, List.filter_map, List.map_map, List.filterMap_append,
    List.filterMap_map, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil, Function.comp_def,
    Bool.not_false, Bool.false_eq_true, ite_true, ite_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false, Bool.cond_true,
    List.filterMap_cons, List.filterMap_nil, List.append_nil, List.nil_append, Sig.conj, Bool.true_or,
    List.cons_append, Sig.pairFacts, Bool.or_self] at h
  rw [pairFacts_ro _ (by simp)] at h
  obtain ⟨al, w₁, w₂, rd, wr, ⟨cd, ct, nd, nt, ad, at_, dt, dbk, dds, ⟨dl, da⟩, tbk, tds, ⟨tl, ta⟩, -⟩, bc, bn, ba,
    bd, bt, bbk, ⟨bds, bl, barg⟩, oc, on, oa, od, ot, ob, ⟨ods, ol⟩, hR, hg, hbk, ca, bal⟩ := h
  exact ⟨by rw [rd]; simp, wr, cd, ct, nd, nt, ad, at_, dds.symm, tds.symm, dbk.symm, tbk.symm,
    fun r hr' => ⟨(dl r hr').symm, (tl r hr').symm⟩, dt, da, ta, bc, bn, ba, bds, bbk, bl, barg, bd, bt, oc, on,
    oa, ods, ol, od, ot, ob, al, w₁, w₂, hR, hg, ca, bal, hbk⟩

theorem gatherPost_of {s s' : State} (h : gatherPost s s') :
    (Proof.AesGcm.sealGatherBitslicedRoundsContract RISCV64.abi 4672).post s s' := by
  sig_post [Proof.AesGcm.sealGatherBitslicedRoundsContract, Spec.Gcm.sealGatherBitslicedSig, Spec.Gcm.sealGatherSig,
    Spec.Gcm.bitslicedParam, Proof.AesGcm.sealGatherBitslicedRoundsPost, Proof.AesGcm.sealGatherRoundsPost,
    RISCV64.abi, RISCV64.argRegs, stackArgs_four, List.append_eq]
  exact fun _ _ => h

theorem gatherPub_of {s₁ s₂ : State}
    (hp : (Proof.AesGcm.sealGatherBitslicedRoundsContract RISCV64.abi 4672).pub s₁ s₂) : gatherPub s₁ s₂ := by
  sig_pub [Proof.AesGcm.sealGatherBitslicedRoundsContract, Spec.Gcm.sealGatherBitslicedSig,
    Spec.Gcm.sealGatherBitslicedPre, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, Spec.Gcm.bitslicedParam,
    RISCV64.abi, RISCV64.argRegs, stackArgs_four, List.append_eq, List.getD] at hp
  obtain ⟨qsp, q3, q4, q5, q6, q7, q8, q9, q10, a0, a1, a2, a3, hd⟩ := hp
  exact ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, a0, a1, a2, a3, hd⟩

/-- The memory of a state satisfying the precondition: `tag` at `0x5000` and
`bk` at `0x7000`, the third and fourth stack arguments, at `sp + 16` and
`sp + 24`, and zeros elsewhere. -/
def gatherBsSatMem : Mem := fun a =>
  bif Nat.beq a.toNat 0x9011 then 0x50 else bif Nat.beq a.toNat 0x9019 then 0x70 else 0

theorem gatherBsSatMem_zero {p : Addr} {n : Nat} (h : p.toNat + n ≤ 0x9011) :
    ∀ i < n, gatherBsSatMem (p + BitVec.ofNat 64 i) = 0 := fun i hi => by
  obtain e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h, hi]
  obtain hb : ∀ k, 0x9011 ≤ k → Nat.beq (p.toNat + i) k = false := fun k hk => by
    rw [← Bool.not_eq_true, Nat.beq_eq]; omega_using [h, hi, hk]
  simp only [gatherBsSatMem, e, hb _ (Nat.le_refl _), hb 0x9019 (by decide), Bool.cond_false]

/-- A state satisfying the precondition of `vg_aes_gcm_seal_gather_bitsliced`:
no slices, nonce, additional data or text. -/
def gatherBsSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem := gatherBsSatMem
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x7000, 1248⟩, ⟨0x4000, 0⟩, ⟨0x9000, 32⟩]
  wr := [⟨0, 0⟩, ⟨0x5000, 16⟩]

theorem gatherBsSat_pre : ∃ s, (Proof.AesGcm.sealGatherBitslicedRoundsContract RISCV64.abi 4672).pre s := by
  refine ⟨gatherBsSat, ?_⟩
  sig_pre [Proof.AesGcm.sealGatherBitslicedRoundsContract, Spec.Gcm.sealGatherBitslicedSig,
    Spec.Gcm.sealGatherBitslicedPre, Spec.Gcm.sealGatherSig, Spec.Gcm.sealGatherPre, Spec.Gcm.bitslicedParam,
    RISCV64.abi, RISCV64.argRegs, stackArgs_four, List.append_eq, stackArg, stackArgAddr, List.getD,
    gatherBsSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact Proof.AesGcm.ctxSlicedRepr_of_zero (gatherBsSatMem_zero (by decide)) (gatherBsSatMem_zero (by decide))

theorem gather_implies :
    gatherBsRISCV64.Implies (Proof.AesGcm.sealGatherBitslicedRoundsContract RISCV64.abi 4672) :=
  ⟨fun _ h => gatherPre_of_spec h, fun _ _ _ h => gatherPost_of h, fun _ _ _ _ h => gatherPub_of h, gatherBsSat_pre⟩

theorem sealGatherBs_correct [VG.Proof.Gcm.RISCV64.GhashLaw] (s : State) (hs : gatherBsRISCV64.pre s) :
    ∃ t s', Exec isa sealGatherBs s t s' ∧ abiPreserved s s' ∧ gatherBsRISCV64.post s s' :=
  sealGatherBs_wp sealBs_framed.1 hs

theorem sealGatherBs_verified [VG.Proof.Gcm.RISCV64.GhashLaw] :
    Verified RISCV64.target sealGatherBs (Proof.AesGcm.sealGatherBitslicedRoundsContract RISCV64.abi 4672) :=
  Verified.of_correct (k := gatherBsRISCV64) sealGatherBs_correct
    (sealGatherBs_ct sealBs_framed.1 sealBs_framed.2.1) gather_implies

/-! ## The registration -/

open VG.RISCV64.Scrub

theorem gatherBsOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherBitslicedContract abi stack) (Spec.Gcm.sealGatherBitslicedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (Proof.AesGcm.sealGatherBitslicedPost_out _)

/-- `vg_aes_gcm_seal_gather_bitsliced` as emitted (`Impl.AesGcm.RISCV64.Fn.sealGatherBs`) meets its
contract in constant time and returns without secret residue: the theorem its registration binds. -/
theorem sealGatherBs_scrubbed [VG.Proof.Gcm.RISCV64.GhashLaw] :
    VerifiedScrubbed target Impl.AesGcm.RISCV64.Fn.sealGatherBs
      (Spec.Gcm.sealGatherBitslicedContract abi 4672) 0 :=
  verifiedScrubbedSelT (api := Spec.Gcm.sealGatherBitslicedApi) (W := 4672)
    { code := sealGatherBs
      verified := Proof.AesGcm.sealGatherBitsliced_keyed sealGatherBs_verified }
    [(2048, [(0, 256)]), (2048, [(0, 256)]), (176, [(0, 22)])] []
    (gatherBsOut _) (by lit_decide) (hbp_nil _) ⟨_, by taint_decide_ct⟩

end VG.Proof.AesGcm.RISCV64.GatherBs
