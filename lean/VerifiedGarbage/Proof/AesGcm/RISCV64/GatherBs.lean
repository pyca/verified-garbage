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

/-! # RISC-V bitsliced AES-GCM gather contract and caller layout

The direct gather entry point consumes the public descriptor layout and meets
the keyed gather contract through its round-key representation.
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

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen CtxSlicedRepr)
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

theorem argIn : argR s ∈ s.rd := by rw [h.pre.1]; simp

end Lay

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

/-! ## The registration -/

open VG.RISCV64.Scrub

theorem gatherBsOut (stack : Nat) :
    PostOut (Spec.Gcm.sealGatherBitslicedContract abi stack) (Spec.Gcm.sealGatherBitslicedSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain (Proof.AesGcm.sealGatherBitslicedPost_out _)

end VG.Proof.AesGcm.RISCV64.GatherBs
