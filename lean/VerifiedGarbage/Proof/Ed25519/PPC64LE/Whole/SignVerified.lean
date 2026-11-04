module

import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignCached
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKeyVerified
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Sha512OK
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.SignCached
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Whole
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Spec.Ed25519.ExpandedSign
import VerifiedGarbage.Proof.Ed25519.Expanded
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.VectorTaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKeyVerified
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBase
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts

/-!
# `vg_ed25519_sign_cached` on PPC64LE, verified

The code meets `signCachedContract` under `abi.withConsts combConsts` (the
comb's table, which `vg_ed25519_scalar_base` reads) with the frame as one more
argument (`Sig.scratchContract`) and 48 bytes of stack for the callees' frames
(the proof against the contract's facts by register, `signC`: `signR` without
the table, and what the table adds), and, in a frame of 320 bytes whose first
224 it zeroes before returning (`Verified.stackScratchWipedC`), the contract
itself. Only the pointers, the length and the table's address are public: the
pointers and the length stay in `r20`–`r25`, which no function called writes,
so the taint analysis (`taint_decide`, under `vectorTaintSym`) sees them public
throughout, callees included.

`signExpanded` meets `signExpandedContract` the same way (`signCE`,
`signExpanded_framed`), with the seed's digest and public key of
`PublicKeyVerified`'s `satMemE` in its witness.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.PPC64LE (combSym combWords combConsts)
open VG.Proof.Ed25519.PPC64LE (combWords_length TBL tbl_of_consts rd_of_consts consts_implies base_ok)

/-- The contract by register: `out` in `r3`, `seed` in `r4`, `pk` in `r5`, the message in `r6`
(`len` in `r7`), `scratch` in `r8`, the frame in `r9`; without the comb's table. -/
def signR : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 64⟩
    let seed : Region := ⟨s.gpr .r4, 32⟩
    let pk : Region := ⟨s.gpr .r5, 32⟩
    let msg : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let sc : Region := ⟨s.gpr .r8, 8192⟩
    let fr : Region := ⟨s.gpr .r9, 288⟩
    s.rd = [seed, pk, msg] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint seed ∧ out.Disjoint pk ∧
      out.Disjoint msg ∧ out.Disjoint sc ∧ out.Disjoint fr ∧ seed.Disjoint sc ∧ seed.Disjoint fr ∧
      pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧ msg.Disjoint fr ∧ sc.Disjoint fr ∧
      48 ≤ s.sp.toNat ∧ (below s.sp 48).Disjoint out ∧ (below s.sp 48).Disjoint seed ∧
      (below s.sp 48).Disjoint pk ∧ (below s.sp 48).Disjoint msg ∧ (below s.sp 48).Disjoint sc ∧
      (below s.sp 48).Disjoint fr ∧ bytesAt s.mem (s.gpr .r5) 32 = Spec.Ed25519.publicKey (bytesAt s.mem (s.gpr .r4) 32)
  post s s' := bytesAt s'.mem (s.gpr .r3) 64 =
    Spec.Ed25519.sign (bytesAt s.mem (s.gpr .r4) 32) (bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.sp = s₂.sp

/-- `signR` with the comb's table (`abi.withConsts`). -/
def signC : Contract isa where
  pre s := signR.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 48 s
  post := signR.post
  pub s₁ s₂ := signR.pub s₁ s₂ ∧ s₁.syms combSym = s₂.syms combSym

theorem sign_ok (B : BaseOk) (s : State) (hs : signC.pre s) :
    ∃ t s', Exec isa signCached s t s' ∧ abiPreserved s s' ∧ signC.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, x⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp, stripConsts_mem] at *
  obtain ⟨-, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .r4, 32⟩, ⟨s.gpr .r5, 32⟩, msgR s, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ signW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [signW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ :=
    signCached_wp sha512OK B ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, tfit, words, tW⟩ x
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

theorem sign_ct : ConstantTime isa signC.pre signC.pub signCached :=
  VG.Taint.constantTime (A := vectorTaintSym [combSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (fun s₁ s₂ _ _ ⟨⟨p3, p4, p5, p6, p7, p8, p9, psp⟩, hsy⟩ => ⟨⟨psp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- A state satisfying the precondition, with memory `m`, without the table. -/
def signSat (m : Mem) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x2100 | .r6 => 0x3000 | .r8 => 0x4000 | .r9 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem := m
  rd := [⟨0x2000, 32⟩, ⟨0x2100, 32⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩]

theorem signR_implies : signR.Implies (Sig.scratchContract PPC64LE.abi Spec.Ed25519.signCachedSig "frame" .u8 288
    (Proof.Ed25519.WholeLocal.signCachedPre PPC64LE.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost PPC64LE.abi.ptrBits) true 48) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signR, PPC64LE.abi, PPC64LE.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signR, PPC64LE.abi, PPC64LE.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          Proof.Ed25519.WholeLocal.signCachedPost, signR, PPC64LE.abi, PPC64LE.argRegs]
      sat := by
        obtain ⟨m, hm⟩ : ∃ m : Mem, bytesAt m 0x2100 32 = Spec.Ed25519.publicKey (bytesAt m 0x2000 32) :=
          ⟨_, Proof.Ed25519.WholeLocal.sat_pk⟩
        refine ⟨signSat m, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
          PPC64LE.abi, PPC64LE.argRegs, signSat]
        sig_and_intros
        all_goals first
          | exact hm
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- The seed and public key of `satMem` below `0x100000`, the comb's table above. -/
@[irreducible] def signMem : Mem := fun a => if a.toNat < 0x100000 then Proof.Ed25519.WholeLocal.satMem a else tblMem a

theorem signMem_held : ∀ i < combWords.length,
    signMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  rw [combWords_length] at hi
  rw [← tblMem_held i (by rw [combWords_length]; exact hi)]
  refine Mem.readW_congr fun j hj => ?_
  have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j).toNat = 0x100000 + 8 * i + j := by
    rw [show (0x100000 : Addr) = BitVec.ofNat 64 0x100000 from rfl]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [signMem, e, show ¬ 0x100000 + 8 * i + j < 0x100000 by omega, ↓reduceIte]

theorem signMem_bytes {p : Addr} {n : Nat} (h : p.toNat + n ≤ 0x100000) :
    bytesAt signMem p n = bytesAt Proof.Ed25519.WholeLocal.satMem p n := by
  unfold bytesAt
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.mp hi
  have e : (p + BitVec.ofNat 64 i).toNat = p.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [signMem, e, show p.toNat + i < 0x100000 by omega, ↓reduceIte]

theorem signMem_pk : bytesAt signMem 0x2100 32 = Spec.Ed25519.publicKey (bytesAt signMem 0x2000 32) := by
  rw [signMem_bytes (by decide), signMem_bytes (by decide)]
  exact Proof.Ed25519.WholeLocal.sat_pk

/-- `signSat` with the table. -/
def signSatC : State :=
  { signSat signMem with rd := (signSat signMem).rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem signC_sat : (Sig.scratchContract (PPC64LE.abi.withConsts combConsts) Spec.Ed25519.signCachedSig "frame"
    .u8 288 (Proof.Ed25519.WholeLocal.signCachedPre PPC64LE.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost PPC64LE.abi.ptrBits) true 48).pre signSatC := by
  have hl := combWords_length
  have held := signMem_held
  have hm := signMem_pk
  change (Sig.scratchContract (PPC64LE.abi.withConsts [(combSym, combWords)]) Spec.Ed25519.signCachedSig "frame"
    .u8 288 (Proof.Ed25519.WholeLocal.signCachedPre PPC64LE.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost PPC64LE.abi.ptrBits) true 48).pre signSatC
  generalize combWords = W' at hl held ⊢
  generalize e : signSatC = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.signCachedPre,
    PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact hm
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem signC_implies : signC.Implies (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
    Spec.Ed25519.signCachedSig "frame" .u8 288 (Proof.Ed25519.WholeLocal.signCachedPre PPC64LE.abi.ptrBits)
    (Proof.Ed25519.WholeLocal.signCachedPost PPC64LE.abi.ptrBits) true 48) :=
  consts_implies (kR := signR) signR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨signSatC, signC_sat⟩

theorem signCached_verified :
    Verified PPC64LE.target signCached (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
      Spec.Ed25519.signCachedSig "frame" .u8 288 (Proof.Ed25519.WholeLocal.signCachedPre PPC64LE.abi.ptrBits)
      (Proof.Ed25519.WholeLocal.signCachedPost PPC64LE.abi.ptrBits) true 48) :=
  Verified.of_correct (sign_ok base_ok) sign_ct signC_implies

/-- A state satisfying `vg_ed25519_sign_cached`'s precondition, without the frame. -/
def signFrameSat : State := { signSatC with wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩] }

theorem signFrameSat_pre : ∃ s, (Spec.Ed25519.signCachedContract (PPC64LE.abi.withConsts combConsts)
    (48 + 320)).pre s := by
  refine ⟨signFrameSat, ?_⟩
  have hl := combWords_length
  have held := signMem_held
  have hm := signMem_pk
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : signFrameSat = s
  sig_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig, Spec.Ed25519.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact hm
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 320 bytes, whose first 224 it zeroes before returning. -/
theorem signCached_framed :
    Verified PPC64LE.target signCachedCode
      (Spec.Ed25519.signCachedContract (PPC64LE.abi.withConsts combConsts) (48 + 320)) :=
  Verified.stackScratchWipedC (c₀ := (combSym, combWords)) (cs := []) (sig := Spec.Ed25519.signCachedSig) (nm := "frame") (e := .u8) (n := 288)
    (pre := Proof.Ed25519.WholeLocal.signCachedPre PPC64LE.abi.ptrBits)
    (post := Proof.Ed25519.WholeLocal.signCachedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 320)
    (words := 28) signCached_verified (by decide) (by decide) (by decide)
    (Proof.Ed25519.WholeLocal.signCachedPre_local _) (Proof.Ed25519.WholeLocal.signCachedPost_local _)
    (Proof.Ed25519.WholeLocal.signCachedPostOut_local _) signFrameSat_pre

/-! ## `vg_ed25519_sign_expanded` -/

/-- The contract by register: `out` in `r3`, the seed's digest at `r4`, `pk` in `r5`, the message in
`r6` (`len` in `r7`), `scratch` in `r8`, the frame in `r9`; without the comb's table. -/
def signRE : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 64⟩
    let dg : Region := ⟨s.gpr .r4, 64⟩
    let pk : Region := ⟨s.gpr .r5, 32⟩
    let msg : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let sc : Region := ⟨s.gpr .r8, 8192⟩
    let fr : Region := ⟨s.gpr .r9, 288⟩
    s.rd = [dg, pk, msg] ∧ s.wr = [out, sc, fr] ∧ out.Disjoint dg ∧ out.Disjoint pk ∧
      out.Disjoint msg ∧ out.Disjoint sc ∧ out.Disjoint fr ∧ dg.Disjoint sc ∧ dg.Disjoint fr ∧
      pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧ msg.Disjoint fr ∧ sc.Disjoint fr ∧
      48 ≤ s.sp.toNat ∧ (below s.sp 48).Disjoint out ∧ (below s.sp 48).Disjoint dg ∧
      (below s.sp 48).Disjoint pk ∧ (below s.sp 48).Disjoint msg ∧ (below s.sp 48).Disjoint sc ∧
      (below s.sp 48).Disjoint fr ∧
      ∃ seed : List Byte, seed.length = 32 ∧ bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed ∧
        bytesAt s.mem (s.gpr .r5) 32 = Spec.Ed25519.publicKey seed
  post s s' := ∀ seed : List Byte, seed.length = 32 → bytesAt s.mem (s.gpr .r4) 64 = Spec.Sha512.sha512 seed →
    bytesAt s'.mem (s.gpr .r3) 64 = Spec.Ed25519.sign seed (bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
  pub := signR.pub

/-- `signRE` with the comb's table. -/
def signCE : Contract isa where
  pre s := signRE.pre (stripConsts combConsts s) ∧ ConstsOk combConsts 48 s
  post := signRE.post
  pub := signC.pub

theorem signE_ok (B : BaseOk) (s : State) (hs : signCE.pre s) :
    ∃ t s', Exec isa signExpanded s t s' ∧ abiPreserved s s' ∧ signCE.post s s' := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, seed, -, hsd, hpk⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp, stripConsts_mem] at *
  obtain ⟨-, tfit, words, twr, tres⟩ := tbl_of_consts hk
  have hrd : s.rd = [⟨s.gpr .r4, 64⟩, ⟨s.gpr .r5, 32⟩, msgR s, TBL (s.syms combSym)] := rd_of_consts hk a
  have tW : ∀ r ∈ signW s, (TBL (s.syms combSym)).Disjoint r := fun r hr => by
    simp only [signW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact twr _ (by rw [b]; simp)
    · exact tres _ (below_reserved s)
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ :=
    signExpanded_wp sha512OK B ⟨hrd, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, u, v, w, tfit, words, tW⟩
      hsd hpk
  refine ⟨t, s', he, ⟨hg, hsp, hlr⟩, fun seed' _ hs' => ?_⟩
  rw [hq]
  exact Proof.Ed25519.sign_of_sha512_eq (hsd.symm.trans hs') _

theorem signE_ct : ConstantTime isa signCE.pre signCE.pub signExpanded :=
  VG.Taint.constantTime (A := vectorTaintSym [combSym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8, .r9])
    (fun s₁ s₂ _ _ ⟨⟨p3, p4, p5, p6, p7, p8, p9, psp⟩, hsy⟩ => ⟨⟨psp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption⟩, fun n hn => by
        simp only [List.mem_singleton] at hn; subst hn; exact hsy⟩) (by taint_decide)

/-- `signExpandedContract`'s precondition and postcondition. -/
def signEPre (pb : Nat) : Curry (Spec.Ed25519.signExpandedSig.words pb) (Mem → Prop) :=
  fun _out expanded pk _message _len _scratch m =>
    ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m expanded 64 = Spec.Sha512.sha512 seed ∧
      bytesAt m pk 32 = Spec.Ed25519.publicKey seed

def signEPost (pb : Nat) : Spec.Ed25519.signExpandedSig.Post pb :=
  fun out expanded _pk message len _scratch m m' _ =>
    ∀ seed : List Byte, seed.length = 32 → bytesAt m expanded 64 = Spec.Sha512.sha512 seed →
      bytesAt m' out 64 = Spec.Ed25519.sign seed (bytesAt m message len.toNat)

theorem signEPre_local (pb : Nat) : ∀ vs m₁ m₂, vs.length = (Spec.Ed25519.signExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Ed25519.signExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Ed25519.signExpandedSig.words pb) (signEPre pb) vs m₁ →
    Curry.apply (Spec.Ed25519.signExpandedSig.words pb) (signEPre pb) vs m₂ := by
  intro vs m₁ m₂ hlen hb h
  match vs, hlen with
  | [o, dg, pk, msg, l, sc], _ =>
    simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m₁ dg 64 = Spec.Sha512.sha512 seed ∧
      bytesAt m₁ pk 32 = Spec.Ed25519.publicKey seed at h
    change ∃ seed : List Byte, seed.length = 32 ∧ bytesAt m₂ dg 64 = Spec.Sha512.sha512 seed ∧
      bytesAt m₂ pk 32 = Spec.Ed25519.publicKey seed
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.2.2.1, Proof.Ed25519.WholeLocal.bytesAt_congr hb.2.1]
    exact h

theorem signEPost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (Spec.Ed25519.signExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Ed25519.signExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Ed25519.signExpandedSig.words pb) (signEPost pb) vs m₁ m' r →
    Curry.apply (Spec.Ed25519.signExpandedSig.words pb) (signEPost pb) vs m₂ m' r := by
  intro vs m₁ m₂ m' r hlen hb h
  match vs, hlen with
  | [o, dg, pk, msg, l, sc], _ =>
    simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m₁ dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m' o 64 = Spec.Ed25519.sign seed (bytesAt m₁ msg (l.setWidth pb).toNat) at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m₂ dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m' o 64 = Spec.Ed25519.sign seed (bytesAt m₂ msg (l.setWidth pb).toNat)
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.2.1,
      Proof.Ed25519.WholeLocal.bytesAt_congr (Proof.Ed25519.WholeLocal.slice_agree pb hb.2.2.2.1)]
    exact h

theorem signEPostOut_local (pb : Nat) : ∀ vs m m₁ m₂ r,
    vs.length = (Spec.Ed25519.signExpandedSig.words pb).length →
    (∀ b ∈ Sig.bufs Spec.Ed25519.signExpandedSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (Spec.Ed25519.signExpandedSig.words pb) (signEPost pb) vs m m₁ r →
    Curry.apply (Spec.Ed25519.signExpandedSig.words pb) (signEPost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  match vs, hlen with
  | [o, dg, pk, msg, l, sc], _ =>
    simp only [Spec.Ed25519.signExpandedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m₁ o 64 = Spec.Ed25519.sign seed (bytesAt m msg (l.setWidth pb).toNat) at h
    change ∀ seed : List Byte, seed.length = 32 → bytesAt m dg 64 = Spec.Sha512.sha512 seed →
      bytesAt m₂ o 64 = Spec.Ed25519.sign seed (bytesAt m msg (l.setWidth pb).toNat)
    rw [Proof.Ed25519.WholeLocal.bytesAt_congr hb.1]
    exact h

theorem satMemTE_key : bytesAt satMemTE 0x2100 32 = Spec.Ed25519.publicKey Proof.Ed25519.WholeLocal.satSeed := by
  rw [satMemTE_bytes (by decide), sat_keyE]; rfl

/-- A state satisfying the precondition, without the table. -/
def signSatE : State := { signSat satMemE with rd := [⟨0x2000, 64⟩, ⟨0x2100, 32⟩, ⟨0x3000, 0⟩] }

theorem signRE_implies : signRE.Implies (Sig.scratchContract PPC64LE.abi Spec.Ed25519.signExpandedSig "frame" .u8
    288 (signEPre PPC64LE.abi.ptrBits) (signEPost PPC64LE.abi.ptrBits) true 48) :=
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, PPC64LE.abi,
          PPC64LE.argRegs]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signExpandedSig, Spec.Ed25519.scratchWords, signEPre, signEPost, signRE, signR, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        have hd : bytesAt satMemE 0x2000 64 = Spec.Sha512.sha512 Proof.Ed25519.WholeLocal.satSeed := sat_digestE
        have hk : bytesAt satMemE 0x2100 32 = Spec.Ed25519.publicKey Proof.Ed25519.WholeLocal.satSeed := sat_keyE
        refine ⟨signSatE, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed25519.signExpandedSig, Spec.Ed25519.scratchWords, signEPre, PPC64LE.abi, PPC64LE.argRegs,
          signSatE, signSat]
        sig_and_intros
        all_goals first
          | exact ⟨_, satSeed_length, hd, hk⟩
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide) }

/-- `signSatE` with the table. -/
def signSatCE : State :=
  { signSatE with mem := satMemTE, rd := signSatE.rd ++ [⟨0x100000, 49152⟩], syms := fun _ => 0x100000 }

theorem signCE_sat : (Sig.scratchContract (PPC64LE.abi.withConsts combConsts) Spec.Ed25519.signExpandedSig
    "frame" .u8 288 (signEPre PPC64LE.abi.ptrBits) (signEPost PPC64LE.abi.ptrBits) true 48).pre signSatCE := by
  have hl := combWords_length
  have held := satMemTE_held
  have hd := satMemTE_digest
  have hk := satMemTE_key
  change (Sig.scratchContract (PPC64LE.abi.withConsts [(combSym, combWords)]) Spec.Ed25519.signExpandedSig
    "frame" .u8 288 (signEPre PPC64LE.abi.ptrBits) (signEPost PPC64LE.abi.ptrBits) true 48).pre signSatCE
  generalize combWords = W' at hl held ⊢
  generalize e : signSatCE = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
    Spec.Ed25519.signExpandedSig, Spec.Ed25519.scratchWords, signEPre,
    PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨_, satSeed_length, hd, hk⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩, ⟨0x8000, 288⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem signCE_implies : signCE.Implies (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
    Spec.Ed25519.signExpandedSig "frame" .u8 288 (signEPre PPC64LE.abi.ptrBits)
    (signEPost PPC64LE.abi.ptrBits) true 48) :=
  consts_implies (kR := signRE) signRE_implies (fun _ _ h => h) (fun _ _ h => h) ⟨signSatCE, signCE_sat⟩

theorem signExpanded_verified :
    Verified PPC64LE.target signExpanded (Sig.scratchContract (PPC64LE.abi.withConsts combConsts)
      Spec.Ed25519.signExpandedSig "frame" .u8 288 (signEPre PPC64LE.abi.ptrBits)
      (signEPost PPC64LE.abi.ptrBits) true 48) :=
  Verified.of_correct (signE_ok base_ok) signE_ct signCE_implies

/-- A state satisfying `vg_ed25519_sign_expanded`'s precondition, without the frame. -/
def signFrameSatE : State := { signSatCE with wr := [⟨0x1000, 64⟩, ⟨0x4000, 8192⟩] }

theorem signFrameSatE_pre : ∃ s, (Spec.Ed25519.signExpandedContract (PPC64LE.abi.withConsts combConsts)
    (48 + 320)).pre s := by
  refine ⟨signFrameSatE, ?_⟩
  have hl := combWords_length
  have held := satMemTE_held
  have hd := satMemTE_digest
  have hk := satMemTE_key
  rw [show combConsts = [(combSym, combWords)] from rfl]
  generalize combWords = W' at hl held ⊢
  generalize e : signFrameSatE = s
  sig_pre [Spec.Ed25519.signExpandedContract, Spec.Ed25519.signExpandedSig, Spec.Ed25519.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact ⟨_, satSeed_length, hd, hk⟩
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x1000, 64⟩ : Region), ⟨0x4000, 8192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 320 bytes, whose first 224 it zeroes before returning. -/
theorem signExpanded_framed :
    Verified PPC64LE.target signExpandedCode
      (Spec.Ed25519.signExpandedContract (PPC64LE.abi.withConsts combConsts) (48 + 320)) :=
  Verified.stackScratchWipedC (c₀ := (combSym, combWords)) (cs := []) (sig := Spec.Ed25519.signExpandedSig)
    (nm := "frame") (e := .u8) (n := 288) (pre := signEPre PPC64LE.abi.ptrBits)
    (post := signEPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 320)
    (words := 28) signExpanded_verified (by decide) (by decide) (by decide)
    (signEPre_local _) (signEPost_local _) (signEPostOut_local _) signFrameSatE_pre

end VG.Proof.Ed25519.PPC64LE.Whole
