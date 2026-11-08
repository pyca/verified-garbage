module

import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Lit

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyMsg
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Sha512OK
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed25519.WholeLocal
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Ed25519.VerifyBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
public import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowRhs
import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowCT
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.VerifyWindow
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyMsg
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Ed25519.WholeLocal
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Ed25519.VerifyBytes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-!
# `vg_ed25519_verify` on PPC64LE, verified

The code meets `verifyContract` under `abi.withConsts bConsts` (the static of
the cached `-[1]B … -[15]B`, which `verify_equation` reads) with the frame as
one more argument (`Sig.scratchContract`) and 48 bytes of stack for the
callees' frames: the proof against the contract's facts by register (`verC`:
`verR` without the static, and what the static adds), which it implies
(`bconsts_implies`), with the windows' proofs (`rhs_ok`, `rhs_ct`), and a
state satisfying it, with the static at `0x100000` (`bMem`). In a frame of
224 bytes (`Verified.stackScratchLC`), it meets the contract itself. The
contract declares the inputs public. Two runs on the same inputs leak the
same trace (`ver_ct`): the taint analysis checks the challenge's computation
(only the pointers and the length matter to it) and the restores, and the
call of `verify_equation` leaks the same trace in both runs by its own
constant time, since its arguments, the challenge and the static's address
included, are the same in both (`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole
open VG.Spec.Ed25519 (bytesAt)
open VG.Impl.Ed25519.PPC64LE (bSym bWords bConsts)
open VG.Proof.Ed25519.PPC64LE (bWords_length bstat_of_consts rd_of_bconsts rhs_ok rhs_ct RhsOk RhsCT)

/-- The contract by register: `pk` in `r3`, the message in `r4` (`len` in `r5`), the signature in
`r6`, `scratch` in `r7`, the frame in `r8`. -/
def verR : Contract isa where
  pre s :=
    let pk : Region := ⟨s.gpr .r3, 32⟩
    let msg : Region := ⟨s.gpr .r4, (s.gpr .r5).toNat⟩
    let sig : Region := ⟨s.gpr .r6, 64⟩
    let sc : Region := ⟨s.gpr .r7, 8192⟩
    let fr : Region := ⟨s.gpr .r8, 192⟩
    s.rd = [pk, msg, sig] ∧ s.wr = [sc, fr] ∧ pk.Disjoint sc ∧ pk.Disjoint fr ∧ msg.Disjoint sc ∧
      msg.Disjoint fr ∧ sig.Disjoint sc ∧ sig.Disjoint fr ∧ sc.Disjoint fr ∧ 48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint pk ∧ (below s.sp 48).Disjoint msg ∧ (below s.sp 48).Disjoint sig ∧
      (below s.sp 48).Disjoint sc ∧ (below s.sp 48).Disjoint fr
  post s s' := (s'.gpr .r3).setWidth 32 = verResult s
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.sp = s₂.sp ∧
    (bytesAt s₁.mem (s₁.gpr .r3) 32 ++ bytesAt s₁.mem (s₁.gpr .r4) (s₁.gpr .r5).toNat ++
      bytesAt s₁.mem (s₁.gpr .r6) 64).map (·.toNat) =
    (bytesAt s₂.mem (s₂.gpr .r3) 32 ++ bytesAt s₂.mem (s₂.gpr .r4) (s₂.gpr .r5).toNat ++
      bytesAt s₂.mem (s₂.gpr .r6) 64).map (·.toNat)

/-- `verR` with the static of `verify_equation` (`abi.withConsts bConsts`). -/
def verC : Contract isa where
  pre s := verR.pre (stripConsts bConsts s) ∧ ConstsOk bConsts 48 s
  post := verR.post
  pub s₁ s₂ := verR.pub s₁ s₂ ∧ s₁.syms bSym = s₂.syms bSym

theorem verC_pre {s : State} (h : verC.pre s) : VerPre s := by
  obtain ⟨⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o⟩, hk⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at *
  obtain ⟨-, tfit, words, twr, tres⟩ := bstat_of_consts hk
  have hrd : s.rd = [⟨s.gpr .r3, 32⟩, vmsgR s, ⟨s.gpr .r6, 64⟩, vtbR s] := rd_of_bconsts hk a
  have hB : below s.sp 48 ∈ PPC64LE.abi.reserved 48 s := by
    show _ ∈ stackBelow s.sp 48
    rw [stackBelow_pos _ (by decide)]; simp
  exact ⟨hrd, b, c, d, e, f, g, h', i, j, k, l, m, n, o, tfit, words, twr _ (by rw [b]; simp),
    twr _ (by rw [b]; simp), tres _ hB⟩

theorem ver_ok (hR : RhsOk) (s : State) (hs : verC.pre s) :
    ∃ t s', Exec isa verifyMessage s t s' ∧ abiPreserved s s' ∧ verC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ := verifyMessage_wp sha512OK hR (verC_pre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

/-- Two runs on the same public data, as `RelCT.constantTime` relates them. -/
abbrev VP (s₁ s₂ : State) : Prop := verC.pre s₁ ∧ verC.pre s₂ ∧ verC.pub s₁ s₂

/-- The inputs agree in two such runs. -/
theorem vp_bytes {s₁ s₂ : State} (h : VP s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .r3) 32 = bytesAt s₂.mem (s₂.gpr .r3) 32 ∧ vmsgB s₁ = vmsgB s₂ ∧
      bytesAt s₁.mem (s₁.gpr .r6) 64 = bytesAt s₂.mem (s₂.gpr .r6) 64 := by
  obtain ⟨-, -, ⟨-, -, p5, -, -, -, -, pl⟩, -⟩ := h
  have hl : ∀ (s : State) (p : Addr) (n : Nat), (bytesAt s.mem p n).length = n := fun _ _ _ => by
    simp [bytesAt]
  exact bytes_of_leak (by rw [hl, hl]) (by rw [hl, hl, p5]) pl

/-- The restores, with `F` in `r25` in both runs. -/
theorem restore_ct {P : State → State → Prop}
    (hp : ∀ t₁ t₂, P t₁ t₂ → t₁.sp = t₂.sp ∧ t₁.gpr .r25 = t₂.gpr .r25) :
    RelCT isa P (.block (restoreRegs .r25 128 verifyRegs)) fun _ _ => True :=
  RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r25]) (fun t₁ t₂ h => ⟨(hp _ _ h).1, fun r hr => by
    simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
    subst hr; exact (hp _ _ h).2⟩) (by taint_decide)

/-- Two runs' entry states. -/
abbrev VPair : Type := {σ : State × State // VP σ.1 σ.2}

theorem ver_ct (hR : RhsOk) (hRC : RhsCT) : ConstantTime isa verC.pre verC.pub verifyMessage := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold verifyMessage
  refine RelCT.seq (R := fun (t₁ t₂ : State) => ∃ σ : VPair, (VerArgs σ.1.1 t₁ ∧ t₁.syms = σ.1.1.syms) ∧
    (VerArgs σ.1.2 t₂ ∧ t₂.syms = σ.1.2.syms)) ?_ <|
    RelCT.seq (R := fun t₁ t₂ => ∃ σ : VPair, VerInv σ.1.1 t₁ ∧ VerInv σ.1.2 t₂) ?_ ?_
  · refine ((RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (fun s₁ s₂ h => ?_)
      (by taint_decide)).wpDep (F := fun (s t : State) => VerArgs s t ∧ t.syms = s.syms) fun s₁ s₂ h =>
        ⟨WP.mono_syms (verifyHash_ok sha512OK (verC_pre h.1)) fun _ a sy => ⟨a, sy⟩,
          WP.mono_syms (verifyHash_ok sha512OK (verC_pre h.2.1)) fun _ a sy => ⟨a, sy⟩⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨⟨(σ₁, σ₂), hp⟩, a₁, a₂⟩
    obtain ⟨-, -, ⟨p3, p4, p5, p6, p7, p8, psp, -⟩, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ => ?_
    refine ((RelCT.callEx (k := Proof.Ed25519.PPC64LE.verifyPPC) (Proof.Ed25519.PPC64LE.verify_ok' hR)
      (Proof.Ed25519.PPC64LE.verify_ct hR hRC) fun t₁ t₂ ⟨⟨a₁, y₁⟩, ⟨a₂, y₂⟩⟩ => ?_).wp
      (F₁ := VerInv σ.1.1) (F₂ := VerInv σ.1.2) fun t₁ t₂ ⟨⟨a₁, y₁⟩, ⟨a₂, y₂⟩⟩ =>
        ⟨WP.mono (verCall_ok hR (verC_pre σ.2.1) a₁ y₁) fun _ h => h.1,
          WP.mono (verCall_ok hR (verC_pre σ.2.2.1) a₂ y₂) fun _ h => h.1⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, i₁, i₂⟩ => ⟨σ, i₁, i₂⟩
    have hp₁ := verC_pre σ.2.1
    have hp₂ := verC_pre σ.2.2.1
    obtain ⟨c₁, w₁⟩ := verCall_covers hp₁ a₁
    obtain ⟨c₂, w₂⟩ := verCall_covers hp₂ a₂
    refine ⟨_, _, _, _, verCall_pre hp₁ a₁ y₁, verCall_pre hp₂ a₂ y₂, ?_, c₁, w₁, c₂, w₂⟩
    obtain ⟨-, -, ⟨p3, p4, p5, p6, p7, p8, psp, -⟩, psy⟩ := σ.2
    obtain ⟨b3, bm, b6⟩ := vp_bytes σ.2
    have ch : vChallenge σ.1.1 = vChallenge σ.1.2 := by
      unfold vChallenge
      rw [← Proof.Ed25519.signatureBytes_take, ← Proof.Ed25519.signatureBytes_take σ.1.2.mem, b6, b3, bm]
    simp only [Proof.Ed25519.PPC64LE.verifyPPC, State.withRegions_gpr, State.withRegions_sp,
      State.withRegions_mem, State.callEntry_sp,
      State.callEntry_mem, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide)]
    rw [a₁.r3, a₂.r3, a₁.r4, a₂.r4, a₁.r5, a₂.r5, a₁.r6, a₂.r6, a₁.inv.sp, a₂.inv.sp, a₁.ch, a₂.ch,
      ver_pk hp₁ a₁.inv, ver_pk hp₂ a₂.inv, ver_sig hp₁ a₁.inv, ver_sig hp₂ a₂.inv, b3, b6, ch]
    exact ⟨p3, p6, p8, p7, psp, rfl, by
      show t₁.syms bSym = t₂.syms bSym
      rw [y₁, y₂]; exact psy⟩
  · exact RelCT.exists_ fun σ => restore_ct fun t₁ t₂ ⟨i₁, i₂⟩ => by
      obtain ⟨-, -, ⟨-, -, -, -, -, p8, psp, -⟩, -⟩ := σ.2
      exact ⟨by rw [i₁.sp, i₂.sp]; exact psp, by
        rw [i₁.regs .r25 (by decide), i₂.regs .r25 (by decide), verV_r25, verV_r25]
        exact p8⟩

/-- A contract by register `kR` without the static implies the signature's contract under
`abi`; so does it with the static, under `abi.withConsts bConsts`. -/
theorem bconsts_implies {kR : Contract isa} {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {st : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (h : kR.Implies (sig.contract abi pre post wa st leak))
    (hpost : ∀ s s', kR.post s s' → kR.post (stripConsts bConsts s) s')
    (hpub : ∀ s₁ s₂, kR.pub (stripConsts bConsts s₁) (stripConsts bConsts s₂) → kR.pub s₁ s₂)
    (hsat : ∃ s, (sig.contract (abi.withConsts bConsts) pre post wa st leak).pre s) :
    Contract.Implies (M := isa)
      { pre := fun s => kR.pre (stripConsts bConsts s) ∧ ConstsOk bConsts st s
        post := kR.post
        pub := fun s₁ s₂ => kR.pub s₁ s₂ ∧ s₁.syms bSym = s₂.syms bSym }
      (sig.contract (abi.withConsts bConsts) pre post wa st leak) where
  pre _ hs := ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (post_stripConsts.mp (h.post (stripConsts bConsts s) s'
    (pre_consts.mp hs).1 (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := ⟨hpub _ _ (h.pub (stripConsts bConsts s₁) (stripConsts bConsts s₂)
      (pre_consts.mp h₁).1 (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)),
    (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

/-- A state satisfying the precondition, without the static. -/
def verSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r7 => 0x4000 | .r8 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 0⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8000, 192⟩]

theorem verR_implies : verR.Implies (Sig.scratchContract PPC64LE.abi Spec.Ed25519.verifySig "frame" .u8 192
    (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true 48
    (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))) := by
  sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.verifyPost, Proof.Ed25519.WholeLocal.verifyLeak, verR,
    verResult, PPC64LE.abi, PPC64LE.argRegs] [verSat] using verSat

/-- The static at `0x100000`. -/
@[irreducible] def bMem : Mem := constMem 0x100000 bWords

theorem bMem_held : ∀ i < bWords.length,
    bMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = bWords.getD i 0 := by
  have h := constMem_held 0x100000 bWords (by rw [bWords_length]; decide)
  unfold bMem
  exact h

/-- `verSat` with the static. -/
def verSatC : State :=
  { verSat with mem := bMem, rd := verSat.rd ++ [⟨0x100000, 1920⟩], syms := fun _ => 0x100000 }

theorem verC_sat : (Sig.scratchContract (PPC64LE.abi.withConsts bConsts) Spec.Ed25519.verifySig "frame"
    .u8 192 (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true
    48 (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))).pre verSatC := by
  have hl := bWords_length
  have held := bMem_held
  dsimp only [bConsts]
  generalize bWords = W' at hl held ⊢
  generalize e : verSatC = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.verifySig,
    Spec.Ed25519.scratchWords, PPC64LE.abi, PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x4000, 8192⟩ : Region), ⟨0x8000, 192⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

theorem verC_implies : verC.Implies (Sig.scratchContract (PPC64LE.abi.withConsts bConsts)
    Spec.Ed25519.verifySig "frame" .u8 192 (Curry.const (fun _ => True) _)
    (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true 48
    (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))) :=
  bconsts_implies (kR := verR) verR_implies (fun _ _ h => h) (fun _ _ h => h) ⟨verSatC, verC_sat⟩

theorem verify_verified :
    Verified PPC64LE.target verifyMessage (Sig.scratchContract (PPC64LE.abi.withConsts bConsts)
      Spec.Ed25519.verifySig "frame" .u8 192 (Curry.const (fun _ => True) _)
      (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true 48
      (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))) :=
  Verified.of_correct (ver_ok rhs_ok) (ver_ct rhs_ok rhs_ct) verC_implies

/-- A state satisfying `vg_ed25519_verify`'s precondition, without the frame. -/
def verFrameSat : State := { verSatC with wr := [⟨0x4000, 8192⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Ed25519.verifyContract (PPC64LE.abi.withConsts bConsts) (48 + 224)).pre s := by
  refine ⟨verFrameSat, ?_⟩
  have hl := bWords_length
  have held := bMem_held
  dsimp only [bConsts]
  generalize bWords = W' at hl held ⊢
  generalize e : verFrameSat = s
  sig_pre [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig, Spec.Ed25519.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x4000, 8192⟩ : Region)] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       rcases hr with rfl <;> exact Region.disjoint_of_sep (by decide))

/-- In its frame of 224 bytes. -/
theorem verify_framed :
    Verified PPC64LE.target verifyCode (Spec.Ed25519.verifyContract (PPC64LE.abi.withConsts bConsts) (48 + 224)) :=
  Verified.stackScratchLC (sig := Spec.Ed25519.verifySig) (nm := "frame") (e := .u8) (n := 192)
    (post := Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 224)
    (leak := some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits)) verify_verified (by decide)
    (by decide)
    (fun vs _ m₂ _ _ _ => (congrFun (Curry.apply_const (fun _ : Mem => True)
      (Spec.Ed25519.verifySig.words PPC64LE.abi.ptrBits) vs) m₂).mpr trivial)
    (Proof.Ed25519.WholeLocal.verifyPost_local _) (Proof.Ed25519.WholeLocal.verifyLeak_local _) verFrameSat_pre

end VG.Proof.Ed25519.PPC64LE.Whole
