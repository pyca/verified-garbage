module

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
import VerifiedGarbage.Proof.Framework.Contract
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
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Vector

/-!
# `vg_ed25519_verify` on PPC64LE, verified

The code meets `verifyContract` with the frame as one more argument
(`Sig.scratchContract`) and 48 bytes of stack for the callees' frames (the
proof against the contract's facts by register, `verC`), and, in a frame of
224 bytes (`Verified.stackScratchL`), the contract itself. The contract
declares the inputs public. Two runs on the same inputs leak the same trace
(`ver_ct`): the taint analysis checks the challenge's computation (only the
pointers and the length matter to it) and the restores, and the call of
`verify_equation` leaks the same trace in both runs by its own constant time,
since its arguments, the challenge included, are the same in both
(`RelCT.callEx`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE.Whole
open VG.Spec.Ed25519 (bytesAt)

/-- The contract by register: `pk` in `r3`, the message in `r4` (`len` in `r5`), the signature in
`r6`, `scratch` in `r7`, the frame in `r8`. -/
def verC : Contract isa where
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

theorem verC_pre {s : State} (h : verC.pre s) : VerPre s :=
  let ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h', i, j, k, l, m, n, o⟩

theorem ver_ok (s : State) (hs : verC.pre s) :
    ∃ t s', Exec isa verifyMessage s t s' ∧ abiPreserved s s' ∧ verC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ := verifyMessage_wp sha512OK (verC_pre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

/-- Two runs on the same public data, as `RelCT.constantTime` relates them. -/
abbrev VP (s₁ s₂ : State) : Prop := verC.pre s₁ ∧ verC.pre s₂ ∧ verC.pub s₁ s₂

/-- The inputs agree in two such runs. -/
theorem vp_bytes {s₁ s₂ : State} (h : VP s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .r3) 32 = bytesAt s₂.mem (s₂.gpr .r3) 32 ∧ vmsgB s₁ = vmsgB s₂ ∧
      bytesAt s₁.mem (s₁.gpr .r6) 64 = bytesAt s₂.mem (s₂.gpr .r6) 64 := by
  obtain ⟨-, -, -, -, p5, -, -, -, -, pl⟩ := h
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

theorem ver_ct : ConstantTime isa verC.pre verC.pub verifyMessage := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold verifyMessage
  refine RelCT.seq (R := fun t₁ t₂ => ∃ σ : VPair, VerArgs σ.1.1 t₁ ∧ VerArgs σ.1.2 t₂) ?_ <|
    RelCT.seq (R := fun t₁ t₂ => ∃ σ : VPair, VerInv σ.1.1 t₁ ∧ VerInv σ.1.2 t₂) ?_ ?_
  · refine ((RelCT.taint (A := vectorTaint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8]) (fun s₁ s₂ h => ?_)
      (by taint_decide)).wpDep (F := VerArgs) fun s₁ s₂ h =>
        ⟨verifyHash_ok sha512OK (verC_pre h.1), verifyHash_ok sha512OK (verC_pre h.2.1)⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, σ₁, σ₂, hp, a₁, a₂⟩ => ⟨⟨(σ₁, σ₂), hp⟩, a₁, a₂⟩
    obtain ⟨-, -, p3, p4, p5, p6, p7, p8, psp, -⟩ := h
    refine ⟨psp, fun r hr => ?_⟩
    simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption
  · refine RelCT.exists_ fun σ => ?_
    refine ((RelCT.callEx (k := verifyPPC) verify_ok' verify_ct fun t₁ t₂ ⟨a₁, a₂⟩ => ?_).wp
      (F₁ := VerInv σ.1.1) (F₂ := VerInv σ.1.2) fun t₁ t₂ ⟨a₁, a₂⟩ =>
        ⟨WP.mono (verCall_ok (verC_pre σ.2.1) a₁) fun _ h => h.1,
          WP.mono (verCall_ok (verC_pre σ.2.2.1) a₂) fun _ h => h.1⟩).mono (fun _ _ h => h)
      fun t₁ t₂ ⟨_, i₁, i₂⟩ => ⟨σ, i₁, i₂⟩
    have hp₁ := verC_pre σ.2.1
    have hp₂ := verC_pre σ.2.2.1
    obtain ⟨c₁, w₁⟩ := verCall_covers hp₁ a₁
    obtain ⟨c₂, w₂⟩ := verCall_covers hp₂ a₂
    refine ⟨_, _, _, _, verCall_pre hp₁ a₁, verCall_pre hp₂ a₂, ?_, c₁, w₁, c₂, w₂⟩
    obtain ⟨-, -, p3, p4, p5, p6, p7, p8, psp, -⟩ := σ.2
    obtain ⟨b3, bm, b6⟩ := vp_bytes σ.2
    have ch : vChallenge σ.1.1 = vChallenge σ.1.2 := by
      unfold vChallenge
      rw [← Proof.Ed25519.signatureBytes_take, ← Proof.Ed25519.signatureBytes_take σ.1.2.mem, b6, b3, bm]
    simp only [verifyPPC, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem, State.callEntry_sp,
      State.callEntry_mem, State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide),
      State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide)]
    rw [a₁.r3, a₂.r3, a₁.r4, a₂.r4, a₁.r5, a₂.r5, a₁.r6, a₂.r6, a₁.inv.sp, a₂.inv.sp, a₁.ch, a₂.ch,
      ver_pk hp₁ a₁.inv, ver_pk hp₂ a₂.inv, ver_sig hp₁ a₁.inv, ver_sig hp₂ a₂.inv, b3, b6, ch]
    exact ⟨p3, p6, p8, p7, psp, rfl⟩
  · exact RelCT.exists_ fun σ => restore_ct fun t₁ t₂ ⟨i₁, i₂⟩ =>
      ⟨by rw [i₁.sp, i₂.sp]; exact σ.2.2.2.2.2.2.2.2.2.1, by
        rw [i₁.regs .r25 (by decide), i₂.regs .r25 (by decide), verV_r25, verV_r25]
        exact σ.2.2.2.2.2.2.2.2.1⟩

/-- A state satisfying the precondition. -/
def verSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r6 => 0x3000 | .r7 => 0x4000 | .r8 => 0x8000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 0⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩, ⟨0x8000, 192⟩]

theorem verify_verified :
    Verified PPC64LE.target verifyMessage (Sig.scratchContract PPC64LE.abi Spec.Ed25519.verifySig "frame" .u8 192
      (Curry.const (fun _ => True) _) (Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) true 48
      (some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits))) :=
  Verified.of_correct ver_ok ver_ct (by
    sig_implies [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Spec.Ed25519.verifySig,
      Spec.Ed25519.scratchWords, Proof.Ed25519.WholeLocal.verifyPost, Proof.Ed25519.WholeLocal.verifyLeak, verC,
      verResult, PPC64LE.abi, PPC64LE.argRegs] [verSat] using verSat)

/-- A state satisfying `vg_ed25519_verify`'s precondition, without the frame. -/
def verFrameSat : State := { verSat with wr := [⟨0x4000, 8192⟩] }

theorem verFrameSat_pre : ∃ s, (Spec.Ed25519.verifyContract PPC64LE.abi (48 + 224)).pre s := by
  implies_sat [Spec.Ed25519.verifyContract, Spec.Ed25519.verifySig, Spec.Ed25519.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs] [verFrameSat, verSat] using verFrameSat

/-- In its frame of 224 bytes. -/
theorem verify_framed :
    Verified PPC64LE.target verifyCode (Spec.Ed25519.verifyContract PPC64LE.abi (48 + 224)) :=
  Verified.stackScratchL (sig := Spec.Ed25519.verifySig) (nm := "frame") (e := .u8) (n := 192)
    (post := Proof.Ed25519.WholeLocal.verifyPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 224)
    (leak := some (Proof.Ed25519.WholeLocal.verifyLeak PPC64LE.abi.ptrBits)) verify_verified (by decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Ed25519.WholeLocal.verifyPost_local _) (Proof.Ed25519.WholeLocal.verifyLeak_local _) verFrameSat_pre

end VG.Proof.Ed25519.PPC64LE.Whole
