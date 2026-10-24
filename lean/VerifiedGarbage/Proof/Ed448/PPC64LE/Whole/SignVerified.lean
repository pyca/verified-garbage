module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignCT
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignCached
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Ed448.WholeLocal
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Impl.StackScratch.PPC64LE.Args
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.SigEval

/-!
# `vg_ed448_sign_cached` on PPC64LE, verified

The code meets `signCachedContract` with the frame as one more argument, on
the stack after the eight in registers (`Sig.scratchContract`), and 48 bytes
of stack for the callees' frames: the proof against the contract's facts by
register (`signC`), which it implies, and a state satisfying it; and, in a
frame of 576 bytes that holds the frame argument's copy and the frame
(`Verified.stackScratchArgs`), the contract itself. The body zeroes the
frame's secrets itself before returning.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole
open VG.Spec.Ed448 (bytesAt)

/-- The contract by register: `SignPre`, as the contract's facts. -/
def signC : Contract isa where
  pre s :=
    (s.rd = [sdR s, pkR s, cxR s, msR s, aR s] ∧ s.wr = [oR s, scR s, fR s] ∧
      (oR s).Disjoint (sdR s) ∧ (oR s).Disjoint (pkR s) ∧ (oR s).Disjoint (cxR s) ∧ (oR s).Disjoint (msR s) ∧
      (oR s).Disjoint (scR s) ∧ (oR s).Disjoint (fR s) ∧
      (scR s).Disjoint (sdR s) ∧ (scR s).Disjoint (pkR s) ∧ (scR s).Disjoint (cxR s) ∧ (scR s).Disjoint (msR s) ∧
      (scR s).Disjoint (fR s) ∧
      (fR s).Disjoint (sdR s) ∧ (fR s).Disjoint (pkR s) ∧ (fR s).Disjoint (cxR s) ∧ (fR s).Disjoint (msR s) ∧
      48 ≤ s.sp.toNat ∧
      (below s.sp 48).Disjoint (oR s) ∧ (below s.sp 48).Disjoint (sdR s) ∧ (below s.sp 48).Disjoint (pkR s) ∧
      (below s.sp 48).Disjoint (cxR s) ∧ (below s.sp 48).Disjoint (msR s) ∧ (below s.sp 48).Disjoint (scR s) ∧
      (below s.sp 48).Disjoint (fR s) ∧
      bytesAt s.mem (s.gpr .r5) 57 = Spec.Ed448.publicKey (bytesAt s.mem (s.gpr .r4) 57)) ∧
    (s.gpr .r7).toNat ≤ 255
  post s s' := bytesAt s'.mem (s.gpr .r3) 114 = Spec.Ed448.sign (seedB s) (ctxB s) (msgB s)
  pub := SPub

theorem signC_pre {s : State} (hs : signC.pre s) : SignPre s := by
  obtain ⟨⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, pk⟩, cl⟩ := hs
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x, y, z, pk, cl⟩

theorem sign_ok (hl : Proof.Ed448.BaseLadder2Ok) (s : State) (hs : signC.pre s) :
    ∃ t s', Exec isa signCached s t s' ∧ abiPreserved s s' ∧ signC.post s s' := by
  obtain ⟨t, s', he, hg, hsp, hlr, hq⟩ := signCached_wp hl (signC_pre hs)
  exact ⟨t, s', he, ⟨hg, hsp, hlr⟩, hq⟩

theorem sign_ct (hl : Proof.Ed448.BaseLadder2Ok) : ConstantTime isa signC.pre SPub signCached :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => signCached_ct hl s₁ s₂ t₁ t₂ s₁' s₂' (signC_pre h₁) (signC_pre h₂) hp e₁ e₂

/-- The stack argument of `signSat`, at `sp + 96`, is zero. -/
theorem sat_arg : Mem.readW Proof.Ed448.WholeLocal.satMem 0x10060 64 = 0 := by
  have h : ∀ i < 64 / 8, Proof.Ed448.WholeLocal.satMem ((0x10060 : Addr) + BitVec.ofNat 64 i) =
      (fun _ => (0 : Byte)) ((0x10060 : Addr) + BitVec.ofNat 64 i) := by
    intro i hi
    have ha : ((0x10060 : Addr) + BitVec.ofNat 64 i).toNat = 0x10060 + i := by
      change (0x10060 + i % 2 ^ 64) % 2 ^ 64 = _; omega
    simp only [Proof.Ed448.WholeLocal.satMem, ha, show ¬ 0x10060 + i < 0x2100 by omega,
      show ¬ 0x10060 + i < 0x2139 by omega, ↓reduceIte]
  rw [Mem.readW_congr (m' := fun _ => (0 : Byte)) h]
  decide

/-- A state satisfying the precondition, with memory `m`: `F` at 0 (the stack argument, at `sp + 96`, zero
in `m`), the seed and its public key at `0x2000` and `0x2100`. -/
def signSat (m : Mem) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x2100 | .r6 => 0x3000 | .r8 => 0x3100 | .r10 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem := m
  rd := [⟨0x2000, 57⟩, ⟨0x2100, 57⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x10060, 8⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x4000, 8192⟩, ⟨0, 464⟩]

theorem signCached_verified (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified PPC64LE.target signCached (Sig.scratchContract PPC64LE.abi Spec.Ed448.signCachedSig "frame" .u8 464
      (Proof.Ed448.WholeLocal.signCachedPre PPC64LE.abi.ptrBits)
      (Proof.Ed448.WholeLocal.signCachedPost PPC64LE.abi.ptrBits) true 48) :=
  Verified.of_correct (sign_ok hl) (sign_ct hl)
    { pre := by
        sig_implies_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.signCachedPre,
          Proof.Ed448.WholeLocal.signCachedPost, signC, sF, oR, sdR, pkR, cxR, msR, scR, fR, aR, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr,
          List.getD, List.range, List.range.loop]
      post := by
        sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.signCachedPre,
          Proof.Ed448.WholeLocal.signCachedPost, signC, sF, oR, sdR, pkR, cxR, msR, scR, fR, aR, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr,
          List.getD, List.range, List.range.loop]
      pub := by
        sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.signCachedPre,
          Proof.Ed448.WholeLocal.signCachedPost, signC, SPub, sF, PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr,
          List.getD, List.range, List.range.loop]
      sat := by
        obtain ⟨m, hm, hz⟩ : ∃ m : Mem, bytesAt m 0x2100 57 = Spec.Ed448.publicKey (bytesAt m 0x2000 57) ∧
            m.readW 0x10060 64 = 0 := ⟨_, Proof.Ed448.WholeLocal.sat_pk, sat_arg⟩
        have hz' : m.readW ((65536 : Addr) + 96#64) 64 = 0 := by
          rw [show (65536 : Addr) + 96#64 = 0x10060 by decide]; exact hz
        refine ⟨signSat m, ?_⟩
        sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app,
          Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, Proof.Ed448.WholeLocal.signCachedPre,
          PPC64LE.abi, PPC64LE.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop, signSat]
        sig_and_intros
        all_goals first
          | exact hm
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | (rw [hz']; first | done | exact Region.disjoint_of_sep (by decide) | decide) }

/-- A state satisfying `vg_ed448_sign_cached`'s precondition, without the frame. -/
def signFrameSat (m : Mem) : State := { signSat m with
  rd := [⟨0x2000, 57⟩, ⟨0x2100, 57⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩], wr := [⟨0x1000, 114⟩, ⟨0x4000, 8192⟩] }

theorem signFrameSat_pre : ∃ s, (Spec.Ed448.signCachedContract PPC64LE.abi (48 + 576)).pre s := by
  obtain ⟨m, hm⟩ : ∃ m : Mem, bytesAt m 0x2100 57 = Spec.Ed448.publicKey (bytesAt m 0x2000 57) :=
    ⟨_, Proof.Ed448.WholeLocal.sat_pk⟩
  refine ⟨signFrameSat m, ?_⟩
  sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, PPC64LE.abi,
    PPC64LE.argRegs, signFrameSat, signSat]
  sig_and_intros
  all_goals first
    | exact hm
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

/-- In its frame of 576 bytes: the frame argument's copy, then the frame. -/
theorem signCached_framed (hl : Proof.Ed448.BaseLadder2Ok) :
    Verified PPC64LE.target signCachedCode (Spec.Ed448.signCachedContract PPC64LE.abi (48 + 576)) :=
  Verified.stackScratchArgs (sig := Spec.Ed448.signCachedSig) (nm := "frame") (e := .u8) (n := 464)
    (pre := Proof.Ed448.WholeLocal.signCachedPre PPC64LE.abi.ptrBits)
    (post := Proof.Ed448.WholeLocal.signCachedPost PPC64LE.abi.ptrBits) (wa := true) (stack := 48) (bytes := 576)
    (m := 0) (signCached_verified hl) (by decide) (by decide) (Proof.Ed448.WholeLocal.signCachedPre_local _)
    (Proof.Ed448.WholeLocal.signCachedPost_local _) signFrameSat_pre

end VG.Proof.Ed448.PPC64LE.Whole
