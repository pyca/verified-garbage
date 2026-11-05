module

public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.Contract

/-!
# An FFDH parameter candidate on PPC64LE: the callable contract

`vg_ffdh_parameter_candidate(out = r3, out_len = r4, used = r5, bits = r6,
generator = r7, rand = r8, rand_len = r9, scratch = r10, scratch_len)`, the
last on the stack (`pcContract`), with 176 bytes of stack below `sp` for the
round it calls, and RSA's table of trial division (`VG_RSA_KEYGEN_TRIAL32`,
`TabAt`) readable, apart from `out` and `scratch`.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Spec.Ffdh
open VG.Spec.Rsa (bytesAt wordsAt i2osp)

/-- RSA's table of trial division in memory `m` at `T`. -/
def TabAt (T : Addr) (m : Mem) : Prop :=
  ∀ i < 1024, m.readW (T + BitVec.ofNat 64 (8 * i)) 64 =
    BitVec.ofNat 64 (VG.Impl.RsaKeyGen.TrialTable32.entry i)

/-- The table's region, where the state names it. -/
abbrev tabR (s : State) : Region := ⟨s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩

/-- The table: in memory, fitting, and apart from `out` and `scratch`. -/
def PcTab (s : State) : Prop :=
  (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol).toNat + 8192 ≤ 2 ^ 64 ∧
    TabAt (s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol) s.mem ∧
    (tabR s).Disjoint ⟨s.gpr .r3, (s.gpr .r4).toNat⟩ ∧ (tabR s).Disjoint ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩

def pcPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
  let used : Region := ⟨s.gpr .r5, 8⟩
  let rand : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let scr : Region := ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩
  let args : Region := ⟨stackArgAddr s 0, 8⟩
  let below : Region := ⟨s.sp - BitVec.ofNat 64 176, 176⟩
  176 ≤ s.sp.toNat ∧ s.sp.toNat + 32 + 8 * 9 ≤ 2 ^ 64 ∧
    s.rd = [rand, args, tabR s] ∧ s.wr = [out, used, scr] ∧
    out.Disjoint used ∧ out.Disjoint rand ∧ out.Disjoint scr ∧ out.Disjoint args ∧
    used.Disjoint rand ∧ used.Disjoint scr ∧ used.Disjoint args ∧
    rand.Disjoint scr ∧ scr.Disjoint args ∧
    below.Disjoint out ∧ below.Disjoint used ∧ below.Disjoint rand ∧ below.Disjoint scr ∧ below.Disjoint args ∧
    (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r10).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
    512 ≤ (s.gpr .r6).toNat ∧ (s.gpr .r6).toNat ≤ 8192 ∧
    (s.gpr .r4).toNat = ((s.gpr .r6).toNat + 7) / 8 ∧
    (((s.gpr .r7).setWidth 32).toNat = 2 ∨ ((s.gpr .r7).setWidth 32).toNat = 5) ∧
    Spec.Rsa.scratchWords (s.gpr .r4).toNat ≤ (stackArg s 0).toNat ∧ PcTab s

abbrev pcRand (s : State) : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat

def pcResult (s : State) : Option (Option Nat × Spec.RsaKeyGen.Rand) :=
  sievedParameterCandidate (s.gpr .r6).toNat ((s.gpr .r7).setWidth 32).toNat (pcRand s)

def pcPost (s t : State) : Prop :=
  ((t.gpr .r3).setWidth 32).toNat = candidateStatus (pcResult s) ∧
    bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat =
      (match pcResult s with
        | some (some p, _) => i2osp p (s.gpr .r4).toNat
        | _ => List.replicate (s.gpr .r4).toNat 0) ∧
    wordsAt t.mem (s.gpr .r5) 1 =
      [BitVec.ofNat 64 (match pcResult s with
        | some (_, rest) => (s.gpr .r9).toNat - rest.length
        | none => 0)]

def pcPub (s t : State) : Prop :=
  s.sp = t.sp ∧ (pcRand s).map (·.toNat) = (pcRand t).map (·.toNat) ∧
    s.gpr .r3 = t.gpr .r3 ∧ s.gpr .r4 = t.gpr .r4 ∧ s.gpr .r5 = t.gpr .r5 ∧
    s.gpr .r6 = t.gpr .r6 ∧ (s.gpr .r7).setWidth 32 = (t.gpr .r7).setWidth 32 ∧ s.gpr .r8 = t.gpr .r8 ∧
    s.gpr .r9 = t.gpr .r9 ∧ s.gpr .r10 = t.gpr .r10 ∧ stackArg s 0 = stackArg t 0 ∧
    s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol

def pcContract : Contract isa where
  pre := pcPre
  post := pcPost
  pub := pcPub

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
