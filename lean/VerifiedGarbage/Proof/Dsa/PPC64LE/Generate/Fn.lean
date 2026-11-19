module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Attempt
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Zero
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Proof.Dsa.RandomResult
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Prepare
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.PPC64LE.DeriveChecked.Fn
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Q
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Dsa.PPC64LE.Generate.DeriveCall`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Generate.Sampler`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Generate.Check`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Generate.Entry`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.Generate.Contract`, which this module and modules that import it used -/

section

/-!
# DSA key generation on PPC64LE: the contract on the registers and the stack

`gkContract`: `vg_dsa_generate_key(out = r3, out_len = r4, used = r5,
params = r6, params_len = r7, p_len = r8, q_len = r9, rand = r10, rand_len,
scratch, scratch_len)`, the last three on the stack, with the 304 bytes of
stack below the stack pointer that its frame uses (the functions it calls
use none). `generate_implies`: it implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev gkStack : Nat := 304

/-- The arguments on the stack. -/
abbrev gkStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The result `generateKeyBytes` gives, on entry. -/
def gkRes (s : State) : Spec.Dsa.GenerateKeyResult :=
  Spec.Dsa.generateKeyBytes (s.gpr .r8).toNat (s.gpr .r9).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)

/-- `vg_dsa_generate_key`, on the registers and the stack. -/
def gkContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let used : Region := ⟨s.gpr .r5, 8⟩
    let ps : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let rnd : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 gkStack, gkStack⟩
    gkStack ≤ s.sp.toNat ∧ s.sp.toNat + 32 + 8 * 11 ≤ 2 ^ 64 ∧
      s.rd = [ps, rnd, gkStackArgs s] ∧ s.wr = [out, used, scr] ∧
      out.Disjoint used ∧ out.Disjoint ps ∧ out.Disjoint rnd ∧ out.Disjoint scr ∧
      out.Disjoint (gkStackArgs s) ∧ used.Disjoint ps ∧ used.Disjoint rnd ∧
      used.Disjoint scr ∧ used.Disjoint (gkStackArgs s) ∧ ps.Disjoint scr ∧
      rnd.Disjoint scr ∧ scr.Disjoint (gkStackArgs s) ∧
      stk.Disjoint out ∧ stk.Disjoint used ∧ stk.Disjoint ps ∧ stk.Disjoint rnd ∧
      stk.Disjoint scr ∧ stk.Disjoint (gkStackArgs s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r8).toNat (s.gpr .r9).toNat ∧
      (s.gpr .r4).toNat = 3 * (s.gpr .r8).toNat + 2 * (s.gpr .r9).toNat ∧
      (s.gpr .r7).toNat = 2 * (s.gpr .r8).toNat + (s.gpr .r9).toNat ∧
      Spec.Dsa.generationScratchWords (s.gpr .r8).toNat ≤ (stackArg s 2).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = (gkRes s).status ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat =
        (gkRes s).key.getD (List.replicate (s.gpr .r4).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .r5) 1 = [BitVec.ofNat 64 (gkRes s).used]
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat).map (·.toNat) ++
          [(gkRes s₁).status, (gkRes s₁).used] ++ (gkRes s₁).trace =
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat).map (·.toNat) ++
          [(gkRes s₂).status, (gkRes s₂).used] ++ (gkRes s₂).trace

theorem gkStackArgs_three (s : State) :
    List.map (stackArg s) (List.range 3) = [stackArg s 0, stackArg s 1, stackArg s 2] :=
  rfl

/-- A state meeting `gkContract.pre`: 1024-bit p and 160-bit q, `out` at
`0x4000`, `used` at `0x5000`, the domain at `0x1000`, the tape at `0x6000`
and the working space at `0x10000`; the stack's arguments at `0x9060`. -/
def gkSatState : State where
  gpr r := match r with
    | .r3 => 0x4000 | .r4 => 424 | .r5 => 0x5000 | .r6 => 0x1000 | .r7 => 276 | .r8 => 128 | .r9 => 20
    | .r10 => 0x6000 | _ => 0
  lr := 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x906A then 0x01 else bif Nat.beq a.toNat 0x9071 then 0x24 else 0
  rd := [⟨0x1000, 276⟩, ⟨0x6000, 0⟩, ⟨0x9060, 24⟩]
  wr := [⟨0x4000, 424⟩, ⟨0x5000, 8⟩, ⟨0x10000, 73728⟩]

theorem generate_implies : gkContract.Implies (Spec.Dsa.generateKeyContract abi gkStack) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] at h
        sig_split h
        have hx : Sig.conj (Sig.pairFacts [(⟨s.gpr .r10, (stackArg s 0).toNat⟩, false),
            (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩, true), (⟨stackArgAddr s 0, 24⟩, false)]) := by
          with_reducible assumption
        simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
          Bool.or_false, Bool.false_or, List.nil_append, List.cons_append, Sig.conj_cons,
          Sig.conj] at hx
        obtain ⟨_, _⟩ := hx
        sig_reduce [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
        sig_simp [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract, gkRes,
      gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow] []
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | sig_disjoint_symm
          | omega
          | skip
        all_goals done
      post := by sig_implies_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract,
      gkRes, gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      pub := by sig_implies_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract,
      gkRes, gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
      sat := by sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, gkContract,
      gkRes, gkStackArgs_three, List.append_eq, List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts,
      List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false,
      List.cons_append, List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append, stackBelow]
          [gkSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using gkSatState }

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.Generate.Ctx`, which this module and modules that import it used -/

section

/-!
# DSA key generation on PPC64LE: the layout of a call, and its context

`GL`: a call's public data (`glOf`): the stack pointer on entry, the
buffers' addresses and the lengths; `GL.Ok`, what `gkContract.pre` says of
them (`glOf_ok`). The frame is at `F`, 304 octets below the stack pointer.

`Ctx L s₀ t`: in the frame's body, the registers that hold the call's data,
the frame's saved registers, return address and `vg_dsa_derive_key`'s stack
argument, and the domain and the tape as on entry. A change of memory in
`out`, `scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

/-- A call's public data. -/
structure GL where
  sp : Addr
  out : Addr
  used : Addr
  par : Addr
  rand : Addr
  scr : Addr
  pl : Nat
  ql : Nat
  rl : Nat
  sl : Nat

def glOf (s : State) : GL :=
  ⟨s.sp, s.gpr .r3, s.gpr .r5, s.gpr .r6, s.gpr .r10, stackArg s 1, (s.gpr .r8).toNat,
    (s.gpr .r9).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat⟩

namespace GL

variable (L : GL)

abbrev F : Addr := L.sp - BitVec.ofNat 64 frameBytes
/-- The domain's length. -/
abbrev kl : Nat := 2 * L.pl + L.ql
/-- The key's length. -/
abbrev ol : Nat := 3 * L.pl + 2 * L.ql
abbrev outR : Region := ⟨L.out, L.ol⟩
abbrev usedR : Region := ⟨L.used, 8⟩
abbrev parR : Region := ⟨L.par, L.kl⟩
abbrev randR : Region := ⟨L.rand, L.rl⟩
abbrev scrR : Region := ⟨L.scr, L.sl * 8⟩
abbrev frR : Region := ⟨L.F, frameBytes⟩
/-- The nonce. -/
abbrev nR : Region := ⟨off L.F oNonce, 32⟩

end GL

/-- What the precondition says of a call's data. -/
structure GL.Ok (L : GL) : Prop where
  lv : Spec.Dsa.lengthsValid L.pl L.ql
  sw : 64 * L.pl + 1024 ≤ L.sl
  spF : frameBytes ≤ L.sp.toNat
  spTop : L.sp.toNat + 120 ≤ 2 ^ 64
  nwOut : L.out.toNat + L.ol ≤ 2 ^ 64
  nwUsed : L.used.toNat + 8 ≤ 2 ^ 64
  nwPar : L.par.toNat + L.kl ≤ 2 ^ 64
  nwRand : L.rand.toNat + L.rl ≤ 2 ^ 64
  nwScr : L.scr.toNat + L.sl * 8 ≤ 2 ^ 64
  rl : L.rl < 2 ^ 64
  sl : L.sl < 2 ^ 64
  dOU : L.outR.Disjoint L.usedR
  dOK : L.outR.Disjoint L.parR
  dOR : L.outR.Disjoint L.randR
  dOS : L.outR.Disjoint L.scrR
  dUK : L.usedR.Disjoint L.parR
  dUR : L.usedR.Disjoint L.randR
  dUS : L.usedR.Disjoint L.scrR
  dKS : L.parR.Disjoint L.scrR
  dRS : L.randR.Disjoint L.scrR
  dFO : L.frR.Disjoint L.outR
  dFU : L.frR.Disjoint L.usedR
  dFK : L.frR.Disjoint L.parR
  dFR : L.frR.Disjoint L.randR
  dFS : L.frR.Disjoint L.scrR

theorem glOf_ok {s : State} (h : gkContract.pre s) : (glOf s).Ok := by
  obtain ⟨hF, hT, -, -, dOU, dOK, dOR, dOS, -, dUK, dUR, dUS, -, dKS, dRS, -,
    dFO, dFU, dFK, dFR, dFS, -, nO, nU, nK, nR, nS, lv, hol, hkl, hsw⟩ := h
  simp only [Spec.Dsa.generationScratchWords] at hsw
  have e4 : 3 * (s.gpr .r8).toNat + 2 * (s.gpr .r9).toNat = (s.gpr .r4).toNat := hol.symm
  have e7 : 2 * (s.gpr .r8).toNat + (s.gpr .r9).toNat = (s.gpr .r7).toNat := hkl.symm
  have hT' : s.sp.toNat + 120 ≤ 2 ^ 64 := by omega_using [hT]
  refine ⟨lv, hsw, hF, hT', ?_, nU, ?_, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
    ?_, ?_, ?_, ?_, ?_, dUR, dUS, ?_, dRS, ?_, dFU, ?_, dFR, dFS⟩ <;>
  simp only [GL.outR, GL.parR, GL.kl, GL.ol, GL.frR, GL.F, glOf, e4, e7]
  · exact nO
  · exact nK
  · exact dOU
  · exact dOK
  · exact dOR
  · exact dOS
  · exact dUK
  · exact dKS
  · exact dFO
  · exact dFK

namespace GL.Ok

variable {L : GL} (hL : L.Ok)
include hL

theorem ql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem pl : L.pl = 128 ∨ L.pl = 256 ∨ L.pl = 384 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem F_toNat : L.F.toNat = L.sp.toNat - frameBytes := by
  have h1 := hL.spF
  have h2 := L.sp.isLt
  simp only [GL.F, frameBytes] at h1 ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [h1]

theorem fnw : L.F.toNat + frameBytes ≤ 2 ^ 64 := by
  have := hL.F_toNat; have := hL.spF; have := hL.spTop; omega_arith

omit hL in
/-- A range of the frame is apart from a region apart from the frame. -/
theorem frame_disj {r : Region} (hd : L.frR.Disjoint r) {d n : Nat} (h : d + n ≤ frameBytes) :
    (⟨off L.F d, n⟩ : Region).Disjoint r :=
  hd.sub_left (VG.Offset.sub_base _ h)

end GL.Ok

/-- In the frame's body. -/
structure Ctx (L : GL) (s₀ : State) (t : State) : Prop where
  sp : t.sp = L.F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr
  r2 : t.gpr .r2 = s₀.gpr .r2
  r18 : t.gpr .r18 = L.out
  r19 : t.gpr .r19 = L.par
  r20 : t.gpr .r20 = BitVec.ofNat 64 L.pl
  r21 : t.gpr .r21 = BitVec.ofNat 64 L.ql
  r22 : t.gpr .r22 = L.scr
  r23 : t.gpr .r23 = L.rand
  r24 : t.gpr .r24 = BitVec.ofNat 64 L.rl
  r26 : t.gpr .r26 = BitVec.ofNat 64 L.sl
  r30 : t.gpr .r30 = L.used
  sav : ∀ i < 18, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (nv i)
  lr : t.mem.readW (off L.F oLr) 64 = s₀.lr
  a0 : t.mem.readW (off L.F oArgs) 64 = BitVec.ofNat 64 L.sl
  par : Spec.Rsa.bytesAt t.mem L.par L.kl = Spec.Rsa.bytesAt s₀.mem L.par L.kl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.r2, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r26, .r30]

/-- A change of memory in `out`, `scratch` or the nonce, with the registers
of `Ctx` kept, keeps `Ctx`. -/
theorem Ctx.step {L : GL} {s₀ t t' : State} (hL : L.Ok) (h : Ctx L s₀ t) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ ctxRegs, t'.gpr r = t.gpr r)
    (hf : Frame [L.outR, L.scrR, L.nR] t.mem t'.mem) : Ctx L s₀ t' := by
  have hF := hL.fnw
  have hq := hL.ql
  simp only [frameBytes] at hF
  have fw : ∀ d, d + 8 ≤ frameBytes → (d + 8 ≤ oNonce ∨ oNonce + 32 ≤ d) →
      t'.mem.readW (off L.F d) 64 = t.mem.readW (off L.F d) 64 := fun d hd hn =>
    hf.readW (r := ⟨off L.F d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact GL.Ok.frame_disj hL.dFO hd
      · exact GL.Ok.frame_disj hL.dFS hd
      · exact VG.Offset.disjoint L.F (by simp only [oNonce] at hn ⊢; omega_using [hn]) (by simp only [frameBytes] at hd; omega_using [hd])
          (by simp only [oNonce]; omega_using [])) (by decide)
  have nr : ∀ {A : Addr} {k : Nat}, L.frR.Disjoint ⟨A, k⟩ → (⟨A, k⟩ : Region).Disjoint L.nR := fun hd =>
    (GL.Ok.frame_disj hd (d := oNonce) (n := 32) (by decide)).symm
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.r2,
    (hg _ (by decide)).trans h.r18, (hg _ (by decide)).trans h.r19, (hg _ (by decide)).trans h.r20,
    (hg _ (by decide)).trans h.r21, (hg _ (by decide)).trans h.r22, (hg _ (by decide)).trans h.r23,
    (hg _ (by decide)).trans h.r24, (hg _ (by decide)).trans h.r26, (hg _ (by decide)).trans h.r30,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave, oNonce]; omega_using [])).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.lr, (fw _ (by decide) (by decide)).trans h.a0, ?_, ?_⟩
  · refine (RS.bytes_frame hf (fun r hr => ?_) (by have := hL.nwPar; omega_using [this])).trans h.par
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (RS.bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.rl)).trans h.rand
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOR.symm
    · exact hL.dRS
    · exact nr hL.dFR

end VG.Proof.Dsa.PPC64LE.GK

end

end

/-!
# DSA key generation on PPC64LE: the entry

`entry_ok`: from the frame's push, `entry` saves the registers and the
return address, writes `vg_dsa_derive_key`'s argument on the stack, keeps
the call's data in the registers of `Ctx`, starts with no octets consumed,
and zeroes the nonce; memory changes in the frame only.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

/-- The frame's local variable space contains its offsets from 32 on. -/
theorem frameR_contains {L : GL} {s₀ : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) {d n : Nat} (h₁ : 32 ≤ d)
    (h₂ : d + n ≤ frameBytes) : (frameR frameBytes s₀).Contains (off L.F d) n := by
  have hF := hL.fnw
  simp only [frameR, hsp, frameBytes] at hF h₂ ⊢
  rw [show L.sp - BitVec.ofNat 64 304 + 32 = off L.F 32 from rfl]
  exact VG.Offset.contains L.F h₁ (by omega_using [h₂]) (by omega_using [])

/-- The frame's offsets past it are the stack pointer's. -/
theorem F_add (L : GL) (d : Nat) : off L.F (frameBytes + d) = L.sp + BitVec.ofNat 64 d := by
  simp only [off, GL.F]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The octets of a region apart from the frame are kept by a change within it. -/
theorem bytes_outside {L : GL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : k ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  refine ho _ (.inr ?_)
  obtain hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega_using [hi]) (by omega_using [hk, hi])
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

theorem add0 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

/-- The nonce is a working space of the frame. -/
theorem scr_nonce {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR frameBytes s₀ :: s₀.wr) : Scr t (off L.F oNonce) 32 := by
  have hF := hL.fnw
  simp only [frameBytes] at hF
  refine ⟨⟨(frameR frameBytes s₀).base, 88, 272, by rw [hw]; exact List.mem_cons_self .., ?_, by decide,
    by decide⟩, ?_⟩
  · show L.sp - BitVec.ofNat 64 304 + BitVec.ofNat 64 120 = s₀.sp - BitVec.ofNat 64 304 + 32 + BitVec.ofNat 64 88
    rw [hsp, BitVec.add_assoc]
    rfl
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega_using [hF]

/-- What `entry` leaves. -/
structure Entered (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : gkContract.pre s₀) :
    WP isa (.block entry) (allocated frameBytes s₀) (Entered (glOf s₀) s₀) := by
  obtain hL := glOf_ok h
  generalize hLd : glOf s₀ = L at hL
  obtain hsp : s₀.sp = L.sp := by rw [← hLd]; rfl
  have hF := hL.fnw
  have hF' := hF
  simp only [frameBytes] at hF'
  obtain hE : (allocated frameBytes s₀).sp = L.F := by simp only [allocated, hsp]
  obtain hin : ∀ i < 19, InRegions (allocated frameBytes s₀).wr (off L.F (oSave + 8 * i)) 8 := fun i hi =>
    ⟨_, List.mem_cons_self .., frameR_contains hL hsp (by simp only [oSave]; omega_using [])
      (by simp only [oSave, frameBytes]; omega_using [hi])⟩
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok _ hF hE hin) fun t₁ h₁ => ?_
  -- The call's data.
  obtain eo : s₀.gpr .r3 = L.out := by rw [← hLd]; rfl
  obtain eu : s₀.gpr .r5 = L.used := by rw [← hLd]; rfl
  obtain ek : s₀.gpr .r6 = L.par := by rw [← hLd]; rfl
  obtain ep : s₀.gpr .r8 = BitVec.ofNat 64 L.pl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain eq : s₀.gpr .r9 = BitVec.ofNat 64 L.ql := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain ed : s₀.gpr .r10 = L.rand := by rw [← hLd]; rfl
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain a1 : stackArg s₀ 1 = L.scr := by rw [← hLd]; rfl
  obtain a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  -- Memory so far changed within the frame.
  obtain o₀ : Outside L.F 0 8 s₀.mem (allocated frameBytes s₀).mem := by
    intro x hx
    simp only [allocated, hsp, ofs] at hx ⊢
    apply Mem.write_apply
    show ¬ (x - L.F).toNat < 8
    omega_using [hx]
  obtain o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    (o₀.mono (by omega_using []) (by simp only [frameBytes]; omega_using [])).trans (h₁.out.mono (by omega_using [])
      (by simp only [oSave, frameBytes]; omega_using []))
  -- The arguments on the stack.
  obtain ⟨-, -, hrd, -⟩ := h
  obtain hargs : ∀ i < 3, InRegions (t₁.rd ++ t₁.wr) (L.F + BitVec.ofNat 64 (argOff i)) 8 ∧
      t₁.mem.readW (L.F + BitVec.ofNat 64 (argOff i)) 64 = stackArg s₀ i := fun i hi => by
    obtain e : L.F + BitVec.ofNat 64 (argOff i) = stackArgAddr s₀ 0 + BitVec.ofNat 64 (8 * i) := by
      rw [show L.F + BitVec.ofNat 64 (argOff i) = off L.F (frameBytes + (96 + 8 * i)) by
        simp only [argOff, frameBytes]; rw [show 304 + 96 + 8 * i = 304 + (96 + 8 * i) by omega_using []], F_add,
        stackArgAddr, hsp, show 32 + 8 * (8 + 0) = 96 by rfl, BitVec.add_assoc, BitVec.ofNat_add]
    refine ⟨?_, ?_⟩
    · rw [h₁.rd, e]
      exact ⟨gkStackArgs s₀, List.mem_append_left _ (show gkStackArgs s₀ ∈ s₀.rd by rw [hrd]; simp),
        VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
    · rw [show L.F + BitVec.ofNat 64 (argOff i) = off L.F (argOff i) from rfl,
        show t₁.mem.readW (off L.F (argOff i)) 64 = word t₁.mem L.F (argOff i) from rfl,
        o₁.word (.inr (by simp only [argOff, frameBytes]; omega_using [])) (by simp only [argOff, frameBytes]; omega_using [hi])]
      show s₀.mem.readW (L.F + BitVec.ofNat 64 (argOff i)) 64 = _
      rw [e]
      simp only [stackArg, stackArgAddr]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 + 8 * (8 + 0) + 8 * i = 32 + 8 * (8 + i) by omega_using []]
  obtain ⟨l0, v0⟩ := hargs 0 (by decide)
  obtain ⟨l1, v1⟩ := hargs 1 (by decide)
  obtain ⟨l2, v2⟩ := hargs 2 (by decide)
  simp only [argOff, frameBytes, Nat.reduceAdd, Nat.reduceMul] at l0 v0 l1 v1 l2 v2
  obtain st : InRegions t₁.wr (L.F + BitVec.ofNat 64 96) 8 := by
    rw [h₁.wr]; exact ⟨_, List.mem_cons_self .., frameR_contains hL hsp (by omega_using []) (by simp only [frameBytes]; omega_using [])⟩
  obtain hr : ∀ r, r ≠ .r0 → r ≠ .r12 → t₁.gpr r = s₀.gpr r := fun r h0 h12 => h₁.others r h0 h12
  simp only [argOff, oArgs, frameBytes, Nat.reduceAdd, Nat.reduceMul]
  refine WP.mono (WP.keep [.r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r30] (Q := fun t =>
    t.gpr .r18 = L.out ∧ t.gpr .r19 = L.par ∧ t.gpr .r20 = BitVec.ofNat 64 L.pl ∧ t.gpr .r21 = BitVec.ofNat 64 L.ql ∧
      t.gpr .r22 = L.scr ∧ t.gpr .r23 = L.rand ∧ t.gpr .r24 = BitVec.ofNat 64 L.rl ∧ t.gpr .r30 = L.used ∧
      t.gpr .r25 = BitVec.ofNat 64 0 ∧ t.gpr .r26 = BitVec.ofNat 64 L.sl ∧
      t.mem = t₁.mem.writeW (L.F + BitVec.ofNat 64 96) (BitVec.ofNat 64 L.sl))
    (by prun [h₁.r12, l0, l1, l2, v0, v1, v2, a0, a1, a2, st,
      hr .r3 (by decide) (by decide), hr .r5 (by decide) (by decide), hr .r6 (by decide) (by decide),
      hr .r8 (by decide) (by decide), hr .r9 (by decide) (by decide), hr .r10 (by decide) (by decide),
      eo, eu, ek, ep, eq, ed, add0])
    (by decide)) fun t₂ ⟨⟨b18, b19, b20, b21, b22, b23, b24, b30, b25, b26, bm⟩, k₂⟩ => ?_
  obtain e₂sp : t₂.sp = L.F := by rw [k₂.sp, h₁.sp, hE]
  obtain e₂wr : t₂.wr = frameR frameBytes s₀ :: s₀.wr := by rw [k₂.wr, h₁.wr]; rfl
  refine WP.mono (clearNonce_ok t₂ hF e₂sp (scr_nonce hL hsp e₂wr)) fun t ⟨⟨_, tz, tou⟩, k₃⟩ => ?_
  -- Memory on exit, from `t₁`'s.
  obtain o₂ : Outside L.F oArgs 8 t₁.mem t₂.mem := by
    rw [bm]
    exact (writeW_outside _ L.F (d := 96) _ (by omega_using [])).mono (by simp only [oArgs]; omega_using []) (by simp only [oArgs]; omega_using [])
  obtain o₃ : Outside L.F 0 frameBytes s₀.mem t.mem :=
    (o₁.trans (o₂.mono (by omega_using []) (by simp only [oArgs, frameBytes]; omega_using []))).trans
      (tou.mono (by omega_using []) (by simp only [oNonce, frameBytes]; omega_using []))
  obtain w₃ : ∀ d, (d + 8 ≤ oArgs ∨ oNonce + 32 ≤ d) → d + 8 ≤ frameBytes →
      t.mem.readW (off L.F d) 64 = t₁.mem.readW (off L.F d) 64 := fun d hd hd' => by
    obtain e1 := tou.word (d := d) (by simp only [oNonce, oArgs] at hd ⊢; omega_using [hd]) (by simp only [frameBytes] at hd'; omega_using [hd'])
    obtain e2 := o₂.word (d := d) (by simp only [oNonce, oArgs] at hd ⊢; omega_using [hd]) (by simp only [frameBytes] at hd'; omega_using [hd'])
    exact e1.trans e2
  obtain g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ∉ ([.r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
      .r30] : List Reg) → t.gpr r = s₀.gpr r := fun r h0 h12 hr =>
    (k₃.gpr r (by simp [h0, h12])).trans ((k₂.gpr r hr).trans (h₁.others r h0 h12))
  refine ⟨⟨k₃.sp.trans e₂sp, by rw [k₃.rd, k₂.rd, h₁.rd]; rfl, k₃.wr.trans e₂wr, g₃ .r2 (by decide) (by decide) (by decide),
    (k₃.gpr _ (by decide)).trans b18, (k₃.gpr _ (by decide)).trans b19, (k₃.gpr _ (by decide)).trans b20,
    (k₃.gpr _ (by decide)).trans b21, (k₃.gpr _ (by decide)).trans b22, (k₃.gpr _ (by decide)).trans b23,
    (k₃.gpr _ (by decide)).trans b24, (k₃.gpr _ (by decide)).trans b26, (k₃.gpr _ (by decide)).trans b30,
    fun i hi => ?_, ?_, ?_,
    bytes_outside o₃ hL.dFK (by have := hL.nwPar; omega_using [this]), bytes_outside o₃ hL.dFR (Nat.le_of_lt hL.rl)⟩,
    (k₃.gpr _ (by decide)).trans b25, tz⟩
  · rw [w₃ _ (.inr (by simp only [oSave, oNonce]; omega_using [])) (by simp only [oSave, frameBytes]; omega_using [hi])]
    exact h₁.saved i hi
  · rw [w₃ _ (.inr (by decide)) (by decide)]
    exact h₁.savedLr
  · rw [show t.mem.readW (off L.F oArgs) 64 = t₂.mem.readW (off L.F oArgs) 64 from
      tou.word (by simp only [oNonce, oArgs]; omega_using []) (by simp only [oArgs]; omega_using []), bm]
    simp only [off, oArgs]
    rw [Mem.readW_writeW_self64]

end VG.Proof.Dsa.PPC64LE.GK

end

end

/-!
# DSA key generation on PPC64LE: the call of `vg_dsa_check_parameters`

`checkArgs` passes the domain, its lengths and `scratch`, so
`vg_dsa_check_parameters`'s contract on the registers (`pcContract`) holds
with the domain to read and `scratch` to write (`check_pre`); `check_ok`
runs the call by `WP.call` from `checkParameters_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont

/-- The regions on entry, by the call's data. -/
theorem regions_eq {s₀ : State} (h : gkContract.pre s₀) :
    s₀.rd = [(glOf s₀).parR, (glOf s₀).randR, gkStackArgs s₀] ∧
      s₀.wr = [(glOf s₀).outR, (glOf s₀).usedR, (glOf s₀).scrR] := by
  obtain ⟨-, -, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, hkl, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hrd]; simp only [glOf, GL.parR, GL.randR, GL.kl, hkl]
  · rw [hwr]; simp only [glOf, GL.outR, GL.usedR, GL.scrR, GL.ol, hol]

/-- The registers `checkArgs` writes. -/
def checkRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8]

/-- The state after `checkArgs`. -/
structure CArgs (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r3 : t.gpr .r3 = L.par
  r4 : t.gpr .r4 = BitVec.ofNat 64 L.kl
  r5 : t.gpr .r5 = BitVec.ofNat 64 L.pl
  r6 : t.gpr .r6 = BitVec.ofNat 64 L.ql
  r7 : t.gpr .r7 = L.scr
  r8 : t.gpr .r8 = BitVec.ofNat 64 L.sl

theorem checkArgs_ok {L : GL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    WP isa (.block checkArgs) t fun t' => CArgs L s₀ t' ∧ t'.mem = t.mem ∧ Keep checkRegs t t' := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ checkRegs := by decide
  refine WP.mono (WP.keep checkRegs (Q := fun t' => t'.gpr .r3 = L.par ∧ t'.gpr .r4 = BitVec.ofNat 64 L.kl ∧
    t'.gpr .r5 = BitVec.ofNat 64 L.pl ∧ t'.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t'.gpr .r7 = L.scr ∧
    t'.gpr .r8 = BitVec.ofNat 64 L.sl ∧ t'.mem = t.mem)
    ?_ (by decide)) fun t' ⟨⟨a3, a4, a5, a6, a7, a8, am⟩, k⟩ =>
      ⟨⟨hc.step hL k.sp k.rd k.wr (fun r hr => k.gpr r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a3, a4, a5, a6, a7, a8⟩, am, k⟩
  unfold checkArgs
  prun [hc.r19, hc.r20, hc.r21, hc.r22, hc.r26, add0, ← BitVec.ofNat_add]
  congr 1; simp only [GL.kl]; omega_using []

/-- `vg_dsa_check_parameters`'s contract on the registers holds when it is called. -/
theorem check_pre {s₀ t : State} (h : gkContract.pre s₀) (ha : CArgs (glOf s₀) s₀ t) :
    pcContract.pre (t.callEntry.withRegions [(glOf s₀).parR] [(glOf s₀).scrR]) := by
  have hL := glOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have hsw := hL.sw
  have hsl := hL.sl
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  unfold pcContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  rw [g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide), g .r7 (by decide),
    g .r8 (by decide), ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, tn _ (by simp only [GL.kl]; omega_using [hp, hq]),
    tn (glOf s₀).pl (by omega_using [hp]), tn (glOf s₀).ql (by omega_using [hq]), tn _ hsl]
  refine ⟨rfl, rfl, hL.dKS, hL.nwPar, hL.nwScr, hL.lv, rfl, by simp only [Spec.Dsa.scratchWords]; omega_using [hsw]⟩

theorem check_cov {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    Covers ([(glOf s₀).parR] ++ [(glOf s₀).scrR]) (t.rd ++ t.wr) ∧ Covers [(glOf s₀).scrR] t.wr := by
  obtain ⟨hrd, hwr⟩ := regions_eq h
  refine ⟨VG.Covers.of_mem fun r hr => ?_, VG.Covers.of_mem fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hc.wr, hwr]; simp

/-- Whether the domain is valid, on entry. -/
abbrev chkOf (s₀ : State) : Bool :=
  Spec.Dsa.checkParametersBytes (glOf s₀).pl (glOf s₀).ql (Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl)

/-- What the call leaves. -/
structure Checked (L : GL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame [L.scrR] t.mem t'.mem
  r3 : ((t'.gpr .r3).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem check_ok {s₀ t : State} (h : gkContract.pre s₀) (ha : CArgs (glOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_check_parameters" Impl.Dsa.PPC64LE.Params.checkParameters) t (Checked (glOf s₀) s₀ t) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := check_cov h hc
  refine WP.call (k := pcContract) checkParameters_correct (check_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, ?_⟩
  have hpost' := hpost
  simp only [pcContract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem] at hpost'
  have e4 : (BitVec.ofNat 64 (glOf s₀).kl).toNat = (glOf s₀).kl := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [GL.kl]; omega_using [hp, hq])]
  have e5 : (BitVec.ofNat 64 (glOf s₀).pl).toNat = (glOf s₀).pl := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hp])]
  have e6 : (BitVec.ofNat 64 (glOf s₀).ql).toNat = (glOf s₀).ql := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hq])]
  simp only [g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide), ha.r3, ha.r4, ha.r5,
    ha.r6, e4, e5, e6, hc.par] at hpost'
  exact hpost'

end VG.Proof.Dsa.PPC64LE.GK

end

end

/-!
# DSA key generation on PPC64LE: the sampler's data

q's octets `qbOf` (on entry); the sampler's data `seOf` for them, which are
`SE.Ok` and `SE.Q` when `q > 1`; `prepareQ_ok`: the scan of q keeps `Ctx`
and leaves its data in `r27`–`r29` (`Scanned`), from which `SEnv` follows
(`Scanned.env`), with the tape `randOf` (on entry).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (significant qSigOf)

/-- q's octets, on entry. -/
abbrev qbOf (L : GL) (m : Mem) : List Byte := Spec.Rsa.bytesAt m (off L.par L.pl) L.ql

/-- The tape, on entry. -/
abbrev randOf (L : GL) (m : Mem) : List Byte := Spec.Rsa.bytesAt m L.rand L.rl

/-- The sampler's data. -/
def seOf (L : GL) (qb : List Byte) : SE :=
  ⟨L.F, L.rand, L.rl, off (off L.par L.pl) (L.ql - (significant qb).1), L.ql, (significant qb).1,
    maskOf (significant qb).2.toNat, qSigOf qb⟩

theorem bytesAt_drop (m : Mem) (p : Addr) {n d : Nat} (h : d ≤ n) :
    (Spec.Rsa.bytesAt m p n).drop d = Spec.Rsa.bytesAt m (off p d) (n - d) := by
  have := VG.Proof.Dsa.bytesAt_slice m p (offset := d) (len := n - d) (total := n) (by omega_using [h])
  rw [← this, List.take_of_length_le]
  simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length]; omega_using []

theorem qs_eq (L : GL) (m : Mem) :
    qSigOf (qbOf L m) = Spec.Rsa.bytesAt m (off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1))
      (significant (qbOf L m)).1 := by
  have hf := Dsa.significant_fits (qbOf L m)
  rw [VG.Proof.Bignum.bytesAt_length] at hf
  rw [qSigOf, VG.Proof.Bignum.bytesAt_length, bytesAt_drop _ _ (by omega_using []),
    show L.ql - (L.ql - (significant (qbOf L m)).1) = (significant (qbOf L m)).1 by omega_using [hf]]

theorem seOf_Q {L : GL} (m : Mem) (hq : 1 < Spec.Dsa.decodeBE (qbOf L m)) : (seOf L (qbOf L m)).Q (qbOf L m) :=
  ⟨VG.Proof.Bignum.bytesAt_length _ _ _, rfl, rfl, rfl, hq⟩

theorem seOf_ok {L : GL} (hL : L.Ok) (m : Mem) (hq : 1 < Spec.Dsa.decodeBE (qbOf L m)) :
    (seOf L (qbOf L m)).Ok := by
  have hQ := seOf_Q m hq
  have hW := hQ.W_pos
  have hf := Dsa.significant_fits (qbOf L m)
  rw [VG.Proof.Bignum.bytesAt_length] at hf
  have hqb := hL.ql
  have hpl := hL.pl
  have hk := hL.nwPar
  have ht : 0 < (significant (qbOf L m)).2.toNat := by
    have hn : (significant (qbOf L m)).2 ≠ 0 := fun h0 => by
      have := (Dsa.significant_nonzero (qbOf L m)).mpr h0
      simp only [seOf] at hW; omega_using [hW, this]
    exact Nat.pos_of_ne_zero fun h0 => hn (BitVec.eq_of_toNat_eq h0)
  have qoff : (off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1)) =
      off L.par (L.pl + (L.ql - (significant (qbOf L m)).1)) := off_off _ _ _
  have qsub : Region.Sub ⟨off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1), (significant (qbOf L m)).1⟩
      L.parR := by
    rw [qoff]; exact VG.Offset.sub_base _ (by simp only [GL.kl]; omega_using [hf])
  refine ⟨hqb.2, hW, hf, maskOf_lt (significant (qbOf L m)).2.isLt ht, qSigOf_length _, hL.nwRand, hL.rl, ?_,
    hL.fnw, ?_, ?_⟩
  · simp only [seOf]
    rw [qoff, off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [GL.kl] at hk; omega_using [hpl, hk])]
    simp only [GL.kl] at hk
    rw [Nat.mod_eq_of_lt (by omega_using [hqb, hpl])]; omega_using [hf, hk]
  · exact (GL.Ok.frame_disj (d := oNonce) (n := 32) hL.dFR (by decide)).symm
  · exact (GL.Ok.frame_disj (d := oNonce) (n := 32) hL.dFK (by decide)).symm.sub_left qsub

/-- After the scan of q. -/
structure Scanned (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r27 : t.gpr .r27 = (seOf L (qbOf L s₀.mem)).qp
  r28 : t.gpr .r28 = BitVec.ofNat 64 (seOf L (qbOf L s₀.mem)).W
  r29 : 1 < Spec.Dsa.decodeBE (qbOf L s₀.mem) → t.gpr .r29 = BitVec.ofNat 64 (seOf L (qbOf L s₀.mem)).M

/-- q's octets as the key holds them in a state of the body. -/
theorem Ctx.qb {L : GL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    Spec.Rsa.bytesAt t.mem (off L.par L.pl) L.ql = qbOf L s₀.mem := by
  have := hL.ql
  rw [← VG.Proof.Dsa.bytesAt_slice t.mem L.par (total := L.kl) (by simp only [GL.kl]; omega_using []), hc.par,
    VG.Proof.Dsa.bytesAt_slice s₀.mem L.par (total := L.kl) (by simp only [GL.kl]; omega_using [])]

theorem prepareQ_ok {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa prepareQ t fun t' => Scanned (glOf s₀) s₀ t' ∧
      (t'.gpr .r0 = 0 ↔ ¬ 1 < Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)) ∧ t'.mem = t.mem ∧
      Keep (([.r6, .r12] : List Reg) ++ prepRegs) t t' := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  obtain ⟨hrd, -⟩ := regions_eq h
  unfold prepareQ
  refine WP.seq (WP.mono (WP.keep [.r6, .r12] (Q := fun t₁ => t₁.gpr .r12 = off (glOf s₀).par (glOf s₀).pl ∧
    t₁.gpr .r6 = BitVec.ofNat 64 (glOf s₀).ql ∧ t₁.mem = t.mem) (by prun [hc.r19, hc.r20, hc.r21, add0]) (by decide))
    fun t₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  refine WP.mono (prepare_ok a12 a6 (by omega_using [hq]) hq.2 fun i hi => ?_) fun t' ⟨⟨b28, b27, b0, b29, m2⟩, k2⟩ => ?_
  · rw [k1.rd, k1.wr, hc.rd, off_off]
    exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
      VG.Offset.contains_base _ (by simp only [GL.kl]; omega_using [hp, hi]) (by omega_using [hq, hp, hi])⟩
  have kk := k1.trans k2
  have eqb : Spec.Rsa.bytesAt t₁.mem (off (glOf s₀).par (glOf s₀).pl) (glOf s₀).ql = qbOf (glOf s₀) s₀.mem := by
    rw [m1]; exact hc.qb hL
  rw [eqb] at b28 b27 b0 b29
  have hdis : ∀ r ∈ ctxRegs, r ∉ ([.r6, .r12] ++ prepRegs : List Reg) := by decide
  refine ⟨⟨hc.step hL kk.sp kk.rd kk.wr (fun r hr => kk.gpr r (hdis r hr))
    (by rw [m2, m1]; exact Frame.refl _ _), b27, b28, b29⟩, b0, by rw [m2, m1], kk⟩

/-- The sampler's state, after the scan, for `q > 1`. -/
theorem Scanned.env {s₀ t : State} (h : gkContract.pre s₀) (hs : Scanned (glOf s₀) s₀ t)
    (hq : 1 < Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)) :
    SEnv (seOf (glOf s₀) (qbOf (glOf s₀) s₀.mem)) (randOf (glOf s₀) s₀.mem) t := by
  have hL := glOf_ok h
  have hE := seOf_ok hL s₀.mem hq
  obtain ⟨hrd, -⟩ := regions_eq h
  have hc := hs.ctx
  have hW := hE.Wq
  have hk := hL.nwPar
  have hpl := hL.pl
  have hql := hL.ql
  refine ⟨hc.sp, hc.r21, hc.r23, hc.r24, hs.r27, hs.r28, hs.r29 hq, scr_nonce hL rfl hc.wr, fun i hi => ?_,
    fun i hi => ?_, hc.rand, ?_⟩
  · rw [hc.rd, hc.wr]
    exact ⟨(glOf s₀).randR, List.mem_append_left _ (by rw [hrd]; simp),
      VG.Offset.contains_base _ (by simp only [seOf] at hi ⊢; omega_using [hi]) (by have := hL.rl; simp only [seOf] at hi; omega_using [hi, this])⟩
  · rw [hc.rd, hc.wr]
    simp only [seOf, off_off]
    simp only [seOf] at hW hi
    have ekl : (glOf s₀).kl = 2 * (glOf s₀).pl + (glOf s₀).ql := rfl
    exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
      VG.Offset.contains_base _ (by omega_using [hW, hi, ekl]) (by omega_using [hW, hpl, hql, hi])⟩
  · have := qs_eq (glOf s₀) s₀.mem
    simp only [seOf] at this ⊢
    rw [this, off_off]
    simp only [seOf] at hW
    have e1 := VG.Proof.Dsa.bytesAt_slice t.mem (glOf s₀).par (total := (glOf s₀).kl)
      (offset := (glOf s₀).pl + ((glOf s₀).ql - (significant (qbOf (glOf s₀) s₀.mem)).1))
      (len := (significant (qbOf (glOf s₀) s₀.mem)).1) (by simp only [GL.kl]; omega_using [hW])
    have e2 := VG.Proof.Dsa.bytesAt_slice s₀.mem (glOf s₀).par (total := (glOf s₀).kl)
      (offset := (glOf s₀).pl + ((glOf s₀).ql - (significant (qbOf (glOf s₀) s₀.mem)).1))
      (len := (significant (qbOf (glOf s₀) s₀.mem)).1) (by simp only [GL.kl]; omega_using [hW])
    rw [hc.par] at e1
    exact e1.symm.trans e2

end VG.Proof.Dsa.PPC64LE.GK

end

end

/-!
# DSA key generation on PPC64LE: the call of `vg_dsa_derive_key_checked`

`deriveArgs` passes `out`, the domain, x (the nonce, in the frame) and
`scratch`, with their lengths, and the frame holds `scratch_len` on the
stack, so, for a domain that passed `vg_dsa_check_parameters` and is
unchanged since (`Ctx.par`), `vg_dsa_derive_key_checked`'s contract on the
registers (`dcContract`) holds, with the regions it is given (`derRd`,
`derWr`): `derive_ok` runs the call by `WP.call` from
`deriveChecked_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

/-- The regions `vg_dsa_derive_key_checked` may read. -/
abbrev derRd (L : GL) : List Region := [L.parR, ⟨off L.F oNonce, L.ql⟩, ⟨off L.F oArgs, 8⟩]

/-- The regions `vg_dsa_derive_key_checked` may write. -/
abbrev derWr (L : GL) : List Region := [L.outR, L.scrR]

/-- The registers `deriveArgs` writes. -/
def derRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The state after `deriveArgs`. -/
structure DArgs (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r3 : t.gpr .r3 = L.out
  r4 : t.gpr .r4 = BitVec.ofNat 64 L.ol
  r5 : t.gpr .r5 = L.par
  r6 : t.gpr .r6 = BitVec.ofNat 64 L.kl
  r7 : t.gpr .r7 = BitVec.ofNat 64 L.pl
  r8 : t.gpr .r8 = off L.F oNonce
  r9 : t.gpr .r9 = BitVec.ofNat 64 L.ql
  r10 : t.gpr .r10 = L.scr

theorem deriveArgs_ok {L : GL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    WP isa (.block deriveArgs) t fun t' => DArgs L s₀ t' ∧ t'.mem = t.mem ∧ Keep derRegs t t' := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ derRegs := by decide
  refine WP.mono (WP.keep derRegs (Q := fun t' => t'.gpr .r3 = L.out ∧ t'.gpr .r4 = BitVec.ofNat 64 L.ol ∧
    t'.gpr .r5 = L.par ∧ t'.gpr .r6 = BitVec.ofNat 64 L.kl ∧ t'.gpr .r7 = BitVec.ofNat 64 L.pl ∧
    t'.gpr .r8 = off L.F oNonce ∧ t'.gpr .r9 = BitVec.ofNat 64 L.ql ∧ t'.gpr .r10 = L.scr ∧ t'.mem = t.mem)
    ?_ (by decide)) fun t' ⟨⟨a3, a4, a5, a6, a7, a8, a9, a10, am⟩, k⟩ =>
      ⟨⟨hc.step hL k.sp k.rd k.wr (fun r hr => k.gpr r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a3, a4, a5, a6, a7, a8, a9, a10⟩, am, k⟩
  unfold deriveArgs
  prun [hc.r18, hc.r19, hc.r20, hc.r21, hc.r22, hc.sp, exec_addSp (show oNonce < 2 ^ 15 by decide), add0,
    ← BitVec.ofNat_add]
  refine ⟨by simp only [GL.ol]; congr 1; omega_using [], by simp only [GL.kl]; congr 1; omega_using []⟩

theorem dentry_stackArg (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 := rfl

/-- `vg_dsa_derive_key`'s contract on the registers holds when it is called. -/
theorem derive_pre {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t) :
    dContract.pre (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  have hF := hL.fnw
  have hsw := hL.sw
  have hk := hL.nwPar
  simp only [frameBytes] at hF
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  have sa0 : stackArg (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) 0 =
      BitVec.ofNat 64 (glOf s₀).sl := by rw [dentry_stackArg, hc.sp]; exact hc.a0
  have ssp : (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))).sp = (glOf s₀).F := hc.sp
  have sargs : dStackArgs (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) =
      ⟨off (glOf s₀).F oArgs, 8⟩ := by
    simp only [dStackArgs, stackArgAddr, ssp]; rfl
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hsl := hL.sl
  have nwN : (off (glOf s₀).F oNonce).toNat + (glOf s₀).ql ≤ 2 ^ 64 := by
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega_using [hF])]
    simp only [oNonce]; omega_using [hq, hF]
  unfold dContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  rw [g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide), g .r7 (by decide),
    g .r8 (by decide), g .r9 (by decide), g .r10 (by decide), ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, ha.r9,
    ha.r10, sa0, sargs, ssp, tn (glOf s₀).ol (by simp only [GL.ol]; omega_using [hp, hq]),
    tn (glOf s₀).kl (by simp only [GL.kl]; omega_using [hp, hq]), tn (glOf s₀).ql (by omega_using [hq]), tn (glOf s₀).pl (by omega_using [hp]),
    tn _ hsl]
  refine ⟨by omega_using [hF], rfl, rfl, hL.dOK, ?_, hL.dOS, ?_, hL.dKS, ?_, ?_, hL.nwOut, hk, nwN,
    hL.nwScr, hL.lv, by simp only [GL.ol], by simp only [GL.kl], by simp only [Spec.Dsa.scratchWords]; omega_using [hsw]⟩
  · exact (GL.Ok.frame_disj (d := oNonce) (n := (glOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega_using [hq])).symm
  · exact (GL.Ok.frame_disj (d := oArgs) (n := 8) hL.dFO (by decide)).symm
  · exact GL.Ok.frame_disj (d := oNonce) (n := (glOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega_using [hq])
  · exact (GL.Ok.frame_disj (d := oArgs) (n := 8) hL.dFS (by decide)).symm

/-- `vg_dsa_derive_key_checked`'s contract on the registers holds when it is
called, for a domain that passed the specification's checks on entry. -/
theorem derive_pre_checked {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t)
    (hchk : Spec.Dsa.checkParametersBytes (glOf s₀).pl (glOf s₀).ql
      (Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl) = true) :
    dcContract.pre (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) := by
  have hL := glOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  refine ⟨derive_pre h ha, ?_⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem]
  rw [g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r9 (by decide), ha.r5, ha.r6, ha.r7, ha.r9]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (glOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (glOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (glOf s₀).kl) (by simp only [GL.kl]; omega_using [hp, hq]), ha.ctx.par]
  exact hchk

/-- The regions given to `vg_dsa_derive_key_checked` are within the caller's. -/
theorem derive_cov {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    Covers (derRd (glOf s₀) ++ derWr (glOf s₀)) (t.rd ++ t.wr) ∧ Covers (derWr (glOf s₀)) t.wr := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨hrd, hwr⟩ := regions_eq h
  have inF : ∀ d n, 32 ≤ d → d + n ≤ frameBytes → InRegions (t.rd ++ t.wr) (off (glOf s₀).F d) n :=
    fun d n h₁ h₂ =>
      ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), frameR_contains hL rfl h₁ h₂⟩
  refine ⟨VG.Covers.of_forall fun r hr => ?_, VG.Covers.of_mem fun r hr => ?_⟩
  · simp only [derRd, derWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact VG.Covers.one (inF _ _ (by decide) (by simp only [oNonce, frameBytes]; omega_using [hq]))
    · exact VG.Covers.one (inF _ _ (by decide) (by decide))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
  · rw [hc.wr, hwr]
    simp only [derWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

/-- The key `vg_dsa_derive_key_checked` computes from the state `t` it is called in. -/
abbrev dresOf (L : GL) (m : Mem) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m L.par L.kl) (Spec.Rsa.bytesAt m (off L.F oNonce) L.ql)

/-- The key `vg_dsa_derive_key_checked` computes, from the state the call enters. -/
theorem dres_eq {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t) :
    dRes (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) = dresOf (glOf s₀) t.mem := by
  have hL := glOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  simp only [dRes, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr]
  rw [g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide),
    ha.r5, ha.r6, ha.r7, ha.r8, ha.r9]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (glOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (glOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (glOf s₀).kl) (by simp only [GL.kl]; omega_using [hp, hq])]

/-- What the call leaves. -/
structure Derived (L : GL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame (derWr L) t.mem t'.mem
  r3 : ((t'.gpr .r3).setWidth 32).toNat = Spec.Dsa.signStatus (dresOf L t.mem)
  out : Spec.Rsa.bytesAt t'.mem L.out L.ol = (dresOf L t.mem).getD (List.replicate L.ol 0)

theorem derive_ok {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t)
    (hchk : Spec.Dsa.checkParametersBytes (glOf s₀).pl (glOf s₀).ql
      (Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl) = true) :
    WP isa (.call "vg_dsa_derive_key_checked" Impl.Dsa.PPC64LE.Derive.deriveChecked) t
      (Derived (glOf s₀) s₀ t) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := derive_cov h hc
  refine WP.call (k := dcContract) deriveChecked_correct (derive_pre_checked h ha hchk) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p3, pout⟩ := hpost
  have es := dres_eq h ha
  rw [es] at p3 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p3, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .r3) (by decide), State.callEntry_gpr t (r := .r4) (by decide), ha.r3, ha.r4,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (glOf s₀).ol) (by simp only [GL.ol]; omega_using [hp, hq])] at pout
  exact pout

end VG.Proof.Dsa.PPC64LE.GK

end

end

/-! ### `Dsa.PPC64LE.Generate.Finish`, which only this module used -/

section

/-!
# DSA key generation on PPC64LE: the exit

`finish_ok`: unless the status is 1, `out` is zeroed; the nonce is zeroed,
the octets consumed are written to `used`, the status returned and the
registers restored (`Fin`); after the frame is freed, that meets the
contract (`fin_post`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

theorem ctx_r3 : ∀ r ∈ ctxRegs, r ∉ ([.r3] : List Reg) := by decide

theorem ctx_31 : ∀ r ∈ ctxRegs, r ∉ ([.r31] : List Reg) := by decide

theorem ctx_012 : ∀ r ∈ ctxRegs, r ∉ ([.r0, .r12] : List Reg) := by decide

theorem ctx_z : ∀ r ∈ ctxRegs, r ∉ (([.r0, .r16, .r17] : List Reg) ++ ([.r16, .r17] : List Reg)) := by decide

theorem preserved_nv : ∀ r ∈ preserved, r = .r2 ∨ ∃ i < 18, r = nv i := by decide

/-- A change within the nonce is one within `Ctx`'s regions. -/
theorem outside_frame {L : GL} (hL : L.Ok) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
    (ho : Outside L.F (oNonce + o) n m m') : Frame [L.outR, L.scrR, L.nR] m m' := by
  intro x hx
  have hF := hL.fnw
  refine ho x ?_
  obtain hn := hx L.nR (by simp)
  simp only [Region.Contains, off] at hn
  rw [VG.Offset.toNat_sub_add x L.F (by simp only [oNonce]; omega_using [])] at hn
  simp only [ofs, oNonce, frameBytes] at hn hF ⊢
  have := (x - L.F).isLt
  by_contra hc
  rw [show 2 ^ 64 - 120 + (x - L.F).toNat = (x - L.F).toNat - 120 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])] at hn
  omega

/-- The length of the key, into `r17`. -/
abbrev olen : List Instr := [.add .r17 .r20 .r20, .add .r17 .r17 .r20, .add .r17 .r17 .r21, .add .r17 .r17 .r21]

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  r3 : t.gpr .r3 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol = R.key.getD (List.replicate (glOf s₀).ol 0)
  used : t.mem.readW (glOf s₀).used 64 = BitVec.ofNat 64 R.used
  nv : ∀ i < 18, t.gpr (nv i) = s₀.gpr (nv i)
  r2 : t.gpr .r2 = s₀.gpr .r2
  lr : t.lr = s₀.lr
  sp : t.sp = (glOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.GenerateKeyResult} (h : gkContract.pre s₀)
    (hc : Ctx (glOf s₀) s₀ t) (h25 : t.gpr .r25 = BitVec.ofNat 64 R.used)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
      R.key.getD (List.replicate (glOf s₀).ol 0))
    (hnone : R.status ≠ 1 → R.key = none) :
    WP isa (finish olen) t (Fin s₀ R) := by
  obtain hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (WP.keep (c := .block [.subi .r3 .r31 1]) [.r3] (Q := fun t₁ => t₁.mem = t.mem ∧
    t₁.gpr .r3 = t.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₁ ⟨⟨m1, a3⟩, k1⟩ => ?_)
  obtain hc₁ : Ctx (glOf s₀) s₀ t₁ := hc.step hL k1.sp k1.rd k1.wr (fun r hr => k1.gpr r (ctx_r3 r hr))
    (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  obtain hout : ∀ (P : State → Prop), (∀ t₂, Ctx (glOf s₀) s₀ t₂ → Keep [.r0, .r3, .r16, .r17] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (glOf s₀).out (glOf s₀).ol =
        R.key.getD (List.replicate (glOf s₀).ol 0) → P t₂) →
      WP isa (.ite (.zero .d .r3) (.block []) (zeroOut olen)) t₁ P := by
    intro P hP
    refine WP.ite (decide (R.status = 1)) (by rw [eval_zero, a3, h31, RS.sub1_beq _ (by omega_using [hst])]) (fun hs => ?_)
      (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (hP t₁ hc₁ (Keep.refl _ _) (by rw [m1]; exact hsig hs))
    · simp only [decide_eq_false_iff_not] at hs
      unfold zeroOut
      refine WP.seq (WP.mono (WP.keep [.r0, .r16, .r17] (Q := fun t₂ => t₂.gpr .r0 = 0 ∧
        t₂.gpr .r16 = off (glOf s₀).out 0 ∧ t₂.gpr .r17 = BitVec.ofNat 64 (glOf s₀).ol ∧ t₂.mem = t₁.mem)
        (by prun [hc₁.r18, hc₁.r20, hc₁.r21, ← BitVec.ofNat_add]; exact ⟨rfl, by simp only [GL.ol]; congr 1; omega_using []⟩)
        (by decide))
        fun t₂ ⟨⟨b0, b16, b17, m2⟩, k2⟩ => ?_)
      obtain ho : Scr t₂ (glOf s₀).out (glOf s₀).ol :=
        Scr.of_mem (by rw [k2.wr, hc₁.wr, hwr]; simp) hL.nwOut
      refine WP.mono (zeroLoop_ok (by simp only [GL.ol]; omega_using [hq]) (by simp only [GL.ol]; omega_using [hq, hp]) ho b0 b16 b17)
        fun t₃ ⟨⟨z3, o3⟩, k3⟩ => ?_
      refine hP t₃ (hc₁.step hL (k2.trans k3).sp (k2.trans k3).rd (k2.trans k3).wr
        (fun r hr => (k2.trans k3).gpr r (ctx_z r hr)) ?_) ((k2.trans k3).mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega_using [hc'])
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  obtain c25 : t₂.gpr .r25 = BitVec.ofNat 64 R.used := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h25)
  obtain c31 : t₂.gpr .r31 = BitVec.ofNat 64 R.status := (k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h31)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)) fun t₃ ⟨⟨_, _, o3⟩, k3⟩ => ?_
  obtain hc₃ : Ctx (glOf s₀) s₀ t₃ := hc₂.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_012 r hr))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  obtain hus : InRegions t₃.wr ((glOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [hc₃.wr, hwr, BitVec.add_zero]
    exact ⟨(glOf s₀).usedR, by simp, Region.contains_self _ _⟩
  obtain hus' : InRegions t₃.wr (glOf s₀).used 8 := by rw [← BitVec.add_zero (glOf s₀).used]; exact hus
  refine WP.mono (WP.keep (c := .block [.store .d .r25 .r30 0, .addi .r3 .r31 0]) [.r3] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW ((glOf s₀).used + BitVec.ofNat 64 0) (BitVec.ofNat 64 R.used) ∧
      t₄.gpr .r3 = BitVec.ofNat 64 R.status)
    (by prun [hc₃.r30, (k3.gpr _ (by decide)).trans c25, (k3.gpr _ (by decide)).trans c31, hus, hus', add0]) (by decide))
    fun t₄ ⟨⟨m4, a3⟩, k4⟩ => ?_
  -- The used word apart from the frame and `out`.
  obtain huR : (glOf s₀).usedR.Contains ((glOf s₀).used + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero]; exact Region.contains_self _ _
  obtain fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (glOf s₀).F d) 64 = t₃.mem.readW (off (glOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (GL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  obtain hin : ∀ i < 19, InRegions (t₄.rd ++ t₄.wr) (off (glOf s₀).F (oSave + 8 * i)) 8 := fun i hi => by
    rw [k4.rd, k4.wr, hc₃.rd, hc₃.wr]
    exact ⟨_, List.mem_append_right _ (List.mem_cons_self ..), frameR_contains hL rfl (by simp only [oSave]; omega_using [])
      (by simp only [oSave, frameBytes]; omega_using [hi])⟩
  refine WP.mono (restoreRegs_ok t₄ (k4.sp.trans hc₃.sp) hin
    (fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi])).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.lr)) fun t₅ ⟨r5, l5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, r5, ?_, l5, sp5.trans (k4.sp.trans hc₃.sp), rd5.trans (k4.rd.trans hc₃.rd),
    wr5.trans (k4.wr.trans hc₃.wr)⟩
  · rw [o5 .r3 (by decide) (by decide) (by decide)]; exact a3
  · rw [m5, m4, RS.bytes_frame (rs := [(glOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by simp only [GL.ol]; omega_using [hq, hp])]
    rw [bytes_outside (o3.mono (by omega_using []) (by simp only [oNonce, frameBytes]; omega_using [])) hL.dFO
      (by simp only [GL.ol]; omega_using [hq, hp])]
    exact o2
  · rw [m5, m4, BitVec.add_zero, Mem.readW_writeW_self64]
  · rw [o5 .r2 (by decide) (by decide) (by decide), k4.gpr _ (by decide), k3.gpr _ (by decide)]; exact hc₂.r2

/-- The exit's state, after the frame is freed, meets the contract. -/
theorem fin_post {s₀ t : State} (h : gkContract.pre s₀) (hst : (gkRes s₀).status ≤ 2) (hf : Fin s₀ (gkRes s₀) t)
    (m : Mem) (u : Nat → BitVec 64) (fl : Frame [(glOf s₀).frR] t.mem m) :
    abiPreserved s₀ { freed frameBytes t with mem := m, unknowns := u } ∧
      gkContract.post s₀ { freed frameBytes t with mem := m, unknowns := u } := by
  obtain hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, -, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.lr⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    rcases preserved_nv r hr with rfl | ⟨i, hi, rfl⟩
    · exact hf.r2
    · exact hf.nv i hi
  · simp only [freed, hf.sp, GL.F, glOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.r3, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hst])]
  · have e3 : s₀.gpr .r3 = (glOf s₀).out := rfl
    have e4 : (s₀.gpr .r4).toNat = (glOf s₀).ol := hol
    rw [e3, e4]
    -- The `free` loses the frame's bytes, which lie apart from the output and `used`.
    exact Eq.trans (List.map_congr_left fun i hi =>
      lost_byte fl (R := (glOf s₀).outR) hL.dFO.symm (List.mem_range.mp hi)) hf.out
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) ((fl.readW (r := (glOf s₀).usedR) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hL.dFU.symm) (by decide)).trans hf.used)

end VG.Proof.Dsa.PPC64LE.GK

end

end


/-!
# DSA key generation on PPC64LE: the function

`generate_correct`: `vg_dsa_generate_key` meets `gkContract`. In its frame,
the entry (`entry_ok`), the check of the domain (`checked_ok`), then for a
valid domain the scan of q (`prepareQ_ok`), the sampling (`sample_ok`) and
the derivation (`derive_ok`, by `vg_dsa_derive_key_checked`, for the
checked domain), and the exit (`finish_ok`) follow one
another; the result is `generateKeyBytes`'s (`gkRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa.Random (sampleStatus)

/-- q, on entry. -/
abbrev qOf (s₀ : State) : Nat := Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)

/-- The sampler's data, on entry. -/
abbrev eOf (s₀ : State) : SE := seOf (glOf s₀) (qbOf (glOf s₀) s₀.mem)

/-- The draw of x. -/
abbrev drawOf (s₀ : State) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (qOf s₀) 128 (randOf (glOf s₀) s₀.mem)

/-- The domain, on entry. -/
abbrev parOf (s₀ : State) : List Byte := Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl

/-- The key derived from `x`. -/
abbrev dkOf (s₀ : State) (x : Nat) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀) (Spec.Dsa.encodeBE (glOf s₀).ql x)

/-- The result, by the domain's check and the draw. -/
abbrev resOf (s₀ : State) : Spec.Dsa.GenerateKeyResult :=
  if chkOf s₀ then
    match (drawOf s₀).scalar with
    | none => ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used, (drawOf s₀).trace⟩
    | some x => ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩
  else ⟨none, 0, 0, [4]⟩

theorem gkRes_eq {s₀ : State} (h : gkContract.pre s₀) : gkRes s₀ = resOf s₀ := by
  obtain hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hkl, -⟩ := h
  have e7 : (s₀.gpr .r7).toNat = (glOf s₀).kl := hkl
  obtain hq' : (Spec.Dsa.paramsBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀)).q = qOf s₀ := by
    rw [VG.Proof.Dsa.paramsBytes_eq]
    show Spec.Dsa.decodeBE _ = Spec.Dsa.decodeBE _
    rw [VG.Proof.Dsa.bytesAt_slice s₀.mem _ (by simp only [GL.kl]; omega_using [])]
  unfold gkRes
  rw [e7]
  show Spec.Dsa.generateKeyBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀) (randOf (glOf s₀) s₀.mem) = _
  rw [VG.Proof.Dsa.generateKeyBytes_eq hL.lv (by rw [VG.Proof.Bignum.bytesAt_length])]
  simp only [hq']
  rfl

theorem resOf_status (s₀ : State) : (resOf s₀).status ≤ 2 := by
  unfold resOf
  split
  · split
    · dsimp only; split <;> omega_using []
    · dsimp only; unfold Spec.Dsa.signStatus; split <;> omega_using []
  · dsimp only; omega_using []

theorem resOf_none {s₀ : State} (hs : (resOf s₀).status ≠ 1) : (resOf s₀).key = none := by
  revert hs
  unfold resOf
  split
  · split
    · intro _; rfl
    · dsimp only
      intro hs
      unfold Spec.Dsa.signStatus at hs
      split at hs
      · exact absurd rfl hs
      · rename_i hn; simpa using hn
  · intro _; rfl

/-- A frame's octet is kept by a call that writes regions apart from the frame. -/
theorem frame_byte {L : GL} (hL : L.Ok) {rs : List Region} (hd : ∀ r ∈ rs, L.frR.Disjoint r) {m m' : Mem}
    (hf : Frame rs m m') {d : Nat} (hdl : d < frameBytes) : m' (off L.F d) = m (off L.F d) := by
  have hF := hL.fnw
  refine hf _ fun r hr hc => ?_
  obtain hin : L.frR.Contains (off L.F d) 1 :=
    VG.Offset.contains_base _ (by omega_using [hdl]) (by simp only [frameBytes] at hdl; omega_using [hdl])
  exact hd r hr _ hin hc

/-- After the check of the domain. -/
structure Chk (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off (glOf s₀).F (oNonce + j)) = 0
  r3 : ((t.gpr .r3).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem checked_ok {s₀ t : State} (h : gkContract.pre s₀) (he : Entered (glOf s₀) s₀ t) :
    WP isa (.seq (.block checkArgs) (.call "vg_dsa_check_parameters" Impl.Dsa.PPC64LE.Params.checkParameters)) t
      (Chk s₀) := by
  obtain hL := glOf_ok h
  refine WP.seq (WP.mono (checkArgs_ok hL he.ctx) fun t₂ ⟨ca, m2, k2⟩ => WP.mono (check_ok h ca) fun t₃ ck => ?_)
  refine ⟨ck.ctx, (ck.pres _ (by decide)).trans ((k2.gpr _ (by decide)).trans he.r25), fun j hj => ?_, ck.r3⟩
  rw [frame_byte hL (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dFS) ck.frame
    (by simp only [oNonce, frameBytes]; omega_using [hj]), m2]
  exact he.nonce j hj

/-- The nonce's first `q_len − W` octets are zero. -/
abbrev NZero (s₀ : State) (m : Mem) : Prop :=
  ∀ j < (glOf s₀).ql - (eOf s₀).W, m (off (glOf s₀).F (oNonce + j)) = 0

/-- The derivation, from the sampler's result. -/
theorem derive_wp {s₀ t : State} (h : gkContract.pre s₀) (hq : 1 < qOf s₀) (hc : Ctx (glOf s₀) s₀ t)
    (hz : NZero s₀ t.mem) (h25 : t.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used)
    (h31 : t.gpr .r31 = BitVec.ofNat 64 (sampleStatus (drawOf s₀)))
    (hk : ∀ x, (drawOf s₀).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₀) t.mem) = x)
    (hchk : chkOf s₀ = true) :
    WP isa Impl.Dsa.PPC64LE.Generate.derive t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used ∧
        t'.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status ∧
        ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t'.mem (glOf s₀).out (glOf s₀).ol =
          (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) := by
  obtain hL := glOf_ok h
  obtain hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  obtain hst := sampleStatus_le (drawOf s₀)
  unfold Impl.Dsa.PPC64LE.Generate.derive
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t.mem ∧
    t₂.gpr .r3 = t.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_)
  obtain c₂ : Ctx (glOf s₀) s₀ t₂ :=
    hc.step hL k2.sp k2.rd k2.wr (fun r hr => k2.gpr r (ctx_r3 r hr)) (by rw [m2]; exact Frame.refl _ _)
  obtain b25 : t₂.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used := (k2.gpr _ (by decide)).trans h25
  refine WP.ite (decide (sampleStatus (drawOf s₀) = 1))
    (by rw [eval_zero, a3, h31, RS.sub1_beq _ (by omega_using [hst])]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (RS.sampleStatus_some.mp hs)
    obtain hR : resOf s₀ = ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    obtain hnonce : Spec.Rsa.bytesAt t₂.mem (off (glOf s₀).F oNonce) (glOf s₀).ql =
        Spec.Dsa.encodeBE (glOf s₀).ql x := by
      rw [m2]
      exact RS.nonce_eq (W := (eOf s₀).W) hE.Wq hz (hk x hx)
    refine WP.seq (WP.mono (deriveArgs_ok hL c₂) fun t₃ ⟨da, m3, k3⟩ => ?_)
    refine WP.seq (WP.mono (derive_ok h da hchk) fun t₄ dv => ?_)
    obtain es : dresOf (glOf s₀) t₃.mem = dkOf s₀ x := by
      simp only [dresOf, dkOf, parOf]; rw [m3, c₂.par, hnonce]
    have hr3 := dv.r3
    rw [es] at hr3
    unfold deriveFinish
    refine WP.ite (decide (Spec.Dsa.signStatus (dkOf s₀ x) = 0))
      (by rw [RS.eval_zero_w, RS.setWidth_beq_zero hr3]) (fun hz' => ?_) (fun hz' => ?_)
    · simp only [decide_eq_true_eq] at hz'
      refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₅ => t₅.mem = t₄.mem ∧
        t₅.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₅ ⟨⟨m5, a31⟩, k5⟩ => ?_
      refine ⟨dv.ctx.step hL k5.sp k5.rd k5.wr (fun r hr => k5.gpr r (ctx_31 r hr))
        (by rw [m5]; exact Frame.refl _ _), ?_, ?_, fun _ => ?_⟩
      · rw [k5.gpr _ (by decide), dv.pres _ (by decide), k3.gpr _ (by decide), b25, hR]
      · rw [a31, hR]; dsimp only; rw [hz']
      · rw [m5, dv.out, es, hR]
    · simp only [decide_eq_false_iff_not] at hz'
      refine WP.mono (WP.keep (c := .block [.li .r31 1]) [.r31] (Q := fun t₅ => t₅.mem = t₄.mem ∧
        t₅.gpr .r31 = BitVec.ofNat 64 1) (by prun) (by decide)) fun t₅ ⟨⟨m5, a31⟩, k5⟩ => ?_
      refine ⟨dv.ctx.step hL k5.sp k5.rd k5.wr (fun r hr => k5.gpr r (ctx_31 r hr))
        (by rw [m5]; exact Frame.refl _ _), ?_, ?_, fun _ => ?_⟩
      · rw [k5.gpr _ (by decide), dv.pres _ (by decide), k3.gpr _ (by decide), b25, hR]
      · rw [a31, hR]; dsimp only
        unfold Spec.Dsa.signStatus at hz' ⊢
        split at hz' <;> simp_all
      · rw [m5, dv.out, es, hR]
  · simp only [decide_eq_false_iff_not] at hs
    obtain hx : (drawOf s₀).scalar = none := by
      cases hc' : (drawOf s₀).scalar with
      | none => rfl
      | some k => exact absurd (RS.sampleStatus_some.mpr (by rw [hc']; rfl)) hs
    obtain hR : resOf s₀ = ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used,
        (drawOf s₀).trace⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    refine WP.block_nil ⟨c₂, by rw [b25, hR], ?_, fun h1 => ?_⟩
    · rw [(k2.gpr _ (by decide)).trans h31, hR]
      simp only [sampleStatus, hx]
    · rw [hR] at h1 ⊢
      exact absurd h1 (by dsimp only; split <;> decide)

theorem ctx_draw : ∀ r ∈ ctxRegs, r ∉ drawRegs := by decide

/-- After the steps for a valid domain. -/
structure VOut (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used
  r31 : t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status
  out : (resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
    (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)

theorem valid_ok {s₀ t₂ : State} (h : gkContract.pre s₀) (ck : Chk s₀ t₂) (hchk : chkOf s₀ = true) :
    WP isa valid t₂ (VOut s₀) := by
  obtain hL := glOf_ok h
  have hql := hL.ql
  unfold valid
  refine WP.seq (WP.mono (prepareQ_ok h ck.ctx) fun t₃ ⟨sc, h0, m3, k3⟩ => ?_)
  obtain c25 : t₃.gpr .r25 = BitVec.ofNat 64 0 := (k3.gpr _ (by decide)).trans ck.r25
  refine WP.ite (decide (¬ 1 < qOf s₀)) (by rw [eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_)
  · -- q ≤ 1: no draw.
    simp only [decide_eq_true_eq] at hq
    obtain hd : drawOf s₀ = ⟨none, 0, [4]⟩ := by
      show Spec.Dsa.Random.sample (qOf s₀) (127 + 1) _ = _
      rw [Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega_using [hq])]
    obtain hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk, hd]; rfl
    refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₄ => t₄.mem = t₃.mem ∧
      t₄.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₄ ⟨⟨m4, a31⟩, k4⟩ => ?_
    refine ⟨sc.ctx.step hL k4.sp k4.rd k4.wr (fun r hr => k4.gpr r (ctx_31 r hr))
      (by rw [m4]; exact Frame.refl _ _), ?_, ?_, fun h1 => ?_⟩
    · rw [k4.gpr _ (by decide), c25, hR]
    · rw [a31, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- q > 1: the draw and the derivation.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    obtain hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    obtain hQ := seOf_Q (L := glOf s₀) s₀.mem hq
    have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
    have hql' : (eOf s₀).ql ≤ 32 := hE.ql
    have hF := hL.fnw
    refine WP.seq (WP.mono (sample_ok hE hQ (sc.env h hq) c25 (Nat.zero_le _)) fun t₄ so => ?_)
    rw [List.drop_zero] at so
    obtain c₄ : Ctx (glOf s₀) s₀ t₄ := sc.ctx.step hL so.keep.sp so.keep.rd so.keep.wr
      (fun r hr => so.keep.gpr r (ctx_draw r hr))
      (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega_using [hW, hql']) so.out)
    obtain nz : NZero s₀ t₄.mem := fun j hj => by
      obtain e : ofs (eOf s₀).F (off (glOf s₀).F (oNonce + j)) = oNonce + j :=
        Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega_using [hql, hj])
      obtain hj' : oNonce + j < (eOf s₀).o := by
        have e2 : (eOf s₀).ql = (glOf s₀).ql := rfl
        simp only [SE.o]; omega_using [hj, e2]
      rw [so.out _ (.inl (by rw [e]; exact hj')), m3]
      exact ck.nonce j (by omega_using [hql, hj])
    obtain r25 : t₄.gpr .r25 = BitVec.ofNat 64 (drawOf s₀).used := by rw [so.r25, Nat.zero_add]
    exact WP.mono (derive_wp h hq c₄ nz r25 so.r31 so.cand hchk) fun t₅ ⟨c, a, b, d⟩ => ⟨c, a, b, d⟩


theorem generate_correct (s₀ : State) (h : gkContract.pre s₀) :
    ∃ tr t, Exec isa Impl.Dsa.PPC64LE.Generate.code s₀ tr t ∧ abiPreserved s₀ t ∧ gkContract.post s₀ t := by
  show WP isa Impl.Dsa.PPC64LE.Generate.code s₀ fun t => abiPreserved s₀ t ∧ gkContract.post s₀ t
  obtain hL := glOf_ok h
  have hql := hL.ql
  obtain hfin : ∀ t, Ctx (glOf s₀) s₀ t → t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
        (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) →
      WP isa (finish olen) t fun t' =>
        ∀ m u, Frame [⟨s₀.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩] t'.mem m →
          abiPreserved s₀ { freed frameBytes t' with mem := m, unknowns := u } ∧
            gkContract.post s₀ { freed frameBytes t' with mem := m, unknowns := u } :=
    fun t hc h25 h31 hsig => WP.mono (finish_ok h hc h25 h31 (resOf_status s₀) hsig resOf_none) fun t' hf m u fl =>
      fin_post h (by rw [gkRes_eq h]; exact resOf_status s₀) (by rw [gkRes_eq h]; exact hf) m u fl
  unfold Impl.Dsa.PPC64LE.Generate.code
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.PPC64LE.Generate.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (checked_ok h he) fun t₂ ck => ?_)
  refine WP.seq (WP.ite (decide ((if chkOf s₀ then 1 else 0) = 0))
    (by rw [RS.eval_zero_w, RS.setWidth_beq_zero ck.r3]) (fun hc => ?_) (fun hc => ?_))
  · -- An invalid domain.
    obtain hchk : chkOf s₀ = false := by
      cases hc' : chkOf s₀ <;> simp_all
    obtain hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk]; rfl
    refine WP.mono (WP.keep (c := .block [.li .r31 0]) [.r31] (Q := fun t₃ => t₃.mem = t₂.mem ∧
      t₃.gpr .r31 = BitVec.ofNat 64 0) (by prun) (by decide)) fun t₃ ⟨⟨m3, a31⟩, k3⟩ => ?_
    refine hfin t₃ (ck.ctx.step hL k3.sp k3.rd k3.wr (fun r hr => k3.gpr r (ctx_31 r hr))
      (by rw [m3]; exact Frame.refl _ _)) ?_ ?_ fun h1 => ?_
    · rw [k3.gpr _ (by decide), ck.r25, hR]
    · rw [a31, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- A valid domain.
    obtain hchk : chkOf s₀ = true := by
      cases hc' : chkOf s₀ <;> simp_all
    exact WP.mono (valid_ok h ck hchk) fun t₄ v => hfin t₄ v.ctx v.r25 v.r31 v.out

end VG.Proof.Dsa.PPC64LE.GK
