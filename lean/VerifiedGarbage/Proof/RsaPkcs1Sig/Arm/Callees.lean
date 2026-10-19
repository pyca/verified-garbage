module

public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The ARMv7 PKCS #1 v1.5 functions: their callee `vg_rsa_public_precomputed_checked`

`PdImpl`: an implementation of `vg_rsa_public_precomputed_checked`, with
its proof and the stack it uses (at most 56 bytes); `pdBase`, the baseline
(`Impl/Bignum/Arm/PdFn.lean`). Its contract, at a call with given arguments
(`pd_pre`, `pd_pub`, `pd_post`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.Arm

open VG VG.Arm

/-- An implementation of `vg_rsa_public_precomputed_checked`. -/
structure PdImpl where
  name : String
  code : Prog isa
  verified : Verified target code (Spec.Rsa.publicPrecomputedCheckedContract abi 56)
  stack : FrameStack.armStack code ≤ 56

/-- The baseline. -/
def pdBase : PdImpl where
  name := Spec.Rsa.publicPrecomputedCheckedApi.name
  code := Impl.Bignum.Arm.PdFn.code
  verified := Proof.Bignum.Arm.pd_verified
  stack := by decide +kernel

theorem stackArg_call (s : State) (rd wr : List Region) (i : Nat) :
    stackArg (s.callEntry.withRegions rd wr) i = stackArg s i := by
  simp [stackArg, stackArgAddr]

theorem stackArgAddr_call (s : State) (rd wr : List Region) (i : Nat) :
    stackArgAddr (s.callEntry.withRegions rd wr) i = stackArgAddr s i := by
  simp [stackArgAddr]

section

variable {s : State} {out pre e inp scr : BitVec 32} {K el rl sl : Nat}

/-- The call's arguments. -/
structure PdArgs (s : State) (out pre e inp scr : BitVec 32) (K el rl sl : Nat) : Prop where
  r0 : s.gpr .r0 = out
  r1 : s.gpr .r1 = BitVec.ofNat 32 K
  r2 : s.gpr .r2 = pre
  r3 : s.gpr .r3 = BitVec.ofNat 32 rl
  a0 : stackArg s 0 = e
  a1 : stackArg s 1 = BitVec.ofNat 32 el
  a2 : stackArg s 2 = inp
  a3 : stackArg s 3 = BitVec.ofNat 32 K
  a4 : stackArg s 4 = scr
  a5 : stackArg s 5 = BitVec.ofNat 32 sl
  kv : Spec.Rsa.lenValid K
  rlK : rl = Spec.Rsa.precomputedWords K
  el1 : 1 ≤ el
  elK : el ≤ K
  slK : Spec.Rsa.publicScratchWords K ≤ sl
  sl32 : sl < 2 ^ 32

/-- The callee's buffers. -/
abbrev pdRd (sp pre e inp : BitVec 32) (K el rl : Nat) : List Region :=
  [⟨State.addr pre, rl * 8⟩, ⟨State.addr e, el⟩, ⟨State.addr inp, K⟩, ⟨State.addr sp, 24⟩]
abbrev pdWr (out scr : BitVec 32) (K sl : Nat) : List Region :=
  [⟨State.addr out, K⟩, ⟨State.addr scr, sl * 8⟩]

theorem PdArgs.k32 (h : PdArgs s out pre e inp scr K el rl sl) : K < 2 ^ 32 := by
  have := h.kv.2; omega

theorem PdArgs.rl32 (h : PdArgs s out pre e inp scr K el rl sl) : rl < 2 ^ 32 := by
  have := h.kv.2; rw [h.rlK]; simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]; omega

theorem pd_pre {sp : BitVec 32} (h : PdArgs s out pre e inp scr K el rl sl) (hspE : s.sp = sp)
    (hsp : 56 ≤ sp.toNat) (hsa : sp.toNat + 24 ≤ 2 ^ 32)
    (fOut : out.toNat + K ≤ 2 ^ 32) (fPre : pre.toNat + rl * 8 ≤ 2 ^ 32) (fE : e.toNat + el ≤ 2 ^ 32)
    (fInp : inp.toNat + K ≤ 2 ^ 32) (fScr : scr.toNat + sl * 8 ≤ 2 ^ 32)
    (dOP : Region.Disjoint ⟨State.addr out, K⟩ ⟨State.addr pre, rl * 8⟩)
    (dOE : Region.Disjoint ⟨State.addr out, K⟩ ⟨State.addr e, el⟩)
    (dOI : Region.Disjoint ⟨State.addr out, K⟩ ⟨State.addr inp, K⟩)
    (dOS : Region.Disjoint ⟨State.addr out, K⟩ ⟨State.addr scr, sl * 8⟩)
    (dOA : Region.Disjoint ⟨State.addr out, K⟩ ⟨State.addr sp, 24⟩)
    (dPS : Region.Disjoint ⟨State.addr pre, rl * 8⟩ ⟨State.addr scr, sl * 8⟩)
    (dES : Region.Disjoint ⟨State.addr e, el⟩ ⟨State.addr scr, sl * 8⟩)
    (dIS : Region.Disjoint ⟨State.addr inp, K⟩ ⟨State.addr scr, sl * 8⟩)
    (dSA : Region.Disjoint ⟨State.addr scr, sl * 8⟩ ⟨State.addr sp, 24⟩)
    (lowD : ∀ r ∈ pdRd sp pre e inp K el rl ++ pdWr out scr K sl,
      Region.Disjoint ⟨State.addr sp - BitVec.ofNat 64 56, 56⟩ r) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pre
      (s.callEntry.withRegions (pdRd sp pre e inp K el rl) (pdWr out scr K sl)) := by
  subst hspE
  have k32 := h.k32
  have rl32 := h.rl32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, stackArgAddr_call, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a2, h.a3, h.a4, h.a5,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt rl32, Nat.mod_eq_of_lt el32,
    Nat.mod_eq_of_lt h.sl32]
  have a0 : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [a0]
  have l := fun r hr => lowD r (List.mem_append.mpr hr)
  refine ⟨hsp, hsa, rfl, rfl, dOP, dOE, dOI, dOS, dOA, dPS, dES, dIS, dSA,
    l _ (.inr List.mem_cons_self), l _ (.inl List.mem_cons_self),
    l _ (.inl (List.mem_cons_of_mem _ List.mem_cons_self)),
    l _ (.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))),
    l _ (.inr (List.mem_cons_of_mem _ List.mem_cons_self)),
    l _ (.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))),
    fOut, fPre, fE, fInp, fScr, h.kv, h.rlK, trivial, h.el1, h.elK,
    h.slK⟩

theorem pd_pub {s₁ s₂ : State} (h₁ : PdArgs s₁ out pre e inp scr K el rl sl)
    (h₂ : PdArgs s₂ out pre e inp scr K el rl sl) (hsp : s₁.sp = s₂.sp)
    (hpre : Spec.Rsa.wordsAt s₁.mem (State.addr pre) rl = Spec.Rsa.wordsAt s₂.mem (State.addr pre) rl)
    (he : Spec.Rsa.bytesAt s₁.mem (State.addr e) el = Spec.Rsa.bytesAt s₂.mem (State.addr e) el)
    (rd wr : List Region) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 56).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  have k32 := h₁.k32
  have rl32 := h₁.rl32
  have el32 : el < 2 ^ 32 := by have := h₁.elK; omega
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val]
  simp only [stackArg_call, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₁.a5,
    h₂.r0, h₂.r1, h₂.r2, h₂.r3, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, h₂.a5,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt rl32, Nat.mod_eq_of_lt el32]
  have hpre' : Spec.Rsa.wordsAt s₁.mem (pre.setWidth 64) rl = Spec.Rsa.wordsAt s₂.mem (pre.setWidth 64) rl := hpre
  have he' : Spec.Rsa.bytesAt s₁.mem (e.setWidth 64) el = Spec.Rsa.bytesAt s₂.mem (e.setWidth 64) el := he
  exact ⟨hsp, by rw [hpre', he'], trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial⟩

/-- The call's result: what it writes to `out` and returns, for every
modulus whose precomputed values are `pre`'s. -/
theorem pd_post {s t : State} (h : PdArgs s out pre e inp scr K el rl sl) {rd wr : List Region}
    (hp : (Spec.Rsa.publicPrecomputedCheckedContract abi 56).post (s.callEntry.withRegions rd wr)
      (t.withRegions rd wr)) :
    ∀ nB : List Byte, nB.length = K →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (State.addr pre) rl) →
      Spec.Rsa.written t.mem (State.addr out) K (t.gpr .r0)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (State.addr e) el)
          (Spec.Rsa.bytesAt s.mem (State.addr inp) K)) := by
  have k32 := h.k32
  have rl32 := h.rl32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    reduceClassify, Loc.val] at hp
  simp only [stackArg_call, h.r0, h.r1, h.r2, h.r3, h.a0, h.a1, h.a2,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32, Nat.mod_eq_of_lt rl32, Nat.mod_eq_of_lt el32] at hp
  rw [BitVec.setWidth_append_eq_right] at hp
  exact hp

end

end VG.Proof.RsaPkcs1Sig.Arm
