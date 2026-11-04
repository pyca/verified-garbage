module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Widths
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Sized
public import VerifiedGarbage.Spec.Dsa.GenerationSized
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64.Base
public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Verified
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SharedChecker
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SizedBackend
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.BackendCorrect
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Sized
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
public import VerifiedGarbage.Proof.Framework.X86_64.ForwardCall
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SizedContract

/-! # Parameter generation by the public modulus width, on x86-64

`widths` (`Impl/Dsa/X86_64/Generation/Widths.lean`) calls the function for
`p_len`'s width, whose code is the restricted generation body
(`Sized.single`), forwarding its arguments (`Verified.forward`): it is
verified against the complete generation contract from the restricted
helpers' (`Spec.Dsa.GenerationSized`), each the complete contract with the
width fixed, by choosing on entry (`Verified.entryBranch`).
-/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation.Widths
open VG VG.X86_64 VG.Proof.Pbkdf2.Md.X86_64 VG.Proof.MillerRabin.X86_64 VG.Proof.Dsa.X86_64.Generation
open VG.Spec.Rsa (bytesAt)

variable {checkName : String}

/-! ## The restricted bodies' depth -/

theorem sized_depth_le (G1 G256 : Impl.Pbkdf2.Md.X86_64.Stream) (sq : Prog isa)
    (mul : Nat → Nat → Nat → Prog isa) (round : Prog isa) (pBytes : Nat) :
    (Impl.Dsa.X86_64.Generation.Sized.code (checkName := checkName) pBytes G1 G256 sq mul round).x86_64Depth ≤
      (Impl.Dsa.X86_64.Generation.code (checkName := checkName) G1 G256 sq mul round).x86_64Depth := by
  unfold Impl.Dsa.X86_64.Generation.Sized.code Impl.Dsa.X86_64.Generation.Sized.entryBody
    Impl.Dsa.X86_64.Generation.Sized.dispatch Impl.Dsa.X86_64.Generation.code
    Impl.Dsa.X86_64.Generation.entryBody Impl.Dsa.X86_64.Generation.dispatch
  simp only [Code.x86_64Depth, Instr.frameBytes]
  split <;> split <;> split <;> (try simp only [Code.x86_64Depth]) <;> omega

theorem single_depth (h : MdHash) (v : RoundImpl) (pBytes : Nat) :
    (Impl.Dsa.X86_64.Generation.Sized.single (checkName := checkName) pBytes h.H.stream
      VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS.mm
      VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.mm
      (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run).x86_64Depth ≤ 536 :=
  Nat.le_trans (sized_depth_le (checkName := checkName) _ _ _ _ _ pBytes)
    (backend_depth (checkName := checkName) h h v)

/-! ## Forwarding to a restricted body -/

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) : bytesAt m₁ p n = bytesAt m₂ p n := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => h _ ?_
  have hi := List.mem_range.mp hi
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_arith) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_arith

theorem setWidth_ptr (x : BitVec 64) : (BitVec.setWidth abi.ptrBits x).toNat = x.toNat :=
  congrArg BitVec.toNat (BitVec.setWidth_eq x)

theorem forward_sized (p : Nat) {name : String} {body : Prog isa}
    (h : Verified target body (Spec.Dsa.GenerationSized.contract p abi 536))
    (hsp : body.all (fun i => !isa.writesSp i) = true) (hd : body.x86_64Depth ≤ 536)
    (hsat : ∃ s, (Spec.Dsa.GenerationSized.contract p abi 600).pre s) :
    Verified target (Impl.Dsa.X86_64.Generation.Widths.width name body)
      (Spec.Dsa.GenerationSized.contract p abi 600) := by
  refine Verified.forward (sig := Spec.Dsa.generateParametersSig) (bytes := 56) h (by decide) (by decide)
    (by decide) (by decide) hsp hd ?_ ?_ hsat ?_
  · intro vs m₁ m₂ hl _ _ hpr
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hl
    replace hl := Nat.succ.inj hl
    iterate 11
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact hpr
  · intro vs m₁ m₂ m' r hl hb _ hq
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hl
    replace hl := Nat.succ.inj hl
    iterate 3
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨seeds, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨seedsLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨hs, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨hsLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨wit, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨witLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.generateParametersSig, Sig.bufs_nil, Sig.bufs_int, Sig.bufs_slice,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one] at hb
    obtain ⟨-, b1, b2, b3, -⟩ := hb
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Dsa.generateParametersSig.retBits abi.ptrBits) → Prop) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.int (IntTy.usize.bits abi.ptrBits), ArgWord.int (IntTy.usize.bits abi.ptrBits), ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits] _ _ m₁ m' r at hq
    change Curry.apply (α := Mem → Mem → BitVec (Spec.Dsa.generateParametersSig.retBits abi.ptrBits) → Prop) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.int (IntTy.usize.bits abi.ptrBits), ArgWord.int (IntTy.usize.bits abi.ptrBits), ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits] _ _ m₂ m' r
    dsimp only [Curry.apply, ArgWord.ofRaw] at hq ⊢
    rw [← setWidth_ptr seedsLen] at b1
    rw [← setWidth_ptr hsLen] at b2
    rw [← setWidth_ptr witLen] at b3
    rwa [← bytesAt_congr b1, ← bytesAt_congr b2, ← bytesAt_congr b3]
  · intro vs m₁ m₂ hl hb _
    obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 11) hl
    replace hl := Nat.succ.inj hl
    iterate 3
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain ⟨seeds, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨seedsLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨hs, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨hsLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨wit, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    obtain ⟨witLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
    replace hl := Nat.succ.inj hl
    iterate 2
      obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      replace hl := Nat.succ.inj hl
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    simp only [Spec.Dsa.generateParametersSig, Sig.bufs_nil, Sig.bufs_int, Sig.bufs_slice,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Elem.size,
      Nat.mul_one] at hb
    obtain ⟨-, b1, b2, b3, -⟩ := hb
    change Curry.apply (α := Mem → List Nat) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.int (IntTy.usize.bits abi.ptrBits), ArgWord.int (IntTy.usize.bits abi.ptrBits), ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits] _ _ m₁ = Curry.apply (α := Mem → List Nat) [ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.int (IntTy.usize.bits abi.ptrBits), ArgWord.int (IntTy.usize.bits abi.ptrBits), ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits, ArgWord.addr, ArgWord.int abi.ptrBits] _ _ m₂
    dsimp only [Curry.apply, ArgWord.ofRaw]
    rw [← setWidth_ptr seedsLen] at b1
    rw [← setWidth_ptr hsLen] at b2
    rw [← setWidth_ptr witLen] at b3
    rw [bytesAt_congr b1, bytesAt_congr b2, bytesAt_congr b3]

/-! ## The contracts the choice passes through -/

/-- The complete generation contract for the two larger widths. -/
def largeContract (stack : Nat := 0) : Contract isa :=
  Spec.Dsa.generateParametersSig.contract abi
    (pre := fun _out outLen pLen qLen _seeds seedsLen _hs hsLen _witnesses _witnessesLen
        _scratch scratchLen _ =>
      (pLen.toNat = 256 ∨ pLen.toNat = 384) ∧ Spec.Dsa.generationLengthsValid pLen.toNat qLen.toNat ∧
        outLen.toNat = 2 * pLen.toNat + qLen.toNat ∧
        seedsLen.toNat % qLen.toNat = 0 ∧ hsLen.toNat % pLen.toNat = 0 ∧
        Spec.Dsa.generationScratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen pLen qLen seeds seedsLen hs hsLen witnesses witnessesLen
        _scratch _scratchLen m m' r =>
      let res := Spec.Dsa.generateParametersBytes pLen.toNat qLen.toNat (bytesAt m seeds seedsLen.toNat)
        (bytesAt m hs hsLen.toNat) (bytesAt m witnesses witnessesLen.toNat)
      r.toNat = Spec.Dsa.signStatus res ∧
        bytesAt m' out outLen.toNat = res.getD (List.replicate outLen.toNat 0))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _pLen _qLen seeds seedsLen hs hsLen witnesses witnessesLen
        _scratch _scratchLen m =>
      (bytesAt m seeds seedsLen.toNat).map (·.toNat) ++
        (bytesAt m hs hsLen.toNat).map (·.toNat) ++
        (bytesAt m witnesses witnessesLen.toNat).map (·.toNat))

theorem sized_of_full {p : Nat} {s : State} (h : (Spec.Dsa.generateParametersContract abi 600).pre s)
    (hw : (s.gpr .rdx).toNat = p) : (Spec.Dsa.GenerationSized.contract p abi 600).pre s := by
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_split h
  sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_and_intros
  all_goals with_reducible assumption

theorem large_of_full {s : State} (h : (Spec.Dsa.generateParametersContract abi 600).pre s)
    (hw : (s.gpr .rdx).toNat ≠ 128) : (largeContract 600).pre s := by
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_split h
  sig_pre [largeContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_pre [largeContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_and_intros
  all_goals first
    | with_reducible assumption
    | (simp only [Spec.Dsa.generationLengthsValid] at *; omega)

theorem sized_of_large {p : Nat} {s : State} (h : (largeContract 600).pre s)
    (hw : (s.gpr .rdx).toNat = p) : (Spec.Dsa.GenerationSized.contract p abi 600).pre s := by
  sig_pre [largeContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_pre [largeContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_split h
  sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_and_intros
  all_goals with_reducible assumption

/-! ## Satisfiable with the call's stack -/

theorem satArgs (p : Nat) :
    stackArg (Sized.sizedSatState p) 0 = 0x3000 ∧ stackArg (Sized.sizedSatState p) 1 = 0 ∧
    stackArg (Sized.sizedSatState p) 2 = 0x4000 ∧ stackArg (Sized.sizedSatState p) 3 = 0 ∧
    stackArg (Sized.sizedSatState p) 4 = 0x10000 ∧ stackArg (Sized.sizedSatState p) 5 = 25600 := by
  dsimp only [stackArg, stackArgAddr, Sized.sizedSatState]
  decide +kernel

theorem sized_sat (p : Nat) (hp : p = 128 ∨ p = 256 ∨ p = 384) :
    ∃ s, (Spec.Dsa.GenerationSized.contract p abi 600).pre s := by
  have hargs := satArgs p
  refine ⟨Sized.sizedSatState p, ?_⟩
  rcases hp with rfl | rfl | rfl
  all_goals sig_pre [Spec.Dsa.GenerationSized.contract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  all_goals sig_and_intros
  all_goals try simp only [hargs.1, hargs.2.1, hargs.2.2.1, hargs.2.2.2.1,
    hargs.2.2.2.2.1, hargs.2.2.2.2.2]
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp [Region.Contains, stackArgAddr, Sized.sizedSatState] at h₁ h₂ <;> bv_omega)

theorem large_sat : ∃ s, (largeContract 600).pre s := by
  have hargs := satArgs 256
  refine ⟨Sized.sizedSatState 256, ?_⟩
  sig_pre [largeContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_and_intros
  all_goals try simp only [hargs.1, hargs.2.1, hargs.2.2.1, hargs.2.2.2.1,
    hargs.2.2.2.2.1, hargs.2.2.2.2.2]
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp [Region.Contains, stackArgAddr, Sized.sizedSatState] at h₁ h₂ <;> bv_omega)

theorem full_sat : ∃ s, (Spec.Dsa.generateParametersContract abi 600).pre s := by
  have hargs := satArgs 256
  refine ⟨Sized.sizedSatState 256, ?_⟩
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six]
  sig_and_intros
  all_goals try simp only [hargs.1, hargs.2.1, hargs.2.2.1, hargs.2.2.2.1,
    hargs.2.2.2.2.1, hargs.2.2.2.2.2]
  all_goals first
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp [Region.Contains, stackArgAddr, Sized.sizedSatState] at h₁ h₂ <;> bv_omega)

/-! ## The choice -/

theorem width_of_large {s : State} (h : (largeContract 600).pre s) :
    (s.gpr .rdx).toNat = 256 ∨ (s.gpr .rdx).toNat = 384 := by
  sig_pre [largeContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_pre [largeContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at h
  sig_split h
  with_reducible assumption

theorem large_verified {n₂₅₆ n₃₈₄ : String} {c₂₅₆ c₃₈₄ : Prog isa}
    (h₂₅₆ : Verified target (Impl.Dsa.X86_64.Generation.Widths.width n₂₅₆ c₂₅₆)
      (Spec.Dsa.GenerationSized.contract 256 abi 600))
    (h₃₈₄ : Verified target (Impl.Dsa.X86_64.Generation.Widths.width n₃₈₄ c₃₈₄)
      (Spec.Dsa.GenerationSized.contract 384 abi 600)) :
    Verified target (Impl.Dsa.X86_64.Generation.Widths.large n₂₅₆ n₃₈₄ c₂₅₆ c₃₈₄) (largeContract 600) := by
  refine Verified.entryBranch (p := fun s => s.gpr .rdx == 256) (fun _ => []) h₂₅₆ h₃₈₄
    (fun s hs => ⟨_, rfl, ?_, fun hp => ⟨sized_of_large hs ?_, fun s' a q => ⟨a, q⟩⟩,
      fun hp => ⟨sized_of_large hs ?_, fun s' a q => ⟨a, q⟩⟩⟩) ?_ large_sat
  · show some ((s.gpr .rdx - BitVec.signExtend 64 (256 : BitVec 32)) == 0) = some (s.gpr .rdx == 256)
    rw [show BitVec.signExtend 64 (256 : BitVec 32) = 256 from by decide, VG.Proof.Bignum.X86_64.sub_beq_zero]
  · show (s.gpr .rdx).toNat = 256
    rw [beq_iff_eq.mp hp]; rfl
  · show (s.gpr .rdx).toNat = 384
    rcases width_of_large hs with h | h
    · exfalso
      have : s.gpr .rdx = 256 := BitVec.eq_of_toNat_eq h
      simp [this] at hp
    · exact h
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [largeContract, Spec.Dsa.generateParametersSig, abi, argRegs, stackArgs_six] at hq'
    obtain ⟨-, -, -, -, hrdx, -⟩ := hq'
    exact ⟨rfl, by rw [hrdx], fun _ => hq, fun _ => hq⟩

theorem widths_verified {n₁₂₈ n₂₅₆ n₃₈₄ : String} {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa}
    (h₁₂₈ : Verified target (Impl.Dsa.X86_64.Generation.Widths.width n₁₂₈ c₁₂₈)
      (Spec.Dsa.GenerationSized.contract 128 abi 600))
    (h₂₅₆ : Verified target (Impl.Dsa.X86_64.Generation.Widths.width n₂₅₆ c₂₅₆)
      (Spec.Dsa.GenerationSized.contract 256 abi 600))
    (h₃₈₄ : Verified target (Impl.Dsa.X86_64.Generation.Widths.width n₃₈₄ c₃₈₄)
      (Spec.Dsa.GenerationSized.contract 384 abi 600)) :
    Verified target (Impl.Dsa.X86_64.Generation.Widths.widths n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄)
      (Spec.Dsa.generateParametersContract abi 600) := by
  refine Verified.entryBranch (p := fun s => s.gpr .rdx == 128) (fun _ => []) h₁₂₈
    (large_verified h₂₅₆ h₃₈₄)
    (fun s hs => ⟨_, rfl, ?_, fun hp => ⟨sized_of_full hs ?_, fun s' a q => ⟨a, q⟩⟩,
      fun hp => ⟨large_of_full hs ?_, fun s' a q => ⟨a, q⟩⟩⟩) ?_ full_sat
  · show some ((s.gpr .rdx - BitVec.signExtend 64 (128 : BitVec 32)) == 0) = some (s.gpr .rdx == 128)
    rw [show BitVec.signExtend 64 (128 : BitVec 32) = 128 from by decide, VG.Proof.Bignum.X86_64.sub_beq_zero]
  · show (s.gpr .rdx).toNat = 128
    rw [beq_iff_eq.mp hp]; rfl
  · show (s.gpr .rdx).toNat ≠ 128
    intro h
    have : s.gpr .rdx = 128 := BitVec.eq_of_toNat_eq h
    simp [this] at hp
  · intro s s' u u' hs hs' hq e e'
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e)
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    have hq' := hq
    sig_pub [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs,
      stackArgs_six] at hq'
    obtain ⟨-, -, -, -, hrdx, -⟩ := hq'
    exact ⟨rfl, by rw [hrdx], fun _ => hq, fun _ => hq⟩

/-- The complete generation, by the restricted bodies for each width, each
verified against its restricted contract. -/
theorem generation_verified {n₁₂₈ n₂₅₆ n₃₈₄ : String} {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa}
    (h₁₂₈ : Verified target c₁₂₈ (Spec.Dsa.GenerationSized.contract 128 abi 536))
    (h₂₅₆ : Verified target c₂₅₆ (Spec.Dsa.GenerationSized.contract 256 abi 536))
    (h₃₈₄ : Verified target c₃₈₄ (Spec.Dsa.GenerationSized.contract 384 abi 536))
    (s₁₂₈ : c₁₂₈.all (fun i => !isa.writesSp i) = true) (s₂₅₆ : c₂₅₆.all (fun i => !isa.writesSp i) = true)
    (s₃₈₄ : c₃₈₄.all (fun i => !isa.writesSp i) = true)
    (d₁₂₈ : c₁₂₈.x86_64Depth ≤ 536) (d₂₅₆ : c₂₅₆.x86_64Depth ≤ 536) (d₃₈₄ : c₃₈₄.x86_64Depth ≤ 536) :
    Verified target (Impl.Dsa.X86_64.Generation.Widths.widths n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄)
      (Spec.Dsa.generateParametersContract abi 600) :=
  widths_verified (forward_sized 128 h₁₂₈ s₁₂₈ d₁₂₈ (sized_sat 128 (.inl rfl)))
    (forward_sized 256 h₂₅₆ s₂₅₆ d₂₅₆ (sized_sat 256 (.inr (.inl rfl))))
    (forward_sized 384 h₃₈₄ s₃₈₄ d₃₈₄ (sized_sat 384 (.inr (.inr rfl))))

/-- The choice writes `rsp` only in frames and calls, if its bodies do. -/
theorem widths_spSafe {n₁₂₈ n₂₅₆ n₃₈₄ : String} {c₁₂₈ c₂₅₆ c₃₈₄ : Prog isa}
    (s₁₂₈ : c₁₂₈.all (fun i => !isa.writesSp i) = true) (s₂₅₆ : c₂₅₆.all (fun i => !isa.writesSp i) = true)
    (s₃₈₄ : c₃₈₄.all (fun i => !isa.writesSp i) = true) :
    (Impl.Dsa.X86_64.Generation.Widths.widths n₁₂₈ n₂₅₆ n₃₈₄ c₁₂₈ c₂₅₆ c₃₈₄).all
      (fun i => !isa.writesSp i) = true := by
  simp only [Impl.Dsa.X86_64.Generation.Widths.widths, Impl.Dsa.X86_64.Generation.Widths.large,
    Impl.Dsa.X86_64.Generation.Widths.width, Code.iteCold, Code.all, forward_spSafe s₁₂₈, forward_spSafe s₂₅₆,
    forward_spSafe s₃₈₄, Bool.and_true]
  rfl

/-! ## The instances the registration binds -/

/-- The restricted body for width `p`, with the hash `h` and Miller–Rabin `v`. -/
def body (h : MdHash) (v : RoundImpl) (p : Nat) : Prog isa :=
  Impl.Dsa.X86_64.Generation.Sized.single (checkName := SharedChecker.name) p h.H.stream
    VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.toS.mm
    VG.Proof.Variants.MillerRabin.X86_64.Base.variant.inlineMont.mm
    (VG.Proof.Dsa.X86_64.ProbablePrime.primeTest v).run

/-- The name the restricted body for width `p` is emitted as, its hash tagged `tag`. -/
def name (tag : String) (h : MdHash) (v : RoundImpl) (p : Nat) : String :=
  (Spec.Dsa.GenerationSized.api p).name ++ Emit.qualifiedName "" [(tag, h.suffix), ("mr", v.suffix)]

/-- The complete generation with the hashes `v1` and `v256` and Miller–Rabin `v`. -/
def code (v1 v256 : MdHash) (v : RoundImpl) : Prog isa :=
  Impl.Dsa.X86_64.Generation.Widths.widths (name "sha1" v1 v 128) (name "sha256" v256 v 256)
    (name "sha256" v256 v 384) (body v1 v 128) (body v256 v 256) (body v256 v 384)

theorem code_verified (v1 v256 : MdHash) (v : RoundImpl) (h1 : v1.mgf.G.rust = "sha1")
    (h256 : v256.mgf.G.rust = "sha256") :
    Verified target (code v1 v256 v) (Spec.Dsa.generateParametersContract abi 600) :=
  generation_verified (Sized.sha1_verified v1 v h1) (Sized.sha256_verified v256 v h256 256 (.inl rfl))
    (Sized.sha256_verified v256 v h256 384 (.inr rfl)) (Sized.sha1_safe v1 v)
    (Sized.sha256_safe v256 v 256 (.inl rfl)) (Sized.sha256_safe v256 v 384 (.inr rfl))
    (single_depth v1 v 128) (single_depth v256 v 256) (single_depth v256 v 384)

theorem code_spSafe (v1 v256 : MdHash) (v : RoundImpl) :
    (code v1 v256 v).all (fun i => !isa.writesSp i) = true :=
  widths_spSafe (Sized.sha1_safe v1 v) (Sized.sha256_safe v256 v 256 (.inl rfl))
    (Sized.sha256_safe v256 v 384 (.inr rfl))

end VG.Proof.Dsa.X86_64.Generation.Widths
