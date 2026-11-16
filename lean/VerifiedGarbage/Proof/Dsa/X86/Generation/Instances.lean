module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Hash
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
public import VerifiedGarbage.Proof.MillerRabin.X86.Baseline
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABI
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Test
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.TimingFront
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCoreTiming
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Width
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinishTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Parameters
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Load
public import VerifiedGarbage.Proof.Mont.X86.Compact.Frame
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSieve
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveSetup
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveCandidateSlots
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoopTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.RsaKeyGen.X86.CandidateSieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.NoSp
import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Environment
public import VerifiedGarbage.Proof.RsaKeyGen.MrCounts
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.ABIEntry
import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateEnvironment
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinState
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.RsaKeyGen.KeyCheck
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpPrepare
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Enter
public import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Finish
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateNoSpWords
import VerifiedGarbage.Proof.Mont.X86.Compact.Restore
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFinish
import VerifiedGarbage.Proof.Dsa.X86.ProbablePrime.Memory
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessStep
public import VerifiedGarbage.Impl.Dsa.X86.ProbablePrime
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStackUse
public import VerifiedGarbage.Proof.Dsa.X86.CheckingVerified
public import VerifiedGarbage.Proof.MillerRabin.X86.MontInstance
public import VerifiedGarbage.Proof.Mont.X86.Sse2.PreparedVerified

/-! ### `Dsa.X86.Generation.HashInst`, which only this module used -/

section

/-! # SHA-1 and SHA-256, with any backend, hash a seed -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Dsa.X86.Generation

theorem ivBytes_getElem? (iv : List (BitVec 32)) {j i : Nat} (hj : j < iv.length) (hi : i < 4) :
    (ivBytes iv)[4 * j + i]? = some (iv[j].extractLsb' (8 * i) 8) := by
  induction iv generalizing j with
  | nil => simp at hj
  | cons w ws ih =>
    obtain chunk : ((List.range 4).map fun k => w.extractLsb' (8 * k) 8).length = 4 := by simp
    simp only [ivBytes, List.flatMap_cons] at ih ⊢
    rcases j with _ | j
    · rw [List.getElem?_append_left (by rw [chunk]; omega_using [hi])]
      simp [hi]
    · rw [List.getElem?_append_right (by rw [chunk]; omega_using []), chunk,
        show 4 * (j + 1) + i - 4 = 4 * j + i by omega_using []]
      exact ih (by simp at hj; omega_using [hj])

/-- The word `j` of an initial value whose bytes memory holds. -/
theorem iv_word {m : Mem} {p : Addr} {iv : List (BitVec 32)}
    (h : Spec.Sha256.bytesAt m p (4 * iv.length) = ivBytes iv) {j : Nat} (hj : j < iv.length) :
    m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = iv[j] := by
  show m.read _ 4 = _
  apply Mem.read_eq_of_bytes
  intro i hi
  obtain e := congrArg (·[4 * j + i]?) h
  simp only [Spec.Sha256.bytesAt, List.getElem?_map, List.getElem?_range (show 4 * j + i < 4 * iv.length by omega_using [hj, hi]),
    Option.map_some, ivBytes_getElem? iv hj hi, Option.some.injEq] at e
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact e

def sha1_hashOk (v : Proof.Sha1.X86.Variants.Backend) :
    HashOk (Proof.Pbkdf2.Md.X86.sha1M v.stream v.cmpN v.cmpC) Spec.Sha1.H0.toList where
  ok := Proof.Pbkdf2.Md.X86.sha1Ok v.stream v.cmpN v.comp
  ivLen := rfl
  ivVal m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Pbkdf2.Md.X86.sha1Ok, Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact (iv_word (iv := Spec.Sha1.H0.toList) h (by simpa using hj)).trans (by simp)
  lenB := by
    show Proof.Sha1.md.lenBytes 20 = (List.range 8).map fun i => BitVec.ofNat 8 ((8 * 20) >>> (8 * (7 - i)))
    decide
  B := rfl
  L := rfl
  DN := rfl

def sha256_hashOk (v : Proof.Sha256.X86.Variants.Backend) :
    HashOk (Proof.Pbkdf2.Md.X86.sha256M v.stream v.cmpN v.cmpC) Spec.Sha256.H0.toList where
  ok := Proof.Pbkdf2.Md.X86.sha256Ok v.stream v.cmpN v.comp
  ivLen := rfl
  ivVal m p h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Pbkdf2.Md.X86.sha256Ok, Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact (iv_word (iv := Spec.Sha256.H0.toList) h (by simpa using hj)).trans (by simp)
  lenB := by
    show Proof.Sha256.md.lenBytes 32 = (List.range 8).map fun i => BitVec.ofNat 8 ((8 * 32) >>> (8 * (7 - i)))
    decide
  B := rfl
  L := rfl
  DN := rfl

example (v : Proof.Sha1.X86.Variants.Backend) (m : List Byte) :
    (sha1_hashOk v).ok.hH.SH.H.hash m = Spec.Dsa.seedHash 160 m := rfl

example (v : Proof.Sha256.X86.Variants.Backend) (m : List Byte) :
    (sha256_hashOk v).ok.hH.SH.H.hash m = Spec.Dsa.seedHash 256 m := rfl

end VG.Proof.Dsa.X86.Generation

end

end

/-! ### `Dsa.X86.ProbablePrime.Verified`, which only this module used -/

section

/-! ### `Dsa.X86.ProbablePrime.ConstantTime`, which only this module used -/

section

/-! ### `Dsa.X86.ProbablePrime.TimingBody`, which only this module used -/

section

/-! ### `Dsa.X86.ProbablePrime.TimingTest`, which only this module used -/

section

/-! # The prepared test leaks only the candidate, the tape and public pointers -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86 VG.Impl.Mont.X86

/-- The private frame's input to RSA's prepared test. -/
theorem private_input {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t : State}
    (L : Loaded E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits)
    (S : Scr t E.base E.size) (C : Caller E.geometry E.capacity (E.p - 28#32) t)
    (F : Frame [below E.p 28] s.mem t.mem) (K : Keeps [.edx] (allocFrame 28 s) t) :
    CandidatePrepare.Input (E.parameters c entropy) t := by
  obtain shape := candidate_shape odd length (by have := v.bits.low; omega_using [this])
  obtain workspaceFar : E.workspaceRegion.Disjoint (below E.p 28) :=
    (v.stackFar _ List.mem_cons_self).sub_right (below_sub (by decide) v.low)
  obtain randFar : E.randRegion.Disjoint (below E.p 28) :=
    (v.stackFar _ (List.mem_cons_of_mem _ List.mem_cons_self)).sub_right (below_sub (by decide) v.low)
  obtain fit : E.base.toNat + E.size ≤ 2 ^ 32 := by rw [v.baseNat]; exact v.workspaceFit
  obtain W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F fit
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  have header := v.header
  obtain big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := v.bits.low; omega_using [this])
  refine ⟨⟨S, C, ?_, ?_, odd, by change 1 < c; omega_using [shape, big], Nat.le_of_lt shape.2.1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (W.val32 (v.geometry.arrayFit (j := 0) (by decide)) (by intro r mem; cases mem)).trans L.value
  · exact (W.val32 (v.geometry.arrayFit (j := 5) (by decide)) (by intro r mem; cases mem)).trans L.minusOne
  · rw [K.2.1, K.2.2]
    obtain ⟨r, mem, contains⟩ := L.input.memory.randRead
    refine ⟨r, ?_, contains⟩
    change r ∈ s.rd ++ (⟨(s.gpr .esp - 28#32).setWidth 64, 28⟩ :: s.wr)
    exact (List.mem_append.mp mem).elim (List.mem_append_left _)
      (fun known => List.mem_append_right _ (List.mem_cons_of_mem _ known))
  · change Spec.Rsa.bytesAt t.mem (E.rand.setWidth 64) E.randLength = entropy
    rw [VG.Proof.RsaKeyGen.frame_bytesAt F
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact randFar) (by have := v.randLengthFit; omega_using [this])]
    exact L.input.memory.entropy
  · exact (W.read32 (d := 28) (by change 28 + 4 ≤ E.size; omega_using [header]) (by intro r mem; cases mem)).trans L.input.randPtr
  · exact (congrArg BitVec.toNat (W.read32 (d := 32) (by change 32 + 4 ≤ E.size; omega_using [header])
      (by intro r mem; cases mem))).trans L.input.randLength
  · exact (congrArg BitVec.toNat (W.read32 (d := 152) (by change 152 + 4 ≤ E.size; omega_using [header])
      (by intro r mem; cases mem))).trans L.count

theorem core_pair {E : Environment} {c : Nat} {entropy : List Byte} {s t : State}
    (I : CandidatePrepare.Input (E.parameters c entropy) s) (J : CandidatePrepare.Input (E.parameters c entropy) t) :
    CandidateTest.CorePair (E.parameters c entropy) c entropy s t := by
  refine ⟨?_, I, J, rfl⟩
  apply agree_regs
  intro r mem
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact I.prepare.caller.sp.trans J.prepare.caller.sp.symm
  · exact BitVec.eq_of_toNat_eq (I.prepare.scratch.edi_toNat.trans J.prepare.scratch.edi_toNat.symm)

theorem capacity_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (space : 44 ≤ size) :
    WP isa (.block [.mov .edx (.mem (sc 40))]) s fun t => Upd s t .edx (s.mem.readW (off base 40) 32) :=
  wp_movS (readSrc_sc S space) fun _ U _ => WP.block_nil U

theorem Loaded.capacityWord {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) : s.mem.readW (off E.base 40) 32 = BitVec.ofNat 32 E.capacity := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := v.workspaceFit; unfold Environment.size at this; omega_using [this])]
  exact L.input.capacity

theorem tested_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (LoadedPair E c entropy)
      (VG.Impl.RsaKeyGen.X86.CandidateTest.codeWith (E.bits - 1) (Spec.Dsa.primeChecks E.bits)
        (8 * ((E.bits + 63) / 64)) E.words E.width montName mont roundName round) (fun _ _ => True) := by
  intro s t tr ur u z H A B
  have space := v.header
  obtain P := v.parameters_valid odd length H.1.input.memory.entropyLength
  obtain raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block [.mov .edx (.mem (sc 40))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  cases A with
  | seq argsA frameA =>
    cases B with
    | seq argsB frameB =>
      obtain argsTrace := (raw _ _ _ _ _ _ (H.1.input.agree H.2.input) argsA argsB).1
      obtain Ua := wp_result (capacity_ok H.1.input.scratch (by omega_using [space])) argsA
      obtain Ub := wp_result (capacity_ok H.2.input.scratch (by omega_using [space])) argsB
      obtain ⟨Da, _, _⟩ := H.1.keepStack v (by rw [Ua.mem]; exact Frame.refl _ _) Ua.keeps (by decide) (by decide)
        (by rw [Ua.syms])
      obtain ⟨Db, _, _⟩ := H.2.keepStack v (by rw [Ub.mem]; exact Frame.refl _ _) Ub.keeps (by decide) (by decide)
        (by rw [Ub.syms])
      obtain capA := Ua.gpr.trans (H.1.capacityWord v)
      obtain capB := Ub.gpr.trans (H.2.capacityWord v)
      cases frameA with
      | frame pushA bodyA popA =>
        cases frameB with
        | frame pushB bodyB popB =>
          obtain ea := alloc_some pushA
          obtain eb := alloc_some pushB
          subst ea eb
          cases bodyA with
          | seq storeA coreA =>
            cases bodyB with
            | seq storeB coreB =>
              have separate (q : State) (D : Loaded E c entropy q) :
                  (q.gpr .esp).toNat ≤ E.geometry.W.toNat ∨ E.geometry.W.toNat + E.geometry.L + 136 ≤ (q.gpr .esp).toNat := by
                rw [D.input.stack]; rcases v.workspaceStack with h | h; exact Or.inl h; exact Or.inr h
              obtain ⟨Sa, Ca, _, Fa, Ka⟩ := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity)
                Da.input.scratch (by rw [Da.input.stack]; exact v.low) (separate _ Da) capA) storeA
              obtain ⟨Sb, Cb, _, Fb, Kb⟩ := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity)
                Db.input.scratch (by rw [Db.input.stack]; exact v.low) (separate _ Db) capB) storeB
              rw [CandidateFrame.privateSp, Da.input.stack] at Ca
              rw [CandidateFrame.privateSp, Db.input.stack] at Cb
              rw [Da.input.stack] at Fa
              rw [Db.input.stack] at Fb
              obtain Ia := private_input v Da odd length Sa Ca Fa (Keeps.mono Ka (rs' := [.edx]) (by decide))
              obtain Ib := private_input v Db odd length Sb Cb Fb (Keeps.mono Kb (rs' := [.edx]) (by decide))
              obtain coreTrace := (CandidateTest.core_trace montVerified montNoSp montStack roundVerified roundNoSp
                roundStack P v.width_high (other := c) (entropy := entropy) P (Nat.zero_le _)
                _ _ _ _ _ _ (core_pair Ia Ib) coreA coreB).1
              obtain storeRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.store (at_ .esp 24) .edx])
                  (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
              obtain storeTrace := (storeRaw _ _ _ _ _ _ (by
                apply agree_regs
                intro r mem
                obtain rfl := List.mem_singleton.mp mem
                rw [allocFrame_esp, allocFrame_esp, Da.input.stack, Db.input.stack]) storeA storeB).1
              refine ⟨?_, trivial⟩
              change _ ++ ([] ++ (_ ++ _) ++ []) = _ ++ ([] ++ (_ ++ _) ++ [])
              rw [argsTrace, storeTrace, coreTrace]

/-- What the finish reads, equal on both sides. -/
structure FinishPair (E : Environment) (s t : State) : Prop where
  left : Scr s E.base E.size
  right : Scr t E.base E.size
  stack : s.gpr .esp = t.gpr .esp
  used : s.mem.readW (off E.base 44) 32 = t.mem.readW (off E.base 44) 32
  status : s.mem.readW (off E.base 168) 32 = t.mem.readW (off E.base 168) 32

def ControlPair (E : Environment) (s t : State) : Prop :=
  FinishPair E s t ∧ s.gpr .eax = t.gpr .eax ∧ isa.eval .e s = isa.eval .e t

theorem FinishPair.keep {E : Environment} {s t u z : State} (P : FinishPair E s t)
    (mu : u.mem = s.mem) (mz : z.mem = t.mem) {rs : List Reg} (Ku : Keeps rs s u) (Kz : Keeps rs t z)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : FinishPair E u z :=
  ⟨P.left.of_keeps Ku edi esp, P.right.of_keeps Kz edi esp,
    by rw [Ku.1 .esp esp, Kz.1 .esp esp]; exact P.stack, by rw [mu, mz]; exact P.used, by rw [mu, mz]; exact P.status⟩

theorem FinishPair.agree {E : Environment} {s t : State} (P : FinishPair E s t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact P.stack
  · exact BitVec.eq_of_toNat_eq (P.left.edi_toNat.trans P.right.edi_toNat.symm)

theorem status_trace {E : Environment} (v : E.Valid) :
    RelCT isa (FinishPair E) (.block Candidate.statusArgs) (ControlPair E) := by
  intro s t tr ur u z P A B
  obtain space : 172 ≤ E.size := by have := v.header; omega_using [this]
  obtain raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block Candidate.statusArgs)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  obtain ⟨valueU, flagU, memU, KU⟩ := wp_result (Candidate.statusArgs_ok P.left space) A
  obtain ⟨valueZ, flagZ, memZ, KZ⟩ := wp_result (Candidate.statusArgs_ok P.right space) B
  exact ⟨(raw _ _ _ _ _ _ P.agree A B).1, P.keep memU memZ KU KZ, valueU.trans (P.status.trans valueZ.symm),
    by rw [flagU, flagZ, P.status]⟩

theorem compare_trace {E : Environment} :
    RelCT isa (ControlPair E) (.block [.alu .cmp .eax (.imm 0)]) (ControlPair E) := by
  intro s t tr ur u z P A B
  obtain raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .eax])) (.block [.alu .cmp .eax (.imm 0)])
      (VG.X86.Taint.Agree (τr [.esp, .edi, .eax])) := checkedBlockInvariant rfl rfl
  obtain agree : VG.X86.Taint.Agree (τr [.esp, .edi, .eax]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact P.1.stack
    · exact BitVec.eq_of_toNat_eq (P.1.left.edi_toNat.trans P.1.right.edi_toNat.symm)
    · exact P.2.1
  obtain ⟨U, flagU⟩ := wp_result Candidate.compareZero_ok A
  obtain ⟨Z, flagZ⟩ := wp_result Candidate.compareZero_ok B
  refine ⟨(raw _ _ _ _ _ _ agree A B).1, P.1.keep U.mem Z.mem (U.keeps []) (Z.keeps []), ?_, ?_⟩
  · rw [U.gpr, Z.gpr]; exact P.2.1
  · rw [flagU, flagZ, P.2.1]

theorem finish_trace {E : Environment} (v : E.Valid) :
    RelCT isa (FinishPair E) VG.Impl.Dsa.X86.ProbablePrime.finish (fun _ _ => True) := by
  have pair {s t : State} (P : ControlPair E s t) : CandidateFinish.FinishPair E.base E.size s t :=
    ⟨P.1.left, P.1.right, P.1.used⟩
  obtain space : 156 ≤ E.size := by have := v.header; omega_using [this]
  unfold VG.Impl.Dsa.X86.ProbablePrime.finish
  refine RelCT.seq (status_trace v) (VG.RelCT.ite (fun _ _ P => P.2.2) ?_ ?_)
  · exact (CandidateFinish.used_trace space 1).mono (fun _ _ P => pair P.1) (fun _ _ _ => trivial)
  · refine RelCT.seq (compare_trace.mono (fun _ _ P => P.1) (fun _ _ P => P))
      (VG.RelCT.ite (fun _ _ P => P.2.2) ?_ ?_)
    · exact (CandidateFinish.none_trace space).mono (fun _ _ P => pair P.1) (fun _ _ _ => trivial)
    · exact (CandidateFinish.used_trace space 2).mono (fun _ _ P => pair P.1) (fun _ _ _ => trivial)

theorem test_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (LoadedPair E c entropy) (VG.Impl.Dsa.X86.ProbablePrime.test E.bits montName mont roundName round)
      (fun _ _ => True) := by
  unfold VG.Impl.Dsa.X86.ProbablePrime.test
  refine RelCT.seq (R := FinishPair E) ?_ (finish_trace v)
  intro s t tr ur u z H A B
  obtain trace := (tested_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v odd length
    _ _ _ _ _ _ H A B).1
  obtain ⟨Iu, statusU, _, _, _, _⟩ := wp_result
    (tested_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v H.1 odd length) A
  obtain ⟨Iz, statusZ, _, _, _, _⟩ := wp_result
    (tested_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v H.2 odd length) B
  refine ⟨trace, Iu.scratch, Iz.scratch, Iu.stack.trans Iz.stack.symm, Iu.usedPtr.trans Iz.usedPtr.symm, ?_⟩
  exact BitVec.eq_of_toNat_eq (statusU.trans statusZ.symm)

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! ### `RsaKeyGen.X86.CandidateSieveTiming`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.SieveTiming`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.SieveSetupTiming`, which only this module used -/

section

/-! # The static table and stack setup have public memory addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem setup_trace {g : Geometry} (v : g.Valid) {c d : Nat} (low : 4 ≤ g.sp.toNat) :
    RelCT isa (fun s t => Context g c s ∧ Context g d t ∧ s.gpr .edi = g.candidate ∧ t.gpr .edi = g.candidate)
      (.seq (.block (candidateSlots stackSlots g.w))
        (.seq tableAddress (.block (tableSlots stackSlots g.w))))
      (VG.X86.Taint.Agree (τr [.esp])) := by
  obtain first : RelCT isa (fun s t => Context g c s ∧ Context g d t ∧ s.gpr .edi = g.candidate ∧ t.gpr .edi = g.candidate)
      (.block (candidateSlots stackSlots g.w))
      (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp) := by
    intro s t tr ur u z ⟨S, T, Ps, Pt⟩ E G
    obtain A : VG.X86.Taint.Agree (τr [.esp]) s t :=
      agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact S.stack.sp.trans T.stack.sp.symm)
    obtain trace := ((erased_relCT (τ := τr [.esp]) (σ := τr [.esp]) (.block (candidateSlots stackSlots g.w)) (.block (candidateSlots stackSlots 0)) (.block []) rfl rfl rfl (by decide +kernel))
      _ _ _ _ _ _ A E G).1
    obtain U := wp_result (candidateSlots_ok v S Ps) E
    obtain Z := wp_result (candidateSlots_ok v T Pt) G
    exact ⟨trace, U.1.context.stack.sp, Z.1.context.stack.sp⟩
  obtain middle : RelCT isa (fun s t => s.gpr .esp = g.sp ∧ t.gpr .esp = g.sp)
      tableAddress (VG.X86.Taint.Agree (τr [.esp])) := by
    intro s t tr ur u z ⟨S, T⟩ E G
    obtain Ls : 4 ≤ (s.gpr .esp).toNat := by rw [S]; exact low
    obtain Lt : 4 ≤ (t.gpr .esp).toNat := by rw [T]; exact low
    obtain U := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol s Ls) E
    obtain Z := wp_result (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol t Lt) G
    refine ⟨?_, agree_regs (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact
      (U.gpr .esp (by decide)).trans (S.trans (T.symm.trans (Z.gpr .esp (by decide)).symm)))⟩
    rw [symFrame_trace Ls E, symFrame_trace Lt G, S, T]
  exact RelCT.seq first (RelCT.seq middle (erased_relCT (.block (tableSlots stackSlots g.w)) (.block (tableSlots stackSlots 0)) (.block []) rfl rfl rfl (by decide +kernel)))

end VG.Proof.RsaKeyGen.X86.Sieve

end

end


/-! # The complete sieve preserves the candidate contract's timing distinction -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

def Ready (g : Geometry) (c : Nat) (s : State) : Prop :=
  Context g c s ∧ s.gpr .edi = g.candidate ∧ s.syms TrialTable32.symbol = g.table

theorem body_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d)
    (length : g.limit = tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => Ready g c s ∧ Ready g d t)
      (body stackSlots g.w) (VG.X86.Taint.Agree (τr [.esp])) := by
  obtain setup : RelCT isa (fun s t => Ready g c s ∧ Ready g d t)
      (.seq (.block (candidateSlots stackSlots g.w))
        (.seq tableAddress (.block (tableSlots stackSlots g.w))))
      (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t) := by
    intro s t tr ur u z ⟨⟨S, Ps, Ss⟩, ⟨T, Pt, St⟩⟩ E G
    obtain trace := (setup_trace v low _ _ _ _ _ _ ⟨S, T, Ps, Pt⟩ E G).1
    obtain U := wp_result (setup_ok v S Ps length Ss low candidateFar tableFar) E
    obtain Z := wp_result (setup_ok v T Pt length St low candidateFar tableFar) G
    exact ⟨trace, U.1, Z.1⟩
  intro s t tr ur u z H E G
  cases E with
  | seq A E =>
    cases E with
    | seq B E =>
      cases E with
      | seq C L =>
        cases G with
        | seq D G =>
          cases G with
          | seq F G =>
            cases G with
            | seq K N =>
              obtain R := RelCT.seq setup (loop_trace v pattern) _ _ _ _ _ _ H
                (.seq (.seq A (.seq B C)) L) (.seq (.seq D (.seq F K)) N)
              simpa only [List.append_assoc] using R

end VG.Proof.RsaKeyGen.X86.Sieve

end

end


/-! # Candidate sieve framing releases only the existing trial-divisor pattern -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateSieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.CandidateSieve

def Entry (g : Sieve.Geometry) (c : Nat) (s : State) : Prop :=
  Sieve.Context g c s ∧ s.gpr .edi + 256#32 = g.candidate ∧ s.syms TrialTable32.symbol = g.table

theorem setup_ready {g : Sieve.Geometry} {c : Nat} {s : State} (S : Entry g c s) :
    WP isa (.block setup) s (Sieve.Ready g c) := by
  unfold setup
  refine wp_addS rfl fun a A _ => WP.block_nil ?_
  refine ⟨?_, A.gpr.trans S.2.1, ?_⟩
  · refine ⟨S.1.stack.keep A.keeps (by decide), ?_, ?_, ?_, ?_⟩
    · intro i index; rw [A.keeps.2.1, A.keeps.2.2]; exact S.1.candidateRead i index
    · intro i index d mem; rw [A.keeps.2.1, A.keeps.2.2]; exact S.1.tableRead i index d mem
    · intro i index; rw [A.mem]; exact S.1.tableWords i index
    · rw [A.mem]; exact S.1.candidateValue
  · rw [A.syms]; exact S.2.2

theorem setup_trace {g : Sieve.Geometry} {c d : Nat} :
    RelCT isa (fun s t => Entry g c s ∧ Entry g d t) (.block setup)
      (fun s t => Sieve.Ready g c s ∧ Sieve.Ready g d t) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  obtain A : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact S.1.stack.sp.trans T.1.stack.sp.symm
    · have H := congrArg (fun x : BitVec 32 => x - 256#32) (S.2.1.trans T.2.1.symm)
      simpa only [BitVec.add_sub_cancel] using H
  obtain raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block setup)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  exact ⟨(raw _ _ _ _ _ _ A E G).1, wp_result (setup_ready S) E, wp_result (setup_ready T) G⟩

theorem body_trace {g : Sieve.Geometry} (v : g.Valid) {c d : Nat} (pattern : Sieve.SamePattern g c d)
    (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => Entry g c s ∧ Entry g d t) (body g.w)
      (VG.X86.Taint.Agree (τr [.esp])) := by
  unfold body
  exact RelCT.seq setup_trace (RelCT.seq (Sieve.body_trace v pattern length low candidateFar tableFar)
    (checkedBlockInvariant rfl rfl))

theorem code_trace {g : Sieve.Geometry} (v : g.Valid) {c d : Nat} (pattern : Sieve.SamePattern g c d)
    (length : g.limit = VG.Impl.RsaKeyGen.X86.Sieve.tableCount g.w) (low : 4 ≤ g.sp.toNat)
    (candidateFar : g.candidateRegion.Disjoint (below g.sp 4))
    (tableFar : g.tableRegion.Disjoint (below g.sp 4)) :
    RelCT isa (fun s t => Entry g c (allocFrame 20 s) ∧ Entry g d (allocFrame 20 t))
      (code g.w) (fun _ _ => True) := by
  unfold code
  apply RelCT.frameAlloc
  refine (body_trace v pattern length low candidateFar tableFar).mono ?_ (fun _ _ _ => trivial)
  rintro _ _ ⟨s, t, H, rfl, rfl⟩
  exact H

end VG.Proof.RsaKeyGen.X86.CandidateSieve

end

end


/-! # The whole test leaks only what the contract releases -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86 VG.Impl.Mont.X86

theorem sieve_entry {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) : CandidateSieve.Entry E.sieveGeometry c (allocFrame 20 s) := by
  obtain pointer : s.gpr .edi = E.workspace := by
    apply BitVec.eq_of_toNat_eq
    rw [L.input.scratch.edi_toNat, v.baseNat]
  refine ⟨sieve_context v L, ?_, ?_⟩
  · rw [allocFrame_gpr _ _ (by decide), pointer]; rfl
  · exact L.input.memory.symbol

theorem sieve_pair {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (large : 8161 < c) :
    RelCT isa (LoadedPair E c entropy) (VG.Impl.RsaKeyGen.X86.CandidateSieve.code E.width)
      (Candidate.WithFlag (LoadedPair E c entropy)
        (Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c)) := by
  obtain privateSub : (below E.sieveGeometry.sp 4).Sub (below E.p 136) := below_inner (by decide) v.low
  obtain workspaceFar : E.workspaceRegion.Disjoint (below E.p 136) := v.stackFar _ List.mem_cons_self
  obtain tableFar : E.tableRegion.Disjoint (below E.p 136) := v.stackFar _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  intro s t tr ur u z P A B
  obtain trace := (CandidateSieve.code_trace v.sieve_valid (c := c) (d := c) (fun _ _ => rfl) rfl
    (by change 4 ≤ (E.p - 20#32).toNat; rw [sub_toNat (by have := v.low; omega_using [this])]; have := v.low; omega_using [this])
    ((workspaceFar.sub_left v.sieveCandidateSub).sub_right privateSub) (tableFar.sub_right privateSub)
    _ _ _ _ _ _ ⟨sieve_entry v P.1, sieve_entry v P.2⟩ A B).1
  obtain ⟨LU, flagU, _, _, _⟩ := wp_result (sieve_ok v P.1 large) A
  obtain ⟨LZ, flagZ, _, _, _⟩ := wp_result (sieve_ok v P.2 large) B
  exact ⟨trace, ⟨LU, LZ⟩, flagU, flagZ⟩

theorem LoadedPair.keepFlags {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s t u z : State}
    (P : LoadedPair E c entropy s t) (U : Fupd s u) (Z : Fupd t z) : LoadedPair E c entropy u z :=
  ⟨(P.1.keepStack v (by rw [U.mem]; exact Frame.refl _ _) (U.keeps []) (by decide) (by decide)
      (by rw [U.syms])).1,
    (P.2.keepStack v (by rw [Z.mem]; exact Frame.refl _ _) (Z.keeps []) (by decide) (by decide)
      (by rw [Z.syms])).1⟩

theorem sieved_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (LoadedPair E c entropy)
      (VG.Impl.Dsa.X86.ProbablePrime.sieved E.bits montName mont roundName round) (fun _ _ => True) := by
  obtain shape := candidate_shape odd length (by have := v.bits.low; omega_using [this])
  obtain big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := v.bits.low; omega_using [this])
  obtain space : 156 ≤ E.size := by have := v.header; omega_using [this]
  have finishPair {s t : State} (P : LoadedPair E c entropy s t) : CandidateFinish.FinishPair E.base E.size s t :=
    ⟨P.1.input.scratch, P.2.input.scratch, P.1.input.usedPtr.trans P.2.input.usedPtr.symm⟩
  unfold VG.Impl.Dsa.X86.ProbablePrime.sieved
  cases composite : Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c
  · have initial := sieve_pair v (c := c) (entropy := entropy) (by omega_using [shape, big])
    rw [composite] at initial
    refine RelCT.seq initial (RelCT.seq ((Candidate.cmp_flag_trace false
      (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact Candidate.branch_false (test_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
      v odd length)
  · have initial := sieve_pair v (c := c) (entropy := entropy) (by omega_using [shape, big])
    rw [composite] at initial
    refine RelCT.seq initial (RelCT.seq ((Candidate.cmp_flag_trace true
      (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono (fun _ _ P => P) (fun _ _ P => P.2)) ?_)
    exact Candidate.branch_true ((CandidateFinish.used_trace space 2).mono (fun _ _ P => finishPair P)
      (fun _ _ _ => trivial))

theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (EntryPair E c entropy)
      (VG.Impl.Dsa.X86.ProbablePrime.body E.bits montName mont roundName round) (VG.X86.Taint.Agree (τr [.esp])) := by
  intro s t tr ur u z P A B
  obtain raw : RelCT isa (EntryPair E c entropy)
      (VG.Impl.Dsa.X86.ProbablePrime.body E.bits montName mont roundName round) (fun _ _ => True) := by
    unfold VG.Impl.Dsa.X86.ProbablePrime.body
    exact RelCT.seq (enter_trace v) (RelCT.seq (load_trace v odd)
      (sieved_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v odd length))
  refine ⟨(raw _ _ _ _ _ _ P A B).1, agree_regs ?_⟩
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  rw [Exec.gpr (body_noSp montNoSp roundNoSp E.bits montName roundName) A,
    Exec.gpr (body_noSp montNoSp roundNoSp E.bits montName roundName) B]
  exact P.1.sp.trans P.2.sp.symm

def FramedPair (E : Environment) (c : Nat) (entropy : List Byte) (s t : State) : Prop :=
  EntryPair E c entropy (Compact.entered s) (Compact.entered t) ∧ s.gpr .esp = t.gpr .esp

theorem framed_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} (odd : c % 2 = 1)
    (length : Spec.Dsa.bitLength c = E.bits) :
    RelCT isa (FramedPair E c entropy)
      (VG.Impl.Dsa.X86.ProbablePrime.code E.bits montName mont roundName round) (fun _ _ => True) := by
  obtain restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.Mont.X86.Compact.restoreRegs)
      (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
  unfold VG.Impl.Dsa.X86.ProbablePrime.code
  apply VG.X86.RelCT.frame (rs := Compact.savedRegisters) (R := VG.X86.Taint.Agree (τr [.esp])) (fun _ _ P => P.2)
  exact (RelCT.seq (body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v odd length)
    restore).mono (by rintro _ _ ⟨s, t, P, rfl, rfl⟩; exact P.1) (fun _ _ P => P)

end VG.Proof.Dsa.X86.ProbablePrime

end

end


/-! # The test is constant time under the shared contract's leak -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86

structure PublicInputs (bits : Nat) (s t : State) : Prop where
  stack : s.gpr .esp = t.gpr .esp
  symbol : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = t.syms VG.Impl.RsaKeyGen.TrialTable32.symbol
  observations : Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem
      ((arg s 0).setWidth 64) :: (callEntropy s).map (·.toNat) =
    Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) t.mem
      ((arg t 0).setWidth 64) :: (callEntropy t).map (·.toNat)
  arg0 : arg s 0 = arg t 0
  arg1 : arg s 1 = arg t 1
  arg2 : arg s 2 = arg t 2
  arg3 : arg s 3 = arg t 3
  arg4 : arg s 4 = arg t 4

theorem public_inputs {bits : Nat} {s t : State} (H : (contract bits).pub s t) : PublicInputs bits s t := by
  sig_pub [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts] at H
  sig_split H
  constructor <;> first | with_reducible assumption | (dsimp only [callEntropy]; with_reducible assumption)

theorem PublicInputs.environment {bits : Nat} {s t : State} (P : PublicInputs bits s t) :
    callEnvironment bits s = callEnvironment bits t := by
  simp only [callEnvironment, P.arg0, P.arg1, P.arg2, P.arg3, P.arg4, P.stack, P.symbol]

theorem PublicInputs.candidate {bits : Nat} {s t : State} (P : PublicInputs bits s t) :
    (callEnvironment bits s).candidate s.mem = (callEnvironment bits t).candidate t.mem :=
  (List.cons.inj P.observations).1

theorem PublicInputs.entropy {bits : Nat} {s t : State} (P : PublicInputs bits s t) :
    callEntropy s = callEntropy t :=
  VG.Proof.RsaKeyGen.map_toNat_inj (List.cons.inj P.observations).2

theorem constantTime {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) {bits : Nat} (b : Bits bits) :
    ConstantTime isa (contract bits).pre (contract bits).pub
      (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round) := by
  apply RelCT.constantTime
  intro s t tr ur u z ⟨HS, HT, HP⟩ A B
  obtain P := public_inputs HP
  obtain F := call_facts HS
  obtain G := call_facts HT
  obtain I := F.entry b
  obtain J := G.entry b
  rw [← P.candidate, ← P.environment, ← P.entropy] at J
  exact framed_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack (F.valid b)
    F.odd F.length _ _ _ _ _ _ ⟨⟨I, J⟩, P.stack⟩ A B

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! ### `Dsa.X86.ProbablePrime.Satisfiable`, which only this module used -/

section

/-! # A state meets the precondition: an all-ones candidate and an empty tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Impl.Dsa.X86.ProbablePrime

def satArgument : Nat → BitVec 32
  | 0 => 0x10000
  | 1 => 2000
  | 2 => 0x5000
  | 3 => 0
  | _ => 0x2000

/-- The arguments at the stack pointer plus 4. -/
def satArguments : Mem := fun a =>
  (satArgument ((a - 0x20004#64).toNat / 4)).extractLsb' (8 * ((a - 0x20004#64).toNat % 4)) 8

def satBase (bits : Nat) : Addr := 0x10000#64 + BitVec.ofNat 64 (scratchBytes (width bits))

def satMemory (bits : Nat) : Mem := fun a =>
  if (a - 0x20004#64).toNat < 20 then satArguments a
  else if (a - satBase bits).toNat < bits / 8 then 0xFF#8
  else constMem 0x30000#64 VG.Impl.RsaKeyGen.TrialTable32.packed a

def satState (bits : Nat) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMemory bits
  rd := [⟨0x5000, 0⟩, ⟨0x30000, 8192⟩]
  wr := [⟨0x10000, 16000⟩, ⟨0x2000, 8⟩, ⟨0x20004, 20⟩]
  syms _ := 0x30000

theorem scratch_bound {bits : Nat} (b : Bits bits) : scratchBytes (width bits) + bits / 8 ≤ 16000 := by
  have := b.width_high
  have := b.high
  unfold scratchBytes VG.Impl.Bignum.X86.PublicContext.slot VG.Impl.Bignum.X86.PublicContext.stride
    VG.Impl.Bignum.hdrBytes
  omega_arith

theorem sat_argument_word (i : Nat) (index : i < 5) :
    satArguments.readW (BitVec.ofNat 64 (0x20004 + 4 * i)) 32 = satArgument i := by
  obtain cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega_using [index]
  rcases cases with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem sat_arguments (bits : Nat) (i : Nat) (index : i < 5) : arg (satState bits) i = satArgument i := by
  obtain address : argAddr (satState bits) i = BitVec.ofNat 64 (0x20004 + 4 * i) := by
    change ((0x20000#32 + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) = _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [index]
  unfold arg
  rw [address, ← sat_argument_word i index]
  apply Mem.readW_congr
  intro j hj
  change (if _ then _ else _) = _
  refine ite_eq_left ?_
  change ((BitVec.ofNat 64 (0x20004 + 4 * i) + BitVec.ofNat 64 j) - 0x20004#64).toNat < 20
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [index, hj]

theorem satBase_toNat {bits : Nat} (b : Bits bits) :
    (satBase bits).toNat = 0x10000 + scratchBytes (width bits) := by
  have := scratch_bound b
  unfold satBase
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [this]

theorem os2ip_ones : ∀ (n acc : Nat),
    (List.replicate n (0xFF#8)).foldl (fun x b => 256 * x + b.toNat) acc = acc * 256 ^ n + (256 ^ n - 1)
  | 0, acc => by simp
  | n + 1, acc => by
    rw [List.replicate_succ, List.foldl_cons, os2ip_ones n, Nat.pow_succ]
    have ff : (0xFF#8).toNat = 255 := rfl
    rw [ff]
    obtain pos : 0 < 256 ^ n := Nat.pow_pos (by decide)
    generalize 256 ^ n = p at *
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega_using [pos]⟩
    grind

theorem sat_candidate {bits : Nat} (b : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) ((satArgument 0).setWidth 64) =
      2 ^ bits - 1 := by
  obtain bound := scratch_bound b
  obtain baseNat := satBase_toNat b
  obtain bytes : Spec.Rsa.bytesAt (satMemory bits) ((satArgument 0).setWidth 64 +
      BitVec.ofNat 64 (layout bits).candidate) ((layout bits).bits / 8) = List.replicate (bits / 8) 0xFF#8 := by
    change Spec.Rsa.bytesAt (satMemory bits) (satBase bits) (bits / 8) = _
    unfold Spec.Rsa.bytesAt
    apply List.ext_getElem (by simp)
    intro i hi _
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [List.length_map, List.length_range] at hi
    unfold satMemory
    rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, baseNat]; omega_using [bound, hi]),
      ite_eq_left (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, baseNat]; omega_using [bound, hi])]
  unfold Proof.Dsa.ProbablePrime.candidateAt
  rw [bytes, VG.Proof.Dsa.decodeBE_os2ip]
  unfold Spec.Rsa.os2ip
  rw [os2ip_ones, Nat.zero_mul, Nat.zero_add]
  have whole := b.whole
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul, show 8 * (bits / 8) = bits by omega_using [whole]]

theorem sat_odd {bits : Nat} (b : Bits bits) :
    Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) ((satArgument 0).setWidth 64) % 2 = 1 := by
  rw [sat_candidate b]
  have : 2 ^ bits % 2 = 0 := by
    rw [show bits = (bits - 1) + 1 by have := b.low; omega_using [this], Nat.pow_succ]; omega_using []
  have := Nat.two_pow_pos bits
  omega_arith

theorem sat_length {bits : Nat} (b : Bits bits) :
    Spec.Dsa.bitLength
      (Proof.Dsa.ProbablePrime.candidateAt (layout bits) (satMemory bits) ((satArgument 0).setWidth 64)) = bits := by
  rw [sat_candidate b]
  have low := b.low
  obtain half : 2 ^ bits = 2 ^ (bits - 1) * 2 := by
    rw [← Nat.pow_succ]; congr 1; omega_using [low]
  obtain pos := Nat.two_pow_pos (bits - 1)
  have := VG.Proof.RsaKeyGen.bitLength_of (n := 2 ^ bits - 1) (b := bits - 1) (by omega_using [half])
    (by rw [show bits - 1 + 1 = bits by omega_using [low]]; omega_using [half, pos])
  rw [show bits - 1 + 1 = bits by omega_using [low]] at this
  exact this

private theorem single_held {m : Mem} {f : String → Addr} {name : String} {words : List (BitVec 64)}
    (H : ∀ i < words.length, m.readW (f name + BitVec.ofNat 64 (8 * i)) 64 = words.getD i 0) :
    Abi.constsHeld m f [(name, words)] := by
  intro c mem
  obtain rfl := List.mem_singleton.mp mem
  exact H

private theorem packed_regions (f : String → Addr) :
    Abi.constRegions f [(VG.Impl.RsaKeyGen.TrialTable32.symbol, VG.Impl.RsaKeyGen.TrialTable32.packed)] =
      [⟨f VG.Impl.RsaKeyGen.TrialTable32.symbol, 8192⟩] := by
  rw [Abi.constRegions_cons, Abi.constRegions_nil, packed_length]

theorem sat_table {bits : Nat} (b : Bits bits) :
    Abi.constsHeld (satState bits).mem (fun name => ((satState bits).syms name).setWidth 64)
      VG.Impl.RsaKeyGen.TrialTable32.consts := by
  apply single_held
  intro i index
  obtain bound := scratch_bound b
  obtain baseNat := satBase_toNat b
  obtain fit : 8 * VG.Impl.RsaKeyGen.TrialTable32.packed.length ≤ 2 ^ 64 := by rw [packed_length]; decide
  obtain small : i < 1024 := by simpa only [packed_length] using index
  change (satMemory bits).readW (0x30000#64 + BitVec.ofNat 64 (8 * i)) 64 =
    VG.Impl.RsaKeyGen.TrialTable32.packed.getD i 0
  obtain held := constMem_held 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed fit i index
  refine Eq.trans (Mem.readW_congr (m := satMemory bits)
    (m' := constMem 0x30000 VG.Impl.RsaKeyGen.TrialTable32.packed) ?_) held
  intro j hj
  change (if _ then _ else _) = _
  rw [ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [small, hj]),
    ite_eq_right (by simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, baseNat]; omega_using [bound, small, hj])]
  rfl

theorem sat_argAddr (bits : Nat) : argAddr (satState bits) 0 = 0x20004#64 := by
  change ((0x20000#32 + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64) = _
  decide

theorem satisfiable {bits : Nat} (b : Bits bits) : ∃ s, (contract bits).pre s := by
  refine ⟨satState bits, ?_⟩
  sig_pre [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi,
    argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts, stackBelow]
  simp only [sat_arguments bits 0 (by decide), sat_arguments bits 1 (by decide), sat_arguments bits 2 (by decide),
    sat_arguments bits 3 (by decide), sat_arguments bits 4 (by decide), sat_argAddr]
  simp only [packed_regions, List.forall_mem_singleton]
  sig_and_intros
  all_goals first
    | exact sat_table b
    | exact sat_odd b
    | exact sat_length b
    | (have := scratch_bound b; change _ ≤ 8 * 2000; omega_using [this])
    | rfl
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! ### `Dsa.X86.ProbablePrime.Framed`, which only this module used -/

section

/-! # The four saved registers and the return address survive the test -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ProbablePrime/Body.lean`, which only this module imported.
section

/-! # Trial division, then the blinded loop -/

section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86
open VG.Impl.Dsa.X86.ProbablePrime

theorem used_tail {E : Environment} (v : E.Valid) {m m' : Mem} (F : Frame [E.usedRegion] m m') :
    Tail E m m' := by
  intro i _ hi
  apply F
  intro r mem
  obtain rfl := List.mem_singleton.mp mem
  intro contains
  have fit := v.workspaceFit
  exact v.usedWorkspace _ contains (Offset.contains_base E.base (by omega) (by omega))

theorem sieved_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (L : Loaded E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) :
    WP isa (sieved E.bits montName mont roundName round) s fun t =>
      Outputs E (Spec.Dsa.probablePrime c entropy) t ∧ MutableFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps WitnessStep.clob s t := by
  obtain shape := candidate_shape odd length (by have := v.bits.low; omega)
  obtain big : 2 ^ 63 ≤ 2 ^ (E.bits - 1) := Nat.pow_le_pow_right (by decide) (by have := v.bits.low; omega)
  unfold sieved
  refine WP.seq (WP.mono (sieve_ok v L (by omega)) fun a ⟨La, flag, Wa, Ta, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Candidate.cmp_bool flag) fun b ⟨B, _, cond⟩ => ?_)
  obtain ⟨Lb, Wb, Tb⟩ := La.keepStack v (by rw [B.mem]; exact Frame.refl _ _) (B.keeps []) (by decide) (by decide)
    (by rw [B.syms])
  obtain Kb : Keeps WitnessStep.clob s b := (Ka.mono (by unfold WitnessStep.clob; decide)).widen (B.keeps [])
  obtain Mb : MutableFrame E s.mem b.mem := (Wa.trans Wb).mutable
  obtain Tsb : Tail E s.mem b.mem := Ta.trans Tb
  obtain same : Spec.RsaKeyGen.obviouslyComposite (64 * E.width) c = Spec.RsaKeyGen.obviouslyComposite E.bits c :=
    obviouslyComposite_eq v.bits c
  rw [same] at cond
  cases composite : Spec.RsaKeyGen.obviouslyComposite E.bits c
  · refine WP.ite false (by rw [cond, composite]) (fun bad => nomatch bad) (fun _ => ?_)
    refine WP.mono (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Lb odd length)
      fun t ⟨out, Mt, Tt, Kt⟩ => ?_
    rw [← probablePrime_eq v entropy odd length composite] at out
    exact ⟨out, Mb.trans Mt, Tsb.trans Tt, Kb.trans Kt⟩
  · refine WP.ite true (by rw [cond, composite]) (fun _ => ?_) (fun bad => nomatch bad)
    obtain result : Spec.Dsa.probablePrime c entropy = some (false, entropy) := by
      obtain three : (c == 3) = false := by rw [beq_eq_false_iff_ne]; omega
      unfold Spec.Dsa.probablePrime
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by rw [three]; decide), length,
        composite]
      rfl
    refine WP.mono (CandidateFinish.used_ok (status := 2) Lb.input.scratch (by have := v.header; omega)
      Lb.input.memory.usedWrite Lb.input.usedPtr rfl) fun t ⟨eax, mem, O, Kt⟩ => ?_
    obtain F := used_frame O
    refine ⟨⟨?_, ?_⟩, Mb.trans (MutableFrame.of_used F), Tsb.trans (used_tail v F),
      Kb.trans (Kt.mono (by decide))⟩
    · rw [eax, result]; rfl
    · rw [mem]
      refine used_outputs (fun _ rest same => ?_)
      rw [result] at same
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      rw [L.input.memory.entropyLength, Nat.sub_self]
      change w32 b.mem E.base 152 = 0
      exact Lb.count

def bodyClob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem body_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : EntryInput E c entropy s) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits) :
    WP isa (body E.bits montName mont roundName round) s fun t =>
      Outputs E (Spec.Dsa.probablePrime c entropy) t ∧ MutableFrame E s.mem t.mem ∧ Tail E s.mem t.mem ∧
      Keeps bodyClob s t := by
  unfold body
  refine WP.seq (WP.mono (enter_ok v I) fun a ⟨Ia, count, O, Ka⟩ => ?_)
  obtain Wa := v.work_of_outside O (by have := v.header; omega)
  obtain Ta := v.tail_of_outside O (by have := v.scratchLow; omega)
  refine WP.seq (WP.mono (load_ok v Ia count odd) fun b ⟨Lb, Wb, Tb, Kb⟩ => ?_)
  refine WP.mono (sieved_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Lb odd length)
    fun t ⟨out, Mt, Tt, Kt⟩ => ?_
  exact ⟨out, (Wa.trans Wb).mutable.trans Mt, (Ta.trans Tb).trans Tt,
    ((Ka.mono (by unfold bodyClob; decide)).trans (Kb.mono (by unfold bodyClob; decide))).trans
      (Kt.mono (by unfold WitnessStep.clob bodyClob; decide))⟩

end VG.Proof.Dsa.X86.ProbablePrime
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Mont.X86

theorem saved_stack_far {E : Environment} (v : E.Valid) :
    (⟨E.p.setWidth 64, 16⟩ : Region).Disjoint (below E.p 136) := by
  unfold below
  rw [Taint.sub_setWidth v.low]
  exact Offset.base_disjoint_below _ (by decide)

theorem pFit {E : Environment} {s : State} (fit : 16 ≤ (s.gpr .esp).toNat)
    (sp : (Compact.entered s).gpr .esp = E.p) : E.p.toNat + 16 ≤ 2 ^ 32 := by
  rw [← sp, Compact.entered, pushed_esp]
  change (s.gpr .esp - 16#32).toNat + 16 ≤ 2 ^ 32
  rw [sub_toNat fit]
  have := (s.gpr .esp).isLt
  omega

theorem saved_read {E : Environment} (v : E.Valid) {s t : State}
    (fit : 16 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (F : MutableFrame E (Compact.entered s).mem t.mem) {i : Nat} (index : i < 4) :
    t.mem.readW (addr E.p (4 * i)) 32 = s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega)) := by
  obtain fitP := pFit fit sp
  obtain same := F.readW (r := (⟨E.p.setWidth 64, 16⟩ : Region)) (a := addr E.p (4 * i)) (w := 32)
    (by rw [addr_eq (by omega)]; exact Offset.contains_base _ (by omega) (by omega)) (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact (v.savedFar _ List.mem_cons_self).symm
      · exact saved_stack_far v
      · exact (v.savedFar _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).symm)
    (by decide)
  obtain word := pushed_word (rs := Compact.savedRegisters) (by decide) fit index
  change (Compact.entered s).mem.readW (addr ((Compact.entered s).gpr .esp) (4 * i)) 32 = _ at word
  rw [sp] at word
  exact same.trans word

theorem return_read {E : Environment} (_ : E.Valid) {s t : State}
    (fit : 152 ≤ (s.gpr .esp).toNat) (sp : (Compact.entered s).gpr .esp = E.p)
    (returnFar : ∀ r ∈ [E.workspaceRegion, E.usedRegion], (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r)
    (F : MutableFrame E (Compact.entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  obtain outside : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (below (s.gpr .esp) 152) := by
    unfold below
    rw [Taint.sub_setWidth fit]
    exact Offset.base_disjoint_below _ (by decide)
  obtain inner : (below E.p 136).Sub (below (s.gpr .esp) 152) := by
    rw [← sp, Compact.entered, pushed_esp]
    exact below_inner (by decide) fit
  obtain same := F.readW (w := 32) (Region.contains_self ((s.gpr .esp).setWidth 64) 4) (by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact returnFar _ List.mem_cons_self
    · exact outside.sub_right inner
    · exact returnFar _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by decide)
  obtain pushed := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) (by change 16 ≤ _; omega)
  exact same.trans (pushed.readW (Region.contains_self _ _) (by
    intro r mem; obtain rfl := List.mem_singleton.mp mem
    exact outside.sub_right (below_sub (by decide) fit)) (by decide))

theorem Outputs.keep {E : Environment} {res : Option (Bool × Spec.RsaKeyGen.Rand)} {s t : State}
    (R : Outputs E res s) (eax : t.gpr .eax = s.gpr .eax) (mem : t.mem = s.mem) : Outputs E res t := by
  unfold Outputs at *
  rw [eax, mem]
  exact R

theorem framed_ok {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {c : Nat} {entropy : List Byte} {s : State}
    (I : EntryInput E c entropy (Compact.entered s)) (odd : c % 2 = 1) (length : Spec.Dsa.bitLength c = E.bits)
    (fit : 152 ≤ (s.gpr .esp).toNat)
    (returnFar : ∀ r ∈ [E.workspaceRegion, E.usedRegion], (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r) :
    WP isa (VG.Impl.Dsa.X86.ProbablePrime.code E.bits montName mont roundName round) s fun t =>
      abiPreserved s t ∧ Outputs E (Spec.Dsa.probablePrime c entropy) t ∧ Tail E s.mem t.mem := by
  obtain savedFit : 16 ≤ (s.gpr .esp).toNat := by omega
  have entrySp := I.sp
  obtain inner : NoSp (.seq (VG.Impl.Dsa.X86.ProbablePrime.body E.bits montName mont roundName round)
      (.block Compact.restoreRegs)) :=
    VG.Proof.RsaKeyGen.X86.CandidateNoSp.sequence (body_noSp montNoSp roundNoSp E.bits montName roundName)
      (NoSp.of_all (by rfl))
  obtain pushedTail : Tail E s.mem (Compact.entered s).mem := by
    obtain F := pushed_frame (rs := Compact.savedRegisters) (s := s) (by decide) savedFit
    intro i _ hi
    apply F
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    obtain region : below (s.gpr .esp) (4 * Compact.savedRegisters.length) = ⟨E.p.setWidth 64, 16⟩ := by
      rw [← entrySp, Compact.entered, pushed_esp]
      rfl
    rw [region]
    intro contains
    have fitW := v.workspaceFit
    exact v.savedFar _ List.mem_cons_self _ (Offset.contains_base E.base (by omega) (by omega)) contains
  unfold VG.Impl.Dsa.X86.ProbablePrime.code
  refine WP.frame (rs := Compact.savedRegisters) (by decide) (by decide) (by decide) savedFit inner ?_
  refine WP.seq (WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v I odd length)
    fun t ⟨R, F, T, K⟩ => ?_)
  obtain sp : t.gpr .esp = E.p := (K.1 .esp (by unfold bodyClob; decide)).trans entrySp
  obtain fitP := pFit savedFit entrySp
  have read (i : Nat) (index : i < 4) : readSrc t (.mem (at_ .esp (4 * i))) = some
      (s.gpr (Compact.savedRegisters[3 - i]'(by change 3 - i < 4; omega))) := by
    obtain access : InRegions (t.rd ++ t.wr) (addr (t.gpr .esp) (4 * i)) 4 := by
      rw [K.2.1, K.2.2, sp]
      change InRegions (s.rd ++ (below (s.gpr .esp) 16 :: s.wr)) (addr E.p (4 * i)) 4
      refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ List.mem_cons_self, ?_⟩
      obtain region : below (s.gpr .esp) 16 = ⟨E.p.setWidth 64, 16⟩ := by
        rw [← entrySp, Compact.entered, pushed_esp]
        rfl
      rw [region, addr_eq (by omega)]
      exact Offset.contains_base _ (by omega) (by omega)
    change t.load32 (addr (t.gpr .esp) (4 * i)) = _
    rw [State.load32, ite_eq_left access, sp, saved_read v savedFit entrySp F index]
  refine WP.mono (Compact.restore_ok (read 0 (by decide)) (read 1 (by decide)) (read 2 (by decide))) ?_
  rintro u ⟨edi, esi, ebp, mem, keep⟩
  obtain sp' : u.gpr .esp = E.p := (keep.1 .esp (by decide)).trans sp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show Compact.savedRegisters.length = 4 from rfl, Compact.popped_four_value, sp', mem]
      exact saved_read v savedFit entrySp F (by decide : 3 < 4)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact esi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact edi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact ebp
    · rw [popped_esp, sp', ← entrySp, Compact.entered, pushed_esp]
      exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]
    exact return_read v fit entrySp returnFar F
  · apply R.keep
    · rw [popped_gpr _ _ _ (by decide) (by decide)]
      exact keep.1 .eax (by decide)
    · rw [popped_mem, mem]
  · rw [popped_mem, mem]
    exact pushedTail.trans T

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! # DSA's probable-prime test on i686 is verified -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/ProbablePrime/Correct.lean`, which only this module imported.
section

/-! # The probable-prime test meets the shared contract's postcondition -/

section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem correct {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) {bits : Nat} (b : Bits bits)
    (s : State) (h : (contract bits).pre s) :
    ∃ trace t, Exec isa (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round) s trace t ∧
      abiPreserved s t ∧ (contract bits).post s t := by
  obtain F := call_facts h
  obtain v := F.valid b
  obtain ⟨trace, t, run, preserved, R, T⟩ := framed_ok montVerified montNoSp montStack roundVerified roundNoSp
    roundStack v (F.entry b) F.odd F.length F.low (by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [F.workspaceRegion]; exact F.retWs
      · exact F.retUsed)
  refine ⟨trace, t, run, preserved, ?_⟩
  sig_post [contract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig,
    abi, argSlots, argVal, argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
  rw [BitVec.setWidth_append_eq_right]
  obtain ⟨status, used⟩ := R
  refine ⟨status, ?_, fun b rest same => used b rest same⟩
  intro i index outside
  obtain far := outside _ List.mem_cons_self
  change i < 0 ∨ 0 + (callEnvironment bits s).scratch ≤ i at far
  exact T i (by omega) index

end VG.Proof.Dsa.X86.ProbablePrime
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86

theorem verified {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96) (bits : Nat)
    (low : 64 ≤ bits := by decide) (high : bits ≤ 4096 := by decide) (whole : bits % 32 = 0 := by decide) :
    Verified target (VG.Impl.Dsa.X86.ProbablePrime.code bits montName mont roundName round) (contract bits) :=
  ⟨correct montVerified montNoSp montStack roundVerified roundNoSp roundStack ⟨low, high, whole⟩,
    constantTime montVerified montNoSp montStack roundVerified roundNoSp roundStack ⟨low, high, whole⟩,
    satisfiable ⟨low, high, whole⟩⟩

end VG.Proof.Dsa.X86.ProbablePrime

end

end

/-! ### `Dsa.X86.ProbablePrime.StackUse`, which only this module used -/

section

/-! # The probable-prime test uses at most 152 bytes below its caller -/

@[expose] public section
namespace VG.Proof.Dsa.X86.ProbablePrime
open VG VG.X86 VG.Impl.Dsa.X86.ProbablePrime

theorem test_stack {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (bits : Nat) (montName roundName : String) : stackUse (test bits montName mont roundName round) ≤ 136 := by
  obtain bound := VG.Proof.RsaKeyGen.X86.CandidateStackUse.testWith Hm Hr (bits - 1) (Spec.Dsa.primeChecks bits)
    (8 * ((bits + 63) / 64)) (bits / 32) (width bits) montName roundName
  change max (stackUse (VG.Impl.RsaKeyGen.X86.CandidateTest.codeWith (bits - 1) (Spec.Dsa.primeChecks bits)
    (8 * ((bits + 63) / 64)) (bits / 32) (width bits) montName mont roundName round)) (stackUse finish) ≤ 136
  have : stackUse finish = 0 := rfl
  omega_using [bound, this]

theorem sieved_stack {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (bits : Nat) (montName roundName : String) : stackUse (sieved bits montName mont roundName round) ≤ 136 := by
  obtain bound := test_stack Hm Hr bits montName roundName
  have sieve : stackUse (VG.Impl.RsaKeyGen.X86.CandidateSieve.code (width bits)) = 24 := rfl
  have used : stackUse (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 2) = 0 := rfl
  change max (stackUse (VG.Impl.RsaKeyGen.X86.CandidateSieve.code (width bits)))
    (max 0 (max (stackUse (VG.Impl.RsaKeyGen.X86.CandidateFinish.used 2))
      (stackUse (test bits montName mont roundName round)))) ≤ 136
  omega_using [bound, sieve, used]

theorem body_stack {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (bits : Nat) (montName roundName : String) : stackUse (body bits montName mont roundName round) ≤ 136 := by
  obtain bound := sieved_stack Hm Hr bits montName roundName
  have loaded : stackUse (load (bits / 32) (width bits)) = 0 := rfl
  change max 0 (max (stackUse (load (bits / 32) (width bits))) (stackUse (sieved bits montName mont roundName round))) ≤ 136
  omega_using [bound, loaded]

theorem code_stack {mont round : Prog isa} (Hm : stackUse mont ≤ 56) (Hr : stackUse round ≤ 96)
    (bits : Nat) (montName roundName : String) : stackUse (code bits montName mont roundName round) ≤ 152 := by
  obtain bound := body_stack Hm Hr bits montName roundName
  change max (stackUse (body bits montName mont roundName round)) 0 + 16 ≤ 152
  omega_using [bound]

end VG.Proof.Dsa.X86.ProbablePrime

end

end


/-! # The three geometries, for every SHA-1, SHA-256 and Miller–Rabin backend -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Dsa.X86.Generation

/-- The geometry of `(pLen, qLen)`, hashing with `H` from `iv` and testing
with the probable-prime functions of the Miller–Rabin backend `v`. -/
def geo (pLen qLen : Nat) (H : Impl.Pbkdf2.Md.X86.Hash) (iv : List (BitVec 32)) (v : RoundImpl) : Geo where
  pLen := pLen
  qLen := qLen
  e := (8 * pLen - 8 * qLen) / 32 + 1
  H := H
  iv := iv
  qName := s!"vg_dsa_probable_prime_{(Impl.Dsa.X86.ProbablePrime.layout (8 * qLen)).bits}" ++ v.suffix
  qCode := Impl.Dsa.X86.ProbablePrime.code (8 * qLen) montName montCode v.name v.code
  pName := s!"vg_dsa_probable_prime_{(Impl.Dsa.X86.ProbablePrime.layout (8 * pLen)).bits}" ++ v.suffix
  pCode := Impl.Dsa.X86.ProbablePrime.code (8 * pLen) montName montCode v.name v.code
  checkName := "vg_dsa_check_parameters"
  checkCode := Impl.Dsa.X86.Generate.checkParameters

theorem check_noSp : NoSp Impl.Dsa.X86.Generate.checkParameters := NoSp.of_all (by decide +kernel)

theorem check_stack : stackUse Impl.Dsa.X86.Generate.checkParameters ≤ 108 := by decide +kernel

/-- The geometry `(pLen, qLen)` is one the proofs support. -/
def geoOk {pLen qLen : Nat} {H : Impl.Pbkdf2.Md.X86.Hash} {iv : List (BitVec 32)} (v : RoundImpl)
    (hash : HashOk H iv) (lengths : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32))
    (N : H.N = qLen) (seedHash : ∀ m, hash.ok.hH.SH.H.hash m = Spec.Dsa.seedHash (8 * qLen) m)
    (qWide : 64 ≤ 8 * qLen := by decide) (qNarrow : 8 * qLen ≤ 4096 := by decide)
    (qWhole : 8 * qLen % 32 = 0 := by decide)
    (pWide : 64 ≤ 8 * pLen := by decide) (pNarrow : 8 * pLen ≤ 4096 := by decide)
    (pWhole : 8 * pLen % 32 = 0 := by decide)
    (prepCt : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (scr .ebx sState ++ ivStore iv ++
        Impl.Pbkdf2.Md.X86.storeW .ebx (H.N + qLen) (padBytes qLen) ((64 - qLen) / 4) ++
        [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 H.N))] ++ scr .ebp sHScr)) fun _ _ => True)
    (outCt : ∀ dst, RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (scr .ebx sState ++ scr .eax dst ++ H.out)) fun _ _ => True)
    (outNoSp : ∀ i ∈ H.out, Taint.clobbers i .esp = false) :
    GeoOk (geo pLen qLen H iv v) where
  lengths := lengths
  hash := hash
  N := N
  seedHash := seedHash
  e := rfl
  qv := ProbablePrime.verified VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack v.verified v.noSp
    v.stack (8 * qLen) qWide qNarrow qWhole
  qNoSp := ProbablePrime.code_noSp compact_noSp v.noSp _ _ _
  qStack := ProbablePrime.code_stack compact_stack v.stack _ _ _
  pv := ProbablePrime.verified VG.Proof.Mont.X86.Sse2.prepared_verified compact_noSp compact_stack v.verified v.noSp
    v.stack (8 * pLen) pWide pNarrow pWhole
  pNoSp := ProbablePrime.code_noSp compact_noSp v.noSp _ _ _
  pStack := ProbablePrime.code_stack compact_stack v.stack _ _ _
  cv := Proof.Dsa.X86.checking_verified
  cNoSp := check_noSp
  cStack := check_stack
  prepCt := prepCt
  outCt := outCt
  outNoSp := outNoSp

/-- 1024/160, with SHA-1. -/
abbrev geo1 (v1 : Proof.Sha1.X86.Variants.Backend) (v : RoundImpl) : Geo :=
  geo 128 20 (Proof.Pbkdf2.Md.X86.sha1M v1.stream v1.cmpN v1.cmpC) Spec.Sha1.H0.toList v

/-- 2048/256 or 3072/256, with SHA-256. -/
abbrev geo256 (pLen : Nat) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) : Geo :=
  geo pLen 32 (Proof.Pbkdf2.Md.X86.sha256M v256.stream v256.cmpN v256.cmpC) Spec.Sha256.H0.toList v

theorem sha1_prepCt : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ ivStore Spec.Sha1.H0.toList ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (20 + 20) (padBytes 20) ((64 - 20) / 4) ++
      ([.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 20))] : List Instr) ++ scr .ebp sHScr)) fun _ _ => True :=
  (erased_relCT _ _ (.block []) rfl rfl rfl (σ := τr []) (by decide +kernel)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem sha256_prepCt : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ ivStore Spec.Sha256.H0.toList ++
      Impl.Pbkdf2.Md.X86.storeW .ebx (32 + 32) (padBytes 32) ((64 - 32) / 4) ++
      ([.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 32))] : List Instr) ++ scr .ebp sHScr)) fun _ _ => True :=
  (erased_relCT _ _ (.block []) rfl rfl rfl (σ := τr []) (by decide +kernel)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem sha1_outCt (dst : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ scr .eax dst ++ Impl.Sha1.X86.Stream.params.out)) fun _ _ => True :=
  (erased_relCT (.block (scr .ebx sState ++ scr .eax dst ++ Impl.Sha1.X86.Stream.params.out))
    (.block (scr .ebx sState ++ scr .eax 0 ++ Impl.Sha1.X86.Stream.params.out)) (.block []) rfl rfl rfl
    (τ := τr [.esp, .edi]) (σ := τr []) (by decide +kernel)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem sha256_outCt (dst : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
    (.block (scr .ebx sState ++ scr .eax dst ++ Impl.Sha256.X86.Stream.params.out)) fun _ _ => True :=
  (erased_relCT (.block (scr .ebx sState ++ scr .eax dst ++ Impl.Sha256.X86.Stream.params.out))
    (.block (scr .ebx sState ++ scr .eax 0 ++ Impl.Sha256.X86.Stream.params.out)) (.block []) rfl rfl
    rfl (τ := τr [.esp, .edi]) (σ := τr []) (by decide +kernel)).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem sha1_outNoSp : ∀ i ∈ Impl.Sha1.X86.Stream.params.out, Taint.clobbers i .esp = false := by decide

theorem sha256_outNoSp : ∀ i ∈ Impl.Sha256.X86.Stream.params.out, Taint.clobbers i .esp = false := by decide

def geo1Ok (v1 : Proof.Sha1.X86.Variants.Backend) (v : RoundImpl) : GeoOk (geo1 v1 v) :=
  geoOk v (sha1_hashOk v1) (.inl ⟨rfl, rfl⟩) rfl (fun _ => rfl) (prepCt := sha1_prepCt) (outCt := sha1_outCt)
    (outNoSp := sha1_outNoSp)

def geo2Ok (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) : GeoOk (geo256 256 v256 v) :=
  geoOk v (sha256_hashOk v256) (.inr (.inl ⟨rfl, rfl⟩)) rfl (fun _ => rfl) (prepCt := sha256_prepCt)
    (outCt := sha256_outCt) (outNoSp := sha256_outNoSp)

def geo3Ok (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) : GeoOk (geo256 384 v256 v) :=
  geoOk v (sha256_hashOk v256) (.inr (.inr ⟨rfl, rfl⟩)) rfl (fun _ => rfl) (prepCt := sha256_prepCt)
    (outCt := sha256_outCt) (outNoSp := sha256_outNoSp)

end VG.Proof.Dsa.X86.Generation
