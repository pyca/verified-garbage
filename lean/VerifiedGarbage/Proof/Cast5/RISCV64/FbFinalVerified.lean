module

public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
public import VerifiedGarbage.Impl.Cast5.RISCV64.FbFinal
public import VerifiedGarbage.Spec.Cast5.CfbFinal
import VerifiedGarbage.Proof.Cast5.Table
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit
meta import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
meta import VerifiedGarbage.Proof.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Modes.RISCV64.SeqFinal
meta import VerifiedGarbage.Impl.Cast5.RISCV64.FbFinal
meta import VerifiedGarbage.Spec.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Cast5.Table
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit

/-!
# CAST5-CFB64 of a message's last piece on RISC-V meets its contracts

`modeFn` (`ModesVerified.lean`) of the modes' CFB over a message's last
piece (`Proof.Modes.RISCV64.cfbEncFinal_wp`, `cfbDecFinal_wp`) over CAST5's
encryption core (`Mode.dirCoreSpec`) meets the contracts with the count of
rounds (`Proof.Cast5.cfbEncryptFinalRoundsContract`, …) with `stack := 128`,
the whole-block functions' frame, under the calling convention with the
table, as the whole-block functions do: the proof's contract (`finalPC`) is
`finalP` for the state without the table's region, whose precondition, with
the data `len` bytes, is `seq`'s for the data a byte at a time (`byteMode`).
Constant time as the whole-block functions.
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64.Modes

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Cast5.RISCV64 VG.Impl.Modes
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Modes.RISCV64 (SeqPre byteMode)
open VG.Proof.Cast5.RISCV64.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Cast5.RISCV64 (modePub modes_agree s1234_len ecbSatMem ecbSatMem_held ecbConsts_eq)

/-- A final function on RISC-V, with its frame below the stack pointer, the
data `len` bytes, and the postcondition `post`. -/
def finalP (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, 128⟩
    let iv : Region := ⟨s.gpr .a2, 8⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - frameBytes, frameBytes⟩
    s.rd = [key] ∧ s.wr = [iv, data] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ iv.Disjoint data ∧
      (s.gpr .a0).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      s.sp.toNat % 16 = 0 ∧ frameBytes ≤ s.sp.toNat ∧ stack.Disjoint key ∧ stack.Disjoint iv ∧
      stack.Disjoint data ∧ ((s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 16)
  post := post
  pub := argPub

/-- `finalP`, with the table. -/
def finalPC (post : State → State → Prop) : Contract isa where
  pre s := (finalP post).pre (stripConsts ecbConsts s) ∧ ConstsOk ecbConsts frameBytes s
  post := post
  pub := modePub

/-- The final functions' postconditions. -/
def encFinalPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (Spec.Cast5.cipher (keyOf s) (rounds s)) 8 s.mem s'.mem (s.gpr .a2) (s.gpr .a3)
    (s.gpr .a4).toNat
def decFinalPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (Spec.Cast5.cipher (keyOf s) (rounds s)) 8 s.mem s'.mem (s.gpr .a2) (s.gpr .a3)
    (s.gpr .a4).toNat

section
variable {post : State → State → Prop} {s s₁ : State} (hs : (finalPC post).pre s) (h₁ : Shifted s s₁)
include hs

theorem roundsF_of : rounds s = 12 ∨ rounds s = 16 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hn⟩, -⟩ := hs
  exact hn

include h₁

theorem seqPreF_of (up : Bool) {n : Nat} : SeqPre (dirCore up n) byteMode s₁ := by
  obtain ⟨⟨-, hwr, -, -, dVD, -, fV, fD, al, sp, -, dSV, dSD, -⟩, -⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at hwr dVD fV fD al sp dSV dSD
  have eS : Proof.Modes.RISCV64.scrRegion (dirCore up n) (Proof.Modes.RISCV64.Fb s₁ (dirCore up n)) =
      ⟨s.sp - frameBytes, frameBytes⟩ := by
    simp only [Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Fb, h₁.sp]; rfl
  have eV : Proof.Modes.RISCV64.ivR s₁ (dirCore up n) = ⟨s.gpr .a2, 8⟩ := by
    simp only [Proof.Modes.RISCV64.ivR, Proof.Modes.RISCV64.P, h₁.a1]; rfl
  have eD : Proof.Modes.RISCV64.dataRegion (Proof.Modes.RISCV64.Dp s₁) byteMode.step (Proof.Modes.RISCV64.N s₁) =
      ⟨s.gpr .a3, (s.gpr .a4).toNat⟩ := by
    simp only [Proof.Modes.RISCV64.dataRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3,
      byteMode, Nat.one_mul]
  have hwr₁ : s₁.wr = [⟨s.gpr .a2, 8⟩, ⟨s.gpr .a3, (s.gpr .a4).toNat⟩] := by rw [h₁.wr, hwr]
  refine ⟨by rw [h₁.sp]; exact al, by rw [h₁.sp]; exact sp, by rw [eV, hwr₁]; simp,
    fun _ => by rw [eV, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.P, h₁.a1]; exact fV, by rw [eD, hwr₁]; simp,
    by simp only [Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, h₁.a2, h₁.a3, byteMode, Nat.one_mul]; exact fD,
    by rw [eD, eS]; exact dSD.symm, by rw [eV, eS]; exact dSV.symm, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by decide, show 1 ≤ 8 by decide⟩, layout up n⟩

theorem keyArgsF_of (up : Bool) {n : Nat} :
    KeyArgs s₁ (Proof.Modes.RISCV64.wrs0 (dirCore up n) byteMode s₁) (keyOf s) := by
  obtain ⟨⟨hrd, hwr, -, dKD, -, fK, -, -, -, -, dSK, -, -, -⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stripConsts_sp] at hrd hwr dKD fK dSK
  have trd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  have tst : Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ ⟨s.sp - frameBytes, frameBytes⟩ := by
    have := (hk.2.2.1 _ List.mem_cons_self).2.2 ⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩ (by
      simp [abi, stackBelow])
    simp only [s1234_len] at this; exact this
  have ews : Proof.Modes.RISCV64.wrs0 (dirCore up n) byteMode s₁ =
      [⟨s.gpr .a3, (s.gpr .a4).toNat⟩, ⟨s.sp - frameBytes, frameBytes⟩] := by
    simp only [Proof.Modes.RISCV64.wrs0, Proof.Modes.RISCV64.wrs, Proof.Modes.RISCV64.dataRegion,
      Proof.Modes.RISCV64.scrRegion, Proof.Modes.RISCV64.Dp, Proof.Modes.RISCV64.N, Proof.Modes.RISCV64.Fb,
      h₁.a2, h₁.a3, h₁.sp, byteMode, Nat.one_mul]
    rfl
  refine ⟨by rw [h₁.mem, h₁.a0], ?_, by rw [h₁.a0]; exact fK, fun r hr => ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₁.rd, h₁.wr, Mode.keyR, h₁.a0]
    exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  · rw [ews] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Mode.keyR, h₁.a0]; exact dKD
    · rw [Mode.keyR, h₁.a0]; exact dSK.symm
  · rw [h₁.rd, h₁.wr, Mode.tblR, h₁.syms]; exact List.mem_append_left _ trd
  · rw [h₁.syms]; exact ConstsOk.aligned hk List.mem_cons_self
  · rw [h₁.mem, h₁.syms]; exact ConstsOk.held1 hk
  · rw [ews] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Mode.tblR, h₁.syms]; exact twr _ (by rw [hwr]; simp)
    · rw [Mode.tblR, h₁.syms]; exact tst

end

/-- The final functions' arguments from the modes' proof, in the functions'
terms. -/
theorem argsF_eq {s s₁ : State} (h₁ : Shifted s s₁) :
    Proof.Modes.RISCV64.P s₁ = s.gpr .a2 ∧ Proof.Modes.RISCV64.Dp s₁ = s.gpr .a3 ∧
      Proof.Modes.RISCV64.N s₁ = (s.gpr .a4).toNat :=
  ⟨h₁.a1, h₁.a2, by simp only [Proof.Modes.RISCV64.N, h₁.a3]⟩

theorem cfbEncryptFinal_correct (s : State) (hs : (finalPC encFinalPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ encFinalPost s s' := by
  refine modeFn_wp (roundsF_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbEncFinal_wp
    (dirCoreSpec true _ (roundsF_of hs)) (seqPreF_of hs h₁ true) (keyArgsF_of hs h₁ true))
    fun s' ⟨h1, h2, _⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsF_eq h₁
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, ↓reduceIte] at h2
  rw [e1, e2, e3, h₁.mem] at h2
  exact h2

theorem cfbDecryptFinal_correct (s : State) (hs : (finalPC decFinalPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ decFinalPost s s' := by
  refine modeFn_wp (roundsF_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.RISCV64.cfbDecFinal_wp
    (dirCoreSpec true _ (roundsF_of hs)) (seqPreF_of hs h₁ true) (keyArgsF_of hs h₁ true))
    fun s' ⟨h1, h2, _⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsF_eq h₁
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, ↓reduceIte] at h2
  rw [e1, e2, e3, h₁.mem] at h2
  exact h2

/-! ## Constant time -/

theorem cfbEncryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem cfbDecryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

/-! ## The contracts -/

section
variable {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)} {post' : sig.Post abi.ptrBits}
  {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))} {post : State → State → Prop}

/-- A final function's contract with the table, from `finalP`'s implying it
without. -/
theorem final_implies_consts (h : (finalP post).Implies (sig.contract abi pre post' true frameBytes leak))
    (hpost : ∀ s s', post s s' → post (stripConsts ecbConsts s) s')
    (hsat : ∃ s, (sig.contract (abi.withConsts ecbConsts) pre post' true frameBytes leak).pre s) :
    (finalPC post).Implies (sig.contract (abi.withConsts ecbConsts) pre post' true frameBytes leak) where
  pre s hs := ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := post_consts.mpr (post_stripConsts.mp (h.post (stripConsts ecbConsts s) s'
    (pre_consts.mp hs).1 (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := by
    have a := h.pub (stripConsts ecbConsts s₁) (stripConsts ecbConsts s₂) (pre_consts.mp h₁).1
      (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)
    obtain ⟨hsp, e0, e1, e2, e3, e4⟩ := a
    exact ⟨hsp, by simp only [stripConsts_gpr] at e0 e1 e2 e3 e4; simp [e0, e1, e2, e3, e4],
      (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

end

/-- `finalP`'s precondition and public data follow from the contract's, and
the contract's postcondition from `finalP`'s, with the table, as
`ModesVerified.lean`'s `mode_implies` for the whole-block functions. `ls`
unfolds the contract and its signature. -/
local macro "final_implies " "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  refine final_implies_consts
    { pre := by
        intro s h
        sig_pre [$ls,*, abi, argRegs, stackBelow] at h
        obtain ⟨al, sp, hrd, hwr, dKV, dKD, dVD, dSK, dSV, dSD, fK, fV, fD, hn⟩ := h
        exact ⟨hrd, hwr, dKV, dKD, dVD, fK, fV, fD, al, sp, dSK, dSV, dSD, hn⟩
      post := fun s s' _ h => by sig_post [$ls,*, abi, argRegs]; exact h
      pub := by sig_implies_pub [$ls,*, abi, argRegs, argPub]
      sat := by sig_implies_sat [$ls,*, abi, argRegs, stackBelow] [modeSat] using modeSat }
    (fun _ _ h => h) ⟨modeSatC, ?_⟩
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  rw [ecbConsts_eq]
  generalize s1234 = W at hl held ⊢
  generalize e : modeSatC = s
  sig_pre [$ls,*, abi, argRegs, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow]
  subst e
  rw [hl]
  repeat' apply And.intro
  all_goals first
    | exact fun i hi => held i (by rw [hl]; exact hi)
    | rfl
    | decide
    | exact Or.inr rfl
    | exact Region.disjoint_of_sep (by decide)
    | (intro r hr
       change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩] at hr
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
       -- (A `rfl` pattern in a macro names a new variable, by hygiene.)
       rcases hr with hr | hr <;> (subst hr; exact Region.disjoint_of_sep (by decide)))))

theorem cfbEncFinal_implies : (finalPC encFinalPost).Implies
    (Proof.Cast5.cfbEncryptFinalRoundsContract (abi.withConsts ecbConsts) frameBytes) := by
  final_implies [Proof.Cast5.cfbEncryptFinalRoundsContract, Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre,
    Proof.Cast5.cfbEncFinalPost, encFinalPost]

theorem cfbDecFinal_implies : (finalPC decFinalPost).Implies
    (Proof.Cast5.cfbDecryptFinalRoundsContract (abi.withConsts ecbConsts) frameBytes) := by
  final_implies [Proof.Cast5.cfbDecryptFinalRoundsContract, Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre,
    Proof.Cast5.cfbDecFinalPost, decFinalPost]

/-! ## Verified -/

theorem cfbEncryptFinal_verified : Verified target cfbEncryptFinal
    (Proof.Cast5.cfbEncryptFinalRoundsContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cfbEncryptFinal_correct (cfbEncryptFinal_constantTime _) cfbEncFinal_implies

theorem cfbDecryptFinal_verified : Verified target cfbDecryptFinal
    (Proof.Cast5.cfbDecryptFinalRoundsContract (abi.withConsts ecbConsts) frameBytes) :=
  Verified.of_correct cfbDecryptFinal_correct (cfbDecryptFinal_constantTime _) cfbDecFinal_implies

end VG.Proof.Cast5.RISCV64.Modes
