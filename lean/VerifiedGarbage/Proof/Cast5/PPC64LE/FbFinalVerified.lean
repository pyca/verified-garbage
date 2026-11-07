module

public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesVerified
public import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
public import VerifiedGarbage.Impl.Cast5.PPC64LE.FbFinal
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit
import VerifiedGarbage.Proof.Cast5.ModeMem
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.FbFinalLit
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesVerified
meta import VerifiedGarbage.Proof.Cast5.PPC64LE.ModesFrame
meta import VerifiedGarbage.Proof.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Modes.PPC64LE.SeqFinal
meta import VerifiedGarbage.Impl.Cast5.PPC64LE.FbFinal
meta import VerifiedGarbage.Spec.Cast5.CfbFinal
meta import VerifiedGarbage.Spec.Cast5.OfbFinal
meta import VerifiedGarbage.Proof.Cast5.ModeMem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintSym
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Consts
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegSet

/-!
# CAST5-CFB64 and CAST5-OFB of a message's last piece on PPC64LE meet their contracts

`modeFn m` moves the arguments to the modes' registers and runs `m n` for
the count of rounds `n` (`modeFn_wp`), and each `m n` is here the modes' CFB
or OFB over a message's last piece (`Proof.Modes.PPC64LE.cfbEncFinal_wp`, …,
`ofbFinal_wp`) over
CAST5's core with `n` rounds (`Mode.dirCoreSpec`). With the working space as
the sixth argument (`finalP`, under the calling convention with the table:
`finalPC`), as the whole-block functions are (`ModesVerified.lean`), but the
data `len` bytes, each meets its contract with a scratch buffer of 22 words
(`Proof.Cast5.modeScratchContract`), constant time by the taint analysis
from the public argument registers and the table's address, as theirs are;
the `_framed` theorems run them with their working space on the stack,
zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Cast5.PPC64LE.FbFinal

open VG VG.PPC64LE VG.Impl.Cast5.PPC64LE VG.Impl.Modes
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Modes.PPC64LE (SeqPre byteMode)
open VG.Proof.Cast5.PPC64LE.Mode (dirCoreSpec KeyArgs layout)
open VG.Proof.Cast5.PPC64LE (modePub modes_agree ConstsOk.held1 ConstsOk.rd1 ConstsOk.wr1 stripConsts_rd_mem
  s1234_len ecbSatMem ecbSatMem_held ecbConsts_eq)
open VG.Proof.Cast5.PPC64LE.Modes (keyOf rounds Shifted Shifted.abi modeFn_wp argPub modeSat modeSatC frameSatC)

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (Spec.Cast5.cipher (keyOf s) (rounds s)) 8 s.mem s'.mem (s.gpr .r5) (s.gpr .r6)
    (s.gpr .r7).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (Spec.Cast5.cipher (keyOf s) (rounds s)) 8 s.mem s'.mem (s.gpr .r5) (s.gpr .r6)
    (s.gpr .r7).toNat

/-- A final function on PPC64LE with its working space as the sixth argument,
the data `len` bytes, and the postcondition `post`. -/
def finalP (post : State → State → Prop) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 128⟩
    let iv : Region := ⟨s.gpr .r5, 8⟩
    let data : Region := ⟨s.gpr .r6, (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * 22⟩
    s.rd = [key] ∧ s.wr = [iv, data, scratch] ∧
      key.Disjoint iv ∧ key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧
      iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      (s.gpr .r3).toNat + 128 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .r6).toNat + (s.gpr .r7).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 22 ≤ 2 ^ 64 ∧
      ((s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 16)
  post := post
  pub := argPub

/-- `finalP`, with the table. -/
def finalPC (post : State → State → Prop) : Contract isa where
  pre s := (finalP post).pre (stripConsts ecbConsts s) ∧ ConstsOk ecbConsts 0 s
  post := post
  pub := modePub

section
variable {post : State → State → Prop} {s s₁ : State} (hs : (finalPC post).pre s) (h₁ : Shifted s s₁)
include hs

theorem rounds_of : rounds s = 12 ∨ rounds s = 16 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hn⟩, -⟩ := hs
  exact hn

include h₁

/-- `finalPC`'s precondition gives the modes', for steps of a byte. -/
theorem seqPre_of (up : Bool) {n : Nat} : SeqPre (dirCore up n) byteMode s₁ := by
  obtain ⟨⟨-, hwr, -, -, -, dVD, dVS, dDS, -, fV, fD, fS, -⟩, -⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hwr dVD dVS dDS fV fD fS
  have eS : Proof.Modes.PPC64LE.scrRegion (dirCore up n) (Proof.Modes.PPC64LE.S s₁) = ⟨s.gpr .r8, 8 * 22⟩ := by
    simp only [Proof.Modes.PPC64LE.scrRegion, Proof.Modes.PPC64LE.S, h₁.r7]; rfl
  have eV : Proof.Modes.PPC64LE.ivR s₁ (dirCore up n) = ⟨s.gpr .r5, 8⟩ := by
    simp only [Proof.Modes.PPC64LE.ivR, Proof.Modes.PPC64LE.P, h₁.r4]; rfl
  have eD : Proof.Modes.PPC64LE.dataRegion (Proof.Modes.PPC64LE.Dp s₁) byteMode.step (Proof.Modes.PPC64LE.N s₁) =
      ⟨s.gpr .r6, (s.gpr .r7).toNat⟩ := by
    simp only [Proof.Modes.PPC64LE.dataRegion, Proof.Modes.PPC64LE.Dp, Proof.Modes.PPC64LE.N, h₁.r5, h₁.r6,
      byteMode, Nat.one_mul]
  have hwr₁ : s₁.wr = [⟨s.gpr .r5, 8⟩, ⟨s.gpr .r6, (s.gpr .r7).toNat⟩, ⟨s.gpr .r8, 8 * 22⟩] := by
    rw [h₁.wr, hwr]
  refine ⟨⟨by rw [hwr₁]; simp [Proof.Modes.PPC64LE.S, h₁.r7, dirCore], by
      simp only [Proof.Modes.PPC64LE.S, h₁.r7]; exact fS⟩,
    by rw [eV, hwr₁]; simp, fun _ => by rw [eV, hwr₁]; simp,
    by simp only [Proof.Modes.PPC64LE.P, h₁.r4]; exact fV, by rw [eD, hwr₁]; simp,
    by simp only [Proof.Modes.PPC64LE.Dp, Proof.Modes.PPC64LE.N, h₁.r5, h₁.r6, byteMode, Nat.one_mul]; exact fD,
    by rw [eD, eS]; exact dDS, by rw [eV, eS]; exact dVS, fun _ => by rw [eV, eD]; exact dVD,
    ⟨by decide, by show 1 ≤ 8; decide⟩, layout up n⟩

/-- `finalPC`'s precondition gives the key's arguments. -/
theorem keyArgs_of (up : Bool) {n : Nat} :
    KeyArgs s₁ (Proof.Modes.PPC64LE.wrs0 (dirCore up n) byteMode s₁) (keyOf s) := by
  obtain ⟨⟨hrd, hwr, -, dKD, dKS, -, -, -, fK, -, -, -, -⟩, hk⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr] at hrd hwr dKD dKS fK
  have trd : (⟨s.syms s1234Sym, 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  have twr : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms s1234Sym, 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  have ews : Proof.Modes.PPC64LE.wrs0 (dirCore up n) byteMode s₁ =
      [⟨s.gpr .r6, (s.gpr .r7).toNat⟩, ⟨s.gpr .r8, 8 * 22⟩] := by
    simp only [Proof.Modes.PPC64LE.wrs0, Proof.Modes.PPC64LE.wrs, Proof.Modes.PPC64LE.dataRegion,
      Proof.Modes.PPC64LE.scrRegion, Proof.Modes.PPC64LE.Dp, Proof.Modes.PPC64LE.N, Proof.Modes.PPC64LE.S,
      h₁.r5, h₁.r6, h₁.r7, byteMode, Nat.one_mul]
    rfl
  have hin : ∀ r ∈ Proof.Modes.PPC64LE.wrs0 (dirCore up n) byteMode s₁, r ∈ s.wr := fun r hr => by
    rw [ews] at hr; rw [hwr]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  refine ⟨by rw [h₁.mem, h₁.r3], ?_, by rw [h₁.r3]; exact fK, fun r hr => ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [h₁.rd, h₁.wr, Mode.keyR, h₁.r3]
    exact List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp))
  · rw [ews] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [Mode.keyR, h₁.r3]; exact dKD
    · rw [Mode.keyR, h₁.r3]; exact dKS
  · rw [h₁.rd, h₁.wr, Mode.tblR, h₁.syms]; exact List.mem_append_left _ trd
  · rw [h₁.mem, h₁.syms]; exact ConstsOk.held1 hk
  · rw [Mode.tblR, h₁.syms]; exact twr r (hin r hr)

end

theorem args_eq {s s₁ : State} (h₁ : Shifted s s₁) :
    Proof.Modes.PPC64LE.P s₁ = s.gpr .r5 ∧ Proof.Modes.PPC64LE.Dp s₁ = s.gpr .r6 ∧
      Proof.Modes.PPC64LE.N s₁ = (s.gpr .r7).toNat := by
  simp only [Proof.Modes.PPC64LE.P, Proof.Modes.PPC64LE.Dp, Proof.Modes.PPC64LE.N, h₁.r4, h₁.r5, h₁.r6,
    and_self]

/-! ## Correctness -/

theorem cfbEncryptFinal_correct (s : State) (hs : (finalPC encPost).pre s) :
    ∃ t s', Exec isa cfbEncryptFinal s t s' ∧ abiPreserved s s' ∧ encPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.PPC64LE.cfbEncFinal_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true) (keyArgs_of hs h₁ true))
    fun s' ⟨h1, h2⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨eP, eD, eN⟩ := args_eq h₁
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, ↓reduceIte, eP, eD, eN, h₁.mem] at h2
  exact h2

theorem cfbDecryptFinal_correct (s : State) (hs : (finalPC decPost).pre s) :
    ∃ t s', Exec isa cfbDecryptFinal s t s' ∧ abiPreserved s s' ∧ decPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.PPC64LE.cfbDecFinal_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true) (keyArgs_of hs h₁ true))
    fun s' ⟨h1, h2⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨eP, eD, eN⟩ := args_eq h₁
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, ↓reduceIte, eP, eD, eN, h₁.mem] at h2
  exact h2

/-! ## Constant time -/

theorem cfbEncryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

theorem cfbDecryptFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

/-! ## The contracts -/

/-- The final functions' scratch contract with the table, from `finalP`'s
implying it without. -/
theorem implies_consts {sig : Sig} {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : State → State → Prop} {post' : sig.Post abi.ptrBits}
    (h : (finalP post).Implies (Proof.Cast5.modeScratchContract abi sig 22 pre post'))
    (hpost : ∀ s s', post s s' → post (stripConsts ecbConsts s) s')
    (hsat : ∃ s, (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) sig 22 pre post').pre s) :
    (finalPC post).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) sig 22 pre post') where
  pre s hs := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at hs
    exact ⟨h.pre _ (pre_consts.mp hs).1, (pre_consts.mp hs).2⟩
  post s s' hs hp := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at hs ⊢
    exact post_consts.mpr (post_stripConsts.mp (h.post (stripConsts ecbConsts s) s' (pre_consts.mp hs).1
      (hpost s s' hp)))
  pub s₁ s₂ h₁ h₂ hp := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h₁ h₂ hp
    have a := h.pub (stripConsts ecbConsts s₁) (stripConsts ecbConsts s₂) (pre_consts.mp h₁).1
      (pre_consts.mp h₂).1 (pub_stripConsts.mpr (pub_consts.mp hp).1)
    exact ⟨a.1, a.2, (pub_consts.mp hp).2 _ List.mem_cons_self⟩
  sat := hsat

/-- `finalP`'s precondition, public data and witness are the scratch
contract's under `abi`, for any postcondition it implies. -/
theorem finalP_implies {post : State → State → Prop} {post' : Spec.Cast5.cfbFinalSig.Post abi.ptrBits}
    (hpost : ∀ s s', post s s' → (Proof.Cast5.modeScratchContract abi Spec.Cast5.cfbFinalSig 22
      (Spec.Cast5.cfbFinalPre abi.ptrBits) post').post s s') :
    (finalP post).Implies (Proof.Cast5.modeScratchContract abi Spec.Cast5.cfbFinalSig 22
      (Spec.Cast5.cfbFinalPre abi.ptrBits) post') where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, abi, argRegs, stackBelow] at h
    simp only [Curry.app] at h
    exact h
  post s s' _ hp := hpost s s' hp
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, abi, argRegs] at h
    obtain ⟨hsp, h3, h4, h5, h6, h7, h8⟩ := h
    exact ⟨hsp, by simp [h3, h4, h5, h6, h7, h8]⟩
  sat := ⟨modeSat, by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, abi, argRegs, stackBelow]
    simp only [Curry.app]
    repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem final_sat (post : Spec.Cast5.cfbFinalSig.Post abi.ptrBits) :
    ∃ s, (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 22
      (Spec.Cast5.cfbFinalPre abi.ptrBits) post).pre s := by
  refine ⟨modeSatC, ?_⟩
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  generalize e : modeSatC = s
  sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, abi, argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Cast5.s1234_length]
  subst e
  simp only [Curry.app]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, ?_⟩
  · change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩, ⟨0x4000, 176⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

theorem cfbEnc_implies : (finalPC encPost).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts)
    Spec.Cast5.cfbFinalSig 22 (Spec.Cast5.cfbFinalPre abi.ptrBits) (Proof.Cast5.cfbEncFinalPost abi.ptrBits)) :=
  implies_consts (finalP_implies fun s s' hp => by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Proof.Cast5.cfbEncFinalPost, abi, argRegs]
    simp only [Curry.app]
    exact hp) (fun _ _ h => h) (final_sat _)

theorem cfbDec_implies : (finalPC decPost).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts)
    Spec.Cast5.cfbFinalSig 22 (Spec.Cast5.cfbFinalPre abi.ptrBits) (Proof.Cast5.cfbDecFinalPost abi.ptrBits)) :=
  implies_consts (finalP_implies fun s s' hp => by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Proof.Cast5.cfbDecFinalPost, abi, argRegs]
    simp only [Curry.app]
    exact hp) (fun _ _ h => h) (final_sat _)

theorem cfbEncryptFinal_verified : Verified target cfbEncryptFinal
    (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 22
      (Spec.Cast5.cfbFinalPre abi.ptrBits) (Proof.Cast5.cfbEncFinalPost abi.ptrBits)) :=
  Verified.of_correct cfbEncryptFinal_correct (cfbEncryptFinal_constantTime _) cfbEnc_implies

theorem cfbDecryptFinal_verified : Verified target cfbDecryptFinal
    (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 22
      (Spec.Cast5.cfbFinalPre abi.ptrBits) (Proof.Cast5.cfbDecFinalPost abi.ptrBits)) :=
  Verified.of_correct cfbDecryptFinal_correct (cfbDecryptFinal_constantTime _) cfbDec_implies

/-! ## With the working space on the stack -/

theorem frame_sat (post : Spec.Cast5.cfbFinalSig.Post abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbFinalSig.contract (abi.withConsts ecbConsts) (Spec.Cast5.cfbFinalPre abi.ptrBits)
      post true (0 + 208)).pre s := by
  refine ⟨frameSatC, ?_⟩
  have held := ecbSatMem_held
  have hl := Proof.Cast5.s1234_length
  generalize e : frameSatC = s
  sig_pre [Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, abi, argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Cast5.s1234_length]
  subst e
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, ?_⟩
  · change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- `cfbEncryptFinal` with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 cfbEncryptFinal)
      (Proof.Cast5.cfbEncryptFinalRoundsContract (abi.withConsts ecbConsts) 208) :=
  PPC64LE.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 22) (pre := Spec.Cast5.cfbFinalPre abi.ptrBits)
    (post := Proof.Cast5.cfbEncFinalPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 208) (words := 22)
    cfbEncryptFinal_verified (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.cfbFinalPre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbEncFinalPost_local _) (Proof.Cast5.cfbEncFinalPostOut_local _) (frame_sat _)

/-- `cfbDecryptFinal` with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 cfbDecryptFinal)
      (Proof.Cast5.cfbDecryptFinalRoundsContract (abi.withConsts ecbConsts) 208) :=
  PPC64LE.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 22) (pre := Spec.Cast5.cfbFinalPre abi.ptrBits)
    (post := Proof.Cast5.cfbDecFinalPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 208) (words := 22)
    cfbDecryptFinal_verified (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.cfbFinalPre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbDecFinalPost_local _) (Proof.Cast5.cfbDecFinalPostOut_local _) (frame_sat _)

/-! ## OFB of a message's last piece -/

/-- The final OFB function's postcondition. -/
def ofbPost (s s' : State) : Prop :=
  Spec.Ofb.CryptFinal (Spec.Cast5.cipher (keyOf s) (rounds s)) 8 s.mem s'.mem (s.gpr .r5) (s.gpr .r6)
    (s.gpr .r7).toNat

theorem ofbFinal_correct (s : State) (hs : (finalPC ofbPost).pre s) :
    ∃ t s', Exec isa ofbFinal s t s' ∧ abiPreserved s s' ∧ ofbPost s s' := by
  refine modeFn_wp (rounds_of hs) fun s₁ h₁ => WP.mono (Proof.Modes.PPC64LE.ofbFinal_wp
    (dirCoreSpec true _ (rounds_of hs)) (seqPre_of hs h₁ true) (keyArgs_of hs h₁ true))
    fun s' ⟨h1, h2⟩ => ⟨h₁.abi h1, ?_⟩
  obtain ⟨eP, eD, eN⟩ := args_eq h₁
  simp only [dirCore, dirCoreSpec, Proof.Cast5.dirCipher, ↓reduceIte, eP, eD, eN, h₁.mem] at h2
  exact h2

theorem ofbFinal_constantTime (pre : State → Prop) : ConstantTime isa pre modePub ofbFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (fun _ _ _ _ hp => modes_agree _ _ hp) (by taint_decide)

/-- `finalP`'s precondition, public data and witness are the OFB scratch
contract's under `abi`, for any postcondition it implies. -/
theorem ofbFinalP_implies {post : State → State → Prop} {post' : Spec.Cast5.ofbFinalSig.Post abi.ptrBits}
    (hpost : ∀ s s', post s s' → (Proof.Cast5.modeScratchContract abi Spec.Cast5.ofbFinalSig 22
      (Spec.Cast5.ofbFinalPre abi.ptrBits) post').post s s') :
    (finalP post).Implies (Proof.Cast5.modeScratchContract abi Spec.Cast5.ofbFinalSig 22
      (Spec.Cast5.ofbFinalPre abi.ptrBits) post') where
  pre s h := by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.ofbFinalSig, Spec.Cast5.ofbFinalPre, abi, argRegs, stackBelow] at h
    simp only [Curry.app] at h
    exact h
  post s s' _ hp := hpost s s' hp
  pub s₁ s₂ _ _ h := by
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.ofbFinalSig, abi, argRegs] at h
    obtain ⟨hsp, h3, h4, h5, h6, h7, h8⟩ := h
    exact ⟨hsp, by simp [h3, h4, h5, h6, h7, h8]⟩
  sat := ⟨modeSat, by
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.ofbFinalSig, Spec.Cast5.ofbFinalPre, abi, argRegs, stackBelow]
    simp only [Curry.app]
    repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)⟩

theorem ofbFinal_sat (post : Spec.Cast5.ofbFinalSig.Post abi.ptrBits) :
    ∃ s, (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.ofbFinalSig 22
      (Spec.Cast5.ofbFinalPre abi.ptrBits) post).pre s := by
  refine ⟨modeSatC, ?_⟩
  have hl : s1234.length = 512 := by rw [Impl.Cast5.s1234, table_length]
  have held := ecbSatMem_held
  generalize e : modeSatC = s
  sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Spec.Cast5.ofbFinalSig, Spec.Cast5.ofbFinalPre, abi, argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Cast5.s1234_length]
  subst e
  simp only [Curry.app]
  refine ⟨rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, ?_⟩
  · change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩, ⟨0x4000, 176⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

theorem ofb_implies : (finalPC ofbPost).Implies (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts)
    Spec.Cast5.ofbFinalSig 22 (Spec.Cast5.ofbFinalPre abi.ptrBits) (Proof.Cast5.ofbFinalPost abi.ptrBits)) :=
  implies_consts (ofbFinalP_implies fun s s' hp => by
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.ofbFinalSig, Proof.Cast5.ofbFinalPost, abi, argRegs]
    simp only [Curry.app]
    exact hp) (fun _ _ h => h) (ofbFinal_sat _)

theorem ofbFinal_verified : Verified target ofbFinal
    (Proof.Cast5.modeScratchContract (abi.withConsts ecbConsts) Spec.Cast5.ofbFinalSig 22
      (Spec.Cast5.ofbFinalPre abi.ptrBits) (Proof.Cast5.ofbFinalPost abi.ptrBits)) :=
  Verified.of_correct ofbFinal_correct (ofbFinal_constantTime _) ofb_implies

theorem ofbFrame_sat (post : Spec.Cast5.ofbFinalSig.Post abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbFinalSig.contract (abi.withConsts ecbConsts) (Spec.Cast5.ofbFinalPre abi.ptrBits)
      post true (0 + 208)).pre s := by
  refine ⟨frameSatC, ?_⟩
  have held := ecbSatMem_held
  have hl := Proof.Cast5.s1234_length
  generalize e : frameSatC = s
  sig_pre [Spec.Cast5.ofbFinalSig, Spec.Cast5.ofbFinalPre, abi, argRegs, ecbConsts_eq, Abi.withConsts,
    Abi.constRegions, Abi.constsHeld, stackBelow, Proof.Cast5.s1234_length]
  subst e
  refine ⟨by decide, rfl, fun i hi => held i (by rw [hl]; exact hi), by decide, fun r hr => ?_, ?_⟩
  · change r ∈ [(⟨0x2000, 8⟩ : Region), ⟨0x3000, 0⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | rfl | decide | exact Or.inr rfl | exact Region.disjoint_of_sep (by decide)

/-- `ofbFinal` with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 208 .r8 22 ofbFinal)
      (Proof.Cast5.ofbFinalRoundsContract (abi.withConsts ecbConsts) 208) :=
  PPC64LE.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbFinalSig)
    (nm := "scratch") (e := .u64) (n := 22) (pre := Spec.Cast5.ofbFinalPre abi.ptrBits)
    (post := Proof.Cast5.ofbFinalPost abi.ptrBits) (wa := true) (stack := 0) (bytes := 208) (words := 22)
    ofbFinal_verified (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.ofbFinalPre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.ofbFinalPost_local _) (Proof.Cast5.ofbFinalPostOut_local _) (ofbFrame_sat _)

end VG.Proof.Cast5.PPC64LE.FbFinal
