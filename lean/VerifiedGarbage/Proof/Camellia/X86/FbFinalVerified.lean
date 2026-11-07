module

public import VerifiedGarbage.Proof.Camellia.X86.FbVerified
public import VerifiedGarbage.Impl.Camellia.X86.FbFinal
public import VerifiedGarbage.Spec.Camellia.CfbFinal
public import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Modes.X86.SeqFinal
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit
import VerifiedGarbage.Proof.Camellia.X86.CallSum
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Camellia.X86.FbVerified
meta import VerifiedGarbage.Impl.Camellia.X86.FbFinal
meta import VerifiedGarbage.Spec.Camellia.CfbFinal
meta import VerifiedGarbage.Proof.Camellia.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Modes.X86.SeqFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Camellia.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Camellia.X86.CallSum
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData

/-!
# Camellia-CFB128 of a message's last piece on x86 (32-bit) meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.X86.cfbEncFinal_wp`, `cfbDecFinal_wp`) over
Camellia's core in the encryption direction (`dirCoreSpec .encrypt`), with the
working space as a sixth argument (`finalX86`), as the whole-block functions
are (`FbVerified.lean`), but the data `len` bytes. Each is correct and
constant time, by the taint analysis from the same initial taint
(`Fb.fbTaint`) with the core's call summary; the `_framed` theorems run them
with their working space on the stack, zeroed on return, on the subkeys at
`schedule` (`Proof.Camellia.cfbEncFinalScratchContract`), which give the
specification's contracts (`cfbEncryptFinal_of_sk`).
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.FbFinal

open VG VG.X86 VG.Impl.Camellia.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre byteMode argAddr_eq)
open VG.Proof.Camellia.X86 (scr_eq disjoint_empty KeyArgs dirCoreSpec dirCore_ka)
open VG.Proof.Camellia (schedWords)
open VG.Proof.Camellia.X86.Fb (ciph fbTaint frameSat stk_eq stk_ret modeSlots_sub)

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 16 s.mem s'.mem ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) (arg s 4).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 16 s.mem s'.mem ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) (arg s 4).toNat

/-- A final CFB128 function on x86 with its working space as the sixth
argument, the data `len` bytes, and the postcondition `post`. -/
def finalX86 (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * 341⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩
    s.rd = [sched, args] ∧ s.wr = [data, iv, scratch] ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * 341 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) ∧
    stk.Disjoint data ∧ stk.Disjoint iv ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧ 16 ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- `finalX86`'s precondition gives the modes', for steps of a byte. -/
theorem seqPre_of {post : State → State → Prop} {s : State} (h : (finalX86 post).pre s) :
    SeqPre (dirCore .encrypt) byteMode s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, hRn, sD, sV, sS, sA, sE⟩ := h
  have hL := (dirCoreSpec .encrypt).layout
  have e1 : ∀ n : Nat, byteMode.step * n = n := fun n => Nat.one_mul n
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, slots_eq]),
      (by simp only [dirCore, slots_eq]; omega)⟩, (by rw [hwr]; simp [dirCore]),
    (fun _ => by rw [hwr]; simp [dirCore]), (by simp only [dirCore]; omega),
    (by rw [hwr]; simp [dirCore, Proof.Modes.X86.dataRegion, e1]),
    (by rw [e1]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => ?_), ?_, ?_, ?_, ?_, sE, (by simp [byteMode, dirCore]), hL⟩
  · simp only [Proof.Modes.X86.dataRegion, e1]; rw [scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dVD
  · rw [scr_eq]; exact dAS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dAD
  · rw [scr_eq]; exact dRS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dRD
  · exact dRV
  · rw [stk_eq sE]; simp only [Proof.Modes.X86.dataRegion, e1]; exact sD
  · rw [stk_eq sE]; exact sS.sub_right (modeSlots_sub _)
  · rw [stk_eq sE]; exact sA
  · rw [stk_eq sE]; exact stk_ret s

theorem keyArgs_of {post : State → State → Prop} {s : State} (h : (finalX86 post).pre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore .encrypt)]
      ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) := by
  obtain ⟨hrd, hwr, dKS, -, -, -, dAD, dAV, dAS, -, -, -, fK, -, -, -, fE, hRn, sD, sV, sS, sA, sE⟩ := h
  have inA : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.argOp i)) 4 := fun i hi =>
    ⟨⟨argAddr s 0, 24⟩, by rw [hrd]; simp, by
      rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega) hi]
      exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  have subA : ∀ i < 6, Region.Sub ⟨s.ea (VG.Impl.Aes.X86.argOp i), 4⟩ ⟨argAddr s 0, 24⟩ := fun i hi => by
    rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega) hi]
    exact VG.Offset.sub_base _ (by omega)
  refine ⟨arg s 0, inA 0 (by decide), rfl, inA 1 (by decide), ?_, hRn, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, ?_⟩
  · show arg s 1 = BitVec.ofNat 32 (arg s 1).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (subA 0 (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (subA 1 (by decide))
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dAD.sub_left (subA 1 (by decide))
    · exact dAV.sub_left (subA 1 (by decide))
    · exact dAS.sub_left (subA 1 (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    rw [show Proof.Modes.X86.stkRegion (s.gpr .esp) 16 = _ from stk_eq sE .encrypt]; exact sS
  · rw [show Proof.Modes.X86.stkRegion (s.gpr .esp) 16 = _ from stk_eq sE .encrypt]
    exact sA.sub_right (subA 1 (by decide))

theorem cfbEncryptFinal_wp {s₀ : State} (hp : (finalX86 encPost).pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalX86 encPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.cfbEncFinal_wp (dirCoreSpec .encrypt) (seqPre_of hp) rfl rfl (keyArgs_of hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, by show encPost _ _; rw [encPost, ← Fb.cipher_eq]; exact h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : (finalX86 decPost).pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalX86 decPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.cfbDecFinal_wp (dirCoreSpec .encrypt) (seqPre_of hp) rfl rfl (keyArgs_of hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, by show decPost _ _; rw [decPost, ← Fb.cipher_eq]; exact h2⟩

/-! ## Constant time -/

theorem fbTaint_wf {post : State → State → Prop} {s : State} (hp : (finalX86 post).pre s) :
    VG.X86.Taint.Wf fbTaint s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, hRn, sD, sV, sS, sA, sE⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega, ?_⟩, ?_⟩ fun _ => ⟨sE, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) dRS dAS
  · intro p hp'
    simp only [fbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact sD
    · exact sV
    · exact sS

theorem fbTaint_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (finalX86 post).pre s₁)
    (h₂ : (finalX86 post).pre s₂) (hpub : (finalX86 post).pub s₁ s₂) : VG.X86.Taint.Agree fbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -, -, -, -, -, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -, -, -, -, -, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 2 (by omega), ha 3 (by omega), ha 4 (by omega), ha 5 (by omega)]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth fbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 28) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 28) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem cfbEncryptFinal_ct : ConstantTime isa (finalX86 encPost).pre (finalX86 encPost).pub cfbEncryptFinal :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [cryptCallSum] :
    ∃ h, (VG.X86.taint.check fbTaint cfbEncryptFinal h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfbDecryptFinal_ct : ConstantTime isa (finalX86 decPost).pre (finalX86 decPost).pub cfbDecryptFinal :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [cryptCallSum] :
    ∃ h, (VG.X86.taint.check fbTaint cfbDecryptFinal h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

/-- `finalX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`final_verified` narrows to `finalX86`). -/
def wideContract (post : State → State → Prop) : Contract isa :=
  { finalX86 post with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
      let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * 341⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩
      s.rd = [sched] ∧ s.wr = [iv, data, scratch, args] ∧
      sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * 341 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) ∧
    stk.Disjoint data ∧ stk.Disjoint iv ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧ 16 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 272⟩, ⟨argAddr s 0, 24⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨(arg s 2).setWidth 64, 16⟩, ⟨(arg s 5).setWidth 64, 8 * 341⟩]

tactic_template "camellia_final_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.Camellia.X86.FbFinal.finalX86, VG.Proof.Camellia.X86.FbFinal.wideContract,
                     VG.Proof.Camellia.X86.FbFinal.narrowRd, VG.Proof.Camellia.X86.FbFinal.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

theorem wide_pre (post : State → State → Prop) (s : State) (h : (wideContract post).pre s) :
    (finalX86 post).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  camellia_final_narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 18, 0x2000, 0x3000, 1, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 0x12 else if a = 0x800D then 0x20
    else if a = 0x8011 then 0x30 else if a = 0x8014 then 1 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩, ⟨0x4000, 2728⟩, ⟨0x8004, 24⟩]

theorem wide_implies_enc : (wideContract encPost).Implies (Proof.Camellia.cfbEncFinalScratchContract X86.abi 341 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbEncryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbEncryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbEncryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost,
      ciph]
  · sig_implies_pub [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbEncryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost]
  · sig_implies_sat [Proof.Camellia.cfbEncFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbEncryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec : (wideContract decPost).Implies (Proof.Camellia.cfbDecFinalScratchContract X86.abi 341 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbDecryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbDecryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbDecryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost,
      ciph]
  · sig_implies_pub [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbDecryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost]
  · sig_implies_sat [Proof.Camellia.cfbDecFinalScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Curry.app, Spec.Camellia.cfbFinalSig, Proof.Camellia.cfbDecryptFinalPostSk, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem final_verified {post : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (finalX86 post).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (finalX86 post).post s s')
    (hct : ConstantTime isa (finalX86 post).pre (finalX86 post).pub c)
    (hR : ∀ s s' rd wr rd' wr', post (s.withRegions rd wr) (s'.withRegions rd' wr') → post s s')
    {k : Contract isa} (hi : (wideContract post).Implies k) : Verified X86.target c k := by
  have hsat := hi.sat_left
  have narrowSat : ∃ s, (finalX86 post).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre post s hs⟩
  apply Verified.of_implies _ hi
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat))
    narrowRd narrowWr (wide_pre post) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    exact hR _ _ _ _ _ _ h
  · intro s₁ s₂ _ _ h
    camellia_final_narrow
    exact h

theorem cfbEncryptFinal_verified : Verified X86.target cfbEncryptFinal (Proof.Camellia.cfbEncFinalScratchContract X86.abi 341 16) :=
  final_verified (fun _ hs => cfbEncryptFinal_wp hs) cfbEncryptFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cfbDecryptFinal_verified : Verified X86.target cfbDecryptFinal (Proof.Camellia.cfbDecFinalScratchContract X86.abi 341 16) :=
  final_verified (fun _ hs => cfbDecryptFinal_wp hs) cfbDecryptFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

theorem frameSat_pre (post : Spec.Camellia.cfbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.cfbFinalSig.contract X86.abi (pre := Spec.Camellia.cfbFinalPre X86.abi.ptrBits) (post := post)
      (writeArgs := true) (stack := 2772)).pre s := by
  implies_sat [Spec.Camellia.cfbFinalSig, Spec.Camellia.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 cfbEncryptFinal)
      (Spec.Camellia.cfbEncryptFinalContract X86.abi 2772) :=
  Proof.Camellia.cfbEncryptFinal_of_sk <|
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.cfbFinalPre X86.abi.ptrBits)
    (post := Proof.Camellia.cfbEncryptFinalPostSk X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2756) cfbEncryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cfbFinalPre_local _)
    (Proof.Camellia.cfbEncryptFinalPost_local _) (Proof.Camellia.cfbEncryptFinalPostOut_local _) (frameSat_pre _)

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 cfbDecryptFinal)
      (Spec.Camellia.cfbDecryptFinalContract X86.abi 2772) :=
  Proof.Camellia.cfbDecryptFinal_of_sk <|
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.cfbFinalPre X86.abi.ptrBits)
    (post := Proof.Camellia.cfbDecryptFinalPostSk X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2756) cfbDecryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cfbFinalPre_local _)
    (Proof.Camellia.cfbDecryptFinalPost_local _) (Proof.Camellia.cfbDecryptFinalPostOut_local _) (frameSat_pre _)

end VG.Proof.Camellia.X86.FbFinal
