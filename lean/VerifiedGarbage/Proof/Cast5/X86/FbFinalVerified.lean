module

public import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
public import VerifiedGarbage.Impl.Cast5.X86.FbFinal
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Modes.X86.SeqFinal
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.TaintSym
public import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit
import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Cast5.X86.ModesVerified
meta import VerifiedGarbage.Impl.Cast5.X86.FbFinal
meta import VerifiedGarbage.Spec.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Cast5.CfbFinal
meta import VerifiedGarbage.Proof.Modes.X86.SeqFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Cast5.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/-!
# CAST5-CFB64 of a message's last piece on x86 (32-bit): correctness and contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.X86.cfbEncFinal_wp`, `cfbDecFinal_wp`) over CAST5's
encrypting core (`Mode.dirCoreSpec true`), with the working space as a sixth
argument (`finalX`: `ModeFns.modeX true` but the data `len` bytes). The table
of S-boxes is readable, where the static `VG_CAST5_S1234` puts it, and holds
the S-boxes. Each is constant time from the modes' initial taint
(`ModeFns.τFb`); the `_framed` theorems run them with their working space on
the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.FbFinal

open VG VG.X86 VG.Impl.Cast5.X86.Modes VG.Impl.Modes
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)
open VG.Proof.Modes.X86 (SeqPre byteMode)
open VG.Proof.Cast5.X86.Mode (dirCoreSpec KeyArgs)
open VG.Proof.Cast5 (Held)
open VG.Proof.Cast5.X86 (ecbConsts_eq s1234_length)
open VG.Proof.Cast5.X86.ModeFns (keyA ivA scrA argsA tabA retA stkA scr_eq τFb stk_eq argBytes_agree ciph fbK
  satMem_held)

/-- The data, `len` bytes. -/
abbrev dataF (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩

/-- The readable regions. -/
def rdF (s : State) : List Region := [keyA s, argsA s, tabA s]

/-- The writable regions. -/
def wrF (s : State) : List Region := [dataF s, ivA s, scrA s]

/-- A final function's precondition on x86, with the working space as the
sixth argument: `ModeFns.MPre true` with the data `len` bytes. -/
structure FPre (s : State) : Prop where
  rdEq : s.rd = rdF s
  wrEq : s.wr = wrF s
  sp : 4 ≤ (s.gpr .esp).toNat
  espFit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  nv : (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 16
  fitK : (arg s 0).toNat + 128 ≤ 2 ^ 32
  fitV : (arg s 2).toNat + 8 ≤ 2 ^ 32
  fitD : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  fitS : (arg s 5).toNat + 304 ≤ 2 ^ 32
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  held : Held s.mem ((s.syms s1234Sym).setWidth 64) s1234
  dDS : (dataF s).Disjoint (scrA s)
  dVS : (ivA s).Disjoint (scrA s)
  dVD : (ivA s).Disjoint (dataF s)
  dKw : ∀ r ∈ s.wr, (keyA s).Disjoint r
  dTw : ∀ r ∈ s.wr, (tabA s).Disjoint r
  dAw : ∀ r ∈ s.wr, (argsA s).Disjoint r
  dRw : ∀ r ∈ s.wr, (retA s).Disjoint r
  dSw : ∀ r ∈ s.wr, (stkA s).Disjoint r
  dKs : (keyA s).Disjoint (stkA s)
  dTs : (tabA s).Disjoint (stkA s)

/-- A final function on x86 with the precondition `FPre` and the
postcondition `post`. -/
def finalX (post : State → State → Prop) : Contract isa where
  pre := FPre
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    s₁.syms s1234Sym = s₂.syms s1234Sym

section
variable {s : State}

theorem FPre.mem_wr_data (h : FPre s) : dataF s ∈ s.wr := by rw [h.wrEq]; simp [wrF]
theorem FPre.mem_wr_scr (h : FPre s) : scrA s ∈ s.wr := by rw [h.wrEq]; simp [wrF]
theorem FPre.mem_wr_iv (h : FPre s) : ivA s ∈ s.wr := by rw [h.wrEq]; simp [wrF]
theorem FPre.mem_iv (h : FPre s) : ivA s ∈ s.rd ++ s.wr := by rw [h.rdEq, h.wrEq]; simp [rdF, wrF]
theorem FPre.mem_args (h : FPre s) : argsA s ∈ s.rd ++ s.wr := by rw [h.rdEq]; simp [rdF]
theorem FPre.mem_key (h : FPre s) : keyA s ∈ s.rd ++ s.wr := by rw [h.rdEq]; simp [rdF]
theorem FPre.mem_tab (h : FPre s) : tabA s ∈ s.rd ++ s.wr := by rw [h.rdEq]; simp [rdF]

/-- The word below `esp` is apart from the arguments and the return address. -/
theorem stk_apart (h : FPre s) :
    Region.Disjoint (stkA s) (argsA s) ∧ Region.Disjoint (stkA s) (retA s) := by
  have hlo := h.sp
  have hfit := h.espFit
  have e : (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ ⟨argAddr s 0, 24⟩
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 4) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

end

/-- `FPre` gives the modes' precondition, for steps of a byte. -/
theorem seqPre_of {s : State} (h : FPre s) : SeqPre (dirCore true) byteMode s := by
  have hL := (dirCoreSpec true).layout
  have e1 : ∀ n : Nat, byteMode.step * n = n := fun n => Nat.one_mul n
  obtain ⟨sA, sR⟩ := stk_apart h
  have mS := h.mem_wr_scr
  have mD := h.mem_wr_data
  refine ⟨h.mem_args, h.espFit, ⟨mS, h.fitS⟩, h.mem_iv, fun _ => h.mem_wr_iv, h.fitV,
    by simp only [Proof.Modes.X86.dataRegion, e1]; exact mD, by rw [e1]; exact h.fitD,
    by simp only [Proof.Modes.X86.dataRegion, e1]; exact h.dDS, h.dVS,
    fun _ => by simp only [Proof.Modes.X86.dataRegion, e1]; exact h.dVD, h.dAw _ mS,
    by simp only [Proof.Modes.X86.dataRegion, e1]; exact h.dAw _ mD,
    h.dRw _ mS, by simp only [Proof.Modes.X86.dataRegion, e1]; exact h.dRw _ mD, fun _ => h.dRw _ h.mem_wr_iv,
    by simp only [Proof.Modes.X86.dataRegion, e1]; exact h.dSw _ mD,
    (h.dSw _ mS).sub_right (VG.Offset.sub_base _ (by simp [dirCore, coreSlots])), sA, sR, h.sp,
    by simp [byteMode, dirCore], hL⟩

theorem keyArgs_of {s : State} (h : FPre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore true)]
      (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64), (arg s 1).toNat) := by
  obtain ⟨sA, -⟩ := stk_apart h
  have hfit := h.espFit
  have ea : ∀ k, k + 4 ≤ 24 → (⟨addr (s.gpr .esp) (4 + k), 4⟩ : Region).Sub (argsA s) := by
    intro k hk
    have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
    have ek : addr (s.gpr .esp) (4 + k) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 k := by
      rw [addr_eq (by omega), VG.Offset.add_add]
    show Region.Sub ⟨addr (s.gpr .esp) (4 + k), 4⟩ ⟨argAddr s 0, 24⟩
    rw [e0, ek]; exact VG.Offset.sub_base _ hk
  have argSub : (Mode.argR s).Sub (argsA s) := by
    have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
    show Region.Sub ⟨addr (s.gpr .esp) 4, 8⟩ ⟨argAddr s 0, 24⟩
    rw [e0, show addr (s.gpr .esp) 4 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 0 by
      rw [BitVec.add_zero]; exact addr_eq (by omega)]
    exact VG.Offset.sub_base _ (by decide)
  have mS := h.mem_wr_scr
  refine ⟨arg s 0, ⟨by omega, h.sp, ⟨_, h.mem_args, by
      show (⟨argAddr s 0, 24⟩ : Region).Contains (argAddr s 0) 8
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩, rfl, ?_, h.nv, h.fitK, ⟨_, h.mem_key,
    Region.contains_self _ _⟩, rfl, h.fitT, ⟨_, h.mem_tab, Region.contains_self _ _⟩, h.held,
    fun r hr => ⟨h.dKw r hr, h.dTw r hr, (h.dAw r hr).sub_left argSub⟩, h.dKs, h.dTs,
    (sA.symm.sub_left argSub)⟩, fun r hr => ?_⟩
  · show arg s 1 = BitVec.ofNat 32 (arg s 1).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact ⟨h.dKw _ mS, h.dTw _ mS, (h.dAw _ mS).sub_left argSub, h.dSw _ mS⟩

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 8 s.mem s'.mem ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) (arg s 4).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 8 s.mem s'.mem ((arg s 2).setWidth 64) ((arg s 3).setWidth 64) (arg s 4).toNat

theorem cfbEncryptFinal_wp {s₀ : State} (hp : (finalX encPost).pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalX encPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.cfbEncFinal_wp (dirCoreSpec true) (seqPre_of hp) rfl rfl (keyArgs_of hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : (finalX decPost).pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalX decPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.cfbDecFinal_wp (dirCoreSpec true) (seqPre_of hp) rfl rfl (keyArgs_of hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

/-! ## Constant time -/

theorem τFb_wf {s : State} (h : FPre s) : VG.X86.Taint.Wf τFb s := by
  have hw := h.wrEq
  simp only [wrF] at hw
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [τFb]; have := h.espFit; omega, ?_⟩, ?_⟩ ?_
  · rw [hw]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨h.dVD.symm, h.dDS⟩, h.dVS, fun _ h => h.elim⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · simp only [toNat_setWidth]; exact h.fitD
    · simp only [toNat_setWidth]; exact h.fitV
    · simp only [toNat_setWidth]; exact h.fitS
  · intro r hr
    exact VG.X86.Taint.frame_disjoint (n := 24) (by have := h.espFit; omega) (h.dRw r hr) (h.dAw r hr)
  · intro p hp
    simp only [τFb, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hw, addr, arg, argAddr]
  · intro _
    refine ⟨h.sp, fun r hr => ?_⟩
    simp only [τFb]
    rw [stk_eq s h.sp]
    exact h.dSw r hr

theorem τFb_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (finalX post).pre s₁)
    (h₂ : (finalX post).pre s₂) (hp : (finalX post).pub s₁ s₂) :
    VG.X86.Taint.AgreeS [s1234Sym] τFb s₁ s₂ := by
  obtain ⟨sp, args, sy⟩ := hp
  refine ⟨⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τFb_wf h₁, τFb_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp,
    fun k h4 hk => argBytes_agree rfl rfl h₁.espFit h₂.espFit args h4 hk⟩, fun n hn => ?_⟩
  · simp only [τFb, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [h₁.wrEq, h₂.wrEq]
    simp only [wrF, dataF, ivA, scrA, args 2 (by decide), args 3 (by decide), args 4 (by decide),
      args 5 (by decide)]
  · simp only [List.mem_singleton] at hn
    subst hn; exact sy

theorem cfbEncryptFinal_ct : ConstantTime isa (finalX encPost).pre (finalX encPost).pub cfbEncryptFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecryptFinal_ct : ConstantTime isa (finalX decPost).pre (finalX decPost).pub cfbDecryptFinal :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

theorem final_pre {post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits} (s : State)
    (h : (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s) :
    FPre (s.withRegions (rdF s) (wrF s)) ∧ s.rd = [keyA s, tabA s] ∧
      s.wr = [ivA s, dataF s, scrA s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, -, htake, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA,
    -, dRV, dRD, dRS, -, dBK, dBV, dBD, dBS, -, fK, fV, fD, fS, nv⟩ := h
  have hrd : s.rd = [keyA s, tabA s] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, VG.X86.Taint.sub_setWidth h4]
  have mV : ivA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mD : dataF s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : scrA s ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨⟨rfl, rfl, h4, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega), nv, fK, fV, fD, fS, fitT,
    (fun i hi => held i (by rw [s1234_length] at hi; exact hi)), dDS, dVS, dVD,
    (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dBK.symm),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dTB)⟩, hrd,
    hwr⟩
  all_goals
    simp only [State.withRegions_wr, wrF, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dTw _ mD
  · exact dTw _ mV
  · exact dTw _ mS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBS

theorem final_pub {post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s₁)
    (_ : (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s₂)
    (h : (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (finalX postX).pub (s₁.withRegions (rdF s₁) (wrF s₁))
      (s₂.withRegions (rdF s₂) (wrF s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
  obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_, hsy⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem finalK_verified {post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits} {postX : State → State → Prop}
    {c : Prog isa}
    (hwp : ∀ s, (finalX postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (finalX postX).post s s')
    (hct : ConstantTime isa (finalX postX).pre (finalX postX).pub c)
    (hpost : ∀ s s', (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdF s) (wrF s)) (s'.withRegions (rdF s) (wrF s)) →
        (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (finalX postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (final_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) rdF wrF
    (fun s h => (final_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost final_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := final_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdF, wrF, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := final_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrF, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem final_sat {post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits} :
    (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post).pre (ModeFns.satState true) := by
  have a0 : arg (ModeFns.satState true) 0 = 0x1000 := (ModeFns.sat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (ModeFns.satState true) 1 = 16 := (ModeFns.sat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (ModeFns.satState true) 2 = 0x2000 := (ModeFns.sat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (ModeFns.satState true) 3 = 0x3000 := (ModeFns.sat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (ModeFns.satState true) 4 = 0 := (ModeFns.sat_arg true 4 (by decide)).trans (by decide)
  have a5 : arg (ModeFns.satState true) 5 = 0x4000 := (ModeFns.sat_arg true 5 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : ModeFns.satState true = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch]
  subst s
  rw [a0, a1, a2, a3, a4, a5]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem final_frameSat (post : Spec.Cast5.cfbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbFinalSig.contract (X86.abi.withConsts ecbConsts) (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) post true
      336).pre s := by
  refine ⟨ModeFns.frameSat true, ?_⟩
  have a0 : arg (ModeFns.frameSat true) 0 = 0x1000 := (ModeFns.frameSat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (ModeFns.frameSat true) 1 = 16 := (ModeFns.frameSat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (ModeFns.frameSat true) 2 = 0x2000 := (ModeFns.frameSat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (ModeFns.frameSat true) 3 = 0x3000 := (ModeFns.frameSat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (ModeFns.frameSat true) 4 = 0 := (ModeFns.frameSat_arg true 4 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : ModeFns.frameSat true = s
  sig_pre [Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  rw [a0, a1, a2, a3, a4]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl


theorem cfbEncryptFinal_verified :
    Verified X86.target cfbEncryptFinal
      (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) (Proof.Cast5.cfbEncFinalPost X86.abi.ptrBits)) :=
  finalK_verified (fun _ hs => cfbEncryptFinal_wp hs) cfbEncryptFinal_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, Proof.Cast5.cfbEncFinalPost, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, final_sat⟩

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cfbEncryptFinal)
      (Proof.Cast5.cfbEncryptFinalRoundsContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Spec.Cast5.cfbFinalPre X86.abi.ptrBits)
    (post := Proof.Cast5.cfbEncFinalPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cfbEncryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.cfbFinalPre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbEncFinalPost_local _) (Proof.Cast5.cfbEncFinalPostOut_local _) (final_frameSat _)

theorem cfbDecryptFinal_verified :
    Verified X86.target cfbDecryptFinal
      (fbK Spec.Cast5.cfbFinalSig (Spec.Cast5.cfbFinalPre X86.abi.ptrBits) (Proof.Cast5.cfbDecFinalPost X86.abi.ptrBits)) :=
  finalK_verified (fun _ hs => cfbDecryptFinal_wp hs) cfbDecryptFinal_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbFinalSig, Proof.Cast5.cfbDecFinalPost, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, final_sat⟩

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cfbDecryptFinal)
      (Proof.Cast5.cfbDecryptFinalRoundsContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Spec.Cast5.cfbFinalPre X86.abi.ptrBits)
    (post := Proof.Cast5.cfbDecFinalPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cfbDecryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.cfbFinalPre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbDecFinalPost_local _) (Proof.Cast5.cfbDecFinalPostOut_local _) (final_frameSat _)

end VG.Proof.Cast5.X86.FbFinal
