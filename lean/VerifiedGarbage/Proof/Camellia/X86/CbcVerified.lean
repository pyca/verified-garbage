module

public import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.NativeTaint
public import VerifiedGarbage.Proof.Camellia.X86.ModeCore
meta import VerifiedGarbage.Proof.Camellia.X86.ModeCore
public import VerifiedGarbage.Proof.Modes.X86.Modes
meta import VerifiedGarbage.Proof.Modes.X86.Modes
public import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
public import VerifiedGarbage.Proof.Camellia.X86.CbcLit
meta import VerifiedGarbage.Proof.Camellia.X86.CbcLit
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Camellia-CBC on x86 (32-bit) meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
(`Proof.Modes.X86.cbcEnc_wp`, `cbcDec_wp`) over Camellia's core for each
direction (`dirCoreSpec`), with the working space as a sixth argument
(`cbcX86`). Each is correct and constant time, by the taint analysis, which
starts with `esp` public and knows which argument words are the base
addresses of the data and the scratch buffer. `cbcEncrypt_framed` and
`cbcDecrypt_framed` run them with their working space on the stack, zeroed
on return.
-/

@[expose] public section

namespace VG.Proof.Camellia

open VG VG.X86 VG.Impl.Camellia.X86

/-- CBC on x86 with its working space as the sixth argument: encryption if
`enc`, else decryption. -/
def cbcX86 (enc : Bool) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * 341⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, iv, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧
    data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * 341 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24)
  post s s' :=
    Spec.Cbc.blocksAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat =
      (if enc then Spec.Cbc.encrypt (Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat))
       else Spec.Cbc.decrypt (Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)))
        (Spec.Aes.bytesAt s.mem ((arg s 2).setWidth 64) 16)
        (Spec.Cbc.blocksAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.Camellia

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.Impl.Camellia.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre stkRegion slotA cbcEnc_wp cbcDec_wp)
open VG.Proof.Camellia (cbcX86)
open VG.Proof.Camellia (schedWords)
open VG.Proof.Modes.X86 (argAddr_eq)

theorem disjoint_empty (r : Region) (a : Addr) : Region.Disjoint ⟨a, 0⟩ r := fun _ h => by
  simp only [Region.Contains] at h; omega

theorem scr_eq (s : State) (d : Dir) :
    Modes.X86.scrR s (dirCore d) = ⟨(arg s 5).setWidth 64, 8 * 341⟩ := by
  simp [Modes.X86.scrR, dirCore, slots_eq]

/-- `cbcX86`'s precondition gives the modes'. -/
theorem seqPre_of {enc : Bool} {M : Mode} (d : Dir) (hstep : M.step = 16) (hiv : M.ivOut = false) {s : State} (h : (cbcX86 enc).pre s) :
    SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dAD, dAS, dRD, dRS, fK, fV, fD, fS, fE, hRn⟩ := h
  have hL := (dirCoreSpec d).layout
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, slots_eq]),
      (by simp only [dirCore, slots_eq]; omega)⟩, (by rw [hrd]; simp [dirCore]),
    (fun h => by rw [hiv] at h; cases h), (by simp only [dirCore]; omega), (by rw [hwr, hstep]; simp [dirCore]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun h => by rw [hiv] at h; cases h), ?_, ?_, ?_, ?_,
    (fun h => by rw [hiv] at h; cases h), disjoint_empty _ _, disjoint_empty _ _,
    disjoint_empty _ _, disjoint_empty _ _, (by simp [dirCore]), (by rw [hstep]; simp [dirCore]), hL⟩
  all_goals first
    | (rw [hstep, scr_eq]; first | exact dDS)
    | (rw [scr_eq]; first | exact dVS | exact dAS | exact dRS)
    | (rw [hstep]; first | exact dVD | exact dAD | exact dRD)


theorem keyArgs_of {enc : Bool} (d : Dir) {s : State} (h : (cbcX86 enc).pre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore d)]
      ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) := by
  obtain ⟨hrd, hwr, -, dKS, -, -, -, dAD, dAS, -, -, fK, -, -, -, fE, hRn⟩ := h
  have inA : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.argOp i)) 4 := fun i hi =>
    ⟨⟨argAddr s 0, 24⟩, by rw [hrd]; simp, by
      rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega) hi]
      exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  have subA : ∀ i < 6, Region.Sub ⟨s.ea (VG.Impl.Aes.X86.argOp i), 4⟩ ⟨argAddr s 0, 24⟩ := fun i hi => by
    rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega) hi]
    exact VG.Offset.sub_base _ (by omega)
  refine ⟨arg s 0, inA 0 (by decide), rfl, inA 1 (by decide), ?_, hRn, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · show arg s 1 = BitVec.ofNat 32 (arg s 1).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (subA 0 (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (subA 1 (by decide))
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dAD.sub_left (subA 1 (by decide))
    · exact dAS.sub_left (subA 1 (by decide))

attribute [local irreducible] Spec.Camellia.cipher in
/-- The core's cipher is the contract's (stated once: unifying them unfolds the cipher's spec). -/
theorem encCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    (dirCoreSpec .encrypt).cipher (R, schedWords m p R) = Spec.Camellia.cipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

attribute [local irreducible] Spec.Camellia.invCipher in
/-- The core's cipher is the contract's (stated once: unifying them unfolds the cipher's spec). -/
theorem decCipher_eq (m : Mem) (p : Addr) (R : Nat) :
    (dirCoreSpec .decrypt).cipher (R, schedWords m p R) = Spec.Camellia.invCipher (Spec.Camellia.subkeysAt m p R) :=
  rfl

theorem cbcEncrypt_wp {s₀ : State} (hp : (cbcX86 true).pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (cbcX86 true).post s₀ s' :=
  WP.mono (cbcEnc_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, by rw [encCipher_eq] at h2; exact h2⟩

theorem cbcDecrypt_wp {s₀ : State} (hp : (cbcX86 false).pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (cbcX86 false).post s₀ s' :=
  WP.mono (cbcDec_wp (dirCoreSpec .decrypt) (seqPre_of .decrypt rfl rfl hp) (keyArgs_of .decrypt hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, by rw [decCipher_eq] at h2; exact h2⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def cbcTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8 * 341], argLen := 28, argBases := [(16, 0), (24, 1)] }

theorem cbcTaint_wf {enc : Bool} {s : State} (hp : (cbcX86 enc).pre s) : VG.X86.Taint.Wf cbcTaint s := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dAD, dAS, dRD, dRS, fK, fV, fD, fS, fE, hRn⟩ := hp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [cbcTaint]; omega, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨dDS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [setWidth_toNat] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) dRS dAS
  · intro p hp'
    simp only [cbcTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem cbcTaint_agree {enc : Bool} {s₁ s₂ : State} (h₁ : (cbcX86 enc).pre s₁) (h₂ : (cbcX86 enc).pre s₂)
    (hpub : (cbcX86 enc).pub s₁ s₂) : VG.X86.Taint.Agree cbcTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have fE₁ : (s₁.gpr .esp).toNat + 28 ≤ 2 ^ 32 := h₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fE₂ : (s₂.gpr .esp).toNat + 28 ≤ 2 ^ 32 := h₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, cbcTaint_wf h₁, cbcTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [cbcTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1, ha 3 (by omega), ha 4 (by omega), ha 5 (by omega)]
  · simp only [cbcTaint] at hk
    rw [show VG.X86.Taint.depth cbcTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 28) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 28) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- What is public at the core's loop of pairs of rounds: `eax`, the stack
pointer, the round keys' and the scratch buffer's pointers, the flags, the
group's end, and the data pointer and the blocks left in their slots. -/
def cbcPairTaint : VG.X86.Taint.T :=
  { regs := .ofList [.eax, .esp, .esi, .edi], flags := true, lens := [0, 4 * (dirCore .encrypt).total],
    bases := [(.edi, 1, 0)], slots := [(1, 4 * grpSlot, 4), (1, 4 * (dirCore .encrypt).dSlot, 8)],
    argLen := 28, argBases := [(16, 0), (24, 1)] }

/-! The loop of pairs of rounds, which both directions run for 18 and 24
rounds, analysed once, as a summary. -/

taint_summary cbcPairSum : VG.X86.taint cbcPairTaint (.block pairBody)

theorem cbcEncrypt_ct : ConstantTime isa (cbcX86 true).pre (cbcX86 true).pub cbcEncrypt :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [cbcPairSum] :
    ∃ h, (VG.X86.taint.check cbcTaint cbcEncrypt h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) cbcTaint (fun _ _ h₁ h₂ hp => cbcTaint_agree h₁ h₂ hp) h

theorem cbcDecrypt_ct : ConstantTime isa (cbcX86 false).pre (cbcX86 false).pub cbcDecrypt :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [cbcPairSum] :
    ∃ h, (VG.X86.taint.check cbcTaint cbcDecrypt h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) cbcTaint (fun _ _ h₁ h₂ hp => cbcTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

/-- `cbcX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`cbc_verified` narrows to `cbcX86`). -/
def cbcWideContract (enc : Bool) : Contract isa :=
  { cbcX86 enc with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
      let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * 341⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [sched, iv] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * 341 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) }

def cbcNarrowRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 272⟩, ⟨(arg s 2).setWidth 64, 16⟩, ⟨argAddr s 0, 24⟩]
def cbcNarrowWr (s : State) : List Region :=
  [⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩, ⟨(arg s 5).setWidth 64, 8 * 341⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| plain_simp_names simp only [VG.Proof.Camellia.cbcX86, VG.Proof.Camellia.X86.cbcWideContract,
                     VG.Proof.Camellia.X86.cbcNarrowRd, VG.Proof.Camellia.X86.cbcNarrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem cbcWide_pre (enc : Bool) (s : State) (h : (cbcWideContract enc).pre s) :
    (cbcX86 enc).pre (s.withRegions (cbcNarrowRd s) (cbcNarrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 18, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def cbcSatState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 0x12 else if a = 0x800D then 0x20
    else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2728⟩, ⟨0x8004, 24⟩]

theorem wide_implies_enc :
    (cbcWideContract true).Implies (Proof.Camellia.cbcEncScratchContract X86.abi 341) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cbcEncScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcEncryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86] at h
    sig_split h
    sig_reduce [Proof.Camellia.cbcEncScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcEncryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
    sig_simp [Proof.Camellia.cbcEncScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcEncryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cbcEncScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcEncryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86, ite_true, ite_false, Bool.false_eq_true]
  · sig_implies_pub [Proof.Camellia.cbcEncScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcEncryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
  · sig_implies_sat [Proof.Camellia.cbcEncScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcEncryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
      [cbcSatState, arg, argAddr, Mem.readW, Mem.read] using cbcSatState

theorem wide_implies_dec :
    (cbcWideContract false).Implies (Proof.Camellia.cbcDecScratchContract X86.abi 341) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cbcDecScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcDecryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86] at h
    sig_split h
    sig_reduce [Proof.Camellia.cbcDecScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcDecryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
    sig_simp [Proof.Camellia.cbcDecScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcDecryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cbcDecScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcDecryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86, ite_true, ite_false, Bool.false_eq_true]
  · sig_implies_pub [Proof.Camellia.cbcDecScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcDecryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
  · sig_implies_sat [Proof.Camellia.cbcDecScratchContract, Proof.Camellia.cbcScratchSig, Spec.Camellia.cbcSig, Spec.Camellia.cbcDecryptPost, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
      [cbcSatState, arg, argAddr, Mem.readW, Mem.read] using cbcSatState

/-- A state satisfying the CBC functions' precondition: the schedule at
`0x1000`, 18 rounds, the IV at `0x2000`, and no blocks at `0x3000`, as stack arguments at
`0x8004`, which are writable. -/
def cbcFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 0x12 else if a = 0x800D then 0x20
    else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x8004, 20⟩]

theorem cbcFrameSat_pre (post : Spec.Camellia.cbcSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.cbcSig.contract X86.abi (pre := Spec.Camellia.cbcPre X86.abi.ptrBits) (post := post) (writeArgs := true) (stack := 2756)).pre s := by
  implies_sat [Spec.Camellia.cbcSig, Spec.Camellia.cbcPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [cbcFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using cbcFrameSat

theorem cbcEncrypt_verified : Verified X86.target cbcEncrypt (Proof.Camellia.cbcEncScratchContract X86.abi 341) := by
  have hsat := wide_implies_enc.sat_left
  have narrowSat : ∃ s, (cbcX86 true).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, cbcWide_pre true s hs⟩
  apply Verified.of_implies _ wide_implies_enc
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => cbcEncrypt_wp hs) cbcEncrypt_ct (.refl narrowSat))
    cbcNarrowRd cbcNarrowWr (cbcWide_pre true) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [cbcNarrowRd, cbcNarrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [cbcNarrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

/-- cbcEncrypt with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 cbcEncrypt)
      (Spec.Camellia.cbcEncryptContract X86.abi 2756) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cbcSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.cbcPre X86.abi.ptrBits) (post := Spec.Camellia.cbcEncryptPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2756) cbcEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cbcPre_local _)
    (Proof.Camellia.cbcEncryptPost_local _) (Proof.Camellia.cbcEncPostOut_local _) (cbcFrameSat_pre _)

theorem cbcDecrypt_verified : Verified X86.target cbcDecrypt (Proof.Camellia.cbcDecScratchContract X86.abi 341) := by
  have hsat := wide_implies_dec.sat_left
  have narrowSat : ∃ s, (cbcX86 false).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, cbcWide_pre false s hs⟩
  apply Verified.of_implies _ wide_implies_dec
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => cbcDecrypt_wp hs) cbcDecrypt_ct (.refl narrowSat))
    cbcNarrowRd cbcNarrowWr (cbcWide_pre false) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [cbcNarrowRd, cbcNarrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [cbcNarrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

/-- cbcDecrypt with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 cbcDecrypt)
      (Spec.Camellia.cbcDecryptContract X86.abi 2756) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cbcSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.cbcPre X86.abi.ptrBits) (post := Spec.Camellia.cbcDecryptPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 2756) cbcDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cbcPre_local _)
    (Proof.Camellia.cbcDecryptPost_local _) (Proof.Camellia.cbcDecPostOut_local _) (cbcFrameSat_pre _)

end VG.Proof.Camellia.X86
