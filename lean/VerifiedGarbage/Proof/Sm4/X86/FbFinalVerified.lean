module

public import VerifiedGarbage.Proof.Sm4.X86.FbVerified
public import VerifiedGarbage.Impl.Sm4.X86.FbFinal
public import VerifiedGarbage.Spec.Sm4.CfbFinal
public import VerifiedGarbage.Spec.Sm4.OfbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Modes.X86.SeqFinal
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Sm4.CtrCipher
public import VerifiedGarbage.Proof.Sm4.X86.ModeCore
public import VerifiedGarbage.Proof.Sm4.X86.CallSum
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Sm4.X86.FbVerified
meta import VerifiedGarbage.Impl.Sm4.X86.FbFinal
meta import VerifiedGarbage.Spec.Sm4.CfbFinal
meta import VerifiedGarbage.Spec.Sm4.OfbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Modes.X86.SeqFinal
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Sm4.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Sm4.CtrCipher
meta import VerifiedGarbage.Proof.Sm4.X86.ModeCore
meta import VerifiedGarbage.Proof.Sm4.X86.CallSum
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-!
# SM4-CFB128 and SM4-OFB of a message's last piece on x86 (32-bit) meet their contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`, `ofbFinal_wp`: the modes' CFB
and OFB over a message's last piece (`Proof.Modes.X86.cfbEncFinal_wp`,
`cfbDecFinal_wp`, `ofbFinal_wp`) over SM4's
core in the encryption direction (`dirCoreSpec .encrypt`), with the working
space as a fifth argument (`finalX86`), as the whole-block functions are
(`FbVerified.lean`), but the data `len` bytes. Each is correct and constant
time, by the taint analysis from the same initial taint (`Fb.fbTaint`) with
the summaries of the calls (`CallSum.lean`); the `_framed` theorems run them
with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86.FbFinal

open VG VG.X86 VG.Impl.Sm4.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre stkRegion byteMode)
open VG.Proof.Sm4.X86 (scr_eq stk_apart KeyArgs dirCoreSpec dirCoreSpec_cipher)
open VG.Proof.Sm4.X86.Fb (ciph fbTaint frameSat)

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 16 s.mem s'.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) (arg s 3).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 16 s.mem s'.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) (arg s 3).toNat

/-- A final CFB128 function on x86 with its working space as the fifth
argument, the data `len` bytes, and the postcondition `post`. -/
def finalX86 (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 184⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 20
    s.rd = [sched, args] ∧ s.wr = [data, iv, scratch] ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 184 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `finalX86`'s precondition gives the modes', for steps of a byte. -/
theorem seqPre_of {post : State → State → Prop} {s : State} (h : (finalX86 post).pre s) :
    SeqPre (dirCore .encrypt) byteMode s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, -, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := h
  have hL := (dirCoreSpec .encrypt).layout
  have e1 : ∀ n : Nat, byteMode.step * n = n := fun n => Nat.one_mul n
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, slots_eq]),
      (by simp only [dirCore, slots_eq]; omega_arith)⟩, (by rw [hwr]; simp [dirCore]),
    (fun _ => by rw [hwr]; simp [dirCore]), (by simp only [dirCore]; omega_arith),
    (by rw [hwr]; simp [dirCore, Proof.Modes.X86.dataRegion, e1]),
    (by rw [e1]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => dRV), (by simp only [Proof.Modes.X86.dataRegion, e1]; exact dSD), ?_, sA, sR,
    (by simp only [dirCore]; omega_arith), (by simp [byteMode, dirCore]), hL⟩
  · simp only [Proof.Modes.X86.dataRegion, e1]; rw [scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dVD
  · rw [scr_eq]; exact dAS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dAD
  · rw [scr_eq]; exact dRS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dRD
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, slots_eq]; omega_arith))

theorem keyArgs_of {post : State → State → Prop} {s : State} (h : (finalX86 post).pre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore .encrypt)] (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, dKS, -, -, -, -, -, dAS, -, -, -, dSK, -, -, dSS, fK, -, -, -, fE, fLo⟩ := h
  obtain ⟨sA, -⟩ := stk_apart fE fLo
  have a4 : Region.Sub ⟨argAddr s 4, 4⟩ ⟨argAddr s 0, 20⟩ := by
    rw [Proof.Modes.X86.argAddr_eq s (n := 5) (by omega_arith) (by decide)]
    exact VG.Offset.sub_base _ (by decide)
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK, fun r hr => ?_,
    fun r hr => ?_, fun r hr => ?_, arg s 4, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, arg_in s (n := 5) (by omega_arith) (by decide)⟩,
    rfl, fun r hr => ?_, fun r hr => ?_, sA.sub_right a4⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dSK
    · rw [scr_eq]; exact dSS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left a4

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
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, -, dSD, dSV, dSS, fK, fV, fD, fS, fE, fLo⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega_arith, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_arith) dRS dAS
  · intro p hp'
    simp only [fbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨fLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20 =
        (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 := (VG.X86.Taint.sub_setWidth fLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dSD
    · exact dSV
    · exact dSS

theorem fbTaint_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (finalX86 post).pre s₁)
    (h₂ : (finalX86 post).pre s₂) (hpub : (finalX86 post).pub s₁ s₂) : VG.X86.Taint.Agree fbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega_arith), ha 2 (by omega_arith), ha 3 (by omega_arith), ha 4 (by omega_arith)]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth fbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

theorem cfbEncryptFinal_ct : ConstantTime isa (finalX86 encPost).pre (finalX86 encPost).pub cfbEncryptFinal :=
  VG.Taint.constantTime_of_exists (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide_sum [prepSum, cryptSum])

theorem cfbDecryptFinal_ct : ConstantTime isa (finalX86 decPost).pre (finalX86 decPost).pub cfbDecryptFinal :=
  VG.Taint.constantTime_of_exists (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide_sum [prepSum, cryptSum])

/-! ## The contracts -/

/-- `finalX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`final_verified` narrows to `finalX86`). -/
def wideContract (post : State → State → Prop) : Contract isa :=
  { finalX86 post with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 184⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 20
      s.rd = [sched] ∧ s.wr = [iv, data, scratch, args] ∧
      sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint iv ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 184 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨(arg s 1).setWidth 64, 16⟩, ⟨(arg s 4).setWidth 64, 8 * 184⟩]

tactic_template "sm4_final_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.Sm4.X86.FbFinal.finalX86, VG.Proof.Sm4.X86.FbFinal.wideContract,
                     VG.Proof.Sm4.X86.FbFinal.narrowRd, VG.Proof.Sm4.X86.FbFinal.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

theorem wide_pre (post : State → State → Prop) (s : State) (h : (wideContract post).pre s) :
    (finalX86 post).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  sm4_final_narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 1, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8010 then 1 else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1472⟩, ⟨0x8004, 20⟩]

/-- SM4's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Sm4.cipher (Spec.Sm4.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 128 16

/-- The final encryption's contract with the working space as an argument. -/
abbrev encScratch : Contract isa :=
  Sig.scratchContract X86.abi finalSig "scratch" .u64 184 (Curry.const (fun _ => True) _)
    (Proof.Modes.encFinalPost ciphAt 16 X86.abi.ptrBits) true 20

/-- The final decryption's contract with the working space as an argument. -/
abbrev decScratch : Contract isa :=
  Sig.scratchContract X86.abi finalSig "scratch" .u64 184 (Curry.const (fun _ => True) _)
    (Proof.Modes.decFinalPost ciphAt 16 X86.abi.ptrBits) true 20

theorem wide_implies_enc : (wideContract encPost).Implies encScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below,
      encPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, encPost,
      ciph, ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, encPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec : (wideContract decPost).Implies decScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below,
      decPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, decPost,
      ciph, ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, decPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, decPost]
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
    sm4_final_narrow
    exact h

theorem cfbEncryptFinal_verified : Verified X86.target cfbEncryptFinal encScratch :=
  final_verified (fun _ hs => cfbEncryptFinal_wp hs) cfbEncryptFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cfbDecryptFinal_verified : Verified X86.target cfbDecryptFinal decScratch :=
  final_verified (fun _ hs => cfbDecryptFinal_wp hs) cfbDecryptFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

theorem frameSat_pre (post : Spec.Sm4.cfbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Sm4.cfbFinalSig.contract X86.abi (post := post) (writeArgs := true) (stack := 1516)).pre s := by
  implies_sat [Spec.Sm4.cfbFinalSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

/-- SM4's cipher reads only the schedule. -/
theorem ciphAt_congr : ∀ m₁ m₂ k, (∀ i < 128, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) →
    ciphAt m₂ k = ciphAt m₁ k := fun _ _ _ h => congrArg Spec.Sm4.cipher (Proof.Sm4.scheduleAt_congr h)

/-- The final CFB128 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 cfbEncryptFinal)
      (Spec.Sm4.cfbEncryptFinalContract X86.abi 1516) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 184) (post := Proof.Modes.encFinalPost ciphAt 16 X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1496) cfbEncryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.encFinalPost_inLocal _ ciphAt_congr) (Proof.Modes.encFinalPost_local _) (frameSat_pre _)

/-- The final CFB128 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 cfbDecryptFinal)
      (Spec.Sm4.cfbDecryptFinalContract X86.abi 1516) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 184) (post := Proof.Modes.decFinalPost ciphAt 16 X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1496) cfbDecryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.decFinalPost_inLocal _ ciphAt_congr) (Proof.Modes.decFinalPost_local _) (frameSat_pre _)

/-! ## OFB of a message's last piece -/

/-- The final OFB function's postcondition. -/
def ofbPost (s s' : State) : Prop :=
  Spec.Ofb.CryptFinal (ciph s) 16 s.mem s'.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) (arg s 3).toNat

theorem ofbFinal_wp {s₀ : State} (hp : (finalX86 ofbPost).pre s₀) :
    WP isa ofbFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalX86 ofbPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.ofbFinal_wp (dirCoreSpec .encrypt) (seqPre_of hp) rfl rfl (keyArgs_of hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, by show ofbPost _ _; rw [ofbPost, ← Fb.cipher_eq]; exact h2⟩

theorem ofbFinal_ct : ConstantTime isa (finalX86 ofbPost).pre (finalX86 ofbPost).pub ofbFinal :=
  VG.Taint.constantTime_of_exists (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide_sum [prepSum, cryptSum])

/-- The final OFB function's contract with the working space as an argument. -/
abbrev ofbScratch : Contract isa :=
  Sig.scratchContract X86.abi finalSig "scratch" .u64 184 (Curry.const (fun _ => True) _)
    (Proof.Modes.ofbFinalPost ciphAt 16 X86.abi.ptrBits) true 20

theorem wide_implies_ofb : (wideContract ofbPost).Implies ofbScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below,
      ofbPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, ofbPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, ofbPost,
      ciph, ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, ofbPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.ofbFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, below, ofbPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ofbFinal_verified : Verified X86.target ofbFinal ofbScratch :=
  final_verified (fun _ hs => ofbFinal_wp hs) ofbFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_ofb

theorem ofbFrameSat_pre (post : Spec.Sm4.ofbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Sm4.ofbFinalSig.contract X86.abi (post := post) (writeArgs := true) (stack := 1516)).pre s := by
  implies_sat [Spec.Sm4.ofbFinalSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

/-- The final OFB function with its working space on the stack. -/
theorem ofbFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 ofbFinal)
      (Spec.Sm4.ofbFinalContract X86.abi 1516) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.ofbFinalSig) (nm := "scratch") (e := .u64)
    (n := 184) (post := Proof.Modes.ofbFinalPost ciphAt 16 X86.abi.ptrBits) (wa := true) (stack := 20)
    (bytes := 1496) ofbFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.ofbFinalPost_inLocal _ ciphAt_congr) (Proof.Modes.ofbFinalPost_local _) (ofbFrameSat_pre _)

end VG.Proof.Sm4.X86.FbFinal
