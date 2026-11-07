module

public import VerifiedGarbage.Proof.Idea.X86.FbVerified
public import VerifiedGarbage.Impl.Idea.X86.FbFinal
public import VerifiedGarbage.Spec.Idea.CfbFinal
public import VerifiedGarbage.Proof.Modes.CfbFinalScratch
public import VerifiedGarbage.Proof.Framework.Scratch
public import VerifiedGarbage.Proof.Modes.X86.SeqFinal
import VerifiedGarbage.Proof.Idea.X86.FbFinalLit
import VerifiedGarbage.Proof.Idea.Arith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Idea.X86.FbVerified
meta import VerifiedGarbage.Impl.Idea.X86.FbFinal
meta import VerifiedGarbage.Spec.Idea.CfbFinal
meta import VerifiedGarbage.Proof.Modes.CfbFinalScratch
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Modes.X86.SeqFinal
meta import VerifiedGarbage.Proof.Idea.X86.FbFinalLit
meta import VerifiedGarbage.Proof.Idea.Arith
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TacticTemplate

/-!
# IDEA-CFB64 of a message's last piece on x86 (32-bit) meets its contracts

`cfbEncryptFinal_wp`, `cfbDecryptFinal_wp`: the modes' CFB over a message's
last piece (`Proof.Modes.X86.cfbEncFinal_wp`, `cfbDecFinal_wp`) over IDEA's
core (`modeCoreSpec`), with the working space as a fifth argument
(`finalX86`), as the whole-block functions are (`FbVerified.lean`), but the
data `len` bytes. Each is correct and constant time, by the taint analysis
from the same initial taint (`Fb.fbTaint`); the `_framed` theorems run them
with their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Idea.X86.FbFinal

open VG VG.X86 VG.Impl.Idea.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre byteMode)
open VG.Proof.Idea.X86 (scr_eq disjoint_empty KeyArgs modeCoreSpec modeCore_ka)
open VG.Proof.Idea.X86.Fb (ciph fbTaint frameSat)

/-- The functions' postconditions. -/
def encPost (s s' : State) : Prop :=
  Spec.Cfb.EncryptFinal (ciph s) 8 s.mem s'.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) (arg s 3).toNat
def decPost (s s' : State) : Prop :=
  Spec.Cfb.DecryptFinal (ciph s) 8 s.mem s'.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) (arg s 3).toNat

/-- A final CFB64 function on x86 with its working space as the fifth
argument, the data `len` bytes, and the postcondition `post`. -/
def finalX86 (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 104⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
    let data : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 23⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, iv, scratch] ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 104 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 23 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `finalX86`'s precondition gives the modes', for steps of a byte. -/
theorem seqPre_of {post : State → State → Prop} {s : State} (h : (finalX86 post).pre s) :
    SeqPre modeCore byteMode s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE⟩ := h
  have hL := modeCoreSpec.layout
  have e1 : ∀ n : Nat, byteMode.step * n = n := fun n => Nat.one_mul n
  refine ⟨(by rw [hrd]; simp [modeCore]), fE, ⟨(by rw [hwr]; simp [modeCore, coreSlots, bufSlot, Impl.Idea.X86.slots]),
      (by simp only [modeCore, coreSlots, bufSlot, Impl.Idea.X86.slots]; omega_arith)⟩, (by rw [hwr]; simp [modeCore]),
    (fun _ => by rw [hwr]; simp [modeCore]), (by simp only [modeCore]; omega_arith),
    (by rw [hwr]; simp [modeCore, Proof.Modes.X86.dataRegion, e1]),
    (by rw [e1]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => ?_), disjoint_empty _ _, disjoint_empty _ _,
    disjoint_empty _ _, disjoint_empty _ _, (by simp [modeCore]), (by simp [byteMode, modeCore]), hL⟩
  · simp only [Proof.Modes.X86.dataRegion, e1]; rw [scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dVD
  · rw [scr_eq]; exact dAS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dAD
  · rw [scr_eq]; exact dRS
  · simp only [Proof.Modes.X86.dataRegion, e1]; exact dRD
  · exact dRV

theorem keyArgs_of {post : State → State → Prop} {s : State} (h : (finalX86 post).pre s) :
    KeyArgs s [Modes.X86.scrR s modeCore] (Spec.Idea.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, dKS, -, -, -, -, -, dAS, -, -, -, fK, -, -, -, -⟩ := h
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK, fun r hr => ?_,
    fun r hr => ?_⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))

theorem cfbEncryptFinal_wp {s₀ : State} (hp : (finalX86 encPost).pre s₀) :
    WP isa cfbEncryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalX86 encPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.cfbEncFinal_wp modeCoreSpec (seqPre_of hp) rfl rfl (keyArgs_of hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

theorem cfbDecryptFinal_wp {s₀ : State} (hp : (finalX86 decPost).pre s₀) :
    WP isa cfbDecryptFinal s₀ fun s' => abiPreserved s₀ s' ∧ (finalX86 decPost).post s₀ s' :=
  WP.mono (Proof.Modes.X86.cfbDecFinal_wp modeCoreSpec (seqPre_of hp) rfl rfl (keyArgs_of hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

/-! ## Constant time -/

theorem fbTaint_wf {post : State → State → Prop} {s : State} (hp : (finalX86 post).pre s) :
    VG.X86.Taint.Wf fbTaint s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE⟩ := hp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega_arith, ?_⟩, ?_⟩
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

theorem fbTaint_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (finalX86 post).pre s₁)
    (h₂ : (finalX86 post).pre s₂) (hpub : (finalX86 post).pub s₁ s₂) : VG.X86.Taint.Agree fbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂⟩ := id h₂
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
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecryptFinal_ct : ConstantTime isa (finalX86 decPost).pre (finalX86 decPost).pub cfbDecryptFinal :=
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

/-- `finalX86` with the argument slots writable, as the signature's contract
has them; the code reads them only (`final_verified` narrows to `finalX86`). -/
def wideContract (post : State → State → Prop) : Contract isa :=
  { finalX86 post with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 104⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
      let data : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 23⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [sched] ∧ s.wr = [iv, data, scratch, args] ∧
      sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 104 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 23 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 104⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩, ⟨(arg s 1).setWidth 64, 8⟩, ⟨(arg s 4).setWidth 64, 8 * 23⟩]

tactic_template "idea_final_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.Idea.X86.FbFinal.finalX86, VG.Proof.Idea.X86.FbFinal.wideContract,
                     VG.Proof.Idea.X86.FbFinal.narrowRd, VG.Proof.Idea.X86.FbFinal.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

theorem wide_pre (post : State → State → Prop) (s : State) (h : (wideContract post).pre s) :
    (finalX86 post).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  idea_final_narrow
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
  rd := [⟨0x1000, 104⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 1⟩, ⟨0x4000, 184⟩, ⟨0x8004, 20⟩]

/-- IDEA's cipher of the schedule at `k`. -/
abbrev ciphAt (m : Mem) (k : Addr) : Spec.Cbc.Cipher := Spec.Idea.cipher (Spec.Idea.scheduleAt m k)

/-- The final functions' signature. -/
abbrev finalSig : Sig := Proof.Modes.finalSig "schedule" .u8 104 8

/-- The final encryption's contract with the working space as an argument. -/
abbrev encScratch : Contract isa :=
  Sig.scratchContract X86.abi finalSig "scratch" .u64 23 (Curry.const (fun _ => True) _)
    (Proof.Modes.encFinalPost ciphAt 8 X86.abi.ptrBits) true 0

/-- The final decryption's contract with the working space as an argument. -/
abbrev decScratch : Contract isa :=
  Sig.scratchContract X86.abi finalSig "scratch" .u64 23 (Curry.const (fun _ => True) _)
    (Proof.Modes.decFinalPost ciphAt 8 X86.abi.ptrBits) true 0

theorem wide_implies_enc : (wideContract encPost).Implies encScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86,
      encPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost,
      ciph, ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.encFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, encPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec : (wideContract decPost).Implies decScratch := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86,
      decPost] at h
    sig_split h
    sig_reduce [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost,
      ciph, ciphAt]
  · sig_implies_pub [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost]
  · sig_implies_sat [Sig.scratchContract, Sig.withScratch, Curry.withScratch, Curry.app, Proof.Modes.finalSig,
      Proof.Modes.decFinalPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, finalX86, decPost]
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
    idea_final_narrow
    exact h

theorem cfbEncryptFinal_verified : Verified X86.target cfbEncryptFinal encScratch :=
  final_verified (fun _ hs => cfbEncryptFinal_wp hs) cfbEncryptFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_enc

theorem cfbDecryptFinal_verified : Verified X86.target cfbDecryptFinal decScratch :=
  final_verified (fun _ hs => cfbDecryptFinal_wp hs) cfbDecryptFinal_ct (fun _ _ _ _ _ _ h => h) wide_implies_dec

theorem frameSat_pre (post : Spec.Idea.cfbFinalSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Idea.cfbFinalSig.contract X86.abi (post := post) (writeArgs := true) (stack := 208)).pre s := by
  implies_sat [Spec.Idea.cfbFinalSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

/-- IDEA's cipher reads only the schedule. -/
theorem ciphAt_congr : ∀ m₁ m₂ k, (∀ i < 104, m₂ (k + BitVec.ofNat 64 i) = m₁ (k + BitVec.ofNat 64 i)) →
    ciphAt m₂ k = ciphAt m₁ k := fun _ _ _ h => congrArg Spec.Idea.cipher (Proof.Idea.scheduleAt_congr h)

/-- The final CFB64 encryption with its working space on the stack. -/
theorem cfbEncryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 cfbEncryptFinal)
      (Spec.Idea.cfbEncryptFinalContract X86.abi 208) :=
  X86.Verified.stackScratchWiped (sig := Spec.Idea.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 23) (post := Proof.Modes.encFinalPost ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) cfbEncryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.encFinalPost_inLocal _ ciphAt_congr) (Proof.Modes.encFinalPost_local _) (frameSat_pre _)

/-- The final CFB64 decryption with its working space on the stack. -/
theorem cfbDecryptFinal_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 208 4 46 cfbDecryptFinal)
      (Spec.Idea.cfbDecryptFinalContract X86.abi 208) :=
  X86.Verified.stackScratchWiped (sig := Spec.Idea.cfbFinalSig) (nm := "scratch") (e := .u64)
    (n := 23) (post := Proof.Modes.decFinalPost ciphAt 8 X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 208) cfbDecryptFinal_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Modes.decFinalPost_inLocal _ ciphAt_congr) (Proof.Modes.decFinalPost_local _) (frameSat_pre _)

end VG.Proof.Idea.X86.FbFinal
