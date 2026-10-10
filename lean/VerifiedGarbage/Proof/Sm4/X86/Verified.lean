import VerifiedGarbage.Proof.Sm4.X86.Ecb
import VerifiedGarbage.Proof.Sm4.Scratch
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# SM4 ECB on x86 (32-bit) meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis, which starts with `esp` public and knows which argument
words are the base addresses of the data and the scratch buffer: the
pointers, `n` and what the code computes from them are public, in registers
or in the scratch buffer's slots, which the code stores again after each
store through another pointer. `ecb_framed` runs it with its working space
on the stack, zeroed on return: 1452 bytes, the 1432 of the scratch buffer,
the copies of the three argument slots, the buffer's address and the return
address of the call of the code, which uses no other stack.
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.Impl.Sm4.X86
open VG.Proof.Sm4 (specDirX86 ecbX86)

/-- `ecbX86.pre`, by name. -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 4 * Impl.Sm4.X86.slots⟩]
  dDB : Region.Disjoint ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Sm4.X86.slots⟩
  aD : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
  aB : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Sm4.X86.slots⟩
  rD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Sm4.X86.slots⟩
  fD : (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32
  fB : (arg s 3).toNat + 4 * Impl.Sm4.X86.slots ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem EPre.of {dir : Dir} {s : State} (h : (ecbX86 dir).pre s) : EPre s := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9, -, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h5, h6, h7, h8, h9, h11, h12, h13⟩

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 4 * Impl.Sm4.X86.slots], argLen := 20,
    argBases := [(8, 0), (16, 1)] }

theorem ecbTaint_wf {s : State} (hp : EPre s) : VG.X86.Taint.Wf ecbTaint s := by
  have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ecbTaint]; omega, ?_⟩, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [setWidth_toNat] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem ecbTaint_agree (dir : Dir) {s₁ s₂ : State} (h₁ : (ecbX86 dir).pre s₁) (h₂ : (ecbX86 dir).pre s₂)
    (hpub : (ecbX86 dir).pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := EPre.of h₁; have hp₂ := EPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf hp₁, ecbTaint_wf hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr, ha 1 (by omega), ha 2 (by omega), ha 3 (by omega)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 20) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbX86 dir).pre (ecbX86 dir).pub (ecb dir) := by
  cases dir
  · exact VG.Taint.constantTime (A := VG.X86.taint) ecbTaint
      (fun _ _ h₁ h₂ hp => ecbTaint_agree .encrypt h₁ h₂ hp) (by taint_decide)
  · exact VG.Taint.constantTime (A := VG.X86.taint) ecbTaint
      (fun _ _ h₁ h₂ hp => ecbTaint_agree .decrypt h₁ h₂ hp) (by taint_decide)

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbX86 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbX86 dir).post s s' :=
  ecb_wp dir hs

/-- `ecbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`ecb_verified` narrows to `ecbX86`). -/
def wideContract (dir : Dir) : Contract isa :=
  { ecbX86 dir with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * Impl.Sm4.X86.slots⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [sched] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 4 * Impl.Sm4.X86.slots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 4 * Impl.Sm4.X86.slots⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.Sm4.ecbX86, VG.Proof.Sm4.X86.wideContract,
    VG.Proof.Sm4.X86.narrowRd, VG.Proof.Sm4.X86.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wide_pre (dir : Dir) (s : State) (h : (wideContract dir).pre s) :
    (ecbX86 dir).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x30 else if a = 0x8011 then 0x40 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 1432⟩, ⟨0x8004, 16⟩]

theorem wide_implies (dir : Dir) :
    (wideContract dir).Implies (Proof.Sm4.ecbScratchContract X86.abi (specDirX86 dir) 179) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Sm4.X86.slots] at h
    sig_split h
    sig_reduce [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Sm4.X86.slots]
    sig_simp [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Sm4.X86.slots] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, specDirX86, Impl.Sm4.X86.slots]
  · sig_implies_pub [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Sm4.X86.slots]
  · sig_implies_sat [Proof.Sm4.ecbScratchContract, Proof.Sm4.ecbScratchSig, Spec.Sm4.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Sm4.X86.slots]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ecb_verified (dir : Dir) :
    Verified X86.target (ecb dir) (Proof.Sm4.ecbScratchContract X86.abi (specDirX86 dir) 179) := by
  have hsat := (wide_implies dir).sat_left
  have narrowSat : ∃ s, (ecbX86 dir).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre dir s hs⟩
  apply Verified.of_implies _ (wide_implies dir)
  refine Verified.narrowTo
    (Verified.of_correct (ecb_correct dir) (ecb_ct dir) (.refl narrowSat))
    narrowRd narrowWr (wide_pre dir) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowRd, narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no blocks at `0x2000`, as stack arguments at `0x8004`, which
are writable. -/
def ecbFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x8004, 12⟩]

theorem ecbFrameSat_pre (d : Spec.Sm4.Direction) : ∃ s, (Spec.Sm4.ecbContract X86.abi d 1452).pre s := by
  implies_sat [Spec.Sm4.ecbContract, Spec.Sm4.ecbSig, Spec.Sm4.ecbPost, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] [ecbFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1452 3 358 (ecb dir))
      (Spec.Sm4.ecbContract X86.abi (specDirX86 dir) 1452) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.ecbSig) (nm := "scratch") (e := .u64)
    (n := 179) (post := Spec.Sm4.ecbPost (specDirX86 dir) X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1452) (ecb_verified dir) (by decide) (by cases dir <;> decide +kernel)
    (by cases dir <;> decide +kernel) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.ecbPost_local _ _) (Proof.Sm4.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Sm4.X86
