import VerifiedGarbage.Proof.Idea.X86.Ecb
import VerifiedGarbage.Proof.Idea.X86.Lit
import VerifiedGarbage.Proof.Idea.Local
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Verified IDEA on x86 (32-bit), with its working space on the stack

`ecb_verified`: `ecb` is correct (`ecb_wp`) and constant time, by the taint
analysis, which starts with `esp` public and knows which argument words are
the base addresses of the data and the scratch buffer: the pointers, `n` and
what the code computes from them are public, in registers or in the scratch
buffer's slots, which the code reads again after each store through another
pointer.

`ecb_framed` runs it with its working space on the stack (152 bytes: the
132 of the buffer, the copies of the three argument slots, the buffer's
address and the return address of the call of the code), zeroing the copy
of the subkeys and the spilled word of the block (`wipedWords`) on return.
`invertKey_framed` keeps the four registers `invertKey` saves in a frame of
32 bytes, which only ever holds the caller's registers and is not zeroed.
-/

namespace VG.Proof.Idea.X86

open VG VG.X86 VG.Impl.Idea.X86

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 4 * Impl.Idea.X86.slots], argLen := 20,
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
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> rw [Nat.mod_eq_of_lt (by omega)] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem ecbTaint_agree {s₁ s₂ : State} (h₁ : ecbContract.pre s₁) (h₂ : ecbContract.pre s₂)
    (hpub : ecbContract.pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := EPre.of h₁; have hp₂ := EPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf hp₁, ecbTaint_wf hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr, ha 1 (by omega), ha 2 (by omega), ha 3 (by omega)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 20) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ecb_constantTime : ConstantTime isa ecbContract.pre ecbContract.pub ecb :=
  VG.Taint.constantTime (A := taint) ecbTaint (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def ecbSatState : State where
  gpr r := if r = .esp then 0x4000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0
  rd := [⟨0x1000, 104⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x3000, 132⟩]

theorem ecb_verified : Verified target ecb (Proof.Idea.ecbScratchContract32 abi Impl.Idea.X86.slots) := by
  refine Verified.of_correct ecb_wp ecb_constantTime ?_
  sig_implies [Proof.Idea.ecbScratchContract32, Proof.Idea.ecbScratchSig32,
    Spec.Idea.ecbPost, abi, argSlots, argVal, argBytes, ecbContract, Impl.Idea.X86.slots]
    [ecbSatState, arg, argAddr, Mem.readW, Mem.read] using ecbSatState

/-- The copy of the subkeys and the spilled word of the block: the part of
the scratch buffer that may hold secrets. -/
abbrev wipedWords : Nat := 27

/-- A state satisfying the ECB precondition without the scratch buffer: the
arguments `0x1000, 0x2000, 0` at `0x4004`. -/
def ecbFrameSat : State := { ecbSatState with rd := [⟨0x1000, 104⟩, ⟨0x4004, 12⟩], wr := [⟨0x2000, 0⟩] }

theorem ecbFrameSat_pre : ∃ s, (Spec.Idea.ecbContract X86.abi 152).pre s := by
  implies_sat [Spec.Idea.ecbContract, Spec.Idea.ecbSig, Spec.Idea.ecbPost, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes] [ecbFrameSat, ecbSatState, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using ecbFrameSat

theorem ecb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 152 3 wipedWords ecb)
      (Spec.Idea.ecbContract X86.abi 152) :=
  X86.Verified.stackScratchWiped (sig := Spec.Idea.ecbSig) (nm := "scratch") (e := .u32)
    (n := Impl.Idea.X86.slots) (post := Spec.Idea.ecbPost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 152) ecb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.ecbPost_local _) (Proof.Idea.ecbPostOut_local _) ecbFrameSat_pre

/-- A state satisfying the inversion's precondition without the scratch
buffer: the arguments `0x1000, 0x2000` at `0x4004`. -/
def invertFrameSat : State := { invSatState with rd := [⟨0x1000, 104⟩, ⟨0x4004, 8⟩], wr := [⟨0x2000, 104⟩] }

theorem invertFrameSat_pre : ∃ s, (Spec.Idea.invertKeyContract X86.abi 32).pre s := by
  implies_sat [Spec.Idea.invertKeyContract, Spec.Idea.invertKeySig, Spec.Idea.invertKeyPost, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes]
    [invertFrameSat, invSatState, X86.arg, X86.argAddr, Mem.readW, Mem.read] using invertFrameSat

theorem invertKey_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 32 2 invertKey)
      (Spec.Idea.invertKeyContract X86.abi 32) :=
  X86.Verified.stackScratch (sig := Spec.Idea.invertKeySig) (nm := "scratch") (e := .u32) (n := 4)
    (post := Spec.Idea.invertKeyPost X86.abi.ptrBits) (wa := false) (stack := 0) (bytes := 32)
    invertKey_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Idea.invertKeyPost_local _) invertFrameSat_pre

end VG.Proof.Idea.X86
