module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Seed.Contract
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Seed.X86.Ecb
meta import VerifiedGarbage.Proof.Seed.X86.Ecb
public import VerifiedGarbage.Proof.Seed.X86.Lit
meta import VerifiedGarbage.Proof.Seed.X86.Lit
public import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Seed.X86.Lanes
meta import VerifiedGarbage.Proof.Seed.X86.Lanes
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Aes.X86.Sbox
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Seed.G16
import VerifiedGarbage.Proof.Seed.Memory
import VerifiedGarbage.Proof.Seed.X86.Crypt8
meta import VerifiedGarbage.Proof.Aes.X86.Sbox
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Linear
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Seed.G16
meta import VerifiedGarbage.Proof.Seed.Memory
meta import VerifiedGarbage.Proof.Seed.X86.Crypt8

/-!
# SEED ECB on x86 (32-bit) meets its contracts

`ecb_verified`: `ecb dir`, `vg_seed_encrypt_blocks` and
`vg_seed_decrypt_blocks` (`Proof.Seed.blocksContract`), is correct
(`ecb_wp`) and constant time, by the taint analysis, which starts with `esp`
public and knows which argument words are the base addresses of the data and
the scratch buffer: the pointers, `n` and what the code computes from them
are public, in registers or in the scratch buffer's slots, which the code
stores again after each store through another pointer.
-/

@[expose] public section

namespace VG.Proof.Seed.X86

open VG VG.X86 VG.Impl.Seed.X86
open VG.Proof.Seed (ecbX86)

/-- `ecbX86.pre`, by name. -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
  wr : s.wr = [⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 4 * Impl.Seed.X86.wsSlots⟩]
  dDB : Region.Disjoint ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Seed.X86.wsSlots⟩
  aD : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
  aB : Region.Disjoint ⟨argAddr s 0, 16⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Seed.X86.wsSlots⟩
  rD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 3).setWidth 64, 4 * Impl.Seed.X86.wsSlots⟩
  fD : (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32
  fB : (arg s 3).toNat + 4 * Impl.Seed.X86.wsSlots ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32

theorem EPre.of {dir : Spec.Seed.Direction} {s : State} (h : (ecbX86 dir).pre s) : EPre s := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9, -, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h5, h6, h7, h8, h9, h11, h12, h13⟩

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 4 * Impl.Seed.X86.wsSlots], argLen := 20,
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
    rintro r (rfl | rfl) <;> simp only [toNat_addr] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem ecbTaint_agree (dir : Spec.Seed.Direction) {s₁ s₂ : State} (h₁ : (ecbX86 dir).pre s₁) (h₂ : (ecbX86 dir).pre s₂)
    (hpub : (ecbX86 dir).pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
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

/-- What is public at the loop of rounds: the stack pointer, the round keys'
and the scratch buffer's pointers, the flags, and the slots of the caller's
`esi` and `ebp` and of the group's data pointer. -/
def roundsTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp, .esi, .edi], flags := true, lens := [0, 4 * Impl.Seed.X86.wsSlots],
    bases := [(.edi, 1, 0)],
    slots := [(1, 4 * (Impl.Seed.X86.savedSlot + 1), 4), (1, 4 * (Impl.Seed.X86.savedSlot + 3), 8)], argLen := 20,
    argBases := [(8, 0), (16, 1)] }

/-! The loop of rounds, which both directions run, analysed once, as a summary. -/

taint_summary roundsSum : VG.X86.taint roundsTaint (.block Impl.Seed.X86.roundPair)

theorem ecb_taint (dir : Spec.Seed.Direction) : ∃ h, (VG.X86.taint.check ecbTaint (ecb dir) h).isSome = true := by
  cases dir
  · native_taint_decide_sum [roundsSum]
  · native_taint_decide_sum [roundsSum]

theorem ecb_ct (dir : Spec.Seed.Direction) : ConstantTime isa (ecbX86 dir).pre (ecbX86 dir).pub (ecb dir) :=
  let ⟨_, h⟩ := ecb_taint dir
  VG.Taint.constantTime (A := VG.X86.taint) ecbTaint (fun _ _ h₁ h₂ hp => ecbTaint_agree dir h₁ h₂ hp) h

theorem ecb_correct (dir : Spec.Seed.Direction) (s : State) (hs : (ecbX86 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbX86 dir).post s s' :=
  ecb_wp dir hs

/-- `ecbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`ecb_verified` narrows to `ecbX86`). -/
def wideContract (dir : Spec.Seed.Direction) : Contract isa :=
  { ecbX86 dir with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 4 * Impl.Seed.X86.wsSlots⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [sched] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 4 * Impl.Seed.X86.wsSlots ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 4 * Impl.Seed.X86.wsSlots⟩]

tactic_template "narrow_seed_x86_verified" : tactic => `(tactic| simp only [VG.Proof.Seed.ecbX86, VG.Proof.Seed.X86.wideContract,
                     VG.Proof.Seed.X86.narrowRd, VG.Proof.Seed.X86.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])
tactic_template "narrow_seed_x86_verified" loc:Lean.Parser.Tactic.location : tactic => `(tactic| simp only [VG.Proof.Seed.ecbX86, VG.Proof.Seed.X86.wideContract,
                     VG.Proof.Seed.X86.narrowRd, VG.Proof.Seed.X86.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wide_pre (dir : Spec.Seed.Direction) (s : State) (h : (wideContract dir).pre s) :
    (ecbX86 dir).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow_seed_x86_verified
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
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 1088⟩, ⟨0x8004, 16⟩]

theorem wide_implies (dir : Spec.Seed.Direction) :
    (wideContract dir).Implies (Proof.Seed.blocksContract X86.abi dir) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Seed.X86.wsSlots] at h
    sig_split h
    sig_reduce [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Seed.X86.wsSlots]
    sig_simp [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Seed.X86.wsSlots] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Seed.X86.wsSlots]
  · sig_implies_pub [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Seed.X86.wsSlots]
  · sig_implies_sat [Proof.Seed.blocksContract, Proof.Seed.blocksSig, Spec.Seed.ecbPost, X86.abi,
      X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, Impl.Seed.X86.wsSlots]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ecb_verified (dir : Spec.Seed.Direction) :
    Verified X86.target (ecb dir) (Proof.Seed.blocksContract X86.abi dir) := by
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
    narrow_seed_x86_verified at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow_seed_x86_verified
    exact h

theorem encrypt_blocks_verified :
    Verified X86.target Impl.Seed.X86.encrypt (Proof.Seed.blocksContract X86.abi .encrypt) :=
  ecb_verified .encrypt

theorem decrypt_blocks_verified :
    Verified X86.target Impl.Seed.X86.decrypt (Proof.Seed.blocksContract X86.abi .decrypt) :=
  ecb_verified .decrypt

end VG.Proof.Seed.X86
