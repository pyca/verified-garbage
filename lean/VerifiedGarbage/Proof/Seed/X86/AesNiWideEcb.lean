module
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Seed.Scratch
public import VerifiedGarbage.Proof.Seed.X86.AesNiWideCore
public import VerifiedGarbage.Impl.Seed.X86.AesNiWideEcb
public import VerifiedGarbage.Proof.Modes.X86.Ecb
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Seed.Scratch
meta import VerifiedGarbage.Proof.Seed.X86.AesNiWideCore
meta import VerifiedGarbage.Impl.Seed.X86.AesNiWideEcb
meta import VerifiedGarbage.Proof.Modes.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Seed.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# SEED-ECB by the AES S-box on x86 (32-bit) meets its contract

`ecb_wp`: ECB for any core (`Proof.Modes.X86.ecbLevels_wp`) over SEED's core
for four blocks (`coreSpec d`), with the working space, 89 64-bit words, as
a fourth argument (`ecbX86 d`): each block's `Spec.Seed.encryptBlock` or
`decryptBlock` (`blocksAt_of_chunks`). It is constant time by the taint
analysis of its code (`X86.sseTaint`); `ecb_framed` runs it with its working
space on the stack, zeroed on return, and `ecbEncrypt_scrubbed` and
`ecbDecrypt_scrubbed` are the functions as emitted
(`Impl.Seed.X86.AesNiWide.Fn`), which return without secret residue
(`X86.rtaint`), with five doublewords of the stack zeroed, the header of the
frame.
-/

@[expose] public section

namespace VG.Proof.Seed.X86.AesNiWide.Ecb

open VG VG.X86 VG.Impl.Seed.X86.AesNiWide VG.Impl.Modes
open VG.Spec.Seed (Direction)
open VG.Proof.Modes.X86 (EcbPre stkRegion ecbLevels_wp eScrR)
open VG.Proof.Seed (dirCipher)
open VG.Proof.Seed.X86.AesNiWide (coreSpec)

/-- ECB on x86 with its working space as the fourth argument, in the
direction `d`. -/
def ecbX86 (d : Direction) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8 * 89⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 4
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧
    (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8 * 89 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 4 ≤ (s.gpr .esp).toNat
  post s s' :=
    Spec.Seed.blocksAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      Spec.Seed.ecb (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) d
        (Spec.Seed.blocksAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

theorem scr_eq (d : Direction) (s : State) : eScrR s (core d) = ⟨(arg s 3).setWidth 64, 8 * 89⟩ := by
  simp [eScrR, core, Impl.Seed.X86.AesNiWide.slots]

/-- The four bytes of stack below `esp` are apart from the arguments and the return address. -/
theorem stk_apart {s : State} (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) (hlo : 4 ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨argAddr s 0, 16⟩ ∧
      Region.Disjoint (stkRegion (s.gpr .esp) 4) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  have e : (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega_arith)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 4) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

/-- `ecbX86`'s precondition gives the mode's. -/
theorem ecbPre_of {d : Direction} {s : State} (h : (ecbX86 d).pre s) : EcbPre (core d) s := by
  obtain ⟨hrd, hwr, dKS, dDS, dAD, dAS, dRD, dRS, -, dSD, dSS, fK, fD, fS, fE, fLo⟩ := h
  have hL := (coreSpec d).layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp [core]), fE, ⟨(by rw [hwr]; simp [core, Impl.Seed.X86.AesNiWide.slots]),
      (by simp only [core, Impl.Seed.X86.AesNiWide.slots]; omega_arith)⟩, (by rw [hwr]; simp [core]),
    fD, ?_, ?_, ?_, dRD, dSD, ?_, sA, sR, (by simp only [core]; omega_arith), hL⟩
  · rw [scr_eq]; exact dDS
  · rw [scr_eq]; exact dAS
  · rw [scr_eq]; exact dRS
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [core, Impl.Seed.X86.AesNiWide.slots]; omega_arith))

theorem keyArgs_of {d : Direction} {s : State} (h : (ecbX86 d).pre s) :
    AesNi.KeyArgs s [eScrR s (core d)] (Spec.Seed.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, dKS, -, -, dAS, -, -, dSK, -, -, fK, -, -, fE, fLo⟩ := h
  obtain ⟨sA, -⟩ := stk_apart fE fLo
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 16⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK, fun r hr => ?_,
    fun r hr => ?_, dSK, sA.sub_right (Region.sub_prefix (by decide))⟩
  · show (⟨argAddr s 0, 16⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_arith
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))

private theorem ofFn_toList (v : Spec.Seed.Block) : (Vector.ofFn fun i : Fin 16 => v.toList.getD i.val 0) = v := by
  apply Vector.ext; intro i hi
  simp

/-- The blocks, from their bytes: each the block function of the block it
was. -/
theorem blocksAt_of_chunks {m m' : Mem} {p : Addr} {n : Nat} {f : Spec.Seed.Block → Spec.Seed.Block}
    (h : Proof.Modes.chunksAt 16 m' p n = (Proof.Modes.chunksAt 16 m p n).map fun b =>
      (f (Vector.ofFn fun i : Fin 16 => b.getD i.val 0)).toList) :
    Spec.Seed.blocksAt m' p n = (Spec.Seed.blocksAt m p n).map f := by
  simp only [Proof.Modes.chunksAt, List.map_map] at h
  simp only [Spec.Seed.blocksAt, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have e := List.map_inj_left.mp h i hi
  simp only [Function.comp_apply] at e ⊢
  rw [Proof.Seed.bytesAt_eq, Proof.Seed.bytesAt_eq, ofFn_toList, show (16 : Nat) * i = 16 * i from rfl] at e
  exact Vector.toList_inj.mp e

theorem levels_fit (d : Direction) : Proof.Modes.X86.LevelsFit (core d) levels := by
  intro g hg
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact ⟨by decide, by show _ ≤ 4; decide⟩

theorem ecb_wp (d : Direction) {s₀ : State} (hp : (ecbX86 d).pre s₀) :
    WP isa (ecb d) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 d).post s₀ s' :=
  WP.mono (ecbLevels_wp (coreSpec d) (gs := levels) (levels_fit d) (ecbPre_of hp) (keyArgs_of hp))
    fun s' ⟨h1, h2⟩ => ⟨h1, by
      show Spec.Seed.blocksAt s'.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat = Spec.Seed.ecb _ _ _
      have e : (coreSpec d).cipher (Spec.Seed.scheduleAt s₀.mem ((arg s₀ 0).setWidth 64)) =
          dirCipher d (Spec.Seed.scheduleAt s₀.mem ((arg s₀ 0).setWidth 64)) := rfl
      rw [e] at h2
      cases d
      · exact blocksAt_of_chunks (f := Spec.Seed.encryptBlock _) h2
      · exact blocksAt_of_chunks (f := Spec.Seed.decryptBlock _) h2⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8 * 89], argLen := 20,
    argBases := [(8, 0), (16, 1)], room := 4 }

theorem ecbTaint_wf {d : Direction} {s : State} (hp : (ecbX86 d).pre s) : VG.X86.Taint.Wf ecbTaint s := by
  obtain ⟨hrd, hwr, dKS, dDS, dAD, dAS, dRD, dRS, -, dSD, dSS, fK, fD, fS, fE, fLo⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ecbTaint]; omega_arith, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨dDS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_arith) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_arith) dRS dAS
  · intro p hp'
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨fLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 =
        (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 := (VG.X86.Taint.sub_setWidth fLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dSD
    · exact dSS

theorem ecbTaint_agree {d : Direction} {s₁ s₂ : State} (h₁ : (ecbX86 d).pre s₁) (h₂ : (ecbX86 d).pre s₂)
    (hpub : (ecbX86 d).pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf h₁, ecbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 1 (by omega_arith), ha 2 (by omega_arith), ha 3 (by omega_arith)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 20) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 20) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_arith)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_arith))]
    exact congrArg _ (ha _ (by omega_arith))

theorem ecb_ct (d : Direction) : ConstantTime isa (ecbX86 d).pre (ecbX86 d).pub (ecb d) := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.sseTaint.check ecbTaint (ecb d) h).isSome = true := by
    cases d <;> exact ⟨_, by taint_decide⟩
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) ecbTaint (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

/-- `ecbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`ecb_verified` narrows to `ecbX86`). -/
def wideContract (d : Direction) : Contract isa :=
  { ecbX86 d with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let data : Region := ⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 8 * 89⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 4
      s.rd = [sched] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 16 * (arg s 2).toNat ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8 * 89 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ 4 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 16⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 16 * (arg s 2).toNat⟩, ⟨(arg s 3).setWidth 64, 8 * 89⟩]

tactic_template "seed_aesni_wide_ecb_narrow" : tactic =>
  `(tactic| simp only [VG.Proof.Seed.X86.AesNiWide.Ecb.ecbX86, VG.Proof.Seed.X86.AesNiWide.Ecb.wideContract,
                     VG.Proof.Seed.X86.AesNiWide.Ecb.narrowRd, VG.Proof.Seed.X86.AesNiWide.Ecb.narrowWr,
                     VG.X86.arg_withRegions, VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr,
                     VG.X86.State.withRegions_mem, VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

tactic_template "seed_aesni_wide_ecb_narrow" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| simp only [VG.Proof.Seed.X86.AesNiWide.Ecb.ecbX86, VG.Proof.Seed.X86.AesNiWide.Ecb.wideContract,
                     VG.Proof.Seed.X86.AesNiWide.Ecb.narrowRd, VG.Proof.Seed.X86.AesNiWide.Ecb.narrowWr,
                     VG.X86.arg_withRegions, VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr,
                     VG.X86.State.withRegions_mem, VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wide_pre (d : Direction) (s : State) (h : (wideContract d).pre s) :
    (ecbX86 d).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  seed_aesni_wide_ecb_narrow
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
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 712⟩, ⟨0x8004, 16⟩]

theorem wide_implies (d : Direction) :
    (wideContract d).Implies (Proof.Seed.ecbScratchContract X86.abi d 89 4) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below] at h
    sig_split h
    sig_reduce [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega_arith
      | (rw [VG.X86.Taint.sub_setWidth (by omega_arith)]; try simp only [Nat.mul_comm] at *
         first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
  · sig_implies_pub [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
  · sig_implies_sat [Proof.Seed.ecbScratchContract, Proof.Seed.ecbScratchSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, ecbX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem ecb_verified (d : Direction) :
    Verified X86.target (ecb d) (Proof.Seed.ecbScratchContract X86.abi d 89 4) := by
  have hsat := (wide_implies d).sat_left
  have narrowSat : ∃ s, (ecbX86 d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre d s hs⟩
  apply Verified.of_implies _ (wide_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (fun _ hs => ecb_wp d hs) (ecb_ct d) (.refl narrowSat))
    narrowRd narrowWr (wide_pre d) ?_ ?_ ?_ ?_ hsat
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
    seed_aesni_wide_ecb_narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    seed_aesni_wide_ecb_narrow
    exact h

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000` and no blocks at `0x2000`, as stack arguments at `0x8004`, which
are writable. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 0⟩, ⟨0x8004, 12⟩]

theorem frameSat_pre (d : Direction) : ∃ s, (Spec.Seed.ecbContract X86.abi d 736).pre s := by
  implies_sat [Spec.Seed.ecbContract, Spec.Seed.ecbSig, Spec.Seed.ecbPost, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

/-- ECB in the direction `d`, with its working space on the stack. -/
theorem ecb_framed (d : Direction) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 732 3 178 (ecb d))
      (Spec.Seed.ecbContract X86.abi d 736) :=
  X86.Verified.stackScratchWiped (sig := Spec.Seed.ecbSig) (nm := "scratch") (e := .u64)
    (n := 89) (post := Spec.Seed.ecbPost d X86.abi.ptrBits) (wa := true) (stack := 4)
    (bytes := 732) (ecb_verified d) (by decide) (by cases d <;> lit_decide)
    (by cases d <;> lit_decide) (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Seed.ecbPost_local _ _) (Proof.Seed.ecbPostOut_local _ _) (frameSat_pre _)

/-! ## The functions as emitted -/

open VG.X86.Scrub in
theorem ecbOut (d : Direction) (stack : Nat) :
    PostOut (Spec.Seed.ecbContract X86.abi d stack) (Spec.Seed.ecbSig.retBits 32) :=
  postOut_of_local ScrubAbi.plain (Proof.Seed.ecbPostOut_local _ d)

open VG.X86.Scrub in
/-- `Spec.Seed.ecbEncryptApi` as emitted (`Impl.Seed.X86.AesNiWide.Fn.ecbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNiWide.Fn.ecbEncrypt
      (Spec.Seed.ecbContract X86.abi .encrypt 736) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ecbEncryptApi) (W := 736)
    { code := Impl.StackScratch.X86.withStackScratchWiped 732 3 178 (ecb .encrypt)
      verified := ecb_framed .encrypt }
    Impl.Seed.X86.AesNiWide.Fn.ecbWords (ecbOut _ _) (by decide) ⟨_, by taint_decide_ct⟩

open VG.X86.Scrub in
/-- `Spec.Seed.ecbDecryptApi` as emitted (`Impl.Seed.X86.AesNiWide.Fn.ecbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Seed.X86.AesNiWide.Fn.ecbDecrypt
      (Spec.Seed.ecbContract X86.abi .decrypt 736) 0 :=
  verifiedScrubbedSel (api := Spec.Seed.ecbDecryptApi) (W := 736)
    { code := Impl.StackScratch.X86.withStackScratchWiped 732 3 178 (ecb .decrypt)
      verified := ecb_framed .decrypt }
    Impl.Seed.X86.AesNiWide.Fn.ecbWords (ecbOut _ _) (by decide) ⟨_, by taint_decide_ct⟩

end VG.Proof.Seed.X86.AesNiWide.Ecb
