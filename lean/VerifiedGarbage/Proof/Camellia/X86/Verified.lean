module

public import VerifiedGarbage.Proof.Camellia.X86.Ecb
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Camellia.X86.Lit
import VerifiedGarbage.Proof.Camellia.X86.CallSum
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.X86.Ecb
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Camellia.X86.Lit
meta import VerifiedGarbage.Proof.Camellia.X86.CallSum
import VerifiedGarbage.Proof.Camellia.X86.CallSum
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Camellia ECB on x86 (32-bit) meets its contracts

`ecb_verified`: `ecb dir` is correct (`ecb_wp`) and constant time, by the
taint analysis, which starts with `esp` public and knows which argument
words are the base addresses of the data and the scratch buffer, and that
the 16 bytes below the stack pointer, where the calls of
`vg_camellia_crypt_prepared` push their frames, are apart from them: the
pointers, `rounds`, `n` and what the code computes from them are public, in
registers or in the scratch buffer's slots, which the code stores again
after each store through another pointer. The analysis of the call is a
summary (`ecbCallSum`). `ecb_framed` runs it with its working space on the
stack, zeroed on return: 2712 bytes, the 2688 of the scratch buffer, the
copies of the four argument slots, the buffer's address and the return
address of the call of the code, below which its calls use 16 bytes more.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.Impl.Camellia.X86

/-- `ecbX86.pre`, by name. -/
structure EPre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 0).setWidth 64, 272⟩, ⟨argAddr s 0, 20⟩]
  wr : s.wr = [⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩, ⟨(arg s 4).setWidth 64, 4 * Impl.Camellia.X86.slots⟩]
  dDB : Region.Disjoint ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    ⟨(arg s 4).setWidth 64, 4 * Impl.Camellia.X86.slots⟩
  aD : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
  aB : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 4).setWidth 64, 4 * Impl.Camellia.X86.slots⟩
  rD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
  rB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 4 * Impl.Camellia.X86.slots⟩
  fD : (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32
  fB : (arg s 4).toNat + 4 * Impl.Camellia.X86.slots ≤ 2 ^ 32
  fSp : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  sD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩
    ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
  sB : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩
    ⟨(arg s 4).setWidth 64, 4 * Impl.Camellia.X86.slots⟩
  s16 : 16 ≤ (s.gpr .esp).toNat

theorem EPre.of {dir : Dir} {s : State} (h : (ecbX86 dir).pre s) : EPre s := by
  obtain ⟨h1, h2, -, -, h5, h6, h7, h8, h9, -, h11, h12, h13, -, h15, h16, -, h18⟩ := h
  exact ⟨h1, h2, h5, h6, h7, h8, h9, h11, h12, h13, h15, h16, h18⟩

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 4 * Impl.Camellia.X86.slots], argLen := 24,
    argBases := [(12, 0), (20, 1)], room := 16 }

theorem ecbTaint_wf {s : State} (hp : EPre s) : VG.X86.Taint.Wf ecbTaint s := by
  have hD := hp.fD; have hB := hp.fB; have hs := hp.fSp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ecbTaint]; omega, ?_⟩, ?_⟩ fun _ => ⟨hp.s16, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.dDB, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [setWidth_toNat] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rD hp.aD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.rB hp.aB
  · intro p hp'
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.sD
    · exact hp.sB

theorem ecbTaint_agree (dir : Dir) {s₁ s₂ : State} (h₁ : (ecbX86 dir).pre s₁) (h₂ : (ecbX86 dir).pre s₂)
    (hpub : (ecbX86 dir).pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := EPre.of h₁; have hp₂ := EPre.of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf hp₁, ecbTaint_wf hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr, ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) hp₁.fSp h4 hk, VG.X86.Taint.argByte_eq (n := 24) hp₂.fSp h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ecb_taint (dir : Dir) : ∃ h, (VG.X86.taint.check ecbTaint (ecb dir) h).isSome = true := by
  cases dir
  · native_taint_decide_sum [ecbCallSum]
  · native_taint_decide_sum [ecbCallSum]

theorem ecb_ct (dir : Dir) : ConstantTime isa (ecbX86 dir).pre (ecbX86 dir).pub (ecb dir) :=
  let ⟨_, h⟩ := ecb_taint dir
  VG.Taint.constantTime (A := VG.X86.taint) ecbTaint (fun _ _ h₁ h₂ hp => ecbTaint_agree dir h₁ h₂ hp) h

theorem ecb_correct (dir : Dir) (s : State) (hs : (ecbX86 dir).pre s) :
    ∃ t s', Exec isa (ecb dir) s t s' ∧ abiPreserved s s' ∧ (ecbX86 dir).post s s' :=
  ecb_wp dir hs

/-- Memory holding the arguments `0x1000, 18, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 18 else if a = 0x800D then 0x30 else
    if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x8004, 20⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 2688⟩]

theorem ecb_verified (dir : Dir) :
    Verified X86.target (ecb dir) (Proof.Camellia.ecbScratchContract X86.abi (specDir dir) 336 16) :=
  Verified.of_correct (ecb_correct dir) (ecb_ct dir) (by
    cases dir <;>
    sig_implies [Proof.Camellia.ecbScratchContract, Proof.Camellia.ecbScratchSig, Spec.Camellia.ecbSig,
      Spec.Camellia.ecbPre, Spec.Camellia.ecbPost, ecbX86, specDir, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes, Impl.Camellia.X86.slots, Impl.Camellia.X86.grpSlot, Impl.Camellia.X86.nSlot,
      Impl.Camellia.X86.dSlot, Impl.Camellia.X86.savedSlot, Impl.Camellia.X86.keySlot, Impl.Camellia.X86.tailSlot]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, 18 rounds and no blocks at `0x2000`, as stack arguments at
`0x8004`. -/
def ecbFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 18 else if a = 0x800D then 0x20 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 0⟩]

theorem ecbFrameSat_pre (d : Spec.Camellia.Direction) :
    ∃ s, (Spec.Camellia.ecbContract X86.abi d 2728).pre s := by
  implies_sat [Spec.Camellia.ecbContract, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Spec.Camellia.ecbPost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [ecbFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using ecbFrameSat

/-- ECB in the direction `dir`, with its working space on the stack. -/
theorem ecb_framed (dir : Dir) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2712 4 672 (ecb dir))
      (Spec.Camellia.ecbContract X86.abi (specDir dir) 2728) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.ecbSig) (nm := "scratch") (e := .u64)
    (n := 336) (pre := Spec.Camellia.ecbPre X86.abi.ptrBits)
    (post := Spec.Camellia.ecbPost (specDir dir) X86.abi.ptrBits) (wa := false) (stack := 16)
    (bytes := 2712) (by rw [← Proof.Camellia.ecbScratchContract_eq]; exact ecb_verified dir)
    (by decide) (by cases dir <;> lit_decide) (by cases dir <;> lit_decide) (by decide)
    (Proof.Camellia.ecbPre_local _) (Proof.Camellia.ecbPost_local _ _)
    (Proof.Camellia.ecbPostOut_local _ _) (ecbFrameSat_pre _)

end VG.Proof.Camellia.X86
