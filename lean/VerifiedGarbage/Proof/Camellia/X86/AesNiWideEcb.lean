module
public import VerifiedGarbage.Proof.Camellia.Scratch
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideModes
public import VerifiedGarbage.Proof.Camellia.X86.Scrub
public import VerifiedGarbage.Impl.Camellia.X86.AesNiWideEcb
public import VerifiedGarbage.Proof.Modes.X86.Ecb
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Proof.Framework.X86.ScrubSel
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiWideModes
meta import VerifiedGarbage.Proof.Camellia.X86.Scrub
meta import VerifiedGarbage.Impl.Camellia.X86.AesNiWideEcb
meta import VerifiedGarbage.Proof.Modes.X86.Ecb
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.Scrub
meta import VerifiedGarbage.Proof.Framework.X86.ScrubSel
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Impl.StackScratch.X86
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Camellia.CtrCipher
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# Camellia-ECB by the AES S-box on x86 (32-bit) meets its contract

`ecb_wp`: ECB for any core (`Proof.Modes.X86.ecbLevels_wp`) over Camellia's
core for four blocks (`coreSpec d`), with the working space, 107 64-bit
words, as a fifth argument (`ecbX86 d`): each block's
`Spec.Camellia.encryptBlock` or `decryptBlock` (`blocksAt_of_chunks`). It
is constant time by the taint analysis of its code (`X86.sseTaint`);
`ecb_framed` runs it with its working space on the stack, zeroed on return,
and `ecbEncrypt_scrubbed` and `ecbDecrypt_scrubbed` are the functions as
emitted (`Impl.Camellia.X86.AesNiWide.Fn`), which return without secret
residue (`X86.rtaint`), with seven doublewords of the stack zeroed, the
header of the frame and its last doubleword.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNiWide.Ecb

open VG VG.X86 VG.Impl.Camellia.X86.AesNiWide VG.Impl.Modes
open VG.Impl.Camellia.X86 (Dir)
open VG.Proof.Modes.X86 (EcbPre stkRegion ecbLevels_wp eScrR argAddr_eq)
open VG.Proof.Camellia (schedWords)
open VG.Proof.Camellia.X86.AesNiWide (coreSpec)

/-- ECB on x86 with its working space as the fifth argument, in the
direction `d`, and four bytes of stack below the return address. -/
def ecbX86 (d : Dir) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 107⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint scratch ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 8 * 107 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) ∧
    stk.Disjoint data ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧ 4 ≤ (s.gpr .esp).toNat ∧ stk.Disjoint sched
  post s s' :=
    Spec.Camellia.blocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      Spec.Camellia.ecb (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (specDir d)
        (Spec.Camellia.blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem scr_eq (d : Dir) (s : State) : eScrR s (core d) = ⟨(arg s 4).setWidth 64, 8 * 107⟩ := by
  simp [eScrR, core, Impl.Camellia.X86.AesNiWide.slots]

/-- `ecbX86`'s precondition gives the mode's. -/
theorem ecbPre_of {d : Dir} {s : State} (h : (ecbX86 d).pre s) : EcbPre (core d) s := by
  obtain ⟨hrd, hwr, -, dKS, dDS, dAD, dAS, dRD, dRS, fK, fD, fS, fE, hRn, sD, sS, sA, sE, sK⟩ := h
  have hL := (coreSpec d).layout
  refine ⟨(by rw [hrd]; simp [core]), fE, ⟨(by rw [hwr]; simp [core, Impl.Camellia.X86.AesNiWide.slots]),
      (by simp only [core, Impl.Camellia.X86.AesNiWide.slots]; omega)⟩, (by rw [hwr]; simp [core]),
    fD, ?_, ?_, ?_, dRD, ?_, ?_, ?_, ?_, sE, hL⟩
  · rw [scr_eq]; exact dDS
  · rw [scr_eq]; exact dAS
  · rw [scr_eq]; exact dRS
  · rw [Modes.stk_eq d sE]; exact sD
  · rw [Modes.stk_eq d sE]
    exact sS.sub_right (VG.Offset.sub_base _ (by simp only [core, Impl.Camellia.X86.AesNiWide.slots]; omega))
  · rw [Modes.stk_eq d sE]; exact sA
  · rw [Modes.stk_eq d sE]; exact Modes.stk_ret s

theorem keyArgs_of {d : Dir} {s : State} (h : (ecbX86 d).pre s) :
    AesNi.KeyArgs s [eScrR s (core d)]
      ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) := by
  obtain ⟨hrd, hwr, -, dKS, dDS, dAD, dAS, dRD, dRS, fK, fD, fS, fE, hRn, sD, sS, sA, sE, sK⟩ := h
  have inA : ∀ i < 5, InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Modes.X86.argOp i)) 4 := fun i hi =>
    ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, by
      rw [show s.ea (VG.Impl.Modes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 5) (by omega_using [fE]) hi]
      exact VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have subA : ∀ i < 5, Region.Sub ⟨s.ea (VG.Impl.Modes.X86.argOp i), 4⟩ ⟨argAddr s 0, 20⟩ := fun i hi => by
    rw [show s.ea (VG.Impl.Modes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 5) (by omega_using [fE]) hi]
    exact VG.Offset.sub_base _ (by omega_using [hi])
  have hstk : Proof.Modes.X86.stkRegion (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ :=
    Modes.stk_eq d sE
  refine ⟨arg s 0, inA 0 (by decide), rfl, inA 1 (by decide), ?_, hRn, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
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
  · rw [hstk]; exact sK
  · rw [hstk]; exact sA.sub_right (subA 0 (by decide))
  · rw [hstk]; exact sA.sub_right (subA 1 (by decide))

/-- The blocks, from their bytes: each the block function of the block it
was. -/
theorem blocksAt_of_chunks {m m' : Mem} {p : Addr} {n : Nat}
    {f : Spec.Camellia.Block → Spec.Camellia.Block}
    (h : Proof.Modes.chunksAt 16 m' p n = (Proof.Modes.chunksAt 16 m p n).map fun b =>
      (f (Vector.ofFn fun i : Fin 16 => b.getD i.val 0)).toList) :
    Spec.Camellia.blocksAt m' p n = (Spec.Camellia.blocksAt m p n).map f := by
  simp only [Proof.Modes.chunksAt, List.map_map] at h
  simp only [Spec.Camellia.blocksAt, List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have e := List.map_inj_left.mp h i hi
  simp only [Function.comp_apply] at e ⊢
  rw [Proof.Camellia.bytesAt_eq_blockAt, Proof.Camellia.bytesAt_eq_blockAt, Proof.Camellia.ofFn_toList,
    show (16 : Nat) * i = 16 * i from rfl] at e
  exact Vector.toList_inj.mp e

attribute [local irreducible] Spec.Camellia.encryptBlock Spec.Camellia.decryptBlock in
theorem ecb_wp (d : Dir) {s₀ : State} (hp : (ecbX86 d).pre s₀) :
    WP isa (ecb d) s₀ fun s' => abiPreserved s₀ s' ∧ (ecbX86 d).post s₀ s' :=
  WP.mono (ecbLevels_wp (coreSpec d) (gs := levels) (Modes.levels_fit d) (ecbPre_of hp) (keyArgs_of hp))
    fun s' ⟨h1, h2⟩ => ⟨h1, by
      show Spec.Camellia.blocksAt s'.mem ((arg s₀ 2).setWidth 64) (arg s₀ 3).toNat = Spec.Camellia.ecb _ _ _
      cases d
      · exact blocksAt_of_chunks (f := Spec.Camellia.encryptBlock _) h2
      · exact blocksAt_of_chunks (f := Spec.Camellia.decryptBlock _) h2⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def ecbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8 * 107], argLen := 24,
    argBases := [(12, 0), (20, 1)], room := 4 }

theorem ecbTaint_wf {d : Dir} {s : State} (hp : (ecbX86 d).pre s) : VG.X86.Taint.Wf ecbTaint s := by
  obtain ⟨hrd, hwr, -, dKS, dDS, dAD, dAS, dRD, dRS, fK, fD, fS, fE, hRn, sD, sS, sA, sE, sK⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [ecbTaint]; omega_using [fE], ?_⟩, ?_⟩ fun _ => ⟨sE, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨dDS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [fE]) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [fE]) dRS dAS
  · intro p hp'
    simp only [ecbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact sD
    · exact sS

theorem ecbTaint_agree {d : Dir} {s₁ s₂ : State} (h₁ : (ecbX86 d).pre s₁) (h₂ : (ecbX86 d).pre s₂)
    (hpub : (ecbX86 d).pub s₁ s₂) : VG.X86.Taint.Agree ecbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, fE₁, -, -, -, -, -, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, fE₂, -, -, -, -, -, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, ecbTaint_wf h₁, ecbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [ecbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 2 (by omega_using []), ha 3 (by omega_using []), ha 4 (by omega_using [])]
  · simp only [ecbTaint] at hk
    rw [show VG.X86.Taint.depth ecbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (ha _ (by omega_using [hk]))

theorem ecb_ct (d : Dir) : ConstantTime isa (ecbX86 d).pre (ecbX86 d).pub (ecb d) := by
  obtain ⟨_, h⟩ : ∃ h, (VG.X86.sseTaint.check ecbTaint (ecb d) h).isSome = true := by
    cases d <;> exact ⟨_, by taint_decide⟩
  exact VG.Taint.constantTime (A := VG.X86.sseTaint) ecbTaint (fun _ _ h₁ h₂ hp => ecbTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

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
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 856⟩]

theorem ecb_verified (d : Dir) :
    Verified X86.target (ecb d) (Proof.Camellia.ecbScratchContract X86.abi (specDir d) 107 4) :=
  Verified.of_correct (fun _ hs => ecb_wp d hs) (ecb_ct d) (by
    cases d <;>
    sig_implies [Proof.Camellia.ecbScratchContract, Proof.Camellia.ecbScratchSig, Spec.Camellia.ecbSig,
      Spec.Camellia.ecbPre, Proof.Camellia.ecbPostSk, ecbX86, specDir, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState)

/-- A state satisfying the ECB functions' precondition: the schedule at
`0x1000`, 18 rounds and no blocks at `0x2000`, as stack arguments at
`0x8004`. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 18 else if a = 0x800D then 0x20 else 0
  rd := [⟨0x1000, 272⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x2000, 0⟩]

theorem frameSat_pre (d : Spec.Camellia.Direction) :
    ∃ s, (Proof.Camellia.ecbContractSk X86.abi d 888).pre s := by
  implies_sat [Proof.Camellia.ecbContractSk, Spec.Camellia.ecbSig, Spec.Camellia.ecbPre, Proof.Camellia.ecbPostSk,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes] [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using frameSat

/-- ECB in the direction `d`, with its working space on the stack. -/
theorem ecb_framed (d : Dir) :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 884 4 214 (ecb d))
      (Spec.Camellia.ecbContract X86.abi (specDir d) 888) :=
  Proof.Camellia.ecb_of_sk <|
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.ecbSig) (nm := "scratch") (e := .u64)
    (n := 107) (pre := Spec.Camellia.ecbPre X86.abi.ptrBits)
    (post := Proof.Camellia.ecbPostSk (specDir d) X86.abi.ptrBits) (wa := false) (stack := 4)
    (bytes := 884) (by rw [← Proof.Camellia.ecbScratchContract_eq]; exact ecb_verified d)
    (by decide) (by cases d <;> lit_decide) (by cases d <;> lit_decide) (by decide)
    (Proof.Camellia.ecbPre_local _) (Proof.Camellia.ecbPost_local _ _)
    (Proof.Camellia.ecbPostOut_local _ _) (frameSat_pre _)

/-! ## The functions as emitted -/

open VG.X86.Scrub in
/-- `Spec.Camellia.ecbEncryptApi` as emitted (`Impl.Camellia.X86.AesNiWide.Fn.ecbEncrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNiWide.Fn.ecbEncrypt
      (Spec.Camellia.ecbContract X86.abi .encrypt 888) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ecbEncryptApi) (W := 888)
    { code := Impl.StackScratch.X86.withStackScratchWiped 884 4 214 (ecb .encrypt)
      verified := ecb_framed .encrypt }
    Impl.Camellia.X86.AesNiWide.Fn.ecbWords (Proof.Camellia.X86.Scrub.ecbOut _ _) (by decide)
    ⟨_, by taint_decide_ct⟩

open VG.X86.Scrub in
/-- `Spec.Camellia.ecbDecryptApi` as emitted (`Impl.Camellia.X86.AesNiWide.Fn.ecbDecrypt`) meets
its contract in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed X86.target Impl.Camellia.X86.AesNiWide.Fn.ecbDecrypt
      (Spec.Camellia.ecbContract X86.abi .decrypt 888) 0 :=
  verifiedScrubbedSel (api := Spec.Camellia.ecbDecryptApi) (W := 888)
    { code := Impl.StackScratch.X86.withStackScratchWiped 884 4 214 (ecb .decrypt)
      verified := ecb_framed .decrypt }
    Impl.Camellia.X86.AesNiWide.Fn.ecbWords (Proof.Camellia.X86.Scrub.ecbOut _ _) (by decide)
    ⟨_, by taint_decide_ct⟩

end VG.Proof.Camellia.X86.AesNiWide.Ecb
