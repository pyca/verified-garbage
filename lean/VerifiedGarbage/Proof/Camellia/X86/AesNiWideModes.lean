module
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Camellia.FbScratch
meta import VerifiedGarbage.Proof.Camellia.FbScratch
public import VerifiedGarbage.Proof.Camellia.CbcScratch
public import VerifiedGarbage.Proof.Camellia.CtrScratch
meta import VerifiedGarbage.Proof.Camellia.CbcScratch
meta import VerifiedGarbage.Proof.Camellia.CtrScratch
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiWideLit
public import VerifiedGarbage.Proof.Camellia.X86.AesNiWideCore
meta import VerifiedGarbage.Proof.Camellia.X86.AesNiWideCore
public import VerifiedGarbage.Impl.Camellia.X86.AesNiWide
meta import VerifiedGarbage.Impl.Camellia.X86.AesNiWide
public import VerifiedGarbage.Proof.Modes.X86.Wide
meta import VerifiedGarbage.Proof.Modes.X86.Wide
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Modes.X86.Seq
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Camellia's wide modes by the AES S-box on x86 (32-bit) meet their contracts

`cbcDecryptChained_wp`, `cfbDecrypt_wp`, `ctr_wp_x86`: CBC decryption,
CFB128 decryption and CTR by groups of four and two blocks, then one at a
time (`Proof.Modes.X86.cbcDecLevels_wp`, `cfbDecLevels_wp`, `ctrLevels_wp`),
over Camellia's core for four blocks (`coreSpec`), with the working space,
107 64-bit words, as a sixth argument (`fbX86`). The four bytes below `esp`,
where the core gets its tables' addresses, are apart from the schedule as
from the other buffers. Each is constant time by the taint analysis of its
code (`X86.sseTaint`); the `_framed` theorems run them with their working
space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86.AesNiWide.Modes

open VG VG.X86 VG.Impl.Camellia.X86.AesNiWide VG.Impl.Modes
open VG.Impl.Camellia.X86 (Dir)
open VG.Proof.Modes.X86 (SeqPre cbcDecLevels_wp cfbDecLevels_wp ctrLevels_wp argAddr_eq)
open VG.Proof.Camellia.X86.AesNiWide (coreSpec)
open VG.Proof.Camellia (schedWords)

theorem scr_eq (d : Dir) (s : State) : Modes.X86.scrR s (core d) = ⟨(arg s 5).setWidth 64, 8 * 107⟩ := by
  simp [Modes.X86.scrR, core, Impl.Camellia.X86.AesNiWide.slots]

/-- Camellia under the schedule at the first argument, with the number of rounds in the second. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m ((arg s 2).setWidth 64) 16
/-- The data. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m ((arg s 3).setWidth 64) (arg s 4).toNat

/-- Camellia's inverse under the schedule at the first argument. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.invCipher (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)

/-- The functions' postconditions. -/
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ctrPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ctr.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ctr.next (ivAt s.mem s) (arg s 4).toNat

/-- A mode on x86 with its working space as the sixth argument, and
the postcondition `post`. -/
def fbX86 (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * 107⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩
    s.rd = [sched, args] ∧ s.wr = [data, iv, scratch] ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * 107 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) ∧
    stk.Disjoint data ∧ stk.Disjoint iv ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧ stk.Disjoint sched ∧
    4 ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- The core's four bytes of stack, as the contracts write them. -/
theorem stk_eq (d : Dir) {s : State} (h : 4 ≤ (s.gpr .esp).toNat) :
    Proof.Modes.X86.stkRegion (Proof.Modes.X86.E s) (core d).stack =
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
  show (⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region) = _
  rw [VG.X86.Taint.sub_setWidth h]

/-- The stack below the return address is apart from it. -/
theorem stk_ret (s : State) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ ⟨(s.gpr .esp).setWidth 64, 4⟩ :=
  (VG.Offset.base_disjoint_below _ (by decide)).symm

/-- The modes' slots are in the scratch buffer. -/
theorem modeSlots_sub (d : Dir) (S : BitVec 32) :
    Region.Sub ⟨Proof.Modes.X86.slotA S (core d).slots, 40⟩ ⟨S.setWidth 64, 8 * 107⟩ :=
  VG.Offset.sub_base _ (by simp only [core, Impl.Camellia.X86.AesNiWide.slots]; omega_using [])

/-- `fbX86`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (d : Dir) (hstep : M.step = 16) {s : State}
    (h : (fbX86 post).pre s) : SeqPre (core d) M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, hRn, sD, sV, sS, sA, sK,
    sE⟩ := h
  have hL := (coreSpec d).layout
  refine ⟨(by rw [hrd]; simp [core]), fE, ⟨(by rw [hwr]; simp [core, Impl.Camellia.X86.AesNiWide.slots]),
      (by simp only [core, Impl.Camellia.X86.AesNiWide.slots]; omega)⟩, (by rw [hwr]; simp [core]),
    (fun _ => by rw [hwr]; simp [core]), (by simp only [core]; omega), (by rw [hwr, hstep]; simp [core]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => ?_), ?_, ?_, ?_, ?_, sE, (by rw [hstep]; simp [core]), hL⟩
  · rw [hstep, scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · rw [hstep]; exact dVD
  · rw [scr_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scr_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dRV
  · rw [stk_eq d sE, hstep]; exact sD
  · rw [stk_eq d sE]; exact sS.sub_right (modeSlots_sub d _)
  · rw [stk_eq d sE]; exact sA
  · rw [stk_eq d sE]; exact stk_ret s

theorem keyArgs_of {post : State → State → Prop} (d : Dir) {s : State} (h : (fbX86 post).pre s) :
    AesNi.KeyArgs s [Modes.X86.scrR s (core d)]
      ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) := by
  obtain ⟨hrd, hwr, dKS, -, -, -, dAD, dAV, dAS, -, -, -, fK, -, -, -, fE, hRn, sD, sV, sS, sA, sK, sE⟩ := h
  have inA : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Modes.X86.argOp i)) 4 := fun i hi =>
    ⟨⟨argAddr s 0, 24⟩, by rw [hrd]; simp, by
      rw [show s.ea (VG.Impl.Modes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega_using [fE]) hi]
      exact VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
  have subA : ∀ i < 6, Region.Sub ⟨s.ea (VG.Impl.Modes.X86.argOp i), 4⟩ ⟨argAddr s 0, 24⟩ := fun i hi => by
    rw [show s.ea (VG.Impl.Modes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega_using [fE]) hi]
    exact VG.Offset.sub_base _ (by omega_using [hi])
  have hstk : Proof.Modes.X86.stkRegion (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ :=
    stk_eq d sE
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
    rcases hr with rfl | rfl | rfl
    · exact dAD.sub_left (subA 1 (by decide))
    · exact dAV.sub_left (subA 1 (by decide))
    · exact dAS.sub_left (subA 1 (by decide))
  · rw [hstk]; exact sK
  · rw [hstk]; exact sA.sub_right (subA 0 (by decide))
  · rw [hstk]; exact sA.sub_right (subA 1 (by decide))

theorem core_ka (d : Dir) : (core d).ka = 2 := rfl
theorem data_eq (d : Dir) (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * (core d).bw) m ((arg s 3).setWidth 64) (arg s 4).toNat = dataAt m s := rfl
theorem iv_eq (d : Dir) (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 2).setWidth 64) (4 * (core d).bw) = ivAt m s := rfl
attribute [local irreducible] Spec.Camellia.cipher in
theorem cipher_enc (s : State) :
    (coreSpec .encrypt).cipher ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) =
      ciph s := rfl
attribute [local irreducible] Spec.Camellia.invCipher in
theorem cipher_dec (s : State) :
    (coreSpec .decrypt).cipher ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) =
      invCiph s := rfl

theorem levels_fit (d : Dir) : Proof.Modes.X86.LevelsFit (core d) levels := by
  intro g hg
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact ⟨by decide, by show _ ≤ 4; decide⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : (fbX86 cbcDecPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 cbcDecPost).post s₀ s' :=
  WP.mono (cbcDecLevels_wp (coreSpec .decrypt) (levels_fit _) (seqPre_of .decrypt rfl hp) (keyArgs_of .decrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, core_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_dec] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (fbX86 cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 cfbDecPost).post s₀ s' :=
  WP.mono (cfbDecLevels_wp (coreSpec .encrypt) (levels_fit _) (seqPre_of .encrypt rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, core_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_enc] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem ctr_wp_x86 {s₀ : State} (hp : (fbX86 ctrPost).pre s₀) :
    WP isa ctr s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 ctrPost).post s₀ s' :=
  WP.mono (ctrLevels_wp (coreSpec .encrypt) rfl (levels_fit _) (seqPre_of .encrypt rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, core_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_enc] at h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data`, `iv` and
`scratch` known to be the base addresses of the writable regions. -/
def fbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 16, 8 * 107], argLen := 28,
    argBases := [(16, 0), (12, 1), (24, 2)], room := 4 }

theorem fbTaint_wf {post : State → State → Prop} {s : State} (hp : (fbX86 post).pre s) :
    VG.X86.Taint.Wf fbTaint s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, hRn, sD, sV, sS, sA, sK,
    sE⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega_using [fE], ?_⟩, ?_⟩ fun _ => ⟨sE, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega_using [fE]) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega_using [fE]) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega_using [fE]) dRS dAS
  · intro p hp'
    simp only [fbTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact sD
    · exact sV
    · exact sS

theorem fbTaint_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (fbX86 post).pre s₁)
    (h₂ : (fbX86 post).pre s₂) (hpub : (fbX86 post).pub s₁ s₂) : VG.X86.Taint.Agree fbTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -, -, -, -, -, -, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -, -, -, -, -, -, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 2 (by omega_using []), ha 3 (by omega_using []), ha 4 (by omega_using []), ha 5 (by omega_using [])]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth fbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 28) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 28) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
    exact congrArg _ (ha _ (by omega_using [hk]))

theorem cbcDecryptChained_ct :
    ConstantTime isa (fbX86 cbcDecPost).pre (fbX86 cbcDecPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa (fbX86 cfbDecPost).pre (fbX86 cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem ctr_ct : ConstantTime isa (fbX86 ctrPost).pre (fbX86 ctrPost).pub ctr :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

/-- `fbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`fb_verified` narrows to `fbX86`). -/
def wideContract (post : State → State → Prop) : Contract isa :=
  { fbX86 post with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
      let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * 107⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩
      s.rd = [sched] ∧ s.wr = [iv, data, scratch, args] ∧
      sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * 107 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) ∧
      stk.Disjoint data ∧ stk.Disjoint iv ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧ stk.Disjoint sched ∧
      4 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 272⟩, ⟨argAddr s 0, 24⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩, ⟨(arg s 2).setWidth 64, 16⟩, ⟨(arg s 5).setWidth 64, 8 * 107⟩]

tactic_template "narrow_camellia_x86_aesniwide" : tactic => `(tactic| simp only [VG.Proof.Camellia.X86.AesNiWide.Modes.fbX86, VG.Proof.Camellia.X86.AesNiWide.Modes.wideContract,
                     VG.Proof.Camellia.X86.AesNiWide.Modes.narrowRd, VG.Proof.Camellia.X86.AesNiWide.Modes.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])

theorem wide_pre (post : State → State → Prop) (s : State) (h : (wideContract post).pre s) :
    (fbX86 post).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow_camellia_x86_aesniwide
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 18, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 0x12 else if a = 0x800D then 0x20
    else if a = 0x8011 then 0x30 else if a = 0x8019 then 0x40 else 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 856⟩, ⟨0x8004, 24⟩]

theorem wide_implies_cbcDec :
    (wideContract cbcDecPost).Implies (Proof.Camellia.cbcDecChainedScratchContract X86.abi 107 4) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cbcDecPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cbcDecPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cbcDecPost, ciph, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cbcDecPost]
  · sig_implies_sat [Proof.Camellia.cbcDecChainedScratchContract, Proof.Camellia.cbcChainedScratchSig, Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcDecChainedPost, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cbcDecPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbDec :
    (wideContract cfbDecPost).Implies (Proof.Camellia.cfbDecScratchContract X86.abi 107 4) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Proof.Camellia.cfbDecryptPostSk, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Proof.Camellia.cfbDecryptPostSk, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Proof.Camellia.cfbDecryptPostSk, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost, ciph, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Proof.Camellia.cfbDecryptPostSk, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
  · sig_implies_sat [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Proof.Camellia.cfbDecryptPostSk, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_ctr :
    (wideContract ctrPost).Implies (Proof.Camellia.ctrScratchContract X86.abi 107 4) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost, ciph, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
  · sig_implies_sat [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

/-- The four bytes below `esp` are apart from what the 1888 below it are. -/
theorem below4_of_1888 {E : BitVec 32} {R : Region} (hlo : 1888 ≤ E.toNat)
    (h : Region.Disjoint ⟨E.setWidth 64 - 1888#64, 1888⟩ R) : Region.Disjoint ⟨E.setWidth 64 - 4#64, 4⟩ R := by
  have hs := VG.X86.below_sub (sp := E) (a := 4) (b := 1888) (by decide) hlo
  have e : below E 1888 = ⟨E.setWidth 64 - 1888#64, 1888⟩ := by
    show (⟨(E - BitVec.ofNat 32 1888).setWidth 64, 1888⟩ : Region) = _
    rw [VG.X86.Taint.sub_setWidth hlo]
  have e4 : below E 4 = ⟨E.setWidth 64 - 4#64, 4⟩ := by
    show (⟨(E - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region) = _
    rw [VG.X86.Taint.sub_setWidth (by omega_arith)]
  rw [e, e4] at hs
  exact h.sub_left hs

theorem wide_implies_ctrK :
    (wideContract ctrPost).Implies (Proof.Camellia.ctrScratchContract X86.abi 107 1888) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | with_reducible (refine below4_of_1888 (by assumption) ?_; assumption)
      | (simp only [Nat.mul_comm] at *
         first
           | with_reducible assumption
           | with_reducible exact Region.Disjoint.symm ‹_›
           | with_reducible (refine below4_of_1888 (by assumption) ?_; assumption))
  · sig_implies_post [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost, ciph, invCiph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
  · sig_implies_sat [Proof.Camellia.ctrScratchContract, Proof.Camellia.ctrScratchSig, Spec.Camellia.ctrSig, Proof.Camellia.ctrPostSk, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ctrPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

/-- A state satisfying the functions' precondition: the schedule at `0x1000`,
18 rounds, the chaining value at `0x2000`, and no blocks at `0x3000`, as stack arguments
at `0x8004`, which are writable. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8008 then 0x12 else if a = 0x800D then 0x20
    else if a = 0x8011 then 0x30 else 0
  rd := [⟨0x1000, 272⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩]

theorem frameSat_cbc (post : Spec.Camellia.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.cbcChainedSig.contract X86.abi (pre := Proof.Camellia.cbcChainedPre X86.abi.ptrBits)
      (post := post) (writeArgs := true) (stack := 888)).pre s := by
  implies_sat [Spec.Camellia.cbcChainedSig, Proof.Camellia.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal,
      X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem frameSat_cfb (post : Spec.Camellia.cfbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.cfbSig.contract X86.abi (pre := Spec.Camellia.cfbPre X86.abi.ptrBits) (post := post)
      (writeArgs := true) (stack := 888)).pre s := by
  implies_sat [Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem frameSat_ctr (post : Spec.Camellia.ctrSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.ctrSig.contract X86.abi (pre := Spec.Camellia.ctrPre X86.abi.ptrBits) (post := post)
      (writeArgs := true) (stack := 888)).pre s := by
  implies_sat [Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem fb_verified {post : State → State → Prop} {c : Prog isa}
    (hwp : ∀ s, (fbX86 post).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (fbX86 post).post s s')
    (hct : ConstantTime isa (fbX86 post).pre (fbX86 post).pub c)
    (hR : ∀ s s' rd wr rd' wr', post (s.withRegions rd wr) (s'.withRegions rd' wr') → post s s')
    {k : Contract isa} (hi : (wideContract post).Implies k) : Verified X86.target c k := by
  have hsat := hi.sat_left
  have narrowSat : ∃ s, (fbX86 post).pre s := by
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
    narrow_camellia_x86_aesniwide
    exact h

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained (Proof.Camellia.cbcDecChainedScratchContract X86.abi 107 4) :=
  fb_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun _ _ _ _ _ _ h => h)
    wide_implies_cbcDec

theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt (Proof.Camellia.cfbDecScratchContract X86.abi 107 4) :=
  fb_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbDec

theorem ctr_verified : Verified X86.target ctr (Proof.Camellia.ctrScratchContract X86.abi 107 4) :=
  fb_verified (fun _ hs => ctr_wp_x86 hs) ctr_ct (fun _ _ _ _ _ _ h => h) wide_implies_ctr

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 884 5 214 cbcDecryptChained)
      (Spec.Camellia.cbcDecryptChainedContract X86.abi 888) :=
  Proof.Camellia.cbcDecryptChained_of_sk <|
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 107) (pre := Proof.Camellia.cbcChainedPre X86.abi.ptrBits)
    (post := Proof.Camellia.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 4)
    (bytes := 884) cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cbcChainedPre_local _)
    (Proof.Camellia.cbcDecChainedPost_local _) (Proof.Camellia.cbcDecChainedPostOut_local _) (frameSat_cbc _)

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 884 5 214 cfbDecrypt)
      (Spec.Camellia.cfbDecryptContract X86.abi 888) :=
  Proof.Camellia.cfbDecrypt_of_sk <|
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 107) (pre := Spec.Camellia.cfbPre X86.abi.ptrBits)
    (post := Proof.Camellia.cfbDecryptPostSk X86.abi.ptrBits) (wa := true) (stack := 4)
    (bytes := 884) cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cfbPre_local _)
    (Proof.Camellia.cfbDecryptPost_local _) (Proof.Camellia.cfbDecryptPostOut_local _) (frameSat_cfb _)

/-- `ctr` with its working space on the stack. -/
theorem ctr_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 884 5 214 ctr)
      (Spec.Camellia.ctrContract X86.abi 888) :=
  Proof.Camellia.ctr_of_sk <|
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64)
    (n := 107) (pre := Spec.Camellia.ctrPre X86.abi.ptrBits) (post := Proof.Camellia.ctrPostSk X86.abi.ptrBits)
    (wa := true) (stack := 4) (bytes := 884) ctr_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.ctrPre_local _)
    (Proof.Camellia.ctrPost_local _) (Proof.Camellia.ctrPostOut_local _) (frameSat_ctr _)

/-- `vg_camellia_ctr_final` calls `ctr` with 2772 bytes of stack. -/
theorem frameSat_ctrK (post : Spec.Camellia.ctrSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.ctrSig.contract X86.abi (pre := Spec.Camellia.ctrPre X86.abi.ptrBits) (post := post)
      (writeArgs := true) (stack := 2772)).pre s := by
  implies_sat [Spec.Camellia.ctrSig, Spec.Camellia.ctrPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem ctr_verifiedK : Verified X86.target ctr (Proof.Camellia.ctrScratchContract X86.abi 107 1888) :=
  fb_verified (fun _ hs => ctr_wp_x86 hs) ctr_ct (fun _ _ _ _ _ _ h => h) wide_implies_ctrK

/-- `ctr` with its working space on the stack, and the stack of
`vg_camellia_ctr_final`'s call. -/
theorem ctr_framedK :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 884 5 214 ctr)
      (Proof.Camellia.ctrContractSk X86.abi 2772) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.ctrSig) (nm := "scratch") (e := .u64)
    (n := 107) (pre := Spec.Camellia.ctrPre X86.abi.ptrBits) (post := Proof.Camellia.ctrPostSk X86.abi.ptrBits)
    (wa := true) (stack := 1888) (bytes := 884) ctr_verifiedK (by decide) (by lit_decide) (by lit_decide)
    (by decide) (Proof.Camellia.ctrPre_local _) (Proof.Camellia.ctrPost_local _)
    (Proof.Camellia.ctrPostOut_local _) (frameSat_ctrK _)

end VG.Proof.Camellia.X86.AesNiWide.Modes
