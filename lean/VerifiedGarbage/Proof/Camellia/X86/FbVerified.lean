module
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Camellia.FbScratch
meta import VerifiedGarbage.Proof.Camellia.FbScratch
public import VerifiedGarbage.Proof.Camellia.X86.FbLit
meta import VerifiedGarbage.Proof.Camellia.X86.FbLit
public import VerifiedGarbage.Proof.Camellia.X86.ModeCore
import VerifiedGarbage.Proof.Camellia.X86.CallSum
meta import VerifiedGarbage.Proof.Camellia.X86.CallSum
meta import VerifiedGarbage.Proof.Camellia.X86.ModeCore
import VerifiedGarbage.Proof.Modes.X86.Modes
meta import VerifiedGarbage.Proof.Modes.X86.Modes
public import VerifiedGarbage.Proof.Framework.X86.TaintMono
meta import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.Modes.X86.Seq
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Camellia.CtrCipher
import VerifiedGarbage.Proof.Camellia.Scratch
import VerifiedGarbage.Proof.Camellia.X86.Copy
import VerifiedGarbage.Proof.Camellia.X86.Crypt8
import VerifiedGarbage.Proof.Camellia.X86.Fl
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Spec.Ctr.Contract
meta import VerifiedGarbage.Proof.AesCtr.Inc
meta import VerifiedGarbage.Proof.Camellia.CtrCipher
meta import VerifiedGarbage.Proof.Camellia.Scratch
meta import VerifiedGarbage.Proof.Camellia.X86.Copy
meta import VerifiedGarbage.Proof.Camellia.X86.Crypt8
meta import VerifiedGarbage.Proof.Camellia.X86.Fl
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.NativeTaint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Modes.Steps
meta import VerifiedGarbage.Proof.Modes.X86.Counter
meta import VerifiedGarbage.Proof.Modes.X86.Ops
meta import VerifiedGarbage.Spec.Ctr.Contract

/-!
# Camellia-OFB and Camellia-CFB128 on x86 (32-bit) meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86.ofb_wp`, `cfbEnc_wp`, `cfbDec_wp`) over Camellia's core in the
encryption direction (`dirCoreSpec .encrypt`), with the working space as a
sixth argument (`fbX86`). The chaining value is written back, so it is
writable, and the taint analysis knows the argument words holding the
addresses of the data, the chaining value and the scratch buffer as the base
addresses of the writable regions. The `_framed` theorems run them with
their working space on the stack, zeroed on return.
-/

@[expose] public section

namespace VG.Proof.Camellia.X86

open VG VG.X86 VG.Impl.Camellia.X86

theorem disjoint_empty (r : Region) (a : Addr) : Region.Disjoint ⟨a, 0⟩ r := fun _ h => by
  simp only [Region.Contains] at h; omega

theorem scr_eq (s : State) (d : Dir) :
    Modes.X86.scrR s (dirCore d) = ⟨(arg s 5).setWidth 64, 8 * 341⟩ := by
  simp [Modes.X86.scrR, dirCore, slots_eq]

end VG.Proof.Camellia.X86

namespace VG.Proof.Camellia.X86.Fb

open VG VG.X86 VG.Impl.Camellia.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre ofb_wp cfbEnc_wp cfbDec_wp)
open VG.Proof.Camellia.X86 (scr_eq disjoint_empty KeyArgs dirCoreSpec dirCore_ka)
open VG.Proof.Camellia (schedWords)
open VG.Proof.Modes.X86 (argAddr_eq)

/-- Camellia under the schedule at the first argument, with the number of rounds in the second. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.Camellia.cipher (Spec.Camellia.subkeysAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m ((arg s 2).setWidth 64) 16
/-- The data. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) := Spec.Cbc.blocksAt m ((arg s 3).setWidth 64) (arg s 4).toNat

/-- The functions' postconditions. -/
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (arg s 4).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

/-- OFB or CFB128 on x86 with its working space as the sixth argument, and
the postcondition `post`. -/
def fbX86 (post : State → State → Prop) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * 341⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩
    s.rd = [sched, args] ∧ s.wr = [data, iv, scratch] ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * 341 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) ∧
    stk.Disjoint data ∧ stk.Disjoint iv ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧ 16 ≤ (s.gpr .esp).toNat
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- The core's 16 bytes of stack, as the contracts write them. -/
theorem stk_eq {s : State} (h : 16 ≤ (s.gpr .esp).toNat) (d : Dir) :
    Proof.Modes.X86.stkRegion (Proof.Modes.X86.E s) (dirCore d).stack =
      ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ := by
  show (⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ : Region) = _
  rw [VG.X86.Taint.sub_setWidth h]

/-- The stack below the return address is apart from it. -/
theorem stk_ret (s : State) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ ⟨(s.gpr .esp).setWidth 64, 4⟩ :=
  (VG.Offset.base_disjoint_below _ (by decide)).symm

/-- The modes' slots are in the scratch buffer. -/
theorem modeSlots_sub (S : BitVec 32) (d : Dir := .encrypt) :
    Region.Sub ⟨Proof.Modes.X86.slotA S (dirCore d).slots, 40⟩ ⟨S.setWidth 64, 8 * 341⟩ :=
  VG.Offset.sub_base _ (by simp only [dirCore, slots_eq]; omega)

/-- `fbX86`'s precondition gives the modes'. -/
theorem seqPre_of {post : State → State → Prop} {M : Mode} (hstep : M.step = 16) {s : State}
    (h : (fbX86 post).pre s) : SeqPre (dirCore .encrypt) M s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, hRn, sD, sV, sS, sA, sE⟩ := h
  have hL := (dirCoreSpec .encrypt).layout
  refine ⟨(by rw [hrd]; simp [dirCore]), fE, ⟨(by rw [hwr]; simp [dirCore, slots_eq]),
      (by simp only [dirCore, slots_eq]; omega)⟩, (by rw [hwr]; simp [dirCore]),
    (fun _ => by rw [hwr]; simp [dirCore]), (by simp only [dirCore]; omega), (by rw [hwr, hstep]; simp [dirCore]),
    (by rw [hstep]; exact fD), ?_, ?_, (fun _ => ?_), ?_, ?_, ?_, ?_,
    (fun _ => ?_), ?_, ?_, ?_, ?_, sE, (by rw [hstep]; simp [dirCore]), hL⟩
  · rw [hstep, scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · rw [hstep]; exact dVD
  · rw [scr_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scr_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dRV
  · rw [stk_eq sE, hstep]; exact sD
  · rw [stk_eq sE]; exact sS.sub_right (modeSlots_sub _)
  · rw [stk_eq sE]; exact sA
  · rw [stk_eq sE]; exact stk_ret s

theorem keyArgs_of {post : State → State → Prop} {s : State} (h : (fbX86 post).pre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore .encrypt)]
      ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) := by
  obtain ⟨hrd, hwr, dKS, -, -, -, dAD, dAV, dAS, -, -, -, fK, -, -, -, fE, hRn, sD, sV, sS, sA, sE⟩ := h
  have inA : ∀ i < 6, InRegions (s.rd ++ s.wr) (s.ea (VG.Impl.Aes.X86.argOp i)) 4 := fun i hi =>
    ⟨⟨argAddr s 0, 24⟩, by rw [hrd]; simp, by
      rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega) hi]
      exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  have subA : ∀ i < 6, Region.Sub ⟨s.ea (VG.Impl.Aes.X86.argOp i), 4⟩ ⟨argAddr s 0, 24⟩ := fun i hi => by
    rw [show s.ea (VG.Impl.Aes.X86.argOp i) = argAddr s i from rfl, argAddr_eq s (n := 6) (by omega) hi]
    exact VG.Offset.sub_base _ (by omega)
  refine ⟨arg s 0, inA 0 (by decide), rfl, inA 1 (by decide), ?_, hRn, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr => ?_, ?_⟩
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
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    rw [show Proof.Modes.X86.stkRegion (s.gpr .esp) 16 = _ from stk_eq sE .encrypt]; exact sS
  · rw [show Proof.Modes.X86.stkRegion (s.gpr .esp) 16 = _ from stk_eq sE .encrypt]
    exact sA.sub_right (subA 1 (by decide))

theorem data_eq (m : Mem) (s : State) :
    Proof.Modes.chunksAt (4 * (dirCore .encrypt).bw) m ((arg s 3).setWidth 64) (arg s 4).toNat = dataAt m s := rfl
theorem iv_eq (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 2).setWidth 64) (4 * (dirCore .encrypt).bw) = ivAt m s := rfl
attribute [local irreducible] Spec.Camellia.cipher in
theorem cipher_eq (s : State) :
    (dirCoreSpec .encrypt).cipher ((arg s 1).toNat, schedWords s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) =
      ciph s := rfl

theorem ofb_wp_x86 {s₀ : State} (hp : (fbX86 ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 ofbPost).post s₀ s' :=
  WP.mono (ofb_wp (dirCoreSpec .encrypt) (seqPre_of rfl hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : (fbX86 cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 cfbEncPost).post s₀ s' :=
  WP.mono (cfbEnc_wp (dirCoreSpec .encrypt) (seqPre_of rfl hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (fbX86 cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (fbX86 cfbDecPost).post s₀ s' :=
  WP.mono (cfbDec_wp (dirCoreSpec .encrypt) (seqPre_of rfl hp) (keyArgs_of hp))
    fun _ ⟨h1, h2, h3⟩ => by
      simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp, Proof.Modes.X86.P,
        Proof.Modes.X86.N, dirCore_ka, Nat.reduceAdd, data_eq, iv_eq, cipher_eq] at h2 h3
      exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data`, `iv` and
`scratch` known to be the base addresses of the writable regions. -/
def fbTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 16, 8 * 341], argLen := 28,
    argBases := [(16, 0), (12, 1), (24, 2)], room := 16 }

theorem fbTaint_wf {post : State → State → Prop} {s : State} (hp : (fbX86 post).pre s) :
    VG.X86.Taint.Wf fbTaint s := by
  obtain ⟨hrd, hwr, dKS, dVD, dVS, dDS, dAD, dAV, dAS, dRD, dRV, dRS, fK, fV, fD, fS, fE, hRn, sD, sV, sS, sA, sE⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [fbTaint]; omega, ?_⟩, ?_⟩ fun _ => ⟨sE, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨dVD.symm, dDS⟩, dVS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) dRV dAV
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) dRS dAS
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
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -, -, -, -, -, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -, -, -, -, -, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, fbTaint_wf h₁, fbTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 2 (by omega), ha 3 (by omega), ha 4 (by omega), ha 5 (by omega)]
  · simp only [fbTaint] at hk
    rw [show VG.X86.Taint.depth fbTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 28) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 28) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem ofb_ct : ConstantTime isa (fbX86 ofbPost).pre (fbX86 ofbPost).pub ofb :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [cryptCallSum] :
    ∃ h, (VG.X86.taint.check fbTaint ofb h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfbEncrypt_ct : ConstantTime isa (fbX86 cfbEncPost).pre (fbX86 cfbEncPost).pub cfbEncrypt :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [cryptCallSum] :
    ∃ h, (VG.X86.taint.check fbTaint cfbEncrypt h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

theorem cfbDecrypt_ct : ConstantTime isa (fbX86 cfbDecPost).pre (fbX86 cfbDecPost).pub cfbDecrypt :=
  let ⟨_, h⟩ := (by native_taint_decide_sum [cryptCallSum] :
    ∃ h, (VG.X86.taint.check fbTaint cfbDecrypt h).isSome = true)
  VG.Taint.constantTime (A := VG.X86.taint) fbTaint (fun _ _ h₁ h₂ hp => fbTaint_agree h₁ h₂ hp) h

/-! ## The contracts -/

/-- `fbX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`fb_verified` narrows to `fbX86`). -/
def wideContract (post : State → State → Prop) : Contract isa :=
  { fbX86 post with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 272⟩
      let iv : Region := ⟨(arg s 2).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 8 * 341⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩
      s.rd = [sched] ∧ s.wr = [iv, data, scratch, args] ∧
      sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
      args.Disjoint data ∧ args.Disjoint iv ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint iv ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 8 * 341 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 18 ∨ (arg s 1).toNat = 24) ∧
    stk.Disjoint data ∧ stk.Disjoint iv ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧ 16 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region := [⟨(arg s 0).setWidth 64, 272⟩, ⟨argAddr s 0, 24⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩, ⟨(arg s 2).setWidth 64, 16⟩, ⟨(arg s 5).setWidth 64, 8 * 341⟩]

tactic_template "narrow_camellia_x86_fbverified" : tactic => `(tactic| simp only [VG.Proof.Camellia.X86.Fb.fbX86, VG.Proof.Camellia.X86.Fb.wideContract,
                     VG.Proof.Camellia.X86.Fb.narrowRd, VG.Proof.Camellia.X86.Fb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr])
tactic_template "narrow_camellia_x86_fbverified" loc:Lean.Parser.Tactic.location : tactic => `(tactic| simp only [VG.Proof.Camellia.X86.Fb.fbX86, VG.Proof.Camellia.X86.Fb.wideContract,
                     VG.Proof.Camellia.X86.Fb.narrowRd, VG.Proof.Camellia.X86.Fb.narrowWr, VG.X86.arg_withRegions,
                     VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
                     VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $loc)

theorem wide_pre (post : State → State → Prop) (s : State) (h : (wideContract post).pre s) :
    (fbX86 post).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow_camellia_x86_fbverified
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
  wr := [⟨0x2000, 16⟩, ⟨0x3000, 0⟩, ⟨0x4000, 2728⟩, ⟨0x8004, 24⟩]

theorem wide_implies_ofb :
    (wideContract ofbPost).Implies (Proof.Camellia.ofbScratchContract X86.abi 341 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPost, Spec.Camellia.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPost, Spec.Camellia.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPost, Spec.Camellia.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPost, Spec.Camellia.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
  · sig_implies_sat [Proof.Camellia.ofbScratchContract, Proof.Camellia.ofbScratchSig, Spec.Camellia.ofbSig, Spec.Camellia.ofbPost, Spec.Camellia.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, ofbPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbEnc :
    (wideContract cfbEncPost).Implies (Proof.Camellia.cfbEncScratchContract X86.abi 341 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbEncryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbEncryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbEncryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbEncryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
  · sig_implies_sat [Proof.Camellia.cfbEncScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbEncryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbEncPost]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_cfbDec :
    (wideContract cfbDecPost).Implies (Proof.Camellia.cfbDecScratchContract X86.abi 341 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbDecryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost] at h
    sig_split h
    sig_reduce [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbDecryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbDecryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost, ciph, ivAt, dataAt]
  · sig_implies_pub [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbDecryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
  · sig_implies_sat [Proof.Camellia.cfbDecScratchContract, Proof.Camellia.cfbScratchSig, Spec.Camellia.cfbSig, Spec.Camellia.cfbDecryptPost, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, fbX86, cfbDecPost]
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

theorem frameSat_ofb (post : Spec.Camellia.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.ofbSig.contract X86.abi (pre := Spec.Camellia.ofbPre X86.abi.ptrBits) (post := post)
      (writeArgs := true) (stack := 2772)).pre s := by
  implies_sat [Spec.Camellia.ofbSig, Spec.Camellia.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem frameSat_cfb (post : Spec.Camellia.cfbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Camellia.cfbSig.contract X86.abi (pre := Spec.Camellia.cfbPre X86.abi.ptrBits) (post := post)
      (writeArgs := true) (stack := 2772)).pre s := by
  implies_sat [Spec.Camellia.cfbSig, Spec.Camellia.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
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
    narrow_camellia_x86_fbverified
    exact h

theorem ofb_verified : Verified X86.target ofb (Proof.Camellia.ofbScratchContract X86.abi 341 16) :=
  fb_verified (fun _ hs => ofb_wp_x86 hs) ofb_ct (fun _ _ _ _ _ _ h => h) wide_implies_ofb

theorem cfbEncrypt_verified :
    Verified X86.target cfbEncrypt (Proof.Camellia.cfbEncScratchContract X86.abi 341 16) :=
  fb_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbEnc

theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt (Proof.Camellia.cfbDecScratchContract X86.abi 341 16) :=
  fb_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun _ _ _ _ _ _ h => h) wide_implies_cfbDec

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 ofb)
      (Spec.Camellia.ofbContract X86.abi 2772) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.ofbSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.ofbPre X86.abi.ptrBits) (post := Spec.Camellia.ofbPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2756) ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.ofbPre_local _)
    (Proof.Camellia.ofbPost_local _) (Proof.Camellia.ofbPostOut_local _) (frameSat_ofb _)

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 cfbEncrypt)
      (Spec.Camellia.cfbEncryptContract X86.abi 2772) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.cfbPre X86.abi.ptrBits) (post := Spec.Camellia.cfbEncryptPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2756) cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cfbPre_local _)
    (Proof.Camellia.cfbEncryptPost_local _) (Proof.Camellia.cfbEncryptPostOut_local _) (frameSat_cfb _)

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 cfbDecrypt)
      (Spec.Camellia.cfbDecryptContract X86.abi 2772) :=
  X86.Verified.stackScratchWiped (sig := Spec.Camellia.cfbSig) (nm := "scratch") (e := .u64)
    (n := 341) (pre := Spec.Camellia.cfbPre X86.abi.ptrBits) (post := Spec.Camellia.cfbDecryptPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 2756) cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (Proof.Camellia.cfbPre_local _)
    (Proof.Camellia.cfbDecryptPost_local _) (Proof.Camellia.cfbDecryptPostOut_local _) (frameSat_cfb _)

end VG.Proof.Camellia.X86.Fb
