import VerifiedGarbage.Proof.TripleDes.X86.ModeCore
import VerifiedGarbage.Proof.Modes.X86.Modes
import VerifiedGarbage.Proof.TripleDes.CbcScratch
import VerifiedGarbage.Proof.TripleDes.X86.CbcLit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Triple DES-CBC on x86 (32-bit) meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
(`Proof.Modes.X86.cbcEnc_wp`, `cbcDec_wp`) over Triple DES's core for each
direction (`Mode.dirCoreSpec`), with the working space as a fifth argument
(`cbcX86`). Each is correct and constant time, by the taint analysis, which
starts with `esp` public, knows which argument words are the base addresses
of the data and the scratch buffer, and has room for the block function's
call below `esp`. `cbcEncrypt_framed` and `cbcDecrypt_framed` run them with
their working space on the stack, zeroed on return.
-/

namespace VG.Proof.TripleDes.X86.Cbc

open VG VG.X86 VG.Impl.TripleDes.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre stkRegion slotA cbcEnc_wp cbcDec_wp)
open VG.Proof.TripleDes.X86.Mode (dirCoreSpec KeyArgs)
open VG.Proof.TripleDes (bytesAt_eq)
open VG.Proof.Rc2.X86 (addr32)

/-- CBC on x86 with its working space as the fifth argument: encryption if
`enc`, else decryption. -/
def cbcX86 (enc : Bool) : Contract X86.isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 384⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 118⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 16
    s.rd = [key, iv, args] ∧ s.wr = [data, scratch] ∧
    key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧
    data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 118 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 16 ≤ (s.gpr .esp).toNat
  post s s' :=
    Spec.TripleDes.cbcBlocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      (if enc then Spec.Cbc.encrypt (Spec.TripleDes.cipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)))
       else Spec.Cbc.decrypt (Spec.TripleDes.invCipher (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64))))
        (Spec.TripleDes.bytesAt s.mem ((arg s 1).setWidth 64) 8)
        (Spec.TripleDes.cbcBlocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

theorem scr_eq (s : State) (d : Spec.TripleDes.Direction) :
    Modes.X86.scrR s (dirCore d) = ⟨(arg s 4).setWidth 64, 8 * 118⟩ := by
  simp [Modes.X86.scrR, dirCore, schedSlot]

/-- The data in blocks, as the modes' steps. -/
theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.TripleDes.cbcBlocksAt m p n = Proof.Modes.chunksAt 8 m p n := by
  simp only [Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Proof.Modes.chunksAt, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

/-- The stack below `esp` is apart from the arguments and the return address. -/
theorem stk_apart {s : State} (hfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) (hlo : 16 ≤ (s.gpr .esp).toNat) :
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨argAddr s 0, 20⟩ ∧
      Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨(s.gpr .esp).setWidth 64, 4⟩ := by
  have e : (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ _
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 16) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

/-- `cbcX86`'s precondition gives the modes'. -/
theorem seqPre_of {enc : Bool} {M : Mode} (d : Spec.TripleDes.Direction) (hstep : M.step = 8)
    (hiv : M.ivOut = false) {s : State} (h : (cbcX86 enc).pre s) : SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dAD, dAS, dRD, dRS, dSD, dSS, fK, fV, fD, fS, fE, fLo⟩ := h
  have hL := (dirCoreSpec d).layout
  obtain ⟨sA, sR⟩ := stk_apart fE fLo
  refine ⟨(by rw [hrd]; simp), fE, ⟨(by rw [hwr]; simp [dirCore, schedSlot]),
      (by simp only [dirCore, schedSlot]; omega)⟩, (by rw [hrd]; simp [dirCore]),
    (fun h => by rw [hiv] at h; cases h), (by simp only [dirCore]; omega), (by rw [hwr, hstep]; simp),
    (by rw [hstep]; exact fD), ?_, ?_, (fun h => by rw [hiv] at h; cases h), ?_, ?_, ?_, ?_,
    (fun h => by rw [hiv] at h; cases h), (by rw [hstep]; exact dSD), ?_, sA, sR, (by simp [dirCore]; omega),
    (by rw [hstep]; simp [dirCore]), hL⟩
  · rw [hstep, scr_eq]; exact dDS
  · rw [scr_eq]; exact dVS
  · rw [scr_eq]; exact dAS
  · rw [hstep]; exact dAD
  · rw [scr_eq]; exact dRS
  · rw [hstep]; exact dRD
  · exact dSS.sub_right (VG.Offset.sub_base _ (by simp only [dirCore, schedSlot]; omega))

theorem keyArgs_of {enc : Bool} (d : Spec.TripleDes.Direction) {s : State} (h : (cbcX86 enc).pre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore d)] (Spec.TripleDes.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, -, dKS, -, -, -, -, dAS, -, -, -, dSS, fK, -, -, -, -, -⟩ := h
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK,
    fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dSS

theorem cbcEncrypt_wp {s₀ : State} (hp : (cbcX86 true).pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (cbcX86 true).post s₀ s' :=
  WP.mono (cbcEnc_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl rfl hp) (keyArgs_of .encrypt hp))
    fun s' ⟨h1, h2⟩ => ⟨h1, by
      show Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.encrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2⟩

theorem cbcDecrypt_wp {s₀ : State} (hp : (cbcX86 false).pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (cbcX86 false).post s₀ s' :=
  WP.mono (cbcDec_wp (dirCoreSpec .decrypt) (seqPre_of .decrypt rfl rfl hp) (keyArgs_of .decrypt hp))
    fun s' ⟨h1, h2⟩ => ⟨h1, by
      show Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq]; exact h2⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, the words holding `data` and `scratch`
known to be the base addresses of the writable regions, and room for the
block function's call below `esp`. -/
def cbcTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8 * 118], argLen := 24,
    argBases := [(12, 0), (20, 1)], room := 16 }

theorem cbcTaint_wf {enc : Bool} {s : State} (hp : (cbcX86 enc).pre s) : VG.X86.Taint.Wf cbcTaint s := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dAD, dAS, dRD, dRS, dSD, dSS, fK, fV, fD, fS, fE, fLo⟩ := hp
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [cbcTaint]; omega, ?_⟩, ?_⟩ ?_
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨dDS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) dRS dAS
  · intro p hp'
    simp only [cbcTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]
  · intro _
    refine ⟨fLo, ?_⟩
    intro r hr
    have e : (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 =
        (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := (VG.X86.Taint.sub_setWidth fLo).symm
    change (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16, 16⟩ : Region).Disjoint r
    rw [e]
    simp only [hwr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dSD
    · exact dSS

theorem cbcTaint_agree {enc : Bool} {s₁ s₂ : State} (h₁ : (cbcX86 enc).pre s₁) (h₂ : (cbcX86 enc).pre s₂)
    (hpub : (cbcX86 enc).pub s₁ s₂) : VG.X86.Taint.Agree cbcTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  obtain ⟨-, hwr₁, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₁, -⟩ := id h₁
  obtain ⟨-, hwr₂, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, fE₂, -⟩ := id h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, cbcTaint_wf h₁, cbcTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [cbcTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hwr₁, hwr₂, ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)]
  · simp only [cbcTaint] at hk
    rw [show VG.X86.Taint.depth cbcTaint.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (n := 24) fE₁ h4 hk, VG.X86.Taint.argByte_eq (n := 24) fE₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

theorem cbcEncrypt_ct : ConstantTime isa (cbcX86 true).pre (cbcX86 true).pub cbcEncrypt :=
  VG.Taint.constantTime (A := VG.X86.taint) cbcTaint (fun _ _ h₁ h₂ hp => cbcTaint_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcDecrypt_ct : ConstantTime isa (cbcX86 false).pre (cbcX86 false).pub cbcDecrypt :=
  VG.Taint.constantTime (A := VG.X86.taint) cbcTaint (fun _ _ h₁ h₂ hp => cbcTaint_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

/-- `cbcX86` with the argument slots writable, as the signature's contract has
them; the code reads them only (`cbc_verified` narrows to `cbcX86`). -/
def wideContract (enc : Bool) : Contract isa :=
  { cbcX86 enc with
    pre := fun s =>
      let key : Region := ⟨(arg s 0).setWidth 64, 384⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 8⟩
      let data : Region := ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 118⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 16
      s.rd = [key, iv] ∧ s.wr = [data, scratch, args] ∧
      key.Disjoint data ∧ key.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 118 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ 16 ≤ (s.gpr .esp).toNat }

def narrowRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 384⟩, ⟨(arg s 1).setWidth 64, 8⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩, ⟨(arg s 4).setWidth 64, 8 * 118⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.TripleDes.X86.Cbc.cbcX86, VG.Proof.TripleDes.X86.Cbc.wideContract,
    VG.Proof.TripleDes.X86.Cbc.narrowRd, VG.Proof.TripleDes.X86.Cbc.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wide_pre (enc : Bool) (s : State) (h : (wideContract enc).pre s) :
    (cbcX86 enc).pre (s.withRegions (narrowRd s) (narrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def satState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 944⟩, ⟨0x8004, 20⟩]

theorem wide_implies_enc :
    (wideContract true).Implies (Proof.TripleDes.cbcEncScratchContract X86.abi 118 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below, ite_true, ite_false, Bool.false_eq_true]
  · sig_implies_pub [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below]
  · sig_implies_sat [Proof.TripleDes.cbcEncScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

theorem wide_implies_dec :
    (wideContract false).Implies (Proof.TripleDes.cbcDecScratchContract X86.abi 118 16) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below] at h
    sig_split h
    sig_reduce [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below]
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [VG.X86.Taint.sub_setWidth (by omega)]; simp only [Nat.mul_comm] at *; with_reducible assumption)
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below, ite_true, ite_false, Bool.false_eq_true]
  · sig_implies_pub [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below]
  · sig_implies_sat [Proof.TripleDes.cbcDecScratchContract, Proof.TripleDes.cbcScratchSig, Spec.TripleDes.cbcSig, Proof.TripleDes.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, wideContract, cbcX86, below]
      [satState, arg, argAddr, Mem.readW, Mem.read] using satState

/-- A state satisfying the CBC functions' precondition: the schedule at
`0x1000`, the IV at `0x2000`, and no blocks at `0x3000`, as stack arguments at
`0x8004`, which are writable. -/
def frameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0
  rd := [⟨0x1000, 384⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x8004, 16⟩]

theorem frameSat_pre (post : Spec.TripleDes.cbcSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.TripleDes.cbcSig.contract X86.abi (post := post) (writeArgs := true) (stack := 984)).pre s := by
  implies_sat [Spec.TripleDes.cbcSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [frameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using frameSat

theorem cbc_verified (enc : Bool)
    (hwp : ∀ s, (cbcX86 enc).pre s → WP isa (if enc then cbcEncrypt else cbcDecrypt) s
      fun s' => abiPreserved s s' ∧ (cbcX86 enc).post s s')
    (hct : ConstantTime isa (cbcX86 enc).pre (cbcX86 enc).pub (if enc then cbcEncrypt else cbcDecrypt))
    {k : Contract isa} (hi : (wideContract enc).Implies k) :
    Verified X86.target (if enc then cbcEncrypt else cbcDecrypt) k := by
  have hsat := hi.sat_left
  have narrowSat : ∃ s, (cbcX86 enc).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, wide_pre enc s hs⟩
  apply Verified.of_implies _ hi
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat))
    narrowRd narrowWr (wide_pre enc) ?_ ?_ ?_ ?_ hsat
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
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem cbcEncrypt_verified : Verified X86.target cbcEncrypt (Proof.TripleDes.cbcEncScratchContract X86.abi 118 16) :=
  cbc_verified true (fun _ hs => cbcEncrypt_wp hs) cbcEncrypt_ct wide_implies_enc

theorem cbcDecrypt_verified : Verified X86.target cbcDecrypt (Proof.TripleDes.cbcDecScratchContract X86.abi 118 16) :=
  cbc_verified false (fun _ hs => cbcDecrypt_wp hs) cbcDecrypt_ct wide_implies_dec

/-- `cbcEncrypt` with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cbcEncrypt)
      (Spec.TripleDes.cbcEncryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cbcEncPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cbcEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cbcEncPost_local _) (Proof.TripleDes.cbcEncPostOut_local _) (frameSat_pre _)

/-- `cbcDecrypt` with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 968 4 236 cbcDecrypt)
      (Spec.TripleDes.cbcDecryptContract X86.abi 984) :=
  X86.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcSig) (nm := "scratch") (e := .u64)
    (n := 118) (post := Proof.TripleDes.cbcDecPost X86.abi.ptrBits) (wa := true) (stack := 16)
    (bytes := 968) cbcDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.TripleDes.cbcDecPost_local _) (Proof.TripleDes.cbcDecPostOut_local _) (frameSat_pre _)

end VG.Proof.TripleDes.X86.Cbc
