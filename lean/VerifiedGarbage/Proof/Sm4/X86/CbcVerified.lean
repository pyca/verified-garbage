import VerifiedGarbage.Proof.Sm4.X86.ModeCore
import VerifiedGarbage.Proof.Modes.X86.Modes
import VerifiedGarbage.Proof.Sm4.CbcScratch
import VerifiedGarbage.Proof.Sm4.X86.CbcLit
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract

/-!
# SM4-CBC on x86 (32-bit) meets its contracts

`cbcEncrypt_wp`, `cbcDecrypt_wp`: the modes' CBC encryption and decryption
(`Proof.Modes.X86.cbcEnc_wp`, `cbcDec_wp`) over SM4's core for each
direction (`dirCoreSpec`), with the working space as a fifth argument
(`cbcX86`). Each is correct and constant time, by the taint analysis, which
starts with `esp` public and knows which argument words are the base
addresses of the data and the scratch buffer. `cbcEncrypt_framed` and
`cbcDecrypt_framed` run them with their working space on the stack, zeroed
on return.
-/

namespace VG.Proof.Sm4

open VG VG.X86 VG.Impl.Sm4.X86

/-- CBC on x86 with its working space as the fifth argument: encryption if
`enc`, else decryption. -/
def cbcX86 (enc : Bool) : Contract X86.isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
    let iv : Region := ⟨(arg s 1).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 181⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, iv, args] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧
    data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
    ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 181 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    Spec.Cbc.blocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      (if enc then Spec.Cbc.encrypt (Spec.Sm4.cipher (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)))
       else Spec.Cbc.decrypt (Spec.Sm4.invCipher (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64))))
        (Spec.Aes.bytesAt s.mem ((arg s 1).setWidth 64) 16)
        (Spec.Cbc.blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Sm4

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.Impl.Sm4.X86 VG.Impl.Modes
open VG.Proof.Modes.X86 (SeqPre stkRegion slotA cbcEnc_wp cbcDec_wp)
open VG.Proof.Sm4 (cbcX86)

theorem disjoint_empty (r : Region) (a : Addr) : Region.Disjoint ⟨a, 0⟩ r := fun _ h => by
  simp only [Region.Contains] at h; omega

theorem scr_eq (s : State) (d : Dir) :
    Modes.X86.scrR s (dirCore d) = ⟨(arg s 4).setWidth 64, 8 * 181⟩ := by
  simp [Modes.X86.scrR, dirCore, tableEnd_eq]

/-- `cbcX86`'s precondition gives the modes'. -/
theorem seqPre_of {enc : Bool} {M : Mode} (d : Dir) (hstep : M.step = 16) (hiv : M.ivOut = false) {s : State} (h : (cbcX86 enc).pre s) :
    SeqPre (dirCore d) M s := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dAD, dAS, dRD, dRS, fK, fV, fD, fS, fE⟩ := h
  have hL := (dirCoreSpec d).layout
  refine ⟨(by rw [hrd]; simp), fE, ⟨(by rw [hwr]; simp [dirCore, tableEnd_eq]),
      (by simp only [dirCore, tableEnd_eq]; omega)⟩, (by rw [hrd]; simp [dirCore]),
    (fun h => by rw [hiv] at h; cases h), (by simp only [dirCore]; omega), (by rw [hwr, hstep]; simp),
    (by rw [hstep]; exact fD), ?_, ?_, (fun h => by rw [hiv] at h; cases h), ?_, ?_, ?_, ?_,
    (fun h => by rw [hiv] at h; cases h), disjoint_empty _ _, disjoint_empty _ _,
    disjoint_empty _ _, disjoint_empty _ _, (by simp [dirCore]), (by rw [hstep]; simp [dirCore]), hL⟩
  all_goals first
    | (rw [hstep, scr_eq]; first | exact dDS)
    | (rw [scr_eq]; first | exact dVS | exact dAS | exact dRS)
    | (rw [hstep]; first | exact dVD | exact dAD | exact dRD)


theorem keyArgs_of {enc : Bool} (d : Dir) {s : State} (h : (cbcX86 enc).pre s) :
    KeyArgs s [Modes.X86.scrR s (dirCore d)] (Spec.Sm4.scheduleAt s.mem ((arg s 0).setWidth 64)) := by
  obtain ⟨hrd, -, -, dKS, -, -, -, -, dAS, -, -, fK, -, -, -, -⟩ := h
  refine ⟨arg s 0, ⟨⟨argAddr s 0, 20⟩, by rw [hrd]; simp, ?_⟩, rfl, rfl, by rw [hrd]; simp, fK, fun r hr => ?_,
    fun r hr => ?_⟩
  · show (⟨argAddr s 0, 20⟩ : Region).Contains (argAddr s 0) 4
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]; exact dKS
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact dAS.sub_left (Region.sub_prefix (by decide))

theorem cbcEncrypt_wp {s₀ : State} (hp : (cbcX86 true).pre s₀) :
    WP isa cbcEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (cbcX86 true).post s₀ s' :=
  WP.mono (cbcEnc_wp (dirCoreSpec .encrypt) (seqPre_of .encrypt rfl rfl hp) (keyArgs_of .encrypt hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

theorem cbcDecrypt_wp {s₀ : State} (hp : (cbcX86 false).pre s₀) :
    WP isa cbcDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (cbcX86 false).post s₀ s' :=
  WP.mono (cbcDec_wp (dirCoreSpec .decrypt) (seqPre_of .decrypt rfl rfl hp) (keyArgs_of .decrypt hp))
    fun _ ⟨h1, h2⟩ => ⟨h1, h2⟩

/-! ## Constant time -/

/-- The initial taint: `esp` public, and the words holding `data` and
`scratch` known to be the base addresses of the writable regions. -/
def cbcTaint : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8 * 181], argLen := 24, argBases := [(12, 0), (20, 1)] }

theorem cbcTaint_wf {enc : Bool} {s : State} (hp : (cbcX86 enc).pre s) : VG.X86.Taint.Wf cbcTaint s := by
  obtain ⟨hrd, hwr, dKD, dKS, dVD, dVS, dDS, dAD, dAS, dRD, dRS, fK, fV, fD, fS, fE⟩ := hp
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨?_, ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [cbcTaint]; omega, ?_⟩, ?_⟩
  · rw [hwr]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) .nil)
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨dDS, fun _ h => h.elim⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [setWidth_toNat] <;> omega
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) dRD dAD
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) dRS dAS
  · intro p hp'
    simp only [cbcTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hwr, addr, arg, argAddr]

theorem cbcTaint_agree {enc : Bool} {s₁ s₂ : State} (h₁ : (cbcX86 enc).pre s₁) (h₂ : (cbcX86 enc).pre s₂)
    (hpub : (cbcX86 enc).pub s₁ s₂) : VG.X86.Taint.Agree cbcTaint s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have fE₁ : (s₁.gpr .esp).toNat + 24 ≤ 2 ^ 32 := h₁.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have fE₂ : (s₂.gpr .esp).toNat + 24 ≤ 2 ^ 32 := h₂.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, cbcTaint_wf h₁, cbcTaint_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [cbcTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [h₁.2.1, h₂.2.1, ha 2 (by omega), ha 3 (by omega), ha 4 (by omega)]
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
def cbcWideContract (enc : Bool) : Contract isa :=
  { cbcX86 enc with
    pre := fun s =>
      let sched : Region := ⟨(arg s 0).setWidth 64, 128⟩
      let iv : Region := ⟨(arg s 1).setWidth 64, 16⟩
      let data : Region := ⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * 181⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [sched, iv] ∧ s.wr = [data, scratch, args] ∧
      sched.Disjoint data ∧ sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧
      data.Disjoint scratch ∧ args.Disjoint data ∧ args.Disjoint scratch ∧
      ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 128 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 16 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * 181 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

def cbcNarrowRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, 128⟩, ⟨(arg s 1).setWidth 64, 16⟩, ⟨argAddr s 0, 20⟩]
def cbcNarrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, 16 * (arg s 3).toNat⟩, ⟨(arg s 4).setWidth 64, 8 * 181⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.Sm4.cbcX86, VG.Proof.Sm4.X86.cbcWideContract,
    VG.Proof.Sm4.X86.cbcNarrowRd, VG.Proof.Sm4.X86.cbcNarrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem cbcWide_pre (enc : Bool) (s : State) (h : (cbcWideContract enc).pre s) :
    (cbcX86 enc).pre (s.withRegions (cbcNarrowRd s) (cbcNarrowWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0, 0x4000` at `0x8004`. -/
def cbcSatState : State where
  gpr r := if r = .esp then 0x8000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30
    else if a = 0x8015 then 0x40 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x4000, 1448⟩, ⟨0x8004, 20⟩]

theorem wide_implies_enc :
    (cbcWideContract true).Implies (Proof.Sm4.cbcEncScratchContract X86.abi 181) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86] at h
    sig_split h
    sig_reduce [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
    sig_simp [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86, ite_true, ite_false, Bool.false_eq_true]
  · sig_implies_pub [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
  · sig_implies_sat [Proof.Sm4.cbcEncScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcEncPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
      [cbcSatState, arg, argAddr, Mem.readW, Mem.read] using cbcSatState

theorem wide_implies_dec :
    (cbcWideContract false).Implies (Proof.Sm4.cbcDecScratchContract X86.abi 181) := by
  refine { pre := ?_, post := ?_, pub := ?_, sat := ?_ }
  · intro s h
    sig_pre [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86] at h
    sig_split h
    sig_reduce [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
    sig_simp [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (simp only [Nat.mul_comm] at *; first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›)
  · sig_implies_post [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86, ite_true, ite_false, Bool.false_eq_true]
  · sig_implies_pub [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
  · sig_implies_sat [Proof.Sm4.cbcDecScratchContract, Proof.Sm4.cbcScratchSig, Spec.Sm4.cbcSig, Proof.Sm4.cbcDecPost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, cbcWideContract, cbcX86]
      [cbcSatState, arg, argAddr, Mem.readW, Mem.read] using cbcSatState

/-- A state satisfying the CBC functions' precondition: the schedule at
`0x1000`, the IV at `0x2000`, and no blocks at `0x3000`, as stack arguments at
`0x8004`, which are writable. -/
def cbcFrameSat : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800D then 0x30 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩]
  wr := [⟨0x3000, 0⟩, ⟨0x8004, 16⟩]

theorem cbcFrameSat_pre (post : Spec.Sm4.cbcSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Sm4.cbcSig.contract X86.abi (post := post) (writeArgs := true) (stack := 1472)).pre s := by
  implies_sat [Spec.Sm4.cbcSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [cbcFrameSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using cbcFrameSat

theorem cbcEncrypt_verified : Verified X86.target cbcEncrypt (Proof.Sm4.cbcEncScratchContract X86.abi 181) := by
  have hsat := wide_implies_enc.sat_left
  have narrowSat : ∃ s, (cbcX86 true).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, cbcWide_pre true s hs⟩
  apply Verified.of_implies _ wide_implies_enc
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => cbcEncrypt_wp hs) cbcEncrypt_ct (.refl narrowSat))
    cbcNarrowRd cbcNarrowWr (cbcWide_pre true) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [cbcNarrowRd, cbcNarrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [cbcNarrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

/-- cbcEncrypt with its working space on the stack. -/
theorem cbcEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 cbcEncrypt)
      (Spec.Sm4.cbcEncryptContract X86.abi 1472) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.cbcSig) (nm := "scratch") (e := .u64)
    (n := 181) (post := Proof.Sm4.cbcEncPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1472) cbcEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cbcEncPost_local _) (Proof.Sm4.cbcEncPostOut_local _) (cbcFrameSat_pre _)

theorem cbcDecrypt_verified : Verified X86.target cbcDecrypt (Proof.Sm4.cbcDecScratchContract X86.abi 181) := by
  have hsat := wide_implies_dec.sat_left
  have narrowSat : ∃ s, (cbcX86 false).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, cbcWide_pre false s hs⟩
  apply Verified.of_implies _ wide_implies_dec
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => cbcDecrypt_wp hs) cbcDecrypt_ct (.refl narrowSat))
    cbcNarrowRd cbcNarrowWr (cbcWide_pre false) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [cbcNarrowRd, cbcNarrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp_all only [or_true, true_or]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [cbcNarrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp_all only [or_true, true_or]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

/-- cbcDecrypt with its working space on the stack. -/
theorem cbcDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 1472 4 362 cbcDecrypt)
      (Spec.Sm4.cbcDecryptContract X86.abi 1472) :=
  X86.Verified.stackScratchWiped (sig := Spec.Sm4.cbcSig) (nm := "scratch") (e := .u64)
    (n := 181) (post := Proof.Sm4.cbcDecPost X86.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1472) cbcDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial)
    (Proof.Sm4.cbcDecPost_local _) (Proof.Sm4.cbcDecPostOut_local _) (cbcFrameSat_pre _)

end VG.Proof.Sm4.X86
