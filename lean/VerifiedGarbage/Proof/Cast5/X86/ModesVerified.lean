module

public import VerifiedGarbage.Proof.Cast5.X86.ModeCore
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Cast5.X86.ModeCore
public import VerifiedGarbage.Proof.Cast5.X86.ModesLit
meta import VerifiedGarbage.Proof.Cast5.X86.ModesLit
public import VerifiedGarbage.Proof.Cast5.ModeScratch
meta import VerifiedGarbage.Proof.Cast5.ModeScratch
import VerifiedGarbage.Proof.Modes.X86.CbcChained
meta import VerifiedGarbage.Proof.Modes.X86.CbcChained
public import VerifiedGarbage.Proof.Framework.X86.TaintSym
meta import VerifiedGarbage.Proof.Framework.X86.TaintSym
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.X86.EcbVerified
public import VerifiedGarbage.Proof.Framework.ConstMem
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Modes.X86.Seq
meta import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Modes.StepsChained
meta import VerifiedGarbage.Proof.AesCtr.Inc
meta import VerifiedGarbage.Proof.Cast5.Memory
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.ReadHalves
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
meta import VerifiedGarbage.Proof.Modes.StepsChained
meta import VerifiedGarbage.Proof.Modes.X86.Counter
meta import VerifiedGarbage.Proof.Modes.X86.Ops

/-!
# CAST5-CBC, -OFB and -CFB64 on x86 (32-bit): correctness

`cbcEncryptChained_wp`, …, `cfbDecrypt_wp`: the modes' CBC that updates
the chaining value, OFB and CFB (`Proof.Modes.X86.cbcEncChained_wp`, …)
over CAST5's core (`Mode.dirCoreSpec`), with the working space as a sixth
argument (`modeX ivw post`: the chaining value is writable if `ivw`, as it
is for all of them). The table of S-boxes is readable, where the static
`VG_CAST5_S1234` puts it, and holds the S-boxes (`Held`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86.ModeFns

open VG VG.X86 VG.Impl.Cast5.X86.Modes VG.Impl.Modes
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Proof.Modes.X86 (SeqPre stkRegion cbcEncChained_wp cbcDecChained_wp ofb_wp cfbEnc_wp cfbDec_wp)
open VG.Proof.Cast5.X86.Mode (dirCoreSpec KeyArgs Base)
open VG.Proof.Cast5 (Held)

/-- The subkeys. -/
abbrev keyA (s : State) : Region := ⟨(arg s 0).setWidth 64, 128⟩
/-- The chaining value. -/
abbrev ivA (s : State) : Region := ⟨(arg s 2).setWidth 64, 8⟩
/-- The data. -/
abbrev dataA (s : State) : Region := ⟨(arg s 3).setWidth 64, 8 * (arg s 4).toNat⟩
/-- The working space. -/
abbrev scrA (s : State) : Region := ⟨(arg s 5).setWidth 64, 304⟩
/-- The arguments. -/
abbrev argsA (s : State) : Region := ⟨argAddr s 0, 24⟩
/-- The table of S-boxes. -/
abbrev tabA (s : State) : Region := ⟨(s.syms s1234Sym).setWidth 64, 4096⟩
/-- The return address. -/
abbrev retA (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
/-- The word below `esp`, which the core's scans use. -/
abbrev stkA (s : State) : Region := below (s.gpr .esp) 4

/-- The readable regions: the chaining value too unless it is written. -/
def rdL : Bool → State → List Region
  | false, s => [keyA s, ivA s, argsA s, tabA s]
  | true, s => [keyA s, argsA s, tabA s]

/-- The writable regions: the chaining value too if it is written. -/
def wrL : Bool → State → List Region
  | false, s => [dataA s, scrA s]
  | true, s => [dataA s, ivA s, scrA s]

/-- A mode's precondition on x86, with the working space as the sixth
argument, the chaining value writable if `ivw`. -/
structure MPre (ivw : Bool) (s : State) : Prop where
  rdEq : s.rd = rdL ivw s
  wrEq : s.wr = wrL ivw s
  sp : 4 ≤ (s.gpr .esp).toNat
  espFit : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  nv : (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 16
  fitK : (arg s 0).toNat + 128 ≤ 2 ^ 32
  fitV : (arg s 2).toNat + 8 ≤ 2 ^ 32
  fitD : (arg s 3).toNat + 8 * (arg s 4).toNat ≤ 2 ^ 32
  fitS : (arg s 5).toNat + 304 ≤ 2 ^ 32
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  held : Held s.mem ((s.syms s1234Sym).setWidth 64) s1234
  dDS : (dataA s).Disjoint (scrA s)
  dVS : (ivA s).Disjoint (scrA s)
  dVD : ivw = true → (ivA s).Disjoint (dataA s)
  dKw : ∀ r ∈ s.wr, (keyA s).Disjoint r
  dTw : ∀ r ∈ s.wr, (tabA s).Disjoint r
  dAw : ∀ r ∈ s.wr, (argsA s).Disjoint r
  dRw : ∀ r ∈ s.wr, (retA s).Disjoint r
  dSw : ∀ r ∈ s.wr, (stkA s).Disjoint r
  dKs : (keyA s).Disjoint (stkA s)
  dTs : (tabA s).Disjoint (stkA s)

/-- A mode on x86 with the precondition `MPre ivw` and the postcondition
`post`. -/
def modeX (ivw : Bool) (post : State → State → Prop) : Contract isa where
  pre := MPre ivw
  post := post
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    s₁.syms s1234Sym = s₂.syms s1234Sym

section
variable {ivw : Bool} {s : State}

theorem MPre.mem_wr_data (h : MPre ivw s) : dataA s ∈ s.wr := by
  rw [h.wrEq]; cases ivw <;> simp [wrL]
theorem MPre.mem_wr_scr (h : MPre ivw s) : scrA s ∈ s.wr := by
  rw [h.wrEq]; cases ivw <;> simp [wrL]
theorem MPre.mem_wr_iv (h : MPre ivw s) (hw : ivw = true) : ivA s ∈ s.wr := by
  rw [h.wrEq]; subst hw; simp [wrL]
theorem MPre.mem_iv (h : MPre ivw s) : ivA s ∈ s.rd ++ s.wr := by
  rw [h.rdEq, h.wrEq]; cases ivw <;> simp [rdL, wrL]
theorem MPre.mem_args (h : MPre ivw s) : argsA s ∈ s.rd ++ s.wr := by
  rw [h.rdEq]; cases ivw <;> simp [rdL]
theorem MPre.mem_key (h : MPre ivw s) : keyA s ∈ s.rd ++ s.wr := by
  rw [h.rdEq]; cases ivw <;> simp [rdL]
theorem MPre.mem_tab (h : MPre ivw s) : tabA s ∈ s.rd ++ s.wr := by
  rw [h.rdEq]; cases ivw <;> simp [rdL]

/-- The word below `esp` is apart from the arguments and the return address. -/
theorem stk_apart (h : MPre ivw s) :
    Region.Disjoint (stkA s) (argsA s) ∧ Region.Disjoint (stkA s) (retA s) := by
  have hlo := h.sp
  have hfit := h.espFit
  have e : (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4 :=
    VG.X86.Taint.sub_setWidth hlo
  have ea : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  refine ⟨?_, ?_⟩
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ ⟨argAddr s 0, 24⟩
    rw [e, ea]; exact VG.Offset.disjoint_below_above _ (by decide)
  · show Region.Disjoint ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ _
    have := VG.Offset.disjoint_below_above ((s.gpr .esp).setWidth 64) (m := 4) (a := 0) (l := 4) (by decide)
    rw [BitVec.add_zero] at this
    rw [e]; exact this

end

theorem scr_eq (up : Bool) (s : State) : Modes.X86.scrR s (dirCore up) = scrA s := rfl

/-- `MPre`'s precondition gives the modes'. -/
theorem seqPre_of (up : Bool) {ivw : Bool} {M : Mode} (hstep : M.step = 8) (hiv : M.ivOut = ivw) {s : State}
    (h : MPre ivw s) : SeqPre (dirCore up) M s := by
  have hL := (dirCoreSpec up).layout
  obtain ⟨sA, sR⟩ := stk_apart h
  have mS := h.mem_wr_scr
  have mD := h.mem_wr_data
  refine ⟨h.mem_args, h.espFit, ⟨mS, h.fitS⟩, h.mem_iv, fun hv => h.mem_wr_iv (hiv ▸ hv), h.fitV,
    by rw [hstep]; exact mD, by rw [hstep]; exact h.fitD, by rw [hstep]; exact h.dDS, h.dVS,
    fun hv => by rw [hstep]; exact h.dVD (hiv ▸ hv), h.dAw _ mS, by rw [hstep]; exact h.dAw _ mD,
    h.dRw _ mS, by rw [hstep]; exact h.dRw _ mD, fun hv => ?_, by rw [hstep]; exact h.dSw _ mD,
    (h.dSw _ mS).sub_right (VG.Offset.sub_base _ (by simp [dirCore, coreSlots])), sA, sR, h.sp,
    by rw [hstep]; simp [dirCore], hL⟩
  exact h.dRw _ (h.mem_wr_iv (hiv ▸ hv))

theorem keyArgs_of (up : Bool) {ivw : Bool} {s : State} (h : MPre ivw s) :
    KeyArgs s [Modes.X86.scrR s (dirCore up)]
      (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64), (arg s 1).toNat) := by
  obtain ⟨sA, -⟩ := stk_apart h
  have hfit := h.espFit
  have ea : ∀ k, k + 4 ≤ 24 → (⟨addr (s.gpr .esp) (4 + k), 4⟩ : Region).Sub (argsA s) := by
    intro k hk
    have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
    have ek : addr (s.gpr .esp) (4 + k) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 k := by
      rw [addr_eq (by omega), VG.Offset.add_add]
    show Region.Sub ⟨addr (s.gpr .esp) (4 + k), 4⟩ ⟨argAddr s 0, 24⟩
    rw [e0, ek]; exact VG.Offset.sub_base _ hk
  have argSub : (Mode.argR s).Sub (argsA s) := by
    have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
    show Region.Sub ⟨addr (s.gpr .esp) 4, 8⟩ ⟨argAddr s 0, 24⟩
    rw [e0, show addr (s.gpr .esp) 4 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 + BitVec.ofNat 64 0 by
      rw [BitVec.add_zero]; exact addr_eq (by omega)]
    exact VG.Offset.sub_base _ (by decide)
  have mS := h.mem_wr_scr
  refine ⟨arg s 0, ⟨by omega, h.sp, ⟨_, h.mem_args, by
      show (⟨argAddr s 0, 24⟩ : Region).Contains (argAddr s 0) 8
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩, rfl, ?_, h.nv, h.fitK, ⟨_, h.mem_key,
    Region.contains_self _ _⟩, rfl, h.fitT, ⟨_, h.mem_tab, Region.contains_self _ _⟩, h.held,
    fun r hr => ⟨h.dKw r hr, h.dTw r hr, (h.dAw r hr).sub_left argSub⟩, h.dKs, h.dTs,
    (sA.symm.sub_left argSub)⟩, fun r hr => ?_⟩
  · show arg s 1 = BitVec.ofNat 32 (arg s 1).toNat
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [List.mem_singleton] at hr; subst hr; rw [scr_eq]
    exact ⟨h.dKw _ mS, h.dTw _ mS, (h.dAw _ mS).sub_left argSub, h.dSw _ mS⟩

/-- The data, in blocks. -/
abbrev dataAt (m : Mem) (s : State) : List (List Byte) :=
  Spec.Cast5.cbcBlocksAt m ((arg s 3).setWidth 64) (arg s 4).toNat
/-- The chaining value. -/
abbrev ivAt (m : Mem) (s : State) : List Byte := Spec.Aes.bytesAt m ((arg s 2).setWidth 64) 8
/-- CAST5 encryption under the key of `s`. -/
abbrev ciph (s : State) : Spec.Cbc.Cipher :=
  Spec.Cast5.cipher (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64)) (arg s 1).toNat
/-- CAST5 decryption under the key of `s`. -/
abbrev invCiph (s : State) : Spec.Cbc.Cipher :=
  Spec.Cast5.invCipher (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64)) (arg s 1).toNat

/-- The functions' postconditions. -/
def cbcEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cbc.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cbcDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cbc.decrypt (invCiph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)
def ofbPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Ofb.crypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Ofb.next (ciph s) (ivAt s.mem s) (arg s 4).toNat
def cfbEncPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (Spec.Cfb.encrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s))
def cfbDecPost (s s' : State) : Prop :=
  dataAt s'.mem s = Spec.Cfb.decrypt (ciph s) (ivAt s.mem s) (dataAt s.mem s) ∧
    ivAt s'.mem s = Spec.Cbc.next (ivAt s.mem s) (dataAt s.mem s)

@[simp] theorem dirCore_ka (up : Bool) : (dirCore up).ka = 2 := rfl

theorem data_eq (m : Mem) (s : State) :
    Proof.Modes.chunksAt 8 m ((arg s 3).setWidth 64) (arg s 4).toNat = dataAt m s :=
  (Proof.Cast5.cbcBlocksAt_eq _ _ _).symm
theorem iv_eq (m : Mem) (s : State) :
    Spec.Aes.bytesAt m ((arg s 2).setWidth 64) 8 = ivAt m s := rfl
theorem cipher_eq (s : State) :
    (dirCoreSpec true).cipher (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64), (arg s 1).toNat) = ciph s := rfl
theorem invCipher_eq (s : State) :
    (dirCoreSpec false).cipher (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64), (arg s 1).toNat) =
      invCiph s := rfl

tactic_template "post_eq_cast5_x86_modesverified" h:ident : tactic =>
  `(tactic| simp only [Proof.Modes.X86.blocks0, Proof.Modes.X86.iv0, Proof.Modes.X86.Dp,
                     Proof.Modes.X86.P, Proof.Modes.X86.N, dirCore_ka, Mode.dirCore_bw, Nat.reduceMul, Nat.reduceAdd,
                     data_eq, iv_eq, cipher_eq, invCipher_eq] at $h:ident)

theorem cbcEncryptChained_wp {s₀ : State} (hp : (modeX true cbcEncPost).pre s₀) :
    WP isa cbcEncryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true cbcEncPost).post s₀ s' :=
  WP.mono (cbcEncChained_wp (dirCoreSpec true) (seqPre_of true rfl rfl hp) (keyArgs_of true hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

theorem cbcDecryptChained_wp {s₀ : State} (hp : (modeX true cbcDecPost).pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true cbcDecPost).post s₀ s' :=
  WP.mono (cbcDecChained_wp (dirCoreSpec false) (seqPre_of false rfl rfl hp) (keyArgs_of false hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

theorem ofb_wp_x86 {s₀ : State} (hp : (modeX true ofbPost).pre s₀) :
    WP isa ofb s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true ofbPost).post s₀ s' :=
  WP.mono (ofb_wp (dirCoreSpec true) (seqPre_of true rfl rfl hp) (keyArgs_of true hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

theorem cfbEncrypt_wp {s₀ : State} (hp : (modeX true cfbEncPost).pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true cfbEncPost).post s₀ s' :=
  WP.mono (cfbEnc_wp (dirCoreSpec true) (seqPre_of true rfl rfl hp) (keyArgs_of true hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

theorem cfbDecrypt_wp {s₀ : State} (hp : (modeX true cfbDecPost).pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => abiPreserved s₀ s' ∧ (modeX true cfbDecPost).post s₀ s' :=
  WP.mono (cfbDec_wp (dirCoreSpec true) (seqPre_of true rfl rfl hp) (keyArgs_of true hp))
    fun _ ⟨h1, h2, h3⟩ => by post_eq_cast5_x86_modesverified h2; post_eq_cast5_x86_modesverified h3; exact ⟨h1, h2, h3⟩

/-! ## Constant time -/

/-- The initial taint of the modes: `esp` public, the words holding `data`,
`iv` and `scratch` known to be the base addresses of the writable regions,
and room for the core's word below `esp`. -/
def τFb : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 8, 304], argLen := 28,
    argBases := [(16, 0), (12, 1), (24, 2)], room := 4 }

theorem stk_eq (s : State) (h : 4 ≤ (s.gpr .esp).toNat) :
    (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ : Region) = stkA s := by
  show _ = (⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩ : Region)
  rw [VG.X86.Taint.sub_setWidth h]

theorem τFb_wf {s : State} (h : MPre true s) : VG.X86.Taint.Wf τFb s := by
  have hw := h.wrEq
  simp only [wrL] at hw
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [τFb]; have := h.espFit; omega, ?_⟩, ?_⟩ ?_
  · rw [hw]
    exact .cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil))
  · simp only [hw, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨⟨(h.dVD rfl).symm, h.dDS⟩, h.dVS, fun _ h => h.elim⟩
  · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · simp only [toNat_setWidth]; exact h.fitD
    · simp only [toNat_setWidth]; exact h.fitV
    · simp only [toNat_setWidth]; exact h.fitS
  · intro r hr
    exact VG.X86.Taint.frame_disjoint (n := 24) (by have := h.espFit; omega) (h.dRw r hr) (h.dAw r hr)
  · intro p hp
    simp only [τFb, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hw, addr, arg, argAddr]
  · intro _
    refine ⟨h.sp, fun r hr => ?_⟩
    simp only [τFb]
    rw [stk_eq s h.sp]
    exact h.dSw r hr

theorem argBytes_agree {τ : VG.X86.Taint.T} (hl : τ.argLen = 28) (hstk : τ.stk = []) {s₁ s₂ : State}
    (f₁ : (s₁.gpr .esp).toNat + 28 ≤ 2 ^ 32) (f₂ : (s₂.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    (ha : ∀ i < 6, arg s₁ i = arg s₂ i) {k : Nat} (h4 : 4 ≤ k) (hk : k < τ.argLen) :
    s₁.mem (VG.X86.Taint.argByte s₁ (VG.X86.Taint.depth τ.stk + k)) =
      s₂.mem (VG.X86.Taint.argByte s₂ (VG.X86.Taint.depth τ.stk + k)) := by
  rw [hl] at hk
  rw [hstk, show VG.X86.Taint.depth [] = 0 from rfl, Nat.zero_add]
  rw [VG.X86.Taint.argByte_eq (n := 28) f₁ h4 hk, VG.X86.Taint.argByte_eq (n := 28) f₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (ha _ (by omega))

theorem τFb_agree {post : State → State → Prop} {s₁ s₂ : State} (h₁ : (modeX true post).pre s₁)
    (h₂ : (modeX true post).pre s₂) (hp : (modeX true post).pub s₁ s₂) :
    VG.X86.Taint.AgreeS [s1234Sym] τFb s₁ s₂ := by
  obtain ⟨sp, args, sy⟩ := hp
  refine ⟨⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, τFb_wf h₁, τFb_wf h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp,
    fun k h4 hk => argBytes_agree rfl rfl h₁.espFit h₂.espFit args h4 hk⟩, fun n hn => ?_⟩
  · simp only [τFb, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · rw [h₁.wrEq, h₂.wrEq]
    simp only [wrL, dataA, ivA, scrA, args 2 (by decide), args 3 (by decide), args 4 (by decide),
      args 5 (by decide)]
  · simp only [List.mem_singleton] at hn
    subst hn; exact sy

theorem cbcEncryptChained_ct :
    ConstantTime isa (modeX true cbcEncPost).pre (modeX true cbcEncPost).pub cbcEncryptChained :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem cbcDecryptChained_ct :
    ConstantTime isa (modeX true cbcDecPost).pre (modeX true cbcDecPost).pub cbcDecryptChained :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem ofb_ct : ConstantTime isa (modeX true ofbPost).pre (modeX true ofbPost).pub ofb :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbEncrypt_ct : ConstantTime isa (modeX true cfbEncPost).pre (modeX true cfbEncPost).pub cfbEncrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

theorem cfbDecrypt_ct : ConstantTime isa (modeX true cfbDecPost).pre (modeX true cfbDecPost).pub cfbDecrypt :=
  VG.Taint.constantTime (A := taintSym [s1234Sym]) τFb (fun _ _ h₁ h₂ hp => τFb_agree h₁ h₂ hp)
    (by taint_decide)

/-! ## The contracts -/

open VG.Impl.Cast5 (ecbConsts)
open VG.Proof.Cast5.X86 (ecbConsts_eq s1234_length)

/-! ## Satisfiability -/

/-- The arguments of the witness at `0x8004`: the schedule at `0x1000`, 16
rounds, the chaining value at `0x2000`, no blocks at `0x3000` and the working
space at `0x4000`. -/
def satArgs : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8008 then 16 else if a = 0x800d then 0x20 else if a = 0x8011 then 0x30
  else if a = 0x8019 then 0x40 else 0

/-- The memory of the witness: the table at `0x100000`, the arguments
elsewhere (irreducible: unfolding it in a definitional check would evaluate
the table). -/
@[irreducible] def satMem : Mem := fun a =>
  if (a - 0x100000).toNat < 4096 then constMem 0x100000 s1234 a else satArgs a

theorem satMem_held : ∀ i < s1234.length,
    satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = s1234.getD i 0 := by
  intro i hi
  rw [s1234_length] at hi
  have hm : satMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 =
      (constMem 0x100000 s1234).readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 := by
    apply Mem.readW_congr
    intro j hj
    have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j - 0x100000).toNat = 8 * i + j := by
      rw [Offset.add_add, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold satMem
    rw [e, ite_eq_left (show 8 * i + j < 4096 by omega)]
  exact hm.trans (constMem_held 0x100000 s1234 (by rw [s1234_length]; decide) i (by rw [s1234_length]; exact hi))

/-- A state satisfying the modes' precondition, with the chaining value
readable (`ivw = false`) or writable. -/
def satState (ivw : Bool) : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := if ivw then [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩] else [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x100000, 4096⟩]
  wr := if ivw then [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩]
    else [⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩]
  syms _ := 0x100000

theorem sat_arg (ivw : Bool) (j : Nat) (hj : j < 6) : arg (satState ivw) j = satArgs.readW (argAddr (satState ivw) j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMem _ = _
  unfold satMem
  have : ∀ j < 6, ∀ b < 4, ¬ (argAddr (satState ivw) j + BitVec.ofNat 64 b - 0x100000).toNat < 4096 := by
    cases ivw <;> decide
  rw [ite_eq_right (this j hj b (by omega))]

/-! ## The functions with their working space on the stack -/

/-- A state satisfying the functions' precondition, with `336` bytes of
stack: the schedule at `0x1000`, the chaining value at `0x2000`, no blocks at
`0x3000`, as stack arguments at `0x8004`, which are writable. -/
def frameSat (ivw : Bool) : State where
  gpr r := match r with | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := if ivw then [⟨0x1000, 128⟩, ⟨0x100000, 4096⟩] else [⟨0x1000, 128⟩, ⟨0x2000, 8⟩, ⟨0x100000, 4096⟩]
  wr := if ivw then [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] else [⟨0x3000, 0⟩, ⟨0x8004, 20⟩]
  syms _ := 0x100000

theorem frameSat_arg (ivw : Bool) (j : Nat) (hj : j < 5) :
    arg (frameSat ivw) j = satArgs.readW (argAddr (frameSat ivw) j) 32 := by
  unfold arg
  apply Mem.readW_congr
  intro b hb
  change satMem _ = _
  unfold satMem
  have : ∀ j < 5, ∀ b < 4, ¬ (argAddr (frameSat ivw) j + BitVec.ofNat 64 b - 0x100000).toNat < 4096 := by
    cases ivw <;> decide
  rw [ite_eq_right (this j hj b (by omega))]

/-! ## OFB, CFB64 and CBC -/

/-- OFB's, CFB's or CBC's contract (`sig`, `ofbSig`, `cfbSig` or `cbcChainedSig`)
with the working space as a sixth argument, under the calling convention with the table. -/
abbrev fbK (sig : Sig) (pre : Curry (sig.words X86.abi.ptrBits) (Mem → Prop)) (post : sig.Post X86.abi.ptrBits) :
    Contract isa :=
  Sig.scratchContract (X86.abi.withConsts ecbConsts) sig "scratch" .u64 38 pre post true 4

theorem ofb_pre {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} (s : State)
    (h : (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s) :
    MPre true (s.withRegions (rdL true s) (wrL true s)) ∧ s.rd = [keyA s, tabA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrA s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, htake, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA,
    -, dRV, dRD, dRS, -, dBK, dBV, dBD, dBS, -, fK, fV, fD, fS, nv⟩ := h
  have hrd : s.rd = [keyA s, tabA s] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, VG.X86.Taint.sub_setWidth h4]
  have e8 : (arg s 4).toNat * 8 = 8 * (arg s 4).toNat := Nat.mul_comm _ _
  rw [e8] at hwr dKD dVD dDS dDA dRD dBD fD
  have mV : ivA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mD : dataA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : scrA s ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨⟨rfl, rfl, h4, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega), nv, fK, fV, fD, fS, fitT,
    (fun i hi => held i (by rw [s1234_length] at hi; exact hi)), dDS, dVS, (fun _ => dVD),
    (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dBK.symm),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dTB)⟩, hrd,
    (by rw [← e8] at hwr; exact hwr)⟩
  all_goals
    simp only [State.withRegions_wr, wrL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dTw _ mD
  · exact dTw _ mV
  · exact dTw _ mS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBS

theorem ofb_pub {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s₁)
    (_ : (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s₂)
    (h : (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeX true postX).pub (s₁.withRegions (rdL true s₁) (wrL true s₁))
      (s₂.withRegions (rdL true s₂) (wrL true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
  obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_, hsy⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem ofbK_verified {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} {postX : State → State → Prop}
    {c : Prog isa}
    (hwp : ∀ s, (modeX true postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeX true postX).post s s')
    (hct : ConstantTime isa (modeX true postX).pre (modeX true postX).pub c)
    (hpost : ∀ s s', (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdL true s) (wrL true s)) (s'.withRegions (rdL true s) (wrL true s)) →
        (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeX true postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (ofb_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdL true) (wrL true)
    (fun s h => (ofb_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost ofb_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := ofb_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdL, wrL, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := ofb_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrL, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem ofb_sat {post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits} :
    (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) post).pre (satState true) := by
  have a0 : arg (satState true) 0 = 0x1000 := (sat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (satState true) 1 = 16 := (sat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (satState true) 2 = 0x2000 := (sat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (satState true) 3 = 0x3000 := (sat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (satState true) 4 = 0 := (sat_arg true 4 (by decide)).trans (by decide)
  have a5 : arg (satState true) 5 = 0x4000 := (sat_arg true 5 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : satState true = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch]
  subst s
  rw [a0, a1, a2, a3, a4, a5]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem ofb_frameSat (post : Spec.Cast5.ofbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbSig.contract (X86.abi.withConsts ecbConsts) (Spec.Cast5.ofbPre X86.abi.ptrBits) post true
      336).pre s := by
  refine ⟨frameSat true, ?_⟩
  have a0 : arg (frameSat true) 0 = 0x1000 := (frameSat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (frameSat true) 1 = 16 := (frameSat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (frameSat true) 2 = 0x2000 := (frameSat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (frameSat true) 3 = 0x3000 := (frameSat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (frameSat true) 4 = 0 := (frameSat_arg true 4 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : frameSat true = s
  sig_pre [Spec.Cast5.ofbSig, Spec.Cast5.ofbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  rw [a0, a1, a2, a3, a4]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem cfb_pre {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} (s : State)
    (h : (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s) :
    MPre true (s.withRegions (rdL true s) (wrL true s)) ∧ s.rd = [keyA s, tabA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrA s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, htake, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA,
    -, dRV, dRD, dRS, -, dBK, dBV, dBD, dBS, -, fK, fV, fD, fS, nv⟩ := h
  have hrd : s.rd = [keyA s, tabA s] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, VG.X86.Taint.sub_setWidth h4]
  have e8 : (arg s 4).toNat * 8 = 8 * (arg s 4).toNat := Nat.mul_comm _ _
  rw [e8] at hwr dKD dVD dDS dDA dRD dBD fD
  have mV : ivA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mD : dataA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : scrA s ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨⟨rfl, rfl, h4, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega), nv, fK, fV, fD, fS, fitT,
    (fun i hi => held i (by rw [s1234_length] at hi; exact hi)), dDS, dVS, (fun _ => dVD),
    (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dBK.symm),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dTB)⟩, hrd,
    (by rw [← e8] at hwr; exact hwr)⟩
  all_goals
    simp only [State.withRegions_wr, wrL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dTw _ mD
  · exact dTw _ mV
  · exact dTw _ mS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBS

theorem cfb_pub {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s₁)
    (_ : (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s₂)
    (h : (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeX true postX).pub (s₁.withRegions (rdL true s₁) (wrL true s₁))
      (s₂.withRegions (rdL true s₂) (wrL true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
  obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_, hsy⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem cfbK_verified {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} {postX : State → State → Prop}
    {c : Prog isa}
    (hwp : ∀ s, (modeX true postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeX true postX).post s s')
    (hct : ConstantTime isa (modeX true postX).pre (modeX true postX).pub c)
    (hpost : ∀ s s', (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdL true s) (wrL true s)) (s'.withRegions (rdL true s) (wrL true s)) →
        (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeX true postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (cfb_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdL true) (wrL true)
    (fun s h => (cfb_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost cfb_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := cfb_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdL, wrL, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := cfb_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrL, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem cfb_sat {post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits} :
    (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) post).pre (satState true) := by
  have a0 : arg (satState true) 0 = 0x1000 := (sat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (satState true) 1 = 16 := (sat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (satState true) 2 = 0x2000 := (sat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (satState true) 3 = 0x3000 := (sat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (satState true) 4 = 0 := (sat_arg true 4 (by decide)).trans (by decide)
  have a5 : arg (satState true) 5 = 0x4000 := (sat_arg true 5 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : satState true = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch]
  subst s
  rw [a0, a1, a2, a3, a4, a5]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem cfb_frameSat (post : Spec.Cast5.cfbSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbSig.contract (X86.abi.withConsts ecbConsts) (Spec.Cast5.cfbPre X86.abi.ptrBits) post true
      336).pre s := by
  refine ⟨frameSat true, ?_⟩
  have a0 : arg (frameSat true) 0 = 0x1000 := (frameSat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (frameSat true) 1 = 16 := (frameSat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (frameSat true) 2 = 0x2000 := (frameSat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (frameSat true) 3 = 0x3000 := (frameSat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (frameSat true) 4 = 0 := (frameSat_arg true 4 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : frameSat true = s
  sig_pre [Spec.Cast5.cfbSig, Spec.Cast5.cfbPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  rw [a0, a1, a2, a3, a4]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl


theorem ofb_verified :
    Verified X86.target ofb
      (fbK Spec.Cast5.ofbSig (Spec.Cast5.ofbPre X86.abi.ptrBits) (Proof.Cast5.ofbPost X86.abi.ptrBits)) :=
  ofbK_verified (fun _ hs => ofb_wp_x86 hs) ofb_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.ofbSig, Proof.Cast5.ofbPost, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, ofb_sat⟩

/-- `ofb` with its working space on the stack. -/
theorem ofb_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 ofb)
      (Spec.Cast5.ofbContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Spec.Cast5.ofbPre X86.abi.ptrBits)
    (post := Proof.Cast5.ofbPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    ofb_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.ofbPost_local _) (Proof.Cast5.ofbPostOut_local _) (ofb_frameSat _)

theorem cfbEncrypt_verified :
    Verified X86.target cfbEncrypt
      (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) (Proof.Cast5.cfbEncPost X86.abi.ptrBits)) :=
  cfbK_verified (fun _ hs => cfbEncrypt_wp hs) cfbEncrypt_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbEncPost, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, cfb_sat⟩

/-- `cfbEncrypt` with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cfbEncrypt)
      (Spec.Cast5.cfbEncryptContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Spec.Cast5.cfbPre X86.abi.ptrBits)
    (post := Proof.Cast5.cfbEncPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cfbEncrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbEncPost_local _) (Proof.Cast5.cfbEncPostOut_local _) (cfb_frameSat _)

theorem cfbDecrypt_verified :
    Verified X86.target cfbDecrypt
      (fbK Spec.Cast5.cfbSig (Spec.Cast5.cfbPre X86.abi.ptrBits) (Proof.Cast5.cfbDecPost X86.abi.ptrBits)) :=
  cfbK_verified (fun _ hs => cfbDecrypt_wp hs) cfbDecrypt_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cfbSig, Proof.Cast5.cfbDecPost, X86.abi,
        X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, cfb_sat⟩

/-- `cfbDecrypt` with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cfbDecrypt)
      (Spec.Cast5.cfbDecryptContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Spec.Cast5.cfbPre X86.abi.ptrBits)
    (post := Proof.Cast5.cfbDecPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cfbDecrypt_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cfbDecPost_local _) (Proof.Cast5.cfbDecPostOut_local _) (cfb_frameSat _)

/-! ## CBC -/

theorem cbcC_pre {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} (s : State)
    (h : (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s) :
    MPre true (s.withRegions (rdL true s) (wrL true s)) ∧ s.rd = [keyA s, tabA s] ∧
      s.wr = [ivA s, ⟨(arg s 3).setWidth 64, (arg s 4).toNat * 8⟩, scrA s, argsA s] := by
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch] at h
  obtain ⟨h4, hsp, hdrop, held, fitT, dTw, -, dTB, htake, hwr, dKV, dKD, dKS, -, dVD, dVS, dVA, dDS, dDA, dSA,
    -, dRV, dRD, dRS, -, dBK, dBV, dBD, dBS, -, fK, fV, fD, fS, nv⟩ := h
  have hrd : s.rd = [keyA s, tabA s] := by
    rw [← List.take_append_drop (s.rd.length - 1) s.rd, htake, hdrop]; rfl
  have be : below (s.gpr .esp) 4 = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 4, 4⟩ := by
    simp only [below, VG.X86.Taint.sub_setWidth h4]
  have e8 : (arg s 4).toNat * 8 = 8 * (arg s 4).toNat := Nat.mul_comm _ _
  rw [e8] at hwr dKD dVD dDS dDA dRD dBD fD
  have mV : ivA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_self
  have mD : dataA s ∈ s.wr := by rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : scrA s ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨⟨rfl, rfl, h4, (by show (s.gpr .esp).toNat + 28 ≤ 2 ^ 32; omega), nv, fK, fV, fD, fS, fitT,
    (fun i hi => held i (by rw [s1234_length] at hi; exact hi)), dDS, dVS, (fun _ => dVD),
    (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_), (fun r hr => ?_),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dBK.symm),
    (by show Region.Disjoint _ (below (s.gpr .esp) 4); rw [be]; exact dTB)⟩, hrd,
    (by rw [← e8] at hwr; exact hwr)⟩
  all_goals
    simp only [State.withRegions_wr, wrL, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
  · exact dKD
  · exact dKV
  · exact dKS
  · exact dTw _ mD
  · exact dTw _ mV
  · exact dTw _ mS
  · exact dDA.symm
  · exact dVA.symm
  · exact dSA.symm
  · exact dRD
  · exact dRV
  · exact dRS
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBD
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBV
  · show Region.Disjoint (below (s.gpr .esp) 4) _; rw [be]; exact dBS

theorem cbcC_pub {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} {postX : State → State → Prop} (s₁ s₂ : State)
    (_ : (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s₁)
    (_ : (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s₂)
    (h : (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pub s₁ s₂) :
    (modeX true postX).pub (s₁.withRegions (rdL true s₁) (wrL true s₁))
      (s₂.withRegions (rdL true s₂) (wrL true s₂)) := by
  sig_pub [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch] at h
  obtain ⟨hsp, hsy, h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hsp, fun i hi => ?_, hsy⟩
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem cbcK_verified {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} {postX : State → State → Prop}
    {c : Prog isa}
    (hwp : ∀ s, (modeX true postX).pre s → WP isa c s fun s' => abiPreserved s s' ∧ (modeX true postX).post s s')
    (hct : ConstantTime isa (modeX true postX).pre (modeX true postX).pub c)
    (hpost : ∀ s s', (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s →
      postX (s.withRegions (rdL true s) (wrL true s)) (s'.withRegions (rdL true s) (wrL true s)) →
        (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).post s s')
    (hsat : ∃ s, (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre s) :
    Verified X86.target c (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post) := by
  have narrowSat : ∃ s, (modeX true postX).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, (cbcC_pre s hs).1⟩
  refine Verified.narrowTo (Verified.of_correct hwp hct (.refl narrowSat)) (rdL true) (wrL true)
    (fun s h => (cbcC_pre s h).1) (fun s h => ?_) (fun s h => ?_) hpost cbcC_pub hsat
  · obtain ⟨-, hrd, hwr⟩ := cbcC_pre s h
    rw [hrd, hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [rdL, wrL, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  · obtain ⟨-, -, hwr⟩ := cbcC_pre s h
    rw [hwr]
    refine Covers.of_mem fun r hr => ?_
    simp only [wrL, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rw [Nat.mul_comm]
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]

theorem cbcC_sat {post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits} :
    (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post).pre (satState true) := by
  have a0 : arg (satState true) 0 = 0x1000 := (sat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (satState true) 1 = 16 := (sat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (satState true) 2 = 0x2000 := (sat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (satState true) 3 = 0x3000 := (sat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (satState true) 4 = 0 := (sat_arg true 4 (by decide)).trans (by decide)
  have a5 : arg (satState true) 5 = 0x4000 := (sat_arg true 5 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : satState true = s
  sig_pre [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow,
    s1234_length, Curry.withScratch]
  subst s
  rw [a0, a1, a2, a3, a4, a5]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x4000, 304⟩, ⟨0x8004, 24⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem cbcC_frameSat (post : Spec.Cast5.cbcChainedSig.Post X86.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cbcChainedSig.contract (X86.abi.withConsts ecbConsts) (Proof.Cast5.cbcChainedPre X86.abi.ptrBits) post true
      336).pre s := by
  refine ⟨frameSat true, ?_⟩
  have a0 : arg (frameSat true) 0 = 0x1000 := (frameSat_arg true 0 (by decide)).trans (by decide)
  have a1 : arg (frameSat true) 1 = 16 := (frameSat_arg true 1 (by decide)).trans (by decide)
  have a2 : arg (frameSat true) 2 = 0x2000 := (frameSat_arg true 2 (by decide)).trans (by decide)
  have a3 : arg (frameSat true) 3 = 0x3000 := (frameSat_arg true 3 (by decide)).trans (by decide)
  have a4 : arg (frameSat true) 4 = 0 := (frameSat_arg true 4 (by decide)).trans (by decide)
  have held := satMem_held
  generalize e : frameSat true = s
  sig_pre [Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcChainedPre, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst s
  rw [a0, a1, a2, a3, a4]
  refine ⟨by decide, by decide, rfl, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ [⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0x8004, 20⟩] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inr rfl

theorem cbcEncryptChained_verified :
    Verified X86.target cbcEncryptChained
      (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits)
        (Proof.Cast5.cbcEncChainedPost X86.abi.ptrBits)) :=
  cbcK_verified (fun _ hs => cbcEncryptChained_wp hs) cbcEncryptChained_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcEncChainedPost,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, cbcC_sat⟩

/-- `cbcEncryptChained` with its working space on the stack. -/
theorem cbcEncryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cbcEncryptChained)
      (Spec.Cast5.cbcEncryptChainedContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Proof.Cast5.cbcChainedPre X86.abi.ptrBits)
    (post := Proof.Cast5.cbcEncChainedPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cbcEncryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cbcEncChainedPost_local _) (Proof.Cast5.cbcEncChainedPostOut_local _) (cbcC_frameSat _)

theorem cbcDecryptChained_verified :
    Verified X86.target cbcDecryptChained
      (fbK Spec.Cast5.cbcChainedSig (Proof.Cast5.cbcChainedPre X86.abi.ptrBits)
        (Proof.Cast5.cbcDecChainedPost X86.abi.ptrBits)) :=
  cbcK_verified (fun _ hs => cbcDecryptChained_wp hs) cbcDecryptChained_ct (fun s s' _ h => by
      sig_post [Sig.scratchContract, Sig.withScratch, Spec.Cast5.cbcChainedSig, Proof.Cast5.cbcDecChainedPost,
        X86.abi, X86.argSlots, X86.argVal, X86.argBytes, ecbConsts_eq, Abi.withConsts, Curry.withScratch]
      exact h) ⟨_, cbcC_sat⟩

/-- `cbcDecryptChained` with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratchWiped 332 5 76 cbcDecryptChained)
      (Spec.Cast5.cbcDecryptChainedContract (X86.abi.withConsts ecbConsts) 336) :=
  X86.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cbcChainedSig)
    (nm := "scratch") (e := .u64) (n := 38) (pre := Proof.Cast5.cbcChainedPre X86.abi.ptrBits)
    (post := Proof.Cast5.cbcDecChainedPost X86.abi.ptrBits) (wa := true) (stack := 4) (bytes := 332)
    cbcDecryptChained_verified (by decide) (by lit_decide) (by lit_decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.modePre_local _ vs m₁ m₂ hl h)
    (Proof.Cast5.cbcDecChainedPost_local _) (Proof.Cast5.cbcDecChainedPostOut_local _) (cbcC_frameSat _)

end VG.Proof.Cast5.X86.ModeFns
