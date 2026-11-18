module

import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
import VerifiedGarbage.Proof.MlKem.X86.Top
import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlKem.X86.Top
meta import VerifiedGarbage.Proof.Sha3.Stream
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Sign
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlKem.X86.TopCall
meta import VerifiedGarbage.Proof.Framework.Sig

/-! ### `MlDsa.X86.Message.VerifyCall`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86 (32-bit), `verify_message_cached`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. With `μ` at `X + 840`, the
call of `vg_mldsa*_verify(pk, μ, sig, scratch)` (`verifyCall_piece`): its
arguments in `eax`, `ecx`, `edx` and `ebx`, pushed; its precondition
(`verifyContract p X86.abi 96`), from `verify_message_cached`'s; what it
leaks, its inputs, which `verify_message_cached`'s inputs determine; and its
result, which is `verify_message_cached`'s. For `na` arguments (8, with the
cached `tr`), and the read-only regions `T` after the others (`VPre`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR LeafEnd)
open VG.Proof.MlKem.X86.Top (entry_regions entry_self covers_of)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- A verification function on `μ`, as `verify_message_cached` calls it. -/
structure VerifyFn (p : Params) (K : KeyArg) (c : Prog isa) : Prop where
  ver : Verified X86.target c (verifyKContract p K X86.abi 136)
  nosp : NoSp c
  su : stackUse c ≤ 136

/-- The arguments of the call of the verification function on `μ`, and their registers. -/
abbrev verifyArgs : List (Reg × Arg) := [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6)]
abbrev rs4 : List Reg := [.ebx, .edx, .ecx, .eax]

section
variable (p : Params) (K : KeyArg) (na : Nat) (s₀ : State)

/-- The message representative of the run from `s₀`. -/
abbrev vMu : List Byte :=
  H (H (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) 64 ++ hdrBytes (vlay p K na s₀) ++
    bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++ bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
    64

/-- The regions the verification function on `μ` is given. -/
abbrev vRd : List Region :=
  [⟨(arg s₀ 0).setWidth 64, K.len⟩, ⟨((vlay p K na s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩,
    ⟨(arg s₀ 5).setWidth 64, p.sigLen⟩]
abbrev vWr : List Region := [⟨(arg s₀ 6).setWidth 64, sScr p⟩, below (vlay p K na s₀).E1 16]

/-- What `verify_message_cached` changes: `scratch` and the stack. -/
abbrev vW : List Region := [(vlay p K na s₀).SC, (vlay p K na s₀).STK]

/-- The result. -/
def VB (s : State) : Prop :=
  (arg s₀ 4).toNat < 256 ∧
    ((s.gpr .eax = 1 ∧ ∃ b, verifyMu p b (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) (vMu p K na s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen) = some true) ∨
      (s.gpr .eax = 0 ∧ verifyMu p minBounds (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) (vMu p K na s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen) ≠ some true))

end

section
variable {p : Params} {K : KeyArg} {na : Nat} {T : State → List Region}

theorem verifyArgs_ok : argsOk 7 verifyArgs = true := by decide

theorem verifyArgs_okN (h : na = 7 ∨ na = 8) : argsOk na verifyArgs = true := by
  rcases h with rfl | rfl <;> decide

/-- The values of the arguments. -/
theorem verifyArgs_val {s₀ s s₁ : State} (h₀ : VPre p K na T s₀) (hc : CtxO (vlay p K na) s₀ s)
    (hs : SetPost verifyArgs s s₁) :
    s₁.gpr .eax = arg s₀ 0 ∧ s₁.gpr .ecx = (vlay p K na s₀).X32 + BitVec.ofNat 32 840 ∧ s₁.gpr .edx = arg s₀ 5 ∧
      s₁.gpr .ebx = arg s₀ 6 := by
  have h7 : ∀ {i}, i < 7 → i < (vlay p K na s₀).nA := fun h => by have := h₀.hn; show _ < na; omega_using [h, this]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hs.1 (.eax, .arg 0) (by simp), hc.ctx.argV (h7 (by decide))]; rfl
  · rw [hs.1 (.ecx, .off oMU) (by simp), hc.ctx.off]; rfl
  · rw [hs.1 (.edx, .arg 5) (by simp), hc.ctx.argV (h7 (by decide))]; rfl
  · rw [hs.1 (.ebx, .arg 6) (by simp), hc.ctx.argV (h7 (by decide))]; rfl

/-- The facts about regions the call needs. -/
structure VRegs (p : Params) (K : KeyArg) (na : Nat) (s₀ : State) : Prop where
  hE : 156 ≤ (vlay p K na s₀).E1.toNat
  scrSub : Region.Sub ⟨(arg s₀ 6).setWidth 64, sScr p⟩ (vlay p K na s₀).SC
  argsSub : Region.Sub (below (vlay p K na s₀).E1 16) (vlay p K na s₀).STK
  muSub : Region.Sub ⟨((vlay p K na s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (vlay p K na s₀).SC
  kPk : (vlay p K na s₀).STK.Disjoint ⟨(arg s₀ 0).setWidth 64, K.len⟩
  kMu : (vlay p K na s₀).STK.Disjoint ⟨((vlay p K na s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩
  kSig : (vlay p K na s₀).STK.Disjoint ⟨(arg s₀ 5).setWidth 64, p.sigLen⟩
  kScr : (vlay p K na s₀).STK.Disjoint ⟨(arg s₀ 6).setWidth 64, sScr p⟩
  muScr : Region.Disjoint ⟨((vlay p K na s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ ⟨(arg s₀ 6).setWidth 64, sScr p⟩

theorem vregs {s₀ : State} (h₀ : VPre p K na T s₀) (hL : (vlay p K na s₀).Ok) : VRegs p K na s₀ := by
  have hsp := h₀.sp
  have hE : 156 ≤ (vlay p K na s₀).E1.toNat := by
    show 156 ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega_arith)]; omega_arith
  have hk : ∀ {R : Region}, (sStk s₀ 172).Disjoint R → (vlay p K na s₀).STK.Disjoint R := fun h =>
    (stk_eq hsp ▸ h).sub_left hL.stk_sub
  have scrSub : Region.Sub ⟨(arg s₀ 6).setWidth 64, sScr p⟩ (vlay p K na s₀).SC :=
    (within_base _ (by show sScr p ≤ mScrLen p; simp only [sScr, mScrLen, messageScratchWords]; omega_arith)).sub
  have muSub : Region.Sub ⟨((vlay p K na s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (vlay p K na s₀).SC := by
    rw [mu_eq hL]; exact hL.sub_sc (e := 840) (k := 64) (by omega_arith)
  refine ⟨hE, scrSub, below_sub (by show 16 ≤ 172 - 16; decide) (by show 172 - 16 ≤ _; omega_arith), muSub, hk h₀.kPk,
    by rw [mu_eq hL]; exact k_mu hL, hk h₀.kSig, hL.kSC.sub_right scrSub, ?_⟩
  have hx := hL.x_eq
  have := h₀.nScr
  have := mScr_eq p
  have e : ((vlay p K na s₀).X32 + BitVec.ofNat 32 840).setWidth 64 =
      (arg s₀ 6).setWidth 64 + BitVec.ofNat 64 (oE p + 840) := by
    rw [mu_eq hL, Lay.MU, hx, add_add]; rfl
  rw [e]
  have d := Offset.disjoint ((arg s₀ 6).setWidth 64) (d := oE p + 840) (n := 64) (e := 0) (k := sScr p)
    (.inr (by simp only [oE, sScr]; omega_arith)) (by omega_arith) (by simp only [oE, sScr] at *; omega_arith)
  rwa [BitVec.add_zero] at d

/-- Bytes apart from the stack and from `scratch` are, on the callee's entry, as on `verify_message`'s. -/
theorem verify_bytes {s₀ s s₁ : State} (h₀ : VPre p K na T s₀) (hc : CtxO (vlay p K na) s₀ s)
    (hs : SetPost verifyArgs s s₁) {R : Region} (hk : (sStk s₀ 172).Disjoint R) (hx : (vlay p K na s₀).SC.Disjoint R)
    (hn : R.len ≤ 2 ^ 64) : bytesAt (pushed rs4 s₁).callEntry.mem R.base R.len = bytesAt s₀.mem R.base R.len := by
  have hL := hc.ok
  have hc1 := SetPost.ctx verifyArgs_ok hs hc.ctx
  have hE := (vregs h₀ hL).hE
  have hsp1 : s₁.gpr .esp = (vlay p K na s₀).E1 := hc1.esp
  have fit : 4 * rs4.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega_arith
  have fr := callEntry_frame fit (by decide : Reg.esp ∉ rs4)
  rw [hsp1] at fr
  have b20 : Region.Sub (below (vlay p K na s₀).E1 (4 * rs4.length + 4)) (vlay p K na s₀).STK :=
    below_sub (by show 20 ≤ 172 - 16; decide) (by show 172 - 16 ≤ _; omega_arith)
  have hsp := h₀.sp
  have hkS : (vlay p K na s₀).STK.Disjoint R := (stk_eq hsp ▸ hk).sub_left hL.stk_sub
  rw [Proof.MlKem.bytesAt_congr fun _ hi => fr.bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hkS.sub_left b20).symm) hn hi,
    hs.2.mem, hc.ctx.bytesAt_eq hx hkS hn]
  exact p0_bytes (by decide) hsp hk hn

/-- The encoded key, on the callee's entry. -/
theorem verify_bPk {s₀ s s₁ : State} (hK : K.Ok p.pkLen) (h₀ : VPre p K na T s₀) (hc : CtxO (vlay p K na) s₀ s)
    (hs : SetPost verifyArgs s s₁) {l : Nat} (hl : l ≤ K.len) :
    bytesAt (pushed rs4 s₁).callEntry.mem ((arg s₀ 0).setWidth 64) l =
      bytesAt s₀.mem ((arg s₀ 0).setWidth 64) l := by
  have w : Region.Sub ⟨(arg s₀ 0).setWidth 64, l⟩ ⟨(arg s₀ 0).setWidth 64, K.len⟩ := (within_base _ hl).sub
  have := hK.lt
  exact verify_bytes (R := ⟨_, l⟩) h₀ hc hs (h₀.kPk.sub_right w) (hc.ok.xKey.sub_right w) (by show l ≤ 2 ^ 64; omega_using [hl, this])

/-- The callee's precondition. -/
theorem verify_callPre {s₀ s s₁ : State} (hK : K.Ok p.pkLen) (h₀ : VPre p K na T s₀) (hc : CtxO (vlay p K na) s₀ s)
    (hs : SetPost verifyArgs s s₁) : CallPre (verifyKContract p K X86.abi 136) rs4 (vRd p K na s₀) (vWr p K na s₀) s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx verifyArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3⟩ := verifyArgs_val h₀ hc hs
  have R := vregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (vlay p K na s₀).E1 := hc1.esp
  have fit : 4 * rs4.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega_arith
  have a0 : arg (pushed rs4 s₁).callEntry 0 = arg s₀ 0 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v0
  have a1 : arg (pushed rs4 s₁).callEntry 1 = (vlay p K na s₀).X32 + BitVec.ofNat 32 840 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v1
  have a2 : arg (pushed rs4 s₁).callEntry 2 = arg s₀ 5 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v2
  have a3 : arg (pushed rs4 s₁).callEntry 3 = arg s₀ 6 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v3
  have eA : argAddr (pushed rs4 s₁).callEntry 0 = ((vlay p K na s₀).E1 - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0, hsp1]; rfl
  have eSp : (pushed rs4 s₁).callEntry.gpr .esp = (vlay p K na s₀).E1 - BitVec.ofNat 32 (4 * 4 + 4) := by
    rw [callEntry_esp', hsp1]; rfl
  have cv := covers_of (s := s₁) (n := 4) (rd := vRd p K na s₀) (wr := vWr p K na s₀) (fun r hr => ?_) fun r hr => ?_
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact withinRW hc1 ⟨_, List.mem_append_left _ hL.inKey, within_self _⟩
    · exact withinRW hc1 (by rw [mu_eq hL]; exact cov_x hL (e := 840) (k := 64) (by omega_arith))
    · exact withinRW hc1 ⟨_, List.mem_append_left _ (by show _ ∈ s₀.rd; rw [h₀.rd]; simp), within_self _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (withinW hc1 ⟨_, hL.inSC, within_base _
        (by show sScr p ≤ mScrLen p; simp only [sScr, mScrLen, messageScratchWords]; omega_arith)⟩)
    · exact .inl (by rw [hsp1])
  refine ⟨?_, cv.1, cv.2⟩
  obtain ⟨rPk₁, rPk₂, rPk₃⟩ := entry_regions (E := (vlay p K na s₀).E1) (k := 4) (K := 136) (by omega_arith) R.kPk
  obtain ⟨rMu₁, rMu₂, rMu₃⟩ := entry_regions (E := (vlay p K na s₀).E1) (k := 4) (K := 136) (by omega_arith) R.kMu
  obtain ⟨rSig₁, rSig₂, rSig₃⟩ := entry_regions (E := (vlay p K na s₀).E1) (k := 4) (K := 136) (by omega_arith) R.kSig
  obtain ⟨rScr₁, rScr₂, rScr₃⟩ := entry_regions (E := (vlay p K na s₀).E1) (k := 4) (K := 136) (by omega_arith) R.kScr
  obtain ⟨rA₂, rA₃⟩ := entry_self (E := (vlay p K na s₀).E1) (k := 4) (K := 136) (by omega_arith)
  generalize he : (pushed rs4 s₁).callEntry = e at a0 a1 a2 a3 eA eSp ⊢
  sig_pre [verifyKContract, verifyKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  subst he
  simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp]
  have hX := hL.x32_lt
  refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (vlay p K na s₀).E1.isLt; omega_arith,
    trivial, trivial, h₀.pkScr.sub_right R.scrSub, rPk₁, R.muScr, rMu₁, h₀.sigScr.sub_right R.scrSub, rSig₁, rScr₁,
    rPk₂, rMu₂, rSig₂, rScr₂, rA₂, rPk₃, rMu₃, rSig₃, rScr₃, rA₃, h₀.nPk,
    by rw [hL.x32_toNat (by omega_arith)]; omega_arith, h₀.nSig,
    by have := h₀.nScr; simp only [mScrLen, messageScratchWords] at this ⊢; omega_arith,
    hK.congr (verify_bPk hK h₀ hc hs (Nat.le_refl _)) h₀.kp⟩


/-- What the verification function on `μ` sees on entry. -/
structure VView (p : Params) (K : KeyArg) (na : Nat) (s₀ s₁ : State) : Prop where
  a0 : arg (pushed rs4 s₁).callEntry 0 = arg s₀ 0
  a1 : arg (pushed rs4 s₁).callEntry 1 = (vlay p K na s₀).X32 + BitVec.ofNat 32 840
  a2 : arg (pushed rs4 s₁).callEntry 2 = arg s₀ 5
  a3 : arg (pushed rs4 s₁).callEntry 3 = arg s₀ 6
  esp : (pushed rs4 s₁).callEntry.gpr .esp = (vlay p K na s₀).E1 - BitVec.ofNat 32 (4 * 4 + 4)
  bPk : bytesAt (pushed rs4 s₁).callEntry.mem ((arg s₀ 0).setWidth 64) p.pkLen =
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen
  bMu : bytesAt (pushed rs4 s₁).callEntry.mem (((vlay p K na s₀).X32 + BitVec.ofNat 32 840).setWidth 64) 64 = vMu p K na s₀
  bSig : bytesAt (pushed rs4 s₁).callEntry.mem ((arg s₀ 5).setWidth 64) p.sigLen =
    bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen

theorem verify_view {s₀ s s₁ : State} (hK : K.Ok p.pkLen) (h₀ : VPre p K na T s₀) (hc : CtxO (vlay p K na) s₀ s)
    (hμ : bytesAt s.mem (vlay p K na s₀).MU 64 = vMu p K na s₀) (hs : SetPost verifyArgs s s₁) :
    VView p K na s₀ s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx verifyArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3⟩ := verifyArgs_val h₀ hc hs
  have R := vregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (vlay p K na s₀).E1 := hc1.esp
  have fit : 4 * rs4.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega_arith
  have fr := callEntry_frame fit (by decide : Reg.esp ∉ rs4)
  rw [hsp1] at fr
  have b20 : Region.Sub (below (vlay p K na s₀).E1 (4 * rs4.length + 4)) (vlay p K na s₀).STK :=
    below_sub (by show 20 ≤ 172 - 16; decide) (by show 172 - 16 ≤ _; omega_arith)
  refine ⟨by rw [callEntry_arg fit (by decide) (by decide)]; exact v0,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v1,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v2,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v3,
    by rw [callEntry_esp', hsp1]; rfl, verify_bPk hK h₀ hc hs hK.le, ?_,
    verify_bytes (R := ⟨_, p.sigLen⟩) h₀ hc hs h₀.kSig h₀.sigScr.symm
      (by show p.sigLen ≤ 2 ^ 64; have := h₀.nSig; omega_arith)⟩
  rw [Proof.MlKem.bytesAt_congr fun _ hi => fr.bytes (R := ⟨_, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (R.kMu.sub_left b20).symm) (by show 64 ≤ 2 ^ 64; decide) hi,
    hs.2.mem, mu_eq hL]
  exact hμ

/-- Two runs with the same public data have the same `μ`, and the same inputs. -/
theorem vInputs_pub {s₀ s₀' : State} (h₀ : VPre p K na T s₀) (hq : VPub p na s₀ s₀') :
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen = bytesAt s₀'.mem ((arg s₀' 0).setWidth 64) p.pkLen ∧
      vMu p K na s₀ = vMu p K na s₀' ∧
      bytesAt s₀.mem ((arg s₀ 5).setWidth 64) p.sigLen = bytesAt s₀'.mem ((arg s₀' 5).setWidth 64) p.sigLen := by
  obtain ⟨e₁, e₂, e₃, e₄⟩ := leak4 (by simp only [Proof.MlKem.bytesAt_length])
    (by simp only [Proof.MlKem.bytesAt_length, hq.args 2 (by have := h₀.hn; omega_using [this])])
    (by simp only [Proof.MlKem.bytesAt_length, hq.args 4 (by have := h₀.hn; omega_using [this])]) hq.leak
  refine ⟨e₁, ?_, e₄⟩
  simp only [vMu, hdrBytes, vlay, e₁, e₂, e₃]
  rw [hq.args 4 (by have := h₀.hn; omega_using [this])]

/-- The call of the verification function on `μ`. -/
theorem verifyCall_piece (hK : K.Ok p.pkLen) {n : String} {f : Prog isa} (hf : VerifyFn p K f) :
    Piece (VPre p K na T) (VPub p na) (fun s₀ s => CtxO (vlay p K na) s₀ s ∧ bytesAt s.mem (vlay p K na s₀).MU 64 = vMu p K na s₀)
      (fun s₀ s => LeafEnd s₀ (vW p K na s₀) s ∧ VB p K na s₀ s)
      (.seq (.block (setArgs verifyArgs)) (Impl.MlKem.X86.callRet rs4 n f)) := by
  refine argsRet_piece hf.ver.1 hf.ver.2.1 hf.nosp (by decide) (by decide) (by native_taint_decide) (vShape hK).pubL
    (fun _ _ _ h => h.1) (fun _ h₀ => verifyArgs_okN h₀.hn) (vRd p K na) (vWr p K na)
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => verify_callPre hK h₀ ha.1 hs)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · refine ⟨?_, ?_⟩
    · simp only [vRd, Lay.X32, vlay, hq.args 0 (by have := h₀.hn; omega_using [this]), hq.args 5 (by have := h₀.hn; omega_using [this]), hq.args 6 (by have := h₀.hn; omega_using [this])]
    · simp only [vWr, Lay.E1, vlay, hq.esp, hq.args 6 (by have := h₀.hn; omega_using [this])]
  · have := hf.su
    have := h₀.sp
    show _ ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega_arith)]
    simp only [List.length_cons, List.length_nil]
    omega_arith
  · obtain ⟨hc, hμ⟩ := ha
    obtain ⟨hc', hμ'⟩ := ha'
    have hp' := (vShape hK).pubL s₀ s₀' h₀ h₀' hq
    obtain ⟨i₁, i₂, i₃⟩ := vInputs_pub h₀ hq
    obtain ⟨a0, a1, a2, a3, eS, bPk, bMu, bSig⟩ := verify_view hK h₀ hc hμ hs
    obtain ⟨a0', a1', a2', a3', eS', bPk', bMu', bSig'⟩ := verify_view hK h₀' hc' hμ' hs'
    generalize (pushed rs4 s₁).callEntry = e at a0 a1 a2 a3 eS bPk bMu bSig ⊢
    generalize (pushed rs4 s₁').callEntry = e' at a0' a1' a2' a3' eS' bPk' bMu' bSig' ⊢
    sig_pub [verifyKContract, verifyKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a0', a1', a2', a3', eS, eS']
    rw [bPk, bMu, bSig, bPk', bMu', bSig', i₁, i₂, i₃]
    exact ⟨by simp only [Lay.E1, hp'.sp], rfl, hq.args 0 (by have := h₀.hn; omega_using [this]), by rw [hp'.x], hq.args 5 (by have := h₀.hn; omega_using [this]),
      hq.args 6 (by have := h₀.hn; omega_using [this])⟩
  · obtain ⟨hc, hμ⟩ := ha
    have hL := hc.ok
    have R := vregs h₀ hL
    have hE := R.hE
    have hsp1 : s₁.gpr .esp = (vlay p K na s₀).E1 := (SetPost.ctx verifyArgs_ok hs hc.ctx).esp
    refine ⟨CtxO.leafEnd (vShape hK) h₀ hc (W := vW p K na s₀) (by simp) (rs := vWr p K na s₀ ++
        [below (s₁.gpr .esp) (4 * rs4.length + stackUse f + 4)]) (by rw [← hs.2.mem]; exact fr)
        (fun r hr => ?_) ((e₃ .esp (by decide)).trans (hs.esp verifyArgs_ok)) (e₁.trans hs.2.rd)
        (e₂.trans hs.2.wr), ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨(vlay p K na s₀).SC, by simp, R.scrSub⟩
      · exact ⟨(vlay p K na s₀).STK, by simp, R.argsSub⟩
      · refine ⟨(vlay p K na s₀).STK, by simp, ?_⟩
        rw [hsp1]
        have := hf.su
        exact below_sub (by show _ ≤ 172 - 16; simp only [List.length_cons, List.length_nil]; omega_arith)
          (by show 172 - 16 ≤ _; omega_arith)
    · have v := verify_view hK h₀ hc hμ hs
      obtain ⟨s₂, -, g₂, post⟩ := post
      obtain ⟨a0, a1, a2, -, -, bPk, bMu, bSig⟩ := v
      generalize (pushed rs4 s₁).callEntry = e at a0 a1 a2 bPk bMu bSig post
      sig_post [verifyKContract, verifyKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
      simp only [arg_withRegions, a0, a1, a2] at post
      rw [bPk, bMu, bSig, Proof.MlKem.X86.setWidth_append32, g₂] at post
      exact ⟨hc.ok.ctxLt, post⟩

end

end VG.Proof.MlDsa.X86.Message

end

end

/-!
# ML-DSA on x86 (32-bit), `verify_message_cached`: correct and constant time

Untrusted: everything here is checked by Lean. The body past the entry:
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` from the `tr` argument, which the
precondition says is `H(pk, 64)`, then the call of the verification function
on it (`cachedRest_piece`); in the leaf, after the check
(`verifyMessageCached_piece`); and what that says of the contract's
postcondition (`verifyMessageCached_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece P0 E0 frameR retR LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

section
variable {p : Params} {K : KeyArg}

theorem H_length (s : List Byte) (n : Nat) : (H s n).length = n :=
  Proof.Sha3.length_squeeze (by decide) (by decide) _ _

/-- What `verify_message_cached` changes is apart from its frame and return address. -/
theorem verify_hW {na : Nat} {T : State → List Region} :
    ∀ s₀, VPre p K na T s₀ → ∀ r ∈ vW p K na s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro s₀ h₀ r hr
  have hsp := h₀.sp
  have fr : Region.Sub (frameR s₀) (sStk s₀ 172) := by rw [stk_eq hsp]; exact below_sub (by decide) hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨h₀.kScr.sub_left fr, h₀.rScr⟩
  · exact ⟨Proof.MlKem.X86.Top.below_adj (sp := s₀.gpr .esp) (a := 16) (b := 172 - 16) (by omega_using [hsp]),
      (Proof.MlKem.X86.Top.ret_below hsp).sub_right (below_inner (a := 172 - 16) (k := 16) (by omega_using []) hsp)⟩

/-- `μ` from the cached `tr`, then the call of the verification function on it. -/
theorem cachedRest_piece (hK : K.Ok p.pkLen) {n : String} {f : Prog isa} (hf : VerifyFn p K f) :
    Piece (CPre p K) (VPub p 8) (CtxO (vlay p K 8)) (fun s₀ s => LeafEnd s₀ (vW p K 8 s₀) s ∧ VB p K 8 s₀ s)
      (.seq (muHash (.arg 7)) (.seq (.block (setArgs verifyArgs)) (Impl.MlKem.X86.callRet rs4 n f))) := by
  have hk : ∀ {s₀ : State} {R : Region}, CPre p K s₀ → (vlay p K 8 s₀).Ok → (sStk s₀ 172).Disjoint R →
      (vlay p K 8 s₀).STK.Disjoint R := fun h₀ hL h => (stk_eq h₀.sp ▸ h).sub_left hL.stk_sub
  refine Piece.seq ((muHash_piece (lay := vlay p K 8) (.arg 7) (fun s₀ => arg s₀ 7)
    (fun s₀ => H (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.pkLen) 64) (by native_taint_decide)
    (fun s₀ s₀' h₀ h₀' hq => (vShape hK).pubL s₀ s₀' h₀.toVPre h₀'.toVPre hq) (fun _ _ _ h => h)
    (fun _ _ => by show 5 ≤ 8; decide) (fun _ _ => rfl) rfl
    (fun s₀ s h₀ hc => hc.ctx.argV (by show 7 < 8; decide)) (fun s₀ s₀' h₀ h₀' hq => hq.args 7 (by decide))
    (fun s₀ s h₀ hc => ?_) (fun _ _ => H_length _ _) (fun s₀ h₀ hL => ?_)).mono
    (fun _ _ _ h => h) fun s₀ s h₀ ⟨hc, hm⟩ => ⟨hc, ?_⟩)
    ((verifyCall_piece hK hf).pre_mono (fun _ h => h.toVPre) fun _ _ _ _ h => h)
  · have hL := hc.ok
    rw [hc.ctx.bytesAt_eq h₀.scrTr (hk h₀ hL h₀.kTr) (by decide), p0_bytes (by decide) h₀.sp h₀.kTr (by decide)]
    exact h₀.tr
  · have hst : Region.Sub ⟨(vlay p K 8 s₀).ST, 200⟩ (vlay p K 8 s₀).SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega_using [])
      simpa only [x0] using this
    exact ⟨h₀.nTr, ⟨aR s₀ 7 64, List.mem_append_left _ (by show _ ∈ s₀.rd; rw [h₀.rd]; simp), within_self _⟩,
      h₀.scrTr.symm.sub_right hst, h₀.scrTr.symm.sub_right (hL.sub_sc (by omega_using [] : 200 + 640 ≤ 1024)),
      hk h₀ hL h₀.kTr⟩
  · rw [hm]
    simp only [ctxB, msgB]
    rw [p0_bytes (a := (vlay p K 8 s₀).ctx.setWidth 64) (n := (vlay p K 8 s₀).ctxLen.toNat) (by decide) h₀.sp h₀.kCtx
        (by have := (arg s₀ 4).isLt; show (arg s₀ 4).toNat ≤ _; omega_using []),
      p0_bytes (a := (vlay p K 8 s₀).msg.setWidth 64) (n := (vlay p K 8 s₀).len.toNat) (by decide) h₀.sp h₀.kMsg
        (by have := (arg s₀ 2).isLt; show (arg s₀ 2).toNat ≤ _; omega_using [])]
    rfl

/-- What `verify_message_cached` runs after `enter` never writes `esp`, if the
verification function it calls does not. -/
theorem cachedRest_nosp {n : String} {f : Prog isa} (hf : NoSp f) :
    NoSp (.seq (muHash (.arg 7))
      (.seq (.block (setArgs [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6)]))
        (Impl.MlKem.X86.callRet [.ebx, .edx, .ecx, .eax] n f))) :=
  nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_seq (NoSp.of_all (by decide +kernel)) (callRet_nosp hf))

/-- `verify_message_cached` never writes `esp`, if the verification function it
calls does not. -/
theorem verifyMessageCached_nosp (p : Params) {n : String} {f : Prog isa} (hf : NoSp f) :
    NoSp (verifyMessageCached n f p) :=
  KeyGen.NoSp.leaf (topBody_nosp 6 p (cachedRest_nosp hf))

/-- `verify_message_cached`, in its leaf. -/
theorem verifyMessageCached_piece (hK : K.Ok p.pkLen) {n : String} {f : Prog isa} (hf : VerifyFn p K f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 6)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Piece (CPre p K) (VPub p 8) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ VB p K 8 s₀ s) s₀ s') (verifyMessageCached n f p) :=
  top_piece ((vShape hK).pre_mono fun _ h => h.toVPre) tt (vW p K 8) (fun s₀ h₀ => verify_hW s₀ h₀.toVPre)
    (topBody_nosp 6 p (cachedRest_nosp hf.nosp)) (cachedRest_piece hK hf)

/-- Memory with the arguments `0`, `0x2000`, `0`, `0x2000`, `0`, `0x3000`,
`0x10000` and `0x8000` at `0x5004`. -/
def satMemC0 : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else
  if a = 0x501e then 1 else if a = 0x5021 then 0x80 else 0

/-- `satMemC0`, with `tr = H(pk, 64)` at `0x8000`. -/
def satMemC (p : Params) : Mem := fun a =>
  if 0x8000 ≤ a.toNat ∧ a.toNat < 0x8040 then (pkTr (bytesAt satMemC0 0 p.pkLen)).getD (a.toNat - 0x8000) 0
  else satMemC0 a

theorem satMemC_digest {p : Params} (hp : p.pkLen < 0x8000) :
    bytesAt (satMemC p) 0x8000 64 = pkTr (bytesAt (satMemC p) 0 p.pkLen) := by
  have hk : bytesAt (satMemC p) 0 p.pkLen = bytesAt satMemC0 0 p.pkLen := Proof.MlKem.bytesAt_congr fun i hi => by
    have he : ((0 : Addr) + BitVec.ofNat 64 i).toNat = i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega_using [hp, hi]
    simp only [satMemC, he, show ¬(0x8000 ≤ i ∧ i < 0x8040) by omega_using [hp, hi], ↓reduceIte]
  rw [hk]
  apply Proof.MlKem.bytesAt_eq (H_length _ _)
  intro i hi
  have he : ((0x8000 : Addr) + BitVec.ofNat 64 i).toNat = 0x8000 + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega_using [hi]
  simp only [satMemC, he, show 0x8000 ≤ 0x8000 + i ∧ 0x8000 + i < 0x8040 by omega_using [hi], and_self, ↓reduceIte,
    Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [pkTr, H_length]; omega_using [hi]), Option.getD_some]
  rfl

/-- A state satisfying the precondition of `verify_message_cached`. -/
def cachedSat (p : Params) : State :=
  Proof.MlKem.X86.satState (satMemC p) [⟨0, p.pkLen⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, p.sigLen⟩, ⟨0x8000, 64⟩]
    [⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]

/-- Its arguments, as `satMemC0` holds them. -/
theorem cachedSat_arg {p : Params} (i : Nat) (hi : i < 8) :
    arg (cachedSat p) i = (satMemC0.readW ((0x5000 + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32) :=
  Mem.readW_congr fun j hj => by
    have he : (argAddr (cachedSat p) i + BitVec.ofNat 64 j).toNat = 0x5004 + 4 * i + j := by
      show (((0x5000 : BitVec 32) + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 + BitVec.ofNat 64 j).toNat = _
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega_using [hi, hj]
    show satMemC p _ = _
    simp only [satMemC, he, show ¬(0x8000 ≤ 0x5004 + 4 * i + j ∧ 0x5004 + 4 * i + j < 0x8040) by omega_using [hi, hj], ↓reduceIte]

theorem verifyMessageCached_verified (hK : K.Ok p.pkLen) {VP : Mem → Addr → Addr → Prop}
    (hV : ∀ {m pk tr}, VP m pk tr → K.pre m pk ∧ bytesAt m tr 64 = pkTr (bytesAt m pk p.pkLen))
    {n : String} {f : Prog isa} (hf : VerifyFn p K f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 6)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    (hsat : ∃ s, (verifyMessageKContract p K.len VP X86.abi 172).pre s) :
    Verified X86.target (verifyMessageCached n f p) (verifyMessageKContract p K.len VP X86.abi 172) := by
  refine Piece.verified (((verifyMessageCached_piece hK hf tt).pre_mono (fun _ h => cPre_of hV h)
    fun _ _ _ _ h => cpub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) hsat
  obtain ⟨habi, -, -, s, hB, -, hax⟩ := hq
  refine ⟨habi, ?_⟩
  sig_post [verifyMessageKContract, verifyMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  rw [Proof.MlKem.X86.setWidth_append32, hax]
  rcases hB with ⟨h8, h2⟩ | ⟨h8, hout⟩
  · rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; exact h8)]; exact h2
  · rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [verifyInternal, messageRep, pkTr, Proof.MlKem.bytesAt_length]
    simp only [vMu, hdrBytes, vlay, List.append_assoc] at hout
    simp only [List.append_assoc]
    exact hout

theorem verifyMessageCached_sat (hp : p ∈ params) :
    ∃ s, (verifyMessageKContract p p.pkLen (plainTr p) X86.abi 172).pre s := by
  refine ⟨cachedSat p, ?_⟩
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    sig_apply_check
    · decide +kernel
    · sig_reduce [verifyMessageKContract, verifyMessageKSig, X86.abi, X86.argSlots, X86.argVal,
        X86.argBytes]
      sig_and_intros
      all_goals first
        | (rw [cachedSat_arg 7 (by decide), cachedSat_arg 0 (by decide)]; exact satMemC_digest (by decide))
        | decide

end

end VG.Proof.MlDsa.X86.Message
