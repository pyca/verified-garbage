module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyEntry
public import VerifiedGarbage.Proof.Dsa.AArch64.Backend
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyABI
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # Key generation's call of the domain check -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def keygenCheckName (v : Backend) : String := "vg_dsa_check_parameters" ++ v.suffix
def keygenDeriveName (v : Backend) : String := Spec.Dsa.deriveKeyApi.name ++ v.suffix

theorem keygenStackBase_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (randomStackBase extra s).toNat = (s.sp).toNat - (extra + 256) := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  simp only [randomStackBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem keygenStack_offset_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {d : Nat} (hd : d ≤ extra + 256) :
    (off (randomStackBase extra s) d).toNat = (randomStackBase extra s).toNat + d := by
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hk := keygenStackBase_toNat h
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem keygen_callee_sub {extra : Nat} {s : State} (_h : GenerateKeyABI extra s) :
    Region.Sub (below (randomBase s) extra) (below s.sp (extra + 256)) :=
  random_calleeFrame_sub extra s

theorem keygen_checkArgs_ok {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.sp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.checkArgs) t fun u =>
      u.gpr .x0 = s.gpr .x3 ∧ u.gpr .x1 = s.gpr .x4 ∧ u.gpr .x2 = s.gpr .x5 ∧
      u.gpr .x3 = s.gpr .x6 ∧ u.gpr .x4 = stackArg s 1 ∧ u.gpr .x5 = stackArg s 2 ∧
      u.mem = t.mem ∧ Keep [.x0, .x1, .x2, .x3, .x4, .x5] t u := by
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x5] (Q := fun u =>
      u.gpr .x0 = s.gpr .x3 ∧ u.gpr .x1 = s.gpr .x4 ∧ u.gpr .x2 = s.gpr .x5 ∧
      u.gpr .x3 = s.gpr .x6 ∧ u.gpr .x4 = stackArg s 1 ∧ u.gpr .x5 = stackArg s 2 ∧
      u.mem = t.mem) ?_ rfl rfl rfl)
    fun u ⟨⟨h1, h2, h3, h4, h5, h6, hm⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, h6, hm, hk⟩
  unfold GenerateKey.checkArgs
  brun [exec_ldrSp_x', hsp, hs.ld (d := Random.oKey) (by decide), hs.ld (d := Random.oKeyLen) (by decide),
    hs.ld (d := Random.oPLen) (by decide), hs.ld (d := Random.oQLen) (by decide),
    hs.ld (d := Random.oScratch) (by decide), hs.ld (d := Random.oScratchLen) (by decide),
    hv (64, s.gpr .x3) (by simp [keygenSavedValues]), hv (72, s.gpr .x4) (by simp [keygenSavedValues]),
    hv (80, s.gpr .x5) (by simp [keygenSavedValues]), hv (88, s.gpr .x6) (by simp [keygenSavedValues]),
    hv (128, stackArg s 1) (by simp [keygenSavedValues]), hv (136, stackArg s 2) (by simp [keygenSavedValues])]
  exact ⟨hv (64, s.gpr .x3) (by simp [keygenSavedValues]),
    hv (72, s.gpr .x4) (by simp [keygenSavedValues]),
    hv (80, s.gpr .x5) (by simp [keygenSavedValues]),
    hv (88, s.gpr .x6) (by simp [keygenSavedValues]),
    hv (128, stackArg s 1) (by simp [keygenSavedValues]),
    hv (136, stackArg s 2) (by simp [keygenSavedValues])⟩

def keygenCheckRd (s : State) : List Region := [⟨s.gpr .x3, (s.gpr .x4).toNat⟩]
def keygenCheckWr (s : State) : List Region := [⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]

theorem keygen_check_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenCheckRd s ++ keygenCheckWr s) (t.rd ++ t.wr) ∧ Covers (keygenCheckWr s) t.wr := by
  have hs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have zero (p : Addr) : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  have cw : Covers (keygenCheckWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [keygenCheckWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, hs, 0, zero _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [keygenCheckRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩

theorem keygen_check_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.sp = randomBase s)
    (hdi : t.gpr .x0 = s.gpr .x3) (hsi : t.gpr .x1 = s.gpr .x4) (hdx : t.gpr .x2 = s.gpr .x5)
    (hcx : t.gpr .x3 = s.gpr .x6) (h8 : t.gpr .x4 = stackArg s 1) (h9 : t.gpr .x5 = stackArg s 2) :
    (Proof.Dsa.checkParametersContract abi extra).pre
      (t.callEntry.withRegions (keygenCheckRd s) (keygenCheckWr s)) := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  simp only [hdi, hsi, hdx, hcx, h8, h9, hsp, keygenCheckRd, keygenCheckWr]
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hk := keygenStackBase_toNat h
  have hs := h.scratchLength
  have hsmall : Spec.Dsa.scratchWords (s.gpr .x5).toNat ≤ (stackArg s 2).toNat := by
    unfold Spec.Dsa.generationScratchWords at hs
    unfold Spec.Dsa.scratchWords
    omega
  cases extra with
  | zero => exact ⟨trivial, trivial, trivial, h.paramsScratch, trivial, h.paramsBound, h.scratchBound,
      h.lengths, h.paramsLength, hsmall⟩
  | succ n => exact ⟨by
      simp only
      have := keygenBase_toNat h
      unfold Random.frameBytes at this
      omega,
      trivial, trivial, h.paramsScratch, ⟨h.stackParams.sub_left (keygen_callee_sub h),
      h.stackScratch.sub_left (keygen_callee_sub h)⟩, h.paramsBound, h.scratchBound,
      h.lengths, h.paramsLength, hsmall⟩

theorem keygen_check_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.sp = randomBase s)
    (hdi : t.gpr .x0 = s.gpr .x3) (hsi : t.gpr .x1 = s.gpr .x4) (hdx : t.gpr .x2 = s.gpr .x5)
    (hcx : t.gpr .x3 = s.gpr .x6) (h8 : t.gpr .x4 = stackArg s 1) (h9 : t.gpr .x5 = stackArg s 2)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    WP isa (.call (keygenCheckName v) (Generate.checkParameters v.mul)) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      Frame (keygenCheckWr s ++ [below (randomBase s) v.stack]) t.mem u.mem ∧
      ((u.gpr .x0).setWidth 32).toNat =
        (if Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen
          (Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat) then 1 else 0) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) := by
  obtain ⟨hc, hcw⟩ := keygen_check_covers h hrd hwr
  have hd := v.parametersDepth
  have hb := v.stackBound
  refine WP.callFV v.parametersVerified.1 (keygen_check_pre h hsp hdi hsi hdx hcx h8 h9)
    hc hcw (fun u hur huw husp hf huc hv hp => ?_) (by omega)
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at hp
  simp only [hdi, hsi, hdx, hcx] at hp
  refine ⟨hur, huw, husp, huc, ?_, hp, hv⟩
  rw [hsp] at hf
  exact Frame.below_mono hf hd (by omega)

end VG.Proof.Dsa.AArch64
