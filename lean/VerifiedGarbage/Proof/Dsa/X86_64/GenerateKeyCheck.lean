module

public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Backend
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyABI
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallGeometry
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallMemory
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.ParametersVerified
public import VerifiedGarbage.Proof.Dsa.Contract

/-! # Key generation's call of the domain check -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def keygenCheckName (v : Backend) : String := "vg_dsa_check_parameters" ++ v.suffix
def keygenDeriveName (v : Backend) : String := Spec.Dsa.deriveKeyApi.name ++ v.suffix

theorem keygenStackBase_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (randomStackBase extra s).toNat = (s.gpr .rsp).toNat - (extra + 256) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  simp only [randomStackBase, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_arith

theorem keygenStack_offset_toNat {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    {d : Nat} (hd : d ≤ extra + 256) :
    (off (randomStackBase extra s) d).toNat = (randomStackBase extra s).toNat + d := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := keygenStackBase_toNat h
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-- The frame's return slot and the callee's frame lie in the wrapper's stack allowance. -/
theorem keygen_ret_sub {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Region.Sub ⟨randomBase s - 8, 8⟩ (below (s.gpr .rsp) (extra + 256)) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := keygenStackBase_toNat h
  rw [random_callBase extra s]
  exact Offset.sub_base _ (by omega_arith)

theorem keygen_callee_sub {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    Region.Sub (below (randomBase s - 8) extra) (below (s.gpr .rsp) (extra + 256)) := by
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := keygenStackBase_toNat h
  change Region.Sub ⟨randomBase s - 8 - BitVec.ofNat 64 extra, extra⟩ _
  rw [random_calleeBase extra s]
  exact Region.sub_prefix (by omega_arith)

theorem keygen_checkArgs_ok {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.gpr .rsp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.checkArgs) t fun u =>
      u.gpr .rdi = s.gpr .rcx ∧ u.gpr .rsi = s.gpr .r8 ∧ u.gpr .rdx = s.gpr .r9 ∧
      u.gpr .rcx = stackArg s 0 ∧ u.gpr .r8 = stackArg s 3 ∧ u.gpr .r9 = stackArg s 4 ∧
      u.mem = t.mem ∧ Keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] t u := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u =>
      u.gpr .rdi = s.gpr .rcx ∧ u.gpr .rsi = s.gpr .r8 ∧ u.gpr .rdx = s.gpr .r9 ∧
      u.gpr .rcx = stackArg s 0 ∧ u.gpr .r8 = stackArg s 3 ∧ u.gpr .r9 = stackArg s 4 ∧
      u.mem = t.mem) ?_ rfl)
    fun u ⟨⟨h1, h2, h3, h4, h5, h6, hm⟩, hk⟩ => ⟨h1, h2, h3, h4, h5, h6, hm, hk⟩
  unfold GenerateKey.checkArgs
  xrun [random_ea_sp, hsp, hs.ld (d := Random.oKey) (by decide), hs.ld (d := Random.oKeyLen) (by decide),
    hs.ld (d := Random.oPLen) (by decide), hs.ld (d := Random.oQLen) (by decide),
    hs.ld (d := Random.oScratch) (by decide), hs.ld (d := Random.oScratchLen) (by decide),
    hv (64, s.gpr .rcx) (by simp [keygenSavedValues]), hv (72, s.gpr .r8) (by simp [keygenSavedValues]),
    hv (80, s.gpr .r9) (by simp [keygenSavedValues]), hv (88, stackArg s 0) (by simp [keygenSavedValues]),
    hv (128, stackArg s 3) (by simp [keygenSavedValues]), hv (136, stackArg s 4) (by simp [keygenSavedValues])]
  exact ⟨hv (64, s.gpr .rcx) (by simp [keygenSavedValues]), hv (72, s.gpr .r8) (by simp [keygenSavedValues]),
    hv (80, s.gpr .r9) (by simp [keygenSavedValues]), hv (88, stackArg s 0) (by simp [keygenSavedValues]),
    hv (128, stackArg s 3) (by simp [keygenSavedValues]), hv (136, stackArg s 4) (by simp [keygenSavedValues])⟩

def keygenCheckRd (s : State) : List Region := [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩]
def keygenCheckWr (s : State) : List Region := [⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]

theorem keygen_check_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenCheckRd s ++ keygenCheckWr s) (t.rd ++ t.wr) ∧ Covers (keygenCheckWr s) t.wr := by
  have hs : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
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
    (hsp : t.gpr .rsp = randomBase s)
    (hdi : t.gpr .rdi = s.gpr .rcx) (hsi : t.gpr .rsi = s.gpr .r8) (hdx : t.gpr .rdx = s.gpr .r9)
    (hcx : t.gpr .rcx = stackArg s 0) (h8 : t.gpr .r8 = stackArg s 3) (h9 : t.gpr .r9 = stackArg s 4) :
    (Proof.Dsa.checkParametersContract abi extra).pre
      (t.callEntry.withRegions (keygenCheckRd s) (keygenCheckWr s)) := by
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  sig_pre [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  simp only [hdi, hsi, hdx, hcx, h8, h9, hsp, keygenCheckRd, keygenCheckWr]
  have hl := h.stackLower
  have hb := (s.gpr .rsp).isLt
  have hk := keygenStackBase_toNat h
  have hR : (randomBase s - 8).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_callBase extra s, keygenStack_offset_toNat h (by omega_arith)]
  have sR := keygen_ret_sub h
  have sK := keygen_callee_sub h
  refine ⟨?_, trivial, trivial, h.paramsScratch, h.stackParams.sub_left sR, ?_, h.paramsBound, h.scratchBound,
    h.lengths, h.paramsLength, ?_⟩
  · cases extra <;> simp only <;> omega_arith
  · cases extra with
    | zero => exact h.stackScratch.sub_left sR
    | succ n => exact ⟨h.stackScratch.sub_left sR, h.stackParams.sub_left sK, h.stackScratch.sub_left sK⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.generationScratchWords at hh
    unfold Spec.Dsa.scratchWords
    omega_arith

/-- The bytes of a buffer apart from the wrapper's stack allowance, as the callee reads them. -/
theorem keygen_callEntry_bytes {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.gpr .rsp = randomBase s) {p : Addr} {n : Nat}
    (hd : (below (s.gpr .rsp) (extra + 256)).Disjoint ⟨p, n⟩) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt t.callEntry.mem p n = Spec.Rsa.bytesAt t.mem p n :=
  random_callEntry_bytes hsp ((hd.sub_left (keygen_ret_sub h)).symm.sep (Region.contains_self _ _)
    (Region.contains_self _ _)) hn

theorem keygen_check_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.gpr .rsp = randomBase s)
    (hdi : t.gpr .rdi = s.gpr .rcx) (hsi : t.gpr .rsi = s.gpr .r8) (hdx : t.gpr .rdx = s.gpr .r9)
    (hcx : t.gpr .rcx = stackArg s 0) (h8 : t.gpr .r8 = stackArg s 3) (h9 : t.gpr .r9 = stackArg s 4)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    WP isa (.call (keygenCheckName v) (Generate.checkParameters v.sq v.mul)) t fun u =>
      u.rd = t.rd ∧ u.wr = t.wr ∧ (∀ r ∈ calleeSaved, u.gpr r = t.gpr r) ∧
      Frame (keygenCheckWr s ++ [below (randomBase s) (v.stack + 8)]) t.mem u.mem ∧
      ((u.gpr .rax).setWidth 32).toNat =
        (if Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen
          (Spec.Rsa.bytesAt t.mem (s.gpr .rcx) (s.gpr .r8).toNat) then 1 else 0) ∧
      u.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hcw⟩ := keygen_check_covers h hrd hwr
  have hd := v.parametersDepth
  have hb := v.stackBound
  refine WP.call_sp_mx v.parametersVerified.1 (SpSafe.of_all v.parametersSp) (by omega_arith)
    (keygen_check_pre h hsp hdi hsi hdx hcx h8 h9) hc hcw
    (fun u hur huw huc hf _ ⟨w, hwm, hwg, hp⟩ hmx => ?_)
  sig_post [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero] at hp
  simp only [hdi, hsi, hdx, hcx, hwg .rax (by decide)] at hp
  refine ⟨hur, huw, huc, ?_, ?_, hmx⟩
  · rw [hsp] at hf
    exact VG.X86_64.Frame.below_mono hf (by omega_arith) (by omega_arith)
  · rw [hp, ← keygen_callEntry_bytes h hsp h.stackParams (s.gpr .r8).isLt]
    rfl

end VG.Proof.Dsa.X86_64
