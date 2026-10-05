import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
import VerifiedGarbage.Proof.Bignum.X86_64.PcVerified
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Verify
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCtx`. -/
section

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the contract on the registers

`verContract` states the shared contract (with the stack the frame and the
call use, `verStack`) on the registers and the stack (`verify_implies`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer `vg_rsa_pkcs1_verify` uses: its
frame, and the return address of its call (whose callee uses none). -/
def verStack : Nat := 2144

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) =
      [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4] := rfl

/-- `vg_rsa_pkcs1_verify(n = rdi, n_len = rsi, e = rdx, e_len = rcx,
hash = r8d, digest = r9, digest_len = [rsp + 8], sig = [rsp + 16],
sig_len = [rsp + 24], scratch = [rsp + 32], scratch_len = [rsp + 40])`,
using `verStack` bytes of stack. -/
def verContract : Contract isa where
  pre s :=
    let n : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let e : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let dig : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
    let sig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩
    VG.Proof.RsaPkcs1Sig.X86_64.verStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
      s.rd = [n, e, dig, sig, args] ∧ s.wr = [scr] ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dig.Disjoint scr ∧ sig.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dig ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dig ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .rcx).toNat ∧ (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (stackArg s 4).toNat
  post s s' :=
    (s'.gpr .rax).setWidth 32 = if Spec.RsaPkcs1Sig.verifyId (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((s.gpr .r8).setWidth 32).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32 ∧
      (List.range 5).map (stackArg s₁) = (List.range 5).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r9) (stackArg s₁ 0).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r9) (stackArg s₂ 0).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 1) (stackArg s₁ 2).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 1) (stackArg s₂ 2).toNat

/-- A state meeting `verContract.pre`: a 512-bit modulus, a one-byte `e`, a
one-byte hash value and signature, and the stack arguments at `0x10008`. -/
def verSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 1 | .r9 => 0x3000
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10008 then 1 else if a = 0x10011 then 0x40 else if a = 0x10018 then 1
    else if a = 0x10022 then 0x02 else if a = 0x10029 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x20000, 8192⟩]

theorem leak_eq4 {a b c d a' b' c' d' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (hc : c.length = c'.length)
    (h : (a ++ b ++ c ++ d).map (·.toNat) = (a' ++ b' ++ c' ++ d').map (·.toNat)) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hi : a ++ b ++ c ++ d = a' ++ b' ++ c' ++ d' :=
    List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb, hc])
  obtain ⟨h₂, rfl⟩ := List.append_inj h₁ (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₂ ha
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem verify_implies : verContract.Implies (Spec.RsaPkcs1Sig.verifyContract abi VG.Proof.RsaPkcs1Sig.X86_64.verStack) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.verContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq] at h
    sig_pre [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.verContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.verContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.verContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.verContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4⟩ := h
    obtain ⟨hn, he, hd, hs⟩ := VG.Proof.RsaPkcs1Sig.X86_64.leak_eq4 (by simp [Spec.Rsa.bytesAt, hsi]) (by simp [Spec.Rsa.bytesAt, hcx])
      (by simp [Spec.Rsa.bytesAt, a0]) hl
    refine ⟨?_, h8, by simp only [VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, a0, a1, a2, a3, a4], hn, he, hd, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.verifyContract, Spec.RsaPkcs1Sig.verifySig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.verContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq] [verSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.RsaPkcs1Sig.X86_64.verSatState

end VG.Proof.RsaPkcs1Sig.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyFrame`. -/
section

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, the blocks that
store to its slots and read the function's stack arguments, at
`S + frameBytes + 8 + 8 j` (`stackArgAddr`), and the arguments of the call
of `vg_rsa_public_checked` (`pubArgs_ok`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## Addresses in the frame -/

theorem ea_sp (t : State) (d : Nat) : t.ea (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp, BitVec.ofInt_natCast]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

/-! ## The precondition, by name -/

/-- `verContract.pre`, by name. -/
structure PreV (s : State) : Prop where
  sp1 : VG.Proof.RsaPkcs1Sig.X86_64.verStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩,
    ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  hwr : s.wr = [⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  dns : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  des : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dds : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dgs : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dsa : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKd : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dKg : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  wN : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wE : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wD : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wG : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wS : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rsi).toNat
  k2 : (s.gpr .rsi).toNat ≤ 1024
  L1 : 1 ≤ (s.gpr .rcx).toNat
  L2 : (s.gpr .rcx).toNat ≤ (s.gpr .rsi).toNat
  hsl : 16 * (s.gpr .rsi).toNat ≤ (stackArg s 4).toNat

theorem preV_of {s : State} (h : verContract.pre s) : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s := by
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.verContract] at h
  obtain ⟨sp1, sp2, hrd, hwr, dns, des, dds, dgs, dsa, -, -, -, -, dRs, -, dKn, dKe, dKd, dKg, dKs, dKa,
    wN, wE, wD, wG, wS, ⟨k1, k2⟩, L1, L2, hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dns, des, dds, dgs, dsa, dRs, dKn, dKe, dKd, dKg, dKs, dKa, wN, wE, wD, wG, wS,
    k1, k2, L1, L2, hsl⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack

/-- The stack the function uses and the working space: all the function and
its call may write. -/
def stkR (s : State) : Region := ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩
def scrR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

theorem fb_eq (s : State) : VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s) 8 :=
  Offset.sub_ofNat_eq _ (by decide)

theorem fb_sub8 (s : State) : VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s - 8 = VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s := by
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq]; exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s).toNat + VG.Proof.RsaPkcs1Sig.X86_64.verStack + 48 ≤ 2 ^ 64 ∧
    (VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s).toNat + VG.Proof.RsaPkcs1Sig.X86_64.verStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold VG.Proof.RsaPkcs1Sig.X86_64.verStack at *; omega

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (VG.Proof.Bignum.X86_64.off p d).toNat = p.toNat + d := by
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem fb_toNat {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s).toNat + VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes + 8 + 40 ≤ 2 ^ 64 ∧
    (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s).toNat = (VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s).toNat + 8 := by
  have ⟨h1, h2⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb_toNat hp
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq, VG.Proof.RsaPkcs1Sig.X86_64.Ver.toNat_off (by unfold VG.Proof.RsaPkcs1Sig.X86_64.verStack at *; omega)]
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes VG.Proof.RsaPkcs1Sig.X86_64.verStack at *; omega

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d, n⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := by
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq, off_off]
  exact Offset.sub_base _ (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at h; unfold VG.Proof.RsaPkcs1Sig.X86_64.verStack; omega)

/-- The return address of a call from the frame. -/
theorem below_sub (s : State) : Region.Sub (below (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := by
  rw [show below (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, 8⟩ by simp only [below]; rw [← VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_sub8]; rfl]
  exact Region.sub_prefix (by decide)

/-- A region of the frame at `d`, apart from the return address of a call. -/
theorem ret_disjoint (s : State) {d n : Nat} (h : d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) :
    (below (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d, n⟩ := by
  rw [show below (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, 8⟩ by simp only [below]; rw [← VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_sub8]; rfl, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq, off_off]
  exact Offset.base_disjoint _ (by omega) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at h; omega)

/-- A byte outside the stack the function uses is outside the frame. -/
theorem outside_frame (s : State) {x : Addr} (hx : ¬ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Contains x 1) :
    VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, VG.Proof.Bignum.X86_64.ofs] at hlt ⊢; omega
  have := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (d := 0) (n := VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) (by decide)
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] at this
  exact this x hc

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ :: s.wr
  mem : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem t.mem
  sN : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oN = s.gpr .rdi
  sK : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oK = s.gpr .rsi
  sE : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oE = s.gpr .rdx
  sEl : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oEl = s.gpr .rcx
  sH : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oH = s.gpr .r8
  sD : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oD = s.gpr .r9

theorem Env.scr {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t) (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) : VG.Proof.Bignum.X86_64.Scr t (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_toNat hp; omega)

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hk.symm
  · exact hs.symm

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes + 8 + 8 * j) := by
  rw [VG.Proof.Bignum.X86_64.off, show VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes + 8 + 8 * j = VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

/-- Memory changed only in the frame turns into `Env`'s. -/
theorem frame_of_outside {s : State} {m : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s.mem m) :
    Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem m :=
  fun x hx => h x (.inr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) {m : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s.mem m) {j : Nat}
    (hj : j < 5) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArgAddr_fb]
  exact h.word (.inr (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega)) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)

/-- A stack argument, in memory changed only where the function may write. -/
theorem Env.arg {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t) (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) {j : Nat} (hj : j < 5) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 40⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dsa.symm

/-- A word past a store to another word of the frame. -/
theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : VG.Proof.Bignum.X86_64.word (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) base d' = VG.Proof.Bignum.X86_64.word m base d' :=
  (VG.Proof.Bignum.X86_64.writeW_outside m base v (by omega)).word (by omega) (by omega)

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s).gpr r = if r = .rsp then VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s else s.gpr r := rfl

/-- The stack arguments are readable. -/
theorem arg_in {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 5) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 40⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
    by rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem arg_ea {s t : State} (h : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (j : Nat) :
    t.ea (VG.Impl.RsaPkcs1Sig.X86_64.Verify.arg j) = stackArgAddr s j := by
  rw [VG.Impl.RsaPkcs1Sig.X86_64.Verify.arg, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, h, VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArgAddr_fb]

theorem ofNat_lt32 {d : Nat} (h : d < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 d) = BitVec.ofNat 64 d :=
  sx_ofNat h

end VG.Proof.RsaPkcs1Sig.X86_64.Ver

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCall`. -/
section

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the call of `vg_rsa_public_checked`

The arguments kept in the frame's slots and those of the call
(`pubArgs_ok`), and the call (`pub_call`): it runs from the frame with its
stack arguments at `rsp`, writing `s^e mod n` to `EM₁`, and returns with the
slots kept.

The callee is any code meeting `pubChk`, the contract of
`vg_rsa_public_checked` on the registers: `vg_rsa_public`'s, with BoringSSL's
limits on `e` (`Spec.Rsa.publicOpChecked`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- The postcondition of `vg_rsa_public_checked` on the registers. -/
def pubChkPost (s s' : State) : Prop :=
  Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
    (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat))

/-- `vg_rsa_public_checked` on the registers: `vg_rsa_public`'s contract,
with BoringSSL's limits on `e`. -/
def pubChk : Contract isa where
  pre := pubContract.pre
  pub := pubContract.pub
  post := VG.Proof.RsaPkcs1Sig.X86_64.pubChkPost

/-- An implementation of `vg_rsa_public_checked`, and what its callers need
of it. -/
structure PubImpl where
  name : String
  code : Prog isa
  ok : ∀ s, pubChk.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ pubChk.post s s'
  ct : ConstantTime isa pubChk.pre pubChk.pub code
  nosp : NoSp code
  depth : code.depth = 0
  spSafe : code.all (fun i => !isa.writesSp i) = true

end VG.Proof.RsaPkcs1Sig.X86_64

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## The arguments -/

def slotStores : List Instr :=
  [.store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Verify.oN) .rdi, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Verify.oK) .rsi, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Verify.oE) .rdx, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Verify.oEl) .rcx,
    .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oH) .r8, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oD) .r9]

def callArgs : List Instr :=
  [.mov .rax (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.arg 1)), .mov .r10 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.arg 3)), .mov .r11 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.arg 4)),
    .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 0) .rax, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 8) .rsi, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 16) .r10, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 24) .r11,
    .mov .r8 (.reg .rdx), .mov .r9 (.reg .rcx), .mov .rdx (.reg .rdi), .mov .rcx (.reg .rsi)] ++
  VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea .rdi oEM1

theorem pubArgs_eq : pubArgs = VG.Proof.RsaPkcs1Sig.X86_64.Ver.slotStores ++ VG.Proof.RsaPkcs1Sig.X86_64.Ver.callArgs := rfl

/-- The frame's push and the slots. -/
theorem slotStores_ok {s A : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) (hA : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block VG.Proof.RsaPkcs1Sig.X86_64.Ver.slotStores) A fun t =>
      VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) t ∧ VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s.mem t.mem ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oN = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oK = s.gpr .rsi ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oE = s.gpr .rdx ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oEl = s.gpr .rcx ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oH = s.gpr .r8 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oD = s.gpr .r9 := by
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_toNat hp
  have hsp : A.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s := hA.gpr (by decide)
  have hs : VG.Proof.Bignum.X86_64.Scr A (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes := Scr.of_mem (by rw [hA.2.2]; exact List.mem_cons_self ..) (by omega)
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → A.gpr r = s.gpr r := fun r h h' => by
    rw [hA.gpr (by simpa using h')]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, h]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oN) (s.gpr .rdi)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oK) (s.gpr .rsi)).writeW
        (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oE) (s.gpr .rdx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.oEl) (s.gpr .rcx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oH)
        (s.gpr .r8)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oD) (s.gpr .r9)) (by
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Ver.slotStores, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, hsp, hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Verify.oN) (by decide), hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Verify.oK) (by decide),
      hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Verify.oE) (by decide), hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Verify.oEl) (by decide), hs.st (d := oH) (by decide),
      hs.st (d := oD) (by decide), hAm, g .rdi (by decide) (by decide), g .rsi (by decide) (by decide),
      g .rdx (by decide) (by decide), g .rcx (by decide) (by decide), g .r8 (by decide) (by decide),
      g .r9 (by decide) (by decide)]) rfl) fun t ⟨hm, k⟩ => ⟨(hA.trans k).mono (by simp), ?_, ?_⟩
  · rw [hm]
    intro x hx
    have hx' : VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) x := by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hx ⊢; omega
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hx hx'
    simp only [VG.Impl.RsaPkcs1Sig.X86_64.Verify.oN, VG.Impl.RsaPkcs1Sig.X86_64.Verify.oK, VG.Impl.RsaPkcs1Sig.X86_64.Verify.oE, VG.Impl.RsaPkcs1Sig.X86_64.Verify.oEl, oH, oD] at *
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega)]
  · rw [hm]
    simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo, VG.Proof.Bignum.X86_64.word_writeW_self, VG.Impl.RsaPkcs1Sig.X86_64.Verify.oN, VG.Impl.RsaPkcs1Sig.X86_64.Verify.oK, VG.Impl.RsaPkcs1Sig.X86_64.Verify.oE, VG.Impl.RsaPkcs1Sig.X86_64.Verify.oEl, oH, oD, and_self]

/-- The arguments of `vg_rsa_public_checked`. -/
theorem callArgs_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) (hk : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) t)
    (ho : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s.mem t.mem) :
    WP isa (.block VG.Proof.RsaPkcs1Sig.X86_64.Ver.callArgs) t fun t' => VG.Proof.MlKem.X86_64.Keep [.rax, .rdi, .rdx, .rcx, .r8, .r9, .r10, .r11] t t' ∧
      t'.mem = (((t.mem.writeW (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (stackArg s 1)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8) (s.gpr .rsi)).writeW
        (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16) (stackArg s 3)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24) (stackArg s 4) ∧
      t'.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rdi ∧
      t'.gpr .rcx = s.gpr .rsi ∧ t'.gpr .r8 = s.gpr .rdx ∧ t'.gpr .r9 = s.gpr .rcx := by
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_toNat hp
  have hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s := hk.gpr (by decide)
  have hs : VG.Proof.Bignum.X86_64.Scr t (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes :=
    Scr.of_mem (by rw [hk.2.2]; exact List.mem_cons_self ..) (by omega)
  have hrd : t.rd = s.rd := hk.2.1
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → t.gpr r = s.gpr r := fun r h h' => by
    rw [hk.gpr (by simpa using h')]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, h]
  have h0 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 := by
    simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.keep [.rax, .rdi, .rdx, .rcx, .r8, .r9, .r10, .r11] (by
    have h8 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s + 8) 8 := hs.st (d := 8) (by decide)
    have h16 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s + 16) 8 := hs.st (d := 16) (by decide)
    have h24 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s + 24) 8 := hs.st (d := 24) (by decide)
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Ver.callArgs, VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, @VG.Proof.RsaPkcs1Sig.X86_64.Ver.arg_ea s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, hsp, h0, h8, h16, h24,
      VG.Proof.RsaPkcs1Sig.X86_64.Ver.arg_in hp hrd (show 1 < 5 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Ver.arg_in hp hrd (show 3 < 5 by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Ver.arg_in hp hrd (show 4 < 5 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Ver.arg_outside hp ho (show 1 < 5 by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Ver.arg_outside hp ho (show 3 < 5 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Ver.arg_outside hp ho (show 4 < 5 by decide),
      hs.st (d := 8) (by decide), hs.st (d := 16) (by decide), hs.st (d := 24) (by decide),
      sx_ofNat (show oEM1 < 2 ^ 31 by decide),
      g .rsi (by decide) (by decide), g .rdx (by decide) (by decide), g .rcx (by decide) (by decide),
      g .rdi (by decide) (by decide)]) rfl |> fun h => WP.mono h fun t' ⟨q, k⟩ => ⟨k, q⟩

/-! ## The call -/

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (8 * i) := by
  have hsep := Offset.sep (VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega) (by omega) (by omega)
  rw [show VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s + BitVec.ofNat 64 0 = VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (8 * i)) 64
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq, off_off, show 8 + 8 * i = 8 * (i + 1) by omega]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_sub8]
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq]

/-- `EM₁` in the frame. -/
def em1R (s : State) : Region := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1, (s.gpr .rsi).toNat⟩

/-- What the call reads: `n`, `e`, `sig` and its stack arguments. -/
def pubRd (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨stackArg s 1, (s.gpr .rsi).toNat⟩,
    ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, 32⟩]

/-- What it writes: `EM₁` and the working space. -/
def pubWr (s : State) : List Region := [VG.Proof.RsaPkcs1Sig.X86_64.Ver.em1R s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s]

theorem pub_pre {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) (hsig : stackArg s 2 = s.gpr .rsi) (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s)
    (hw0 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 = stackArg s 1) (hw1 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = s.gpr .rsi)
    (hw2 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16 = stackArg s 3) (hw3 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24 = stackArg s 4)
    (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdi)
    (hcx : t.gpr .rcx = s.gpr .rsi) (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    pubChk.pre (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr s)) := by
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr s)) i = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (8 * i) :=
    fun i hi => VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArg_entry hsp _ _ (by omega)
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.pubChk, pubContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide),
    Nat.reduceMul, hw0, hw1, hw2, hw3, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_sub8]
  have ⟨hK1, hK2⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb_toNat hp
  have e1 : VG.Proof.RsaPkcs1Sig.X86_64.verStack = 2144 := rfl
  have e2 : oEM1 = 80 := rfl
  have e3 : VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes = 2136 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have sM : Region.Sub (VG.Proof.RsaPkcs1Sig.X86_64.Ver.em1R s) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega)
  have sA : Region.Sub ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, 32⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := by
    have := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (d := 0) (n := 32) (by decide); simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, 8⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := Region.sub_prefix (by decide)
  have hfb : VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s = VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s + BitVec.ofNat 64 8 := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq s
  have dMA : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.em1R s).Disjoint ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, 32⟩ := Offset.disjoint_base _ (by decide) (by omega)
  have dRM : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, 8⟩ : Region).Disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Ver.em1R s) := by
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.em1R]; rw [hfb, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, 8⟩ : Region).Disjoint ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := by
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.toNat_off (by rw [hfb, ← VG.Proof.Bignum.X86_64.off, VG.Proof.RsaPkcs1Sig.X86_64.Ver.toNat_off (by omega)]; unfold oEM1; omega), hfb, ← VG.Proof.Bignum.X86_64.off,
      VG.Proof.RsaPkcs1Sig.X86_64.Ver.toNat_off (by omega)]; unfold oEM1; omega
  have dKg : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Disjoint ⟨stackArg s 1, (s.gpr .rsi).toNat⟩ := by rw [← hsig]; exact hp.dKg
  have dgs : (⟨stackArg s 1, (s.gpr .rsi).toNat⟩ : Region).Disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s) := by rw [← hsig]; exact hp.dgs
  have wG : (stackArg s 1).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := by rw [← hsig]; exact hp.wG
  refine ⟨by omega, rfl, rfl, hp.dKn.sub_left sM, hp.dKe.sub_left sM, dKg.sub_left sM, hp.dKs.sub_left sM, dMA,
    hp.dns, hp.des, dgs, (hp.dKs.sub_left sA).symm, dRM, hp.dKn.sub_left sR, hp.dKe.sub_left sR,
    dKg.sub_left sR, hp.dKs.sub_left sR, dRA, wM, hp.wN, hp.wE, wG, hp.wS, ⟨hk1, hk2⟩, trivial, trivial, hp.L1,
    hp.L2, hp.hsl⟩

/-! ## Memory across the call -/

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) : Frame [below (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- Memory changed by a call from the frame, within regions in the stack
the function uses or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) ∨ Region.Sub r (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s)) :
    Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {s : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d, 8⟩ : Region).Disjoint r) : VG.Proof.Bignum.X86_64.word m' (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d = VG.Proof.Bignum.X86_64.word m (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The slots are apart from `EM₁`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ oEM1) :
    ∀ r ∈ VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr s ++ [below (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8], (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d, 8⟩ : Region).Disjoint r := by
  have hk2 := hp.k2
  intro r hr
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr, VG.Proof.RsaPkcs1Sig.X86_64.Ver.em1R, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by unfold oEM1 at *; omega) (by unfold oEM1 at *; omega)
  · exact (hp.dKs.sub_left (VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)))
  · exact (VG.Proof.RsaPkcs1Sig.X86_64.Ver.ret_disjoint s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)).symm

theorem pub_covers {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) (hsig : stackArg s 2 = s.gpr .rsi) (he : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t) :
    Covers (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubRd s ++ VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr s) (t.rd ++ t.wr) ∧ Covers (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr s) t.wr := by
  have hk2 := hp.k2
  have hfr : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR]
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr, VG.Proof.RsaPkcs1Sig.X86_64.Ver.em1R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oEM1, rfl, by dsimp only; unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega⟩
    · exact ⟨_, hscr, 0, z _, by simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR]; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 1, (stackArg s 2).toNat⟩ (by rw [hp.hrd]; simp), 0, z _,
      by dsimp only; rw [hsig]; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega⟩

/-- The call of `vg_rsa_public_checked`: `EM₁` holds `s^e mod n`, which it
returns, or zeros. -/
theorem pub_call (v : VG.Proof.RsaPkcs1Sig.X86_64.PubImpl) {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Ver.PreV s) (hsig : stackArg s 2 = s.gpr .rsi) (he : VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t)
    (hw0 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 = stackArg s 1) (hw1 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = s.gpr .rsi)
    (hw2 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16 = stackArg s 3) (hw3 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24 = stackArg s 4)
    (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdi)
    (hcx : t.gpr .rcx = s.gpr .rsi) (h8 : t.gpr .r8 = s.gpr .rdx) (h9 : t.gpr .r9 = s.gpr .rcx) :
    WP isa (.call v.name v.code) t fun t' => VG.Proof.RsaPkcs1Sig.X86_64.Ver.Env s t' ∧
      Spec.Rsa.written t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rsi).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rsi).toNat)) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Ver.pub_covers hp hsig he
  refine WP.call_mx (k := VG.Proof.RsaPkcs1Sig.X86_64.pubChk) v.ok v.nosp (by rw [v.depth]; decide)
    (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pub_pre hp hsig he.rsp hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, he.rsp] at hf
  have hE : stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr s)) 0 = stackArg s 1 :=
    (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArg_entry he.rsp _ _ (by omega)).trans hw0
  have hfE : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem t.callEntry.mem :=
    VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_call he.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (VG.Proof.RsaPkcs1Sig.X86_64.Ver.below_sub s)
  have hk2 := hp.k2
  have b : ∀ {p : Addr} {len : Nat}, (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Disjoint ⟨p, len⟩ → (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk hs hl =>
    VG.Proof.RsaPkcs1Sig.X86_64.Ver.bytes_of_frame hfE hk hs hl
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.pubChk, VG.Proof.RsaPkcs1Sig.X86_64.pubChkPost, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, h9, hE, hm₂, hg₂ .rax (by decide)] at hpost
  rw [b hp.dKn hp.dns.symm (by have := hp.wN; omega), b hp.dKe hp.des.symm (by have := hp.wE; omega),
    b (by rw [← hsig]; exact hp.dKg) (by rw [← hsig]; exact hp.dgs.symm) (by omega)] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, hcs, hmx⟩
  · simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega))
    · exact .inr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.sub_refl _)
    · exact .inl (VG.Proof.RsaPkcs1Sig.X86_64.Ver.below_sub s)
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_apart hp (by decide) (by decide))]; exact he.sN
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_apart hp (by decide) (by decide))]; exact he.sK
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_apart hp (by decide) (by decide))]; exact he.sE
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_apart hp (by decide) (by decide))]; exact he.sEl
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_apart hp (by decide) (by decide))]; exact he.sH
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Ver.slot_apart hp (by decide) (by decide))]; exact he.sD

end VG.Proof.RsaPkcs1Sig.X86_64.Ver

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub`. -/
section

/-!
# `vg_rsa_public_checked` for its callers on x86-64

The implementation of `vg_rsa_public_checked` that `vg_rsa_pkcs1_verify` and
`vg_rsa_pkcs1_recover` call (`PubImpl`), with what they need of it.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64

/-- `vg_rsa_public_checked`. -/
def pubChecked : VG.Proof.RsaPkcs1Sig.X86_64.PubImpl where
  name := Spec.Rsa.publicCheckedApi.name
  code := Impl.Rsa.X86_64.Checked.publicChecked
  ok := Proof.Rsa.X86_64.publicChecked_correct
  ct := Proof.Rsa.X86_64.publicChecked_constantTime
  nosp := Proof.Rsa.X86_64.noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)

end VG.Proof.RsaPkcs1Sig.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCtx`. -/
section

/-!
# `vg_rsa_pkcs1_recover` on x86-64: the contract on the registers

`recContract` states the shared contract (with the stack the frame and the
call use, `verStack`, as for `vg_rsa_pkcs1_verify`) on the registers and the
stack (`recover_implies`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- `vg_rsa_pkcs1_recover(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, hash = [rsp + 8] (32 bits), sig = [rsp + 16],
sig_len = [rsp + 24], scratch = [rsp + 32], scratch_len = [rsp + 40])`,
using `verStack` bytes of stack. -/
def recContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let sig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let scr : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 40⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.verStack⟩
    VG.Proof.RsaPkcs1Sig.X86_64.verStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64 ∧
      s.rd = [n, e, sig, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint sig ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ sig.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint sig ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint sig ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      (∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h ∧
        (s.gpr .rsi).toNat = h.len) ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 4).toNat
  post s s' := ∀ h, Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h →
    Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Sig.recover (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) h
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (stackArg s₁ 0).setWidth 32 = (stackArg s₂ 0).setWidth 32 ∧
      [stackArg s₁ 1, stackArg s₁ 2, stackArg s₁ 3, stackArg s₁ 4] =
        [stackArg s₂ 1, stackArg s₂ 2, stackArg s₂ 3, stackArg s₂ 4] ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (stackArg s₁ 1) (stackArg s₁ 2).toNat =
        Spec.Rsa.bytesAt s₂.mem (stackArg s₂ 1) (stackArg s₂ 2).toNat

/-- A state meeting `recContract.pre`: a 512-bit modulus, a one-byte `e`,
MD5 (16-byte values), a one-byte signature, and the stack arguments at
`0x10008`. -/
def recSatState : State where
  gpr r := match r with
    | .rdi => 0x5000 | .rsi => 16 | .rdx => 0x1000 | .rcx => 64 | .r8 => 0x2000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10011 then 0x40 else if a = 0x10018 then 1
    else if a = 0x10022 then 0x02 else if a = 0x10029 then 0x04 else 0
  rd := [⟨0x1000, 64⟩, ⟨0x2000, 1⟩, ⟨0x4000, 1⟩, ⟨0x10008, 40⟩]
  wr := [⟨0x5000, 16⟩, ⟨0x20000, 8192⟩]

theorem leak_eq3 {a b c a' b' c' : List Byte} (ha : a.length = a'.length) (hb : b.length = b'.length)
    (h : (a ++ b ++ c).map (·.toNat) = (a' ++ b' ++ c').map (·.toNat)) : a = a' ∧ b = b' ∧ c = c' := by
  have hi : a ++ b ++ c = a' ++ b' ++ c' :=
    List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h
  obtain ⟨h₁, rfl⟩ := List.append_inj hi (by simp [ha, hb])
  obtain ⟨rfl, rfl⟩ := List.append_inj h₁ ha
  exact ⟨rfl, rfl, rfl⟩

theorem recover_implies : recContract.Implies (Spec.RsaPkcs1Sig.recoverContract abi VG.Proof.RsaPkcs1Sig.X86_64.verStack) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.recContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq] at h
    sig_pre [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.recContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.recContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.recContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.recContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4⟩ := h
    obtain ⟨hn, he, hs⟩ := VG.Proof.RsaPkcs1Sig.X86_64.leak_eq3 (by simp [Spec.Rsa.bytesAt, hcx]) (by simp [Spec.Rsa.bytesAt, h9]) hl
    refine ⟨?_, a0, by rw [a1, a2, a3, a4], hn, he, hs⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.recoverContract, Spec.RsaPkcs1Sig.recoverSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.recContract, VG.Proof.RsaPkcs1Sig.X86_64.verStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_five, List.append_eq] [recSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.RsaPkcs1Sig.X86_64.recSatState

end VG.Proof.RsaPkcs1Sig.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCtx`. -/
section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the contract on the registers

`sigContract` states the shared contract (with the stack the frame and the
call of `vg_rsa_private_checked` use, `sigStack`) on the registers and the
stack (`sign_implies`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64

open VG VG.X86_64 VG.Proof.Bignum.X86_64

/-- The stack below the stack pointer `vg_rsa_pkcs1_sign` uses: its frame of
1192 bytes, the return address of its call, and the 3248 bytes its callee
`vg_rsa_private_checked` uses. -/
def sigStack : Nat := 4448

theorem stackArgs_fifteen (s : State) :
    List.map (stackArg s) (List.range 15) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13, stackArg s 14] := rfl

/-- `vg_rsa_pkcs1_sign(out = rdi, out_len = rsi, n = rdx, n_len = rcx,
e = r8, e_len = r9, hash = [rsp + 8] (32 bits), digest = [rsp + 16],
digest_len = [rsp + 24], p = [rsp + 32], p_len = [rsp + 40], q = [rsp + 48],
q_len = [rsp + 56], dp = [rsp + 64], dp_len = [rsp + 72], dq = [rsp + 80],
dq_len = [rsp + 88], qinv = [rsp + 96], qinv_len = [rsp + 104],
scratch = [rsp + 112], scratch_len = [rsp + 120])`, using `sigStack` bytes of
stack. -/
def sigContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let n : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let dig : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
    let p : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
    let q : Region := ⟨stackArg s 5, (stackArg s 6).toNat⟩
    let dp : Region := ⟨stackArg s 7, (stackArg s 8).toNat⟩
    let dq : Region := ⟨stackArg s 9, (stackArg s 10).toNat⟩
    let qi : Region := ⟨stackArg s 11, (stackArg s 12).toNat⟩
    let scr : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 120⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stk : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 VG.Proof.RsaPkcs1Sig.X86_64.sigStack, VG.Proof.RsaPkcs1Sig.X86_64.sigStack⟩
    VG.Proof.RsaPkcs1Sig.X86_64.sigStack ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 128 ≤ 2 ^ 64 ∧
      s.rd = [n, e, dig, p, q, dp, dq, qi, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint dig ∧ out.Disjoint p ∧ out.Disjoint q ∧
      out.Disjoint dp ∧ out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ dig.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint n ∧ ret.Disjoint e ∧ ret.Disjoint dig ∧ ret.Disjoint p ∧
      ret.Disjoint q ∧ ret.Disjoint dp ∧ ret.Disjoint dq ∧ ret.Disjoint qi ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint dig ∧ stk.Disjoint p ∧
      stk.Disjoint q ∧ stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64 ∧
      (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64 ∧ (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64 ∧
      (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64 ∧ (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64 ∧
      (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rcx).toNat ∧ (s.gpr .rsi).toNat = (s.gpr .rcx).toNat ∧
      1 ≤ (s.gpr .r9).toNat ∧ (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat ∧
      1 ≤ (stackArg s 4).toNat ∧ (stackArg s 4).toNat < (s.gpr .rcx).toNat ∧ 1 ≤ (stackArg s 6).toNat ∧
      (stackArg s 6).toNat < (s.gpr .rcx).toNat ∧ (stackArg s 8).toNat = (stackArg s 4).toNat ∧
      (stackArg s 12).toNat = (stackArg s 4).toNat ∧ (stackArg s 10).toNat = (stackArg s 6).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .rcx).toNat ≤ (stackArg s 14).toNat
  post s s' :=
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((s'.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Sig.signId (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)
        ((stackArg s 0).setWidth 32).toNat
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      (stackArg s₁ 0).setWidth 32 = (stackArg s₂ 0).setWidth 32 ∧
      (List.range 14).map (fun i => stackArg s₁ (i + 1)) = (List.range 14).map (fun i => stackArg s₂ (i + 1)) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-- A state meeting `sigContract.pre`: a 512-bit modulus, a one-byte `e`, a
one-byte hash value, one-byte primes, exponents and `qInv`, and the stack
arguments at `0x10008`. -/
def sigSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x10011 then 0x40 else if a = 0x10018 then 1 else if a = 0x10021 then 0x41
    else if a = 0x10028 then 1 else if a = 0x10031 then 0x42 else if a = 0x10038 then 1
    else if a = 0x10041 then 0x43 else if a = 0x10048 then 1 else if a = 0x10051 then 0x44
    else if a = 0x10058 then 1 else if a = 0x10061 then 0x45 else if a = 0x10068 then 1
    else if a = 0x10072 then 0x02 else if a = 0x10079 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 1⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10008, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8192⟩]

theorem sign_implies : sigContract.Implies (Spec.RsaPkcs1Sig.signContract abi VG.Proof.RsaPkcs1Sig.X86_64.sigStack) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.sigContract, VG.Proof.RsaPkcs1Sig.X86_64.sigStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_fifteen, List.append_eq] at h
    sig_pre [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.sigContract, VG.Proof.RsaPkcs1Sig.X86_64.sigStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_fifteen, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.sigContract, VG.Proof.RsaPkcs1Sig.X86_64.sigStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_fifteen, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.sigContract, VG.Proof.RsaPkcs1Sig.X86_64.sigStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_fifteen, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.sigContract, VG.Proof.RsaPkcs1Sig.X86_64.sigStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_fifteen, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
      a14⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, a0, ?_, hn, he⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
    · simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.map_append,
        a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]
  sat := by sig_implies_sat [Spec.RsaPkcs1Sig.signContract, Spec.RsaPkcs1Sig.signSig, abi, argRegs, VG.Proof.RsaPkcs1Sig.X86_64.sigContract, VG.Proof.RsaPkcs1Sig.X86_64.sigStack, VG.Proof.RsaPkcs1Sig.X86_64.stackArgs_fifteen, List.append_eq] [sigSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using VG.Proof.RsaPkcs1Sig.X86_64.sigSatState

end VG.Proof.RsaPkcs1Sig.X86_64

end
