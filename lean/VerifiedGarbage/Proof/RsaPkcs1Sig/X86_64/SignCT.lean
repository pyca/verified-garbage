import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub
import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Sign
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT
import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Framework.X86_64.CallSp

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignFrame`. -/
section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, below which the
call of `vg_rsa_private_checked` uses 3256 bytes; its slots, and the
function's stack arguments, at `S + frameBytes + 8 + 8 j` (`stackArgAddr`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

theorem ea_sp (t : State) (d : Nat) : t.ea (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp, BitVec.ofInt_natCast]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

/-! ## The precondition, by name -/

/-- `sigContract.pre`, by name. -/
structure PreS (s : State) : Prop where
  sp1 : sigStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 128 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨stackArgAddr s 0, 120⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOd : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dds : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dps : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dqs : (⟨stackArg s 5, (stackArg s 6).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddps : (⟨stackArg s 7, (stackArg s 8).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddqs : (⟨stackArg s 9, (stackArg s 10).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dqis : (⟨stackArg s 11, (stackArg s 12).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dsa : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKd : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wD : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wP : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wQ : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wDp : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wDq : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wQi : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wS : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 4).toNat
  pl2 : (stackArg s 4).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 6).toNat
  ql2 : (stackArg s 6).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 8).toNat = (stackArg s 4).toNat
  hqil : (stackArg s 12).toNat = (stackArg s 4).toNat
  hdql : (stackArg s 10).toNat = (stackArg s 6).toNat
  hsl : 16 * (s.gpr .rcx).toNat ≤ (stackArg s 14).toNat

theorem preS_of {s : State} (h : sigContract.pre s) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s := by
  simp only [sigContract] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOd, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dns, des, dds, dps, dqs, ddps,
    ddqs, dqis, dsa, dRo, -, -, -, -, -, -, -, -, dRs, -, dKo, dKn, dKe, dKd, dKp, dKq, dKdp, dKdq, dKqi, dKs, dKa,
    wO, wN, wE, wD, wP, wQ, wDp, wDq, wQi, wS, ⟨k1, k2⟩, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql,
    hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOd, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dns, des, dds, dps, dqs, ddps,
    ddqs, dqis, dsa, dRo, dRs, dKo, dKn, dKe, dKd, dKp, dKq, dKdp, dKdq, dKqi, dKs, dKa, wO, wN, wE, wD, wP, wQ, wDp,
    wDq, wQi, wS, k1, k2, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl⟩

/-! ## The frame -/

abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 sigStack

def stkR (s : State) : Region := ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s, sigStack⟩
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩

/-- The frame's base, from the stack's: `frameBytes` above it, below which
the call uses `sigStack - frameBytes` bytes. -/
theorem fb_eq (s : State) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) (sigStack - VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes) :=
  Offset.sub_ofNat_eq _ (by decide)

theorem kb_toNat {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s).toNat + sigStack + 128 ≤ 2 ^ 64 ∧
    (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s).toNat + sigStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold sigStack at *; omega

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (VG.Proof.Bignum.X86_64.off p d).toNat = p.toNat + d := by
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem fb_toNat {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s).toNat + VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes + 8 + 120 ≤ 2 ^ 64 ∧
    (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s).toNat = (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s).toNat + (sigStack - VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes) := by
  have ⟨h1, h2⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb_toNat hp
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_eq, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.toNat_off (by unfold sigStack VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega)]
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes sigStack at *; omega

theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes) : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d, n⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s) := by
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_eq, off_off]
  exact Offset.sub_base _ (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at h; unfold sigStack VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega)

theorem outside_frame (s : State) {x : Addr} (hx : ¬ (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s).Contains x 1) :
    VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, VG.Proof.Bignum.X86_64.ofs] at hlt ⊢; omega
  have := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_sub s (d := 0) (n := VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes) (by decide)
  simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] at this
  exact this x hc

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes⟩ :: s.wr
  mem : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s] s.mem t.mem
  sOut : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut = s.gpr .rdi
  sOl : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oOl = s.gpr .rsi
  sN : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oN = s.gpr .rdx
  sK : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK = s.gpr .rcx
  sE : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oE = s.gpr .r8
  sEl : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oEl = s.gpr .r9

theorem Env.scr {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) : VG.Proof.Bignum.X86_64.Scr t (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_toNat hp; omega)

theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s).Disjoint ⟨p, len⟩) (ho : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes + 8 + 8 * j) := by
  rw [VG.Proof.Bignum.X86_64.off, show VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes + 8 + 8 * j = VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem frame_of_outside {s : State} {m : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes s.mem m) :
    Frame [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s] s.mem m :=
  fun x hx => h x (.inr (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outside_frame s (hx _ (List.mem_cons_self ..))))

theorem arg_outside {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) {m : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes s.mem m) {j : Nat}
    (hj : j < 15) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stackArgAddr_fb]
  exact h.word (.inr (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega)) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega)

theorem Env.arg {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) {j : Nat} (hj : j < 15) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 120⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

theorem arg_in {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 15) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 120⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
    by rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem arg_ea {s t : State} (h : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (j : Nat) : t.ea (VG.Impl.RsaPkcs1Sig.X86_64.Sign.arg j) = stackArgAddr s j := by
  rw [VG.Impl.RsaPkcs1Sig.X86_64.Sign.arg, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ea_sp, h, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stackArgAddr_fb]

theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : VG.Proof.Bignum.X86_64.word (m.writeW (VG.Proof.Bignum.X86_64.off base d) v) base d' = VG.Proof.Bignum.X86_64.word m base d' :=
  (VG.Proof.Bignum.X86_64.writeW_outside m base v (by omega)).word (by omega) (by omega)

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes s).gpr r = if r = .rsp then VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s else s.gpr r := rfl

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignBlocks`. -/
section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the blocks around the encoding and the call

The frame's push, the slots and the arguments of `encode` (`head_ok`, and
`encPre`, what `encode` needs), the zeros to `out` if it fails
(`zeroSlots_ok`), the arguments of `vg_rsa_private_checked` (`callArgs_ok`),
and the zeros to `EM` after the call (`wipe_ok`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes

/-! ## Memory in the frame -/

/-- `Env` past changes of the registers but `rsp`, and of memory in the
frame outside its slots or in `out`. -/
theorem Env.of {s t u : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, (∃ d n, r = ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d, n⟩ ∧ (d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut ∨ oEM ≤ d) ∧ d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes) ∨
      r = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s u := by
  have hsl : ∀ {d}, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut ≤ d → d + 8 ≤ oEM → VG.Proof.Bignum.X86_64.word u.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d := fun hd hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      rcases hs r hr with ⟨d', n, rfl, h₁, h₂⟩ | rfl
      · exact Offset.disjoint _ (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut oEM at *; omega) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes oEM at *; omega)
          (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega)
      · exact (hp.dKo.sub_left (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_sub s (by unfold oEM VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega)))) (by decide)
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, he.mem.trans (hf.sub fun r hr => ?_),
    (hsl (by decide) (by decide)).trans he.sOut, (hsl (by decide) (by decide)).trans he.sOl,
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl⟩
  rcases hs r hr with ⟨d, n, rfl, -, h₂⟩ | rfl
  · exact ⟨_, List.mem_cons_self .., VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_sub s h₂⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `Env` past changes of the registers but `rsp`. -/
theorem Env.regs {s t u : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sOut, hm ▸ he.sOl, hm ▸ he.sN,
    hm ▸ he.sK, hm ▸ he.sE, hm ▸ he.sEl⟩

theorem frame_bytes {s : State} {d n : Nat} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (h : d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes) :
    ∀ i < n, InRegions (⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes⟩ :: s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d + BitVec.ofNat 64 i) 1 := by
  have := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_toNat hp
  intro i hi
  refine ⟨_, List.mem_cons_self .., ?_⟩
  rw [show VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d + BitVec.ofNat 64 i = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (d + i) from off_off _ _ _]
  exact Offset.contains_base _ (by omega) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega)

/-! ## The head -/

/-- The frame's push, the slots and the arguments of `encode`. -/
theorem head_ok {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) :
    WP isa (.block (VG.Impl.RsaPkcs1Sig.X86_64.Sign.slotStores ++ encArgs)) (allocState VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes s) fun t => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t ∧
      t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM ∧ t.gpr .rcx = s.gpr .rcx ∧
      t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧
      t.gpr .r9 = stackArg s 2 ∧ (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_toNat hp
  set A := allocState VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes s with hA
  have hsp : A.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s := rfl
  have hs : VG.Proof.Bignum.X86_64.Scr A (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes := Scr.of_mem (List.mem_cons_self ..) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut) (s.gpr .rdi)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oOl) (s.gpr .rsi)).writeW
        (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oN) (s.gpr .rdx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK) (s.gpr .rcx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oE)
        (s.gpr .r8)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oEl) (s.gpr .r9)) (by
    xrun [VG.Impl.RsaPkcs1Sig.X86_64.Sign.slotStores, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ea_sp, hsp, hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut) (by decide), hs.st (d := oOl) (by decide),
      hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oN) (by decide), hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK) (by decide), hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oE) (by decide),
      hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oEl) (by decide)]
    rfl) rfl) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have ho₁ : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes s.mem t₁.mem := by
    rw [hm₁]
    intro x hx
    have hx' : VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) x := by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at hx ⊢; omega
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at hx hx'
    simp only [VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut, oOl, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oN, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oE, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oEl] at *
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega)]
  have hslots : VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oOl = s.gpr .rsi ∧
      VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oN = s.gpr .rdx ∧ VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK = s.gpr .rcx ∧
      VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oE = s.gpr .r8 ∧ VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Sign.oEl = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.word_wo, VG.Proof.Bignum.X86_64.word_writeW_self, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut, oOl, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oN, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oE, VG.Impl.RsaPkcs1Sig.X86_64.Sign.oEl, and_self]
  have hsp₁ : t₁.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s := (k₁.gpr (by decide)).trans hsp
  have hrd : t₁.rd = s.rd := k₁.2.1
  have g : ∀ r, r ≠ .rsp → t₁.gpr r = s.gpr r := fun r h => by
    rw [k₁.gpr (by simp)]; simp [hA, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.allocState_gpr, h]
  refine WP.mono (WP.keep [.r8, .rdx, .rsi, .r9] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM ∧
      t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧
      t.gpr .r9 = stackArg s 2) (by
    xrun [encArgs, VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, @VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_ea s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ea_sp, hsp₁,
      sx_ofNat (show oEM < 2 ^ 31 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_in hp hrd (show 0 < 15 by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_in hp hrd (show 1 < 15 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_in hp hrd (show 2 < 15 by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_outside hp ho₁ (show 0 < 15 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_outside hp ho₁ (show 1 < 15 by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_outside hp ho₁ (show 2 < 15 by decide)]) rfl) fun t ⟨⟨hm, h8, hdx, hsi, h9⟩, k⟩ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hslots
  refine ⟨⟨(k.gpr (by decide)).trans hsp₁, k.2.1.trans hrd, k.2.2.trans k₁.2.2, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_of_outside (hm ▸ ho₁),
    hm ▸ h1, hm ▸ h2, hm ▸ h3, hm ▸ h4, hm ▸ h5, hm ▸ h6⟩, h8, by rw [k.gpr (by decide), g _ (by decide)],
    hdx, hsi, h9, fun r hr hr' => ?_⟩
  rw [k.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all),
    g r hr']

/-- What `encode` needs, from the head. -/
theorem encPre {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) (h8 : t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM)
    (hcx : t.gpr .rcx = s.gpr .rcx) (hdx : t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64)
    (hsi : t.gpr .rsi = stackArg s 1) (h9 : t.gpr .r9 = stackArg s 2) :
    VG.Proof.RsaPkcs1Sig.X86_64.EPre t ((stackArg s 0).setWidth 32) (s.gpr .rcx).toNat := by
  have hk2 := hp.k2
  have hdl := hp.wD
  have sEM : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM, (s.gpr .rcx).toNat⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s) :=
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_sub s (by unfold oEM VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega)
  exact {
    rdx := by rw [hdx]; apply BitVec.eq_of_toNat_eq; simp
    hk := by rw [hcx]
    kle := hk2
    buf := fun i hi => by rw [h8, he.wr]; exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_bytes hp (by unfold oEM VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega) i hi
    rd := fun j hj => by
      rw [hsi, he.rd, he.wr]
      rw [h9] at hj
      exact ⟨⟨stackArg s 1, (stackArg s 2).toNat⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
        Offset.contains_base _ (by omega) (by omega)⟩
    sep := fun j hj i hi => by
      rw [hsi, h8]
      rw [h9] at hj
      exact ne_of_disjoint (hp.dKd.sub_left sEM).symm (by omega) (by omega) hj hi }

/-! ## Zeros to `out` -/

/-- The address and length of `out`, from their slots. -/
theorem zeroHead_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) :
    WP isa (.block [.mov .rdi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut)), .mov .rsi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOl))]) t
      fun u => VG.Proof.MlKem.X86_64.Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧
      u.gpr .rsi = s.gpr .rsi) (by
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ea_sp, he.rsp, hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun u ⟨h, k⟩ => ⟨k, h⟩

theorem zeroSlots_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) :
    WP isa zeroSlots t fun u => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s u ∧ (u.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsiK := hp.hsi
  unfold zeroSlots
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.zeroHead_ok hp he) fun t₁ ⟨k₁, hm₁, hdi, hsi⟩ => ?_)
  have hwr : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s ∈ t₁.wr := by rw [k₁.2.2, he.wr, hp.hwr]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR]
  refine WP.mono (Rec.zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega) (by omega)
    (by rw [hsi, Rec.ofNat_toNat64]) (by
      rw [hdi]; intro i hi; exact ⟨_, hwr, Offset.contains_base _ (by have := hp.wO; omega) (by omega)⟩))
    fun u ⟨hK, hm, hax⟩ => ⟨?_, by rw [hax]; rfl, ?_⟩
  · refine Env.of (he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2) hp (hK.gpr (by decide)) hK.2.1 hK.2.2
      (hm ▸ frame_writeBytes _ _ _) fun r hr => .inr ?_
    rw [List.mem_singleton.mp hr, hdi, List.length_replicate]; rfl
  · rw [hm, hdi, ← hsiK]
    have := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_writeBytes t₁.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega)
    rwa [List.length_replicate] at this

/-! ## The arguments of the call -/

/-- The call's stack argument `i`: `EM`, `n_len`, then the function's stack
arguments from `p` on. -/
def callArg (s : State) : Nat → BitVec 64
  | 0 => VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM
  | 1 => s.gpr .rcx
  | i + 2 => stackArg s (i + 3)

/-- Stack argument `j + 3` to the frame's word `j + 2`. -/
theorem copyArg_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) {j : Nat} (hj : j < 12) :
    WP isa (.block (VG.Impl.RsaPkcs1Sig.X86_64.Sign.copyArg j)) t fun t' => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t' ∧
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * (j + 2))) (stackArg s (j + 3)) ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t' := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rax] (Q := fun t' =>
      t'.mem = t.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * (j + 2))) (stackArg s (j + 3))) (by
    xrun [VG.Impl.RsaPkcs1Sig.X86_64.Sign.copyArg, @VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_ea s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ea_sp, he.rsp, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.arg_in hp he.rd (show j + 3 < 15 by omega),
      he.arg hp (show j + 3 < 15 by omega), hs.st (d := 8 * (j + 2)) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega)]) rfl)
    fun t' ⟨hm, k⟩ => ⟨Env.of he hp (k.gpr (by decide)) k.2.1 k.2.2 (hm ▸ (Frame.refl _ _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
      ⟨8 * (j + 2), 8, List.mem_singleton.mp hr, .inl (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut; omega), by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega⟩, hm, k⟩

/-- The first `n` copies. -/
theorem copies_ok {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) : ∀ (n : Nat), n ≤ 12 → ∀ (t : State), VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t →
    WP isa (.block ((List.range n).flatMap VG.Impl.RsaPkcs1Sig.X86_64.Sign.copyArg)) t fun t' => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t' ∧
      (∀ i < n, VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * (i + 2)) = stackArg s (i + 3)) ∧
      (∀ d, d + 8 ≤ 16 ∨ 16 + 8 * n ≤ d → d + 8 ≤ VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes → VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d) ∧
      Frame [⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 112⟩] t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax] t t'
  | 0, _, t, he => WP.block_nil ⟨he, fun _ h => absurd h (by omega), fun _ _ _ => rfl, Frame.refl _ _,
      Keep.refl _ _⟩
  | n + 1, hn, t, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.copies_ok hp n (by omega) t he) fun t₁ ⟨he₁, hw₁, hk₁, hf₁, k₁⟩ => ?_
    refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.copyArg_ok hp he₁ (show n < 12 by omega)) fun t' ⟨he', hm, k'⟩ =>
      ⟨he', fun i hi => ?_, fun d hd hd' => ?_, hf₁.trans (hm ▸ (Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (d := 8 * (n + 2)) (n := 8) (k := 112)
          (by omega) (by omega))), (k₁.trans k').mono (by decide)⟩
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.word_wo _ _ _ (.inr (by omega)) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega)]
        exact hw₁ i hi
      · exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
    · rw [hm, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.word_wo _ _ _ (by omega) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes at *; omega)]
      exact hk₁ d (by omega) hd'

theorem callArgs_eq : VG.Impl.RsaPkcs1Sig.X86_64.Sign.callArgs =
    (([.mov .rdi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut)), .mov .rsi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOl)), .mov .rdx (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Sign.oN)), .mov .rcx (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK)),
      .mov .r8 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Sign.oE)), .mov .r9 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Sign.oEl))] : List Instr) ++ VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea .rax oEM ++
      ([.store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 0) .rax, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 8) .rcx] : List Instr)) ++ (List.range 12).flatMap VG.Impl.RsaPkcs1Sig.X86_64.Sign.copyArg := by
  simp only [VG.Impl.RsaPkcs1Sig.X86_64.Sign.callArgs, List.append_assoc]

/-- The arguments of `vg_rsa_private_checked`. -/
theorem callArgs_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) :
    WP isa (.block VG.Impl.RsaPkcs1Sig.X86_64.Sign.callArgs) t fun t' => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t' ∧ (∀ i < 14, VG.Proof.Bignum.X86_64.word t'.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * i) = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg s i) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rdx ∧
      t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 ∧
      Frame [⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 112⟩] t.mem t'.mem ∧ VG.Proof.MlKem.X86_64.Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t t' := by
  have hs := he.scr hp
  have h0 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) 8 := by
    simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArgs_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u =>
      u.mem = (t.mem.writeW (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) 8) (s.gpr .rcx) ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi ∧ u.gpr .rdx = s.gpr .rdx ∧
      u.gpr .rcx = s.gpr .rcx ∧ u.gpr .r8 = s.gpr .r8 ∧ u.gpr .r9 = s.gpr .r9) (by
    have h8 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s + 8) 8 := hs.st (d := 8) (by decide)
    xrun [VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ea_sp, he.rsp, h0, h8, hs.st (d := 8) (by decide),
      hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oOut) (by decide), hs.ld (d := oOl) (by decide), hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oN) (by decide),
      hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK) (by decide), hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oE) (by decide), hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oEl) (by decide),
      he.sOut, he.sOl, he.sN, he.sK, he.sE, he.sEl, sx_ofNat (show oEM < 2 ^ 31 by decide)]) rfl) fun u ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have f : Frame [⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 64 / 8⟩, ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) 8, 64 / 8⟩] t.mem u.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have f' : Frame [⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 112⟩] t.mem u.mem := f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (d := 8) (n := 8) (k := 112) (by decide)⟩
  have heu : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s u := by
    refine Env.of he hp (k.gpr (by decide)) k.2.1 k.2.2 f fun r hr => .inl ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 8, by simp [VG.Proof.Bignum.X86_64.off], .inl (by decide), by decide⟩
    · exact ⟨8, 8, rfl, .inl (by decide), by decide⟩
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.copies_ok hp 12 (le_refl _) u heu) fun t' ⟨he', hw, hk, hf', k'⟩ =>
    ⟨he', fun i hi => ?_, by rw [k'.gpr (by decide), hdi], by rw [k'.gpr (by decide), hsi],
      by rw [k'.gpr (by decide), hdx], by rw [k'.gpr (by decide), hcx], by rw [k'.gpr (by decide), h8],
      by rw [k'.gpr (by decide), h9], f'.trans hf', (k.trans k').mono (by decide)⟩
  match i, hi with
  | 0, _ =>
    rw [hk 0 (.inl (by decide)) (by decide), hm]
    have := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.word_wo (t.mem.writeW (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM)) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (d := 8) (d' := 0) (s.gpr .rcx)
      (.inr (by decide)) (by decide) (by decide)
    rw [this]; exact Ver.word_self0 _ _ _
  | 1, _ =>
    rw [hk 8 (.inl (by decide)) (by decide), hm]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _
  | i + 2, hi => exact hw i (by omega)

/-- The count and address of `EM`'s bytes, and the zero byte. -/
theorem wipeHead_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) :
    WP isa (.block (([.mov .r11 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK)), .mov32 .rdx (.imm 0)] : List Instr) ++ VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea .r10 oEM)) t fun u =>
      VG.Proof.MlKem.X86_64.Keep [.r11, .rdx, .r10] t u ∧ u.mem = t.mem ∧ u.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧
      u.gpr .rdx = 0 ∧ u.gpr .r10 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.r11, .rdx, .r10] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ u.gpr .rdx = 0 ∧ u.gpr .r10 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (by
    xrun [VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ea_sp, he.rsp, hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Sign.oK) (by decide), he.sK,
      sx_ofNat (show oEM < 2 ^ 31 by decide), Rec.ofNat_toNat64]) rfl) fun u ⟨h, k⟩ => ⟨k, h⟩

/-- `EM` overwritten with zeros, keeping `rax`. -/
theorem wipe_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) :
    WP isa wipe t fun u => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s u ∧ u.gpr .rax = t.gpr .rax ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat := by
  have hs := he.scr hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_toNat hp
  unfold wipe
  refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.wipeHead_ok hp he) fun t₁ ⟨k₁, hm₁, h11, hdx, h10⟩ => ?_)
  have he₁ : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t₁ := he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2
  refine wp_countdown (cnt := .r11) (N := (s.gpr .rcx).toNat) (by omega) (by omega)
    (fun i u => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s u ∧ VG.Proof.MlKem.X86_64.Keep [.r11, .rdx, .r10] t₁ u ∧ u.gpr .rdx = 0 ∧
      u.gpr .r10 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (oEM + i) ∧
      u.mem = VG.WriteBytes.writeBytes t₁.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (List.replicate i 0)) ?_ (fun u ⟨heu, ku, _, _, hmu⟩ => ?_)
    ⟨he₁, Keep.refl _ _, hdx, by rw [h10]; rfl, by simp only [List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩ h11
  · intro i hi u ⟨heu, ku, hdxu, h10u, hmu⟩ _
    have hA : InRegions u.wr (u.gpr .r10) 1 := by
      rw [h10u, heu.wr]
      obtain ⟨r, h, c⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_bytes hp (d := oEM + i) (n := 1) (by unfold oEM VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega) 0 (by decide)
      exact ⟨r, h, by simpa only [BitVec.add_zero, VG.Proof.Bignum.X86_64.off] using c⟩
    refine WP.mono (WP.keep [.r10, .r11] (Q := fun u' => u'.mem = u.mem.writeW (u.gpr .r10) (0 : Byte) ∧
        u'.gpr .r10 = u.gpr .r10 + 1 ∧ u'.gpr .r11 = u.gpr .r11 - 1 ∧ u'.zf = some (u.gpr .r11 - 1 == 0)) (by
      xrun [ea0, hA, hdxu]; rfl) rfl) fun u' ⟨⟨hm', h10', h11', hz⟩, k'⟩ => ⟨⟨?_, (ku.trans k').mono (by simp),
        by rw [k'.gpr (by decide), hdxu], ?_, ?_⟩, h11', hz⟩
    · refine Env.of heu hp (k'.gpr (by decide)) k'.2.1 k'.2.2 (hm' ▸ (Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
        ⟨oEM + i, 1, by rw [List.mem_singleton.mp hr, h10u], .inr (by unfold oEM; omega),
          by unfold oEM VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega⟩
    · rw [h10', h10u]; exact off_off _ _ _
    · rw [hm', hmu, h10u, List.replicate_succ', VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate,
        show VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM + BitVec.ofNat 64 i = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (oEM + i) from off_off _ _ _]
  · refine ⟨heu, ku.gpr (by decide) |>.trans (k₁.gpr (by decide)), ?_⟩
    rw [hmu, hm₁]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (frame_writeBytes t.mem _ _).bytes (R := ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩)
      (fun r hr => ?_) (by dsimp only; omega) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr, List.length_replicate]
    have h := hp.dKo.sub_left (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_sub s (d := oEM) (n := (s.gpr .rcx).toNat)
      (by unfold oEM VG.Impl.RsaPkcs1Sig.X86_64.Sign.frameBytes; omega))
    rw [hp.hsi] at h
    exact h.symm

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignEntry`. -/
section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the entry of `vg_rsa_private_checked`

Everything the call uses is in the function's stack, at offsets of its
base `kb`: the callee's stack (`stackBytes` bytes at `kb`), the return
address (at `kb + stackBytes`), and the frame above (at
`kb + stackBytes + 8`), which holds the call's stack arguments and `EM`. Its
precondition at the call (`priv_pre`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (chkContract stackBytes)

theorem fb_kb (s : State) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3256 := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_eq s

/-- The callee's stack pointer. -/
theorem fb_sub8 (s : State) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s - 8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248 := by
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_kb, VG.Proof.Bignum.X86_64.off, VG.Proof.Bignum.X86_64.off, show (3256 : Nat) = 3248 + 8 from rfl, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem ksub (s : State) {d n : Nat} (h : d + n ≤ sigStack) : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) d, n⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s) :=
  Offset.sub_base _ h

theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (rd wr : List Region) {i : Nat} (hi : i < 100) :
    stackArg (t.callEntry.withRegions rd wr) i = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * i) := by
  have hsep := Offset.sep (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) (d := 3248 + 8 * (i + 1)) (n := 8) (e := 3248) (k := 8) (by omega) (by omega)
    (by omega)
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_sub8]
  rw [VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, ← BitVec.ofNat_add, Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * i)) 64
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_kb, off_off, show 3248 + 8 * (i + 1) = 3256 + 8 * i by omega]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_sub8]
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_kb, VG.Proof.Bignum.X86_64.off, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `EM`, as the call's input. -/
def emR (s : State) : Region := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM, (s.gpr .rcx).toNat⟩

/-- What the call reads: `n`, `e`, `EM`, the key's parts and its stack
arguments. -/
def privRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR s,
    ⟨stackArg s 3, (stackArg s 4).toNat⟩, ⟨stackArg s 5, (stackArg s 6).toNat⟩,
    ⟨stackArg s 7, (stackArg s 8).toNat⟩, ⟨stackArg s 9, (stackArg s 10).toNat⟩,
    ⟨stackArg s 11, (stackArg s 12).toNat⟩, ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 112⟩]

/-- What it writes: `out` and the working space. -/
def privWr (s : State) : List Region := [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s]

theorem priv_pre {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s)
    (hw : ∀ i < 14, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * i) = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    chkContract.pre (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)) := by
  have hE : ∀ i, i < 14 → stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)) i = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg s i :=
    fun i hi => (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stackArg_entry hsp _ _ (by omega)).trans (hw i hi)
  have hE2 : ∀ j, j < 12 → stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)) (j + 2) = stackArg s (j + 3) :=
    fun j hj => hE (j + 2) (by omega)
  simp only [chkContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg,
    (hE2 0 (by decide) : stackArg _ 2 = _), (hE2 1 (by decide) : stackArg _ 3 = _),
    (hE2 2 (by decide) : stackArg _ 4 = _), (hE2 3 (by decide) : stackArg _ 5 = _),
    (hE2 4 (by decide) : stackArg _ 6 = _), (hE2 5 (by decide) : stackArg _ 7 = _),
    (hE2 6 (by decide) : stackArg _ 8 = _), (hE2 7 (by decide) : stackArg _ 9 = _),
    (hE2 8 (by decide) : stackArg _ 10 = _), (hE2 9 (by decide) : stackArg _ 11 = _),
    (hE2 10 (by decide) : stackArg _ 12 = _), (hE2 11 (by decide) : stackArg _ 13 = _), VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_sub8]
  have ⟨hK1, hK2⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb_toNat hp
  have e1 : sigStack = 4448 := rfl
  have e2 : oEM = 160 := rfl
  have e3 : stackBytes = 3248 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hfb : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3256 := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_kb s
  have hem : VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3416 := by rw [hfb, off_off]; rfl
  have sM : Region.Sub (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s) := by simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR]; rw [hem]; exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ksub s (by omega)
  have sA : Region.Sub ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 112⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s) := by rw [hfb]; exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ksub s (by decide)
  have sR : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248, 8⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s) := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ksub s (by decide)
  have sK : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248 - BitVec.ofNat 64 3248, 3248⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s) := by
    rw [show VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248 - BitVec.ofNat 64 3248 = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s from BitVec.add_sub_cancel _ _]
    exact Region.sub_prefix (by decide)
  have hkk : VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248 - BitVec.ofNat 64 3248 = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s := BitVec.add_sub_cancel _ _
  have dMA : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR s).Disjoint ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 112⟩ := by
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR]; rw [hem, hfb]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have dRM : (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248, 8⟩ : Region).Disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR s) := by
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR]; rw [hem]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dRA : (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248, 8⟩ : Region).Disjoint ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 112⟩ := by
    rw [hfb]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
  have dKM : (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248 - BitVec.ofNat 64 3248, 3248⟩ : Region).Disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR s) := by
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR]; rw [hkk, hem]; exact Offset.base_disjoint _ (by omega) (by omega)
  have dKA : (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248 - BitVec.ofNat 64 3248, 3248⟩ : Region).Disjoint ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, 112⟩ := by
    rw [hkk, hfb]; exact Offset.base_disjoint _ (by omega) (by omega)
  have wM : (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [hem, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.toNat_off (by omega)]; omega
  have hR : (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) 3248).toNat = (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s).toNat + 3248 := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.toNat_off (by omega)
  have dK := hp.dKo; have dKn := hp.dKn; have dKe := hp.dKe; have dKp := hp.dKp; have dKq := hp.dKq
  have dKdp := hp.dKdp; have dKdq := hp.dKdq; have dKqi := hp.dKqi; have dKs := hp.dKs
  refine ⟨by omega, by omega, rfl, rfl, hp.dOn, hp.dOe, (dK.sub_left sM).symm, hp.dOp, hp.dOq, hp.dOdp, hp.dOdq,
    hp.dOqi, hp.dOs, (dK.sub_left sA).symm,
    hp.dns, hp.des, dKs.sub_left sM, hp.dps, hp.dqs, hp.ddps, hp.ddqs, hp.dqis, (dKs.sub_left sA).symm,
    dK.sub_left sR, dKn.sub_left sR, dKe.sub_left sR, dRM, dKp.sub_left sR, dKq.sub_left sR, dKdp.sub_left sR,
    dKdq.sub_left sR, dKqi.sub_left sR, dKs.sub_left sR, dRA,
    dK.sub_left sK, dKn.sub_left sK, dKe.sub_left sK, dKM, dKp.sub_left sK, dKq.sub_left sK, dKdp.sub_left sK,
    dKdq.sub_left sK, dKqi.sub_left sK, dKs.sub_left sK, dKA,
    hp.wO, hp.wN, hp.wE, wM, hp.wP, hp.wQ, hp.wDp, hp.wDq, hp.wQi, hp.wS, ⟨hk1, hk2⟩, hp.hsi, trivial, hp.L1,
    hp.L2, hp.pl1, hp.pl2, hp.ql1, hp.ql2, hp.hdpl, hp.hqil, hp.hdql, by simp only [Spec.Rsa.scratchWords]; exact hp.hsl⟩

/-! ## Memory across the call -/

theorem priv_covers {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) :
    Covers (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s ++ VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s) (t.rd ++ t.wr) ∧ Covers (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s) t.wr := by
  have hk2 := hp.k2
  have hfr : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hout : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR]
  have hscr : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR]
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR]; omega⟩
    · exact ⟨_, hscr, 0, z _, by simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR]; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, oEM, rfl, by dsimp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.emR]; unfold oEM frameBytes; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 3, (stackArg s 4).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 5, (stackArg s 6).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 7, (stackArg s 8).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 9, (stackArg s 10).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 11, (stackArg s 12).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold frameBytes; omega⟩

/-- The callee's stack and the return address, below the frame. -/
theorem below_kb (s : State) : below (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (3248 + 8) = ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s, 3256⟩ := by
  simp only [below]; rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_kb]; exact congrArg (Region.mk · 3256) (BitVec.add_sub_cancel _ _)

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s) ∨ Region.Sub r (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s) ∨ Region.Sub r (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s)) :
    Frame [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

/-- What the call writes is apart from the frame. -/
theorem frame_apart {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) {d n : Nat} (hd : d + n ≤ frameBytes) :
    ∀ r ∈ VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s ++ [below (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (3248 + 8)], (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.dKo.sub_left (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_sub s hd))
  · exact (hp.dKs.sub_left (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_sub s hd))
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.below_kb, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_kb, off_off]
    exact (Offset.base_disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) (e := 3256 + d) (n := n) (k := 3256) (by omega)
      (by have := (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb_toNat hp).1; unfold frameBytes at hd; unfold sigStack at this; omega)).symm

theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) :
    Frame [below (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (3248 + 8)] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {p : Addr} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨VG.Proof.Bignum.X86_64.off p d, 8⟩ : Region).Disjoint r) : VG.Proof.Bignum.X86_64.word m' p d = VG.Proof.Bignum.X86_64.word m p d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCall`. -/
section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the call of `vg_rsa_private_checked`

The private operation, for an implementation `v` of the CRT (`CrtImpl`), is
`vg_rsa_private_checked`'s code (`privCode v`), which has a frame of its own:
it uses 3248 bytes of stack (`privCode_depth`). Its arguments
(`callArgs_ok`) and the call (`priv_call`), which signs `EM` into `out`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract code_correct code_spSafe)

/-! ## The private operation -/

/-- The names of the public operation `vg_rsa_private_checked` calls, as in
`Generic/RsaPrivateCrt/X86_64/Rsa.lean`. -/
def pcName (v : CrtImpl) : String := Spec.Rsa.publicPrecomputeApi.name ++ v.montSuffix
def pdName (v : CrtImpl) : String := Spec.Rsa.publicPrecomputedCheckedApi.name ++ v.montSuffix

/-- `vg_rsa_private_checked`'s name and code, for `v`. -/
def privName (v : CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ v.suffix
def privCode (v : CrtImpl) : Prog isa :=
  Impl.Rsa.X86_64.PrivChecked.code v.name v.code (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pcName v) (Impl.Rsa.X86_64.Precompute.code v.mont.mm)
    (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pdName v) (Impl.Rsa.X86_64.Checked.precomputedChecked v.mont.mm)

/-- Code that never writes `rsp` and makes no calls uses no stack. -/
theorem xdepth_zero {c : Prog isa} (hsp : NoSp c) (hd : c.depth = 0) : c.x86_64Depth = 0 := by
  induction c with
  | block _ => rfl
  | seq a b iha ihb =>
    simp only [Code.depth, Nat.max_eq_zero_iff] at hd
    simp only [Code.x86_64Depth, iha (fun i hi => hsp i (by simp [instrs, hi])) hd.1,
      ihb (fun i hi => hsp i (by simp [instrs, hi])) hd.2, Nat.max_self]
  | ite _ t e iht ihe =>
    simp only [Code.depth, Nat.max_eq_zero_iff] at hd
    simp only [Code.x86_64Depth, iht (fun i hi => hsp i (by simp [instrs, hi])) hd.1,
      ihe (fun i hi => hsp i (by simp [instrs, hi])) hd.2, Nat.max_self]
  | loop b _ ih => exact ih (fun i hi => hsp i (by simpa [instrs] using hi)) hd
  | call _ b _ => simp [Code.depth] at hd
  | frame i b j ih =>
    simp only [Code.depth] at hd
    have hi := hsp i (by simp [instrs])
    simp only [Code.x86_64Depth, ih (fun x hx => hsp x (by simp [instrs, hx])) hd]
    cases i <;> simp_all [Taint.clobbers, X86_64.Instr.frameBytes]

theorem privCode_depth (v : CrtImpl) : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v).x86_64Depth = 3248 := by
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode, Impl.Rsa.X86_64.PrivChecked.code, Impl.Rsa.X86_64.PrivChecked.body,
    Impl.Rsa.X86_64.PrivChecked.check, Impl.Rsa.X86_64.PrivChecked.tail, List.cons_append, List.nil_append,
    Impl.Bignum.X86_64.seqs, Code.x86_64Depth, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.xdepth_zero v.nosp v.depth, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.xdepth_zero v.pcNosp v.pcDepth,
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.xdepth_zero v.pdNosp v.pdDepth, X86_64.Instr.frameBytes, Impl.Rsa.X86_64.PrivChecked.frameBytes,
    Impl.Rsa.X86_64.PrivChecked.cmpLoop, Impl.Rsa.X86_64.PrivChecked.releaseLoop]
  rfl

/-- The call of `vg_rsa_private_checked`: `out` holds the signature of
`EM`, or zeros. -/
theorem priv_call (v : CrtImpl) {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t)
    (hw : ∀ i < 14, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * i) = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg s i)
    (hdi : t.gpr .rdi = s.gpr .rdi) (hsi : t.gpr .rsi = s.gpr .rsi) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) t fun t' => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t' ∧
      Spec.Rsa.writtenOutcome t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)) ∧
      (∀ d n, d + n ≤ frameBytes → ∀ i < n,
        t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d + BitVec.ofNat 64 i) = t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d + BitVec.ofNat 64 i)) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hcw⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_covers hp he
  have hd := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode_depth v
  unfold VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode at hd
  refine WP.call_sp_mx (k := chkContract) (VG.Proof.Rsa.X86_64.code_correct v (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pcName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pdName v))
    (SpSafe.of_all (VG.Proof.Rsa.X86_64.code_spSafe v _ _)) (by rw [hd]; decide)
    (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_pre hp he.rsp hw hdi hsi hdx hcx h8 h9) hc hcw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [hd, he.rsp] at hf
  have hE : ∀ i, i < 14 → stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)) i = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg s i :=
    fun i hi => (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stackArg_entry he.rsp _ _ (by omega)).trans (hw i hi)
  have hE2 : ∀ j, j < 12 → stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)) (j + 2) = stackArg s (j + 3) :=
    fun j hj => hE (j + 2) (by omega)
  have hfE : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s] s.mem t.callEntry.mem :=
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_call he.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.below_kb]; exact .inl (Region.sub_prefix (by decide))
  have hk2 := hp.k2
  have b : ∀ {p : Addr} {len : Nat}, (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s).Disjoint ⟨p, len⟩ → (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s).Disjoint ⟨p, len⟩ →
      (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.bytes_of_frame hfE hk ho hs hl
  have hEM : Spec.Rsa.bytesAt t.callEntry.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (s.gpr .rcx).toNat := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callEntry_frame he.rsp).bytes
      (R := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM, (s.gpr .rcx).toNat⟩) (fun r hr => ?_) (by dsimp only; omega) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.below_kb, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_kb, off_off]
    exact (Offset.base_disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb s) (e := 3256 + oEM) (n := (s.gpr .rcx).toNat) (k := 3256) (by omega)
      (by have := (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb_toNat hp).1; unfold oEM; unfold sigStack at this; omega)).symm
  simp only [chkContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, h9, hE 0 (by decide), VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg, hm₂, hg₂ .rax (by decide),
    (hE2 0 (by decide) : stackArg _ 2 = _), (hE2 1 (by decide) : stackArg _ 3 = _),
    (hE2 2 (by decide) : stackArg _ 4 = _), (hE2 3 (by decide) : stackArg _ 5 = _),
    (hE2 4 (by decide) : stackArg _ 6 = _), (hE2 6 (by decide) : stackArg _ 8 = _),
    (hE2 8 (by decide) : stackArg _ 10 = _)] at hpost
  rw [b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), b hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega),
    hEM, b hp.dKp hp.dOp hp.dps.symm (by have := hp.wP; omega), b hp.dKq hp.dOq hp.dqs.symm (by have := hp.wQ; omega),
    ← hp.hdpl, b hp.dKdp hp.dOdp hp.ddps.symm (by have := hp.wDp; omega), hp.hdpl,
    ← hp.hdql, b hp.dKdq hp.dOdq hp.ddqs.symm (by have := hp.wDq; omega), hp.hdql,
    ← hp.hqil, b hp.dKqi hp.dOqi hp.dqis.symm (by have := hp.wQi; omega), hp.hqil] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, fun d n hd i hi => ?_, hcs, hmx⟩
  · simp only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (.inl (Ver.sub_refl _))
    · exact .inr (.inr (Ver.sub_refl _))
    · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.below_kb]; exact .inl (Region.sub_prefix (by decide))
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_apart hp (by decide))]; exact he.sOut
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_apart hp (by decide))]; exact he.sOl
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_apart hp (by decide))]; exact he.sN
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_apart hp (by decide))]; exact he.sK
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_apart hp (by decide))]; exact he.sE
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_apart hp (by decide))]; exact he.sEl
  · have := (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_toNat hp).1
    exact hf.bytes (R := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) d, n⟩) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_apart hp hd) (by dsimp only; unfold frameBytes at hd; omega) hi

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCorrect`. -/
section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: correctness

The encoding into `EM`, then zeros to `out` if it fails, or the private
operation on `EM` and zeros to `EM` (`afterEnc_ok`); the whole function
(`code_correct`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea test0)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes
open VG.Proof.Rsa.X86_64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (test0_ok freed)

theorem writtenOutcome_of {m m' : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (hb : Spec.Rsa.bytesAt m' out n = Spec.Rsa.bytesAt m out n) (h : Spec.Rsa.writtenOutcome m out n r o) :
    Spec.Rsa.writtenOutcome m' out n r o := by
  cases o <;> exact ⟨h.1, hb.trans h.2⟩

/-- The result of the private operation on the encoding `o`, or `invalid`. -/
def privOut (s : State) : Option (List Byte) → Spec.Rsa.Outcome
  | some em => Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) em
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)
  | none => .invalid

/-- After the encoding, whose result is `o`. -/
theorem afterEnc_ok (v : CrtImpl) {s t₁ t₂ : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (he₁ : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t₁)
    (h8₁ : t₁.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (hK₂ : VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob t₁ t₂) {o : Option (List Byte)}
    (hlen : ∀ em, o = some em → em.length = (s.gpr .rcx).toNat) (hpost : EOut t₁ t₂ o) :
    WP isa (afterEnc (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) t₂ fun u => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s u ∧
      Spec.Rsa.writtenOutcome u.mem (s.gpr .rdi) (s.gpr .rcx).toNat ((u.gpr .rax).setWidth 32)
        (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privOut s o) ∧
      (∀ r ∈ calleeSaved, u.gpr r = t₂.gpr r) ∧ u.mxcsr.extractLsb' 6 10 = t₂.mxcsr.extractLsb' 6 10 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb_toNat hp
  unfold afterEnc
  refine WP.seq (WP.mono_mx (by decide) (test0_ok t₂) fun t₃ ⟨hs₃, hz₃⟩ hmx₃ => ?_)
  cases o with
  | none =>
    obtain ⟨hax, hm₂⟩ := hpost
    have he₃ : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t₃ := he₁.regs (by rw [hs₃.1, hK₂.gpr (by decide)]) (hs₃.2.1.trans hm₂)
      (hs₃.2.2.1.trans hK₂.2.1) (hs₃.2.2.2.trans hK₂.2.2)
    refine WP.ite true (by simp [VG.X86_64.eval, hz₃, hax]) (fun _ => ?_) (by simp)
    refine WP.mono_mx (by decide) (WP.keep [.rdi, .rsi, .r8, .r10, .rax] (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.zeroSlots_ok hp he₃) (by decide))
      fun u ⟨⟨heu, hax', hout⟩, ku⟩ hmx => ⟨heu, ⟨hax', hout⟩, fun r hr => ?_, by rw [hmx, hmx₃]⟩
    rw [ku.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
      hs₃.1]
  | some em =>
    obtain ⟨hax, hm₂⟩ := hpost
    have hl : em.length = (s.gpr .rcx).toNat := hlen em rfl
    have he₂ : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t₂ := Env.of he₁ hp (hK₂.gpr (by decide)) hK₂.2.1 hK₂.2.2 (hm₂ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM, (s.gpr .rcx).toNat, by rw [List.mem_singleton.mp hr, h8₁, hl], .inr (Nat.le_refl _),
        by unfold oEM frameBytes; omega⟩
    have he₃ : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t₃ := he₂.regs (by rw [hs₃.1]) hs₃.2.1 hs₃.2.2.1 hs₃.2.2.2
    refine WP.ite false (by simp [VG.X86_64.eval, hz₃, hax]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono_mx (by decide) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArgs_ok hp he₃)
      fun t₄ ⟨he₄, hw₄, hdi, hsi, hdx, hcx, h8, h9, hf₄, k₄⟩ hmx₄ => ?_)
    have hEM : Spec.Rsa.bytesAt t₄.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (s.gpr .rcx).toNat = em := by
      have h₁ : Spec.Rsa.bytesAt t₄.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (s.gpr .rcx).toNat := by
        simp only [Spec.Rsa.bytesAt]
        refine List.map_congr_left fun i hi => hf₄.bytes (R := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM, (s.gpr .rcx).toNat⟩)
          (fun r hr => ?_) (by dsimp only; omega) (List.mem_range.mp hi)
        rw [List.mem_singleton.mp hr]
        exact (Offset.base_disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (e := oEM) (n := (s.gpr .rcx).toNat) (k := 112) (by decide)
          (by unfold oEM frameBytes at *; omega)).symm
      have h₂ := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_writeBytes t₁.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) em (by omega)
      rw [hl] at h₂
      rw [h₁, hs₃.2.1, hm₂, h8₁, h₂]
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_call v hp he₄ hw₄ hdi hsi hdx hcx h8 h9)
      fun t₅ ⟨he₅, hout₅, _, hcs₅, hmx₅⟩ => ?_)
    rw [hEM] at hout₅
    refine WP.mono_mx (by decide) (WP.keep [.r11, .rdx, .r10] (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.wipe_ok hp he₅) (by decide))
      fun u ⟨⟨heu, haxu, hbytes⟩, ku⟩ hmxu => ⟨heu, ?_, fun r hr => ?_, ?_⟩
    · rw [haxu]; exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.writtenOutcome_of hbytes hout₅
    · have hr' : r ∉ [Reg.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] := by
        simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
      rw [ku.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        hcs₅ r hr, k₄.gpr hr', hs₃.1]
    · rw [hmxu, hmx₅, hmx₄, hmx₃]

/-- The frame: its body runs from `allocState frameBytes s` and ends with
`rsp` and the writable regions as the push left them. -/
theorem wp_alloc {body : Prog isa} {s : State} {Q : State → Prop} (hsp : frameBytes ≤ (s.gpr .rsp).toNat)
    (hb : WP isa body (allocState frameBytes s) fun s₂ => s₂.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s ∧
      s₂.wr = (allocState frameBytes s).wr ∧ Q (freed frameBytes s₂)) :
    WP isa (.frame (.alloc frameBytes) body (.free frameBytes)) s Q := by
  obtain ⟨t, s₂, he, hsp₂, hw, hq⟩ := hb
  have ha : isa.push (.alloc frameBytes) s = some (allocState frameBytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp⟩
  have hf : isa.pop (.free frameBytes) (allocState frameBytes s) s₂ = some (freed frameBytes s₂) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨by decide, by decide, by decide, hsp₂, hw, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) {m : Mem} (h : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := sigStack) (d := 0) (k := 8)
      (by unfold sigStack; omega)
    simpa only [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.kb, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem signId_eq (nB eB pB qB dPB dQB qInvB : List Byte) (x : BitVec 32) (H : List Byte) :
    Spec.RsaPkcs1Sig.signId nB eB pB qB dPB dQB qInvB x.toNat H =
      match encodeId x H nB.length with
      | some em => Spec.Rsa.privateChecked nB eB em pB qB dPB dQB qInvB
      | none => .invalid := by
  unfold Spec.RsaPkcs1Sig.signId encodeId Spec.RsaPkcs1Sig.sign
  cases Spec.RsaPkcs1Sig.Hash.ofId x.toNat <;> rfl

theorem encodeId_length {x : BitVec 32} {H : List Byte} {k : Nat} {em : List Byte}
    (h : encodeId x H k = some em) : em.length = k := by
  unfold encodeId at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.encode_length h
  · cases h

theorem code_correct (v : CrtImpl) (s : State) (h : sigContract.pre s) :
    ∃ t s', Exec isa (VG.Impl.RsaPkcs1Sig.X86_64.Sign.code (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) s t s' ∧ abiPreserved s s' ∧ sigContract.post s s' := by
  have hp := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of h
  have hk2 := hp.k2
  suffices hw : WP isa (VG.Impl.RsaPkcs1Sig.X86_64.Sign.code (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) s fun s' => abiPreserved s s' ∧ sigContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  refine VG.Proof.RsaPkcs1Sig.X86_64.Sgn.wp_alloc (by have := hp.sp1; unfold sigStack at this; unfold frameBytes; omega) ?_
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.body
  refine WP.seq (WP.mono_mx (by decide) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.head_ok hp) fun t₁ ⟨he₁, h8₁, hcx₁, hdx₁, hsi₁, h9₁, hcs₁⟩ hmx₁ => ?_)
  refine WP.seq (WP.mono_mx (by decide +kernel) (encode_ok (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encPre hp he₁ h8₁ hcx₁ hdx₁ hsi₁ h9₁))
    fun t₂ ⟨hK₂, hout₂⟩ hmx₂ => ?_)
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.afterEnc_ok v hp he₁ h8₁ hK₂ (fun em h' => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encodeId_length h') hout₂)
    fun u ⟨heu, hwu, hcsu, hmxu⟩ => ⟨heu.rsp, by rw [heu.wr]; rfl, ⟨fun r hr => ?_, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.ret_frame hp heu.mem, ?_⟩, ?_⟩
  · by_cases hr' : r = .rsp
    · subst hr'
      show u.gpr .rsp + BitVec.ofNat 64 frameBytes = s.gpr .rsp
      rw [heu.rsp, BitVec.sub_add_cancel]
    · show (if r = .rsp then _ else u.gpr r) = s.gpr r
      simp only [hr', ↓reduceIte]
      rw [hcsu r hr, hK₂.gpr (by simp [calleeSaved, VG.Proof.RsaPkcs1Sig.X86_64.clob] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all),
        hcs₁ r hr hr']
  · show u.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
    rw [hmxu, hmx₂, hmx₁]; rfl
  · show Spec.Rsa.writtenOutcome u.mem _ _ _ _
    have hH : Spec.Rsa.bytesAt t₁.mem (t₁.gpr .rsi) (t₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat := by
      rw [hsi₁, h9₁]
      exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.bytes_of_frame he₁.mem hp.dKd hp.dOd hp.dds.symm (by have := hp.wD; omega)
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.signId_eq, VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length, ← hH]
    exact hwu

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCT`. -/
section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: constant time

As for `vg_rsa_pkcs1_recover` (`RecoverCT.lean`): each point of the code is
described, in each run, by what correctness says of it from that run's entry
state, which agrees with an anchor on the public data (`At`). The blocks are
checked by the taint analysis from the registers this fixes, the branch on
`encode`'s result is fixed by it too (whether the encoding succeeds depends
on the hash function, the length of the hash value and `k` alone), and the
call is constant time for `vg_rsa_private_checked`'s contract, whose public
data (its registers and stack arguments, `n` and `e`) it fixes. The zeros to
`out` and to `EM` take their address and length from the frame's slots:
their loads are pieces of their own, and the loops after them are checked
from the registers correctness fixes.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea test0)
open VG.Impl.RsaPkcs1Sig.X86_64.Recover (zeroOut)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.Rsa.X86_64 (CrtImpl chkContract)
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (test0_ok entry_regs regs_eq)

/-! ## The taint checks -/

theorem head_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block (slotStores ++ encArgs)) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem zeroHead_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block [.mov .rdi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOut)), .mov .rsi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOl))]) fun _ _ => True :=
  two_taint [.rsp] h (by taint_decide)

theorem callArgs_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block VG.Impl.RsaPkcs1Sig.X86_64.Sign.callArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem wipeHead_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block (([.mov .r11 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oK)), .mov32 .rdx (.imm 0)] : List Instr) ++ lea .r10 oEM))
      fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem wipeLoop_taint {Φ : State → State → Prop} (h : Pins Φ [.r10, .r11]) :
    RelCT isa (Two Φ)
      (.loop (.block [.store8 { base := .r10 } .rdx, .alu .add .r10 (.imm 1), .alu .sub .r11 (.imm 1)]) .ne)
      fun _ _ => True := two_taint [.r10, .r11] h (by taint_decide)

/-! ## Entry states and the anchor -/

def Sib (a s : State) : Prop := sigContract.pre s ∧ sigContract.pub a s

theorem pub_refl (s : State) : sigContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.h {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) : (stackArg s 0).setWidth 32 = (stackArg a 0).setWidth 32 :=
  h.2.2.1.symm

theorem Sib.arg {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) {i : Nat} (hi : 1 ≤ i) (hi' : i < 15) : stackArg s i = stackArg a i := by
  have := (List.map_inj_left.mp h.2.2.2.1) (i - 1) (List.mem_range.mpr (by omega))
  simp only [show i - 1 + 1 = i by omega] at this
  exact this.symm

theorem Sib.n {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.2.2.2.1.symm

theorem Sib.e {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s ∧ J s t

theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At J a t₁) (h₂ : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s → f s = f a) :
    ∀ a t₁ t₂, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At J a t₁ → VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, sigContract.pre s → J s t → t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) :
    Pins (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At J) [.rsp] :=
  fun _ _ _ ⟨_, S₁, j₁⟩ ⟨_, S₂, j₂⟩ r hr => by
    rw [List.mem_singleton.mp hr, hJ _ _ S₁.1 j₁, hJ _ _ S₂.1 j₂, S₁.fb, S₂.fb]

theorem at_and {J : State → State → Prop} {P : State → Prop} {a t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At J a t ∧ P t) :
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At (fun s t => J s t ∧ P t) a t :=
  let ⟨⟨s, S, j⟩, p⟩ := h; ⟨s, S, j, p⟩

theorem two_and {J : State → State → Prop} {P : State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At fun s t => J s t ∧ P t)) c Q) :
    RelCT isa (Two fun a t => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At J a t ∧ P t) c Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.at_and h₁, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.at_and h₂⟩) fun _ _ h => h

/-! ## The points of the code -/

def JA (s t : State) : Prop := t = allocState frameBytes s

def J1 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧ t.gpr .r9 = stackArg s 2

/-- The encoding of the hash value, as the entry state gives it. -/
def encOut (s : State) : Option (List Byte) :=
  encodeId ((stackArg s 0).setWidth 32) (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)
    (s.gpr .rcx).toNat

/-- Whether the encoding succeeds depends on the hash value's length alone. -/
theorem encodeId_isSome {x : BitVec 32} {H H' : List Byte} {k : Nat} (h : H.length = H'.length) :
    (encodeId x H k).isSome = (encodeId x H' k).isSome := by
  unfold encodeId
  split
  · simp only [Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo, List.length_append, h]
    split <;> rfl
  · rfl

theorem encOut_sib {a s : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut s).isSome = (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut a).isSome := by
  unfold VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut
  rw [S.h, S.gpr (r := .rcx) (by decide)]
  exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encodeId_isSome (by rw [VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length, VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length, S.arg (by decide) (by decide)])

def J2 (s t : State) : Prop := ∃ t₁, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J1 s t₁ ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob t₁ t ∧ EOut t₁ t (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut s)

def J3 (s t : State) : Prop := ∃ t₂, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J2 s t₂ ∧ SameF t₂ t ∧ t.zf = some !(VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut s).isSome

theorem J3_env {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.PreS s) (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J3 s t) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t := by
  obtain ⟨t₂, ⟨t₁, ⟨he₁, h8₁, -⟩, hK, hout⟩, hs, -⟩ := h
  have hk2 := hp.k2
  have he₂ : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t₂ := by
    cases ho : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut s with
    | none =>
      rw [ho] at hout
      exact he₁.regs (by rw [hK.gpr (by decide)]) hout.2 hK.2.1 hK.2.2
    | some em =>
      rw [ho] at hout
      have hl : em.length = (s.gpr .rcx).toNat := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encodeId_length ho
      exact Env.of he₁ hp (hK.gpr (by decide)) hK.2.1 hK.2.2 (hout.2 ▸ frame_writeBytes _ _ _)
        fun r hr => .inl ⟨oEM, (s.gpr .rcx).toNat, by rw [List.mem_singleton.mp hr, h8₁, hl],
          .inr (Nat.le_refl _), by unfold oEM frameBytes; omega⟩
  exact he₂.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2

theorem J3_rsp {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J3 s t) : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s := by
  obtain ⟨t₂, ⟨t₁, ⟨he₁, -⟩, hK, -⟩, hs, -⟩ := h
  rw [hs.1, hK.gpr (by decide), he₁.rsp]

def J4 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t ∧ (∀ i < 14, VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) (8 * i) = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg s i) ∧
    t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi ∧ t.gpr .rdx = s.gpr .rdx ∧
    t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9

def J6 (s t : State) : Prop :=
  t.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ t.gpr .r10 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM

/-! ## The call -/

theorem entryBytes {s t : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stkR s).Disjoint ⟨p, len⟩) (ho : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.outR s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.bytes_of_frame (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.frame_call he.mem (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.below_kb]; exact .inl (Region.sub_prefix (by decide))) hk ho hs hl

theorem callArg_sib {a s : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) {i : Nat} (hi : i < 14) : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg s i = VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg a i := by
  match i, hi with
  | 0, _ => show VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb a) oEM; rw [S.fb]
  | 1, _ => exact S.gpr (by decide)
  | j + 2, hj => exact S.arg (by omega) (by omega)

/-- What `vg_rsa_private_checked`'s contract makes public. -/
theorem priv_view {a s t : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Sib a s) (h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J4 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)).gpr =
      [a.gpr .rdi, a.gpr .rsi, a.gpr .rdx, a.gpr .rcx, a.gpr .r8, a.gpr .r9, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb a - 8] ∧
    (List.range 14).map (stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s))) =
      (List.range 14).map (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg a) ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)).mem
      ((t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)).gpr .rdx)
      ((t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)).mem
      ((t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)).gpr .r8)
      ((t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨he, hw, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  have hp := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rdi) (by decide),
      S.gpr (r := .rsi) (by decide), S.gpr (r := .rdx) (by decide), S.gpr (r := .rcx) (by decide),
      S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide)]
  · refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.stackArg_entry he.rsp _ _ (by omega), hw i hi, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArg_sib S hi]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.entryBytes he _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), S.n]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.entryBytes he _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega), S.e]

theorem call_ct (v : CrtImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J4)) (.call (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) fun _ _ => True := by
  refine RelCT.callEx (k := chkContract) (Rsa.X86_64.code_correct v (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pcName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pdName v))
    (Rsa.X86_64.code_constantTime v _ _)
    fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, g₁, n₁, e₁⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_view S₁ j₁
  obtain ⟨r₂, g₂, n₂, e₂⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_covers (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S₁.1) j₁.1
  obtain ⟨c₂, w₂⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_covers (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S₂.1) j₂.1
  obtain ⟨he₁, hw₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁⟩ := j₁
  obtain ⟨he₂, hw₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂⟩ := j₂
  exact ⟨VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s₁, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s₁, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privRd s₂, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privWr s₂,
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_pre (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S₁.1) he₁.rsp hw₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁,
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_pre (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S₂.1) he₂.rsp hw₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂,
    ⟨regs_eq (r₁.trans r₂.symm), g₁.trans g₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## The pieces -/

theorem head_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.JA)) (.block (slotStores ++ encArgs)) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J1)) :=
  two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pins_rsp fun s t _ h => by rw [show t = _ from h]; rfl) (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = _ from ht]
      exact WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.head_ok (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S.1)) fun _ ⟨he, h8, hcx, hdx, hsi, h9, _⟩ =>
        ⟨s, S, he, h8, hcx, hdx, hsi, h9⟩

theorem encode_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J1)) encode (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J2)) :=
  two_piece [.rsp, .r8, .rcx, .rdx, .rsi, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => ((stackArg s 0).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
          (fun _ _ S => by rw [S.h]) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => stackArg s 1) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.arg (by decide) (by decide))
          h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => stackArg s 2) (fun _ _ h => h.2.2.2.2.2) (fun _ _ S => S.arg (by decide) (by decide))
          h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, j⟩ => by
      obtain ⟨he, h8, hcx, hdx, hsi, h9⟩ := j
      have hp := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S.1
      refine WP.mono (encode_ok (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encPre hp he h8 hcx hdx hsi h9)) fun u ⟨hK, hout⟩ =>
        ⟨s, S, t, ⟨he, h8, hcx, hdx, hsi, h9⟩, hK, ?_⟩
      have hH : Spec.Rsa.bytesAt t.mem (t.gpr .rsi) (t.gpr .r9).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat := by
        rw [hsi, h9]
        exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.bytes_of_frame he.mem hp.dKd hp.dOd hp.dds.symm (by have := hp.wD; omega)
      rw [hH] at hout
      exact hout

theorem test0_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J2)) (.block test0) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J3)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, j⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ => ⟨s, S, t, j, hs, by
      obtain ⟨t₁, -, -, hout⟩ := j
      rw [hz]
      cases h : VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut s with
      | none => rw [h] at hout; rw [hout.1]; rfl
      | some em => rw [h] at hout; rw [hout.1]; rfl⟩

def JZ (s t : State) : Prop := t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi

theorem zeroSlots_ct {J : State → State → Prop} (hJ : ∀ s t, sigContract.pre s → J s t → VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t) :
    RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At J)) zeroSlots fun _ _ => True := by
  unfold zeroSlots
  refine RelCT.seq (two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pins_rsp fun s t hs h => (hJ s t hs h).rsp) (by taint_decide)
    (Ψ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.JZ) fun _ t ⟨s, S, h⟩ => WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.zeroHead_ok (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S.1) (hJ s t S.1 h))
      fun _ ⟨_, _, hdi, hsi⟩ => ⟨s, S, hdi, hsi⟩) (Rec.zeroOut_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => s.gpr .rdi) (fun _ _ h => h.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂

theorem callArgs_two :
    RelCT isa (Two fun a t => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J3 a t ∧ isa.eval .e t = some false) (.block VG.Impl.RsaPkcs1Sig.X86_64.Sign.callArgs) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J4)) :=
  VG.Proof.RsaPkcs1Sig.X86_64.Sgn.two_and (two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pins_rsp fun _ _ _ h => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J3_rsp h.1) (by taint_decide)
    fun _ t ⟨s, S, j, _⟩ => WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArgs_ok (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S.1) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J3_env (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S.1) j))
      fun _ ⟨he, hw, hdi, hsi, hdx, hcx, h8, h9, _, _⟩ => ⟨s, S, he, hw, hdi, hsi, hdx, hcx, h8, h9⟩)

def J5 (s t : State) : Prop := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.Env s t

theorem call_two (v : CrtImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J4)) (.call (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J5)) :=
  two_post (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.call_ct v) fun _ _ ⟨s, S, he, hw, hdi, hsi, hdx, hcx, h8, h9⟩ =>
    WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.priv_call v (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S.1) he hw hdi hsi hdx hcx h8 h9) fun _ h => ⟨s, S, h.1⟩

theorem wipe_ct : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J5)) wipe fun _ _ => True := by
  unfold wipe
  refine RelCT.seq (two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pins_rsp fun _ _ _ h => h.rsp) (by taint_decide)
    (Ψ := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J6) fun _ t ⟨s, S, he⟩ => WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.wipeHead_ok (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of S.1) he)
      fun _ ⟨_, _, h11, _, h10⟩ => ⟨s, S, h11, h10⟩) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.wipeLoop_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.fb s) oEM) (fun _ _ h => h.2) (fun _ _ S => by rw [S.fb]) h₁ h₂
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pin (fun s => BitVec.ofNat 64 (s.gpr .rcx).toNat) (fun _ _ h => h.1)
      (fun _ _ S => by rw [S.gpr (r := .rcx) (by decide)]) h₁ h₂

/-! ## The composition -/

theorem afterEnc_ct (v : CrtImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J2)) (afterEnc (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) fun _ _ => True := by
  unfold afterEnc
  refine RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Sgn.test0_two (two_ite ?_ (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.two_and (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.zeroSlots_ct fun _ _ hs h => VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J3_env (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.preS_of hs) h.1))
    (RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Sgn.callArgs_two (RelCT.seq (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.call_two v) VG.Proof.RsaPkcs1Sig.X86_64.Sgn.wipe_ct)))
  refine VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pinEval (fun s => some !(VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut s).isSome) (fun s t h => by
    obtain ⟨_, _, _, hz⟩ := h
    simp only [VG.X86_64.eval, hz]) ?_
  intro a s S
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encOut_sib S]

theorem body_ct (v : CrtImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.JA)) (VG.Impl.RsaPkcs1Sig.X86_64.Sign.body (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) fun _ _ => True :=
  RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Sgn.head_two (RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Sgn.encode_two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.afterEnc_ct v))

/-! ## The frame -/

theorem alloc_push {s s₁ : State} (h : isa.push (.alloc frameBytes) s = some s₁) : s₁ = allocState frameBytes s := by
  simp only [isa, push] at h
  split at h
  · cases h; rfl
  · cases h

/-- A frame of `frameBytes` bytes leaks what its body does. -/
theorem relCT_alloc {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState frameBytes s₁ ∧ b = allocState frameBytes s₂)
      body R) :
    RelCT isa P (.frame (.alloc frameBytes) body (.free frameBytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ q₁ =>
    cases e₂ with
    | frame p₂ b₂ q₂ =>
      obtain rfl := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.alloc_push p₁
      obtain rfl := VG.Proof.RsaPkcs1Sig.X86_64.Sgn.alloc_push p₂
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨rfl, trivial⟩

def J0 (s t : State) : Prop := t = s

theorem code_ct (v : CrtImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.At VG.Proof.RsaPkcs1Sig.X86_64.Sgn.J0)) (VG.Impl.RsaPkcs1Sig.X86_64.Sign.code (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) fun _ _ => True := by
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Sign.code
  refine VG.Proof.RsaPkcs1Sig.X86_64.Sgn.relCT_alloc ((VG.Proof.RsaPkcs1Sig.X86_64.Sgn.body_ct v).mono ?_ fun _ _ h => h)
  rintro _ _ ⟨t₁, t₂, ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩, rfl, rfl⟩
  exact ⟨a, ⟨s₁, S₁, by rw [show t₁ = s₁ from j₁]; rfl⟩, ⟨s₂, S₂, by rw [show t₂ = s₂ from j₂]; rfl⟩⟩

theorem code_constantTime (v : CrtImpl) :
    ConstantTime isa sigContract.pre sigContract.pub (VG.Impl.RsaPkcs1Sig.X86_64.Sign.code (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) :=
  RelCT.constantTime ((VG.Proof.RsaPkcs1Sig.X86_64.Sgn.code_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ⟨s₁, ⟨s₁, ⟨h₁, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_sign`, calling `vg_rsa_private_checked` for the
implementation `v` of the CRT, meets the shared contract. -/
theorem code_verified (v : CrtImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86_64.Sign.code (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) (Spec.RsaPkcs1Sig.signContract abi sigStack) :=
  have hct : ConstantTime isa sigContract.pre sigContract.pub (VG.Impl.RsaPkcs1Sig.X86_64.Sign.code (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)) :=
    VG.Proof.RsaPkcs1Sig.X86_64.Sgn.code_constantTime v
  Verified.of_correct (k := sigContract) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.code_correct v) hct sign_implies

/-- It writes `rsp` only in its frame's push and pop, and its callee in its
own. -/
theorem code_spSafe (v : CrtImpl) : (VG.Impl.RsaPkcs1Sig.X86_64.Sign.code (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode v)).all (fun i => !isa.writesSp i) = true := by
  have h := Rsa.X86_64.code_spSafe v (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pcName v) (VG.Proof.RsaPkcs1Sig.X86_64.Sgn.pdName v)
  simp only [VG.Impl.RsaPkcs1Sig.X86_64.Sign.code, VG.Impl.RsaPkcs1Sig.X86_64.Sign.body, afterEnc, Code.all, VG.Proof.RsaPkcs1Sig.X86_64.Sgn.privCode, h, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end
