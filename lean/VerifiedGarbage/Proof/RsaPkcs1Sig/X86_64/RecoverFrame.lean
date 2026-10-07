import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCtx
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyFrame
import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Recover

/-!
# `vg_rsa_pkcs1_recover` on x86-64: the frame

`vg_rsa_pkcs1_verify`'s frame (`Ver.fb`, `Ver.stkR`, the working space at the
same stack arguments, `Ver.scrR`), with `out` written too, and other slots.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq fb_sub8 toNat_off frame_sub below_sub
  ret_disjoint outside_frame stackArgAddr_fb stackArgAddr_eq ea_sp word_wo allocState_gpr arg_ea)

/-! ## The precondition, by name -/

/-- `recContract.pre`, by name. -/
structure PreR (s : State) : Prop where
  sp1 : verStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOg : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dgs : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dsa : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKg : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wG : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wS : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  hash : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h ∧ (s.gpr .rsi).toNat = h.len
  hsl : 16 * (s.gpr .rcx).toNat ≤ (stackArg s 4).toNat

theorem preR_of {s : State} (h : recContract.pre s) : PreR s := by
  simp only [recContract] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOg, dOs, dOa, dns, des, dgs, dsa, dRo, -, -, -, dRs, -, dKo, dKn, dKe,
    dKg, dKs, dKa, wO, wN, wE, wG, wS, ⟨k1, k2⟩, L1, L2, hash, hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOg, dOs, dOa, dns, des, dgs, dsa, dRo, dRs, dKo, dKn, dKe, dKg, dKs, dKa,
    wO, wN, wE, wG, wS, k1, k2, L1, L2, hash, hsl⟩

/-- `out_len` is the length of the hash function's values: from 16 to 64. -/
theorem PreR.ol {s : State} (hp : PreR s) : 16 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64 := by
  obtain ⟨h, -, hl⟩ := hp.hash
  rw [hl]; cases h <;> decide

/-! ## The frame -/

def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩

theorem kb_toNat {s : State} (hp : PreR s) : (kb s).toNat + verStack + 48 ≤ 2 ^ 64 ∧
    (kb s).toNat + verStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold verStack at *; omega

theorem fb_toNat {s : State} (hp : PreR s) : (fb s).toNat + frameBytes + 8 + 40 ≤ 2 ^ 64 ∧
    (fb s).toNat = (kb s).toNat + 8 := by
  have ⟨h1, h2⟩ := kb_toNat hp
  rw [fb_eq, toNat_off (by unfold verStack at *; omega)]
  unfold frameBytes verStack at *; omega

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  sOut : word t.mem (fb s) oOut = s.gpr .rdi
  sOl : word t.mem (fb s) oOl = s.gpr .rsi
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9

theorem Env.scr {s t : State} (h : Env s t) (hp : PreR s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega)

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- Memory changed only in the frame turns into `Env`'s. -/
theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, outR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : PreR s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 5) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

/-- A stack argument, in memory changed only where the function may write. -/
theorem Env.arg {s t : State} (h : Env s t) (hp : PreR s) {j : Nat} (hj : j < 5) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 40⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

/-- The stack arguments are readable. -/
theorem arg_in {s t : State} (hp : PreR s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 5) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 40⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

end VG.Proof.RsaPkcs1Sig.X86_64.Rec
