import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Pub
import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Recover
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCT
import VerifiedGarbage.Proof.RsaPkcs1Sig.Recover

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverFrame`. -/
section

/-!
# `vg_rsa_pkcs1_recover` on x86-64: the frame

`vg_rsa_pkcs1_verify`'s frame (`Ver.fb`, `Ver.stkR`, the working space at the
same stack arguments, `Ver.scrR`), with `out` written too, and other slots.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
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

theorem preR_of {s : State} (h : recContract.pre s) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s := by
  simp only [recContract] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOg, dOs, dOa, dns, des, dgs, dsa, dRo, -, -, -, dRs, -, dKo, dKn, dKe,
    dKg, dKs, dKa, wO, wN, wE, wG, wS, ⟨k1, k2⟩, L1, L2, hash, hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOg, dOs, dOa, dns, des, dgs, dsa, dRo, dRs, dKo, dKn, dKe, dKg, dKs, dKa,
    wO, wN, wE, wG, wS, k1, k2, L1, L2, hash, hsl⟩

/-- `out_len` is the length of the hash function's values: from 16 to 64. -/
theorem PreR.ol {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) : 16 ≤ (s.gpr .rsi).toNat ∧ (s.gpr .rsi).toNat ≤ 64 := by
  obtain ⟨h, -, hl⟩ := hp.hash
  rw [hl]; cases h <;> decide

/-! ## The frame -/

def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩

theorem kb_toNat {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s).toNat + verStack + 48 ≤ 2 ^ 64 ∧
    (VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s).toNat + verStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold verStack at *; omega

theorem fb_toNat {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s).toNat + VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes + 8 + 40 ≤ 2 ^ 64 ∧
    (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s).toNat = (VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s).toNat + 8 := by
  have ⟨h1, h2⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.kb_toNat hp
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq, toNat_off (by unfold verStack at *; omega)]
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes verStack at *; omega

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ :: s.wr
  mem : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem t.mem
  sOut : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut = s.gpr .rdi
  sOl : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oOl = s.gpr .rsi
  sN : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oN = s.gpr .rdx
  sK : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oK = s.gpr .rcx
  sE : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oE = s.gpr .r8
  sEl : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oEl = s.gpr .r9

theorem Env.scr {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) : VG.Proof.Bignum.X86_64.Scr t (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp; omega)

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Disjoint ⟨p, len⟩) (ho : (VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

/-- Memory changed only in the frame turns into `Env`'s. -/
theorem frame_of_outside {s : State} {m : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s.mem m) :
    Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem m :=
  fun x hx => h x (.inr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) {m : Mem} (h : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s.mem m) {j : Nat}
    (hj : j < 5) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArgAddr_fb]
  exact h.word (.inr (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega)) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)

/-- A stack argument, in memory changed only where the function may write. -/
theorem Env.arg {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) {j : Nat} (hj : j < 5) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 40⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

/-- The stack arguments are readable. -/
theorem arg_in {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 5) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 40⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
    by rw [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

end VG.Proof.RsaPkcs1Sig.X86_64.Rec

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCall`. -/
section

/-!
# `vg_rsa_pkcs1_recover` on x86-64: the call of `vg_rsa_public_checked`

As for `vg_rsa_pkcs1_verify` (`VerifyCall.lean`): the arguments kept in the
frame's slots and those of the call (`slotStores_ok`, `callArgs_ok`), and the
call (`pub_call`), writing `s^e mod n` to `EM₁`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq fb_sub8 toNat_off frame_sub below_sub
  ret_disjoint outside_frame stackArgAddr_fb stackArgAddr_eq ea_sp word_wo allocState_gpr arg_ea
  stackArg_entry stackArgAddr_entry callEntry_frame sub_refl slot_keep)

/-! ## The arguments -/

def slotStores : List Instr :=
  [.store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut) .rdi, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOl) .rsi, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oN) .rdx, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oK) .rcx,
    .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oE) .r8, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oEl) .r9]

def callArgs : List Instr :=
  [.mov .rax (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.arg 1)), .mov .r10 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.arg 3)), .mov .r11 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.arg 4)),
    .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 0) .rax, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 8) .rcx, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 16) .r10, .store (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp 24) .r11,
    .mov .rsi (.reg .rcx)] ++
  VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea .rdi oEM1

theorem pubArgs_eq : pubArgs = VG.Proof.RsaPkcs1Sig.X86_64.Rec.slotStores ++ VG.Proof.RsaPkcs1Sig.X86_64.Rec.callArgs := rfl

/-- The slots. -/
theorem slotStores_ok {s A : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hA : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block VG.Proof.RsaPkcs1Sig.X86_64.Rec.slotStores) A fun t =>
      VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) t ∧ VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s.mem t.mem ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut = s.gpr .rdi ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oOl = s.gpr .rsi ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oN = s.gpr .rdx ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oK = s.gpr .rcx ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oE = s.gpr .r8 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oEl = s.gpr .r9 := by
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  have hsp : A.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s := hA.gpr (by decide)
  have hs : VG.Proof.Bignum.X86_64.Scr A (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes := Scr.of_mem (by rw [hA.2.2]; exact List.mem_cons_self ..) (by omega)
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → A.gpr r = s.gpr r := fun r h h' => by
    rw [hA.gpr (by simpa using h')]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, h]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut) (s.gpr .rdi)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oOl) (s.gpr .rsi)).writeW
        (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oN) (s.gpr .rdx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oK) (s.gpr .rcx)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oE)
        (s.gpr .r8)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Recover.oEl) (s.gpr .r9)) (by
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Rec.slotStores, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, hsp, hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut) (by decide), hs.st (d := oOl) (by decide),
      hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oN) (by decide), hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oK) (by decide), hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oE) (by decide),
      hs.st (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oEl) (by decide), hAm, g .rdi (by decide) (by decide), g .rsi (by decide) (by decide),
      g .rdx (by decide) (by decide), g .rcx (by decide) (by decide), g .r8 (by decide) (by decide),
      g .r9 (by decide) (by decide)]) rfl) fun t ⟨hm, k⟩ => ⟨(hA.trans k).mono (by simp), ?_, ?_⟩
  · rw [hm]
    intro x hx
    have hx' : VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) x := by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hx ⊢; omega
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hx hx'
    simp only [VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut, oOl, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oN, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oK, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oE, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oEl] at *
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (by omega) x (by omega)]
  · rw [hm]
    simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo, VG.Proof.Bignum.X86_64.word_writeW_self, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut, oOl, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oN, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oK, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oE, VG.Impl.RsaPkcs1Sig.X86_64.Recover.oEl, and_self]

/-- The arguments of `vg_rsa_public_checked`. -/
theorem callArgs_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hk : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) t)
    (ho : VG.Proof.Bignum.X86_64.Outside (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s.mem t.mem) :
    WP isa (.block VG.Proof.RsaPkcs1Sig.X86_64.Rec.callArgs) t fun t' => VG.Proof.MlKem.X86_64.Keep [.rax, .rdi, .rsi, .r10, .r11] t t' ∧
      t'.mem = (((t.mem.writeW (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (stackArg s 1)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8) (s.gpr .rcx)).writeW
        (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16) (stackArg s 3)).writeW (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24) (stackArg s 4) ∧
      t'.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ t'.gpr .rsi = s.gpr .rcx := by
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  have hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s := hk.gpr (by decide)
  have hs : VG.Proof.Bignum.X86_64.Scr t (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes :=
    Scr.of_mem (by rw [hk.2.2]; exact List.mem_cons_self ..) (by omega)
  have hrd : t.rd = s.rd := hk.2.1
  have g : ∀ r, r ≠ .rsp → r ≠ .rax → t.gpr r = s.gpr r := fun r h h' => by
    rw [hk.gpr (by simpa using h')]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, h]
  have h0 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 := by
    simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  refine WP.keep [.rax, .rdi, .rsi, .r10, .r11] (by
    have h8 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s + 8) 8 := hs.st (d := 8) (by decide)
    have h16 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s + 16) 8 := hs.st (d := 16) (by decide)
    have h24 : InRegions t.wr (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s + 24) 8 := hs.st (d := 24) (by decide)
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Rec.callArgs, VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, @arg_ea s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, hsp, h0, h8, h16, h24,
      hs.st (d := 8) (by decide), hs.st (d := 16) (by decide), hs.st (d := 24) (by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Rec.arg_in hp hrd (show 1 < 5 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Rec.arg_in hp hrd (show 3 < 5 by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Rec.arg_in hp hrd (show 4 < 5 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Rec.arg_outside hp ho (show 1 < 5 by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Rec.arg_outside hp ho (show 3 < 5 by decide), VG.Proof.RsaPkcs1Sig.X86_64.Rec.arg_outside hp ho (show 4 < 5 by decide),
      sx_ofNat (show oEM1 < 2 ^ 31 by decide), g .rcx (by decide) (by decide)]) rfl |>
    fun h => WP.mono h fun t' ⟨q, k⟩ => ⟨k, q⟩

/-! ## The call -/

/-- `EM₁` in the frame. -/
def em1R (s : State) : Region := ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1, (s.gpr .rcx).toNat⟩

/-- What the call reads: `n`, `e`, `sig` and its stack arguments. -/
def pubRd (s : State) : List Region :=
  [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩, ⟨stackArg s 1, (s.gpr .rcx).toNat⟩,
    ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, 32⟩]

/-- What it writes: `EM₁` and the working space. -/
def pubWr (s : State) : List Region := [VG.Proof.RsaPkcs1Sig.X86_64.Rec.em1R s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s]

theorem pub_pre {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hsig : stackArg s 2 = s.gpr .rcx) (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s)
    (hw0 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 = stackArg s 1) (hw1 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = s.gpr .rcx)
    (hw2 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16 = stackArg s 3) (hw3 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24 = stackArg s 4)
    (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    pubChk.pre (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)) := by
  have hE : ∀ i, i < 4 → stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)) i = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (8 * i) :=
    fun i hi => stackArg_entry hsp _ _ (by omega)
  simp only [pubChk, pubContract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), hdi, hsi, hdx, hcx, h8, h9, hsp,
    stackArgAddr_entry hsp, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide),
    Nat.reduceMul, hw0, hw1, hw2, hw3, fb_sub8]
  have ⟨hK1, hK2⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.kb_toNat hp
  have e1 : verStack = 2144 := rfl
  have e2 : oEM1 = 80 := rfl
  have e3 : VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes = 2136 := rfl
  have hk1 := hp.k1
  have hk2 := hp.k2
  have sM : Region.Sub (VG.Proof.RsaPkcs1Sig.X86_64.Rec.em1R s) (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega)
  have sA : Region.Sub ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, 32⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := by
    have := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (d := 0) (n := 32) (by decide); simpa only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] using this
  have sR : Region.Sub ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, 8⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := Region.sub_prefix (by decide)
  have hfb : VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s = VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s + BitVec.ofNat 64 8 := VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb_eq s
  have dMA : (VG.Proof.RsaPkcs1Sig.X86_64.Rec.em1R s).Disjoint ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, 32⟩ := Offset.disjoint_base _ (by decide) (by omega)
  have dRM : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, 8⟩ : Region).Disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Rec.em1R s) := by
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.em1R]; rw [hfb, VG.Proof.Bignum.X86_64.off, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.base_disjoint _ (by decide) (by omega)
  have dRA : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb s, 8⟩ : Region).Disjoint ⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, 32⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by decide) (by omega)
  have wM : (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by
    rw [toNat_off (by rw [hfb, ← VG.Proof.Bignum.X86_64.off, toNat_off (by omega)]; unfold oEM1; omega), hfb, ← VG.Proof.Bignum.X86_64.off,
      toNat_off (by omega)]; unfold oEM1; omega
  have dKg : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Disjoint ⟨stackArg s 1, (s.gpr .rcx).toNat⟩ := by rw [← hsig]; exact hp.dKg
  have dgs : (⟨stackArg s 1, (s.gpr .rcx).toNat⟩ : Region).Disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s) := by rw [← hsig]; exact hp.dgs
  have wG : (stackArg s 1).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 := by rw [← hsig]; exact hp.wG
  refine ⟨by omega, rfl, rfl, hp.dKn.sub_left sM, hp.dKe.sub_left sM, dKg.sub_left sM, hp.dKs.sub_left sM, dMA,
    hp.dns, hp.des, dgs, (hp.dKs.sub_left sA).symm, dRM, hp.dKn.sub_left sR, hp.dKe.sub_left sR,
    dKg.sub_left sR, hp.dKs.sub_left sR, dRA, wM, hp.wN, hp.wE, wG, hp.wS, ⟨hk1, hk2⟩, trivial, trivial, hp.L1,
    hp.L2, hp.hsl⟩

/-! ## Memory across the call -/

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) ∨ Region.Sub r (VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s) ∨ Region.Sub r (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s)) :
    Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

/-- The slots are apart from `EM₁`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) {d : Nat} (hd : 32 ≤ d) (hd' : d + 8 ≤ oEM1) :
    ∀ r ∈ VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s ++ [below (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8], (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d, 8⟩ : Region).Disjoint r := by
  have hk2 := hp.k2
  intro r hr
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr, VG.Proof.RsaPkcs1Sig.X86_64.Rec.em1R, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega)) (by unfold oEM1 at *; omega) (by unfold oEM1 at *; omega)
  · exact (hp.dKs.sub_left (VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)))
  · exact (ret_disjoint s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)).symm

theorem pub_covers {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hsig : stackArg s 2 = s.gpr .rcx) (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) :
    Covers (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s ++ VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s) (t.rd ++ t.wr) ∧ Covers (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s) t.wr := by
  have hk2 := hp.k2
  have hfr : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  have hscr : VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s ∈ t.wr := by rw [he.wr, hp.hwr]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR]
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr, VG.Proof.RsaPkcs1Sig.X86_64.Rec.em1R, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hfr, oEM1, rfl, by dsimp only; unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega⟩
    · exact ⟨_, hscr, 0, z _, by simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR]; omega⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  have hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [he.rd]; exact hx)
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨s.gpr .r8, (s.gpr .r9).toNat⟩ (by rw [hp.hrd]; simp), 0, z _, by dsimp only; omega⟩
  · exact ⟨_, hrd ⟨stackArg s 1, (stackArg s 2).toNat⟩ (by rw [hp.hrd]; simp), 0, z _,
      by dsimp only; rw [hsig]; omega⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega⟩

/-- The call of `vg_rsa_public_checked`: `EM₁` holds `s^e mod n`, which it
returns, or zeros. -/
theorem pub_call (v : PubImpl) {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hsig : stackArg s 2 = s.gpr .rcx) (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t)
    (hw0 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 = stackArg s 1) (hw1 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = s.gpr .rcx)
    (hw2 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16 = stackArg s 3) (hw3 : VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24 = stackArg s 4)
    (hdi : t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (hsi : t.gpr .rsi = s.gpr .rcx) (hdx : t.gpr .rdx = s.gpr .rdx)
    (hcx : t.gpr .rcx = s.gpr .rcx) (h8 : t.gpr .r8 = s.gpr .r8) (h9 : t.gpr .r9 = s.gpr .r9) :
    WP isa (.call v.name v.code) t fun t' => VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t' ∧
      Spec.Rsa.written t'.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rcx).toNat ((t'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat)) ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧ t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  obtain ⟨hc, hw⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_covers hp hsig he
  refine WP.call_mx (k := pubChk) v.ok v.nosp (by rw [v.depth]; decide)
    (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_pre hp hsig he.rsp hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [v.depth, he.rsp] at hf
  have hE : stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)) 0 = stackArg s 1 :=
    (stackArg_entry he.rsp _ _ (by omega)).trans hw0
  have hfE : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem t.callEntry.mem :=
    VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)
  have hk2 := hp.k2
  have b : ∀ {p : Addr} {len : Nat}, (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Disjoint ⟨p, len⟩ → (VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s).Disjoint ⟨p, len⟩ →
      (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s).Disjoint ⟨p, len⟩ → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len := fun hk ho hs hl =>
    VG.Proof.RsaPkcs1Sig.X86_64.Rec.bytes_of_frame hfE hk ho hs hl
  simp only [pubChk, pubChkPost, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide),
    hdi, hdx, hcx, h8, h9, hE, hm₂, hg₂ .rax (by decide)] at hpost
  rw [b hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), b hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega),
    b (by rw [← hsig]; exact hp.dKg) (by rw [← hsig]; exact hp.dOg) (by rw [← hsig]; exact hp.dgs.symm)
      (by omega)] at hpost
  refine ⟨⟨(hcs .rsp (by decide)).trans he.rsp, hrd.trans he.rd, hwr.trans he.wr,
    VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_call he.mem hf fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hpost, hcs, hmx⟩
  · simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inl (VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega))
    · exact .inr (.inr (sub_refl _))
    · exact .inl (below_sub s)
  · rw [slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Rec.slot_apart hp (by decide) (by decide))]; exact he.sOut
  · rw [slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Rec.slot_apart hp (by decide) (by decide))]; exact he.sOl
  · rw [slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Rec.slot_apart hp (by decide) (by decide))]; exact he.sN
  · rw [slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Rec.slot_apart hp (by decide) (by decide))]; exact he.sK
  · rw [slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Rec.slot_apart hp (by decide) (by decide))]; exact he.sE
  · rw [slot_keep hf (VG.Proof.RsaPkcs1Sig.X86_64.Rec.slot_apart hp (by decide) (by decide))]; exact he.sEl

end VG.Proof.RsaPkcs1Sig.X86_64.Rec

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect`. -/
section

/-!
# `vg_rsa_pkcs1_recover` on x86-64: correctness

After the call (`afterPub_ok`): the encoding of the last `out_len` bytes of
`EM₁` into `EM₂` (`encode_ok`), their comparison (`compare_ok`) and the
release of those bytes to `out`, or zeros, which is BoringSSL's recovery
(`recover_eq_recoverEnc`). With the length check, the frame's push, the call
(`pub_call`) and the pop: `code_correct`.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 ret0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR fb_eq fb_sub8 toNat_off frame_sub below_sub
  ret_disjoint outside_frame stackArgAddr_fb stackArgAddr_eq ea_sp word_wo allocState_gpr arg_ea
  stackArg_entry stackArgAddr_entry callEntry_frame sub_refl slot_keep test0_ok result_ok bytesAt_eq_iff setWidth_byte_eq_zero word_wo0 word_self0 freed wp_alloc arg0_ea)
open Spec.RsaPkcs1Sig

/-! ## Memory in the frame and in `out` -/

/-- `Env` past changes of the registers but `rsp`, and of memory in the
frame from `EM₁` on or in `out`. -/
theorem Env.of {s t u : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, (∃ d n, r = ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d, n⟩ ∧ oEM1 ≤ d ∧ d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) ∨ r = VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s u := by
  have hsl : ∀ {d}, 32 ≤ d → d + 8 ≤ oEM1 → VG.Proof.Bignum.X86_64.word u.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d = VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d := fun hd hd' =>
    slot_keep hf fun r hr => by
      rcases hs r hr with ⟨d', n, rfl, h₁, h₂⟩ | rfl
      · exact Offset.disjoint _ (.inl (by omega)) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
          (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
      · exact (hp.dKo.sub_left (VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)))
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_call he.mem hf fun r hr => ?_,
    (hsl (by decide) (by decide)).trans he.sOut, (hsl (by decide) (by decide)).trans he.sOl,
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl⟩
  rcases hs r hr with ⟨d, n, rfl, -, h₂⟩ | rfl
  · exact .inl (VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s h₂)
  · exact .inr (.inl (sub_refl _))

/-- `Env` past changes of the registers but `rsp`. -/
theorem Env.regs {s t u : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sOut, hm ▸ he.sOl, hm ▸ he.sN,
    hm ▸ he.sK, hm ▸ he.sE, hm ▸ he.sEl⟩

theorem frame_bytes' {s : State} {d n : Nat} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (h : d + n ≤ VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes) :
    ∀ i < n, InRegions (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ :: s.wr) (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d + BitVec.ofNat 64 i) 1 := by
  have := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  intro i hi
  refine ⟨_, List.mem_cons_self .., ?_⟩
  rw [show VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d + BitVec.ofNat 64 i = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (d + i) from off_off _ _ _]
  exact Offset.contains_base _ (by omega) (by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)

/-- `out` is writable. -/
theorem out_wr {s : State} {wr : List Region} (hwr : VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s ∈ wr) :
    ∀ i < (s.gpr .rsi).toNat, InRegions wr (s.gpr .rdi + BitVec.ofNat 64 i) 1 := fun i hi =>
  ⟨_, hwr, Offset.contains_base _ (by omega) (by omega)⟩

/-! ## Zeros to `out` -/

/-- Zeros to the `n` bytes at `rdi`. -/
theorem zeroOut_ok {u : State} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64) (hsi : u.gpr .rsi = BitVec.ofNat 64 n)
    (hw : ∀ i < n, InRegions u.wr (u.gpr .rdi + BitVec.ofNat 64 i) 1) :
    WP isa zeroOut u fun t => VG.Proof.MlKem.X86_64.Keep [.r8, .r10, .rax, .rdi, .rsi, .r9, .r11] u t ∧
      t.mem = VG.WriteBytes.writeBytes u.mem (u.gpr .rdi) (List.replicate n 0) ∧ t.gpr .rax = 0 := by
  unfold zeroOut
  refine WP.seq (WP.mono (WP.keep [.r8, .r10, .rax] (Q := fun t => t.mem = u.mem ∧ t.gpr .r8 = u.gpr .rdi ∧
      t.gpr .r10 = BitVec.ofNat 64 n ∧ t.gpr .rax = 0) (by xrun [hsi]) rfl) fun u₁ ⟨⟨hm₁, h8, h10, hax⟩, k₁⟩ => ?_)
  have hdi : u₁.gpr .rdi = u₁.gpr .r8 := by rw [k₁.gpr (by decide), h8]
  have hb : Buf u₁ n := fun i hi => by rw [k₁.2.2, h8]; exact hw i hi
  have hW : W u₁ [] u₁ := ⟨Keep.refl _ _, by rw [VG.WriteBytes.writeBytes_nil], by rw [hdi]; simp⟩
  refine WP.mono (psLoop_ok hb hn' hn (by simp) hW 0 (by rw [hax]; rfl) h10) fun t ⟨hW', hK'⟩ =>
    ⟨(k₁.trans hW'.1).mono (by simp [VG.Proof.RsaPkcs1Sig.X86_64.clob]), ?_, by rw [hK'.gpr (by decide), hax]⟩
  rw [hW'.2.1, hm₁, h8, List.nil_append]

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- Zeros to `out`, with its address and length from the slots: the result
`none`. -/
theorem zeroSlots_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) :
    WP isa zeroSlots t fun u => VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s u ∧
      Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((u.gpr .rax).setWidth 32) none := by
  have hs := he.scr hp
  have ol := hp.ol
  unfold zeroSlots
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧
      u.gpr .rsi = s.gpr .rsi) (by
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, he.rsp, hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun t₁ ⟨⟨hm₁, hdi, hsi⟩, k₁⟩ => ?_)
  have hwr : VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s ∈ t₁.wr := by rw [k₁.2.2, he.wr, hp.hwr]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR]
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega) (by omega) (by rw [hsi, VG.Proof.RsaPkcs1Sig.X86_64.Rec.ofNat_toNat64])
    (by rw [hdi]; exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.out_wr hwr)) fun u ⟨hK, hm, hax⟩ => ⟨?_, ?_, ?_⟩
  · refine Env.of (he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2) hp (hK.gpr (by decide)) hK.2.1 hK.2.2
      (hm ▸ frame_writeBytes _ _ _) fun r hr => .inr ?_
    rw [List.mem_singleton.mp hr, hdi, List.length_replicate]; rfl
  · rw [hax]; rfl
  · rw [hm, hdi]
    have := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_writeBytes t₁.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega)
    rwa [List.length_replicate] at this

theorem valPtr_eq (p a b : Addr) (h : b.toNat ≤ a.toNat) :
    p + a - b = p + BitVec.ofNat 64 (a.toNat - b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := a.isLt; have := b.isLt; have := p.isLt
  rw [Nat.mod_eq_of_lt (show a.toNat - b.toNat < 2 ^ 64 by omega)]
  omega

/-- The hash value's place in `EM₁`. -/
abbrev valA (s : State) : Addr := VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (oEM1 + ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat))

theorem valPtr_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hsp : t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (hcx : t.gpr .rcx = s.gpr .rcx)
    (h9 : t.gpr .r9 = s.gpr .rsi) :
    WP isa (.block valPtr) t fun u => VG.Proof.MlKem.X86_64.Keep [.rsi] t u ∧ u.mem = t.mem ∧ u.gpr .rsi = VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s := by
  have ol := hp.ol
  have hk1 := hp.k1
  refine WP.mono (WP.keep [.rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rsi = VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s) (by
    xrun [valPtr, VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, hsp, hcx, h9, sx_ofNat (show oEM1 < 2 ^ 31 by decide)]
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Rec.valPtr_eq _ _ _ (by omega)]; exact off_off _ _ _) rfl) fun u ⟨h, k⟩ => ⟨k, h⟩

theorem encArgs_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) :
    WP isa (.block encArgs) t fun u => VG.Proof.MlKem.X86_64.Keep [.r8, .rcx, .rdx, .r9, .rsi] t u ∧ u.mem = t.mem ∧
      u.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rcx ∧
      u.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ u.gpr .r9 = s.gpr .rsi ∧ u.gpr .rsi = VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s := by
  have hs := he.scr hp
  unfold encArgs
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .rcx, .rdx, .r9] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 ∧ u.gpr .rcx = s.gpr .rcx ∧
      u.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ u.gpr .r9 = s.gpr .rsi) (by
    xrun [VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, @arg_ea s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, he.rsp,
      sx_ofNat (show oEM2 < 2 ^ 31 by decide), hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oK) (by decide), hs.ld (d := oOl) (by decide),
      VG.Proof.RsaPkcs1Sig.X86_64.Rec.arg_in hp he.rd (show 0 < 5 by decide), he.arg hp (show 0 < 5 by decide), he.sK, he.sOl]) rfl)
    fun t₁ ⟨⟨hm₁, h8, hcx, hdx, h9⟩, k₁⟩ => ?_
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valPtr_ok hp ((k₁.gpr (by decide)).trans he.rsp) hcx h9) fun u ⟨k, hm, hsi⟩ =>
    ⟨(k₁.trans k).mono (by simp), hm.trans hm₁, by rw [k.gpr (by decide), h8], by rw [k.gpr (by decide), hcx],
      by rw [k.gpr (by decide), hdx], by rw [k.gpr (by decide), h9], hsi⟩

/-- The hash value's place in `EM₁` is in the frame. -/
theorem valA_sub {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) : Region.Sub ⟨VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s, (s.gpr .rsi).toNat⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := by
  have := hp.ol; have := hp.k2; have := hp.k1
  exact VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega)

/-- The value to `out`, and 1 returned. -/
theorem copyOut_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) (hcx : t.gpr .rcx = s.gpr .rcx) :
    WP isa copyOut t fun u => VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s u ∧ (u.gpr .rax).setWidth 32 = 1 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
        Spec.Rsa.bytesAt t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s) (s.gpr .rsi).toNat := by
  have hs := he.scr hp
  have ol := hp.ol
  have hk2 := hp.k2
  have hk1 := hp.k1
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  unfold copyOut
  rw [WP.seq_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .rdi, .r9] (Q := fun u => u.mem = t.mem ∧ u.gpr .r8 = s.gpr .rdi ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .r9 = s.gpr .rsi) (by
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, he.rsp, hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun t₀ ⟨⟨hm₀, h8₀, hdi₀, h9₀⟩, k₀⟩ => ?_
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valPtr_ok hp ((k₀.gpr (by decide)).trans he.rsp) ((k₀.gpr (by decide)).trans hcx) h9₀)
    fun t₁ ⟨k₁, hm₁, hsi₁⟩ => ?_
  have h8 : t₁.gpr .r8 = s.gpr .rdi := by rw [k₁.gpr (by decide), h8₀]
  have hdi : t₁.gpr .rdi = s.gpr .rdi := by rw [k₁.gpr (by decide), hdi₀]
  have h9 : t₁.gpr .r9 = BitVec.ofNat 64 (s.gpr .rsi).toNat := by rw [k₁.gpr (by decide), h9₀, VG.Proof.RsaPkcs1Sig.X86_64.Rec.ofNat_toNat64]
  have hwr : VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s ∈ t₁.wr := by rw [k₁.2.2, k₀.2.2, he.wr, hp.hwr]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR]
  have hfr : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ : Region) ∈ t₁.wr := by rw [k₁.2.2, k₀.2.2, he.wr]; exact List.mem_cons_self ..
  have hb : Buf t₁ (s.gpr .rsi).toNat := fun i hi => by rw [h8]; exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.out_wr hwr i hi
  have hW : W t₁ [] t₁ := ⟨Keep.refl _ _, by rw [VG.WriteBytes.writeBytes_nil], by rw [hdi, h8]; simp⟩
  have hr : ∀ j < (s.gpr .rsi).toNat, InRegions (t₁.rd ++ t₁.wr) (t₁.gpr .rsi + BitVec.ofNat 64 j) 1 :=
    fun j hj => ⟨_, List.mem_append_right _ hfr, by
      rw [hsi₁, show VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s + BitVec.ofNat 64 j = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (oEM1 + ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) + j)
        from off_off _ _ _]
      exact Offset.contains_base _ (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)⟩
  have hd : ∀ j < (s.gpr .rsi).toNat, ∀ i < (s.gpr .rsi).toNat,
      t₁.gpr .rsi + BitVec.ofNat 64 j ≠ t₁.gpr .r8 + BitVec.ofNat 64 i := fun j hj i hi => by
    rw [hsi₁, h8]
    exact ne_of_disjoint ((hp.dKo.sub_left (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA_sub hp))) (by omega) (by omega) hj hi
  refine WP.seq (WP.mono (copyLoop_ok hb (by omega) (by omega) (by simp) hW rfl h9 hr hd) fun t₂ hW₂ => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun u => u.mem = t₂.mem ∧ u.gpr .rax = 1) (by xrun) rfl)
    fun u ⟨⟨hm, hax⟩, hK⟩ => ⟨?_, by rw [hax]; rfl, ?_⟩
  · have hm' : u.mem = VG.WriteBytes.writeBytes t₁.mem (s.gpr .rdi)
        (Spec.Rsa.bytesAt t₁.mem (t₁.gpr .rsi) (s.gpr .rsi).toNat) := by
      rw [hm, hW₂.2.1, h8, List.nil_append]
    have heT : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₁ := (he.regs (k₀.gpr (by decide)) hm₀ k₀.2.1 k₀.2.2).regs (k₁.gpr (by decide)) hm₁
      k₁.2.1 k₁.2.2
    refine Env.of heT hp ((hK.gpr (by decide)).trans (hW₂.1.gpr (by decide))) (hK.2.1.trans hW₂.1.2.1)
      (hK.2.2.trans hW₂.1.2.2) (hm' ▸ frame_writeBytes _ _ _) fun r hr => .inr ?_
    rw [List.mem_singleton.mp hr, VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length]; rfl
  · rw [hm, hW₂.2.1, h8, List.nil_append, hsi₁, hm₁, hm₀]
    have := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_writeBytes t.mem (s.gpr .rdi) (Spec.Rsa.bytesAt t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s) (s.gpr .rsi).toNat)
      (by rw [VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length]; omega)
    rwa [VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length] at this

theorem cmpArgs_ok {s t : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) :
    WP isa (.block VG.Impl.RsaPkcs1Sig.X86_64.Verify.cmpArgs) t fun u => VG.Proof.MlKem.X86_64.Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧
      u.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ u.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 := by
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧
      u.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ u.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) (by
    xrun [VG.Impl.RsaPkcs1Sig.X86_64.Verify.cmpArgs, VG.Impl.RsaPkcs1Sig.X86_64.Verify.lea, List.cons_append, List.nil_append, he.rsp,
      sx_ofNat (show oEM1 < 2 ^ 31 by decide), sx_ofNat (show oEM2 < 2 ^ 31 by decide)]) rfl)
    fun u ⟨h, hK⟩ => ⟨hK, h⟩

theorem test_ok (t : State) :
    WP isa (.block [.alu .test .rdx (.reg .rdx)]) t fun u => SameF t u ∧ u.zf = some (t.gpr .rdx == 0) := by
  xrun
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, by rw [BitVec.and_self]⟩

theorem bytesAt_drop (m : Mem) (p : Addr) (d n : Nat) :
    (Spec.Rsa.bytesAt m p (d + n)).drop d = Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 d) n := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h₁ h₂
  simp only [List.getElem_drop, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- Recovery's result, for a signature of `k` bytes. -/
def recOut (nB eB : List Byte) (h : Hash) (sig : List Byte) : Option (List Byte) :=
  match Spec.Rsa.publicOpChecked nB eB sig with
  | some em =>
    if Spec.RsaPkcs1Sig.encode h (em.drop (nB.length - h.len)) nB.length = some em then
      some (em.drop (nB.length - h.len))
    else none
  | none => none

/-- After the encoding into `EM₂`, whose result is `o`: the comparison with
`EM₁` and the release. -/
theorem tail_ok {s t₂ t₃ : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he₂ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₂) (hK₃ : VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob t₂ t₃) {h : Hash}
    {em : List Byte} (hcx₂ : t₂.gpr .rcx = s.gpr .rcx) (h8₂ : t₂.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2)
    (hem : Spec.Rsa.bytesAt t₂.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rcx).toNat = em)
    (hval : Spec.Rsa.bytesAt t₂.mem (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s) (s.gpr .rsi).toNat = em.drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat))
    {o : Option (List Byte)} (ho : Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .rcx).toNat - h.len))
      (s.gpr .rcx).toNat = o)
    (hpost : EOut t₂ t₃ o) :
    WP isa VG.Impl.RsaPkcs1Sig.X86_64.Recover.tail t₃ fun u => VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s u ∧ Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32)
      (if o = some em then some (em.drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat)) else none) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  set k := (s.gpr .rcx).toNat with hkdef
  have dVE : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, k⟩ :=
    Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
      (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Recover.tail
  refine WP.seq (WP.mono (test0_ok t₃) fun t₄ ⟨hs₄, hz₄⟩ => ?_)
  cases o with
  | none =>
    obtain ⟨hax, hm₃⟩ := hpost
    have he₄ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₄ := he₂.regs (by rw [hs₄.1, hK₃.gpr (by decide)]) (hs₄.2.1.trans hm₃)
      (hs₄.2.2.1.trans hK₃.2.1) (hs₄.2.2.2.trans hK₃.2.2)
    refine WP.ite true (by simp [VG.X86_64.eval, hz₄, hax]) (fun _ => ?_) (by simp)
    simp only [reduceCtorEq, ↓reduceIte]
    exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroSlots_ok hp he₄
  | some em' =>
    obtain ⟨hax, hm₃⟩ := hpost
    have hl' : em'.length = k := VG.Proof.RsaPkcs1Sig.encode_length ho
    have he₃ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₃ := Env.of he₂ hp (hK₃.gpr (by decide)) hK₃.2.1 hK₃.2.2 (hm₃ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM2, k, by rw [List.mem_singleton.mp hr, h8₂, hl'], by decide,
        by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega⟩
    have he₄ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₄ := he₃.regs (by rw [hs₄.1]) hs₄.2.1 hs₄.2.2.1 hs₄.2.2.2
    refine WP.ite false (by simp [VG.X86_64.eval, hz₄, hax]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.cmpArgs_ok he₄) fun t₅ ⟨hK₅, hm₅, hdi₅, hsi₅⟩ => ?_)
    have hcx₅ : t₅.gpr .rcx = s.gpr .rcx := by
      rw [hK₅.gpr (by decide), hs₄.1, hK₃.gpr (by decide), hcx₂]
    have he₅ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₅ := he₄.regs (hK₅.gpr (by decide)) hm₅ hK₅.2.1 hK₅.2.2
    have hr5 : ∀ i < k, InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
        InRegions (t₅.rd ++ t₅.wr) (t₅.gpr .rsi + BitVec.ofNat 64 i) 1 := fun i hi => by
      rw [hdi₅, hsi₅, he₅.wr]
      obtain ⟨r₁, h₁, c₁⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_bytes' hp (d := oEM1) (n := k) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
      obtain ⟨r₂, h₂, c₂⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_bytes' hp (d := oEM2) (n := k) (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
      exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
    refine WP.seq (WP.mono (compare_ok (by rw [hcx₅]) (by omega) hr5) fun t₆ ⟨hK₆, hm₆, hdx₆⟩ => ?_)
    have he₆ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₆ := he₅.regs (hK₆.gpr (by decide)) hm₆ hK₆.2.1 hK₆.2.2
    have hmem : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, em'.length⟩ → n ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t₃.mem p n = Spec.Rsa.bytesAt t₂.mem p n := fun {p n} hd hn => by
      rw [hm₃, h8₂]
      simp only [Spec.Rsa.bytesAt]
      exact List.map_congr_left fun i hi =>
        (frame_writeBytes t₂.mem _ em').bytes (R := ⟨p, n⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
          hn (List.mem_range.mp hi)
    have d12 : (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1, k⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, em'.length⟩ := by
      rw [hl']
      exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
        (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
    have h1 : Spec.Rsa.bytesAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) k = em := by
      rw [hmem d12 (by omega), hem]
    have h2 : Spec.Rsa.bytesAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) k = em' := by
      have := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_writeBytes t₂.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) em' (by omega)
      rw [hl'] at this
      rw [hm₃, h8₂]; exact this
    have hdiff : (t₆.gpr .rdx = 0) ↔ em = em' := by
      rw [hdx₆, hdi₅, hsi₅, setWidth_byte_eq_zero, VG.Proof.Ct.diff_zero, ← bytesAt_eq_iff, hm₅, hs₄.2.1, h1, h2]
    unfold release
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.test_ok t₆) fun t₇ ⟨hs₇, hz₇⟩ => ?_)
    have he₇ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₇ := he₆.regs (by rw [hs₇.1]) hs₇.2.1 hs₇.2.2.1 hs₇.2.2.2
    by_cases hq : em = em'
    · subst hq
      refine WP.ite false (by simp [VG.X86_64.eval, hz₇, hdiff.2 rfl]) (by simp) (fun _ => ?_)
      refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.copyOut_ok hp he₇ (by rw [hs₇.1, hK₆.gpr (by decide), hcx₅])) fun u ⟨heu, hax', hout⟩ =>
        ⟨heu, ?_⟩
      have hv : Spec.Rsa.bytesAt t₇.mem (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s) (s.gpr .rsi).toNat = em.drop (k - (s.gpr .rsi).toNat) := by
        rw [hs₇.2.1, hm₆, hm₅, hs₄.2.1, hmem (by rw [hl']; exact dVE) (by omega), hval]
      simp only [↓reduceIte]
      exact ⟨hax', hout.trans hv⟩
    · have hne : t₆.gpr .rdx ≠ 0 := fun h' => hq (hdiff.1 h')
      rw [show (t₆.gpr .rdx == 0) = false from beq_eq_false_iff_ne.mpr hne] at hz₇
      refine WP.ite true (by simp [VG.X86_64.eval, hz₇]) (fun _ => ?_) (by simp)
      rw [ite_eq_right_iff.mpr (fun h' => absurd (Option.some.inj h').symm hq)]
      exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroSlots_ok hp he₇

theorem afterPub_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) {h : Hash}
    (hid : Hash.ofId ((stackArg s 0).setWidth 32).toNat = some h)
    (hw : Spec.Rsa.written t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat))) :
    WP isa afterPub t fun u => VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s u ∧ Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32)
      (VG.Proof.RsaPkcs1Sig.X86_64.Rec.recOut (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) h
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat)) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  have hol : (s.gpr .rsi).toNat = h.len := by
    obtain ⟨h', hid', hl⟩ := hp.hash; rw [hid] at hid'; cases hid'; exact hl
  set k := (s.gpr .rcx).toNat with hkdef
  set nB := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) k
  set eB := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
  set gB := Spec.Rsa.bytesAt s.mem (stackArg s 1) k
  set x := (stackArg s 0).setWidth 32
  have hnl : nB.length = k := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length _ _ _
  unfold afterPub
  refine WP.seq (WP.mono (test0_ok t) fun t₁ ⟨hs₁, hz₁⟩ => ?_)
  have he₁ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₁ := he.regs (by rw [hs₁.1]) hs₁.2.1 hs₁.2.2.1 hs₁.2.2.2
  have hz : ∀ u, VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s u → VG.Proof.RsaPkcs1Sig.X86_64.Rec.recOut nB eB h gB = none → WP isa zeroSlots u fun v => VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s v ∧
      Spec.Rsa.written v.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((v.gpr .rax).setWidth 32) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.recOut nB eB h gB) :=
    fun u hu hr => by rw [hr]; exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroSlots_ok hp hu
  cases hpo : Spec.Rsa.publicOpChecked nB eB gB with
  | none =>
    rw [hpo] at hw
    obtain ⟨hr, -⟩ := hw
    refine WP.ite true (by simp [VG.X86_64.eval, hz₁, hr]) (fun _ => hz t₁ he₁ (by simp [VG.Proof.RsaPkcs1Sig.X86_64.Rec.recOut, hpo])) (by simp)
  | some em =>
    rw [hpo] at hw
    obtain ⟨hr, hem⟩ := hw
    refine WP.ite false (by simp [VG.X86_64.eval, hz₁, hr]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.encArgs_ok hp he₁) fun t₂ ⟨hK₂, hm₂, h8₂, hcx₂, hdx₂, h9₂, hsi₂⟩ => ?_)
    have he₂ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₂ := he₁.regs (hK₂.gpr (by decide)) hm₂ hK₂.2.1 hK₂.2.2
    have sE2 : Region.Sub ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, k⟩ (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s) := VG.Proof.RsaPkcs1Sig.X86_64.Ver.frame_sub s (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega)
    have dVE : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, k⟩ :=
      Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
        (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
    have hfr : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ : Region) ∈ t₂.wr := by rw [he₂.wr]; exact List.mem_cons_self ..
    have hpre : VG.Proof.RsaPkcs1Sig.X86_64.EPre t₂ x k := {
      rdx := by rw [hdx₂]; apply BitVec.eq_of_toNat_eq; simp [x]
      hk := by rw [hcx₂]
      kle := hk2
      buf := fun i hi => by
        rw [h8₂, he₂.wr]; exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_bytes' hp (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
      rd := fun j hj => by
        rw [hsi₂]
        rw [h9₂] at hj
        exact ⟨_, List.mem_append_right _ hfr, by
          rw [show VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s + BitVec.ofNat 64 j = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (oEM1 + ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) + j)
            from off_off _ _ _]
          exact Offset.contains_base _ (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)⟩
      sep := fun j hj i hi => by
        rw [hsi₂, h8₂]
        rw [h9₂] at hj
        exact ne_of_disjoint dVE (by omega) (by omega) hj hi }
    have hH : Spec.Rsa.bytesAt t₂.mem (t₂.gpr .rsi) (t₂.gpr .r9).toNat = em.drop (nB.length - h.len) := by
      rw [hsi₂, h9₂, hm₂, hs₁.2.1, hnl, ← hol, ← hem]
      have := VG.Proof.RsaPkcs1Sig.X86_64.Rec.bytesAt_drop t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (k - (s.gpr .rsi).toNat) (s.gpr .rsi).toNat
      rw [show k - (s.gpr .rsi).toNat + (s.gpr .rsi).toNat = k by omega] at this
      rw [this]
      exact congrArg (Spec.Rsa.bytesAt t.mem · _) (off_off _ _ _).symm
    have hE : ∀ H, encodeId x H k = Spec.RsaPkcs1Sig.encode h H k := fun H => by simp only [encodeId, hid]
    refine WP.seq (WP.mono (encode_ok hpre) fun t₃ ⟨hK₃, hpost⟩ => ?_)
    rw [hH, hE, hnl] at hpost
    have hem₂ : Spec.Rsa.bytesAt t₂.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) k = em := by rw [hm₂, hs₁.2.1, hem]
    have hval : Spec.Rsa.bytesAt t₂.mem (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s) (s.gpr .rsi).toNat = em.drop (k - (s.gpr .rsi).toNat) := by
      have := hH
      rw [hsi₂, h9₂, hnl, ← hol] at this
      exact this
    refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.tail_ok (h := h) (o := Spec.RsaPkcs1Sig.encode h (em.drop (k - h.len)) k) hp he₂ hK₃ hcx₂ h8₂
      hem₂ hval rfl hpost) fun u ⟨heu, hwu⟩ => ⟨heu, ?_⟩
    simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.recOut, hpo, hnl]
    simp only [hol] at hwu ⊢
    exact hwu

/-! ## The arguments and the frame -/

/-- The frame's push and the arguments of the call. -/
theorem pubArgs_ok {s A : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (hA : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) A)
    (hAm : A.mem = s.mem) :
    WP isa (.block pubArgs) A fun t => VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 = stackArg s 1 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = s.gpr .rcx ∧
      VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16 = stackArg s 3 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24 = stackArg s 4 ∧
      t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9 ∧
      (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  rw [VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubArgs_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.slotStores_ok hp hA hAm) fun t₁ ⟨k₁, ho₁, hO, hOl, hN, hK, hE, hEl⟩ => ?_
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.callArgs_ok hp k₁ ho₁) fun t ⟨k, hm, hdi, hsi⟩ => ?_
  have k' := k₁.trans k
  have g : ∀ r, r ≠ .rsp → r ∉ [Reg.rax] ++ [Reg.rax, .rdi, .rsi, .r10, .r11] → t.gpr r = s.gpr r :=
    fun r h h' => by rw [k'.gpr h']; simp [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, h]
  have hw : ∀ d, 32 ≤ d → d + 8 ≤ VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes → VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d = VG.Proof.Bignum.X86_64.word t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) d := fun d hd hd' => by
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hd'
    rw [hm, VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo _ _ _ (d := 24) (.inl (by omega)) (by decide) (by omega),
      VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo _ _ _ (d := 16) (.inl (by omega)) (by decide) (by omega),
      VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo _ _ _ (d := 8) (.inl (by omega)) (by decide) (by omega), word_wo0 _ _ _ (by omega) (by omega)]
  refine ⟨⟨(k'.gpr (by decide)).trans rfl, k'.2.1, k'.2.2, VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_of_outside ?_,
      (hw _ (by decide) (by decide)).trans hO, (hw _ (by decide) (by decide)).trans hOl,
      (hw _ (by decide) (by decide)).trans hN, (hw _ (by decide) (by decide)).trans hK,
      (hw _ (by decide) (by decide)).trans hE, (hw _ (by decide) (by decide)).trans hEl⟩, ?_, ?_, ?_, ?_,
    hdi, hsi, g _ (by decide) (by decide), g _ (by decide) (by decide), g _ (by decide) (by decide),
    g _ (by decide) (by decide), fun r hr hr' => g r hr' (by
      simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)⟩
  · rw [hm]
    intro x hx
    have hx' : VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes ≤ VG.Proof.Bignum.X86_64.ofs (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) x := by unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hx ⊢; omega
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at hx hx'
    rw [VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (d := 24) (by omega) x (by omega), VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (d := 16) (by omega) x (by omega),
      VG.Proof.Bignum.X86_64.writeW_outside _ _ _ (d := 8) (by omega) x (by omega)]
    have := VG.Proof.Bignum.X86_64.writeW_outside t₁.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (stackArg s 1) (d := 0) (by omega) x (by omega)
    simp only [VG.Proof.Bignum.X86_64.off, BitVec.add_zero] at this
    rw [this]; exact ho₁ x hx
  · rw [hm]; simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo]; exact word_self0 _ _ _
  · rw [hm]; simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm]; simp (disch := decide) only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.word_wo, VG.Proof.Bignum.X86_64.word_writeW_self]
  · rw [hm]; exact VG.Proof.Bignum.X86_64.word_writeW_self _ _ _ _

theorem lenCheck_ok {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) :
    WP isa (.block lenCheck) s fun t => VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧
      t.zf = some (stackArg s 2 == s.gpr .rcx) := by
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rcx)) (by
    xrun [lenCheck, arg0_ea, VG.Proof.RsaPkcs1Sig.X86_64.Rec.arg_in hp rfl (show 2 < 5 by decide), sub_beq64]
    rfl) rfl) fun t ⟨h, hK⟩ => ⟨hK, h⟩

theorem recover_eq_recOut {nB eB sig : List Byte} (h : Hash) (hs : sig.length = nB.length) :
    recover nB eB h sig = VG.Proof.RsaPkcs1Sig.X86_64.Rec.recOut nB eB h sig := by
  rw [VG.Proof.RsaPkcs1Sig.recover_eq_recoverEnc]
  unfold VG.Proof.RsaPkcs1Sig.recoverEnc VG.Proof.RsaPkcs1Sig.X86_64.Rec.recOut
  rw [ite_eq_left hs]
  cases Spec.Rsa.publicOpChecked nB eB sig <;> rfl

theorem recover_len {nB eB sig : List Byte} (h : Hash) (hs : sig.length ≠ nB.length) :
    recover nB eB h sig = none := by
  unfold recover; rw [ite_eq_right_iff.mpr (fun h' => absurd h' hs)]

/-- The return address is outside everything the function writes. -/
theorem ret_frame {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) {m : Mem} (h : Frame [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s, VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s] s.mem m) :
    m.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hsp2 := hp.sp2
  refine h.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := Offset.disjoint_below (s.gpr .rsp) (n := verStack) (d := 0) (k := 8)
      (by unfold verStack; omega)
    simpa only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR, VG.Proof.RsaPkcs1Sig.X86_64.Ver.kb, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · exact hp.dRo
  · exact hp.dRs

theorem code_correct (v : PubImpl) (s : State) (h : recContract.pre s) :
    ∃ t s', Exec isa (VG.Impl.RsaPkcs1Sig.X86_64.Recover.code v.name v.code) s t s' ∧ abiPreserved s s' ∧ recContract.post s s' := by
  have hp := VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of h
  have hk2 := hp.k2
  have ol := hp.ol
  obtain ⟨hh, hid, hol⟩ := hp.hash
  suffices hw : WP isa (VG.Impl.RsaPkcs1Sig.X86_64.Recover.code v.name v.code) s fun s' => abiPreserved s s' ∧ recContract.post s s' by
    obtain ⟨t, s', he, hq⟩ := hw
    exact ⟨t, s', he, hq⟩
  have hpost : ∀ (u : State) (o : Option (List Byte)), Spec.Rsa.written u.mem (s.gpr .rdi) (s.gpr .rsi).toNat
      ((u.gpr .rax).setWidth 32) o →
      (o = recover (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) hh
        (Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat)) → recContract.post s u := by
    intro u o hw ho h' hid'
    rw [hid] at hid'; cases hid'
    rw [← ho]; exact hw
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Recover.code
  refine WP.seq (WP.mono_mx (by decide) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.lenCheck_ok hp) fun t₀ ⟨k₀, hm₀, hz₀⟩ hmx₀ => ?_)
  have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
  by_cases hsig : stackArg s 2 = s.gpr .rcx
  · refine WP.ite false (by simp [VG.X86_64.eval, hz₀, hsig]) (by simp) (fun _ => ?_)
    have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
    have hA : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes t₀) :=
      ⟨fun r hr => by
        simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.allocState_gpr, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb, hsp₀]
        split
        · rfl
        · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
    have hfb : VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb t₀ = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s := by simp only [VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb, hsp₀]
    refine wp_alloc (s := t₀) (by rw [hsp₀]; have := hp.sp1; unfold verStack at this; unfold VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) ?_
    unfold VG.Impl.RsaPkcs1Sig.X86_64.Recover.body
    refine WP.seq (WP.mono_mx (by decide) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubArgs_ok hp hA hm₀)
      fun t₁ ⟨he₁, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hcs₁⟩ hmx₁ => ?_)
    refine WP.seq (WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_call v hp hsig he₁ hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9)
      fun t₂ ⟨he₂, hw, hcs₂, hmx₂⟩ => ?_)
    refine WP.mono_mx (by decide +kernel) (WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
      (VG.Proof.RsaPkcs1Sig.X86_64.Rec.afterPub_ok hp he₂ hid hw) (by decide +kernel)) fun t₃ ⟨⟨he₃, hwu⟩, k₃⟩ hmx₃ => ?_
    refine ⟨he₃.rsp.trans hfb.symm, by rw [he₃.wr]; simp only [allocState, hsp₀, k₀.2.2],
      ⟨fun r hr => ?_, VG.Proof.RsaPkcs1Sig.X86_64.Rec.ret_frame hp he₃.mem, ?_⟩, hpost _ _ hwu ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        show t₃.gpr .rsp + BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes = s.gpr .rsp
        rw [he₃.rsp, BitVec.sub_add_cancel]
      · show (if r = .rsp then _ else t₃.gpr r) = s.gpr r
        simp only [hr', ↓reduceIte]
        have hr'' : r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
          simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
        rw [k₃.gpr hr'', hcs₂ r hr, hcs₁ r hr hr']
    · show t₃.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10
      rw [hmx₃, hmx₂, hmx₁]; exact congrArg _ hmx₀
    · rw [hsig, VG.Proof.RsaPkcs1Sig.X86_64.Rec.recover_eq_recOut _ (by simp only [VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length])]
  · refine WP.ite true (by simp [VG.X86_64.eval, hz₀, hsig]) (fun _ => ?_) (by simp)
    have hwr : VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s ∈ t₀.wr := by rw [k₀.2.2, hp.hwr]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR]
    refine WP.mono_mx (by decide) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega) (by omega)
      (by rw [g₀ _ (by decide), VG.Proof.RsaPkcs1Sig.X86_64.Rec.ofNat_toNat64]) (by rw [g₀ _ (by decide)]; exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.out_wr hwr))
      fun u ⟨hK, hm, hax⟩ hmx => ⟨⟨fun r hr => ?_, ?_, by rw [hmx, hmx₀]⟩, hpost u none ⟨by rw [hax]; rfl, ?_⟩ ?_⟩
    · rw [hK.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        k₀.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
    · rw [hm, g₀ _ (by decide)]
      refine ((frame_writeBytes t₀.mem _ _).readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)).trans (by rw [hm₀])
      rw [List.mem_singleton.mp hr, List.length_replicate]; exact hp.dRo
    · rw [hm, g₀ _ (by decide)]
      have := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_writeBytes t₀.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega)
      rwa [List.length_replicate] at this
    · rw [VG.Proof.RsaPkcs1Sig.X86_64.Rec.recover_len _ (by simp only [VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_length]; intro h'; exact hsig (BitVec.eq_of_toNat_eq h'))]

/-! ## Facts for constant time -/

/-- After an encoding `em'` into `EM₂`: `Env`, `EM₁` kept, `EM₂` the encoding,
and what lies apart from `EM₂` kept. -/
theorem encDone {s t₂ t₃ : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he₂ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₂) (hK₃ : VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob t₂ t₃)
    (h8₂ : t₂.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) {em' : List Byte} (hl' : em'.length = (s.gpr .rcx).toNat)
    (hpost : EOut t₂ t₃ (some em')) :
    VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₃ ∧ t₃.gpr .rax = 1 ∧ Spec.Rsa.bytesAt t₃.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) (s.gpr .rcx).toNat = em' ∧
      ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, (s.gpr .rcx).toNat⟩ → n ≤ 2 ^ 64 →
        Spec.Rsa.bytesAt t₃.mem p n = Spec.Rsa.bytesAt t₂.mem p n := by
  have hk2 := hp.k2
  have hk1 := hp.k1
  obtain ⟨hax, hm₃⟩ := hpost
  refine ⟨Env.of he₂ hp (hK₃.gpr (by decide)) hK₃.2.1 hK₃.2.2 (hm₃ ▸ frame_writeBytes _ _ _)
      fun r hr => .inl ⟨oEM2, (s.gpr .rcx).toNat, by rw [List.mem_singleton.mp hr, h8₂, hl'], by decide,
        by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega⟩, hax, ?_, fun {p n} hd hn => ?_⟩
  · have := VG.Proof.RsaPkcs1Sig.X86_64.bytesAt_writeBytes t₂.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) em' (by omega)
    rw [hl'] at this
    rw [hm₃, h8₂]; exact this
  · rw [hm₃, h8₂]
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi =>
      (frame_writeBytes t₂.mem _ em').bytes (R := ⟨p, n⟩) (fun r hr => by
        rw [List.mem_singleton.mp hr, hl']; exact hd) hn (List.mem_range.mp hi)

theorem EM12_disjoint {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) :
    (⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, (s.gpr .rcx).toNat⟩ := by
  have hk2 := hp.k2; have := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
    (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)

theorem valA_disjoint {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) :
    (⟨VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2, (s.gpr .rcx).toNat⟩ := by
  have hk2 := hp.k2; have hk1 := hp.k1; have ol := hp.ol; have := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  exact Offset.disjoint _ (.inl (by unfold oEM1 oEM2; omega)) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)
    (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)

/-- The head of `copyOut`. -/
theorem copyHead_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) (hcx : t.gpr .rcx = s.gpr .rcx) :
    WP isa (.block (([.mov .r8 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut)), .mov .rdi (.reg .r8), .mov .r9 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOl))] : List Instr) ++ valPtr)) t
      fun u => VG.Proof.MlKem.X86_64.Keep [.r8, .rdi, .r9, .rsi] t u ∧ u.mem = t.mem ∧ u.gpr .r8 = s.gpr .rdi ∧
        u.gpr .rdi = s.gpr .rdi ∧ u.gpr .r9 = s.gpr .rsi ∧ u.gpr .rsi = VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s := by
  have hs := he.scr hp
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r8, .rdi, .r9] (Q := fun u => u.mem = t.mem ∧ u.gpr .r8 = s.gpr .rdi ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .r9 = s.gpr .rsi) (by
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, he.rsp, hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun t₀ ⟨⟨hm₀, h8₀, hdi₀, h9₀⟩, k₀⟩ => ?_
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valPtr_ok hp ((k₀.gpr (by decide)).trans he.rsp) ((k₀.gpr (by decide)).trans hcx) h9₀)
    fun u ⟨k, hm, hsi⟩ => ⟨(k₀.trans k).mono (by simp), hm.trans hm₀, by rw [k.gpr (by decide), h8₀],
      by rw [k.gpr (by decide), hdi₀], by rw [k.gpr (by decide), h9₀], hsi⟩

/-- The head of `zeroSlots`. -/
theorem zeroHead_ok {s t : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) :
    WP isa (.block [.mov .rdi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut)), .mov .rsi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOl))]) t
      fun u => VG.Proof.MlKem.X86_64.Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧
      u.gpr .rsi = s.gpr .rsi) (by
    xrun [VG.Proof.RsaPkcs1Sig.X86_64.Ver.ea_sp, he.rsp, hs.ld (d := VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun u ⟨h, k⟩ => ⟨k, h⟩

/-- What `encode` needs, from `encArgs`. -/
theorem encPre {s t₂ : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (he₂ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t₂) (h8₂ : t₂.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2)
    (hcx₂ : t₂.gpr .rcx = s.gpr .rcx) (hdx₂ : t₂.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64)
    (h9₂ : t₂.gpr .r9 = s.gpr .rsi) (hsi₂ : t₂.gpr .rsi = VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s) :
    VG.Proof.RsaPkcs1Sig.X86_64.EPre t₂ ((stackArg s 0).setWidth 32) (s.gpr .rcx).toNat := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have ol := hp.ol
  have hF := VG.Proof.RsaPkcs1Sig.X86_64.Rec.fb_toNat hp
  have hfr : (⟨VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s, VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes⟩ : Region) ∈ t₂.wr := by rw [he₂.wr]; exact List.mem_cons_self ..
  exact {
    rdx := by rw [hdx₂]; apply BitVec.eq_of_toNat_eq; simp
    hk := by rw [hcx₂]
    kle := hk2
    buf := fun i hi => by
      rw [h8₂, he₂.wr]; exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_bytes' hp (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
    rd := fun j hj => by
      rw [hsi₂]
      rw [h9₂] at hj
      exact ⟨_, List.mem_append_right _ hfr, by
        rw [show VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s + BitVec.ofNat 64 j = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) (oEM1 + ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) + j)
          from off_off _ _ _]
        exact Offset.contains_base _ (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes at *; omega)⟩
    sep := fun j hj i hi => by
      rw [hsi₂, h8₂]
      rw [h9₂] at hj
      exact ne_of_disjoint (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA_disjoint hp) (by omega) (by omega) hj hi }

/-- The hash value's place in `EM₁` holds its last `out_len` bytes. -/
theorem valBytes {s : State} (hp : VG.Proof.RsaPkcs1Sig.X86_64.Rec.PreR s) (m : Mem) :
    Spec.Rsa.bytesAt m (VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s) (s.gpr .rsi).toNat =
      (Spec.Rsa.bytesAt m (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rcx).toNat).drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) := by
  have hk1 := hp.k1
  have ol := hp.ol
  have := VG.Proof.RsaPkcs1Sig.X86_64.Rec.bytesAt_drop m (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat) (s.gpr .rsi).toNat
  rw [show (s.gpr .rcx).toNat - (s.gpr .rsi).toNat + (s.gpr .rsi).toNat = (s.gpr .rcx).toNat by omega] at this
  rw [this]
  exact congrArg (Spec.Rsa.bytesAt m · _) (off_off _ _ _).symm

end VG.Proof.RsaPkcs1Sig.X86_64.Rec

end

/- Proofs formerly in `VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCT`. -/
section

/-!
# `vg_rsa_pkcs1_recover` on x86-64: constant time

As for `vg_rsa_pkcs1_verify` (`VerifyCT.lean`): each point of the code is
described, in each run, by what correctness says of it from that run's entry
state, which agrees with an anchor on the public data (`At`). The blocks
between the call and the branches are checked by the taint analysis from the
registers this fixes, each branch's condition is fixed by it too, and the
call is constant time for its callee's contract. The zeros and the copy to
`out` take its address and length from the frame's slots, which the taint
analysis does not know public: their loads are a piece of their own, and the
loops after them are checked from the registers correctness fixes.
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Rec

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Recover
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (frameBytes oEM1 oEM2 sp arg arg0 lea test0 ret0 cmpArgs)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64
open VG.Proof.RsaPkcs1Sig.X86_64.Ver (fb kb stkR scrR frame_sub test0_ok relCT_alloc entry_regs regs_eq
  written_r stackArg_entry callEntry_frame below_sub)

/-! ## The taint checks -/

theorem lenCheck_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block lenCheck) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem zeroOut_taint {Φ : State → State → Prop} (h : Pins Φ [.rdi, .rsi]) :
    RelCT isa (Two Φ) zeroOut fun _ _ => True := two_taint [.rdi, .rsi] h (by taint_decide)

theorem pubArgs_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block pubArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem zeroHead_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block [.mov .rdi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut)), .mov .rsi (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOl))]) fun _ _ => True :=
  two_taint [.rsp] h (by taint_decide)

theorem encArgs_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block encArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem encode_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp, .r8, .rcx, .rdx, .rsi, .r9]) :
    RelCT isa (Two Φ) encode fun _ _ => True :=
  two_taint [.rsp, .r8, .rcx, .rdx, .rsi, .r9] h (by taint_decide)

theorem cmpArgs_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block VG.Impl.RsaPkcs1Sig.X86_64.Verify.cmpArgs) fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem compare_taint {Φ : State → State → Prop} (h : Pins Φ [.rdi, .rsi, .rcx]) :
    RelCT isa (Two Φ) compare fun _ _ => True := two_taint [.rdi, .rsi, .rcx] h (by taint_decide)

theorem copyHead_taint {Φ : State → State → Prop} (h : Pins Φ [.rsp]) :
    RelCT isa (Two Φ) (.block (([.mov .r8 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp VG.Impl.RsaPkcs1Sig.X86_64.Recover.oOut)), .mov .rdi (.reg .r8), .mov .r9 (.mem (VG.Impl.RsaPkcs1Sig.X86_64.Verify.sp oOl))] : List Instr) ++ valPtr))
      fun _ _ => True := two_taint [.rsp] h (by taint_decide)

theorem copyRest_taint {Φ : State → State → Prop} (h : Pins Φ [.rsi, .rdi, .r9]) :
    RelCT isa (Two Φ) (.seq copyLoop (.block [.mov32 .rax (.imm 1)])) fun _ _ => True :=
  two_taint [.rsi, .rdi, .r9] h (by taint_decide)

/-! ## Entry states and the anchor -/

def Sib (a s : State) : Prop := recContract.pre s ∧ recContract.pub a s

theorem pub_refl (s : State) : recContract.pub s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Sib.gpr {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) :
    s.gpr r = a.gpr r := (h.2.1 r hr).symm

theorem Sib.h {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) : (stackArg s 0).setWidth 32 = (stackArg a 0).setWidth 32 :=
  h.2.2.1.symm

theorem Sib.arg {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) {i : Nat} (hi : 1 ≤ i) (hi' : i < 5) : stackArg s i = stackArg a i := by
  have := h.2.2.2.1
  simp only [List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, -⟩ := this
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm

theorem Sib.n {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat :=
  h.2.2.2.2.1.symm

theorem Sib.e {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) :
    Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat = Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat :=
  h.2.2.2.2.2.1.symm

theorem Sib.g {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) :
    Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat =
      Spec.Rsa.bytesAt a.mem (stackArg a 1) (stackArg a 2).toNat :=
  h.2.2.2.2.2.2.symm

theorem Sib.fb {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) : VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb a := by
  show s.gpr .rsp - _ = a.gpr .rsp - _
  rw [h.gpr (r := .rsp) (by decide)]

theorem Sib.valA {a s : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA a := by
  show VG.Proof.Bignum.X86_64.off (Ver.fb s) _ = VG.Proof.Bignum.X86_64.off (Ver.fb a) _
  rw [h.fb, h.gpr (r := .rcx) (by decide), h.gpr (r := .rsi) (by decide)]

def At (J : State → State → Prop) (a t : State) : Prop := ∃ s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s ∧ J s t

theorem pin {J : State → State → Prop} {r : Reg} (f : State → BitVec 64) (hf : ∀ s t, J s t → t.gpr r = f s)
    (hs : ∀ a s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s → f s = f a) {a t₁ t₂ : State} (h₁ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J a t₁) (h₂ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J a t₂) :
    t₁.gpr r = t₂.gpr r := by
  obtain ⟨s₁, S₁, j₁⟩ := h₁
  obtain ⟨s₂, S₂, j₂⟩ := h₂
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pinEval {J : State → State → Prop} {c : Cond} (f : State → Option Bool)
    (hf : ∀ s t, J s t → isa.eval c t = f s) (hs : ∀ a s, VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s → f s = f a) :
    ∀ a t₁ t₂, VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J a t₁ → VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J a t₂ → isa.eval c t₁ = isa.eval c t₂ := by
  rintro a t₁ t₂ ⟨s₁, S₁, j₁⟩ ⟨s₂, S₂, j₂⟩
  rw [hf _ _ j₁, hf _ _ j₂, hs _ _ S₁, hs _ _ S₂]

theorem pins_rsp {J : State → State → Prop} (hJ : ∀ s t, J s t → t.gpr .rsp = VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) : Pins (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J) [.rsp] :=
  fun _ _ _ h₁ h₂ r hr => by
    rw [List.mem_singleton.mp hr]
    exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb hJ (fun _ _ h => h.fb) h₁ h₂

/-- `At` with a condition on the state. -/
theorem at_and {J : State → State → Prop} {P : State → Prop} {a t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J a t ∧ P t) :
    VG.Proof.RsaPkcs1Sig.X86_64.Rec.At (fun s t => J s t ∧ P t) a t :=
  let ⟨⟨s, S, j⟩, p⟩ := h; ⟨s, S, j, p⟩

theorem two_and {J : State → State → Prop} {P : State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At fun s t => J s t ∧ P t)) c Q) :
    RelCT isa (Two fun a t => VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J a t ∧ P t) c Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, VG.Proof.RsaPkcs1Sig.X86_64.Rec.at_and h₁, VG.Proof.RsaPkcs1Sig.X86_64.Rec.at_and h₂⟩) fun _ _ h => h

/-! ## The points of the code -/

def J0 (s t : State) : Prop := t = s

def JL (s t : State) : Prop := VG.Proof.MlKem.X86_64.Keep [.rax] s t ∧ t.mem = s.mem ∧ t.zf = some (stackArg s 2 == s.gpr .rcx)

def JA (s t : State) : Prop :=
  ∃ t₀, VG.Proof.RsaPkcs1Sig.X86_64.Rec.JL s t₀ ∧ stackArg s 2 = s.gpr .rcx ∧ t = allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes t₀

def J1 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 0 = stackArg s 1 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 8 = s.gpr .rcx ∧
    VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 16 = stackArg s 3 ∧ VG.Proof.Bignum.X86_64.word t.mem (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) 24 = stackArg s 4 ∧
    t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
    t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9 ∧ stackArg s 2 = s.gpr .rcx

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 1) (s.gpr .rcx).toNat)

theorem pubOut_sib {a s : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) (hs : stackArg s 2 = s.gpr .rcx) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut a := by
  have ha : stackArg a 2 = a.gpr .rcx := by rw [← S.arg (by decide) (by decide), hs, S.gpr (by decide)]
  have hg := S.g
  rw [hs, ha] at hg
  unfold VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut; rw [S.n, S.e, hg]

def J2 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t ∧ Spec.Rsa.written t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rcx).toNat ((t.gpr .rax).setWidth 32) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut s) ∧
    stackArg s 2 = s.gpr .rcx

def J3 (s t : State) : Prop := VG.Proof.RsaPkcs1Sig.X86_64.Rec.J2 s t ∧ t.zf = some !(VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut s).isSome

/-- `EM`, if RSAVP1 succeeds. -/
def emOut (s : State) : List Byte := (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut s).getD []

def J4 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t ∧ t.gpr .r8 = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rcx ∧
    t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .r9 = s.gpr .rsi ∧ t.gpr .rsi = VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rcx).toNat = VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s ∧ stackArg s 2 = s.gpr .rcx

/-- The encoding of the last `out_len` bytes of `EM`. -/
def encRes (s : State) : Option (List Byte) :=
  encodeId ((stackArg s 0).setWidth 32) ((VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s).drop ((s.gpr .rcx).toNat - (s.gpr .rsi).toNat))
    (s.gpr .rcx).toNat

def J5 (s t : State) : Prop := ∃ t₄, VG.Proof.RsaPkcs1Sig.X86_64.Rec.J4 s t₄ ∧ VG.Proof.MlKem.X86_64.Keep VG.Proof.RsaPkcs1Sig.X86_64.clob t₄ t ∧ EOut t₄ t (VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes s)

def J6 (s t : State) : Prop := ∃ t₅, VG.Proof.RsaPkcs1Sig.X86_64.Rec.J5 s t₅ ∧ SameF t₅ t ∧ t.zf = some !(VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes s).isSome

/-- The encoding, if it succeeds. -/
def encVal (s : State) : List Byte := (VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes s).getD []

def J7 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t ∧ t.gpr .rdi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1 ∧ t.gpr .rsi = VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2 ∧ t.gpr .rcx = s.gpr .rcx ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rcx).toNat = VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s ∧
    Spec.Rsa.bytesAt t.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) (s.gpr .rcx).toNat = VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal s ∧ stackArg s 2 = s.gpr .rcx

def J8 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t ∧ t.gpr .rcx = s.gpr .rcx ∧ (t.gpr .rdx = 0 ↔ VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal s) ∧ stackArg s 2 = s.gpr .rcx

def J9 (s t : State) : Prop :=
  VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t ∧ t.gpr .rcx = s.gpr .rcx ∧ t.zf = some (decide (VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal s)) ∧ stackArg s 2 = s.gpr .rcx

theorem emOut_sib {a s : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) (hs : stackArg s 2 = s.gpr .rcx) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut a := by
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut, VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut_sib S hs]

theorem encRes_sib {a s : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) (hs : stackArg s 2 = s.gpr .rcx) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes a := by
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes, VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut_sib S hs, S.h, S.gpr (r := .rcx) (by decide), S.gpr (r := .rsi) (by decide)]

theorem encVal_sib {a s : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) (hs : stackArg s 2 = s.gpr .rcx) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal a := by
  simp only [VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal, VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes_sib S hs]

theorem encodeId_length {x : BitVec 32} {H : List Byte} {k : Nat} {em' : List Byte}
    (h : encodeId x H k = some em') : em'.length = k := by
  unfold encodeId at h
  split at h
  · exact VG.Proof.RsaPkcs1Sig.encode_length h
  · cases h

/-! ## The call -/

theorem entryBytes {s t : State} (he : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) (rd wr : List Region) {p : Addr} {len : Nat}
    (hk : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.stkR s).Disjoint ⟨p, len⟩) (ho : (VG.Proof.RsaPkcs1Sig.X86_64.Rec.outR s).Disjoint ⟨p, len⟩) (hs : (VG.Proof.RsaPkcs1Sig.X86_64.Ver.scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt (t.callEntry.withRegions rd wr).mem p len = Spec.Rsa.bytesAt s.mem p len := by
  rw [State.withRegions_mem]
  exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.bytes_of_frame (VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_call he.mem (callEntry_frame he.rsp) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact .inl (below_sub s)) hk ho hs hl

theorem pub_view {a s t : State} (S : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Sib a s) (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.J1 s t) :
    [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp].map (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)).gpr =
      [VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb a) oEM1, a.gpr .rcx, a.gpr .rdx, a.gpr .rcx, a.gpr .r8, a.gpr .r9, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb a - 8] ∧
    stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)) 0 = stackArg a 1 ∧
    stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)) 1 = a.gpr .rcx ∧
    stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)) 2 = stackArg a 3 ∧
    stackArg (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)) 3 = stackArg a 4 ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)).mem
      ((t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)).gpr .rdx)
      ((t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)).gpr .rcx).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat ∧
    Spec.Rsa.bytesAt (t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)).mem
      ((t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)).gpr .r8)
      ((t.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s)).gpr .r9).toNat =
      Spec.Rsa.bytesAt a.mem (a.gpr .r8) (a.gpr .r9).toNat := by
  obtain ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, -⟩ := h
  have hp := VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [entry_regs, hdi, hsi, hdx, hcx, h8, h9, he.rsp, S.fb, S.gpr (r := .rcx) (by decide),
      S.gpr (r := .rdx) (by decide), S.gpr (r := .r8) (by decide), S.gpr (r := .r9) (by decide)]
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide) (by decide)]; exact hw0
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.gpr (r := .rcx) (by decide)]; exact hw1
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide) (by decide)]; exact hw2
  · rw [stackArg_entry he.rsp _ _ (by decide), ← S.arg (by decide) (by decide)]; exact hw3
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), hdx, hcx]
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Rec.entryBytes he _ _ hp.dKn hp.dOn hp.dns.symm (by have := hp.wN; omega), S.n]
  · simp only [State.withRegions_gpr, State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h8, h9]
    rw [VG.Proof.RsaPkcs1Sig.X86_64.Rec.entryBytes he _ _ hp.dKe hp.dOe hp.des.symm (by have := hp.wE; omega), S.e]

theorem call_ct (v : PubImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J1)) (.call v.name v.code) fun _ _ => True := by
  refine RelCT.callEx (k := pubChk) v.ok v.ct fun t₁ t₂ ⟨a, ⟨s₁, S₁, j₁⟩, ⟨s₂, S₂, j₂⟩⟩ => ?_
  obtain ⟨r₁, a0₁, a1₁, a2₁, a3₁, n₁, e₁⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_view S₁ j₁
  obtain ⟨r₂, a0₂, a1₂, a2₂, a3₂, n₂, e₂⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_view S₂ j₂
  obtain ⟨c₁, w₁⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_covers (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S₁.1) j₁.2.2.2.2.2.2.2.2.2.2.2 j₁.1
  obtain ⟨c₂, w₂⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_covers (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S₂.1) j₂.2.2.2.2.2.2.2.2.2.2.2 j₂.1
  obtain ⟨he₁, hw0₁, hw1₁, hw2₁, hw3₁, hdi₁, hsi₁, hdx₁, hcx₁, h8₁, h9₁, hg₁⟩ := j₁
  obtain ⟨he₂, hw0₂, hw1₂, hw2₂, hw3₂, hdi₂, hsi₂, hdx₂, hcx₂, h8₂, h9₂, hg₂⟩ := j₂
  have p₁ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_pre (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S₁.1) hg₁ he₁.rsp hw0₁ hw1₁ hw2₁ hw3₁ hdi₁ hsi₁ hdx₁ hcx₁ h8₁ h9₁
  have p₂ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_pre (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S₂.1) hg₂ he₂.rsp hw0₂ hw1₂ hw2₂ hw3₂ hdi₂ hsi₂ hdx₂ hcx₂ h8₂ h9₂
  have hpub : pubChk.pub (t₁.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s₁) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s₁))
      (t₂.callEntry.withRegions (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s₂) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s₂)) :=
    ⟨regs_eq (r₁.trans r₂.symm), a0₁.trans a0₂.symm, a1₁.trans a1₂.symm, a2₁.trans a2₂.symm,
      a3₁.trans a3₂.symm, n₁.trans n₂.symm, e₁.trans e₂.symm⟩
  exact ⟨VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s₁, VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s₁, VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubRd s₂, VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubWr s₂, p₁, p₂, hpub, c₁, w₁, c₂, w₂,
    by rw [he₁.rsp, he₂.rsp, S₁.fb, S₂.fb]⟩

/-! ## Zeros and the copy to `out` -/

def JZ (s t : State) : Prop := t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi

def JC (s t : State) : Prop := t.gpr .rsi = VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA s ∧ t.gpr .rdi = s.gpr .rdi ∧ t.gpr .r9 = s.gpr .rsi

theorem zeroSlots_ct {J : State → State → Prop} (hJ : ∀ s t, J s t → VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t) :
    RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J)) zeroSlots fun _ _ => True := by
  unfold zeroSlots
  refine RelCT.seq (two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pins_rsp fun s t h => (hJ s t h).rsp) (by taint_decide)
    (Ψ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.JZ) fun _ t ⟨s, S, h⟩ => WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroHead_ok (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1) (hJ s t h))
      fun _ ⟨_, _, hdi, hsi⟩ => ⟨s, S, hdi, hsi⟩) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroOut_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rdi) (fun _ _ h => h.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂

theorem copyOut_ct {J : State → State → Prop} (hJ : ∀ s t, J s t → VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t ∧ t.gpr .rcx = s.gpr .rcx) :
    RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At J)) copyOut fun _ _ => True := by
  unfold copyOut
  refine RelCT.seq (two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pins_rsp fun s t h => (hJ s t h).1.rsp) (by taint_decide)
    (Ψ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.JC) fun _ t ⟨s, S, h⟩ => WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.copyHead_ok (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1) (hJ s t h).1 (hJ s t h).2)
      fun _ ⟨_, _, _, hdi, h9, hsi⟩ => ⟨s, S, hsi, hdi, h9⟩) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.copyRest_taint fun _ _ _ h₁ h₂ r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA (fun _ _ h => h.1) (fun _ _ S => S.valA) h₁ h₂
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rdi) (fun _ _ h => h.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
  · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2) (fun _ _ S => S.gpr (by decide)) h₁ h₂

/-! ## The pieces -/

theorem lenCheck_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J0)) (.block lenCheck) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.JL)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rsp) (fun s t h => by rw [show t = s from h]) (fun _ _ S => S.gpr (by decide))
        h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ht⟩ => by
      rw [show t = s from ht]
      exact WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.lenCheck_ok (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1)) fun _ h => ⟨s, S, h⟩

theorem zeroOut0_ct : RelCT isa (Two fun a t => VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.JL a t ∧ isa.eval .ne t = some true) zeroOut fun _ _ => True :=
  VG.Proof.RsaPkcs1Sig.X86_64.Rec.two_and (VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroOut_taint fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rdi) (fun _ _ h => h.1.1.gpr (by decide)) (fun _ _ S => S.gpr (by decide)) h₁ h₂
    · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rsi) (fun _ _ h => h.1.1.gpr (by decide)) (fun _ _ S => S.gpr (by decide)) h₁ h₂)

theorem pubArgs_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.JA)) (.block pubArgs) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J1)) :=
  two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pins_rsp fun s t ⟨t₀, ⟨k₀, _, _⟩, _, ht⟩ => by
      subst ht; show t₀.gpr .rsp - _ = _; rw [k₀.gpr (by decide)]) (by taint_decide)
    fun _ t ⟨s, S, t₀, ⟨k₀, hm₀, _⟩, hg, ht⟩ => by
      subst ht
      have g₀ : ∀ r, r ≠ .rax → t₀.gpr r = s.gpr r := fun r h => k₀.gpr (by simpa using h)
      have hsp₀ : t₀.gpr .rsp = s.gpr .rsp := g₀ _ (by decide)
      have hA : VG.Proof.MlKem.X86_64.Keep [.rax] (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes s) (allocState VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes t₀) :=
        ⟨fun r hr => by
          simp only [Ver.allocState_gpr, VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb, hsp₀]
          split
          · rfl
          · exact g₀ r (by simpa using hr), k₀.2.1, by simp only [allocState, hsp₀, k₀.2.2]⟩
      exact WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubArgs_ok (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1) hA hm₀)
        fun _ ⟨he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, _⟩ =>
          ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩

theorem call_two (v : PubImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J1)) (.call v.name v.code) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J2)) :=
  two_post (VG.Proof.RsaPkcs1Sig.X86_64.Rec.call_ct v) fun _ _ ⟨s, S, he, hw0, hw1, hw2, hw3, hdi, hsi, hdx, hcx, h8, h9, hg⟩ =>
    WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_call v (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1) hg he hw0 hw1 hw2 hw3 hdi hsi hdx hcx h8 h9) fun _ h =>
      ⟨s, S, h.1, h.2.1, hg⟩

theorem test0_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J2)) (.block test0) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J3)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, he, hw, hg⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ =>
      ⟨s, S, ⟨he.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2, by rw [hs.2.1, hs.1]; exact hw, hg⟩, by
        rw [hz, written_r hw]; cases (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut s).isSome <;> rfl⟩

theorem encArgs_two : RelCT isa (Two fun a t => VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J3 a t ∧ isa.eval .e t = some false) (.block encArgs)
    (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J4)) :=
  VG.Proof.RsaPkcs1Sig.X86_64.Rec.two_and (two_piece [.rsp] (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pins_rsp fun _ _ h => h.1.1.1.rsp) (by taint_decide)
    fun _ t ⟨s, S, ⟨⟨he, hw, hg⟩, hz⟩, he'⟩ => by
      have hsome : (VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut s).isSome = true := by
        simp only [VG.X86_64.eval, hz, Option.some.injEq, Bool.not_eq_false'] at he'; simpa using he'
      obtain ⟨em, hem⟩ := Option.isSome_iff_exists.mp hsome
      rw [hem] at hw
      refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.encArgs_ok (VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1) he) fun u ⟨hK, hm, h8, hcx, hdx, h9, hsi⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, h8, hcx, hdx, h9, hsi, ?_, hg⟩
      rw [hm, hw.2]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut, hem])

theorem encode_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J4)) encode (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J5)) :=
  two_piece [.rsp, .r8, .rcx, .rdx, .rsi, .r9] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb (fun _ _ h => h.1.rsp) (fun _ _ S => S.fb) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => ((stackArg s 0).setWidth 32).setWidth 64) (fun _ _ h => h.2.2.2.1)
          (fun _ _ S => by rw [S.h]) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin VG.Proof.RsaPkcs1Sig.X86_64.Rec.valA (fun _ _ h => h.2.2.2.2.2.1) (fun _ _ S => S.valA) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rsi) (fun _ _ h => h.2.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, j⟩ => by
      obtain ⟨he, h8, hcx, hdx, h9, hsi, hem, hg⟩ := j
      have hp := VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1
      refine WP.mono (encode_ok (VG.Proof.RsaPkcs1Sig.X86_64.Rec.encPre hp he h8 hcx hdx h9 hsi)) fun u ⟨hK, hout⟩ =>
        ⟨s, S, t, ⟨he, h8, hcx, hdx, h9, hsi, hem, hg⟩, hK, ?_⟩
      rw [hsi, h9, VG.Proof.RsaPkcs1Sig.X86_64.Rec.valBytes hp, hem] at hout
      exact hout

def J5n (s t : State) : Prop := VG.Proof.RsaPkcs1Sig.X86_64.Rec.J6 s t ∧ isa.eval .e t = some true
def J5s (s t : State) : Prop := VG.Proof.RsaPkcs1Sig.X86_64.Rec.J6 s t ∧ isa.eval .e t = some false

theorem test0_two5 : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J5)) (.block test0) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J6)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, j⟩ => WP.mono (test0_ok t) fun u ⟨hs, hz⟩ => ⟨s, S, t, j, hs, by
      obtain ⟨t₄, -, -, hout⟩ := j
      rw [hz]
      cases h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes s with
      | none => rw [h] at hout; rw [hout.1]; rfl
      | some em' => rw [h] at hout; rw [hout.1]; rfl⟩

theorem J5n_env {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.J5n s t) : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t := by
  obtain ⟨⟨t₅, ⟨t₄, j₄, hK, hout⟩, hs, hz⟩, he⟩ := h
  have hn : VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes s = none := by
    simp only [VG.X86_64.eval, hz, Option.some.injEq, Bool.not_eq_true'] at he
    simpa using he
  rw [hn] at hout
  exact (j₄.1.regs (by rw [hK.gpr (by decide)]) hout.2 hK.2.1 hK.2.2).regs (by rw [hs.1]) hs.2.1 hs.2.2.1
    hs.2.2.2

theorem cmpArgs_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J5s)) (.block VG.Impl.RsaPkcs1Sig.X86_64.Verify.cmpArgs) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J7)) :=
  two_piece [.rsp] (fun _ _ _ h₁ h₂ r hr => by
      rw [List.mem_singleton.mp hr]
      exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb (fun s t h => by
        obtain ⟨⟨t₅, ⟨t₄, j₄, hK, _⟩, hs, _⟩, _⟩ := h
        rw [hs.1, hK.gpr (by decide)]; exact j₄.1.rsp) (fun _ _ S => S.fb) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, ⟨t₅, ⟨t₄, j₄, hK, hout⟩, hs, hz⟩, he⟩ => by
      have hp := VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1
      have hsome : (VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes s).isSome = true := by
        simp only [VG.X86_64.eval, hz, Option.some.injEq, Bool.not_eq_false'] at he; simpa using he
      obtain ⟨em', hem'⟩ := Option.isSome_iff_exists.mp hsome
      rw [hem'] at hout
      obtain ⟨he₄, h8₄, hcx₄, -, -, -, hem₄, hg₄⟩ := j₄
      obtain ⟨he₅, -, h2, hkeep⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.encDone hp he₄ hK h8₄ (VG.Proof.RsaPkcs1Sig.X86_64.Rec.encodeId_length hem') hout
      have h1 : Spec.Rsa.bytesAt t₅.mem (VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (s.gpr .rcx).toNat = VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s := by
        rw [hkeep (VG.Proof.RsaPkcs1Sig.X86_64.Rec.EM12_disjoint hp) (by have := hp.k2; omega), hem₄]
      have he₆ : VG.Proof.RsaPkcs1Sig.X86_64.Rec.Env s t := he₅.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2
      refine WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.cmpArgs_ok he₆) fun u ⟨hK', hm, hdi, hsi⟩ =>
        ⟨s, S, he₆.regs (hK'.gpr (by decide)) hm hK'.2.1 hK'.2.2, hdi, hsi, ?_, ?_, ?_, hg₄⟩
      · rw [hK'.gpr (by decide), hs.1, hK.gpr (by decide), hcx₄]
      · rw [hm, hs.2.1, h1]
      · rw [hm, hs.2.1, h2]; simp [VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal, hem']

theorem compare_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J7)) compare (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J8)) :=
  two_piece [.rdi, .rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM1) (fun _ _ h => h.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => VG.Proof.Bignum.X86_64.off (VG.Proof.RsaPkcs1Sig.X86_64.Ver.fb s) oEM2) (fun _ _ h => h.2.2.1) (fun _ _ S => by rw [S.fb]) h₁ h₂
      · exact VG.Proof.RsaPkcs1Sig.X86_64.Rec.pin (fun s => s.gpr .rcx) (fun _ _ h => h.2.2.2.1) (fun _ _ S => S.gpr (by decide)) h₁ h₂)
    (by taint_decide)
    fun _ t ⟨s, S, he, hdi, hsi, hcx, h1, h2, hg⟩ => by
      have hp := VG.Proof.RsaPkcs1Sig.X86_64.Rec.preR_of S.1
      have hk1 := hp.k1
      have hk2 := hp.k2
      have hr : ∀ i < (s.gpr .rcx).toNat, InRegions (t.rd ++ t.wr) (t.gpr .rdi + BitVec.ofNat 64 i) 1 ∧
          InRegions (t.rd ++ t.wr) (t.gpr .rsi + BitVec.ofNat 64 i) 1 := fun i hi => by
        rw [hdi, hsi, he.wr]
        obtain ⟨r₁, h₁, c₁⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_bytes' hp (d := oEM1) (n := (s.gpr .rcx).toNat)
          (by unfold oEM1 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
        obtain ⟨r₂, h₂, c₂⟩ := VG.Proof.RsaPkcs1Sig.X86_64.Rec.frame_bytes' hp (d := oEM2) (n := (s.gpr .rcx).toNat)
          (by unfold oEM2 VG.Impl.RsaPkcs1Sig.X86_64.Verify.frameBytes; omega) i hi
        exact ⟨⟨r₁, List.mem_append_right _ h₁, c₁⟩, ⟨r₂, List.mem_append_right _ h₂, c₂⟩⟩
      refine WP.mono (compare_ok (by rw [hcx]) (by omega) hr) fun u ⟨hK, hm, hdx⟩ =>
        ⟨s, S, he.regs (hK.gpr (by decide)) hm hK.2.1 hK.2.2, by rw [hK.gpr (by decide), hcx], ?_, hg⟩
      rw [hdx, hdi, hsi, Ver.setWidth_byte_eq_zero, VG.Proof.Ct.diff_zero, ← Ver.bytesAt_eq_iff, h1, h2]

theorem test_two : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J8)) (.block [.alu .test .rdx (.reg .rdx)]) (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J9)) :=
  two_piece [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)
    fun _ t ⟨s, S, he, hcx, hd, hg⟩ => WP.mono (VG.Proof.RsaPkcs1Sig.X86_64.Rec.test_ok t) fun u ⟨hs, hz⟩ => by
      refine ⟨s, S, he.regs (by rw [hs.1]) hs.2.1 hs.2.2.1 hs.2.2.2, by rw [hs.1]; exact hcx, ?_, hg⟩
      rw [hz]
      by_cases h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal s
      · rw [decide_eq_true h, show t.gpr .rdx = 0 from hd.2 h]; rfl
      · rw [decide_eq_false h, show (t.gpr .rdx == 0) = false from beq_eq_false_iff_ne.mpr (fun h' => h (hd.1 h'))]

/-! ## The composition -/

theorem release_ct : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J8)) release fun _ _ => True := by
  unfold release
  refine RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.test_two (two_ite ?_ (VG.Proof.RsaPkcs1Sig.X86_64.Rec.two_and (VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroSlots_ct fun _ _ h => h.1.1))
    (VG.Proof.RsaPkcs1Sig.X86_64.Rec.two_and (VG.Proof.RsaPkcs1Sig.X86_64.Rec.copyOut_ct fun _ _ h => ⟨h.1.1, h.1.2.1⟩)))
  refine VG.Proof.RsaPkcs1Sig.X86_64.Rec.pinEval (fun s => if stackArg s 2 = s.gpr .rcx then some (!decide (VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut s = VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal s)) else none)
    (fun s t h => by simp only [VG.X86_64.eval, h.2.2.1, h.2.2.2, Option.map_some, ↓reduceIte]) ?_
  intro a s S
  have he : (stackArg s 2 = s.gpr .rcx) = (stackArg a 2 = a.gpr .rcx) := by
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  by_cases hs : stackArg s 2 = s.gpr .rcx
  · have ha : stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte, VG.Proof.RsaPkcs1Sig.X86_64.Rec.emOut_sib S hs, VG.Proof.RsaPkcs1Sig.X86_64.Rec.encVal_sib S hs]
  · have ha : ¬ stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte]

theorem J6_sig {s t : State} (h : VG.Proof.RsaPkcs1Sig.X86_64.Rec.J6 s t) : stackArg s 2 = s.gpr .rcx := by
  obtain ⟨_, ⟨_, j₄, _, _⟩, _, _⟩ := h
  exact j₄.2.2.2.2.2.2.2

theorem tail_ct : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J5)) VG.Impl.RsaPkcs1Sig.X86_64.Recover.tail fun _ _ => True := by
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Recover.tail
  refine RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.test0_two5 (two_ite ?_ (VG.Proof.RsaPkcs1Sig.X86_64.Rec.two_and (VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroSlots_ct fun _ _ h => VG.Proof.RsaPkcs1Sig.X86_64.Rec.J5n_env h))
    (VG.Proof.RsaPkcs1Sig.X86_64.Rec.two_and (RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.cmpArgs_two (RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.compare_two VG.Proof.RsaPkcs1Sig.X86_64.Rec.release_ct))))
  refine VG.Proof.RsaPkcs1Sig.X86_64.Rec.pinEval (fun s => if stackArg s 2 = s.gpr .rcx then some (!(VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes s).isSome) else none)
    (fun s t h => by
      have hg := VG.Proof.RsaPkcs1Sig.X86_64.Rec.J6_sig h
      obtain ⟨_, _, _, hz⟩ := h
      simp only [VG.X86_64.eval, hz, hg, ↓reduceIte]) ?_
  intro a s S
  have he : (stackArg s 2 = s.gpr .rcx) = (stackArg a 2 = a.gpr .rcx) := by
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  by_cases hs : stackArg s 2 = s.gpr .rcx
  · have ha : stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte, VG.Proof.RsaPkcs1Sig.X86_64.Rec.encRes_sib S hs]
  · have ha : ¬ stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte]

theorem afterPub_ct : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J2)) afterPub fun _ _ => True := by
  unfold afterPub
  refine RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.test0_two (two_ite ?_ (VG.Proof.RsaPkcs1Sig.X86_64.Rec.two_and (VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroSlots_ct fun _ _ h => h.1.1.1))
    (RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.encArgs_two (RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.encode_two VG.Proof.RsaPkcs1Sig.X86_64.Rec.tail_ct)))
  refine VG.Proof.RsaPkcs1Sig.X86_64.Rec.pinEval (fun s => if stackArg s 2 = s.gpr .rcx then some (!(VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut s).isSome) else none)
    (fun s t h => by simp only [VG.X86_64.eval, h.2, h.1.2.2, ↓reduceIte]) ?_
  intro a s S
  have he : (stackArg s 2 = s.gpr .rcx) = (stackArg a 2 = a.gpr .rcx) := by
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  by_cases hs : stackArg s 2 = s.gpr .rcx
  · have ha : stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte, VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubOut_sib S hs]
  · have ha : ¬ stackArg a 2 = a.gpr .rcx := he ▸ hs
    simp only [hs, ha, ↓reduceIte]

theorem body_ct (v : PubImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.JA)) (VG.Impl.RsaPkcs1Sig.X86_64.Recover.body v.name v.code) fun _ _ => True :=
  RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.pubArgs_two (RelCT.seq (VG.Proof.RsaPkcs1Sig.X86_64.Rec.call_two v) VG.Proof.RsaPkcs1Sig.X86_64.Rec.afterPub_ct)

theorem code_ct (v : PubImpl) : RelCT isa (Two (VG.Proof.RsaPkcs1Sig.X86_64.Rec.At VG.Proof.RsaPkcs1Sig.X86_64.Rec.J0)) (VG.Impl.RsaPkcs1Sig.X86_64.Recover.code v.name v.code) fun _ _ => True := by
  unfold VG.Impl.RsaPkcs1Sig.X86_64.Recover.code
  refine RelCT.seq VG.Proof.RsaPkcs1Sig.X86_64.Rec.lenCheck_two (two_ite ?_ VG.Proof.RsaPkcs1Sig.X86_64.Rec.zeroOut0_ct (relCT_alloc ((VG.Proof.RsaPkcs1Sig.X86_64.Rec.body_ct v).mono ?_ fun _ _ h => h)))
  · refine VG.Proof.RsaPkcs1Sig.X86_64.Rec.pinEval (fun s => some (!(stackArg s 2 == s.gpr .rcx))) (fun s t h => by
      simp only [VG.X86_64.eval, h.2.2, Option.map_some]) ?_
    intro a s S
    rw [S.arg (by decide) (by decide), S.gpr (by decide)]
  · rintro _ _ ⟨t₁, t₂, ⟨a, ⟨⟨s₁, S₁, j₁⟩, e₁⟩, ⟨⟨s₂, S₂, j₂⟩, e₂⟩⟩, rfl, rfl⟩
    have hg : ∀ {s t}, VG.Proof.RsaPkcs1Sig.X86_64.Rec.JL s t → isa.eval .ne t = some false → stackArg s 2 = s.gpr .rcx := fun j e => by
      simp only [VG.X86_64.eval, j.2.2, Option.map_some, Option.some.injEq, Bool.not_eq_false', beq_iff_eq] at e
      exact e
    exact ⟨a, ⟨s₁, S₁, t₁, j₁, hg j₁ e₁, rfl⟩, ⟨s₂, S₂, t₂, j₂, hg j₂ e₂, rfl⟩⟩

theorem code_constantTime (v : PubImpl) :
    ConstantTime isa recContract.pre recContract.pub (VG.Impl.RsaPkcs1Sig.X86_64.Recover.code v.name v.code) :=
  RelCT.constantTime ((VG.Proof.RsaPkcs1Sig.X86_64.Rec.code_ct v).mono
    (fun s₁ s₂ ⟨h₁, h₂, hpub⟩ => ⟨s₁, ⟨s₁, ⟨h₁, VG.Proof.RsaPkcs1Sig.X86_64.Rec.pub_refl s₁⟩, rfl⟩, ⟨s₂, ⟨h₂, hpub⟩, rfl⟩⟩) fun _ _ h => h)

/-! ## `Verified` -/

/-- `vg_rsa_pkcs1_recover`, calling the implementation `v` of
`vg_rsa_public_checked`, meets the shared contract. -/
theorem code_verified (v : PubImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86_64.Recover.code v.name v.code) (Spec.RsaPkcs1Sig.recoverContract abi verStack) :=
  have hct : ConstantTime isa recContract.pre recContract.pub (VG.Impl.RsaPkcs1Sig.X86_64.Recover.code v.name v.code) := VG.Proof.RsaPkcs1Sig.X86_64.Rec.code_constantTime v
  Verified.of_correct (k := recContract) (VG.Proof.RsaPkcs1Sig.X86_64.Rec.code_correct v) hct recover_implies

/-- It writes `rsp` only in its frame's push and pop. -/
theorem code_spSafe (v : PubImpl) : (VG.Impl.RsaPkcs1Sig.X86_64.Recover.code v.name v.code).all (fun i => !isa.writesSp i) = true := by
  simp only [VG.Impl.RsaPkcs1Sig.X86_64.Recover.code, VG.Impl.RsaPkcs1Sig.X86_64.Recover.body, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

end VG.Proof.RsaPkcs1Sig.X86_64.Rec

end
