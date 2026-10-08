import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCtx
import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Verify
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_pkcs1_verify` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, the blocks that
store to its slots and read the function's stack arguments, at
`S + frameBytes + 8 + 8 j` (`stackArgAddr`), and the arguments of the call
of `vg_rsa_public_checked` (`pubArgs_ok`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Ver

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Verify
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

/-! ## Addresses in the frame -/

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega

/-! ## The precondition, by name -/

/-- `verContract.pre`, by name. -/
structure PreV (s : State) : Prop where
  sp1 : verStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 48 ≤ 2 ^ 64
  hrd : Covers [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩,
    ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArgAddr s 0, 40⟩] s.rd
  hwr : s.wr = [⟨stackArg s 3, (stackArg s 4).toNat * 8⟩]
  dns : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  des : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dds : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dgs : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dsa : (⟨stackArg s 3, (stackArg s 4).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKd : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dKg : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 verStack, verStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 40⟩
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

theorem preV_of {s : State} (h : verContract.pre s) : PreV s := by
  simp only [verContract] at h
  obtain ⟨sp1, sp2, hrd, hwr, dns, des, dds, dgs, dsa, -, -, -, -, dRs, -, dKn, dKe, dKd, dKg, dKs, dKa,
    wN, wE, wD, wG, wS, ⟨k1, k2⟩, L1, L2, hsl⟩ := h
  exact ⟨sp1, sp2, by rw [hrd]; exact Covers.refl _, hwr, dns, des, dds, dgs, dsa, dRs, dKn, dKe, dKd, dKg, dKs, dKa, wN, wE, wD, wG, wS,
    k1, k2, L1, L2, hsl⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 verStack

/-- The stack the function uses and the working space: all the function and
its call may write. -/
def stkR (s : State) : Region := ⟨kb s, verStack⟩
def scrR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

theorem fb_eq (s : State) : fb s = off (kb s) 8 :=
  Offset.sub_ofNat_eq _ (by decide)

theorem fb_sub8 (s : State) : fb s - 8 = kb s := by
  rw [fb_eq]; exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : PreV s) : (kb s).toNat + verStack + 48 ≤ 2 ^ 64 ∧
    (kb s).toNat + verStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold verStack at *; omega

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem fb_toNat {s : State} (hp : PreV s) : (fb s).toNat + frameBytes + 8 + 40 ≤ 2 ^ 64 ∧
    (fb s).toNat = (kb s).toNat + 8 := by
  have ⟨h1, h2⟩ := kb_toNat hp
  rw [fb_eq, toNat_off (by unfold verStack at *; omega)]
  unfold frameBytes verStack at *; omega

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold verStack; omega)

/-- The return address of a call from the frame. -/
theorem below_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := by
  rw [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl]
  exact Region.sub_prefix (by decide)

/-- A region of the frame at `d`, apart from the return address of a call. -/
theorem ret_disjoint (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (below (fb s) 8).Disjoint ⟨off (fb s) d, n⟩ := by
  rw [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl, fb_eq, off_off]
  exact Offset.base_disjoint _ (by omega) (by unfold frameBytes at h; omega)

/-- A byte outside the stack the function uses is outside the frame. -/
theorem outside_frame (s : State) {x : Addr} (hx : ¬ (stkR s).Contains x 1) :
    frameBytes ≤ ofs (fb s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨fb s, frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hlt ⊢; omega
  have := frame_sub s (d := 0) (n := frameBytes) (by decide)
  simp only [off, BitVec.add_zero] at this
  exact this x hc

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, scrR s] s.mem t.mem
  sN : word t.mem (fb s) oN = s.gpr .rdi
  sK : word t.mem (fb s) oK = s.gpr .rsi
  sE : word t.mem (fb s) oE = s.gpr .rdx
  sEl : word t.mem (fb s) oEl = s.gpr .rcx
  sH : word t.mem (fb s) oH = s.gpr .r8
  sD : word t.mem (fb s) oD = s.gpr .r9

theorem Env.scr {s t : State} (h : Env s t) (hp : PreV s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega)

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hk.symm
  · exact hs.symm

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

/-- Memory changed only in the frame turns into `Env`'s. -/
theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : PreV s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 5) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

/-- A stack argument, in memory changed only where the function may write. -/
theorem Env.arg {s t : State} (h : Env s t) (hp : PreV s) {j : Nat} (hj : j < 5) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 40⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dsa.symm

/-- A word past a store to another word of the frame. -/
theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : word (m.writeW (off base d) v) base d' = word m base d' :=
  (writeW_outside m base v (by omega)).word (by omega) (by omega)

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState frameBytes s).gpr r = if r = .rsp then fb s else s.gpr r := rfl

/-- The stack arguments are readable. -/
theorem arg_in {s t : State} (hp : PreV s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 5) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  by
    rw [hrd]
    exact hp.hrd.left _ _ ⟨⟨stackArgAddr s 0, 40⟩, by simp,
      by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem arg_ea {s t : State} (h : t.gpr .rsp = fb s) (j : Nat) :
    t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

theorem ofNat_lt32 {d : Nat} (h : d < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 d) = BitVec.ofNat 64 d :=
  sx_ofNat h

end VG.Proof.RsaPkcs1Sig.X86_64.Ver
