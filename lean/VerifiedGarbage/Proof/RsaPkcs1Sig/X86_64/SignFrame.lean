import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCtx
import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Sign
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, below which the
call of `vg_rsa_private_checked` uses 3264 bytes; its slots, and the
function's stack arguments, at `S + frameBytes + 8 + 8 j` (`stackArgAddr`).
-/

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

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

theorem preS_of {s : State} (h : sigContract.pre s) : PreS s := by
  simp only [sigContract] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOn dOe dOd dOp dOq dOdp dOdq dOqi dOs dOa dns des dds dps dqs ddps ddqs dqis dsa
    dRo hdrop1 hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 dRs hdrop9 dKo dKn dKe dKd dKp dKq dKdp dKdq
    dKqi dKs dKa wO wN wE wD wP wQ wDp wDq wQi wS hsplit10 hsi L1 L2 pl1 pl2 ql1 ql2 hdpl hqil hdql
  clear hdrop1 hdrop2 hdrop3 hdrop4 hdrop5 hdrop6 hdrop7 hdrop8 hdrop9
  obtain ⟨k1, k2⟩ := hsplit10
  have hsl := h
  clear h
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOd, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dns, des, dds, dps, dqs, ddps,
    ddqs, dqis, dsa, dRo, dRs, dKo, dKn, dKe, dKd, dKp, dKq, dKdp, dKdq, dKqi, dKs, dKa, wO, wN, wE, wD, wP, wQ, wDp,
    wDq, wQi, wS, k1, k2, hsi, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl⟩

/-! ## The frame -/

abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 sigStack

def stkR (s : State) : Region := ⟨kb s, sigStack⟩
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩

/-- The frame's base, from the stack's: `frameBytes` above it, below which
the call uses `sigStack - frameBytes` bytes. -/
theorem fb_eq (s : State) : fb s = off (kb s) (sigStack - frameBytes) :=
  Offset.sub_ofNat_eq _ (by decide)

theorem kb_toNat {s : State} (hp : PreS s) : (kb s).toNat + sigStack + 128 ≤ 2 ^ 64 ∧
    (kb s).toNat + sigStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold sigStack at *; omega

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem fb_toNat {s : State} (hp : PreS s) : (fb s).toNat + frameBytes + 8 + 120 ≤ 2 ^ 64 ∧
    (fb s).toNat = (kb s).toNat + (sigStack - frameBytes) := by
  have ⟨h1, h2⟩ := kb_toNat hp
  rw [fb_eq, toNat_off (by unfold sigStack frameBytes at *; omega)]
  unfold frameBytes sigStack at *; omega

theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold sigStack frameBytes; omega)

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
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  sOut : word t.mem (fb s) oOut = s.gpr .rdi
  sOl : word t.mem (fb s) oOl = s.gpr .rsi
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9

theorem Env.scr {s t : State} (h : Env s t) (hp : PreS s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega)

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

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, outR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

theorem arg_outside {s : State} (hp : PreS s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 15) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

theorem Env.arg {s t : State} (h : Env s t) (hp : PreS s) {j : Nat} (hj : j < 15) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 120⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

theorem arg_in {s t : State} (hp : PreS s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 15) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 120⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem arg_ea {s t : State} (h : t.gpr .rsp = fb s) (j : Nat) : t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : word (m.writeW (off base d) v) base d' = word m base d' :=
  (writeW_outside m base v (by omega)).word (by omega) (by omega)

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState frameBytes s).gpr r = if r = .rsp then fb s else s.gpr r := rfl

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
