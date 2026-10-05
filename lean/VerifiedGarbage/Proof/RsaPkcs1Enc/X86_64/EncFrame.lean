import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncContract
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Bytes

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the frame

The precondition by name (`EPre`), the frame of `frameBytes` bytes at
`fb s = rsp - frameBytes` and what lies around it, and the first block
(`setup_ok`): the slots, the call's stack arguments and the first two bytes
of `EM`.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-! ## The precondition, by name -/

/-- `encK.pre`, by name. -/
structure EPre (s : State) : Prop where
  sp1 : encStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArgAddr s 0, 48⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOm : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 48⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dms : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dps : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dsa : (⟨stackArg s 4, (stackArg s 5).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 48⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKm : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint
    ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint
    ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint
    ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 48⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wM : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wP : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wS : (stackArg s 4).toNat + (stackArg s 5).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  hml : (stackArg s 1).toNat + 11 ≤ (s.gpr .rcx).toNat
  hpl : (stackArg s 3).toNat = (s.gpr .rcx).toNat - (stackArg s 1).toNat - 3
  hsl : 16 * (s.gpr .rcx).toNat ≤ (stackArg s 5).toNat

theorem ePre_of {s : State} (h : encK.pre s) : EPre s := by
  simp only [encK] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOm, dOp, dOs, dOa, dns, des, dms, dps, dsa, dRo, -, -, -, -, dRs, -,
    dKo, dKn, dKe, dKm, dKp, dKs, dKa, wO, wN, wE, wM, wP, wS, ⟨k1, k2⟩, hsi, L1, L2, hml, hpl, hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOm, dOp, dOs, dOa, dns, des, dms, dps, dsa, dRo, dRs, dKo, dKn, dKe, dKm,
    dKp, dKs, dKa, wO, wN, wE, wM, wP, wS, k1, k2, hsi, L1, L2, hml, hpl, hsl⟩

/-- The length of `PS`. -/
theorem EPre.psLen {s : State} (hp : EPre s) :
    (stackArg s 3).toNat + (stackArg s 1).toNat + 3 = (s.gpr .rcx).toNat := by
  have := hp.hpl; have := hp.hml; omega

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, the caller's `out` and the working space:
all the function and its call may write. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, encStack⟩
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩

theorem fb_eq (s : State) : fb s = off (s.gpr .rsp - BitVec.ofNat 64 encStack) 8 :=
  Offset.sub_ofNat_eq _ (by decide)

theorem fb_toNat {s : State} (hp : EPre s) : (fb s).toNat + frameBytes + 8 + 48 ≤ 2 ^ 64 ∧
    (fb s).toNat + frameBytes = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack frameBytes at *; omega

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold encStack frameBytes; omega)

/-- The return address of a call from the frame. -/
theorem ret_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := by
  rw [show below (fb s) 8 = ⟨s.gpr .rsp - BitVec.ofNat 64 encStack, 8⟩ by
    simp only [below, fb, BitVec.sub_sub, ← BitVec.ofNat_add]; rfl]
  exact Region.sub_prefix (by decide)

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

/-- Memory changed only in the frame is changed only where the function may
write. -/
theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, outR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A byte of a buffer apart from the stack the function uses, past changes
to the frame. -/
theorem byte_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {p : Addr} {n : Nat}
    (hd : (stkR s).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) :=
  h _ (.inr (outside_frame s fun hc => hd _ hc (Offset.contains_base _ (by omega) (by omega))))

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega]

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : EPre s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 6) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

/-! ## The first block -/

theorem allocState_gpr (bytes : Nat) (s : State) (r : Reg) :
    (allocState bytes s).gpr r = if r = .rsp then s.gpr .rsp - BitVec.ofNat 64 bytes else s.gpr r := rfl

theorem allocState_mem (bytes : Nat) (s : State) : (allocState bytes s).mem = s.mem := rfl

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem ea_arg {t : State} {s : State} (h : t.gpr .rsp = fb s) (j : Nat) :
    t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

theorem arg_in {s : State} (hp : EPre s) {rd : List Region} (hrd : rd = s.rd) (wr : List Region) {j : Nat}
    (hj : j < 6) : InRegions (rd ++ wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 48⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

/-- What the first block leaves. -/
structure Setup (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  out : Outside (fb s) 0 frameBytes s.mem t.mem
  sOut : word t.mem (fb s) oOut = s.gpr .rdi
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9
  a0 : word t.mem (fb s) 0 = off (fb s) oEM
  a1 : word t.mem (fb s) 8 = s.gpr .rcx
  a2 : word t.mem (fb s) 16 = stackArg s 4
  a3 : word t.mem (fb s) 24 = stackArg s 5
  b0 : byte t.mem (fb s) oEM = 0
  b1 : byte t.mem (fb s) (oEM + 1) = 2
  rsi : t.gpr .rsi = stackArg s 2
  rcx : t.gpr .rcx = stackArg s 3
  r10 : t.gpr .r10 = BitVec.ofNat 64 0
  rdx : t.gpr .rdx = 0

/-- The memory after the first block. -/
def setupMem (s : State) : Mem :=
  ((((((((((s.mem.writeW (off (fb s) oOut) (s.gpr .rdi)).writeW (off (fb s) oN) (s.gpr .rdx)).writeW
    (off (fb s) oK) (s.gpr .rcx)).writeW (off (fb s) oE) (s.gpr .r8)).writeW (off (fb s) oEl) (s.gpr .r9)).writeW
    (fb s) (off (fb s) oEM)).writeW (off (fb s) 8) (s.gpr .rcx)).writeW (off (fb s) 16) (stackArg s 4)).writeW
    (off (fb s) 24) (stackArg s 5)).writeW (off (fb s) oEM) (0 : Byte)).writeW (off (fb s) (oEM + 1)) (2 : Byte)

theorem setup_run {s : State} (hp : EPre s) : WP isa (.block setup) (allocState frameBytes s) fun t =>
    t.mem = setupMem s ∧ t.gpr .rsi = stackArg s 2 ∧ t.gpr .rcx = stackArg s 3 ∧
      t.gpr .r10 = BitVec.ofNat 64 0 ∧ t.gpr .rdx = 0 ∧
      Keep [.r10, .r11, .rsi, .rax, .rdi, .rcx, .rdx] (allocState frameBytes s) t := by
  have hF := fb_toNat hp
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  have hs : Scr (allocState frameBytes s) (fb s) frameBytes :=
    Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  have hrd : (allocState frameBytes s).rd = s.rd := rfl
  have h0 : InRegions (allocState frameBytes s).wr (fb s) 8 := by
    have := hs.st (d := 0) (by decide); rwa [off, BitVec.add_zero] at this
  refine WP.mono (WP.keep [.r10, .r11, .rsi, .rax, .rdi, .rcx, .rdx] (c := .block setup) (Q := fun t =>
    t.mem = setupMem s ∧ t.gpr .rsi = stackArg s 2 ∧ t.gpr .rcx = stackArg s 3 ∧
      t.gpr .r10 = BitVec.ofNat 64 0 ∧ t.gpr .rdx = 0) ?_ rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5⟩, k⟩ => ⟨h1, h2, h3, h4, h5, k⟩
  xrun [h0, setup, ea_arg (s := s), ea_sp, hsp, arg_in hp hrd _ (show 4 < 6 by decide),
    arg_in hp hrd _ (show 5 < 6 by decide), arg_in hp hrd _ (show 2 < 6 by decide),
    arg_in hp hrd _ (show 3 < 6 by decide),
    hs.st (d := oOut) (by decide), hs.st (d := oN) (by decide), hs.st (d := oK) (by decide),
    hs.st (d := oE) (by decide), hs.st (d := oEl) (by decide),
    hs.st (d := 8) (by decide), hs.st (d := 16) (by decide), hs.st (d := 24) (by decide),
    hs.st8 (d := oEM) (by decide), hs.st8 (d := oEM + 1) (by decide), sx_ofNat (show oEM < 2 ^ 31 by decide),
    allocState_gpr, allocState_mem]
  exact ⟨rfl, rfl, rfl⟩

end VG.Proof.RsaPkcs1Enc.X86_64
