import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecContract
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the frame

The precondition by name (`DPre`), the frame of `frameBytes` bytes at
`fb s = rsp - frameBytes` and what lies around it, and the first block
(`setup_run`): the slots, the private-key operation's stack arguments in the
frame, and its arguments in registers.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-! ## The precondition, by name -/

/-- `decK.pre`, by name. -/
structure DPre (s : State) : Prop where
  sp1 : decStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 144 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩,
    ⟨stackArg s 13, (stackArg s 14).toNat⟩, ⟨stackArgAddr s 0, 136⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨s.gpr .rdx, 8⟩, ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩]
  dOm : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dOd : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dOi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  dMn : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dMe : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dMd : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dMi : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dMp : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dMq : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dMdp : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dMdq : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dMqi : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat⟩
  dMs : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dMa : (⟨s.gpr .rdx, 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  dns : (⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  des : (⟨s.gpr .r9, (stackArg s 0).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dds : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dis : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dps : (⟨stackArg s 5, (stackArg s 6).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dqs : (⟨stackArg s 7, (stackArg s 8).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  ddps : (⟨stackArg s 9, (stackArg s 10).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  ddqs : (⟨stackArg s 11, (stackArg s 12).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dqis : (⟨stackArg s 13, (stackArg s 14).toNat⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dsa : (⟨stackArg s 15, (stackArg s 16).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRm : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKm : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨s.gpr .rdx, 8⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨s.gpr .r9, (stackArg s 0).toNat⟩
  dKd : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKi : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint
    ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint
    ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint
    ⟨stackArg s 13, (stackArg s 14).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint
    ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 136⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wM : (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64
  wN : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wE : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wD : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wI : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wP : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wQ : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wDp : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wDq : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wQi : (stackArg s 13).toNat + (stackArg s 14).toNat ≤ 2 ^ 64
  wS : (stackArg s 15).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r8).toNat
  k2 : (s.gpr .r8).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .r8).toNat
  hil : (stackArg s 4).toNat = (s.gpr .r8).toNat
  L1 : 1 ≤ (stackArg s 0).toNat
  L2 : (stackArg s 0).toNat ≤ (s.gpr .r8).toNat
  dl1 : 1 ≤ (stackArg s 2).toNat
  dl2 : (stackArg s 2).toNat ≤ (s.gpr .r8).toNat
  pl1 : 1 ≤ (stackArg s 6).toNat
  pl2 : (stackArg s 6).toNat < (s.gpr .r8).toNat
  ql1 : 1 ≤ (stackArg s 8).toNat
  ql2 : (stackArg s 8).toNat < (s.gpr .r8).toNat
  hdpl : (stackArg s 10).toNat = (stackArg s 6).toNat
  hqil : (stackArg s 14).toNat = (stackArg s 6).toNat
  hdql : (stackArg s 12).toNat = (stackArg s 8).toNat
  hsl : 16 * (s.gpr .r8).toNat ≤ (stackArg s 16).toNat

theorem dPre_of {s : State} (h : decK.pre s) : DPre s := by
  simp only [decK] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr dOm dOn dOe dOd dOi dOp dOq dOdp dOdq dOqi dOs dOa dMn dMe dMd dMi dMp dMq dMdp
    dMdq dMqi dMs dMa dns des dds dis dps dqs ddps ddqs dqis dsa dRo dRm dRs dKo dKm dKn dKe dKd dKi dKp dKq
    dKdp dKdq dKqi dKs dKa wO wM wN wE wD wI wP wQ wDp wDq wQi wS hsplit1 hsi hil L1 L2 dl1 dl2 pl1 pl2 ql1
    ql2 hdpl hqil hdql
  obtain ⟨k1, k2⟩ := hsplit1
  have hsl := h
  clear h
  exact ⟨sp1, sp2, hrd, hwr, dOm, dOn, dOe, dOd, dOi, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dMn, dMe, dMd, dMi,
    dMp, dMq, dMdp, dMdq, dMqi, dMs, dMa, dns, des, dds, dis, dps, dqs, ddps, ddqs, dqis, dsa, dRo, dRm, dRs,
    dKo, dKm, dKn, dKe, dKd, dKi, dKp, dKq, dKdp, dKdq, dKqi, dKs, dKa, wO, wM, wN, wE, wD, wI, wP, wQ, wDp, wDq,
    wQi, wS, k1, k2, hsi, hil, L1, L2, dl1, dl2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, and the buffers it writes. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 decStack, decStack⟩
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def mlR (s : State) : Region := ⟨s.gpr .rdx, 8⟩
def scrR (s : State) : Region := ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩

theorem fb_eq (s : State) : fb s = off (s.gpr .rsp - BitVec.ofNat 64 decStack) (8 + privStack) :=
  Offset.sub_ofNat_eq _ (by decide)

theorem fb_toNat {s : State} (hp : DPre s) : (fb s).toNat + frameBytes + 8 + 136 ≤ 2 ^ 64 ∧
    (fb s).toNat + frameBytes = (s.gpr .rsp).toNat ∧ 8 + privStack ≤ (fb s).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold decStack privStack frameBytes at *; omega

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold decStack privStack frameBytes; omega)

/-- The `n ≤ 8 + privStack` bytes below the frame are in the stack the
function uses. -/
theorem below_sub (s : State) {n : Nat} (hn : n ≤ 8 + privStack) : Region.Sub (below (fb s) n) (stkR s) := by
  rw [show below (fb s) n = ⟨s.gpr .rsp - BitVec.ofNat 64 (frameBytes + n), n⟩ by
    simp only [below, fb, BitVec.sub_sub, ← BitVec.ofNat_add]]
  exact Offset.sub_below _ (by unfold decStack frameBytes; omega) (by unfold decStack frameBytes; omega)

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

/-- The regions the function may write. -/
abbrev wrs (s : State) : List Region := [stkR s, outR s, mlR s, scrR s]

/-- Memory changed only in the frame is changed only where the function may
write. -/
theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame (wrs s) s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega]

/-- A stack argument, past changes to the frame. -/
theorem arg_outside {s : State} (hp : DPre s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 17) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

/-- A byte of a buffer apart from the stack the function uses, past changes
to the frame. -/
theorem byte_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {p : Addr} {n : Nat}
    (hd : (stkR s).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < n) :
    m (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) :=
  h _ (.inr (outside_frame s fun hc => hd _ hc (Offset.contains_base _ (by omega) (by omega))))

/-! ## The first block -/

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem ea_arg {t : State} {s : State} (h : t.gpr .rsp = fb s) (j : Nat) :
    t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

theorem arg_in {s : State} (hp : DPre s) {rd : List Region} (hrd : rd = s.rd) (wr : List Region) {j : Nat}
    (hj : j < 17) : InRegions (rd ++ wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 136⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)⟩

theorem allocState_gpr (bytes : Nat) (s : State) (r : Reg) :
    (allocState bytes s).gpr r = if r = .rsp then s.gpr .rsp - BitVec.ofNat 64 bytes else s.gpr r := rfl

/-- The registers' arguments to their slots. -/
theorem slotStores_run {s : State} (hp : DPre s) :
    WP isa (.block slotStores) (allocState frameBytes s) fun t =>
      t.mem = ((((s.mem.writeW (off (fb s) oOut) (s.gpr .rdi)).writeW (off (fb s) oML) (s.gpr .rdx)).writeW
        (off (fb s) oN) (s.gpr .rcx)).writeW (off (fb s) oK) (s.gpr .r8)).writeW (off (fb s) oE) (s.gpr .r9) ∧
      Keep [] (allocState frameBytes s) t := by
  have hF := fb_toNat hp
  have hs : Scr (allocState frameBytes s) (fb s) frameBytes :=
    Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  exact WP.keep [] (by
    xrun [slotStores, ea_sp, hsp, hs.st (d := oOut) (by decide), hs.st (d := oML) (by decide),
      hs.st (d := oK) (by decide), hs.st (d := oN) (by decide), hs.st (d := oE) (by decide), allocState_gpr]
    rfl) rfl

/-- Stack argument `j` to the frame's word at `d`. -/
theorem mvArg_run {s t : State} (hp : DPre s) (hsp : t.gpr .rsp = fb s) (hs : Scr t (fb s) frameBytes)
    (hrd : t.rd = s.rd) (ho : Outside (fb s) 0 frameBytes s.mem t.mem) {j d : Nat} (hj : j < 17)
    (hd : d + 8 ≤ frameBytes) :
    WP isa (.block (mvArg j d)) t fun t' => t'.mem = t.mem.writeW (off (fb s) d) (stackArg s j) ∧
      Keep [.rax] t t' := by
  have ha := arg_in hp hrd t.wr hj
  exact WP.keep [.rax] (by xrun [mvArg, ea_arg hsp, ea_sp, hsp, ha, arg_outside hp ho hj, hs.st hd]) rfl

/-- The stack arguments `argMoves` names, each to its word of the frame. -/
theorem mvArgs_run {s : State} (hp : DPre s) : ∀ (ps : List (Nat × Nat)),
    (∀ p ∈ ps, p.1 < 17 ∧ p.2 % 8 = 0 ∧ p.2 + 8 ≤ frameBytes) → (ps.map (·.2)).Nodup →
    ∀ (t : State), t.gpr .rsp = fb s → Scr t (fb s) frameBytes → t.rd = s.rd →
    Outside (fb s) 0 frameBytes s.mem t.mem →
    WP isa (.block (ps.flatMap fun p => mvArg p.1 p.2)) t fun t' => Outside (fb s) 0 frameBytes s.mem t'.mem ∧
      (∀ p ∈ ps, word t'.mem (fb s) p.2 = stackArg s p.1) ∧
      (∀ d, d % 8 = 0 → d + 8 ≤ frameBytes → (∀ p ∈ ps, p.2 ≠ d) → word t'.mem (fb s) d = word t.mem (fb s) d) ∧
      Keep [.rax] t t'
  | [], _, _, t, _, _, _, ho => WP.block_nil ⟨ho, fun _ h => absurd h List.not_mem_nil, fun _ _ _ _ => rfl,
      Keep.refl _ _⟩
  | p :: ps, hps, hnd, t, hsp, hs, hrd, ho => by
    have hF := fb_toNat hp
    obtain ⟨hj, h8, hd⟩ := hps p (List.mem_cons_self ..)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (mvArg_run hp hsp hs hrd ho hj hd) fun t₁ ⟨hm₁, k₁⟩ => ?_
    have ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := by
      rw [hm₁]; exact Outside.ww ho _ (by omega) hd (by unfold frameBytes at *; omega)
    have hnd' := List.nodup_cons.mp hnd
    refine WP.mono (mvArgs_run hp ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hnd'.2 t₁
      ((k₁.gpr (by decide)).trans hsp) (hs.congr k₁.2.2) (k₁.2.1.trans hrd) ho₁)
      fun t' ⟨ho', hw', hk', k'⟩ => ⟨ho', fun q hq => ?_, fun d hd8 hdF hne => ?_, (k₁.trans k').mono (by decide)⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [hk' _ h8 hd fun q' hq' he => hnd'.1 (List.mem_map.mpr ⟨q', hq', he⟩), hm₁, word_writeW_self]
      · exact hw' q hq
    · rw [hk' d hd8 hdF fun q hq => hne q (List.mem_cons_of_mem _ hq), hm₁,
        word_ww _ _ _ (by have := hne p (List.mem_cons_self ..); omega) (by unfold frameBytes at *; omega)
          (by unfold frameBytes at *; omega)]

/-- The slots set by the first block, in memory `m`. -/
structure Slots (s : State) (m : Mem) : Prop where
  sOut : word m (fb s) oOut = s.gpr .rdi
  sML : word m (fb s) oML = s.gpr .rdx
  sN : word m (fb s) oN = s.gpr .rcx
  sK : word m (fb s) oK = s.gpr .r8
  sE : word m (fb s) oE = s.gpr .r9
  sEl : word m (fb s) oEl = stackArg s 0
  sD : word m (fb s) oD = stackArg s 1
  sDl : word m (fb s) oDl = stackArg s 2
  sIn : word m (fb s) oIn = stackArg s 3
  sScr : word m (fb s) oScr = stackArg s 15

/-- Changes from offset `oR` on keep the slots. -/
theorem Slots.outside {s : State} {m m' : Mem} (h : Slots s m) {o n : Nat} (ho : oR ≤ o)
    (h' : Outside (fb s) o n m m') : Slots s m' := by
  have w : ∀ {d : Nat}, d + 8 ≤ oR → word m' (fb s) d = word m (fb s) d := fun hd =>
    h'.word (.inl (by omega)) (by unfold oR at hd; omega)
  exact ⟨(w (by decide)).trans h.sOut, (w (by decide)).trans h.sML, (w (by decide)).trans h.sN,
    (w (by decide)).trans h.sK, (w (by decide)).trans h.sE, (w (by decide)).trans h.sEl,
    (w (by decide)).trans h.sD, (w (by decide)).trans h.sDl, (w (by decide)).trans h.sIn,
    (w (by decide)).trans h.sScr⟩

/-- What the first block leaves. -/
structure Setup (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  out : Outside (fb s) 0 frameBytes s.mem t.mem
  slots : Slots s t.mem
  args : ∀ i < 14, word t.mem (fb s) (8 * i) = stackArg s (i + 3)
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .r8
  rdx : t.gpr .rdx = s.gpr .rcx
  rcx : t.gpr .rcx = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = stackArg s 0

theorem argMoves_ok : ∀ p ∈ argMoves, p.1 < 17 ∧ p.2 % 8 = 0 ∧ p.2 + 8 ≤ frameBytes := by decide

theorem argMoves_nodup : (argMoves.map (·.2)).Nodup := by decide

theorem setup_run {s : State} (hp : DPre s) : WP isa (.block setup) (allocState frameBytes s) (Setup s) := by
  have hF := fb_toNat hp
  have hs : Scr (allocState frameBytes s) (fb s) frameBytes :=
    Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  rw [setup, WP.block_append_iff]
  refine WP.mono (slotStores_run hp) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := by
    rw [hm₁]
    exact Outside.ww (Outside.ww (Outside.ww (Outside.ww (Outside.ww (Outside.refl _ _ _ _) _ (by decide)
      (by decide) (by decide)) _ (by decide) (by decide) (by decide)) _ (by decide) (by decide) (by decide)) _
      (by decide) (by decide) (by decide)) _ (by decide) (by decide) (by decide)
  have hw₁ : word t₁.mem (fb s) oOut = s.gpr .rdi ∧ word t₁.mem (fb s) oML = s.gpr .rdx ∧
      word t₁.mem (fb s) oN = s.gpr .rcx ∧ word t₁.mem (fb s) oK = s.gpr .r8 ∧ word t₁.mem (fb s) oE = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [word_ww, word_writeW_self, and_self]
  rw [WP.block_append_iff]
  refine WP.mono (mvArgs_run hp argMoves argMoves_ok argMoves_nodup t₁ ((k₁.gpr (by decide)).trans rfl)
    (hs.congr k₁.2.2) k₁.2.1 ho₁) fun t₂ ⟨ho₂, hw₂, hk₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hsp₂ : t₂.gpr .rsp = fb s := (k12.gpr (by decide)).trans rfl
  have hs₂ : Scr t₂ (fb s) frameBytes := hs.congr k12.2.2
  have mv : ∀ {j d : Nat}, (j, d) ∈ argMoves → word t₂.mem (fb s) d = stackArg s j := fun {j d} h => hw₂ (j, d) h
  have keep : ∀ {d : Nat}, d % 8 = 0 → d + 8 ≤ frameBytes → (∀ p ∈ argMoves, p.2 ≠ d) →
      word t₂.mem (fb s) d = word t₁.mem (fb s) d := fun {d} h₁ h₂ h₃ => hk₂ d h₁ h₂ h₃
  have sl : Slots s t₂.mem := ⟨(keep (by decide) (by decide) (by decide)).trans hw₁.1,
    (keep (by decide) (by decide) (by decide)).trans hw₁.2.1, (keep (by decide) (by decide) (by decide)).trans hw₁.2.2.1,
    (keep (by decide) (by decide) (by decide)).trans hw₁.2.2.2.1,
    (keep (by decide) (by decide) (by decide)).trans hw₁.2.2.2.2,
    mv (by decide), mv (by decide), mv (by decide), mv (by decide), mv (by decide)⟩
  have hargs : ∀ i < 14, word t₂.mem (fb s) (8 * i) = stackArg s (i + 3) := fun i hi =>
    mv (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  refine WP.mono (WP.keep [.rsi, .rdx, .rcx, .r8, .r9] (c := .block privRegs) (Q := fun t =>
      t.mem = t₂.mem ∧ t.gpr .rsi = t₂.gpr .r8 ∧ t.gpr .rdx = t₂.gpr .rcx ∧ t.gpr .rcx = t₂.gpr .r8 ∧
      t.gpr .r8 = t₂.gpr .r9 ∧ t.gpr .r9 = stackArg s 0) (by
    xrun [privRegs, ea_sp, hsp₂, hs₂.ld (d := oEl) (by decide), sl.sEl]) rfl) fun t ⟨⟨hm, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have k' := k12.trans k
  have hreg : ∀ q : Reg, q ≠ .rax → q ≠ .rsp → t₂.gpr q = s.gpr q := fun q h₁ h₂ => by
    rw [k12.gpr (by simpa using h₁), allocState_gpr]; simp only [h₂, ↓reduceIte]
  exact ⟨(k'.gpr (by decide)).trans rfl, k'.2.1, k'.2.2, hm ▸ ho₂, hm ▸ sl, fun i hi => hm ▸ hargs i hi,
    (k.gpr (by decide)).trans (hreg _ (by decide) (by decide)), hsi.trans (hreg _ (by decide) (by decide)),
    hdx.trans (hreg _ (by decide) (by decide)), hcx.trans (hreg _ (by decide) (by decide)),
    h8.trans (hreg _ (by decide) (by decide)), h9⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
