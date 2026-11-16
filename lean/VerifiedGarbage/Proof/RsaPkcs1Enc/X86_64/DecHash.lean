module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecContract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Bytes
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.Steps
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Bignum.X86_64.CTSetup

/-! ### `RsaPkcs1Enc.X86_64.DecD`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86_64.DecCtx`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86_64.DecPriv`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.X86_64.DecFrame`, which only this module used -/

section

/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the frame

The precondition by name (`DPre`), the frame of `frameBytes` bytes at
`fb s = rsp - frameBytes` and what lies around it, and the first block
(`setup_run`): the slots, the private-key operation's stack arguments in the
frame, and its arguments in registers.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-! ## The precondition, by name -/

/-- `decK.pre`, by name. -/
structure DPre (s : State) : Prop where
  sp1 : decStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 144 ≤ 2 ^ 64
  hrd : ∀ r ∈ ([⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩,
    ⟨stackArg s 13, (stackArg s 14).toNat⟩] : List Region), r ∈ s.rd
  /-- The stack arguments, in a readable region of at least 136 bytes. -/
  hra : ∃ A, 136 ≤ A ∧ A < 2 ^ 32 ∧ (⟨stackArgAddr s 0, A⟩ : Region) ∈ s.rd
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
  hsl : 16 * (s.gpr .r8).toNat + 32 ≤ (stackArg s 16).toNat

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
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold decStack privStack frameBytes at *; omega_arith

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold decStack privStack frameBytes; omega_arith)

/-- The `n ≤ 8 + privStack` bytes below the frame are in the stack the
function uses. -/
theorem below_sub (s : State) {n : Nat} (hn : n ≤ 8 + privStack) : Region.Sub (below (fb s) n) (stkR s) := by
  rw [show below (fb s) n = ⟨s.gpr .rsp - BitVec.ofNat 64 (frameBytes + n), n⟩ by
    simp only [below, fb, BitVec.sub_sub, ← BitVec.ofNat_add]]
  exact Offset.sub_below _ (by unfold decStack frameBytes; omega_arith) (by unfold decStack frameBytes; omega_arith)

/-- A byte outside the stack the function uses is outside the frame. -/
theorem outside_frame (s : State) {x : Addr} (hx : ¬ (stkR s).Contains x 1) :
    frameBytes ≤ ofs (fb s) x := by
  by_contra hlt
  apply hx
  obtain hc : (⟨fb s, frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hlt ⊢; omega_arith
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
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega_arith, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega_arith]

/-- A stack argument, past changes to the frame. -/
theorem arg_outside {s : State} (hp : DPre s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 17) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_arith)) (by unfold frameBytes at *; omega_arith)

/-! ## The first block -/

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem ea_arg {t : State} {s : State} (h : t.gpr .rsp = fb s) (j : Nat) :
    t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

theorem arg_in {s : State} (hp : DPre s) {rd : List Region} (hrd : rd = s.rd) (wr : List Region) {j : Nat}
    (hj : j < 17) : InRegions (rd ++ wr) (stackArgAddr s j) 8 := by
  obtain ⟨A, hA, hA', hm⟩ := hp.hra
  exact ⟨⟨stackArgAddr s 0, A⟩, List.mem_append_left _ (by rw [hrd]; exact hm),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem allocState_gpr (bytes : Nat) (s : State) (r : Reg) :
    (allocState bytes s).gpr r = if r = .rsp then s.gpr .rsp - BitVec.ofNat 64 bytes else s.gpr r := rfl

/-- The registers' arguments to their slots. -/
theorem slotStores_run {s : State} (hp : DPre s) :
    WP isa (.block slotStores) (allocState frameBytes s) fun t =>
      t.mem = ((((s.mem.writeW (off (fb s) oOut) (s.gpr .rdi)).writeW (off (fb s) oML) (s.gpr .rdx)).writeW
        (off (fb s) oN) (s.gpr .rcx)).writeW (off (fb s) oK) (s.gpr .r8)).writeW (off (fb s) oE) (s.gpr .r9) ∧
      Keep [] (allocState frameBytes s) t := by
  obtain hF := fb_toNat hp
  obtain hs : Scr (allocState frameBytes s) (fb s) frameBytes :=
    Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega_arith)
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
  obtain ha := arg_in hp hrd t.wr hj
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
    obtain hF := fb_toNat hp
    obtain ⟨hj, h8, hd⟩ := hps p (List.mem_cons_self ..)
    rw [List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (mvArg_run hp hsp hs hrd ho hj hd) fun t₁ ⟨hm₁, k₁⟩ => ?_
    obtain ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := by
      rw [hm₁]; exact Outside.ww ho _ (by omega_arith) hd (by unfold frameBytes at *; omega_arith)
    obtain hnd' := List.nodup_cons.mp hnd
    refine WP.mono (mvArgs_run hp ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hnd'.2 t₁
      ((k₁.gpr (by decide)).trans hsp) (hs.congr k₁.2.2) (k₁.2.1.trans hrd) ho₁)
      fun t' ⟨ho', hw', hk', k'⟩ => ⟨ho', fun q hq => ?_, fun d hd8 hdF hne => ?_, (k₁.trans k').mono (by decide)⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [hk' _ h8 hd fun q' hq' he => hnd'.1 (List.mem_map.mpr ⟨q', hq', he⟩), hm₁, word_writeW_self]
      · exact hw' q hq
    · rw [hk' d hd8 hdF fun q hq => hne q (List.mem_cons_of_mem _ hq), hm₁,
        word_ww _ _ _ (by have := hne p (List.mem_cons_self ..); omega_arith) (by unfold frameBytes at *; omega_arith)
          (by unfold frameBytes at *; omega_arith)]

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

/-- What a call of the private-key operation from the frame needs of the
state before it: the frame, the call's stack arguments and its registers. -/
structure CallAt (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  out : Outside (fb s) 0 frameBytes s.mem t.mem
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
  obtain hF := fb_toNat hp
  obtain hs : Scr (allocState frameBytes s) (fb s) frameBytes :=
    Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega_arith)
  rw [setup, WP.block_append_iff]
  refine WP.mono (slotStores_run hp) fun t₁ ⟨hm₁, k₁⟩ => ?_
  obtain ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := by
    rw [hm₁]
    exact Outside.ww (Outside.ww (Outside.ww (Outside.ww (Outside.ww (Outside.refl _ _ _ _) _ (by decide)
      (by decide) (by decide)) _ (by decide) (by decide) (by decide)) _ (by decide) (by decide) (by decide)) _
      (by decide) (by decide) (by decide)) _ (by decide) (by decide) (by decide)
  obtain hw₁ : word t₁.mem (fb s) oOut = s.gpr .rdi ∧ word t₁.mem (fb s) oML = s.gpr .rdx ∧
      word t₁.mem (fb s) oN = s.gpr .rcx ∧ word t₁.mem (fb s) oK = s.gpr .r8 ∧ word t₁.mem (fb s) oE = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [word_ww, word_writeW_self, and_self]
  rw [WP.block_append_iff]
  refine WP.mono (mvArgs_run hp argMoves argMoves_ok argMoves_nodup t₁ ((k₁.gpr (by decide)).trans rfl)
    (hs.congr k₁.2.2) k₁.2.1 ho₁) fun t₂ ⟨ho₂, hw₂, hk₂, k₂⟩ => ?_
  obtain k12 := k₁.trans k₂
  obtain hsp₂ : t₂.gpr .rsp = fb s := (k12.gpr (by decide)).trans rfl
  obtain hs₂ : Scr t₂ (fb s) frameBytes := hs.congr k12.2.2
  obtain mv : ∀ {j d : Nat}, (j, d) ∈ argMoves → word t₂.mem (fb s) d = stackArg s j := fun {j d} h => hw₂ (j, d) h
  obtain keep : ∀ {d : Nat}, d % 8 = 0 → d + 8 ≤ frameBytes → (∀ p ∈ argMoves, p.2 ≠ d) →
      word t₂.mem (fb s) d = word t₁.mem (fb s) d := fun {d} h₁ h₂ h₃ => hk₂ d h₁ h₂ h₃
  obtain sl : Slots s t₂.mem := ⟨(keep (by decide) (by decide) (by decide)).trans hw₁.1,
    (keep (by decide) (by decide) (by decide)).trans hw₁.2.1, (keep (by decide) (by decide) (by decide)).trans hw₁.2.2.1,
    (keep (by decide) (by decide) (by decide)).trans hw₁.2.2.2.1,
    (keep (by decide) (by decide) (by decide)).trans hw₁.2.2.2.2,
    mv (by decide), mv (by decide), mv (by decide), mv (by decide), mv (by decide)⟩
  obtain hargs : ∀ i < 14, word t₂.mem (fb s) (8 * i) = stackArg s (i + 3) := fun i hi =>
    mv (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  refine WP.mono (WP.keep [.rsi, .rdx, .rcx, .r8, .r9] (c := .block privRegs) (Q := fun t =>
      t.mem = t₂.mem ∧ t.gpr .rsi = t₂.gpr .r8 ∧ t.gpr .rdx = t₂.gpr .rcx ∧ t.gpr .rcx = t₂.gpr .r8 ∧
      t.gpr .r8 = t₂.gpr .r9 ∧ t.gpr .r9 = stackArg s 0) (by
    xrun [privRegs, ea_sp, hsp₂, hs₂.ld (d := oEl) (by decide), sl.sEl]) rfl) fun t ⟨⟨hm, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  obtain k' := k12.trans k
  obtain hreg : ∀ q : Reg, q ≠ .rax → q ≠ .rsp → t₂.gpr q = s.gpr q := fun q h₁ h₂ => by
    rw [k12.gpr (by simpa using h₁), allocState_gpr]; simp only [h₂, ↓reduceIte]
  exact ⟨(k'.gpr (by decide)).trans rfl, k'.2.1, k'.2.2, hm ▸ ho₂, hm ▸ sl, fun i hi => hm ▸ hargs i hi,
    (k.gpr (by decide)).trans (hreg _ (by decide) (by decide)), hsi.trans (hreg _ (by decide) (by decide)),
    hdx.trans (hreg _ (by decide) (by decide)), hcx.trans (hreg _ (by decide) (by decide)),
    h8.trans (hreg _ (by decide) (by decide)), h9⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: the private-key operation

Its precondition with its stack arguments in the frame (`priv_pre`), and
what it leaves (`priv_call`): `out` holds its outcome for the ciphertext,
and the frame its slots.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- The base of the stack the function uses. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 decStack

theorem fb_sub8 (s : State) : fb s - 8 = off (kb s) privStack := by
  rw [fb_eq, off, off, show 8 + privStack = privStack + 8 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem kb_toNat {s : State} (hp : DPre s) : (kb s).toNat + decStack + 144 ≤ 2 ^ 64 ∧
    (kb s).toNat + decStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold decStack privStack frameBytes at *; omega_arith

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  obtain hsep := Offset.sep (off (kb s) privStack) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_arith)
    (by omega_arith) (by omega_arith)
  rw [show off (kb s) privStack + BitVec.ofNat 64 0 = off (kb s) privStack from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_eq, off_off, off_add, show privStack + 8 * (i + 1) = 8 + privStack + 8 * i by omega_arith]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_eq, off_add, show privStack + 8 * (0 + 1) = 8 + privStack by omega_arith]

/-- What `vg_rsa_private_checked` reads. -/
def privRd (s : State) : List Region :=
  [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩, ⟨s.gpr .r9, (stackArg s 0).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩,
    ⟨stackArg s 13, (stackArg s 14).toNat⟩, ⟨fb s, 112⟩]

/-- What it writes: `out` and the working space. -/
def privWr (s : State) : List Region :=
  [⟨s.gpr .rdi, (s.gpr .r8).toNat⟩, ⟨stackArg s 15, (stackArg s 16).toNat * 8⟩]

/-- What the callee's entry state's stack arguments are. -/
theorem priv_args {s t : State} (h : CallAt s t) (rd wr : List Region) {i : Nat} (hi : i < 14) :
    stackArg (t.callEntry.withRegions rd wr) i = stackArg s (i + 3) :=
  (stackArg_entry h.rsp _ _ (by omega_arith)).trans (h.args i hi)

theorem priv_pre {s t : State} (hp : DPre s) (h : CallAt s t) :
    privK.pre (t.callEntry.withRegions (privRd s) (privWr s)) := by
  obtain e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions (privRd s) (privWr s)) i = stackArg s (i + 3) :=
    fun hi => priv_args h _ _ hi
  simp only [privK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp,
    stackArgAddr_entry h.rsp, e (show 0 < 14 by decide), e (show 1 < 14 by decide), e (show 2 < 14 by decide),
    e (show 3 < 14 by decide), e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide),
    e (show 7 < 14 by decide), e (show 8 < 14 by decide), e (show 9 < 14 by decide),
    e (show 10 < 14 by decide), e (show 11 < 14 by decide), e (show 12 < 14 by decide),
    e (show 13 < 14 by decide), Nat.reduceAdd, fb_sub8]
  have ⟨hK1, hK2⟩ := kb_toNat hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi := hp.hsi
  have hil := hp.hil
  have e5 : decStack = 3480 := rfl
  have e6 : privStack = 3256 := rfl
  have e7 : frameBytes = 216 := rfl
  obtain hfb : fb s = off (kb s) (8 + privStack) := fb_eq s
  -- The callee's stack, its return address and its stack arguments, in ours.
  obtain sK : Region.Sub ⟨kb s, privStack⟩ (stkR s) := Region.sub_prefix (by omega_arith)
  obtain sR : Region.Sub ⟨off (kb s) privStack, 8⟩ (stkR s) := Offset.sub_base _ (by omega_arith)
  obtain sA : Region.Sub ⟨fb s, 112⟩ (stkR s) := by rw [hfb]; exact Offset.sub_base _ (by omega_arith)
  obtain dRA : (⟨off (kb s) privStack, 8⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain dKA : (⟨kb s, privStack⟩ : Region).Disjoint ⟨fb s, 112⟩ := by
    rw [hfb]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  obtain hoff : (off (kb s) privStack).toNat = (kb s).toNat + privStack := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith
  obtain kbsub : kb s = off (kb s) privStack - BitVec.ofNat 64 privStack := by
    rw [off, BitVec.add_sub_cancel]
  rw [← kbsub]
  obtain rw' : ∀ {r : Region}, (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint r →
      (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region).Disjoint r := fun h => by rwa [hsi] at h
  obtain dKo : (stkR s).Disjoint ⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ := by have := hp.dKo; rwa [hsi] at this
  have dKi : (stkR s).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩ := hp.dKi
  refine ⟨by omega_arith, by omega_arith, rfl, rfl, rw' hp.dOn, rw' hp.dOe, rw' hp.dOi, rw' hp.dOp, rw' hp.dOq, rw' hp.dOdp,
    rw' hp.dOdq, rw' hp.dOqi, rw' hp.dOs, (dKo.sub_left sA).symm, hp.dns, hp.des, hp.dis, hp.dps, hp.dqs, hp.ddps,
    hp.ddqs, hp.dqis, (hp.dKs.sub_left sA).symm, dKo.sub_left sR, hp.dKn.sub_left sR, hp.dKe.sub_left sR,
    hp.dKi.sub_left sR, hp.dKp.sub_left sR, hp.dKq.sub_left sR, hp.dKdp.sub_left sR, hp.dKdq.sub_left sR,
    hp.dKqi.sub_left sR, hp.dKs.sub_left sR, dRA, dKo.sub_left sK, hp.dKn.sub_left sK, hp.dKe.sub_left sK,
    hp.dKi.sub_left sK, hp.dKp.sub_left sK, hp.dKq.sub_left sK, hp.dKdp.sub_left sK, hp.dKdq.sub_left sK,
    hp.dKqi.sub_left sK, hp.dKs.sub_left sK, dKA, by have := hp.wO; omega_arith, hp.wN, hp.wE, hp.wI, hp.wP, hp.wQ,
    hp.wDp, hp.wDq, hp.wQi, hp.wS, ⟨hk1, hk2⟩, trivial, hil, hp.L1, hp.L2, hp.pl1, hp.pl2, hp.ql1, hp.ql2,
    hp.hdpl, hp.hqil, hp.hdql, hp.hsl⟩


theorem priv_covers {s t : State} (hp : DPre s) (h : CallAt s t) :
    Covers (privRd s ++ privWr s) (t.rd ++ t.wr) ∧ Covers (privWr s) t.wr := by
  have hk2 := hp.k2
  have hsi := hp.hsi
  have e3 : frameBytes = 216 := rfl
  obtain hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [h.wr]; exact List.mem_cons_self ..
  obtain hscr : (⟨stackArg s 15, (stackArg s 16).toNat * 8⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr]; simp
  obtain hout : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region) ∈ t.wr := by rw [h.wr, hp.hwr]; simp
  obtain z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  obtain cw : Covers (privWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [privWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, hout, 0, z _, by dsimp only; omega_arith⟩
    · exact ⟨_, hscr, 0, z _, by dsimp only; omega_arith⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  obtain hrd : ∀ x, x ∈ s.rd → x ∈ t.rd ++ t.wr := fun x hx => List.mem_append_left _ (by rw [h.rd]; exact hx)
  simp only [privRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, hrd ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨s.gpr .r9, (stackArg s 0).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 3, (stackArg s 4).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 5, (stackArg s 6).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 7, (stackArg s 8).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 9, (stackArg s 10).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 11, (stackArg s 12).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, hrd ⟨stackArg s 13, (stackArg s 14).toNat⟩ (hp.hrd _ (by simp)), 0, z _, by dsimp only; omega_arith⟩
  · exact ⟨_, List.mem_append_right _ hfr, 0, z _, by dsimp only; omega_arith⟩

/-- Memory changed by a call from the frame, within regions the function
may write. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame (wrs s) m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, ∃ R ∈ wrs s, Region.Sub r R) : Frame (wrs s) m₁ m₃ :=
  h₁.trans (h₂.sub hs)

/-- A buffer the function does not write, from memory changed only where it
may write. -/
theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame (wrs s) s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hm : (mlR s).Disjoint ⟨p, len⟩)
    (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hm.symm
  · exact hs.symm

/-! ## The inputs -/

abbrev kOf (s : State) : Nat := (s.gpr .r8).toNat
abbrev nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (kOf s)
abbrev eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
abbrev dB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
abbrev cB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 3) (kOf s)
abbrev pB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat
abbrev qB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 8).toNat
abbrev dpB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat
abbrev dqB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 8).toNat
abbrev qiB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 13) (stackArg s 6).toNat

/-- The private-key operation's outcome for the ciphertext. -/
abbrev privOut (s : State) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (nB s) (eB s) (cB s) (pB s) (qB s) (dpB s) (dqB s) (qiB s)

/-- After the call. -/
structure PostPriv (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame (wrs s) s.mem t.mem
  slots : Slots s t.mem
  res : Spec.Rsa.writtenOutcome t.mem (s.gpr .rdi) (kOf s) ((t.gpr .rax).setWidth 32) (privOut s)

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- The slots are apart from what the call writes. -/
theorem slot_apart {s : State} (hp : DPre s) {d n : Nat} (hd : d + n ≤ frameBytes) :
    ∀ r ∈ privWr s ++ [below (fb s) (8 + privStack)], (⟨off (fb s) d, n⟩ : Region).Disjoint r := by
  have ⟨hK1, _⟩ := kb_toNat hp
  have e1 : decStack = 3480 := rfl
  have e2 : privStack = 3256 := rfl
  have e3 : frameBytes = 216 := rfl
  have hsi := hp.hsi
  intro r hr
  simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := hp.dKo; rw [hsi] at this; exact this.sub_left (frame_sub s hd)
  · exact hp.dKs.sub_left (frame_sub s hd)
  · rw [show below (fb s) (8 + privStack) = ⟨kb s, 8 + privStack⟩ by
      simp only [below, fb_eq, off, BitVec.add_sub_cancel], fb_eq, off_off]
    exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

/-- What a call of the private-key operation leaves, but the slots: the
frame's words are kept. -/
structure PostCall (s t t' : State) : Prop where
  rsp : t'.gpr .rsp = fb s
  rd : t'.rd = s.rd
  wr : t'.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame (wrs s) s.mem t'.mem
  keep : ∀ {d : Nat}, d + 8 ≤ frameBytes → word t'.mem (fb s) d = word t.mem (fb s) d
  res : Spec.Rsa.writtenOutcome t'.mem (s.gpr .rdi) (kOf s) ((t'.gpr .rax).setWidth 32) (privOut s)

/-- A call of code that does what `vg_rsa_private_checked` does (`k`, with
its postcondition), given what it reads (`rds`, `privRd` and more). -/
theorem privWith_call {name : String} {code : Prog isa} {k : Contract isa}
    (hcorr : ∀ s, k.pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hk : ∀ a b, k.post a b → privK.post a b) (hsp : code.all (fun i => !isa.writesSp i) = true)
    (hdp : code.x86_64Depth ≤ privStack) {s t : State} (hp : DPre s) (h : CallAt s t) {rds : List Region}
    (hpre : k.pre (t.callEntry.withRegions rds (privWr s)))
    (hc : Covers (rds ++ privWr s) (t.rd ++ t.wr)) (hw : Covers (privWr s) t.wr) :
    WP isa (.call name code) t fun t' => PostCall s t t' ∧ (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      t'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 := by
  have e2 : privStack = 3256 := rfl
  refine WP.call_sp_mx (k := k) hcorr (SpSafe.of_all hsp) (by omega_arith) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  replace hpost := hk _ _ hpost
  rw [h.rsp] at hf
  obtain hf' : Frame (privWr s ++ [below (fb s) (8 + privStack)]) t.mem s'.mem :=
    Frame.below_mono hf (by omega_arith) (by have := (fb_toNat hp).2.2; omega_arith)
  have hk2 := hp.k2
  have hsi' := hp.hsi
  have e7 : frameBytes = 216 := rfl
  obtain hfE : Frame (wrs s) s.mem t.callEntry.mem :=
    frame_call (frame_of_outside h.out) (callEntry_frame h.rsp) fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨stkR s, List.mem_cons_self .., below_sub s (by omega_arith)⟩
  obtain e : ∀ {i : Nat}, i < 14 → stackArg (t.callEntry.withRegions rds (privWr s)) i = stackArg s (i + 3) :=
    fun hi => priv_args h _ _ hi
  obtain bo : ∀ {p : Addr} {len : Nat}, (stkR s).Disjoint ⟨p, len⟩ → (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨p, len⟩ →
      (mlR s).Disjoint ⟨p, len⟩ → (⟨p, len⟩ : Region).Disjoint (scrR s) → len ≤ 2 ^ 64 →
      Spec.Rsa.bytesAt t.callEntry.mem p len = Spec.Rsa.bytesAt s.mem p len :=
    fun hk ho hm hs hl => bytes_of_frame hfE hk ho hm hs.symm hl
  simp only [privK, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide), h.rdi, h.rdx, h.rcx, h.r8, h.r9, hm₂,
    hg₂ .rax (by decide), e (show 0 < 14 by decide), e (show 2 < 14 by decide), e (show 3 < 14 by decide),
    e (show 4 < 14 by decide), e (show 5 < 14 by decide), e (show 6 < 14 by decide), e (show 8 < 14 by decide),
    e (show 10 < 14 by decide), Nat.reduceAdd] at hpost
  have hl := hp.hil
  rw [bo hp.dKn hp.dOn hp.dMn hp.dns (by have := hp.wN; omega_arith),
    bo hp.dKe hp.dOe hp.dMe hp.des (by have := hp.wE; omega_arith),
    show (s.gpr .r8).toNat = (stackArg s 4).toNat from hl.symm,
    bo hp.dKi hp.dOi hp.dMi hp.dis (by have := hp.wI; omega_arith),
    bo hp.dKp hp.dOp hp.dMp hp.dps (by have := hp.wP; omega_arith),
    bo hp.dKq hp.dOq hp.dMq hp.dqs (by have := hp.wQ; omega_arith),
    show (stackArg s 6).toNat = (stackArg s 10).toNat from hp.hdpl.symm,
    bo hp.dKdp hp.dOdp hp.dMdp hp.ddps (by have := hp.wDp; omega_arith),
    show (stackArg s 8).toNat = (stackArg s 12).toNat from hp.hdql.symm,
    bo hp.dKdq hp.dOdq hp.dMdq hp.ddqs (by have := hp.wDq; omega_arith),
    show (stackArg s 10).toNat = (stackArg s 14).toNat by rw [hp.hdpl, hp.hqil],
    bo hp.dKqi hp.dOqi hp.dMqi hp.dqis (by have := hp.wQi; omega_arith)] at hpost
  obtain hkeep : ∀ {d : Nat}, d + 8 ≤ frameBytes → word s'.mem (fb s) d = word t.mem (fb s) d := fun hd =>
    hf'.readW (Region.contains_self _ _) (slot_apart hp (by omega_arith)) (by decide)
  refine ⟨⟨(hcs .rsp (by decide)).trans h.rsp, hrd.trans h.rd, hwr.trans h.wr,
    frame_call (frame_of_outside h.out) hf' fun r hr => ?_, hkeep, ?_⟩, hcs, hmx⟩
  · simp only [privWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨outR s, by simp, by rw [outR, hsi']; exact fun _ h => h⟩
    · exact ⟨scrR s, by simp, fun _ h => h⟩
    · exact ⟨stkR s, by simp, below_sub s (Nat.le_refl _)⟩
  · simp only [privOut, nB, eB, cB, pB, qB, dpB, dqB, qiB, kOf]
    rw [hl, hp.hqil, hp.hdql] at hpost
    exact hpost

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: after the private-key operation

From the call of the private-key operation to the output, the function
writes only the first `scrBytes` bytes of `scratch`, its slots from `oR` on
and the stack below its frame (`Safe`): through all of it, the slots, the
result `R` in its slot and `EM` in `out` stay as they are (`Ctx`,
`Ctx.step`). What it computes in `scratch` is tracked with the regions each
step writes (`bytes_keep`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- `scratch`, and an address in it. -/
abbrev sc (s : State) : Addr := stackArg s 15
abbrev scA (s : State) (d : Nat) : Addr := off (sc s) d

/-- The part of `scratch` used after the private-key operation. -/
def scrBytes : Nat := 3440

theorem scr_len {s : State} (hp : DPre s) : scrBytes ≤ (stackArg s 16).toNat * 8 ∧
    (sc s).toNat + (stackArg s 16).toNat * 8 ≤ 2 ^ 64 := by
  have := hp.hsl; have := hp.k1; have := hp.wS
  exact ⟨by unfold scrBytes; omega_arith, by omega⟩

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

/-- What a step may write. -/
def Safe (s : State) (r : Region) : Prop :=
  Region.Sub r ⟨sc s, scrBytes⟩ ∨ Region.Sub r (below (fb s) (8 + privStack)) ∨ Region.Sub r ⟨off (fb s) oI, 16⟩

/-- After the call: the slots, `R` in its slot, `EM` in `out`. -/
structure Ctx (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame (wrs s) s.mem t.mem
  slots : Slots s t.mem
  sR : word t.mem (fb s) oR = R
  out : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s) = EM
  cs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r

theorem Safe.sub {s : State} (hp : DPre s) {r : Region} (h : Safe s r) : ∃ R ∈ wrs s, Region.Sub r R := by
  rcases h with h | h | h
  · obtain ⟨h1, _⟩ := scr_len hp
    exact ⟨scrR s, by simp, sub_trans h (Region.sub_prefix h1)⟩
  · exact ⟨stkR s, by simp, sub_trans h (below_sub s (Nat.le_refl _))⟩
  · exact ⟨stkR s, by simp, sub_trans h (frame_sub s (by decide))⟩

/-- A region apart from the stack the function uses and from `scratch` is
apart from what a step writes. -/
theorem Safe.disj {s : State} (hp : DPre s) {r X : Region} (h : Safe s r) (hk : (stkR s).Disjoint X)
    (hs : (scrR s).Disjoint X) : X.Disjoint r := by
  rcases h with h | h | h
  · obtain ⟨h1, _⟩ := scr_len hp
    exact (hs.sub_left (sub_trans h (Region.sub_prefix h1))).symm
  · exact (hk.sub_left (sub_trans h (below_sub s (Nat.le_refl _)))).symm
  · exact (hk.sub_left (sub_trans h (frame_sub s (by decide)))).symm

/-- Words of the frame below `oI` are apart from what a step writes. -/
theorem Safe.slot {s : State} (hp : DPre s) {r : Region} (h : Safe s r) {d : Nat} (hd : d + 8 ≤ oI) :
    (⟨off (fb s) d, 8⟩ : Region).Disjoint r := by
  obtain hF := fb_toNat hp
  have e1 : oI = 200 := rfl
  rcases h with h | h | h
  · obtain ⟨h1, _⟩ := scr_len hp
    exact (hp.dKs.sub_left (frame_sub s (by unfold frameBytes; omega_using [hd, e1]))).sub_right (sub_trans h (Region.sub_prefix h1))
  · refine Region.Disjoint.sub_right ?_ h
    exact Offset.disjoint_below (fb s) (by have := hF.2.2; unfold frameBytes privStack at *; omega_using [hd, e1])
  · refine Region.Disjoint.sub_right ?_ h
    exact Offset.disjoint _ (.inl hd) (by unfold frameBytes at hF; omega_using [hd, e1]) (by unfold frameBytes at hF; omega_using [e1])

/-- `[b + i + d]` for `b = p` and `i = j`. -/
theorem ea_bxd {t : State} {b i : Reg} {p : Addr} {j : Nat} (d : Nat) (hb : t.gpr b = p)
    (hi : t.gpr i = BitVec.ofNat 64 j) : t.ea (bx b i d) = off p (d + j) := by
  simp only [State.ea, bx, hb, hi, BitVec.mul_one, BitVec.ofInt_natCast, off]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]

/-- `[b + d]`. -/
theorem ea_atd {t : State} {b : Reg} {p : Addr} (d : Nat) (hb : t.gpr b = p) : t.ea (at_ b d) = off p d := by
  simp only [State.ea, at_, hb, BitVec.ofInt_natCast, off]

theorem blen (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem bget (m : Mem) (p : Addr) {n i : Nat} (h : i < (Spec.Rsa.bytesAt m p n).length) :
    (Spec.Rsa.bytesAt m p n)[i] = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt]

/-- A buffer apart from what a step writes keeps its bytes. -/
theorem bytes_keep {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

/-- A step that writes only where it may keeps `Ctx`. -/
theorem Ctx.step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hcs : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) {ws : List Region}
    (hf : Frame ws t.mem t'.mem) (hs : ∀ r ∈ ws, Safe s r) : Ctx s R EM t' := by
  obtain w : ∀ {d : Nat}, d + 8 ≤ oI → word t'.mem (fb s) d = word t.mem (fb s) d := fun hd =>
    hf.readW (Region.contains_self _ _) (fun r hr => Safe.slot hp (hs r hr) hd) (by decide)
  have hk2 := hp.k2
  have hsi := hp.hsi
  refine ⟨(hcs .rsp (by decide)).trans hc.rsp, hrd.trans hc.rd, hwr.trans hc.wr, frame_call hc.mem hf fun r hr => (hs r hr).sub hp,
    ⟨(w (by decide)).trans hc.slots.sOut, (w (by decide)).trans hc.slots.sML, (w (by decide)).trans hc.slots.sN,
      (w (by decide)).trans hc.slots.sK, (w (by decide)).trans hc.slots.sE, (w (by decide)).trans hc.slots.sEl,
      (w (by decide)).trans hc.slots.sD, (w (by decide)).trans hc.slots.sDl, (w (by decide)).trans hc.slots.sIn,
      (w (by decide)).trans hc.slots.sScr⟩, (w (by decide)).trans hc.sR, ?_,
    fun r hr hr' => (hcs r hr).trans (hc.cs r hr hr')⟩
  rw [bytes_keep hf (fun r hr => Safe.disj hp (hs r hr) (by have := hp.dKo; rwa [hsi] at this)
    (by have := hp.dOs; rw [hsi] at this; exact this.symm)) (by unfold kOf; omega_using [])]
  exact hc.out

/-- What a block keeps of the callee-saved registers. -/
theorem _root_.VG.Proof.MlKem.X86_64.Keep.cs {rs : List Reg} {t t' : State} (k : Keep rs t t')
    (h : ∀ r ∈ calleeSaved, r ∉ rs) : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r := fun r hr => k.gpr (h r hr)

/-- `m'` differs from `m` only at the offsets `[o, o + n)` of `base`, a
region. -/
theorem frame_of_out {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    (hn : o + n ≤ 2 ^ 64) : Frame [⟨off base o, n⟩] m m' := fun x hx => by
  refine h x ?_
  obtain hc := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains, off] at hc
  obtain hc' : ¬ (x - (base + BitVec.ofNat 64 o)).toNat < n := by omega_using [hc]
  rw [Offset.lt_iff x base hn] at hc'
  simp only [ofs]
  omega_using [hc']

/-- The used part of `scratch` is working space. -/
theorem Ctx.scr {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    Scr t (sc s) scrBytes := by
  obtain ⟨h1, h2⟩ := scr_len hp
  obtain hs : Scr t (sc s) ((stackArg s 16).toNat * 8) :=
    Scr.of_mem (by rw [hc.wr, hp.hwr]; simp) h2
  have := hs.sub (o := 0) (n := scrBytes) (by omega_using [h1]) (by decide)
  rwa [off_zero] at this

/-- The frame is working space. -/
theorem Ctx.frm {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [hc.wr]; exact List.mem_cons_self ..) (by have := (fb_toNat hp).1; omega_using [this])

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: `D = I2OSP(d, k)`

The private-key operation's result to its slot (`p1_step`, which starts
`Ctx`), `k` zeros at `scratch + sD` (`zeroLoop_ok`), then `d` at their end
(`copyLoop_ok`): `D`, `d` after `k - d_len` zeros, is `I2OSP(d, k)`
(`dBuild_step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64

/-- The length of `d`. -/
abbrev dlOf (s : State) : Nat := (stackArg s 2).toNat

/-- After the result's store: `Ctx`, and the zero loop's registers. -/
structure P1 (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  rdi : t.gpr .rdi = sc s
  rcx : t.gpr .rcx = s.gpr .r8
  r10 : t.gpr .r10 = BitVec.ofNat 64 0
  rax : t.gpr .rax = BitVec.setWidth 64 (0 : BitVec 32)

theorem p1_step {s t : State} (hp : DPre s) (h : PostPriv s t)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) :
    WP isa (.block dPtrs₁) t (P1 s (t.gpr .rax) (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s))) := by
  obtain hF := fb_toNat hp
  obtain hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega_arith)
  have hk2 := hp.k2
  have hsi := hp.hsi
  refine WP.mono (WP.keep [.rdi, .rcx, .r10, .rax] (c := .block dPtrs₁) (Q := fun t' =>
      t'.mem = t.mem.writeW (off (fb s) oR) (t.gpr .rax) ∧ t'.gpr .rdi = sc s ∧ t'.gpr .rcx = s.gpr .r8 ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rax = BitVec.setWidth 64 (0 : BitVec 32)) (by
    xrun [dPtrs₁, ea_sp, h.rsp, hs.st (d := oR) (by decide), hs.ld (d := oScr) (by decide),
      hs.ld (d := oK) (by decide), word_ww _ _ _ (show oScr + 8 ≤ oR ∨ oR + 8 ≤ oScr by decide)
        (by decide) (by decide),
      word_ww _ _ _ (show oK + 8 ≤ oR ∨ oR + 8 ≤ oK by decide) (by decide) (by decide), h.slots.sScr, h.slots.sK]
    done) rfl) fun t' ⟨⟨hm, hdi, hcx, h10, hax⟩, k⟩ => ?_
  obtain hfw : Frame [⟨off (fb s) oR, 8⟩] t.mem t'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain w : ∀ {d : Nat}, d + 8 ≤ oR → word t'.mem (fb s) d = word t.mem (fb s) d := fun hd => by
    rw [hm]; exact word_ww _ _ _ (.inl hd) (by unfold frameBytes at hF; unfold oR at hd; omega_arith)
      (by unfold frameBytes at hF; unfold oR; omega_arith)
  refine ⟨⟨(k.gpr (by decide)).trans h.rsp, k.2.1.trans h.rd, k.2.2.trans h.wr,
    frame_call h.mem hfw fun r hr => ?_,
    ⟨(w (by decide)).trans h.slots.sOut, (w (by decide)).trans h.slots.sML, (w (by decide)).trans h.slots.sN,
      (w (by decide)).trans h.slots.sK, (w (by decide)).trans h.slots.sE, (w (by decide)).trans h.slots.sEl,
      (w (by decide)).trans h.slots.sD, (w (by decide)).trans h.slots.sDl, (w (by decide)).trans h.slots.sIn,
      (w (by decide)).trans h.slots.sScr⟩, by rw [hm]; exact word_writeW_self _ _ _ _, ?_,
    fun r hr hr' => (k.cs (by decide) r hr).trans (hcs r hr hr')⟩, hdi, hcx, h10, hax⟩
  · rw [List.mem_singleton.mp hr]; exact ⟨stkR s, by simp, frame_sub s (by decide)⟩
  · refine bytes_keep hfw (fun r hr => ?_) (by unfold kOf; omega_arith)
    rw [List.mem_singleton.mp hr]
    have := hp.dKo; rw [hsi] at this
    exact (this.sub_left (frame_sub s (by decide))).symm

/-! ## The zeros -/

/-- After `j` zeros, from the state `t₀` before the loop. -/
structure ZInv (s t₀ : State) (j : Nat) (t : State) : Prop where
  keep : Keep [.r10] t₀ t
  out : Outside (sc s) sD j t₀.mem t.mem
  zs : ∀ i < j, byte t.mem (sc s) (sD + i) = 0
  r10 : t.gpr .r10 = BitVec.ofNat 64 j

theorem zeroLoop_ok {s t₀ : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} (h : P1 s R EM t₀) :
    WP isa zeroLoop t₀ (ZInv s t₀ (kOf s)) := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  obtain hs := h.ctx.scr hp
  have ⟨_, hS⟩ := scr_len hp
  obtain hcx' : t₀.gpr .rcx = BitVec.ofNat 64 (kOf s) := by rw [h.rcx]; simp
  refine wp_upto (a := 0) (N := kOf s) (by unfold kOf; omega_arith) (ZInv s t₀) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), h.r10⟩
  intro j _ hj u hI
  obtain hdi : u.gpr .rdi = sc s := (hI.keep.gpr (by decide)).trans h.rdi
  obtain hcx : u.gpr .rcx = BitVec.ofNat 64 (kOf s) := (hI.keep.gpr (by decide)).trans hcx'
  obtain hax : u.gpr .rax = BitVec.setWidth 64 (0 : BitVec 32) := (hI.keep.gpr (by decide)).trans h.rax
  obtain hst : InRegions u.wr (off (sc s) (sD + j)) 1 :=
    (hs.congr hI.keep.2.2).st8 (by unfold scrBytes sD; unfold kOf at hj; omega_arith)
  obtain hea : u.ea (bx .rdi .r10 sD) = off (sc s) (sD + j) := ea_bxd sD hdi hI.r10
  have hkk : kOf s ≤ 1024 := hk2
  refine WP.mono (WP.keep [.r10] (Q := fun u' =>
      u'.mem = u.mem.writeW (off (sc s) (sD + j)) (0 : Byte) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = kOf s))) (by
    xrun [zeroLoop, hea, hst, hI.r10, hcx, hax, zero_trunc, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_arith) (show kOf s < 2 ^ 64 by omega_arith)]
    done) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), ?_, ?_, h10'⟩
  · rw [hm]
    exact Outside.wb (Outside.mono hI.out (by omega_arith) (by omega_arith)) _ (by omega_arith) (by omega_arith)
      (by unfold sD; unfold kOf at hj; omega_arith)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega_arith) (by unfold sD; unfold kOf at hj; omega_arith)
        (by unfold sD; unfold kOf at hj; omega_arith)]
      exact hI.zs i hi
    · exact byte_wb_self _ _ _ _


/-! ## `d` -/

/-- A byte of a buffer apart from `L` bytes at `p` lies `L` or more past `p`. -/
theorem ofs_of_disjoint {p q : Addr} {L n j : Nat} (hd : (⟨p, L⟩ : Region).Disjoint ⟨q, n⟩) (hj : j < n)
    (hn : n ≤ 2 ^ 64) : L ≤ ofs p (q + BitVec.ofNat 64 j) := by
  refine Nat.le_of_not_lt fun hl => hd (q + BitVec.ofNat 64 j) ?_ (Offset.contains_base q (by omega_arith) (by omega_arith))
  simp only [Region.Contains, ofs] at hl ⊢; omega_arith

/-- A byte of a buffer the function only reads, in a state of `Ctx` and
then changed only in `scratch`. -/
theorem ctx_byte {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {m : Mem} {o n : Nat} (ho : Outside (sc s) o n t.mem m) (hon : o + n ≤ scrBytes) {q : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨q, len⟩) (hO : (outR s).Disjoint ⟨q, len⟩) (hM : (mlR s).Disjoint ⟨q, len⟩)
    (hS : (scrR s).Disjoint ⟨q, len⟩) (hl : len ≤ 2 ^ 64) {j : Nat} (hj : j < len) :
    m (q + BitVec.ofNat 64 j) = s.mem (q + BitVec.ofNat 64 j) := by
  obtain ⟨h1, _⟩ := scr_len hp
  rw [ho _ (.inr (by have := ofs_of_disjoint (p := sc s) hS hj hl; omega_arith))]
  exact hc.mem.bytes (R := ⟨q, len⟩) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hk.symm
    · exact hO.symm
    · exact hM.symm
    · exact hS.symm) hl hj

/-- `x + y - z` for `z ≤ y`. -/
theorem add_sub_ofNat (x : Addr) {y z : BitVec 64} (h : z.toNat ≤ y.toNat) :
    x + y - z = off x (y.toNat - z.toNat) := by
  rw [off, BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := y.isLt; have := z.isLt
  omega_arith

/-- The copy loop's registers. -/
structure P2 (s : State) (R : BitVec 64) (EM : List Byte) (t₀ t : State) : Prop where
  ctx : Ctx s R EM t
  out : Outside (sc s) sD (kOf s) t₀.mem t.mem
  zs : ∀ i < kOf s, byte t.mem (sc s) (sD + i) = 0
  rsi : t.gpr .rsi = stackArg s 1
  rcx : t.gpr .rcx = stackArg s 2
  rdi : t.gpr .rdi = off (sc s) (kOf s - dlOf s)
  r10 : t.gpr .r10 = BitVec.ofNat 64 0

theorem p2_step {s t₀ t : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} (h₀ : P1 s R EM t₀)
    (h : ZInv s t₀ (kOf s) t) : WP isa (.block dPtrs₂) t (P2 s R EM t₀) := by
  obtain hF := fb_toNat hp
  obtain hc₁ : Ctx s R EM t := h₀.ctx.step hp h.keep.2.1 h.keep.2.2 (h.keep.cs (by decide))
    (frame_of_out h.out (by unfold sD; have := hp.k2; unfold kOf; omega_arith)) fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by unfold sD scrBytes; have := hp.k2; unfold kOf; omega_arith))
  obtain hs := hc₁.frm hp
  have hsp := hc₁.rsp
  have hdl := hp.dl2
  refine WP.mono (WP.keep [.rsi, .rcx, .rdi, .r10] (c := .block dPtrs₂) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .rsi = stackArg s 1 ∧ t'.gpr .rcx = stackArg s 2 ∧
      t'.gpr .rdi = sc s + s.gpr .r8 - stackArg s 2 ∧ t'.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [dPtrs₂, ea_sp, hsp, hs.ld (d := oD) (by decide), hs.ld (d := oDl) (by decide),
      hs.ld (d := oScr) (by decide), hs.ld (d := oK) (by decide), hc₁.slots.sD, hc₁.slots.sDl,
      hc₁.slots.sScr, hc₁.slots.sK]) rfl) fun t' ⟨⟨hm, hsi, hcx, hdi, h10⟩, k⟩ => ?_
  obtain hc : Ctx s R EM t' := hc₁.step hp k.2.1 k.2.2 (k.cs (by decide)) (ws := [])
    (fun x _ => by rw [hm]) (fun _ h => absurd h List.not_mem_nil)
  refine ⟨hc, by rw [hm]; exact h.out, fun i hi => by rw [hm]; exact h.zs i hi, hsi, hcx, ?_, h10⟩
  rw [hdi, add_sub_ofNat _ hdl]


/-- After `j` bytes of `d`, from the state `t₀` before the loop. -/
structure CInv (s t₀ : State) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r10] t₀ t
  out : Outside (sc s) (sD + (kOf s - dlOf s)) j t₀.mem t.mem
  ds : ∀ i < j, byte t.mem (sc s) (sD + (kOf s - dlOf s) + i) = s.mem (stackArg s 1 + BitVec.ofNat 64 i)
  r10 : t.gpr .r10 = BitVec.ofNat 64 j

theorem copyLoop_ok {s t₁ t₀ : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} (h : P2 s R EM t₁ t₀) :
    WP isa copyLoop t₀ (CInv s t₀ (dlOf s)) := by
  have hk2 := hp.k2
  have hdl1 := hp.dl1
  have hdl := hp.dl2
  have hkk : kOf s ≤ 1024 := hk2
  have hd1 : 1 ≤ dlOf s := hdl1
  have hd2 : dlOf s ≤ kOf s := hdl
  obtain hs := h.ctx.scr hp
  obtain hcx' : t₀.gpr .rcx = BitVec.ofNat 64 (dlOf s) := by rw [h.rcx]; simp
  refine wp_upto (a := 0) (N := dlOf s) (by omega_arith) (CInv s t₀) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith), h.r10⟩
  intro j _ hj u hI
  obtain hdi : u.gpr .rdi = off (sc s) (kOf s - dlOf s) := (hI.keep.gpr (by decide)).trans h.rdi
  obtain hsi : u.gpr .rsi = stackArg s 1 := (hI.keep.gpr (by decide)).trans h.rsi
  obtain hcx : u.gpr .rcx = BitVec.ofNat 64 (dlOf s) := (hI.keep.gpr (by decide)).trans hcx'
  obtain hea₁ : u.ea (bx .rsi .r10) = off (stackArg s 1) (0 + j) := ea_bxd 0 hsi hI.r10
  obtain hea₂ : u.ea (bx .rdi .r10 sD) = off (sc s) (sD + (kOf s - dlOf s) + j) := by
    rw [ea_bxd sD hdi hI.r10, off_off, show kOf s - dlOf s + (sD + j) = sD + (kOf s - dlOf s) + j by omega_arith]
  obtain hst : InRegions u.wr (off (sc s) (sD + (kOf s - dlOf s) + j)) 1 :=
    (hs.congr hI.keep.2.2).st8 (by unfold scrBytes sD; omega_arith)
  have hjd : j < (stackArg s 2).toNat := hj
  obtain hin : InRegions (u.rd ++ u.wr) (off (stackArg s 1) (0 + j)) 1 :=
    ⟨⟨stackArg s 1, (stackArg s 2).toNat⟩, List.mem_append_left _ (by
      rw [hI.keep.2.1, h.ctx.rd]; exact hp.hrd _ (by simp)),
      by rw [Nat.zero_add]; exact Offset.contains_base _ (by omega_arith) (by have := hp.wD; omega_arith)⟩
  obtain hb : u.mem (off (stackArg s 1) (0 + j)) = s.mem (stackArg s 1 + BitVec.ofNat 64 j) := by
    rw [Nat.zero_add]
    exact ctx_byte hp h.ctx hI.out (by unfold scrBytes sD; omega_arith) hp.dKd hp.dOd hp.dMd hp.dds.symm
      (by have := hp.wD; omega_arith) hj
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun u' =>
      u'.mem = u.mem.writeW (off (sc s) (sD + (kOf s - dlOf s) + j)) (s.mem (stackArg s 1 + BitVec.ofNat 64 j)) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = dlOf s))) (by
    obtain hidx : kOf s - dlOf s + (sD + j) = sD + (kOf s - dlOf s) + j := by omega_arith
    xrun [copyLoop, hea₁, ea_bxd (j := j) (p := off (sc s) (kOf s - dlOf s)), hdi, off_off, hidx, hin, hst, hb, hI.r10, hcx, trunc_zext, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_arith) (show dlOf s < 2 ^ 64 by omega_arith)]
    done) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), ?_, ?_, h10'⟩
  · rw [hm]
    exact Outside.wb (Outside.mono hI.out (by omega_arith) (by omega_arith)) _ (by omega_arith) (by omega_arith)
      (by unfold sD; omega_arith)
  · intro i hi
    rw [hm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [byte_wb _ _ _ (by omega_arith) (by unfold sD; omega_arith) (by unfold sD; omega_arith)]
      exact hI.ds i hi
    · exact byte_wb_self _ _ _ _

/-- After `dBuild`: `D = I2OSP(d, k)` at `scratch + sD`. -/
structure DB (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  D : Spec.Rsa.bytesAt t.mem (scA s sD) (kOf s) = Spec.Rsa.i2osp (Spec.Rsa.os2ip (dB s)) (kOf s)

theorem dBuild_step {s t : State} (hp : DPre s) (h : PostPriv s t)
    (hcs : ∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) :
    WP isa dBuild t (DB s (t.gpr .rax) (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (kOf s))) := by
  have hk2 := hp.k2
  have hdl1 := hp.dl1
  have hdl := hp.dl2
  have hkk : kOf s ≤ 1024 := hk2
  have hd1 : 1 ≤ dlOf s := hdl1
  have hd2 : dlOf s ≤ kOf s := hdl
  have hdd : dlOf s = (stackArg s 2).toNat := rfl
  refine WP.seq (WP.mono (p1_step hp h hcs) fun t₁ h₁ => ?_)
  refine WP.seq (WP.mono (zeroLoop_ok hp h₁) fun t₂ h₂ => ?_)
  refine WP.seq (WP.mono (p2_step hp h₁ h₂) fun t₃ h₃ => ?_)
  refine WP.mono (copyLoop_ok hp h₃) fun t₄ h₄ => ?_
  obtain hc : Ctx s _ _ t₄ := h₃.ctx.step hp h₄.keep.2.1 h₄.keep.2.2 (h₄.keep.cs (by decide))
    (frame_of_out h₄.out (by unfold sD; omega_arith)) fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact .inl (Offset.sub_base _ (by unfold sD scrBytes; omega_arith))
  refine ⟨hc, ?_⟩
  rw [i2osp_os2ip_pad _ (by rw [blen]; exact hdl), blen]
  refine List.ext_getElem (by simp only [blen, List.length_append, List.length_replicate]; omega_arith)
    fun i h₁ h₂ => ?_
  rw [bget, off_add]
  simp only [blen] at h₁
  by_cases hi : i < kOf s - dlOf s
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate,
      h₄.out _ (.inl (by rw [ofs_off0 _ (by unfold sD; omega_arith)]; omega_arith))]
    exact h₃.zs i h₁
  · rw [List.getElem_append_right (by simp; omega_arith), bget]
    simp only [List.length_replicate]
    have := h₄.ds (i - (kOf s - dlOf s)) (by omega_arith)
    rw [show sD + (kOf s - dlOf s) + (i - (kOf s - dlOf s)) = sD + i by omega_arith] at this
    exact this

end VG.Proof.RsaPkcs1Enc.X86_64.Dec

end

end


/-!
# RSAES-PKCS1-v1_5 decryption on x86-64: `DH = SHA256(D)`

SHA-256's functions, with an implementation `v` of its compression function
(`HH v`), and what is proven of them; the regions of `scratch` the calls use
(`scD`, `stkD`, `scS`), and the hash of `D` (`hashD_step`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Dec

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Decrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Enc.X86_64
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK hmacInit_ok hmacFin_ok core_hmacInit core_hmacFin core_hmacInit_depth
  core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)

variable (v : Compress)

/-- SHA-256's functions, and what is proven of them. -/
abbrev HH : Impl.Pbkdf2.Md.X86_64.Hash := Proof.Pbkdf2.Md.X86_64.Sha256.hash v
abbrev OK : HashOK (HH v) := Proof.Pbkdf2.Md.X86_64.Sha256.ok v

theorem hI : Verified X86_64.target (HH v).hmacInit (initG (OK v).SH (HH v).W) :=
  hmacInit_ok (OK v) (Proof.Pbkdf2.Md.X86_64.Sha256.coreOK v) (Proof.Pbkdf2.Md.X86_64.Sha256.callees v)
    (Proof.Pbkdf2.Md.X86_64.Sha256.satI (Proof.Pbkdf2.Md.X86_64.Sha256.hashW v))

theorem hIsp : NoSp (HH v).hmacInit :=
  nosp_of (core_hmacInit (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).iNs
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).b.bNs (Proof.Pbkdf2.Md.X86_64.Sha256.coreOK v).hinitNs)

theorem hId : (HH v).hmacInit.depth ≤ 2 :=
  core_hmacInit_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).iD (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).b.bD
    (Proof.Pbkdf2.Md.X86_64.Sha256.coreOK v).hinitD

theorem hF : Verified X86_64.target (HH v).hmacFin (finG (OK v).SH (HH v).W) :=
  hmacFin_ok (OK v) (Proof.Pbkdf2.Md.X86_64.Sha256.coreOK v) (Proof.Pbkdf2.Md.X86_64.Sha256.callees v)
    (Proof.Pbkdf2.Md.X86_64.Sha256.satF (Proof.Pbkdf2.Md.X86_64.Sha256.hashW v))

theorem hFsp : NoSp (HH v).hmacFin :=
  nosp_of (core_hmacFin (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cNs (Proof.Pbkdf2.Md.X86_64.Sha256.coreOK v).hfinNs)

theorem hFd : (HH v).hmacFin.depth ≤ 2 :=
  core_hmacFin_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees v).cD (Proof.Pbkdf2.Md.X86_64.Sha256.coreOK v).hfinD

/-- The sizes: the working space of the functions called with `scratch + sWork`
is that of `v` (at most AVX2's). -/
theorem sizes : (HH v).S = 96 ∧ (HH v).W ≤ 104 ∧ (HH v).D = 32 ∧ (HH v).P.B = 64 ∧ (HH v).stream.S = 96 ∧
    (HH v).stream.F = 32 ∧ (HH v).stream.D = 32 ∧ (OK v).stream.Wb ≤ 608 := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show (Proof.Pbkdf2.Md.X86_64.Sha256.hash v).W ≤ 104
    rcases Proof.Pbkdf2.Md.X86_64.Sha256.hashW v with h | h | h <;> omega_using [h]
  · show v.callee.so + 48 ≤ 608
    rcases v.hso with h | h | h <;> omega_using [h]

/-- `scratch + sWork` holds the HMAC functions' working space. -/
theorem wFit : sWork + 8 * (HH v).W ≤ sMsg := by
  have := (sizes v).2.1; unfold sWork sMsg; omega_using [this]

/-- `scratch + sWork` holds the streaming functions' working space. -/
theorem wbFit : sWork + (OK v).stream.Wb ≤ sMsg := by
  have := (sizes v).2.2.2.2.2.2.2; unfold sWork sMsg; omega_using [this]

theorem wScr : sWork + 8 * (HH v).W ≤ scrBytes := Nat.le_trans (wFit v) (by decide)

theorem wbScr : sWork + (OK v).stream.Wb ≤ scrBytes := Nat.le_trans (wbFit v) (by decide)

/-- Regions of `scratch` from `sMsg` on lie above the working space. -/
theorem wbBelow {a : Nat} (h : sMsg ≤ a) : sWork + (OK v).stream.Wb ≤ a := Nat.le_trans (wbFit v) h

theorem wBelow {a : Nat} (h : sMsg ≤ a) : sWork + 8 * (HH v).W ≤ a := Nat.le_trans (wFit v) h

theorem sh_hash : (OK v).SH.H = Spec.Hmac.sha256 := rfl
/-! ## Regions of `scratch` -/

variable {v}

theorem scD {s : State} {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ scrBytes) (hb : b + m ≤ scrBytes) :
    Region.Disjoint ⟨scA s a, n⟩ ⟨scA s b, m⟩ :=
  Offset.disjoint (sc s) h (by unfold scrBytes at ha; omega_using [ha]) (by unfold scrBytes at hb; omega_using [hb])

theorem scSub {s : State} {a n : Nat} (ha : a + n ≤ scrBytes) : Region.Sub ⟨scA s a, n⟩ ⟨sc s, scrBytes⟩ :=
  Offset.sub_base _ ha

theorem stkD {s : State} (hp : DPre s) {n a m : Nat} (hn : n ≤ 8 + privStack) (ha : a + m ≤ scrBytes) :
    (below (fb s) n).Disjoint ⟨scA s a, m⟩ := by
  obtain ⟨h1, _⟩ := scr_len hp
  exact (hp.dKs.sub_left (below_sub s hn)).sub_right (sub_trans (scSub ha) (Region.sub_prefix h1))

theorem scS {s : State} {a n : Nat} (ha : a + n ≤ scrBytes) : Safe s ⟨scA s a, n⟩ := .inl (scSub ha)

theorem belowS {s : State} (hp : DPre s) {n : Nat} (hn : n ≤ 8 + privStack) : Safe s (below (fb s) n) :=
  .inr (.inl (VG.X86_64.below_sub hn (by have := (fb_toNat hp).2.2; unfold privStack at *; omega_using [])))

theorem scCov {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t)
    {a n : Nat} (ha : a + n ≤ scrBytes) : Covers [⟨scA s a, n⟩] t.wr := by
  obtain ⟨h1, _⟩ := scr_len hp
  exact Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨scrR s, by rw [hc.wr, hp.hwr]; simp [scrR], a, rfl, by dsimp only [scrR]; omega_using [ha, h1]⟩

/-- `(BitVec.ofNat 32 d).signExtend 64`, for `d < 2³¹`. -/
theorem sx {d : Nat} (h : d < 2 ^ 31) : (BitVec.ofNat 32 d).signExtend 64 = BitVec.ofNat 64 d := by
  obtain hm : (BitVec.ofNat 32 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_using [h]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_using [h]

/-! ## The hash of `D` -/

/-- Code that changes only registers but `rsp` keeps `Ctx`. -/
theorem Ctx.regs {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    (hm : t'.mem = t.mem) {rs : List Reg} (k : Keep rs t t') (hr : ∀ r ∈ calleeSaved, r ∉ rs) : Ctx s R EM t' :=
  hc.step hp k.2.1 k.2.2 (k.cs hr) (ws := []) (fun x _ => by rw [hm]) (fun _ h => absurd h List.not_mem_nil)

/-- What a call leaves, from `Calls.After`, for writes in `scratch` and below the frame. -/
theorem Ctx.after {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t t' : State} (hc : Ctx s R EM t)
    {ws : List Region} (h : Proof.Pbkdf2.Md.X86_64.Calls.After t ws t') (hs : ∀ r ∈ ws, Safe s r) :
    Ctx s R EM t' :=
  hc.step hp h.rd h.wr h.cs h.frame fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · rw [List.mem_singleton.mp hr, hc.rsp]; exact belowS hp (by decide)

theorem scA_zero (s : State) : scA s 0 = sc s := off_zero _

theorem shaInitArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block shaInitArgs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 := by
  obtain hs := hc.frm hp
  refine (WP.keep [.rdi] (c := .block shaInitArgs) (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h.1, h.2⟩
  xrun [shaInitArgs, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide), hc.slots.sScr, scA_zero]

theorem shaUpdArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block shaUpdArgs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = scA s sD ∧ t'.gpr .rcx = s.gpr .r8 ∧
      t'.gpr .r8 = scA s sWork := by
  obtain hs := hc.frm hp
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (c := .block shaUpdArgs) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = scA s sD ∧ t'.gpr .rcx = s.gpr .r8 ∧
    t'.gpr .r8 = scA s sWork) ?_ rfl).mono
    fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [shaUpdArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide), hs.ld (d := oK) (by decide),
    hc.slots.sScr, hc.slots.sK, scA_zero, sx (d := sD) (by decide), sx (d := sWork) (by decide)]


theorem shaFinArgs_run {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) :
    WP isa (.block shaFinArgs) t fun t' => Ctx s R EM t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = scA s 0 ∧
      t'.gpr .rsi = s.gpr .r8 ∧ t'.gpr .rdx = scA s sDH ∧ t'.gpr .rcx = scA s sWork := by
  obtain hs := hc.frm hp
  refine (WP.keep [.rdi, .rsi, .rdx, .rcx] (c := .block shaFinArgs) (Q := fun t' => t'.mem = t.mem ∧
    t'.gpr .rdi = scA s 0 ∧ t'.gpr .rsi = s.gpr .r8 ∧ t'.gpr .rdx = scA s sDH ∧ t'.gpr .rcx = scA s sWork) ?_
    rfl).mono fun t' ⟨h, k⟩ => ⟨hc.regs hp h.1 k (by decide), h⟩
  xrun [shaFinArgs, scr, List.cons_append, List.nil_append, ea_sp, hc.rsp, hs.ld (d := oScr) (by decide),
    hs.ld (d := oK) (by decide), hc.slots.sScr, hc.slots.sK, scA_zero, sx (d := sDH) (by decide),
    sx (d := sWork) (by decide)]

/-- After `hashD`: `DH = SHA256(D)` at `scratch + sDH`. -/
structure HD (s : State) (R : BitVec 64) (EM : List Byte) (t : State) : Prop where
  ctx : Ctx s R EM t
  dh : Spec.Rsa.bytesAt t.mem (scA s sDH) 32 =
    Spec.Sha256.hash (Spec.Rsa.i2osp (Spec.Rsa.os2ip (dB s)) (kOf s))

/-- `below (fb s) 16`, as the calls see it. -/
theorem below_rsp {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hc : Ctx s R EM t) (n : Nat) :
    below (t.gpr .rsp) n = below (fb s) n := by rw [hc.rsp]

theorem hashD_step {s : State} (hp : DPre s) {R : BitVec 64} {EM : List Byte} {t : State} (h : DB s R EM t) :
    WP isa (hashD (HH v)) t (HD s R EM) := by
  have hk2 := hp.k2
  have hk1 := hp.k1
  have hkk : kOf s ≤ 1024 := hk2
  obtain ⟨hW, -, -, -, hS, hF, hD, -⟩ := sizes v
  obtain so := (OK v).stream
  -- `init`
  refine WP.seq (WP.mono (shaInitArgs_run hp h.ctx) fun t₁ ⟨hc₁, hm₁, hdi₁⟩ => ?_)
  refine WP.seq (Proof.Pbkdf2.Md.X86_64.Calls.init_call (OK v).stream hdi₁
    (by rw [hS]; exact scCov hp hc₁ (by decide))
    (by rw [below_rsp hc₁, hS]; exact stkD hp (by decide) (by decide)) fun t₂ a₂ hr₂ => ?_)
  obtain hc₂ := hc₁.after hp a₂ fun r hr => by
    rw [List.mem_singleton.mp hr, hS]; exact scS (by decide)
  obtain hD₂ : Spec.Rsa.bytesAt t₂.mem (scA s sD) (kOf s) = Spec.Rsa.i2osp (Spec.Rsa.os2ip (dB s)) (kOf s) := by
    rw [bytes_keep a₂.frame (fun r hr => ?_) (by omega_using [hkk]), hm₁]
    · exact h.D
    · rcases List.mem_append.mp hr with hr | hr
      · rw [List.mem_singleton.mp hr, hS]; exact scD (.inr (by decide)) (by unfold sD scrBytes; omega_using [hkk]) (by decide)
      · rw [List.mem_singleton.mp hr, below_rsp hc₁]
        exact (stkD hp (by decide) (by unfold sD scrBytes; omega_using [hkk])).symm
  -- `update`
  refine WP.seq (WP.mono (shaUpdArgs_run hp hc₂) fun t₃ ⟨hc₃, hm₃, hdi₃, hsi₃, hdx₃, hcx₃, h8₃⟩ => ?_)
  obtain hD₃ := hm₃ ▸ hD₂
  obtain hr₃ : (OK v).stream.SH.Repr t₃.mem (scA s 0) [] := by rw [hm₃]; exact hr₂
  refine WP.seq (Proof.Pbkdf2.Md.X86_64.Calls.upd_call (OK v).stream (len := kOf s)
    { rdi := hdi₃, rdx := hdx₃, rcx := by rw [hcx₃], r8 := h8₃
      cd := Covers.right (scCov hp hc₃ (by unfold sD scrBytes; omega_using [hkk]))
      cw := by rw [hS]; exact Covers.pair (scCov hp hc₃ (by decide)) (scCov hp hc₃ (wbScr v))
      st_sc := by rw [hS]; exact scD (.inl (by decide)) (by decide) (wbScr v)
      d_st := by rw [hS]; exact scD (.inr (by decide)) (by unfold sD scrBytes; omega_using [hkk]) (by decide)
      d_sc := scD (.inr (wbBelow v (by decide))) (by unfold sD scrBytes; omega_using [hkk]) (wbScr v)
      stk_st := by rw [below_rsp hc₃, hS]; exact stkD hp (by decide) (by decide)
      stk_d := by rw [below_rsp hc₃]; exact stkD hp (by decide) (by unfold sD scrBytes; omega_using [hkk])
      stk_sc := by rw [below_rsp hc₃]; exact stkD hp (by decide) (wbScr v) } (by omega_using [hkk])
    fun t₄ a₄ hu₄ => ?_)
  obtain hc₄ := hc₃.after hp a₄ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hS]; exact scS (by decide)
    · exact scS (wbScr v)
  obtain hr₄ := hu₄ [] hr₃ (by rw [hsi₃]; rfl)
  -- `finalize`
  refine WP.seq (WP.mono (shaFinArgs_run hp hc₄) fun t₅ ⟨hc₅, hm₅, hdi₅, hsi₅, hdx₅, hcx₅⟩ => ?_)
  obtain cw₅ : Covers [⟨scA s 0, 96⟩, ⟨scA s sDH, 32⟩, ⟨scA s sWork, (OK v).stream.Wb⟩] t₅.wr :=
    (scCov hp hc₅ (by decide)).cons ((scCov hp hc₅ (by decide)).cons ((scCov hp hc₅ (wbScr v)).cons Covers.nil))
  refine Proof.Pbkdf2.Md.X86_64.Calls.fin_call (OK v).stream
    { rdi := hdi₅, rdx := hdx₅, rcx := hcx₅
      cw := by rw [hS, hF]; exact cw₅
      st_o := by rw [hS, hF]; exact scD (.inl (by decide)) (by decide) (by decide)
      st_sc := by rw [hS]; exact scD (.inl (by decide)) (by decide) (wbScr v)
      o_sc := by rw [hF]; exact scD (.inr (wbBelow v (by decide))) (by decide) (wbScr v)
      stk_st := by rw [below_rsp hc₅, hS]; exact stkD hp (by decide) (by decide)
      stk_o := by rw [below_rsp hc₅, hF]; exact stkD hp (by decide) (by decide)
      stk_sc := by rw [below_rsp hc₅]; exact stkD hp (by decide) (wbScr v) } fun t₆ a₆ hf₆ => ?_
  obtain hc₆ := hc₅.after hp a₆ fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hS]; exact scS (by decide)
    · rw [hF]; exact scS (by decide)
    · exact scS (wbScr v)
  refine ⟨hc₆, ?_⟩
  have := hf₆ _ (by rw [hm₅]; exact hr₄) (by simp [Spec.Sha256.bytesAt]; omega_using [hkk])
    (by rw [hsi₅]; simp [Spec.Sha256.bytesAt])
  rw [hF, hD] at this
  rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])] at this
  rw [show Spec.Rsa.bytesAt t₆.mem (scA s sDH) 32 = Spec.Sha256.bytesAt t₆.mem (scA s sDH) 32 from rfl, this]
  show Spec.Sha256.hash ([] ++ Spec.Sha256.bytesAt t₃.mem (scA s sD) (kOf s)) = _
  rw [List.nil_append, show Spec.Sha256.bytesAt t₃.mem (scA s sD) (kOf s) =
    Spec.Rsa.bytesAt t₃.mem (scA s sD) (kOf s) from rfl, hD₃]

end VG.Proof.RsaPkcs1Enc.X86_64.Dec
