module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Random
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncFrame
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCtx
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.PcCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncLoops
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.CallSp
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86-64: the pieces

What each piece of the code does, in order: the frame, the setup, the scan,
the call to `vg_rsa_pkcs1_encrypt_precomputed` and the two ends.

## The frame

The precondition by name (`RPre`), with the stack `rndStack` (the frame,
the return address of the call and the stack of
`vg_rsa_pkcs1_encrypt_precomputed`), the frame of `frameBytes` bytes at
`fb s = rsp - frameBytes`, and how its slots and stack arguments are read.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack allocState_gpr allocState_mem)

/-- The stack: the frame, the call's return address and the callee's. -/
def rndStack : Nat := frameBytes + 8 + encStack

theorem rndStack_eq : rndStack = 2288 := rfl

theorem stackArgs_nine (s : State) :
    (List.range 9).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2,
      stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8] := rfl

/-! ## The regions -/

def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def tapeR (s : State) : Region := ⟨s.gpr .rdx, 16⟩
def nR (s : State) : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
def eR (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat⟩
def msgR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
def randR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
def preR (s : State) : Region := ⟨stackArg s 7, (stackArg s 8).toNat * 8⟩
def argsR (s : State) : Region := ⟨stackArgAddr s 0, 72⟩
def retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 rndStack, rndStack⟩

/-- The contract's precondition, by name. -/
structure RPre (s : State) : Prop where
  sp1 : rndStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 80 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, msgR s, randR s, preR s, argsR s]
  hwr : s.wr = [outR s, tapeR s, scrR s]
  dOt : (outR s).Disjoint (tapeR s)
  dOn : (outR s).Disjoint (nR s)
  dOe : (outR s).Disjoint (eR s)
  dOm : (outR s).Disjoint (msgR s)
  dOr : (outR s).Disjoint (randR s)
  dOs : (outR s).Disjoint (scrR s)
  dOq : (outR s).Disjoint (preR s)
  dOa : (outR s).Disjoint (argsR s)
  dTn : (tapeR s).Disjoint (nR s)
  dTe : (tapeR s).Disjoint (eR s)
  dTm : (tapeR s).Disjoint (msgR s)
  dTr : (tapeR s).Disjoint (randR s)
  dTs : (tapeR s).Disjoint (scrR s)
  dTq : (tapeR s).Disjoint (preR s)
  dTa : (tapeR s).Disjoint (argsR s)
  dNs : (nR s).Disjoint (scrR s)
  dEs : (eR s).Disjoint (scrR s)
  dMs : (msgR s).Disjoint (scrR s)
  dRs : (randR s).Disjoint (scrR s)
  dSq : (scrR s).Disjoint (preR s)
  dSa : (scrR s).Disjoint (argsR s)
  dXo : (retR s).Disjoint (outR s)
  dXt : (retR s).Disjoint (tapeR s)
  dXn : (retR s).Disjoint (nR s)
  dXe : (retR s).Disjoint (eR s)
  dXm : (retR s).Disjoint (msgR s)
  dXr : (retR s).Disjoint (randR s)
  dXs : (retR s).Disjoint (scrR s)
  dXq : (retR s).Disjoint (preR s)
  dXa : (retR s).Disjoint (argsR s)
  dKo : (stkR s).Disjoint (outR s)
  dKt : (stkR s).Disjoint (tapeR s)
  dKn : (stkR s).Disjoint (nR s)
  dKe : (stkR s).Disjoint (eR s)
  dKm : (stkR s).Disjoint (msgR s)
  dKr : (stkR s).Disjoint (randR s)
  dKs : (stkR s).Disjoint (scrR s)
  dKq : (stkR s).Disjoint (preR s)
  dKa : (stkR s).Disjoint (argsR s)
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wT : (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64
  wN : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  wE : (s.gpr .r9).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wM : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wR : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wS : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  wQ : (stackArg s 7).toNat + (stackArg s 8).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .r8).toNat
  k2 : (s.gpr .r8).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .r8).toNat
  L1 : 1 ≤ (stackArg s 0).toNat
  L2 : (stackArg s 0).toNat ≤ (s.gpr .r8).toNat
  hml : (stackArg s 2).toNat + 11 ≤ (s.gpr .r8).toNat
  hrl : (stackArg s 4).toNat ≤ Spec.RsaPkcs1Enc.padEntropy ((s.gpr .r8).toNat - (stackArg s 2).toNat - 3)
  hsl : Spec.Rsa.publicScratchWords (s.gpr .r8).toNat ≤ (stackArg s 6).toNat
  hql : (stackArg s 8).toNat = Spec.Rsa.precomputedWords (s.gpr .r8).toNat

theorem pre_of {s : State} (h : (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s) : RPre s := by
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig,
    abi, argRegs, stackArgs_nine, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOt, dOn, dOe, dOm, dOr, dOs, dOq, dOa, dTn, dTe, dTm, dTr, dTs, dTq, dTa,
    dNs, dEs, dMs, dRs, dSq, dSa, dXo, dXt, dXn, dXe, dXm, dXr, dXs, dXq, dXa,
    dKo, dKt, dKn, dKe, dKm, dKr, dKs, dKq, dKa, wO, wT, wN, wE, wM, wR, wS, wQ,
    ⟨k1, k2⟩, hsi, L1, L2, hml, hrl, hsl, hql⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOt, dOn, dOe, dOm, dOr, dOs, dOq, dOa, dTn, dTe, dTm, dTr, dTs, dTq, dTa,
    dNs, dEs, dMs, dRs, dSq, dSa, dXo, dXt, dXn, dXe, dXm, dXr, dXs, dXq, dXa,
    dKo, dKt, dKn, dKe, dKm, dKr, dKs, dKq, dKa, wO, wT, wN, wE, wM, wR, wS, wQ,
    k1, k2, hsi, L1, L2, hml, hrl, hsl, hql⟩

/-! ## The values -/

def kOf (s : State) : Nat := (s.gpr .r8).toNat
def psLen (s : State) : Nat := kOf s - (stackArg s 2).toNat - 3
def nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (kOf s)
def eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (stackArg s 0).toNat
def msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
def randB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat
def preW (s : State) : List (BitVec 64) := Spec.Rsa.wordsAt s.mem (stackArg s 7) (stackArg s 8).toNat

theorem RPre.ps {s : State} (hp : RPre s) : 8 ≤ psLen s ∧ psLen s + (stackArg s 2).toNat + 3 = kOf s ∧
    psLen s ≤ 1021 := by
  have := hp.hml; have := hp.k2; unfold psLen kOf; omega

theorem RPre.randLen {s : State} (hp : RPre s) : (stackArg s 4).toNat ≤ psLen s + 128 := hp.hrl

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

theorem fb_eq (s : State) : fb s = off (s.gpr .rsp - BitVec.ofNat 64 rndStack) (8 + encStack) :=
  Offset.sub_ofNat_eq _ (by decide)

theorem fb_toNat {s : State} (hp : RPre s) : (fb s).toNat + frameBytes + 8 + 72 ≤ 2 ^ 64 ∧
    (fb s).toNat + frameBytes = (s.gpr .rsp).toNat ∧ 8 + encStack ≤ (fb s).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]
  unfold rndStack frameBytes encStack Impl.RsaPkcs1Enc.X86_64.Encrypt.frameBytes at *; omega

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold rndStack frameBytes; omega)

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

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega]

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem ea_arg {t : State} {s : State} (h : t.gpr .rsp = fb s) (j : Nat) :
    t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

theorem arg_in {s : State} (hp : RPre s) {rd : List Region} (hrd : rd = s.rd) (wr : List Region) {j : Nat}
    (hj : j < 9) : InRegions (rd ++ wr) (stackArgAddr s j) 8 := by
  rw [hrd, hp.hrd]
  refine ⟨argsR s, by simp, ?_⟩
  rw [argsR, stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd

/-!
## The first block

The slots (`Slots`), and the scan's registers (`setup_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack allocState_gpr allocState_mem)

/-- The slots of the frame, in the memory `m`. -/
structure Slots (s : State) (m : Mem) : Prop where
  sOut : word m (fb s) oOut = s.gpr .rdi
  sTape : word m (fb s) oTape = s.gpr .rdx
  sN : word m (fb s) oN = s.gpr .rcx
  sK : word m (fb s) oK = s.gpr .r8
  sE : word m (fb s) oE = s.gpr .r9
  sPs : word m (fb s) oPs = BitVec.ofNat 64 (psLen s)

/-- In the frame, after the first block: the frame and its slots. -/
structure InFrame (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  out : Outside (fb s) 0 frameBytes s.mem t.mem
  slots : Slots s t.mem

theorem psLen_bv {s : State} (hp : RPre s) :
    s.gpr .r8 - stackArg s 2 - 3 = BitVec.ofNat 64 (psLen s) := by
  have := hp.hml
  rw [show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, psLen, kOf]
  omega

theorem readArg (s : State) (j : Nat) : s.mem.readW (stackArgAddr s j) 64 = stackArg s j := rfl

theorem off_buf (s : State) :
    s.gpr .rsp - BitVec.ofNat 64 frameBytes + BitVec.signExtend 64 (BitVec.ofNat 32 oBuf) =
      off (fb s) oBuf := by
  rw [sx_ofNat (show oBuf < 2 ^ 31 by decide)]

/-- The memory after the first block. -/
def setupMem (s : State) : Mem :=
  (((((s.mem.writeW (off (fb s) oOut) (s.gpr .rdi)).writeW (off (fb s) oTape) (s.gpr .rdx)).writeW
    (off (fb s) oN) (s.gpr .rcx)).writeW (off (fb s) oK) (s.gpr .r8)).writeW (off (fb s) oE) (s.gpr .r9)).writeW
    (off (fb s) oPs) (BitVec.ofNat 64 (psLen s))

theorem setup_run {s : State} (hp : RPre s) : WP isa (.block setup) (allocState frameBytes s) fun t =>
    t.mem = setupMem s ∧ t.gpr .rsi = stackArg s 3 ∧ t.gpr .r11 = stackArg s 4 ∧
      t.gpr .rdi = off (fb s) oBuf ∧ t.gpr .rcx = 0 ∧ t.gpr .rdx = 0 ∧
      t.zf = some (stackArg s 4 == 0) ∧
      Keep [.rax, .rsi, .r11, .rdi, .rcx, .rdx] (allocState frameBytes s) t := by
  have hF := fb_toNat hp
  have hsp : (allocState frameBytes s).gpr .rsp = fb s := rfl
  have hs : Scr (allocState frameBytes s) (fb s) frameBytes :=
    Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  have hrd : (allocState frameBytes s).rd = s.rd := rfl
  have hps := psLen_bv hp
  refine WP.mono (WP.keep [.rax, .rsi, .r11, .rdi, .rcx, .rdx] (c := .block setup) (Q := fun t =>
    t.mem = setupMem s ∧ t.gpr .rsi = stackArg s 3 ∧ t.gpr .r11 = stackArg s 4 ∧
      t.gpr .rdi = off (fb s) oBuf ∧ t.gpr .rcx = 0 ∧ t.gpr .rdx = 0 ∧
      t.zf = some (stackArg s 4 == 0)) ?_ rfl)
    fun t ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, k⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, k⟩
  xrun [setup, ea_arg (s := s), ea_sp, hsp, arg_in hp hrd _ (show 2 < 9 by decide),
    arg_in hp hrd _ (show 3 < 9 by decide), arg_in hp hrd _ (show 4 < 9 by decide),
    hs.st (d := oOut) (by decide), hs.st (d := oTape) (by decide), hs.st (d := oN) (by decide),
    hs.st (d := oK) (by decide), hs.st (d := oE) (by decide), hs.st (d := oPs) (by decide),
    allocState_gpr, allocState_mem, readArg, hps, off_buf, BitVec.and_self]
  simp only [setupMem, off]

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd

/-!
## The scan

After `i` octets of the tape `randB s`, the scan has kept their nonzero
octets, `nz (take i)`, at the start of `PS` (`At`); it goes on while it has
kept fewer than `psLen s` and has octets left (`step_ok`), and ends with
`PS` full, the padding string of `nonzeroPrefix`, or with the tape read
(`scan_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (byte byte_wb byte_wb_self trunc_zext zext_toNat ea_bx bytesAt_succ)
open VG.Proof.RsaPkcs1Enc (nz nz_zero nz_ne nz_length_le)

/-- The kept octets after `i` octets of the tape. -/
abbrev kept (s : State) (i : Nat) : List Byte := nz ((randB s).take i)

/-- The state before the scan: the frame and the scan's registers. -/
structure Before (s t : State) : Prop extends InFrame s t where
  rsi : t.gpr .rsi = stackArg s 3
  r11 : t.gpr .r11 = stackArg s 4
  rdi : t.gpr .rdi = off (fb s) oBuf

/-- After `i` octets of the tape, from the state `t₀` before the scan. -/
structure At (s t₀ : State) (i : Nat) (u : State) : Prop where
  keep : Keep [.rax, .rcx, .rdx] t₀ u
  out : Outside (fb s) oBuf (kept s i).length t₀.mem u.mem
  buf : ∀ j < (kept s i).length, byte u.mem (fb s) (oBuf + j) = (kept s i).getD j 0
  rcx : u.gpr .rcx = BitVec.ofNat 64 i
  rdx : u.gpr .rdx = BitVec.ofNat 64 (kept s i).length
  hi : i ≤ (stackArg s 4).toNat
  hc : (kept s i).length ≤ psLen s

theorem randB_getD {s : State} {i : Nat} (hi : i < (stackArg s 4).toNat) :
    (randB s).getD i 0 = s.mem (stackArg s 3 + BitVec.ofNat 64 i) := by
  simp [randB, Spec.Rsa.bytesAt, hi]

theorem randB_length (s : State) : (randB s).length = (stackArg s 4).toNat := by
  simp [randB, Spec.Rsa.bytesAt]

theorem take_succ_eq {s : State} {i : Nat} (hi : i < (stackArg s 4).toNat) :
    (randB s).take (i + 1) = (randB s).take i ++ [(randB s).getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by rw [randB_length]; exact hi)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [randB_length]; exact hi)]

theorem kept_succ {s : State} {i : Nat} (hi : i < (stackArg s 4).toNat) :
    kept s (i + 1) = if (randB s).getD i 0 = 0 then kept s i else kept s i ++ [(randB s).getD i 0] := by
  simp only [kept, take_succ_eq hi]
  split
  · rename_i h; rw [h, nz_zero]
  · rename_i h; exact nz_ne h _

theorem getD_append_lt {l : List Byte} {j : Nat} (b : Byte) (h : j < l.length) :
    (l ++ [b]).getD j 0 = l.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_eq (l : List Byte) (b : Byte) : (l ++ [b]).getD l.length 0 = b := by
  simp [List.getD_eq_getElem?_getD]

/-- The `zf` of `test` on a zero-extended byte. -/
theorem test_byte : ∀ b : Byte,
    (BitVec.setWidth 64 b &&& BitVec.setWidth 64 b == 0) = decide (b = 0) := by decide

/-- `[b + i]` for `b = p` and `i = j`. -/
theorem ea_bx0 {t : State} {b i : Reg} {p : Addr} {j : Nat} (hb : t.gpr b = p)
    (hi : t.gpr i = BitVec.ofNat 64 j) : t.ea (bx b i) = off p j := by
  simp only [State.ea, bx, hb, hi, BitVec.mul_one, off]
  simp

theorem eval_ne {v : State} {b : Bool} (h : v.zf = some b) : isa.eval .ne v = some (!b) := by
  show v.zf.map (!·) = _; rw [h]; rfl

theorem eval_e {v : State} {b : Bool} (h : v.zf = some b) : isa.eval .e v = some b := h

theorem ofNat_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  rw [ofNat_sub_beq ha hb]

theorem word0_wb' (m : Mem) (base : Addr) {d d' : Nat} (v : Byte) (h : d + 8 ≤ d')
    (hd' : d' < 2 ^ 64) : (m.writeW (off base d') v).readW (off base d) 64 = m.readW (off base d) 64 :=
  VG.Proof.RsaPkcs1Enc.X86_64.word_wb m base v (.inl h) (by omega) hd'

/-- Whether to go on, with `c` octets kept after `i` octets: ZF set if `PS`
is full or the tape has ended. -/
theorem more_ok {s v : State} {i c : Nat} (hsp : v.gpr .rsp = fb s)
    (hps : InRegions (v.rd ++ v.wr) (off (fb s) oPs) 8)
    (hpsv : v.mem.readW (off (fb s) oPs) 64 = BitVec.ofNat 64 (psLen s))
    (h11 : v.gpr .r11 = BitVec.ofNat 64 (stackArg s 4).toNat) (hcx : v.gpr .rcx = BitVec.ofNat 64 i)
    (hdx : v.gpr .rdx = BitVec.ofNat 64 c) (hcl : c < 2 ^ 64) (hpl : psLen s < 2 ^ 64)
    (hil : i < 2 ^ 64) (hll : (stackArg s 4).toNat < 2 ^ 64) :
    WP isa more v fun x => x.mem = v.mem ∧ Keep [.rax, .rdx] v x ∧ x.gpr .rdx = v.gpr .rdx ∧
      x.zf = some (decide (c = psLen s ∨ i = (stackArg s 4).toNat)) := by
  refine WP.seq (WP.mono (WP.keep [.rdx] (c := .block [.alu .cmp .rdx (.mem (sp oPs))]) (Q := fun w =>
      w.mem = v.mem ∧ w.zf = some (decide (c = psLen s)) ∧ w.gpr .rdx = v.gpr .rdx) (by
    xrun [ea_sp, hsp, show (fb s + BitVec.ofNat 64 oPs) = off (fb s) oPs from rfl, hps, hpsv, hdx,
      ofNat_beq hcl hpl]) (by decide)) fun w ⟨⟨hwm, hwz, hwd⟩, kw⟩ => ?_)
  by_cases he : c = psLen s
  · refine WP.ite true (by rw [eval_e hwz, decide_eq_true he]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (WP.keep [.rax] (c := .block [.mov32 .rax (.imm 0), .alu .test .rax (.reg .rax)])
      (Q := fun x => x.mem = w.mem ∧ x.zf = some true) (by xrun []) rfl) fun x ⟨⟨hxm, hxz⟩, kx⟩ => ?_
    refine ⟨hxm.trans hwm, (kw.trans kx).mono (by decide), (kx.gpr (by decide)).trans hwd, ?_⟩
    rw [hxz]; simp [he]
  · refine WP.ite false (by rw [eval_e hwz, decide_eq_false he]) (fun h => absurd h (by decide)) fun _ => ?_
    refine WP.mono (WP.keep [.rax] (c := .block [.mov .rax (.reg .r11), .alu .sub .rax (.reg .rcx)])
      (Q := fun x => x.mem = w.mem ∧ x.zf = some (decide (i = (stackArg s 4).toNat))) (by
        xrun [(kw.gpr (show Reg.r11 ∉ [Reg.rdx] by decide)).trans h11,
          (kw.gpr (show Reg.rcx ∉ [Reg.rdx] by decide)).trans hcx, ofNat_beq hll hil]
        simp only [eq_comm]) rfl) fun x ⟨⟨hxm, hxz⟩, kx⟩ => ?_
    refine ⟨hxm.trans hwm, (kw.trans kx).mono (by decide), (kx.gpr (by decide)).trans hwd, ?_⟩
    rw [hxz]; simp [he]

/-- One octet of the scan, with fewer than `psLen` octets kept and octets
left: after it, `At` for `i + 1`, and ZF set if `PS` is full or the tape has
ended. -/
theorem step_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hi : i < (stackArg s 4).toNat) (hc : (kept s i).length < psLen s) :
    WP isa step u fun u' => At s t₀ (i + 1) u' ∧
      u'.zf = some (decide ((kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 4).toNat)) := by
  have hF := fb_toNat hp
  have hP := hp.ps
  have hrl := hp.randLen
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [hI.keep.2.2, hb.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hsp : u.gpr .rsp = fb s := (hI.keep.gpr (by decide)).trans hb.rsp
  have hsi : u.gpr .rsi = stackArg s 3 := (hI.keep.gpr (by decide)).trans hb.rsi
  have h11 : u.gpr .r11 = BitVec.ofNat 64 (stackArg s 4).toNat :=
    by rw [(hI.keep.gpr (by decide)).trans hb.r11]; simp
  have hdi : u.gpr .rdi = off (fb s) oBuf := (hI.keep.gpr (by decide)).trans hb.rdi
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s 3) i) 1 := by
    rw [hI.keep.2.1, hb.rd, hp.hrd]
    exact ⟨randR s, by simp, Offset.contains_base _ (by omega) (by have := hp.wR; omega)⟩
  have hval : u.mem (off (stackArg s 3) i) = (randB s).getD i 0 := by
    rw [randB_getD hi]
    have hd : (stkR s).Disjoint (randR s) := hp.dKr
    have ho : frameBytes ≤ ofs (fb s) (off (stackArg s 3) i) := outside_frame s fun hc =>
      hd _ hc (Offset.contains_base _ (by omega) (by have := hp.wR; omega))
    rw [hI.out _ (.inr (by unfold frameBytes oBuf at *; omega)), hb.out _ (.inr ho)]
  have hps : InRegions (u.rd ++ u.wr) (off (fb s) oPs) 8 := hs.ld (by decide)
  have hpsv : u.mem.readW (off (fb s) oPs) 64 = BitVec.ofNat 64 (psLen s) := by
    have := hb.slots.sPs
    rw [← this]
    exact (hI.out.word (.inl (by unfold oPs oBuf; omega)) (by unfold frameBytes oPs at *; omega))
  have hcx : u.gpr .rcx = BitVec.ofNat 64 i := hI.rcx
  have hdx : u.gpr .rdx = BitVec.ofNat 64 (kept s i).length := hI.rdx
  have hst : InRegions u.wr (off (fb s) (oBuf + (kept s i).length)) 1 :=
    hs.st8 (by unfold frameBytes oBuf; omega)
  -- the load
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx] (c := .block load) (Q := fun v =>
      v.mem = u.mem ∧ v.gpr .rax = BitVec.setWidth 64 ((randB s).getD i 0) ∧
      v.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧ v.zf = some (decide ((randB s).getD i 0 = 0))) (by
    xrun [load, ea_bx0 (j := i) (p := stackArg s 3) hsi hcx, hsi, hcx, hin, hval, ofNat_add_one, test_byte])
    rfl) fun v ⟨⟨hvm, hva, hvc, hvz⟩, kv⟩ => ?_)
  have g : ∀ {r : Reg}, r ∉ [Reg.rax, .rcx] → v.gpr r = u.gpr r := fun h => kv.gpr h
  by_cases hz : (randB s).getD i 0 = 0
  · -- a zero octet: rejected
    have hk : kept s (i + 1) = kept s i := by rw [kept_succ hi, ite_eq_left hz]
    refine WP.seq (WP.ite false (by rw [eval_ne hvz, decide_eq_true hz]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil ?_)
    refine WP.mono (more_ok (i := i + 1) (c := (kept s i).length) ((g (by decide)).trans hsp)
      (by rw [kv.2.1, kv.2.2]; exact hps) (by rw [hvm]; exact hpsv) ((g (by decide)).trans h11) hvc
      ((g (by decide)).trans hdx) (by omega) (by omega) (by omega) (by omega)) fun x ⟨hxm, kx, hxd, hxz⟩ => ?_
    refine ⟨⟨((hI.keep.trans (kv.mono (rs' := [.rax, .rcx, .rdx]) (by decide))).trans kx).mono (by decide),
      ?_, ?_, ?_, ?_, by omega, by rw [hk]; omega⟩, ?_⟩
    · rw [hk, hxm, hvm]; exact hI.out
    · intro j hj; rw [hk, hxm, hvm]; rw [hk] at hj; exact hI.buf j hj
    · rw [(kx.gpr (by decide)).trans hvc]
    · rw [hxd, (g (by decide)).trans hdx, hk]
    · rw [hxz, hk]
  · -- a nonzero octet: kept
    have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
    refine WP.seq (WP.ite true (by rw [eval_ne hvz, decide_eq_false hz]; rfl)
      (fun _ => WP.mono (WP.keep [.rdx] (c := .block keep) (Q := fun w =>
        w.mem = v.mem.writeW (off (fb s) (oBuf + (kept s i).length)) ((randB s).getD i 0) ∧
        w.gpr .rdx = BitVec.ofNat 64 ((kept s i).length + 1)) (by
          xrun [keep, ea_bx0 (j := (kept s i).length) (p := off (fb s) oBuf) ((g (by decide)).trans hdi)
            ((g (by decide)).trans hdx), (g (by decide)).trans hdi, (g (by decide)).trans hdx, hva,
            kv.2.2, hst, trunc_zext, off_off, ofNat_add_one]) (by decide)) fun w ⟨⟨hwm, hwd⟩, kw⟩ => ?_)
      (fun h => absurd h (by decide)))
    have gw : ∀ {r : Reg}, r ∉ [Reg.rdx] → w.gpr r = v.gpr r := fun h => kw.gpr h
    have hl : (kept s i).length + 1 = (kept s (i + 1)).length := by rw [hk]; simp
    refine WP.mono (more_ok (i := i + 1) (c := (kept s i).length + 1)
      ((gw (by decide)).trans ((g (by decide)).trans hsp))
      (by rw [kw.2.1, kw.2.2, kv.2.1, kv.2.2]; exact hps)
      (by rw [hwm, word0_wb' _ _ _ (by unfold oPs oBuf; omega) (by unfold frameBytes oBuf at *; omega), hvm];
          exact hpsv)
      ((gw (by decide)).trans ((g (by decide)).trans h11)) ((gw (by decide)).trans hvc)
      hwd (by omega) (by omega) (by omega) (by omega)) fun x ⟨hxm, kx, hxd, hxz⟩ => ?_
    refine ⟨⟨(((hI.keep.trans (kv.mono (rs' := [.rax, .rcx, .rdx]) (by decide))).trans
      (kw.mono (rs' := [.rax, .rcx, .rdx]) (by decide))).trans kx).mono (by decide),
      ?_, ?_, ?_, ?_, by omega, by omega⟩, ?_⟩
    · rw [← hl, hxm, hwm, hvm]
      exact Outside.wb (Outside.mono hI.out (by omega) (by omega)) _ (by omega) (by omega)
        (by unfold oBuf; omega)
    · intro j hj
      rw [hxm, hwm, hvm, hk]
      rw [← hl] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [byte_wb _ _ _ (by omega) (by unfold oBuf; omega) (by unfold oBuf; omega), getD_append_lt _ hj]
        exact hI.buf j hj
      · rw [byte_wb_self, getD_append_eq]
    · rw [(kx.gpr (by decide)).trans ((gw (by decide)).trans hvc)]
    · rw [hxd, hwd, hl]
    · rw [hxz, hl]

/-- After the load of octet `i`. -/
def LoadPt (s t₀ : State) (i : Nat) (v : State) : Prop :=
  ∃ u, At s t₀ i u ∧ v.mem = u.mem ∧ v.gpr .rax = BitVec.setWidth 64 ((randB s).getD i 0) ∧
    v.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧ v.zf = some (decide ((randB s).getD i 0 = 0)) ∧
    Keep [.rax, .rcx] u v

theorem load_ok {s t₀ u : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hI : At s t₀ i u)
    (hi : i < (stackArg s 4).toNat) (hc : (kept s i).length < psLen s) :
    WP isa (.block load) u (LoadPt s t₀ i) := by
  have hF := fb_toNat hp
  have hP := hp.ps
  have hrl := hp.randLen
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [hI.keep.2.2, hb.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hsp : u.gpr .rsp = fb s := (hI.keep.gpr (by decide)).trans hb.rsp
  have hsi : u.gpr .rsi = stackArg s 3 := (hI.keep.gpr (by decide)).trans hb.rsi
  have h11 : u.gpr .r11 = BitVec.ofNat 64 (stackArg s 4).toNat :=
    by rw [(hI.keep.gpr (by decide)).trans hb.r11]; simp
  have hdi : u.gpr .rdi = off (fb s) oBuf := (hI.keep.gpr (by decide)).trans hb.rdi
  have hin : InRegions (u.rd ++ u.wr) (off (stackArg s 3) i) 1 := by
    rw [hI.keep.2.1, hb.rd, hp.hrd]
    exact ⟨randR s, by simp, Offset.contains_base _ (by omega) (by have := hp.wR; omega)⟩
  have hval : u.mem (off (stackArg s 3) i) = (randB s).getD i 0 := by
    rw [randB_getD hi]
    have hd : (stkR s).Disjoint (randR s) := hp.dKr
    have ho : frameBytes ≤ ofs (fb s) (off (stackArg s 3) i) := outside_frame s fun hc =>
      hd _ hc (Offset.contains_base _ (by omega) (by have := hp.wR; omega))
    rw [hI.out _ (.inr (by unfold frameBytes oBuf at *; omega)), hb.out _ (.inr ho)]
  have hps : InRegions (u.rd ++ u.wr) (off (fb s) oPs) 8 := hs.ld (by decide)
  have hpsv : u.mem.readW (off (fb s) oPs) 64 = BitVec.ofNat 64 (psLen s) := by
    have := hb.slots.sPs
    rw [← this]
    exact (hI.out.word (.inl (by unfold oPs oBuf; omega)) (by unfold frameBytes oPs at *; omega))
  have hcx : u.gpr .rcx = BitVec.ofNat 64 i := hI.rcx
  have hdx : u.gpr .rdx = BitVec.ofNat 64 (kept s i).length := hI.rdx
  have hst : InRegions u.wr (off (fb s) (oBuf + (kept s i).length)) 1 :=
    hs.st8 (by unfold frameBytes oBuf; omega)
  refine WP.mono (WP.keep [.rax, .rcx] (c := .block load) (Q := fun v =>
      v.mem = u.mem ∧ v.gpr .rax = BitVec.setWidth 64 ((randB s).getD i 0) ∧
      v.gpr .rcx = BitVec.ofNat 64 (i + 1) ∧ v.zf = some (decide ((randB s).getD i 0 = 0))) (by
    xrun [load, ea_bx0 (j := i) (p := stackArg s 3) hsi hcx, hsi, hcx, hin, hval, ofNat_add_one, test_byte])
    rfl) fun v ⟨⟨hvm, hva, hvc, hvz⟩, kv⟩ => ⟨u, hI, hvm, hva, hvc, hvz, kv⟩

theorem branch_ok {s t₀ v : State} (hp : RPre s) (hb : Before s t₀) {i : Nat} (hL : LoadPt s t₀ i v)
    (hi : i < (stackArg s 4).toNat) (hc : (kept s i).length < psLen s) :
    WP isa (.ite .ne (.block keep) (.block [])) v (At s t₀ (i + 1)) := by
  obtain ⟨u, hI, hvm, hva, hvc, hvz, kv⟩ := hL
  have hF := fb_toNat hp
  have hP := hp.ps
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [hI.keep.2.2, hb.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hdi : u.gpr .rdi = off (fb s) oBuf := (hI.keep.gpr (by decide)).trans hb.rdi
  have hdx : u.gpr .rdx = BitVec.ofNat 64 (kept s i).length := hI.rdx
  have hst : InRegions u.wr (off (fb s) (oBuf + (kept s i).length)) 1 :=
    hs.st8 (by unfold frameBytes oBuf; omega)
  have g : ∀ {r : Reg}, r ∉ [Reg.rax, .rcx] → v.gpr r = u.gpr r := fun h => kv.gpr h
  by_cases hz : (randB s).getD i 0 = 0
  · have hk : kept s (i + 1) = kept s i := by rw [kept_succ hi, ite_eq_left hz]
    refine WP.ite false (by rw [eval_ne hvz, decide_eq_true hz]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil ?_
    refine ⟨(hI.keep.trans (kv.mono (rs' := [.rax, .rcx, .rdx]) (by decide))).mono (by decide),
      ?_, ?_, hvc, ?_, by omega, by rw [hk]; omega⟩
    · rw [hk, hvm]; exact hI.out
    · intro j hj; rw [hk, hvm]; rw [hk] at hj; exact hI.buf j hj
    · rw [(g (by decide)).trans hdx, hk]
  · have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
    have hl : (kept s i).length + 1 = (kept s (i + 1)).length := by rw [hk]; simp
    refine WP.ite true (by rw [eval_ne hvz, decide_eq_false hz]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (WP.keep [.rdx] (c := .block keep) (Q := fun w =>
        w.mem = v.mem.writeW (off (fb s) (oBuf + (kept s i).length)) ((randB s).getD i 0) ∧
        w.gpr .rdx = BitVec.ofNat 64 ((kept s i).length + 1)) (by
          xrun [keep, ea_bx0 (j := (kept s i).length) (p := off (fb s) oBuf) ((g (by decide)).trans hdi)
            ((g (by decide)).trans hdx), (g (by decide)).trans hdi, (g (by decide)).trans hdx, hva,
            kv.2.2, hst, trunc_zext, off_off, ofNat_add_one]) (by decide)) fun w ⟨⟨hwm, hwd⟩, kw⟩ => ?_
    refine ⟨((hI.keep.trans (kv.mono (rs' := [.rax, .rcx, .rdx]) (by decide))).trans
      (kw.mono (rs' := [.rax, .rcx, .rdx]) (by decide))).mono (by decide), ?_, ?_, ?_, ?_, by omega, by omega⟩
    · rw [← hl, hwm, hvm]
      exact Outside.wb (Outside.mono hI.out (by omega) (by omega)) _ (by omega) (by omega)
        (by unfold oBuf; omega)
    · intro j hj
      rw [hwm, hvm, hk]
      rw [← hl] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [byte_wb _ _ _ (by omega) (by unfold oBuf; omega) (by unfold oBuf; omega), getD_append_lt _ hj]
        exact hI.buf j hj
      · rw [byte_wb_self, getD_append_eq]
    · rw [(kw.gpr (by decide)).trans hvc]
    · rw [hwd, hl]

/-- `PS` filled at octet `i`: the padding string of `nonzeroPrefix`. -/
theorem prefix_of_fill {s : State} {i : Nat} (hi : i < (stackArg s 4).toNat)
    (hc : (kept s i).length < psLen s) (hf : (kept s (i + 1)).length = psLen s) :
    Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s (i + 1), i + 1) := by
  have hz : (randB s).getD i 0 ≠ 0 := by
    intro hz; rw [kept_succ hi, ite_eq_left hz] at hf; omega
  have hk : kept s (i + 1) = kept s i ++ [(randB s).getD i 0] := by rw [kept_succ hi, ite_eq_right hz]
  have hl : i < (randB s).length := by rw [randB_length]; exact hi
  have e : randB s = (randB s).take i ++ (randB s).getD i 0 :: (randB s).drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i (randB s)]
    congr 1
    rw [List.drop_eq_getElem_cons hl]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  have hlen : ((randB s).take i).length = i := by rw [List.length_take]; omega
  rw [e, VG.Proof.RsaPkcs1Enc.nonzeroPrefix_last _ hz (by rw [hk] at hf; simpa using hf), hk, hlen]

/-- What the scan leaves: after `i` octets, `PS` full with the padding
string, or the tape read with fewer nonzero octets. -/
def Done (s t₀ : State) (u : State) : Prop :=
  ∃ i, At s t₀ i u ∧ (((kept s i).length = psLen s ∧
      Spec.RsaPkcs1Enc.nonzeroPrefix (psLen s) (randB s) = some (kept s i, i)) ∨
    (i = (stackArg s 4).toNat ∧ (kept s i).length < psLen s))

theorem kept_zero (s : State) : kept s 0 = [] := by simp [kept, VG.Proof.RsaPkcs1Enc.nz_nil]

/-- The loop's invariant, with the octets left as its measure. -/
def LoopInv (s t₀ : State) (n : Nat) (u : State) : Prop :=
  ∃ i, n = (stackArg s 4).toNat - i ∧ At s t₀ i u ∧ i < (stackArg s 4).toNat ∧ (kept s i).length < psLen s

theorem scan_ok {s t₀ : State} (hp : RPre s) (hb : Before s t₀) (hcx : t₀.gpr .rcx = 0)
    (hdx : t₀.gpr .rdx = 0) (hz : t₀.zf = some (stackArg s 4 == 0)) :
    WP isa scan t₀ (Done s t₀) := by
  have hP := hp.ps
  have hrl := hp.randLen
  have h0 : At s t₀ 0 t₀ := ⟨Keep.refl _ _, Outside.refl _ _ _ _, fun j hj => absurd hj (by simp [kept_zero]),
    hcx, by rw [hdx, kept_zero]; rfl, Nat.zero_le _, by rw [kept_zero]; simp⟩
  by_cases hl : stackArg s 4 = 0
  · refine WP.ite false (by rw [eval_ne hz, hl]; rfl) (fun h => absurd h (by decide)) fun _ => WP.block_nil ?_
    have hl' : (stackArg s 4).toNat = 0 := by rw [hl]; rfl
    exact ⟨0, h0, .inr ⟨hl'.symm, by rw [kept_zero]; simp; omega⟩⟩
  have hl' : 0 < (stackArg s 4).toNat := by
    rcases Nat.eq_zero_or_pos (stackArg s 4).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by rw [h]; rfl)) hl
    · exact h
  refine WP.ite true (by rw [eval_ne hz, beq_false_of_ne hl]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
  have hinit : LoopInv s t₀ ((stackArg s 4).toNat - 0) t₀ := ⟨0, rfl, h0, hl', by rw [kept_zero]; simp; omega⟩
  refine WP.loop (LoopInv s t₀) ?_ _ _ hinit
  rintro n u ⟨i, rfl, hI, hi, hc⟩
  refine WP.mono (step_ok hp hb hI hi hc) fun u' ⟨hI', hz'⟩ => ?_
  by_cases hstop : (kept s (i + 1)).length = psLen s ∨ i + 1 = (stackArg s 4).toNat
  · refine .inl ⟨by rw [eval_ne hz', decide_eq_true hstop]; rfl, ⟨i + 1, hI', ?_⟩⟩
    by_cases hf : (kept s (i + 1)).length = psLen s
    · exact .inl ⟨hf, prefix_of_fill hi hc hf⟩
    · exact .inr ⟨hstop.resolve_left hf, by have := hI'.hc; omega⟩
  · refine .inr ⟨by rw [eval_ne hz', decide_eq_false hstop]; rfl, _, by omega, i + 1, rfl, hI', by omega,
      by have := hI'.hc; omega⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd

/-!
## The call's arguments

With `PS` full (`Ready`): `tape` is `[i, 0]`, and the arguments of
`vg_rsa_pkcs1_encrypt_precomputed` in registers and at `rsp` (`callArgs_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack byte off_zero)

/-- `PS` full after `i` octets, its octets `ps`, before the call's arguments. -/
structure Ready (s t : State) (i : Nat) (ps : List Byte) : Prop extends InFrame s t where
  rcx : t.gpr .rcx = BitVec.ofNat 64 i
  rdi : t.gpr .rdi = off (fb s) oBuf
  len : ps.length = psLen s
  buf : Spec.Rsa.bytesAt t.mem (off (fb s) oBuf) (psLen s) = ps
  used : i ≤ (stackArg s 4).toNat

/-- The tape after the call's arguments: `[i, 0]`. -/
def tapeMem (s : State) (m : Mem) (i : Nat) : Mem :=
  (m.writeW (s.gpr .rdx) (BitVec.ofNat 64 i)).writeW (s.gpr .rdx + BitVec.ofNat 64 8) (0 : BitVec 64)

/-- The callee's stack arguments. -/
def callArg (s : State) : Nat → Addr
  | 0 => stackArg s 1
  | 1 => stackArg s 2
  | 2 => off (fb s) oBuf
  | 3 => BitVec.ofNat 64 (psLen s)
  | 4 => stackArg s 5
  | 5 => stackArg s 6
  | 6 => stackArg s 7
  | _ => stackArg s 8

/-- The callee's stack arguments, at `fb`. -/
def argR (s : State) : Region := ⟨fb s, 64⟩

/-- After the call's arguments. -/
structure Args (s t : State) (i : Nat) (ps : List Byte) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  fr : Frame [stkR s, tapeR s] s.mem t.mem
  slots : Slots s t.mem
  args : ∀ j < 8, word t.mem (fb s) (8 * j) = callArg s j
  buf : Spec.Rsa.bytesAt t.mem (off (fb s) oBuf) (psLen s) = ps
  len : ps.length = psLen s
  tape0 : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 i
  tape1 : t.mem.readW (s.gpr .rdx + BitVec.ofNat 64 8) 64 = 0
  rdi : t.gpr .rdi = s.gpr .rdi
  rsi : t.gpr .rsi = s.gpr .r8
  rdx : t.gpr .rdx = s.gpr .rcx
  rcx : t.gpr .rcx = s.gpr .r8
  r8 : t.gpr .r8 = s.gpr .r9
  r9 : t.gpr .r9 = stackArg s 0

/-! ## Memory during the arguments -/

theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, tapeR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

theorem argR_sub (s : State) : Region.Sub (argR s) (stkR s) := by
  have := frame_sub s (d := 0) (n := 64) (by decide)
  simpa [off, argR] using this

/-- A slot is apart from the callee's stack arguments. -/
theorem slot_apart_args (s : State) (hp : RPre s) {d : Nat} (hd : 64 ≤ d) (hd' : d + 8 ≤ frameBytes) :
    (⟨off (fb s) d, 8⟩ : Region).Disjoint (argR s) := by
  have := fb_toNat hp
  exact (Offset.disjoint_base (fb s) (d := d) (n := 8) (k := 64) hd (by unfold frameBytes at *; omega))

/-- A part of the frame is apart from the tape. -/
theorem frame_apart_tape (s : State) (hp : RPre s) {d n : Nat} (h : d + n ≤ frameBytes) :
    (⟨off (fb s) d, n⟩ : Region).Disjoint (tapeR s) :=
  fun x h₁ h₂ => hp.dKt x (frame_sub s h x h₁) h₂

theorem off_contains_argR (s : State) (hp : RPre s) {d : Nat} (hd : d + 8 ≤ 64) :
    (argR s).Contains (off (fb s) d) 8 := by
  have := fb_toNat hp
  exact Offset.contains_base (fb s) (by omega) (by unfold frameBytes at *; omega)

/-- A store of a word to the callee's stack arguments. -/
theorem store_frame {s t u : State} (hp : RPre s) (ht : t.gpr .rsp = fb s)
    (htw : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hk : Keep [.rax] t u) (hf : Frame [argR s] t.mem u.mem)
    {r : Reg} {d : Nat} (hd8 : d + 8 ≤ 64) :
    WP isa (.block [.store (sp d) r]) u fun u' => Keep [.rax] t u' ∧ Frame [argR s] t.mem u'.mem ∧
      word u'.mem (fb s) d = u.gpr r ∧
      (∀ d', d' + 8 ≤ 64 → (d' + 8 ≤ d ∨ d + 8 ≤ d') → word u'.mem (fb s) d' = word u.mem (fb s) d') ∧
      u'.gpr .rax = u.gpr .rax := by
  have hF := fb_toNat hp
  have hsp : u.gpr .rsp = fb s := (hk.gpr (by decide)).trans ht
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [hk.2.2, htw]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  refine WP.mono (WP.keep [] (c := .block [.store (sp d) r]) (Q := fun u' =>
      u'.mem = u.mem.writeW (off (fb s) d) (u.gpr r)) (by
    xrun [ea_sp, hsp, show fb s + BitVec.ofNat 64 d = off (fb s) d from rfl, hs.st (d := d) (by unfold frameBytes; omega)]
    ) rfl) fun u' ⟨hm, k⟩ => ?_
  refine ⟨(hk.trans k).mono (by decide), ?_, by rw [hm]; exact word_writeW_self _ _ _ _, fun d' h1 h2 => ?_,
    k.gpr (by decide)⟩
  · rw [hm]; exact hf.writeW (List.mem_singleton_self _) _ (off_contains_argR s hp hd8)
  · rw [hm]; exact VG.Proof.RsaPkcs1Enc.X86_64.word_ww _ _ _ h2 (by omega) (by omega)

/-- A copy to the callee's stack arguments. -/
theorem copy_frame {s t u : State} (hp : RPre s) (ht : t.gpr .rsp = fb s)
    (htw : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hk : Keep [.rax] t u) (hf : Frame [argR s] t.mem u.mem)
    {src : MemOp} {a : Addr} {r : Region} (hea : u.ea src = a) (hin : InRegions (u.rd ++ u.wr) a 8)
    (hc : r.Contains a 8) (hd : r.Disjoint (argR s)) {d : Nat} (hd8 : d + 8 ≤ 64) :
    WP isa (.block (copyArg src d)) u fun u' => Keep [.rax] t u' ∧ Frame [argR s] t.mem u'.mem ∧
      word u'.mem (fb s) d = t.mem.readW a 64 ∧
      (∀ d', d' + 8 ≤ 64 → (d' + 8 ≤ d ∨ d + 8 ≤ d') → word u'.mem (fb s) d' = word u.mem (fb s) d') := by
  have hF := fb_toNat hp
  have hsp : u.gpr .rsp = fb s := (hk.gpr (by decide)).trans ht
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [hk.2.2, htw]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hv : u.mem.readW a 64 = t.mem.readW a 64 :=
    hf.readW hc (fun r' hr' => by rw [List.mem_singleton.mp hr']; exact hd) (by decide)
  refine WP.mono (WP.keep [.rax] (c := .block (copyArg src d)) (Q := fun u' =>
      u'.mem = u.mem.writeW (off (fb s) d) (t.mem.readW a 64)) (by
    xrun [copyArg, hea, hin, hv, ea_sp, hsp, show fb s + BitVec.ofNat 64 d = off (fb s) d from rfl,
      hs.st (d := d) (by unfold frameBytes; omega)]
    ) rfl) fun u' ⟨hm, k⟩ => ?_
  refine ⟨(hk.trans k).mono (by decide), ?_, by rw [hm]; exact word_writeW_self _ _ _ _, fun d' h1 h2 => ?_⟩
  · rw [hm]; exact hf.writeW (List.mem_singleton_self _) _ (off_contains_argR s hp hd8)
  · rw [hm]; exact VG.Proof.RsaPkcs1Enc.X86_64.word_ww _ _ _ h2 (by omega) (by omega)

theorem argsR_apart (s : State) (hp : RPre s) : (argsR s).Disjoint (argR s) := by
  have := fb_toNat hp
  rw [argsR, stackArgAddr_fb, argR]
  exact Offset.disjoint_base (fb s) (by unfold frameBytes; omega) (by unfold frameBytes at *; omega)

theorem arg_contains (s : State) {j : Nat} (hj : j < 9) : (argsR s).Contains (stackArgAddr s j) 8 := by
  rw [argsR, stackArgAddr_eq s j]
  exact Offset.contains_base _ (by omega) (by omega)

/-- What the stack arguments read, before them. -/
structure StackIn (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  rdi : t.gpr .rdi = off (fb s) oBuf
  args : ∀ j, j < 9 → t.mem.readW (stackArgAddr s j) 64 = stackArg s j
  ps : word t.mem (fb s) oPs = BitVec.ofNat 64 (psLen s)

theorem stackArgs_ok {s t : State} (hp : RPre s) (h : StackIn s t) :
    WP isa stackArgs t fun u => Keep [.rax] t u ∧ Frame [argR s] t.mem u.mem ∧
      ∀ j < 8, word u.mem (fb s) (8 * j) = callArg s j := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have argIn : ∀ {u : State}, Keep [.rax] t u → ∀ j, j < 9 → InRegions (u.rd ++ u.wr) (stackArgAddr s j) 8 :=
    fun hk j hj => by rw [hk.2.1, hk.2.2]; exact arg_in hp h.rd _ hj
  have argEa : ∀ {u : State}, Keep [.rax] t u → ∀ j, u.ea (arg j) = stackArgAddr s j :=
    fun hk j => ea_arg ((hk.gpr (by decide)).trans h.rsp) j
  have cp := fun {u : State} (hk : Keep [.rax] t u) (hf : Frame [argR s] t.mem u.mem) {d : Nat}
      (hd8 : d + 8 ≤ 64) (j : Nat) (hj : j < 9) =>
    copy_frame (src := arg j) hp h.rsp h.wr hk hf (argEa hk j) (argIn hk j hj) (arg_contains s hj)
      (argsR_apart s hp) hd8
  refine WP.seq (WP.mono (cp (Keep.refl _ _) (Frame.refl _ _) (d := 0) (by decide) 1 (by decide))
    fun u₀ ⟨k₀, f₀, w₀, _⟩ => ?_)
  refine WP.seq (WP.mono (cp k₀ f₀ (d := 8) (by decide) 2 (by decide)) fun u₁ ⟨k₁, f₁, w₁, p₁⟩ => ?_)
  refine WP.seq (WP.mono (store_frame (r := .rdi) hp h.rsp h.wr k₁ f₁ (d := 16) (by decide))
    fun u₂ ⟨k₂, f₂, w₂, p₂, _⟩ => ?_)
  have hps : u₂.ea (sp oPs) = off (fb s) oPs := by
    rw [ea_sp, (k₂.gpr (by decide)).trans h.rsp]
  refine WP.seq (WP.mono (copy_frame (src := sp oPs) (r := ⟨off (fb s) oPs, 8⟩) hp h.rsp h.wr k₂ f₂ hps
      (by rw [k₂.2.1, k₂.2.2]; exact hs.ld (by decide)) (Region.contains_self _ _)
      (slot_apart_args s hp (by decide) (by decide)) (d := 24) (by decide)) fun u₃ ⟨k₃, f₃, w₃, p₃⟩ => ?_)
  refine WP.seq (WP.mono (cp k₃ f₃ (d := 32) (by decide) 5 (by decide)) fun u₄ ⟨k₄, f₄, w₄, p₄⟩ => ?_)
  refine WP.seq (WP.mono (cp k₄ f₄ (d := 40) (by decide) 6 (by decide)) fun u₅ ⟨k₅, f₅, w₅, p₅⟩ => ?_)
  refine WP.seq (WP.mono (cp k₅ f₅ (d := 48) (by decide) 7 (by decide)) fun u₆ ⟨k₆, f₆, w₆, p₆⟩ => ?_)
  refine WP.mono (cp k₆ f₆ (d := 56) (by decide) 8 (by decide)) fun u₇ ⟨k₇, f₇, w₇, p₇⟩ => ?_
  refine ⟨k₇, f₇, fun j hj => ?_⟩
  have rdi₁ : u₁.gpr .rdi = off (fb s) oBuf := (k₁.gpr (by decide)).trans h.rdi
  match j, hj with
  | 0, _ => rw [p₇ 0 (by decide) (by decide), p₆ 0 (by decide) (by decide), p₅ 0 (by decide) (by decide),
      p₄ 0 (by decide) (by decide), p₃ 0 (by decide) (by decide), p₂ 0 (by decide) (by decide),
      p₁ 0 (by decide) (by decide), w₀, h.args 1 (by decide)] <;> rfl
  | 1, _ => rw [p₇ 8 (by decide) (by decide), p₆ 8 (by decide) (by decide), p₅ 8 (by decide) (by decide),
      p₄ 8 (by decide) (by decide), p₃ 8 (by decide) (by decide), p₂ 8 (by decide) (by decide),
      w₁, h.args 2 (by decide)] <;> rfl
  | 2, _ => rw [p₇ 16 (by decide) (by decide), p₆ 16 (by decide) (by decide), p₅ 16 (by decide) (by decide),
      p₄ 16 (by decide) (by decide), p₃ 16 (by decide) (by decide), w₂, rdi₁] <;> rfl
  | 3, _ => rw [p₇ 24 (by decide) (by decide), p₆ 24 (by decide) (by decide), p₅ 24 (by decide) (by decide),
      p₄ 24 (by decide) (by decide), w₃]; exact h.ps
  | 4, _ => rw [p₇ 32 (by decide) (by decide), p₆ 32 (by decide) (by decide), p₅ 32 (by decide) (by decide),
      w₄, h.args 5 (by decide)] <;> rfl
  | 5, _ => rw [p₇ 40 (by decide) (by decide), p₆ 40 (by decide) (by decide), w₅,
      h.args 6 (by decide)] <;> rfl
  | 6, _ => rw [p₇ 48 (by decide) (by decide), w₆, h.args 7 (by decide)] <;> rfl
  | 7, _ => rw [w₇, h.args 8 (by decide)] <;> rfl
  | _ + 8, h => exact absurd h (by omega)
theorem ea_at (t : State) (b : Reg) (d : Nat) : t.ea (at_ b d) = t.gpr b + BitVec.ofNat 64 d := by
  simp only [State.ea, at_, BitVec.ofInt_natCast]

/-- `tape` is `[i, 0]`. -/
theorem tapeArgs_ok {s t : State} (hp : RPre s) (hsp : t.gpr .rsp = fb s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (htape : word t.mem (fb s) oTape = s.gpr .rdx) {i : Nat}
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa tapeArgs t fun u => u.mem = tapeMem s t.mem i ∧ Keep [.rax, .r10] t u := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hT0 : InRegions t.wr (s.gpr .rdx) 8 := by
    rw [hwr, hp.hwr]
    have := Offset.contains_base (s.gpr .rdx) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    rw [BitVec.add_zero] at this
    exact ⟨tapeR s, by simp, this⟩
  have hT1 : InRegions t.wr (s.gpr .rdx + BitVec.ofNat 64 8) 8 := by
    rw [hwr, hp.hwr]
    exact ⟨tapeR s, by simp, Offset.contains_base (d := 8) _ (by decide) (by decide)⟩
  refine WP.seq (WP.mono (WP.keep [.rax] (c := .block [.mov .rax (.mem (sp oTape))]) (Q := fun u =>
      u.mem = t.mem ∧ u.gpr .rax = s.gpr .rdx) (by
    xrun [ea_sp, hsp, show fb s + BitVec.ofNat 64 oTape = off (fb s) oTape from rfl,
      hs.ld (d := oTape) (by decide), show t.mem.readW (off (fb s) oTape) 64 = word t.mem (fb s) oTape from rfl,
      htape]) rfl) fun u ⟨⟨hm, hax⟩, k⟩ => ?_)
  refine WP.mono (WP.keep [.r10] (c := .block [.store (at_ .rax) .rcx, .mov32 .r10 (.imm 0),
      .store (at_ .rax 8) .r10]) (Q := fun w => w.mem = tapeMem s t.mem i) (by
    xrun [ea_at, hax, (k.gpr (by decide)).trans hcx, k.2.2 ▸ hT0, k.2.2 ▸ hT1, hm, BitVec.add_zero]
    rfl) rfl) fun w ⟨hw, k'⟩ => ⟨hw, (k.trans k').mono (by decide)⟩

/-- The load of `tape`'s address, alone. -/
theorem tapeLoad_ok {s t : State} (hp : RPre s) (hsp : t.gpr .rsp = fb s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (htape : word t.mem (fb s) oTape = s.gpr .rdx) :
    WP isa (.block [.mov .rax (.mem (sp oTape))]) t fun u => u.gpr .rax = s.gpr .rdx := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  xrun [ea_sp, hsp, show fb s + BitVec.ofNat 64 oTape = off (fb s) oTape from rfl,
    hs.ld (d := oTape) (by decide), show t.mem.readW (off (fb s) oTape) 64 = word t.mem (fb s) oTape from rfl,
    htape]

theorem fb_off (s : State) (d : Nat) : fb s + BitVec.ofNat 64 d = off (fb s) d := rfl

theorem ea_arg' (t : State) (j : Nat) : t.ea (arg j) = t.gpr .rsp + BitVec.ofNat 64 (frameBytes + 8 + 8 * j) :=
  ea_sp t _

theorem off_arg (s : State) (j : Nat) : off (fb s) (frameBytes + 8 + 8 * j) = stackArgAddr s j :=
  (stackArgAddr_fb s j).symm

theorem regArgs_ok {s u : State} (hp : RPre s) (hsp : u.gpr .rsp = fb s) (hrd : u.rd = s.rd)
    (hwr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hsl : Slots s u.mem)
    (ha0 : u.mem.readW (stackArgAddr s 0) 64 = stackArg s 0) :
    WP isa (.block regArgs) u fun w => w.mem = u.mem ∧ w.gpr .rdi = s.gpr .rdi ∧ w.gpr .rsi = s.gpr .r8 ∧
      w.gpr .rdx = s.gpr .rcx ∧ w.gpr .rcx = s.gpr .r8 ∧ w.gpr .r8 = s.gpr .r9 ∧ w.gpr .r9 = stackArg s 0 ∧
      Keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] u w := by
  have hF := fb_toNat hp
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (c := .block regArgs) (Q := fun w =>
      w.mem = u.mem ∧ w.gpr .rdi = s.gpr .rdi ∧ w.gpr .rsi = s.gpr .r8 ∧
      w.gpr .rdx = s.gpr .rcx ∧ w.gpr .rcx = s.gpr .r8 ∧ w.gpr .r8 = s.gpr .r9 ∧ w.gpr .r9 = stackArg s 0) (by
    xrun [Impl.RsaPkcs1Enc.X86_64.Random.regArgs, ea_sp, ea_arg', hsp, fb_off, off_arg, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide),
      hs.ld (d := oN) (by decide), hs.ld (d := oE) (by decide), arg_in hp hrd u.wr (show 0 < 9 by decide),
      show u.mem.readW (off (fb s) oOut) 64 = word u.mem (fb s) oOut from rfl,
      show u.mem.readW (off (fb s) oK) 64 = word u.mem (fb s) oK from rfl,
      show u.mem.readW (off (fb s) oN) 64 = word u.mem (fb s) oN from rfl,
      show u.mem.readW (off (fb s) oE) 64 = word u.mem (fb s) oE from rfl,
      hsl.sOut, hsl.sK, hsl.sN, hsl.sE, ha0]) (by decide)) fun w ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1,
    h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, k⟩

theorem tapeR_contains0 (s : State) : (tapeR s).Contains (s.gpr .rdx) 8 := by
  have := Offset.contains_base (s.gpr .rdx) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
  rwa [BitVec.add_zero] at this

theorem tapeR_contains8 (s : State) : (tapeR s).Contains (s.gpr .rdx + BitVec.ofNat 64 8) 8 :=
  Offset.contains_base (s.gpr .rdx) (d := 8) (n := 8) (k := 16) (by decide) (by decide)

theorem frame_tapeMem (s : State) (m : Mem) (i : Nat) : Frame [tapeR s] m (tapeMem s m i) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tapeR_contains0 s)).writeW
    (List.mem_singleton_self _) _ (tapeR_contains8 s)

theorem tape_sep (s : State) : Mem.Sep (s.gpr .rdx) 8 (s.gpr .rdx + BitVec.ofNat 64 8) 8 := by
  have := Offset.sep (s.gpr .rdx) (d := 0) (n := 8) (e := 8) (k := 8) (.inl (by decide)) (by decide) (by decide)
  rwa [BitVec.add_zero] at this

theorem tapeMem_read0 (s : State) (m : Mem) (i : Nat) :
    (tapeMem s m i).readW (s.gpr .rdx) 64 = BitVec.ofNat 64 i := by
  rw [tapeMem, Mem.readW_writeW_sep (tape_sep s) (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem tapeMem_read1 (s : State) (m : Mem) (i : Nat) :
    (tapeMem s m i).readW (s.gpr .rdx + BitVec.ofNat 64 8) 64 = 0 := by
  rw [tapeMem]; exact Mem.readW_writeW_self64 _ _ _

theorem prep_rest_ok {s t u₁ : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : Ready s t i ps)
    (hm₁ : u₁.mem = tapeMem s t.mem i) (k₁ : Keep [.rax, .r10] t u₁) :
    WP isa (.seq stackArgs (.block regArgs)) u₁ fun w => Args s w i ps ∧
      Keep [.rax, .r10, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t w := by
  have hF := fb_toNat hp
  have hfr : Frame [stkR s, tapeR s] s.mem t.mem := frame_of_outside h.out
  have f₁ : Frame [tapeR s] t.mem u₁.mem := hm₁ ▸ frame_tapeMem s t.mem i
  -- what the stack arguments read is unchanged since the entry
  have dSt : ∀ {r : Region}, Region.Sub r (stkR s) → r.Disjoint (tapeR s) := fun hs x h₁ h₂ =>
    hp.dKt x (hs x h₁) h₂
  have argU : ∀ j, j < 9 → u₁.mem.readW (stackArgAddr s j) 64 = stackArg s j := fun j hj => by
    rw [f₁.readW (arg_contains s hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dTa.symm)
      (by decide)]
    exact (hfr.readW (arg_contains s hj) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKa.symm
      · exact hp.dTa.symm) (by decide))
  have slotU : ∀ {d : Nat}, 64 ≤ d → d + 8 ≤ frameBytes → word u₁.mem (fb s) d = word t.mem (fb s) d :=
    fun h1 h2 => f₁.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact frame_apart_tape s hp h2) (by decide)
  have hsi : StackIn s u₁ := ⟨(k₁.gpr (by decide)).trans h.rsp, k₁.2.1.trans h.rd, k₁.2.2.trans h.wr,
    (k₁.gpr (by decide)).trans h.rdi, argU, (slotU (by decide) (by decide)).trans h.slots.sPs⟩
  refine WP.seq (WP.mono (stackArgs_ok hp hsi) fun u₂ ⟨k₂, f₂, w₂⟩ => ?_)
  have slot2 : ∀ {d : Nat}, 64 ≤ d → d + 8 ≤ frameBytes → word u₂.mem (fb s) d = word t.mem (fb s) d :=
    fun h1 h2 => (f₂.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact slot_apart_args s hp h1 h2) (by decide)).trans (slotU h1 h2)
  have sl2 : Slots s u₂.mem := ⟨(slot2 (by decide) (by decide)).trans h.slots.sOut,
    (slot2 (by decide) (by decide)).trans h.slots.sTape, (slot2 (by decide) (by decide)).trans h.slots.sN,
    (slot2 (by decide) (by decide)).trans h.slots.sK, (slot2 (by decide) (by decide)).trans h.slots.sE,
    (slot2 (by decide) (by decide)).trans h.slots.sPs⟩
  have a0 : u₂.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := by
    rw [f₂.readW (arg_contains s (show 0 < 9 by decide)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact argsR_apart s hp) (by decide)]
    exact argU 0 (by decide)
  have k₁₂ := k₁.trans k₂
  refine WP.mono (regArgs_ok hp ((k₁₂.gpr (by decide)).trans h.rsp) (k₁₂.2.1.trans h.rd)
    (k₁₂.2.2.trans h.wr) sl2 a0) fun w ⟨hwm, h1, h2, h3, h4, h5, h6, k₃⟩ => ?_
  have k := k₁₂.trans k₃
  refine ⟨⟨(k.gpr (by decide)).trans h.rsp, k.2.1.trans h.rd, k.2.2.trans h.wr, ?_, hwm ▸ sl2,
    fun j hj => hwm ▸ w₂ j hj, ?_, h.len, ?_, ?_, h1, h2, h3, h4, h5, h6⟩, k.mono (by decide)⟩
  · rw [hwm]
    refine (hfr.trans ((f₁.mono (by simp)).trans (f₂.sub fun r hr => ?_)))
    rw [List.mem_singleton.mp hr]; exact ⟨stkR s, by simp, argR_sub s⟩
  · -- `PS` is unchanged
    rw [hwm, ← h.buf]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    have hP := hp.ps
    have dA : (⟨off (fb s) oBuf, psLen s⟩ : Region).Disjoint (argR s) :=
      Offset.disjoint_base (fb s) (by decide) (by unfold frameBytes oBuf at *; omega)
    have dT : (⟨off (fb s) oBuf, psLen s⟩ : Region).Disjoint (tapeR s) :=
      frame_apart_tape s hp (by unfold frameBytes oBuf; omega)
    rw [f₂.bytes (R := ⟨off (fb s) oBuf, psLen s⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact dA)
      (by show psLen s ≤ 2 ^ 64; omega) hj]
    exact f₁.bytes (R := ⟨off (fb s) oBuf, psLen s⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact dT)
      (by show psLen s ≤ 2 ^ 64; omega) hj
  · rw [hwm, f₂.readW (tapeR_contains0 s) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact fun x h₁ h₂ => hp.dKt x (argR_sub s x h₂) h₁) (by decide), hm₁]
    exact tapeMem_read0 s t.mem i
  · rw [hwm, f₂.readW (tapeR_contains8 s) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact fun x h₁ h₂ => hp.dKt x (argR_sub s x h₂) h₁) (by decide), hm₁]
    exact tapeMem_read1 s t.mem i

theorem prep_ok {s t : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : Ready s t i ps) :
    WP isa (.seq tapeArgs (.seq stackArgs (.block regArgs))) t fun w => Args s w i ps ∧
      Keep [.rax, .r10, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t w :=
  WP.seq (WP.mono (tapeArgs_ok hp h.rsp h.wr h.slots.sTape h.rcx) fun _ ⟨hm₁, k₁⟩ => prep_rest_ok hp h hm₁ k₁)

/-! ## The callee's view -/

/-- The base of the stack the function uses. -/
def kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 rndStack

/-- The callee's entry `rsp`. -/
theorem fb_sub8 (s : State) : fb s - 8 = off (kb s) encStack := by
  rw [fb_eq]
  show kb s + BitVec.ofNat 64 (8 + encStack) - 8 = kb s + BitVec.ofNat 64 encStack
  rw [show (8 + encStack : Nat) = encStack + 8 by omega, BitVec.ofNat_add, ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem off_add_ofNat (p : Addr) (a b : Nat) : off p a + BitVec.ofNat 64 b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem kb_toNat {s : State} (hp : RPre s) : (kb s).toNat + rndStack + 80 ≤ 2 ^ 64 ∧
    (kb s).toNat + rndStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold rndStack at *; omega

theorem stkR_eq (s : State) : stkR s = ⟨kb s, rndStack⟩ := rfl

/-- A part of the stack at an offset of its base. -/
theorem kb_sub {s : State} {d n : Nat} (h : d + n ≤ rndStack) : Region.Sub ⟨off (kb s) d, n⟩ (stkR s) := by
  rw [stkR_eq]; exact Offset.sub_base _ h

theorem fb_kb (s : State) (d : Nat) : off (fb s) d = off (kb s) (8 + encStack + d) := by
  rw [fb_eq, off_off]; rfl

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 100) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (off (kb s) encStack) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega)
    (by omega) (by omega)
  rw [show off (kb s) encStack + BitVec.ofNat 64 0 = off (kb s) encStack from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_kb, off_add_ofNat, show encStack + 8 * (i + 1) = 8 + encStack + 8 * i by omega]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [off_add_ofNat, show fb s = off (fb s) 0 from (BitVec.add_zero _).symm, fb_kb,
    show encStack + 8 * (0 + 1) = 8 + encStack + 0 by omega]

/-- What `vg_rsa_pkcs1_encrypt_precomputed` reads: `n`, `e`, `msg`, `PS`,
`pre` and its stack arguments. -/
def callRd (s : State) : List Region :=
  [nR s, eR s, msgR s, ⟨off (fb s) oBuf, psLen s⟩, preR s, argR s]

/-- What it writes: `out` and the working space. -/
def callWr (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .r8).toNat⟩, scrR s]

theorem off_toNat {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

theorem kb_1120 (s : State) : off (kb s) encStack - BitVec.ofNat 64 1120 = kb s := by
  simp only [off]; exact BitVec.add_sub_cancel _ _

theorem outR_eq {s : State} (hp : RPre s) : (⟨s.gpr .rdi, (s.gpr .r8).toNat⟩ : Region) = outR s := by
  rw [outR, hp.hsi]

theorem call_pre {s w : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : Args s w i ps) :
    (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre
      (w.callEntry.withRegions (callRd s) (callWr s)) := by
  have hE (j : Nat) (hj : j < 8) :
      stackArg (w.callEntry.withRegions (callRd s) (callWr s)) j = callArg s j :=
    (stackArg_entry h.rsp _ _ (by omega)).trans (h.args j hj)
  have hP := hp.ps
  have hpsN : (BitVec.ofNat 64 (psLen s)).toNat = psLen s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
    abi, argRegs, VG.Proof.RsaPkcs1Enc.X86_64.Pc.stackArgs_eight, List.append_eq, List.range, List.range.loop]
  simp only [h.rdi, h.rsi, h.rdx, h.rcx, h.r8, h.r9, h.rsp, fb_sub8, stackArgAddr_entry h.rsp,
    hE 0 (by decide), hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hE 4 (by decide),
    hE 5 (by decide), hE 6 (by decide), hE 7 (by decide), callArg, hpsN, outR_eq hp, kb_1120]
  have hK := kb_toNat hp
  have hF := fb_toNat hp
  have e0 : encStack = 1120 := rfl
  have hE8 : (off (kb s) encStack).toNat = (kb s).toNat + encStack := by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; unfold rndStack at hK; omega
  have hfb0 : fb s = off (kb s) (8 + encStack) := by
    rw [show fb s = off (fb s) 0 from (BitVec.add_zero _).symm, fb_kb, Nat.add_zero]
  have hbuf : off (fb s) oBuf = off (kb s) (8 + encStack + oBuf) := fb_kb s oBuf
  have sBuf : Region.Sub ⟨off (fb s) oBuf, psLen s⟩ (stkR s) := frame_sub s (by unfold frameBytes oBuf; omega)
  have sArg : Region.Sub ⟨fb s, 64⟩ (stkR s) := argR_sub s
  have sRet : Region.Sub ⟨off (kb s) encStack, 8⟩ (stkR s) := kb_sub (by decide)
  have sStk : Region.Sub ⟨kb s, 1120⟩ (stkR s) := Region.sub_prefix (by decide)
  have wK : (kb s).toNat + rndStack ≤ 2 ^ 64 := by omega
  have dRB : (⟨off (kb s) encStack, 8⟩ : Region).Disjoint ⟨off (fb s) oBuf, psLen s⟩ := by
    rw [hbuf]; exact Offset.disjoint _ (.inl (by unfold oBuf; omega)) (by unfold rndStack at *; omega)
      (by unfold rndStack oBuf at *; omega)
  have dRA : (⟨off (kb s) encStack, 8⟩ : Region).Disjoint ⟨fb s, 64⟩ := by
    rw [hfb0]; exact Offset.disjoint _ (.inl (by omega)) (by unfold rndStack at *; omega)
      (by unfold rndStack at *; omega)
  have dSB : (⟨kb s, 1120⟩ : Region).Disjoint ⟨off (fb s) oBuf, psLen s⟩ := by
    rw [hbuf]; exact Offset.base_disjoint _ (by unfold oBuf; omega) (by unfold rndStack oBuf at *; omega)
  have dSA : (⟨kb s, 1120⟩ : Region).Disjoint ⟨fb s, 64⟩ := by
    rw [hfb0]; exact Offset.base_disjoint _ (by omega) (by unfold rndStack at *; omega)
  refine ⟨by omega, by unfold rndStack at hK; omega, rfl, by rw [callWr, outR_eq hp]; rfl,
    hp.dOn, hp.dOe, hp.dOm, (hp.dKo.sub_left sBuf).symm, hp.dOs, hp.dOq, (hp.dKo.sub_left sArg).symm,
    hp.dNs, hp.dEs, hp.dMs, hp.dKs.sub_left sBuf, hp.dSq, (hp.dKs.sub_left sArg).symm,
    hp.dKo.sub_left sRet, hp.dKn.sub_left sRet, hp.dKe.sub_left sRet, hp.dKm.sub_left sRet, dRB,
    hp.dKs.sub_left sRet, hp.dKq.sub_left sRet, dRA,
    hp.dKo.sub_left sStk, hp.dKn.sub_left sStk, hp.dKe.sub_left sStk, hp.dKm.sub_left sStk, dSB,
    hp.dKs.sub_left sStk, hp.dKq.sub_left sStk, dSA,
    by have := hp.wO; have := hp.hsi; omega, hp.wN, hp.wE, hp.wM, ?_, hp.wS, hp.wQ,
    ⟨hp.k1, hp.k2⟩, trivial, hp.L1, hp.L2, hp.hml, rfl, hp.hsl, hp.hql⟩
  have hk1 := hK.1
  rw [rndStack_eq] at hk1
  have hP2 := hP.2.2
  rw [hbuf, off_toNat (by rw [e0]; unfold oBuf; omega), e0]
  unfold oBuf; omega

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd

/-!
## The call

The call of `vg_rsa_pkcs1_encrypt_precomputed`, with the implementation `v`
of the precomputed public operation, by its contract (`call_ok`): what it
leaves, the frame's slots, the tape and, if `pre` holds the values for `n`,
the encryption with `PS` the padding string drawn.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack)
open VG.Proof.Rsa.X86_64 (PublicImpl)

/-- The callee, `vg_rsa_pkcs1_encrypt_precomputed` calling `v`. -/
def encName (v : PublicImpl) : String := "vg_rsa_pkcs1_encrypt_precomputed" ++ v.suffix
def encCode (v : PublicImpl) : Prog isa := Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code

theorem enc_depth (v : PublicImpl) : (encCode v).x86_64Depth = encStack := by
  simp only [encCode, Impl.RsaPkcs1Enc.X86_64.Precomputed.code, Impl.RsaPkcs1Enc.X86_64.Precomputed.body,
    Code.x86_64Depth, x86_64Depth_noSp v.nosp, v.depth]
  decide

/-- After the call. -/
structure AfterCall (s u : State) (i : Nat) (ps : List Byte) : Prop where
  rsp : u.gpr .rsp = fb s
  rd : u.rd = s.rd
  wr : u.wr = ⟨fb s, frameBytes⟩ :: s.wr
  fr : Frame [stkR s, tapeR s, outR s, scrR s] s.mem u.mem
  slots : Slots s u.mem
  tape0 : u.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 i
  tape1 : u.mem.readW (s.gpr .rdx + BitVec.ofNat 64 8) 64 = 0
  res : Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
    Spec.Rsa.written u.mem (s.gpr .rdi) (kOf s) ((u.gpr .rax).setWidth 32)
      (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)

/-- The bytes of a buffer apart from the stack and the tape. -/
theorem bytes_apart {s : State} {m : Mem} (hf : Frame [stkR s, tapeR s] s.mem m) {R : Region}
    (h₁ : (stkR s).Disjoint R) (h₂ : (tapeR s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun j hj => hf.bytes (R := R) (fun r hr => ?_) hl (List.mem_range.mp hj)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h₁.symm
  · exact h₂.symm

/-- The words of a buffer apart from the stack and the tape. -/
theorem words_apart {s : State} {m : Mem} (hf : Frame [stkR s, tapeR s] s.mem m) {p : Addr} {n : Nat}
    (h₁ : (stkR s).Disjoint ⟨p, n * 8⟩) (h₂ : (tapeR s).Disjoint ⟨p, n * 8⟩) (hw : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  refine hf.readW (r := ⟨p, n * 8⟩) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h₁.symm
  · exact h₂.symm

theorem below_fb (s : State) : below (fb s) (encStack + 8) = ⟨kb s, 8 + encStack⟩ := by
  simp only [below]
  rw [show fb s = off (kb s) (8 + encStack) by
    rw [show fb s = off (fb s) 0 from (BitVec.add_zero _).symm, fb_kb, Nat.add_zero]]
  simp only [off, show encStack + 8 = 8 + encStack by omega]
  rw [BitVec.add_sub_cancel]

theorem call_covers {s w : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : Args s w i ps) :
    Covers (callRd s ++ callWr s) (w.rd ++ w.wr) ∧ Covers (callWr s) w.wr := by
  have hP := hp.ps
  have hfr : (⟨fb s, frameBytes⟩ : Region) ∈ w.rd ++ w.wr := by rw [h.wr]; simp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (callWr s) w.wr := by
    apply Covers.of_mem
    intro r hr
    simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.wr, hp.hwr]
    rcases hr with rfl | rfl
    · rw [outR_eq hp]; simp
    · simp
  refine ⟨Covers.append_left ?_ cw.right, cw⟩
  apply Covers.of_forall
  intro r hr
  simp only [callRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, hfr, oBuf, rfl, by dsimp only; unfold frameBytes oBuf; omega⟩
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, h.rd, hp.hrd]; simp
  · exact Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, hfr, 0, z _, by dsimp only [argR]; unfold frameBytes; omega⟩

theorem call_ok (v : PublicImpl) {s w : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : Args s w i ps) :
    WP isa (.call (encName v) (encCode v)) w fun u => AfterCall s u i ps ∧
      (∀ r ∈ calleeSaved, u.gpr r = w.gpr r) ∧ u.mxcsr.extractLsb' 6 10 = w.mxcsr.extractLsb' 6 10 := by
  have hpre := call_pre hp h
  obtain ⟨hc, hw⟩ := call_covers hp h
  have hv := (PcCT.code_verified v).1
  have hd : (Impl.RsaPkcs1Enc.X86_64.Precomputed.code v.name v.code).x86_64Depth = encStack := enc_depth v
  refine WP.call_sp_mx (k := Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack) (rd := callRd s)
    (wr := callWr s) hv (SpSafe.of_all (PcCT.code_spSafe v)) (by rw [hd]; decide) hpre hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩ hmx
  rw [hd, h.rsp, below_fb] at hf
  sig_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig,
    abi, argRegs, VG.Proof.RsaPkcs1Enc.X86_64.Pc.stackArgs_eight, List.append_eq, List.range, List.range.loop] at hpost
  have hE (j : Nat) (hj : j < 8) :
      stackArg (w.callEntry.withRegions (callRd s) (callWr s)) j = callArg s j :=
    (stackArg_entry h.rsp _ _ (by omega)).trans (h.args j hj)
  have hP := hp.ps
  have hF := fb_toNat hp
  have hpsN : (BitVec.ofNat 64 (psLen s)).toNat = psLen s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  simp only [h.rsp, h.rdi, h.rdx, h.rcx, h.r8, h.r9, hE 0 (by decide), hE 1 (by decide), hE 2 (by decide),
    hE 3 (by decide), hE 6 (by decide), hE 7 (by decide), callArg, hpsN, fb_sub8, hm₂,
    hg₂ .rax (by decide)] at hpost
  -- the memory the callee read
  have hfE : Frame [stkR s, tapeR s] s.mem (w.mem.writeW (off (kb s) encStack) (w.unknowns 0)) :=
    h.fr.writeW (r := stkR s) (List.mem_cons_self ..) _
      (show (stkR s).Contains (off (kb s) encStack) 8 from by
        rw [stkR_eq]; exact Offset.contains_base _ (by decide) (by decide))
  have nE : Spec.Rsa.bytesAt (w.mem.writeW (off (kb s) encStack) (w.unknowns 0)) (s.gpr .rcx)
      (s.gpr .r8).toNat = nB s :=
    bytes_apart (R := nR s) hfE hp.dKn hp.dTn (by have := hp.wN; unfold nR; dsimp only; omega)
  have eE : Spec.Rsa.bytesAt (w.mem.writeW (off (kb s) encStack) (w.unknowns 0)) (s.gpr .r9)
      (stackArg s 0).toNat = eB s :=
    bytes_apart (R := eR s) hfE hp.dKe hp.dTe (by have := hp.wE; unfold eR; dsimp only; omega)
  have mE : Spec.Rsa.bytesAt (w.mem.writeW (off (kb s) encStack) (w.unknowns 0)) (stackArg s 1)
      (stackArg s 2).toNat = msgB s :=
    bytes_apart (R := msgR s) hfE hp.dKm hp.dTm (by have := hp.wM; unfold msgR; dsimp only; omega)
  have qE : Spec.Rsa.wordsAt (w.mem.writeW (off (kb s) encStack) (w.unknowns 0)) (stackArg s 7)
      (stackArg s 8).toNat = preW s := words_apart hfE hp.dKq hp.dTq hp.wQ
  have pE : Spec.Rsa.bytesAt (w.mem.writeW (off (kb s) encStack) (w.unknowns 0)) (off (fb s) oBuf)
      (psLen s) = ps := by
    rw [← h.buf]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun j hj => ?_
    have hj := List.mem_range.mp hj
    have hd : (⟨off (fb s) oBuf, psLen s⟩ : Region).Disjoint ⟨off (kb s) encStack, 8⟩ := by
      have hk := (kb_toNat hp).1
      rw [rndStack_eq] at hk
      rw [fb_kb]
      exact Offset.disjoint _ (.inr (by unfold oBuf; omega)) (by rw [show encStack = 1120 from rfl]; unfold oBuf; omega)
        (by rw [show encStack = 1120 from rfl]; omega)
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)).bytes
      (R := ⟨off (fb s) oBuf, psLen s⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by show psLen s ≤ 2 ^ 64; omega) hj
  rw [nE, eE, mE, qE, pE] at hpost
  -- what the call leaves
  have hsp' : s'.gpr .rsp = fb s := (hcs .rsp (by decide)).trans h.rsp
  have sK : Region.Sub ⟨kb s, 8 + encStack⟩ (stkR s) := Region.sub_prefix (by decide)
  have hf' : Frame [stkR s, tapeR s, outR s, scrR s] s.mem s'.mem := by
    refine (h.fr.mono (by simp)).trans (hf.sub fun r hr => ?_)
    simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨outR s, by simp, by rw [outR_eq hp]; exact fun x h => h⟩
    · exact ⟨scrR s, by simp, fun x h => h⟩
    · exact ⟨stkR s, by simp, sK⟩
  have apart : ∀ {R : Region}, R.Disjoint (outR s) → R.Disjoint (scrR s) → R.Disjoint ⟨kb s, 8 + encStack⟩ →
      ∀ {a : Addr}, R.Contains a 8 → s'.mem.readW a 64 = w.mem.readW a 64 := fun h₁ h₂ h₃ _ ha =>
    hf.readW ha (fun r hr => by
      simp only [callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [outR_eq hp]; exact h₁
      · exact h₂
      · exact h₃) (by decide)
  have slotK : ∀ {d : Nat}, 64 ≤ d → d + 8 ≤ frameBytes →
      (⟨off (fb s) d, 8⟩ : Region).Disjoint ⟨kb s, 8 + encStack⟩ := fun h1 h2 => by
    have hk := (kb_toNat hp).1
    rw [rndStack_eq] at hk
    rw [fb_kb]
    exact Offset.disjoint_base (kb s) (by omega) (by rw [show encStack = 1120 from rfl]; unfold frameBytes at h2; omega)
  have slot : ∀ {d : Nat}, 64 ≤ d → d + 8 ≤ frameBytes → word s'.mem (fb s) d = word w.mem (fb s) d :=
    fun h1 h2 => apart (hp.dKo.sub_left (frame_sub s h2)) (hp.dKs.sub_left (frame_sub s h2)) (slotK h1 h2)
      (Region.contains_self _ _)
  have tK : (tapeR s).Disjoint ⟨kb s, 8 + encStack⟩ := (hp.dKt.sub_left sK).symm
  refine ⟨⟨hsp', hrd.trans h.rd, hwr.trans h.wr, hf',
    ⟨(slot (by decide) (by decide)).trans h.slots.sOut, (slot (by decide) (by decide)).trans h.slots.sTape,
      (slot (by decide) (by decide)).trans h.slots.sN, (slot (by decide) (by decide)).trans h.slots.sK,
      (slot (by decide) (by decide)).trans h.slots.sE, (slot (by decide) (by decide)).trans h.slots.sPs⟩,
    (apart hp.dOt.symm hp.dTs tK (tapeR_contains0 s)).trans h.tape0,
    (apart hp.dOt.symm hp.dTs tK (tapeR_contains8 s)).trans h.tape1, fun hq => hpost hq⟩,
    fun r hr => hcs r hr, hmx⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd

/-!
## The loops after the scan

The wipe of `PS` (`wipe_ok`), which writes only the frame, and the zeroing
of `out` (`zeroOut_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack byte byte_wb byte_wb_self)
open VG.WriteBytes (writeW8_apply)

/-- `n` bytes from `PS` zeroed: memory changed only in the frame. -/
theorem wipe_ok {s t : State} (hp : RPre s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {n : Nat} (hn : 0 < n) (hn' : oBuf + n ≤ frameBytes)
    (hdi : t.gpr .rdi = off (fb s) oBuf) (hcx : t.gpr .rcx = BitVec.ofNat 64 n)
    (h10 : t.gpr .r10 = BitVec.ofNat 64 0) :
    WP isa wipe t fun t' => Frame [⟨off (fb s) oBuf, n⟩] t.mem t'.mem ∧ Keep [.r10] t t' := by
  have hF := fb_toNat hp
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  refine wp_upto (a := 0) (N := n) hn (fun j u => Keep [.r10] t u ∧ Frame [⟨off (fb s) oBuf, n⟩] t.mem u.mem ∧
      u.gpr .r10 = BitVec.ofNat 64 j) ?_ (fun _ h => ⟨h.2.1, h.1⟩) ⟨Keep.refl _ _, Frame.refl _ _, h10⟩
  intro j _ hj u ⟨k, f, h10'⟩
  have hdi' : u.gpr .rdi = off (fb s) oBuf := (k.gpr (by decide)).trans hdi
  have hcx' : u.gpr .rcx = BitVec.ofNat 64 n := (k.gpr (by decide)).trans hcx
  have hst : InRegions u.wr (off (fb s) (oBuf + j)) 1 := (hs.congr k.2.2).st8 (by omega)
  refine WP.mono (WP.keep [.r10] (c := .block [.store8 (bx .rdi .r10) .rax, .alu .add .r10 (.imm 1),
      .alu .cmp .r10 (.reg .rcx)]) (Q := fun u' =>
      u'.mem = u.mem.writeW (off (fb s) (oBuf + j)) (BitVec.setWidth 8 (u.gpr .rax)) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = n))) (by
    xrun [ea_bx0 (j := j) (p := off (fb s) oBuf) hdi' h10', hst, h10', hcx', ofNat_add_one, off_off,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show n < 2 ^ 64 by omega)]) rfl)
    fun u' ⟨⟨hm, h10'', hz⟩, k'⟩ => ⟨hz, (k.trans k').mono (by decide), ?_, h10''⟩
  rw [hm]
  have := Offset.contains_base (off (fb s) oBuf) (d := j) (n := 1) (k := n) (by omega) (by omega)
  rw [show off (fb s) oBuf + BitVec.ofNat 64 j = off (fb s) (oBuf + j) from off_off _ _ _] at this
  exact f.writeW (List.mem_singleton_self _) _ this

theorem ofNat_sub_one_beq {n j : Nat} (hj : j < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (j + 1)) == 0) = decide (j + 1 = n) := by
  by_cases h : j + 1 = n
  · rw [show n - (j + 1) = 0 by omega]; simp [h]
  · have hne : BitVec.ofNat 64 (n - (j + 1)) ≠ 0 := fun e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    rw [decide_eq_false h]; exact beq_false_of_ne hne

theorem ofNat_sub_one {n j : Nat} (hj : j < n) :
    BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem off_succ (p : Addr) (j : Nat) : off p j + 1 = off p (j + 1) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl]
  simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem setWidth8_zero : BitVec.setWidth 8 (0 : BitVec 64) = 0 := rfl

/-- `out` zeroed: `n_len` zero bytes, and memory changed only there. -/
theorem zeroOut_ok {s t : State} (hp : RPre s) (hsp : t.gpr .rsp = fb s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hsl : Slots s t.mem) :
    WP isa zeroOut t fun u => Frame [outR s] t.mem u.mem ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (kOf s) = List.replicate (kOf s) 0 ∧
      Keep [.rdi, .r10, .rax] t u := by
  have hF := fb_toNat hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hkk : kOf s ≤ 1024 := hk2
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hK : (s.gpr .r8) = BitVec.ofNat 64 (kOf s) := by simp [kOf]
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .rax] (c := .block [.mov .rdi (.mem (sp oOut)),
      .mov .r10 (.mem (sp oK)), .mov32 .rax (.imm 0)]) (Q := fun u => u.mem = t.mem ∧
      u.gpr .rdi = off (s.gpr .rdi) 0 ∧ u.gpr .r10 = BitVec.ofNat 64 (kOf s - 0) ∧ u.gpr .rax = 0) (by
    xrun [ea_sp, hsp, fb_off, hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide),
      show t.mem.readW (off (fb s) oOut) 64 = word t.mem (fb s) oOut from rfl,
      show t.mem.readW (off (fb s) oK) 64 = word t.mem (fb s) oK from rfl, hsl.sOut, hsl.sK, hK,
      VG.Proof.RsaPkcs1Enc.X86_64.off_zero]
    rfl) rfl) fun u₀ ⟨⟨hm₀, hdi₀, h10₀, hax₀⟩, k₀⟩ => ?_)
  have hO : (outR s).base = s.gpr .rdi := rfl
  refine wp_upto (a := 0) (N := kOf s) (by unfold kOf; omega) (fun j u => Keep [.rdi, .r10] u₀ u ∧
      Frame [outR s] t.mem u.mem ∧ u.gpr .rdi = off (s.gpr .rdi) j ∧ u.gpr .r10 = BitVec.ofNat 64 (kOf s - j) ∧
      ∀ i < j, u.mem (off (s.gpr .rdi) i) = 0) ?_ (fun u ⟨k, f, _, _, hz⟩ => ⟨f, ?_, (k₀.trans k).mono (by decide)⟩)
    ⟨Keep.refl _ _, hm₀ ▸ Frame.refl _ _, hdi₀, h10₀, fun _ h => absurd h (by omega)⟩
  · intro j _ hj u ⟨k, f, hdi, h10, hz⟩
    have hax : u.gpr .rax = 0 := (k.gpr (by decide)).trans hax₀
    have hst : InRegions u.wr (off (s.gpr .rdi) j) 1 := by
      rw [k.2.2, k₀.2.2, hwr, hp.hwr]
      exact ⟨outR s, by simp, Offset.contains_base _ (by have := hp.hsi; unfold kOf at hj; omega)
        (by omega)⟩
    refine WP.mono (WP.keep [.rdi, .r10] (c := .block [.store8 (at_ .rdi) .rax, .alu .add .rdi (.imm 1),
        .alu .sub .r10 (.imm 1)]) (Q := fun u' => u'.mem = u.mem.writeW (off (s.gpr .rdi) j) (0 : Byte) ∧
        u'.gpr .rdi = off (s.gpr .rdi) (j + 1) ∧ u'.gpr .r10 = BitVec.ofNat 64 (kOf s - (j + 1)) ∧
        u'.zf = some (decide (j + 1 = kOf s))) (by
      xrun [ea_at, hdi, hax, hst, h10, BitVec.add_zero, off_succ, ofNat_sub_one hj,
        ofNat_sub_one_beq hj (by omega), setWidth8_zero]) rfl) fun u' ⟨⟨hm, hdi', h10', hz'⟩, k'⟩ => ⟨hz', (k.trans k').mono (by decide), ?_, hdi', h10', ?_⟩
    · rw [hm]
      exact f.writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (by have := hp.hsi; unfold kOf at hj; omega) (by omega))
    · intro i hi
      rw [hm, writeW8_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))]; exact hz i hi
      · simp
  · simp only [Spec.Rsa.bytesAt]
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hz i h₁

/-- The drawn octets wiped, unless there are none. -/
theorem wipeDrawn_ok {s t : State} (hp : RPre s) (hsp : t.gpr .rsp = fb s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {c : Nat} (hc : c < psLen s)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 c) :
    WP isa wipeDrawn t fun u => Frame [⟨off (fb s) oBuf, c⟩] t.mem u.mem ∧ Keep [.rdi, .r10, .rcx, .rdx] t u ∧
      u.gpr .rdx = t.gpr .rdx := by
  have hP := hp.ps
  refine WP.seq (WP.mono (WP.keep [.rdi, .r10, .rcx, .rdx] (c := .block [.mov .rdi (.reg .rsp),
      .alu .add .rdi (.imm (BitVec.ofNat 32 oBuf)), .mov32 .r10 (.imm 0), .mov .rcx (.reg .rdx),
      .alu .test .rdx (.reg .rdx)]) (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = off (fb s) oBuf ∧
      u.gpr .r10 = BitVec.ofNat 64 0 ∧ u.gpr .rcx = BitVec.ofNat 64 c ∧ u.zf = some (decide (c = 0)) ∧ u.gpr .rdx = t.gpr .rdx) (by
    xrun [hsp, off_buf, hdx, BitVec.and_self]
    by_cases h0 : c = 0
    · subst h0; rfl
    · have : BitVec.ofNat 64 c ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this; exact h0 this
      rw [decide_eq_false h0]; exact beq_false_of_ne this) rfl)
    fun u ⟨⟨hm, hdi, h10, hcx, hz, hd⟩, k⟩ => ?_)
  by_cases h0 : c = 0
  · refine WP.ite false (by rw [eval_ne hz, decide_eq_true h0]; rfl) (fun h => absurd h (by decide))
      fun _ => WP.block_nil ⟨hm ▸ Frame.refl _ _, k, hd⟩
  · refine WP.ite true (by rw [eval_ne hz, decide_eq_false h0]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (wipe_ok (n := c) hp (k.2.2.trans hwr) (by omega) (by unfold frameBytes oBuf; omega) hdi hcx h10)
      fun v ⟨f, k'⟩ => ⟨hm ▸ f, (k.trans k').mono (by decide), (k'.gpr (by decide)).trans hd⟩

/-- The budget: `psLen + 128`. -/
abbrev cap (s : State) : Nat := Spec.RsaPkcs1Enc.padEntropy (psLen s)

/-- The tape and the status, with `c` octets drawn from all `rand_len`. -/
theorem budget_ok {s t : State} (hp : RPre s) (hsp : t.gpr .rsp = fb s)
    (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) (hsl : Slots s t.mem) {c : Nat} (hc : c < psLen s)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 c) (h11 : t.gpr .r11 = stackArg s 4) :
    WP isa (.seq (.block budget) (.ite .ae (.block exhausted) (.block request))) t fun u =>
      Frame [tapeR s] t.mem u.mem ∧ Keep [.rax, .r8, .r9, .r10, .r11] t u ∧
      (cap s ≤ (stackArg s 4).toNat → u.mem.readW (s.gpr .rdx) 64 = stackArg s 4 ∧
        u.mem.readW (s.gpr .rdx + BitVec.ofNat 64 8) 64 = 0 ∧ (u.gpr .rax).setWidth 32 = 3) ∧
      ((stackArg s 4).toNat < cap s → u.mem.readW (s.gpr .rdx) 64 = 0 ∧
        u.mem.readW (s.gpr .rdx + BitVec.ofNat 64 8) 64 =
          BitVec.ofNat 64 (min (cap s) (psLen s + (stackArg s 4).toNat - c)) ∧
        (u.gpr .rax).setWidth 32 = 0) := by
  have hF := fb_toNat hp
  have hP := hp.ps
  have hrl := hp.randLen
  have hs : Scr t (fb s) frameBytes := Scr.of_mem (by rw [hwr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  have hcap : BitVec.ofNat 64 (psLen s) + BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (cap s) := by
    rw [show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 128 by decide, ← BitVec.ofNat_add]; rfl
  have hcapN : (BitVec.ofNat 64 (cap s)).toNat = cap s := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by unfold cap Spec.RsaPkcs1Enc.padEntropy; omega)
  have hcf : decide ((stackArg s 4).toNat < (BitVec.ofNat 64 (cap s)).toNat) =
      decide ((stackArg s 4).toNat < cap s) := by rw [hcapN]
  refine WP.seq (WP.mono (WP.keep [.r10, .r8, .r11] (c := .block budget) (Q := fun u => u.mem = t.mem ∧
      u.gpr .r10 = BitVec.ofNat 64 (cap s) ∧ u.gpr .r8 = s.gpr .rdx ∧
      u.cf = some (decide ((stackArg s 4).toNat < cap s)) ∧ u.gpr .r11 = t.gpr .r11) (by
    xrun [budget, ea_sp, hsp, fb_off, hs.ld (d := oPs) (by decide), hs.ld (d := oTape) (by decide),
      show t.mem.readW (off (fb s) oPs) 64 = word t.mem (fb s) oPs from rfl,
      show t.mem.readW (off (fb s) oTape) 64 = word t.mem (fb s) oTape from rfl, hsl.sPs, hsl.sTape,
      hcap, h11, hcf]) rfl) fun u ⟨⟨hm, h10, h8, hcf', h11'⟩, k⟩ => ?_)
  have hT0 : InRegions u.wr (s.gpr .rdx) 8 := by
    rw [k.2.2, hwr, hp.hwr]; exact ⟨tapeR s, by simp, tapeR_contains0 s⟩
  have hT1 : InRegions u.wr (s.gpr .rdx + BitVec.ofNat 64 8) 8 := by
    rw [k.2.2, hwr, hp.hwr]; exact ⟨tapeR s, by simp, tapeR_contains8 s⟩
  have g : ∀ {r : Reg}, r ∉ [Reg.r10, .r8, .r11] → u.gpr r = t.gpr r := fun h => k.gpr h
  by_cases hge : cap s ≤ (stackArg s 4).toNat
  · refine WP.ite true (by show u.cf.map (!·) = _; rw [hcf', decide_eq_false (by omega)]; rfl)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.mono (WP.keep [.rax] (c := .block exhausted) (Q := fun v =>
        v.mem = (u.mem.writeW (s.gpr .rdx) (stackArg s 4)).writeW (s.gpr .rdx + BitVec.ofNat 64 8) (0 : BitVec 64) ∧
        (v.gpr .rax).setWidth 32 = 3) (by
      xrun [exhausted, ea_at, h8, h11'.trans h11, hT0, hT1, BitVec.add_zero]
      rfl) rfl) fun v ⟨⟨hvm, hva⟩, kv⟩ => ?_
    refine ⟨?_, (k.trans kv).mono (by decide), fun _ => ⟨?_, ?_, hva⟩, fun h => absurd h (by omega)⟩
    · rw [hvm, hm]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tapeR_contains0 s)).writeW
        (List.mem_singleton_self _) _ (tapeR_contains8 s)
    · rw [hvm, Mem.readW_writeW_sep (tape_sep s) (by decide)]; exact Mem.readW_writeW_self64 _ _ _
    · rw [hvm]; exact Mem.readW_writeW_self64 _ _ _
  · refine WP.ite false (by show u.cf.map (!·) = _; rw [hcf', decide_eq_true (by omega)]; rfl)
      (fun h => absurd h (by decide)) fun _ => ?_
    have hs' : Scr u (fb s) frameBytes := hs.congr k.2.2
    have hreq : BitVec.ofNat 64 (psLen s) + stackArg s 4 - BitVec.ofNat 64 c =
        BitVec.ofNat 64 (psLen s + (stackArg s 4).toNat - c) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (stackArg s 4).isLt
      rw [Nat.mod_eq_of_lt (show psLen s < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show psLen s + (stackArg s 4).toNat < 2 ^ 64 by omega)]
      omega
    have hreqN : (BitVec.ofNat 64 (psLen s + (stackArg s 4).toNat - c)).toNat =
        psLen s + (stackArg s 4).toNat - c := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have hslot : ∀ v : BitVec 64, (t.mem.writeW (s.gpr .rdx) v).readW (off (fb s) oPs) 64 =
        BitVec.ofNat 64 (psLen s) := fun v => by
      rw [((Frame.refl _ _).writeW (List.mem_singleton_self (tapeR s)) v (tapeR_contains0 s)).readW
        (Region.contains_self _ _) (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact frame_apart_tape s hp (by decide)) (by decide)]
      exact hsl.sPs
    refine WP.mono (WP.keep [.rax, .r9, .r10] (c := .block request) (Q := fun v =>
        v.mem = (u.mem.writeW (s.gpr .rdx) (0 : BitVec 64)).writeW (s.gpr .rdx + BitVec.ofNat 64 8)
          (BitVec.ofNat 64 (min (cap s) (psLen s + (stackArg s 4).toNat - c))) ∧
        (v.gpr .rax).setWidth 32 = 0) (by
      by_cases hl : cap s < psLen s + (stackArg s 4).toNat - c
      · have hmn : min (cap s) (psLen s + (stackArg s 4).toNat - c) = cap s := Nat.min_eq_left (by omega)
        xrun [request, ea_at, ea_sp, (g (by decide)).trans hsp, fb_off, hm, h8, h10,
          h11'.trans h11, (g (by decide)).trans hdx, hs'.ld (d := oPs) (by decide), hslot, hreq, hreqN, hcapN, hT0, hT1, BitVec.add_zero,
          execCmov, eval, hmn, decide_eq_true hl]
        rfl
      · have hmn : min (cap s) (psLen s + (stackArg s 4).toNat - c) = psLen s + (stackArg s 4).toNat - c :=
          Nat.min_eq_right (by omega)
        xrun [request, ea_at, ea_sp, (g (by decide)).trans hsp, fb_off, hm, h8, h10,
          h11'.trans h11, (g (by decide)).trans hdx, hs'.ld (d := oPs) (by decide), hslot, hreq, hreqN, hcapN, hT0, hT1, BitVec.add_zero,
          execCmov, eval, hmn, decide_eq_false hl]
        rfl) rfl) fun v ⟨⟨hvm, hva⟩, kv⟩ => ?_
    refine ⟨?_, (k.trans kv).mono (by decide), fun h => absurd h (by omega), fun _ => ⟨?_, ?_, hva⟩⟩
    · rw [hvm, hm]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tapeR_contains0 s)).writeW
        (List.mem_singleton_self _) _ (tapeR_contains8 s)
    · rw [hvm, Mem.readW_writeW_sep (tape_sep s) (by decide)]; exact Mem.readW_writeW_self64 _ _ _
    · rw [hvm]; exact Mem.readW_writeW_self64 _ _ _

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd

/-!
## Correctness

After the call, the status `2 - r` and the wipe of `PS` (`accTail_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64.Rnd

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Random
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaPkcs1Enc.X86_64 (encStack)

/-- `writtenRandom` from `written` and the status `2 - r`. -/
theorem written_random {m : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) :
    Spec.RsaPkcs1Enc.writtenRandom m out k (2 - r) res := by
  cases res with
  | some C => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩
  | none => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩

theorem setWidth_sub2 (x : BitVec 64) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (2 : BitVec 32)) -
      BitVec.setWidth 32 x)) = 2 - BitVec.setWidth 32 x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- The end of the accepting path. -/
theorem accTail_ok {s u : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : AfterCall s u i ps) :
    WP isa (.seq (.block status) (.seq wipe (.block [.mov32 .rax (.reg .r11)]))) u fun x =>
      x.gpr .rsp = fb s ∧ x.rd = s.rd ∧ x.wr = ⟨fb s, frameBytes⟩ :: s.wr ∧
      Frame [stkR s, tapeR s, outR s, scrR s] s.mem x.mem ∧
      x.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 i ∧
      x.mem.readW (s.gpr .rdx + BitVec.ofNat 64 8) 64 = 0 ∧
      (Spec.Rsa.publicPrecompute (nB s) = some (preW s) →
        Spec.RsaPkcs1Enc.writtenRandom x.mem (s.gpr .rdi) (kOf s) ((x.gpr .rax).setWidth 32)
          (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)) ∧
      Keep [.rax, .rcx, .rdi, .r10, .r11] u x := by
  have hF := fb_toNat hp
  have hP := hp.ps
  have hs : Scr u (fb s) frameBytes := Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..)
    (by have := hF.1; omega)
  refine WP.seq (WP.mono (WP.keep [.r11, .rdi, .rcx, .r10, .rax] (c := .block status) (Q := fun v =>
      v.mem = u.mem ∧ (v.gpr .r11).setWidth 32 = 2 - (u.gpr .rax).setWidth 32 ∧
      v.gpr .rdi = off (fb s) oBuf ∧ v.gpr .rcx = BitVec.ofNat 64 (psLen s) ∧
      v.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [status, h.rsp, off_buf, ea_sp, fb_off, hs.ld (d := oPs) (by decide),
      show u.mem.readW (off (fb s) oPs) 64 = word u.mem (fb s) oPs from rfl, h.slots.sPs, setWidth_sub2]
    ) rfl) fun v ⟨⟨hm, h11, hdi, hcx, h10⟩, k⟩ => ?_)
  refine WP.seq (WP.mono (wipe_ok (n := psLen s) hp (k.2.2.trans h.wr) (by omega)
    (by unfold frameBytes oBuf; omega) hdi hcx h10) fun w ⟨fw, kw⟩ => ?_)
  refine WP.mono (WP.keep [.rax] (c := .block [.mov32 .rax (.reg .r11)]) (Q := fun x =>
      x.mem = w.mem ∧ (x.gpr .rax).setWidth 32 = (w.gpr .r11).setWidth 32) (by
    xrun []) rfl) fun x ⟨⟨hxm, hxa⟩, kx⟩ => ?_
  have k' := (k.trans kw).trans kx
  have hfr : Frame [stkR s, tapeR s, outR s, scrR s] u.mem x.mem := by
    rw [hxm]; rw [hm] at fw
    exact fw.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨stkR s, by simp, by
        exact frame_sub s (d := oBuf) (n := psLen s) (by unfold frameBytes oBuf; omega)⟩
  have tF : ∀ {a : Addr}, (tapeR s).Contains a 8 → x.mem.readW a 64 = u.mem.readW a 64 := fun ha => by
    rw [hxm]; rw [hm] at fw
    exact fw.readW ha (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun y h₁ h₂ => hp.dKt y (by
        exact frame_sub s (d := oBuf) (n := psLen s) (by unfold frameBytes oBuf; omega) y h₂) h₁)
      (by decide)
  refine ⟨(k'.gpr (by decide)).trans h.rsp, k'.2.1.trans h.rd, k'.2.2.trans h.wr,
    h.fr.trans (hfr.mono (by simp)), (tF (tapeR_contains0 s)).trans h.tape0,
    (tF (tapeR_contains8 s)).trans h.tape1, fun hq => ?_, k'.mono (by decide)⟩
  have hw := h.res hq
  rw [hxa, show w.gpr .r11 = v.gpr .r11 from kw.gpr (by decide), h11]
  have hout : Spec.Rsa.bytesAt x.mem (s.gpr .rdi) (kOf s) = Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (kOf s) := by
    rw [hxm]; rw [hm] at fw
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun j hj => fw.bytes (R := ⟨s.gpr .rdi, kOf s⟩) (fun r hr => ?_)
      (by have := hp.k2; show kOf s ≤ 2 ^ 64; unfold kOf; omega) (List.mem_range.mp hj)
    rw [List.mem_singleton.mp hr]
    have e : (⟨s.gpr .rdi, kOf s⟩ : Region) = outR s := by rw [outR, hp.hsi]; rfl
    rw [e]
    exact fun y h₁ h₂ => hp.dKo y (by
      exact frame_sub s (d := oBuf) (n := psLen s) (by unfold frameBytes oBuf; omega) y h₂) h₁
  have := written_random hw
  cases hres : Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps <;> rw [hres] at this <;>
    exact ⟨this.1, hout.trans this.2⟩

end VG.Proof.RsaPkcs1Enc.X86_64.Rnd
