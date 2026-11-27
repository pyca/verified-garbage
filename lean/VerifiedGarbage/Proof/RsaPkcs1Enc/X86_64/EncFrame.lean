module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncContract
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.TCB.X86_64.Sse
import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Bignum.X86_64.Words

/-! ### `RsaPkcs1Enc.X86_64.Bytes`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 on x86-64: bytes at offsets of a base

Byte `d` of a buffer at `base` is `byte m base d`. These lemmas read bytes
and words through writes of bytes and words at other offsets (`byte_wb`,
`byte_ww`, `word_wb`), for offsets that do not wrap around, and turn a
store of a byte into `Outside` (`writeB_outside`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

/-- A byte, zero-extended and truncated back. -/
theorem trunc_zext (b : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 b) = b :=
  BitVec.eq_of_toNat_eq (by simp)

theorem zext_toNat (b : Byte) : (BitVec.setWidth 64 b).toNat = b.toNat := by
  have := b.isLt; simp; omega_using []

theorem zero_trunc : BitVec.setWidth 8 (BitVec.setWidth 64 (0 : BitVec 32)) = 0 := rfl

theorem one64_toNat : (1 : BitVec 64).toNat = 1 := rfl

/-- Byte `d` of the buffer at `base`. -/
abbrev byte (m : Mem) (base : Addr) (d : Nat) : Byte := m (off base d)

theorem ofs_off0 (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d := by
  have := ofs_off base (d := d) (i := 0) (by omega_using [h])
  rwa [BitVec.add_zero, Nat.add_zero] at this

theorem byte_wb_self (m : Mem) (base : Addr) (d : Nat) (v : Byte) :
    byte (m.writeW (off base d) v) base d = v := by
  simp only [byte, writeW8_apply, ↓reduceIte]

/-- A byte past a store of a byte at another offset. -/
theorem byte_wb (m : Mem) (base : Addr) {d d' : Nat} (v : Byte) (h : d ≠ d') (hd : d < 2 ^ 64)
    (hd' : d' < 2 ^ 64) : byte (m.writeW (off base d') v) base d = byte m base d := by
  simp only [byte, writeW8_apply, off, Offset.add_ofNat_ne base hd hd' h, ↓reduceIte]

/-- A store of a byte changes only that byte. -/
theorem writeB_outside (m : Mem) (base : Addr) {d : Nat} (v : Byte) (h : d < 2 ^ 64) :
    Outside base d 1 m (m.writeW (off base d) v) := by
  intro x hx
  rw [writeW8_apply]
  have : x ≠ off base d := by
    rintro rfl
    rw [ofs_off0 base h] at hx
    omega_using [hx]
  simp only [this, ↓reduceIte]

/-- A byte past a store of a word elsewhere. -/
theorem byte_ww (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 1 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d < 2 ^ 64) (hd' : d' + 8 ≤ 2 ^ 64) : byte (m.writeW (off base d') v) base d = byte m base d := by
  have := writeW_outside m base v hd'
  refine this _ ?_
  rw [ofs_off0 base hd]
  omega_using [h]

/-- A word past a store of a byte elsewhere. -/
theorem word_wb (m : Mem) (base : Addr) {d d' : Nat} (v : Byte) (h : d + 8 ≤ d' ∨ d' + 1 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (hd' : d' < 2 ^ 64) : word (m.writeW (off base d') v) base d = word m base d :=
  (writeB_outside m base v hd').word (by omega_using [h]) hd

/-- A word past a store of a word elsewhere. -/
theorem word_ww (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (hd' : d' + 8 ≤ 2 ^ 64) : word (m.writeW (off base d') v) base d = word m base d :=
  (writeW_outside m base v hd').word (by omega_using [h]) hd

/-- `Outside` past a store of a byte within its range. -/
theorem _root_.VG.Proof.Bignum.Outside.wb {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat} (v : Byte)
    (h₁ : o ≤ d) (h₂ : d < o + n) (hd : d < 2 ^ 64) : Outside base o n m (m'.writeW (off base d) v) :=
  fun x hx => ((writeB_outside m' base v hd) x (by omega_using [h₁, h₂, hx])).trans (h x hx)

/-- `Outside` past a store of a word within its range. -/
theorem _root_.VG.Proof.Bignum.Outside.ww {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat} (v : BitVec 64)
    (h₁ : o ≤ d) (h₂ : d + 8 ≤ o + n) (hd : d + 8 ≤ 2 ^ 64) : Outside base o n m (m'.writeW (off base d) v) :=
  fun x hx => ((writeW_outside m' base v hd) x (by omega_using [h₁, h₂, hx])).trans (h x hx)

/-! ### Stores at the base itself (offset 0, as `xrun` leaves them) -/

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

theorem word_ww0 (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) :
    word (m.writeW base v) base d = word m base d := by
  have := word_ww m base v (d := d) (d' := 0) (.inr h) hd (by omega_using [])
  rwa [off_zero] at this

theorem word0_ww (m : Mem) (base : Addr) {d' : Nat} (v : BitVec 64) (h : 8 ≤ d') (hd' : d' + 8 ≤ 2 ^ 64) :
    (m.writeW (off base d') v).readW base 64 = m.readW base 64 := by
  have := word_ww m base v (d := 0) (d' := d') (.inl h) (by omega_using []) hd'
  simp only [Bignum.word, off_zero] at this; exact this

theorem word0_wb (m : Mem) (base : Addr) {d' : Nat} (v : Byte) (h : 8 ≤ d') (hd' : d' < 2 ^ 64) :
    (m.writeW (off base d') v).readW base 64 = m.readW base 64 := by
  have := word_wb m base v (d := 0) (d' := d') (.inl h) (by omega_using []) hd'
  simp only [Bignum.word, off_zero] at this; exact this

theorem _root_.VG.Proof.Bignum.Outside.ww0 {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (v : BitVec 64)
    (h₁ : o = 0) (h₂ : 8 ≤ n) : Outside base o n m (m'.writeW base v) := by
  have := Outside.ww h (d := 0) v (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])
  rwa [off_zero] at this

/-- `p + i` with `p = base + d` as an offset of `base`. -/
theorem off_add (base : Addr) (d i : Nat) : off base d + BitVec.ofNat 64 i = off base (d + i) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

end VG.Proof.RsaPkcs1Enc.X86_64

end

end

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: the frame

The precondition by name (`EPre`), the frame of `frameBytes` bytes at
`fb s = rsp - frameBytes` and what lies around it, and the first block
(`setup_ok`): the slots, the call's stack arguments and the first two bytes
of `EM`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-! ## The precondition, by name -/

/-- `encK.pre`, by name. -/
structure EPre (s : State) : Prop where
  sp1 : encStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 56 ≤ 2 ^ 64
  hrd : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩, ⟨stackArgAddr s 0, 48⟩] s.rd
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
  hsl : Spec.Rsa.publicScratchWords (s.gpr .rcx).toNat ≤ (stackArg s 5).toNat

/-- The length of `PS`. -/
theorem EPre.psLen {s : State} (hp : EPre s) :
    (stackArg s 3).toNat + (stackArg s 1).toNat + 3 = (s.gpr .rcx).toNat := by
  have := hp.hpl; have := hp.hml; omega_arith

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
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold encStack frameBytes at *; omega_arith

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold encStack frameBytes; omega_using [h])

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
    simp only [Region.Contains, ofs] at hlt ⊢; omega_using [hlt]
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
  h _ (.inr (outside_frame s fun hc => hd _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi]))))

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega_using [], BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem stackArgAddr_eq (s : State) (j : Nat) : stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rw [show 8 * (0 + 1) + 8 * j = 8 * (j + 1) by omega_using []]

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : EPre s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 6) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_using [])) (by unfold frameBytes at *; omega_using [hj])

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
  by
    rw [hrd]
    exact hp.hrd.left _ _ ⟨⟨stackArgAddr s 0, 48⟩, by simp,
      by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩

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
    Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega_using [hF])
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
