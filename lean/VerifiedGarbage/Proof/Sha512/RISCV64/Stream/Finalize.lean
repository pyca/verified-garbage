module

public import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.TCB.RISCV64.Target
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Sha512.Digest
meta import VerifiedGarbage.Proof.Sha512.Digest
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Spec.Sha256
meta import VerifiedGarbage.Spec.Sha256
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Impl.Words.RISCV64

/-!
# Streaming SHA-512 on RISC-V: `finalize`

Untrusted: everything here is checked by Lean. The structure of SHA-256's
proof (`Proof/Sha256/RISCV64/Stream/Finalize.lean`), in a frame on the stack
(`WP.alloc`), with the message length and the digest stored a byte at a
time (`storeBE_ok`), and the output of the PPC64LE proof of SHA-512's
(`Proof/Sha512/PPC64LE/Stream/Finalize.lean`): `finalize` is proven for any
output `o` writing the first `D` bytes of the final hash value
(`correct`): all 64 for SHA-512's `finalize`, and the digests of SHA-384,
SHA-512/256 and SHA-512/224 (`finalize384`, `finalize512_256`,
`finalize512_224`).
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64.Stream.Finalize

open VG VG.RISCV64 VG.Impl.Sha512.RISCV64.Stream VG.WriteBytes VG.RISCV64.ByteLoad
open VG.Impl.Words.RISCV64 (storeBE loadLE32)
open VG.Proof.Sha512.RISCV64.Stream
open VG.Proof.Sha512.Stream
open VG.Spec.Sha512 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev cnt : Nat := (s₀.gpr .a1).toNat
abbrev out : Addr := s₀.gpr .a2
/-- The frame. -/
abbrev scr : Addr := s₀.sp - BitVec.ofNat 64 frameBytes
abbrev stR : Region := ⟨st s₀, 192⟩
abbrev outR (D : Nat) : Region := ⟨out s₀, D⟩
abbrev scR : Region := ⟨scr s₀, frameBytes⟩

/-- The messages the initial state represents, from the initial hash value
`iv`, of fewer than 2⁶⁴ bytes. -/
def R₀ (iv : HashValue) (m : List Byte) : Prop :=
  Spec.Sha512.Repr iv s₀.mem (st s₀) m ∧ m.length < 2 ^ 64 ∧ s₀.gpr .a1 = BitVec.ofNat 64 m.length

/-- The caller's registers are saved in the frame. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

/-- The digest, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (compress (stateAt mem (st s₀))
    (parseBlock fun t => (bytesAt mem (st s₀ + 64) n ++ List.replicate (128 - n) 0).getD t 0))
    (parseBlock fun t => (List.replicate 112 0 ++ lenBytes m).getD t 0)

/-- The digest, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : HashValue :=
  compress (stateAt mem (st s₀))
    (parseBlock fun t => (bytesAt mem (st s₀ + 64) n ++ List.replicate (112 - n) 0 ++ lenBytes m).getD t 0)

end

/-- The precondition, with `out` of `D` bytes. -/
structure Pre (D : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, outR s₀ D]
  st_out : (stR s₀).Disjoint (outR s₀ D)
  al : s₀.sp.toNat % 16 = 0
  sp208 : 208 ≤ s₀.sp.toNat
  scr_st : (scR s₀).Disjoint (stR s₀)
  scr_out : (scR s₀).Disjoint (outR s₀ D)

variable {D : Nat}

theorem pre_of {s₀ : State} (h : (Proof.Sha512.finalizeDRISCV64 D).pre s₀) : Pre D s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem Pre.st_scr {s₀ : State} (hp : Pre D s₀) : (stR s₀).Disjoint (scR s₀) := hp.scr_st.symm
theorem Pre.out_scr {s₀ : State} (hp : Pre D s₀) : (outR s₀ D).Disjoint (scR s₀) := hp.scr_out.symm

theorem Pre.scr_al {s₀ : State} (hp : Pre D s₀) : (scr s₀).toNat % 16 = 0 :=
  frame_aligned hp.al hp.sp208

theorem R₀.length {s₀ : State} {iv : HashValue} {m : List Byte} (h : R₀ s₀ iv m) :
    cnt s₀ % 128 = m.length % 128 := by
  rw [cnt, h.2.2, BitVec.toNat_ofNat]
  omega

theorem st_add (s₀ : State) (n : Nat) :
    st s₀ + 64 + BitVec.ofNat 64 n = st s₀ + BitVec.ofNat 64 (64 + n) := by
  simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

/-! ## Invariants -/

structure Common (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = scR s₀ :: s₀.wr
  s1 : s.gpr .s1 = st s₀
  s2 : s.gpr .s2 = scr s₀
  s3 : s.gpr .s3 = out s₀
  s4 : s.gpr .s4 = s₀.gpr .a1
  sp : s.sp = scr s₀
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 112 + 16 * k
  s5 : s.gpr .s5 = BitVec.ofNat 64 n
  s6 : s.gpr .s6 = BitVec.ofNat 64 k
  hash : ∀ iv m, R₀ s₀ iv m → Spec.Sha512.finalHash iv m =
    (if k = 1 then Fin1 s₀ s.mem n m else Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  Common s₀ s ∧ ∀ iv m, R₀ s₀ iv m → Spec.Sha512.finalHash iv m = (stateAt s.mem (st s₀)).toList.flatMap wordBytes

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common s₀ s)
    (hg : ∀ r ∈ [Reg.s1, .s2, .s3, .s4], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  s1 := by rw [hg _ (by simp)]; exact h.s1
  s2 := by rw [hg _ (by simp)]; exact h.s2
  s3 := by rw [hg _ (by simp)]; exact h.s3
  s4 := by rw [hg _ (by simp)]; exact h.s4
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := by
  simp only [Impl.Sha512.RISCV64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Offset.sub_base _ (by simp only [frameBytes]; omega)

/-- The saved registers are not in the compression function's scratch space. -/
theorem saved_disj {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ ⟨scr s₀, 144⟩ := by
  simp only [Impl.Sha512.RISCV64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Offset.disjoint_base _ (by decide) (by decide)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf {s₀ : State} (hp : Pre D s₀) {s : State} (h : Common s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ 128) :
    Frame [stR s₀] s.mem (writeBytes s.mem (st s₀ + 64 + BitVec.ofNat 64 n) xs) ∧
      Frame [stR s₀, scR s₀] s₀.mem (writeBytes s.mem (st s₀ + 64 + BitVec.ofNat 64 n) xs) ∧
      Saved s₀ (writeBytes s.mem (st s₀ + 64 + BitVec.ofNat 64 n) xs) := by
  have hf : Frame [stR s₀] s.mem (writeBytes s.mem (st s₀ + 64 + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [st_add]
    exact Offset.contains_base _ (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hp')

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s6] ++ nvRegs, s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  t1 : s.gpr .t1 = 0
  s5 : s.gpr .s5 = BitVec.ofNat 64 (n + j)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (st s₀ + 64 + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step {s₀ : State} (hp : Pre D s₀) {sI : State} (hC : Common s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ 128) (hj : j < lim - n) {s : State} (h : Zero s₀ sI n lim j s) :
    WP isa (.block zeroBody) s fun s' =>
      Zero s₀ sI n lim (j + 1) s' ∧ s'.gpr .t2 = BitVec.ofNat 64 (lim - n - (j + 1)) := by
  have hx19 : s.gpr .s1 = st s₀ := by rw [h.keep _ (by simp), hC.s1]
  have hout : InRegions s.wr (st s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [show st s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = st s₀ + BitVec.ofNat 64 (64 + n + j) by
      simp only [BitVec.ofNat_add]; ac_rfl]
    exact Offset.contains_base _ (by omega) (by omega)
  unfold zeroBody
  refine wp_add fun s₁ u₁ => wp_sb (a := st s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by decide)
    ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hx19, h.s5, BitVec.ofNat_add, show BitVec.ofNat 64 64 = (64 : BitVec 64) from rfl]
    ac_rfl
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => wp_subi (imm := 1) (by decide) fun s₄ u₄ =>
    WP.block_nil ⟨⟨by omega,
    fun r hr => ?_, by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd], by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr],
    by rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .t2 ∧ r ≠ .s5 ∧ r ≠ .t3 := by revert r hr; decide
    rw [u₄.other r this.1, u₃.other r this.2.1, g₂.gpr, u₁.other r this.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t1]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.s5, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t2,
      sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide), h.t1, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t2,
      sub_ofNat (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : Pre D s₀) {sI : State} (hC : Common s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 128) (hn : n ≤ lim) {s : State} (h : Zero s₀ sI n lim 0 s) :
    WP isa (.ite (.zero .t2) (.block []) (.loop (.block zeroBody) (.nonzero .t2))) s
      (Zero s₀ sI n lim (lim - n)) := by
  have hz : eval (.zero .t2) s = some (decide (lim - n = 0)) := by
    rw [eval_zero, h.t2, Nat.sub_zero, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hp hC hlim hj hZ) fun s' ⟨hZ', h11⟩ => ?_
    have hz' : isa.eval (.nonzero .t2) s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show VG.RISCV64.eval (.nonzero .t2) s' = _
      rw [eval_nonzero, h11, bne, ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The compression of the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre D s₀) {s : State} (hC : Common s₀ s)
    (hx1 : s.gpr .a1 = st s₀ + 64) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      stateAt s'.mem (st s₀) = compress (stateAt s.mem (st s₀)) (blockAt s.mem (st s₀ + 64)) → Q s') :
    WP isa compressAt s Q := by
  have e32 : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e80 : Region.Sub ⟨scr s₀, 144⟩ (scR s₀) := Region.sub_prefix (by simp only [frameBytes]; omega)
  have eb : Region.Sub ⟨st s₀ + 64, 128⟩ (stR s₀) := Offset.sub_base (d := 64) (n := 128) (k := 192) _ (by omega)
  refine compressAt_ok hC.s1 hC.s2 hx1 ((hp.st_scr.sub_left e32).sub_right e80) ?_
    ((hp.st_scr.sub_left eb).sub_right e80) ?_ ?_ fun s' hrd hwr hcs hsp hf hstate =>
      hQ s' ?_ hcs hstate
  · have := Offset.disjoint (st s₀) (d := 64) (n := 128) (e := 0) (k := 64) (by omega) (by omega) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 64, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp [frameBytes]⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp [frameBytes]⟩
  · have cs : ∀ r, r ∈ preserved → s'.gpr r = s.gpr r := hcs
    refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.s1,
      by rw [cs _ (by decide)]; exact hC.s2,
      by rw [cs _ (by decide)]; exact hC.s3,
      by rw [cs _ (by decide)]; exact hC.s4, hsp.trans hC.sp, hC.frame.trans (hf.sub ?_),
      fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e80⟩
    · rw [← hC.saved p hp']
      refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hp')).sub_right e32
      · exact saved_disj hp'

/-- A byte of a register, as a right shift leaves it. -/
theorem shr_byte (x : BitVec 64) (s : Nat) : (x >>> s).setWidth 8 = x.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, hi]

/-- A doubleword, as `storeBE 8` stores it: big-endian. -/
theorem beBytes_wordBytes (x : BitVec 64) : beBytes 8 x = wordBytes x := by
  simp only [beBytes, wordBytes, shr_byte]
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  rfl

/-- The length in bits, modulo 2⁶⁴. -/
theorem shl3_ofNat (n : Nat) : BitVec.ofNat 64 n <<< 3 = BitVec.ofNat 64 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem setWidth_byte (w : BitVec 32) {s : Nat} (h : s + 8 ≤ 32) :
    (w.setWidth 64).extractLsb' s 8 = w.extractLsb' s 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show s + i < 32 by omega, show s + i < 64 by omega]

/-- A 32-bit word, as `storeBE 4` stores it. -/
theorem beBytes_word (w : BitVec 32) : beBytes 4 (w.setWidth 64) = Spec.Sha256.wordBytes w := by
  simp only [beBytes, shr_byte]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp (disch := decide) only [List.map_cons, List.map_nil, Nat.reduceMul, Nat.reduceSub, setWidth_byte,
    Spec.Sha256.wordBytes]

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval (.zero .s6) s = some false ∧ Done s₀ s) ∨
    (eval (.zero .s6) s = some true ∧ k = 1 ∧ LInv s₀ 0 0 s)

theorem body_eq : finalizeBody =
    .seq (.block [.li .t2 128])
    (.seq (.ite (.zero .s6) (.block [.li .t2 112]) (.block []))
    (.seq (.block [.li .t1 0, .sub .t2 .t2 .s5])
    (.seq (.ite (.zero .t2) (.block []) (.loop (.block zeroBody) (.nonzero .t2)))
    (.seq (.ite (.zero .s6) (.block lenStore) (.block []))
    (.seq (.block [.addi .a1 .s1 64])
    (.seq compressAt (.block [.li .s5 0, .addi .s6 .s6 (-(1 : Nat) : Int)]))))))) := rfl

theorem lenStore_nv : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s6] ++ nvRegs,
    ∀ i ∈ instrs (.block lenStore : Prog isa), dstOf i ≠ some r := by
  intro r hr i hi e
  have hc : ((instrs (.block lenStore : Prog isa)).all fun i => dstOf i == none || dstOf i == some .t1 || dstOf i == some .t3) = true := by
    decide
  have := List.all_eq_true.mp hc i hi
  rw [e] at this
  simp only [List.cons_append, nvRegs, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at this

theorem body_ok {s₀ : State} (hp : Pre D s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa finalizeBody s fun s' => Step s₀ k s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := by
  have hk := h.k_le; have hn := h.n_le
  have hC := h.toCommon
  rw [body_eq]
  -- `t2 := 128` or `112`: the end of the zeros.
  refine WP.seq (wp_li (imm := 128) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hz₁ : eval (.zero .s6) s₁ = some (decide (k = 0)) := by
    rw [eval_zero, u₁.other _ (by decide), h.s6, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .t2 = BitVec.ofNat 64 (112 + 16 * k) ∧
      (∀ r, r ≠ .t2 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.sp = s.sp) ?_ fun s₃ ⟨h11₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₁ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_li (imm := 112) (by decide) fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr], fun r hr => ?_,
        by rw [u₃.mem, u₁.mem], by rw [u₃.rd, u₁.rd], by rw [u₃.wr, u₁.wr], by rw [u₃.sp, u₁.sp]⟩
      rw [u₃.other r hr, u₁.other r hr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [u₁.gpr, show k = 1 by omega], fun r hr => ?_,
        u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩
      rw [u₁.other r hr]
  -- Zero the rest of the buffer, up to `lim`.
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hZ : Zero s₀ s n (112 + 16 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃],
      by rw [u₅.sp, u₄.sp, sp₃], ?_, ?_, ?_, ?_⟩
    · have : r ≠ .t2 ∧ r ≠ .t1 := by revert r hr; decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.s5, Nat.add_zero]
    · rw [u₅.gpr, u₄.other _ (by decide), h11₃, u₄.other _ (by decide), g₃ _ (by decide), h.s5,
        sub_ofNat (by omega), Nat.sub_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, writeBytes_nil]
  refine WP.seq (WP.mono (zero_ok hp hC (by omega) hn hZ) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hp (n := n) (xs := List.replicate (112 + 16 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.s1],
      by rw [hZ₆.keep _ (by simp), hC.s2], by rw [hZ₆.keep _ (by simp), hC.s3],
      by rw [hZ₆.keep _ (by simp), hC.s4], hZ₆.sp.trans hC.sp,
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : stateAt s₆.mem (st s₀) = stateAt s.mem (st s₀) := by
    rw [hZ₆.mem]
    apply stateAt_congr
    intro i hi
    rw [st_add]
    exact writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (st s₀ + 64) (112 + 16 * k) =
      bytesAt s.mem (st s₀ + 64) n ++ List.replicate (112 + 16 * k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h24₆ : s₆.gpr .s6 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.s6]
  have nv₆ : ∀ r ∈ nvRegs, s₆.gpr r = s.gpr r := fun r hr => hZ₆.keep r (by simp [hr])
  -- In the last block, the length.
  have hz₆ : eval (.zero .s6) s₆ = some (decide (k = 0)) := by
    rw [eval_zero, h24₆, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common s₀ s₈ ∧ s₈.gpr .s6 = BitVec.ofNat 64 k ∧
      stateAt s₈.mem (st s₀) = stateAt s.mem (st s₀) ∧
      (∀ iv m, R₀ s₀ iv m → bytesAt s₈.mem (st s₀ + 64) 128 = bytesAt s.mem (st s₀ + 64) n ++
        (if k = 1 then List.replicate (128 - n) 0 else List.replicate (112 - n) 0 ++ lenBytes m)) ∧
      ∀ r ∈ nvRegs, s₈.gpr r = s.gpr r) ?_
    fun s₈ ⟨hC₈, h24₈, hst₈, hby₈, nv₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₆ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      unfold lenStore
      refine wp_srl (by decide) fun s₇ u₇ => ?_
      have h7 : s₇.gpr .s1 = st s₀ := by rw [u₇.other _ (by decide), hC₆.s1]
      rw [List.append_eq, WP.block_append_iff]
      refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by decide)
        fun j hj => ⟨stR s₀, by simp [u₇.wr, hC₆.wr, hp.wr], ?_⟩) fun s₈ e₈ => ?_
      · rw [h7]; exact Offset.contains_base _ (by omega) (by omega)
      refine wp_sll (by decide) fun s₉ u₉ => ?_
      have h9 : s₉.gpr .s1 = st s₀ := by
        rw [u₉.other _ (by decide), e₈, RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h7
      have wr₉ : s₉.wr = s₆.wr := by rw [u₉.wr, e₈, RegUpd.wr_write]; exact u₇.wr
      refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by decide)
        fun j hj => ⟨stR s₀, by simp [wr₉, hC₆.wr, hp.wr], ?_⟩) fun s₁₁ e => ?_
      · rw [h9]; exact Offset.contains_base _ (by omega) (by omega)
      let L₁ := beBytes 8 (s₀.gpr .a1 >>> 61)
      let L₂ := beBytes 8 (s₀.gpr .a1 <<< 3)
      have v7 : s₇.gpr .t1 = s₀.gpr .a1 >>> 61 := by rw [u₇.gpr, hC₆.s4]
      have v9 : s₉.gpr .t1 = s₀.gpr .a1 <<< 3 := by
        rw [u₉.gpr, e₈, RegUpd.gpr_write_of_ne _ _ (by decide)]
        show s₇.gpr .s4 <<< 3 = _
        rw [u₇.other _ (by decide), hC₆.s4]
      have hw : s₁₁.mem = writeBytes s₆.mem (st s₀ + 64 + BitVec.ofNat 64 112) (L₁ ++ L₂) := by
        rw [e, RegUpd.mem_write]
        show writeBytes s₉.mem _ _ = _
        rw [h9, v9, u₉.mem, e₈, RegUpd.mem_write]
        show writeBytes (writeBytes s₇.mem _ _) _ _ = _
        rw [h7, v7, u₇.mem, ← writeBytes_append _ _ _ _ (by simp [L₁, L₂, beBytes_length])]
        simp only [L₁, L₂, beBytes_length]
        rw [show st s₀ + 64 + BitVec.ofNat 64 112 = st s₀ + BitVec.ofNat 64 (176 + 0) by
            rw [BitVec.add_assoc]; rfl,
          show st s₀ + BitVec.ofNat 64 (176 + 0) + BitVec.ofNat 64 8 = st s₀ + BitVec.ofNat 64 (184 + 0) by
            rw [BitVec.add_assoc]; rfl]
      have keep : ∀ r, r ≠ .t1 → r ≠ .t3 → s₁₁.gpr r = s₆.gpr r := fun r h h' => by
        rw [e, RegUpd.gpr_write_of_ne _ _ h', show ({ s₉ with mem := _ } : State).gpr r = s₉.gpr r from rfl,
          u₉.other r h, e₈, RegUpd.gpr_write_of_ne _ _ h']
        exact u₇.other r h
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hp (n := 112) (xs := L₁ ++ L₂) (by simp [L₁, L₂, beBytes_length])
      refine ⟨⟨by rw [e, u₉.rd, e₈]; exact (u₇.rd.trans hC₆.rd), by rw [e, wr₉]; exact hC₆.wr,
        by rw [keep _ (by decide) (by decide), hC₆.s1], by rw [keep _ (by decide) (by decide), hC₆.s2],
        by rw [keep _ (by decide) (by decide), hC₆.s3], by rw [keep _ (by decide) (by decide), hC₆.s4],
        by rw [e, u₉.sp, e₈]; exact (u₇.sp.trans hC₆.sp),
        by rw [hw]; exact hfr, by rw [hw]; exact hsv⟩,
        by rw [keep _ (by decide) (by decide), h24₆], ?_, fun iv m hm => ?_,
        fun r hr => (keep r (by revert r hr; decide) (by revert r hr; decide)).trans (nv₆ r hr)⟩
      · rw [hw, ← hst₆]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by simp [L₁, L₂, beBytes_length])
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e' := bytesAt_writeBytes s₆.mem (st s₀ + 64) 112 (L₁ ++ L₂) (by simp [L₁, L₂, beBytes_length])
        simp only [L₁, L₂, List.length_append, beBytes_length] at e'
        rw [hw, e', beBytes_wordBytes, beBytes_wordBytes, hm.2.2, shl3_ofNat, ← lenBytes_split m hm.2.1,
          hby₆]
        simp [List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₆, h24₆, hst₆, fun iv m _ => ?_, nv₆⟩
      rw [hby₆]; simp
  -- Compress the block.
  refine WP.seq (wp_addi (imm := 64) (by decide) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : Common s₀ s₉ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .a1 := by revert r hr; decide
      rw [u₉.other r this]) u₉.mem u₉.rd u₉.wr u₉.sp
  have hx1 : s₉.gpr .a1 = st s₀ + 64 := by rw [u₉.gpr, hC₈.s1]; rfl
  have nv₉ : ∀ r ∈ nvRegs, s₉.gpr r = s.gpr r := fun r hr =>
    (u₉.other r (by revert r hr; decide)).trans (nv₈ r hr)
  refine WP.seq (compress_buf hp hC₉ hx1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have nv₁₁ : ∀ r ∈ nvRegs, s₁₁.gpr r = s.gpr r := fun r hr => (cs₁₁ r (nv_pres r hr)).trans (nv₉ r hr)
  have h24₁₁ : s₁₁.gpr .s6 = BitVec.ofNat 64 k := by
    rw [cs₁₁ _ (by decide), u₉.other _ (by decide), h24₈]
  have hblk : ∀ iv m, R₀ s₀ iv m → blockAt s₉.mem (st s₀ + 64) = parseBlock fun t =>
      (bytesAt s.mem (st s₀ + 64) n ++
        (if k = 1 then List.replicate (128 - n) 0 else List.replicate (112 - n) 0 ++ lenBytes m)).getD t 0 := by
    intro iv m hm
    apply parseBlock_congr
    intro t ht
    rw [u₉.mem]
    exact Stream.bytesAt_getD (hby₈ iv m hm) ht
  -- Next block, if any.
  refine wp_li (imm := 0) (by decide) fun s₁₂ u₁₂ => wp_subi (imm := 1) (by decide) fun s₁₃ u₁₃ =>
    WP.block_nil ?_
  have hC₁₃ : Common s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .s6 ∧ r ≠ .s5 := by revert r hr; decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr]) (by rw [u₁₃.sp, u₁₂.sp])
  have nv₁₃ : ∀ r ∈ nvRegs, s₁₃.gpr r = s.gpr r := fun r hr =>
    (u₁₃.other r (by revert r hr; decide)).trans ((u₁₂.other r (by revert r hr; decide)).trans (nv₁₁ r hr))
  have hz : eval (.zero .s6) s₁₃ = some (decide (k = 1)) := by
    rw [eval_zero, u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁, sub_beq (by omega) (by omega)]
  have hst : ∀ iv m, R₀ s₀ iv m → stateAt s₁₃.mem (st s₀) = compress (stateAt s.mem (st s₀)) (parseBlock fun t =>
      (bytesAt s.mem (st s₀ + 64) n ++
        (if k = 1 then List.replicate (128 - n) 0 else List.replicate (112 - n) 0 ++ lenBytes m)).getD t 0) := by
    intro iv m hm
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₉.mem, hst₈, ← hblk iv m hm, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine ⟨.inr ⟨by rw [hz]; simp, rfl, ⟨hC₁₃, by omega, by omega, ?_, ?_, fun iv m hm => ?_⟩⟩, nv₁₃⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), h24₁₁]; rfl
    · rw [h.hash iv m hm]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst iv m hm]
      rw [show bytesAt s₁₃.mem (st s₀ + 64) 0 = [] from rfl, List.nil_append, Nat.sub_zero]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨.inl ⟨by rw [hz]; simp, hC₁₃, fun iv m hm => ?_⟩, nv₁₃⟩
    rw [h.hash iv m hm, hst iv m hm]
    simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

/-! ## Prologue -/

/-- The prologue after saving. -/
def prologue : List Instr :=
  [mov .s1 .a0, mov .s2 .t0, mov .s3 .a2, mov .s4 .a1, .logicImm .and .s5 .s4 127,
    .li .t1 0x80, .add .t3 .s1 .s5, .store .b .t1 .t3 64, .addi .s5 .s5 1,
    .addi .s6 .s5 15, .shift .srl .d .s6 .s6 7]

theorem finalize_eq (o : List Instr) : finalizeMainWith o = .seq (.block (save ++ prologue))
    (.seq (.loop finalizeBody (.zero .s6)) (.block (o ++ restore))) := rfl

/-- The state the frame's body starts in. -/
abbrev inner (s₀ : State) : State := allocd frameBytes s₀

theorem prologue_ok {s₀ : State} (hp : Pre D s₀) :
    WP isa (.block (save ++ prologue)) (inner s₀) fun s => ∃ k, LInv s₀ k (cnt s₀ % 128 + 1) s := by
  have hr : cnt s₀ % 128 < 128 := Nat.mod_lt _ (by omega)
  have hsp : (inner s₀).sp = scr s₀ := rfl
  refine save_ok (by rw [hsp]; exact hp.scr_al)
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [inner, allocd_wr],
      Offset.contains_base _ (by simp only [frameBytes]; omega) (by omega)⟩)
    fun s₁ t₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  unfold prologue
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_andi127 fun s₆ u₆ => ?_
  have hC₆ : Common s₀ s₆ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; rfl
    · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide)]; rfl
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.other _ (by decide), t₁, hsp]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]; rfl
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide)]; rfl
    · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁, hsp]
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, hsp]
      exact (saveMem_frame _ _ _).mono (by simp)
    · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, hsp]
      intro p hp'
      exact saveMem_saved _ _ _ p hp'
  have hm₆ : s₆.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]; rfl
  have hr23 : s₆.gpr .s5 = BitVec.ofNat 64 (cnt s₀ % 128) := by
    rw [u₆.gpr, u₅.gpr, u₄.other .a1 (by decide), u₃.other .a1 (by decide), u₂.other .a1 (by decide),
      g₁ _ (by decide)]; rfl
  -- The `0x80` byte.
  have hout : InRegions s₆.wr (st s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) 1 := by
    refine ⟨stR s₀, by simp [hC₆.wr, hp.wr], ?_⟩
    rw [st_add]; exact Offset.contains_base _ (by omega) (by omega)
  refine wp_li (imm := 0x80) (by decide) fun s₈ u₈ => wp_add fun s₉ u₉ =>
    wp_sb (a := st s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) (by decide) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₆.s1, hr23,
      show BitVec.ofNat 64 64 = (64 : BitVec 64) from rfl]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hp (n := cnt s₀ % 128) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = writeBytes s₆.mem (st s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  refine wp_addi (imm := 1) (by decide) fun s₁₁ u₁₁ => wp_addi (imm := 15) (by decide) fun s₁₂ u₁₂ =>
    wp_srl (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .s5 → r ≠ .s6 → r ≠ .t1 → r ≠ .t3 → s₁₃.gpr r = s₆.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : Common s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, hC₆.rd],
      by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, hC₆.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₆.s1],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₆.s2],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₆.s3],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₆.s4],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, hC₆.sp],
      by rw [hm₁₃, hm₁₀]; exact hfr, by rw [hm₁₃, hm₁₀]; exact hsv⟩
  have hr23' : s₁₃.gpr .s5 = BitVec.ofNat 64 (cnt s₀ % 128 + 1) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), hr23, ← BitVec.ofNat_add]
  have hr24 : s₁₃.gpr .s6 = BitVec.ofNat 64 ((cnt s₀ % 128 + 16) / 128) := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hr23,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ofNat_shr7 (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, R₀ s₀ iv m → bytesAt s₁₃.mem (st s₀ + 64) (cnt s₀ % 128 + 1) = rest m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₆.mem (st s₀ + 64) (cnt s₀ % 128) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₆]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := Frame.bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀) (by simpa using hp.st_scr)
      (by simp) (i := 64 + i) (by show 64 + i < 192; omega)
    rwa [← st_add] at this
  have hstate : stateAt s₁₃.mem (st s₀) = stateAt s₀.mem (st s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₆]
    exact Frame.bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀) (by simpa using hp.st_scr)
      (by simp) (by show i < 192; omega)
  by_cases hb : 113 ≤ cnt s₀ % 128 + 1
  · have hk : (cnt s₀ % 128 + 16) / 128 = 1 := by omega
    refine ⟨1, hC₁₃, (Nat.le_refl _), by omega, hr23', by rw [hr24, hk], fun iv m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), Fin1, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 128 - (cnt s₀ % 128 + 1) = 127 - cnt s₀ % 128 by omega]
  · have hk : (cnt s₀ % 128 + 16) / 128 = 0 := by omega
    refine ⟨0, hC₁₃, by omega, by omega, hr23', by rw [hr24, hk], fun iv m hm => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 112 - (cnt s₀ % 128 + 1) = 111 - cnt s₀ % 128 by omega]

/-! ## Output and epilogue -/

/-- `k` words of the digest are written. -/
structure Out (s₀ sD : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = scR s₀ :: s₀.wr
  keep : ∀ r ∈ [Reg.s1, .s2, .s3], s.gpr r = sD.gpr r
  sp : s.sp = sD.sp
  mem : s.mem = writeBytes sD.mem (out s₀) (((stateAt sD.mem (st s₀)).toList.take k).flatMap wordBytes)

/-- The first `D` bytes of the final hash value are written. -/
structure OutD (s₀ sD : State) (D : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = scR s₀ :: s₀.wr
  keep : ∀ r ∈ [Reg.s1, .s2, .s3], s.gpr r = sD.gpr r
  sp : s.sp = sD.sp
  mem : s.mem = writeBytes sD.mem (out s₀) (((stateAt sD.mem (st s₀)).toList.flatMap wordBytes).take D)

theorem flat_length (H : HashValue) (k : Nat) (hk : k ≤ 8) :
    ((H.toList.take k).flatMap wordBytes).length = 8 * k := by
  rw [List.length_flatMap]
  have : ∀ w ∈ H.toList.take k, (wordBytes w).length = 8 := fun w _ => rfl
  rw [List.map_congr_left this, List.map_const', List.sum_replicate_nat, List.length_take]
  simp; omega

theorem flat_length_all (H : HashValue) : (H.toList.flatMap wordBytes).length = 64 := by
  have := flat_length H 8 (Nat.le_refl _)
  rwa [List.take_of_length_le (by simp)] at this

/-- The first `n` words, big-endian, are the first `8 n` bytes. -/
theorem take_flatMap_wordBytes (l : List Spec.Sha512.Word) (n : Nat) :
    (l.flatMap wordBytes).take (8 * n) = (l.take n).flatMap wordBytes := by
  induction l generalizing n with
  | nil => simp
  | cons w l ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons, List.take_append,
        List.take_of_length_le (by simp [wordBytes] <;> omega), show 8 * (n + 1) - (wordBytes w).length = 8 * n by
          simp [wordBytes] <;> omega, ih]

theorem Out.outD {s₀ sD s : State} {n : Nat} (h : Out s₀ sD n s) : OutD s₀ sD (8 * n) s :=
  ⟨h.rd, h.wr, h.keep, h.sp, by rw [h.mem, take_flatMap_wordBytes]⟩

theorem out_frame (s₀ : State) (m : Mem) (xs : List Byte) (hx : xs.length ≤ D) :
    Frame [outR s₀ D] m (writeBytes m (out s₀) xs) :=
  writeBytes_frame _ _ _ (by
    rw [show out s₀ = out s₀ + BitVec.ofNat 64 0 by simp]
    exact Offset.contains_base _ (by omega) (by omega))

theorem out_step {s₀ : State} (hp : Pre D s₀) (hD64 : D ≤ 64) {sD : State} (hD : Done s₀ sD) {k : Nat}
    (hk : 8 * k + 8 ≤ D) {s : State} (h : Out s₀ sD k s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', Out s₀ sD (k + 1) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outW k ++ rest)) s Q := by
  have hC := hD.1
  have hx19 : s.gpr .s1 = st s₀ := by rw [h.keep _ (by simp), hC.s1]
  have hx21 : s.gpr .s3 = out s₀ := by rw [h.keep _ (by simp), hC.s3]
  have hP := flat_length (stateAt sD.mem (st s₀)) k (by omega)
  simp only [outW, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Words64.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega)
    (by rw [hx19]; exact ⟨stR s₀, by simp [h.rd, h.wr, hp.wr],
      Offset.contains_base _ (by omega) (by omega)⟩)) fun s₁ u₁ => ?_
  have k3 : s₁.gpr .s3 = out s₀ := by rw [u₁.other _ (by decide) (by decide) (by decide), hx21]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega)
    fun j hj => ?_) fun s₃ e₃ => hnext s₃ ?_
  · rw [k3, u₁.wr]
    exact ⟨outR s₀ D, by simp [h.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  subst e₃
  refine ⟨u₁.rd.trans h.rd, u₁.wr.trans h.wr, fun r hr => ?_, u₁.sp.trans h.sp, ?_⟩
  · have : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t4 := by revert r hr; decide
    rw [RegUpd.gpr_write_of_ne _ _ this.2.1]
    show s₁.gpr r = _
    rw [u₁.other _ this.1 this.2.1 this.2.2]
    exact h.keep r hr
  · have hread : s.mem.readW (st s₀ + BitVec.ofNat 64 (8 * k)) 64 = (stateAt sD.mem (st s₀))[k]'(by omega) := by
      rw [h.mem, (out_frame (D := D) s₀ sD.mem _ (by omega)).readW
        (r := ⟨st s₀ + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hp.st_out.sub_left (Offset.sub_base _ (by omega))
    rw [RegUpd.mem_write]
    show writeBytes s₁.mem (s₁.gpr .s3 + _) (beBytes 8 (s₁.gpr .t1)) = _
    rw [k3, u₁.gpr, u₁.mem, hx19, hread, beBytes_wordBytes]
    rw [h.mem, ← hP, writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

/-- The first 28 bytes of the output: the first 3 words, then the high half of
the fourth (`Proof.Sha512.digest_take28`). -/
theorem take28 (mem : Mem) (p : Addr) :
    ((stateAt mem p).toList.flatMap wordBytes).take 28 =
      ((stateAt mem p).toList.take 3).flatMap wordBytes ++
        Spec.Sha256.wordBytes (mem.readW (p + BitVec.ofNat 64 28) 32) := by
  rw [show (stateAt mem p).toList.flatMap wordBytes = Proof.Sha512.md.digest (Proof.Sha512.md.stateAt mem p)
      from rfl, Proof.Sha512.digest_take28, ← Proof.Sha512.digest_take _ _ (n := 3) (by decide),
    show Proof.Sha512.md.digest (Proof.Sha512.md.stateAt mem p) = (stateAt mem p).toList.flatMap wordBytes
      from rfl, take_flatMap_wordBytes]
  rfl

/-- `outHi 3` after 3 words: the first 28 bytes are written. -/
theorem outHi_ok {s₀ : State} (hp : Pre 28 s₀) {sD : State} (hD : Done s₀ sD) {s : State}
    (h : Out s₀ sD 3 s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', OutD s₀ sD 28 s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outHi 3 ++ rest)) s Q := by
  have hC := hD.1
  have hx19 : s.gpr .s1 = st s₀ := by rw [h.keep _ (by simp), hC.s1]
  have hx21 : s.gpr .s3 = out s₀ := by rw [h.keep _ (by simp), hC.s3]
  have hP : (((stateAt sD.mem (st s₀)).toList.take 3).flatMap wordBytes).length = 24 :=
    flat_length (stateAt sD.mem (st s₀)) 3 (by decide)
  simp only [outHi, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega)
    (by rw [hx19]; exact ⟨stR s₀, by simp [h.rd, h.wr, hp.wr],
      Offset.contains_base _ (by omega) (by omega)⟩)) fun s₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega)
    fun j hj => ?_) fun s₃ e₃ => hnext s₃ ?_
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.wr_write,
      RegUpd.wr_write, hx21]
    exact ⟨outR s₀ 28, by simp [h.wr, hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  subst e₃
  refine ⟨h.rd, h.wr, fun r hr => ?_, h.sp, ?_⟩
  · have : r ≠ .t1 ∧ r ≠ .t2 := by revert r hr; decide
    simp only [RegUpd.gpr_write, this.1, this.2, ite_false]
    exact h.keep r hr
  · -- The high half of word 3 is not overwritten by the first 24 bytes.
    have hread : s.mem.readW (st s₀ + BitVec.ofNat 64 (8 * 3 + 4)) 32 =
        sD.mem.readW (st s₀ + BitVec.ofNat 64 28) 32 := by
      rw [h.mem, (out_frame (D := 28) s₀ sD.mem _ (by omega)).readW
        (r := ⟨st s₀ + BitVec.ofNat 64 (8 * 3 + 4), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hp.st_out.sub_left (Offset.sub_base _ (by omega))
    simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, hx19, hx21, hread,
      beBytes_word]
    rw [h.mem, show (8 * 3 : Nat) = (((stateAt sD.mem (st s₀)).toList.take 3).flatMap wordBytes).length
        from hP.symm,
      writeBytes_append _ _ _ _ (by rw [hP]; simp [Spec.Sha256.wordBytes]), take28]

/-- The epilogue's postcondition. -/
def Post (D : Nat) (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = scr s₀ ∧ s'.wr = scR s₀ :: s₀.wr ∧
    (Proof.Sha512.finalizeDRISCV64 D).post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre D s₀) (hD64 : D ≤ 64) {sD : State} (hD : Done s₀ sD) {s : State}
    (h : OutD s₀ sD D s) : WP isa (.block restore) s (Post D s₀) := by
  have hC := hD.1
  have hl : (((stateAt sD.mem (st s₀)).toList.flatMap wordBytes).take D).length = D := by
    rw [List.length_take, flat_length_all]; omega
  have hfo := out_frame s₀ sD.mem (((stateAt sD.mem (st s₀)).toList.flatMap wordBytes).take D) (Nat.le_of_eq hl)
  refine restore_ok (scr := scr s₀) (by rw [h.keep _ (by simp), hC.s2]) hp.scr_al
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [h.rd, h.wr, hp.wr],
      Offset.contains_base _ (by simp only [frameBytes]; omega) (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ hwr hsp => ⟨hs, by rw [hsp, h.sp, hC.sp], by rw [hwr, h.wr], ?_⟩
  · rw [h.mem, ← hC.saved p hp']
    refine hfo.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.out_scr.symm.sub_left (saved_sub hp')
  · intro iv m hr hlt hc
    have e := bytesAt_writeBytes sD.mem (out s₀) 0
      (((stateAt sD.mem (st s₀)).toList.flatMap wordBytes).take D) (by rw [hl]; omega)
    have e' : bytesAt (writeBytes sD.mem (out s₀) (((stateAt sD.mem (st s₀)).toList.flatMap wordBytes).take D))
        (out s₀) D = ((stateAt sD.mem (st s₀)).toList.flatMap wordBytes).take D := by
      rw [hl, Nat.zero_add, show out s₀ + BitVec.ofNat 64 0 = out s₀ by simp,
        show bytesAt sD.mem (out s₀) 0 = [] from rfl, List.nil_append] at e
      exact e
    rw [← h.mem, ← hmem] at e'
    rw [e', hD.2 iv m ⟨hr, hlt, hc⟩]

theorem out_all {s₀ : State} (hp : Pre D s₀) (hD64 : D ≤ 64) {sD : State} (hD : Done s₀ sD) {n : Nat}
    (hn : 8 * n ≤ D) {rest : List Instr} {Q : State → Prop}
    (hrest : ∀ s, Out s₀ sD n s → WP isa (.block rest) s Q) :
    ∀ j ≤ n, ∀ s, Out s₀ sD (n - j) s →
      WP isa (.block (((List.range n).drop (n - j)).flatMap outW ++ rest)) s Q := by
  intro j
  induction j with
  | zero =>
    intro _ s h
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append]
    exact hrest s (by rwa [Nat.sub_zero] at h)
  | succ j ih =>
    intro hj s h
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.append_assoc,
      List.getElem_range]
    refine out_step hp hD64 hD (by omega) h fun s' h' => ?_
    rw [show n - (j + 1) + 1 = n - j by omega]
    exact ih (by omega) s' (by rwa [show n - (j + 1) + 1 = n - j by omega] at h')

/-- The first `n` words, `D = 8 n` bytes. -/
theorem words_ok {s₀ : State} (hp : Pre D s₀) (hD64 : D ≤ 64) {n : Nat} (hn : 8 * n = D) {sD : State}
    (hD : Done s₀ sD) : WP isa (.block ((List.range n).flatMap outW ++ restore)) sD (Post D s₀) := by
  have := out_all hp hD64 hD (n := n) (by omega) (fun s h => epilogue_ok hp hD64 hD (hn ▸ h.outD)) n
    (Nat.le_refl _) sD ⟨hD.1.rd, hD.1.wr, fun _ _ => rfl, rfl, by simp [writeBytes_nil]⟩
  rwa [Nat.sub_self, List.drop_zero] at this

/-- The first 3 words and the high half of the fourth, 28 bytes. -/
theorem out224_ok {s₀ : State} (hp : Pre 28 s₀) {sD : State} (hD : Done s₀ sD) :
    WP isa (.block (((List.range 3).flatMap outW ++ outHi 3) ++ restore)) sD (Post 28 s₀) := by
  have := out_all hp (by decide) hD (n := 3) (by decide) (rest := outHi 3 ++ restore)
    (fun s h => outHi_ok hp hD h fun s' h' => epilogue_ok hp (by decide) hD h') 3 (Nat.le_refl _) sD
    ⟨hD.1.rd, hD.1.wr, fun _ _ => rfl, rfl, by simp [writeBytes_nil]⟩
  rwa [Nat.sub_self, List.drop_zero, ← List.append_assoc] at this

theorem prologue_nv : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (save ++ prologue) : Prog isa),
    dstOf i ≠ some r := keepsN_all _ (by decide)

/-- `finalize`'s body, in its frame, writing the first `D` bytes with `o`:
the callee-saved registers are kept. -/
theorem correctMain {o : List Instr} {s₀ : State} (hp : Pre D s₀)
    (hu : ∀ r ∈ untouched, ∀ i ∈ instrs (finalizeMainWith o), dstOf i ≠ some r)
    (hnvo : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (o ++ restore) : Prog isa), dstOf i ≠ some r)
    (hout : ∀ sD, Done s₀ sD → WP isa (.block (o ++ restore)) sD (Post D s₀)) :
    WP isa (finalizeMainWith o) (inner s₀) fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = scr s₀ ∧ s'.wr = scR s₀ :: s₀.wr ∧
      (Proof.Sha512.finalizeDRISCV64 D).post s₀ s' := by
  refine WP.mono (WP.gprs (Q := fun (s' : State) => Post D s₀ s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r) ?_
      hu) fun s' ⟨⟨⟨hsv, hsp, hwr, hpost⟩, hnv⟩, hu'⟩ => ⟨fun r hr => ?_, hsv (.ra, 144) (by decide), hsp,
        hwr, hpost⟩
  · rw [finalize_eq]
    refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (prologue_ok hp) prologue_nv)
      fun s₁ ⟨⟨k, hL⟩, hnv₁⟩ => ?_)
    refine WP.seq (WP.mono (Q := fun (s : State) => Done s₀ s ∧ ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r) ?_
      fun sD ⟨hD, hnvD⟩ => ?_)
    · refine WP.loop (M := isa) (fun i s => (∃ n, LInv s₀ i n s) ∧ ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r)
        ?_ k s₁ ⟨⟨_, hL⟩, hnv₁⟩
      rintro i s ⟨⟨n, hL⟩, hnv⟩
      refine WP.mono (body_ok hp hL) fun s' ⟨h, hnv'⟩ => ?_
      have hnv'' : ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r := fun r hr => (hnv' r hr).trans (hnv r hr)
      rcases h with ⟨he, hD⟩ | ⟨he, rfl, hL'⟩
      · exact .inl ⟨he, hD, hnv''⟩
      · exact .inr ⟨he, 0, by omega, ⟨0, hL'⟩, hnv''⟩
    · exact WP.mono (WP.gprs (rs := nvRegs) (hout sD hD) hnvo)
        fun s' ⟨h, hnv'⟩ => ⟨h, fun r hr => (hnv' r hr).trans (hnvD r hr)⟩
  · have key : ∀ r ∈ preserved, r ∈ untouched ∨ r ∈ nvRegs ∨ r ∈ saved.map Prod.fst := by decide
    rcases key r hr with hr' | hr' | hr'
    · exact hu' r hr'
    · exact hnv r hr'
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
      exact hsv p hp'

theorem correct {o : List Instr} {s₀ : State} (hp : Pre D s₀)
    (hu : ∀ r ∈ untouched, ∀ i ∈ instrs (finalizeMainWith o), dstOf i ≠ some r)
    (hnvo : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (o ++ restore) : Prog isa), dstOf i ≠ some r)
    (hout : ∀ sD, Done s₀ sD → WP isa (.block (o ++ restore)) sD (Post D s₀)) :
    WP isa (finalizeWith o) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha512.finalizeDRISCV64 D).post s₀ s' := by
  refine WP.alloc (by decide) (by simp only [frameBytes]; exact hp.sp208)
    (WP.mono (correctMain hp hu hnvo hout) fun s' ⟨hk, hra, hsp, hwr, hpost⟩ => ?_)
  rw [freed_eq (by rw [hwr]; rfl) (by rw [hsp]; rfl)]
  exact ⟨⟨hk, rfl, hra⟩, hpost⟩

/-- A property of every instruction of `finalizeMainWith o`: of those of
`finalizeMainWith []`, checked once, and of `o`'s. -/
theorem all_finalizeMainWith (p : Instr → Bool) (o : List Instr) :
    (instrs (finalizeMainWith o)).all p = ((instrs (finalizeMainWith [])).all p && o.all p) := by
  simp only [finalizeMainWith, instrs, List.all_append, List.nil_append]
  cases o.all p <;> simp only [Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and]

theorem untouched_fixed : ((instrs (finalizeMainWith [])).all fun i => keepsU (dstOf i)) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : (Proof.Sha512.finalizeDRISCV64 D).pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [p1, p2, p3]

/-- A state satisfying the precondition, with `out` of `D` bytes. -/
def sat (D : Nat) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩]

theorem finalizeD_verified {o : List Instr}
    (hu : ∀ r ∈ untouched, ∀ i ∈ instrs (finalizeMainWith o), dstOf i ≠ some r)
    (hnvo : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (o ++ restore) : Prog isa), dstOf i ≠ some r)
    (hout : ∀ s₀, Pre D s₀ → ∀ sD, Done s₀ sD → WP isa (.block (o ++ restore)) sD (Post D s₀))
    (hct : ConstantTime RISCV64.isa (Proof.Sha512.finalizeDRISCV64 D).pre
      (Proof.Sha512.finalizeDRISCV64 D).pub (finalizeWith o))
    (hsat : ∃ s, (Proof.Sha512.finalizeDRISCV64 D).pre s) :
    Verified RISCV64.target (finalizeWith o) (Proof.Sha512.finalizeDRISCV64 D) := by
  refine ⟨fun s hs => ?_, hct, hsat⟩
  obtain ⟨t, s', he, h⟩ := correct (pre_of hs) hu hnvo (hout s (pre_of hs))
  exact ⟨t, s', he, h⟩

/-- SHA-512's `finalize`, all 64 bytes of the final hash value. -/
theorem finalize64_verified : Verified RISCV64.target finalize (Proof.Sha512.finalizeDRISCV64 64) :=
  finalizeD_verified (keepsU_all _ (by rw [all_finalizeMainWith, untouched_fixed]; decide +kernel))
    (keepsN_all _ (by decide +kernel)) (fun _ hp _ hD => words_ok hp (by decide) (n := 8) rfl hD)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide))
    ⟨sat 64, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

/-- SHA-384's `finalize`, the first 48 bytes. -/
theorem finalize384_verified : Verified RISCV64.target finalize384 (Proof.Sha512.finalizeDRISCV64 48) :=
  finalizeD_verified (keepsU_all _ (by rw [all_finalizeMainWith, untouched_fixed]; decide +kernel))
    (keepsN_all _ (by decide +kernel)) (fun _ hp _ hD => words_ok hp (by decide) (n := 6) rfl hD)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide))
    ⟨sat 48, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

/-- SHA-512/256's `finalize`, the first 32 bytes. -/
theorem finalize512_256_verified :
    Verified RISCV64.target finalize512_256 (Proof.Sha512.finalizeDRISCV64 32) :=
  finalizeD_verified (keepsU_all _ (by rw [all_finalizeMainWith, untouched_fixed]; decide +kernel))
    (keepsN_all _ (by decide +kernel)) (fun _ hp _ hD => words_ok hp (by decide) (n := 4) rfl hD)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide))
    ⟨sat 32, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

/-- SHA-512/224's `finalize`, the first 28 bytes. -/
theorem finalize512_224_verified :
    Verified RISCV64.target finalize512_224 (Proof.Sha512.finalizeDRISCV64 28) :=
  finalizeD_verified (keepsU_all _ (by rw [all_finalizeMainWith, untouched_fixed]; decide +kernel))
    (keepsN_all _ (by decide +kernel)) (fun _ hp _ hD => out224_ok hp hD)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide))
    ⟨sat 28, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

end VG.Proof.Sha512.RISCV64.Stream.Finalize
