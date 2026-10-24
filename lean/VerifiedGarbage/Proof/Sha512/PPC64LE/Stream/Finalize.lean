module

public import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Common
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Common
import VerifiedGarbage.Proof.Sha512.Digest
meta import VerifiedGarbage.Proof.Sha512.Digest
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import Mathlib.Tactic.IntervalCases
meta import Mathlib.Tactic.IntervalCases
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Sha512.Stream
public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Streaming SHA-512 on PPC64LE: `finalize`

Untrusted: everything here is checked by Lean. The same structure as the
AArch64 proof (`VG.Proof.Sha512.AArch64.Stream.Finalize`). `finalizeWith o`
is proven for any output `o` writing the first `D` bytes of the final hash
value (`correct`): all 64 for SHA-512's `finalize`, and the digests of
SHA-384, SHA-512/256 and SHA-512/224 (`finalize384`, `finalize512_256`,
`finalize512_224`).
-/

@[expose] public section

namespace VG.Proof.Sha512.PPC64LE.Stream.Finalize

open VG VG.PPC64LE VG.Impl.Sha512.PPC64LE.Stream
open VG.Proof.Sha512.PPC64LE (contains_offset toNat_ofNat_lt sub_offset)
open VG.Proof.Sha512.PPC64LE.Stream
open VG.Proof.Sha512.Stream
open VG.Spec.Sha512 (HashValue stateAt blockAt compress parseBlock bytesAt wordBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev cnt : Nat := (s₀.gpr .r4).toNat
abbrev out : Addr := s₀.gpr .r5
abbrev scr : Addr := s₀.gpr .r6
abbrev stR : Region := ⟨st s₀, 192⟩
abbrev outR (D : Nat) : Region := ⟨out s₀, D⟩
abbrev scR : Region := ⟨scr s₀, 224⟩

/-- The messages the initial state represents, from the initial hash value
`iv`, of fewer than 2⁶⁴ bytes. -/
def R₀ (iv : HashValue) (m : List Byte) : Prop :=
  Spec.Sha512.Repr iv s₀.mem (st s₀) m ∧ m.length < 2 ^ 64 ∧ s₀.gpr .r4 = BitVec.ofNat 64 m.length

/-- The caller's registers are saved in the scratch space. -/
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
  wr : s₀.wr = [stR s₀, outR s₀ D, scR s₀]
  st_out : (stR s₀).Disjoint (outR s₀ D)
  st_scr : (stR s₀).Disjoint (scR s₀)
  out_scr : (outR s₀ D).Disjoint (scR s₀)

theorem pre_of {D : Nat} {s₀ : State} (h : (Proof.Sha512.finalizeDPPC64LE D).pre s₀) : Pre D s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

variable {D : Nat}

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
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = st s₀
  r27 : s.gpr .r27 = scr s₀
  r28 : s.gpr .r28 = out s₀
  r29 : s.gpr .r29 = s₀.gpr .r4
  sp : s.sp = s₀.sp
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv (s₀ : State) (k n : Nat) (s : State) : Prop extends Common s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ 112 + 16 * k
  r30 : s.gpr .r30 = BitVec.ofNat 64 n
  r31 : s.gpr .r31 = BitVec.ofNat 64 k
  hash : ∀ iv m, R₀ s₀ iv m → Spec.Sha512.finalHash iv m =
    (if k = 1 then Fin1 s₀ s.mem n m else Fin0 s₀ s.mem n m).toList.flatMap wordBytes

/-- All blocks are compressed. -/
def Done (s₀ : State) (s : State) : Prop :=
  Common s₀ s ∧ ∀ iv m, R₀ s₀ iv m → Spec.Sha512.finalHash iv m = (stateAt s.mem (st s₀)).toList.flatMap wordBytes

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common s₀ s)
    (hg : ∀ r ∈ [Reg.r26, .r27, .r28, .r29], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r26 := by rw [hg _ (by simp)]; exact h.r26
  r27 := by rw [hg _ (by simp)]; exact h.r27
  r28 := by rw [hg _ (by simp)]; exact h.r28
  r29 := by rw [hg _ (by simp)]; exact h.r29
  sp := hsp.trans h.sp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := by
  simp only [Impl.Sha512.PPC64LE.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact sub_offset (by omega) (by omega)

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`'s memory facts. -/
theorem Common.writeBuf {s₀ : State} (hp : Pre D s₀) {s : State} (h : Common s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ 128) :
    Frame [stR s₀] s.mem (writeBytes s.mem (st s₀ + 64 + BitVec.ofNat 64 n) xs) ∧
      Frame [stR s₀, scR s₀] s₀.mem (writeBytes s.mem (st s₀ + 64 + BitVec.ofNat 64 n) xs) ∧
      Saved s₀ (writeBytes s.mem (st s₀ + 64 + BitVec.ofNat 64 n) xs) := by
  have hf : Frame [stR s₀] s.mem (writeBytes s.mem (st s₀ + 64 + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [st_add]
    exact contains_offset (by omega) (by omega)
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
  keep : ∀ r ∈ [Reg.r26, .r27, .r28, .r29, .r31] ++ nvRegs, s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  sp : s.sp = sI.sp
  r8 : s.gpr .r8 = 0
  r30 : s.gpr .r30 = BitVec.ofNat 64 (n + j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = writeBytes sI.mem (st s₀ + 64 + BitVec.ofNat 64 n) (List.replicate j 0)

/-- The zeroing loop's body. -/
def zeroBody : List Instr :=
  [.add .r11 .r26 .r30, .stb .r8 .r11 64, .addi .r30 .r30 1, .subi .r10 .r10 1]

theorem zero_step {s₀ : State} (hp : Pre D s₀) {sI : State} (hC : Common s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ 128) (hj : j < lim - n) {s : State} (h : Zero s₀ sI n lim j s) :
    WP isa (.block zeroBody) s fun s' =>
      Zero s₀ sI n lim (j + 1) s' ∧ s'.gpr .r10 = BitVec.ofNat 64 (lim - n - (j + 1)) := by
  have hx19 : s.gpr .r26 = st s₀ := by rw [h.keep _ (by simp), hC.r26]
  have hout : InRegions s.wr (st s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [show st s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j = st s₀ + BitVec.ofNat 64 (64 + n + j) by
      simp only [BitVec.ofNat_add]; ac_rfl]
    exact contains_offset (by omega) (by omega)
  unfold zeroBody
  refine wp_add fun s₁ u₁ => wp_stb (a := st s₀ + 64 + BitVec.ofNat 64 n + BitVec.ofNat 64 j) (by decide) (by omega)
    ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hx19, h.r30, BitVec.ofNat_add, show BitVec.ofNat 64 64 = (64 : BitVec 64) from rfl]
    ac_rfl
  refine wp_addi (by decide) (by omega) fun s₃ u₃ => wp_subi (by decide) (by omega) fun s₄ u₄ => WP.block_nil ⟨⟨by omega,
    fun r hr => ?_, by rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd], by rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr],
    by rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .r10 ∧ r ≠ .r30 ∧ r ≠ .r11 := by revert r hr; decide
    rw [u₄.other r this.1, u₃.other r this.2.1, g₂.gpr, u₁.other r this.2.2, h.keep r hr]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r8]
  · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r30, ← BitVec.ofNat_add,
      Nat.add_assoc]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r10,
      sub_ofNat (by omega), Nat.sub_sub]
  · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide), h.r8, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r10,
      sub_ofNat (by omega), Nat.sub_sub, Nat.sub_sub]

theorem zero_ok {s₀ : State} (hp : Pre D s₀) {sI : State} (hC : Common s₀ sI) {n lim : Nat}
    (hlim : lim ≤ 128) (hn : n ≤ lim) {s : State} (h : Zero s₀ sI n lim 0 s) :
    WP isa (.ite (.zero .d .r10) (.block []) (.loop (.block zeroBody) (.nonzero .d .r10))) s
      (Zero s₀ sI n lim (lim - n)) := by
  have hz : eval (.zero .d .r10) s = some (decide (lim - n = 0)) := by
    rw [eval_zero, h.r10, Nat.sub_zero, ofNat_beq_zero (by omega)]
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hp hC hlim hj hZ) fun s' ⟨hZ', h11⟩ => ?_
    have hz' : isa.eval (.nonzero .d .r10) s' = some (decide (lim - n - (j + 1) ≠ 0)) := by
      show VG.PPC64LE.eval (.nonzero .d .r10) s' = _
      rw [eval_nonzero, h11, bne, ofNat_beq_zero (by omega)]
      simp
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The inlined compression of the buffer. -/
theorem compress_buf {s₀ : State} (hp : Pre D s₀) {s : State} (hC : Common s₀ s)
    (hx1 : s.gpr .r4 = st s₀ + 64) {Q : State → Prop}
    (hQ : ∀ s', Common s₀ s' → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      stateAt s'.mem (st s₀) = compress (stateAt s.mem (st s₀)) (blockAt s.mem (st s₀ + 64)) → Q s') :
    WP isa compressAt s Q := by
  have e32 : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := Region.sub_prefix (by omega)
  have e112 : Region.Sub ⟨scr s₀, 176⟩ (scR s₀) := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨st s₀ + 64, 128⟩ (stR s₀) := sub_offset (off := 64) (by omega) (by omega)
  refine compressAt_ok hC.r26 hC.r27 hx1 ((hp.st_scr.sub_left e32).sub_right e112) ?_
    ((hp.st_scr.sub_left eb).sub_right e112) ?_ ?_ fun s' hrd hwr hcs hsp hf hstate =>
      hQ s' ?_ hcs hstate
  · intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 64, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · have cs : ∀ r, r ∈ preserved → s'.gpr r = s.gpr r := hcs
    refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.r26,
      by rw [cs _ (by decide)]; exact hC.r27,
      by rw [cs _ (by decide)]; exact hC.r28,
      by rw [cs _ (by decide)]; exact hC.r29, hsp.trans hC.sp, hC.frame.trans (hf.sub ?_),
      fun p hp' => ?_⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e112⟩
    · rw [← hC.saved p hp']
      refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hp')).sub_right e32
      · simp only [Impl.Sha512.PPC64LE.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
        rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Offset.disjoint_base _ (by decide) (by decide)

theorem times8 (x : BitVec 64) : x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

theorem len_bits {m : List Byte} {x : BitVec 64} (hx : x = BitVec.ofNat 64 m.length) :
    BitVec.ofNat 64 (8 * x.toNat) = BitVec.ofNat 64 (8 * m.length) := by
  subst hx
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mul_mod, Nat.mod_mod]

/-- The loop's postcondition for one iteration. -/
def Step (s₀ : State) (k : Nat) (s : State) : Prop :=
  (eval (.zero .d .r31) s = some false ∧ Done s₀ s) ∨
    (eval (.zero .d .r31) s = some true ∧ k = 1 ∧ LInv s₀ 0 0 s)

theorem body_eq : finalizeBody =
    .seq (.block [.li .r10 128])
    (.seq (.ite (.zero .d .r31) (.block [.li .r10 112]) (.block []))
    (.seq (.block [.li .r8 0, .sub .r10 .r10 .r30])
    (.seq (.ite (.zero .d .r10) (.block []) (.loop (.block zeroBody) (.nonzero .d .r10)))
    (.seq (.ite (.zero .d .r31)
        (.block [.lsr .d .r8 .r29 61, .li .r11 176, .storeRev .d .r8 .r26 .r11,
          .add .r8 .r29 .r29, .add .r8 .r8 .r8, .add .r8 .r8 .r8, .li .r11 184,
          .storeRev .d .r8 .r26 .r11])
        (.block []))
    (.seq (.block [.addi .r4 .r26 64])
    (.seq compressAt (.block [.li .r30 0, .subi .r31 .r31 1]))))))) := rfl

theorem body_ok {s₀ : State} (hp : Pre D s₀) {k n : Nat} {s : State} (h : LInv s₀ k n s) :
    WP isa finalizeBody s fun s' => Step s₀ k s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := by
  have hk := h.k_le; have hn := h.n_le
  have hC := h.toCommon
  rw [body_eq]
  -- `r10 := 128` or `112`: the end of the zeros.
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hz₁ : eval (.zero .d .r31) s₁ = some (decide (k = 0)) := by
    rw [eval_zero, u₁.other _ (by decide), h.r31, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .r10 = BitVec.ofNat 64 (112 + 16 * k) ∧
      (∀ r, r ≠ .r10 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.sp = s.sp) ?_ fun s₃ ⟨h11₃, g₃, m₃, rd₃, wr₃, sp₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₁ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine wp_li (by decide) fun s₃ u₃ => WP.block_nil ⟨by rw [u₃.gpr], fun r hr => ?_,
        by rw [u₃.mem, u₁.mem], by rw [u₃.rd, u₁.rd], by rw [u₃.wr, u₁.wr], by rw [u₃.sp, u₁.sp]⟩
      rw [u₃.other r hr, u₁.other r hr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨by rw [u₁.gpr, show k = 1 by omega], fun r hr => ?_,
        u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩
      rw [u₁.other r hr]
  -- Zero the rest of the buffer, up to `lim`.
  refine WP.seq (wp_li (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hZ : Zero s₀ s n (112 + 16 * k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃],
      by rw [u₅.sp, u₄.sp, sp₃], ?_, ?_, ?_, ?_⟩
    · have : r ≠ .r10 ∧ r ≠ .r8 := by revert r hr; decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.r30, Nat.add_zero]
    · rw [u₅.gpr, u₄.other _ (by decide), h11₃, u₄.other _ (by decide), g₃ _ (by decide), h.r30,
        sub_ofNat (by omega), Nat.sub_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, writeBytes_nil]
  refine WP.seq (WP.mono (zero_ok hp hC (by omega) hn hZ) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hp (n := n) (xs := List.replicate (112 + 16 * k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : Common s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.r26],
      by rw [hZ₆.keep _ (by simp), hC.r27], by rw [hZ₆.keep _ (by simp), hC.r28],
      by rw [hZ₆.keep _ (by simp), hC.r29], hZ₆.sp.trans hC.sp,
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
  have h24₆ : s₆.gpr .r31 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.r31]
  have nv₆ : ∀ r ∈ nvRegs, s₆.gpr r = s.gpr r := fun r hr => hZ₆.keep r (by simp [hr])
  -- In the last block, the length.
  have hz₆ : eval (.zero .d .r31) s₆ = some (decide (k = 0)) := by
    rw [eval_zero, h24₆, ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => Common s₀ s₈ ∧ s₈.gpr .r31 = BitVec.ofNat 64 k ∧
      stateAt s₈.mem (st s₀) = stateAt s.mem (st s₀) ∧
      (∀ iv m, R₀ s₀ iv m → bytesAt s₈.mem (st s₀ + 64) 128 = bytesAt s.mem (st s₀ + 64) n ++
        (if k = 1 then List.replicate (128 - n) 0 else List.replicate (112 - n) 0 ++ lenBytes m)) ∧
      ∀ r ∈ nvRegs, s₈.gpr r = s.gpr r) ?_
    fun s₈ ⟨hC₈, h24₈, hst₈, hby₈, nv₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) hz₆ (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have hout : ∀ d : Nat, d + 8 ≤ 192 → InRegions s₆.wr (st s₀ + BitVec.ofNat 64 d) 8 :=
        fun d hd => ⟨stR s₀, by simp [hC₆.wr, hp.wr], contains_offset hd (by omega)⟩
      -- The high word, `count >> 61`.
      refine wp_lsr (by decide) fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ =>
        wp_stdbrx (a := st s₀ + BitVec.ofNat 64 176) (by decide) ?_ ?_ fun s₉ g₉ => ?_
      · rw [u₈.other _ (by decide), u₇.other _ (by decide), hC₆.r26, u₈.gpr]
      · rw [u₈.wr, u₇.wr]; exact hout 176 (by omega)
      -- The low word, `count << 3`.
      refine wp_add fun s₁₀ u₁₀ => wp_add fun s₁₁ u₁₁ => wp_add fun s₁₂ u₁₂ =>
        wp_li (by decide) fun s₁₃ u₁₃ =>
        wp_stdbrx (a := st s₀ + BitVec.ofNat 64 184) (by decide) ?_ ?_ fun s₁₄ g₁₄ => WP.block_nil ?_
      · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
          u₁₀.other _ (by decide), g₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), hC₆.r26,
          u₁₃.gpr]
      · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, g₉.wr, u₈.wr, u₇.wr]; exact hout 184 (by omega)
      have keep : ∀ r, r ≠ .r8 → r ≠ .r11 → s₁₄.gpr r = s₆.gpr r := fun r h h' => by
        rw [g₁₄.gpr, u₁₃.other r h', u₁₂.other r h, u₁₁.other r h, u₁₀.other r h, g₉.gpr, u₈.other r h',
          u₇.other r h]
      have h22 : s₉.gpr .r29 = s₀.gpr .r4 := by
        rw [g₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), hC₆.r29]
      have hv₁ : s₈.gpr .r8 = s₀.gpr .r4 >>> 61 := by
        rw [u₈.other _ (by decide), u₇.gpr, hC₆.r29]
      have hv₂ : s₁₃.gpr .r8 = BitVec.ofNat 64 (8 * (s₀.gpr .r4).toNat) := by
        rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, h22, times8]
      let L₁ := (List.range 8).map fun j => (rev64 (s₀.gpr .r4 >>> 61)).extractLsb' (8 * j) 8
      let L₂ := (List.range 8).map fun j =>
        (rev64 (BitVec.ofNat 64 (8 * (s₀.gpr .r4).toNat))).extractLsb' (8 * j) 8
      have hL₁ : L₁.length = 8 := by simp [L₁]
      have hw : s₁₄.mem = writeBytes s₆.mem (st s₀ + 64 + BitVec.ofNat 64 112) (L₁ ++ L₂) := by
        rw [← writeBytes_append _ _ _ _ (by simp [L₁, L₂]), hL₁, g₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem,
          u₁₀.mem, g₉.mem, u₈.mem, u₇.mem, hv₁, hv₂,
          show st s₀ + 64 + BitVec.ofNat 64 112 = st s₀ + BitVec.ofNat 64 176 by
            rw [BitVec.add_assoc]; rfl,
          show st s₀ + BitVec.ofNat 64 176 + BitVec.ofNat 64 8 = st s₀ + BitVec.ofNat 64 184 by
            rw [BitVec.add_assoc]; rfl,
          Mem.writeW, write_eq_writeBytes, Mem.writeW, write_eq_writeBytes]
        rfl
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hp (n := 112) (xs := L₁ ++ L₂) (by simp [L₁, L₂])
      refine ⟨⟨g₁₄.rd.trans (by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, g₉.rd, u₈.rd, u₇.rd]; exact hC₆.rd),
        g₁₄.wr.trans (by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, g₉.wr, u₈.wr, u₇.wr]; exact hC₆.wr),
        by rw [keep _ (by decide) (by decide), hC₆.r26], by rw [keep _ (by decide) (by decide), hC₆.r27],
        by rw [keep _ (by decide) (by decide), hC₆.r28], by rw [keep _ (by decide) (by decide), hC₆.r29],
        by rw [g₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, g₉.sp, u₈.sp, u₇.sp]; exact hC₆.sp,
        by rw [hw]; exact hfr, by rw [hw]; exact hsv⟩,
        by rw [keep _ (by decide) (by decide), h24₆], ?_, fun iv m hm => ?_,
        fun r hr => (keep r (by revert r hr; decide) (by revert r hr; decide)).trans (nv₆ r hr)⟩
      · rw [hw, ← hst₆]
        apply stateAt_congr
        intro i hi
        rw [st_add]
        exact writeBytes_before _ _ _ (by omega) (by simp [L₁, L₂])
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        have e := bytesAt_writeBytes s₆.mem (st s₀ + 64) 112 (L₁ ++ L₂) (by simp [L₁, L₂])
        simp only [L₁, L₂, List.length_append, List.length_map, List.length_range] at e
        rw [hw, e, rev64_wordBytes, rev64_wordBytes, len_bits hm.2.2, hm.2.2,
          ← lenBytes_split m hm.2.1, hby₆]
        simp [List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₆, h24₆, hst₆, fun iv m _ => ?_, nv₆⟩
      rw [hby₆]; simp
  -- Compress the block.
  refine WP.seq (wp_addi (by decide) (by decide) fun s₉ u₉ => WP.block_nil ?_)
  have hC₉ : Common s₀ s₉ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .r4 := by revert r hr; decide
      rw [u₉.other r this]) u₉.mem u₉.rd u₉.wr u₉.sp
  have hx1 : s₉.gpr .r4 = st s₀ + 64 := by rw [u₉.gpr, hC₈.r26]; rfl
  have nv₉ : ∀ r ∈ nvRegs, s₉.gpr r = s.gpr r := fun r hr =>
    (u₉.other r (by revert r hr; decide)).trans (nv₈ r hr)
  refine WP.seq (compress_buf hp hC₉ hx1 fun s₁₁ hC₁₁ cs₁₁ hst₁₁ => ?_)
  have nv₁₁ : ∀ r ∈ nvRegs, s₁₁.gpr r = s.gpr r := fun r hr => (cs₁₁ r (nv_pres r hr)).trans (nv₉ r hr)
  have h24₁₁ : s₁₁.gpr .r31 = BitVec.ofNat 64 k := by
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
  refine wp_li (by decide) fun s₁₂ u₁₂ => wp_subi (by decide) (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have hC₁₃ : Common s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .r31 ∧ r ≠ .r30 := by revert r hr; decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr]) (by rw [u₁₃.sp, u₁₂.sp])
  have nv₁₃ : ∀ r ∈ nvRegs, s₁₃.gpr r = s.gpr r := fun r hr =>
    (u₁₃.other r (by revert r hr; decide)).trans ((u₁₂.other r (by revert r hr; decide)).trans (nv₁₁ r hr))
  have hz : eval (.zero .d .r31) s₁₃ = some (decide (k = 1)) := by
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
  [mov .r26 .r3, mov .r27 .r6, mov .r28 .r5, mov .r29 .r4,
    .li .r8 127, .logic .and .r30 .r29 .r8,
    .li .r8 0x80, .add .r11 .r26 .r30, .stb .r8 .r11 64, .addi .r30 .r30 1,
    .addi .r31 .r30 15, .lsr .d .r31 .r31 7]

theorem finalize_eq (o : List Instr) : finalizeWith o = .seq (.block (save .r6 ++ prologue))
    (.seq (.loop finalizeBody (.zero .d .r31)) (.block (o ++ restore))) := rfl

theorem prologue_ok {s₀ : State} (hp : Pre D s₀) :
    WP isa (.block (save .r6 ++ prologue)) s₀ fun s => ∃ k, LInv s₀ k (cnt s₀ % 128 + 1) s := by
  have hr : cnt s₀ % 128 < 128 := Nat.mod_lt _ (by omega)
  refine save_ok (by decide) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  unfold prologue
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_li (by decide) fun s₆ u₆ => wp_and fun s₇ u₇ => ?_
  have hC₇ : Common s₀ s₇ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.other _ (by decide), g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
        u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
      exact (saveMem_frame _ _ _).mono (by simp)
    · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
      intro p hp'
      exact saveMem_saved _ _ _ p hp'
  have hm₇ : s₇.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  have hr23 : s₇.gpr .r30 = BitVec.ofNat 64 (cnt s₀ % 128) := by
    rw [u₇.gpr, u₆.other .r29 (by decide), u₆.gpr, u₅.gpr, u₄.other .r4 (by decide),
      u₃.other .r4 (by decide), u₂.other .r4 (by decide), g₁]
    exact and127 _
  -- The `0x80` byte.
  have hout : InRegions s₇.wr (st s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) 1 := by
    refine ⟨stR s₀, by simp [hC₇.wr, hp.wr], ?_⟩
    rw [st_add]; exact contains_offset (by omega) (by omega)
  refine wp_li (by decide) fun s₈ u₈ => wp_add fun s₉ u₉ =>
    wp_stb (a := st s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) (by decide) (by omega) ?_
      (by rw [u₉.wr, u₈.wr]; exact hout) fun s₁₀ g₁₀ => ?_
  · rw [u₉.gpr, u₈.other _ (by decide), u₈.other _ (by decide), hC₇.r26, hr23,
      show BitVec.ofNat 64 64 = (64 : BitVec 64) from rfl]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₇.writeBuf hp (n := cnt s₀ % 128) (xs := [0x80]) (by simp; omega)
  have hm₁₀ : s₁₀.mem = writeBytes s₇.mem (st s₀ + 64 + BitVec.ofNat 64 (cnt s₀ % 128)) [0x80] := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₉.other _ (by decide), u₈.gpr, ← List.nil_append [(0x80 : Byte)],
      writeBytes_snoc _ _ _ _ (by simp), writeBytes_nil]
    simp
  refine wp_addi (by decide) (by decide) fun s₁₁ u₁₁ => wp_addi (by decide) (by decide) fun s₁₂ u₁₂ =>
    wp_lsr (by decide) fun s₁₃ u₁₃ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r30 → r ≠ .r31 → r ≠ .r8 → r ≠ .r11 → s₁₃.gpr r = s₇.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₁₃.other r h2, u₁₂.other r h2, u₁₁.other r h1, g₁₀.gpr, u₉.other r h4, u₈.other r h3]
  have hm₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  have hC₁₃ : Common s₀ s₁₃ :=
    ⟨by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, hC₇.rd],
      by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, hC₇.wr],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r26],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r27],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r28],
      by rw [keep _ (by decide) (by decide) (by decide) (by decide), hC₇.r29],
      by rw [u₁₃.sp, u₁₂.sp, u₁₁.sp, g₁₀.sp, u₉.sp, u₈.sp, hC₇.sp],
      by rw [hm₁₃, hm₁₀]; exact hfr, by rw [hm₁₃, hm₁₀]; exact hsv⟩
  have hr23' : s₁₃.gpr .r30 = BitVec.ofNat 64 (cnt s₀ % 128 + 1) := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), hr23, ← BitVec.ofNat_add]
  have hr24 : s₁₃.gpr .r31 = BitVec.ofNat 64 ((cnt s₀ % 128 + 16) / 128) := by
    rw [u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), hr23,
      ← BitVec.ofNat_add, ← BitVec.ofNat_add, ofNat_shr7 (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, R₀ s₀ iv m → bytesAt s₁₃.mem (st s₀ + 64) (cnt s₀ % 128 + 1) = rest m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₇.mem (st s₀ + 64) (cnt s₀ % 128) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₃, hm₁₀, e, hm₇]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := frame_bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀) (by simpa using hp.st_scr)
      (by simp) (i := 64 + i) (by show 64 + i < 192; omega)
    rwa [← st_add] at this
  have hstate : stateAt s₁₃.mem (st s₀) = stateAt s₀.mem (st s₀) := by
    apply stateAt_congr
    intro i hi
    rw [hm₁₃, hm₁₀, st_add, writeBytes_before _ _ _ (by omega) (by simp; omega), hm₇]
    exact frame_bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀) (by simpa using hp.st_scr) (by simp)
      (by show i < 192; omega)
  by_cases hb : 113 ≤ cnt s₀ % 128 + 1
  · have hk : (cnt s₀ % 128 + 16) / 128 = 1 := by omega
    refine ⟨1, hC₁₃, le_rfl, by omega, hr23', by rw [hr24, hk], fun iv m hm => ?_⟩
    simp only [↓reduceIte]
    rw [hash_two (by rw [← hm.length]; omega), Fin1, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 128 - (cnt s₀ % 128 + 1) = 127 - cnt s₀ % 128 by omega]
  · have hk : (cnt s₀ % 128 + 16) / 128 = 0 := by omega
    refine ⟨0, hC₁₃, by omega, by omega, hr23', by rw [hr24, hk], fun iv m hm => ?_⟩
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [hash_one (by rw [← hm.length]; omega), Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length, show 112 - (cnt s₀ % 128 + 1) = 111 - cnt s₀ % 128 by omega]

/-! ## Output and epilogue

The output writes the first `D` bytes of the final hash value to `out`: its
first `n` words (`outW`), `D = 8 n`, for SHA-512, SHA-384 and SHA-512/256;
its first 3 and the high half of the fourth (`outHi 3`), `D = 28`, for
SHA-512/224. -/

/-- `k` words of the digest are written. -/
structure Out (s₀ sD : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ [Reg.r26, .r27, .r28], s.gpr r = sD.gpr r
  sp : s.sp = sD.sp
  mem : s.mem = writeBytes sD.mem (out s₀) (((stateAt sD.mem (st s₀)).toList.take k).flatMap wordBytes)

/-- The first `D` bytes of the final hash value are written. -/
structure OutD (s₀ sD : State) (D : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ [Reg.r26, .r27, .r28], s.gpr r = sD.gpr r
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
    exact contains_offset (by omega) (by omega))

theorem writeW_rev64 (m : Mem) (a : Addr) (w : BitVec 64) :
    m.writeW a (rev64 w) = writeBytes m a (wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes, ← rev64_wordBytes]; rfl

theorem rev32_wordBytes (x : BitVec 32) :
    (List.range 4).map (fun j => (rev32 x).extractLsb' (8 * j) 8) = Spec.Sha256.wordBytes x := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true, Spec.Sha256.wordBytes]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [rev32, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
    interval_cases i <;> simp

theorem writeW_rev32 (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a (rev32 w) = writeBytes m a (Spec.Sha256.wordBytes w) := by
  rw [Mem.writeW, write_eq_writeBytes, ← rev32_wordBytes]; rfl

theorem sw32 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by ext i hi; simp

theorem out_step {s₀ : State} (hp : Pre D s₀) (hD64 : D ≤ 64) {sD : State} (hD : Done s₀ sD) {k : Nat}
    (hk : 8 * k + 8 ≤ D) {s : State} (h : Out s₀ sD k s) {rest : List Instr} {Q : State → Prop}
    (hnext : ∀ s', Out s₀ sD (k + 1) s' → WP isa (.block rest) s' Q) :
    WP isa (.block (outW k ++ rest)) s Q := by
  have hC := hD.1
  have hx19 : s.gpr .r26 = st s₀ := by rw [h.keep _ (by simp), hC.r26]
  have hx21 : s.gpr .r28 = out s₀ := by rw [h.keep _ (by simp), hC.r28]
  have hP := flat_length (stateAt sD.mem (st s₀)) k (by omega)
  simp only [outW, List.cons_append, List.nil_append]
  refine wp_ld (a := st s₀ + BitVec.ofNat 64 (8 * k)) (by decide) ⟨by omega, by omega⟩ (by rw [hx19])
    ⟨stR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_li (by omega) fun s₂ u₂ => wp_stdbrx (a := out s₀ + BitVec.ofNat 64 (8 * k)) (by decide)
    (by rw [u₂.other .r28 (by decide), u₁.other .r28 (by decide), hx21, u₂.gpr])
    (by rw [u₂.wr, u₁.wr]; exact ⟨outR s₀ D, by simp [h.wr, hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₃ g₃ => hnext s₃ ⟨by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, u₂.wr, u₁.wr, h.wr],
      fun r hr => ?_, by rw [g₃.sp, u₂.sp, u₁.sp, h.sp], ?_⟩
  · have : r ≠ .r8 ∧ r ≠ .r11 := by revert r hr; decide
    rw [g₃.gpr, u₂.other r this.2, u₁.other r this.1, h.keep r hr]
  · have hread : s.mem.readW (st s₀ + BitVec.ofNat 64 (8 * k)) 64 = (stateAt sD.mem (st s₀))[k] := by
      rw [h.mem, (out_frame (D := D) s₀ sD.mem _ (by omega)).readW
        (r := ⟨st s₀ + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hp.st_out.sub_left (sub_offset (by omega) (by omega))
    rw [g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hread, h.mem, writeW_rev64, ← hP]
    rw [writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega), List.take_add_one,
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
  have hx19 : s.gpr .r26 = st s₀ := by rw [h.keep _ (by simp), hC.r26]
  have hx21 : s.gpr .r28 = out s₀ := by rw [h.keep _ (by simp), hC.r28]
  have hP := flat_length (stateAt sD.mem (st s₀)) 3 (by decide)
  simp only [outHi, List.cons_append, List.nil_append]
  refine wp_lwz (a := st s₀ + BitVec.ofNat 64 (8 * 3 + 4)) (by decide) (by decide) (by rw [hx19])
    ⟨stR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine wp_li (by decide) fun s₂ u₂ => wp_stwbrx (a := out s₀ + BitVec.ofNat 64 (8 * 3)) (by decide)
    (by rw [u₂.other .r28 (by decide), u₁.other .r28 (by decide), hx21, u₂.gpr])
    (by rw [u₂.wr, u₁.wr]; exact ⟨outR s₀ 28, by simp [h.wr, hp.wr], contains_offset (by omega) (by omega)⟩)
    fun s₃ g₃ => hnext s₃ ⟨by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, u₂.wr, u₁.wr, h.wr],
      fun r hr => ?_, by rw [g₃.sp, u₂.sp, u₁.sp, h.sp], ?_⟩
  · have : r ≠ .r8 ∧ r ≠ .r11 := by revert r hr; decide
    rw [g₃.gpr, u₂.other r this.2, u₁.other r this.1, h.keep r hr]
  · -- The high half of word 3 is not overwritten by the first 24 bytes.
    have hread : s.mem.readW (st s₀ + BitVec.ofNat 64 (8 * 3 + 4)) 32 =
        sD.mem.readW (st s₀ + BitVec.ofNat 64 28) 32 := by
      rw [h.mem, (out_frame (D := 28) s₀ sD.mem _ (by omega)).readW
        (r := ⟨st s₀ + BitVec.ofNat 64 (8 * 3 + 4), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hp.st_out.sub_left (sub_offset (by omega) (by omega))
    rw [g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, sw32, hread, h.mem, writeW_rev32,
      show 8 * 3 = (((stateAt sD.mem (st s₀)).toList.take 3).flatMap wordBytes).length from hP.symm,
      writeBytes_append _ _ _ _ (by rw [hP]; simp [Spec.Sha256.wordBytes]), take28]

/-- The epilogue's postcondition. -/
def Post (D : Nat) (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ (Proof.Sha512.finalizeDPPC64LE D).post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre D s₀) (hD64 : D ≤ 64) {sD : State} (hD : Done s₀ sD) {s : State}
    (h : OutD s₀ sD D s) : WP isa (.block restore) s (Post D s₀) := by
  have hC := hD.1
  have hl : (((stateAt sD.mem (st s₀)).toList.flatMap wordBytes).take D).length = D := by
    rw [List.length_take, flat_length_all]; omega
  have hfo := out_frame s₀ sD.mem (((stateAt sD.mem (st s₀)).toList.flatMap wordBytes).take D) hl.le
  refine restore_ok (scr := scr s₀) (by rw [h.keep _ (by simp), hC.r27])
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [h.rd, h.wr, hp.wr], contains_offset hd₂ (by omega)⟩) s₀.gpr
    (fun p hp' => ?_) fun s' hs _ hmem _ _ hsp => ⟨hs, by rw [hsp, h.sp, hC.sp], ?_⟩
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

/-- No instruction of `finalizeWith o` writes the callee-saved registers it does not save. -/
theorem untouched_of {o : List Instr}
    (h : ((instrs (finalizeWith o)).all fun i => untouched.all fun r => dstOf i != some r) = true) :
    ∀ r ∈ untouched, ∀ i ∈ instrs (finalizeWith o), dstOf i ≠ some r := by
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using this

/-- `finalizeWith o`, whose output `o` writes the first `D` bytes: the
callee-saved registers are kept. -/
theorem correct {o : List Instr} {s₀ : State} (hp : Pre D s₀)
    (hu : ∀ r ∈ untouched, ∀ i ∈ instrs (finalizeWith o), dstOf i ≠ some r)
    (hnvo : ((instrs (.block (o ++ restore) : Prog isa)).all fun i =>
      nvRegs.all fun r => dstOf i != some r) = true)
    (hout : ∀ sD, Done s₀ sD → WP isa (.block (o ++ restore)) sD (Post D s₀)) :
    WP isa (finalizeWith o) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ (Proof.Sha512.finalizeDPPC64LE D).post s₀ s' := by
  refine WP.mono (WP.gprs (Q := fun (s' : State) => Post D s₀ s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r) ?_
      hu) fun s' ⟨⟨⟨hsv, hsp, hpost⟩, hnv⟩, hu'⟩ => ⟨fun r hr => ?_, hsp, hpost⟩
  · rw [finalize_eq]
    refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (prologue_ok hp) (by
        intro r hr i hi
        have : ((instrs (.block (save .r6 ++ prologue) : Prog isa)).all fun i =>
            nvRegs.all fun r => dstOf i != some r) = true := by decide
        simpa using List.all_eq_true.mp (List.all_eq_true.mp this i hi) r hr))
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
    · refine WP.mono (WP.gprs (rs := nvRegs) (hout sD hD) (by
        intro r hr i hi
        simpa using List.all_eq_true.mp (List.all_eq_true.mp hnvo i hi) r hr))
        fun s' ⟨h, hnv'⟩ => ⟨h, fun r hr => (hnv' r hr).trans (hnvD r hr)⟩
  · have key : ∀ r ∈ preserved, r ∈ untouched ∨ r ∈ nvRegs ∨ r ∈ saved.map Prod.fst := by decide
    rcases key r hr with hr' | hr' | hr'
    · exact hu' r hr'
    · exact hnv r hr'
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
      exact hsv p hp'

/-- The initial taint: only the arguments are public. -/
theorem agree₀ {s₁ s₂ : State} (hpub : (Proof.Sha512.finalizeDPPC64LE D).pub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x2000 | .r6 => 0x3000 | _ => 0
  lr := 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 224⟩]

/-- `sat`, with `out` of `D` bytes. -/
def satD (D : Nat) : State := { sat with wr := [⟨0x1000, 192⟩, ⟨0x2000, D⟩, ⟨0x3000, 224⟩] }

theorem satD_pre (hD64 : D ≤ 64) : (Proof.Sha512.finalizeDPPC64LE D).pre (satD D) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, satD, sat] at h₁ h₂
    bv_omega

/-- `untouched.all fun r => o != some r` as one `match`, which the kernel
evaluates several times faster on the inlined compression function. -/
def keepsU : Option Reg → Bool
  | some .r2 | some .r20 | some .r21 | some .r22 | some .r23 | some .r24 | some .r25 => false
  | _ => true

theorem keepsU_all (l : List Instr) (h : (l.all fun i => keepsU (dstOf i)) = true) :
    (l.all fun i => untouched.all fun r => dstOf i != some r) = true := by
  refine List.all_eq_true.mpr fun i hi => ?_
  have h := List.all_eq_true.mp h i hi
  generalize dstOf i = o at h ⊢
  rcases o with _ | d
  · rfl
  · cases d <;> revert h <;> decide

/-- A property of every instruction of `finalizeWith o`: of those of
`finalizeWith []`, checked once, and of `o`'s. -/
theorem all_finalizeWith (p : Instr → Bool) (o : List Instr) :
    (instrs (finalizeWith o)).all p = ((instrs (finalizeWith [])).all p && o.all p) := by
  simp only [finalizeWith, instrs, List.all_append, List.nil_append]
  cases o.all p <;> simp only [Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and]

theorem untouched_fixed :
    ((instrs (finalizeWith [])).all fun i => untouched.all fun r => dstOf i != some r) = true :=
  keepsU_all _ (by rw [← Code.allInstrs_eq]; decide +kernel)

theorem lr_fixed : (instrs (finalizeWith [])).all (fun i => !i.writesLr) = true := by
  rw [← Code.allInstrs_eq]; decide +kernel

theorem noCalls_finalizeWith (o : List Instr) : (finalizeWith o).noCalls = true := by
  have h : (finalizeWith []).noCalls = true := by decide +kernel
  exact h

theorem finalize64_verified : Verified PPC64LE.target finalize (Proof.Sha512.finalizeDPPC64LE 64) := by
  refine ⟨fun s hs => ?_, ?_, ⟨satD 64, satD_pre (by decide)⟩⟩
  · obtain ⟨t, s', he, hk, hsp, h⟩ := correct (pre_of hs)
      (untouched_of (by rw [all_finalizeWith, untouched_fixed]; decide)) (by decide)
      fun sD hD => words_ok (pre_of hs) (by decide) (n := 8) rfl hD
    exact ⟨t, s', he, ⟨hk, hsp, Exec.lr he (noCalls_finalizeWith _)
      (by rw [all_finalizeWith, lr_fixed]; decide)⟩, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)

/-- `finalize`: SHA-512's, all 64 bytes of the final hash value. -/
theorem finalize_verified : Verified PPC64LE.target finalize Proof.Sha512.finalizePPC64LE :=
  Verified.of_implies finalize64_verified
    { pre := fun _ h => h
      post := fun _ _ _ h iv m hr hl hc => by
        rw [h iv m hr hl hc]
        exact List.take_of_length_le (by unfold Spec.Sha512.finalHash; exact (flat_length_all _).le)
      pub := fun _ _ _ _ h => h
      sat := ⟨satD 64, satD_pre (by decide)⟩ }

theorem finalize384_verified : Verified PPC64LE.target finalize384 (Proof.Sha512.finalizeDPPC64LE 48) := by
  refine ⟨fun s hs => ?_, ?_, ⟨satD 48, satD_pre (by decide)⟩⟩
  · obtain ⟨t, s', he, hk, hsp, h⟩ := correct (pre_of hs)
      (untouched_of (by rw [all_finalizeWith, untouched_fixed]; decide)) (by decide)
      fun sD hD => words_ok (pre_of hs) (by decide) (n := 6) rfl hD
    exact ⟨t, s', he, ⟨hk, hsp, Exec.lr he (noCalls_finalizeWith _)
      (by rw [all_finalizeWith, lr_fixed]; decide)⟩, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)

theorem finalize512_256_verified :
    Verified PPC64LE.target finalize512_256 (Proof.Sha512.finalizeDPPC64LE 32) := by
  refine ⟨fun s hs => ?_, ?_, ⟨satD 32, satD_pre (by decide)⟩⟩
  · obtain ⟨t, s', he, hk, hsp, h⟩ := correct (pre_of hs)
      (untouched_of (by rw [all_finalizeWith, untouched_fixed]; decide)) (by decide)
      fun sD hD => words_ok (pre_of hs) (by decide) (n := 4) rfl hD
    exact ⟨t, s', he, ⟨hk, hsp, Exec.lr he (noCalls_finalizeWith _)
      (by rw [all_finalizeWith, lr_fixed]; decide)⟩, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)

theorem finalize512_224_verified :
    Verified PPC64LE.target finalize512_224 (Proof.Sha512.finalizeDPPC64LE 28) := by
  refine ⟨fun s hs => ?_, ?_, ⟨satD 28, satD_pre (by decide)⟩⟩
  · obtain ⟨t, s', he, hk, hsp, h⟩ := correct (pre_of hs)
      (untouched_of (by rw [all_finalizeWith, untouched_fixed]; decide)) (by decide)
      fun sD hD => out224_ok (pre_of hs) hD
    exact ⟨t, s', he, ⟨hk, hsp, Exec.lr he (noCalls_finalizeWith _)
      (by rw [all_finalizeWith, lr_fixed]; decide)⟩, h⟩
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6]) (fun _ _ _ _ hp => agree₀ hp)
      (by taint_decide)

end VG.Proof.Sha512.PPC64LE.Stream.Finalize
