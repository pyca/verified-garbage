module

public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
public import VerifiedGarbage.Proof.Hmac.Stream.Reloc
public import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Proof.Sha512.Stream
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
public import VerifiedGarbage.Impl.Sha512.RISCV64.Fn
meta import VerifiedGarbage.Impl.Sha512.RISCV64.Fn
public import VerifiedGarbage.Proof.Sha512.RISCV64.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Contract
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
public import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Cold
meta import VerifiedGarbage.Proof.Framework.Cold

/-! ### `Sha512.RISCV64.Stream.Update`, which this module and modules that import it used -/

section

/-!
# Streaming SHA-512 on RISC-V: `update`

Untrusted: everything here is checked by Lean. The structure of SHA-256's
proof (`Proof/Hmac/Stream/RISCV64/Sha256Family.lean`); the loop runs while data
is left, so every iteration consumes at least one byte. The body runs in a
frame on the stack (`WP.alloc`), which holds the compression function's
scratch space and the registers we save.
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64.Stream.Update

open VG VG.RISCV64 VG.Impl.Sha512.RISCV64.Stream VG.WriteBytes
open VG.Proof.Sha512.RISCV64.Stream
open VG.Proof.Sha512.Stream
open VG.Spec.Sha512 (HashValue stateAt blockAt compress parseBlock bytesAt)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev cnt : Nat := (s₀.gpr .a1).toNat
abbrev dp : Addr := s₀.gpr .a2
abbrev len : Nat := (s₀.gpr .a3).toNat
/-- The frame. -/
abbrev scr : Addr := s₀.sp - BitVec.ofNat 64 frameBytes
abbrev stR : Region := ⟨st s₀, 192⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, frameBytes⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (len s₀)

/-- The messages the initial state represents. -/
def R₀ (iv : HashValue) (m : List Byte) : Prop :=
  Spec.Sha512.Repr iv s₀.mem (st s₀) m ∧ s₀.gpr .a1 = BitVec.ofNat 64 m.length

/-- The caller's registers are saved in the frame. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (scr s₀ + BitVec.ofNat 64 p.2) 64 = s₀.gpr p.1

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀]
  d_st : (dR s₀).Disjoint (stR s₀)
  al : s₀.sp.toNat % 16 = 0
  sp208 : 208 ≤ s₀.sp.toNat
  scr_st : (scR s₀).Disjoint (stR s₀)
  scr_d : (scR s₀).Disjoint (dR s₀)

theorem pre_of {s₀ : State} (h : Proof.Sha512.updateRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem Pre.st_scr {s₀ : State} (hp : Pre s₀) : (stR s₀).Disjoint (scR s₀) := hp.scr_st.symm
theorem Pre.d_scr {s₀ : State} (hp : Pre s₀) : (dR s₀).Disjoint (scR s₀) := hp.scr_d.symm

theorem Pre.scr_al {s₀ : State} (hp : Pre s₀) : (scr s₀).toNat % 16 = 0 :=
  frame_aligned hp.al hp.sp208

theorem R₀.length {s₀ : State} {iv : HashValue} {m : List Byte} (h : R₀ s₀ iv m) : cnt s₀ % 128 = m.length % 128 := by
  rw [cnt, h.2, BitVec.toNat_ofNat]
  omega_arith

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = scR s₀ :: s₀.wr
  s1 : s.gpr .s1 = st s₀
  s2 : s.gpr .s2 = scr s₀
  sp : s.sp = scr s₀
  s3 : s.gpr .s3 = dp s₀ + BitVec.ofNat 64 c
  s4 : s.gpr .s4 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  s5 : s.gpr .s5 = BitVec.ofNat 64 ((cnt s₀ + c) % 128)
  repr : ∀ iv m, R₀ s₀ iv m → Spec.Sha512.Repr iv s.mem (st s₀) (m ++ (D s₀).take c)

/-- A whole block is ready at `a1`, and compressing it absorbs the first `c`
bytes of data. -/
structure Pending (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  s5 : s.gpr .s5 = 0
  t0 : s.gpr .t0 = 1
  mod : (cnt s₀ + c) % 128 = 0
  src : s.gpr .a1 = st s₀ + 64 ∨ ∃ c₀, s.gpr .a1 = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + 128 ≤ len s₀
  repr : ∀ iv m, R₀ s₀ iv m → ∀ mem', stateAt mem' (st s₀) =
      compress (stateAt s.mem (st s₀)) (blockAt s.mem (s.gpr .a1)) →
    Spec.Sha512.Repr iv mem' (st s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done (s₀ : State) (s : State) : Prop := Inv s₀ (len s₀) s ∧ s.gpr .t0 = 0

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common s₀ c s)
    (hg : ∀ r ∈ [Reg.s1, .s2, .s3, .s4], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  s1 := by rw [hg _ (by simp)]; exact h.s1
  s2 := by rw [hg _ (by simp)]; exact h.s2
  sp := hsp.trans h.sp
  s3 := by rw [hg _ (by simp)]; exact h.s3
  s4 := by rw [hg _ (by simp)]; exact h.s4
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv s₀ c s)
    (hg : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s5], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.dropLast_subset _ hr)) hm hrd hwr hsp with
    s5 := by rw [hg _ (by simp)]; exact h.s5
    repr := by rw [hm]; exact h.repr }

/-- Where the caller's registers are saved. -/
theorem saved_sub {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := by
  simp only [Impl.Sha512.RISCV64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Offset.sub_base _ (by simp only [frameBytes]; omega_arith)

/-- The saved registers are not in the compression function's scratch space. -/
theorem saved_disj {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ ⟨scr s₀, 144⟩ := by
  simp only [Impl.Sha512.RISCV64.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Offset.disjoint_base _ (by decide) (by decide)

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact Frame.bytes h.frame (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

theorem length_mid (s₀ : State) {iv : HashValue} {m : List Byte} (hm : R₀ s₀ iv m) {c : Nat} (hc : c ≤ len s₀) :
    (m ++ (D s₀).take c).length % 128 = (cnt s₀ + c) % 128 := by
  have := hm.length
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  omega_arith

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Compressing a pending block -/

theorem Pending.compress_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Pending s₀ c s) :
    WP isa compressAt s fun s' => Inv s₀ c s' ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  obtain e32 : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := Region.sub_prefix (by omega_arith)
  obtain e80 : Region.Sub ⟨scr s₀, 144⟩ (scR s₀) := Region.sub_prefix (by simp only [frameBytes]; omega_arith)
  obtain eSrc : Region.Sub ⟨s.gpr .a1, 128⟩ (stR s₀) ∨ Region.Sub ⟨s.gpr .a1, 128⟩ (dR s₀) := by
    rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ Offset.sub_base (d := 64) (n := 128) (k := 192) _ (by omega_arith))
    · exact .inr (h' ▸ Offset.sub_base (d := c₀) (n := 128) (k := len s₀) _ (by omega_arith))
  refine compressAt_ok h.s1 h.s2 rfl ((hp.st_scr.sub_left e32).sub_right e80) ?_ ?_ ?_ ?_ ?_
  · rcases h.src with h' | ⟨c₀, h', hc₀⟩
    · rw [h']
      exact Offset.disjoint (st s₀) (d := 64) (n := 128) (e := 0) (k := 64) (by omega_arith)
        (by omega_arith) (by omega_arith)
        |> fun h => by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
    · exact (hp.d_st.sub_left (h' ▸ Offset.sub_base (d := c₀) (n := 128) (k := len s₀) _
        (by omega_arith))).sub_right e32
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right e80
    · exact (hp.d_scr.sub_left e).sub_right e80
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases h.src with h' | ⟨c₀, h', hc₀⟩
      · exact ⟨stR s₀, by simp, 64, by rw [h']; rfl, by simp⟩
      · exact ⟨dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp [frameBytes]⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp [frameBytes]⟩
  · intro s' hrd hwr hcs hsp hf hstate
    have cs : ∀ r, r ∈ preserved → s'.gpr r = s.gpr r := hcs
    refine ⟨⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide)]; exact h.s1,
      by rw [cs _ (by decide)]; exact h.s2, hsp.trans h.sp,
      by rw [cs _ (by decide)]; exact h.s3,
      by rw [cs _ (by decide)]; exact h.s4,
      h.frame.trans (hf.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩, cs⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, e32⟩
      · exact ⟨scR s₀, by simp, e80⟩
    · rw [← h.saved p hp']
      refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hp')).sub_right e32
      · exact saved_disj hp'
    · rw [cs _ (by decide), h.s5, h.mod]; rfl

/-! ## A whole block straight from the data -/

theorem direct_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s)
    (hr : (cnt s₀ + c) % 128 = 0) (hl : 128 ≤ len s₀ - c) :
    WP isa (.block direct) s (Pending s₀ (c + 128)) := by
  obtain hlen := len_lt s₀
  unfold direct
  refine wp_mov fun s₁ u₁ => wp_addi (imm := 128) (by decide) fun s₂ u₂ =>
    wp_subi (imm := 128) (by decide) fun s₃ u₃ => wp_li (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .a1 → r ≠ .s3 → r ≠ .s4 → r ≠ .t0 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain h1 : s₄.gpr .a1 = dp s₀ + BitVec.ofNat 64 c := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.s3]
  refine ⟨⟨by omega_arith, by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.s1],
    by rw [g _ (by decide) (by decide) (by decide) (by decide), hI.s2],
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, by rw [m₄]; exact hI.frame,
    by rw [m₄]; exact hI.saved⟩, ?_, by rw [u₄.gpr]; rfl, by omega_arith, .inr ⟨c, h1, by omega_arith⟩, ?_⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hI.s3,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.s4,
      sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [g _ (by decide) (by decide) (by decide) (by decide), hI.s5, hr]; rfl
  · intro iv m hm mem' hs
    obtain hmod := length_mid s₀ hm (c := c) (by omega_arith)
    rw [← take_add_data]
    refine repr_append_block (hI.repr iv m hm)
      (by rw [hmod, hr, List.length_take, List.length_drop, D_length]; omega_arith) ?_
    rw [hs, m₄, h1]
    refine congrArg _ ?_
    rw [show (m ++ List.take c (D s₀)).drop (128 * ((m ++ List.take c (D s₀)).length / 128)) = [] by
      rw [List.drop_eq_nil_iff]; omega_arith, List.nil_append]
    apply parseBlock_congr
    intro k hk
    rw [show dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 k = dp s₀ + BitVec.ofNat 64 (c + k) by
      simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc], hI.data hp (by omega_arith)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hk]

/-! ## Buffering data -/

section
variable (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % 128
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (128 - rr s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := st s₀ + 64 + BitVec.ofNat 64 (rr s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt s₀ c)
end

theorem rr_lt (s₀ : State) (c : Nat) : rr s₀ c < 128 := Nat.mod_lt _ (by omega_arith)
theorem tt_le (s₀ : State) (c : Nat) : tt s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt s₀ c ≤ 128 - rr s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : rr s₀ c = (cnt s₀ + c) % 128 := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt s₀ c = min (128 - rr s₀ c) (len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : q s₀ c = st s₀ + BitVec.ofNat 64 (64 + rr s₀ c) := by
  simp only [q, BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl

theorem xs_length (s₀ : State) (c : Nat) : (xs s₀ c).length = tt s₀ c := by
  have := tt_le s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega_arith

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = scR s₀ :: s₀.wr
  s1 : s.gpr .s1 = st s₀
  s2 : s.gpr .s2 = scr s₀
  sp : s.sp = scr s₀
  s3 : s.gpr .s3 = dp s₀ + BitVec.ofNat 64 (c + j)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (len s₀ - c - tt s₀ c)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (rr s₀ c + j)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (tt s₀ c - j)
  t0 : s.gpr .t0 = 0
  mem : s.mem = writeBytes mI (q s₀ c) ((xs s₀ c).take j)

theorem write_frame (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt s₀ c) :
    Frame [stR s₀] mI (writeBytes mI (q s₀ c) ((xs s₀ c).take j)) := by
  have := tt_le' s₀ c; have := rr_lt s₀ c
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact Offset.contains_base _ (by simp only [List.length_take]; omega_arith) (by omega_arith)

theorem copy_step {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {j : Nat}
    (hj : j < tt s₀ c) {s : State} (h : Copy s₀ c sI.mem j s) :
    WP isa (.block copyBody) s fun s' =>
      Copy s₀ c sI.mem (j + 1) s' ∧ s'.gpr .t2 = BitVec.ofNat 64 (tt s₀ c - (j + 1)) := by
  obtain hlen := len_lt s₀
  have hc := hI.c_le
  obtain hr := rr_lt s₀ c
  obtain ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  -- The byte read.
  obtain hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hbyte : s.mem (dp s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega_arith)]
    exact Frame.bytes (write_frame s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega_arith) (by show c + j < len s₀; omega_arith)
  -- The byte written.
  obtain hout : InRegions s.wr (q s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hxs := xs_length s₀ c
  unfold copyBody
  refine wp_lbu (a := dp s₀ + BitVec.ofNat 64 (c + j)) (by decide) (by rw [h.s3]; simp) hin
    fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_sb (a := q s₀ c + BitVec.ofNat 64 j) (by decide) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.s1, h.s5, q]
    simp only [BitVec.ofNat_add, show BitVec.ofNat 64 64 = (64 : BitVec 64) from rfl]
    ac_rfl
  refine wp_addi (imm := 1) (by decide) fun s₄ u₄ => wp_addi (imm := 1) (by decide) fun s₅ u₅ =>
    wp_subi (imm := 1) (by decide) fun s₆ u₆ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .s3 → r ≠ .s5 → r ≠ .t2 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  obtain hx11 : s₆.gpr .t2 = BitVec.ofNat 64 (tt s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.t2, sub_ofNat (by omega_arith), Nat.sub_sub]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx11, ?_, ?_⟩, hx11⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .s1 (by decide) (by decide) (by decide) (by decide) (by decide), h.s1]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide), h.s2]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.s3, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .s4 (by decide) (by decide) (by decide) (by decide) (by decide), h.s4]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.s5, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .t0 (by decide) (by decide) (by decide) (by decide) (by decide), h.t0]
  · have hj' : j < (xs s₀ c).length := by omega_arith
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega_arith)]
    obtain hl : (List.take j (xs s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    obtain e : ((List.getD (D s₀) (c + j) 0).setWidth 64).setWidth 8 = List.getD (D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega_arith), Option.getD_some]

theorem copy_loop_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem 0 s) (ht : 0 < tt s₀ c) :
    WP isa (.loop (.block copyBody) (.nonzero .t2)) s (Copy s₀ c sI.mem (tt s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt s₀ c - j ∧ j < tt s₀ c ∧ Copy s₀ c sI.mem j s)
    ?_ (tt s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hp hI hj hc) fun s' ⟨hc', h11⟩ => ?_
  obtain hz : isa.eval (.nonzero .t2) s' = some (decide (tt s₀ c - (j + 1) ≠ 0)) := by
    show VG.RISCV64.eval (.nonzero .t2) s' = _
    rw [eval_nonzero, h11, bne, ofNat_beq_zero (by have := tt_le' s₀ c; omega_arith)]
    simp
  by_cases hl : tt s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show j + 1 = tt s₀ c by omega_arith] at hc'
  · exact .inr ⟨by rw [hz]; simp [hl], _, by omega_arith, j + 1, rfl, by omega_arith, hc'⟩

/-- The memory after copying `tt` bytes. -/
theorem copied_facts {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) :
    let mem := writeBytes sI.mem (q s₀ c) (xs s₀ c)
    Frame [stR s₀, scR s₀] s₀.mem mem ∧ Saved s₀ mem ∧ stateAt mem (st s₀) = stateAt sI.mem (st s₀) ∧
      bytesAt mem (st s₀ + 64) (rr s₀ c + tt s₀ c) = bytesAt sI.mem (st s₀ + 64) (rr s₀ c) ++ xs s₀ c := by
  intro mem
  obtain hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  obtain hxs := xs_length s₀ c
  obtain hf : Frame [stR s₀] sI.mem mem := by
    have := write_frame s₀ c sI.mem (tt s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega_arith)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_⟩
  · rw [← hI.saved p hp']
    refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact hp.st_scr.symm.sub_left (saved_sub hp')
  · apply stateAt_congr
    intro i hi
    simp only [mem, q_eq]
    exact writeBytes_before _ _ _ (by omega_arith) (by omega_arith)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega_arith)

/-- A full buffer: compress it. -/
theorem fill_pending {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hfull : rr s₀ c + tt s₀ c = 128) :
    WP isa (.block [.addi .a1 .s1 64, .li .s5 0, .li .t0 1]) s
      (Pending s₀ (c + tt s₀ c)) := by
  obtain hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  obtain hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  obtain hxs := xs_length s₀ c
  have hc := hI.c_le
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hp hI
  obtain hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_arith)]
  refine wp_addi (imm := 64) (by decide) fun s₁ u₁ => wp_li (imm := 0) (by decide) fun s₂ u₂ =>
    wp_li (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .a1 → r ≠ .s5 → r ≠ .t0 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain hx1 : s₃.gpr .a1 = st s₀ + 64 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.s1]; rfl
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₃, hmem]; exact hfr, by rw [m₃, hmem]; exact hsv⟩,
    by rw [u₃.other _ (by decide), u₂.gpr]; rfl, by rw [u₃.gpr]; rfl, by omega_arith, .inl hx1, ?_⟩
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .s1 (by decide) (by decide) (by decide), h.s1]
  · rw [g .s2 (by decide) (by decide) (by decide), h.s2]
  · rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [g .s3 (by decide) (by decide) (by decide), h.s3]
  · rw [g .s4 (by decide) (by decide) (by decide), h.s4, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [← take_add_data]
    obtain hmod := length_mid s₀ hm hc
    refine repr_append_block (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hst, hx1]
    refine congrArg (compress _) (parseBlock_congr fun k hk => ?_)
    obtain hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr s₀ c + tt s₀ c = 128 from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hnf : rr s₀ c + tt s₀ c ≠ 128) : Done s₀ s := by
  obtain hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  obtain hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  obtain hxs := xs_length s₀ c
  have hc := hI.c_le
  obtain htl : tt s₀ c = len s₀ - c := by omega_arith
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hp hI
  obtain hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_arith)]
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.s1, h.s2, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h.t0⟩
  · rw [h.s3]; congr 2; omega_arith
  · rw [h.s4]; congr 1; omega_arith
  · rw [h.s5]; congr 1; omega_arith
  · have hmod := length_mid s₀ hm hc
    rw [show len s₀ = c + tt s₀ c by omega_arith, ← take_add_data]
    refine repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega_arith) (by rw [hmem, hst]) ?_
    rw [hmod, hxs, hmem, hby]
    obtain hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_eq : fill =
    .seq (.block [.li .t2 128, .sub .t2 .t2 .s5, .shift .srl .d .t1 .s4 7])
    (.seq (.ite (.zero .t1)
        (.seq (.block [.add .t1 .s4 .s5, .shift .srl .d .t1 .t1 7])
          (.ite (.zero .t1) (.block [mov .t2 .s4]) (.block [])))
        (.block []))
    (.seq (.block [.sub .s4 .s4 .t2])
    (.seq (.loop (.block copyBody) (.nonzero .t2))
    (.seq (.block [.addi .t1 .s5 (-(128 : Nat) : Int)])
      (.ite (.zero .t1) (.block [.addi .a1 .s1 64, .li .s5 0, .li .t0 1])
        (.block [])))))) := rfl

theorem fill_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀)
    (h10 : s.gpr .t0 = 0) :
    WP isa fill s fun s' => (∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s' := by
  obtain hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  obtain hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  obtain ne : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s5], r ≠ .t1 ∧ r ≠ .t2 := by decide
  obtain hc := hI.c_le; have hlen := len_lt s₀
  rw [fill_eq]
  -- `t2 := 128 - r; t1 := len >> 7`
  refine WP.seq (wp_li (imm := 128) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ =>
    wp_srl (by decide) fun s₃ u₃ => WP.block_nil ?_)
  obtain e₃ : ∀ r, r ≠ .t1 → r ≠ .t2 → s₃.gpr r = s.gpr r := fun r h h' => by
    rw [u₃.other r h, u₂.other r h', u₁.other r h']
  obtain hI₃ : Inv s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (ne r hr).1 (ne r hr).2)
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  obtain h11₃ : s₃.gpr .t2 = BitVec.ofNat 64 (128 - rr s₀ c) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.s5, sub_ofNat (by omega_arith)]
  obtain h9₃ : s₃.gpr .t1 = BitVec.ofNat 64 ((len s₀ - c) / 128) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.s4, ofNat_shr7 (by omega_arith)]
  -- `t2 := min(t2, len)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Inv s₀ c s₄ ∧ s₄.gpr .t2 = BitVec.ofNat 64 (tt s₀ c) ∧
    s₄.gpr .t0 = 0 ∧ s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, h11₄, h10₄, hm₄⟩ => ?_)
  · have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    obtain h10₃ : s₃.gpr .t0 = 0 := by rw [e₃ _ (by decide) (by decide), h10]
    refine WP.ite (decide ((len s₀ - c) / 128 = 0))
      (by show VG.RISCV64.eval (.zero .t1) s₃ = _; rw [eval_zero, h9₃, ofNat_beq_zero (by omega_arith)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.seq (wp_add fun s₅ u₅ => wp_srl (by decide) fun s₆ u₆ => WP.block_nil ?_)
      obtain e₆ : ∀ r, r ≠ .t1 → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.other r h]
      obtain hI₆ : Inv s₀ c s₆ := hI₃.of_gpr (fun r hr => e₆ r (ne r hr).1) (by rw [u₆.mem, u₅.mem])
        (by rw [u₆.rd, u₅.rd]) (by rw [u₆.wr, u₅.wr]) (by rw [u₆.sp, u₅.sp])
      obtain h9₆ : s₆.gpr .t1 = BitVec.ofNat 64 ((len s₀ - c + rr s₀ c) / 128) := by
        rw [u₆.gpr, u₅.gpr, hI₃.s4, hI₃.s5, ← BitVec.ofNat_add, ofNat_shr7 (by omega_arith)]
      refine WP.ite (decide ((len s₀ - c + rr s₀ c) / 128 = 0))
        (by show VG.RISCV64.eval (.zero .t1) s₆ = _; rw [eval_zero, h9₆, ofNat_beq_zero (by omega_arith)])
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine wp_mov fun s₇ u₇ => WP.block_nil ⟨hI₆.of_gpr (fun r hr => u₇.other r (ne r hr).2)
          u₇.mem u₇.rd u₇.wr u₇.sp,
          ?_, by rw [u₇.other _ (by decide), e₆ _ (by decide), h10₃], by rw [u₇.mem, u₆.mem, u₅.mem, hm₃]⟩
        rw [u₇.gpr, hI₆.s4]; congr 1; omega_arith
      · simp only [decide_eq_false_iff_not] at hb'
        refine WP.block_nil ⟨hI₆, ?_, by rw [e₆ _ (by decide), h10₃], by rw [u₆.mem, u₅.mem, hm₃]⟩
        rw [e₆ _ (by decide), h11₃]; congr 1; omega_arith
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨hI₃, ?_, h10₃, hm₃⟩
      rw [h11₃]; congr 1; omega_arith
  -- `s4 -= t2`
  refine WP.seq (wp_sub fun s₅ u₅ => WP.block_nil ?_)
  obtain hC₀ : Copy s₀ c s.mem 0 s₅ := by
    obtain e : ∀ r, r ≠ .s4 → s₅.gpr r = s₄.gpr r := fun r h => u₅.other r h
    refine ⟨Nat.zero_le _, by rw [u₅.rd, hI₄.rd], by rw [u₅.wr, hI₄.wr],
      by rw [e _ (by decide), hI₄.s1], by rw [e _ (by decide), hI₄.s2], by rw [u₅.sp, hI₄.sp],
      by rw [e _ (by decide), hI₄.s3, Nat.add_zero], ?_, by rw [e _ (by decide), hI₄.s5, Nat.add_zero],
      by rw [e _ (by decide), h11₄, Nat.sub_zero], by rw [e _ (by decide), h10₄], ?_⟩
    · rw [u₅.gpr, hI₄.s4, h11₄, sub_ofNat (by omega_arith), Nat.sub_sub]
    · rw [u₅.mem, hm₄, List.take_zero, writeBytes_nil]
  -- Copy the bytes.
  refine WP.seq (WP.mono (copy_loop_ok hp hI hC₀ (by omega_arith)) fun s₆ hC => ?_)
  -- Is the buffer full?
  refine WP.seq (wp_subi (imm := 128) (by decide) fun s₇ u₇ => WP.block_nil ?_)
  obtain hC₇ : Copy s₀ c s.mem (tt s₀ c) s₇ :=
    ⟨hC.j_le, by rw [u₇.rd, hC.rd], by rw [u₇.wr, hC.wr], by rw [u₇.other _ (by decide), hC.s1],
      by rw [u₇.other _ (by decide), hC.s2], by rw [u₇.sp, hC.sp], by rw [u₇.other _ (by decide), hC.s3],
      by rw [u₇.other _ (by decide), hC.s4], by rw [u₇.other _ (by decide), hC.s5],
      by rw [u₇.other _ (by decide), hC.t2], by rw [u₇.other _ (by decide), hC.t0],
      by rw [u₇.mem, hC.mem]⟩
  obtain hz : eval (.zero .t1) s₇ = some (decide (rr s₀ c + tt s₀ c = 128)) := by
    rw [eval_zero, u₇.gpr, hC.s5, sub_beq (by omega_arith) (by omega_arith)]
  refine WP.ite (decide (rr s₀ c + tt s₀ c = 128)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hp hI hC₇ hb) fun s' h => .inl ⟨c + tt s₀ c, by omega_arith, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hp hI hC₇ hb))

/-! ## One iteration -/

theorem body_eq : updateBody =
    .seq (.block [.li .t0 0])
    (.seq (.ite (.zero .s5)
        (.seq (.block [.shift .srl .d .t1 .s4 7]) (.ite (.zero .t1) fill (.block direct)))
        fill)
      (.ite (.zero .t0) (.block []) compressAt)) := rfl

theorem fill_nv : ∀ r ∈ nvRegs, ∀ i ∈ instrs fill, dstOf i ≠ some r :=
  keepsN_all _ (by decide)

theorem direct_nv : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block direct : Prog isa), dstOf i ≠ some r :=
  keepsN_all _ (by decide)

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (hI : Inv s₀ c s) (hcl : c < len s₀) :
    WP isa updateBody s fun s' => (∃ c', c < c' ∧ Inv s₀ c' s') ∧ ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := by
  obtain hlen := len_lt s₀; have hc := hI.c_le; have hr := rr_lt s₀ c
  obtain ne : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s5], r ≠ .t0 ∧ r ≠ .t1 := by decide
  rw [body_eq]
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain hI₁ : Inv s₀ c s₁ := hI.of_gpr (fun r hr => u₁.other r (ne r hr).1) u₁.mem u₁.rd u₁.wr u₁.sp
  obtain h10₁ : s₁.gpr .t0 = 0 := by rw [u₁.gpr]; rfl
  obtain nv₁ : ∀ r ∈ nvRegs, s₁.gpr r = s.gpr r := fun r hr => u₁.other r (by revert r hr; decide)
  refine WP.seq (WP.mono (Q := fun (s' : State) => ((∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s') ∧
      ∀ r ∈ nvRegs, s'.gpr r = s₁.gpr r) ?_
    fun s' ⟨h, hnv⟩ => ?_)
  · refine WP.ite (decide (rr s₀ c = 0))
      (by show VG.RISCV64.eval (.zero .s5) s₁ = _; rw [eval_zero, hI₁.s5, ofNat_beq_zero (by omega_arith)])
      (fun hb => ?_) (fun _ => WP.gprs (fill_ok hp hI₁ hcl h10₁) fill_nv)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_srl (by decide) fun s₂ u₂ => WP.block_nil ?_)
    obtain hI₂ : Inv s₀ c s₂ := hI₁.of_gpr (fun r hr => u₂.other r (ne r hr).2) u₂.mem u₂.rd u₂.wr u₂.sp
    obtain h10₂ : s₂.gpr .t0 = 0 := by rw [u₂.other _ (by decide), h10₁]
    obtain nv₂ : ∀ r ∈ nvRegs, s₂.gpr r = s₁.gpr r := fun r hr => u₂.other r (by revert r hr; decide)
    refine WP.ite (decide ((len s₀ - c) / 128 = 0))
      (by show VG.RISCV64.eval (.zero .t1) s₂ = _
          rw [eval_zero, u₂.gpr, hI₁.s4, ofNat_shr7 (by omega_arith), ofNat_beq_zero (by omega_arith)])
      (fun _ => WP.mono (WP.gprs (fill_ok hp hI₂ hcl h10₂) fill_nv)
        fun s' ⟨h, hnv⟩ => ⟨h, fun r hr => (hnv r hr).trans (nv₂ r hr)⟩)
      (fun hb' => ?_)
    simp only [decide_eq_false_iff_not] at hb'
    exact WP.mono (WP.gprs (direct_ok hp hI₂ hb (by omega_arith)) direct_nv)
      fun s' ⟨h, hnv⟩ => ⟨.inl ⟨c + 128, by omega_arith, h⟩, fun r hr => (hnv r hr).trans (nv₂ r hr)⟩
  · have nv : ∀ r ∈ nvRegs, s'.gpr r = s.gpr r := fun r hr => (hnv r hr).trans (nv₁ r hr)
    rcases h with ⟨c', hc', hP⟩ | ⟨hD, h10⟩
    · refine WP.ite false (by show VG.RISCV64.eval (.zero .t0) s' = _; rw [eval_zero, hP.t0]; rfl)
        (fun h => by cases h) fun _ => WP.mono (hP.compress_ok hp) fun s'' ⟨h, hpr⟩ =>
          ⟨⟨c', hc', h⟩, fun r hr => (hpr r (nv_pres r hr)).trans (nv r hr)⟩
    · refine WP.ite true (by show VG.RISCV64.eval (.zero .t0) s' = _; rw [eval_zero, h10]; rfl)
        (fun _ => WP.block_nil ⟨⟨len s₀, hcl, hD⟩, nv⟩) fun h => by cases h

/-! ## Prologue and epilogue -/

/-- The prologue after saving. -/
def prologue : List Instr :=
  [mov .s1 .a0, mov .s2 .t0, mov .s3 .a2, mov .s4 .a3, .logicImm .and .s5 .a1 127]

theorem update_eq : updateMain = .seq (.block (save ++ prologue))
    (.seq (.ite (.zero .s4) (.block []) (.loop updateBody (.nonzero .s4))) (.block restore)) := rfl

/-- The state the frame's body starts in. -/
abbrev inner (s₀ : State) : State := allocd frameBytes s₀

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (save ++ prologue)) (inner s₀) (Inv s₀ 0) := by
  have hsp : (inner s₀).sp = scr s₀ := rfl
  refine save_ok (by rw [hsp]; exact hp.scr_al)
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [inner, allocd_wr],
      Offset.contains_base _ (by simp only [frameBytes]; omega_arith) (by omega_arith)⟩)
    fun s₁ t₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  unfold prologue
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_andi127 fun s₆ u₆ => WP.block_nil ?_
  obtain hm₆ : s₆.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
    rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]; rfl
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun iv m hm => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; rfl
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁ _ (by decide)]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), t₁, hsp]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁, hsp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), allocd_gpr]
    simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), allocd_gpr]
    simp
  · rw [hm₆]; exact (saveMem_frame _ _ _).mono (by simp)
  · rw [hm₆]; exact saveMem_saved _ _ _
  · rw [u₆.gpr, u₅.other .a1 (by decide), u₄.other .a1 (by decide),
      u₃.other .a1 (by decide), u₂.other .a1 (by decide), g₁ _ (by decide), Nat.add_zero]; rfl
  · rw [List.take_zero, List.append_nil, hm₆]
    exact repr_congr (fun i hi => Frame.bytes (saveMem_frame s₀.mem (scr s₀) s₀.gpr) (R := stR s₀)
      (by simpa using hp.st_scr) (by simp) hi) hm.1

/-- The epilogue's postcondition. -/
def Post (s₀ s' : State) : Prop :=
  (∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = scr s₀ ∧ s'.wr = scR s₀ :: s₀.wr ∧
    Proof.Sha512.updateRISCV64.post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hI : Inv s₀ (len s₀) s) :
    WP isa (.block restore) s (Post s₀) := by
  refine restore_ok (scr := scr s₀) hI.s2 hp.scr_al
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hI.rd, hI.wr, hp.wr],
      Offset.contains_base _ (by simp only [frameBytes]; omega_arith) (by omega_arith)⟩) s₀.gpr
    hI.saved fun s' hs _ hmem _ hwr hsp =>
      ⟨hs, by rw [hsp, hI.sp], by rw [hwr, hI.wr], fun iv m hr hc => ?_⟩
  have := hI.repr iv m ⟨hr, hc⟩
  rwa [List.take_of_length_le (by rw [D_length]), ← hmem] at this

theorem prologue_nv : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block (save ++ prologue) : Prog isa),
    dstOf i ≠ some r := keepsN_all _ (by decide)

theorem restore_nv : ∀ r ∈ nvRegs, ∀ i ∈ instrs (.block restore : Prog isa), dstOf i ≠ some r :=
  keepsN_all _ (by decide)

/-- No instruction of `updateMain` writes the callee-saved registers it does not save. -/
theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs updateMain, dstOf i ≠ some r :=
  keepsU_all _ (by rw [← Code.allInstrs_eq]; decide +kernel)

/-- `update`'s body, in its frame: the callee-saved registers are kept. -/
theorem correctMain {s₀ : State} (hp : Pre s₀) :
    WP isa updateMain (inner s₀) fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.gpr .ra = s₀.gpr .ra ∧ s'.sp = scr s₀ ∧ s'.wr = scR s₀ :: s₀.wr ∧
      Proof.Sha512.updateRISCV64.post s₀ s' := by
  obtain hlen := len_lt s₀
  refine WP.mono (WP.gprs (Q := fun (s' : State) => Post s₀ s' ∧ ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r) ?_
      untouched_ok)
    fun s' ⟨⟨⟨hsv, hsp, hwr, hpost⟩, hnv⟩, hu⟩ => ⟨fun r hr => ?_, hsv (.ra, 144) (by decide), hsp, hwr,
      hpost⟩
  · rw [update_eq]
    refine WP.seq (WP.mono (WP.gprs (rs := nvRegs) (prologue_ok hp) prologue_nv)
      fun s₁ ⟨hI, hnv₁⟩ => ?_)
    refine WP.seq (WP.mono (Q := fun (s : State) => Inv s₀ (len s₀) s ∧ ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r) ?_
      fun s₂ ⟨hI₂, hnv₂⟩ => WP.mono (WP.gprs (rs := nvRegs) (epilogue_ok hp hI₂) restore_nv)
        fun s₃ ⟨h, hnv₃⟩ => ⟨h, fun r hr => (hnv₃ r hr).trans (hnv₂ r hr)⟩)
    refine WP.ite (decide (len s₀ = 0))
      (by show VG.RISCV64.eval (.zero .s4) s₁ = _
          rw [eval_zero, hI.s4, Nat.sub_zero, ofNat_beq_zero (by omega_arith)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨hb ▸ hI, hnv₁⟩
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s ∧
          ∀ r ∈ nvRegs, s.gpr r = s₀.gpr r) ?_ (len s₀) s₁
        ⟨0, rfl, by omega_arith, hI, hnv₁⟩
      rintro n s ⟨c, rfl, hcl, hI, hnv⟩
      refine WP.mono (body_ok hp hI hcl) fun s' ⟨⟨c', hc, hI'⟩, hnv'⟩ => ?_
      obtain hnv'' : ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r := fun r hr => (hnv' r hr).trans (hnv r hr)
      have hc' := hI'.c_le
      obtain hz : isa.eval (.nonzero .s4) s' = some (decide (len s₀ - c' ≠ 0)) := by
        show VG.RISCV64.eval (.nonzero .s4) s' = _
        rw [eval_nonzero, hI'.s4, bne, ofNat_beq_zero (by omega_arith)]
        simp
      by_cases hl : len s₀ - c' = 0
      · refine .inl ⟨by rw [hz]; simp [hl], ?_, hnv''⟩
        rwa [show c' = len s₀ by omega_arith] at hI'
      · exact .inr ⟨by rw [hz]; simp [hl], len s₀ - c', by omega_arith, c', rfl, by omega_arith, hI', hnv''⟩
  · have key : ∀ r ∈ preserved, r ∈ untouched ∨ r ∈ nvRegs ∨ r ∈ saved.map Prod.fst := by decide
    rcases key r hr with hr' | hr' | hr'
    · exact hu r hr'
    · exact hnv r hr'
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hr'
      exact hsv p hp'

/-- The long path, in its frame. -/
theorem correctLong {s₀ : State} (hp : Pre s₀) :
    WP isa updateLong s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha512.updateRISCV64.post s₀ s' := by
  refine WP.alloc (by decide) (by simp only [frameBytes]; exact hp.sp208)
    (WP.mono (correctMain hp) fun s' ⟨hk, hra, hsp, hwr, hpost⟩ m u f => ?_)
  rw [freed_eq (by rw [hwr]; rfl) (by rw [hsp]; rfl)]
  -- The `free` loses the frame's bytes, which lie apart from the state.
  exact ⟨⟨hk, rfl, hra⟩, fun iv msg hr hc => repr_congr (fun i hi =>
    lost_byte f (R := stR s₀) hp.scr_st.symm hi) (hpost iv msg hr hc)⟩

/-! ## The short path

When no block can complete, `short` copies the data into the buffer, after
`rr s₀ 0` bytes, with no frame. -/

/-- The state while copying: `j` bytes copied. -/
structure SCopy (s₀ : State) (j : Nat) (s : State) : Prop where
  j_le : j ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  a2 : s.gpr .a2 = dp s₀ + BitVec.ofNat 64 j
  t3 : s.gpr .t3 = st s₀ + BitVec.ofNat 64 (rr s₀ 0) + BitVec.ofNat 64 j
  t4 : s.gpr .t4 = dp s₀ + BitVec.ofNat 64 (len s₀)
  mem : s.mem = writeBytes s₀.mem (q s₀ 0) ((xs s₀ 0).take j)

theorem add_ofNat_bne (x : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (x + BitVec.ofNat 64 a != x + BitVec.ofNat 64 b) = decide (a ≠ b) := by
  by_cases h : a = b
  · subst h; simp
  · have e : x + BitVec.ofNat 64 a ≠ x + BitVec.ofNat 64 b := by
      intro e
      obtain e' := congrArg BitVec.toNat ((BitVec.add_right_inj x).mp e)
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e'
      exact h e'
    simp [e, h]

theorem short_step {s₀ : State} (hp : Pre s₀) (hs : rr s₀ 0 + len s₀ < 128) {j : Nat} (hj : j < len s₀)
    {s : State} (h : SCopy s₀ j s) :
    WP isa (.block shortBody) s fun s' =>
      SCopy s₀ (j + 1) s' ∧ VG.RISCV64.eval (.ne .a2 .t4) s' = some (decide (j + 1 ≠ len s₀)) := by
  obtain hr := rr_lt s₀ 0
  obtain htt : tt s₀ 0 = len s₀ := by simp only [tt_eq]; omega_arith
  obtain hxs := xs_length s₀ 0
  -- The byte read.
  obtain hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 j) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hbyte : s.mem (dp s₀ + BitVec.ofNat 64 j) = (D s₀).getD j 0 := by
    rw [h.mem, D_getD s₀ hj]
    exact Frame.bytes (write_frame s₀ 0 s₀.mem j (by omega_arith)) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; have := len_lt s₀; omega_arith) hj
  -- The byte written.
  obtain hout : InRegions s.wr (q s₀ 0 + BitVec.ofNat 64 j) 1 :=
    ⟨stR s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  unfold shortBody
  refine wp_lbu (a := dp s₀ + BitVec.ofNat 64 j) (by decide) (by rw [h.a2]; simp) hin fun s₁ u₁ => ?_
  refine wp_sb (a := q s₀ 0 + BitVec.ofNat 64 j) (by decide) ?_ (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  · rw [u₁.other _ (by decide), h.t3, q]
    simp only [show BitVec.ofNat 64 64 = (64 : BitVec 64) from rfl]
    ac_rfl
  refine wp_addi (imm := 1) (by decide) fun s₃ u₃ => wp_addi (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
  obtain ha2 : s₄.gpr .a2 = dp s₀ + BitVec.ofNat 64 (j + 1) := by
    rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.a2, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  obtain ht4 : s₄.gpr .t4 = dp s₀ + BitVec.ofNat 64 (len s₀) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t4]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ha2, ?_, ht4, ?_⟩, ?_⟩
  · rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
  · rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
  · rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.t3, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  · have hj' : j < (xs s₀ 0).length := by omega_arith
    rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega_arith)]
    obtain hl : (List.take j (xs s₀ 0)).length = j := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    obtain e : ((List.getD (D s₀) j 0).setWidth 64).setWidth 8 = List.getD (D s₀) j 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show j < (D s₀).length by rw [D_length]; omega_arith), Option.getD_some]
  · show some (s₄.gpr .a2 != s₄.gpr .t4) = _
    have := len_lt s₀
    rw [ha2, ht4, add_ofNat_bne _ (by omega_arith) (by omega_arith)]

/-- The state after the short path represents the message followed by the data. -/
theorem short_repr {s₀ : State} (hs : rr s₀ 0 + len s₀ < 128) {iv : HashValue} {m : List Byte}
    (hm : R₀ s₀ iv m) : Spec.Sha512.Repr iv (writeBytes s₀.mem (q s₀ 0) (xs s₀ 0)) (st s₀) (m ++ D s₀) := by
  obtain hr := rr_lt s₀ 0
  obtain htt : tt s₀ 0 = len s₀ := by simp only [tt_eq]; omega_arith
  obtain hxs := xs_length s₀ 0
  obtain hxD : xs s₀ 0 = D s₀ := by
    simp only [xs, List.drop_zero]
    exact List.take_of_length_le (by rw [D_length]; omega_arith)
  obtain hml : m.length % 128 = rr s₀ 0 := by rw [rr_eq, Nat.add_zero, hm.length]
  have hb := hm.1.2
  rw [hml] at hb
  rw [← hxD]
  refine repr_append_buf hm.1 (by rw [hml, hxs]; omega_arith) ?_ ?_
  · apply stateAt_congr
    intro i hi
    simp only [q_eq]
    exact writeBytes_before _ _ _ (by omega_arith) (by omega_arith)
  · rw [hml, ← hb]
    exact bytesAt_writeBytes _ _ _ _ (by omega_arith)

theorem short_eq : short =
    Code.iteCold (.zero .a3) (.block [])
      (.seq (.block [.add .t3 .a0 .t0, .add .t4 .a2 .a3]) (.loop (.block shortBody) (.ne .a2 .t4))) := rfl

/-- The short path, from the state `s` the first block leaves: the
registers it reads as on entry, `t0 = r`. -/
theorem short_ok {s₀ : State} (hp : Pre s₀) (hs : rr s₀ 0 + len s₀ < 128) {s : State}
    (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp)
    (h0 : s.gpr .a0 = st s₀) (h2 : s.gpr .a2 = dp s₀) (h3 : s.gpr .a3 = s₀.gpr .a3)
    (ht0 : s.gpr .t0 = BitVec.ofNat 64 (rr s₀ 0)) :
    WP isa short s fun s' => s'.sp = s₀.sp ∧ Proof.Sha512.updateRISCV64.post s₀ s' := by
  obtain hlen := len_lt s₀
  obtain e3 : s₀.gpr .a3 = BitVec.ofNat 64 (len s₀) := by simp
  rw [short_eq, WP.iteCold_iff]
  refine WP.ite (decide (len s₀ = 0))
    (by show VG.RISCV64.eval (.zero .a3) s = _; rw [eval_zero, h3, e3, ofNat_beq_zero (by omega_arith)])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨hsp, fun iv m hr _ => ?_⟩
    show Spec.Sha512.Repr iv s.mem (st s₀) (m ++ D s₀)
    rw [hm, show D s₀ = [] from List.eq_nil_of_length_eq_zero (by rw [D_length]; exact hb), List.append_nil]
    exact hr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (wp_add fun s₁ u₁ => wp_add fun s₂ u₂ => WP.block_nil ?_)
    obtain hC₀ : SCopy s₀ 0 s₂ := by
      refine ⟨Nat.zero_le _, by rw [u₂.rd, u₁.rd, hrd], by rw [u₂.wr, u₁.wr, hwr],
        by rw [u₂.sp, u₁.sp, hsp], ?_, ?_, ?_, ?_⟩
      · rw [u₂.other _ (by decide), u₁.other _ (by decide), h2, BitVec.add_zero]
      · rw [u₂.other _ (by decide), u₁.gpr, h0, ht0, BitVec.add_zero]
      · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h2, h3, ← e3]
      · rw [u₂.mem, u₁.mem, hm, List.take_zero, writeBytes_nil]
    refine WP.loop (M := isa) (fun n s => ∃ j, n = len s₀ - j ∧ j < len s₀ ∧ SCopy s₀ j s)
      ?_ (len s₀) s₂ ⟨0, by omega_arith, by omega_arith, hC₀⟩
    rintro n s ⟨j, rfl, hj, hc⟩
    refine WP.mono (short_step hp hs hj hc) fun s' ⟨hc', hz⟩ => ?_
    by_cases hl : j + 1 = len s₀
    · refine .inl ⟨by show VG.RISCV64.eval (.ne .a2 .t4) s' = _; rw [hz]; simp [hl], hc'.sp, fun iv m hr hl' => ?_⟩
      obtain hmem : s'.mem = writeBytes s₀.mem (q s₀ 0) (xs s₀ 0) := by
        rw [hc'.mem, hl, List.take_of_length_le (by rw [xs_length]; simp only [tt_eq]; omega_arith)]
      show Spec.Sha512.Repr iv s'.mem (st s₀) (m ++ D s₀)
      rw [hmem]
      exact short_repr hs ⟨hr, hl'⟩
    · exact .inr ⟨by show VG.RISCV64.eval (.ne .a2 .t4) s' = _; rw [hz]; simp [hl], _, by omega_arith, j + 1, rfl, by omega_arith, hc'⟩

/-- No instruction of `short` writes a callee-saved register or `ra`. -/
theorem short_keeps : ∀ r ∈ (.ra :: preserved : List Reg), ∀ i ∈ instrs short, dstOf i ≠ some r := by
  decide

/-! ## `update` -/

theorem update_eq' : update = .seq (.block [.logicImm .and .t0 .a1 127, .logicImm .xor .t2 .t0 127])
    (Code.iteCold (.ltu .t2 .a3) updateLong short) := rfl

theorem xor127 {r : Nat} (h : r < 128) :
    BitVec.ofNat 64 r ^^^ BitVec.ofInt 64 127 = BitVec.ofNat 64 (127 - r) := by
  apply BitVec.eq_of_toNat_eq
  obtain e : ∀ r < 128, r ^^^ 127 = 127 - r := by decide
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h]),
    Nat.mod_eq_of_lt (by omega_using []), show (BitVec.ofInt 64 127).toNat = 127 from rfl, e r h]

theorem wp_xori127 {is : List Instr} {s : State} {Q : State → Prop} {d n : Reg} {r : Nat} (hr : r < 128)
    (hn : s.gpr n = BitVec.ofNat 64 r)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 (127 - r)) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .xor d n 127 :: is)) s Q := by
  refine WP.cons (exec_logicImm (by decide)) ?_
  simp only
  rw [hn, xor127 hr]; exact k _ (Upd.write _ _ _)

/-- A precondition `Pre` of a state is one of another with the same
arguments, regions and stack pointer. -/
theorem Pre.of_eq {s s' : State} (hp : Pre s) (h0 : s'.gpr .a0 = s.gpr .a0) (h2 : s'.gpr .a2 = s.gpr .a2)
    (h3 : s'.gpr .a3 = s.gpr .a3) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Pre s' := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [dR, stR, scR, scr, st, dp, len, h0, h2, h3, hrd, hwr, hsp]
  exacts [p1, p2, p3, p4, p5, p6, p7]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha512.updateRISCV64.post s₀ s' := by
  obtain hlen := len_lt s₀
  obtain hr := rr_lt s₀ 0
  rw [update_eq']
  refine WP.seq (wp_andi127 fun s₁ u₁ => wp_xori127 (r := rr s₀ 0) hr
    (by rw [u₁.gpr, rr_eq, Nat.add_zero]) fun s₂ u₂ => WP.block_nil ?_)
  obtain ht0 : s₂.gpr .t0 = BitVec.ofNat 64 (rr s₀ 0) := by
    rw [u₂.other _ (by decide), u₁.gpr, rr_eq, Nat.add_zero]
  have ht2 : s₂.gpr .t2 = BitVec.ofNat 64 (127 - rr s₀ 0) := u₂.gpr
  obtain g : ∀ r, r ≠ .t0 → r ≠ .t2 → s₂.gpr r = s₀.gpr r := fun r h h' => by
    rw [u₂.other r h', u₁.other r h]
  obtain hm : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
  obtain hrd : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd]
  obtain hwr : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  obtain hsp : s₂.sp = s₀.sp := by rw [u₂.sp, u₁.sp]
  obtain g0 := g .a0 (by decide) (by decide)
  obtain g1 := g .a1 (by decide) (by decide)
  obtain g2 := g .a2 (by decide) (by decide)
  obtain g3 := g .a3 (by decide) (by decide)
  -- The callee-saved registers and `ra` are as on entry.
  obtain abi : ∀ s', (∀ r ∈ (.ra :: preserved : List Reg), s'.gpr r = s₂.gpr r) → s'.sp = s₀.sp →
      abiPreserved s₀ s' := fun s' hk hs =>
    ⟨fun r hr => (hk r (List.mem_cons_of_mem _ hr)).trans
      (g r (by revert r hr; decide) (by revert r hr; decide)), hs,
      (hk .ra List.mem_cons_self).trans (g .ra (by decide) (by decide))⟩
  rw [WP.iteCold_iff]
  refine WP.ite (decide (127 - rr s₀ 0 < len s₀))
    (by show some (decide (s₂.gpr .t2 < s₂.gpr .a3)) = _
        exact congrArg some (decide_eq_decide.mpr (by
          rw [ht2, g3, BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)])))
    (fun _ => ?_) (fun hb => ?_)
  · refine WP.mono (correctLong (hp.of_eq g0 g2 g3 hrd hwr hsp)) fun s' ⟨ha, hq⟩ => ⟨?_, ?_⟩
    · exact abi s' (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ha.2.2
        · exact ha.1 r hr) (ha.2.1.trans hsp)
    · intro iv m hr' hc
      have := hq iv m (by rw [hm, g0]; exact hr') (by rw [g1]; exact hc)
      rwa [hm, g0, g2, g3] at this
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (WP.gprs (rs := .ra :: preserved)
      (short_ok hp (by omega_arith) hm hrd hwr hsp g0 g2 g3 ht0) short_keeps)
      fun s' ⟨⟨hs, hq⟩, hk⟩ => ⟨abi s' hk hs, hq⟩

theorem agree₀ {s₁ s₂ : State} (hpub : Proof.Sha512.updateRISCV64.pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0, .a1, .a2, .a3]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.RISCV64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [p1, p2, p3, p4]

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 192⟩]

theorem update_verified : Verified RISCV64.target update Proof.Sha512.updateRISCV64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of hs)
    exact ⟨t, s', he, h⟩
  · exact VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum])
  · refine ⟨sat, rfl, rfl, ?_, by decide, by decide, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.RISCV64.Stream.Update

end

end

/-! ### `Sha512.RISCV64.Stream.Init`, which this module and modules that import it used -/

section

/-!
# Streaming SHA-512 on RISC-V: `init`

Untrusted: everything here is checked by Lean.
-/

@[expose] public section

namespace VG.Proof.Sha512.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.ByteLoad VG.Impl.Sha512.RISCV64.Stream VG.Impl.Words.RISCV64
open VG.Proof.Sha512.RISCV64 (stateAt_eq readW_writeW_word)
open VG.Spec.Sha512 (stateAt H0_384 H0_512 H0_512_224 H0_512_256 HashValue)

/-- The first `k` words of `iv` are stored. -/
structure InitI (iv : HashValue) (s₀ : State) (k : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = s₀.gpr .a0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ j < k, s.mem.readW (s₀.gpr .a0 + BitVec.ofNat 64 (8 * j)) 64 = iv[j]!

theorem init_step (iv : HashValue) {s₀ : State} (hp : (Proof.Sha512.initRISCV64 iv).pre s₀)
    {k : Nat} (hk : k < 8) {s : State} (h : InitI iv s₀ k s) :
    WP isa (.block (li64 .t0 .t1 iv[k]! ++ Impl.Words64.RISCV64.storeLE64 .t0 .t1 .t2 .a0 (8 * k))) s
      (InitI iv s₀ (k + 1)) := by
  rw [WP.block_append_iff]
  refine WP.mono (li64_ok (by decide) _) fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (Words64.storeLE64_ok (by decide) (by decide) (by decide) (by decide) (by omega_using [hk]) ?_)
    fun s₂ ⟨g₂, m₂, rd₂, wr₂, _⟩ => ?_
  · rw [RegUpd.wr_write, RegUpd.wr_write, RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), h.wr, h.a0, hp.2]
    exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  have ga : s₂.gpr .a0 = s₀.gpr .a0 := by
    rw [g₂ _ (by decide) (by decide)]; simp only [RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h.a0]
  refine ⟨ga, rd₂.trans h.rd, wr₂.trans h.wr, fun j hj => ?_⟩
  · rw [m₂]
    simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h.a0]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [readW_writeW_word _ _ _ (by omega_arith) hk (by omega_using [hj])]
      exact h.words j hj
    · exact Mem.readW_writeW_self64 _ _ _

/-- No instruction of `init` writes a register other than `t0`, `t1` and `t2`. -/
def initDst : Option Reg → Bool
  | some .t0 | some .t1 | some .t2 | none => true
  | _ => false

theorem init_correct (iv : HashValue) {s₀ : State} (hp : (Proof.Sha512.initRISCV64 iv).pre s₀) :
    WP isa (initWith iv) s₀ fun s' => (Proof.Sha512.initRISCV64 iv).post s₀ s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (InitI iv s₀) (fun k s hk h => init_step iv hp hk h) 8
    (Nat.le_refl _) s₀ ⟨rfl, rfl, rfl, fun _ h => absurd h (by omega_using [])⟩) fun s' h => ?_
  refine Proof.Sha512.Stream.repr_nil (stateAt_eq fun k hk => ?_)
  rw [h.words k hk, getElem!_pos iv k hk]

theorem init_dst (iv : HashValue) (r : Reg) (hr : r ≠ .t0 ∧ r ≠ .t1 ∧ r ≠ .t2) :
    ∀ i ∈ instrs (initWith iv), dstOf i ≠ some r := by
  intro i hi e
  have hc : ((instrs (initWith iv)).all fun i => initDst (dstOf i)) = true := by
    simp only [initWith, instrs, List.all_flatMap, List.all_eq_true, List.mem_range]
    intro k _
    simp [li64, li32, Impl.Words64.RISCV64.storeLE64, storeLE32, dstOf, initDst]
  have := List.all_eq_true.mp hc i hi
  rw [e] at this
  revert this hr; cases r <;> decide

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with | .a0 => 0x1000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 192⟩]

theorem noCalls_init (iv : HashValue) : (initWith iv).noCalls = true := rfl

/-- `init`'s functional correctness and calling-convention obligations. -/
theorem initFrom_ok (iv : HashValue) :
    ∀ s, (Proof.Sha512.initRISCV64 iv).pre s → ∃ t s', Exec isa (initWith iv) s t s' ∧
      abiPreserved s s' ∧ (Proof.Sha512.initRISCV64 iv).post s s' := by
  intro s hs
  obtain ⟨t, s', he, h⟩ := init_correct iv hs
  refine ⟨t, s', he, ⟨fun r hr => Exec.gpr (init_dst iv r ?_) he (.inl (noCalls_init iv)),
    Exec.sp he, Exec.gpr (init_dst iv .ra (by decide)) he (.inl (noCalls_init iv))⟩, h⟩
  revert hr; revert r; decide

theorem agree₀ {s₁ s₂ : State} (iv : HashValue) (hpub : (Proof.Sha512.initRISCV64 iv).pub s₁ s₂) :
    VG.RISCV64.Taint.Agree (VG.RISCV64.Taint.ofRegs [.a0]) s₁ s₂ := by
  obtain ⟨h1, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h1

theorem init384_verified : Verified RISCV64.target (initWith H0_384) (Proof.Sha512.initRISCV64 H0_384) :=
  ⟨initFrom_ok H0_384, VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ h => agree₀ H0_384 h) (by taint_decide), ⟨initSat, rfl, rfl⟩⟩

theorem init512_verified : Verified RISCV64.target (initWith H0_512) (Proof.Sha512.initRISCV64 H0_512) :=
  ⟨initFrom_ok H0_512, VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ h => agree₀ H0_512 h) (by taint_decide), ⟨initSat, rfl, rfl⟩⟩

theorem init512_224_verified : Verified RISCV64.target (initWith H0_512_224) (Proof.Sha512.initRISCV64 H0_512_224) :=
  ⟨initFrom_ok H0_512_224, VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ h => agree₀ H0_512_224 h) (by taint_decide), ⟨initSat, rfl, rfl⟩⟩

theorem init512_256_verified : Verified RISCV64.target (initWith H0_512_256) (Proof.Sha512.initRISCV64 H0_512_256) :=
  ⟨initFrom_ok H0_512_256, VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ h => agree₀ H0_512_256 h) (by taint_decide), ⟨initSat, rfl, rfl⟩⟩

end VG.Proof.Sha512.RISCV64.Stream

end

end

/-!
# HMAC over the SHA-512 family on RISC-V

The streaming functions of SHA-384, SHA-512, SHA-512/224 and SHA-512/256 as
HMAC's code over any streaming hash function calls them (`hash`): the hash
function's `init` (from its initial hash value `iv`) and `finalize` (writing
its `D`-byte digest), and SHA-512's `update`, which keep their working space
in frames of their own, within 208 bytes below the stack pointer; and what
the proofs need of them (`ok`).
-/

@[expose] public section

namespace VG.Proof.Hmac.Stream.RISCV64.Sha512Family

open VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open Spec.Sha512 (HashValue)

/-- The streaming functions of the hash function with initial hash value
`iv` (whose `init` is `initN`) and a digest of `D` bytes, written by
`finC` (named `finN`): `Impl.Sha512.RISCV64.Fn.hash`. -/
abbrev hash (iv : HashValue) (D : Nat) (initN finN : String) (finC : Prog isa) : Hash :=
  Impl.Sha512.RISCV64.Fn.hash iv D initN finN finC

theorem updSd : sdepth Impl.Sha512.RISCV64.Stream.update ≤ 208 := by decide +kernel

/-- What the proofs need of them, for a hash function `HF` of SHA-512's block
whose digest is the first `D` bytes of the final hash value from `iv`. -/
def ok (iv : HashValue) (D : Nat) (initN finN : String) (finC : Prog isa) (HF : Spec.Hmac.HashFunction)
    (hB : HF.blockSize = 128) (hD : 0 < D ∧ D ≤ 64)
    (hinit : Verified RISCV64.target (Impl.Sha512.RISCV64.Stream.initWith iv) (Proof.Sha512.initRISCV64 iv))
    (hfin : Verified RISCV64.target finC (Proof.Sha512.finalizeDRISCV64 D)) (hfs : sdepth finC ≤ 208)
    (htake : ∀ x, HF.hash x = (Spec.Sha512.finalHash iv x).take D) :
    HashOK (hash iv D initN finN finC) where
  SH := ⟨HF, 192, D, Spec.Sha512.Repr iv⟩
  hS := rfl
  hD := rfl
  hB := hB
  hb := .inr rfl
  hN := by show 0 < 64 ∧ 64 ≤ 64; decide
  hD0 := hD.1
  hD64 := hD.2
  hF := by show 208 ≤ 1024; decide
  init s hs := hinit.1 s hs
  upd s hs := by
    obtain ⟨t, s', he, ha, h⟩ := Proof.Sha512.RISCV64.Stream.Update.update_verified.1 s hs
    exact ⟨t, s', he, ha, fun m hr hc => h iv m hr hc⟩
  fin s hs := by
    obtain ⟨t, s', he, ha, h⟩ := hfin.1 s hs
    exact ⟨t, s', he, ha, fun m hr hl hc => (h iv m hr hl hc).trans (htake m).symm⟩
  initSd := Nat.zero_le _
  updSd := updSd
  finSd := hfs
  reloc m m' p q x hx h hr := Proof.Hmac.Stream.sha512_reloc iv m m' p q x hx h hr
  congr _ _ _ _ h hr := Proof.Sha512.Stream.repr_congr (fun i hi => h i hi) hr
  hashLen x := by
    rw [htake, List.length_take, Proof.Hmac.Generic.Common.finalHash_length]
    show min D 64 = D
    omega_using [hD]

end VG.Proof.Hmac.Stream.RISCV64.Sha512Family
