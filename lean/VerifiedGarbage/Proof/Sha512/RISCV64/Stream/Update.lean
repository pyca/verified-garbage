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
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Compress

/-!
# Streaming SHA-512 on RISC-V: `update`

Untrusted: everything here is checked by Lean. The structure of SHA-256's
proof (`Proof/Sha256/RISCV64/Stream/Update.lean`); the loop runs while data
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
  have e32 : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := Region.sub_prefix (by omega_arith)
  have e80 : Region.Sub ⟨scr s₀, 144⟩ (scR s₀) := Region.sub_prefix (by simp only [frameBytes]; omega_arith)
  have eSrc : Region.Sub ⟨s.gpr .a1, 128⟩ (stR s₀) ∨ Region.Sub ⟨s.gpr .a1, 128⟩ (dR s₀) := by
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
  have hlen := len_lt s₀
  unfold direct
  refine wp_mov fun s₁ u₁ => wp_addi (imm := 128) (by decide) fun s₂ u₂ =>
    wp_subi (imm := 128) (by decide) fun s₃ u₃ => wp_li (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
  have g : ∀ r, r ≠ .a1 → r ≠ .s3 → r ≠ .s4 → r ≠ .t0 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h1 : s₄.gpr .a1 = dp s₀ + BitVec.ofNat 64 c := by
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
    have hmod := length_mid s₀ hm (c := c) (by omega_arith)
    rw [← take_add_data]
    refine repr_append_block (hI.repr iv m hm)
      (by rw [hmod, hr, List.length_take, List.length_drop, D_length]; omega_arith) ?_
    rw [hs, m₄, h1]
    congr 1
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
  have hlen := len_lt s₀
  have hc := hI.c_le
  have hr := rr_lt s₀ c
  have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hbyte : s.mem (dp s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega_arith)]
    exact Frame.bytes (write_frame s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega_arith) (by show c + j < len s₀; omega_arith)
  -- The byte written.
  have hout : InRegions s.wr (q s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hxs := xs_length s₀ c
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
  have g : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .s3 → r ≠ .s5 → r ≠ .t2 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hx11 : s₆.gpr .t2 = BitVec.ofNat 64 (tt s₀ c - (j + 1)) := by
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
    have hl : (List.take j (xs s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    have e : ((List.getD (D s₀) (c + j) 0).setWidth 64).setWidth 8 = List.getD (D s₀) (c + j) 0 := by
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
  have hz : isa.eval (.nonzero .t2) s' = some (decide (tt s₀ c - (j + 1) ≠ 0)) := by
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
  have hr := rr_lt s₀ c; have ht' := tt_le' s₀ c
  have hxs := xs_length s₀ c
  have hf : Frame [stR s₀] sI.mem mem := by
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
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_arith)]
  refine wp_addi (imm := 64) (by decide) fun s₁ u₁ => wp_li (imm := 0) (by decide) fun s₂ u₂ =>
    wp_li (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .a1 → r ≠ .s5 → r ≠ .t0 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hx1 : s₃.gpr .a1 = st s₀ + 64 := by
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
    have hmod := length_mid s₀ hm hc
    refine repr_append_block (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hst, hx1]
    refine congrArg (compress _) (parseBlock_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr s₀ c + tt s₀ c = 128 from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done {s₀ : State} (hp : Pre s₀) {c : Nat} {sI : State} (hI : Inv s₀ c sI) {s : State}
    (h : Copy s₀ c sI.mem (tt s₀ c) s) (hnf : rr s₀ c + tt s₀ c ≠ 128) : Done s₀ s := by
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have hxs := xs_length s₀ c
  have hc := hI.c_le
  have htl : tt s₀ c = len s₀ - c := by omega_arith
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hp hI
  have hmem : s.mem = writeBytes sI.mem (q s₀ c) (xs s₀ c) := by
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
    have hb := (hI.repr iv m hm).2
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
  have hr := rr_lt s₀ c; have ht := tt_le s₀ c; have ht' := tt_le' s₀ c
  have hrr := rr_eq s₀ c; have htt := tt_eq s₀ c
  have ne : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s5], r ≠ .t1 ∧ r ≠ .t2 := by decide
  have hc := hI.c_le; have hlen := len_lt s₀
  rw [fill_eq]
  -- `t2 := 128 - r; t1 := len >> 7`
  refine WP.seq (wp_li (imm := 128) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ =>
    wp_srl (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have e₃ : ∀ r, r ≠ .t1 → r ≠ .t2 → s₃.gpr r = s.gpr r := fun r h h' => by
    rw [u₃.other r h, u₂.other r h', u₁.other r h']
  have hI₃ : Inv s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (ne r hr).1 (ne r hr).2)
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  have h11₃ : s₃.gpr .t2 = BitVec.ofNat 64 (128 - rr s₀ c) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.s5, sub_ofNat (by omega_arith)]
  have h9₃ : s₃.gpr .t1 = BitVec.ofNat 64 ((len s₀ - c) / 128) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.s4, ofNat_shr7 (by omega_arith)]
  -- `t2 := min(t2, len)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Inv s₀ c s₄ ∧ s₄.gpr .t2 = BitVec.ofNat 64 (tt s₀ c) ∧
    s₄.gpr .t0 = 0 ∧ s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, h11₄, h10₄, hm₄⟩ => ?_)
  · have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have h10₃ : s₃.gpr .t0 = 0 := by rw [e₃ _ (by decide) (by decide), h10]
    refine WP.ite (decide ((len s₀ - c) / 128 = 0))
      (by show VG.RISCV64.eval (.zero .t1) s₃ = _; rw [eval_zero, h9₃, ofNat_beq_zero (by omega_arith)])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.seq (wp_add fun s₅ u₅ => wp_srl (by decide) fun s₆ u₆ => WP.block_nil ?_)
      have e₆ : ∀ r, r ≠ .t1 → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.other r h]
      have hI₆ : Inv s₀ c s₆ := hI₃.of_gpr (fun r hr => e₆ r (ne r hr).1) (by rw [u₆.mem, u₅.mem])
        (by rw [u₆.rd, u₅.rd]) (by rw [u₆.wr, u₅.wr]) (by rw [u₆.sp, u₅.sp])
      have h9₆ : s₆.gpr .t1 = BitVec.ofNat 64 ((len s₀ - c + rr s₀ c) / 128) := by
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
  have hC₀ : Copy s₀ c s.mem 0 s₅ := by
    have e : ∀ r, r ≠ .s4 → s₅.gpr r = s₄.gpr r := fun r h => u₅.other r h
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
  have hC₇ : Copy s₀ c s.mem (tt s₀ c) s₇ :=
    ⟨hC.j_le, by rw [u₇.rd, hC.rd], by rw [u₇.wr, hC.wr], by rw [u₇.other _ (by decide), hC.s1],
      by rw [u₇.other _ (by decide), hC.s2], by rw [u₇.sp, hC.sp], by rw [u₇.other _ (by decide), hC.s3],
      by rw [u₇.other _ (by decide), hC.s4], by rw [u₇.other _ (by decide), hC.s5],
      by rw [u₇.other _ (by decide), hC.t2], by rw [u₇.other _ (by decide), hC.t0],
      by rw [u₇.mem, hC.mem]⟩
  have hz : eval (.zero .t1) s₇ = some (decide (rr s₀ c + tt s₀ c = 128)) := by
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
  have hlen := len_lt s₀; have hc := hI.c_le; have hr := rr_lt s₀ c
  have ne : ∀ r ∈ [Reg.s1, .s2, .s3, .s4, .s5], r ≠ .t0 ∧ r ≠ .t1 := by decide
  rw [body_eq]
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hI₁ : Inv s₀ c s₁ := hI.of_gpr (fun r hr => u₁.other r (ne r hr).1) u₁.mem u₁.rd u₁.wr u₁.sp
  have h10₁ : s₁.gpr .t0 = 0 := by rw [u₁.gpr]; rfl
  have nv₁ : ∀ r ∈ nvRegs, s₁.gpr r = s.gpr r := fun r hr => u₁.other r (by revert r hr; decide)
  refine WP.seq (WP.mono (Q := fun (s' : State) => ((∃ c', c < c' ∧ Pending s₀ c' s') ∨ Done s₀ s') ∧
      ∀ r ∈ nvRegs, s'.gpr r = s₁.gpr r) ?_
    fun s' ⟨h, hnv⟩ => ?_)
  · refine WP.ite (decide (rr s₀ c = 0))
      (by show VG.RISCV64.eval (.zero .s5) s₁ = _; rw [eval_zero, hI₁.s5, ofNat_beq_zero (by omega_arith)])
      (fun hb => ?_) (fun _ => WP.gprs (fill_ok hp hI₁ hcl h10₁) fill_nv)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_srl (by decide) fun s₂ u₂ => WP.block_nil ?_)
    have hI₂ : Inv s₀ c s₂ := hI₁.of_gpr (fun r hr => u₂.other r (ne r hr).2) u₂.mem u₂.rd u₂.wr u₂.sp
    have h10₂ : s₂.gpr .t0 = 0 := by rw [u₂.other _ (by decide), h10₁]
    have nv₂ : ∀ r ∈ nvRegs, s₂.gpr r = s₁.gpr r := fun r hr => u₂.other r (by revert r hr; decide)
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
  have hm₆ : s₆.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
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
  have hlen := len_lt s₀
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
      have hnv'' : ∀ r ∈ nvRegs, s'.gpr r = s₀.gpr r := fun r hr => (hnv' r hr).trans (hnv r hr)
      have hc' := hI'.c_le
      have hz : isa.eval (.nonzero .s4) s' = some (decide (len s₀ - c' ≠ 0)) := by
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

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha512.updateRISCV64.post s₀ s' := by
  refine WP.alloc (by decide) (by simp only [frameBytes]; exact hp.sp208)
    (WP.mono (correctMain hp) fun s' ⟨hk, hra, hsp, hwr, hpost⟩ => ?_)
  rw [freed_eq (by rw [hwr]; rfl) (by rw [hsp]; rfl)]
  exact ⟨⟨hk, rfl, hra⟩, hpost⟩

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
  · exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => agree₀ hp) (by taint_decide)
  · refine ⟨sat, rfl, rfl, ?_, by decide, by decide, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha512.RISCV64.Stream.Update
