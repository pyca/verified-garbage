module

public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Streaming Merkle–Damgård hash functions on PPC64LE: `update`

The functional correctness of `update`, for any hash function (`Md`) and any
correct compression function (`CalleeOk`). The same structure as the x86-64
proof (`VG.Proof.MdStream.X86_64.Update`); the loop runs while data is left,
so every iteration consumes at least one byte. Constant time is proven for
each hash function's code by the taint analysis, calls included.
-/

@[expose] public section

namespace VG.Proof.MdStream.PPC64LE.Update

open VG VG.PPC64LE VG.Impl.MdStream.PPC64LE
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .r3
abbrev cnt : Nat := (s₀.gpr .r4).toNat
abbrev dp : Addr := s₀.gpr .r5
abbrev len : Nat := (s₀.gpr .r6).toNat
abbrev scr : Addr := s₀.gpr .r7
abbrev stR : Region := ⟨st s₀, P.N + P.B⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, P.so + 48⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (len s₀)
/-- The buffer. -/
abbrev buf : Addr := st s₀ + BitVec.ofNat 64 P.N

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (st s₀) m ∧ s₀.gpr .r4 = BitVec.ofNat 64 m.length

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR P s₀, scR P s₀]
  st_scr : (stR P s₀).Disjoint (scR P s₀)
  d_st : (dR s₀).Disjoint (stR P s₀)
  d_scr : (dR s₀).Disjoint (scR P s₀)

/-- The frame saving the link register, below the stack pointer. -/
abbrev stkR (s₀ : State) : Region := ⟨s₀.sp - 48, 48⟩

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (P : Params) (s₀ : State) : Prop where
  sp48 : 48 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR P s₀)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR P s₀)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem pre_of {s₀ : State} (h : (updK H).pre s₀) : Pre P s₀ ∧ Stack P s₀ := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := h
  exact ⟨⟨p1, p2, p3, p4, p5⟩, ⟨p6, p7, p8, p9⟩⟩

theorem R₀.length (hd : Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) :
    cnt s₀ % P.B = m.length % P.B := by
  rw [cnt, h.2, BitVec.toNat_ofNat, hd.mod]

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .r6).isLt

theorem D_length (s₀ : State) : (D s₀).length = len s₀ := by simp [bytesAt]

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = st s₀
  r27 : s.gpr .r27 = scr s₀
  sp : s.sp = s₀.sp
  r28 : s.gpr .r28 = dp s₀ + BitVec.ofNat 64 c
  r29 : s.gpr .r29 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR P s₀, scR P s₀] s₀.mem s.mem
  saved : Saved P (scr s₀) s₀.gpr s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop
    extends Common P s₀ c s where
  r30 : s.gpr .r30 = BitVec.ofNat 64 ((cnt s₀ + c) % P.B)
  repr : ∀ iv m, R₀ H s₀ iv m → H.Repr iv s.mem (st s₀) (m ++ (D s₀).take c)

/-- `k ≥ 1` whole blocks are ready at `r4` (the buffer, or the data), and
compressing them absorbs the first `c` bytes of data. -/
structure Pending {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c k : Nat) (s : State) : Prop
    extends Common P s₀ c s where
  r30 : s.gpr .r30 = 0
  r9 : s.gpr .r9 = BitVec.ofNat 64 k
  k_pos : 0 < k
  mod : (cnt s₀ + c) % P.B = 0
  src : (s.gpr .r4 = buf P s₀ ∧ k = 1) ∨
    ∃ c₀, s.gpr .r4 = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + P.B * k ≤ len s₀
  repr : ∀ iv m, R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (st s₀) =
      H.compressBlocks (H.stateAt s.mem (st s₀)) s.mem (s.gpr .r4) k →
    H.Repr iv mem' (st s₀) (m ++ (D s₀).take c)

/-- All the data is absorbed, and nothing is pending. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  Inv H s₀ (len s₀) s ∧ s.gpr .r9 = 0

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common P s₀ c s)
    (hg : ∀ r ∈ [Reg.r26, .r27, .r28, .r29], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common P s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  r26 := by rw [hg _ (by simp)]; exact h.r26
  r27 := by rw [hg _ (by simp)]; exact h.r27
  sp := hsp.trans h.sp
  r28 := by rw [hg _ (by simp)]; exact h.r28
  r29 := by rw [hg _ (by simp)]; exact h.r29
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Inv H s₀ c s)
    (hg : ∀ r ∈ [Reg.r26, .r27, .r28, .r29, .r30], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv H s₀ c s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_append_left [_] hr)) hm hrd hwr hsp with
    r30 := by rw [hg _ (by simp)]; exact h.r30
    repr := by rw [hm]; exact h.repr }

/-- Where the caller's registers are saved. -/
theorem saved_sub (hd : Dims P) {s₀ : State} {p : Reg × Nat} (hp : p ∈ saved P) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR P s₀) := by
  have := saved_offset hd hp; have hd_so := hd.so
  exact sub_offset (by omega_using [this]) (by omega_arith)

/-- The saved registers survive a write to the state. -/
theorem Saved.of_frame (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {m m' : Mem}
    (hs : Saved P (scr s₀) s₀.gpr m) (hf : Frame [stR P s₀] m m') : Saved P (scr s₀) s₀.gpr m' := by
  intro p hp'
  rw [← hs p hp']
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact hp.st_scr.symm.sub_left (saved_sub hd hp')

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < len s₀) :
    (D s₀).getD i 0 = s₀.mem (dp s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (h : Common P s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = (D s₀).getD i 0 := by
  rw [D_getD s₀ hi]
  exact frame_bytes h.frame (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

theorem length_mid (hd : Dims P) (s₀ : State) {iv : H.HV} {m : List Byte} (hm : R₀ H s₀ iv m) {c : Nat}
    (hc : c ≤ len s₀) : (m ++ (D s₀).take c).length % P.B = (cnt s₀ + c) % P.B := by
  have := hm.length hd
  simp only [List.length_append, List.length_take, D_length, Nat.min_eq_left hc]
  rw [Nat.add_mod, ← this, ← Nat.add_mod]

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (D s₀).take c ++ ((D s₀).drop c).take t = m ++ (D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-! ## Compressing pending blocks -/

theorem Pending.k_lt (hd : Dims P) {s₀ : State} {c k : Nat} {s : State} (h : Pending H s₀ c k s) :
    k < 2 ^ 64 := by
  have := len_lt s₀; have := Nat.le_mul_of_pos_left k hd.pos
  rcases h.src with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega_arith

theorem Pending.compress_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) {c k : Nat} {s : State} (h : Pending H s₀ c k s) :
    WP isa (compressN name code) s fun s' => Inv H s₀ c s' ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  have hd_N := hd.N; have hd_so := hd.so; have hd_B := hd.B; have := len_lt s₀
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega_arith)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega_arith)
  have eSrc : Region.Sub ⟨s.gpr .r4, P.B * k⟩ (stR P s₀) ∨ Region.Sub ⟨s.gpr .r4, P.B * k⟩ (dR s₀) := by
    rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ sub_offset (off := P.N) (by omega_arith) (by omega_arith))
    · exact .inr (h' ▸ sub_offset (by omega_arith) (by omega_arith))
  have hk : (s.gpr .r9).toNat = k := by rw [h.r9, toNat_ofNat_lt (h.k_lt hd)]
  refine compressWith_ok (setsN_r9 s) hk hf h.r26 h.r27 rfl ((hp.st_scr.sub_left eN).sub_right eso)
    ?_ ?_ ?_ ?_ ?_
  · rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)
    · exact (hp.d_st.sub_left (h' ▸ sub_offset (by omega_arith) (by omega_using [hc₀, this]))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨stR P s₀, by simp, P.N, h', by simp⟩
      · exact ⟨dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · intro s' hrd hwr hcs hsp hf' hstate
    have cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r := hcs
    refine ⟨⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide)]; exact h.r26,
      by rw [cs _ (by decide)]; exact h.r27, hsp.trans h.sp,
      by rw [cs _ (by decide)]; exact h.r28,
      by rw [cs _ (by decide)]; exact h.r29,
      h.frame.trans (hf'.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩, cs⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR P s₀, by simp, eN⟩
      · exact ⟨scR P s₀, by simp, eso⟩
    · rw [← h.saved p hp']
      have := saved_offset hd hp'
      refine hf'.readW (r := ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact (hp.st_scr.symm.sub_left (saved_sub hd hp')).sub_right eN
      · exact Offset.disjoint_base _ (by omega_using [this]) (by omega_arith)
    · rw [cs _ (by decide), h.r30, h.mod]; rfl

/-! ## Whole blocks straight from the data -/

theorem direct_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s)
    (hr : (cnt s₀ + c) % P.B = 0) (hl : P.B ≤ len s₀ - c) :
    WP isa (.block (direct P)) s
      (Pending H s₀ (c + P.B * ((len s₀ - c) / P.B)) ((len s₀ - c) / P.B)) := by
  have hlen := len_lt s₀; have hB := hd.pos; have hc := hI.c_le
  have hdm := Nat.div_add_mod (len s₀ - c) P.B
  have hq1 : 0 < (len s₀ - c) / P.B := Nat.div_pos hl hd.pos
  have hsh := hd.shr (a := len s₀ - c) (by omega_arith)
  have hsl := hd.shl (a := (len s₀ - c) / P.B) (by omega_arith)
  generalize (len s₀ - c) / P.B = q at *
  have hq2 : P.B * q ≤ len s₀ - c := by omega_arith
  unfold direct
  have h63 : lg P < 64 := by have hd_log := hd.log; omega_arith
  refine wp_mov fun s₁ u₁ => wp_lsr h63 fun s₂ u₂ => wp_lsl h63 fun s₃ u₃ =>
    wp_add fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r4 → r ≠ .r9 → r ≠ .r8 → r ≠ .r28 → r ≠ .r29 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have h1 : s₅.gpr .r4 = dp s₀ + BitVec.ofNat 64 c := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, hI.r28]
  have h9 : s₅.gpr .r9 = BitVec.ofNat 64 q := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), hI.r29, hsh]
  have h8 : s₃.gpr .r8 = BitVec.ofNat 64 (P.B * q) := by
    rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hI.r29, hsh, hsl]
  have h8' : s₄.gpr .r8 = BitVec.ofNat 64 (P.B * q) := by rw [u₄.other _ (by decide), h8]
  refine ⟨⟨by omega_arith, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.r26],
    by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.r27],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, by rw [m₅]; exact hI.frame,
    by rw [m₅]; exact hI.saved⟩, ?_, h9, hq1, ?_, .inr ⟨c, h1, by omega_arith⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.gpr, h8, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r28, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₅.gpr, h8', u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.r29, sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.r30, hr]; rfl
  · rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]; exact hr
  · intro iv m hm mem' hs
    have hmod := length_mid hd s₀ hm (c := c) (by omega_arith)
    rw [← take_add_data]
    refine H.repr_append_blocks (n := q) hd.pos (hI.repr iv m hm) (by rw [hmod, hr])
      (by rw [List.length_take, List.length_drop, D_length]; omega_arith) ?_
    rw [hs, m₅, h1]
    apply H.compressBlocks_eq
    intro j hj
    rw [add_ofNat, hI.data hp (by omega_using [hj, hdm])]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

/-! ## Buffering data -/

section
variable (P) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (cnt s₀ + c) % P.B
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (P.B - rr P s₀ c) (len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := buf P s₀ + BitVec.ofNat 64 (rr P s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((D s₀).drop c).take (tt P s₀ c)
end

theorem rr_lt (hd : Dims P) (s₀ : State) (c : Nat) : rr P s₀ c < P.B := Nat.mod_lt _ hd.pos
theorem tt_le (s₀ : State) (c : Nat) : tt P s₀ c ≤ len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : tt P s₀ c ≤ P.B - rr P s₀ c := Nat.min_le_left _ _
theorem rr_eq (s₀ : State) (c : Nat) : rr P s₀ c = (cnt s₀ + c) % P.B := rfl
theorem tt_eq (s₀ : State) (c : Nat) : tt P s₀ c = min (P.B - rr P s₀ c) (len s₀ - c) := rfl

theorem q_eq (s₀ : State) (c : Nat) : q P s₀ c = st s₀ + BitVec.ofNat 64 (P.N + rr P s₀ c) :=
  add_ofNat _ _ _

theorem xs_length (s₀ : State) (c : Nat) : (xs P s₀ c).length = tt P s₀ c := by
  have := tt_le (P := P) s₀ c
  simp only [xs, List.length_take, List.length_drop, D_length]; omega_arith

end

/-- The state while copying: `j` bytes copied, into memory otherwise as in `mI`. -/
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ tt P s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r26 : s.gpr .r26 = st s₀
  r27 : s.gpr .r27 = scr s₀
  sp : s.sp = s₀.sp
  r28 : s.gpr .r28 = dp s₀ + BitVec.ofNat 64 (c + j)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (len s₀ - c - tt P s₀ c)
  r30 : s.gpr .r30 = BitVec.ofNat 64 (rr P s₀ c + j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (tt P s₀ c - j)
  r9 : s.gpr .r9 = 0
  mem : s.mem = writeBytes mI (q P s₀ c) ((xs P s₀ c).take j)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem write_frame (hd : Dims P) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ tt P s₀ c) :
    Frame [stR P s₀] mI (writeBytes mI (q P s₀ c) ((xs P s₀ c).take j)) := by
  have := tt_le' (P := P) s₀ c; have := rr_lt hd s₀ c; have hd_N := hd.N; have hd_B := hd.B
  refine writeBytes_frame _ _ _ ?_
  rw [q_eq]
  exact contains_offset (by simp only [List.length_take]; omega_arith) (by omega_arith)

theorem copy_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {j : Nat} (hj : j < tt P s₀ c) {s : State} (h : Copy P s₀ c sI.mem j s) :
    WP isa (.block (copyBody P)) s fun s' =>
      Copy P s₀ c sI.mem (j + 1) s' ∧ s'.gpr .r10 = BitVec.ofNat 64 (tt P s₀ c - (j + 1)) := by
  have hlen := len_lt s₀
  have hc := hI.c_le
  have hr := rr_lt hd s₀ c
  have ht := tt_le (P := P) s₀ c; have ht' := tt_le' (P := P) s₀ c
  have hd_N := hd.N; have hd_B := hd.B
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega_using [ht, hj]) (by omega_using [ht, hlen, hj])⟩
  have hbyte : s.mem (dp s₀ + BitVec.ofNat 64 (c + j)) = (D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega_using [ht, hj])]
    exact frame_bytes (write_frame hd s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega_arith) (by show c + j < len s₀; omega_arith)
  -- The byte written.
  have hout : InRegions s.wr (q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨stR P s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, add_ofNat]; exact contains_offset (by omega_using [ht', hj]) (by omega_arith)⟩
  have hxs := xs_length (P := P) s₀ c
  unfold copyBody
  refine wp_lbz (a := dp s₀ + BitVec.ofNat 64 (c + j)) (by omega_arith) (by rw [h.r28]; simp) hin
    fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => wp_stb (a := q P s₀ c + BitVec.ofNat 64 j) (by omega_arith) ?_
    (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), h.r26, h.r30, q, buf]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_subi (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r8 → r ≠ .r11 → r ≠ .r28 → r ≠ .r30 → r ≠ .r10 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃.gpr, u₂.other r h2, u₁.other r h1]
  have hx10 : s₆.gpr .r10 = BitVec.ofNat 64 (tt P s₀ c - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r10, sub_ofNat (by omega_using [hj]), Nat.sub_sub]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx10, ?_, ?_⟩, hx10⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide), h.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide), h.r27]
  · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r28, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r29 (by decide) (by decide) (by decide) (by decide) (by decide), h.r29]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r30, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r9 (by decide) (by decide) (by decide) (by decide) (by decide), h.r9]
  · have hj' : j < (xs P s₀ c).length := by omega_arith
    rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
      List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega_using [ht, hlen])]
    have hl : (List.take j (xs P s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl]
    have e : ((List.getD (D s₀) (c + j) 0).setWidth 64).setWidth 8 = List.getD (D s₀) (c + j) 0 := by
      ext i hi; simp
    rw [e]
    congr 1
    simp only [xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (D s₀).length by rw [D_length]; omega_using [ht, hj]), Option.getD_some]

theorem copy_loop_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {j₀ : Nat} {s : State} (h : Copy P s₀ c sI.mem j₀ s) (ht : j₀ < tt P s₀ c) :
    WP isa (.loop (.block (copyBody P)) (.nonzero .d .r10)) s (Copy P s₀ c sI.mem (tt P s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = tt P s₀ c - j ∧ j < tt P s₀ c ∧ Copy P s₀ c sI.mem j s)
    ?_ (tt P s₀ c - j₀) s ⟨j₀, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (copy_step hd hp hI hj hc) fun s' ⟨hc', h10⟩ => ?_
  have hz : isa.eval (.nonzero .d .r10) s' = some (decide (tt P s₀ c - (j + 1) ≠ 0)) := by
    show VG.PPC64LE.eval (.nonzero .d .r10) s' = _
    rw [eval_nonzero, h10, bne, ofNat_beq_zero (by have := tt_le' (P := P) s₀ c; have hd_B := hd.B; omega_arith)]
    simp
  by_cases hl : tt P s₀ c - (j + 1) = 0
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [show j + 1 = tt P s₀ c by omega_arith] at hc'
  · exact .inr ⟨by rw [hz]; simp [hl], _, by omega_arith, j + 1, rfl, by omega_arith, hc'⟩

theorem Copy.of_gpr {s₀ : State} {c : Nat} {mI : Mem} {j : Nat} {s s' : State} (h : Copy P s₀ c mI j s)
    (hg : ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : Copy P s₀ c mI j s' :=
  ⟨h.j_le, hrd.trans h.rd, hwr.trans h.wr, by rw [hg _ (by decide), h.r26],
    by rw [hg _ (by decide), h.r27], hsp.trans h.sp, by rw [hg _ (by decide), h.r28],
    by rw [hg _ (by decide), h.r29], by rw [hg _ (by decide), h.r30],
    by rw [hg _ (by decide), h.r10], by rw [hg _ (by decide), h.r9], by rw [hm, h.mem]⟩

theorem xs_chunk (s₀ : State) (c : Nat) {j : Nat} (hj : j + 8 ≤ tt P s₀ c) :
    ((xs P s₀ c).drop j).take 8 = (List.range 8).map fun k => (D s₀).getD (c + j + k) 0 := by
  have ht := tt_le (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_map, List.length_range, hxs]; omega_arith
  · intro k h1 h2
    have hk : k < 8 := by simpa using h2
    simp only [xs, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, Nat.add_assoc]
    rw [List.getElem?_eq_getElem (by rw [D_length]; omega_arith), Option.getD_some]

theorem copy_word_step (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State}
    (hI : Inv H s₀ c sI) {j : Nat} (hj : j + 8 ≤ tt P s₀ c) {s : State} (h : Copy P s₀ c sI.mem j s) :
    WP isa (.block (copyWordBody P)) s fun s' =>
      Copy P s₀ c sI.mem (j + 8) s' ∧ s'.gpr .r12 = BitVec.ofNat 64 ((tt P s₀ c - (j + 8)) / 8) := by
  have hlen := len_lt s₀
  have hc := hI.c_le
  have hr := rr_lt hd s₀ c
  have ht := tt_le (P := P) s₀ c; have ht' := tt_le' (P := P) s₀ c
  have hd_N := hd.N; have hd_B := hd.B
  -- The bytes read.
  have hin : InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 (c + j)) 8 :=
    ⟨dR s₀, by simp [h.rd, hp.rd], contains_offset (by omega_using [ht, hj]) (by omega_using [ht, hlen, hj])⟩
  have hbyte : ∀ k, k < 8 →
      s.mem (dp s₀ + BitVec.ofNat 64 (c + j) + BitVec.ofNat 64 k) = (D s₀).getD (c + j + k) 0 := by
    intro k hk
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.mem, ← hI.data hp (by omega_using [hk, ht, hj])]
    exact frame_bytes (write_frame hd s₀ c sI.mem j h.j_le) (R := dR s₀) (by simpa using hp.d_st)
      (by show len s₀ ≤ 2 ^ 64; omega_arith) (by show c + j + k < len s₀; omega_arith)
  -- The bytes written.
  have hout : InRegions s.wr (q P s₀ c + BitVec.ofNat 64 j) 8 :=
    ⟨stR P s₀, by simp [h.wr, hp.wr], by
      rw [q_eq, BitVec.add_assoc, ← BitVec.ofNat_add]; exact contains_offset (by omega_using [ht', hj]) (by omega_arith)⟩
  have hxs := xs_length (P := P) s₀ c
  unfold copyWordBody
  rw [List.cons_append, List.nil_append]
  refine wp_ld (a := dp s₀ + BitVec.ofNat 64 (c + j)) (by decide) (by rw [h.r28]; simp) hin
    fun s₁ u₁ => ?_
  refine storeWord_ok (by omega_arith) (a := q P s₀ c + BitVec.ofNat 64 j) ?_ (by rw [u₁.wr]; exact hout)
    fun s₃ g₃ rd₃ wr₃ sp₃ m₃ => ?_
  · rw [u₁.other _ (by decide), u₁.other _ (by decide), h.r26, h.r30, q, buf]
    simp only [BitVec.ofNat_add]
    ac_rfl
  refine wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_subi (by decide) fun s₆ u₆ => wp_lsr (by decide) fun s₇ u₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r8 → r ≠ .r11 → r ≠ .r28 → r ≠ .r30 → r ≠ .r10 → r ≠ .r12 →
      s₇.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 h6 => by
    rw [u₇.other r h6, u₆.other r h5, u₅.other r h4, u₄.other r h3, g₃ r h2, u₁.other r h1]
  have hx11₆ : s₆.gpr .r10 = BitVec.ofNat 64 (tt P s₀ c - (j + 8)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
      u₁.other _ (by decide), h.r10, sub_ofNat (by omega_using [hj]), Nat.sub_sub]
  have hx10 : s₇.gpr .r10 = BitVec.ofNat 64 (tt P s₀ c - (j + 8)) := by
    rw [u₇.other _ (by decide), hx11₆]
  have hx12 : s₇.gpr .r12 = BitVec.ofNat 64 ((tt P s₀ c - (j + 8)) / 8) := by
    rw [u₇.gpr, hx11₆, ofNat_shr (by omega_using [ht, hlen])]
  refine ⟨⟨by omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx10, ?_, ?_⟩, hx12⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₁.rd, h.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₁.wr, h.wr]
  · rw [g .r26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r26]
  · rw [g .r27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r27]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₁.sp, h.sp]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃ _ (by decide),
      u₁.other _ (by decide), h.r28, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r29]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃ _ (by decide),
      u₁.other _ (by decide), h.r30, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [g .r9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h.r9]
  · have hl : (List.take j (xs P s₀ c)).length = j := by
      rw [List.length_take, Nat.min_eq_left (by omega_arith)]
    have hw : (List.range 8).map (fun k => (s.mem.readW (dp s₀ + BitVec.ofNat 64 (c + j)) 64).extractLsb' (8 * k) 8) =
        ((xs P s₀ c).drop j).take 8 := by
      rw [xs_chunk s₀ c hj]
      refine List.map_congr_left fun k hk => ?_
      have hk' : k < 8 := List.mem_range.mp hk
      rw [extractLsb'_readW _ _ hk', hbyte k hk']
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₁.mem, u₁.gpr, writeW_eq_writeBytes, hw, h.mem,
      show q P s₀ c + BitVec.ofNat 64 j = q P s₀ c + BitVec.ofNat 64 (List.take j (xs P s₀ c)).length by
        rw [hl],
      VG.WriteBytes.writeBytes_append _ _ _ _ (by simp only [List.length_take, List.length_drop]; omega_arith),
      ← List.take_add]

theorem copy_words_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State}
    (hI : Inv H s₀ c sI) {s : State} (h : Copy P s₀ c sI.mem 0 s)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 (tt P s₀ c / 8)) :
    WP isa (.ite (.zero .d .r12) (.block []) (.loop (.block (copyWordBody P)) (.nonzero .d .r12))) s
      (Copy P s₀ c sI.mem (8 * (tt P s₀ c / 8))) := by
  have ht' := tt_le' (P := P) s₀ c; have hd_B := hd.B
  have hz : eval (.zero .d .r12) s = some (decide (tt P s₀ c / 8 = 0)) := by
    rw [eval_zero, h12, ofNat_beq_zero (by omega_arith)]
  refine WP.ite (decide (tt P s₀ c / 8 = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rw [hb]; exact h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa)
      (fun n s => ∃ i, n = tt P s₀ c / 8 - i ∧ i < tt P s₀ c / 8 ∧ Copy P s₀ c sI.mem (8 * i) s)
      ?_ (tt P s₀ c / 8) s ⟨0, rfl, by omega_arith, h⟩
    rintro n s ⟨i, rfl, hi, hC⟩
    refine WP.mono (copy_word_step hd hp hI (by omega_arith) hC) fun s' ⟨hC', h12'⟩ => ?_
    have hz' : isa.eval (.nonzero .d .r12) s' = some (decide (tt P s₀ c / 8 - (i + 1) ≠ 0)) := by
      show VG.PPC64LE.eval (.nonzero .d .r12) s' = _
      rw [eval_nonzero, h12', show (tt P s₀ c - (8 * i + 8)) / 8 = tt P s₀ c / 8 - (i + 1) by omega_arith,
        bne, ofNat_beq_zero (by omega_arith)]
      simp
    rw [show 8 * i + 8 = 8 * (i + 1) by omega_arith] at hC'
    by_cases hl : tt P s₀ c / 8 - (i + 1) = 0
    · refine .inl ⟨by rw [hz']; simp [hl], ?_⟩
      rwa [show i + 1 = tt P s₀ c / 8 by omega_arith] at hC'
    · exact .inr ⟨by rw [hz']; simp [hl], _, by omega_arith, i + 1, rfl, by omega_arith, hC'⟩

theorem copy_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem 0 s) : WP isa (copy P) s (Copy P s₀ c sI.mem (tt P s₀ c)) := by
  have ht' := tt_le' (P := P) s₀ c; have hd_B := hd.B
  unfold copy
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hC₁ : Copy P s₀ c sI.mem 0 s₁ := h.of_gpr u₁.other u₁.mem u₁.rd u₁.wr u₁.sp
  have h12 : s₁.gpr .r12 = BitVec.ofNat 64 (tt P s₀ c / 8) := by
    rw [u₁.gpr, h.r10, Nat.sub_zero, ofNat_shr (by omega_arith)]
  refine WP.seq (WP.mono (copy_words_ok hd hp hI hC₁ h12) fun s₂ hC₂ => ?_)
  have hz : eval (.zero .d .r10) s₂ = some (decide (tt P s₀ c - 8 * (tt P s₀ c / 8) = 0)) := by
    rw [eval_zero, hC₂.r10, ofNat_beq_zero (by omega_arith)]
  refine WP.ite (decide (tt P s₀ c - 8 * (tt P s₀ c / 8) = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rwa [show 8 * (tt P s₀ c / 8) = tt P s₀ c by omega_arith] at hC₂)
  · simp only [decide_eq_false_iff_not] at hb
    exact copy_loop_ok hd hp hI hC₂ (by omega_arith)

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI) :
    let mem := writeBytes sI.mem (q P s₀ c) (xs P s₀ c)
    Frame [stR P s₀, scR P s₀] s₀.mem mem ∧ Saved P (scr s₀) s₀.gpr mem ∧
      H.stateAt mem (st s₀) = H.stateAt sI.mem (st s₀) ∧
      bytesAt mem (buf P s₀) (rr P s₀ c + tt P s₀ c) = bytesAt sI.mem (buf P s₀) (rr P s₀ c) ++ xs P s₀ c := by
  intro mem
  have hr := rr_lt hd s₀ c; have ht' := tt_le' (P := P) s₀ c; have hd_N := hd.N; have hd_B := hd.B
  have hxs := xs_length (P := P) s₀ c
  have hf : Frame [stR P s₀] sI.mem mem := by
    have := write_frame hd s₀ c sI.mem (tt P s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega_arith)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), Saved.of_frame hd hp hI.saved hf, ?_, ?_⟩
  · apply H.stateAt_congr
    intro i hi
    simp only [mem, q_eq]
    exact writeBytes_before _ _ _ (by omega_arith) (by omega_arith)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega_using [hxs, hd_B, ht', hr])

/-- A full buffer: compress it. -/
theorem fill_pending (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem (tt P s₀ c) s) (hfull : rr P s₀ c + tt P s₀ c = P.B) :
    WP isa (.block [.addi .r4 .r26 P.N, .li .r30 0, .li .r9 1]) s
      (Pending H s₀ (c + tt P s₀ c) 1) := by
  have ht' := tt_le' (P := P) s₀ c
  have hrr := rr_eq (P := P) s₀ c; have htt := tt_eq (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  have hc := hI.c_le
  have hd_N := hd.N; have hd_B := hd.B
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  have hmem : s.mem = writeBytes sI.mem (q P s₀ c) (xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine wp_addi (by omega_arith) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ =>
    WP.block_nil ?_
  have g : ∀ r, r ≠ .r4 → r ≠ .r30 → r ≠ .r9 → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hx1 : s₃.gpr .r4 = buf P s₀ := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.r26]
  refine ⟨⟨by omega_using [hc, htt], ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₃, hmem]; exact hfr, by rw [m₃, hmem]; exact hsv⟩,
    by rw [u₃.other _ (by decide), u₂.gpr]; rfl, by rw [u₃.gpr], Nat.one_pos,
    by rw [← Nat.add_assoc]; exact Md.add_mod_of_eq hfull, .inl ⟨hx1, rfl⟩,
    ?_⟩
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .r26 (by decide) (by decide) (by decide), h.r26]
  · rw [g .r27 (by decide) (by decide) (by decide), h.r27]
  · rw [u₃.sp, u₂.sp, u₁.sp, h.sp]
  · rw [g .r28 (by decide) (by decide) (by decide), h.r28]
  · rw [g .r29 (by decide) (by decide) (by decide), h.r29, Nat.sub_sub]
  · intro iv m hm mem' hs
    rw [Md.compressBlocks_one] at hs
    rw [← take_add_data]
    have hmod := length_mid hd s₀ hm hc
    refine H.repr_append_block hd.pos (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₃, hmem, hst, hx1]
    refine congrArg (H.compress _) (H.parse_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show rr P s₀ c + tt P s₀ c = P.B from hfull] at hby
    exact bytesAt_getD hby hk

/-- All the data fits in the buffer. -/
theorem fill_done (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {sI : State} (hI : Inv H s₀ c sI)
    {s : State} (h : Copy P s₀ c sI.mem (tt P s₀ c) s) (hnf : rr P s₀ c + tt P s₀ c ≠ P.B) : Done H s₀ s := by
  have hr := rr_lt hd s₀ c; have ht' := tt_le' (P := P) s₀ c
  have hrr := rr_eq (P := P) s₀ c; have htt := tt_eq (P := P) s₀ c
  have hxs := xs_length (P := P) s₀ c
  have hc := hI.c_le
  have htl : tt P s₀ c = len s₀ - c := by omega_arith
  obtain ⟨hfr, hsv, hst, hby⟩ := copied_facts hd hp hI
  have hmem : s.mem = writeBytes sI.mem (q P s₀ c) (xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.r26, h.r27, h.sp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h.r9⟩
  · rw [h.r28]; congr 2; omega_using [htl, hc]
  · rw [h.r29]; congr 1; omega_using [htl]
  · rw [h.r30, show cnt s₀ + len s₀ = cnt s₀ + c + tt P s₀ c by omega_using [htl, hc],
      Md.add_mod_of_lt (by omega_using [hr, ht', hnf, hrr])]
  · have hmod := length_mid hd s₀ hm hc
    rw [show len s₀ = c + tt P s₀ c by omega_using [htl, hc], ← take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega_using [hrr, ht', hr, hnf]) (by rw [hmem, hst]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem fill_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s)
    (hcl : c < len s₀) (h9 : s.gpr .r9 = 0) :
    WP isa (fill P) s fun s' => (∃ c' k, c < c' ∧ Pending H s₀ c' k s') ∨ Done H s₀ s' := by
  have ht' := tt_le' (P := P) s₀ c; have hr := rr_lt hd s₀ c
  have hrr := rr_eq (P := P) s₀ c; have htt := tt_eq (P := P) s₀ c
  have ne : ∀ r ∈ [Reg.r26, .r27, .r28, .r29, .r30], r ≠ .r8 ∧ r ≠ .r10 := by decide
  have hlen := len_lt s₀
  have hB := hd.B
  have h63 : lg P < 64 := by have hd_log := hd.log; omega_arith
  unfold fill
  -- `r10 := B - r; r8 := len >> log₂ B`
  refine WP.seq (wp_li hd.B_lt fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr h63 fun s₃ u₃ => WP.block_nil ?_)
  have e₃ : ∀ r, r ≠ .r8 → r ≠ .r10 → s₃.gpr r = s.gpr r := fun r h h' => by
    rw [u₃.other r h, u₂.other r h', u₁.other r h']
  have hI₃ : Inv H s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (ne r hr).1 (ne r hr).2)
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  have h11₃ : s₃.gpr .r10 = BitVec.ofNat 64 (P.B - rr P s₀ c) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r30, sub_ofNat (by omega_arith)]
  have h9₃ : s₃.gpr .r8 = BitVec.ofNat 64 ((len s₀ - c) / P.B) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r29, hd.shr (by omega_arith)]
  -- `r10 := min(r10, len)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => Inv H s₀ c s₄ ∧ s₄.gpr .r10 = BitVec.ofNat 64 (tt P s₀ c) ∧
    s₄.gpr .r9 = 0 ∧ s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, h11₄, h10₄, hm₄⟩ => ?_)
  · have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
    have h10₃ : s₃.gpr .r9 = 0 := by rw [e₃ _ (by decide) (by decide), h9]
    refine WP.ite (decide ((len s₀ - c) / P.B = 0))
      (by show VG.PPC64LE.eval (.zero .d .r8) s₃ = _
          rw [eval_zero, h9₃, ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith))])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq, Nat.div_eq_zero_iff_lt hd.pos] at hb
      refine WP.seq (wp_add fun s₅ u₅ => wp_lsr h63 fun s₆ u₆ => WP.block_nil ?_)
      have e₆ : ∀ r, r ≠ .r8 → s₆.gpr r = s₃.gpr r := fun r h => by rw [u₆.other r h, u₅.other r h]
      have hI₆ : Inv H s₀ c s₆ := hI₃.of_gpr (fun r hr => e₆ r (ne r hr).1) (by rw [u₆.mem, u₅.mem])
        (by rw [u₆.rd, u₅.rd]) (by rw [u₆.wr, u₅.wr]) (by rw [u₆.sp, u₅.sp])
      have h9₆ : s₆.gpr .r8 = BitVec.ofNat 64 ((len s₀ - c + rr P s₀ c) / P.B) := by
        rw [u₆.gpr, u₅.gpr, hI₃.r29, hI₃.r30, ← BitVec.ofNat_add, hd.shr (by omega_using [hb, hB, hrr, hr])]
      refine WP.ite (decide ((len s₀ - c + rr P s₀ c) / P.B = 0))
        (by show VG.PPC64LE.eval (.zero .d .r8) s₆ = _
            rw [eval_zero, h9₆, ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_using [hb, hB, hr]))])
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq, Nat.div_eq_zero_iff_lt hd.pos] at hb'
        refine wp_mov fun s₇ u₇ => WP.block_nil ⟨hI₆.of_gpr (fun r hr => u₇.other r (ne r hr).2)
          u₇.mem u₇.rd u₇.wr u₇.sp,
          ?_, by rw [u₇.other _ (by decide), e₆ _ (by decide), h10₃], by rw [u₇.mem, u₆.mem, u₅.mem, hm₃]⟩
        rw [u₇.gpr, hI₆.r29]; congr 1; omega_using [hb', htt]
      · simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb'
        refine WP.block_nil ⟨hI₆, ?_, by rw [e₆ _ (by decide), h10₃], by rw [u₆.mem, u₅.mem, hm₃]⟩
        rw [e₆ _ (by decide), h11₃]; congr 1; omega_arith
    · simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb
      refine WP.block_nil ⟨hI₃, ?_, h10₃, hm₃⟩
      rw [h11₃]; congr 1; omega_using [hb, htt]
  -- `r29 -= r10`
  refine WP.seq (wp_sub fun s₅ u₅ => WP.block_nil ?_)
  have hC₀ : Copy P s₀ c s.mem 0 s₅ := by
    have e : ∀ r, r ≠ .r29 → s₅.gpr r = s₄.gpr r := fun r h => u₅.other r h
    refine ⟨Nat.zero_le _, by rw [u₅.rd, hI₄.rd], by rw [u₅.wr, hI₄.wr],
      by rw [e _ (by decide), hI₄.r26], by rw [e _ (by decide), hI₄.r27], by rw [u₅.sp, hI₄.sp],
      by rw [e _ (by decide), hI₄.r28, Nat.add_zero], ?_, by rw [e _ (by decide), hI₄.r30, Nat.add_zero],
      by rw [e _ (by decide), h11₄, Nat.sub_zero], by rw [e _ (by decide), h10₄], ?_⟩
    · rw [u₅.gpr, hI₄.r29, h11₄, sub_ofNat (by omega_arith), Nat.sub_sub]
    · rw [u₅.mem, hm₄, List.take_zero, writeBytes_nil]
  -- Copy the data.
  refine WP.seq (WP.mono (copy_ok hd hp hI hC₀) fun s₆ hC => ?_)
  -- Is the buffer full?
  refine WP.seq (wp_subi (by omega_arith) fun s₇ u₇ => WP.block_nil ?_)
  have hC₇ : Copy P s₀ c s.mem (tt P s₀ c) s₇ :=
    ⟨hC.j_le, by rw [u₇.rd, hC.rd], by rw [u₇.wr, hC.wr], by rw [u₇.other _ (by decide), hC.r26],
      by rw [u₇.other _ (by decide), hC.r27], by rw [u₇.sp, hC.sp], by rw [u₇.other _ (by decide), hC.r28],
      by rw [u₇.other _ (by decide), hC.r29], by rw [u₇.other _ (by decide), hC.r30],
      by rw [u₇.other _ (by decide), hC.r10], by rw [u₇.other _ (by decide), hC.r9],
      by rw [u₇.mem, hC.mem]⟩
  have hz : eval (.zero .d .r8) s₇ = some (decide (rr P s₀ c + tt P s₀ c = P.B)) := by
    rw [eval_zero, u₇.gpr, hC.r30, sub_beq (by omega_using [hB, hr, ht']) (by omega_arith)]
  refine WP.ite (decide (rr P s₀ c + tt P s₀ c = P.B)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (fill_pending hd hp hI hC₇ hb) fun s' h => .inl ⟨c + tt P s₀ c, 1, by omega_arith, h⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (fill_done hd hp hI hC₇ hb))

theorem nv_of_all {c : Prog isa}
    (h : ((instrs c).all fun i => untouched.all fun r => dstOf i != some r) = true) :
    ∀ r ∈ untouched, ∀ i ∈ instrs c, dstOf i ≠ some r := fun r hr i hi =>
  bne_iff_ne.mp (List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr)

/-- The first part of an iteration, which calls nothing, writes no
`untouched` register. -/
theorem pick_nv (P : Params) : ∀ r ∈ untouched, ∀ i ∈ instrs (.ite (.zero .d .r30)
    (.seq (.block [.lsr .d .r8 .r29 (lg P)]) (.ite (.zero .d .r8) (fill P) (.block (direct P))))
    (fill P) : Prog isa), dstOf i ≠ some r := by
  have h : (instrs (.ite (.zero .d .r30)
      (.seq (.block [.lsr .d .r8 .r29 (lg P)]) (.ite (.zero .d .r8) (fill P) (.block (direct P))))
      (fill P) : Prog isa)).all (fun i => untouched.all fun r => dstOf i != some r) = true := by
    unfold fill copy copyWordBody copyBody storeWord direct mov
    split <;> simp only [instrs, List.all_append, List.all_cons, List.all_nil, dstOf] <;> decide
  exact nv_of_all h


/-! ## One iteration -/

theorem body_ok (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) {c : Nat} {s : State} (hI : Inv H s₀ c s) (hcl : c < len s₀) :
    WP isa (updateBody P name code) s fun s' =>
      (∃ c', c < c' ∧ Inv H s₀ c' s') ∧ ∀ r ∈ untouched, s'.gpr r = s.gpr r := by
  have hlen := len_lt s₀; have hr := rr_lt hd s₀ c; have hB := hd.B
  have h63 : lg P < 64 := by have hd_log := hd.log; omega_arith
  have ne : ∀ r ∈ [Reg.r26, .r27, .r28, .r29, .r30], r ≠ .r9 ∧ r ≠ .r8 := by decide
  unfold updateBody
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have hI₁ : Inv H s₀ c s₁ := hI.of_gpr (fun r hr => u₁.other r (ne r hr).1) u₁.mem u₁.rd u₁.wr u₁.sp
  have h10₁ : s₁.gpr .r9 = 0 := by rw [u₁.gpr]; rfl
  have nv₁ : ∀ r ∈ untouched, s₁.gpr r = s.gpr r := fun r hr => u₁.other r (by revert r hr; decide)
  refine WP.seq (WP.mono (WP.gprs (rs := untouched)
    (Q := fun s' => (∃ c' k, c < c' ∧ Pending H s₀ c' k s') ∨ Done H s₀ s') ?_ (pick_nv P))
    fun s' ⟨h, hnv⟩ => ?_)
  · refine WP.ite (decide (rr P s₀ c = 0))
      (by show VG.PPC64LE.eval (.zero .d .r30) s₁ = _; rw [eval_zero, hI₁.r30, ofNat_beq_zero (by have := rr_eq (P := P) s₀ c; omega_arith)])
      (fun hb => ?_) (fun _ => fill_ok hd hp hI₁ hcl h10₁)
    simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_lsr h63 fun s₂ u₂ => WP.block_nil ?_)
    have hI₂ : Inv H s₀ c s₂ := hI₁.of_gpr (fun r hr => u₂.other r (ne r hr).2) u₂.mem u₂.rd u₂.wr u₂.sp
    have h10₂ : s₂.gpr .r9 = 0 := by rw [u₂.other _ (by decide), h10₁]
    refine WP.ite (decide ((len s₀ - c) / P.B = 0))
      (by show VG.PPC64LE.eval (.zero .d .r8) s₂ = _
          rw [eval_zero, u₂.gpr, hI₁.r29, hd.shr (by omega_arith),
            ofNat_beq_zero (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith))])
      (fun _ => fill_ok hd hp hI₂ hcl h10₂) (fun hb' => ?_)
    simp only [decide_eq_false_iff_not, Nat.div_eq_zero_iff_lt hd.pos] at hb'
    have hq := Nat.mul_pos hd.pos (Nat.div_pos (Nat.le_of_not_lt hb') hd.pos)
    exact WP.mono (direct_ok hd hp hI₂ hb (by omega_arith)) fun s' h => .inl ⟨_, _, by omega_arith, h⟩
  · have nv : ∀ r ∈ untouched, s'.gpr r = s.gpr r := fun r hr => (hnv r hr).trans (nv₁ r hr)
    rcases h with ⟨c', k, hc', hP⟩ | ⟨hD, h9⟩
    · refine WP.ite false (by
        show VG.PPC64LE.eval (.zero .d .r9) s' = _
        rw [eval_zero, hP.r9, ofNat_beq_zero (hP.k_lt hd), decide_eq_false (Nat.pos_iff_ne_zero.mp hP.k_pos)])
        (fun h => by cases h) fun _ => WP.mono (hP.compress_ok hd hf hp) fun s'' ⟨h, hpr⟩ =>
          ⟨⟨c', hc', h⟩, fun r hr => (hpr r (untouched_pres r hr)).trans (nv r hr)⟩
    · refine WP.ite true (by show VG.PPC64LE.eval (.zero .d .r9) s' = _; rw [eval_zero, h9]; rfl)
        (fun _ => WP.block_nil ⟨⟨len s₀, hcl, hD⟩, nv⟩) fun h => by cases h

/-! ## Prologue and epilogue -/

theorem prologue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (.block (updateStart P)) s₀ (Inv H s₀ 0) := by
  have hd_N := hd.N; have hd_B := hd.B; have hd_so := hd.so
  refine save_ok hd (by decide) (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [hp.wr], contains_offset hd₂ (by omega_arith)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_li (by have := hd.B_lt; omega) fun s₆ u₆ => wp_and fun s₇ u₇ => WP.block_nil ?_
  have hm₇ : s₇.mem = saveMem P s₀.mem (scr s₀) s₀.gpr := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun iv m hm => ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
    simp
  · rw [hm₇]; exact (saveMem_frame hd _ _ _).mono (by simp)
  · rw [hm₇]; exact saveMem_saved hd _ _ _
  · rw [u₇.gpr, u₆.gpr, u₆.other .r4 (by decide), u₅.other .r4 (by decide), u₄.other .r4 (by decide),
      u₃.other .r4 (by decide), u₂.other .r4 (by decide), g₁, hd.and, Nat.add_zero]
  · rw [List.take_zero, List.append_nil, hm₇]
    exact H.repr_congr hd.pos (fun i hi => frame_bytes (saveMem_frame hd s₀.mem (scr s₀) s₀.gpr)
      (R := stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega_arith) hi) hm.1

/-- The epilogue's postcondition. -/
def Post (P : Params) (H : Md P.B P.N P.L) (s₀ s' : State) : Prop :=
  (∀ p ∈ saved P, s'.gpr p.1 = s₀.gpr p.1) ∧ s'.sp = s₀.sp ∧ (updK H).post s₀ s'

theorem epilogue_ok (hd : Dims P) {s₀ : State} (hp : Pre P s₀) {s : State} (hI : Inv H s₀ (len s₀) s) :
    WP isa (.block (restore P)) s (Post P H s₀) := by
  have hd_so := hd.so
  refine restore_ok hd (scr := scr s₀) hI.r27
    (fun d hd₁ hd₂ => ⟨scR P s₀, by simp [hI.rd, hI.wr, hp.wr], contains_offset hd₂ (by omega_arith)⟩) s₀.gpr
    hI.saved fun s' hs _ hmem _ _ hsp => ⟨hs, by rw [hsp, hI.sp], fun iv m hr hc => ?_⟩
  have := hI.repr iv m ⟨hr, hc⟩
  rwa [List.take_of_length_le (Nat.le_of_eq (D_length _)), ← hmem] at this

/-- `update` without its frame: the nonvolatile registers are kept. -/
theorem correctMain (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : Pre P s₀) :
    WP isa (updateMain P name code) s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ (updK H).post s₀ s' := by
  have hlen := len_lt s₀
  unfold updateMain
  refine WP.seq (WP.mono (WP.gprs (rs := untouched) (Q := Inv H s₀ 0) (prologue_ok (H := H) hd hp) (nv_of_all (by
      unfold updateStart save saved mov
      simp only [instrs, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.all_cons,
        List.all_nil, dstOf]
      decide))) fun s₁ ⟨hI, hnv₁⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun (s : State) => Inv H s₀ (len s₀) s ∧ ∀ r ∈ untouched, s.gpr r = s₀.gpr r) ?_
    fun s₂ ⟨hI₂, hnv₂⟩ => WP.mono (WP.gprs (rs := untouched) (epilogue_ok hd hp hI₂) (nv_of_all (by
      unfold restore
      simp only [instrs, List.all_cons, List.all_nil, dstOf]
      decide)))
    fun s₃ ⟨⟨hsv, hsp, hpost⟩, hnv₃⟩ =>
      ⟨preserved_of hsv fun r hr => (hnv₃ r hr).trans (hnv₂ r hr), hsp, hpost⟩)
  refine WP.ite (decide (len s₀ = 0))
    (by show VG.PPC64LE.eval (.zero .d .r29) s₁ = _
        rw [eval_zero, hI.r29, Nat.sub_zero, ofNat_beq_zero (by omega_arith)])
    (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil ⟨hb ▸ hI, hnv₁⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv H s₀ c s ∧
        ∀ r ∈ untouched, s.gpr r = s₀.gpr r) ?_ (len s₀) s₁ ⟨0, rfl, by omega_arith, hI, hnv₁⟩
    rintro n s ⟨c, rfl, hcl, hI, hnv⟩
    refine WP.mono (body_ok hd hf hp hI hcl) fun s' ⟨⟨c', hc, hI'⟩, hnv'⟩ => ?_
    have hnv'' : ∀ r ∈ untouched, s'.gpr r = s₀.gpr r := fun r hr => (hnv' r hr).trans (hnv r hr)
    have hc' := hI'.c_le
    have hz : isa.eval (.nonzero .d .r29) s' = some (decide (len s₀ - c' ≠ 0)) := by
      show VG.PPC64LE.eval (.nonzero .d .r29) s' = _
      rw [eval_nonzero, hI'.r29, bne, ofNat_beq_zero (by omega_using [hlen])]
      simp
    by_cases hl : len s₀ - c' = 0
    · refine .inl ⟨by rw [hz]; simp [hl], ?_, hnv''⟩
      rwa [show c' = len s₀ by omega_arith] at hI'
    · exact .inr ⟨by rw [hz]; simp [hl], len s₀ - c', by omega_arith, c', rfl, by omega_arith, hI', hnv''⟩

/-- The state `updateMain` starts in: the link register moved to `r0`, then
pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem correct (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hn : 48 * (updateMain P name code).fdepth + 48 < 2 ^ 64)
    (hpf : pushFrames (updateMain P name code) = true) {s₀ : State}
    (hp : Pre P s₀) (hs : Stack P s₀) :
    WP isa (update P name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updK H).post s₀ s' := by
  have hpi : Pre P (inner s₀) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr⟩
  refine WP.seq (WP.cons exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by exact hs.sp48) (fun R hR => ?_) (WP.mono (correctMain hd hf hpi)
    fun s' ⟨hk, hsp, hpost⟩ => ?_) hn hpf
  · rw [show (s₀.write .r0 s₀.lr).wr = s₀.wr from rfl, hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st.sub_left (frame_sub _)
    · exact hs.scr.sub_left (frame_sub _)
  · refine WP.cons exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, fun iv m hm hc => ?_⟩)
    · have h0 : r ≠ .r0 := by revert r hr; decide
      simp only [State.write, h0, ite_false]
      rw [hk r hr]
      simp only [framed, State.write, h0, ite_false]
    · simp [State.write]
    · have hd_N := hd.N; have hd_B := hd.B
      have e : bytesAt (inner s₀).mem (dp s₀) (len s₀) = bytesAt s₀.mem (dp s₀) (len s₀) :=
        bytesAt_congr fun i hi => write_frame_bytes hs.d (len_lt s₀) hi
      have := hpost iv m (H.repr_congr hd.pos (fun i hi => write_frame_bytes (R := stR P s₀) hs.st
        (by show P.N + P.B < 2 ^ 64; omega_arith) hi) hm) hc
      change H.Repr iv s'.mem (s₀.gpr .r3)
        (m ++ bytesAt (inner s₀).mem (s₀.gpr .r5) (s₀.gpr .r6).toNat) at this
      rw [e] at this
      exact this

/-- A state satisfying the precondition (with no data). -/
def sat (P : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r5 => 0x2000 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x3000, P.so + 48⟩]

/-- `update` is verified, given that it is constant time (which the taint
analysis proves of each hash function's code). -/
theorem verified (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hct : ConstantTime isa (updK H).pre (updK H).pub (update P name code))
    (hn : 48 * (updateMain P name code).fdepth + 48 < 2 ^ 64)
    (hpf : pushFrames (updateMain P name code) = true) :
    Verified PPC64LE.target (update P name code) (updK H) := by
  have hd_N := hd.N; have hd_B := hd.B; have hd_so := hd.so
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct hd hf hn hpf (pre_of hs').1 (pre_of hs').2
    exact ⟨t, s', he, h⟩
  · refine ⟨sat P, rfl, rfl, ?_, ?_, ?_, by simp only [sat]; decide, ?_, ?_, ?_⟩
    all_goals try simp only [sat]
    · exact Offset.disjoint_of_le (by simp <;> omega_arith) (by simp <;> omega_arith)
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm
    · exact Offset.disjoint_of_le (by simp) (by simp <;> omega_arith)
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm

/-- The initial taint agrees on the public arguments. -/
theorem agree₀ {s₁ s₂ : State} (hpub : (updK H).pub s₁ s₂) :
    VG.PPC64LE.Taint.Agree (VG.PPC64LE.Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, hsp⟩ := hpub
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end

end VG.Proof.MdStream.PPC64LE.Update
