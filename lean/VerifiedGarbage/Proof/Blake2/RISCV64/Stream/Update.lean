module

public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Streaming BLAKE2 on RISC-V: `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`), with the structure of the PPC64LE proof
(`VG.Proof.Blake2.PPC64LE.Stream.Update`): `correctMain` for the code with
its scratch space in `a4` (`update_scratch`), and `correctFramed` for it in
a frame on the stack (`update`).
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64.Stream.Update

open VG VG.RISCV64 VG.Spec.Blake2
open VG.Impl.Blake2.RISCV64.Stream (N B mov copyLoop fill compressBuf head direct tail rest
  updateMain update updateScratch saved save restore frameBytes)
open VG.Impl.Blake2.RISCV64 (lbb compress)
open VG.RISCV64.Wp (Upd Mupd WP.cons wp_mv wp_addi wp_li wp_add wp_sub)
open VG.RISCV64.Align (pad pad_lt align_al)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen_le repr_iff reprR_append reprR_flush reprR_blocks repr_of_reprR
  stateAt_congr bytesAt_congr bytesAt_add updateRISCV64 updatePost)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev cnt : Nat := (s₀.gpr .a1).toNat
abbrev dp : Addr := s₀.gpr .a2
abbrev len : Nat := (s₀.gpr .a3).toNat
abbrev scr : Addr := s₀.gpr .a4
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev sb : Addr := rnd (scr s₀)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR : Region := ⟨scr s₀, 576⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀]
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀)

theorem pre_of {s₀ : State} (h : (updateRISCV64 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .a3).isLt
theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (s₀.gpr .a1).isLt

/-- A range of the rounded scratch space within the scratch space. -/
theorem sb_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 568) :
    Region.Sub ⟨sb s₀ + BitVec.ofNat 64 d, n⟩ (scR s₀) := by
  rw [show sb s₀ + BitVec.ofNat 64 d = scr s₀ + BitVec.ofNat 64 (pad (scr s₀) + d) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  have := pad_lt (scr s₀)
  exact Offset.sub_base _ (by omega)

theorem sb_sub0 (s₀ : State) {n : Nat} (h : n ≤ 568) : Region.Sub ⟨sb s₀, n⟩ (scR s₀) := by
  have := sb_sub s₀ (d := 0) (n := n) (by omega)
  simpa using this

theorem sb_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 568) :
    (scR s₀).Contains (sb s₀ + BitVec.ofNat 64 d) n := by
  rw [show sb s₀ + BitVec.ofNat 64 d = scr s₀ + BitVec.ofNat 64 (pad (scr s₀) + d) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  have := pad_lt (scr s₀)
  exact Offset.contains_base _ (by omega) (by omega)

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (st s₀) d ∧ s₀.gpr .a1 = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [Update.cnt, h.2.1, toNat_ofNat_lt (by have := h.2.2; omega)]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s7 : s.gpr .s7 = st s₀
  s8 : s.gpr .s8 = sb s₀
  s9 : s.gpr .s9 = dp s₀ + BitVec.ofNat 64 c
  s10 : s.gpr .s10 = BitVec.ofNat 64 (len s₀ - c)
  s11 : s.gpr .s11 = BitVec.ofNat 64 (cnt s₀ + c)
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  frame : Frame [stR s₀ w, scR s₀] s₀.mem s.mem
  saved : Saved (sb s₀) s₀.gpr s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w s₀ c s where
  a7 : s.gpr .a7 = BitVec.ofNat 64 r
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg :=
  [.s7, .s8, .s9, .s10, .s11, .s0, .s1, .s2, .s3, .s4, .s5, .s6]

theorem notC {r : Reg} (hr : r ∈ commonRegs) (x : Reg) (hx : x ∉ commonRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  s7 := by rw [hg _ (by simp)]; exact h.s7
  s8 := by rw [hg _ (by simp)]; exact h.s8
  s9 := by rw [hg _ (by simp)]; exact h.s9
  s10 := by rw [hg _ (by simp)]; exact h.s10
  s11 := by rw [hg _ (by simp)]; exact h.s11
  keep := fun r hr => by rw [hg r (by simp only [untouched] at hr; simp [hr])]; exact h.keep r hr
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s)
    (hg : ∀ r ∈ .a7 :: commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv P s₀ c r s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) hm hrd hwr hsp with
    a7 := by rw [hg _ (by simp)]; exact h.a7
    repr := by rw [hm]; exact h.repr }

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-- Writes to the state and the compression function's scratch space keep the
saved registers. -/
theorem saved_frame {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved (sb s₀) s₀.gpr m)
    (hf : Frame [stR s₀ w, ⟨sb s₀, 512⟩] m m') : Saved (sb s₀) s₀.gpr m' :=
  Spill.Saved.frame h hf fun p hp' r' hr' => by
    have hoff := saved_off p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hp.st_scr.symm.sub_left (sb_sub s₀ (by omega))
    · exact Offset.disjoint_base _ (by omega) (by omega)

/-! ## Prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block (save .a4 ++ [mov .s7 .a0, mov .s8 .t0, mov .s9 .a2, mov .s10 .a3, mov .s11 .a1])) s₀
      fun s => Common w s₀ 0 s ∧ s.mem = saveMem s₀.mem (sb s₀) s₀.gpr := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], sb_contains s₀ (by omega)⟩)
    fun s₁ h₀ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁ _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), h₀]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide)]
    simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide)]
    simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁ _ (by decide)]
    simp
  · have : r ≠ .s7 ∧ r ≠ .s8 ∧ r ≠ .s9 ∧ r ≠ .s10 ∧ r ≠ .s11 ∧ r ≠ .t0 := by
      revert r; decide
    rw [u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1, u₃.other _ this.2.1,
      u₂.other _ this.1, g₁ _ this.2.2.2.2.2]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
    exact (saveMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, sb_sub s₀ (by decide)⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]; exact saveMem_saved _ _ _
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## The bytes in the buffer -/

theorem bufLen_ok' (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ 0 s)
    (hm : s.mem = saveMem s₀.mem (sb s₀) s₀.gpr) :
    WP isa (Impl.Blake2.RISCV64.Stream.bufLen (w := w)) s (Inv P s₀ 0 (Blake2.bufLen w (cnt s₀))) := by
  have hN := hP.len
  have hrepr : ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (st s₀) (d ++ D s₀ 0) (Blake2.bufLen w (cnt s₀)) := by
    intro h0 d hd
    have e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    refine repr_congr hP (fun i hi => ?_) hd.1
    rw [hm]
    exact (saveMem_frame _ _ _).bytes (R := stR s₀ w)
      (by simpa using hp.st_scr.sub_right (sb_sub s₀ (by decide))) (by simp only; omega) hi
  refine WP.mono (bufLen_ok hP) fun s' ⟨h23, g, m, rd, wr, sp⟩ => ?_
  rw [hC.s11, Nat.add_zero, toNat_ofNat_lt (cnt_lt s₀)] at h23
  exact { hC.of_gpr (fun r hr => g r (notC hr .a7)) m rd wr sp with
    a7 := h23, repr := by rw [m]; exact hrepr }

/-! ## Copying data into the buffer -/

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega_using [h])
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, hj])]
    simp [hj, List.getD_eq_getElem?_getD]

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hr26 : s.gpr .s7 = st s₀)
    (hr28 : s.gpr .s9 = dp s₀ + BitVec.ofNat 64 c) (hr30 : s.gpr .a7 = BitVec.ofNat 64 r)
    (hr11 : s.gpr .t3 = BitVec.ofNat 64 k) (hf : Frame [stR s₀ w, scR s₀] s₀.mem s.mem)
    (hs : Saved (sb s₀) s₀.gpr s.mem)
    (hrepr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r) :
    WP isa (copyLoop (w := w)) s fun s' =>
      (∀ x, x ≠ .t1 → x ≠ .t2 → x ≠ .s9 → x ≠ .a7 → x ≠ .t3 → s'.gpr x = s.gpr x) ∧
      s'.gpr .s9 = dp s₀ + BitVec.ofNat 64 (c + k) ∧ s'.gpr .a7 = BitVec.ofNat 64 (r + k) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s.sp ∧ Frame [stR s₀ w, scR s₀] s₀.mem s'.mem ∧
      Saved (sb s₀) s₀.gpr s'.mem ∧
      ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s'.mem (st s₀) (d ++ D s₀ (c + k)) (r + k) := by
  have hl := hP.len
  have hL := len_lt s₀
  have hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨dR s₀, by simp [hrd, hp.rd], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hck, hi]) (by omega_using [hck, hL, hi])⟩
  have hdst : ∀ i < k, InRegions s.wr (st s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨stR s₀ w, by simp [hwr, hp.wr], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hrk, hi]) (by omega_using [hrk, hl, hi])⟩
  have hd : Region.Disjoint ⟨dp s₀ + BitVec.ofNat 64 c, k⟩ ⟨st s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ :=
    (hp.d_st.sub_left (Offset.sub_base _ (by omega_using [hck]))).sub_right (Offset.sub_base _ (by omega_using [hrk]))
  refine copyLoop_ok (w := w) hP.N64 hk (by omega_using [hrk, hl]) hr26 hr28 hr30 hr11 hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  have hx : bytesAt s.mem (dp s₀ + BitVec.ofNat 64 c) k = bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k :=
    bytesAt_congr fun i hi => by
      rw [Offset.add_add]
      exact hf.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
        (Nat.le_of_lt hL) (show c + i < len s₀ by omega_using [hck, hi])
  have hm : s'.mem = writeBytes s.mem (st s₀ + BitVec.ofNat 64 (bufOff w + r))
      (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx]
  have hfw : Frame [stR s₀ w] s.mem s'.mem := by
    rw [hm]
    exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Offset.contains_base _ (by omega_using [hrk]) (by omega_using [hrk, hl]))
  refine ⟨h.other, h.s9.trans (Offset.add_add _ _ _), h.a7, h.rd.trans hrd, h.wr.trans hwr, h.sp,
    hf.trans (hfw.mono (by simp)), saved_frame hp hs (hfw.mono (by simp)), fun h0 d hd => ?_⟩
  have e : d ++ D s₀ (c + k) = d ++ D s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k := by
    rw [D, bytesAt_add, List.append_assoc]
  rw [e]
  have := reprR_append P (hrepr h0 d hd) (x := bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k)
    (mem' := s'.mem) (by rw [bytesAt_length]; exact hrk) ?_ ?_
  · rwa [bytesAt_length] at this
  · rw [hm]
    exact stateAt_congr fun i hi => writeBytes_before _ _ _ (by omega_using [hi]) (by rw [bytesAt_length]; omega_using [hrk, hl])
  · rw [hm, ← Offset.add_add, bytesAt_writeBytes _ _ _ _ (by rw [bytesAt_length]; omega_using [hrk, hl])]

/-! ## Calling the compression function -/

/-- The blocks compressed are the (full) buffer or blocks of data. -/
def Src (w : Nat) (s₀ : State) (src : Addr) (n : Nat) : Prop :=
  (src = st s₀ + BitVec.ofNat 64 (bufOff w) ∧ n = blockBytes w) ∨
    ∃ c₀, src = dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + n ≤ len s₀

theorem callOk (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s)
    {src : Addr} {n : Nat} (hsrc : Src w s₀ src n) : CallOk (w := w) s (st s₀) (sb s₀) src n := by
  have hl := hP.len; have := len_lt s₀
  have eN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega_using [])
  have eso : Region.Sub ⟨sb s₀, 512⟩ (scR s₀) := sb_sub0 s₀ (by decide)
  have eSrc : Region.Sub ⟨src, n⟩ (stR s₀ w) ∨ Region.Sub ⟨src, n⟩ (dR s₀) := by
    rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ Offset.sub_base _ (by omega_using []))
    · exact .inr (h' ▸ Offset.sub_base _ (by omega_using [hc₀]))
  refine ⟨h.s7, h.s8, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_, ?_, ?_⟩
  · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hl])
    · exact (hp.d_st.sub_left (h' ▸ Offset.sub_base _ (by omega_using [hc₀]))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨stR s₀ w, by simp, bufOff w, h', by simp⟩
      · exact ⟨dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, pad (scr s₀), rfl, by have := pad_lt (scr s₀); simp only; omega⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, pad (scr s₀), rfl, by have := pad_lt (scr s₀); simp only; omega⟩

theorem commonRegs_preserved : ∀ r ∈ commonRegs, r ∈ preserved := by decide

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State}
    (h : Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, s'.gpr r = s.gpr r)
    (hf : Frame [⟨st s₀, bufOff w⟩, ⟨sb s₀, 512⟩] s.mem s'.mem) :
    Common w s₀ c s' := by
  have hl := hP.len
  have hf' : Frame [stR s₀ w, ⟨sb s₀, 512⟩] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨⟨sb s₀, 512⟩, by simp, fun _ h => h⟩
  have hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r := fun r hr =>
    hcs r (commonRegs_preserved r hr)
  refine ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, by rw [hg _ (by simp)]; exact h.s7,
    by rw [hg _ (by simp)]; exact h.s8, by rw [hg _ (by simp)]; exact h.s9,
    by rw [hg _ (by simp)]; exact h.s10, by rw [hg _ (by simp)]; exact h.s11,
    fun r hr => by rw [hg r (by simp only [untouched] at hr; simp [hr])]; exact h.keep r hr,
    h.frame.trans (hf'.sub fun r hr => ?_), saved_frame hp h.saved hf'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
  · exact ⟨scR s₀, by simp, sb_sub0 s₀ (by decide)⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

theorem one_toNat : (BitVec.ofNat 64 1).toNat = 1 := rfl

/-- Compressing the full buffer. -/
theorem compressBuf_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀)
    {c : Nat} {s : State} (hI : Inv P s₀ c (blockBytes w) s) :
    WP isa (compressBuf P) s (Inv P s₀ c 0) := by
  have hl := hP.len
  have hN := hP.N64
  have hc := hI.c_le
  unfold compressBuf
  refine WP.seq (compressWith_ok hf (bufArgs_ok hP (by decide))
    (by rw [one_toNat, Nat.mul_one]; exact callOk hP hp hI.toCommon (.inl ⟨by rw [hI.s7], rfl⟩))
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  refine wp_li (imm := 0) (by decide) fun s₂ u₂ => WP.block_nil ?_
  have hC := hI.toCommon.after_call hP hp hrd hwr hsp hcs hfr
  refine { hC.of_gpr (fun r hr => u₂.other r (notC hr .a7)) u₂.mem u₂.rd u₂.wr u₂.sp with
    a7 := by rw [u₂.gpr], repr := fun h0 d hd => ?_ }
  rw [u₂.mem]
  refine reprR_flush P hP.pos (hI.repr h0 d hd) ?_
  have hlt := hd.2.2
  rw [hst, one_toNat, compressBlocks_one, hI.s7, hI.s11, List.length_append, D, bytesAt_length,
    ← hd.cnt_eq, toNat_ofNat_lt (by rw [← hd.cnt_eq] at hlt; omega_using [hc, hlt])]
  rfl

/-! ## `head`: filling the buffer -/

theorem lt_of_div_zero {x b : Nat} (hb : 0 < b) (h : x / b = 0) : x < b := by
  refine Nat.lt_of_not_le fun hc => ?_
  have := Nat.div_pos hc hb
  omega_using [h, this]

theorem le_of_div_ne {x b : Nat} (h : x / b ≠ 0) : b ≤ x := by
  refine Nat.le_of_not_lt fun hc => h (Nat.div_eq_of_lt hc)

/-- Copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P s₀ c r s) :
    WP isa (fill (w := w)) s (Inv P s₀ (c + min (blockBytes w - r) (len s₀ - c))
      (r + min (blockBytes w - r) (len s₀ - c))) := by
  have hl := hP.len
  have hL := len_lt s₀
  have hcn := cnt_lt s₀
  have hc := hI.c_le
  have hpos := hP.pos
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  have ha₂ : a ≤ len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold fill
  refine WP.seq (wp_li (B_lt hP) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_srl hP.lbb.1 fun s₃ u₃ => WP.block_nil ?_)
  have h11 : s₃.gpr .t3 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.a7, B_eq, sub_ofNat hr]
  have h9 : s₃.gpr .t1 = BitVec.ofNat 64 ((len s₀ - c) / blockBytes w) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.s10, shr_ofNat hP (by omega_using [hL])]
  have g₃ : ∀ x, x ≠ .t1 → x ≠ .t3 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h1, u₂.other x h2, u₁.other x h2]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  -- `t3` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .t3 = BitVec.ofNat 64 a ∧
      (∀ x, x ≠ .t1 → x ≠ .t3 → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ fun t ht => ?_)
  · refine WP.ite _ (zero_iff s₃ h9 (by have := Nat.div_le_self (len s₀ - c) (blockBytes w); omega_using [hL, this]))
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      have hlt := lt_of_div_zero hpos hb
      refine WP.seq (wp_add fun s₄ u₄ => wp_srl hP.lbb.1 fun s₅ u₅ => WP.block_nil ?_)
      have h9' : s₅.gpr .t1 = BitVec.ofNat 64 ((len s₀ - c + r) / blockBytes w) := by
        rw [u₅.gpr, u₄.gpr, g₃ _ (by decide) (by decide), g₃ _ (by decide) (by decide), hI.s10, hI.a7,
          ← BitVec.ofNat_add, shr_ofNat hP (by omega_using [hr, hl, hlt])]
      have g₅ : ∀ x, x ≠ .t1 → x ≠ .t3 → s₅.gpr x = s.gpr x := fun x h1 h2 => by
        rw [u₅.other x h1, u₄.other x h1, g₃ x h1 h2]
      have hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, hm₃]
      have hrd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, hrd₃]
      have hwr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, hwr₃]
      have hsp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, hsp₃]
      refine WP.ite _ (zero_iff s₅ h9' (by have := Nat.div_le_self (len s₀ - c + r) (blockBytes w); omega_using [hr, hl, hlt, this]))
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        have hlt' := lt_of_div_zero hpos hb'
        refine wp_mv fun s₆ u₆ => WP.block_nil ⟨?_, fun x h1 h2 => by rw [u₆.other x h2, g₅ x h1 h2],
          by rw [u₆.mem, hm₅], by rw [u₆.rd, hrd₅], by rw [u₆.wr, hwr₅], by rw [u₆.sp, hsp₅]⟩
        rw [u₆.gpr, g₅ _ (by decide) (by decide), hI.s10, ha, Nat.min_eq_right (by omega_using [hlt'])]
      · simp only [decide_eq_false_iff_not] at hb'
        have hle := le_of_div_ne hb'
        refine WP.block_nil ⟨?_, g₅, hm₅, hrd₅, hwr₅, hsp₅⟩
        rw [u₅.other _ (by decide), u₄.other _ (by decide), h11, ha, Nat.min_eq_left (by omega_using [hle])]
    · simp only [decide_eq_false_iff_not] at hb
      have hle := le_of_div_ne hb
      refine WP.block_nil ⟨?_, g₃, hm₃, hrd₃, hwr₃, hsp₃⟩
      rw [h11, ha, Nat.min_eq_left (by omega_using [hle])]
  obtain ⟨tx11, tg, tm, trd, twr, tsp⟩ := ht
  refine WP.seq (wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_)
  have g₆ : ∀ x, x ≠ .t1 → x ≠ .t3 → x ≠ .s10 → x ≠ .s11 → s₆.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₆.other x h4, u₅.other x h3, tg x h1 h2]
  have h611 : s₆.gpr .t3 = BitVec.ofNat 64 a := by rw [u₆.other _ (by decide), u₅.other _ (by decide), tx11]
  have h622 : s₆.gpr .s10 = BitVec.ofNat 64 (len s₀ - (c + a)) := by
    rw [u₆.other _ (by decide), u₅.gpr, tx11, tg _ (by decide) (by decide), hI.s10, sub_ofNat (by omega_using [ha₂])]
    exact congrArg _ (by omega_using [])
  have h624 : s₆.gpr .s11 = BitVec.ofNat 64 (cnt s₀ + (c + a)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), tx11, tg _ (by decide) (by decide), hI.s11,
      ← BitVec.ofNat_add, Nat.add_assoc]
  have hm₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, tm]
  have hrd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, trd]
  have hwr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, twr]
  have hsp₆ : s₆.sp = s.sp := by rw [u₆.sp, u₅.sp, tsp]
  have hkeep₆ : ∀ r ∈ untouched, s₆.gpr r = s₀.gpr r := fun r hr => by
    rw [g₆ r (notU hr .t1) (notU hr .t3) (notU hr .s10) (notU hr .s11), hI.keep r hr]
  refine WP.ite _ (zero_iff s₆ h611 (by omega_using [hL, ha₂])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨⟨by omega_using [hc], hrd₆.trans hI.rd, hwr₆.trans hI.wr, hsp₆.trans hI.sp, ?_, ?_, ?_, h622,
      h624, hkeep₆, by rw [hm₆]; exact hI.frame, by rw [hm₆]; exact hI.saved⟩, ?_, ?_⟩
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s7
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s8
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.s9
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.a7
    · rw [hm₆, Nat.add_zero]; exact hI.repr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok hP hp (c := c) (r := r) (k := a) (by omega_using [hb]) (by omega_using [ha₁, hb]) (by omega_using [ha₂, hb])
      (hrd₆.trans hI.rd) (hwr₆.trans hI.wr)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s7)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s9)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.a7) h611
      (by rw [hm₆]; exact hI.frame) (by rw [hm₆]; exact hI.saved) (by rw [hm₆]; exact hI.repr))
      fun s₈ ⟨g₈, h821, h823, rd₈, wr₈, sp₈, f₈, sv₈, rp₈⟩ => ?_
    refine ⟨⟨by omega_using [ha₂, hb], rd₈, wr₈, sp₈.trans (hsp₆.trans hI.sp), ?_, ?_, h821, ?_, ?_, fun r hr => ?_, f₈, sv₈⟩,
      h823, rp₈⟩
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s7
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.s8
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h622
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h624
    · rw [g₈ r (notU hr .t1) (notU hr .t2) (notU hr .s9) (notU hr .a7) (notU hr .t3)]
      exact hkeep₆ r hr

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, Inv P s₀ c r s ∧ ((c = len s₀ ∧ 1 ≤ r) ∨ (c < len s₀ ∧ r = 0))

theorem head_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {r : Nat}
    (hr : r ≤ blockBytes w) (hl : 0 < len s₀) {s : State} (hI : Inv P s₀ 0 r s) :
    WP isa (head P) s (HeadPost P s₀) := by
  have hL := len_lt s₀
  have hl' := hP.len
  unfold head
  refine WP.ite _ (zero_iff s hI.a7 (by omega_using [hr, hl'])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (fill_ok hP hp hr hI) fun s₂ hI₂ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂
    refine WP.ite _ (zero_iff s₂ hI₂.s10 (by omega_using [hL])) (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₂, .inl ⟨by omega_using [hb'], by omega_using [hb]⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      have e : r + min (blockBytes w - r) (len s₀) = blockBytes w := by omega_using [hr, hb']
      rw [e] at hI₂
      exact WP.mono (compressBuf_ok hP hf hp hI₂) fun s₄ hI₄ => ⟨_, _, hI₄, .inr ⟨by omega_using [hb'], rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

/-- The arguments for compressing blocks of data. -/
theorem directArgs_ok {σ : State} (hB : B w < 2048) :
    WP isa (.block (([mov .a0 .s7] : List Instr) ++ ([mov .a1 .s9, mov .a2 .t2,
      .addi .a3 .s11 (B w : Nat), .li .a4 0] : List Instr) ++ ([mov .a5 .s8] : List Instr))) σ
      fun s => Setup σ s (σ.gpr .s9) (σ.gpr .t2) (σ.gpr .s11 + BitVec.ofNat 64 (B w)) false := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_addi hB fun s₄ u₄ =>
    wp_li (imm := 0) (by decide) fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_
  have hcs : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr]; rfl
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hcs r hr
    rw [u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1, u₁.other _ h0]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {c : Nat}
    (hc : c < len s₀) {s : State} (hI : Inv P s₀ c 0 s) :
    WP isa (direct P) s (Inv P s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) 0) := by
  have hl := hP.len
  have hL := len_lt s₀
  have hcn := cnt_lt s₀
  have hpos := hP.pos
  obtain ⟨k, hk⟩ : ∃ k, k = (len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  have hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
  have hmod := Nat.mod_lt (len s₀ - c - 1) hpos
  rw [← hk] at hdm
  have hkle : k ≤ len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_dec fun s₁ u₁ => wp_srl hP.lbb.1 fun s₂ u₂ => WP.block_nil ?_)
  have h10 : s₂.gpr .t2 = BitVec.ofNat 64 k := by
    rw [u₂.gpr, u₁.gpr, hI.s10, sub_ofNat (by omega_using [hc]), shr_ofNat hP (by omega_using [hL]), hk]
  have hC₂ : Common w s₀ c s₂ := hI.toCommon.of_gpr
    (fun r hr => by rw [u₂.other r (notC hr .t2), u₁.other r (notC hr .t1)])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  have h23 : s₂.gpr .a7 = BitVec.ofNat 64 0 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hI.a7
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.ite _ (zero_iff s₂ h10 (by omega_using [hL, hkle])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hC₂, h23, by rw [hm₂]; exact hI.repr⟩
  simp only [decide_eq_false_iff_not] at hb
  have hBk : blockBytes w * k + 1 ≤ len s₀ - c := by omega_using [hdm, hkle, hb]
  have hBk' : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ (by omega_using [hb])
  have hsrc : Src w s₀ (s₂.gpr .s9) (blockBytes w * (s₂.gpr .t2).toNat) :=
    .inr ⟨c, hC₂.s9, by rw [h10, toNat_ofNat_lt (by omega_using [hL, hkle])]; omega_using [hBk]⟩
  refine WP.seq (compressWith_ok hf (directArgs_ok (B_lt hP)) (callOk hP hp hC₂ hsrc)
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  have hC' := hC₂.after_call hP hp hrd hwr hsp hcs hfr
  refine wp_dec fun s₁ u₁ => wp_andi (imm_B1 hP) fun s₄ u₄ =>
    wp_addi (imm := 1) (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_mv fun s₉ u₉ => wp_li (imm := 0) (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
  have hm : (len s₀ - c - 1) % blockBytes w + 1 = len s₀ - (c + blockBytes w * k) := by omega
  have hr9 : s₅.gpr .t1 = BitVec.ofNat 64 (len s₀ - (c + blockBytes w * k)) := by
    rw [u₅.gpr, u₄.gpr, u₁.gpr, hC'.s10, sub_ofNat (by omega), mask_mod hP,
      toNat_ofNat_lt (by omega), ← BitVec.ofNat_add, hm]
  have h10₆ : s₆.gpr .t2 = BitVec.ofNat 64 (blockBytes w * k) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₁.other _ (by decide), hC'.s10, hr9,
      sub_ofNat (by omega)]
    exact congrArg _ (by omega)
  have hg : ∀ x, x ≠ .t1 → x ≠ .t2 → x ≠ .s9 → x ≠ .s10 → x ≠ .s11 → x ≠ .a7 → s₁₀.gpr x = s'.gpr x :=
    fun x h1 h2 h3 h4 h5 h6 => by
      rw [u₁₀.other x h6, u₉.other x h4, u₈.other x h5, u₇.other x h3, u₆.other x h2, u₅.other x h1,
        u₄.other x h1, u₁.other x h1]
  have hm₉ : s₁₀.mem = s'.mem := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₁.mem]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [hm₉]; exact hC'.frame,
    by rw [hm₉]; exact hC'.saved⟩, ?_, fun h0 d hd => ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₁.rd, hC'.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₁.wr, hC'.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₁.sp, hC'.sp]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.s7
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.s8
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h10₆, u₅.other _ (by decide), u₄.other _ (by decide),
      u₁.other _ (by decide), hC'.s9, Offset.add_add]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), hr9]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other .s11 (by decide),
      u₇.other .t2 (by decide), h10₆, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₁.other _ (by decide), hC'.s11, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hg r (notU hr .t1) (notU hr .t2) (notU hr .s9) (notU hr .s10) (notU hr .s11) (notU hr .a7)]
    exact hC'.keep r hr
  · rw [u₁₀.gpr]
  · have hcnt := hd.cnt_eq
    have hlt := hd.2.2
    have e : d ++ D s₀ (c + blockBytes w * k) =
        d ++ D s₀ c ++ bytesAt s₂.mem (dp s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (dp s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₂.data hp (by omega_using [hm, hi])).symm
    rw [hm₉, e]
    refine reprR_blocks P hpos (by rw [hm₂]; exact hI.repr h0 d hd) ?_
    rw [hst, h10, hC₂.s9, hC₂.s11, B_eq, ← BitVec.ofNat_add, toNat_ofNat_lt (by omega_using [hkle, hlt]),
      toNat_ofNat_lt (by omega_using [hBk', hm, hcnt, hlt]), List.length_append, D, bytesAt_length, ← hcnt]

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} (hc₁ : c < len s₀)
    (hc₂ : len s₀ - c ≤ blockBytes w) {s : State} (hI : Inv P s₀ c 0 s) :
    WP isa (tail (w := w)) s (Inv P s₀ (len s₀) (len s₀ - c)) := by
  have hL := len_lt s₀
  unfold tail
  refine WP.seq (wp_mv fun s₁ u₁ => wp_add fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
  have hg : ∀ x, x ≠ .t3 → x ≠ .s11 → x ≠ .s10 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₃.other x h3, u₂.other x h2, u₁.other x h1]
  have h11 : s₃.gpr .t3 = BitVec.ofNat 64 (len s₀ - c) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.s10]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (copy_ok hP hp (c := c) (r := 0) (k := len s₀ - c) (by omega_using [hc₁]) (by omega_using [hc₂]) (by omega_using [hc₁])
      (by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.s7)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.s9)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.a7) h11
      (by rw [hm₃]; exact hI.frame) (by rw [hm₃]; exact hI.saved) (by rw [hm₃]; exact hI.repr))
    fun s₄ ⟨g₄, h421, h423, rd₄, wr₄, sp₄, f₄, sv₄, rp₄⟩ => ?_
  have e : c + (len s₀ - c) = len s₀ := by omega_using [hc₁]
  rw [e] at h421 rp₄
  rw [Nat.zero_add] at h423 rp₄
  have g : ∀ x, x ≠ .t1 → x ≠ .t2 → x ≠ .s9 → x ≠ .a7 → x ≠ .t3 → x ≠ .s11 → x ≠ .s10 →
      s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 => by rw [g₄ x h1 h2 h3 h4 h5, hg x h5 h6 h7]
  refine ⟨⟨Nat.le_refl _, rd₄, wr₄, by rw [sp₄, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, h421, ?_, ?_,
    fun r hr => ?_, f₄, sv₄⟩, h423, rp₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.s7
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.s8
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.gpr, Nat.sub_self]
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide), hI.s11, hI.s10, ← BitVec.ofNat_add]
    exact congrArg _ (by omega_using [e])
  · rw [g r (notU hr .t1) (notU hr .t2) (notU hr .s9) (notU hr .a7) (notU hr .t3) (notU hr .s11)
      (notU hr .s10)]
    exact hI.keep r hr

/-- All the data is in, and the buffer is not empty. -/
def Full (P : Params w) (s₀ : State) (s : State) : Prop := ∃ r, Inv P s₀ (len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) {s : State}
    (h : HeadPost P s₀ s) : WP isa (rest P) s (Full P s₀) := by
  have hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hcr⟩ := h
  have hc := hI.c_le
  unfold rest
  refine WP.ite _ (zero_iff s hI.s10 (by omega_using [hL])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI, hr⟩
    · omega_using [hb, hc']
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega_using [hb]
    refine WP.seq (WP.mono (direct_ok hP hf hp hc' hI) fun s₂ hI₂ => ?_)
    have hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
    have hmod := Nat.mod_lt (len s₀ - c - 1) hpos
    exact WP.mono (tail_ok hP hp (by omega_using [hc', hdm]) (by omega_using [hdm, hmod]) hI₂) fun s₃ hI₃ => ⟨_, hI₃, by omega_using [hc', hdm]⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : Params w) (s₀ : State) (s : State) : Prop :=
  Common w s₀ (len s₀) s ∧
    ∀ h0 d, R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (st s₀) (d ++ D s₀ (len s₀))

theorem Full.done (hP : Ok P) {s₀ : State} {s : State} (h : Full P s₀ s) : Done P s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

/-- The epilogue's postcondition. -/
def Post (P : Params w) (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧ updatePost P s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre w s₀) {s : State} (hI : Done P s₀ s) :
    WP isa (.block restore) s (Post P s₀) := by
  refine restore_ok (scr := sb s₀) hI.1.s8 (align_al _)
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hI.1.rd, hI.1.wr, hp.wr], sb_contains s₀ (by omega)⟩)
    s₀.gpr hI.1.saved fun s' hs ho hmem _ _ hsp => ⟨⟨preserved_of hs fun r hr => ?_,
      by rw [hsp, hI.1.sp], hs (.ra, 512) (by decide)⟩, fun h0 d hr hc hl => ?_⟩
  · rw [ho r (by revert r; decide), hI.1.keep r hr]
  · rw [hmem]; exact hI.2 h0 d ⟨hr, hc, hl⟩

/-- `update`, with its scratch space in `a4`. -/
theorem correctMain (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) :
    WP isa (updateMain P .a4) s₀ (Post P s₀) := by
  have hL := len_lt s₀
  unfold updateMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hm⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok' hP hp hC hm) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (Q := Done P s₀) ?_ fun s₄ h => epilogue_ok hp h)
  refine WP.ite _ (zero_iff s₂ hI.s10 (by omega)) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq, Nat.sub_zero] at hb
    refine WP.block_nil ⟨by rw [hb]; exact hI.toCommon, fun h0 d hd => ?_⟩
    have := hI.repr h0 d hd
    have e0 : ∀ n, n = 0 → bytesAt s₀.mem (dp s₀) n = [] := by rintro _ rfl; simp [bytesAt]
    rw [show D s₀ 0 = [] from e0 _ rfl, List.append_nil] at this
    rw [show D s₀ (len s₀) = [] from e0 _ hb, List.append_nil]
    rw [repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not, Nat.sub_zero] at hb
    have hr := bufLen_le (w := w) hP.pos (cnt s₀)
    exact WP.seq (WP.mono (head_ok hP hf hp hr (by omega) hI) fun s₄ h =>
      WP.mono (rest_ok hP hf hp h) fun s₅ h => h.done hP)

theorem noFrames_updateMain (hf : CalleeOk P (compress P)) (sc : Reg) :
    (updateMain P sc).noFrames = true := by
  simp only [updateMain, head, rest, fill, compressBuf, direct, tail, Impl.Blake2.RISCV64.Stream.compressWith,
    copyLoop, Impl.Blake2.RISCV64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- `update_scratch`. -/
theorem correct (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (updateRISCV64 P).pre s₀) :
    WP isa (updateScratch P) s₀ fun s' => abiPreserved s₀ s' ∧ (updateRISCV64 P).post s₀ s' :=
  correctMain hP hf (pre_of hpre)

/-- `update`: `update_scratch`, with its scratch space in a frame. -/
theorem correctFramed (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (updateFramedRISCV64 P).pre s₀) :
    WP isa (update P) s₀ fun s' => abiPreserved s₀ s' ∧ (updateFramedRISCV64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hds, -, hsp, hks, hkd⟩ := hpre
  refine WP.alloc (by decide) hsp ?_
  refine WP.seq (Wp.wp_addSp (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  let F : Region := ⟨s₀.sp - BitVec.ofNat 64 576, 576⟩
  have ha4 : s₁.gpr .a4 = s₀.sp - BitVec.ofNat 64 576 := by
    rw [u₁.gpr]; simp [allocd, frameBytes]
  have g₁ : ∀ r, r ≠ .a4 → s₁.gpr r = s₀.gpr r := fun r hr => u₁.other r hr
  have hrd₁ : s₁.rd = s₀.rd := u₁.rd
  have hwr₁ : s₁.wr = F :: s₀.wr := u₁.wr
  let σ := s₁.withRegions [dR s₀] [stR s₀ w, F]
  have hpσ : Pre w σ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show [dR s₀] = [dR σ]
      simp only [dR, dp, len, σ, State.withRegions_gpr, g₁ .a2 (by decide), g₁ .a3 (by decide)]
    · show [stR s₀ w, F] = [stR σ w, scR σ]
      simp only [stR, st, scR, scr, σ, State.withRegions_gpr, g₁ .a0 (by decide), ha4, F]
    · simp only [stR, scR, scr, st, σ, State.withRegions_gpr, g₁ .a0 (by decide), ha4]
      exact hks.symm
    · simp only [stR, dR, dp, len, st, σ, State.withRegions_gpr, g₁ .a0 (by decide),
        g₁ .a2 (by decide), g₁ .a3 (by decide)]
      exact hds
    · simp only [scR, dR, dp, len, scr, σ, State.withRegions_gpr, g₁ .a2 (by decide),
        g₁ .a3 (by decide), ha4]
      exact hkd.symm
  refine WP.narrow (correctMain hP hf hpσ) ?_ ?_ (fun s' hrd' hwr' hsp' _ hpost => ?_)
    (noFrames_updateMain hf .a4)
  · rw [hrd₁, hwr₁, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨dR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨F, by simp, 0, by simp, by simp⟩
  · rw [hwr₁, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨F, by simp, 0, by simp, by simp⟩
  obtain ⟨⟨hpres, hsp₂, hra⟩, hpost⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_sp] at hpres hsp₂ hra
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun h0 d hr hc hl => ?_⟩
  · show s'.gpr r = s₀.gpr r
    rw [hpres r hr, g₁ r (by revert r; decide)]
  · show s'.sp + BitVec.ofNat 64 frameBytes = s₀.sp
    rw [hsp₂, u₁.sp]; exact BitVec.sub_add_cancel _ _
  · show s'.gpr .ra = s₀.gpr .ra
    rw [hra, g₁ _ (by decide)]
  · have := hpost h0 d
    simp only [State.withRegions_mem, State.withRegions_gpr, u₁.mem,
      g₁ .a0 (by decide), g₁ .a1 (by decide), g₁ .a2 (by decide), g₁ .a3 (by decide)] at this
    simp only [freed]
    exact this hr hc hl

end VG.Proof.Blake2.RISCV64.Stream.Update
