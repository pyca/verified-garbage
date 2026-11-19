module

import VerifiedGarbage.Proof.Blake2.AArch64.Compress
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.CT
public import VerifiedGarbage.Spec.Blake2.Contract
public import VerifiedGarbage.Proof.Blake2.Contract
import VerifiedGarbage.Proof.Framework.AArch64.StackScratch
public import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Common
public import VerifiedGarbage.Impl.StackScratch.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Residue.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Clears
import VerifiedGarbage.Proof.Blake2.Scratch
public import VerifiedGarbage.Proof.MdStream.AArch64.Common
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! ### `Blake2.AArch64.Stream.Update`, which this module and modules that import it used -/

section

/-!
# Streaming BLAKE2 on AArch64: `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`). The same structure as the x86-64 proof
(`VG.Proof.Blake2.X86_64.Stream.Update`), inside the frame saving `x30`
(`WP.frameReg`).
-/

@[expose] public section

namespace VG.Proof.Blake2.AArch64.Stream.Update

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B mov copyLoop fill compressBuf head direct tail rest updateStart
  updateMain update saved save restore)
open VG.Impl.Blake2.AArch64 (lbb compress)
open VG.Proof.MdStream.AArch64 (Upd Mupd toNat_ofNat_lt wp_mov wp_addImm wp_subImm wp_movz wp_add wp_sub
  wp_and wp_lsr ofNat_beq_zero)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen_le repr_iff reprR_append reprR_flush reprR_blocks repr_of_reprR
  stateAt_congr bytesAt_congr bytesAt_add updateAArch64)

variable {w W : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev cnt : Nat := (s₀.gpr .x1).toNat
abbrev dp : Addr := s₀.gpr .x2
abbrev len : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
abbrev scR (W : Nat) : Region := ⟨scr s₀, W⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c
/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 16, 16⟩

end

structure Pre (w W : Nat) (s₀ : State) : Prop where
  hW : 104 ≤ W
  hW' : W ≤ 576
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀ W]
  st_scr : (stR s₀ w).Disjoint (scR s₀ W)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀ W)

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (w W : Nat) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀ w)
  d : (stkR s₀).Disjoint (dR s₀)
  scr : (stkR s₀).Disjoint (scR s₀ W)

theorem pre_of {s₀ : State} (hW : 104 ≤ W) (hW' : W ≤ 576) (h : (updateAArch64 P W).pre s₀) : Pre w W s₀ ∧ Stack w W s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨hW, hW', h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (s₀.gpr .x1).isLt

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (st s₀) d ∧ s₀.gpr .x1 = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [Update.cnt, h.2.1, toNat_ofNat_lt (by have := h.2.2; omega_using [this])]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w W : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = dp s₀ + BitVec.ofNat 64 c
  x22 : s.gpr .x22 = BitVec.ofNat 64 (len s₀ - c)
  x24 : s.gpr .x24 = BitVec.ofNat 64 (cnt s₀ + c)
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  frame : Frame [stR s₀ w, scR s₀ W] s₀.mem s.mem
  saved : Saved (scr s₀) s₀.gpr s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (W : Nat) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w W s₀ c s where
  x23 : s.gpr .x23 = BitVec.ofNat 64 r
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.x19, .x20, .x21, .x22, .x24, .x25, .x26, .x27, .x28]

theorem notC {r : Reg} (hr : r ∈ commonRegs) (x : Reg) (hx : x ∉ commonRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w W s₀ c s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common w W s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  x19 := by rw [hg _ (by simp)]; exact h.x19
  x20 := by rw [hg _ (by simp)]; exact h.x20
  x21 := by rw [hg _ (by simp)]; exact h.x21
  x22 := by rw [hg _ (by simp)]; exact h.x22
  x24 := by rw [hg _ (by simp)]; exact h.x24
  keep := fun r hr => by rw [hg r (by simp only [untouched] at hr; simp [hr])]; exact h.keep r hr
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w W s₀) {c : Nat} {s : State} (h : Common w W s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-- Writes to the state and the compression function's scratch space keep the
saved registers. -/
theorem saved_frame {s₀ : State} (hp : Pre w W s₀) {m m' : Mem} (h : Saved (scr s₀) s₀.gpr m)
    (hf : Frame [stR s₀ w, ⟨scr s₀, 56⟩] m m') : Saved (scr s₀) s₀.gpr m' :=
  Spill.Saved.frame h hf fun p hp' r' hr' => by
    obtain hoff := saved_off p hp'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega_using [hoff, hp.hW, hp.hW']))
    · exact Offset.disjoint_base _ (by omega_using [hoff]) (by omega_using [hoff])

/-! ## Prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre w W s₀) :
    WP isa (.block updateStart) s₀ fun s => Common w W s₀ 0 s ∧ s.mem = saveMem s₀.mem (scr s₀) s₀.gpr := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀ W, by simp [hp.wr], Offset.contains_base _ (by omega_using [hd₂, hp.hW, hp.hW']) (by omega_using [hd₂, hp.hW, hp.hW'])⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => WP.block_nil ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
    simp
  · have : r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x24 := by
      simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [u₆.other _ this.2.2.2.2, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1, u₃.other _ this.2.1,
      u₂.other _ this.1, g₁]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
    exact (saveMem_frame _ _ _).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀ W, by simp, Offset.sub_base _ (by omega_using [hp.hW, hp.hW'])⟩
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]; exact saveMem_saved _ _ _
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## The bytes in the buffer -/

theorem bufLen_ok' (hP : Ok P) {s₀ : State} (hp : Pre w W s₀) {s : State} (hC : Common w W s₀ 0 s)
    (hm : s.mem = saveMem s₀.mem (scr s₀) s₀.gpr) :
    WP isa (Impl.Blake2.AArch64.Stream.bufLen (w := w)) s (Inv P W s₀ 0 (Blake2.bufLen w (cnt s₀))) := by
  have hN := hP.len
  obtain hrepr : ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (st s₀) (d ++ D s₀ 0) (Blake2.bufLen w (cnt s₀)) := by
    intro h0 d hd
    obtain e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    refine repr_congr hP (fun i hi => ?_) hd.1
    rw [hm]
    exact (saveMem_frame _ _ _).bytes (R := stR s₀ w)
      (by simpa using hp.st_scr.sub_right (Offset.sub_base _ (by omega_using [hp.hW, hp.hW']))) (by simp only; omega_using [hN]) hi
  refine WP.mono (bufLen_ok hP) fun s' ⟨h23, g, m, rd, wr, sp⟩ => ?_
  rw [hC.x24, Nat.add_zero, toNat_ofNat_lt (cnt_lt s₀)] at h23
  exact { hC.of_gpr (fun r hr => g r (notC hr .x9) (notC hr .x23)) m rd wr sp with
    x23 := h23, repr := by rw [m]; exact hrepr }

/-! ## Copying data into the buffer -/

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    obtain hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega_using [h])
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    obtain hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, hj])]
    simp [hj, List.getD_eq_getElem?_getD]

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w W s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hx19 : s.gpr .x19 = st s₀)
    (hx21 : s.gpr .x21 = dp s₀ + BitVec.ofNat 64 c) (hx23 : s.gpr .x23 = BitVec.ofNat 64 r)
    (hx11 : s.gpr .x11 = BitVec.ofNat 64 k) (hf : Frame [stR s₀ w, scR s₀ W] s₀.mem s.mem)
    (hs : Saved (scr s₀) s₀.gpr s.mem)
    (hrepr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (st s₀) (d ++ D s₀ c) r) :
    WP isa (copyLoop (w := w)) s fun s' =>
      (∀ x, x ≠ .x9 → x ≠ .x12 → x ≠ .x21 → x ≠ .x23 → x ≠ .x11 → s'.gpr x = s.gpr x) ∧
      s'.gpr .x21 = dp s₀ + BitVec.ofNat 64 (c + k) ∧ s'.gpr .x23 = BitVec.ofNat 64 (r + k) ∧
      s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧ s'.sp = s.sp ∧ Frame [stR s₀ w, scR s₀ W] s₀.mem s'.mem ∧
      Saved (scr s₀) s₀.gpr s'.mem ∧
      ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s'.mem (st s₀) (d ++ D s₀ (c + k)) (r + k) := by
  have hl := hP.len
  obtain hL := len_lt s₀
  obtain hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (dp s₀ + BitVec.ofNat 64 c + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨dR s₀, by simp [hrd, hp.rd], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hck, hi]) (by omega_using [hck, hL, hi])⟩
  obtain hdst : ∀ i < k, InRegions s.wr (st s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨stR s₀ w, by simp [hwr, hp.wr], by
      rw [Offset.add_add]; exact Offset.contains_base _ (by omega_using [hrk, hi]) (by omega_using [hrk, hl, hi])⟩
  obtain hd : Region.Disjoint ⟨dp s₀ + BitVec.ofNat 64 c, k⟩ ⟨st s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ :=
    (hp.d_st.sub_left (Offset.sub_base _ (by omega_using [hck]))).sub_right (Offset.sub_base _ (by omega_using [hrk]))
  refine copyLoop_ok (w := w) hP.N64 hk (by omega_using [hrk, hl]) hx19 hx21 hx23 hx11 hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  obtain hx : bytesAt s.mem (dp s₀ + BitVec.ofNat 64 c) k = bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k :=
    bytesAt_congr fun i hi => by
      rw [Offset.add_add]
      exact hf.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr⟩)
        (Nat.le_of_lt hL) (show c + i < len s₀ by omega_using [hck, hi])
  obtain hm : s'.mem = writeBytes s.mem (st s₀ + BitVec.ofNat 64 (bufOff w + r))
      (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx]
  obtain hfw : Frame [stR s₀ w] s.mem s'.mem := by
    rw [hm]
    exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Offset.contains_base _ (by omega_using [hrk]) (by omega_using [hrk, hl]))
  refine ⟨h.other, h.x21.trans (Offset.add_add _ _ _), h.x23, h.rd.trans hrd, h.wr.trans hwr, h.sp,
    hf.trans (hfw.mono (by simp)), saved_frame hp hs (hfw.mono (by simp)), fun h0 d hd => ?_⟩
  obtain e : d ++ D s₀ (c + k) = d ++ D s₀ c ++ bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) k := by
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

theorem callOk (hP : Ok P) {s₀ : State} (hp : Pre w W s₀) {c : Nat} {s : State} (h : Common w W s₀ c s)
    {src : Addr} {n : Nat} (hsrc : Src w s₀ src n) : CallOk (w := w) s (st s₀) (scr s₀) src n := by
  obtain hl := hP.len; have := len_lt s₀
  obtain eN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega_using [hp.hW, hp.hW'])
  obtain eso : Region.Sub ⟨scr s₀, 56⟩ (scR s₀ W) := Region.sub_prefix (by omega_using [hp.hW, hp.hW'])
  obtain eSrc : Region.Sub ⟨src, n⟩ (stR s₀ w) ∨ Region.Sub ⟨src, n⟩ (dR s₀) := by
    rcases hsrc with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ Offset.sub_base _ (by omega_using []))
    · exact .inr (h' ▸ Offset.sub_base _ (by omega_using [hc₀]))
  refine ⟨h.x19, h.x20, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_, ?_, ?_⟩
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
    · exact ⟨scR s₀ W, by simp, 0, by simp, by simp; omega_using [hp.hW, hp.hW']⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀ W, by simp, 0, by simp, by simp; omega_using [hp.hW, hp.hW']⟩

theorem commonRegs_preserved : ∀ r ∈ commonRegs, r ∈ preserved ∧ r ≠ .x30 := by decide

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : Ok P) {s₀ : State} (hp : Pre w W s₀) {c : Nat} {s s' : State}
    (h : Common w W s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp)
    (hcs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r)
    (hf : Frame [⟨st s₀, bufOff w⟩, ⟨scr s₀, 56⟩] s.mem s'.mem) :
    Common w W s₀ c s' := by
  have hl := hP.len
  obtain hf' : Frame [stR s₀ w, ⟨scr s₀, 56⟩] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega_using [])⟩
    · exact ⟨⟨scr s₀, 56⟩, by simp, fun _ h => h⟩
  obtain hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r := fun r hr =>
    hcs r (commonRegs_preserved r hr).1 (commonRegs_preserved r hr).2
  refine ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, by rw [hg _ (by simp)]; exact h.x19,
    by rw [hg _ (by simp)]; exact h.x20, by rw [hg _ (by simp)]; exact h.x21,
    by rw [hg _ (by simp)]; exact h.x22, by rw [hg _ (by simp)]; exact h.x24,
    fun r hr => by rw [hg r (by simp only [untouched] at hr; simp [hr])]; exact h.keep r hr,
    h.frame.trans (hf'.sub fun r hr => ?_), saved_frame hp h.saved hf'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
  · exact ⟨scR s₀ W, by simp, Region.sub_prefix (by omega_using [hp.hW, hp.hW'])⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

theorem one_toNat : (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 := rfl

/-- Compressing the full buffer. -/
theorem compressBuf_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w W s₀)
    {c : Nat} {s : State} (hI : Inv P W s₀ c (blockBytes w) s) :
    WP isa (compressBuf P) s (Inv P W s₀ c 0) := by
  have hl := hP.len
  have hN := hP.N64
  have hc := hI.c_le
  unfold compressBuf
  refine WP.seq (compressWith_ok hf (bufArgs_ok (by omega_using [hN]))
    (by rw [one_toNat, Nat.mul_one]; exact callOk hP hp hI.toCommon (.inl ⟨by rw [hI.x19], rfl⟩))
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  refine wp_movz fun s₂ u₂ => WP.block_nil ?_
  obtain hC := hI.toCommon.after_call hP hp hrd hwr hsp hcs hfr
  refine { hC.of_gpr (fun r hr => u₂.other r (notC hr .x23)) u₂.mem u₂.rd u₂.wr u₂.sp with
    x23 := by rw [u₂.gpr]; rfl, repr := fun h0 d hd => ?_ }
  rw [u₂.mem]
  refine reprR_flush P hP.pos (hI.repr h0 d hd) ?_
  have hlt := hd.2.2
  rw [hst, one_toNat, compressBlocks_one, hI.x19, hI.x24, List.length_append, D, bytesAt_length,
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
theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w W s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P W s₀ c r s) :
    WP isa (fill (w := w)) s (Inv P W s₀ (c + min (blockBytes w - r) (len s₀ - c))
      (r + min (blockBytes w - r) (len s₀ - c))) := by
  have hl := hP.len
  obtain hL := len_lt s₀
  obtain hcn := cnt_lt s₀
  have hc := hI.c_le
  have hpos := hP.pos
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  obtain ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  obtain ha₂ : a ≤ len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold fill
  refine WP.seq (wp_movz fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_lsr hP.lbb.1 fun s₃ u₃ => WP.block_nil ?_)
  obtain h11 : s₃.gpr .x11 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.x23, movz_B hP, sub_ofNat hr]
  obtain h9 : s₃.gpr .x9 = BitVec.ofNat 64 ((len s₀ - c) / blockBytes w) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.x22, shr_ofNat hP (by omega_using [hL])]
  obtain g₃ : ∀ x, x ≠ .x9 → x ≠ .x11 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h1, u₂.other x h2, u₁.other x h2]
  obtain hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  -- `x11` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .x11 = BitVec.ofNat 64 a ∧
      (∀ x, x ≠ .x9 → x ≠ .x11 → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp) ?_ fun t ht => ?_)
  · refine WP.ite _ (zero_iff s₃ h9 (by have := Nat.div_le_self (len s₀ - c) (blockBytes w); omega_using [hL, this]))
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      obtain hlt := lt_of_div_zero hpos hb
      refine WP.seq (wp_add fun s₄ u₄ => wp_lsr hP.lbb.1 fun s₅ u₅ => WP.block_nil ?_)
      obtain h9' : s₅.gpr .x9 = BitVec.ofNat 64 ((len s₀ - c + r) / blockBytes w) := by
        rw [u₅.gpr, u₄.gpr, g₃ _ (by decide) (by decide), g₃ _ (by decide) (by decide), hI.x22, hI.x23,
          ← BitVec.ofNat_add, shr_ofNat hP (by omega_using [hr, hl, hlt])]
      obtain g₅ : ∀ x, x ≠ .x9 → x ≠ .x11 → s₅.gpr x = s.gpr x := fun x h1 h2 => by
        rw [u₅.other x h1, u₄.other x h1, g₃ x h1 h2]
      obtain hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, hm₃]
      obtain hrd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, hrd₃]
      obtain hwr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, hwr₃]
      obtain hsp₅ : s₅.sp = s.sp := by rw [u₅.sp, u₄.sp, hsp₃]
      refine WP.ite _ (zero_iff s₅ h9' (by have := Nat.div_le_self (len s₀ - c + r) (blockBytes w); omega_using [hr, hl, hlt, this]))
        (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        obtain hlt' := lt_of_div_zero hpos hb'
        refine wp_mov fun s₆ u₆ => WP.block_nil ⟨?_, fun x h1 h2 => by rw [u₆.other x h2, g₅ x h1 h2],
          by rw [u₆.mem, hm₅], by rw [u₆.rd, hrd₅], by rw [u₆.wr, hwr₅], by rw [u₆.sp, hsp₅]⟩
        rw [u₆.gpr, g₅ _ (by decide) (by decide), hI.x22, ha, Nat.min_eq_right (by omega_using [hlt'])]
      · simp only [decide_eq_false_iff_not] at hb'
        obtain hle := le_of_div_ne hb'
        refine WP.block_nil ⟨?_, g₅, hm₅, hrd₅, hwr₅, hsp₅⟩
        rw [u₅.other _ (by decide), u₄.other _ (by decide), h11, ha, Nat.min_eq_left (by omega_using [hle])]
    · simp only [decide_eq_false_iff_not] at hb
      obtain hle := le_of_div_ne hb
      refine WP.block_nil ⟨?_, g₃, hm₃, hrd₃, hwr₃, hsp₃⟩
      rw [h11, ha, Nat.min_eq_left (by omega_using [hle])]
  obtain ⟨tx11, tg, tm, trd, twr, tsp⟩ := ht
  refine WP.seq (wp_sub fun s₅ u₅ => wp_add fun s₆ u₆ => WP.block_nil ?_)
  obtain g₆ : ∀ x, x ≠ .x9 → x ≠ .x11 → x ≠ .x22 → x ≠ .x24 → s₆.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₆.other x h4, u₅.other x h3, tg x h1 h2]
  obtain h611 : s₆.gpr .x11 = BitVec.ofNat 64 a := by rw [u₆.other _ (by decide), u₅.other _ (by decide), tx11]
  obtain h622 : s₆.gpr .x22 = BitVec.ofNat 64 (len s₀ - (c + a)) := by
    rw [u₆.other _ (by decide), u₅.gpr, tx11, tg _ (by decide) (by decide), hI.x22, sub_ofNat (by omega_using [ha₂])]
    exact congrArg _ (by omega_using [])
  obtain h624 : s₆.gpr .x24 = BitVec.ofNat 64 (cnt s₀ + (c + a)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₅.other _ (by decide), tx11, tg _ (by decide) (by decide), hI.x24,
      ← BitVec.ofNat_add, Nat.add_assoc]
  obtain hm₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, tm]
  obtain hrd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅.rd, trd]
  obtain hwr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, twr]
  obtain hsp₆ : s₆.sp = s.sp := by rw [u₆.sp, u₅.sp, tsp]
  obtain hkeep₆ : ∀ r ∈ untouched, s₆.gpr r = s₀.gpr r := fun r hr => by
    rw [g₆ r (notU hr .x9) (notU hr .x11) (notU hr .x22) (notU hr .x24), hI.keep r hr]
  refine WP.ite _ (zero_iff s₆ h611 (by omega_using [hL, ha₂])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨⟨by omega_using [hc], hrd₆.trans hI.rd, hwr₆.trans hI.wr, hsp₆.trans hI.sp, ?_, ?_, ?_, h622,
      h624, hkeep₆, by rw [hm₆]; exact hI.frame, by rw [hm₆]; exact hI.saved⟩, ?_, ?_⟩
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.x21
    · rw [g₆ _ (by decide) (by decide) (by decide) (by decide), Nat.add_zero]; exact hI.x23
    · rw [hm₆, Nat.add_zero]; exact hI.repr
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok hP hp (c := c) (r := r) (k := a) (by omega_using [hb]) (by omega_using [ha₁, hb]) (by omega_using [ha₂, hb])
      (hrd₆.trans hI.rd) (hwr₆.trans hI.wr)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x21)
      (by rw [g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x23) h611
      (by rw [hm₆]; exact hI.frame) (by rw [hm₆]; exact hI.saved) (by rw [hm₆]; exact hI.repr))
      fun s₈ ⟨g₈, h821, h823, rd₈, wr₈, sp₈, f₈, sv₈, rp₈⟩ => ?_
    refine ⟨⟨by omega_using [ha₂, hb], rd₈, wr₈, sp₈.trans (hsp₆.trans hI.sp), ?_, ?_, h821, ?_, ?_, fun r hr => ?_, f₈, sv₈⟩,
      h823, rp₈⟩
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide),
        g₆ _ (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h622
    · rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h624
    · rw [g₈ r (notU hr .x9) (notU hr .x12) (notU hr .x21) (notU hr .x23) (notU hr .x11)]
      exact hkeep₆ r hr

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : Params w) (W : Nat) (s₀ : State) (s : State) : Prop :=
  ∃ c r, Inv P W s₀ c r s ∧ ((c = len s₀ ∧ 1 ≤ r) ∨ (c < len s₀ ∧ r = 0))

theorem head_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w W s₀) {r : Nat}
    (hr : r ≤ blockBytes w) (hl : 0 < len s₀) {s : State} (hI : Inv P W s₀ 0 r s) :
    WP isa (head P) s (HeadPost P W s₀) := by
  obtain hL := len_lt s₀
  have hl' := hP.len
  unfold head
  refine WP.ite _ (zero_iff s hI.x23 (by omega_using [hr, hl'])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (fill_ok hP hp hr hI) fun s₂ hI₂ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂
    refine WP.ite _ (zero_iff s₂ hI₂.x22 (by omega_using [hL])) (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₂, .inl ⟨by omega_using [hb'], by omega_using [hb]⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      obtain e : r + min (blockBytes w - r) (len s₀) = blockBytes w := by omega_using [hr, hb']
      rw [e] at hI₂
      exact WP.mono (compressBuf_ok hP hf hp hI₂) fun s₄ hI₄ => ⟨_, _, hI₄, .inr ⟨by omega_using [hb'], rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

/-- The arguments for compressing blocks of data. -/
theorem directArgs_ok {σ : State} (hB : B w < 4096) :
    WP isa (.block (([mov .x0 .x19] : List Instr) ++ ([mov .x1 .x21, mov .x2 .x10,
      .addImm .x .x3 .x24 (B w), .movz .x .x4 0 0] : List Instr) ++ ([mov .x5 .x20] : List Instr))) σ
      fun s => Setup σ s (σ.gpr .x21) (σ.gpr .x10) (σ.gpr .x24 + BitVec.ofNat 64 (B w)) false := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addImm hB fun s₄ u₄ =>
    wp_movz fun s₅ u₅ => wp_mov fun s₆ u₆ => WP.block_nil ?_
  obtain hcs : ∀ r ∈ preserved, r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
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
theorem direct_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w W s₀) {c : Nat}
    (hc : c < len s₀) {s : State} (hI : Inv P W s₀ c 0 s) :
    WP isa (direct P) s (Inv P W s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) 0) := by
  have hl := hP.len
  obtain hL := len_lt s₀
  obtain hcn := cnt_lt s₀
  have hpos := hP.pos
  obtain ⟨k, hk⟩ : ∃ k, k = (len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  obtain hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
  obtain hmod := Nat.mod_lt (len s₀ - c - 1) hpos
  rw [← hk] at hdm
  obtain hkle : k ≤ len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_subImm (by decide) fun s₁ u₁ => wp_lsr hP.lbb.1 fun s₂ u₂ => WP.block_nil ?_)
  obtain h10 : s₂.gpr .x10 = BitVec.ofNat 64 k := by
    rw [u₂.gpr, u₁.gpr, hI.x22, sub_ofNat (by omega_using [hc]), shr_ofNat hP (by omega_using [hL]), hk]
  have hC₂ : Common w W s₀ c s₂ := hI.toCommon.of_gpr
    (fun r hr => by rw [u₂.other r (notC hr .x10), u₁.other r (notC hr .x9)])
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  obtain h23 : s₂.gpr .x23 = BitVec.ofNat 64 0 := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact hI.x23
  obtain hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.ite _ (zero_iff s₂ h10 (by omega_using [hL, hkle])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hC₂, h23, by rw [hm₂]; exact hI.repr⟩
  simp only [decide_eq_false_iff_not] at hb
  obtain hBk : blockBytes w * k + 1 ≤ len s₀ - c := by omega_using [hdm, hkle, hb]
  obtain hBk' : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ (by omega_using [hb])
  obtain hsrc : Src w s₀ (s₂.gpr .x21) (blockBytes w * (s₂.gpr .x10).toNat) :=
    .inr ⟨c, hC₂.x21, by rw [h10, toNat_ofNat_lt (by omega_using [hL, hkle])]; omega_using [hBk]⟩
  refine WP.seq (compressWith_ok hf (directArgs_ok (by rw [B_eq]; omega_using [hl])) (callOk hP hp hC₂ hsrc)
    fun s' hrd hwr hsp hcs hfr hst => ?_)
  obtain hC' := hC₂.after_call hP hp hrd hwr hsp hcs hfr
  refine wp_subImm (by decide) fun s₁ u₁ => wp_movz fun s₃ u₃ => wp_and fun s₄ u₄ =>
    wp_addImm (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ => wp_add fun s₇ u₇ => wp_add fun s₈ u₈ =>
    wp_mov fun s₉ u₉ => WP.block_nil ?_
  obtain hm : (len s₀ - c - 1) % blockBytes w + 1 = len s₀ - (c + blockBytes w * k) := by omega_using [hdm, hBk]
  obtain hx9 : s₅.gpr .x9 = BitVec.ofNat 64 (len s₀ - (c + blockBytes w * k)) := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₁.gpr, hC'.x22, sub_ofNat (by omega_using [hm]), mask_mod hP,
      toNat_ofNat_lt (by omega_using [hL]), ← BitVec.ofNat_add, hm]
  obtain h10₆ : s₆.gpr .x10 = BitVec.ofNat 64 (blockBytes w * k) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₁.other _ (by decide), hC'.x22, hx9, sub_ofNat (by omega_using [])]
    exact congrArg _ (by omega_using [hm])
  obtain hg : ∀ x, x ≠ .x9 → x ≠ .x10 → x ≠ .x21 → x ≠ .x22 → x ≠ .x24 → s₉.gpr x = s'.gpr x :=
    fun x h1 h2 h3 h4 h5 => by
      rw [u₉.other x h4, u₈.other x h5, u₇.other x h3, u₆.other x h2, u₅.other x h1, u₄.other x h1,
        u₃.other x h2, u₁.other x h1]
  obtain hm₉ : s₉.mem = s'.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₁.mem]
  refine ⟨⟨by omega_using [hm], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [hm₉]; exact hC'.frame,
    by rw [hm₉]; exact hC'.saved⟩, ?_, fun h0 d hd => ?_⟩
  · rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₁.rd, hC'.rd]
  · rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₁.wr, hC'.wr]
  · rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₁.sp, hC'.sp]
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.x19
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC'.x20
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), h10₆,
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₁.other _ (by decide),
      hC'.x21, Offset.add_add]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), hx9]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other .x24 (by decide), u₇.other .x10 (by decide), h10₆,
      u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₁.other _ (by decide), hC'.x24, ← BitVec.ofNat_add, Nat.add_assoc]
  · rw [hg r (notU hr .x9) (notU hr .x10) (notU hr .x21) (notU hr .x22) (notU hr .x24)]; exact hC'.keep r hr
  · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), hcs _ (by decide) (by decide), h23]
  · have hcnt := hd.cnt_eq
    have hlt := hd.2.2
    obtain e : d ++ D s₀ (c + blockBytes w * k) =
        d ++ D s₀ c ++ bytesAt s₂.mem (dp s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (dp s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₂.data hp (by omega_using [hm, hi])).symm
    rw [hm₉, e]
    refine reprR_blocks P hpos (by rw [hm₂]; exact hI.repr h0 d hd) ?_
    rw [hst, h10, hC₂.x21, hC₂.x24, B_eq, ← BitVec.ofNat_add, toNat_ofNat_lt (by omega_using [hkle, hlt]),
      toNat_ofNat_lt (by omega_using [hBk', hm, hcnt, hlt]), List.length_append, D, bytesAt_length, ← hcnt]

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : Ok P) {s₀ : State} (hp : Pre w W s₀) {c : Nat} (hc₁ : c < len s₀)
    (hc₂ : len s₀ - c ≤ blockBytes w) {s : State} (hI : Inv P W s₀ c 0 s) :
    WP isa (tail (w := w)) s (Inv P W s₀ (len s₀) (len s₀ - c)) := by
  obtain hL := len_lt s₀
  unfold tail
  refine WP.seq (wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil ?_)
  obtain hg : ∀ x, x ≠ .x11 → x ≠ .x24 → x ≠ .x22 → s₃.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₃.other x h3, u₂.other x h2, u₁.other x h1]
  obtain h11 : s₃.gpr .x11 = BitVec.ofNat 64 (len s₀ - c) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.x22]
  obtain hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (copy_ok hP hp (c := c) (r := 0) (k := len s₀ - c) (by omega_using [hc₁]) (by omega_using [hc₂]) (by omega_using [hc₁])
      (by rw [u₃.rd, u₂.rd, u₁.rd, hI.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x19)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x21)
      (by rw [hg _ (by decide) (by decide) (by decide)]; exact hI.x23) h11
      (by rw [hm₃]; exact hI.frame) (by rw [hm₃]; exact hI.saved) (by rw [hm₃]; exact hI.repr))
    fun s₄ ⟨g₄, h421, h423, rd₄, wr₄, sp₄, f₄, sv₄, rp₄⟩ => ?_
  obtain e : c + (len s₀ - c) = len s₀ := by omega_using [hc₁]
  rw [e] at h421 rp₄
  rw [Nat.zero_add] at h423 rp₄
  obtain g : ∀ x, x ≠ .x9 → x ≠ .x12 → x ≠ .x21 → x ≠ .x23 → x ≠ .x11 → x ≠ .x24 → x ≠ .x22 →
      s₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 => by rw [g₄ x h1 h2 h3 h4 h5, hg x h5 h6 h7]
  refine ⟨⟨Nat.le_refl _, rd₄, wr₄, by rw [sp₄, u₃.sp, u₂.sp, u₁.sp, hI.sp], ?_, ?_, h421, ?_, ?_,
    fun r hr => ?_, f₄, sv₄⟩, h423, rp₄⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.x19
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.x20
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.gpr, Nat.sub_self]; rfl
  · rw [g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), u₁.other _ (by decide), hI.x24, hI.x22, ← BitVec.ofNat_add]
    exact congrArg _ (by omega_using [e])
  · rw [g r (notU hr .x9) (notU hr .x12) (notU hr .x21) (notU hr .x23) (notU hr .x11) (notU hr .x24)
      (notU hr .x22)]
    exact hI.keep r hr

/-- All the data is in, and the buffer is not empty. -/
def Full (P : Params w) (W : Nat) (s₀ : State) (s : State) : Prop := ∃ r, Inv P W s₀ (len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w W s₀) {s : State}
    (h : HeadPost P W s₀ s) : WP isa (rest P) s (Full P W s₀) := by
  obtain hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hcr⟩ := h
  have hc := hI.c_le
  unfold rest
  refine WP.ite _ (zero_iff s hI.x22 (by omega_using [hL])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI, hr⟩
    · omega_using [hb, hc']
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega_using [hb]
    refine WP.seq (WP.mono (direct_ok hP hf hp hc' hI) fun s₂ hI₂ => ?_)
    obtain hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
    obtain hmod := Nat.mod_lt (len s₀ - c - 1) hpos
    exact WP.mono (tail_ok hP hp (by omega_using [hc', hdm]) (by omega_using [hdm, hmod]) hI₂) fun s₃ hI₃ => ⟨_, hI₃, by omega_using [hc', hdm]⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : Params w) (W : Nat) (s₀ : State) (s : State) : Prop :=
  Common w W s₀ (len s₀) s ∧
    ∀ h0 d, R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (st s₀) (d ++ D s₀ (len s₀))

theorem Full.done (hP : Ok P) {s₀ : State} {s : State} (h : Full P W s₀ s) : Done P W s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

/-- The epilogue's postcondition. -/
def Post (P : Params w) (W : Nat) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ (updateAArch64 P W).post s₀ s'

theorem epilogue_ok {s₀ : State} (hp : Pre w W s₀) {s : State} (hI : Done P W s₀ s) :
    WP isa (.block restore) s (Post P W s₀) := by
  refine restore_ok (scr := scr s₀) hI.1.x20
    (fun d hd₁ hd₂ => ⟨scR s₀ W, by simp [hI.1.rd, hI.1.wr, hp.wr], Offset.contains_base _ (by omega_using [hd₂, hp.hW, hp.hW']) (by omega_using [hd₂, hp.hW, hp.hW'])⟩)
    s₀.gpr hI.1.saved fun s' hs ho hmem _ _ hsp => ⟨preserved_of hs fun r hr => ?_, by rw [hsp, hI.1.sp],
      fun h0 d hr hc hl => ?_⟩
  · rw [ho r (by simp only [untouched] at hr; simp only [saved, List.map_cons, List.map_nil]; decide +revert),
      hI.1.keep r hr]
  · rw [hmem]; exact hI.2 h0 d ⟨hr, hc, hl⟩

/-- `update` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w W s₀) :
    WP isa (updateMain P) s₀ (Post P W s₀) := by
  obtain hL := len_lt s₀
  unfold updateMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hm⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok' hP hp hC hm) fun s₂ hI => ?_)
  refine WP.seq (WP.mono (Q := Done P W s₀) ?_ fun s₄ h => epilogue_ok hp h)
  refine WP.ite _ (zero_iff s₂ hI.x22 (by omega_using [hL])) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq, Nat.sub_zero] at hb
    refine WP.block_nil ⟨by rw [hb]; exact hI.toCommon, fun h0 d hd => ?_⟩
    have := hI.repr h0 d hd
    obtain e0 : ∀ n, n = 0 → bytesAt s₀.mem (dp s₀) n = [] := by rintro _ rfl; simp [bytesAt]
    rw [show D s₀ 0 = [] from e0 _ rfl, List.append_nil] at this
    rw [show D s₀ (len s₀) = [] from e0 _ hb, List.append_nil]
    rw [repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not, Nat.sub_zero] at hb
    obtain hr := bufLen_le (w := w) hP.pos (cnt s₀)
    exact WP.seq (WP.mono (head_ok hP hf hp hr (by omega_using [hb]) hI) fun s₄ h =>
      WP.mono (rest_ok hP hf hp h) fun s₅ h => h.done hP)

theorem noFrames_updateMain (hf : CalleeOk P (compress P)) : (updateMain P).noFrames = true := by
  simp only [updateMain, head, rest, fill, compressBuf, direct, tail, Impl.Blake2.AArch64.Stream.compressWith,
    copyLoop, Impl.Blake2.AArch64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- The state `updateMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hW : 104 ≤ W) (hW' : W ≤ 576)
    (hpre : (updateAArch64 P W).pre s₀) :
    WP isa (update P) s₀ fun s' => GprAbi s₀ s' ∧ (updateAArch64 P W).post s₀ s' := by
  obtain ⟨hp, hs⟩ := pre_of hW hW' hpre
  have hl := hP.len
  obtain hpi : Pre w W (inner s₀) := ⟨hp.hW, hp.hW', hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_)
    (WP.mono (correctMain hP hf hpi) fun s' ⟨hk, hsp, hpost⟩ mm u f => ?_)
    (by rw [fdepth_of_noFrames (noFrames_updateMain hf)]; decide)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · exact hs.st
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun h0 d hm hc hlt => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · have e : bytesAt (inner s₀).mem (dp s₀) (len s₀) = bytesAt s₀.mem (dp s₀) (len s₀) :=
        bytesAt_congr fun i hi => write_frame_bytes hs.d (len_lt s₀) hi
      have := hpost h0 d (repr_congr hP (fun i hi => write_frame_bytes (R := stR s₀ w) hs.st
        (by show bufOff w + blockBytes w < 2 ^ 64; omega_using [hl]) hi) hm) hc hlt
      rw [e] at this
      -- The state lies apart from the frame, whose bytes the pop loses.
      exact repr_congr hP (fun i hi => lost_byte (R := stR s₀ w) f hs.st.symm hi) this

end VG.Proof.Blake2.AArch64.Stream.Update

end

end

/-! ### `Blake2.AArch64.Stream.Init`, which this module and modules that import it used -/

section

/-!
# Streaming BLAKE2 on AArch64: `init`

`initState` stores the initial hash value (`initState_ok`); for a key,
`keyBlock` zeroes the buffer (`zero_ok`) and copies the key into it
(`keyLoop_ok`). `init` is a leaf function writing only `x2`, `x3` and
`x9`–`x12`.
-/

@[expose] public section

namespace VG.Proof.Blake2.AArch64.Stream.Init

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B initState)
open VG.Impl.Blake2.AArch64 (sz ws movImm64)
open VG.Proof.Blake2 (initAArch64 bufOff repr_keyBlock stateAt_congr)
open VG.Proof.MdStream.AArch64 (Upd Mupd WP.cons toNat_ofNat_lt wp_movz wp_addImm wp_subImm wp_ldrb wp_strb
  wp_str wp_str32 ofNat_succ)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  write_eq_writeBytes)

/-! ## Instructions at the word size -/

section
variable {w W : Nat} {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movImm64 {d : Reg} {v : BitVec 64} {rest : List Instr}
    (k : ∀ s', Upd s s' d v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm64 d v ++ rest)) s Q := by
  simp only [movImm64, List.cons_append, List.nil_append]
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (k _ ⟨?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩))))
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v
  · simp [State.write, h]

theorem wp_strw (hw : w = 64 ∨ w = 32) {t n : Reg} {off : Nat} {a : Addr}
    (ho : off % (w / 8) = 0 ∧ off < 4096 * (w / 8))
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a (w / 8))
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth w)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str (sz w) t n off :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact wp_str ho ha hout fun s' h => k s' (by rwa [BitVec.setWidth_eq])
  · exact wp_str32 ho ha hout k

theorem wp_lslw (hw : w = 64 ∨ w = 32) {d n : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth w <<< 8).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl (sz w) d n 8 :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact WP.cons rfl (k _ (Upd.write s .x d _))
  · exact WP.cons rfl (k _ (Upd.write s .w d _))

theorem wp_eorw (hw : w = 64 ∨ w = 32) {d n m : Reg}
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth w ^^^ (s.gpr m).setWidth w).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor (sz w) d n m :: is)) s Q := by
  rcases hw with rfl | rfl
  · exact WP.cons rfl (k _ (Upd.write s .x d _))
  · exact WP.cons rfl (k _ (Upd.write s .w d _))

end

/-! ## Sizes -/

section
variable {w W : Nat} (hw : w = 64 ∨ w = 32)
include hw

theorem w_le : w ≤ 64 := by omega_arith

theorem word_in {j : Nat} (hj : j < 8) : w / 8 * j + w / 8 ≤ bufOff w := by
  rcases hw with rfl | rfl <;> simp only [bufOff] <;> omega_arith

theorem word_sep {j k : Nat} (h : j ≠ k) :
    w / 8 * j + w / 8 ≤ w / 8 * k ∨ w / 8 * k + w / 8 ≤ w / 8 * j := by
  rcases hw with rfl | rfl <;> omega_arith

theorem sizes : bufOff w + blockBytes w < 2 ^ 32 ∧ 16 ≤ blockBytes w ∧ blockBytes w % 8 = 0 ∧
    blockBytes w < 2 ^ (w - 8) ∧ w / 8 < 2 ^ 64 ∧ bufOff w ≤ 64 ∧ 0 < w / 8 ∧ w / 8 ≤ 8 := by
  rcases hw with rfl | rfl <;> decide

theorem readW_writeW_self_w (m : Mem) (a : Addr) (v : BitVec w) : (m.writeW a v).readW a w = v := by
  rcases hw with rfl | rfl
  · exact Mem.readW_writeW_self64 m a v
  · exact Mem.readW_writeW_self32 m a v

theorem setWidth_back (x : BitVec w) : (x.setWidth 64).setWidth w = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (w_le hw), BitVec.setWidth_eq]

end

/-! ## The initial hash value -/

section
variable {w W : Nat} (P : Params w)

/-- `IV[k]`, for any `k`. -/
def ivAt (k : Nat) : BitVec w := if h : k < 8 then P.IV[k] else 0

/-- The store of `IV[k + 1]`. -/
def ivStep (k : Nat) : List Instr :=
  movImm64 .x9 ((ivAt P (k + 1)).setWidth 64) ++ [.str (sz w) .x9 .x0 (ws w * (k + 1))]

theorem initState_eq : initState P = (List.range 7).flatMap (ivStep P) ++
    (movImm64 .x9 ((P.IV[0] ^^^ 0x01010000).setWidth 64) ++
    ([.lsl (sz w) .x10 .x3 8, .logic .eor (sz w) .x9 .x9 .x10, .logic .eor (sz w) .x9 .x9 .x1,
      .str (sz w) .x9 .x0 0] : List Instr)) := by
  rw [initState, List.append_assoc]
  rfl

/-- After storing `IV[1..k]`. -/
structure IvInv (s₀ : State) (k : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨s₀.gpr .x0, bufOff w⟩] s₀.mem s.mem
  words : ∀ j < k, s.mem.readW (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (j + 1))) w = ivAt P (j + 1)

variable {P}

theorem iv_step (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .x0, bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < 7) (h : IvInv P s₀ k s) :
    WP isa (.block (ivStep P k)) s (IvInv P s₀ (k + 1)) := by
  have hs := sizes hw
  have hin : (⟨s₀.gpr .x0, bufOff w⟩ : Region).Contains
      (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (k + 1))) (w / 8) :=
    Offset.contains_base _ (word_in hw (by omega_arith)) (by have := word_in hw (j := k + 1) (by omega_arith); omega_arith)
  refine wp_movImm64 fun s₁ u₁ => wp_strw hw (a := s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (k + 1)))
    ⟨Nat.mul_mod_right _ _, by unfold ws; have := word_in hw (j := k + 1) (by omega_arith); omega_arith⟩ ?_ ?_
    fun s₂ g₂ => WP.block_nil ?_
  · rw [u₁.other _ (by decide), h.gpr _ (by decide)]; rfl
  · rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have hv : (s₁.gpr .x9).setWidth w = ivAt P (k + 1) := by rw [u₁.gpr, setWidth_back hw]
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, h.gpr r hr], by rw [g₂.rd, u₁.rd, h.rd],
    by rw [g₂.wr, u₁.wr, h.wr], by rw [g₂.sp, u₁.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [g₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [g₂.mem, hv, u₁.mem]
    by_cases e : j = k
    · subst e; exact readW_writeW_self_w hw _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (word_sep hw (fun h => e (by omega_arith)))
        (by have := word_in hw (j := j + 1) (by omega_arith); omega_arith)
        (by have := word_in hw (j := k + 1) (by omega_arith); omega_arith)) hs.2.2.2.2.1]
      exact h.words j (by omega_arith)

/-- The state after `initState`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → r ≠ .x10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨s₀.gpr .x0, bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (s₀.gpr .x0) = Spec.Blake2.init P (s₀.gpr .x1).toNat (s₀.gpr .x3).toNat

theorem initState_ok (hw : w = 64 ∨ w = 32) {s₀ : State}
    (hwr : ∀ a n, InRegions [⟨s₀.gpr .x0, bufOff w⟩] a n → InRegions s₀.wr a n) :
    WP isa (.block (initState P)) s₀ (StateOk (P := P) s₀) := by
  have hs := sizes hw
  have hle := w_le hw
  rw [initState_eq, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (IvInv P s₀) (iv_step hw hwr) 7 (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_arith)⟩) fun s₇ h₇ => ?_
  have hin : (⟨s₀.gpr .x0, bufOff w⟩ : Region).Contains (s₀.gpr .x0 + BitVec.ofNat 64 0) (w / 8) :=
    Offset.contains_base _ (by have := word_in hw (j := 0) (by omega_arith); omega_arith) (by omega_arith)
  refine wp_movImm64 fun s₁ u₁ => wp_lslw hw fun s₂ u₂ => wp_eorw hw fun s₃ u₃ => wp_eorw hw fun s₄ u₄ =>
    wp_strw hw (a := s₀.gpr .x0 + BitVec.ofNat 64 0) ⟨Nat.zero_mod _, by omega_arith⟩ ?_ ?_
    fun s₅ g₅ => WP.block_nil ?_
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h₇.gpr _ (by decide)]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → s₅.gpr r = s₀.gpr r := fun r h1 h2 => by
    rw [g₅.gpr, u₄.other r h1, u₃.other r h1, u₂.other r h2, u₁.other r h1, h₇.gpr r h1]
  -- The word stored.
  have hv : (s₄.gpr .x9).setWidth w = P.IV[0] ^^^ 0x01010000 ^^^
      (BitVec.ofNat w (s₀.gpr .x3).toNat <<< 8) ^^^ BitVec.ofNat w (s₀.gpr .x1).toNat := by
    rw [u₄.gpr, setWidth_back hw, u₃.other .x1 (by decide),
      u₃.gpr, setWidth_back hw, u₂.other .x9 (by decide), u₂.gpr, setWidth_back hw, u₁.gpr,
      setWidth_back hw, u₂.other .x1 (by decide), u₁.other .x1 (by decide), u₁.other .x3 (by decide),
      h₇.gpr .x1 (by decide), h₇.gpr .x3 (by decide), BitVec.ofNat_toNat, BitVec.ofNat_toNat]
    rfl
  have hm : s₅.mem = s₇.mem.writeW (s₀.gpr .x0 + BitVec.ofNat 64 0) ((s₄.gpr .x9).setWidth w) := by
    rw [g₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd],
    by rw [g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr], by rw [g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h₇.sp],
    ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · apply Vector.ext
    intro j hj
    rw [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set, hm]
    simp only
    split
    · rename_i e; subst e
      rw [Nat.mul_zero, readW_writeW_self_w hw, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega_arith⟩
      have hsep : Mem.Sep (s₀.gpr .x0 + BitVec.ofNat 64 (w / 8 * (j + 1))) (w / 8)
          (s₀.gpr .x0 + BitVec.ofNat 64 0) (w / 8) :=
        Offset.sep _ (.inr (by rw [Nat.mul_succ]; omega_arith))
          (by have := word_in hw (j := j + 1) hj; omega_arith) (by have := word_in hw (j := 0) (by omega_arith); omega_arith)
      rw [Mem.readW_writeW_sep hsep hs.2.2.2.2.1, h₇.words j (by omega_arith)]
      simp only [ivAt, hj, ↓reduceDIte]

end

/-! ## The key block -/

section
variable {w W : Nat}

theorem writeW_zero (m : Mem) (a : Addr) :
    m.writeW a (0 : BitVec 64) = writeBytes m a (List.replicate 8 0) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hn : n < 2 ^ 64)
    (hx : xs.length ≤ n) (hz : ∀ i < n, m (q + BitVec.ofNat 64 i) = 0) :
    bytesAt (writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem (by simp [bytesAt]; omega_arith)
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte]
    rw [List.getElem_append_left hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  · simp only [hi, ↓reduceIte]
    rw [hz i h1, List.getElem_append_right (by omega_arith), List.getElem_replicate]

/-- After zeroing `8 · j` bytes of the buffer, from `σ`. -/
structure ZInv (σ : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = σ.gpr
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  mem : s.mem = writeBytes σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (bufOff w)) (List.replicate (8 * j) 0)

theorem zero_ok (hw : w = 64 ∨ w = 32) {σ : State} (hx9 : σ.gpr .x9 = 0)
    (hwr : ∀ a n, InRegions [⟨σ.gpr .x0, bufOff w + blockBytes w⟩] a n → InRegions σ.wr a n) :
    WP isa (.block ((List.range (B w / 8)).flatMap fun j => [.str .x .x9 .x0 (N w + 8 * j)])) σ
      (ZInv (w := w) σ (blockBytes w / 8)) := by
  have hs := sizes hw
  refine wp_range_flatMap (M := isa) (ZInv (w := w) σ) (fun j s hj h => ?_) _ (Nat.le_refl _) σ
    ⟨rfl, rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil]⟩
  rw [B_eq] at hj
  refine wp_str (a := σ.gpr .x0 + BitVec.ofNat 64 (bufOff w + 8 * j)) ⟨?_, ?_⟩ (by rw [h.gpr, N_eq])
    ?_ fun s' g' => WP.block_nil ⟨g'.gpr.trans h.gpr, g'.rd.trans h.rd, g'.wr.trans h.wr, g'.sp.trans h.sp, ?_⟩
  · rw [N_eq]; rcases hw with rfl | rfl <;> simp only [bufOff] <;> omega_arith
  · rw [N_eq]; rcases hw with rfl | rfl <;> simp only [bufOff, blockBytes] at hj ⊢ <;> omega_arith
  · rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  · have e := writeBytes_append σ.mem (σ.gpr .x0 + BitVec.ofNat 64 (bufOff w))
      (List.replicate (8 * j) 0) (List.replicate 8 0) (by simp; omega_arith)
    rw [List.length_replicate] at e
    rw [g'.mem, h.mem, h.gpr, hx9, writeW_zero, ← Offset.add_ofNat_add_ofNat, e,
      List.replicate_append_replicate, Nat.mul_succ]

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev kp : Addr := s₀.gpr .x2
abbrev kk : Nat := (s₀.gpr .x3).toNat
abbrev buf (w : Nat) : Addr := st s₀ + BitVec.ofNat 64 (bufOff w)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev kR : Region := ⟨kp s₀, kk s₀⟩
/-- The key. -/
abbrev key : List Byte := bytesAt s₀.mem (kp s₀) (kk s₀)

end

/-- After copying `j` bytes of the key over the zeroed buffer `Z`. -/
structure KInv (s₀ : State) (Z : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ kk s₀
  x2 : s.gpr .x2 = kp s₀ + BitVec.ofNat 64 j
  x12 : s.gpr .x12 = buf s₀ w + BitVec.ofNat 64 j
  x3 : s.gpr .x3 = BitVec.ofNat 64 (kk s₀ - j)
  other : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes Z (buf s₀ w) ((key s₀).take j)

theorem keyLoop_ok (hw : w = 64 ∨ w = 32) {s₀ : State} {Z : Mem} {σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ w]) (hd : (kR s₀).Disjoint (stR s₀ w))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes w) (hZ : Frame [stR s₀ w] s₀.mem Z)
    (hσ : KInv (w := w) s₀ Z 0 σ) :
    WP isa (.loop (.block [.ldrb .x9 .x2 0, .strb .x9 .x12 0, .addImm .x .x2 .x2 1,
        .addImm .x .x12 .x12 1, .subImm .x .x3 .x3 1]) (.nonzero .x .x3)) σ
      (KInv (w := w) s₀ Z (kk s₀)) := by
  have hs := sizes hw
  have hkl : kk s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = kk s₀ - j ∧ j < kk s₀ ∧ KInv (w := w) s₀ Z j s)
    ?_ (kk s₀) σ ⟨0, by omega_arith, by omega_arith, hσ⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The key byte read is unchanged.
  have hbyte : s.mem (kp s₀ + BitVec.ofNat 64 j) = s₀.mem (kp s₀ + BitVec.ofNat 64 j) := by
    rw [h.mem]
    have hf : Frame [stR s₀ w] s₀.mem (writeBytes Z (buf s₀ w) ((key s₀).take j)) :=
      hZ.trans (writeBytes_frame Z _ _ (Offset.contains_base _ (by simp; omega_arith) (by omega_arith)))
    exact hf.bytes (R := kR s₀) (by simpa using hd) (by simp; omega_arith) hj
  have hin : InRegions (s.rd ++ s.wr) (kp s₀ + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, hrd]; exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hout : InRegions s.wr (buf s₀ w + BitVec.ofNat 64 j) 1 := by
    rw [h.wr, hwr, Offset.add_ofNat_add_ofNat]
    exact ⟨_, List.mem_cons_self .., Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine wp_ldrb (a := kp s₀ + BitVec.ofNat 64 j) (by decide) (by rw [h.x2]; simp) hin fun s₁ u₁ => ?_
  refine wp_strb (a := buf s₀ w + BitVec.ofNat 64 j) (by decide) (by rw [u₁.other _ (by decide), h.x12]; simp)
    (by rw [u₁.wr]; exact hout) fun s₂ g₂ => ?_
  refine wp_addImm (by decide) fun s₃ u₃ => wp_addImm (by decide) fun s₄ u₄ =>
    wp_subImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  have hx3 : s₅.gpr .x3 = BitVec.ofNat 64 (kk s₀ - (j + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x3,
      sub_ofNat (by omega_arith), Nat.sub_sub]
  have hI : KInv (w := w) s₀ Z (j + 1) s₅ := by
    refine ⟨by omega_arith, ?_, ?_, hx3, fun r h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.x2,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.x12,
        BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [u₅.other r h4, u₄.other r h5, u₃.other r h3, g₂.gpr, u₁.other r h1, h.other r h1 h2 h3 h4 h5]
    · rw [u₅.rd, u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · have hj' : j < (key s₀).length := by simp [bytesAt]; omega_arith
      have hl : (List.take j (key s₀)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₅.mem, u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega_arith), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  by_cases hjk : j + 1 = kk s₀
  · refine .inl ⟨?_, hjk ▸ hI⟩
    show VG.AArch64.eval (.nonzero .x .x3) s₅ = _
    rw [MdStream.AArch64.eval_nonzero, hx3, bne, MdStream.AArch64.ofNat_beq_zero (by omega_arith)]
    simp; omega_arith
  · refine .inr ⟨?_, kk s₀ - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hI⟩
    show VG.AArch64.eval (.nonzero .x .x3) s₅ = _
    rw [MdStream.AArch64.eval_nonzero, hx3, bne, MdStream.AArch64.ofNat_beq_zero (by omega_arith)]
    simp; omega_arith

end

section
variable {w W : Nat} {P : Params w}

theorem keyBlock_eq : Impl.Blake2.AArch64.Stream.keyBlock (w := w) =
    .seq (.block ((.movz .x .x9 0 0 :: (List.range (B w / 8)).flatMap fun j =>
        ([.str .x .x9 .x0 (N w + 8 * j)] : List Instr)) ++ ([.addImm .x .x12 .x0 (N w)] : List Instr)))
      (.loop (.block [.ldrb .x9 .x2 0, .strb .x9 .x12 0, .addImm .x .x2 .x2 1, .addImm .x .x12 .x12 1,
        .subImm .x .x3 .x3 1]) (.nonzero .x .x3)) := by
  rw [Impl.Blake2.AArch64.Stream.keyBlock, List.map_eq_flatMap]

theorem keyBlock_ok (hw : w = 64 ∨ w = 32) {s₀ σ : State}
    (hrd : s₀.rd = [kR s₀]) (hwr : s₀.wr = [stR s₀ w]) (hd : (kR s₀).Disjoint (stR s₀ w))
    (hk : 1 ≤ kk s₀) (hkb : kk s₀ ≤ blockBytes w) (hσ : StateOk (P := P) s₀ σ) :
    WP isa (Impl.Blake2.AArch64.Stream.keyBlock (w := w)) σ fun s =>
      (∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x2 → r ≠ .x3 → r ≠ .x12 → s.gpr r = s₀.gpr r) ∧
      s.sp = s₀.sp ∧ Frame [⟨buf s₀ w, blockBytes w⟩] σ.mem s.mem ∧
      bytesAt s.mem (buf s₀ w) (blockBytes w) = key s₀ ++ List.replicate (blockBytes w - kk s₀) 0 := by
  have hs := sizes hw
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hbuf : ∀ n, n ≤ blockBytes w → (stR s₀ w).Contains (buf s₀ w) n := fun n hn =>
    Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hσ0 : σ.gpr .x0 = st s₀ := hσ.gpr _ (by decide) (by decide)
  rw [keyBlock_eq]
  refine WP.seq (wp_movz fun σ₁ u₁ => ?_)
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (zero_ok hw (σ := σ₁) (by rw [u₁.gpr]; rfl) ?_) fun s₂ h₂ => ?_
  · rw [u₁.wr, hσ.wr, hwr, u₁.other _ (by decide), hσ0]; exact fun _ _ h => h
  have hZ : s₂.mem = writeBytes σ.mem (buf s₀ w) (List.replicate (blockBytes w) 0) := by
    rw [h₂.mem, u₁.other _ (by decide), hσ0, u₁.mem, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hs.2.2.1)]
  have hfZ : Frame [stR s₀ w] s₀.mem s₂.mem := by
    rw [hZ]
    exact (hσ.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩).trans
      (writeBytes_frame _ _ _ (by simpa using hbuf _ (Nat.le_refl _)))
  refine wp_addImm (by rw [N_eq]; omega_arith) fun s₃ u₃ => WP.block_nil ?_
  refine WP.mono (keyLoop_ok hw hrd hwr hd hk hkb hfZ ⟨Nat.zero_le _, ?_, ?_, ?_, ?_,
    by rw [u₃.rd, h₂.rd, u₁.rd, hσ.rd], by rw [u₃.wr, h₂.wr, u₁.wr, hσ.wr],
    by rw [u₃.sp, h₂.sp, u₁.sp, hσ.sp], ?_⟩) fun s h => ?_
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide)]; simp
  · rw [u₃.gpr, h₂.gpr, u₁.other _ (by decide), hσ0, N_eq]; simp
  · rw [u₃.other _ (by decide), h₂.gpr, u₁.other _ (by decide), hσ.gpr _ (by decide) (by decide),
      Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro r h1 h2 h3 h4 h5
    rw [u₃.other r h5, h₂.gpr, u₁.other r h1, hσ.gpr r h1 h2]
  · rw [u₃.mem, List.take_zero, writeBytes_nil]
  have hm : s.mem = writeBytes (writeBytes σ.mem (buf s₀ w) (List.replicate (blockBytes w) 0))
      (buf s₀ w) (key s₀) := by
    rw [h.mem, List.take_of_length_le (by omega_arith), hZ]
  refine ⟨h.other, h.sp, ?_, ?_⟩
  · rw [hm]
    exact (writeBytes_frame _ _ _ (contains_prefix _ (by simp))).trans
      (writeBytes_frame _ _ _ (contains_prefix _ (by omega_arith)))
  · rw [hm, bytesAt_writeBytes (by omega_arith) (by omega_arith) fun i hi => ?_, hxs]
    rw [writeBytes_at _ _ _ (by omega_arith)]
    simp [hi]

end

/-! ## The whole function -/

/-- `init` stores the initial hash value and, for a key, the key block. -/
theorem correct {w : Nat} {P : Params w} {s₀ : State} (hP : Ok P) (hp : (initAArch64 P).pre s₀) :
    WP isa (Impl.Blake2.AArch64.Stream.init P) s₀ fun s' =>
      GprAbi s₀ s' ∧ (initAArch64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, -, -, hkk⟩ := hp
  have hw := hP.w
  have hs := sizes hw
  have hkb : kk s₀ ≤ blockBytes w := Nat.le_trans hkk hP.max
  have hxs : (key s₀).length = kk s₀ := by simp [bytesAt]
  have hsub : ∀ r ∈ [(⟨st s₀, bufOff w⟩ : Region)], ∃ r' ∈ [stR s₀ w], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stR s₀ w, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩
  have hcs : ∀ r ∈ preserved, r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x12 := by decide
  unfold Impl.Blake2.AArch64.Stream.init
  refine WP.seq (WP.mono (initState_ok (P := P) hw (fun a n h => ?_)) fun σ hσ => ?_)
  · rw [hwr]
    obtain ⟨r, hr, hc⟩ := h
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  have hx3 : σ.gpr .x3 = BitVec.ofNat 64 (kk s₀) := by
    rw [hσ.gpr _ (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.ite _ (zero_iff σ hx3 (s₀.gpr .x3).isLt) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨⟨fun r hr => hσ.gpr r (hcs r hr).1 (hcs r hr).2.1, hσ.sp⟩, ?_⟩
    exact repr_keyBlock P hP.pos (hxs ▸ hkb) hσ.state fun h => absurd (hxs ▸ hb) h
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (keyBlock_ok hw hrd hwr hd (by omega_arith) hkb hσ) fun s ⟨hg, hsp, hf, hb'⟩ => ?_
    refine ⟨⟨fun r hr => hg r (hcs r hr).1 (hcs r hr).2.1 (hcs r hr).2.2.1 (hcs r hr).2.2.2.1
      (hcs r hr).2.2.2.2, hsp⟩, ?_⟩
    refine repr_keyBlock P hP.pos (hxs ▸ hkb) ?_ fun _ => by rw [hxs]; exact hb'
    rw [← hσ.state]
    exact stateAt_congr fun i hi => hf.bytes (R := ⟨st s₀, bufOff w⟩)
      (by simpa using Offset.base_disjoint (st s₀) (Nat.le_refl (bufOff w)) (n := blockBytes w) (by omega_arith))
      (by simp only; omega_arith) hi

end VG.Proof.Blake2.AArch64.Stream.Init

end

end

@[expose] public section

section

/-!
# Streaming BLAKE2 on AArch64: `finalize`

Inside the frame saving `x30` (`WP.frameReg`), `finalize` saves the
callee-saved registers (`prologue_ok`), computes the number of buffered bytes
(`bufLen_ok`), zeroes the rest of the buffer (`pad_ok`), compresses it as the
last block (`compressWith_ok`), copies the hash value out (`output_ok`) and
restores the registers (`restore_ok`).
-/

namespace VG.Proof.Blake2.AArch64.Stream.Finalize

open VG VG.AArch64 VG.Spec.Blake2
open VG.Impl.Blake2.AArch64.Stream (N B mov zeroLoop pad compressLast output finalizeMain finalize saved save
  restore)
open VG.Impl.Blake2.AArch64 (compress)
open VG.Proof.Blake2 (finalizeAArch64 bufOff final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.Proof.MdStream.AArch64 (Upd Mupd toNat_ofNat_lt wp_mov wp_movz wp_sub wp_ldr wp_str)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_frame writeBytes_append writeBytes_before
  write_eq_writeBytes)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .x0
abbrev op : Addr := s₀.gpr .x2
abbrev scr : Addr := s₀.gpr .x3
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨op s₀, bufOff w⟩
abbrev scR (W : Nat) : Region := ⟨scr s₀, W⟩
/-- The frame saving `x30`, below the stack pointer. -/
abbrev stkR : Region := ⟨s₀.sp - 16, 16⟩

end

structure Pre (w W : Nat) (s₀ : State) : Prop where
  hW : 104 ≤ W
  hW' : W ≤ 576
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀ W]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀ W)
  out_scr : (outR s₀ w).Disjoint (scR s₀ W)

/-- The frame is below the stack pointer, and disjoint from the buffers. -/
structure Stack (w W : Nat) (s₀ : State) : Prop where
  sp16 : 16 ≤ s₀.sp.toNat
  st : (stkR s₀).Disjoint (stR s₀ w)
  out : (stkR s₀).Disjoint (outR s₀ w)
  scr : (stkR s₀).Disjoint (scR s₀ W)

theorem pre_of {w W : Nat} {P : Params w} {s₀ : State} (hW : 104 ≤ W) (hW' : W ≤ 576) (h : (finalizeAArch64 P W).pre s₀) :
    Pre w W s₀ ∧ Stack w W s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨hW, hW', h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩⟩

/-- The saved registers are outside everything written after the saves. -/
theorem Saved.frame {w W : Nat} {s₀ : State} (hp : Pre w W s₀) {g : Reg → BitVec 64} {m m' : Mem}
    (h : Saved (scr s₀) g m) (hf : Frame [stR s₀ w, outR s₀ w, ⟨scr s₀, 56⟩] m m') :
    Saved (scr s₀) g m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    obtain hoff := saved_off p hp'
    obtain hsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀ W) := Offset.sub_base _ (by have := hp.hW; have := hp.hW'; omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left hsub
    · exact hp.out_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = st s₀
  x20 : s.gpr .x20 = scr s₀
  x21 : s.gpr .x21 = op s₀
  x24 : s.gpr .x24 = s₀.gpr .x1
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  mem : s.mem = saveMem s₀.mem (scr s₀) s₀.gpr

theorem prologue_ok {w W : Nat} {s₀ : State} (hp : Pre w W s₀) :
    WP isa (.block (save .x3 ++ ([mov .x19 .x0, mov .x20 .x3, mov .x21 .x2, mov .x24 .x1] : List Instr)))
      s₀ (Start s₀) := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀ W, by simp [hp.wr], Offset.contains_base _ (by have := hp.hW; have := hp.hW'; omega_arith) (by have := hp.hW; have := hp.hW'; omega_arith)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  · rw [u₅.other _ (notU hr .x24), u₄.other _ (notU hr .x21), u₃.other _ (notU hr .x20),
      u₂.other _ (notU hr .x19), g₁]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## Zeroing the rest of the buffer -/

section
variable {w W : Nat}

/-- Zeroing the buffer from byte `r` (in `x23`) on. -/
theorem pad_ok {s : State} {st : Addr} {r : Nat} (hN : bufOff w ≤ 64) (hr : r ≤ blockBytes w)
    (hbb : blockBytes w < 2 ^ 16) (hx19 : s.gpr .x19 = st) (hx23 : s.gpr .x23 = BitVec.ofNat 64 r)
    (hdst : ∀ i < blockBytes w - r,
      InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (pad (w := w)) s fun s' =>
      (∀ x, x ≠ .x9 → x ≠ .x11 → x ≠ .x12 → x ≠ .x23 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (st + BitVec.ofNat 64 (bufOff w + r))
        (List.replicate (blockBytes w - r) 0) := by
  unfold pad
  refine WP.seq (wp_movz fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_sub fun s₃ u₃ => WP.block_nil ?_)
  obtain g : ∀ x, x ≠ .x9 → x ≠ .x11 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h2, u₂.other x h2, u₁.other x h1]
  obtain h11 : s₃.gpr .x11 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.other .x23 (by decide), u₂.gpr, u₁.other .x23 (by decide), hx23,
      movz_ofNat (n := B w) hbb, B_eq, sub_ofNat hr]
  obtain hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite _ (zero_iff s₃ h11 (by omega_arith)) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨fun x h1 h2 _ _ => g x h1 h2, hrd₃, hwr₃, hsp₃, ?_⟩
    rw [hb, List.replicate_zero, writeBytes_nil, hm₃]
  · simp only [decide_eq_false_iff_not] at hb
    refine zeroLoop_ok (st := st) (r := r) hN (by omega_arith) (by omega_arith)
      (by rw [g _ (by decide) (by decide), hx19])
      (by rw [g _ (by decide) (by decide), hx23]) h11
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl)
      (fun i hi => by rw [hwr₃]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 h4 => by rw [h.other x h3 h4 h2, g x h1 h2], by rw [h.rd, hrd₃],
      by rw [h.wr, hwr₃], by rw [h.sp, hsp₃], ?_⟩
    rw [h.mem, hm₃]

end

/-! ## Bytes -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : bytesAt (writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- The buffer after zeroing it from byte `r` on. -/
theorem pad_bytes {m m' : Mem} {st : Addr} {N r bb : Nat} (hr : r ≤ bb) (hlt : N + bb < 2 ^ 64)
    (hm : m' = writeBytes m (st + BitVec.ofNat 64 (N + r)) (List.replicate (bb - r) 0)) :
    bytesAt m' (st + BitVec.ofNat 64 N) bb =
      bytesAt m (st + BitVec.ofNat 64 N) r ++ List.replicate (bb - r) 0 := by
  conv => lhs; rw [show bb = r + (bb - r) by omega_arith]
  rw [bytesAt_add, Offset.add_ofNat_add_ofNat]
  congr 1
  · refine bytesAt_congr fun i hi => ?_
    rw [hm, Offset.add_ofNat_add_ofNat,
      writeBytes_before m st _ (by omega_arith : N + i < N + r) (by simp; omega_arith)]
  · rw [hm]; exact bytesAt_writeBytes_self _ _ (by simp) (by omega_arith)

/-! ## Copying the hash value out -/

section
variable {w W : Nat}

theorem output_eq : output (w := w) = (List.range (N w / 8)).flatMap fun k =>
    [.ldr .x .x9 .x19 (8 * k), .str .x .x9 .x21 (8 * k)] := rfl

/-- After copying `k` words. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .x9 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
    s.mem = writeBytes σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (8 * k))

theorem output_ok {σ : State} (hN : bufOff w ≤ 64) (hN8 : bufOff w % 8 = 0)
    (hin : ∀ a n, (⟨σ.gpr .x19, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨σ.gpr .x21, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨σ.gpr .x19, bufOff w⟩ ⟨σ.gpr .x21, bufOff w⟩) :
    WP isa (.block (output (w := w))) σ fun s =>
      (∀ r, r ≠ .x9 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
      s.mem = writeBytes σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (bufOff w)) := by
  obtain e : 8 * (N w / 8) = bufOff w := by rw [N_eq]; omega_arith
  rw [output_eq, ← e]
  refine wp_range_flatMap (M := isa) (OInv σ) (fun k s hk ⟨hg, hrd, hwr, hsp, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, rfl, by rw [Nat.mul_zero]; simp [bytesAt, writeBytes_nil]⟩
  rw [N_eq] at hk
  obtain hk8 : 8 * k + 8 ≤ bufOff w := by omega_arith
  obtain hl : (bytesAt σ.mem (σ.gpr .x19) (8 * k)).length = 8 * k := by simp [bytesAt]
  refine wp_ldr (a := σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) ⟨by omega_arith, by omega_arith⟩
    (by rw [hg _ (by decide)]) (by rw [hrd, hwr]; exact hin _ _ (Offset.contains_base _ hk8 (by omega_arith)))
    fun s₁ u₁ => wp_str (a := σ.gpr .x21 + BitVec.ofNat 64 (8 * k)) ⟨by omega_arith, by omega_arith⟩ ?_ ?_ fun s₂ g₂ =>
      WP.block_nil ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, hg r hr], by rw [g₂.rd, u₁.rd, hrd],
        by rw [g₂.wr, u₁.wr, hwr], by rw [g₂.sp, u₁.sp, hsp], ?_⟩
  · rw [u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₁.wr, hwr]; exact hout _ _ (Offset.contains_base _ hk8 (by omega_arith))
  · have hv : s.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64 =
        σ.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64 := by
      rw [hm]
      exact (writeBytes_frame (R := ⟨σ.gpr .x21, bufOff w⟩) _ _ _
        (contains_prefix _ (by omega_arith))).readW
        (Offset.contains_base (k := bufOff w) _ hk8 (by omega_arith)) (by simpa using hd) (by decide)
    obtain e := writeBytes_append σ.mem (σ.gpr .x21) (bytesAt σ.mem (σ.gpr .x19) (8 * k))
      (wordBytes (σ.mem.readW (σ.gpr .x19 + BitVec.ofNat 64 (8 * k)) 64))
      (by rw [hl]; simp [wordBytes]; omega_arith)
    rw [hl] at e
    rw [g₂.mem, u₁.gpr, u₁.mem, hv, hm, writeW_eq, e,
      VG.Proof.Blake2.wordBytes_readW _ _ (.inr rfl), ← bytesAt_add, Nat.mul_succ]

end

/-! ## The whole function -/

section
variable {w W : Nat} {P : Params w}

theorem noFrames_finalizeMain (hf : CalleeOk P (compress P)) : (finalizeMain P).noFrames = true := by
  simp only [finalizeMain, pad, compressLast, Impl.Blake2.AArch64.Stream.compressWith, zeroLoop,
    Impl.Blake2.AArch64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- The registers kept from the prologue to the epilogue. -/
abbrev commonKeep : List Reg := [.x19, .x20, .x21, .x24, .x25, .x26, .x27, .x28]

theorem commonKeep_ok : ∀ r ∈ commonKeep,
    r ∈ preserved ∧ r ≠ .x30 ∧ r ≠ .x9 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x23 := by decide

/-- The epilogue's postcondition. -/
def Post (P : Params w) (W : Nat) (s₀ s' : State) : Prop :=
  (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ (finalizeAArch64 P W).post s₀ s'

/-- `finalize` without its frame: the callee-saved registers but `x30` are kept. -/
theorem correctMain (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w W s₀) :
    WP isa (finalizeMain P) s₀ (Post P W s₀) := by
  have hl := hP.len
  have hN := hP.N64
  have hbb := hP.bb
  obtain hN8 : bufOff w % 8 = 0 := by simp only [bufOff]; omega_arith
  obtain hstN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by have := hp.hW; have := hp.hW'; omega_arith)
  obtain hsave_st : ∀ r ∈ [(⟨scr s₀ + BitVec.ofNat 64 56, 48⟩ : Region)], (stR s₀ w).Disjoint r := by
    simpa using hp.st_scr.sub_right (Offset.sub_base _ (by have := hp.hW; have := hp.hW'; omega_arith))
  unfold finalizeMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  obtain hkeep : ∀ i < bufOff w + blockBytes w,
      s₁.mem (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i) := fun i hi => by
    rw [h₁.mem]; exact (saveMem_frame _ _ _).bytes (R := stR s₀ w) hsave_st (by simp only; omega_arith) hi
  refine WP.seq (WP.mono (bufLen_ok hP) fun s₂ ⟨r23₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [h₁.x24] at r23₂
  generalize hn : (s₀.gpr .x1).toNat = n at r23₂
  obtain hr : Blake2.bufLen w n ≤ blockBytes w := bufLen_le (by omega_arith) n
  obtain hx19₂ : s₂.gpr .x19 = st s₀ := by rw [g₂ _ (by decide) (by decide), h₁.x19]
  refine WP.seq (WP.mono (pad_ok (st := st s₀) hN hr (by omega_arith) hx19₂ r23₂ fun i hi => ?_)
    fun s₃ ⟨g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨stR s₀ w, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain g₃' : ∀ r, r ≠ .x9 → r ≠ .x11 → r ≠ .x12 → r ≠ .x23 → s₃.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h1 h4]
  obtain hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  obtain hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  obtain hsp₃ : s₃.sp = s₀.sp := by rw [sp₃, sp₂, h₁.sp]
  obtain hx19₃ : s₃.gpr .x19 = st s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x19]
  obtain hx20₃ : s₃.gpr .x20 = scr s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x20]
  obtain hm₃ : s₃.mem = writeBytes s₁.mem (st s₀ + BitVec.ofNat 64 (bufOff w + Blake2.bufLen w n))
      (List.replicate (blockBytes w - Blake2.bufLen w n) 0) := by rw [m₃, m₂]
  -- The call.
  obtain hbuf : Region.Sub ⟨st s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega_arith)
  obtain hscr : Region.Sub ⟨scr s₀, 56⟩ (scR s₀ W) := Region.sub_prefix (by have := hp.hW; have := hp.hW'; omega_arith)
  obtain hcall : CallOk (w := w) s₃ (st s₀) (scr s₀) (s₃.gpr .x19 + BitVec.ofNat 64 (bufOff w))
      (blockBytes w * (BitVec.setWidth 64 (1 : BitVec 16)).toNat) := by
    rw [show (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 1 from rfl, Nat.mul_one, hx19₃]
    refine ⟨hx19₃, hx20₃, (hp.st_scr.sub_left hstN).sub_right hscr,
      Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith), (hp.st_scr.sub_left hbuf).sub_right hscr, ?_, ?_⟩
    · rw [hrd₃, hwr₃, hp.rd, hp.wr, List.nil_append]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀ w, by simp, bufOff w, rfl, by simp only; omega_arith⟩
      · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega_arith⟩
      · exact ⟨scR s₀ W, by simp, 0, (BitVec.add_zero _).symm, by simp only; have := hp.hW; have := hp.hW'; omega_arith⟩
    · rw [hwr₃, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega_arith⟩
      · exact ⟨scR s₀ W, by simp, 0, (BitVec.add_zero _).symm, by simp only; have := hp.hW; have := hp.hW'; omega_arith⟩
  unfold compressLast
  refine WP.seq (compressWith_ok hf (bufArgs_ok (by omega_arith)) hcall fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_)
  obtain cs : ∀ r ∈ commonKeep, s₄.gpr r = s₁.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := commonKeep_ok r hr
    rw [cs₄ r h1 h2, g₃' r h3 h4 h5 h6]
  obtain hx19₄ : s₄.gpr .x19 = st s₀ := by rw [cs _ (by simp), h₁.x19]
  obtain hx21₄ : s₄.gpr .x21 = op s₀ := by rw [cs _ (by simp), h₁.x21]
  obtain hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, hwr₃]
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (σ := s₄) hN hN8 (fun a k h => ?_) (fun a k h => ?_) ?_)
    fun s₅ ⟨g₅, rd₅, wr₅, sp₅, m₅⟩ => ?_
  · rw [rd₄, hrd₃, hwr₄, hp.rd, hp.wr, List.nil_append]
    rw [hx19₄] at h
    exact ⟨stR s₀ w, by simp, by simp only [Region.Contains] at h ⊢; omega_arith⟩
  · rw [hwr₄, hp.wr]
    rw [hx21₄] at h
    exact ⟨outR s₀ w, by simp, h⟩
  · rw [hx19₄, hx21₄]; exact hp.st_out.sub_left hstN
  -- What the call and the stores wrote.
  obtain F₁ : Frame [stR s₀ w, outR s₀ w, ⟨scr s₀, 56⟩] s₁.mem s₅.mem := by
    obtain f₃ : Frame [stR s₀ w] s₁.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame _ _ _ (Offset.contains_base _ (by simp; omega_arith) (by omega_arith))
    obtain f₅ : Frame [outR s₀ w] s₄.mem s₅.mem := by
      rw [m₅, hx21₄]
      exact writeBytes_frame _ _ _ (contains_prefix _ (by simp [bytesAt]))
    refine ((f₃.mono (by simp)).trans (f₄.sub fun r hr => ?_)).trans (f₅.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, hstN⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  obtain hsv : Saved (scr s₀) s₀.gpr s₅.mem := Saved.frame hp (h₁.mem ▸ saveMem_saved _ _ _) F₁
  refine restore_ok (scr := scr s₀) (by rw [g₅ _ (by decide), cs _ (by simp), h₁.x20])
    (fun d hd₁ hd₂ => ⟨scR s₀ W, by simp [rd₅, wr₅, rd₄, wr₄, hrd₃, hwr₃, hp.wr],
      Offset.contains_base _ (by have := hp.hW; have := hp.hW'; omega_arith) (by have := hp.hW; have := hp.hW'; omega_arith)⟩) s₀.gpr hsv
    fun s₆ hs ho m₆ _ _ sp₆ => ⟨preserved_of hs fun r hr => ?_, by rw [sp₆, sp₅, sp₄, hsp₃], ?_⟩
  · rw [ho r (by simp only [untouched] at hr; simp only [saved, List.map_cons, List.map_nil]; decide +revert),
      g₅ r (notU hr .x9), cs r (by simp only [untouched] at hr; simp [hr]), h₁.keep r hr]
  · intro h0 d hR hlt hcnt
    obtain hnd : n = d.length := by rw [← hn, hcnt, toNat_ofNat_lt hlt]
    subst hnd
    obtain hx24₃ : (s₃.gpr .x24).toNat = d.length := by
      rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.x24, hn]
    rw [m₆, m₅, hx21₄, hx19₄, bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega_arith),
      bytesAt_state _ _ hP.w.symm, e₄, show (BitVec.setWidth 64 (1 : BitVec 16)).toNat = 0 + 1 from rfl,
      compressBlocks_succ, compressBlocks_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, BitVec.add_zero,
      hx24₃, hx19₃, show (((1 : BitVec 16).setWidth 64).setWidth 32 != 0) = true from rfl]
    refine final_eq P (by omega_arith) hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, writeBytes_before s₁.mem _ _ (by omega_arith : i < bufOff w + Blake2.bufLen w d.length)
          (by simp; omega_arith), hkeep i (by omega_arith)]
    · rw [pad_bytes hr (by omega_arith) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hkeep _ (by omega_arith)]

/-- The state `finalizeMain` starts in, inside the frame. -/
abbrev inner (s₀ : State) : State :=
  { s₀ with sp := s₀.sp - 16, mem := s₀.mem.write (s₀.sp - 16) 8 (s₀.gpr .x30) }

theorem correct (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hW : 104 ≤ W) (hW' : W ≤ 576)
    (hpre : (finalizeAArch64 P W).pre s₀) :
    WP isa (finalize P) s₀ fun s' => GprAbi s₀ s' ∧ (finalizeAArch64 P W).post s₀ s' := by
  obtain ⟨hp, hs⟩ := pre_of hW hW' hpre
  have hl := hP.len
  obtain hpi : Pre w W (inner s₀) := ⟨hp.hW, hp.hW', hp.rd, hp.wr, hp.st_out, hp.st_scr, hp.out_scr⟩
  refine WP.frameReg hs.sp16 (fun R hR => ?_)
    (WP.mono (correctMain hP hf hpi) fun s' ⟨hk, hsp, hpost⟩ mm u f => ?_)
    (by rw [fdepth_of_noFrames (noFrames_finalizeMain hf)]; decide)
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact hs.st
    · exact hs.out
    · exact hs.scr
  · refine ⟨⟨fun r hr => ?_, rfl⟩, fun h0 d hm hlt hc => ?_⟩
    · by_cases h30 : r = .x30
      · subst h30; simp [State.write]
      · simp only [State.write, h30, ite_false]
        exact hk r hr h30
    · -- The output lies apart from the frame, whose bytes the pop loses.
      refine Eq.trans (Proof.Blake2.bytesAt_congr fun i hi => lost_byte (R := outR s₀ w) f hs.out.symm hi) ?_
      exact hpost h0 d (repr_congr hP (fun i hi => write_frame_bytes (R := stR s₀ w) hs.st
        (by show bufOff w + blockBytes w < 2 ^ 64; omega_arith) hi) hm) hlt hc

end

end VG.Proof.Blake2.AArch64.Stream.Finalize

end

/-!
# Streaming BLAKE2 on AArch64: `Verified`

Correctness (from `Init`, `Update` and `Finalize`, with the compression
function of `Proof/Blake2/AArch64/Compress.lean`), constant time (from `CT`),
and a state satisfying each precondition, for BLAKE2b and BLAKE2s. `update`
and `finalize` save `x30` in 16 bytes below the stack pointer.
-/

namespace VG.Proof.Blake2.AArch64.Stream

open VG VG.AArch64 VG.Spec.Blake2

theorem calleeB : CalleeOk b (Impl.Blake2.AArch64.compress b) :=
  ⟨Proof.Blake2.AArch64.compressB_correct, Proof.Blake2.AArch64.compressB_noFrames⟩

theorem calleeS : CalleeOk s (Impl.Blake2.AArch64.compress s) :=
  ⟨Proof.Blake2.AArch64.compressS_correct, Proof.Blake2.AArch64.compressS_noFrames⟩

/-! ## States satisfying the preconditions -/

/-- `init` for `w`-bit words, with no key. -/
def initSat (w : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩]

/-- `update`, with no data, for `w`-bit words and `W` bytes of scratch space. -/
def updateSat (w : Nat) (W : Nat := 576) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x3000, W⟩]

/-- `finalize`, for `w`-bit words and `W` bytes of scratch space. -/
def finalizeSat (w : Nat) (W : Nat := 576) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩, ⟨0x3000, W⟩]

/-! ## BLAKE2b -/

theorem initB_correct (st : State) (hs : (initAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.init b) st t s' ∧ abiPreserved st s' ∧
      (initAArch64 b).post st s' :=
  WP.withPreservedV (Init.correct okB hs) (by lit_decide)

theorem updateB_correctW {W : Nat} (hW : 104 ≤ W) (hW' : W ≤ 576) (st : State)
    (hs : (updateAArch64 b W).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.update b) st t s' ∧ abiPreserved st s' ∧
      (updateAArch64 b W).post st s' :=
  WP.withPreservedV (Update.correct okB calleeB hW hW' hs) (by lit_decide)

theorem updateB_correct (st : State) (hs : (updateAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.update b) st t s' ∧ abiPreserved st s' ∧
      (updateAArch64 b).post st s' :=
  updateB_correctW (by decide) (by decide) st hs

theorem finalizeB_correctW {W : Nat} (hW : 104 ≤ W) (hW' : W ≤ 576) (st : State)
    (hs : (finalizeAArch64 b W).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.finalize b) st t s' ∧ abiPreserved st s' ∧
      (finalizeAArch64 b W).post st s' :=
  WP.withPreservedV (Finalize.correct okB calleeB hW hW' hs) (by lit_decide)

theorem finalizeB_correct (st : State) (hs : (finalizeAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.finalize b) st t s' ∧ abiPreserved st s' ∧
      (finalizeAArch64 b).post st s' :=
  finalizeB_correctW (by decide) (by decide) st hs

theorem initB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.init b)
      (Spec.Blake2.initBContract AArch64.abi) :=
  Verified.of_correct initB_correct initB_ct (by
    contract_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, Proof.Blake2.initAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs] [initSat]
      using initSat 64)

theorem updateB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.update b)
      (Proof.Blake2.updateBScratchContract AArch64.abi 16) :=
  Verified.of_correct updateB_correct updateB_ct (by
    sig_implies [Proof.Blake2.updateBScratchContract, Proof.Blake2.updateBScratchSig, Proof.Blake2.updateAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [updateSat] using updateSat 64)

theorem finalizeB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.finalize b)
      (Proof.Blake2.finalizeBScratchContract AArch64.abi 16) :=
  Verified.of_correct finalizeB_correct finalizeB_ct (by
    sig_implies [Proof.Blake2.finalizeBScratchContract, Proof.Blake2.finalizeBScratchSig,
      Proof.Blake2.finalizeAArch64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi,
      AArch64.argRegs]
      [finalizeSat] using finalizeSat 64)

/-! ## BLAKE2s -/

theorem initS_correct (st : State) (hs : (initAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.init s) st t s' ∧ abiPreserved st s' ∧
      (initAArch64 s).post st s' :=
  WP.withPreservedV (Init.correct okS hs) (by lit_decide)

theorem updateS_correctW {W : Nat} (hW : 104 ≤ W) (hW' : W ≤ 576) (st : State)
    (hs : (updateAArch64 s W).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.update s) st t s' ∧ abiPreserved st s' ∧
      (updateAArch64 s W).post st s' :=
  WP.withPreservedV (Update.correct okS calleeS hW hW' hs) (by lit_decide)

theorem updateS_correct (st : State) (hs : (updateAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.update s) st t s' ∧ abiPreserved st s' ∧
      (updateAArch64 s).post st s' :=
  updateS_correctW (by decide) (by decide) st hs

theorem finalizeS_correctW {W : Nat} (hW : 104 ≤ W) (hW' : W ≤ 576) (st : State)
    (hs : (finalizeAArch64 s W).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.finalize s) st t s' ∧ abiPreserved st s' ∧
      (finalizeAArch64 s W).post st s' :=
  WP.withPreservedV (Finalize.correct okS calleeS hW hW' hs) (by lit_decide)

theorem finalizeS_correct (st : State) (hs : (finalizeAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.finalize s) st t s' ∧ abiPreserved st s' ∧
      (finalizeAArch64 s).post st s' :=
  finalizeS_correctW (by decide) (by decide) st hs

theorem initS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.init s)
      (Spec.Blake2.initSContract AArch64.abi) :=
  Verified.of_correct initS_correct initS_ct (by
    contract_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, Proof.Blake2.initAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs] [initSat]
      using initSat 32)

theorem updateS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.update s)
      (Proof.Blake2.updateSScratchContract AArch64.abi 16) :=
  Verified.of_correct updateS_correct updateS_ct (by
    sig_implies [Proof.Blake2.updateSScratchContract, Proof.Blake2.updateSScratchSig, Proof.Blake2.updateAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [updateSat] using updateSat 32)

theorem finalizeS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.finalize s)
      (Proof.Blake2.finalizeSScratchContract AArch64.abi 16) :=
  Verified.of_correct finalizeS_correct finalizeS_ct (by
    sig_implies [Proof.Blake2.finalizeSScratchContract, Proof.Blake2.finalizeSScratchSig,
      Proof.Blake2.finalizeAArch64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi,
      AArch64.argRegs]
      [finalizeSat] using finalizeSat 32)

/-! ## `update` and `finalize` with their working space in a frame of their own

The theorems above are of the streaming functions with their working space
as an argument (`update_scratch`, `finalize_scratch`); `update` and
`finalize` run them in a frame that allocates it (`Verified.stackScratch`).
-/

/-- `vg_blake2{b,s}_update_scratch` and `_finalize_scratch` with `scratch: *mut [u64; n]`:
`Proof.Blake2.updateBScratchSig` and the rest with room for `n` words of
scratch space rather than 72. The code uses 104 bytes of it (the compression
function's 56 and the 48 that hold our caller's `x19`–`x24`), so `update` and
`finalize` allocate 14 words, a multiple of 16 bytes. -/
def updateBScratchSigN (n : Nat) : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 n)]

def updateBScratchContractN {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (updateBScratchSigN n).contract A
    (post := fun state count data len _scratch => updateBPost A.ptrBits state count data len)
    (stack := stack)

def finalizeBScratchSigN (n : Nat) : Sig where
  params := [("state", .array true .u8 192), ("count", .int .u64 true),
    ("out", .array true .u8 64), ("scratch", .array true .u64 n)]

def finalizeBScratchContractN {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (finalizeBScratchSigN n).contract A
    (post := fun state count out _scratch => finalizeBPost A.ptrBits state count out)
    (stack := stack)

def updateSScratchSigN (n : Nat) : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("data", .slice false .u8 "len"), ("scratch", .array true .u64 n)]

def updateSScratchContractN {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (updateSScratchSigN n).contract A
    (post := fun state count data len _scratch => updateSPost A.ptrBits state count data len)
    (stack := stack)

def finalizeSScratchSigN (n : Nat) : Sig where
  params := [("state", .array true .u8 96), ("count", .int .u64 true),
    ("out", .array true .u8 32), ("scratch", .array true .u64 n)]

def finalizeSScratchContractN {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (finalizeSScratchSigN n).contract A
    (post := fun state count out _scratch => finalizeSPost A.ptrBits state count out)
    (stack := stack)

theorem updateB_verified14 :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.update b)
      (updateBScratchContractN AArch64.abi 14 16) :=
  Verified.of_correct (updateB_correctW (W := 112) (by decide) (by decide)) updateB_ct (by
    sig_implies [updateBScratchContractN, updateBScratchSigN, Proof.Blake2.updateAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [updateSat] using updateSat 64 112)

theorem updateB_framed : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 (Impl.Blake2.AArch64.Stream.update b))
    (Spec.Blake2.updateBContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 16) (bytes := 112)
    updateB_verified14 (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Blake2.updateBPost_out _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalizeB_verified14 :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.finalize b)
      (finalizeBScratchContractN AArch64.abi 14 16) :=
  Verified.of_correct (finalizeB_correctW (W := 112) (by decide) (by decide)) finalizeB_ct (by
    sig_implies [finalizeBScratchContractN, finalizeBScratchSigN, Proof.Blake2.finalizeAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [finalizeSat] using finalizeSat 64 112)

theorem finalizeB_framed : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x3 (Impl.Blake2.AArch64.Stream.finalize b))
    (Spec.Blake2.finalizeBContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 16) (bytes := 112)
    finalizeB_verified14 (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Blake2.finalizeBPost_out _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem updateS_verified14 :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.update s)
      (updateSScratchContractN AArch64.abi 14 16) :=
  Verified.of_correct (updateS_correctW (W := 112) (by decide) (by decide)) updateS_ct (by
    sig_implies [updateSScratchContractN, updateSScratchSigN, Proof.Blake2.updateAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [updateSat] using updateSat 32 112)

theorem updateS_framed : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x4 (Impl.Blake2.AArch64.Stream.update s))
    (Spec.Blake2.updateSContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 16) (bytes := 112)
    updateS_verified14 (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Blake2.updateSPost_out _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem finalizeS_verified14 :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.finalize s)
      (finalizeSScratchContractN AArch64.abi 14 16) :=
  Verified.of_correct (finalizeS_correctW (W := 112) (by decide) (by decide)) finalizeS_ct (by
    sig_implies [finalizeSScratchContractN, finalizeSScratchSigN, Proof.Blake2.finalizeAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [finalizeSat] using finalizeSat 32 112)

theorem finalizeS_framed : Verified AArch64.target
    (Impl.StackScratch.AArch64.withStackScratch 112 .x3 (Impl.Blake2.AArch64.Stream.finalize s))
    (Spec.Blake2.finalizeSContract AArch64.abi (16 + 112)) :=
  AArch64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 14) (stack := 16) (bytes := 112)
    finalizeS_verified14 (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.Blake2.finalizeSPost_out _ vs m m₁ m₂ r hl)
    (AArch64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## Returning without secret residue

BLAKE2's `init` leaves a byte of the key or a word of its parameters in
`x9`: the cleared `init` zeroes it before returning (`CT.lean` proves it then
leaves nothing secret). Argon2 calls BLAKE2b's cleared `init` by name, with
its code, its correctness (`initB_post`) and its constant time. -/

/-- `init`'s postcondition looks at the final state only through its memory. -/
theorem initB_post {s₀ u u' : State} (h : (Proof.Blake2.initAArch64 b).post s₀ u)
    (hm : u'.mem = u.mem) (_ : u'.gpr .x0 = u.gpr .x0) : (Proof.Blake2.initAArch64 b).post s₀ u' := by
  show Spec.Blake2.Repr _ _ u'.mem _ _
  rw [hm]
  exact h

theorem initBCleared_verified :
    Verified AArch64.target
      (Impl.Residue.AArch64.withClears [.x9] [] none (Impl.Blake2.AArch64.Stream.init b))
      (Spec.Blake2.initBContract AArch64.abi) :=
  Clears.Verified.withClears initB_verified (by decide)

theorem initSCleared_verified :
    Verified AArch64.target
      (Impl.Residue.AArch64.withClears [.x9] [] none (Impl.Blake2.AArch64.Stream.init s))
      (Spec.Blake2.initSContract AArch64.abi) :=
  Clears.Verified.withClears initS_verified (by decide)

end VG.Proof.Blake2.AArch64.Stream
