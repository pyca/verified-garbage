module

public import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Common
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Omega
/-!
# Streaming BLAKE2 on RISC-V: `finalize`

The structure of the PPC64LE proof (`VG.Proof.Blake2.PPC64LE.Stream.Finalize`):
`finalize` saves the callee-saved registers (`prologue_ok`), computes the
number of buffered bytes (`bufLen_ok`), zeroes the rest of the buffer
(`pad_ok`), compresses it as the last block (`compressWith_ok`), copies the
hash value out a byte at a time (`output_ok`) and restores the registers
(`restore_ok`); `correctMain` for the code with its scratch space in `a3`
(`finalize_scratch`), and `correctFramed` for it in a frame on the stack
(`finalize`).
-/

@[expose] public section

namespace VG.Proof.Blake2.RISCV64.Stream.Finalize

open VG VG.RISCV64 VG.Spec.Blake2
open VG.Impl.Blake2.RISCV64.Stream (N B mov zeroLoop pad compressLast output finalizeMain finalize
  finalizeScratch saved save restore frameBytes)
open VG.Impl.Blake2.RISCV64 (compress)
open VG.Proof.Blake2 (finalizeRISCV64 finalizeFramedRISCV64 finalizePost bufOff final_eq stateAt_congr
  bytesAt_congr bytesAt_add bytesAt_state bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.RISCV64.Wp (Upd Mupd WP.cons wp_mv wp_li wp_sub wp_lbu wp_sb)
open VG.RISCV64.Align (pad_lt align_al)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_frame writeBytes_snoc writeBytes_before)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev op : Addr := s₀.gpr .a2
abbrev scr : Addr := s₀.gpr .a3
/-- The scratch space, rounded up to a multiple of 8. -/
abbrev sb : Addr := rnd (scr s₀)
abbrev stR (w : Nat) : Region := ⟨st s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨op s₀, bufOff w⟩
abbrev scR : Region := ⟨scr s₀, 576⟩

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  out_scr : (outR s₀ w).Disjoint (scR s₀)

theorem pre_of {w : Nat} {P : Params w} {s₀ : State} (h : (finalizeRISCV64 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

/-- A range of the rounded scratch space within the scratch space. -/
theorem sb_sub (s₀ : State) {d n : Nat} (h : d + n ≤ 568) :
    Region.Sub ⟨sb s₀ + BitVec.ofNat 64 d, n⟩ (scR s₀) := by
  rw [show sb s₀ + BitVec.ofNat 64 d = scr s₀ + BitVec.ofNat 64 (VG.RISCV64.Align.pad (scr s₀) + d) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  have := pad_lt (scr s₀)
  exact Offset.sub_base _ (by omega)

theorem sb_sub0 (s₀ : State) {n : Nat} (h : n ≤ 568) : Region.Sub ⟨sb s₀, n⟩ (scR s₀) := by
  have := sb_sub s₀ (d := 0) (n := n) (by omega)
  simpa using this

theorem sb_contains (s₀ : State) {d n : Nat} (h : d + n ≤ 568) :
    (scR s₀).Contains (sb s₀ + BitVec.ofNat 64 d) n := by
  rw [show sb s₀ + BitVec.ofNat 64 d = scr s₀ + BitVec.ofNat 64 (VG.RISCV64.Align.pad (scr s₀) + d) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]
  have := pad_lt (scr s₀)
  exact Offset.contains_base _ (by omega) (by omega)

/-- The saved registers are outside everything written after the saves. -/
theorem Saved.frame {w : Nat} {s₀ : State} (hp : Pre w s₀) {g : Reg → BitVec 64} {m m' : Mem}
    (h : Saved (sb s₀) g m) (hf : Frame [stR s₀ w, outR s₀ w, ⟨sb s₀, 512⟩] m m') :
    Saved (sb s₀) g m' :=
  Spill.Saved.frame h hf fun p hp' r hr => by
    have hoff := saved_off p hp'
    have hsub : Region.Sub ⟨sb s₀ + BitVec.ofNat 64 p.2, 8⟩ (scR s₀) := sb_sub s₀ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.st_scr.symm.sub_left hsub
    · exact hp.out_scr.symm.sub_left hsub
    · exact Offset.disjoint_base _ (by omega) (by omega)

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  s7 : s.gpr .s7 = st s₀
  s8 : s.gpr .s8 = sb s₀
  s9 : s.gpr .s9 = op s₀
  s11 : s.gpr .s11 = s₀.gpr .a1
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  mem : s.mem = saveMem s₀.mem (sb s₀) s₀.gpr

theorem prologue_ok {w : Nat} {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block (save .a3 ++ ([mov .s7 .a0, mov .s8 .t0, mov .s9 .a2, mov .s11 .a1] : List Instr)))
      s₀ (Start s₀) := by
  refine save_ok (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hp.wr], sb_contains s₀ (by omega)⟩)
    fun s₁ h₀ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      g₁ _ (by decide)]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), h₀]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide)]
  · rw [u₅.other _ (notU hr .s11), u₄.other _ (notU hr .s9), u₃.other _ (notU hr .s8),
      u₂.other _ (notU hr .s7), g₁ _ (notU hr .t0)]
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]

/-! ## Zeroing the rest of the buffer -/

section
variable {w : Nat}

/-- Zeroing the buffer from byte `r` (in `a7`) on. -/
theorem pad_ok {s : State} {st : Addr} {r : Nat} (hN : bufOff w ≤ 64) (hr : r ≤ blockBytes w)
    (hbb : blockBytes w < 2048) (hs7 : s.gpr .s7 = st) (ha7 : s.gpr .a7 = BitVec.ofNat 64 r)
    (hdst : ∀ i < blockBytes w - r,
      InRegions s.wr (st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (pad (w := w)) s fun s' =>
      (∀ x, x ≠ .t1 → x ≠ .t3 → x ≠ .t2 → x ≠ .a7 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (st + BitVec.ofNat 64 (bufOff w + r))
        (List.replicate (blockBytes w - r) 0) := by
  unfold pad
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => wp_li (by rw [B_eq]; omega) fun s₂ u₂ =>
    wp_sub fun s₃ u₃ => WP.block_nil ?_)
  have g : ∀ x, x ≠ .t1 → x ≠ .t3 → s₃.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₃.other x h2, u₂.other x h2, u₁.other x h1]
  have h11 : s₃.gpr .t3 = BitVec.ofNat 64 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.other .a7 (by decide), u₂.gpr, u₁.other .a7 (by decide), ha7,
      B_eq, sub_ofNat hr]
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have hsp₃ : s₃.sp = s.sp := by rw [u₃.sp, u₂.sp, u₁.sp]
  refine WP.ite _ (zero_iff s₃ h11 (by omega)) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨fun x h1 h2 _ _ => g x h1 h2, hrd₃, hwr₃, hsp₃, ?_⟩
    rw [hb, List.replicate_zero, writeBytes_nil, hm₃]
  · simp only [decide_eq_false_iff_not] at hb
    refine zeroLoop_ok (st := st) (r := r) hN (by omega) (by omega)
      (by rw [g _ (by decide) (by decide), hs7])
      (by rw [g _ (by decide) (by decide), ha7]) h11
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

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : bytesAt (writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- The buffer after zeroing it from byte `r` on. -/
theorem pad_bytes {m m' : Mem} {st : Addr} {N r bb : Nat} (hr : r ≤ bb) (hlt : N + bb < 2 ^ 64)
    (hm : m' = writeBytes m (st + BitVec.ofNat 64 (N + r)) (List.replicate (bb - r) 0)) :
    bytesAt m' (st + BitVec.ofNat 64 N) bb =
      bytesAt m (st + BitVec.ofNat 64 N) r ++ List.replicate (bb - r) 0 := by
  conv => lhs; rw [show bb = r + (bb - r) by omega]
  rw [bytesAt_add, Offset.add_ofNat_add_ofNat]
  congr 1
  · refine bytesAt_congr fun i hi => ?_
    rw [hm, Offset.add_ofNat_add_ofNat,
      writeBytes_before m st _ (by omega : N + i < N + r) (by simp; omega)]
  · rw [hm]; exact bytesAt_writeBytes_self _ _ (by simp) (by omega)

/-! ## Copying the hash value out -/

section
variable {w : Nat}

/-- After copying `k` bytes. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .t1 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
    s.mem = writeBytes σ.mem (σ.gpr .s9) (bytesAt σ.mem (σ.gpr .s7) k)

theorem bytesAt_succ (m : Mem) (p : Addr) (k : Nat) :
    bytesAt m p (k + 1) = bytesAt m p k ++ [m (p + BitVec.ofNat 64 k)] := by
  simp [bytesAt, List.range_succ]

theorem output_ok {σ : State} (hN : bufOff w ≤ 64)
    (hin : ∀ a n, (⟨σ.gpr .s7, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨σ.gpr .s9, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨σ.gpr .s7, bufOff w⟩ ⟨σ.gpr .s9, bufOff w⟩) :
    WP isa (.block (output (w := w))) σ fun s =>
      (∀ r, r ≠ .t1 → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧ s.sp = σ.sp ∧
      s.mem = writeBytes σ.mem (σ.gpr .s9) (bytesAt σ.mem (σ.gpr .s7) (bufOff w)) := by
  unfold output
  rw [N_eq]
  refine wp_range_flatMap (M := isa) (OInv σ) (fun k s hk ⟨hg, hrd, hwr, hsp, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, rfl, by simp [bytesAt, writeBytes_nil]⟩
  have hl : (bytesAt σ.mem (σ.gpr .s7) k).length = k := by simp [bytesAt]
  refine wp_lbu (a := σ.gpr .s7 + BitVec.ofNat 64 k) (by omega)
    (by rw [hg _ (by decide)]) (by rw [hrd, hwr]; exact hin _ _ (Offset.contains_base _ (by omega) (by omega)))
    fun s₁ u₁ => wp_sb (a := σ.gpr .s9 + BitVec.ofNat 64 k) (by omega) ?_ ?_ fun s₂ g₂ =>
      WP.block_nil ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, hg r hr], by rw [g₂.rd, u₁.rd, hrd],
        by rw [g₂.wr, u₁.wr, hwr], by rw [g₂.sp, u₁.sp, hsp], ?_⟩
  · rw [u₁.other _ (by decide), hg _ (by decide)]
  · rw [u₁.wr, hwr]; exact hout _ _ (Offset.contains_base _ (by omega) (by omega))
  · have hv : s.mem (σ.gpr .s7 + BitVec.ofNat 64 k) = σ.mem (σ.gpr .s7 + BitVec.ofNat 64 k) := by
      rw [hm]
      exact (writeBytes_frame (R := ⟨σ.gpr .s9, bufOff w⟩) _ _ _
        (contains_prefix _ (by rw [hl]; omega))).bytes (R := ⟨σ.gpr .s7, bufOff w⟩)
        (by simpa using hd) (by show bufOff w ≤ 2 ^ 64; omega) hk
    rw [g₂.mem, u₁.gpr, u₁.mem, hv, hm, setWidth_byte, bytesAt_succ,
      writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl]

end

/-! ## The whole function -/

section
variable {w : Nat} {P : Params w}

theorem noFrames_finalizeMain (hf : CalleeOk P (compress P)) (sc : Reg) :
    (finalizeMain P sc).noFrames = true := by
  simp only [finalizeMain, pad, compressLast, Impl.Blake2.RISCV64.Stream.compressWith, zeroLoop,
    Impl.Blake2.RISCV64.Stream.bufLen, Code.noFrames, hf.noFrames, Bool.and_self]

/-- The registers kept from the prologue to the epilogue. -/
abbrev commonKeep : List Reg :=
  [.s7, .s8, .s9, .s11, .s0, .s1, .s2, .s3, .s4, .s5, .s6]

theorem commonKeep_ok : ∀ r ∈ commonKeep,
    r ∈ preserved ∧ r ≠ .t1 ∧ r ≠ .t3 ∧ r ≠ .t2 ∧ r ≠ .a7 := by decide

/-- The epilogue's postcondition. -/
def Post (P : Params w) (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧ finalizePost P s₀ s'

/-- `finalize`, with its scratch space in `a3`. -/
theorem correctMain (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State} (hp : Pre w s₀) :
    WP isa (finalizeMain P .a3) s₀ (Post P s₀) := by
  have hl := hP.len
  have hN := hP.N64
  have hbb := hP.bb
  have hstN : Region.Sub ⟨st s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega)
  have hsave_st : ∀ r ∈ [(⟨sb s₀ + BitVec.ofNat 64 512, 48⟩ : Region)], (stR s₀ w).Disjoint r := by
    simpa using hp.st_scr.sub_right (sb_sub s₀ (by decide))
  unfold finalizeMain
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  have hkeep : ∀ i < bufOff w + blockBytes w,
      s₁.mem (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i) := fun i hi => by
    rw [h₁.mem]; exact (saveMem_frame _ _ _).bytes (R := stR s₀ w) hsave_st (by simp only; omega) hi
  refine WP.seq (WP.mono (bufLen_ok hP) fun s₂ ⟨r23₂, g₂, m₂, rd₂, wr₂, sp₂⟩ => ?_)
  rw [h₁.s11] at r23₂
  generalize hn : (s₀.gpr .a1).toNat = n at r23₂
  have hr : Blake2.bufLen w n ≤ blockBytes w := bufLen_le (by omega) n
  have hx19₂ : s₂.gpr .s7 = st s₀ := by rw [g₂ _ (by decide), h₁.s7]
  refine WP.seq (WP.mono (pad_ok (st := st s₀) hN hr (by omega) hx19₂ r23₂ fun i hi => ?_)
    fun s₃ ⟨g₃, rd₃, wr₃, sp₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, Offset.add_ofNat_add_ofNat]
    exact ⟨stR s₀ w, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have g₃' : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .t2 → r ≠ .a7 → s₃.gpr r = s₁.gpr r := fun r h1 h2 h3 h4 => by
    rw [g₃ r h1 h2 h3 h4, g₂ r h4]
  have hrd₃ : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  have hwr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  have hsp₃ : s₃.sp = s₀.sp := by rw [sp₃, sp₂, h₁.sp]
  have hx19₃ : s₃.gpr .s7 = st s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.s7]
  have hx20₃ : s₃.gpr .s8 = sb s₀ := by rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.s8]
  have hm₃ : s₃.mem = writeBytes s₁.mem (st s₀ + BitVec.ofNat 64 (bufOff w + Blake2.bufLen w n))
      (List.replicate (blockBytes w - Blake2.bufLen w n) 0) := by rw [m₃, m₂]
  -- The call.
  have hbuf : Region.Sub ⟨st s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega)
  have hscr : Region.Sub ⟨sb s₀, 512⟩ (scR s₀) := sb_sub0 s₀ (by decide)
  have hcall : CallOk (w := w) s₃ (st s₀) (sb s₀) (s₃.gpr .s7 + BitVec.ofNat 64 (bufOff w))
      (blockBytes w * (BitVec.ofNat 64 1).toNat) := by
    rw [show (BitVec.ofNat 64 1).toNat = 1 from rfl, Nat.mul_one, hx19₃]
    refine ⟨hx19₃, hx20₃, (hp.st_scr.sub_left hstN).sub_right hscr,
      Offset.disjoint_base _ (Nat.le_refl _) (by omega), (hp.st_scr.sub_left hbuf).sub_right hscr, ?_, ?_⟩
    · rw [hrd₃, hwr₃, hp.rd, hp.wr, List.nil_append]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀ w, by simp, bufOff w, rfl, by simp only; omega⟩
      · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
      · exact ⟨scR s₀, by simp, VG.RISCV64.Align.pad (scr s₀), rfl,
          by have := pad_lt (scr s₀); simp only; omega⟩
    · rw [hwr₃, hp.wr]
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀ w, by simp, 0, (BitVec.add_zero _).symm, by simp only; omega⟩
      · exact ⟨scR s₀, by simp, VG.RISCV64.Align.pad (scr s₀), rfl,
          by have := pad_lt (scr s₀); simp only; omega⟩
  unfold compressLast
  refine WP.seq (compressWith_ok hf (bufArgs_ok hP (by decide)) hcall fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_)
  have cs : ∀ r ∈ commonKeep, s₄.gpr r = s₁.gpr r := fun r hr => by
    obtain ⟨h1, h3, h4, h5, h6⟩ := commonKeep_ok r hr
    rw [cs₄ r h1, g₃' r h3 h4 h5 h6]
  have hx19₄ : s₄.gpr .s7 = st s₀ := by rw [cs _ (by simp), h₁.s7]
  have hx21₄ : s₄.gpr .s9 = op s₀ := by rw [cs _ (by simp), h₁.s9]
  have hwr₄ : s₄.wr = s₀.wr := by rw [wr₄, hwr₃]
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (σ := s₄) hN (fun a k h => ?_) (fun a k h => ?_) ?_)
    fun s₅ ⟨g₅, rd₅, wr₅, sp₅, m₅⟩ => ?_
  · rw [rd₄, hrd₃, hwr₄, hp.rd, hp.wr, List.nil_append]
    rw [hx19₄] at h
    exact ⟨stR s₀ w, by simp, by simp only [Region.Contains] at h ⊢; omega⟩
  · rw [hwr₄, hp.wr]
    rw [hx21₄] at h
    exact ⟨outR s₀ w, by simp, h⟩
  · rw [hx19₄, hx21₄]; exact hp.st_out.sub_left hstN
  -- What the call and the stores wrote.
  have F₁ : Frame [stR s₀ w, outR s₀ w, ⟨sb s₀, 512⟩] s₁.mem s₅.mem := by
    have f₃ : Frame [stR s₀ w] s₁.mem s₃.mem := by
      rw [hm₃]; exact writeBytes_frame _ _ _ (Offset.contains_base _ (by simp; omega) (by omega))
    have f₅ : Frame [outR s₀ w] s₄.mem s₅.mem := by
      rw [m₅, hx21₄]
      exact writeBytes_frame _ _ _ (contains_prefix _ (by simp [bytesAt]))
    refine ((f₃.mono (by simp)).trans (f₄.sub fun r hr => ?_)).trans (f₅.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, hstN⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have hsv : Saved (sb s₀) s₀.gpr s₅.mem := Saved.frame hp (h₁.mem ▸ saveMem_saved _ _ _) F₁
  refine restore_ok (scr := sb s₀) (by rw [g₅ _ (by decide), cs _ (by simp), h₁.s8]) (align_al _)
    (fun d hd₁ hd₂ => ⟨scR s₀, by simp [rd₅, wr₅, rd₄, wr₄, hrd₃, hwr₃, hp.wr],
      sb_contains s₀ (by omega)⟩) s₀.gpr hsv
    fun s₆ hs ho m₆ _ _ sp₆ => ⟨⟨preserved_of hs fun r hr => ?_, by rw [sp₆, sp₅, sp₄, hsp₃],
      hs (.ra, 512) (by decide)⟩, ?_⟩
  · rw [ho r (by revert r; decide), g₅ r (notU hr .t1), cs r (by revert r; decide), h₁.keep r hr]
  · intro h0 d hR hlt hcnt
    have hnd : n = d.length := by rw [← hn, hcnt, toNat_ofNat_lt hlt]
    subst hnd
    have hx24₃ : (s₃.gpr .s11).toNat = d.length := by
      rw [g₃' _ (by decide) (by decide) (by decide) (by decide), h₁.s11, hn]
    rw [m₆, m₅, hx21₄, hx19₄, bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega),
      bytesAt_state _ _ hP.w.symm, e₄, show (BitVec.ofNat 64 1).toNat = 0 + 1 from rfl,
      compressBlocks_succ, compressBlocks_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, BitVec.add_zero,
      hx24₃, hx19₃, show ((BitVec.ofNat 64 1).setWidth 32 != 0) = true from rfl]
    refine final_eq P (by omega) hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, writeBytes_before s₁.mem _ _ (by omega : i < bufOff w + Blake2.bufLen w d.length)
          (by simp; omega), hkeep i (by omega)]
    · rw [pad_bytes hr (by omega) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hkeep _ (by omega)]

/-- `finalize_scratch`. -/
theorem correct (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (finalizeRISCV64 P).pre s₀) :
    WP isa (finalizeScratch P) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeRISCV64 P).post s₀ s' :=
  correctMain hP hf (pre_of hpre)

/-- `finalize`: `finalize_scratch`, with its scratch space in a frame. -/
theorem correctFramed (hP : Ok P) (hf : CalleeOk P (compress P)) {s₀ : State}
    (hpre : (finalizeFramedRISCV64 P).pre s₀) :
    WP isa (finalize P) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeFramedRISCV64 P).post s₀ s' := by
  obtain ⟨hrd, hwr, hso, -, hsp, hks, hko⟩ := hpre
  refine WP.alloc (by decide) hsp ?_
  refine WP.seq (Wp.wp_addSp (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  let F : Region := ⟨s₀.sp - BitVec.ofNat 64 576, 576⟩
  have ha3 : s₁.gpr .a3 = s₀.sp - BitVec.ofNat 64 576 := by
    rw [u₁.gpr]; simp [allocd, frameBytes]
  have g₁ : ∀ r, r ≠ .a3 → s₁.gpr r = s₀.gpr r := fun r hr => u₁.other r hr
  have hrd₁ : s₁.rd = s₀.rd := u₁.rd
  have hwr₁ : s₁.wr = F :: s₀.wr := u₁.wr
  let σ := s₁.withRegions [] [stR s₀ w, outR s₀ w, F]
  have hpσ : Pre w σ := by
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩
    · show [stR s₀ w, outR s₀ w, F] = [stR σ w, outR σ w, scR σ]
      simp only [stR, st, outR, op, scR, scr, σ, State.withRegions_gpr, g₁ .a0 (by decide),
        g₁ .a2 (by decide), ha3, F]
    · simp only [stR, outR, st, op, σ, State.withRegions_gpr, g₁ .a0 (by decide), g₁ .a2 (by decide)]
      exact hso
    · simp only [stR, scR, scr, st, σ, State.withRegions_gpr, g₁ .a0 (by decide), ha3]
      exact hks.symm
    · simp only [outR, scR, scr, op, σ, State.withRegions_gpr, g₁ .a2 (by decide), ha3]
      exact hko.symm
  refine WP.narrow (correctMain hP hf hpσ) ?_ ?_ (fun s' hrd' hwr' hsp' _ hpost => ?_)
    (noFrames_finalizeMain hf .a3)
  · rw [hrd₁, hwr₁, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨F, by simp, 0, by simp, by simp⟩
  · rw [hwr₁, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨outR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨F, by simp, 0, by simp, by simp⟩
  obtain ⟨⟨hpres, hsp₂, hra⟩, hpost⟩ := hpost
  simp only [State.withRegions_gpr, State.withRegions_sp] at hpres hsp₂ hra
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun h0 d hr hl hc => ?_⟩
  · show s'.gpr r = s₀.gpr r
    rw [hpres r hr, g₁ r (by revert r; decide)]
  · show s'.sp + BitVec.ofNat 64 frameBytes = s₀.sp
    rw [hsp₂, u₁.sp]; exact BitVec.sub_add_cancel _ _
  · show s'.gpr .ra = s₀.gpr .ra
    rw [hra, g₁ _ (by decide)]
  · have := hpost h0 d
    simp only [State.withRegions_mem, State.withRegions_gpr, u₁.mem,
      g₁ .a0 (by decide), g₁ .a1 (by decide), g₁ .a2 (by decide)] at this
    simp only [freed]
    exact this hr hl hc

end

end VG.Proof.Blake2.RISCV64.Stream.Finalize
