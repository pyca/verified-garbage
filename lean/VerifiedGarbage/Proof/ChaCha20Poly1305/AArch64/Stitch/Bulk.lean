module

import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Phase
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Loop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop

/-! ### `ChaCha20Poly1305.AArch64.Stitch.Body`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.AArch64.Stitch.Chunk`, which only this module used -/

section

/-!
# ChaCha20 and Poly1305 together (AArch64): a chunk

`Stitch.chunkWith`: the eight-block kernel's chunk (`Mixed8.chunk_ok`), with
its two phases replaced by `Stitch.phaseWith`, which also absorb into the
accumulator the bytes from `B₀` and from `B₁` (`chunkWith_ok`); for
`Stitch.chunk`, the 512 bytes from `B` (`chunk_ok`).

The kernel's proofs describe each stage relative to the state `s₀` at the
start of the chunk, and say that the registers they do not use keep their
values from `s₀`. The phases change the accumulator's registers (`accRegs`),
which the kernel does not use, so after a phase the kernel's stages are
applied relative to `rebase s₀ u`: `s₀` with the accumulator's registers of
`u`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP Prepared Second Spilled2 FinishedFrom ChunkedFrom SrcOK source sr
  br dr lowBuf scalarBuf prepare_ok second_ok spill2_ok finishFrom_ok lastFrom_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

/-- The accumulator's registers, apart from the pointer `x20` and `x27`, which
each phase sets back to the chunk's source (`Stitch.back`). -/
abbrev accRegs : List Reg := [.x21, .x22, .x23, .x24, .x25, .x28, .x30]

/-- `s₀` with the accumulator's registers of `u`. -/
def rebase (s₀ u : State) : State :=
  { s₀ with gpr := fun r => if r ∈ accRegs then u.gpr r else s₀.gpr r }

theorem rebase_of {s₀ u : State} {r : Reg} (h : r ∉ accRegs) : (rebase s₀ u).gpr r = s₀.gpr r := by
  simp only [rebase, h, ite_false]

theorem rebase_acc {s₀ u : State} {r : Reg} (h : r ∈ accRegs) : (rebase s₀ u).gpr r = u.gpr r := by
  simp only [rebase, h, ite_true]

@[simp] theorem rebase_mem (s₀ u : State) : (rebase s₀ u).mem = s₀.mem := rfl
@[simp] theorem rebase_rd (s₀ u : State) : (rebase s₀ u).rd = s₀.rd := rfl
@[simp] theorem rebase_wr (s₀ u : State) : (rebase s₀ u).wr = s₀.wr := rfl
@[simp] theorem rebase_sp (s₀ u : State) : (rebase s₀ u).sp = s₀.sp := rfl

theorem acc_preserved : ∀ r ∈ accRegs, r ∈ preserved ∧ r ≠ .x19 ∧ r ≠ .x26 ∧ r ≠ .x20 := by
  decide

theorem rebase_cp {s₀ : State} (u : State) (hp : CP s₀) : CP (rebase s₀ u) := by
  obtain e0 : (rebase s₀ u).gpr .x0 = s₀.gpr .x0 := rebase_of (by decide)
  obtain e1 : (rebase s₀ u).gpr .x1 = s₀.gpr .x1 := rebase_of (by decide)
  obtain e3 : (rebase s₀ u).gpr .x3 = s₀.gpr .x3 := rebase_of (by decide)
  obtain e20 : (rebase s₀ u).gpr .x20 = s₀.gpr .x20 := rebase_of (by decide)
  obtain ⟨h20, hrd, hvr, hc, hb, hd, h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.sr, VG.Proof.ChaCha20.AArch64.Mixed8.br,
      VG.Proof.ChaCha20.AArch64.Mixed8.dr, e0, e1, e3, e20] <;>
    first | exact h20 | exact hrd | exact hvr | exact hc | exact hb | exact hd | exact h1 | exact h2 | exact h3

theorem source_rebase (s₀ u : State) : source (rebase s₀ u) = source s₀ := by
  simp only [source, rebase_of (show Reg.x0 ∉ accRegs by decide)]
  rfl

/-- Where the chunk's data starts, relative to the bytes it absorbs from `B`. -/
abbrev dataOf (enc : Bool) (B : Addr) : Addr := B + BitVec.ofNat 64 (if enc then 512 else 0)

theorem start_ok (enc : Bool) (half : Nat) (hh : half ≤ 1) (B : Addr) (s : State)
    (hx : enc = true → s.gpr .x26 = dataOf true B) (hx27 : enc = false → s.gpr .x27 = B) :
    exec (start enc half) s = some (s.write .x .x20 (B + BitVec.ofNat 64 (256 * half))) := by
  cases enc
  · simp only [start, Bool.false_eq_true, ite_false]
    rw [exec_addImm_x (by omega_using [hh])]
    simp only [State.read, BitVec.setWidth_eq, hx27 rfl]
  · simp only [start, ite_true]
    rw [exec_subImm_x (by omega_using [])]
    simp only [State.read, BitVec.setWidth_eq, hx rfl, dataOf, ite_true]
    rw [Offset.add_ofNat_sub B (by omega_using []), show 512 - (512 - 256 * half) = 256 * half by omega_using [hh]]

/-- `x27` set back to the chunk's source after phase `half`, which absorbed the
256 bytes from `B + 256 half`: when decrypting, `B`; when encrypting, in place,
the chunk's data, `x26`. -/
theorem back_ok (enc : Bool) (half : Nat) (hh : half ≤ 1) (B X : Addr) (w : State)
    (hx20 : w.gpr .x20 = B + BitVec.ofNat 64 (256 * half) + BitVec.ofNat 64 256)
    (hX : X = if enc then w.gpr .x26 else B) :
    exec (back enc half) w = some (w.write .x .x27 X) := by
  cases enc
  · simp only [back, Bool.false_eq_true, ite_false] at hX ⊢
    rw [exec_subImm_x (by omega_using [hh])]
    simp only [State.read, BitVec.setWidth_eq, hx20, hX]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 256 * half + 256 = 256 * (half + 1) by omega_using [],
      BitVec.add_sub_cancel]
  · simp only [back, ite_true] at hX ⊢
    rw [exec_addImm_x (by decide)]
    simp only [State.read, BitVec.setWidth_eq, BitVec.add_zero, hX]

/-- The phase's precondition, from a stage of the kernel. -/
theorem readable_of {B : Addr} {n : Nat} {s₀ s : State} (hr : ∀ d, d + 8 ≤ n →
      InRegions (s₀.rd ++ s₀.wr) (B + BitVec.ofNat 64 d) 8)
    (hk0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 Poly.r0Off) 8)
    (hk1 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 Poly.r1Off) 8)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hx0 : s.gpr .x0 = s₀.gpr .x0) :
    Readable B n s :=
  ⟨fun d hd => by rw [hrd, hwr]; exact hr d hd, by rw [hrd, hwr, hx0]; exact hk0,
    by rw [hrd, hwr, hx0]; exact hk1⟩

theorem not_poly {r : Reg} (ha : r ∉ accRegs) (h20 : r ≠ .x20) (h27 : r ≠ .x27) : r ∉ Poly.regs := by
  intro hm
  simp only [Poly.regs, accRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ha
  rcases hm with h' | h' | h' | h' | h' | h' | h' | h' | h' <;> simp_all

/-- After the first phase. -/
theorem prepared_rebase {blocks : Nat → VG.Spec.ChaCha20.State} {v : VG.Spec.ChaCha20.State}
    {R a : Nat} {W : Addr} {n : Nat} {s₀ s u : State}
    (hx : s₀.gpr .x20 = s₀.gpr .x0 + 64#64) (h : Prepared s₀ s)
    (hb : blocks = fun j => Nat.repeat innerBlock 0 (ctr (source s₀) j))
    (hv : v = Nat.repeat innerBlock (2 * 0) (ctr (source s₀) 6))
    (hd : Done blocks v R a W n .x26 (s₀.gpr .x27) s u) : Prepared (rebase s₀ u) u 5 := by
  subst hb hv
  obtain hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ not_words_x0 (by decide) (by decide)
  obtain hsrc : source u = source s := by
    simp only [source, hd.mem, hd.keep _ not_words_x0 (by decide) x0_not_poly]
  refine ⟨?_, hd.table, ?_, ?_, ?_, ?_, hd.rd.trans h.rd, hd.wr.trans h.wr, hd.sp.trans h.sp, ?_⟩
  · rw [source_rebase]; exact hd.vec
  · rw [source_rebase]; exact hd.scalar
  · rw [source_rebase, hsrc]; exact h.cnt
  · refine ⟨?_, ?_⟩
    · rw [hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide), rebase_of (by decide)]
      exact h.saved.len
    · rw [hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide), rebase_of (by decide)]
      exact h.saved.data
  · intro r hw h19 h26
    by_cases ha : r ∈ accRegs
    · rw [rebase_acc ha]
    rw [rebase_of ha]
    by_cases h1 : r = .x1
    · subst r
      rw [hd.x1, hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide)]
      exact h.saved.data
    by_cases h20 : r = .x20
    · subst r; rw [hd.x20, hx0, hx]
    by_cases h27 : r = .x27
    · subst r; exact hd.x27
    rw [hd.keep r hw h1 (not_poly ha h20 h27)]
    exact h.keep r hw h19 h26
  · rw [hd.mem]
    simpa only [sr, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide)] using h.frame


/-- After the second phase. -/
theorem second_rebase {blocks : Nat → VG.Spec.ChaCha20.State} {v : VG.Spec.ChaCha20.State}
    {R a : Nat} {W : Addr} {n : Nat} {s₀ s u : State} (hp : CP s₀)
    (hx : s₀.gpr .x20 = s₀.gpr .x0 + 64#64) (h : Second s₀ s)
    (hb : blocks = fun j => Nat.repeat innerBlock 5 (ctr (source s₀) j))
    (hv : v = Nat.repeat innerBlock (2 * 0) (ctr (source s₀) 7))
    (hd : Done blocks v R a W n .x20 (s₀.gpr .x27) s u) : Second (rebase s₀ u) u 5 := by
  subst hb hv
  obtain hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ not_words_x0 (by decide) (by decide) (by decide)
  obtain hsrc : source u = source s := by
    simp only [source, hd.mem, hd.keep _ not_words_x0 (by decide) x0_not_poly]
  have he (f : VG.Spec.ChaCha20.State → VG.Spec.ChaCha20.State) (x : VG.Spec.ChaCha20.State) :
      Nat.repeat f 5 (Nat.repeat f 5 x) = Nat.repeat f 10 x := rfl
  have hvec := hd.vec
  obtain he' : (fun j => Nat.repeat innerBlock 5 (Nat.repeat innerBlock 5 (ctr (source s₀) j))) =
      (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j)) :=
    funext fun j => he innerBlock (ctr (source s₀) j)
  rw [he'] at hvec
  obtain h20 : u.gpr .x20 = s₀.gpr .x3 := by rw [hd.x20, hx0, ← hx, hp.x20]
  refine ⟨?_, hd.table, ?_, ?_, ?_, ?_, ?_, ?_, hd.rd.trans h.rd, hd.wr.trans h.wr,
    hd.sp.trans h.sp, ?_⟩
  · rw [source_rebase]; exact hvec
  · rw [source_rebase]; exact hd.scalar
  · rw [source_rebase, hsrc]; exact h.cnt
  · refine ⟨?_, ?_⟩
    · rw [hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide), rebase_of (by decide)]
      exact h.saved.len
    · rw [hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide), rebase_of (by decide)]
      exact h.saved.data
  · rw [source_rebase, hd.mem, rebase_of (show Reg.x3 ∉ accRegs by decide)]; exact h.first
  · intro r hw h1 h19 h26
    by_cases ha : r ∈ accRegs
    · rw [rebase_acc ha]
    rw [rebase_of ha]
    by_cases h20' : r = .x20
    · subst r; rw [h20, ← hp.x20]
    by_cases h27 : r = .x27
    · subst r; exact hd.x27
    rw [hd.keep r hw h1 (not_poly ha h20' h27)]
    exact h.keep r hw h1 h19 h26
  · rw [hd.x1, h20, rebase_of (by decide)]
  · rw [hd.mem]
    simpa only [sr, lowBuf, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide),
      rebase_of (show Reg.x3 ∉ accRegs by decide)] using h.frame

theorem rebase_rebase (s₀ u w : State) : rebase (rebase s₀ u) w = rebase s₀ w := by
  simp only [rebase]
  congr 1
  funext r
  by_cases h : r ∈ accRegs <;> simp only [h, ite_true, ite_false]

theorem rebase_congr (s₀ : State) {u w : State} (h : ∀ r ∈ accRegs, u.gpr r = w.gpr r) :
    rebase s₀ u = rebase s₀ w := by
  simp only [rebase]
  congr 1
  funext r
  by_cases hr : r ∈ accRegs <;> simp only [hr, ite_true, ite_false, h r]

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- Where the key is. -/
abbrev keyR (s : State) : Region := ⟨s.gpr .x0 + BitVec.ofNat 64 224, 16⟩

/-- The key's words outside a frame are unchanged. -/
theorem rword_frame {rs : List Region} {s u : State} (hf : Frame rs s.mem u.mem)
    (hx0 : u.gpr .x0 = s.gpr .x0) (hd : ∀ r ∈ rs, (keyR s).Disjoint r) (d : Nat)
    (hd' : d = Poly.r0Off ∨ d = Poly.r1Off) : Poly.rword u d = Poly.rword s d := by
  simp only [Poly.rword, hx0]
  refine hf.readW ?_ hd (by decide)
  rcases hd' with rfl | rfl
  · exact Offset.contains _ (by decide) (by decide) (by decide)
  · exact Offset.contains _ (by decide : 224 ≤ 232) (by decide) (by decide)

theorem Acc.frame {R a : Nat} {s u : State} (h : Acc R a s)
    (hg : ∀ r ∈ [Reg.x21, .x22, .x23], u.gpr r = s.gpr r)
    (hk : ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword u d = Poly.rword s d) :
    Acc R a u := by
  obtain hv : Poly.hval u = Poly.hval s := by
    simp only [Poly.hval, hg .x21 (by decide), hg .x22 (by decide), hg .x23 (by decide)]
  exact ⟨by rw [hv]; exact h.h, by rw [hg .x23 (by decide)]; exact h.h2,
    by simp only [Poly.rval, hk _ (.inl rfl), hk _ (.inr rfl)]; exact h.key,
    by rw [hk _ (.inl rfl)]; exact h.k0, by rw [hk _ (.inr rfl)]; exact h.k1⟩

/-- What a chunk needs, absorbing the `n₀` bytes from `B₀` and the `n₁` from
`B₁` (as the phases' starts, `st₀` and `st₁`, point `x20` at them, from the
chunk's saved arguments, its data in `x26` and its length in `x19`, or its
source in `x27`, which the phases' ends, `bk₀` and `bk₁`, set back), and
XORing the source at `r` into the data. -/
structure ChunkPreW (st₀ st₁ bk₀ bk₁ : Instr) (r : Reg) (B₀ B₁ : Addr) (n₀ n₁ : Nat) (s : State) : Prop where
  cp : CP s
  x20 : s.gpr .x20 = s.gpr .x0 + 64#64
  st₀ : ∀ u : State, u.gpr .x19 = s.gpr .x2 → u.gpr .x26 = s.gpr .x1 → u.gpr .x27 = s.gpr .x27 →
    exec st₀ u = some (u.write .x .x20 B₀)
  st₁ : ∀ u : State, u.gpr .x19 = s.gpr .x2 → u.gpr .x26 = s.gpr .x1 → u.gpr .x27 = s.gpr .x27 →
    exec st₁ u = some (u.write .x .x20 B₁)
  bk₀ : ∀ w : State, w.gpr .x20 = B₀ + BitVec.ofNat 64 n₀ → w.gpr .x26 = s.gpr .x1 →
    exec bk₀ w = some (w.write .x .x27 (s.gpr .x27))
  bk₁ : ∀ w : State, w.gpr .x20 = B₁ + BitVec.ofNat 64 n₁ → w.gpr .x26 = s.gpr .x1 →
    exec bk₁ w = some (w.write .x .x27 (s.gpr .x27))
  src : SrcOK r s
  blk₀ : ∀ d, d + 8 ≤ n₀ → InRegions (s.rd ++ s.wr) (B₀ + BitVec.ofNat 64 d) 8
  blk₁ : ∀ d, d + 8 ≤ n₁ → InRegions (s.rd ++ s.wr) (B₁ + BitVec.ofNat 64 d) 8
  k0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r0Off) 8
  k1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r1Off) 8
  win₀ : ∀ r ∈ [sr s, scalarBuf s], (⟨B₀, n₀⟩ : Region).Disjoint r
  win₁ : ∀ r ∈ [sr s, scalarBuf s], (⟨B₁, n₁⟩ : Region).Disjoint r
  le₀ : n₀ ≤ 2 ^ 64
  le₁ : n₁ ≤ 2 ^ 64
  key : ∀ r ∈ [sr s, scalarBuf s, VG.Proof.ChaCha20.AArch64.Mixed8.dr s], (keyR s).Disjoint r

/-- A chunk's source, for states with the accumulator's registers of `u`. -/
theorem srcOK_rebase {r : Reg} {s : State} (h : SrcOK r s) (u : State) : SrcOK r (rebase s u) := by
  obtain hr : (rebase s u).gpr r = s.gpr r := by
    rcases h.reg with rfl | rfl <;> exact rebase_of (by decide)
  obtain e0 : (rebase s u).gpr .x0 = s.gpr .x0 := rebase_of (by decide)
  obtain e1 : (rebase s u).gpr .x1 = s.gpr .x1 := rebase_of (by decide)
  obtain e3 : (rebase s u).gpr .x3 = s.gpr .x3 := rebase_of (by decide)
  exact ⟨h.reg, by simpa only [hr, rebase_rd, rebase_wr] using h.src,
    by simpa only [sr, hr, e0] using h.st_s, by simpa only [br, hr, e3] using h.s_b,
    by simpa only [dr, hr, e1] using h.alias⟩

/-- The key's words, in a state that has written only regions disjoint from
the key since `s`. -/
theorem rword_of {rs : List Region} {s u : State} (hf : Frame rs s.mem u.mem)
    (hx0 : u.gpr .x0 = s.gpr .x0) (hd : ∀ r ∈ rs, (keyR s).Disjoint r) :
    ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword u d = Poly.rword s d :=
  fun d hd' => rword_frame hf hx0 hd d hd'

theorem acc_regs_keep {s u : State} (h : ∀ r ∈ accRegs, u.gpr r = s.gpr r) :
    ∀ r ∈ [Reg.x21, .x22, .x23], u.gpr r = s.gpr r := fun r hr =>
  h r ((show ∀ r ∈ [Reg.x21, .x22, .x23], r ∈ accRegs by decide) r hr)

theorem chunkWith_ok {st₀ st₁ bk₀ bk₁ : Instr} {r : Reg} {l₀ k₀ l₁ k₁ : Nat} {R a : Nat} {B₀ B₁ : Addr}
    (s : State) (hp : ChunkPreW st₀ st₁ bk₀ bk₁ r B₀ B₁ (16 * (l₀ + 5 * k₀)) (16 * (l₁ + 5 * k₁)) s)
    (ha : Acc R a s) :
    WP isa (chunkWith sve st₀ st₁ l₀ k₀ l₁ k₁ bk₀ bk₁ r) s fun g =>
      ChunkedFrom r (rebase s g) g ∧ Acc R (absorbAll R a (bytesAt s.mem B₀ (16 * (l₀ + 5 * k₀)) ++
        bytesAt s.mem B₁ (16 * (l₁ + 5 * k₁)))) g := by
  have hcp := hp.cp
  have hkey (rs : List Region) (h : ∀ r ∈ rs, r ∈ [sr s, scalarBuf s, VG.Proof.ChaCha20.AArch64.Mixed8.dr s]) :
      ∀ r ∈ rs, (keyR s).Disjoint r := fun r hr => hp.key r (h r hr)
  obtain hlow : (lowBuf s).Sub (scalarBuf s) := Region.sub_prefix (by decide : 64 ≤ 128)
  unfold chunkWith
  apply WP.seq
  refine (prepare_ok s hcp).mono fun pa hpa => ?_
  obtain x0a : pa.gpr .x0 = s.gpr .x0 := hpa.keep _ not_words_x0 (by decide) (by decide)
  obtain rwa := rword_of hpa.frame x0a (hkey _ (by simp))
  obtain accA : Acc R a pa := ha.frame (acc_regs_keep fun r hr =>
    hpa.keep _ (not_words_preserved (acc_preserved r hr).1) (acc_preserved r hr).2.1
      (acc_preserved r hr).2.2.1) rwa
  obtain rdA : Readable B₀ (16 * (l₀ + 5 * k₀)) pa :=
    readable_of hp.blk₀ hp.k0 hp.k1 hpa.rd hpa.wr x0a
  -- The first phase.
  apply WP.seq
  obtain x27a : pa.gpr .x27 = s.gpr .x27 :=
    hpa.keep _ (not_words_preserved (by decide)) (by decide) (by decide)
  refine (phaseWith_ok (W := B₀) (len := 16 * (l₀ + 5 * k₀)) (Nat.le_refl _) hpa.vec hpa.scalar
    hpa.table (hp.st₀ pa hpa.saved.len hpa.saved.data x27a)
    (fun w h20 h26 => hp.bk₀ w h20 (h26.trans hpa.saved.data)) accA rdA).mono fun pb hpb => ?_
  obtain prB := prepared_rebase hp.x20 hpa rfl rfl hpb
  obtain hcp₁ := rebase_cp pb hcp
  -- The second block.
  apply WP.seq
  refine (second_ok hcp₁ prB).mono fun pc hpc => ?_
  obtain x0c : pc.gpr .x0 = s.gpr .x0 :=
    (hpc.keep _ not_words_x0 (by decide) (by decide) (by decide)).trans (rebase_of (by decide))
  obtain x19c : pc.gpr .x19 = s.gpr .x2 := by rw [hpc.saved.len, rebase_of (by decide)]
  obtain x26c : pc.gpr .x26 = s.gpr .x1 := by rw [hpc.saved.data, rebase_of (by decide)]
  obtain fc : Frame [sr s, lowBuf s] s.mem pc.mem := by
    simpa only [sr, lowBuf, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide),
      rebase_of (show Reg.x3 ∉ accRegs by decide)] using hpc.frame
  obtain rwc := rword_of fc x0c (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.key _ (by simp)
    · exact (hp.key _ (by simp)).sub_right hlow)
  obtain rwb : ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword pb d = Poly.rword s d := by
    intro d hd
    rw [← rwa d hd]
    simp only [Poly.rword, hpb.mem, hpb.keep _ not_words_x0 (by decide) x0_not_poly]
  obtain accC := hpb.acc.frame (acc_regs_keep fun r hr =>
      (hpc.keep _ (not_words_preserved (acc_preserved r hr).1) (by
        intro he; rw [he] at hr; exact absurd hr (by decide)) (acc_preserved r hr).2.1
        (acc_preserved r hr).2.2.1).trans (rebase_acc hr))
    (fun d hd => (rwc d hd).trans (rwb d hd).symm)
  obtain rdC : Readable B₁ (16 * (l₁ + 5 * k₁)) pc :=
    readable_of hp.blk₁ hp.k0 hp.k1 (hpc.rd.trans (rebase_rd _ _)) (hpc.wr.trans (rebase_wr _ _)) x0c
  -- The second phase.
  apply WP.seq
  obtain x27c : pc.gpr .x27 = s.gpr .x27 :=
    (hpc.keep _ (not_words_preserved (by decide)) (by decide) (by decide) (by decide)).trans
      (rebase_of (by decide))
  refine (phaseWith_ok (W := B₁) (len := 16 * (l₁ + 5 * k₁)) (Nat.le_refl _) hpc.vec hpc.scalar
    hpc.table (hp.st₁ pc x19c x26c x27c) (fun w h20 h26 => hp.bk₁ w h20 (h26.trans x26c)) accC rdC).mono
    fun pd hpd => ?_
  obtain hcp₂ := rebase_cp pd hcp₁
  obtain hx₁ : (rebase s pb).gpr .x20 = (rebase s pb).gpr .x0 + 64#64 := by
    rw [rebase_of (by decide), rebase_of (by decide)]; exact hp.x20
  obtain seD := second_rebase hcp₁ hx₁ hpc (by rw [source_rebase]) (by rw [source_rebase])
    (by rw [rebase_of (show Reg.x27 ∉ accRegs by decide)]; exact hpd)
  rw [rebase_rebase] at seD hcp₂
  obtain hsr₂ : SrcOK r (rebase s pd) := srcOK_rebase hp.src pd
  -- The rest of the kernel's chunk.
  apply WP.seq
  refine (spill2_ok hcp₂ seD).mono fun pe hpe => ?_
  apply WP.seq
  refine (finishFrom_ok r hcp₂ hsr₂ hpe).mono fun pf hpf => ?_
  refine (lastFrom_ok r hcp₂ hsr₂ hpf).mono fun pg hpg => ?_
  obtain hacc : ∀ r ∈ accRegs, pg.gpr r = pd.gpr r := fun r hr =>
    (hpg.cs r (acc_preserved r hr).1 (acc_preserved r hr).2.1 (acc_preserved r hr).2.2.1).trans
      (rebase_acc hr)
  rw [rebase_congr s hacc]
  refine ⟨hpg, ?_⟩
  -- The accumulator.
  obtain x0g : pg.gpr .x0 = s.gpr .x0 := hpg.x0.trans (rebase_of (by decide))
  obtain fg : Frame [sr s, scalarBuf s, VG.Proof.ChaCha20.AArch64.Mixed8.dr s] s.mem pg.mem := by
    simpa only [sr, scalarBuf, VG.Proof.ChaCha20.AArch64.Mixed8.dr, rebase_mem,
      rebase_of (show Reg.x0 ∉ accRegs by decide), rebase_of (show Reg.x1 ∉ accRegs by decide),
      rebase_of (show Reg.x3 ∉ accRegs by decide)] using hpg.frame
  obtain rwg := rword_of fg x0g (hkey _ (fun r hr => hr))
  obtain rwd : ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword pd d = Poly.rword s d := by
    intro d hd
    rw [← rwc d hd]
    simp only [Poly.rword, hpd.mem, hpd.keep _ not_words_x0 (by decide) x0_not_poly]
  obtain accG := hpd.acc.frame (acc_regs_keep hacc) (fun d hd => (rwg d hd).trans (rwd d hd).symm)
  -- The bytes absorbed.
  obtain bA : bytesAt pa.mem B₀ (16 * (l₀ + 5 * k₀)) = bytesAt s.mem B₀ (16 * (l₀ + 5 * k₀)) :=
    bytesAt_frame hpa.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.win₀ _ (by simp)) hp.le₀
  obtain bC : bytesAt pc.mem B₁ (16 * (l₁ + 5 * k₁)) = bytesAt s.mem B₁ (16 * (l₁ + 5 * k₁)) :=
    bytesAt_frame fc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.win₁ _ (by simp)
      · exact (hp.win₁ _ (by simp)).sub_right hlow) hp.le₁
  rw [bC, bA] at accG
  obtain hl : (bytesAt s.mem B₀ (16 * (l₀ + 5 * k₀))).length % 16 = 0 := by
    rw [Poly1305.length_bytesAt]; omega_using []
  rw [← Poly1305.absorbAll_append hl] at accG
  exact accG

/-- What a chunk needs: it absorbs the 512 bytes from `B` (the source,
at `x27`, when decrypting; the output before the destination, at `x1`, which
is also the source, when encrypting in place). -/
structure ChunkPre (enc : Bool) (B : Addr) (s : State) : Prop where
  cp : CP s
  x20 : s.gpr .x20 = s.gpr .x0 + 64#64
  x27 : s.gpr .x27 = dataOf enc B
  x1 : enc = true → s.gpr .x1 = s.gpr .x27
  src : SrcOK .x27 s
  blk : ∀ d, d + 8 ≤ 512 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8
  k0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r0Off) 8
  k1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r1Off) 8
  win : ∀ r ∈ [sr s, scalarBuf s], (⟨B, 512⟩ : Region).Disjoint r
  key : ∀ r ∈ [sr s, scalarBuf s, VG.Proof.ChaCha20.AArch64.Mixed8.dr s], (keyR s).Disjoint r

theorem chunk_ok (enc : Bool) {R a : Nat} {B : Addr} (s : State) (hp : ChunkPre enc B s)
    (ha : Acc R a s) :
    WP isa (chunk sve enc) s fun g =>
      ChunkedFrom .x27 (rebase s g) g ∧ Acc R (absorbAll R a (bytesAt s.mem B 512)) g := by
  have hwin (k : Nat) (hk : k ≤ 1) : (⟨B + BitVec.ofNat 64 (256 * k), 256⟩ : Region).Sub ⟨B, 512⟩ :=
    Offset.sub_base _ (by omega_using [hk])
  have hb (k : Nat) (hk : k ≤ 1) : ∀ d, d + 8 ≤ 16 * (1 + 5 * 3) →
      InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (256 * k) + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.blk _ (by omega_using [hk, hd])
  -- The chunk's data (`x26` in its phases) and source (`x27`).
  have hst (k : Nat) (hk : k ≤ 1) : ∀ u : State, u.gpr .x19 = s.gpr .x2 → u.gpr .x26 = s.gpr .x1 →
      u.gpr .x27 = s.gpr .x27 →
      exec (start enc k) u = some (u.write .x .x20 (B + BitVec.ofNat 64 (256 * k))) := by
    intro u _ h26 h27
    cases enc
    · exact start_ok false k hk B u (fun h => nomatch h)
        (fun _ => by rw [h27, hp.x27]; simp only [dataOf, Bool.false_eq_true, ite_false, BitVec.add_zero])
    · exact start_ok true k hk B u (fun _ => by rw [h26, hp.x1 rfl, hp.x27]) (fun h => nomatch h)
  have hbk (k : Nat) (hk : k ≤ 1) : ∀ w : State,
      w.gpr .x20 = B + BitVec.ofNat 64 (256 * k) + BitVec.ofNat 64 (16 * (1 + 5 * 3)) →
      w.gpr .x26 = s.gpr .x1 → exec (back enc k) w = some (w.write .x .x27 (s.gpr .x27)) := by
    intro w h20 h26
    refine back_ok enc k hk B _ w h20 ?_
    cases enc
    · simp only [Bool.false_eq_true, ite_false, hp.x27, dataOf, BitVec.add_zero]
    · simp only [ite_true, h26, hp.x1 rfl]
  obtain pre : ChunkPreW (start enc 0) (start enc 1) (back enc 0) (back enc 1) .x27
      (B + BitVec.ofNat 64 (256 * 0)) (B + BitVec.ofNat 64 (256 * 1)) (16 * (1 + 5 * 3)) (16 * (1 + 5 * 3)) s :=
    ⟨hp.cp, hp.x20, hst 0 (by decide), hst 1 (by decide), hbk 0 (by decide), hbk 1 (by decide), hp.src,
      hb 0 (by decide), hb 1 (by decide), hp.k0, hp.k1,
      fun r hr => (hp.win r hr).sub_left (hwin 0 (by decide)),
      fun r hr => (hp.win r hr).sub_left (hwin 1 (by decide)), by decide, by decide, hp.key⟩
  refine (chunkWith_ok s pre ha).mono fun g ⟨hg, hag⟩ => ⟨hg, ?_⟩
  obtain e : bytesAt s.mem (B + BitVec.ofNat 64 (256 * 0)) (16 * (1 + 5 * 3)) ++
      bytesAt s.mem (B + BitVec.ofNat 64 (256 * 1)) (16 * (1 + 5 * 3)) = bytesAt s.mem B 512 := by
    rw [show B + BitVec.ofNat 64 (256 * 0) = B by simp, Nat.mul_one,
      show 16 * (1 + 5 * 3) = 256 from rfl, ← Poly1305.bytesAt_add]
  rw [e] at hag
  exact hag

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch

end

end


/-!
# ChaCha20 and Poly1305 together (AArch64): a chunk of the loop

`Stitch.body`, as `Mixed8.tbody_ok`: from the kernel's loop invariant
(`Mixed8.TInv`, the source at `x27` and the destination at `x1`) after `t`
chunks to the one after `t + 1`, relative to the entry state `rebase s₀ u`,
since the chunk changes the accumulator's registers.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP ChunkedFrom SrcOK source sr scalarBuf dr TInv TSaved
  tcp_of_inv tnext_ok twin_sub swin_sub)
open VG.Proof.ChaCha20.AArch64.Xor (TPre st dp L bp tp stR dR tR bR S0 D0 T0 KS Dst Src)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

@[simp] theorem rebase_x0 (s₀ u : State) : (rebase s₀ u).gpr .x0 = s₀.gpr .x0 := rebase_of (by decide)
@[simp] theorem rebase_x1 (s₀ u : State) : (rebase s₀ u).gpr .x1 = s₀.gpr .x1 := rebase_of (by decide)
@[simp] theorem rebase_x2 (s₀ u : State) : (rebase s₀ u).gpr .x2 = s₀.gpr .x2 := rebase_of (by decide)
@[simp] theorem rebase_x3 (s₀ u : State) : (rebase s₀ u).gpr .x3 = s₀.gpr .x3 := rebase_of (by decide)
@[simp] theorem rebase_x4 (s₀ u : State) : (rebase s₀ u).gpr .x4 = s₀.gpr .x4 := rebase_of (by decide)
@[simp] theorem rebase_x19 (s₀ u : State) : (rebase s₀ u).gpr .x19 = s₀.gpr .x19 := rebase_of (by decide)
@[simp] theorem rebase_x20 (s₀ u : State) : (rebase s₀ u).gpr .x20 = s₀.gpr .x20 := rebase_of (by decide)
@[simp] theorem rebase_x26 (s₀ u : State) : (rebase s₀ u).gpr .x26 = s₀.gpr .x26 := rebase_of (by decide)
@[simp] theorem rebase_x27 (s₀ u : State) : (rebase s₀ u).gpr .x27 = s₀.gpr .x27 := rebase_of (by decide)
@[simp] theorem rebase_v (s₀ u : State) : (rebase s₀ u).v = s₀.v := rfl

@[simp] theorem st_rebase (s₀ u : State) : st (rebase s₀ u) = st s₀ := rebase_x0 s₀ u
@[simp] theorem dp_rebase (s₀ u : State) : dp (rebase s₀ u) = dp s₀ := rebase_x1 s₀ u
@[simp] theorem tp_rebase (s₀ u : State) : tp (rebase s₀ u) = tp s₀ := rebase_x4 s₀ u
@[simp] theorem L_rebase (s₀ u : State) : L (rebase s₀ u) = L s₀ := by simp [L]
@[simp] theorem bp_rebase (s₀ u : State) : bp (rebase s₀ u) = bp s₀ := rebase_x3 s₀ u
@[simp] theorem stR_rebase (s₀ u : State) : stR (rebase s₀ u) = stR s₀ := by simp [stR]
@[simp] theorem dR_rebase (s₀ u : State) : dR (rebase s₀ u) = dR s₀ := by simp [dR]
@[simp] theorem tR_rebase (s₀ u : State) : tR (rebase s₀ u) = tR s₀ := by simp [tR]
@[simp] theorem bR_rebase (s₀ u : State) : bR (rebase s₀ u) = bR s₀ := by simp [bR]
@[simp] theorem S0_rebase (s₀ u : State) : S0 (rebase s₀ u) = S0 s₀ := by simp [S0]
@[simp] theorem D0_rebase (s₀ u : State) (k : Nat) : D0 (rebase s₀ u) k = D0 s₀ k := by simp [D0]
@[simp] theorem T0_rebase (s₀ u : State) (k : Nat) : T0 (rebase s₀ u) k = T0 s₀ k := by simp [T0]
@[simp] theorem KS_rebase (s₀ u : State) : KS (rebase s₀ u) = KS s₀ := by simp [KS]

theorem tpre_rebase {s₀ : State} (u : State) (hp : TPre s₀) : TPre (rebase s₀ u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hp
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
    by simpa using h5, by simpa using h6, by simpa using h7, by simpa using h8, by simpa using h9,
    by simpa using h10⟩

theorem dst_rebase {s₀ : State} {n : Nat} {m : Mem} (h : Dst s₀ n m) (u : State) : Dst (rebase s₀ u) n m := by
  intro k hk; simpa using h k (by simpa using hk)

theorem src_rebase {s₀ : State} {n : Nat} {m : Mem} (h : Src s₀ n m) (u : State) : Src (rebase s₀ u) n m := by
  intro k hk hn; simpa using h k (by simpa using hk) hn

/-- The kernel's loop invariant, for states with the accumulator's registers
of `u`. -/
theorem tinv_rebase {s₀ s : State} {t : Nat} (h : TInv s₀ t s) (u : State) :
    TInv (rebase s₀ u) t (rebase s u) := by
  refine ⟨by simpa using h.x0, by simpa using h.x1, by simpa using h.x2, by simpa using h.x3,
    by simpa using h.x20, by simpa using h.x27, by simpa using h.le, ?_, by simpa using h.rd,
    by simpa using h.wr, by simpa using h.sp, by simpa using h.cnt, dst_rebase h.data u,
    src_rebase h.src u, fun p hp => ?_, by simpa using h.savedV⟩
  · intro r hr h19 h20 h27 h26
    by_cases ha : r ∈ accRegs
    · rw [rebase_acc ha, rebase_acc ha]
    · rw [rebase_of ha, rebase_of ha]; exact h.cs r hr h19 h20 h27 h26
  · have e := h.saved p hp
    obtain hp' : p.1 ∉ accRegs :=
      (show ∀ q ∈ VG.Impl.ChaCha20.AArch64.Mixed8.savedFrom, q.1 ∉ accRegs by decide) p hp
    simpa only [bp_rebase, rebase_mem, rebase_of hp'] using e

/-- The bulk's precondition: the stream's (`vg_chacha20_xor`'s), with its
working space 64 bytes after the state, as in the ChaCha20-Poly1305 context. -/
structure BPre (s₀ : State) : Prop extends TPre s₀ where
  bp : bp s₀ = st s₀ + 64#64

theorem BPre.rebase {s₀ : State} (h : BPre s₀) (u : State) : BPre (rebase s₀ u) :=
  ⟨tpre_rebase u h.toTPre, by simpa using h.bp⟩

theorem BPre.key_sub {s₀ : State} (h : BPre s₀) : (⟨st s₀ + 224#64, 16⟩ : Region).Sub (bR s₀) := by
  simp only [bR, h.bp]
  exact Offset.sub (st s₀) (e := 64) (k := 320) (d := 224) (n := 16) (by decide) (by decide)

theorem BPre.key_in {s₀ : State} (h : BPre s₀) {d : Nat} (hd : 224 ≤ d) (hd' : d + 8 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) 8 := by
  rw [h.rd, h.wr]
  refine ⟨bR s₀, by simp, ?_⟩
  simp only [bR, h.bp]
  exact Offset.contains (st s₀) (e := 64) (k := 320) (by omega_using [hd]) (by omega_using [hd']) (by decide)

/-- A chunk of the loop, absorbing the 512 bytes at `dp s₀ + w`: the chunk's
source when decrypting, the output before it when encrypting (in place). -/
theorem body_ok (enc : Bool) {s₀ : State} (hp : BPre s₀) (hin : enc = true → tp s₀ = dp s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s : State} (h : TInv s₀ t s) {R a : Nat} {w : Nat}
    (hw : w + 512 ≤ L s₀)
    (hB : dp s₀ + BitVec.ofNat 64 (512 * t) = dataOf enc (dp s₀ + BitVec.ofNat 64 w))
    (ha : Acc R a s) :
    WP isa (body sve enc) s fun v =>
      (TInv (rebase s₀ v) (t + 1) v ∧
        v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0)) ∧
      Acc R (absorbAll R a (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 w) 512)) v := by
  obtain hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  obtain hBin : (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Sub (dR s₀) := Offset.sub_base _ hw
  have hx0 : s.gpr .x0 = st s₀ := h.x0
  obtain hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  obtain hwin : (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Disjoint (stR s₀) ∧
      (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Disjoint (bR s₀) :=
    ⟨hp.st_d.symm.sub_left hBin, hp.d_b.sub_left hBin⟩
  obtain hsb : (scalarBuf s).Sub (bR s₀) := by
    simp only [scalarBuf, h.x3]; exact Region.sub_prefix (by decide)
  obtain hkey : (keyR s).Sub (bR s₀) := by simp only [keyR, hx0]; exact hp.key_sub
  obtain ⟨hcp, hsrc⟩ := tcp_of_inv hp.toTPre h hge
  obtain hpre : ChunkPre enc (dp s₀ + BitVec.ofNat 64 w) s := by
    refine ⟨hcp, by rw [h.x20, hx0, hp.bp], h.x27.trans hB, fun he => by rw [h.x1, h.x27, hin he],
      hsrc, fun d hd => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrw, hp.rd, hp.wr]
      refine ⟨dR s₀, by simp, ?_⟩
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega_using [hw, hd]) (by omega_using [hw, hL, hd])
    · rw [hrw, hx0]; exact hp.key_in (by decide) (by decide)
    · rw [hrw, hx0]; exact hp.key_in (by decide) (by decide)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa only [sr, hx0] using hwin.1
      · exact hwin.2.sub_right hsb
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · simpa only [sr, hx0] using (hp.st_b.symm.sub_left hkey)
      · simp only [keyR, scalarBuf, hx0, h.x3, hp.bp]
        exact Offset.disjoint (st s₀) (d := 224) (n := 16) (e := 64) (k := 128) (by decide)
          (by decide) (by decide)
      · simp only [dr, h.x1]
        exact (hp.t_b.symm.sub_left hkey).sub_right (twin_sub hge)
  unfold body
  apply WP.seq
  refine (chunk_ok enc s hpre ha).mono fun g ⟨hg, hag⟩ => ?_
  refine (tnext_ok (tpre_rebase g hp.toTPre) (by simpa using hge) (tinv_rebase h g) hg).mono
    fun v ⟨hv, h5, hf⟩ => ?_
  obtain hacc : ∀ r ∈ accRegs, v.gpr r = g.gpr r := fun r hr =>
    (hv.cs r (acc_preserved r hr).1 (by intro he; rw [he] at hr; exact absurd hr (by decide))
      (acc_preserved r hr).2.2.2 (by intro he; rw [he] at hr; exact absurd hr (by decide))
      (acc_preserved r hr).2.2.1).trans (rebase_acc hr)
  rw [rebase_congr s₀ hacc]
  refine ⟨⟨hv, by simpa using h5⟩, hag.frame (acc_regs_keep hacc) ?_⟩
  obtain hg0 : g.gpr .x0 = st s₀ := (hg.x0.trans (rebase_x0 _ _)).trans hx0
  refine rword_frame (by simpa using hf) (hv.x0.trans (by simp [hg0])) ?_
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  simp only [keyR, hg0]
  exact (hp.st_b.symm.sub_left hp.key_sub)

/-- Where `Mixed8.enterFrom` stores: `x20`, `x19`, `x26` and `x27` at
`buf[256, 288)`, and `v8` and `v9` at `buf[128, 160)`. -/
abbrev enterR (s : State) : List Region :=
  [⟨s.gpr .x3 + BitVec.ofNat 64 256, 32⟩, ⟨s.gpr .x3 + BitVec.ofNat 64 128, 32⟩]

theorem enter_frame (s : State)
    (ho : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.enterFrom) s fun u =>
      Frame (enterR s) s.mem u.mem := by
  rw [show VG.Impl.ChaCha20.AArch64.Mixed8.enterFrom =
    Spill.saveCode .x3 VG.Impl.ChaCha20.AArch64.Mixed8.savedFrom ++
    (.addImm .x .x20 .x3 0 :: (VG.Proof.ChaCha20.AArch64.Mixed8.saveV ++
      [.addImm .x .x27 .x1 0, .addImm .x .x1 .x4 0])) from rfl]
  refine Spill.save_ok (by decide) (fun p hp' => ho p.2 8 (by revert p; decide)) ?_
  let b : State := { s with mem := Spill.saveMem s.mem (s.gpr .x3) s.gpr VG.Impl.ChaCha20.AArch64.Mixed8.savedFrom }
  obtain f₁ : Frame (enterR s) s.mem b.mem :=
    (Spill.saveMem_frame (lo := 256) (n := 32) (by decide) (by decide) _ _ _).mono (by simp)
  apply WP.block_cons_iff.mpr
  let a := b.write .x .x20 (b.gpr .x3 + BitVec.ofNat 64 0)
  refine ⟨a, by simpa only [State.read, BitVec.setWidth_eq] using
    exec_addImm_x (s := b) (d := .x20) (n := .x3) (imm := 0) (by decide), ?_⟩
  obtain ha3 : a.gpr .x3 = s.gpr .x3 := RegUpd.gpr_write_of_ne _ .x _ (by decide)
  have haw : a.wr = s.wr := rfl
  refine WP.block_append_iff.mpr ((VG.Proof.ChaCha20.AArch64.Mixed8.saveV_ok a
    (by rw [haw, ha3]; exact ho 128 16 (by decide))
    (by rw [haw, ha3]; exact ho 144 16 (by decide))).mono fun c ⟨_, _, _, _, _, hf, _, _⟩ => ?_)
  simp only [VG.Proof.ChaCha20.AArch64.Mixed8.savedVR, ha3] at hf
  refine VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun d ud _ _ =>
    VG.Proof.ChaCha20.AArch64.Xor.wp_movS fun e ue _ _ => WP.block_nil ?_
  rw [ue.mem, ud.mem]
  exact f₁.trans (hf.mono (by simp))

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch

end

end

/-!
# ChaCha20 and Poly1305 together (AArch64): the whole chunks

`Stitch.bulk`, from a state with the stream's arguments (`Mixed8.TPre`, the
source at `x1` and the destination at `x4`, with its working space 64 bytes
after the state: `BPre`), at least 512 bytes of data, and the accumulator in
`x21`–`x23`: the chunks that fit encrypted (or decrypted), as the stream's
own chunks (`Mixed8.tbulk_ok`), and the bytes they absorbed: when decrypting,
every chunk's source; when encrypting (in place), the output of every chunk
but the last.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP ChunkedFrom source sr scalarBuf dr TInv TRest
  tcp_of_inv tenter_ok tleave_ok tnext_ok twin_sub zero_batches)
open VG.Proof.ChaCha20.AArch64.Xor (TPre st dp L bp tp stR dR tR bR S0 D0 T0 KS Dst Src)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

theorem WP.both {c : Prog isa} {s : State} {Q₁ Q₂ : State → Prop} (h₁ : WP isa c s Q₁)
    (h₂ : WP isa c s Q₂) : WP isa c s fun u => Q₁ u ∧ Q₂ u := by
  obtain ⟨t₁, u₁, e₁, q₁⟩ := h₁
  obtain ⟨t₂, u₂, e₂, q₂⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, u₁, e₁, q₁, q₂⟩

/-- The key is apart from what `enterFrom` stores. -/
theorem key_enter {s₀ : State} (hp : BPre s₀) : ∀ r ∈ enterR s₀, (keyR s₀).Disjoint r := by
  have e (d : Nat) : s₀.gpr .x3 + BitVec.ofNat 64 d = st s₀ + BitVec.ofNat 64 (64 + d) := by
    rw [show s₀.gpr .x3 = bp s₀ from rfl, hp.bp, BitVec.add_assoc, ← BitVec.ofNat_add]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [keyR, e] <;>
    exact Offset.disjoint (st s₀) (by decide) (by decide) (by decide)

/-- The key's words in a state with the entry state's `x0`, whose memory
differs from the entry state's only away from the key. -/
theorem rword_eq {s₀ s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hx0 : s.gpr .x0 = s₀.gpr .x0) (hd : ∀ r ∈ rs, (keyR s₀).Disjoint r) :
    ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword s d = Poly.rword s₀ d :=
  rword_of hf hx0 hd

/-- The source the loop has not reached is as on entry. -/
theorem window_orig {s₀ x : State} {t : Nat} (h : TInv s₀ t x) (hge : 512 * t + 512 ≤ L s₀) :
    bytesAt x.mem (dp s₀ + BitVec.ofNat 64 (512 * t)) 512 =
      bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 (512 * t)) 512 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.src _ (by omega_arith) (by omega_arith)]

/-- The destination the loop has passed is the output. -/
theorem prefix_ct {s₀ : State} {m : Mem} {t n : Nat} (h : Dst s₀ (512 * t) m) (hle : 512 * t ≤ L s₀)
    (hn : n ≤ 512 * t) :
    bytesAt m (tp s₀) n = (List.range n).map fun k => D0 s₀ k ^^^ (KS s₀).getD k 0 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [h _ (by omega_arith), ite_eq_left (by omega_arith)]

theorem bytesAt_join (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n ++ bytesAt m (p + BitVec.ofNat 64 n) 512 = bytesAt m p (n + 512) :=
  (Poly1305.bytesAt_add m p n 512).symm

theorem absorb_join {R a : Nat} {X Y : List Byte} (hx : X.length % 16 = 0) :
    absorbAll R (absorbAll R a X) Y = absorbAll R a (X ++ Y) :=
  (Poly1305.absorbAll_append hx).symm

theorem eval_zero5 {s : State} {n : Nat}
    (h : s.gpr .x5 = BitVec.ofNat 64 (if n < 512 then 1 else 0)) :
    isa.eval (.zero .x .x5) s = some (decide (512 ≤ n)) := zero_batches h

/-- The loop of chunks that decrypt. -/
theorem chunks_open {s₀ : State} (hp : BPre s₀) {R a : Nat} {s : State} {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) (h : TInv (rebase s₀ s) t s)
    (ha : Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * t))) s) :
    WP isa (chunks sve false) s fun u => ∃ T, L s₀ - 512 * T < 512 ∧ t < T ∧
      TInv (rebase s₀ u) T u ∧ Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * T))) u := by
  let Inv : Nat → State → Prop := fun n x => ∃ i, n = L s₀ - 512 * i ∧ 512 ≤ n ∧ t ≤ i ∧
    TInv (rebase s₀ x) i x ∧ Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * i))) x
  refine WP.loop (M := isa) Inv ?_ (L s₀ - 512 * t) s ⟨t, rfl, by omega_arith, Nat.le_refl _, h, ha⟩
  rintro n x ⟨i, rfl, hge', hti, hx, hax⟩
  have hb : dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i) =
      dataOf false (dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i)) := by
    simp only [dataOf, Bool.false_eq_true, ite_false, BitVec.add_zero]
  refine (body_ok false (hp.rebase x) (fun h => nomatch h) (t := i) (by simp; omega_arith) hx (w := 512 * i)
    (by simp; omega_arith) hb hax).mono fun v ⟨⟨hv, h5⟩, hav⟩ => ?_
  rw [rebase_rebase] at hv
  have hwin := window_orig hx (by simp; omega_arith)
  simp only [dp_rebase, rebase_mem] at hwin hav
  rw [hwin, absorb_join (by rw [Poly1305.length_bytesAt]; omega_arith), bytesAt_join,
    show 512 * i + 512 = 512 * (i + 1) by omega_arith] at hav
  rw [L_rebase] at h5
  have hc := eval_zero5 h5
  by_cases he : L s₀ - 512 * (i + 1) < 512
  · left
    rw [decide_eq_false (show ¬ 512 ≤ L s₀ - 512 * (i + 1) by omega_arith)] at hc
    exact ⟨hc, i + 1, he, by omega_arith, hv, hav⟩
  · right
    rw [decide_eq_true (show 512 ≤ L s₀ - 512 * (i + 1) by omega_arith)] at hc
    exact ⟨hc, L s₀ - 512 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by omega_arith, hv, hav⟩

/-- The loop of chunks that encrypt in place, each absorbing the output of the
one before. -/
theorem chunks_seal {s₀ : State} (hp : BPre s₀) (hin : tp s₀ = dp s₀) {R a : Nat} {s : State} {t : Nat}
    (ht : 1 ≤ t) (hge : 512 * t + 512 ≤ L s₀) (h : TInv (rebase s₀ s) t s)
    (ha : Acc R (absorbAll R a (bytesAt s.mem (dp s₀) (512 * (t - 1)))) s) :
    WP isa (chunks sve true) s fun u => ∃ T, L s₀ - 512 * T < 512 ∧ t < T ∧
      TInv (rebase s₀ u) T u ∧
      Acc R (absorbAll R a (bytesAt u.mem (dp s₀) (512 * (T - 1)))) u := by
  let Inv : Nat → State → Prop := fun n x => ∃ i, n = L s₀ - 512 * i ∧ 512 ≤ n ∧ t ≤ i ∧
    TInv (rebase s₀ x) i x ∧ Acc R (absorbAll R a (bytesAt x.mem (dp s₀) (512 * (i - 1)))) x
  refine WP.loop (M := isa) Inv ?_ (L s₀ - 512 * t) s ⟨t, rfl, by omega_arith, Nat.le_refl _, h, ha⟩
  rintro n x ⟨i, rfl, hge', hti, hx, hax⟩
  have hb : dp (rebase s₀ x) + BitVec.ofNat 64 (512 * i) =
      dataOf true (dp (rebase s₀ x) + BitVec.ofNat 64 (512 * (i - 1))) := by
    simp only [dataOf, ite_true, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega_arith
  refine (body_ok true (hp.rebase x) (fun _ => by simpa using hin) (t := i) (by simp; omega_arith) hx
    (w := 512 * (i - 1)) (by simp; omega_arith) hb hax).mono fun v ⟨⟨hv, h5⟩, hav⟩ => ?_
  rw [rebase_rebase] at hv
  simp only [dp_rebase] at hav
  rw [absorb_join (by rw [Poly1305.length_bytesAt]; omega_arith), bytesAt_join,
    show 512 * (i - 1) + 512 = 512 * (i + 1 - 1) by omega_arith] at hav
  have p1 := prefix_ct hx.data hx.le (n := 512 * (i + 1 - 1)) (by omega_arith)
  have p2 := prefix_ct hv.data hv.le (n := 512 * (i + 1 - 1)) (by omega_arith)
  simp only [tp_rebase, D0_rebase, KS_rebase, hin] at p1 p2
  rw [p1, ← p2] at hav
  rw [L_rebase] at h5
  have hc := eval_zero5 h5
  by_cases he : L s₀ - 512 * (i + 1) < 512
  · left
    rw [decide_eq_false (show ¬ 512 ≤ L s₀ - 512 * (i + 1) by omega_arith)] at hc
    exact ⟨hc, i + 1, he, by omega_arith, hv, hav⟩
  · right
    rw [decide_eq_true (show 512 ≤ L s₀ - 512 * (i + 1) by omega_arith)] at hc
    exact ⟨hc, L s₀ - 512 * (i + 1), by omega_arith, i + 1, rfl, by omega_arith, by omega_arith, hv, hav⟩

/-- `leaveFrom` only loads (and moves). -/
theorem leave_mem (s : State)
    (hi : ∀ d n, d + n ≤ 320 → InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.leaveFrom) s fun u => u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self,
    VG.Impl.ChaCha20.AArch64.Mixed8.leaveFrom, VG.Impl.ChaCha20.AArch64.Mixed8.savedFrom,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, runBlock_cons,
    runBlock_nil, exec, addr, Size.bytes, Size.bits, State.load, State.read,
    hi 128 16 (by decide), hi 144 16 (by decide), hi 256 8 (by decide), hi 264 8 (by decide),
    hi 272 8 (by decide), hi 280 8 (by decide), RegUpd.gpr_write, BitVec.setWidth_eq,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, State.setV, Option.bind_some, Option.map_some, isa,
    runStep_some, Option.some.injEq, exists_eq_left']

theorem rebase_self {s₀ u : State} (h : ∀ r ∈ accRegs, u.gpr r = s₀.gpr r) : rebase s₀ u = s₀ := by
  simp only [rebase]
  cases s₀
  congr 1
  funext r
  by_cases hr : r ∈ accRegs <;> simp only [hr, ite_true, ite_false, h r]

/-- What the bulk leaves: `T` chunks done, and the bytes absorbed. -/
structure Bulked (enc : Bool) (R a : Nat) (s₀ : State) (T : Nat) (u : State) : Prop where
  pos : 1 ≤ T
  rest : L s₀ - 512 * T < 512
  inv : TRest (rebase s₀ u) T u
  acc : Acc R (absorbAll R a (if enc then bytesAt u.mem (dp s₀) (512 * (T - 1))
    else bytesAt s₀.mem (dp s₀) (512 * T))) u

/-- Leaving, after the chunks. -/
theorem leave_bulk {enc : Bool} {s₀ : State} (hp : BPre s₀) {R a : Nat} {u : State} {T : Nat}
    (hT : 1 ≤ T) (hr : L s₀ - 512 * T < 512) (h : TInv (rebase s₀ u) T u)
    (ha : Acc R (absorbAll R a (if enc then bytesAt u.mem (dp s₀) (512 * (T - 1))
      else bytesAt s₀.mem (dp s₀) (512 * T))) u) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.leaveFrom) u (Bulked enc R a s₀ T) := by
  have hi : ∀ d n, d + n ≤ 320 → InRegions (u.rd ++ u.wr) (u.gpr .x3 + BitVec.ofNat 64 d) n := by
    intro d n hd
    rw [h.rd, h.wr, h.x3]
    simp only [rebase_rd, rebase_wr, bp_rebase, hp.rd, hp.wr]
    exact ⟨bR s₀, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  refine (WP.both (tleave_ok (hp.rebase u).toTPre h) (leave_mem u hi)).mono
    fun v ⟨hl, hm⟩ => ?_
  have hacc : ∀ r ∈ accRegs, v.gpr r = u.gpr r := fun r hr =>
    (hl.cs r (acc_preserved r hr).1).trans (rebase_acc hr)
  have e := rebase_congr s₀ hacc
  refine ⟨hT, hr, e ▸ hl, ?_⟩
  rw [hm]
  exact ha.frame (acc_regs_keep hacc) fun d _ => by
    simp only [Poly.rword, hm, hl.x0, h.x0]

theorem bytesAt_zero (m : Mem) (p : Addr) : bytesAt m p 0 = [] := rfl

theorem bulk_ok (enc : Bool) {s₀ : State} (hp : BPre s₀) (hin : enc = true → tp s₀ = dp s₀)
    (hL : 512 ≤ L s₀) {R a : Nat} (ha : Acc R a s₀) :
    WP isa (bulk sve enc) s₀ fun u => ∃ T, Bulked enc R a s₀ T u := by
  have ho : ∀ d n, d + n ≤ 320 → InRegions s₀.wr (s₀.gpr .x3 + BitVec.ofNat 64 d) n := by
    intro d n hd
    rw [hp.wr]
    exact ⟨bR s₀, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have nil (m : Mem) (k : Nat) (hk : k = 0) :
      absorbAll R a (bytesAt m (dp s₀) (512 * k)) = a := by
    rw [hk, Nat.mul_zero, bytesAt_zero, Poly1305.absorbAll_nil]
  unfold bulk
  apply WP.seq
  refine (WP.both (tenter_ok hp.toTPre (fun _ _ => rfl) rfl rfl rfl rfl rfl) (enter_frame s₀ ho)).mono
    fun s₁ ⟨h₁, f₁⟩ => ?_
  have acc₁ : ∀ r ∈ accRegs, s₁.gpr r = s₀.gpr r := fun r hr =>
    h₁.cs r (acc_preserved r hr).1 (acc_preserved r hr).2.1 (acc_preserved r hr).2.2.2
      (by intro he; rw [he] at hr; exact absurd hr (by decide)) (acc_preserved r hr).2.2.1
  have rw₁ := rword_eq f₁ h₁.x0 (key_enter hp)
  have ha₁ : Acc R a s₁ := ha.frame (acc_regs_keep acc₁) rw₁
  have hb₁ : TInv (rebase s₀ s₁) 0 s₁ := by rw [rebase_self acc₁]; exact h₁
  apply WP.seq
  cases enc
  · -- Decrypting: every chunk absorbs its source.
    simp only [Bool.false_eq_true, ite_false]
    refine (chunks_open hp (R := R) (a := a) (t := 0) (by omega_arith) hb₁
      (by rw [nil _ _ rfl]; exact ha₁)).mono fun u ⟨T, hr, hT, hu, hau⟩ => ?_
    exact (leave_bulk (enc := false) hp (by omega_arith) hr hu (by simpa using hau)).mono
      fun w hw => ⟨T, hw⟩
  · -- Encrypting: the first chunk is the kernel's.
    have hin' := hin rfl
    simp only [ite_true]
    apply WP.seq
    obtain ⟨hcp, hsrc⟩ := tcp_of_inv hp.toTPre h₁ (by omega_arith)
    have hbody : WP isa (VG.Impl.ChaCha20.AArch64.Mixed8.bodyFrom sve) s₁ fun v => ∃ g,
        ChunkedFrom .x27 s₁ g ∧ TInv s₀ (0 + 1) v ∧
        v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (0 + 1) < 512 then 1 else 0) ∧
        Frame [stR s₀] g.mem v.mem :=
      WP.seq ((VG.Proof.ChaCha20.AArch64.Mixed8.chunkFrom_ok .x27 s₁ hcp hsrc).mono fun g hg =>
        (tnext_ok hp.toTPre (t := 0) (by omega_arith) h₁ hg).mono fun v ⟨hv, h5, hf⟩ => ⟨g, hg, hv, h5, hf⟩)
    refine hbody.mono fun v ⟨g, hg, hv, h5, hf⟩ => ?_
    have accv : ∀ r ∈ accRegs, v.gpr r = s₀.gpr r := fun r hr =>
      hv.cs r (acc_preserved r hr).1 (acc_preserved r hr).2.1 (acc_preserved r hr).2.2.2
        (by intro he; rw [he] at hr; exact absurd hr (by decide)) (acc_preserved r hr).2.2.1
    have hfv : Frame (enterR s₀ ++ [sr s₁, scalarBuf s₁, dr s₁] ++ [stR s₀]) s₀.mem v.mem :=
      ((f₁.mono (by simp)).trans (hg.frame.mono (by simp))).trans (hf.mono (by simp))
    have hx0v : v.gpr .x0 = s₀.gpr .x0 := hv.x0
    have rwv := rword_eq hfv hx0v (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · exact key_enter hp r hr
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · simpa only [sr, h₁.x0] using hp.st_b.symm.sub_left hp.key_sub
          · simp only [keyR, scalarBuf, h₁.x3, hp.bp]
            exact Offset.disjoint (st s₀) (d := 224) (n := 16) (e := 64) (k := 128) (by decide)
              (by decide) (by decide)
          · simp only [dr, h₁.x1]
            exact (hp.t_b.symm.sub_left hp.key_sub).sub_right (twin_sub (by omega_arith))
      · rw [List.mem_singleton.mp hr]; exact (hp.st_b.symm.sub_left hp.key_sub))
    have hav : Acc R (absorbAll R a (bytesAt v.mem (dp s₀) (512 * (1 - 1)))) v := by
      rw [nil _ _ rfl]; exact ha.frame (acc_regs_keep accv) rwv
    have hbv : TInv (rebase s₀ v) 1 v := by rw [rebase_self accv]; exact hv
    apply WP.ite (decide (L s₀ - 512 * (0 + 1) < 512))
      (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short h5)
    · intro hs
      have hs' := of_decide_eq_true hs
      exact WP.block_nil ((leave_bulk (enc := true) hp (Nat.le_refl 1) (by omega_arith) hbv
        (by simpa using hav)).mono fun w hw => ⟨1, hw⟩)
    · intro hs
      have hs' := of_decide_eq_false hs
      refine (chunks_seal hp hin' (t := 1) (Nat.le_refl 1) (by omega_arith) hbv hav).mono
        fun u ⟨T, hr, hT, hu, hau⟩ => ?_
      exact (leave_bulk (enc := true) hp (by omega_arith) hr hu (by simpa using hau)).mono
        fun w hw => ⟨T, hw⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch
