module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Phase
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Chunk
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  have e0 : (rebase s₀ u).gpr .x0 = s₀.gpr .x0 := rebase_of (by decide)
  have e1 : (rebase s₀ u).gpr .x1 = s₀.gpr .x1 := rebase_of (by decide)
  have e3 : (rebase s₀ u).gpr .x3 = s₀.gpr .x3 := rebase_of (by decide)
  have e20 : (rebase s₀ u).gpr .x20 = s₀.gpr .x20 := rebase_of (by decide)
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
    rw [exec_addImm_x (by omega)]
    simp only [State.read, BitVec.setWidth_eq, hx27 rfl]
  · simp only [start, ite_true]
    rw [exec_subImm_x (by omega)]
    simp only [State.read, BitVec.setWidth_eq, hx rfl, dataOf, ite_true]
    rw [Offset.add_ofNat_sub B (by omega), show 512 - (512 - 256 * half) = 256 * half by omega]

/-- `x27` set back to the chunk's source after phase `half`, which absorbed the
256 bytes from `B + 256 half`: when decrypting, `B`; when encrypting, in place,
the chunk's data, `x26`. -/
theorem back_ok (enc : Bool) (half : Nat) (hh : half ≤ 1) (B X : Addr) (w : State)
    (hx20 : w.gpr .x20 = B + BitVec.ofNat 64 (256 * half) + BitVec.ofNat 64 256)
    (hX : X = if enc then w.gpr .x26 else B) :
    exec (back enc half) w = some (w.write .x .x27 X) := by
  cases enc
  · simp only [back, Bool.false_eq_true, ite_false] at hX ⊢
    rw [exec_subImm_x (by omega)]
    simp only [State.read, BitVec.setWidth_eq, hx20, hX]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 256 * half + 256 = 256 * (half + 1) by omega,
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
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ not_words_x0 (by decide) (by decide)
  have hsrc : source u = source s := by
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
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ not_words_x0 (by decide) (by decide) (by decide)
  have hsrc : source u = source s := by
    simp only [source, hd.mem, hd.keep _ not_words_x0 (by decide) x0_not_poly]
  have he (f : VG.Spec.ChaCha20.State → VG.Spec.ChaCha20.State) (x : VG.Spec.ChaCha20.State) :
      Nat.repeat f 5 (Nat.repeat f 5 x) = Nat.repeat f 10 x := rfl
  have hvec := hd.vec
  have he' : (fun j => Nat.repeat innerBlock 5 (Nat.repeat innerBlock 5 (ctr (source s₀) j))) =
      (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j)) :=
    funext fun j => he innerBlock (ctr (source s₀) j)
  rw [he'] at hvec
  have h20 : u.gpr .x20 = s₀.gpr .x3 := by rw [hd.x20, hx0, ← hx, hp.x20]
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
  have hv : Poly.hval u = Poly.hval s := by
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
  have hr : (rebase s u).gpr r = s.gpr r := by
    rcases h.reg with rfl | rfl <;> exact rebase_of (by decide)
  have e0 : (rebase s u).gpr .x0 = s.gpr .x0 := rebase_of (by decide)
  have e1 : (rebase s u).gpr .x1 = s.gpr .x1 := rebase_of (by decide)
  have e3 : (rebase s u).gpr .x3 = s.gpr .x3 := rebase_of (by decide)
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
  have hlow : (lowBuf s).Sub (scalarBuf s) := Region.sub_prefix (by decide : 64 ≤ 128)
  unfold chunkWith
  apply WP.seq
  refine (prepare_ok s hcp).mono fun pa hpa => ?_
  have x0a : pa.gpr .x0 = s.gpr .x0 := hpa.keep _ not_words_x0 (by decide) (by decide)
  have rwa := rword_of hpa.frame x0a (hkey _ (by simp))
  have accA : Acc R a pa := ha.frame (acc_regs_keep fun r hr =>
    hpa.keep _ (not_words_preserved (acc_preserved r hr).1) (acc_preserved r hr).2.1
      (acc_preserved r hr).2.2.1) rwa
  have rdA : Readable B₀ (16 * (l₀ + 5 * k₀)) pa :=
    readable_of hp.blk₀ hp.k0 hp.k1 hpa.rd hpa.wr x0a
  -- The first phase.
  apply WP.seq
  have x27a : pa.gpr .x27 = s.gpr .x27 :=
    hpa.keep _ (not_words_preserved (by decide)) (by decide) (by decide)
  refine (phaseWith_ok (W := B₀) (len := 16 * (l₀ + 5 * k₀)) (Nat.le_refl _) hpa.vec hpa.scalar
    hpa.table (hp.st₀ pa hpa.saved.len hpa.saved.data x27a)
    (fun w h20 h26 => hp.bk₀ w h20 (h26.trans hpa.saved.data)) accA rdA).mono fun pb hpb => ?_
  have prB := prepared_rebase hp.x20 hpa rfl rfl hpb
  have hcp₁ := rebase_cp pb hcp
  -- The second block.
  apply WP.seq
  refine (second_ok hcp₁ prB).mono fun pc hpc => ?_
  have x0c : pc.gpr .x0 = s.gpr .x0 :=
    (hpc.keep _ not_words_x0 (by decide) (by decide) (by decide)).trans (rebase_of (by decide))
  have x19c : pc.gpr .x19 = s.gpr .x2 := by rw [hpc.saved.len, rebase_of (by decide)]
  have x26c : pc.gpr .x26 = s.gpr .x1 := by rw [hpc.saved.data, rebase_of (by decide)]
  have fc : Frame [sr s, lowBuf s] s.mem pc.mem := by
    simpa only [sr, lowBuf, rebase_mem, rebase_of (show Reg.x0 ∉ accRegs by decide),
      rebase_of (show Reg.x3 ∉ accRegs by decide)] using hpc.frame
  have rwc := rword_of fc x0c (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.key _ (by simp)
    · exact (hp.key _ (by simp)).sub_right hlow)
  have rwb : ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword pb d = Poly.rword s d := by
    intro d hd
    rw [← rwa d hd]
    simp only [Poly.rword, hpb.mem, hpb.keep _ not_words_x0 (by decide) x0_not_poly]
  have accC := hpb.acc.frame (acc_regs_keep fun r hr =>
      (hpc.keep _ (not_words_preserved (acc_preserved r hr).1) (by
        intro he; rw [he] at hr; exact absurd hr (by decide)) (acc_preserved r hr).2.1
        (acc_preserved r hr).2.2.1).trans (rebase_acc hr))
    (fun d hd => (rwc d hd).trans (rwb d hd).symm)
  have rdC : Readable B₁ (16 * (l₁ + 5 * k₁)) pc :=
    readable_of hp.blk₁ hp.k0 hp.k1 (hpc.rd.trans (rebase_rd _ _)) (hpc.wr.trans (rebase_wr _ _)) x0c
  -- The second phase.
  apply WP.seq
  have x27c : pc.gpr .x27 = s.gpr .x27 :=
    (hpc.keep _ (not_words_preserved (by decide)) (by decide) (by decide) (by decide)).trans
      (rebase_of (by decide))
  refine (phaseWith_ok (W := B₁) (len := 16 * (l₁ + 5 * k₁)) (Nat.le_refl _) hpc.vec hpc.scalar
    hpc.table (hp.st₁ pc x19c x26c x27c) (fun w h20 h26 => hp.bk₁ w h20 (h26.trans x26c)) accC rdC).mono
    fun pd hpd => ?_
  have hcp₂ := rebase_cp pd hcp₁
  have hx₁ : (rebase s pb).gpr .x20 = (rebase s pb).gpr .x0 + 64#64 := by
    rw [rebase_of (by decide), rebase_of (by decide)]; exact hp.x20
  have seD := second_rebase hcp₁ hx₁ hpc (by rw [source_rebase]) (by rw [source_rebase])
    (by rw [rebase_of (show Reg.x27 ∉ accRegs by decide)]; exact hpd)
  rw [rebase_rebase] at seD hcp₂
  have hsr₂ : SrcOK r (rebase s pd) := srcOK_rebase hp.src pd
  -- The rest of the kernel's chunk.
  apply WP.seq
  refine (spill2_ok hcp₂ seD).mono fun pe hpe => ?_
  apply WP.seq
  refine (finishFrom_ok r hcp₂ hsr₂ hpe).mono fun pf hpf => ?_
  refine (lastFrom_ok r hcp₂ hsr₂ hpf).mono fun pg hpg => ?_
  have hacc : ∀ r ∈ accRegs, pg.gpr r = pd.gpr r := fun r hr =>
    (hpg.cs r (acc_preserved r hr).1 (acc_preserved r hr).2.1 (acc_preserved r hr).2.2.1).trans
      (rebase_acc hr)
  rw [rebase_congr s hacc]
  refine ⟨hpg, ?_⟩
  -- The accumulator.
  have x0g : pg.gpr .x0 = s.gpr .x0 := hpg.x0.trans (rebase_of (by decide))
  have fg : Frame [sr s, scalarBuf s, VG.Proof.ChaCha20.AArch64.Mixed8.dr s] s.mem pg.mem := by
    simpa only [sr, scalarBuf, VG.Proof.ChaCha20.AArch64.Mixed8.dr, rebase_mem,
      rebase_of (show Reg.x0 ∉ accRegs by decide), rebase_of (show Reg.x1 ∉ accRegs by decide),
      rebase_of (show Reg.x3 ∉ accRegs by decide)] using hpg.frame
  have rwg := rword_of fg x0g (hkey _ (fun r hr => hr))
  have rwd : ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword pd d = Poly.rword s d := by
    intro d hd
    rw [← rwc d hd]
    simp only [Poly.rword, hpd.mem, hpd.keep _ not_words_x0 (by decide) x0_not_poly]
  have accG := hpd.acc.frame (acc_regs_keep hacc) (fun d hd => (rwg d hd).trans (rwd d hd).symm)
  -- The bytes absorbed.
  have bA : bytesAt pa.mem B₀ (16 * (l₀ + 5 * k₀)) = bytesAt s.mem B₀ (16 * (l₀ + 5 * k₀)) :=
    bytesAt_frame hpa.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.win₀ _ (by simp)) hp.le₀
  have bC : bytesAt pc.mem B₁ (16 * (l₁ + 5 * k₁)) = bytesAt s.mem B₁ (16 * (l₁ + 5 * k₁)) :=
    bytesAt_frame fc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.win₁ _ (by simp)
      · exact (hp.win₁ _ (by simp)).sub_right hlow) hp.le₁
  rw [bC, bA] at accG
  have hl : (bytesAt s.mem B₀ (16 * (l₀ + 5 * k₀))).length % 16 = 0 := by
    rw [Poly1305.length_bytesAt]; omega
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
    Offset.sub_base _ (by omega)
  have hb (k : Nat) (hk : k ≤ 1) : ∀ d, d + 8 ≤ 16 * (1 + 5 * 3) →
      InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (256 * k) + BitVec.ofNat 64 d) 8 := by
    intro d hd
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.blk _ (by omega)
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
  have pre : ChunkPreW (start enc 0) (start enc 1) (back enc 0) (back enc 1) .x27
      (B + BitVec.ofNat 64 (256 * 0)) (B + BitVec.ofNat 64 (256 * 1)) (16 * (1 + 5 * 3)) (16 * (1 + 5 * 3)) s :=
    ⟨hp.cp, hp.x20, hst 0 (by decide), hst 1 (by decide), hbk 0 (by decide), hbk 1 (by decide), hp.src,
      hb 0 (by decide), hb 1 (by decide), hp.k0, hp.k1,
      fun r hr => (hp.win r hr).sub_left (hwin 0 (by decide)),
      fun r hr => (hp.win r hr).sub_left (hwin 1 (by decide)), by decide, by decide, hp.key⟩
  refine (chunkWith_ok s pre ha).mono fun g ⟨hg, hag⟩ => ⟨hg, ?_⟩
  have e : bytesAt s.mem (B + BitVec.ofNat 64 (256 * 0)) (16 * (1 + 5 * 3)) ++
      bytesAt s.mem (B + BitVec.ofNat 64 (256 * 1)) (16 * (1 + 5 * 3)) = bytesAt s.mem B 512 := by
    rw [show B + BitVec.ofNat 64 (256 * 0) = B by simp, Nat.mul_one,
      show 16 * (1 + 5 * 3) = 256 from rfl, ← Poly1305.bytesAt_add]
  rw [e] at hag
  exact hag

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch
