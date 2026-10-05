import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitch
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Poly
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Xor

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Phase`. -/
section

/-!
# ChaCha20 and Poly1305 together (AArch64): a counted phase

`Stitch.phase`: five double rounds of the eight-block ChaCha20 kernel, as in
`Mixed8.counted_phase_ok`, and sixteen blocks of Poly1305 (`Poly.block_absorb`)
from `W`. The rounds write only the vector registers, the registers of the
integer block (`Words`) and `x1`; the blocks only `Poly.regs`; neither
writes memory, so each preserves what the other computes.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch
open VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0)
open VG.Proof.ChaCha20.AArch64.Mixed8 (N C RI)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps Keeps.gpr' Keeps.trans)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

abbrev Acc := VG.Proof.ChaCha20Poly1305.AArch64.Poly.Acc

theorem words_not_poly {r : Reg} (h : Words r) : r ∉ Poly.regs := by
  obtain ⟨k, hk, rfl⟩ := h
  exact (show ∀ k < 16, VG.Impl.ChaCha20.AArch64.wreg k ∉ Poly.regs by decide) k hk

theorem x0_not_poly : Reg.x0 ∉ Poly.regs := by decide
theorem x1_not_poly : Reg.x1 ∉ Poly.regs := by decide

/-- The blocks from `W` are readable, and so is the key. -/
structure Readable (W : Addr) (s : State) : Prop where
  blk : ∀ d, d + 8 ≤ 256 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8
  k0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r0Off) 8
  k1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r1Off) 8

theorem Readable.of {W : Addr} {s u : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s) (hrd : u.rd = s.rd)
    (hwr : u.wr = s.wr) (hx0 : u.gpr .x0 = s.gpr .x0) : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W u :=
  ⟨fun d hd => by rw [hrd, hwr]; exact h.blk d hd, by rw [hrd, hwr, hx0]; exact h.k0,
    by rw [hrd, hwr, hx0]; exact h.k1⟩

/-- The accumulator is unchanged by code that writes neither its registers,
`x0`, nor memory. -/
theorem Acc.of {R a : Nat} {s u : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a s)
    (hg : ∀ r ∈ [Reg.x0, .x21, .x22, .x23], u.gpr r = s.gpr r) (hm : u.mem = s.mem) :
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a u := by
  have e : ∀ d, Poly.rword u d = Poly.rword s d := fun d => by
    simp only [Poly.rword, hg .x0 (by decide), hm]
  have hv : Poly.hval u = Poly.hval s := by
    simp only [Poly.hval, hg .x21 (by decide), hg .x22 (by decide), hg .x23 (by decide)]
  exact ⟨by rw [hv]; exact h.h, by rw [hg .x23 (by decide)]; exact h.h2,
    by simp only [Poly.rval, e]; exact h.key, by rw [e]; exact h.k0, by rw [e]; exact h.k1⟩

theorem bytesAt_succ (m : Mem) (W : Addr) (n : Nat) :
    bytesAt m W (16 * (n + 1)) = bytesAt m W (16 * n) ++
      bytesAt m (W + BitVec.ofNat 64 (16 * n)) 16 := by
  rw [Nat.mul_succ, Poly1305.bytesAt_add]

/-- The `n + 1`st block from `W`. -/
theorem absorb_next {R a : Nat} {W : Addr} {n : Nat} (hn : 16 * n + 16 ≤ 256) {s : State}
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem W (16 * n))) s)
    (hp : s.gpr .x20 = W + BitVec.ofNat 64 (16 * n)) (hr : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s) :
    WP isa (.block Poly.block) s fun u =>
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem W (16 * (n + 1)))) u ∧
      u.gpr .x20 = W + BitVec.ofNat 64 (16 * (n + 1)) ∧ Keeps Poly.regs s u := by
  have hb (d : Nat) (hd : d + 8 ≤ 16) :
      InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 d) 8 := by
    rw [hp, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hr.blk _ (by omega)
  refine (Poly.block_absorb s ha (hb 0 (by decide)) (hb 8 (by decide)) hr.k0 hr.k1).mono
    fun u ⟨hu, hx, hk⟩ => ⟨?_, ?_, hk⟩
  · have hl : (bytesAt s.mem W (16 * n)).length % 16 = 0 := by
      rw [Poly1305.length_bytesAt]; omega
    rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.bytesAt_succ, Poly1305.absorbAll_append hl, ← hp]
    exact hu
  · rw [hx, hp, BitVec.add_assoc]
    change W + (BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 16) = _
    rw [← BitVec.ofNat_add, Nat.mul_succ]

/-- Code that keeps `Poly.regs`, memory and the regions. -/
theorem keeps_frame {s u : State} (h : Keeps Poly.regs s u) {r : Reg} (hr : r ∉ Poly.regs) :
    u.gpr r = s.gpr r := h.1 r hr

/-- After `i` iterations of the loop. -/
structure PI (blocks : Nat → VG.Spec.ChaCha20.State) (v : VG.Spec.ChaCha20.State)
    (R a : Nat) (W : Addr) (s₀ s : State) (i : Nat) : Prop where
  vec : N (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun b => Nat.repeat innerBlock i (blocks b))) s
  scalar : VG.Proof.ChaCha20.AArch64.Mixed8.C (Nat.repeat (fun x => innerBlock (innerBlock x)) i v) s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → r ≠ .x1 → r ∉ Poly.regs → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  table : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  ptr : s.gpr .x20 = W + BitVec.ofNat 64 (16 * (1 + 3 * i))
  acc : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s₀.mem W (16 * (1 + 3 * i)))) s

theorem PI.readable {blocks v R a W s₀ s i} (h : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.PI blocks v R a W s₀ s i) (hr : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s₀) :
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s := hr.of h.rd h.wr (h.keep _ not_words_x0 (by decide) VG.Proof.ChaCha20Poly1305.AArch64.Stitch.x0_not_poly)

/-- Three blocks, after the double round. -/
theorem absorb3_ok {R a : Nat} {W : Addr} {n : Nat} (hn : 16 * n + 48 ≤ 256) {s : State}
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem W (16 * n))) s)
    (hp : s.gpr .x20 = W + BitVec.ofNat 64 (16 * n)) (hr : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s) :
    WP isa (.block absorb3) s fun u =>
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem W (16 * (n + 3)))) u ∧
      u.gpr .x20 = W + BitVec.ofNat 64 (16 * (n + 3)) ∧ Keeps Poly.regs s u ∧
      u.v = s.v ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  have hv : ∀ i ∈ absorb3, vdstOf i = none := by decide +kernel
  suffices main : WP isa (.block absorb3) s fun u =>
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem W (16 * (n + 3)))) u ∧
      u.gpr .x20 = W + BitVec.ofNat 64 (16 * (n + 3)) ∧ Keeps Poly.regs s u from
    (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv main).mono
      fun u ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩
  unfold absorb3
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.absorb_next (by omega) ha hp hr) fun s₁ ⟨a₁, p₁, k₁⟩ => ?_)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have hr₁ : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s₁ := hr.of k₁.2.2.1 k₁.2.2.2 (k₁.gpr' (r := .x0))
  rw [← hm₁] at a₁
  refine WP.block_append (WP.mono (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.absorb_next (by omega) a₁ p₁ hr₁) fun s₂ ⟨a₂, p₂, k₂⟩ => ?_)
  have hm₂ : s₂.mem = s.mem := k₂.2.1.trans hm₁
  have hr₂ : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s₂ := hr₁.of k₂.2.2.1 k₂.2.2.2 (k₂.gpr' (r := .x0))
  rw [hm₁, ← hm₂] at a₂
  refine WP.mono (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.absorb_next (by omega) a₂ p₂ hr₂) fun u ⟨a₃, p₃, k₃⟩ => ?_
  rw [hm₂] at a₃
  exact ⟨a₃, p₃, ((k₁.trans k₂).trans k₃).mono (by
    intro r h; simp only [List.mem_append] at h; rcases h with (h | h) | h <;> exact h)⟩

/-- The loop body, from `PI … i` to `PI … (i + 1)`. -/
theorem iter_ok {blocks v R a W s₀ s} {i : Nat} (hi : i < 5) (hr : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s₀)
    (h : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.PI blocks v R a W s₀ s i) :
    WP isa (.seq (VG.Impl.ChaCha20.AArch64.Mixed8.parallelRound sve) (.block (absorb3 ++ ([.subImm .x .x1 .x1 1] : List Instr)))) s
      fun u => VG.Proof.ChaCha20Poly1305.AArch64.Stitch.PI blocks v R a W s₀ u (i + 1) ∧ u.gpr .x1 = s.gpr .x1 - 1#64 := by
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.parallelRound_ok h.vec h.scalar h.table).mono
    fun b ⟨hb, hc, hsp, ht⟩ => ?_
  have nw (r : Reg) (hr' : r ∈ Poly.regs) : ¬ Words r := fun hw => VG.Proof.ChaCha20Poly1305.AArch64.Stitch.words_not_poly hw hr'
  have hbacc : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt b.mem W (16 * (1 + 3 * i)))) b := by
    rw [hc.mem, h.mem]
    exact h.acc.of (fun r hr' => hc.keep r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · exact not_words_x0
      all_goals exact nw _ (by decide))) hc.mem
  have hbp : b.gpr .x20 = W + BitVec.ofNat 64 (16 * (1 + 3 * i)) :=
    (hc.keep _ (nw _ (by decide))).trans h.ptr
  have hbr : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W b := (h.readable hr).of hc.rd hc.wr (hc.keep _ not_words_x0)
  apply WP.block_append
  refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.absorb3_ok (n := 1 + 3 * i) (by omega) hbacc hbp hbr).mono
    fun c ⟨hca, hcp, hck, hcv, hcsp, hcr, hcw⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨c.write .x .x1 (c.gpr .x1 - BitVec.ofNat 64 1), ?_, WP.block_nil ?_⟩
  · simpa only [State.read, BitVec.setWidth_eq] using
      exec_subImm_x (s := c) (d := .x1) (n := .x1) (imm := 1) (by decide)
  · have hcm : c.mem = s₀.mem := hck.2.1.trans (hc.mem.trans h.mem)
    have hx1 : c.gpr .x1 = b.gpr .x1 := hck.gpr' (r := .x1)
    refine ⟨⟨?_, ?_, hcm, hcr.trans (hc.rd.trans h.rd), hcw.trans (hc.wr.trans h.wr), ?_,
      hcsp.trans (hsp.trans h.sp), ?_, ?_, ?_⟩, ?_⟩
    · intro k j hj
      rw [RegUpd.v_write, hcv]
      exact hb k j hj
    · intro k hk
      rw [RegUpd.gpr_write_of_ne c .x _ (by intro he; exact not_words_x1 ⟨k, hk, he.symm⟩),
        hck.gpr' (r := VG.Impl.ChaCha20.AArch64.wreg k) (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.words_not_poly ⟨k, hk, rfl⟩)]
      exact hc.holds k hk
    · intro r hw h1 hp
      rw [RegUpd.gpr_write_of_ne c .x _ h1, hck.gpr' (r := r) hp, hc.keep r hw]
      exact h.keep r hw h1 hp
    · rw [RegUpd.v_write, hcv, ht]
    · rw [RegUpd.gpr_write_of_ne c .x _ (by decide), hcp,
        show 1 + 3 * i + 3 = 1 + 3 * (i + 1) by omega]
    · have e : 16 * (1 + 3 * i + 3) = 16 * (1 + 3 * (i + 1)) := by omega
      rw [hc.mem, h.mem, e] at hca
      exact hca.of (fun r hr' => RegUpd.gpr_write_of_ne c .x _ (by
        intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
    · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hx1, hc.keep _ not_words_x1]

theorem write_v (s : State) (sz : Size) (d : Reg) (x : BitVec sz.bits) : (s.write sz d x).v = s.v := rfl

/-- After the phase. -/
structure Done (blocks : Nat → VG.Spec.ChaCha20.State) (v : VG.Spec.ChaCha20.State)
    (R a : Nat) (W : Addr) (restore : Reg) (s u : State) : Prop where
  vec : N (VG.Proof.ChaCha20.AArch64.Rows6.pack
    (fun b => Nat.repeat innerBlock 5 (blocks b))) u
  scalar : VG.Proof.ChaCha20.AArch64.Mixed8.C (Nat.repeat innerBlock 10 v) u
  mem : u.mem = s.mem
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  table : u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  keep : ∀ r, ¬ Words r → r ≠ .x1 → r ∉ Poly.regs → u.gpr r = s.gpr r
  x20 : u.gpr .x20 = s.gpr .x0 + 64#64
  x1 : u.gpr .x1 = u.gpr restore
  acc : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem W 256)) u

theorem phase_ok {blocks : Nat → VG.Spec.ChaCha20.State} {v : VG.Spec.ChaCha20.State}
    {R a : Nat} {W : Addr} {start : Instr} {restore : Reg} {s : State}
    (hn : N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : VG.Proof.ChaCha20.AArch64.Mixed8.C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table)
    (hstart : exec start s = some (s.write .x .x20 W))
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a s) (hr : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s) :
    WP isa (phase sve start restore) s (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Done blocks v R a W restore s) := by
  unfold phase
  apply WP.seq
  -- `x20` set, the first block, and the counter.
  let s₁ := s.write .x .x20 W
  have ha₁ : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s₁.mem W (16 * 0))) s₁ := by
    have e : bytesAt s₁.mem W (16 * 0) = [] := rfl
    rw [e, Poly1305.absorbAll_nil]
    exact ha.of (fun r hr' => RegUpd.gpr_write_of_ne s .x _ (by
      intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
  have hr₁ : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable W s₁ := hr.of rfl rfl (RegUpd.gpr_write_of_ne s .x _ (by decide))
  have hp₁ : s₁.gpr .x20 = W + BitVec.ofNat 64 (16 * 0) := by
    simp only [s₁, RegUpd.gpr_write_self, BitVec.setWidth_eq, Nat.mul_zero, BitVec.add_zero]
  have hv : ∀ i ∈ Poly.block, vdstOf i = none := by decide +kernel
  apply WP.block_cons_iff.mpr
  refine ⟨s₁, hstart, ?_⟩
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv
    (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.absorb_next (n := 0) (by decide) ha₁ hp₁ hr₁)).mono fun s₂ ⟨⟨a₂, p₂, k₂⟩, v₂, sp₂, rd₂, wr₂⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨s₂.write .x .x1 ((5 : BitVec 16).setWidth 64), ?_, WP.block_nil ?_⟩
  · simp only [exec, Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, show 0 < 64 from by decide, ite_true]
  -- The loop.
  · let s₃ := s₂.write .x .x1 5#64
    have nx20 : ∀ r, r ∉ Poly.regs → r ≠ .x20 := fun r h he => h (he ▸ by decide)
    have g₂ : ∀ r, r ∉ Poly.regs → s₂.gpr r = s.gpr r := fun r h =>
      (k₂.gpr' (r := r) h).trans (RegUpd.gpr_write_of_ne s .x _ (nx20 r h))
    have hm₁ : s₁.mem = s.mem := rfl
    have hm₂ : s₂.mem = s.mem := k₂.2.1.trans hm₁
    have h0 : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.PI blocks v R a W s s₃ 0 := by
      refine ⟨?_, ?_, hm₂, rd₂, wr₂, ?_, sp₂, ?_, ?_, ?_⟩
      · intro k j hj; rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.write_v, v₂]; exact hn k j hj
      · intro k hk
        rw [RegUpd.gpr_write_of_ne s₂ .x _ (by intro he; exact not_words_x1 ⟨k, hk, he.symm⟩),
          g₂ _ (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.words_not_poly ⟨k, hk, rfl⟩)]
        exact hc k hk
      · intro r _ h1 hp; rw [RegUpd.gpr_write_of_ne s₂ .x _ h1, g₂ r hp]
      · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.write_v, v₂]; exact ht
      · rw [RegUpd.gpr_write_of_ne s₂ .x _ (by decide), p₂]
      · rw [hm₁] at a₂
        exact a₂.of (fun r hr' => RegUpd.gpr_write_of_ne s₂ .x _ (by
          intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
    apply WP.seq
    let Inv : Nat → State → Prop := fun n u =>
      ∃ i, i < 5 ∧ n = 5 - i ∧ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.PI blocks v R a W s u i ∧ u.gpr .x1 = BitVec.ofNat 64 (5 - i)
    have hstep : ∀ n u, Inv n u → WP isa
        (.seq (VG.Impl.ChaCha20.AArch64.Mixed8.parallelRound sve)
          (.block (absorb3 ++ [.subImm .x .x1 .x1 1]))) u (fun w =>
        (eval (.nonzero .x .x1) w = some false ∧ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.PI blocks v R a W s w 5) ∨
        (eval (.nonzero .x .x1) w = some true ∧ ∃ m < n, Inv m w)) := by
      rintro n u ⟨i, hi, rfl, hu, hcount⟩
      refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.iter_ok hi hr hu).mono fun w ⟨hw, hx⟩ => ?_
      have hwc : w.gpr .x1 = BitVec.ofNat 64 (5 - (i + 1)) := by
        rw [hx, hcount, Offset.ofNat_sub_ofNat (by omega : 1 ≤ 5 - i)]
        simp only [Nat.sub_sub]
      have he : eval (.nonzero .x .x1) w = some (BitVec.ofNat 64 (5 - (i + 1)) != 0) := by
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hwc]
      by_cases hl : i + 1 = 5
      · exact .inl ⟨by rw [he, hl]; rfl, hl ▸ hw⟩
      · have hn0 : BitVec.ofNat 64 (5 - (i + 1)) ≠ 0 := by
          intro hz
          have hz' := congrArg BitVec.toNat hz
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 5 - (i + 1) < 2 ^ 64)] at hz'
          change 5 - (i + 1) = 0 at hz'
          omega
        exact .inr ⟨by rw [he]; simpa using hn0, 5 - (i + 1), by omega, i + 1, by omega, rfl, hw, hwc⟩
    refine (WP.loop (M := isa) Inv hstep 5 s₃ ⟨0, by decide, rfl, h0, rfl⟩).mono fun w hw => ?_
    -- `x20` and `x1` restored.
    let t := w.write .x .x20 (w.gpr .x0 + BitVec.ofNat 64 64)
    have hx0 : w.gpr .x0 = s.gpr .x0 := hw.keep _ not_words_x0 (by decide) (by decide)
    apply WP.block_cons_iff.mpr
    refine ⟨t, ?_, ?_⟩
    · simpa only [State.read, BitVec.setWidth_eq] using
        exec_addImm_x (s := w) (d := .x20) (n := .x0) (imm := 64) (by decide)
    apply WP.block_cons_iff.mpr
    refine ⟨t.write .x .x1 (t.gpr restore), ?_, WP.block_nil ?_⟩
    · simpa only [State.read, BitVec.setWidth_eq, BitVec.add_zero] using
        exec_addImm_x (s := t) (d := .x1) (n := restore) (imm := 0) (by decide)
    have g (r : Reg) (h1 : r ≠ .x1) (h20 : r ≠ .x20) :
        (t.write .x .x1 (t.gpr restore)).gpr r = w.gpr r := by
      rw [RegUpd.gpr_write_of_ne t .x _ h1, RegUpd.gpr_write_of_ne w .x _ h20]
    refine ⟨fun k j hj => hw.vec k j hj, ?_, hw.mem, hw.rd, hw.wr, hw.sp, hw.table, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [g _ (by intro he; exact not_words_x1 ⟨k, hk, he.symm⟩)
        (nx20 _ (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.words_not_poly ⟨k, hk, rfl⟩))]
      have he (f : VG.Spec.ChaCha20.State → VG.Spec.ChaCha20.State) (x : VG.Spec.ChaCha20.State) :
          Nat.repeat (fun x => f (f x)) 5 x = Nat.repeat f 10 x := rfl
      have hs := hw.scalar k hk
      rw [he innerBlock v] at hs
      exact hs
    · intro r hw' h1 hp; rw [g r h1 (nx20 r hp)]; exact hw.keep r hw' h1 hp
    · rw [RegUpd.gpr_write_of_ne t .x _ (by decide), RegUpd.gpr_write_self, BitVec.setWidth_eq, hx0]
    · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      by_cases h1 : restore = .x1
      · subst h1; rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      · rw [RegUpd.gpr_write_of_ne t .x _ h1]
    · have e : 16 * (1 + 3 * 5) = 256 := rfl
      have ha' := hw.acc
      rw [e] at ha'
      exact ha'.of (fun r hr' => g r (by intro he; rw [he] at hr'; exact absurd hr' (by decide))
        (by intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl


end VG.Proof.ChaCha20Poly1305.AArch64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Chunk`. -/
section

/-!
# ChaCha20 and Poly1305 together (AArch64): a chunk

`Stitch.chunk`: the eight-block kernel's chunk (`Mixed8.chunk_ok`), with
its two phases replaced by `Stitch.phase`, which also absorb 512 bytes from
`B` into the accumulator.

The kernel's proofs describe each stage relative to the state `s₀` at the
start of the chunk, and say that the registers they do not use keep their
values from `s₀`. The phases change the accumulator's registers (`accRegs`),
which the kernel does not use, so after a phase the kernel's stages are
applied relative to `rebase s₀ u`: `s₀` with the accumulator's registers of
`u`.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP Prepared Second Spilled2 Finished Chunked source sr
  lowBuf scalarBuf prepare_ok second_ok spill2_ok finish_ok last_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

/-- The accumulator's registers, apart from the pointer `x20`. -/
abbrev accRegs : List Reg := [.x21, .x22, .x23, .x24, .x25, .x27, .x28, .x30]

/-- `s₀` with the accumulator's registers of `u`. -/
def rebase (s₀ u : State) : State :=
  { s₀ with gpr := fun r => if r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs then u.gpr r else s₀.gpr r }

theorem rebase_of {s₀ u : State} {r : Reg} (h : r ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr r = s₀.gpr r := by
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase, h, ite_false]

theorem rebase_acc {s₀ u : State} {r : Reg} (h : r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr r = u.gpr r := by
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase, h, ite_true]

@[simp] theorem rebase_mem (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).mem = s₀.mem := rfl
@[simp] theorem rebase_rd (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).rd = s₀.rd := rfl
@[simp] theorem rebase_wr (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).wr = s₀.wr := rfl
@[simp] theorem rebase_sp (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).sp = s₀.sp := rfl

theorem acc_preserved : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, r ∈ preserved ∧ r ≠ .x19 ∧ r ≠ .x26 ∧ r ≠ .x20 := by
  decide

theorem rebase_cp {s₀ : State} (u : State) (hp : CP s₀) : CP (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) := by
  have e0 : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x0 = s₀.gpr .x0 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
  have e1 : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x1 = s₀.gpr .x1 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
  have e3 : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x3 = s₀.gpr .x3 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
  have e20 : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x20 = s₀.gpr .x20 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
  obtain ⟨h20, hrd, hvr, hc, hb, hd, h1, h2, h3⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [VG.Proof.ChaCha20.AArch64.Mixed8.sr, VG.Proof.ChaCha20.AArch64.Mixed8.br,
      VG.Proof.ChaCha20.AArch64.Mixed8.dr, e0, e1, e3, e20] <;>
    first | exact h20 | exact hrd | exact hvr | exact hc | exact hb | exact hd | exact h1 | exact h2 | exact h3

theorem source_rebase (s₀ u : State) : source (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = source s₀ := by
  simp only [source, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x0 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide)]
  rfl

/-- Where the chunk's data starts, relative to the bytes it absorbs from `B`. -/
abbrev dataOf (enc : Bool) (B : Addr) : Addr := B + BitVec.ofNat 64 (if enc then 512 else 0)

theorem start_ok (enc : Bool) (half : Nat) (hh : half ≤ 1) (B : Addr) (s : State)
    (hx : s.gpr .x26 = VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf enc B) :
    exec (start enc half) s = some (s.write .x .x20 (B + BitVec.ofNat 64 (256 * half))) := by
  cases enc
  · simp only [start, Bool.false_eq_true, ite_false]
    rw [exec_addImm_x (by omega)]
    simp only [State.read, BitVec.setWidth_eq, hx, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf, Bool.false_eq_true, ite_false,
      BitVec.add_zero]
  · simp only [start, ite_true]
    rw [exec_subImm_x (by omega)]
    simp only [State.read, BitVec.setWidth_eq, hx, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf, ite_true]
    rw [Offset.add_ofNat_sub B (by omega), show 512 - (512 - 256 * half) = 256 * half by omega]

/-- The phase's precondition, from a stage of the kernel. -/
theorem readable_of {B : Addr} {s₀ s : State} (hr : ∀ d, d + 8 ≤ 512 →
      InRegions (s₀.rd ++ s₀.wr) (B + BitVec.ofNat 64 d) 8)
    (hk0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 Poly.r0Off) 8)
    (hk1 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 Poly.r1Off) 8)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hx0 : s.gpr .x0 = s₀.gpr .x0)
    (half : Nat) (hh : half ≤ 1) :
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable (B + BitVec.ofNat 64 (256 * half)) s := by
  refine ⟨fun d hd => ?_, by rw [hrd, hwr, hx0]; exact hk0, by rw [hrd, hwr, hx0]; exact hk1⟩
  rw [hrd, hwr, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hr _ (by omega)

/-- After the first phase. -/
theorem prepared_rebase {blocks : Nat → VG.Spec.ChaCha20.State} {v : VG.Spec.ChaCha20.State}
    {R a : Nat} {W : Addr} {s₀ s u : State}
    (hx : s₀.gpr .x20 = s₀.gpr .x0 + 64#64) (h : Prepared s₀ s)
    (hb : blocks = fun j => Nat.repeat innerBlock 0 (ctr (source s₀) j))
    (hv : v = Nat.repeat innerBlock (2 * 0) (ctr (source s₀) 6))
    (hd : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Done blocks v R a W .x26 s u) : Prepared (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) u 5 := by
  subst hb hv
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ not_words_x0 (by decide) (by decide)
  have hsrc : source u = source s := by
    simp only [source, hd.mem, hd.keep _ not_words_x0 (by decide) VG.Proof.ChaCha20Poly1305.AArch64.Stitch.x0_not_poly]
  refine ⟨?_, hd.table, ?_, ?_, ?_, ?_, hd.rd.trans h.rd, hd.wr.trans h.wr, hd.sp.trans h.sp, ?_⟩
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase]; exact hd.vec
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase]; exact hd.scalar
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase, hsrc]; exact h.cnt
  · refine ⟨?_, ?_⟩
    · rw [hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide), VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)]
      exact h.saved.len
    · rw [hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide), VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)]
      exact h.saved.data
  · intro r hw h19 h26
    by_cases ha : r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs
    · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_acc ha]
    rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of ha]
    by_cases h1 : r = .x1
    · subst r
      rw [hd.x1, hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide)]
      exact h.saved.data
    by_cases h20 : r = .x20
    · subst r; rw [hd.x20, hx0, hx]
    have hp' : r ∉ Poly.regs := by
      intro hm
      rcases List.mem_cons.mp hm with h' | h'
      · exact h20 h'
      · exact ha h'
    rw [hd.keep r hw h1 hp']
    exact h.keep r hw h19 h26
  · rw [hd.mem]
    simpa only [sr, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_mem, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x0 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide)] using h.frame

theorem not_poly {r : Reg} (ha : r ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs) (h20 : r ≠ .x20) : r ∉ Poly.regs := by
  intro hm
  rcases List.mem_cons.mp hm with h' | h'
  · exact h20 h'
  · exact ha h'

/-- After the second phase. -/
theorem second_rebase {blocks : Nat → VG.Spec.ChaCha20.State} {v : VG.Spec.ChaCha20.State}
    {R a : Nat} {W : Addr} {s₀ s u : State} (hp : CP s₀)
    (hx : s₀.gpr .x20 = s₀.gpr .x0 + 64#64) (h : Second s₀ s)
    (hb : blocks = fun j => Nat.repeat innerBlock 5 (ctr (source s₀) j))
    (hv : v = Nat.repeat innerBlock (2 * 0) (ctr (source s₀) 7))
    (hd : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Done blocks v R a W .x20 s u) : Second (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) u 5 := by
  subst hb hv
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ not_words_x0 (by decide) (by decide) (by decide)
  have hsrc : source u = source s := by
    simp only [source, hd.mem, hd.keep _ not_words_x0 (by decide) VG.Proof.ChaCha20Poly1305.AArch64.Stitch.x0_not_poly]
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
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase]; exact hvec
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase]; exact hd.scalar
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase, hsrc]; exact h.cnt
  · refine ⟨?_, ?_⟩
    · rw [hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide), VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)]
      exact h.saved.len
    · rw [hd.keep _ (not_words_preserved (by decide)) (by decide) (by decide), VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)]
      exact h.saved.data
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase, hd.mem, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x3 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide)]; exact h.first
  · intro r hw h1 h19 h26
    by_cases ha : r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs
    · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_acc ha]
    rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of ha]
    by_cases h20' : r = .x20
    · subst r; rw [h20, ← hp.x20]
    rw [hd.keep r hw h1 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.not_poly ha h20')]
    exact h.keep r hw h1 h19 h26
  · rw [hd.x1, h20, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)]
  · rw [hd.mem]
    simpa only [sr, lowBuf, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_mem, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x0 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide),
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x3 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide)] using h.frame

theorem rebase_rebase (s₀ u w : State) : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) w = VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ w := by
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase]
  congr 1
  funext r
  by_cases h : r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs <;> simp only [h, ite_true, ite_false]

theorem rebase_congr (s₀ : State) {u w : State} (h : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, u.gpr r = w.gpr r) :
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u = VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ w := by
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase]
  congr 1
  funext r
  by_cases hr : r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs <;> simp only [hr, ite_true, ite_false, h r]

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
    (hx0 : u.gpr .x0 = s.gpr .x0) (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s).Disjoint r) (d : Nat)
    (hd' : d = Poly.r0Off ∨ d = Poly.r1Off) : Poly.rword u d = Poly.rword s d := by
  simp only [Poly.rword, hx0]
  refine hf.readW ?_ hd (by decide)
  rcases hd' with rfl | rfl
  · exact Offset.contains _ (by decide) (by decide) (by decide)
  · exact Offset.contains _ (by decide : 224 ≤ 232) (by decide) (by decide)

theorem Acc.frame {R a : Nat} {s u : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a s)
    (hg : ∀ r ∈ [Reg.x21, .x22, .x23], u.gpr r = s.gpr r)
    (hk : ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword u d = Poly.rword s d) :
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a u := by
  have hv : Poly.hval u = Poly.hval s := by
    simp only [Poly.hval, hg .x21 (by decide), hg .x22 (by decide), hg .x23 (by decide)]
  exact ⟨by rw [hv]; exact h.h, by rw [hg .x23 (by decide)]; exact h.h2,
    by simp only [Poly.rval, hk _ (.inl rfl), hk _ (.inr rfl)]; exact h.key,
    by rw [hk _ (.inl rfl)]; exact h.k0, by rw [hk _ (.inr rfl)]; exact h.k1⟩

/-- What a chunk needs. -/
structure ChunkPre (enc : Bool) (B : Addr) (s : State) : Prop where
  cp : CP s
  x20 : s.gpr .x20 = s.gpr .x0 + 64#64
  x1 : s.gpr .x1 = VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf enc B
  blk : ∀ d, d + 8 ≤ 512 → InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 d) 8
  k0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r0Off) 8
  k1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r1Off) 8
  win : ∀ r ∈ [sr s, scalarBuf s], (⟨B, 512⟩ : Region).Disjoint r
  key : ∀ r ∈ [sr s, scalarBuf s, VG.Proof.ChaCha20.AArch64.Mixed8.dr s], (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s).Disjoint r

/-- The key's words, in a state that has written only regions disjoint from
the key since `s`. -/
theorem rword_of {rs : List Region} {s u : State} (hf : Frame rs s.mem u.mem)
    (hx0 : u.gpr .x0 = s.gpr .x0) (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s).Disjoint r) :
    ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword u d = Poly.rword s d :=
  fun d hd' => VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rword_frame hf hx0 hd d hd'

theorem acc_regs_keep {s u : State} (h : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, u.gpr r = s.gpr r) :
    ∀ r ∈ [Reg.x21, .x22, .x23], u.gpr r = s.gpr r := fun r hr =>
  h r ((show ∀ r ∈ [Reg.x21, .x22, .x23], r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide) r hr)

theorem chunk_ok (enc : Bool) {R a : Nat} {B : Addr} (s : State) (hp : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.ChunkPre enc B s)
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a s) :
    WP isa (chunk sve enc) s fun g =>
      VG.Proof.ChaCha20.AArch64.Mixed8.Chunked (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s g) g ∧ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem B 512)) g := by
  have hcp := hp.cp
  have hkey (rs : List Region) (h : ∀ r ∈ rs, r ∈ [sr s, scalarBuf s, VG.Proof.ChaCha20.AArch64.Mixed8.dr s]) :
      ∀ r ∈ rs, (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s).Disjoint r := fun r hr => hp.key r (h r hr)
  have hlow : (lowBuf s).Sub (scalarBuf s) := Region.sub_prefix (by decide : 64 ≤ 128)
  unfold chunk
  apply WP.seq
  refine (prepare_ok s hcp).mono fun pa hpa => ?_
  have x0a : pa.gpr .x0 = s.gpr .x0 := hpa.keep _ not_words_x0 (by decide) (by decide)
  have x26a : pa.gpr .x26 = VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf enc B := hpa.saved.data.trans hp.x1
  have rwa := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rword_of hpa.frame x0a (hkey _ (by simp))
  have accA : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a pa := ha.frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_regs_keep fun r hr =>
    hpa.keep _ (not_words_preserved (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).1) (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.1
      (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.2.1) rwa
  have rdA : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable (B + BitVec.ofNat 64 (256 * 0)) pa :=
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.readable_of hp.blk hp.k0 hp.k1 hpa.rd hpa.wr x0a 0 (by decide)
  -- The first phase.
  apply WP.seq
  refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.phase_ok (W := B + BitVec.ofNat 64 (256 * 0)) hpa.vec hpa.scalar hpa.table
    (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.start_ok enc 0 (by decide) B pa x26a) accA rdA).mono fun pb hpb => ?_
  have prB := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.prepared_rebase hp.x20 hpa rfl rfl hpb
  have hcp₁ := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_cp pb hcp
  -- The second block.
  apply WP.seq
  refine (second_ok hcp₁ prB).mono fun pc hpc => ?_
  have x0c : pc.gpr .x0 = s.gpr .x0 :=
    (hpc.keep _ not_words_x0 (by decide) (by decide) (by decide)).trans (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide))
  have x26c : pc.gpr .x26 = VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf enc B := by
    rw [hpc.saved.data, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)]; exact hp.x1
  have fc : Frame [sr s, lowBuf s] s.mem pc.mem := by
    simpa only [sr, lowBuf, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_mem, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x0 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide),
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x3 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide)] using hpc.frame
  have rwc := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rword_of fc x0c (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.key _ (by simp)
    · exact (hp.key _ (by simp)).sub_right hlow)
  have rwb : ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword pb d = Poly.rword s d := by
    intro d hd
    rw [← rwa d hd]
    simp only [Poly.rword, hpb.mem, hpb.keep _ not_words_x0 (by decide) VG.Proof.ChaCha20Poly1305.AArch64.Stitch.x0_not_poly]
  have accC := hpb.acc.frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_regs_keep fun r hr =>
      (hpc.keep _ (not_words_preserved (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).1) (by
        intro he; rw [he] at hr; exact absurd hr (by decide)) (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.1
        (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.2.1).trans (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_acc hr))
    (fun d hd => (rwc d hd).trans (rwb d hd).symm)
  have rdC : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Readable (B + BitVec.ofNat 64 (256 * 1)) pc :=
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.readable_of hp.blk hp.k0 hp.k1 (hpc.rd.trans (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_rd _ _)) (hpc.wr.trans (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_wr _ _))
      x0c 1 (by decide)
  -- The second phase.
  apply WP.seq
  refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.phase_ok (W := B + BitVec.ofNat 64 (256 * 1)) hpc.vec hpc.scalar hpc.table
    (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.start_ok enc 1 (by decide) B pc x26c) accC rdC).mono fun pd hpd => ?_
  have hcp₂ := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_cp pd hcp₁
  have hx₁ : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s pb).gpr .x20 = (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s pb).gpr .x0 + 64#64 := by
    rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide), VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)]; exact hp.x20
  have seD := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.second_rebase hcp₁ hx₁ hpc (by rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase]) (by rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.source_rebase]) hpd
  rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_rebase] at seD hcp₂
  -- The rest of the kernel's chunk.
  apply WP.seq
  refine (spill2_ok hcp₂ seD).mono fun pe hpe => ?_
  apply WP.seq
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.finish_ok hcp₂ hpe).mono fun pf hpf => ?_
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.last_ok hcp₂ hpf).mono fun pg hpg => ?_
  have hacc : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, pg.gpr r = pd.gpr r := fun r hr =>
    (hpg.cs r (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).1 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.1 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.2.1).trans
      (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_acc hr)
  rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_congr s hacc]
  refine ⟨hpg, ?_⟩
  -- The accumulator.
  have x0g : pg.gpr .x0 = s.gpr .x0 := hpg.x0.trans (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide))
  have fg : Frame [sr s, scalarBuf s, VG.Proof.ChaCha20.AArch64.Mixed8.dr s] s.mem pg.mem := by
    simpa only [sr, scalarBuf, VG.Proof.ChaCha20.AArch64.Mixed8.dr, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_mem,
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x0 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide), VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x1 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide),
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (show Reg.x3 ∉ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs by decide)] using hpg.frame
  have rwg := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rword_of fg x0g (hkey _ (fun r hr => hr))
  have rwd : ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword pd d = Poly.rword s d := by
    intro d hd
    rw [← rwc d hd]
    simp only [Poly.rword, hpd.mem, hpd.keep _ not_words_x0 (by decide) VG.Proof.ChaCha20Poly1305.AArch64.Stitch.x0_not_poly]
  have accG := hpd.acc.frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_regs_keep hacc) (fun d hd => (rwg d hd).trans (rwd d hd).symm)
  -- The bytes absorbed.
  have hwin (k : Nat) (hk : k ≤ 1) : (⟨B + BitVec.ofNat 64 (256 * k), 256⟩ : Region).Sub ⟨B, 512⟩ :=
    Offset.sub_base _ (by omega)
  have bA : bytesAt pa.mem (B + BitVec.ofNat 64 (256 * 0)) 256 =
      bytesAt s.mem (B + BitVec.ofNat 64 (256 * 0)) 256 :=
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.bytesAt_frame hpa.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.win _ (by simp)).sub_left (hwin 0 (by decide))) (by decide)
  have bC : bytesAt pc.mem (B + BitVec.ofNat 64 (256 * 1)) 256 =
      bytesAt s.mem (B + BitVec.ofNat 64 (256 * 1)) 256 :=
    VG.Proof.ChaCha20Poly1305.AArch64.Stitch.bytesAt_frame fc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.win _ (by simp)).sub_left (hwin 1 (by decide))
      · exact ((hp.win _ (by simp)).sub_left (hwin 1 (by decide))).sub_right hlow) (by decide)
  rw [bC, bA] at accG
  have hl : (bytesAt s.mem (B + BitVec.ofNat 64 (256 * 0)) 256).length % 16 = 0 := by
    rw [Poly1305.length_bytesAt]
  rw [← Poly1305.absorbAll_append hl] at accG
  have e : bytesAt s.mem (B + BitVec.ofNat 64 (256 * 0)) 256 ++
      bytesAt s.mem (B + BitVec.ofNat 64 (256 * 1)) 256 = bytesAt s.mem B 512 := by
    rw [show B + BitVec.ofNat 64 (256 * 0) = B by simp, Nat.mul_one,
      ← Poly1305.bytesAt_add]
  rw [e] at accG
  exact accG

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Body`. -/
section

/-!
# ChaCha20 and Poly1305 together (AArch64): a chunk of the loop

`Stitch.body`, as `Mixed8.body_ok`: from the kernel's loop invariant
(`Mixed8.BulkInv`) after `t` chunks to the one after `t + 1`, relative to the
entry state `rebase s₀ u`, since the chunk changes the accumulator's
registers.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP Chunked source sr scalarBuf dr LInv GPInv BulkInv
  cp_of_inv chunkData next_ok win win_sub guardR guardVR guard_chunk guardV_chunk)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {sve : Bool}

@[simp] theorem rebase_x0 (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x0 = s₀.gpr .x0 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
@[simp] theorem rebase_x1 (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x1 = s₀.gpr .x1 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
@[simp] theorem rebase_x2 (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x2 = s₀.gpr .x2 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
@[simp] theorem rebase_x3 (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x3 = s₀.gpr .x3 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
@[simp] theorem rebase_x19 (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x19 = s₀.gpr .x19 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
@[simp] theorem rebase_x20 (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x20 = s₀.gpr .x20 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
@[simp] theorem rebase_x26 (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr .x26 = s₀.gpr .x26 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of (by decide)
@[simp] theorem rebase_v (s₀ u : State) : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).v = s₀.v := rfl

@[simp] theorem st_rebase (s₀ u : State) : st (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = st s₀ := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_x0 s₀ u
@[simp] theorem dp_rebase (s₀ u : State) : dp (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = dp s₀ := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_x1 s₀ u
@[simp] theorem L_rebase (s₀ u : State) : L (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = L s₀ := by simp [L]
@[simp] theorem bp_rebase (s₀ u : State) : bp (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = bp s₀ := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_x3 s₀ u
@[simp] theorem stR_rebase (s₀ u : State) : stR (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = stR s₀ := by simp [stR]
@[simp] theorem dR_rebase (s₀ u : State) : dR (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = dR s₀ := by simp [dR]
@[simp] theorem bR_rebase (s₀ u : State) : bR (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = bR s₀ := by simp [bR]
@[simp] theorem S0_rebase (s₀ u : State) : S0 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = S0 s₀ := by simp [S0]
@[simp] theorem D0_rebase (s₀ u : State) (k : Nat) : D0 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) k = D0 s₀ k := by simp [D0]
@[simp] theorem KS_rebase (s₀ u : State) : KS (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) = KS s₀ := by simp [KS]

theorem xpre_rebase {s₀ : State} (u : State) (hp : XPre s₀) : XPre (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
    by simpa using h5, by simpa using h6⟩

/-- The kernel's loop invariant, for states with the accumulator's registers
of `u`. -/
theorem bulkInv_rebase {s₀ s : State} {t : Nat} (h : BulkInv s₀ t s) (u : State) :
    BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) t (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s u) := by
  refine ⟨⟨⟨by simpa using h.x0, by simpa using h.x1, by simpa using h.x2, by simpa using h.x3,
    by simpa using h.le, ?_, by simpa using h.rd, by simpa using h.wr, by simpa using h.sp,
    by simpa using h.cnt, by simpa using h.data, by simpa using h.frame⟩,
    by simpa using h.x20, fun j => ?_⟩, by simpa using h.savedV⟩
  · intro r hr h20 h19 h26
    by_cases ha : r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs
    · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_acc ha, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_acc ha]
    · rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of ha, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_of ha]; exact h.cs r hr h20 h19 h26

  · have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [Fin.ext_iff]; omega
    have e := h.saved j
    rcases hj with rfl | rfl | rfl <;> simpa using e
/-- `Mixed8.body_ok` after its chunk: the counter and the pointers advanced. -/
theorem next_after {s₀ : State} (hp : XPre s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s u : State} (h : BulkInv s₀ t s) (hu : Chunked s u) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.next) u fun v =>
      (BulkInv s₀ (t + 1) v ∧
        v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0)) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → r ≠ .x5 → v.gpr r = u.gpr r) ∧
      Frame [stR s₀] u.mem v.mem := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hx0 : u.gpr .x0 = st s₀ := hu.x0.trans h.x0
  have hx1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * t) := hu.x1.trans h.x1
  have hx2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * t) := hu.x2.trans h.x2
  have hx3 : u.gpr .x3 = bp s₀ := hu.x3.trans h.x3
  have hcnt : stateAt u.mem (st s₀) = ctr (S0 s₀) (8 * t) := by
    have hc := hu.cnt
    change stateAt u.mem (u.gpr .x0) = stateAt s.mem (s.gpr .x0) at hc
    rw [hx0,h.x0,h.cnt] at hc
    exact hc
  have hdata := chunkData hp h hge hu
  have hw : u.wr = [stR s₀,dR s₀,bR s₀] := hu.wr.trans (h.wr.trans hp.wr)
  have hi : InRegions (u.rd ++ u.wr) (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hu.rd,h.rd,hp.rd,hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have ho : InRegions u.wr (u.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [hw,hx0]
    exact ⟨stR s₀,by simp,Offset.contains_base _ (by decide) (by decide)⟩
  have hlen : (u.gpr .x2).toNat = L s₀ - 512 * t := by
    rw [hx2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hsaved : ∀ j : Fin 3, u.mem.readW (bp s₀ + BitVec.ofNat 64 (256 + 8 * j)) 64 =
      s₀.gpr ([.x20,.x19,.x26].getD j .x20) := by
    intro j
    rw [hu.frame.readW (r := guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (guard_chunk hp h hge j) (by decide),h.saved j]
  have hsavedV : ∀ j : Fin 2, u.mem.read (bp s₀ + BitVec.ofNat 64 (128 + 16 * j)) 16 =
      s₀.v (#[VReg.v8,VReg.v9][j]) := by
    intro j
    rw [hu.frame.read (r := guardVR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (guardV_chunk hp h hge j) (by decide),h.savedV j]
  refine (next_ok u (by rw [hlen]; omega) hi ho).mono fun v
    ⟨hv1,hv2,hv5,hkeep,hctr,hframe,hrd,hwr,hsp⟩ => ⟨?_, hkeep, by simpa only [stR, hx0] using hframe⟩
  have hptr : v.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * (t + 1)) := by
    rw [hv1,hx1,BitVec.add_assoc]
    change _ + (BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 512) = _
    rw [← BitVec.ofNat_add,show 512 * t + 512 = 512 * (t + 1) by omega]
  have hrem : v.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * (t + 1)) := by
    rw [hv2,hx2]
    change BitVec.ofNat 64 (L s₀ - 512 * t) - BitVec.ofNat 64 512 = _
    rw [Offset.ofNat_sub_ofNat (by omega),show L s₀ - 512 * t - 512 = L s₀ - 512 * (t + 1) by omega]
  refine ⟨⟨⟨⟨?_,hptr,hrem,?_,by omega,?_,hrd.trans (hu.rd.trans h.rd),
    hwr.trans (hu.wr.trans h.wr),hsp.trans (hu.sp.trans h.sp),?_,?_,?_⟩,?_,?_⟩,?_⟩,?_⟩
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx0]
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hx3]
  · intro r hr hr20 hr21 hr22
    have n1 : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    have n2 : r ≠ .x2 := by intro he; subst r; simp [preserved] at hr
    have n4 : r ≠ .x4 := by intro he; subst r; simp [preserved] at hr
    have n5 : r ≠ .x5 := by intro he; subst r; simp [preserved] at hr
    rw [hkeep r n1 n2 n4 n5,hu.cs r hr hr21 hr22,h.cs r hr hr20 hr21 hr22]
  · rw [hx0,hcnt,VG.Proof.ChaCha20.AArch64.Neon4.ctr_add,
      show 8 * t + 8 = 8 * (t + 1) by omega] at hctr
    exact hctr
  · intro k hk
    rw [hframe _ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact fun hc => hp.st_d _ hc (VG.Proof.ChaCha20.AArch64.Neon4.data_in hk)),hdata k hk]
  · have hf' : Frame [stR s₀,dR s₀,bR s₀] s.mem u.mem := hu.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀,by simp,by change (⟨s.gpr .x0,64⟩ : Region).Sub (stR s₀); rw [h.x0]; exact fun _ hx => hx⟩
      · exact ⟨bR s₀,by simp,by simpa only [scalarBuf,h.x3] using Region.sub_prefix (base := bp s₀) (by decide : 128 ≤ 320)⟩
      · exact ⟨dR s₀,by simp,by simpa only [dr,h.x1] using win_sub hge⟩)
    have hn' : Frame [stR s₀,dR s₀,bR s₀] u.mem v.mem := hframe.mono (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      rw [hx0]; exact List.mem_cons_self ..)
    exact (h.frame.trans hf').trans hn'
  · rw [hkeep _ (by decide) (by decide) (by decide) (by decide),hu.cs _ (by decide) (by decide) (by decide),h.x20]
  · intro j
    rw [hframe.readW (r := guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; simp only [List.mem_singleton] at hr; subst r
          rw [hx0]; exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega)))
      (by decide),hsaved j]
  · intro j
    rw [hframe.read (r := guardVR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; have he := List.mem_singleton.mp hr; subst r
          rw [hx0]; exact hp.st_b.symm.sub_left (Offset.sub_base _ (by have hj := j.isLt; omega)))
      (by decide),hsavedV j]
  · rw [hv5,hlen,show L s₀ - 512 * t - 512 = L s₀ - 512 * (t + 1) by omega]


/-- The bulk's precondition: the stream's (`vg_chacha20_xor`'s), with its
working space 64 bytes after the state, as in the ChaCha20-Poly1305 context. -/
structure BPre (s₀ : State) : Prop extends XPre s₀ where
  bp : bp s₀ = st s₀ + 64#64

theorem BPre.rebase {s₀ : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) (u : State) : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) :=
  ⟨VG.Proof.ChaCha20Poly1305.AArch64.Stitch.xpre_rebase u h.toXPre, by simpa using h.bp⟩

theorem BPre.key_sub {s₀ : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) : (⟨st s₀ + 224#64, 16⟩ : Region).Sub (bR s₀) := by
  simp only [bR, h.bp]
  exact Offset.sub (st s₀) (e := 64) (k := 320) (d := 224) (n := 16) (by decide) (by decide)

theorem BPre.key_in {s₀ : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) {d : Nat} (hd : 224 ≤ d) (hd' : d + 8 ≤ 240) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) 8 := by
  rw [h.rd, h.wr]
  refine ⟨bR s₀, by simp, ?_⟩
  simp only [bR, h.bp]
  exact Offset.contains (st s₀) (e := 64) (k := 320) (by omega) (by omega) (by decide)

/-- A chunk of the loop, absorbing the 512 bytes at `B`. -/
theorem body_ok (enc : Bool) {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) {s : State} (h : BulkInv s₀ t s) {R a : Nat} {w : Nat}
    (hw : w + 512 ≤ L s₀)
    (hB : dp s₀ + BitVec.ofNat 64 (512 * t) = VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf enc (dp s₀ + BitVec.ofNat 64 w))
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a s) :
    WP isa (VG.Impl.ChaCha20Poly1305.AArch64.Stitch.body sve enc) s fun v =>
      (BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ v) (t + 1) v ∧
        v.gpr .x5 = BitVec.ofNat 64 (if L s₀ - 512 * (t + 1) < 512 then 1 else 0)) ∧
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem (dp s₀ + BitVec.ofNat 64 w) 512)) v := by
  have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀
  have hBin : (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Sub (dR s₀) := Offset.sub_base _ hw
  have hx0 : s.gpr .x0 = st s₀ := h.x0
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hwin : (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Disjoint (stR s₀) ∧
      (⟨dp s₀ + BitVec.ofNat 64 w, 512⟩ : Region).Disjoint (bR s₀) :=
    ⟨hp.st_d.symm.sub_left hBin, hp.d_b.sub_left hBin⟩
  have hsb : (scalarBuf s).Sub (bR s₀) := by
    simp only [scalarBuf, h.x3]; exact Region.sub_prefix (by decide)
  have hkey : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s).Sub (bR s₀) := by simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR, hx0]; exact hp.key_sub
  have hpre : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.ChunkPre enc (dp s₀ + BitVec.ofNat 64 w) s := by
    refine ⟨cp_of_inv hp.toXPre h hge, by rw [h.x20, hx0, hp.bp], h.x1.trans hB, fun d hd => ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [hrw, hp.rd, hp.wr]
      refine ⟨dR s₀, by simp, ?_⟩
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by omega) (by omega)
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
      · simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR, scalarBuf, hx0, h.x3, hp.bp]
        exact Offset.disjoint (st s₀) (d := 224) (n := 16) (e := 64) (k := 128) (by decide)
          (by decide) (by decide)
      · simp only [dr, h.x1]
        exact (hp.d_b.symm.sub_left hkey).sub_right (win_sub hge)
  unfold VG.Impl.ChaCha20Poly1305.AArch64.Stitch.body
  apply WP.seq
  refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.chunk_ok enc s hpre ha).mono fun g ⟨hg, hag⟩ => ?_
  refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.next_after (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.xpre_rebase g hp.toXPre) (by simpa using hge) (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.bulkInv_rebase h g) hg).mono
    fun v ⟨⟨hv, h5⟩, hkeep, hf⟩ => ?_
  have hacc : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, v.gpr r = g.gpr r := fun r hr => hkeep r
    (by intro he; rw [he] at hr; exact absurd hr (by decide))
    (by intro he; rw [he] at hr; exact absurd hr (by decide))
    (by intro he; rw [he] at hr; exact absurd hr (by decide))
    (by intro he; rw [he] at hr; exact absurd hr (by decide))
  rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_congr s₀ hacc]
  refine ⟨⟨hv, by simpa using h5⟩, hag.frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_regs_keep hacc) ?_⟩
  have hg0 : g.gpr .x0 = st s₀ :=
    (hkeep .x0 (by decide) (by decide) (by decide) (by decide)).symm.trans (hv.x0.trans (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.st_rebase _ _))
  refine VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rword_frame (by simpa using hf) (hkeep _ (by decide) (by decide) (by decide) (by decide)) ?_
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR, hg0]
  exact (hp.st_b.symm.sub_left hp.key_sub)

/-- Where `Mixed8.enter` stores: `x19`, `x20` and `x26` at `buf[256, 280)`,
and `v8` and `v9` at `buf[128, 160)`. -/
abbrev enterR (s : State) : List Region :=
  [⟨s.gpr .x3 + BitVec.ofNat 64 256, 24⟩, ⟨s.gpr .x3 + BitVec.ofNat 64 128, 32⟩]

theorem enter_frame (s : State)
    (ho : ∀ d n, d + n ≤ 320 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.enter) s fun u =>
      Frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.enterR s) s.mem u.mem := by
  have c (d n : Nat) (hd : 256 ≤ d) (hn : d + n ≤ 280) :
      (⟨s.gpr .x3 + BitVec.ofNat 64 256, 24⟩ : Region).Contains (s.gpr .x3 + BitVec.ofNat 64 d) n :=
    Offset.contains _ hd hn (by decide)
  unfold VG.Impl.ChaCha20.AArch64.Mixed8.enter VG.Impl.ChaCha20.AArch64.Mixed5.enter
  apply WP.block_cons_iff.mpr
  let m₁ := s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 256) (s.gpr .x20)
  refine ⟨{s with mem := m₁}, exec_str_x (by decide) (ho 256 8 (by decide)), ?_⟩
  apply WP.block_cons_iff.mpr
  let m₂ := m₁.writeW (s.gpr .x3 + BitVec.ofNat 64 264) (s.gpr .x19)
  refine ⟨{s with mem := m₂}, exec_str_x (s := {s with mem := m₁}) (by decide) (ho 264 8 (by decide)), ?_⟩
  apply WP.block_cons_iff.mpr
  let m₃ := m₂.writeW (s.gpr .x3 + BitVec.ofNat 64 272) (s.gpr .x26)
  refine ⟨{s with mem := m₃}, exec_str_x (s := {s with mem := m₂}) (by decide) (ho 272 8 (by decide)), ?_⟩
  apply WP.block_cons_iff.mpr
  let a := ({s with mem := m₃} : State).write .x .x20 (s.gpr .x3 + BitVec.ofNat 64 0)
  refine ⟨a, by simpa only [State.read, BitVec.setWidth_eq] using
    exec_addImm_x (s := {s with mem := m₃}) (d := .x20) (n := .x3) (imm := 0) (by decide), ?_⟩
  have f₁ : Frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.enterR s) s.mem a.mem :=
    (((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (c 256 8 (by decide) (by decide))).writeW
      (List.mem_cons_self ..) _ (c 264 8 (by decide) (by decide))).writeW (List.mem_cons_self ..) _
      (c 272 8 (by decide) (by decide))
  have ha3 : a.gpr .x3 = s.gpr .x3 := RegUpd.gpr_write_of_ne _ .x _ (by decide)
  have haw : a.wr = s.wr := rfl
  refine (VG.Proof.ChaCha20.AArch64.Mixed8.saveV_ok a (by rw [haw, ha3]; exact ho 128 16 (by decide))
    (by rw [haw, ha3]; exact ho 144 16 (by decide))).mono fun u ⟨_, _, _, _, _, hf, _, _⟩ => ?_
  simp only [VG.Proof.ChaCha20.AArch64.Mixed8.savedVR, ha3] at hf
  exact f₁.trans (hf.mono (by simp))

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk`. -/
section

/-!
# ChaCha20 and Poly1305 together (AArch64): the whole chunks

`Stitch.bulk`, from a state with the stream's arguments (`Mixed8.XPre`, with
its working space 64 bytes after the state: `BPre`), at least 512 bytes of
data, and the accumulator in `x21`–`x23`: the chunks that fit encrypted (or
decrypted), as `Mixed8.bulk_ok`, and the bytes they absorbed: when
decrypting, every chunk's data as it was on entry; when encrypting, the
output of every chunk but the last.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64.Stitch

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64.Stitch VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64 (Words not_words_x1 not_words_x0 not_words_preserved)
open VG.Proof.ChaCha20.AArch64.Mixed8 (CP Chunked source sr scalarBuf dr LInv GPInv BulkInv
  cp_of_inv enter_ok leave_ok zero_batches)
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR S0 D0 KS)
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

/-- The kernel's loop invariant on entry. -/
theorem linv0 (s₀ : State) : VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ 0 s₀ := by
  refine ⟨rfl, ?_, ?_, rfl, by omega, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, ?_, ?_, Frame.refl _ _⟩
  · simp only [Nat.mul_zero, BitVec.add_zero]
  · simp only [Nat.mul_zero, Nat.sub_zero]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 64 (s₀.gpr .x2)).symm
  · exact (VG.Proof.ChaCha20.ctr_zero _).symm
  · intro k _; simp only [Nat.mul_zero, Nat.not_lt_zero, ite_false]

/-- The key is apart from what `enter` stores. -/
theorem key_enter {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.enterR s₀, (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s₀).Disjoint r := by
  have e (d : Nat) : s₀.gpr .x3 + BitVec.ofNat 64 d = st s₀ + BitVec.ofNat 64 (64 + d) := by
    rw [show s₀.gpr .x3 = bp s₀ from rfl, hp.bp, BitVec.add_assoc, ← BitVec.ofNat_add]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR, e] <;>
    exact Offset.disjoint (st s₀) (by decide) (by decide) (by decide)

/-- The key is apart from the regions a chunk writes. -/
theorem key_chunk {s₀ s : State} (hp : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) {t : Nat} (h : VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ t s)
    (hge : 512 * t + 512 ≤ L s₀) :
    ∀ r ∈ [sr s, scalarBuf s, dr s], (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s₀).Disjoint r := by
  have hkey : (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s₀).Sub (bR s₀) := hp.key_sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simpa only [sr, h.x0] using hp.st_b.symm.sub_left hkey
  · simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR, scalarBuf, h.x3, hp.bp]
    exact Offset.disjoint (st s₀) (d := 224) (n := 16) (e := 64) (k := 128) (by decide)
      (by decide) (by decide)
  · simp only [dr, h.x1]
    exact (hp.d_b.symm.sub_left hkey).sub_right
      (VG.Proof.ChaCha20.AArch64.Mixed8.win_sub hge)

/-- The key's words in a state with the entry state's `x0`, whose memory
differs from the entry state's only away from the key. -/
theorem rword_eq {s₀ s : State} {rs : List Region} (hf : Frame rs s₀.mem s.mem)
    (hx0 : s.gpr .x0 = s₀.gpr .x0) (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.keyR s₀).Disjoint r) :
    ∀ d, (d = Poly.r0Off ∨ d = Poly.r1Off) → Poly.rword s d = Poly.rword s₀ d :=
  VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rword_of hf hx0 hd

/-- Data the loop has not reached is as on entry. -/
theorem window_orig {s₀ x : State} {t : Nat} (h : VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ t x) (hge : 512 * t + 512 ≤ L s₀) :
    bytesAt x.mem (dp s₀ + BitVec.ofNat 64 (512 * t)) 512 =
      bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 (512 * t)) 512 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.data _ (by omega), ite_eq_right (by omega)]

/-- Data the loop has passed is the output. -/
theorem prefix_ct {s₀ x : State} {t n : Nat} (h : VG.Proof.ChaCha20.AArch64.Mixed8.LInv s₀ t x) (hn : n ≤ 512 * t) :
    bytesAt x.mem (dp s₀) n = (List.range n).map fun k => D0 s₀ k ^^^ (KS s₀).getD k 0 := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  rw [h.data _ (by have := h.le; omega), ite_eq_left (by omega)]

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
theorem chunks_open {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) {R a : Nat} {s : State} {t : Nat}
    (hge : 512 * t + 512 ≤ L s₀) (h : BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ s) t s)
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * t))) s) :
    WP isa (chunks sve false) s fun u => ∃ T, L s₀ - 512 * T < 512 ∧ t < T ∧
      BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) T u ∧ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * T))) u := by
  let Inv : Nat → State → Prop := fun n x => ∃ i, n = L s₀ - 512 * i ∧ 512 ≤ n ∧ t ≤ i ∧
    BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ x) i x ∧ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s₀.mem (dp s₀) (512 * i))) x
  refine WP.loop (M := isa) Inv ?_ (L s₀ - 512 * t) s ⟨t, rfl, by omega, Nat.le_refl _, h, ha⟩
  rintro n x ⟨i, rfl, hge', hti, hx, hax⟩
  have hb : dp (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ x) + BitVec.ofNat 64 (512 * i) =
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf false (dp (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ x) + BitVec.ofNat 64 (512 * i)) := by
    simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf, Bool.false_eq_true, ite_false, BitVec.add_zero]
  refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.body_ok false (hp.rebase x) (t := i) (by simp; omega) hx (w := 512 * i)
    (by simp; omega) hb hax).mono fun v ⟨⟨hv, h5⟩, hav⟩ => ?_
  rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_rebase] at hv
  have hwin := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.window_orig hx.toLInv (by simp; omega)
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dp_rebase, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_mem] at hwin hav
  rw [hwin, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.absorb_join (by rw [Poly1305.length_bytesAt]; omega), VG.Proof.ChaCha20Poly1305.AArch64.Stitch.bytesAt_join,
    show 512 * i + 512 = 512 * (i + 1) by omega] at hav
  rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.L_rebase] at h5
  have hc := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.eval_zero5 h5
  by_cases he : L s₀ - 512 * (i + 1) < 512
  · left
    rw [decide_eq_false (show ¬ 512 ≤ L s₀ - 512 * (i + 1) by omega)] at hc
    exact ⟨hc, i + 1, he, by omega, hv, hav⟩
  · right
    rw [decide_eq_true (show 512 ≤ L s₀ - 512 * (i + 1) by omega)] at hc
    exact ⟨hc, L s₀ - 512 * (i + 1), by omega, i + 1, rfl, by omega, by omega, hv, hav⟩

/-- The loop of chunks that encrypt, each absorbing the output of the one before. -/
theorem chunks_seal {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) {R a : Nat} {s : State} {t : Nat} (ht : 1 ≤ t)
    (hge : 512 * t + 512 ≤ L s₀) (h : BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ s) t s)
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt s.mem (dp s₀) (512 * (t - 1)))) s) :
    WP isa (chunks sve true) s fun u => ∃ T, L s₀ - 512 * T < 512 ∧ t < T ∧
      BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) T u ∧
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt u.mem (dp s₀) (512 * (T - 1)))) u := by
  let Inv : Nat → State → Prop := fun n x => ∃ i, n = L s₀ - 512 * i ∧ 512 ≤ n ∧ t ≤ i ∧
    BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ x) i x ∧ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt x.mem (dp s₀) (512 * (i - 1)))) x
  refine WP.loop (M := isa) Inv ?_ (L s₀ - 512 * t) s ⟨t, rfl, by omega, Nat.le_refl _, h, ha⟩
  rintro n x ⟨i, rfl, hge', hti, hx, hax⟩
  have hb : dp (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ x) + BitVec.ofNat 64 (512 * i) =
      VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf true (dp (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ x) + BitVec.ofNat 64 (512 * (i - 1))) := by
    simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dataOf, ite_true, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.body_ok true (hp.rebase x) (t := i) (by simp; omega) hx (w := 512 * (i - 1))
    (by simp; omega) hb hax).mono fun v ⟨⟨hv, h5⟩, hav⟩ => ?_
  rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_rebase] at hv
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dp_rebase] at hav
  rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.absorb_join (by rw [Poly1305.length_bytesAt]; omega), VG.Proof.ChaCha20Poly1305.AArch64.Stitch.bytesAt_join,
    show 512 * (i - 1) + 512 = 512 * (i + 1 - 1) by omega] at hav
  have p1 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.prefix_ct hx.toLInv (n := 512 * (i + 1 - 1)) (by omega)
  have p2 := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.prefix_ct hv.toLInv (n := 512 * (i + 1 - 1)) (by omega)
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.dp_rebase, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.D0_rebase, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.KS_rebase] at p1 p2
  rw [p1, ← p2] at hav
  rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.L_rebase] at h5
  have hc := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.eval_zero5 h5
  by_cases he : L s₀ - 512 * (i + 1) < 512
  · left
    rw [decide_eq_false (show ¬ 512 ≤ L s₀ - 512 * (i + 1) by omega)] at hc
    exact ⟨hc, i + 1, he, by omega, hv, hav⟩
  · right
    rw [decide_eq_true (show 512 ≤ L s₀ - 512 * (i + 1) by omega)] at hc
    exact ⟨hc, L s₀ - 512 * (i + 1), by omega, i + 1, rfl, by omega, by omega, hv, hav⟩

/-- `leave` only loads. -/
theorem leave_mem (s : State)
    (hi : ∀ d n, d + n ≤ 320 → InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) n) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.leave) s fun u => u.mem = s.mem := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, VG.Impl.ChaCha20.AArch64.Mixed8.leave,
    VG.Impl.ChaCha20.AArch64.Mixed5.leave, List.cons_append, List.nil_append, runBlock_cons,
    runBlock_nil, exec, addr, Size.bytes, Size.bits, State.load,
    hi 128 16 (by decide), hi 144 16 (by decide), hi 256 8 (by decide), hi 264 8 (by decide),
    hi 272 8 (by decide), RegUpd.gpr_write, BitVec.setWidth_eq, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_write, State.setV, Option.bind_some, Option.map_some, isa, runStep_some,
    Option.some.injEq, exists_eq_left']

theorem rebase_self {s₀ u : State} (h : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, u.gpr r = s₀.gpr r) : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u = s₀ := by
  simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase]
  cases s₀
  congr 1
  funext r
  by_cases hr : r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs <;> simp only [hr, ite_true, ite_false, h r]

/-- What the bulk leaves: `T` chunks done, and the bytes absorbed. -/
structure Bulked (enc : Bool) (R a : Nat) (s₀ : State) (T : Nat) (u : State) : Prop where
  pos : 1 ≤ T
  rest : L s₀ - 512 * T < 512
  inv : VG.Proof.ChaCha20.AArch64.Mixed8.LInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) T u
  cs : ∀ r ∈ preserved, u.gpr r = (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u).gpr r
  v8 : u.v .v8 = s₀.v .v8
  v9 : u.v .v9 = s₀.v .v9
  acc : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (if enc then bytesAt u.mem (dp s₀) (512 * (T - 1))
    else bytesAt s₀.mem (dp s₀) (512 * T))) u

/-- Leaving, after the chunks. -/
theorem leave_bulk {enc : Bool} {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) {R a : Nat} {u : State} {T : Nat}
    (hT : 1 ≤ T) (hr : L s₀ - 512 * T < 512) (h : BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ u) T u)
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (if enc then bytesAt u.mem (dp s₀) (512 * (T - 1))
      else bytesAt s₀.mem (dp s₀) (512 * T))) u) :
    WP isa (.block VG.Impl.ChaCha20.AArch64.Mixed8.leave) u (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulked enc R a s₀ T) := by
  have hi : ∀ d n, d + n ≤ 320 → InRegions (u.rd ++ u.wr) (u.gpr .x3 + BitVec.ofNat 64 d) n := by
    intro d n hd
    rw [h.rd, h.wr, h.x3]
    simp only [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_rd, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_wr, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.bp_rebase, hp.rd, hp.wr]
    exact ⟨bR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  refine (WP.both (leave_ok (hp.rebase u).toXPre h) (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.leave_mem u hi)).mono
    fun v ⟨⟨hl, hcs, h8, h9⟩, hm⟩ => ?_
  have hacc : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, v.gpr r = u.gpr r := fun r hr =>
    (hcs r (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).1).trans (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_acc hr)
  have e := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_congr s₀ hacc
  refine ⟨hT, hr, e ▸ hl, fun r hr => by rw [e]; exact hcs r hr, by simpa using h8,
    by simpa using h9, ?_⟩
  rw [hm]
  exact ha.frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_regs_keep hacc) fun d _ => by
    simp only [Poly.rword, hm, hl.x0, h.x0]

theorem bytesAt_zero (m : Mem) (p : Addr) : bytesAt m p 0 = [] := rfl

theorem bulk_ok (enc : Bool) {s₀ : State} (hp : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.BPre s₀) (hL : 512 ≤ L s₀) {R a : Nat}
    (ha : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a s₀) :
    WP isa (bulk sve enc) s₀ fun u => ∃ T, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulked enc R a s₀ T u := by
  have ho : ∀ d n, d + n ≤ 320 → InRegions s₀.wr (s₀.gpr .x3 + BitVec.ofNat 64 d) n := by
    intro d n hd
    rw [hp.wr]
    exact ⟨bR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
  have nil (m : Mem) (k : Nat) (hk : k = 0) :
      absorbAll R a (bytesAt m (dp s₀) (512 * k)) = a := by
    rw [hk, Nat.mul_zero, VG.Proof.ChaCha20Poly1305.AArch64.Stitch.bytesAt_zero, Poly1305.absorbAll_nil]
  unfold bulk
  apply WP.seq
  refine (WP.both (enter_ok hp.toXPre (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.linv0 s₀) (fun _ _ => rfl) rfl) (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.enter_frame s₀ ho)).mono
    fun s₁ ⟨h₁, f₁⟩ => ?_
  have acc₁ : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, s₁.gpr r = s₀.gpr r := fun r hr =>
    h₁.cs r (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).1 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.2.2 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.1
      (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.2.1
  have rw₁ := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rword_eq f₁ h₁.x0 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.key_enter hp)
  have ha₁ : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R a s₁ := ha.frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_regs_keep acc₁) rw₁
  have hb₁ : BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ s₁) 0 s₁ := by rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_self acc₁]; exact h₁
  apply WP.seq
  cases enc
  · -- Decrypting: every chunk absorbs itself.
    simp only [Bool.false_eq_true, ite_false]
    refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.chunks_open hp (R := R) (a := a) (t := 0) (by omega) hb₁
      (by rw [nil _ _ rfl]; exact ha₁)).mono fun u ⟨T, hr, hT, hu, hau⟩ => ?_
    exact (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.leave_bulk (enc := false) hp (by omega) hr hu (by simpa using hau)).mono
      fun w hw => ⟨T, hw⟩
  · -- Encrypting: the first chunk is the kernel's.
    simp only [ite_true]
    apply WP.seq
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.chunk_ok s₁ (cp_of_inv hp.toXPre h₁ (by omega))).mono
      fun g hg => ?_
    refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.next_after hp.toXPre (t := 0) (by omega) h₁ hg).mono fun v ⟨⟨hv, h5⟩, hkeep, hf⟩ => ?_
    have accv : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.Stitch.accRegs, v.gpr r = s₀.gpr r := fun r hr =>
      (hkeep r (by intro he; rw [he] at hr; exact absurd hr (by decide))
        (by intro he; rw [he] at hr; exact absurd hr (by decide))
        (by intro he; rw [he] at hr; exact absurd hr (by decide))
        (by intro he; rw [he] at hr; exact absurd hr (by decide))).trans
      ((hg.cs r (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).1 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.1 (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_preserved r hr).2.2.1).trans
        (acc₁ r hr))
    have hfv : Frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.enterR s₀ ++ [sr s₁, scalarBuf s₁, dr s₁] ++ [stR s₀]) s₀.mem v.mem :=
      ((f₁.mono (by simp)).trans (hg.frame.mono (by simp))).trans (hf.mono (by simp))
    have hx0v : v.gpr .x0 = s₀.gpr .x0 :=
      (hkeep _ (by decide) (by decide) (by decide) (by decide)).trans (hg.x0.trans h₁.x0)
    have rwv := VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rword_eq hfv hx0v (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · exact VG.Proof.ChaCha20Poly1305.AArch64.Stitch.key_enter hp r hr
        · exact VG.Proof.ChaCha20Poly1305.AArch64.Stitch.key_chunk hp h₁.toLInv (by omega) r hr
      · rw [List.mem_singleton.mp hr]; exact (hp.st_b.symm.sub_left hp.key_sub))
    have hav : VG.Proof.ChaCha20Poly1305.AArch64.Stitch.Acc R (absorbAll R a (bytesAt v.mem (dp s₀) (512 * (1 - 1)))) v := by
      rw [nil _ _ rfl]; exact ha.frame (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.acc_regs_keep accv) rwv
    have hbv : BulkInv (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase s₀ v) 1 v := by rw [VG.Proof.ChaCha20Poly1305.AArch64.Stitch.rebase_self accv]; exact hv
    apply WP.ite (decide (L s₀ - 512 * (0 + 1) < 512))
      (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short h5)
    · intro hs
      have hs' := of_decide_eq_true hs
      exact WP.block_nil ((VG.Proof.ChaCha20Poly1305.AArch64.Stitch.leave_bulk (enc := true) hp (Nat.le_refl 1) (by omega) hbv
        (by simpa using hav)).mono fun w hw => ⟨1, hw⟩)
    · intro hs
      have hs' := of_decide_eq_false hs
      refine (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.chunks_seal hp (t := 1) (Nat.le_refl 1) (by omega) hbv hav).mono
        fun u ⟨T, hr, hT, hu, hau⟩ => ?_
      exact (VG.Proof.ChaCha20Poly1305.AArch64.Stitch.leave_bulk (enc := true) hp (by omega) hr hu (by simpa using hau)).mono
        fun w hw => ⟨T, hw⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Stitch

end
