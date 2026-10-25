module

public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Iterate
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Pbkdf2.Memory

/-!
# PBKDF2-HMAC's iteration over a Merkle–Damgård hash function on RISC-V

The prologue aligns `scratch`, saves our caller's `ra` and `s1`–`s6` there,
sets up our registers, zero-extends `n`, and lays out the block: `U`, then
the padding (`prologue_ok`, which establishes the loop invariant with `n`
steps left); the loop runs the steps (`loop_ok`, `Iterate.lean`); the
epilogue restores the registers, and `Md.iterate_hmac` turns the iteration
of two compressions per step into PBKDF2's (`epilogue_ok`). `correct`
composes them, for any hash function and compression function `HashOk`
describes.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64

open VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd wp_li wp_mv wp_addi wp_subi wp_andi wp_srl wp_sll eval_zero eval_nonzero
  ofNat_beq_zero)
open VG.Impl.Pbkdf2.RISCV64 (It mov)
open VG.Proof.MdStream (Md)
open VG.WriteBytes (writeBytes writeBytes_frame)
open Spec.Sha256 (bytesAt)
open Spec.Pbkdf2 (xorBytes)
open Spec.Hmac (StreamingHash xorPad ipad opad hmacBlockKey)
open VG.Proof.Hmac.Common (bytesAt_length bytesAt_writeBytes_self)

variable {P : It} {Wi : Nat} {s₀ : State} {L : Nat}

/-- `(x << 32) >> 32` is the low 32 bits of `x`. -/
theorem zext32 (x : BitVec 64) : x <<< 32 >>> 32 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

theorem nn_lt (s₀ : State) : nn s₀ < 2 ^ 32 := ((s₀.gpr .a2).setWidth 32).isLt

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

theorem loop_ok {H : Md P.B P.N L} (hR : H.Reloc) (hf : CalleeOk H P.CW P.cmpC) (hout : OutOk H P.D P.out)
    {n : Nat} {s : State} (h : Inv P Wi H s₀ n s) :
    WP isa (.ite (.zero .s6) (.block []) (.loop P.body (.nonzero .s6))) s (Inv P Wi H s₀ 0) := by
  have hlt : n < 2 ^ 64 := by have := h.le; have := nn_lt s₀; omega
  refine WP.ite (decide (n = 0)) (by rw [eval_zero, h.s6, ofNat_beq_zero hlt]) (fun hb => ?_) (fun hb => ?_)
  · obtain rfl : n = 0 := by simpa using hb
    exact WP.block_nil h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hb; omega⟩
    refine WP.loop (M := isa) (fun m s => Inv P Wi H s₀ (m + 1) s)
      (fun m s hs' => WP.mono (body_ok hp hz hR hf hout (Nat.succ_pos m) hs') fun s' hi => ?_) m s h
    have hlt' : m < 2 ^ 64 := by have := hi.le; have := nn_lt s₀; omega
    have hz' : isa.eval (.nonzero .s6) s' = some (decide (m ≠ 0)) := by
      rw [eval_nonzero, hi.s6, Nat.succ_sub_one, bne, ofNat_beq_zero hlt']; simp
    cases m with
    | zero => exact .inl ⟨by rw [hz']; rfl, hi⟩
    | succ m => exact .inr ⟨by rw [hz']; simp, m, by omega, hi⟩

end

theorem saved_fits (hz : Sizes P Wi) : Spill.Fits P.saved := by
  have := hz.CW8
  have := hz.CWle
  refine ⟨fun q hq => ?_, ?_⟩
  · simp only [It.saved, It.so, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
  · simp only [It.saved, It.so, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true, not_false_eq_true]
    omega

theorem saved_in : ∀ q ∈ P.saved, P.CW ≤ q.2 ∧ q.2 + 8 ≤ P.CW + 56 := by
  intro q hq
  simp only [It.saved, It.so, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem ofInt7 : BitVec.ofNat 64 7 = BitVec.ofInt 64 7 := rfl

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

/-- The prologue: the loop invariant with `n` steps left. -/
theorem prologue_ok {H : Md P.B P.N L} (hpad : P.pad.map (BitVec.ofNat 8) = H.tailPad P.D) :
    WP isa (.block P.prologue) s₀ (Inv P Wi H s₀ (nn s₀)) := by
  have hN := hz.N64
  have hB := hz.B128
  have hDB := hz.DB
  have hD := hz.DN
  have hfi := hz.fits
  have hW := hz.W
  have hCW := hz.CWle
  have hpd := pad_le (scr s₀)
  simp only [It.prologue, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_addi (imm := 7) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ => ?_
  have a4₂ : s₂.gpr .a4 = sc s₀ := by rw [u₂.gpr, u₁.gpr, ofInt7, Align.align_eq]
  have g₂ : ∀ r, r ≠ .a4 → s₂.gpr r = s₀.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  show WP isa (.block (Spill.saveCode .a4 P.saved ++ _)) s₂ _
  refine Spill.save_ok (by rw [a4₂]; exact sc_al) (saved_fits hz).1
    (fun q hq => ⟨scR Wi s₀, by rw [u₂.wr, u₁.wr, hp.wr]; simp, by
      rw [a4₂]; exact sc_contains hz (by have := saved_in q hq; omega)⟩) ?_
  refine wp_mv fun s₄ u₄ => wp_addi (by simp only [It.hvO]; omega) fun s₅ u₅ =>
    wp_addi (by simp only [It.blkO, It.hvO]; omega) fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ =>
    wp_sll (by decide) fun s₉ u₉ => wp_srl (by decide) fun s₁₀ u₁₀ => ?_
  -- The registers.
  have G6 : ∀ r, r ≠ .a4 → r ≠ .s2 → r ≠ .s1 → r ≠ .s3 → s₆.gpr r = s₀.gpr r := fun r h0 h1 h2 h3 =>
    (u₆.other r h3).trans ((u₅.other r h2).trans ((u₄.other r h1).trans (g₂ r h0)))
  have G8 : ∀ r, r ≠ .a4 → r ≠ .s2 → r ≠ .s1 → r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → s₈.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h5 => (u₈.other r h5).trans ((u₇.other r h4).trans (G6 r h0 h1 h2 h3))
  have G : ∀ r, r ≠ .a4 → r ≠ .s2 → r ≠ .s1 → r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → r ≠ .s6 →
      s₁₀.gpr r = s₀.gpr r := fun r h0 h1 h2 h3 h4 h5 h6 =>
    (u₁₀.other r h6).trans ((u₉.other r h6).trans (G8 r h0 h1 h2 h3 h4 h5))
  have a4₄ : s₄.gpr .a4 = sc s₀ := (u₄.other _ (by decide)).trans a4₂
  have T : ∀ r, r ≠ .s4 → r ≠ .s5 → r ≠ .s6 → s₁₀.gpr r = s₆.gpr r := fun r h4 h5 h6 =>
    (u₁₀.other r h6).trans ((u₉.other r h6).trans ((u₈.other r h5).trans (u₇.other r h4)))
  have e2 : s₁₀.gpr .s2 = sc s₀ := by
    rw [T _ (by decide) (by decide) (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
    exact a4₂
  have e1 : s₁₀.gpr .s1 = hv P s₀ := by
    rw [T _ (by decide) (by decide) (by decide), u₆.other _ (by decide), u₅.gpr, a4₄]
  have e3 : s₁₀.gpr .s3 = blk P s₀ := by
    rw [T _ (by decide) (by decide) (by decide), u₆.gpr, u₅.other _ (by decide), a4₄]
  have e4 : s₁₀.gpr .s4 = key s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      G6 _ (by decide) (by decide) (by decide) (by decide)]
  have e5 : s₁₀.gpr .s5 = tp s₀ := by
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      G6 _ (by decide) (by decide) (by decide) (by decide)]
  have e6 : s₁₀.gpr .s6 = BitVec.ofNat 64 (nn s₀) := by
    rw [u₁₀.gpr, u₉.gpr, G8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), zext32]
  have ea1 : s₁₀.gpr .a1 = up s₀ :=
    G _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The memory and regions.
  have m₁₀ : s₁₀.mem = Spill.saveMem s₀.mem (sc s₀) s₂.gpr P.saved := by
    rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
    show Spill.saveMem s₂.mem (s₂.gpr .a4) s₂.gpr P.saved = _
    rw [u₂.mem, u₁.mem, a4₂]
  have rd₁₀ : s₁₀.rd = s₀.rd := by
    rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd]; exact u₂.rd.trans u₁.rd
  have wr₁₀ : s₁₀.wr = s₀.wr := by
    rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr]; exact u₂.wr.trans u₁.wr
  have sp₁₀ : s₁₀.sp = s₀.sp := by
    rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp]; exact u₂.sp.trans u₁.sp
  have eD : blk P s₀ + BitVec.ofNat 64 P.D = sc s₀ + BitVec.ofNat 64 (P.blkO + P.D) := Offset.add_add _ _ _
  have S1 : Region.Sub ⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩ (scR Wi s₀) := sc_sub (by omega)
  have S2 : Region.Sub ⟨blk P s₀, P.D⟩ (scR Wi s₀) := by
    rw [blk_eq]; exact sc_sub (by omega)
  have S3 : Region.Sub ⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩ (scR Wi s₀) := by
    rw [eD]; exact sc_sub (by simp only [It.blkO, It.hvO]; omega)
  have uB : Region.Disjoint ⟨up s₀, P.D⟩ ⟨blk P s₀, P.D⟩ := hp.u_s.sub_right S2
  -- `U` into the block, then the padding.
  rw [padCode_eq, ← List.append_nil (bytesCode P.pad P.D P.pad.length)]
  refine cp_ok (src := .a1) (dst := .s3) (by decide) (by decide) 0 0 P.D (by omega) (by omega) _ s₁₀ _
    (fun k hk => by
      rw [ea1, BitVec.add_zero, rd₁₀, wr₁₀, hp.rd]
      exact ⟨uR P s₀, by simp, Offset.contains_base _ hk (by omega)⟩)
    (fun k hk => by
      rw [e3, BitVec.add_zero, blk_eq]
      exact in_scr hp hz wr₁₀ (a := P.CW + 56 + P.N) (n := P.B) (by omega) (by omega))
    (by rw [ea1, e3, BitVec.add_zero, BitVec.add_zero]
        exact uB.sep (Region.contains_self _ _) (Region.contains_self _ _))
    fun s' g' rd' wr' sp' m' => ?_
  rw [e3, ea1, BitVec.add_zero, BitVec.add_zero, m₁₀] at m'
  refine bytes_ok P.pad (fun i hi => by have := hz.padV i hi; omega) P.D P.pad.length (Nat.le_refl _)
    (by rw [hz.padL]; omega) [] s' _
    (fun k hk => by
      rw [g' _ (by decide), e3, blk_eq, Offset.add_add]
      exact in_scr hp hz (wr'.trans wr₁₀) (a := P.CW + 56 + P.N) (n := P.B) (by omega)
        (by rw [hz.padL] at hk; omega))
    fun s'' g'' rd'' wr'' sp'' m'' => WP.block_nil ?_
  rw [g' _ (by decide), e3, List.take_length, m'] at m''
  generalize hM₁ : Spill.saveMem s₀.mem (sc s₀) s₂.gpr P.saved = M₁ at m''
  generalize hM₂ : writeBytes M₁ (blk P s₀) (bytesAt M₁ (up s₀) P.D) = M₂ at m''
  have hl : (P.pad.map (BitVec.ofNat 8)).length = P.B - P.D := by rw [List.length_map, hz.padL]
  have f₁ : Frame [⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩] s₀.mem M₁ := by
    rw [← hM₁]; exact Spill.saveMem_frame saved_in (by omega) _ _ _
  have f₂ : Frame [⟨blk P s₀, P.D⟩] M₁ M₂ := by
    rw [← hM₂]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have f₃ : Frame [⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩] M₂ s''.mem := by
    rw [m'']; exact writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have sub : ∀ {R : Region}, Region.Sub R (scR Wi s₀) → ∀ r ∈ [R], ∃ r' ∈ [tR P s₀, scR Wi s₀], Region.Sub r r' :=
    fun hR r hr => ⟨scR Wi s₀, by simp, by rw [List.mem_singleton.mp hr]; exact hR⟩
  have one : ∀ {R R' : Region}, Region.Disjoint R' R → ∀ r ∈ [R], Region.Disjoint R' r :=
    fun h r hr => by rw [List.mem_singleton.mp hr]; exact h
  have dsv₂ : Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩ ⟨blk P s₀, P.D⟩ :=
    sc_disj hz (.inl (by simp only [It.blkO, It.hvO]; omega)) (by omega) (by simp only [It.blkO, It.hvO]; omega)
  have dsv₃ : Region.Disjoint ⟨sc s₀ + BitVec.ofNat 64 P.CW, 56⟩ ⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩ := by
    rw [eD]; exact sc_disj hz (.inl (by simp only [It.blkO, It.hvO]; omega)) (by omega)
      (by simp only [It.blkO, It.hvO]; omega)
  have d₂₃ : Region.Disjoint ⟨blk P s₀, P.D⟩ ⟨blk P s₀ + BitVec.ofNat 64 P.D, P.B - P.D⟩ := by
    rw [eD]; exact sc_disj hz (.inl (by simp only [It.blkO]; omega)) (by simp only [It.blkO, It.hvO]; omega)
      (by simp only [It.blkO, It.hvO]; omega)
  have tB : ∀ {M M' : Mem} {R : Region}, Frame [R] M M' → Region.Sub R (scR Wi s₀) →
      bytesAt M' (tp s₀) P.D = bytesAt M (tp s₀) P.D := fun hf hR =>
    VG.Proof.Pbkdf2.Memory.frame_bytesAt hf (one (hp.t_s.sub_right hR)) (by omega)
  have saved₁ : Spill.Saved (sc s₀) s₀.gpr P.saved M₁ := by
    rw [← hM₁]
    intro q hq
    rw [Spill.saveMem_saved (saved_fits hz) s₀.mem (sc s₀) s₂.gpr q hq]
    refine g₂ _ ?_
    simp only [It.saved, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have blkU : bytesAt s''.mem (blk P s₀) P.D = bytesAt s₀.mem (up s₀) P.D := by
    rw [VG.Proof.Pbkdf2.Memory.frame_bytesAt f₃ (one d₂₃) (by omega)]
    have := bytesAt_writeBytes_self M₁ (blk P s₀) (bytesAt M₁ (up s₀) P.D) (by rw [bytesAt_length]; omega)
    rw [bytesAt_length, hM₂] at this
    rw [this]
    exact VG.Proof.Pbkdf2.Memory.frame_bytesAt f₁ (one (hp.u_s.sub_right S1)) (by omega)
  exact {
    rd := rd''.trans (rd'.trans rd₁₀)
    wr := wr''.trans (wr'.trans wr₁₀)
    sp := sp''.trans (sp'.trans sp₁₀)
    s1 := by rw [g'' _ (by decide), g' _ (by decide), e1]
    s2 := by rw [g'' _ (by decide), g' _ (by decide), e2]
    s3 := by rw [g'' _ (by decide), g' _ (by decide), e3]
    s4 := by rw [g'' _ (by decide), g' _ (by decide), e4]
    s5 := by rw [g'' _ (by decide), g' _ (by decide), e5]
    s6 := by rw [g'' _ (by decide), g' _ (by decide), e6]
    nv := fun r hr => by
      rw [g'' r (by revert r; decide), g' r (by revert r; decide)]
      exact G r (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide)
    fr := (f₁.sub (sub S1)).trans ((f₂.sub (sub S2)).trans (f₃.sub (sub S3)))
    saved := (saved₁.frame_in saved_in f₂ (one dsv₂)).frame_in saved_in f₃ (one dsv₃)
    pad := by
      rw [m'']
      have := bytesAt_writeBytes_self M₂ (blk P s₀ + BitVec.ofNat 64 P.D) (P.pad.map (BitVec.ofNat 8))
        (by rw [hl]; omega)
      rw [hl] at this
      rw [this, hpad]
    le := Nat.le_refl _
    val := by rw [blkU, tB f₃ S3, tB f₂ S2, tB f₁ S1] }

end

/-- The final `T` is PBKDF2's, for a key as the contract requires. -/
theorem post_eq {H : Md P.B P.N L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv P.D) {m : Mem}
    (hT : bytesAt m (tp s₀) P.D =
      Spec.Pbkdf2.iterate (stepM P H s₀) (nn s₀) (bytesAt s₀.mem (up s₀) P.D) (bytesAt s₀.mem (tp s₀) P.D))
    {k0 : List Byte} (hk : k0.length = S.H.blockSize) (hi : S.Repr s₀.mem (key s₀) (xorPad k0 ipad))
    (ho : S.Repr s₀.mem (key s₀ + BitVec.ofNat 64 S.stateBytes) (xorPad k0 opad)) :
    bytesAt m (tp s₀) S.digestBytes =
      Spec.Pbkdf2.iterate (hmacBlockKey S.H k0) (nn s₀) (bytesAt s₀.mem (up s₀) S.digestBytes)
        (bytesAt s₀.mem (tp s₀) S.digestBytes) := by
  have hB : 0 < P.B := by have hl_DL := hl.DL; omega
  rw [hl.hB] at hk
  rw [hl.hS] at ho
  have li : (xorPad k0 ipad).length = P.B := by simp [xorPad, hk]
  have lo : (xorPad k0 opad).length = P.B := by simp [xorPad, hk]
  have ei := Md.stateAt_of_repr hB li (hl.repr _ _ _ hi)
  have eo := Md.stateAt_of_repr hB lo (hl.repr _ _ _ ho)
  rw [hl.hD]
  refine hT.trans (Md.iterate_congr (fun u hu => ?_) (fun u => Md.step_length H hl.DN _ _ u) _ _ _
    (bytesAt_length _ _ _)).symm
  rw [Md.hmac_step hl hk hu, ei, eo]

theorem restList_ok (hz : Sizes P Wi) : ∀ q ∈ P.restList, q.2 % 8 = 0 ∧ q.2 < 2048 := by
  have := hz.CW8
  have := hz.CWle
  intro q hq
  simp only [It.restList, It.so, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

theorem restList_sub : ∀ q ∈ P.restList, q ∈ P.saved := by
  intro q hq
  simp only [It.restList, It.saved, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem restorable : Spill.Restorable .s2 P.restList := by
  simp [Spill.Restorable, It.restList]

section
variable (hp : Pre P Wi s₀) (hz : Sizes P Wi)
include hp hz

theorem epilogue_ok {H : Md P.B P.N L} {S : StreamingHash} {iv : H.HV} (hl : H.Link S iv P.D) {s : State}
    (h : Inv P Wi H s₀ 0 s) :
    WP isa (.block P.restore) s fun s' => abiPreserved s₀ s' ∧ (iterK S Wi).post s₀ s' := by
  have hCW := hz.CWle
  have hfi := hz.fits
  refine WP.mono (Spill.restore_wp (b := .s2) (l := P.restList) sc_al h.s2 (restList_ok hz) restorable
    (fun q hq => ⟨scR Wi s₀, by rw [h.rd, h.wr, hp.rd, hp.wr]; simp,
      sc_contains hz (by
        have := saved_in q (restList_sub q hq); omega)⟩)
    (h.saved.sub restList_sub)) fun s' hr => ?_
  have keep : ∀ r, r ∈ P.restList.map Prod.fst ∨ s.gpr r = s₀.gpr r → s'.gpr r = s₀.gpr r :=
    fun r h' => hr.gpr_of h'
  refine ⟨⟨fun r hr' => keep r ?_, hr.sp.trans h.sp, keep _ (.inl (by simp [It.restList]))⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [.inr (h.nv _ (by simp)), .inl (by simp [It.restList]), .inl (by simp [It.restList]),
      .inl (by simp [It.restList]), .inl (by simp [It.restList]), .inl (by simp [It.restList]),
      .inl (by simp [It.restList]), .inr (h.nv _ (by simp)), .inr (h.nv _ (by simp)), .inr (h.nv _ (by simp)),
      .inr (h.nv _ (by simp)), .inr (h.nv _ (by simp))]
  · intro k0 hk hi ho
    rw [hr.mem]
    refine post_eq hl ?_ hk hi ho
    rw [h.val]; rfl

end

/-- What the iteration needs of a hash function: the sizes of the code, that
the padding is the hash function's, and that it is the hash function `S` of
the specification. -/
structure HashOk (P : It) (Wi : Nat) (S : StreamingHash) (H : Md P.B P.N L) (iv : H.HV) : Prop where
  sizes : Sizes P Wi
  pad : P.pad.map (BitVec.ofNat 8) = H.tailPad P.D
  reloc : H.Reloc
  out : OutOk H P.D P.out
  link : H.Link S iv P.D

theorem correct {P : It} {Wi : Nat} {S : StreamingHash} {H : Md P.B P.N L} {iv : H.HV}
    (ho : HashOk P Wi S H iv) (hf : CalleeOk H P.CW P.cmpC) {s₀ : State} (hp : Pre P Wi s₀) :
    WP isa P.iterate s₀ fun s' => abiPreserved s₀ s' ∧ (iterK S Wi).post s₀ s' := by
  unfold It.iterate
  refine WP.seq (WP.mono (prologue_ok hp ho.sizes ho.pad) fun s₁ h => ?_)
  exact WP.seq (WP.mono (loop_ok hp ho.sizes ho.reloc hf ho.out h) fun s₂ h₂ =>
    epilogue_ok hp ho.sizes ho.link h₂)

end VG.Proof.Pbkdf2.RISCV64
