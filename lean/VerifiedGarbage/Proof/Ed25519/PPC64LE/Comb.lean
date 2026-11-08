module

-- separate module: its proofs build in parallel with `Encode`'s, which `ScalarBase` also imports

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Comb
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.WindowDigit
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.BaseContract
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldProg
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointOps
public import VerifiedGarbage.Proof.Ed25519.CombDigits64
public import VerifiedGarbage.Proof.Ed25519.Group.Extended
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Ed25519.CombDigits
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointTable
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointMul
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Ed25519's base-point multiplication on PPC64LE: the comb

What `combMultiply` computes, as RISC-V's comb does (`Proof/Ed25519/RISCV64/Comb.lean`).

*The digits.* `combCopy` leaves digit `i`'s nibble `n` of the scalar at `p`, `nibAt` (the
nibble of byte `i / 2`, its high one for odd `i`), at byte `SCAL + i` of the working space
(`combCopy_ok`); `combDigit` leaves the mask of its sign (all ones for `n < 8`) at byte `SGN`,
in `maskReg 1 … 8` the masks of the magnitudes, all ones exactly for `magOf n`, the magnitude
of `n - 8`, and in `r17` 1 exactly for the magnitude 0 (`combDigit_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519 VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.X25519 (sel)

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem comb_ld {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hin : InRegions (s.rd ++ s.wr) a 8) (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

theorem comb_std {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hout : InRegions s.wr a 8) (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem comb_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem comb_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (Upd.write _ _ _))

theorem comb_adrSym {d : Reg} {name : String} (hd : d ≠ .r0)
    (k : ∀ s', Upd s s' d (s.syms name) → s'.syms = s.syms → WP isa (.block is) s' Q) :
    WP isa (.block (.adrSym d name :: is)) s Q := by
  have u := Upd.write s d (s.syms name)
  exact WP.cons (exec_adrSym hd) (k _ ⟨u.gpr, u.other, u.mem, u.rd, u.wr, u.sp⟩ rfl)

end

/-! ## The digits -/

/-- Byte `i` of the scalar's nibbles in the working space at `b`. -/
def nibC (m : Mem) (b : Addr) (i : Nat) : Nat := (m (b + BitVec.ofNat 64 (SCAL + i))).toNat

/-- The magnitude of the digit `n - 8`. -/
def magOf (n : Nat) : Nat := if n < 8 then 8 - n else n - 8

theorem magOf_le {n : Nat} (hn : n < 16) : magOf n ≤ 8 := by
  unfold magOf; split <;> omega

/-- All ones for `true`, zero for `false`. -/
def maskB (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

private theorem mask_fact : ∀ a ≤ 8, ∀ k < 8,
    BitVec.ofNat 64 0 - (((BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 (k + 1)) - BitVec.ofNat 64 1) >>> 63) =
      maskB (decide (a = k + 1)) := by decide

private theorem sign_fact : ∀ n < 16,
    BitVec.ofNat 64 0 - ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) >>> 63) = maskB (decide (n < 8)) ∧
      ((BitVec.ofNat 64 n - BitVec.ofNat 64 8) ^^^ maskB (decide (n < 8))) - maskB (decide (n < 8)) =
        BitVec.ofNat 64 (magOf n) := by decide

private theorem identity_fact : ∀ a ≤ 8,
    (BitVec.ofNat 64 a - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if a = 0 then 1 else 0) := by decide

/-- The mask registers. -/
abbrev maskRegs : List Reg := [.r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11]

private theorem maskReg_fact : ∀ k < 8,
    maskReg (k + 1) ≠ .r0 ∧ maskReg (k + 1) ≠ .r12 ∧ maskReg (k + 1) ≠ .r17 ∧
      maskReg (k + 1) ∈ maskRegs := by decide

private theorem maskReg_ne : ∀ k < 8, ∀ k' < 8, k' ≠ k → maskReg (k' + 1) ≠ maskReg (k + 1) := by
  decide

/-- The masks of the magnitudes, from the magnitude `a` in `r12` and zero in `r0`. -/
structure MaskInv (s₀ : State) (a : Nat) (k : Nat) (s : State) : Prop where
  rest : Rest maskRegs s₀ s
  mem : s.mem = s₀.mem
  masks : ∀ k' < k, s.gpr (maskReg (k' + 1)) = maskB (decide (a = k' + 1))

theorem combMasks_ok {s₀ : State} {a : Nat} (ha : a ≤ 8) (h0 : s₀.gpr .r0 = BitVec.ofNat 64 0)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 a) :
    WP isa (.block ((List.range 8).flatMap fun k => combMask (k + 1))) s₀ (MaskInv s₀ a 8) := by
  refine wp_range_flatMap (M := isa) (MaskInv s₀ a) (fun k s hk h => ?_) 8 (Nat.le_refl _) s₀
    ⟨Rest.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have m := maskReg_fact k hk
  have g0 : s.gpr .r0 = BitVec.ofNat 64 0 := (h.rest.gpr _ (by decide)).trans h0
  have g12 : s.gpr .r12 = BitVec.ofNat 64 a := (h.rest.gpr _ (by decide)).trans h12
  unfold combMask
  refine wp_li (by omega) fun s₁ u₁ => wp_xor fun s₂ u₂ => wp_subi m.1 (by decide) fun s₃ u₃ =>
    comb_lsr (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => WP.block_nil ?_
  have hr : ∀ {t t' : State} {v : BitVec 64}, Upd t t' (maskReg (k + 1)) v → Rest maskRegs t t' :=
    fun u => u.rest m.2.2.2
  refine ⟨h.rest.trans ((hr u₁).trans ((hr u₂).trans ((hr u₃).trans ((hr u₄).trans (hr u₅))))), ?_,
    fun k' hk' => ?_⟩
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, h.mem]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · have ne := maskReg_ne k hk k' (by omega) (by omega)
      rw [u₅.other _ ne, u₄.other _ ne, u₃.other _ ne, u₂.other _ ne, u₁.other _ ne]
      exact h.masks k' hk'
    · rw [u₅.gpr, u₄.other _ m.1.symm, u₃.other _ m.1.symm, u₂.other _ m.1.symm, u₁.other _ m.1.symm, g0,
        u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ m.2.1.symm, u₁.gpr, g12]
      exact mask_fact a ha k' hk

/-- The registers `combDigit` writes. -/
abbrev digitR : List Reg := [.r0, .r3, .r4, .r5, .r7, .r8, .r9, .r10, .r11, .r12, .r17]

theorem combDigit_ok {b : Addr} {s : State} (hc : Ctx8 b s) {i : Nat} (hi : i < 64)
    (h15 : s.gpr .r15 = BitVec.ofNat 64 i) (hn : nibC s.mem b i < 16) :
    WP isa (.block combDigit) s fun t =>
      Rest digitR s t ∧
      t.mem = s.mem.writeW (b + BitVec.ofNat 64 SGN) (maskB (decide (nibC s.mem b i < 8))) ∧
      (∀ k < 8, t.gpr (maskReg (k + 1)) = maskB (decide (magOf (nibC s.mem b i) = k + 1))) ∧
      t.gpr .r17 = BitVec.ofNat 64 (if magOf (nibC s.mem b i) = 0 then 1 else 0) := by
  have hS : SCAL = 1152 := rfl
  unfold combDigit
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_add fun s₁ u₁ => ?_
  have ea : s₁.gpr .r12 + BitVec.ofNat 64 SCAL = b + BitVec.ofNat 64 (SCAL + i) := by
    rw [u₁.gpr, hc.r6, h15, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm i SCAL]
  refine wp_lbz (a := b + BitVec.ofNat 64 (SCAL + i)) (by decide) (by rw [hS]; omega) ea
    (by rw [u₁.rd, u₁.wr]; exact hc.inR (by omega)) fun s₂ u₂ => ?_
  have e2 : s₂.gpr .r12 = BitVec.ofNat 64 (nibC s.mem b i) := by rw [u₂.gpr, u₁.mem]; rfl
  have sf := sign_fact _ hn
  refine wp_li (by decide) fun s₃ u₃ => wp_subi (by decide) (by decide) fun s₄ u₄ =>
    comb_lsr (by decide) fun s₅ u₅ => wp_sub fun s₆ u₆ => ?_
  have g6 : s₆.gpr .r11 = maskB (decide (nibC s.mem b i < 8)) := by
    rw [u₆.gpr, u₅.other .r0 (by decide), u₄.other .r0 (by decide), u₃.gpr, u₅.gpr, u₄.gpr,
      u₃.other .r12 (by decide), e2]
    exact sf.1
  have r6 : Rest [.r0, .r11, .r12] s s₆ :=
    (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest (by decide)).trans
      ((u₄.rest (by decide)).trans ((u₅.rest (by decide)).trans (u₆.rest (by decide))))))
  have m6 : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hc6 : Ctx8 b s₆ := hc.of_rest r6 (by decide)
  refine comb_std (a := b + BitVec.ofNat 64 SGN) (by decide) ⟨by decide, by decide⟩ (by rw [hc6.r6])
    (hc6.inW (by decide)) fun s₇ u₇ => wp_xor fun s₈ u₈ => wp_sub fun s₉ u₉ => ?_
  have g9 : s₉.gpr .r12 = BitVec.ofNat 64 (magOf (nibC s.mem b i)) := by
    rw [u₉.gpr, u₈.gpr, u₈.other .r11 (by decide), u₇.gpr, g6, u₆.other .r12 (by decide),
      u₅.other .r12 (by decide), u₄.gpr, u₃.other .r12 (by decide), e2]
    exact sf.2
  have g0 : s₉.gpr .r0 = BitVec.ofNat 64 0 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have m9 : s₉.mem = s.mem.writeW (b + BitVec.ofNat 64 SGN) (maskB (decide (nibC s.mem b i < 8))) := by
    rw [u₉.mem, u₈.mem, u₇.mem, g6, m6]
  have r9 : Rest [.r0, .r11, .r12] s s₉ :=
    r6.trans ((u₇.rest _).trans ((u₈.rest (by decide)).trans (u₉.rest (by decide))))
  refine WP.block_nil (WP.mono (combMasks_ok (magOf_le hn) g0 g9) fun t h => ?_)
  refine wp_subi (by decide) (by decide) fun t₁ v₁ => comb_lsr (by decide) fun t₂ v₂ => WP.block_nil ?_
  have g12 : t.gpr .r12 = BitVec.ofNat 64 (magOf (nibC s.mem b i)) := (h.rest.gpr _ (by decide)).trans g9
  refine ⟨(r9.mono (by decide)).trans ((h.rest.mono (by decide)).trans ((v₁.rest (by decide)).trans
      (v₂.rest (by decide)))), by rw [v₂.mem, v₁.mem, h.mem, m9], fun k hk => ?_, ?_⟩
  · have m := maskReg_fact k hk
    rw [v₂.other _ m.2.2.1, v₁.other _ m.2.2.1]
    exact h.masks k hk
  · rw [v₂.gpr, v₁.gpr, g12]
    exact identity_fact _ (magOf_le hn)

/-! ## The selection -/

/-- The comb's tables at `T` in `s`: not wrapping around, readable, and their doublewords. -/
structure TblAt (s : State) (T : Addr) : Prop where
  fit : T.toNat + 49152 ≤ 2 ^ 64
  rd : InRegions (s.rd ++ s.wr) T 49152
  words : ∀ q < 64 * 96, s.mem.readW (T + BitVec.ofNat 64 (8 * q)) 64 = combWord q

theorem TblAt.of_frame {s t : State} {T : Addr} {L : List Region} (h : TblAt s T)
    (hr : t.rd ++ t.wr = s.rd ++ s.wr) (hf : Frame L s.mem t.mem) (hd : ∀ r ∈ L, (TBL T).Disjoint r) :
    TblAt t T :=
  ⟨h.fit, hr ▸ h.rd, fun q hq => by
    rw [← h.words q hq]
    exact hf.readW (r := TBL T) (Offset.contains_base T (by omega) (by omega)) hd (by decide)⟩

/-- Doubleword `j` of coordinate `c` of entry `a` of table `i`: the identity's `[1, 1, 0]` for
`a = 0`. -/
def selDw (i a c j : Nat) : Nat := (combCoord (combCached64 i a) c).val / 2 ^ (64 * j) % 2 ^ 64

theorem selDw_lt (i a c j : Nat) : selDw i a c j < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem selDw_succ (i m c j : Nat) : selDw i (m + 1) c j = combDw i m c j := rfl

private theorem selDw_zero_fact : ∀ c < 3, ∀ j < 4,
    (combCoord ⟨1, 1, 0, 2⟩ c).val / 2 ^ (64 * j) % 2 ^ 64 = if c < 2 ∧ j = 0 then 1 else 0 := by
  decide

theorem selDw_zero (i c j : Nat) (hc : c < 3) (hj : j < 4) :
    selDw i 0 c j = if c < 2 ∧ j = 0 then 1 else 0 := by
  have e : combCached64 i 0 = ⟨1, 1, 0, 2⟩ := by
    unfold combCached64 combCached combCached16; split <;> rfl
  rw [selDw, e]
  exact selDw_zero_fact c hc j hj

private theorem cand_fact (a m : Nat) (x w : BitVec 64) :
    x ||| (w &&& maskB (decide (a = m + 1))) = if a = m + 1 then x ||| w else x := by
  by_cases h : a = m + 1
  · rw [ite_eq_left h, maskB, ite_eq_left (decide_eq_true h), BitVec.and_allOnes]
  · rw [ite_eq_right h, maskB, ite_eq_right (by simp [h])]
    show x ||| (w &&& 0#64) = x
    rw [BitVec.and_zero, BitVec.or_zero]

private theorem maskReg_out : ∀ m < 8, maskReg (m + 1) ∉ [Reg.r0, .r12] := by decide

/-- The registers and table the selection reads. -/
structure SelCtx (b T : Addr) (i a : Nat) (s : State) : Prop where
  ctx : Ctx8 b s
  r16 : s.gpr .r16 = T + BitVec.ofNat 64 (768 * i)
  masks : ∀ k < 8, s.gpr (maskReg (k + 1)) = maskB (decide (a = k + 1))
  r17 : s.gpr .r17 = BitVec.ofNat 64 (if a = 0 then 1 else 0)
  tbl : TblAt s T
  apart : (TBL T).Disjoint ⟨b, 8192⟩

theorem SelCtx.of_rest {b T : Addr} {i a : Nat} {s t : State} (h : SelCtx b T i a s)
    (hr : Rest [.r0, .r12] s t) (hf : Frame [⟨b, 8192⟩] s.mem t.mem) : SelCtx b T i a t :=
  ⟨h.ctx.of_rest hr (by decide), (hr.gpr _ (by decide)).trans h.r16,
    fun k hk => (hr.gpr _ (maskReg_out k hk)).trans (h.masks k hk), (hr.gpr _ (by decide)).trans h.r17,
    h.tbl.of_frame (by rw [hr.rd, hr.wr]) hf (by simpa only [List.mem_singleton, forall_eq] using h.apart),
    h.apart⟩

theorem selectCand_ok {b T : Addr} {i a c j m : Nat} {s : State} (h : SelCtx b T i a s)
    (hi : i < 64) (hc : c < 3) (hj : j < 4) (hm : m < 8) :
    WP isa (.block (selectCand (96 * m + 32 * c + 8 * j) m)) s fun t =>
      t.gpr .r12 = s.gpr .r12 ||| (BitVec.ofNat 64 (combDw i m c j) &&& maskB (decide (a = m + 1))) ∧
      Rest [.r0, .r12] s t ∧ t.mem = s.mem := by
  have fit := h.tbl.fit
  have q_lt : 96 * i + 12 * m + 4 * c + j < 64 * 96 := by omega
  have e : 768 * i + (96 * m + 32 * c + 8 * j) = 8 * (96 * i + 12 * m + 4 * c + j) := by omega
  have ha : s.gpr .r16 + BitVec.ofNat 64 (96 * m + 32 * c + 8 * j) =
      T + BitVec.ofNat 64 (8 * (96 * i + 12 * m + 4 * c + j)) := by
    rw [h.r16, BitVec.add_assoc, ← BitVec.ofNat_add, e]
  have hv := h.tbl.words _ q_lt
  have lv : combWord (96 * i + 12 * m + 4 * c + j) = BitVec.ofNat 64 (combDw i m c j) := by
    unfold combWord; congr 2 <;> omega
  have mm := h.masks m hm
  have hne : maskReg (m + 1) ≠ .r0 := (maskReg_fact m hm).1
  unfold selectCand
  refine comb_ld (by decide) ⟨by omega, by omega⟩ ha
    (CallLay.inRegions_sub h.tbl.rd (by omega) (by decide)) fun s₁ u₁ =>
    wp_and fun s₂ u₂ => comb_or fun s₃ u₃ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans (u₃.rest (by decide))),
    by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  rw [u₃.gpr, u₂.other .r12 (by decide), u₁.other .r12 (by decide), u₂.gpr, u₁.gpr, hv, lv,
    u₁.other _ hne, mm]

/-! ## Doublewords of the working space -/

/-- The doubleword at `P + d`, as a number. -/
def cdw (m : Mem) (P : Addr) (d : Nat) : Nat := (m.readW (P + BitVec.ofNat 64 d) 64).toNat

private theorem join_byte (x y : BitVec 32) {i : Nat} (hi : i < 8) :
    (x.setWidth 64 <<< 32 ||| y.setWidth 64).extractLsb' (8 * i) 8 =
      if i < 4 then y.extractLsb' (8 * i) 8 else x.extractLsb' (8 * (i - 4)) 8 := by
  ext j hj
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  split
  · simp only [BitVec.getElem_extractLsb']
    simp (disch := omega) [show 8 * i + j < 32 by omega, show 8 * i + j < 64 by omega]
  · simp only [BitVec.getElem_extractLsb']
    simp (disch := omega) [show ¬ 8 * i + j < 32 by omega, show 8 * i + j < 64 by omega,
      show 8 * i + j - 32 = 8 * (i - 4) + j by omega]
    intro; omega

/-- A little-endian doubleword is its two words. -/
private theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = (m.readW (a + BitVec.ofNat 64 4) 32).setWidth 64 <<< 32 |||
      (m.readW a 32).setWidth 64 := by
  show m.read a 8 = _
  refine Mem.read_eq_of_bytes fun i hi => ?_
  rw [join_byte _ _ hi]
  split
  · exact Mem.readW_byte m a ‹_›
  · rw [← Mem.readW_byte m _ (by omega), BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    congr 3; omega

/-- A doubleword is its two words. -/
theorem cdw_split (m : Mem) (P : Addr) (d : Nat) : cdw m P d = wd m P d + 2 ^ 32 * wd m P (d + 4) := by
  unfold cdw wd
  rw [readW64_split, Offset.add_add]
  have h1 := (m.readW (P + BitVec.ofNat 64 d) 32).isLt
  have h2 := (m.readW (P + BitVec.ofNat 64 (d + 4)) 32).isLt
  generalize m.readW (P + BitVec.ofNat 64 d) 32 = lo at *
  generalize m.readW (P + BitVec.ofNat 64 (d + 4)) 32 = hi at *
  have e : (hi.setWidth 64 <<< 32 ||| lo.setWidth 64) = hi.setWidth 64 <<< 32 + lo.setWidth 64 := by
    rw [BitVec.add_eq_or_of_and_eq_zero]
    ext i hi'
    simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth,
      BitVec.getElem_zero]
    by_cases h : i < 32
    · simp [h]
    · simp [h, BitVec.getLsbD_of_ge lo i (by omega)]
  rw [e, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by omega : lo.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega : hi.toNat < 2 ^ 64),
    Nat.shiftLeft_eq]
  omega_using [h1, h2]

theorem cdw_write_self (m : Mem) (P : Addr) (d : Nat) (v : BitVec 64) :
    cdw (m.writeW (P + BitVec.ofNat 64 d) v) P d = v.toNat := by
  rw [cdw, Mem.readW_writeW_self64]

theorem cdw_write_other (m : Mem) (P : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    cdw (m.writeW (P + BitVec.ofNat 64 e) v) P d = cdw m P d := by
  rw [cdw, Mem.readW_writeW_sep (Offset.sep P h hd he) (by decide), cdw]

/-- Four doublewords, lowest first. -/
def cval4 (f : Nat → Nat) : Nat := f 0 + 2 ^ 64 * (f 1 + 2 ^ 64 * (f 2 + 2 ^ 64 * f 3))

theorem cval4_congr {f g : Nat → Nat} (h : ∀ i < 4, f i = g i) : cval4 f = cval4 g := by
  unfold cval4
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)]

/-- The number of an element is its four doublewords. -/
theorem V_eq4 (m : Mem) (P : Addr) (o : Nat) : V m P o = cval4 (fun j => cdw m P (o + 8 * j)) := by
  simp only [V, cval4, val32, limb, cdw_split]
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]
  omega_arith

theorem val4_digits (v : Nat) :
    cval4 (fun j => v / 2 ^ (64 * j) % 2 ^ 64) = v % 2 ^ 256 := by
  simp only [cval4, Nat.mul_zero, Nat.mul_one, show 64 * 2 = 128 from rfl, show 64 * 3 = 192 from rfl,
    Nat.pow_zero, Nat.div_one]
  omega

/-! ## The selection, continued -/

theorem selectDw_ok {b T : Addr} {i a c j : Nat} {s : State} (h : SelCtx b T i a s)
    (hi : i < 64) (ha : a ≤ 8) (hc : c < 3) (hj : j < 4) :
    WP isa (.block (selectDw c j)) s fun t =>
      Rest [.r0, .r12] s t ∧
      t.mem = s.mem.writeW (b + BitVec.ofNat 64 (64 + 32 * (4 + c) + 8 * j))
        (BitVec.ofNat 64 (selDw i a c j)) := by
  unfold selectDw
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The start: the identity's doubleword.
  have start : WP isa (.block (if c < 2 ∧ j = 0 then [.addi .r12 .r17 0] else [.li .r12 0])) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 (if a = 0 ∧ c < 2 ∧ j = 0 then 1 else 0) ∧ Rest [.r0, .r12] s t ∧
        t.mem = s.mem := by
    split
    · rename_i hcj
      refine wp_addi (by decide) (by decide) fun s₁ u₁ => WP.block_nil ⟨?_, u₁.rest (by decide), u₁.mem⟩
      rw [u₁.gpr, h.r17, BitVec.add_zero]
      by_cases a0 : a = 0 <;> simp [a0, hcj]
    · rename_i hcj
      refine wp_li (by decide) fun s₁ u₁ => WP.block_nil ⟨?_, u₁.rest (by decide), u₁.mem⟩
      rw [u₁.gpr]
      simp only [hcj, and_false, ↓reduceIte]
  refine WP.mono start fun s₀ ⟨g₀, r₀, m₀⟩ => ?_
  -- The candidates.
  have h₀ := h.of_rest r₀ (by rw [m₀]; exact Frame.refl _ _)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n t => SelCtx b T i a t ∧ Rest [.r0, .r12] s₀ t ∧ t.mem = s₀.mem ∧
      t.gpr .r12 = BitVec.ofNat 64 (if 1 ≤ a ∧ a ≤ n then selDw i a c j else
        if a = 0 ∧ c < 2 ∧ j = 0 then 1 else 0))
    (fun n t hn ⟨ht, rt, mt, gt⟩ => ?_) 8 (Nat.le_refl _) s₀
    ⟨h₀, Rest.refl _ _, rfl, by rw [g₀, ite_eq_right (show ¬(1 ≤ a ∧ a ≤ 0) by omega)]⟩) fun s₁ ⟨h₁, r₁, m₁, g₁⟩ => ?_
  · refine WP.mono (selectCand_ok ht hi hc hj hn) fun u ⟨gu, ru, mu⟩ =>
      ⟨ht.of_rest ru (by rw [mu]; exact Frame.refl _ _), rt.trans ru, mu.trans mt, ?_⟩
    rw [gu, gt, cand_fact a n]
    by_cases e : a = n + 1
    · subst e
      rw [ite_eq_left rfl, ite_eq_right (show ¬(1 ≤ n + 1 ∧ n + 1 ≤ n) by omega),
        ite_eq_right (show ¬(n + 1 = 0 ∧ c < 2 ∧ j = 0) by omega),
        ite_eq_left (show 1 ≤ n + 1 ∧ n + 1 ≤ n + 1 from ⟨by omega, Nat.le_refl _⟩), selDw_succ]
      exact BitVec.zero_or
    · rw [ite_eq_right e]
      congr 1
      by_cases h1 : 1 ≤ a ∧ a ≤ n
      · rw [ite_eq_left h1, ite_eq_left (show 1 ≤ a ∧ a ≤ n + 1 from ⟨h1.1, by omega⟩)]
      · rw [ite_eq_right h1, ite_eq_right (show ¬(1 ≤ a ∧ a ≤ n + 1) by omega)]
  -- The store.
  have hc₁ := h₁.ctx
  refine comb_std (a := b + BitVec.ofNat 64 (64 + 32 * (4 + c) + 8 * j)) (by decide) ⟨by omega, by omega⟩
    (by rw [hc₁.r6]) (hc₁.inW (by omega)) fun t ut => WP.block_nil ⟨r₀.trans (r₁.trans (ut.rest _)), ?_⟩
  have sel : (if 1 ≤ a ∧ a ≤ 8 then selDw i a c j else if a = 0 ∧ c < 2 ∧ j = 0 then 1 else 0) =
      selDw i a c j := by
    rcases Nat.eq_zero_or_pos a with a0 | apos
    · subst a0
      rw [ite_eq_right (show ¬(1 ≤ 0 ∧ 0 ≤ 8) by omega), selDw_zero i c j hc hj]
      by_cases hcj : c < 2 ∧ j = 0
      · rw [ite_eq_left ⟨rfl, hcj⟩, ite_eq_left hcj]
      · rw [ite_eq_right (fun h => hcj h.2), ite_eq_right hcj]
    · rw [ite_eq_left ⟨apos, ha⟩]
  rw [ut.mem, m₁, m₀, g₁, sel]

/-- The slots 4–6 the selection writes. -/
abbrev selR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 192, 96⟩

/-- The selection's invariant after `q` doublewords. -/
structure SelInv (b T : Addr) (i a : Nat) (s₀ : State) (q : Nat) (s : State) : Prop where
  sel : SelCtx b T i a s
  rest : Rest [.r0, .r12] s₀ s
  frame : Frame [selR b] s₀.mem s.mem
  dws : ∀ q' < q, cdw s.mem b (192 + 8 * q') = selDw i a (q' / 4) (q' % 4)

theorem combSelect_ok {b T : Addr} {i a : Nat} {s : State} (h : SelCtx b T i a s) (hi : i < 64)
    (ha : a ≤ 8) :
    WP isa (.block combSelect) s fun t =>
      Rest [.r0, .r12] s t ∧ Frame [selR b] s.mem t.mem ∧
      ∀ q < 12, cdw t.mem b (192 + 8 * q) = selDw i a (q / 4) (q % 4) := by
  unfold combSelect
  refine WP.mono (wp_range_flatMap (M := isa) (SelInv b T i a s) (fun q t hq h => ?_) 12
    (Nat.le_refl _) s ⟨h, Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun t h => ⟨h.rest, h.frame, h.dws⟩
  have e : 64 + 32 * (4 + q / 4) + 8 * (q % 4) = 192 + 8 * q := by omega
  refine WP.mono (selectDw_ok h.sel hi ha (by omega) (Nat.mod_lt _ (by decide))) fun u ⟨ru, mu⟩ => ?_
  rw [e] at mu
  have fw : Frame [selR b] t.mem u.mem := by
    rw [mu]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains b (by omega) (by omega) (by omega))
  refine ⟨h.sel.of_rest ru (fw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base b (by decide)⟩),
    h.rest.trans ru, h.frame.trans fw, fun q' hq' => ?_⟩
  rw [mu]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
  · rw [cdw_write_other _ _ _ (by omega) (by omega) (by omega)]
    exact h.dws q' hq'
  · rw [cdw_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (selDw_lt i a _ _)]

/-! ## The slots -/

/-- The selected entry's coordinate `c` in slot `4 + c`. -/
theorem sel_env {m : Mem} {b : Addr} {i a : Nat}
    (h : ∀ q < 12, cdw m b (192 + 8 * q) = selDw i a (q / 4) (q % 4))
    (sl : Slot) (c : Nat) (hc : c < 3) (hs : sl.val = 4 + c) :
    env m b sl = combCoord (combCached64 i a) c := by
  have hv : V m b (offset sl) = (combCoord (combCached64 i a) c).val := by
    rw [V_eq4]
    have hl : ∀ j < 4, cdw m b (offset sl + 8 * j) =
        (combCoord (combCached64 i a) c).val / 2 ^ (64 * j) % 2 ^ 64 := fun j hj => by
      have e := h (4 * c + j) (by omega)
      rw [show (4 * c + j) / 4 = c by omega, show (4 * c + j) % 4 = j by omega,
        show 192 + 8 * (4 * c + j) = offset sl + 8 * j by simp only [offset, hs]; omega] at e
      exact e
    rw [cval4_congr hl, val4_digits,
      Nat.mod_eq_of_lt (Nat.lt_trans (combCoord (combCached64 i a) c).isLt (by decide))]
  simp only [env, FS, hv, VG.Proof.X25519.toFe_self]

/-! ## The addition -/

/-- What `addAffineOps` computes, from the point's coordinates and the cached entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> grind

theorem addAffineOps_formula (e : Env) :
    point (evalOps addAffineOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) :=
  rfl

/-! ## The step -/

theorem maskB_eq (b : Bool) : maskB b = 0 - BitVec.ofNat 64 b.toNat := by cases b <;> decide

theorem magOf_eq (n : Nat) : magOf n = Proof.Ed25519.mag n := rfl

/-- Nibble `i` of a little-endian number is that of byte `i / 2` of its bytes. -/
theorem nib_decodeLE (bs : List Byte) (i : Nat) :
    Proof.Ed25519.nib (Spec.Ed25519.decodeLE bs) i = (bs.getD (i / 2) 0).toNat / 16 ^ (i % 2) % 16 := by
  have hb := Proof.Ed25519.decodeLE_byte bs (i / 2)
  have e16 : 16 ^ i = 256 ^ (i / 2) * 16 ^ (i % 2) := by
    conv_lhs => rw [← Nat.div_add_mod i 2, pow_add, pow_mul]
    rfl
  rw [Proof.Ed25519.nib, e16, ← Nat.div_div_eq_div_mul]
  generalize Spec.Ed25519.decodeLE bs / 256 ^ (i / 2) = y at hb
  generalize (bs.getD (i / 2) 0).toNat = b at hb ⊢
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [h, pow_zero, Nat.div_one, Nat.div_one]; omega
  · rw [h, pow_one]; omega

/-- Nibble `i` of the scalar's bytes is the decoded scalar's. -/
theorem nibAt_eq (m : Mem) (p : Addr) {i : Nat} (hi : i < 64) :
    nibAt m p i = Proof.Ed25519.nib (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32)) i := by
  have hg : (Spec.Ed25519.bytesAt m p 32).getD (i / 2) 0 = m (p + BitVec.ofNat 64 (i / 2)) := by
    simp [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, show i / 2 < 32 by omega]
  rw [nib_decodeLE, hg, nibAt]

/-- The sign's mask in the working space. -/
abbrev SGNR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SGN, 8⟩

/-- What a step writes: the sign's mask and the field area. -/
abbrev stepW (b : Addr) : List Region := [SGNR b, FA b]

/-- The registers a step writes. -/
abbrev stepR : List Reg := .r15 :: .r16 :: .r17 :: fclob

/-- What the loop never changes: the tables, apart from the working space. -/
structure CombEnv (s₀ : State) (b T : Addr) : Prop where
  tbl : TblAt s₀ T
  apart : (TBL T).Disjoint ⟨b, 8192⟩

/-- The loop's invariant, after `j` steps. -/
structure CombInv (s₀ : State) (b T : Addr) (S : Nat) (j : Nat) (s : State) : Prop where
  bound : j ≤ 64
  ctx : Ctx8 b s
  r15 : s.gpr .r15 = BitVec.ofNat 64 j
  r16 : s.gpr .r16 = T + BitVec.ofNat 64 (768 * j)
  zero : env s.mem b 21 = 0
  acc : Rep (point (env s.mem b) 0 1 2 3) ((((17 * combGVal : Nat) : ℤ) + digitSum64 S j) • baseAff)
  rest : Rest stepR s₀ s
  frame : Frame (stepW b) s₀.mem s.mem
  scalar : ∀ i < 64, nibC s.mem b i = Proof.Ed25519.nib S i

theorem stepW_ws {b : Addr} {m m' : Mem} (hf : Frame (stepW b) m m') : Frame [⟨b, 8192⟩] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base _ (by decide)⟩

/-- The scalar's nibbles are apart from what a step writes. -/
theorem scal_apart {b : Addr} {m m' : Mem} (hf : Frame (stepW b) m m') {i : Nat} (hi : i < 64) :
    nibC m' b i = nibC m b i := by
  unfold nibC
  refine congrArg _ (hf _ fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fun hc => Offset.disjoint b (d := SCAL + i) (n := 1) (e := SGN) (k := 8) (.inr (by
      simp only [SCAL, SGN]; omega)) (by simp only [SCAL]; omega) (by decide) _ (Region.contains_self _ _) hc
  · exact fun hc => Offset.disjoint b (d := SCAL + i) (n := 1) (e := 64) (k := 960) (.inr (by
      simp only [SCAL]; omega)) (by simp only [SCAL]; omega) (by decide) _ (Region.contains_self _ _) hc

private theorem next_fact : ∀ j < 64,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 64) != 0) = decide (j + 1 ≠ 64) := by decide

/-- The region `[d, d + n)` of the working space is apart from slot `sl` unless they meet. -/
theorem slot_apart {b : Addr} (sl : Slot) {d n : Nat} (h : d + n ≤ offset sl ∨ offset sl + 32 ≤ d)
    (hn : d + n ≤ 8192) :
    (⟨b + BitVec.ofNat 64 (offset sl), 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 d, n⟩ :=
  Offset.disjoint _ (by omega) (by simp only [offset]; have := sl.isLt; omega) (by omega)

theorem combStep_ok {s₀ s : State} {b T : Addr} {S j : Nat} (E : CombEnv s₀ b T)
    (h : CombInv s₀ b T S j s) (hj : j < 64) :
    WP isa combStep s fun t => isa.eval (.nonzero .d .r7) t = some (decide (j + 1 ≠ 64)) ∧
      CombInv s₀ b T S (j + 1) t := by
  have nf := next_fact j hj
  have hnib : nibC s.mem b j = Proof.Ed25519.nib S j := h.scalar j hj
  have n_lt : nibC s.mem b j < 16 := by rw [hnib]; exact Proof.Ed25519.nib_lt S j
  have hrr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rest.rd, h.rest.wr]
  have hT : TblAt s T := E.tbl.of_frame hrr (stepW_ws h.frame) (by simpa only [List.mem_singleton, forall_eq] using E.apart)
  -- The digit and the selection.
  rw [combStep]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (combDigit_ok h.ctx hj h.r15 n_lt) fun u ⟨ru, mu, gm, g17⟩ => ?_
  have fu : Frame [SGNR b] s.mem u.mem := by
    rw [mu]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have cu := h.ctx.of_rest ru (by decide)
  have hTu : TblAt u T := hT.of_frame (by rw [ru.rd, ru.wr])
    (fu.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (show SGN + 8 ≤ 8192 by decide)⟩)
    (by simpa only [List.mem_singleton, forall_eq] using E.apart)
  have hsel : SelCtx b T j (magOf (nibC s.mem b j)) u :=
    ⟨cu, (ru.gpr _ (by decide)).trans h.r16, gm, g17, hTu, E.apart⟩
  refine WP.mono (combSelect_ok hsel hj (magOf_le n_lt)) fun v ⟨rv, fv, lv⟩ => ?_
  -- The slots after the selection.
  have envv : ∀ sl : Slot, (sl.val < 4 ∨ 7 ≤ sl.val) → env v.mem b sl = env s.mem b sl := fun sl hs => by
    rw [env_keep fv sl fun r hr => by
        rw [List.mem_singleton.mp hr]; exact slot_apart sl (by simp only [offset]; have := sl.isLt; omega) (by decide),
      env_keep fu sl fun r hr => by
        rw [List.mem_singleton.mp hr]; exact slot_apart sl (by simp only [offset, SGN]; omega) (by decide)]
  have ent : ∀ c < 3, ∀ sl : Slot, sl.val = 4 + c →
      env v.mem b sl = combCoord (combCached64 j (magOf (nibC s.mem b j))) c :=
    fun c hc sl hs => sel_env lv sl c hc hs
  have cv := cu.of_rest rv (by decide)
  have sgn : v.mem.readW (b + BitVec.ofNat 64 SGN) 64 = maskB (decide (nibC s.mem b j < 8)) := by
    rw [fv.readW (r := SGNR b) (Region.contains_self _ _)
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (by decide), mu, Mem.readW_writeW_self64]
  -- The negation.
  refine WP.seq ?_
  rw [combNeg, WP.seq_iff]
  refine WP.mono (fieldCode_ok [.sub 7 21 6] cv.ctx) fun w ⟨kw, ew⟩ => ?_
  have cw := cv.of_keep kw
  rw [List.singleton_append]
  have sgnw : w.mem.readW (b + BitVec.ofNat 64 SGN) 64 = maskB (decide (nibC s.mem b j < 8)) := by
    rw [kw.frame.readW (r := SGNR b) (Region.contains_self _ _)
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (by decide), sgn]
  refine comb_ld (a := b + BitVec.ofNat 64 SGN) (by decide) ⟨by decide, by decide⟩ (by rw [cw.r6])
    (cw.inR (by decide)) fun x₀ ux => ?_
  let sw := (decide (nibC s.mem b j < 8)).toNat
  have hsw : sw ≤ 1 := Bool.toNat_le _
  have cx₀ := cw.of_rest (ux.rest (ws := [.r11]) (by decide)) (by decide)
  have t0x : x₀.gpr .r11 = 0 - BitVec.ofNat 64 sw := by rw [ux.gpr, sgnw, maskB_eq]
  refine WP.append (cswapSlot_ok cx₀ hsw t0x 4 5 (by decide)) fun x₁ ⟨r₁, f₁, a₁, c₁, k₁⟩ => ?_
  refine WP.mono (cswapSlot_ok (cx₀.of_rest r₁ (by decide)) hsw (by rw [r₁.gpr _ (by decide), t0x]) 6 7 (by decide))
    fun x ⟨r₂, f₂, a₂, c₂, k₂⟩ => ?_
  have cx := (cx₀.of_rest r₁ (by decide)).of_rest r₂ (by decide)
  -- The addition.
  refine WP.seq (WP.mono (fieldCode_ok addAffineOps cx.ctx) fun y ⟨ky, ey⟩ => ?_)
  have cy := cx.of_keep ky
  -- The counter.
  refine wp_addi (imm := 1) (by decide) (by decide) fun z₁ uz₁ => wp_addi (imm := 768) (by decide) (by decide)
    fun z₂ uz₂ => wp_subi (imm := 64) (by decide) (by decide) fun z uz => WP.block_nil ?_
  have r15y : y.gpr .r15 = BitVec.ofNat 64 j := by
    rw [ky.rest.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), ux.other _ (by decide),
      kw.rest.gpr _ (by decide), rv.gpr _ (by decide), ru.gpr _ (by decide), h.r15]
  have r16y : y.gpr .r16 = T + BitVec.ofNat 64 (768 * j) := by
    rw [ky.rest.gpr _ (by decide), r₂.gpr _ (by decide), r₁.gpr _ (by decide), ux.other _ (by decide),
      kw.rest.gpr _ (by decide), rv.gpr _ (by decide), ru.gpr _ (by decide), h.r16]
  have r15z : z.gpr .r15 = BitVec.ofNat 64 (j + 1) := by
    rw [uz.other _ (by decide), uz₂.other _ (by decide), uz₁.gpr, r15y, nf.1]
  have restz : Rest stepR s z :=
    (ru.mono (by decide)).trans ((rv.mono (by decide)).trans ((kw.rest.mono (by decide)).trans
      ((ux.rest (ws := stepR) (by decide)).trans ((r₁.mono (by decide)).trans ((r₂.mono (by decide)).trans
      ((ky.rest.mono (by decide)).trans ((uz₁.rest (ws := stepR) (by decide)).trans
      ((uz₂.rest (ws := stepR) (by decide)).trans (uz.rest (ws := stepR) (by decide))))))))))
  have memz : z.mem = y.mem := by rw [uz.mem, uz₂.mem, uz₁.mem]
  have fz : Frame (stepW b) s.mem z.mem := by
    rw [memz]
    refine (fu.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans ?_
    refine ((fv.sub fun r hr => ⟨FA b, by simp, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by decide) (by decide)⟩).trans ?_)
    refine (kw.frame.mono (by simp)).trans ?_
    have f₁' := f₁
    rw [ux.mem] at f₁'
    exact (f₁'.mono (by simp)).trans ((f₂.mono (by simp)).trans (ky.frame.mono (by simp)))
  -- The entry's coordinates.
  obtain ⟨q, hq, hqz, hrq⟩ := Proof.Ed25519.combEntry64_ok j (Proof.Ed25519.nib S j) hj (Proof.Ed25519.nib_lt S j)
  rw [hnib] at ent sgn
  have e4 := ent 0 (by decide) 4 rfl
  have e5 := ent 1 (by decide) 5 rfl
  have e6 := ent 2 (by decide) 6 rfl
  have e21 : env v.mem b 21 = 0 := (envv 21 (.inr (by decide))).trans h.zero
  have w4 : env w.mem b 4 = env v.mem b 4 := by rw [ew]; rfl
  have w5 : env w.mem b 5 = env v.mem b 5 := by rw [ew]; rfl
  have w6 : env w.mem b 6 = env v.mem b 6 := by rw [ew]; rfl
  have w7 : env w.mem b 7 = env v.mem b 21 - env v.mem b 6 := by rw [ew]; rfl
  have wlow : ∀ i : Slot, i ≠ 7 → env w.mem b i = env v.mem b i := fun i hi => by
    rw [ew]; exact Function.update_of_ne hi _ _
  have ex₀ : env x₀.mem b = env w.mem b := by rw [ux.mem]
  have x4 : env x.mem b 4 = sel sw (env w.mem b 4) (env w.mem b 5) := by
    rw [k₂ 4 (by decide) (by decide), a₁, ex₀]
  have x5 : env x.mem b 5 = sel sw (env w.mem b 5) (env w.mem b 4) := by
    rw [k₂ 5 (by decide) (by decide), c₁, ex₀]
  have x6 : env x.mem b 6 = sel sw (env w.mem b 6) (env w.mem b 7) := by
    rw [a₂, k₁ 6 (by decide) (by decide), k₁ 7 (by decide) (by decide), ex₀]
  have xlow : ∀ i : Slot, (i.val < 4 ∨ 8 ≤ i.val) → env x.mem b i = env s.mem b i := fun i hi => by
    rw [k₂ i (fun e => by subst e; simp at hi) (fun e => by subst e; simp at hi),
      k₁ i (fun e => by subst e; simp at hi) (fun e => by subst e; simp at hi), ex₀,
      wlow i (fun e => by subst e; simp at hi)]
    exact envv i (by omega)
  have cq : env x.mem b 4 = q.Y - q.X ∧ env x.mem b 5 = q.Y + q.X ∧
      env x.mem b 6 = q.T * 2 * Spec.Ed25519.d := by
    have c0 : ∀ p, combCoord p 0 = p.X := fun _ => rfl
    have c1 : ∀ p, combCoord p 1 = p.Y := fun _ => rfl
    have c2 : ∀ p, combCoord p 2 = p.Z := fun _ => rfl
    rw [c0, magOf_eq] at e4
    rw [c1, magOf_eq] at e5
    rw [c2, magOf_eq] at e6
    rw [x4, x5, x6, w4, w5, w6, w7, e4, e5, e6, e21]
    have hc := congrArg (fun p => (p.X, p.Y, p.Z)) hq
    simp only [Proof.Ed25519.cache, Prod.mk.injEq] at hc
    by_cases hlt : Proof.Ed25519.nib S j < 8
    · have : sw = 1 := by simp only [sw, hnib, hlt, decide_true, Bool.toNat_true]
      simp only [hlt, ↓reduceIte, Proof.Ed25519.negCached] at hc
      simp only [sel, this, ↓reduceIte]
      exact hc
    · have : sw = 0 := by simp only [sw, hnib, hlt, decide_false, Bool.toNat_false]
      simp only [hlt, ↓reduceIte] at hc
      simp only [sel, this, show (0 : Nat) ≠ 1 from by decide, ↓reduceIte]
      exact hc
  refine ⟨?_, ⟨by omega, cy.of_rest ((uz₁.rest (ws := [.r15, .r16, .r7]) (by decide)).trans
      ((uz₂.rest (by decide)).trans (uz.rest (by decide)))) (by decide), r15z, ?_, ?_, ?_,
    h.rest.trans restz, h.frame.trans fz, fun i hi => ?_⟩⟩
  · rw [eval_nonzero, uz.gpr, uz₂.other _ (by decide), uz₁.gpr, r15y, nf.1, nf.2]
  · rw [uz.other _ (by decide), uz₂.gpr, uz₁.other _ (by decide), r16y, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 768 * j + 768 = 768 * (j + 1) by omega]
  · -- Slot 21 is still zero.
    rw [memz, ey]
    show env x.mem b 21 = 0
    rw [xlow 21 (.inr (by decide))]
    exact h.zero
  · -- The accumulator.
    rw [memz, ey, addAffineOps_formula, cq.1, cq.2.1, cq.2.2, xlow 0 (.inl (by decide)),
      xlow 1 (.inl (by decide)), xlow 2 (.inl (by decide)), xlow 3 (.inl (by decide))]
    have e := mixedResult_eq (point (env s.mem b) 0 1 2 3) q hqz
    simp only [point] at e
    rw [e, Proof.Ed25519.digitSum64, ← add_assoc, add_smul]
    exact pointAdd_rep h.acc (by simpa only [Proof.Ed25519.sdig] using hrq)
  · rw [scal_apart fz hi]; exact h.scalar i hi

/-- The loop, from step `j₀ < 64` to the end. -/
theorem combSteps_ok {s₀ s : State} {b T : Addr} {S j₀ : Nat} (E : CombEnv s₀ b T)
    (h : CombInv s₀ b T S j₀ s) (hj₀ : j₀ < 64) :
    WP isa (.loop combStep (.nonzero .d .r7)) s fun t => CombInv s₀ b T S 64 t := by
  apply WP.loop (fun n t => CombInv s₀ b T S (64 - n) t ∧ 0 < n ∧ n ≤ 64) (n := 64 - j₀)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    refine WP.mono (combStep_ok E ht (by omega)) fun u ⟨ue, hu⟩ => ?_
    by_cases hk : k = 0
    · subst hk
      exact Or.inl ⟨by rw [ue]; rfl, hu⟩
    · refine Or.inr ⟨by rw [ue]; simp only [show 64 - (k + 1) + 1 ≠ 64 by omega, ne_eq,
        not_false_eq_true, decide_true], k, by omega, ?_, by omega, by omega⟩
      rw [show 64 - k = 64 - (k + 1) + 1 by omega]; exact hu
  · exact ⟨by rw [show 64 - (64 - j₀) = j₀ by omega]; exact h, by omega, by omega⟩

/-! ## The scalar's nibbles -/

/-- The scalar's nibbles in the working space. -/
abbrev scalR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 SCAL, 64⟩

private theorem nib_facts : ∀ x : BitVec 8,
    ((BitVec.ofNat 64 x.toNat &&& BitVec.ofNat 64 15).setWidth 8).toNat = x.toNat / 16 ^ 0 % 16 ∧
      ((BitVec.ofNat 64 x.toNat >>> 4).setWidth 8).toNat = x.toNat / 16 ^ 1 % 16 := by
  decide

/-- The copy's invariant after `k` bytes. -/
structure CopyInv (s₀ : State) (b P : Addr) (k : Nat) (t : State) : Prop where
  rest : Rest [.r7, .r8, .r9] s₀ t
  r7 : t.gpr .r7 = BitVec.ofNat 64 15
  frame : Frame [scalR b] s₀.mem t.mem
  nibs : ∀ i < 2 * k, nibC t.mem b i = nibAt s₀.mem P i

theorem combCopy_ok {s : State} {b P : Addr} (hc : Ctx8 b s) (hp : s.gpr .r14 = P)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨P, 32⟩ : Region).Disjoint (scalR b)) :
    WP isa (.block combCopy) s fun t => Rest [.r7, .r8, .r9] s t ∧ Frame [scalR b] s.mem t.mem ∧
      ∀ i < 64, nibC t.mem b i = nibAt s.mem P i := by
  have hS : SCAL = 1152 := rfl
  have src : ∀ k < 32, ∀ m : Mem, Frame [scalR b] s.mem m →
      m (P + BitVec.ofNat 64 k) = s.mem (P + BitVec.ofNat 64 k) := fun k hk m hf =>
    hf _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact fun hc' => hsep _ (Offset.contains_base P (by omega) (by omega)) hc'
  have ne : ∀ i e, i < 64 → e < 64 → i ≠ e →
      b + BitVec.ofNat 64 (SCAL + i) ≠ b + BitVec.ofNat 64 (SCAL + e) := fun i e hi he hie h =>
    Offset.disjoint b (d := SCAL + i) (n := 1) (e := SCAL + e) (k := 1)
      (by omega) (by omega) (by omega) _ (Region.contains_self _ _) (h ▸ Region.contains_self _ _)
  unfold combCopy
  rw [List.singleton_append]
  refine wp_li (by decide) fun s₀ u₀ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (CopyInv s b P) (fun k t hk h => ?_) 32 le_rfl s₀
    ⟨u₀.rest (by decide), u₀.gpr, by rw [u₀.mem]; exact Frame.refl _ _,
      fun i hi => absurd hi (by omega)⟩) fun t h => ⟨h.rest, h.frame, fun i hi => h.nibs i (by omega)⟩
  have hct : Ctx8 b t := hc.of_rest h.rest (by decide)
  unfold combNibbles
  refine wp_lbz (a := P + BitVec.ofNat 64 k) (by decide) (by omega)
    (by rw [h.rest.gpr _ (by decide), hp]) (by rw [h.rest.rd, h.rest.wr]; exact hr k hk) fun t₁ u₁ => ?_
  have v1 : t₁.gpr .r8 = BitVec.ofNat 64 (s.mem (P + BitVec.ofNat 64 k)).toNat := by
    rw [u₁.gpr, src k hk _ h.frame]
  refine wp_and fun t₂ u₂ => ?_
  refine wp_stb (a := b + BitVec.ofNat 64 (SCAL + 2 * k)) (by decide) (by omega)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hct.r6]) (by rw [u₂.wr, u₁.wr]; exact hct.inW (by omega))
    fun t₃ u₃ => ?_
  refine comb_lsr (by decide) fun t₄ u₄ => ?_
  refine wp_stb (a := b + BitVec.ofNat 64 (SCAL + (2 * k + 1))) (by decide) (by omega)
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hct.r6, Nat.add_assoc])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hct.inW (by omega)) fun t₅ u₅ => WP.block_nil ?_
  have nf := nib_facts (s.mem (P + BitVec.ofNat 64 k))
  have lt16 : ∀ n, nibAt s.mem P n < 2 ^ 8 := fun n => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  have b2 : (t₂.gpr .r9).setWidth 8 = BitVec.ofNat 8 (nibAt s.mem P (2 * k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [u₂.gpr, v1, u₁.other _ (by decide), h.r7, nf.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt16 _), nibAt,
      show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]
  have b4 : (t₄.gpr .r9).setWidth 8 = BitVec.ofNat 8 (nibAt s.mem P (2 * k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), v1, nf.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt16 _), nibAt,
      show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega]
  have m5 : t₅.mem = (t.mem.writeW (b + BitVec.ofNat 64 (SCAL + 2 * k)) (BitVec.ofNat 8 (nibAt s.mem P (2 * k)))).writeW
      (b + BitVec.ofNat 64 (SCAL + (2 * k + 1))) (BitVec.ofNat 8 (nibAt s.mem P (2 * k + 1))) := by
    rw [u₅.mem, b4, u₄.mem, u₃.mem, b2, u₂.mem, u₁.mem]
  refine ⟨h.rest.trans ((u₁.rest (by decide)).trans ((u₂.rest (by decide)).trans ((u₃.rest _).trans
      ((u₄.rest (by decide)).trans (u₅.rest _))))),
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.r7],
    ?_, fun i hi => ?_⟩
  · rw [m5]
    exact (h.frame.writeW (List.mem_singleton_self _) _
      (Offset.contains b (d := SCAL + 2 * k) (n := 1) (e := SCAL) (k := 64) (by omega) (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains b (d := SCAL + (2 * k + 1)) (n := 1) (e := SCAL) (k := 64) (by omega) (by omega) (by omega))
  · unfold nibC
    rw [m5, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    by_cases h1 : i = 2 * k + 1
    · subst h1
      rw [ite_eq_left rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt16 _)]
    · rw [ite_eq_right (ne i _ (by omega) (by omega) h1)]
      by_cases h0 : i = 2 * k
      · subst h0
        rw [ite_eq_left rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt16 _)]
      · rw [ite_eq_right (ne i _ (by omega) (by omega) h0)]
        exact h.nibs i (by omega)

/-! ## The start -/

private def combStartCheck (p : Spec.Ed25519.Point) : Bool :=
  combStart.X * p.Z == p.X && combStart.Y * p.Z == p.Y && p.Z != 0

private theorem combStart_check :
    combStartCheck (Spec.Ed25519.pointMul (17 * Proof.Ed25519.combGVal) Spec.Ed25519.basePoint) = true := by
  decide +kernel

theorem combStart_ok : Rep combStart ((17 * Proof.Ed25519.combGVal) • baseAff) := by
  have hp := pointMul_rep (17 * Proof.Ed25519.combGVal) basePoint_rep
  have hc := combStart_check
  simp only [combStartCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hx, hy⟩, _⟩ := hc
  exact Proof.Ed25519.combPt_rep (q := combStartAff) hp hx hy

/-! ## The multiplication -/

/-- What `combMultiply` writes: the scalar's nibbles, the sign's mask and the field area. -/
abbrev combW (b : Addr) : List Region := scalR b :: stepW b

/-- The comb after the scalar's nibbles: the accumulator's start, the counter, the tables'
address and the 64 steps, for the scalar `S` whose nibbles are at `SCAL`. -/
theorem combRun_ok {u : State} {b T : Addr} {S : Nat} (cuu : Ctx8 b u) (hT : TblAt u T)
    (hsym : u.syms combSym = T) (apart : (TBL T).Disjoint ⟨b, 8192⟩) (hS : S < 2 ^ 256)
    (hn : ∀ i < 64, nibC u.mem b i = Proof.Ed25519.nib S i) :
    WP isa (.seq combInit (.loop combStep (.nonzero .d .r7))) u fun t => Rest stepR u t ∧
      Frame (stepW b) u.mem t.mem ∧ Rep (point (env t.mem b) 0 1 2 3) (S • baseAff) := by
  rw [combInit, WP.seq_iff, WP.seq_iff]
  refine WP.mono_syms (fieldCode_ok _ cuu.ctx) fun v ⟨kv, ev⟩ syv => ?_
  refine WP.of_syms (wp_li (imm := 0) (by decide) fun w₁ u₁ => comb_adrSym (by decide) fun w u₂ sy₂ =>
    WP.block_nil fun syw => ?_)
  have rw₂ : Rest [.r15, .r16] v w := (u₁.rest (by decide)).trans (u₂.rest (by decide))
  have mw : w.mem = v.mem := by rw [u₂.mem, u₁.mem]
  have cw : Ctx8 b w := (cuu.of_keep kv).of_rest rw₂ (by decide)
  have fsw : Frame (stepW b) u.mem w.mem := by
    rw [mw]
    exact kv.frame.mono (by simp)
  have hTw : TblAt w T := hT.of_frame (by rw [rw₂.rd, rw₂.wr, kv.rest.rd, kv.rest.wr]) fsw
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact apart.sub_right (Offset.sub_base _ (by decide))
      · exact apart.sub_right (Offset.sub_base _ (by decide))
  have E : CombEnv w b T := ⟨hTw, apart⟩
  have syw : w₁.syms = u.syms := (sy₂.symm.trans syw).trans syv
  have I : CombInv w b T S 0 w := by
    refine ⟨by decide, cw, by rw [u₂.other _ (by decide), u₁.gpr],
      by rw [u₂.gpr, syw, hsym, Nat.mul_zero, show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero],
      ?_, ?_, Rest.refl _ _, Frame.refl _ _, fun i hi => by rw [scal_apart fsw hi]; exact hn i hi⟩
    · rw [mw, ev]
      simp [constPointOps, evalOps, evalOp]
    · rw [mw, ev, evalOps, List.foldl_append, ← evalOps, ← evalOps, (env_constPoint _ _).1]
      simpa only [Proof.Ed25519.digitSum64, add_zero, natCast_zsmul] using combStart_ok
  refine WP.mono (combSteps_ok E I (by decide)) fun t ht => ⟨?_, ?_, ?_⟩
  · exact (kv.rest.mono (by decide)).trans ((rw₂.mono (by decide)).trans ht.rest)
  · exact fsw.trans ht.frame
  · have := ht.acc
    rw [Proof.Ed25519.comb64_total hS, natCast_zsmul] at this
    exact this

theorem combMultiply_ok {s : State} {b P T : Addr} (hc : Ctx8 b s) (hp : s.gpr .r14 = P)
    (hr : ∀ k < 32, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 k) 1)
    (hsep : (⟨P, 32⟩ : Region).Disjoint ⟨b, 8192⟩)
    (hT : TblAt s T) (hsym : s.syms combSym = T) (apart : (TBL T).Disjoint ⟨b, 8192⟩) :
    WP isa combMultiply s fun t => Rest stepR s t ∧ Frame (combW b) s.mem t.mem ∧
      Rep (point (env t.mem b) 0 1 2 3)
        (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem P 32) • baseAff) := by
  have sub : (scalR b).Sub ⟨b, 8192⟩ := Offset.sub_base _ (by decide)
  rw [combMultiply, combPrepare]
  refine WP.seq (WP.seq (WP.mono_syms (combCopy_ok hc hp hr (hsep.sub_right sub)) fun u ⟨ru, fu, cu⟩ syu => ?_))
  have hTu : TblAt u T := hT.of_frame (by rw [ru.rd, ru.wr]) fu fun r hr => by
    rw [List.mem_singleton.mp hr]; exact apart.sub_right sub
  refine WP.seq_iff.mp (WP.mono (combRun_ok (hc.of_rest ru (by decide)) hTu (by rw [syu, hsym]) apart
    (Proof.Ed25519.decodeLE_lt32 s.mem P) fun i hi => by rw [cu i hi, nibAt_eq _ _ hi])
    fun t ⟨rt, ft, pt⟩ => ⟨?_, ?_, pt⟩)
  · exact (ru.mono (by decide)).trans rt
  · exact (fu.mono (by simp)).trans (ft.mono (by simp))

end VG.Proof.Ed25519.PPC64LE
