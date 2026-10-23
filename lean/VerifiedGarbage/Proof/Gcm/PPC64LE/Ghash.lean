module

public import VerifiedGarbage.Impl.Gcm.PPC64LE
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
meta import VerifiedGarbage.Impl.Gcm.PPC64LE
meta import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Gcm.Bits
meta import VerifiedGarbage.Proof.Gcm.Bits
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# GHASH on PPC64LE

As on AArch64 (`Proof/Gcm/AArch64/Ghash.lean`): what the instructions of a
step (`Impl.Gcm.PPC64LE.step`) compute on the two halves of a 128-bit
value, stated on the whole value (`step_ok`); the 128 steps (`mul_ok`); one
block (`body_ok`), and every block, with the nonvolatile registers saved in
the scratch buffer around them (`Spill`).
-/

@[expose] public section

namespace VG.Proof.Gcm

open VG.PPC64LE in
/-- PPC64LE contract for `vg_ghash(h = r3, y = r4, data = r5, n = r6, scratch = r7)`:
replaces the block `Y` at `y` with `GHASH_H` continued from `Y` over the `n`
blocks at `data`, where `H` is the block at `h`.

The code may read `h` (16 bytes) and `data` (`16 * n` bytes), and read and
write `y` (16 bytes) and `scratch` (256 bytes, whose contents on exit are
unspecified). `y` and `scratch` may not overlap each other or the other
buffers. The pointers and `n` are public; `H`, `Y` and the data are
secret. -/
def ghashPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let h : Region := ⟨s.gpr .r3, 16⟩
    let y : Region := ⟨s.gpr .r4, 16⟩
    let data : Region := ⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 256⟩
    s.rd = [h, data] ∧ s.wr = [y, scratch] ∧
    h.Disjoint y ∧ h.Disjoint scratch ∧ y.Disjoint data ∧ y.Disjoint scratch ∧
    data.Disjoint scratch ∧ (s.gpr .r7).toNat + 256 ≤ 2 ^ 64
  post s s' :=
    Spec.Gcm.blockAt s'.mem (s.gpr .r4) =
      Spec.Gcm.ghashFrom (Spec.Gcm.blockAt s.mem (s.gpr .r3)) (Spec.Gcm.blockAt s.mem (s.gpr .r4))
        (Spec.Gcm.blocksAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

end VG.Proof.Gcm

namespace VG.Proof.Gcm.PPC64LE

open VG VG.PPC64LE VG.Impl.Gcm.PPC64LE VG.Proof.Gcm
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul)

/-! ## The bit manipulations -/

/-- `sldi hi, hi, 1; srdi t, lo, 63; or hi, hi, t; sldi lo, lo, 1` shifts
`hi ++ lo` left by one bit. -/
theorem shl1 (a b : BitVec 64) : (a <<< 1 ||| b >>> 63) ++ b <<< 1 = (a ++ b) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight]
  by_cases h1 : i < 64
  · by_cases h0 : i = 0
    · subst h0; simp
    · simp [h1, h0, hi, show i - 1 < 64 by omega]
  · by_cases h64 : i = 64
    · subst h64; simp
    · simp [h1, hi, show i - 64 < 64 by omega, show ¬ i - 1 < 64 by omega]
      rw [BitVec.getLsbD_of_ge b (63 + (i - 64)) (by omega), Bool.or_false,
        decide_eq_false (show i - 64 ≠ 0 by omega), decide_eq_false (show i ≠ 0 by omega)]
      simp only [Bool.not_false, Bool.true_and]
      congr 1

/-- `0 − (x >>> 63)` is all ones if the top bit of `x` is set, and zero otherwise. -/
theorem neg_msb (x : BitVec 64) :
    (0 : BitVec 64) - x >>> 63 = if x.msb then BitVec.allOnes 64 else 0 := by
  have h : x >>> 63 = if x.msb then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.msb_eq_getLsbD_last]
    rcases (by omega : i = 0 ∨ 0 < i) with h | h
    · subst h; cases x.getLsbD (64 - 1) <;> simp
    · simp only [show 63 + i ≥ 64 by omega, BitVec.getLsbD_of_ge]
      split <;> simp [BitVec.getLsbD_one, show i ≠ 0 by omega]
  rw [h]; split <;> decide

/-- `sldi t, lo, 63; srdi t, t, 63` isolates the lowest bit. -/
theorem neg_lsb (x : BitVec 64) :
    (0 : BitVec 64) - x <<< 63 >>> 63 = if x.getLsbD 0 then BitVec.allOnes 64 else 0 := by
  rw [neg_msb]
  have : (x <<< 63).msb = x.getLsbD 0 := by
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft]; simp
  rw [this]

theorem mask_z (zh zl vh vl : BitVec 64) (c : Bool) :
    (zh ^^^ (vh &&& if c then BitVec.allOnes 64 else 0)) ++
      (zl ^^^ (vl &&& if c then BitVec.allOnes 64 else 0)) =
      if c then (zh ++ zl) ^^^ (vh ++ vl) else zh ++ zl := by
  cases c
  · simp
  · simp only [ite_true, BitVec.and_allOnes, BitVec.xor_append]

theorem R_eq : Spec.Gcm.R = rHigh ++ 0#64 := by decide

/-- `srdi lo, lo, 1; sldi t, hi, 63; or lo, lo, t; srdi hi, hi, 1` shifts
`hi ++ lo` right by one bit. -/
theorem shr1 (a b : BitVec 64) : a >>> 1 ++ (b >>> 1 ||| a <<< 63) = (a ++ b) >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  rcases (by omega : i < 63 ∨ i = 63 ∨ 64 ≤ i) with h | h | h
  · simp [h, show 1 + i < 64 by omega, show i < 64 by omega]
  · subst h; simp
  · simp only [show ¬ 1 + i < 64 by omega, show ¬ i < 64 by omega, ite_false]
    congr 1; omega

theorem update_v (vh vl : BitVec 64) :
    (vh >>> 1 ^^^ ((0 : BitVec 64) - vl <<< 63 >>> 63 &&& rHigh)) ++ (vl >>> 1 ||| vh <<< 63) =
      if (vh ++ vl).getLsbD 0 then ((vh ++ vl) >>> 1) ^^^ Spec.Gcm.R else (vh ++ vl) >>> 1 := by
  rw [neg_lsb, R_eq, BitVec.getLsbD_append, ← shr1]
  simp only [show (0 : Nat) < 64 by decide, ite_true]
  cases vl.getLsbD 0
  · simp
  · simp only [ite_true, BitVec.allOnes_and]
    rw [BitVec.xor_append, BitVec.xor_zero]

theorem msb_shiftLeft (x : Block) (k : Nat) : (x <<< k).msb = x.getMsbD k := by
  rw [BitVec.msb_eq_getMsbD_zero, BitVec.getMsbD_shiftLeft, Nat.zero_add]

/-! ## One step -/

/-- The registers a step does not write. -/
def stepKeep : List Reg := [.r3, .r4, .r5, .r6, .r7, RH, CNT, ZERO]

theorem step_ok (x : Block) (zv : Block × Block) (k : Nat) (s : State)
    (hx : s.gpr XH ++ s.gpr XL = x <<< k)
    (hzv : (s.gpr ZH ++ s.gpr ZL, s.gpr VH ++ s.gpr VL) = zv)
    (hr : s.gpr RH = rHigh) (hz : s.gpr ZERO = 0) :
    WP isa (.block step) s fun s' =>
      s'.gpr XH ++ s'.gpr XL = x <<< (k + 1) ∧
      (s'.gpr ZH ++ s'.gpr ZL, s'.gpr VH ++ s'.gpr VL) = mulStep x zv k ∧
      (∀ r ∈ stepKeep, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  subst hzv
  simp only [XH, XL, ZH, ZL, VH, VL, RH, ZERO] at hx hr hz ⊢
  apply WP.of_runBlock
  simp only [step, XH, XL, ZH, ZL, VH, VL, M, T, RH, ZERO]
  simp (disch := decide) only [runBlock_cons, runStep_some, runBlock_nil, exec_lsr_d, exec_lsl, exec_sub,
    exec_logic, Option.some.injEq, exists_eq_left']
  simp only [State.write, reduceCtorEq, ↓reduceIte]
  refine ⟨?_, ?_, ?_, trivial, trivial, trivial⟩
  · rw [shl1, hx, BitVec.shiftLeft_add]
  · have hmsb : (s.gpr .r8).msb = x.getMsbD k := by
      rw [← msb_shiftLeft, ← hx, BitVec.msb_append]; rfl
    rw [hz, neg_msb, hmsb, mask_z, hr, update_v]
    rfl
  · intro r hr
    simp only [stepKeep, RH, CNT, ZERO, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [reduceCtorEq, ↓reduceIte]

/-! ## The 128 steps -/

/-- The registers the multiplication does not write. -/
def keepRegs : List Reg := [.r3, .r4, .r5, .r6, .r7]

theorem keep_sub {r : Reg} (h : r ∈ keepRegs) : r ∈ stepKeep := by
  simp only [keepRegs, stepKeep, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

/-- After `k` steps of `x • h`, from the state `sB`. -/
structure Inner (x h : Block) (sB : State) (k : Nat) (s : State) : Prop where
  xr : s.gpr XH ++ s.gpr XL = x <<< k
  zv : (s.gpr ZH ++ s.gpr ZL, s.gpr VH ++ s.gpr VL) = mulSteps x h k
  rh : s.gpr RH = rHigh
  zero : s.gpr ZERO = 0
  keep : ∀ r ∈ keepRegs, s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem inner_step {x h : Block} {sB : State} {k : Nat} {s : State} (hs : Inner x h sB k s) :
    WP isa (.block step) s fun s' => Inner x h sB (k + 1) s' ∧ s'.gpr CNT = s.gpr CNT := by
  refine WP.mono (step_ok x _ k s hs.xr hs.zv hs.rh hs.zero)
    fun s' ⟨hx, hzv, hk, hm, hrd, hwr⟩ => ?_
  refine ⟨⟨hx, by rw [hzv, mulSteps_succ], by rw [hk _ (by simp [stepKeep]), hs.rh],
    by rw [hk _ (by simp [stepKeep]), hs.zero],
    fun r hr => by rw [hk r (keep_sub hr), hs.keep r hr], by rw [hm, hs.mem], by rw [hrd, hs.rd],
    by rw [hwr, hs.wr]⟩, hk _ (by simp [stepKeep])⟩

theorem steps_ok {x h : Block} {sB : State} {j : Nat} (hj : j < 128 / unroll) {s : State}
    (hs : Inner x h sB (unroll * j) s) (hc : s.gpr CNT = BitVec.ofNat 64 (128 / unroll - j)) :
    WP isa (.block steps) s fun s' => Inner x h sB (unroll * (j + 1)) s' ∧
      s'.gpr CNT = BitVec.ofNat 64 (128 / unroll - (j + 1)) := by
  rw [steps, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (N := unroll)
    (fun k s' => Inner x h sB (unroll * j + k) s' ∧ s'.gpr CNT = s.gpr CNT)
    (fun k s' _ ⟨hs', hc'⟩ => WP.mono (inner_step hs') fun s'' ⟨h₁, h₂⟩ => ⟨h₁, h₂.trans hc'⟩)
    unroll (Nat.le_refl _) s ⟨hs, rfl⟩) fun s₁ ⟨hs₁, hc₁⟩ => ?_
  have e : 128 / unroll - j = (128 / unroll - (j + 1)) + 1 := by
    simp only [unroll] at hj ⊢; omega
  rw [e] at hc
  refine wp_subi (by decide) (by decide) fun s₂ u₂ => wp_nil ⟨?_, ?_⟩
  · rw [Nat.mul_succ]
    exact { xr := by rw [u₂.other _ (by decide), u₂.other _ (by decide)]; exact hs₁.xr
            zv := by
              rw [u₂.other _ (by decide), u₂.other _ (by decide), u₂.other _ (by decide),
                u₂.other _ (by decide)]; exact hs₁.zv
            rh := by rw [u₂.other _ (by decide)]; exact hs₁.rh
            zero := by rw [u₂.other _ (by decide)]; exact hs₁.zero
            keep := fun r hr => by
              have : r ≠ CNT := by
                simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
                rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
              rw [u₂.other r this]; exact hs₁.keep r hr
            mem := u₂.mem.trans hs₁.mem
            rd := u₂.rd.trans hs₁.rd
            wr := u₂.wr.trans hs₁.wr }
  · rw [u₂.gpr, hc₁, hc, Offset.ofNat_sub_ofNat (Nat.le_add_left 1 _), Nat.add_sub_cancel]

/-- The loop of `128 / unroll` iterations: all 128 steps. -/
theorem mul_ok {x h : Block} {sB s : State} (hs : Inner x h sB 0 s)
    (hc : s.gpr CNT = BitVec.ofNat 64 (128 / unroll)) :
    WP isa (.loop (.block steps) (.nonzero .d CNT)) s (Inner x h sB 128) := by
  let Inv : Nat → State → Prop := fun m s =>
    ∃ j, m = 128 / unroll - j ∧ j < 128 / unroll ∧ Inner x h sB (unroll * j) s ∧
      s.gpr CNT = BitVec.ofNat 64 (128 / unroll - j)
  refine WP.loop (M := isa) Inv (fun m s ⟨j, hm, hj, hs, hc⟩ => ?_) _ s
    ⟨0, rfl, by decide, hs, hc⟩
  subst hm
  refine WP.mono (steps_ok hj hs hc) fun s' ⟨hs', hc'⟩ => ?_
  have hev := eval_nonzero_ofNat' s' CNT (k := 128 / unroll - (j + 1)) (by simp only [unroll]; omega) hc'
  by_cases hlast : j + 1 = 128 / unroll
  · left
    refine ⟨by rw [hev]; simp [hlast], ?_⟩
    rw [hlast] at hs'
    exact hs'
  · right
    refine ⟨by rw [hev]; simp only [unroll] at hlast hj ⊢; simp; omega, _,
      by omega, j + 1, rfl, by omega, hs', hc'⟩

/-! ## Big-endian halves -/

/-- The 16 bytes as 8 bytes. -/
theorem bytesAt_16 (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 16 =
    [m (p + BitVec.ofNat 64 0), m (p + BitVec.ofNat 64 1), m (p + BitVec.ofNat 64 2),
      m (p + BitVec.ofNat 64 3), m (p + BitVec.ofNat 64 4), m (p + BitVec.ofNat 64 5),
      m (p + BitVec.ofNat 64 6), m (p + BitVec.ofNat 64 7), m (p + BitVec.ofNat 64 8),
      m (p + BitVec.ofNat 64 9), m (p + BitVec.ofNat 64 10), m (p + BitVec.ofNat 64 11),
      m (p + BitVec.ofNat 64 12), m (p + BitVec.ofNat 64 13), m (p + BitVec.ofNat 64 14),
      m (p + BitVec.ofNat 64 15)] := rfl

/-- Two byte-reversed 8-byte loads read a block. -/
theorem blockAt_rev (m : Mem) (p : Addr) :
    rev64 (m.readW (p + BitVec.ofNat 64 0) 64) ++ rev64 (m.readW (p + BitVec.ofNat 64 8) 64) =
      blockAt m p := by
  have e : ∀ j : Nat, j < 15 → p + BitVec.ofNat 64 j + 1 = p + BitVec.ofNat 64 (j + 1) :=
    fun j _ => Offset.add_add p j 1
  rw [rev64_readW, rev64_readW]
  simp only [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 8 (by decide), e 9 (by decide), e 10 (by decide), e 11 (by decide),
    e 12 (by decide), e 13 (by decide), e 14 (by decide)]
  rw [Spec.Gcm.blockAt, bytesAt_16, ofBytes_16]

theorem rev64_rev64 (a : BitVec 64) : rev64 (rev64 a) = a := byteRev64_byteRev64 a

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev hA : Addr := s₀.gpr .r3
abbrev yp : Addr := s₀.gpr .r4
abbrev dp : Addr := s₀.gpr .r5
abbrev nb : Nat := (s₀.gpr .r6).toNat
abbrev scr : Addr := s₀.gpr .r7
abbrev hR : Region := ⟨hA s₀, 16⟩
abbrev yR : Region := ⟨yp s₀, 16⟩
abbrev dR : Region := ⟨dp s₀, 16 * nb s₀⟩
abbrev scrR : Region := ⟨scr s₀, 256⟩
abbrev H₀ : Block := blockAt s₀.mem (hA s₀)
abbrev Y₀ : Block := blockAt s₀.mem (yp s₀)

/-- Block `i`, and where it starts. -/
abbrev blkAddr (i : Nat) : Addr := dp s₀ + BitVec.ofNat 64 (16 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [hR s₀, dR s₀]
  wr : s₀.wr = [yR s₀, scrR s₀]
  h_y : (hR s₀).Disjoint (yR s₀)
  h_scr : (hR s₀).Disjoint (scrR s₀)
  y_d : (yR s₀).Disjoint (dR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  d_scr : (dR s₀).Disjoint (scrR s₀)
  scr_wrap : (scr s₀).toNat + 256 ≤ 2 ^ 64

theorem pre_of (s₀ : State) (h : Proof.Gcm.ghashPPC64LE.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

/-- The blocks fit in the address space (or they could not be disjoint from `y`). -/
theorem nb_lt : 16 * nb s₀ < 2 ^ 64 := by
  by_contra hn
  refine h.y_d (yp s₀) (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (yp s₀ - dp s₀).isLt
  omega

theorem in_h {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (hA s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨hR s₀, by simp [h.rd], Offset.contains_base _ hd (by omega)⟩

theorem in_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (yp s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨yR s₀, by simp [h.wr], Offset.contains_base _ hd (by omega)⟩

theorem out_y {d : Nat} (hd : d + 8 ≤ 16) :
    InRegions s₀.wr (yp s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨yR s₀, by simp [h.wr], Offset.contains_base _ hd (by omega)⟩

theorem in_scr {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s₀.rd ++ s₀.wr) (scr s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨scrR s₀, by simp [h.wr], Offset.contains_base _ hd (by omega)⟩

omit h in
theorem blk_sub {i : Nat} (hi : i < nb s₀) : Region.Sub ⟨blkAddr s₀ i, 16⟩ (dR s₀) :=
  Offset.sub_base _ (by omega)

theorem in_blk {i d : Nat} (hi : i < nb s₀) (hd : d + 8 ≤ 16) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 d) 8 := by
  have := h.nb_lt
  refine ⟨dR s₀, by simp [h.rd], ?_⟩
  rw [blkAddr, Offset.add_add]
  exact Offset.contains_base _ (by omega) (by omega)

end Pre

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .r3 = hA s₀
  r4 : s.gpr .r4 = yp s₀
  r7 : s.gpr .r7 = scr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [yR s₀, scrR s₀] s₀.mem s.mem
  saved : Spill.Saved (scr s₀) s₀.gpr saved s.mem
  y : blockAt s.mem (yp s₀) = ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) i)

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  r5 : s.gpr .r5 = blkAddr s₀ i
  r6 : s.gpr .r6 = BitVec.ofNat 64 (nb s₀ - i)

/-! ## One block -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `ldbrx t, a, b`. -/
theorem wp_ldbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 8)
    (k : ∀ s', Upd s s' t (rev64 (s.mem.readW ea 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := s.write t (rev64 (s.mem.readW ea 64))) ?_ (k _ (Upd.write _ _ _))
  rw [exec_loadRev_d hn (by rw [hea]; exact hin), hea]

/-- `stdbrx t, a, b`. -/
theorem wp_stdbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (rev64 (s.gpr t))) → WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .d t a b :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW ea (rev64 (s.gpr t)) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_d hn (by rw [hea]; exact hout), hea]

/-- `or d, n, m`. -/
theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end

set_option linter.unusedSimpArgs false in
theorem load_ok (s : State)
    (hh : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 d) 8)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .r4 + BitVec.ofNat 64 d) 8)
    (hd : ∀ d : Nat, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .r5 + BitVec.ofNat 64 d) 8) :
    WP isa (.block load) s fun s₁ =>
      Inner (blockAt s.mem (s.gpr .r4) ^^^ blockAt s.mem (s.gpr .r5)) (blockAt s.mem (s.gpr .r3))
        s 0 s₁ ∧ s₁.gpr CNT = BitVec.ofNat 64 (128 / unroll) := by
  unfold load
  refine wp_li (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => ?_
  have g₂ (r : Reg) (a : r ≠ ZERO) (b : r ≠ T) : s₂.gpr r = s.gpr r := by rw [u₂.other _ b, u₁.other _ a]
  have z₂ : s₂.gpr ZERO = BitVec.ofNat 64 0 := by rw [u₂.other _ (by decide), u₁.gpr]
  have rw₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine wp_ldbrx (ea := s.gpr .r4 + BitVec.ofNat 64 0) (by decide)
    (by rw [g₂ _ (by decide) (by decide), z₂]) (by rw [rw₂]; exact hy 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_ldbrx (ea := s.gpr .r5 + BitVec.ofNat 64 0) (by decide)
    (by rw [u₃.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide) (by decide), z₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hd 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_xor fun s₅ u₅ => ?_
  refine wp_ldbrx (ea := s.gpr .r4 + BitVec.ofNat 64 8) (by decide)
    (by simp (disch := decide) only [u₅.other, u₄.other, u₃.other, u₂.gpr, g₂])
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hy 8 (by decide)) fun s₆ u₆ => ?_
  refine wp_ldbrx (ea := s.gpr .r5 + BitVec.ofNat 64 8) (by decide)
    (by simp (disch := decide) only [u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, g₂])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]; exact hd 8 (by decide))
    fun s₇ u₇ => ?_
  refine wp_xor fun s₈ u₈ => ?_
  refine wp_ldbrx (ea := s.gpr .r3 + BitVec.ofNat 64 0) (by decide)
    (by simp (disch := decide) only [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, g₂, z₂])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rw₂]
        exact hh 0 (by decide)) fun s₉ u₉ => ?_
  refine wp_ldbrx (ea := s.gpr .r3 + BitVec.ofNat 64 8) (by decide)
    (by simp (disch := decide) only [u₉.other, u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other,
      u₂.gpr, g₂])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd,
        u₃.wr, rw₂]; exact hh 8 (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_li (by decide) fun s₁₁ u₁₁ => wp_li (by decide) fun s₁₂ u₁₂ => wp_li (by decide) fun s₁₃ u₁₃ =>
    wp_lsl (by decide) fun s₁₄ u₁₄ => wp_li (by decide) fun s₁₅ u₁₅ => wp_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, m₂]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, m₃]
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, m₄]
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, m₅]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, m₆]
  have m₈ : s₈.mem = s.mem := by rw [u₈.mem, m₇]
  have m₉ : s₉.mem = s.mem := by rw [u₉.mem, m₈]
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, m₉]
  have m₁₅ : s₁₅.mem = s.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
  refine ⟨⟨?_, ?_, ?_, ?_, fun r hr => ?_, m₁₅, ?_, ?_⟩, ?_⟩
  · simp (disch := decide) only [u₁₅.gpr, u₁₅.other, u₁₄.gpr, u₁₄.other, u₁₃.gpr, u₁₃.other, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, m₂, m₃, m₄, m₅, m₆]
    rw [BitVec.shiftLeft_zero, ← BitVec.xor_append, blockAt_rev, blockAt_rev]
  · simp (disch := decide) only [u₁₅.gpr, u₁₅.other, u₁₄.gpr, u₁₄.other, u₁₃.gpr, u₁₃.other, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, m₈, m₉]
    rw [mulSteps_zero, blockAt_rev]
    rfl
  · simp (disch := decide) only [u₁₅.gpr, u₁₅.other, u₁₄.gpr, u₁₄.other, u₁₃.gpr, u₁₃.other, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other]; decide
  · simp (disch := decide) only [u₁₅.gpr, u₁₅.other, u₁₄.gpr, u₁₄.other, u₁₃.gpr, u₁₃.other, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, g₂, z₂]; rfl
  · simp only [keepRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (disch := decide) only [u₁₅.gpr, u₁₅.other, u₁₄.gpr, u₁₄.other, u₁₃.gpr, u₁₃.other, u₁₂.gpr, u₁₂.other, u₁₁.gpr, u₁₁.other, u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, u₃.gpr, u₃.other, g₂]
  · rw [u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd,
      u₂.rd, u₁.rd]
  · rw [u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr,
      u₂.wr, u₁.wr]
  · rw [u₁₅.gpr]

/-- The memory after storing `Z` at `p`. -/
def storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) : Mem :=
  (m.writeW (p + BitVec.ofNat 64 0) (rev64 zh)).writeW (p + BitVec.ofNat 64 8) (rev64 zl)

theorem half_sep (p : Addr) : Mem.Sep (p + BitVec.ofNat 64 0) 8 (p + BitVec.ofNat 64 8) 8 :=
  Offset.sep p (by decide) (by decide) (by decide)

theorem blockAt_storeMem (m : Mem) (p : Addr) (zh zl : BitVec 64) :
    blockAt (storeMem m p zh zl) p = zh ++ zl := by
  rw [← blockAt_rev, storeMem, Mem.readW_writeW_self64,
    Mem.readW_writeW_sep (half_sep p) (by decide), Mem.readW_writeW_self64, rev64_rev64,
    rev64_rev64]

theorem store_ok (s : State) (hz : s.gpr ZERO = 0)
    (hy : ∀ d : Nat, d + 8 ≤ 16 → InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 d) 8) :
    WP isa (.block store) s fun s' =>
      s'.mem = storeMem s.mem (s.gpr .r4) (s.gpr ZH) (s.gpr ZL) ∧
      s'.gpr .r5 = s.gpr .r5 + BitVec.ofNat 64 16 ∧ s'.gpr .r6 = s.gpr .r6 - BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ T → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold store
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_stdbrx (ea := s.gpr .r4 + BitVec.ofNat 64 0) (by decide)
    (by rw [u₁.other _ (by decide), u₁.other _ (by decide), hz]; rfl) (by rw [u₁.wr]; exact hy 0 (by decide))
    fun s₂ u₂ => ?_
  refine wp_stdbrx (ea := s.gpr .r4 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), u₁.gpr]) (by rw [u₂.wr, u₁.wr]; exact hy 8 (by decide))
    fun s₃ u₃ => ?_
  refine wp_addi (by decide) (by decide) fun s₄ u₄ => wp_subi (by decide) (by decide) fun s₅ u₅ =>
    wp_nil ⟨?_, ?_, ?_, fun r a b c => ?_, ?_, ?_⟩
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.other _ (by decide), u₁.other _ (by decide),
      storeMem]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide)]
  · rw [u₅.other _ b, u₄.other _ a, u₃.gpr, u₂.gpr, u₁.other _ c]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

theorem storeMem_frame {s₀ : State} {m m' : Mem} (h : Frame [yR s₀, scrR s₀] m m') (zh zl : BitVec 64) :
    Frame [yR s₀, scrR s₀] m (storeMem m' (yp s₀) zh zl) :=
  (h.writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide) (by decide))).writeW
    (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide) (by decide))

/-- Memory outside `y` and the scratch buffer is as on entry. -/
theorem blockAt_frame {s₀ : State} {m : Mem} (h : Frame [yR s₀, scrR s₀] s₀.mem m) {p : Addr}
    (hd : Region.Disjoint ⟨p, 16⟩ (yR s₀)) (hd' : Region.Disjoint ⟨p, 16⟩ (scrR s₀)) :
    blockAt m p = blockAt s₀.mem p :=
  blockAt_congr fun _ hk =>
    h.bytes (R := ⟨p, 16⟩) (by simp [hd, hd']) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk

theorem slots_y {s₀ : State} (hp : Pre s₀) :
    ∀ p ∈ saved, ∀ r ∈ [yR s₀], Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 p.2, 8⟩ r := by
  intro p hp' r hr
  simp only [List.mem_singleton] at hr; subst hr
  have : p.2 + 8 ≤ 40 := by simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'; rcases hp' with rfl | rfl | rfl | rfl | rfl <;> decide
  exact hp.y_scr.symm.sub_left (Offset.sub_base _ (by omega))

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (isa.eval (.nonzero .d .r6) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (isa.eval (.nonzero .d .r6) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  refine WP.seq (WP.mono (load_ok s
    (fun d hd => by rw [hL.rd, hL.wr, hL.r3]; exact hp.in_h hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.r4]; exact hp.in_y hd)
    (fun d hd => by rw [hL.rd, hL.wr, hL.r5]; exact hp.in_blk hi hd)) fun s₁ ⟨hI₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (mul_ok hI₁ hc₁) fun s₂ hI₂ => ?_)
  have hx4₂ : s₂.gpr .r4 = yp s₀ := (hI₂.keep .r4 (by decide)).trans hL.r4
  refine WP.mono (store_ok s₂ hI₂.zero fun d hd => by rw [hI₂.wr, hL.wr, hx4₂]; exact hp.out_y hd)
    fun s₃ ⟨hm₃, hx5₃, hx6₃, hk₃, hrd₃, hwr₃⟩ => ?_
  have hk : ∀ r ∈ keepRegs, s₂.gpr r = s.gpr r := hI₂.keep
  have hx6 : s₂.gpr .r6 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hk .r6 (by decide), hL.r6, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hy : blockAt s₃.mem (yp s₀) =
      ghashFrom (H₀ s₀) (Y₀ s₀) (blocksAt s₀.mem (dp s₀) (i + 1)) := by
    have hz1 := congrArg Prod.fst hI₂.zv
    simp only at hz1
    rw [hm₃, hx4₂, blockAt_storeMem, ghashFrom_blocksAt_succ, ← hL.y, mul_eq, hz1, hL.r4, hL.r5,
      hL.r3, blockAt_frame (p := hA s₀) hL.frame hp.h_y hp.h_scr,
      blockAt_frame (p := blkAddr s₀ i) hL.frame (hp.y_d.symm.sub_left (Pre.blk_sub hi))
        (hp.d_scr.sub_left (Pre.blk_sub hi))]
  have hcommon : Common s₀ (i + 1) s₃ := by
    refine ⟨by rw [hk₃ _ (by decide) (by decide) (by decide), hk .r3 (by decide), hL.r3],
      by rw [hk₃ _ (by decide) (by decide) (by decide), hx4₂],
      by rw [hk₃ _ (by decide) (by decide) (by decide), hk .r7 (by decide), hL.r7],
      by rw [hrd₃, hI₂.rd, hL.rd], by rw [hwr₃, hI₂.wr, hL.wr], ?_, ?_, hy⟩
    · rw [hm₃, hx4₂, hI₂.mem]; exact storeMem_frame hL.frame _ _
    · rw [hm₃, hx4₂, hI₂.mem, storeMem]
      exact hL.saved.frame ((Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide)) |>.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide)))) (slots_y hp)
  have hev := eval_nonzero_ofNat' s₃ .r6 (k := nb s₀ - (i + 1)) (by have := hp.nb_lt; omega)
    (by rw [hx6₃, hx6])
  by_cases hlast : i + 1 = nb s₀
  · left
    exact ⟨by rw [hev]; simp [hlast], hlast ▸ hcommon⟩
  · right
    refine ⟨by rw [hev]; simp; omega, by omega, { hcommon with r5 := ?_, r6 := ?_ }⟩
    · rw [hx5₃, hk .r5 (by decide), hL.r5, blkAddr, blkAddr, Offset.add_add, Nat.mul_succ]
    · rw [hx6₃, hx6]

/-! ## The whole function -/

theorem blocks_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc : Common s₀ 0 s₁)
    (h5 : s₁.gpr .r5 = dp s₀) (h6 : s₁.gpr .r6 = s₀.gpr .r6) :
    WP isa blocks s₁ (Common s₀ (nb s₀)) := by
  have hev := eval_zero s₁ .r6
  refine WP.ite (s₁.gpr .r6 == 0) hev (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by rw [h6] at h; simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc)
  · have hpos : 0 < nb s₀ := by
      rw [h6] at h
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (isa.eval (.nonzero .d .r6) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (isa.eval (.nonzero .d .r6) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₁ :=
      { hc with
        r5 := by rw [h5]; simp [blkAddr]
        r6 := by rw [h6]; simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

theorem saved_bound : ∀ p ∈ saved, p.2 + 8 ≤ 256 := by decide

/-- The registers the code writes. -/
def written : List Reg := [.r0, .r5, .r6, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa ghash s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Gcm.ghashPPC64LE.post s₀ s' := by
  have sw := hp.scr_wrap
  unfold ghash
  rw [show saved.map (fun (r, d) => Instr.store .d r .r7 d) = Spill.saveCode .r7 saved from rfl,
    show saved.map (fun (r, d) => Instr.load .d r .r7 d) = Spill.restoreCode .r7 saved from rfl]
  refine WP.seq (WP.mono (Spill.save_wp (b := .r7) (l := saved) (by decide) (by decide)
    fun p hp' => ⟨scrR s₀, by simp [hp.wr], Offset.contains_base _ (saved_bound p hp')
      (by have := saved_bound p hp'; omega)⟩)
    fun s₁ h₁ => ?_)
  have hc₁ : Common s₀ 0 s₁ :=
    { r3 := by rw [h₁.gpr], r4 := by rw [h₁.gpr], r7 := by rw [h₁.gpr], rd := h₁.rd, wr := h₁.wr
      frame := by
        rw [h₁.mem]
        exact (Spill.saveMem_frame_base saved_bound (by decide) _ _ _).mono (by simp)
      saved := by rw [h₁.mem]; exact Spill.saveMem_saved (by decide) _ _ _
      y := by
        rw [h₁.mem, ghashFrom_blocksAt_zero]
        exact blockAt_congr fun _ hk =>
          (Spill.saveMem_frame_base saved_bound (by decide) s₀.mem (scr s₀) s₀.gpr).bytes (R := yR s₀)
            (by simp [hp.y_scr]) (by show (16 : Nat) ≤ 2 ^ 64; decide) hk }
  refine WP.seq (WP.mono (WP.keep written (blocks_ok hp hc₁ (by rw [h₁.gpr]) (by rw [h₁.gpr]))
    (by decide +kernel)) fun s₂ ⟨hc₂, hk₂⟩ => ?_)
  refine WP.mono (Spill.restore_wp (b := .r7) (l := saved) (by decide) hc₂.r7 (by decide) (by decide)
    (fun p hp' => by rw [hc₂.rd, hc₂.wr]; exact hp.in_scr (saved_bound p hp')) hc₂.saved)
    fun s₃ r₃ => ⟨fun r hr => ?_, ?_⟩
  · refine r₃.gpr_of ?_
    by_cases hv : r ∈ saved.map Prod.fst
    · exact .inl hv
    · have hw : ∀ r ∈ preserved, r ∉ saved.map Prod.fst → r ∉ written := by decide
      exact .inr (by rw [hk₂.gpr (hw r hr hv), h₁.gpr])
  · show blockAt s₃.mem (s₀.gpr .r4) = _
    rw [r₃.mem]; exact hc₂.y

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r7 => 0x4000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x1000, 16⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 256⟩]

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Gcm.PPC64LE.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashPPC64LE.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.lr he (by decide +kernel) (by decide +kernel)⟩, h₂⟩

theorem ghash_ct : ConstantTime isa Proof.Gcm.ghashPPC64LE.pre Proof.Gcm.ghashPPC64LE.pub
    Impl.Gcm.PPC64LE.ghash := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7]) ?_
    (by taint_decide)
  intro s₁ s₂ _ _ ⟨h3, h4, h5, h6, h7, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.PPC64LE.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ghash_verified :
    Verified PPC64LE.target Impl.Gcm.PPC64LE.ghash (Spec.Gcm.ghashContract PPC64LE.abi) :=
  Verified.of_correct ghash_correct ghash_ct (by
    sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, Proof.Gcm.ghashPPC64LE, PPC64LE.abi,
      PPC64LE.argRegs] [Proof.Gcm.PPC64LE.satState] using Proof.Gcm.PPC64LE.satState)

end VG.Proof.Gcm.PPC64LE
