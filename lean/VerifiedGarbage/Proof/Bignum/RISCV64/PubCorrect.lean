module

public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubE
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.PackedRead
import VerifiedGarbage.Proof.Bignum.ExportEncoding
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Framework.Range

/-! ### `Bignum.RISCV64.PubSave`, which only this module used -/

section

/-!
# The RSA public-key operation on RISC-V: saving, restoring and setting up

`loadS` reads the working space's address from the stack into `t0`;
`saveRegs` stores `s0`–`s11` (`saved`) in its header words 16–27 and copies
its address into `s6`; `restore` loads them back through `s6`, `s6` last.
`setup_ok`: `out`, `k`, `w`, the arrays' size and array 0's base in their
registers.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64 (Scr off_add add_ofNat_zero)
open VG.Proof.Bignum (slot)

/-- The saved registers' words, 96 bytes. -/
abbrev savR (w : Addr) : Region := ⟨w, 96⟩

theorem saved_inj : ∀ i < 12, ∀ j < 12, saved i = saved j → i = j := by decide

theorem saved_ne : ∀ i < 11, saved i ≠ .s6 := by decide

theorem saved_11 : saved 11 = .s6 := rfl

theorem sav_contains (w : Addr) {i : Nat} (hi : i < 12) : (savR w).Contains (off w (8 * i)) 8 :=
  Offset.contains_base w (by omega_using [hi]) (by omega_using [hi])

theorem sav_sep (w : Addr) {i j : Nat} (hi : i < 12) (hj : j < 12) (h : i ≠ j) :
    Mem.Sep (off w (8 * i)) 8 (off w (8 * j)) 8 :=
  Offset.sep w (by omega_using [hi, hj, h]) (by omega_using [hi]) (by omega_using [hj])

/-- The saved registers' words of the working space at `S`. -/
abbrev savW (S : Addr) : Addr := S + BitVec.ofNat 64 128

theorem saveOff_eq (S : Addr) (i : Nat) : S + BitVec.ofNat 64 (128 + 8 * i) = off (savW S) (8 * i) := by
  rw [off, Offset.add_add]

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [savR (savW (s₀.gpr .t0))] s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off (savW (s₀.gpr .t0)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_step (s₀ : State) (hin : ∀ i < 12, InRegions s₀.wr (off (savW (s₀.gpr .t0)) (8 * i)) 8)
    (hal : ∀ i < 12, (off (savW (s₀.gpr .t0)) (8 * i)).toNat % 8 = 0)
    {n : Nat} (hn : n < 12) {s : State}
    (h : SI s₀ n s) : WP isa (.block [.store .d (saved n) .t0 (128 + 8 * n)]) s (SI s₀ (n + 1)) := by
  have hw : s.gpr .t0 = s₀.gpr .t0 := by rw [h.gpr]
  have hout : InRegions s.wr (s.gpr .t0 + BitVec.ofNat 64 (128 + 8 * n)) 8 := by
    rw [h.wr, hw, saveOff_eq]; exact hin n hn
  have ha : (s.gpr .t0 + BitVec.ofNat 64 (128 + 8 * n)).toNat % 8 = 0 := by
    rw [hw, saveOff_eq]; exact hal n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show 128 + 8 * n < 2048 by omega_using [hn]) ha hout,
    Option.some.injEq, exists_eq_left', hw, saveOff_eq]
  refine ⟨h.gpr, h.rd, h.wr, h.sp,
    h.frame.writeW (List.mem_singleton_self _) _ (sav_contains _ hn), fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · rw [Mem.readW_writeW_sep (sav_sep _ (by omega_using [hi, hn]) hn (by omega_using [hi])) (by decide)]
    exact h.saved i hi
  · rw [Mem.readW_writeW_self64, h.gpr]

/-- The state after `save`. -/
structure Saved (s₀ : State) (s : State) : Prop where
  keep : Keep [.s6] s₀ s
  sp : s.sp = s₀.sp
  s6 : s.gpr .s6 = s₀.gpr .t0
  frame : Frame [savR (savW (s₀.gpr .t0))] s₀.mem s.mem
  saved : ∀ i < 12, s.mem.readW (off (savW (s₀.gpr .t0)) (8 * i)) 64 = s₀.gpr (saved i)

theorem save_ok (s₀ : State) (hin : ∀ i < 12, InRegions s₀.wr (off (savW (s₀.gpr .t0)) (8 * i)) 8)
    (hal : ∀ i < 12, (off (savW (s₀.gpr .t0)) (8 * i)).toNat % 8 = 0) :
    WP isa (.block saveRegs) s₀ (Saved s₀) := by
  rw [saveRegs]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (SI s₀)
    (fun k s hk h => save_step s₀ hin hal hk h) 12 (Nat.le_refl _) s₀
    ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s h => ?_)
  have hw : s.gpr .t0 = s₀.gpr .t0 := by rw [h.gpr]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 0 by decide),
    BitVec.ofInt_ofNat, add_ofNat_zero, Option.some.injEq, exists_eq_left', hw]
  refine ⟨⟨fun r hr => ?_, h.rd, h.wr⟩, h.sp, ?_, h.frame, h.saved⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e fun e => hr (by simp [e]), h.gpr]
  · rw [gpr_write, ite_eq_left_iff.mpr fun e => absurd rfl e]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (S : Addr) (v : Nat → BitVec 64) (n : Nat) (s : State) : Prop where
  s6 : s.gpr .s6 = S
  restored : ∀ i < n, s.gpr (saved i) = v i
  others : ∀ r, (∀ i < 12, r ≠ saved i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp

theorem restore_step (sB : State) {S : Addr} {v : Nat → BitVec 64}
    (hsin : ∀ i < 12, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 12, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 12, sB.mem.readW (off (savW S) (8 * i)) 64 = v i)
    {n : Nat} (hn : n < 11) {s : State} (h : RI sB S v n s) :
    WP isa (.block [.load .d (saved n) .s6 (128 + 8 * n)]) s (RI sB S v (n + 1)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s6 + BitVec.ofNat 64 (128 + 8 * n)) 8 := by
    rw [h.rd, h.wr, h.s6, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin n (by omega_using [hn])
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .s6 + BitVec.ofNat 64 (128 + 8 * n)).toNat % 8 = 0 := by
    rw [h.s6, saveOff_eq]; exact hal n (by omega_using [hn])
  have hv : s.mem.readW (S + BitVec.ofNat 64 (128 + 8 * n)) 64 = v n := by
    rw [h.mem, saveOff_eq]; exact hsav n (by omega_using [hn])
  have hn6 := saved_ne n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show 128 + 8 * n < 2048 by omega_using [hn]) ha hin,
    Option.some.injEq, exists_eq_left', h.s6, hv]
  refine ⟨?_, fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (Ne.symm hn6)]; exact h.s6
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : saved i ≠ saved n := fun e =>
        absurd (saved_inj i (by omega_using [hi, hn]) n (by omega_using [hn]) e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n (by omega_using [hn]))]
    exact h.others r hr

/-- `restore`, from a state whose saved words, through `s6`, hold `v`. -/
theorem restore_ok (sB : State) {S : Addr} {v : Nat → BitVec 64} (hw : sB.gpr .s6 = S)
    (hsin : ∀ i < 12, InRegions sB.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 12, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 12, sB.mem.readW (off (savW S) (8 * i)) 64 = v i) :
    WP isa (.block PublicChecked.restore) sB fun s =>
      (∀ i < 12, s.gpr (saved i) = v i) ∧ (∀ r, (∀ i < 12, r ≠ saved i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp := by
  rw [PublicChecked.restore]
  refine WP.block_append (WP.mono (wp_range_flatMap (M := isa) (RI sB S v)
    (fun k s hk h => restore_step sB hsin hal hsav hk h) 11 (Nat.le_refl _) sB
    ⟨hw, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩) fun s h => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .s6 + BitVec.ofNat 64 (128 + 8 * 11)) 8 := by
    rw [h.rd, h.wr, h.s6, saveOff_eq]
    obtain ⟨r, hr, hc⟩ := hsin 11 (by decide)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have ha : (s.gpr .s6 + BitVec.ofNat 64 (128 + 8 * 11)).toNat % 8 = 0 := by
    rw [h.s6, saveOff_eq]; exact hal 11 (by decide)
  have hv : s.mem.readW (S + BitVec.ofNat 64 (128 + 8 * 11)) 64 = v 11 := by
    rw [h.mem, saveOff_eq]; exact hsav 11 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show 128 + 8 * 11 < 2048 by decide) ha hin,
    Option.some.injEq, exists_eq_left', h.s6, hv]
  refine ⟨fun i hi => ?_, fun r hr => ?_, h.mem, h.rd, h.wr, h.sp⟩
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_iff.mpr fun e => absurd e (saved_ne i hi)]; exact h.restored i hi
    · rw [saved_11, ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (saved_11 ▸ hr 11 (by decide))]
    exact h.others r hr

/-! ## The working space's address -/

/-- `loadS`: the first argument on the stack into `t0`. -/
theorem loadS_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8)
    (ha : s.sp.toNat % 8 = 0) :
    WP isa (.block loadS) s fun t => (t.gpr .t0 = stackArg s 0 ∧ t.mem = s.mem ∧ t.sp = s.sp) ∧
      Keep [.t0] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold loadS
  simp only [stackArgAddr, Nat.reduceMul] at h
  have ha' : (s.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := by rw [add_ofNat_zero]; exact ha
  have h' : InRegions (s.rd ++ s.wr) s.sp 8 := by simpa only [add_ofNat_zero] using h
  brun [exec_addSp (show 0 < 2048 by decide), h, h', ha, ha']
  simp [stackArg, stackArgAddr]

/-! ## Setting up -/

theorem ofNat_add7_shr3 (k : Nat) (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) :=
  Pre.ofNat_add7_shr3 k hk

/-- `setup`, `out` in `a0`, `k` in `a1` and the working space at `s6`: `out`
in `s10`, `k` in `s11`, `w` in `t0`, an array's size `8 w + 16` in `s5` and
array 0's base in `a7`. -/
theorem setup_ok {s : State} {O S : Addr} {k : Nat} (h10 : s.gpr .a0 = O)
    (h11 : s.gpr .a1 = BitVec.ofNat 64 k) (h6 : s.gpr .s6 = S) (hk' : k ≤ 1024) :
    WP isa (.block setup) s fun t =>
      (t.gpr .s10 = O ∧ t.gpr .s11 = BitVec.ofNat 64 k ∧ t.gpr .t0 = BitVec.ofNat 64 ((k + 7) / 8) ∧
        t.gpr .s5 = BitVec.ofNat 64 (8 * ((k + 7) / 8) + 16) ∧
        t.gpr .a7 = off S (slot ((k + 7) / 8) 0) ∧ t.mem = s.mem) ∧
      Keep [.a7, .s5, .s10, .s11, .t0] s t := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold setup
  brun [h10, h11, h6, add_ofNat_zero, ofNat_add7_shr3 k (by omega_arith), Pre.ofNat_shl3, hdrBytes]
  refine ⟨?_, ?_⟩
  · simp only [BitVec.ofNat_add_ofNat]
  · simp [slot, hdrBytes, off]

end VG.Proof.Bignum.RISCV64.Pub

end

end

/-! ### `Bignum.RISCV64.PubMid`, which this module and modules that import it used -/

section

/-!
# The RSA public-key operation on RISC-V: from `e` to the output

`mid_ok`: from the state after `setup` (`Mid`), `prep`, `power`, `output`
and then `restore` leave the result (`MidPost`), as on PPC64LE, with the
numbers of the arrays as 64-bit words.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot slot_sep slot_le wv)

theorem wsv_wv (m : Mem) (p : Addr) (d n : Nat) : Mont.wordsVal m p d n = wv m p d n := by
  rw [VG.Proof.Bignum.wordsVal_read, VG.Proof.Bignum.read_eq_wv]

theorem exponentValid_sat (v : Nat) : Spec.Rsa.exponentValid (sat v) = Spec.Rsa.exponentValid v := by
  unfold sat
  by_cases h : v < 2 ^ 33
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [Nat.min_eq_right (by omega_arith)]
    obtain h2 : (decide (v < 2 ^ 33)) = false := decide_eq_false h
    simp only [Spec.Rsa.exponentValid, h2, Bool.and_false]
    decide

/-- `k` bytes reversed from the low bytes of a number of `w` words below
`256^k`: its I2OSP. -/
theorem out_bytes {m m' : Mem} {O B : Addr} {d k w v : Nat} (hkw : k ≤ 8 * w)
    (hv : wv m B d w = v) (hvk : v < 256 ^ k)
    (h : ∀ i < k, m' (off O i) = m (off B (d + (k - 1 - i)))) :
    Spec.Rsa.bytesAt m' O k = Spec.Rsa.i2osp v k := by
  rw [VG.Proof.Bignum.reversed_i2osp m m' (off B d) O k fun j hj => by
    rw [h j hj, off, off, Offset.add_add]]
  congr 1
  obtain e := VG.Proof.Bignum.read_eq_wv m B d w
  rw [hv] at e
  rw [VG.Proof.Bignum.read_prefix_value m (off B d) hkw (by
    rw [e, ← VG.Proof.Bignum.pow256_eq]; exact hvk), e]

theorem zero_bytes {m' : Mem} {O : Addr} {k : Nat} (h : ∀ i < k, m' (off O i) = 0) :
    Spec.Rsa.bytesAt m' O k = List.replicate k 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
  exact h i h1

theorem bytes_apart {m m' : Mem} {B X : Addr} {Z o n k : Nat} (h : Mont.Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off X i ≠ x) : Spec.Rsa.bytesAt m' X k = Spec.Rsa.bytesAt m X k := by
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  show m' (off X i) = m (off X i)
  refine h _ (Or.inr ?_)
  have := hsep i hi (off X i)
  simp only [Mont.ofs, ofs] at this ⊢
  by_contra hc
  exact this (by omega) rfl

theorem mask_and_prop (a : Bool) (p : Prop) [Decidable p] :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if a then 1 else 0)) &&&
        (if p then BitVec.allOnes 64 else 0) =
      BitVec.ofNat 64 0 - BitVec.ofNat 64 (if (a && decide p) then 1 else 0) := by
  by_cases hp : p <;> simp only [hp, decide_true, decide_false, ↓reduceIte] <;> cases a <;> decide

/-- Memory changed only at offsets `[d, d + L)` of `S`, then at `O`'s first
`k` bytes. -/
theorem frame_two {S O : Addr} {d L k : Nat} {m m₁ m' : Mem} (h₁ : Mont.Outside S d L m m₁)
    (h₂ : Mont.Outside O 0 k m₁ m') (hdL : d + L ≤ 2 ^ 64) : Frame [⟨off S d, L⟩, ⟨O, k⟩] m m' := by
  intro x hx
  obtain a := hx _ (List.mem_cons_self ..)
  obtain b := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [Region.Contains] at a b
  rw [h₂ x (Or.inr (by simp only [Mont.ofs]; omega_arith))]
  refine h₁ x ?_
  have := Offset.lt_iff x S (d := d) (n := L) hdL
  simp only [Mont.ofs]
  by_contra hc
  exact a (by have := this.mpr ⟨by omega, by omega⟩; simp only [off]; omega_using [this])

/-- The public data of a run: `out` and `k`, `pre`, `e` and its length, the
input, and the working space and its size in bytes. -/
structure PD where
  O : Addr
  k : Nat
  P : Addr
  E : Addr
  L : Nat
  X : Addr
  S : Addr
  Z : Nat

/-- The words of a number of `k` bytes. -/
abbrev PD.w (d : PD) : Nat := (d.k + 7) / 8

/-- What holds after `setup`. -/
structure Mid (d : PD) (s : State) : Prop where
  scr : Scr s d.S d.Z
  outW : ∀ i < d.k, InRegions s.wr (off d.O i) 1
  nwO : d.O.toNat + d.k ≤ 2 ^ 64
  k64 : 64 ≤ d.k
  k1024 : d.k ≤ 1024
  hZ : slot d.w 8 ≤ d.Z
  L1 : 1 ≤ d.L
  Lk : d.L ≤ d.k
  nwP : d.P.toNat + 16 * d.w ≤ 2 ^ 64
  alP : d.P.toNat % 8 = 0
  sepP : ∀ x, ofs d.P x < 16 * d.w → d.Z ≤ ofs d.S x
  sepO : ∀ x, ofs d.O x < d.k → d.Z ≤ ofs d.S x
  sepE : ∀ i < d.L, ∀ x, ofs d.S x < d.Z → off d.E i ≠ x
  sepX : ∀ i < d.k, ∀ x, ofs d.S x < d.Z → off d.X i ≠ x
  rdP : ∀ i < 2 * d.w, InRegions (s.rd ++ s.wr) (off d.P (8 * i)) 8
  rdE : ∀ i < d.L, InRegions (s.rd ++ s.wr) (off d.E i) 1
  rdX : ∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.X i) 1
  a2 : s.gpr .a2 = off d.P 0
  a4 : s.gpr .a4 = off d.E 0
  a5 : s.gpr .a5 = BitVec.ofNat 64 d.L
  a6 : s.gpr .a6 = d.X
  s6 : s.gpr .s6 = d.S
  s10 : s.gpr .s10 = off d.O 0
  s11 : s.gpr .s11 = BitVec.ofNat 64 d.k
  a7 : s.gpr .a7 = off d.S (slot d.w 0)
  t0 : s.gpr .t0 = BitVec.ofNat 64 d.w
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (d.w + 2))

/-- The registers from `readE` to `output`. -/
def midRegs : List Reg :=
  [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4, .s7, .s8,
    .s9]

/-- What holds after `output`: the result, with only the arrays and `out`
changed. -/
def MidPost (d : PD) (s t : State) : Prop :=
  (∀ nB : List Byte, nB.length = d.k →
    Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem d.P (2 * d.w)) →
    Spec.Rsa.written t.mem d.O d.k ((t.gpr .a0).setWidth 32)
      (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem d.E d.L) (Spec.Rsa.bytesAt s.mem d.X d.k))) ∧
    Frame [⟨off d.S (slot d.w 0), 8 * (8 * (d.w + 2))⟩, ⟨d.O, d.k⟩] s.mem t.mem ∧ Keep midRegs s t

/-- `e`'s number, saturated. -/
abbrev PD.ev (d : PD) (m : Mem) : Nat := sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m d.E d.L))

/-- The input's number. -/
abbrev PD.x (d : PD) (m : Mem) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt m d.X d.k)

/-- What holds after `sanitize`, from `s` after `setup`. -/
structure M5 (d : PD) (s t : State) : Prop where
  keep : Keep midRegs s t
  s7 : t.gpr .s7 = BitVec.ofNat 64 (d.ev s.mem) <<< 31
  s9 : t.gpr .s9 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if Spec.Rsa.exponentValid (d.ev s.mem) then 1 else 0)
  a7 : t.gpr .a7 = off d.S (slot d.w 0)
  odd : wv t.mem d.S (slot d.w 0) d.w % 2 = 1
  ge2 : 2 ≤ wv t.mem d.S (slot d.w 0) d.w
  low : (Mont.word t.mem d.S (slot d.w 0)).toNat % 2 = 1
  rr : wv t.mem d.S (slot d.w 1) d.w < wv t.mem d.S (slot d.w 0) d.w
  valid : wv s.mem d.P 0 d.w % 2 = 1 → 2 ^ (64 * (d.w - 1)) ≤ wv s.mem d.P 0 d.w →
    wv t.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w ∧
      (wv s.mem d.P (8 * d.w) d.w < wv s.mem d.P 0 d.w → wv t.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w)
  top : Mont.word t.mem d.S (slot d.w 4 + 8 * d.w) = 0
  x : wv t.mem d.S (slot d.w 4) d.w = d.x s.mem
  frame : Mont.Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s.mem t.mem

theorem mid5_ok {d : PD} {s : State} {c : Prog isa} {Q : State → Prop} (h : Mid d s)
    (hQ : ∀ t, M5 d s t → WP isa c t Q) :
    WP isa (.seq readE (.seq (.block checkE) (.seq copyPre (.seq loadX (.seq sanitize c))))) s Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  obtain hw8 : 8 ≤ d.w := by have := h.k64; omega_arith
  obtain hw' : d.w < 2 ^ 31 := by have := h.k1024; omega_arith
  obtain hkw : d.k ≤ 8 * d.w := by omega_arith
  obtain e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  -- `e`.
  refine WP.seq (WP.mono (readE_ok (E := d.E) (L := d.L) h.a4 h.a5 h.L1
    (by have := h.Lk; have := h.k1024; omega_arith) h.rdE) fun s₁ ⟨⟨a7', m1⟩, k1⟩ => ?_)
  obtain hev2 : d.ev s.mem ≤ 2 ^ 33 := by unfold PD.ev sat; omega_arith
  refine WP.seq (WP.mono (checkE_ok a7' hev2) fun s₂ ⟨⟨a9, a7'', m2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  obtain m12 : s₂.mem = s.mem := m2.trans m1
  -- `pre` into arrays 0 and 1.
  refine WP.seq (WP.mono (copyPre_ok (h.scr.congr k12.2.2) h.nwP h.alP (by rw [k12.2.1, k12.2.2]; exact h.rdP)
    ((k12.gpr (by decide)).trans h.a2) ((k12.gpr (by decide)).trans h.a7)
    ((k12.gpr (by decide)).trans h.s5) ((k12.gpr (by decide)).trans h.t0) (by omega_arith) hw' hZ h.sepP)
    fun s₃ ⟨⟨c0, c1, out3⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  rw [m12] at c0 c1 out3
  obtain N3 : wv s₃.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w :=
    VG.Proof.Bignum.wv_congr2 fun i hi => by rw [Nat.zero_add]; exact c0 i hi
  obtain R3 : wv s₃.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w :=
    VG.Proof.Bignum.wv_congr2 fun i hi => c1 i hi
  -- The input into array 4.
  refine WP.seq (WP.mono (loadX_ok (h.scr.congr k13.2.2) ((k13.gpr (by decide)).trans h.s6)
    ((k13.gpr (by decide)).trans h.a6) ((k13.gpr (by decide)).trans h.s11)
    ((k13.gpr (by decide)).trans h.a7) ((k13.gpr (by decide)).trans h.s5)
    ((k13.gpr (by decide)).trans h.t0) (by omega_arith) hkw hw' hZ (by rw [k13.2.1, k13.2.2]; exact h.rdX) h.sepX)
    fun s₄ ⟨⟨x4, z4, out4, a74, s74⟩, k4⟩ => ?_)
  rw [bytes_apart out3 (by omega_arith) h.sepX] at x4
  obtain k14 := k13.trans k4
  obtain N4 : wv s₄.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w := by
    rw [← wsv_wv, Mont.Outside.wordsVal out4 (by omega_arith) (by omega_arith), wsv_wv, N3]
  obtain R4 : wv s₄.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w := by
    rw [← wsv_wv, Mont.Outside.wordsVal out4 (by omega_arith) (by omega_arith), wsv_wv, R3]
  -- `n` and `R² mod n` made safe.
  refine WP.seq (WP.mono (sanitize_ok (h.scr.congr k14.2.2) (by omega_arith) hw' hZ a74
    ((k14.gpr (by decide)).trans h.s5) ((k14.gpr (by decide)).trans h.t0))
    fun s₅ ⟨⟨n5o, n5g, n5w, r5l, n5v, out5⟩, k5⟩ => hQ s₅ ⟨(k14.trans k5).mono (by decide), ?_, ?_,
      (k5.gpr (by decide)).trans a74, ?_, ?_, n5w, ?_, ?_,
      by rw [Mont.Outside.word out5 (by omega_arith) (by omega_arith)]; exact z4, ?_,
      ((Mont.Outside.mono out3 (Nat.le_refl _) (by omega_arith)).trans
        (Mont.Outside.mono out4 (by omega_arith) (by omega_arith))).trans
        (Mont.Outside.mono out5 (Nat.le_refl _) (by omega_arith))⟩)
  · rw [k5.gpr (by decide), s74, k3.gpr (by decide)]; exact a7''
  · rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide)]; exact a9
  · rw [← wsv_wv]; exact n5o
  · rw [← wsv_wv]; exact n5g
  · rw [← wsv_wv, ← wsv_wv]; exact r5l
  · simp only [wsv_wv, N4, R4] at n5v
    exact n5v
  · rw [← wsv_wv, Mont.Outside.wordsVal out5 (by omega_arith) (by omega_arith)]; exact x4

/-- What holds after `power`, from `s` after `setup`, with `N` the modulus
used. -/
structure M8 (d : PD) (s u : State) (N : Nat) : Prop where
  keep : Keep midRegs s u
  a7 : u.gpr .a7 = off d.S (slot d.w 0)
  s9 : u.gpr .s9 = BitVec.ofNat 64 0 -
    BitVec.ofNat 64 (if (Spec.Rsa.exponentValid (d.ev s.mem) && decide (d.x s.mem < N)) then 1 else 0)
  res : wv s.mem d.P 0 d.w % 2 = 1 → 2 ^ (64 * (d.w - 1)) ≤ wv s.mem d.P 0 d.w →
    wv s.mem d.P (8 * d.w) d.w = 2 ^ (64 * d.w) * 2 ^ (64 * d.w) % wv s.mem d.P 0 d.w →
    N = wv s.mem d.P 0 d.w ∧ (Spec.Rsa.exponentValid (d.ev s.mem) = true →
      wv u.mem d.S (slot d.w 4) d.w = d.x s.mem ^ (d.ev s.mem % 2 ^ 33) % N)
  frame : Mont.Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s.mem u.mem

/-- What holds after `checkX`, from `t` after `sanitize`. -/
def M7 (d : PD) (t s₇ : State) : Prop :=
  ∃ s₆ : State, (((Mont.word t.mem d.S (slot d.w 0)).toNat * (s₆.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
      s₆.mem = t.mem) ∧
    Keep [.s0, .s1, .s2, .s3, .t1] t s₆ ∧
    (s₇.gpr .s9 = s₆.gpr .s9 &&& (if Mont.wordsVal s₆.mem d.S (slot d.w 4) d.w <
        Mont.wordsVal s₆.mem d.S (slot d.w 0) d.w then BitVec.allOnes 64 else 0) ∧
      Mont.Outside d.S (slot d.w 3) (8 * d.w) s₆.mem s₇.mem) ∧
    Keep [.a0, .a5, .a6, .t3, .t4, .t5, .s0, .s1, .s2, .s3, .s4, .s9] s₆ s₇

theorem mid7_ok {d : PD} {s t : State} (h : Mid d s) (h5 : M5 d s t) :
    WP isa (.seq (.block minv) checkX) t (M7 d t) := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  obtain hw8 : 8 ≤ d.w := by have := h.k64; omega_arith
  obtain hw' : d.w < 2 ^ 31 := by have := h.k1024; omega_arith
  obtain e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  have k5 := h5.keep
  obtain hs₅ := h.scr.congr k5.2.2
  refine WP.seq (WP.mono (minv_ok hs₅ h5.a7 (slot_al _ 0) (by omega_arith) h5.low)
    fun s₆ ⟨⟨iinv, m6⟩, k6⟩ => ?_)
  obtain k56 := k5.trans k6
  exact WP.mono (checkX_ok (h.scr.congr k56.2.2) (by omega_arith) hw' hZ ((k6.gpr (by decide)).trans h5.a7)
    ((k56.gpr (by decide)).trans h.s5) ((k56.gpr (by decide)).trans h.t0)
    (by rw [m6]; exact h5.top)) fun s₇ ⟨⟨c9, out7⟩, k7⟩ => ⟨s₆, ⟨iinv, m6⟩, k6, ⟨c9, out7⟩, k7⟩

/-- From `setup` to the checks. -/
theorem prep_ok {d : PD} {s : State} (h : Mid d s) :
    WP isa prep s fun u => ∃ t, M5 d s t ∧ M7 d t u :=
  mid5_ok h fun t h5 => WP.mono (mid7_ok h h5) fun _ h7 => ⟨t, h5, h7⟩

theorem mid8_ok {d : PD} {s t s₇ : State} {Q : State → Prop} (h : Mid d s) (h5 : M5 d s t)
    (h7 : M7 d t s₇) (hQ : ∀ u N, M8 d s u N → Q u) : WP isa power s₇ Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  obtain hw8 : 8 ≤ d.w := by have := h.k64; omega_arith
  obtain hw' : d.w < 2 ^ 31 := by have := h.k1024; omega_arith
  obtain e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  have k5 := h5.keep
  obtain ⟨s₆, ⟨iinv, m6⟩, k6, ⟨c9, out7⟩, k7⟩ := h7
  obtain k56 := k5.trans k6
  obtain k57 := k56.trans k7
  obtain out7' : Mont.Outside d.S (slot d.w 3) (8 * d.w) t.mem s₇.mem := by
    rw [← m6]; exact fun x hx => out7 x hx
  rw [m6, wsv_wv, wsv_wv] at c9
  obtain N7 : wv s₇.mem d.S (slot d.w 0) d.w = wv t.mem d.S (slot d.w 0) d.w := by
    rw [← wsv_wv, ← wsv_wv]; exact Mont.Outside.wordsVal out7' (by omega_arith) (by omega_arith)
  obtain R7 : wv s₇.mem d.S (slot d.w 1) d.w = wv t.mem d.S (slot d.w 1) d.w := by
    rw [← wsv_wv, ← wsv_wv]; exact Mont.Outside.wordsVal out7' (by omega_arith) (by omega_arith)
  obtain X7 : wv s₇.mem d.S (slot d.w 4) d.w = wv t.mem d.S (slot d.w 4) d.w := by
    rw [← wsv_wv, ← wsv_wv]; exact Mont.Outside.wordsVal out7' (by omega_arith) (by omega_arith)
  obtain W7 : Mont.word s₇.mem d.S (slot d.w 0) = Mont.word t.mem d.S (slot d.w 0) :=
    Mont.Outside.word out7' (by omega_arith) (by omega_arith)
  refine WP.mono (power_ok (E := d.ev s.mem) (h.scr.congr k57.2.2) (by omega_arith) hw' hZ
    ((k7.gpr (by decide)).trans ((k6.gpr (by decide)).trans h5.a7)) ((k57.gpr (by decide)).trans h.s5)
    ((k57.gpr (by decide)).trans h.t0)
    (by rw [k7.gpr (by decide)]
        show ((Mont.word s₇.mem d.S (slot d.w 0)).toNat * (s₆.gpr .t1).toNat + 1) % 2 ^ 64 = 0
        rw [W7]; exact iinv)
    (by rw [wsv_wv, N7]; exact h5.ge2) (by rw [wsv_wv, N7]; exact h5.odd)
    (by rw [wsv_wv, wsv_wv, N7, R7]; exact h5.rr)
    (by rw [k7.gpr (by decide), k6.gpr (by decide)]; exact h5.s7)) fun s₈ ⟨⟨p8, out8⟩, k8⟩ => ?_
  simp only [wsv_wv, N7, R7, X7, h5.x] at p8
  refine M8.mk (N := wv t.mem d.S (slot d.w 0) d.w) ((k57.trans k8).mono (by decide))
    ((k8.gpr (by decide)).trans ((k7.gpr (by decide)).trans ((k6.gpr (by decide)).trans h5.a7))) ?_
    (fun hodd htop hRR => ?_) ?_ |> hQ s₈ _
  · rw [k8.gpr (by decide), c9, k6.gpr (by decide), h5.s9, h5.x, mask_and_prop]
  · obtain ⟨N5, RR5⟩ := h5.valid hodd htop
    obtain hRl : wv s.mem d.P (8 * d.w) d.w < wv s.mem d.P 0 d.w := by
      rw [hRR]; exact Nat.mod_lt _ (by omega_arith)
    refine ⟨N5, fun he => p8 ?_ ?_⟩
    · simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at he
      omega_using [he]
    · rw [RR5 hRl, N5, hRR]
  · have o8 : Mont.Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s₇.mem s₈.mem := fun x hx => out8 x fun j hj => by
      obtain e2 := e 2; have e5 := e 5; have e6 := e 6; have e7 := e 7
      simp only [powJs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [Mont.ofs, ofs] at hx ⊢ <;> omega_arith
    exact (h5.frame.trans (Mont.Outside.mono out7' (by omega_arith) (by omega_arith))).trans o8

theorem midOut_ok {d : PD} {s u : State} {N : Nat} {Q : State → Prop} (h : Mid d s) (h8 : M8 d s u N)
    (hQ : ∀ t, MidPost d s t → WP isa (.block PublicChecked.restore) t Q) :
    WP isa (.seq output (.block PublicChecked.restore)) u Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  obtain hkw : d.k ≤ 8 * d.w := by omega_arith
  have e0 : slot d.w 0 = hdrBytes + 0 * (8 * (d.w + 2)) := rfl
  have e8 : slot d.w 8 = hdrBytes + 8 * (8 * (d.w + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have k8 := h8.keep
  refine WP.seq (WP.mono (output_ok (h.scr.congr k8.2.2) (by rw [k8.2.2]; exact h.outW) h.nwO h8.a7
    ((k8.gpr (by decide)).trans h.s5) ((k8.gpr (by decide)).trans h.s11)
    ((k8.gpr (by decide)).trans h.s10) h8.s9 (by have := h.k64; omega_arith) hkw h.hZ h.sepO)
    fun t ⟨⟨ob, outt, t3⟩, kt⟩ => hQ t ⟨?_, frame_two h8.frame outt (by have := h.k1024; omega_arith),
      (k8.trans kt).mono (by decide)⟩)
  intro nB hl hpp
  obtain ⟨hv, hn, hr⟩ := VG.Proof.Bignum.pre_of_some hl h.k64 hpp
  obtain ⟨hodd, hn1, htop⟩ := VG.Proof.Bignum.valid_facts hv h.k64
  rw [← hn] at hodd htop hn1
  obtain ⟨hN, res⟩ := h8.res hodd htop
    (by rw [hr, hn, ← Nat.pow_add, show 64 * d.w + 64 * d.w = 128 * d.w by omega_arith])
  rw [hN, hn] at res ob t3
  obtain hE := exponentValid_sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L))
  obtain hnk : Spec.Rsa.os2ip nB < 256 ^ d.k := by rw [← hl]; exact VG.Proof.Bignum.os2ip_lt nB
  unfold Spec.Rsa.publicOpChecked Spec.Rsa.publicOp Spec.Rsa.encrypt
  rw [← hE, hl]
  by_cases hb : (Spec.Rsa.exponentValid (d.ev s.mem) && decide (d.x s.mem < Spec.Rsa.os2ip nB)) = true
  · obtain ⟨he, hx⟩ : Spec.Rsa.exponentValid (d.ev s.mem) = true ∧ d.x s.mem < Spec.Rsa.os2ip nB := by
      simpa using hb
    obtain hlt : d.ev s.mem < 2 ^ 33 := by
      simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at he; exact he.2
    obtain hev : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L)) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L) := by
      unfold PD.ev sat at hlt; unfold sat; omega_arith
    replace res := res he
    simp only [PD.ev, PD.x] at he hx res
    simp only [he, hv, hx, ↓reduceIte, Option.map_some]
    refine ⟨by rw [t3, hb]; rfl, ?_⟩
    rw [VG.Proof.Bignum.powMod_eq]
    rw [hev, Nat.mod_eq_of_lt (a := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L)) (b := 2 ^ 33)
      (by rw [← hev]; exact hlt)] at res
    exact out_bytes hkw res (Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hnk) fun i hi => by
      rw [ob i hi]; simp only [hb, ↓reduceIte]
  · have hnone : (if Spec.Rsa.exponentValid (d.ev s.mem) = true then
        (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) d.k = true then
          Option.map (fun x => Spec.Rsa.i2osp x d.k)
            (if d.x s.mem < Spec.Rsa.os2ip nB then
              some (Spec.Rsa.powMod (d.x s.mem) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L))
                (Spec.Rsa.os2ip nB))
            else none)
        else none)
      else none) = none := by
      by_cases he : Spec.Rsa.exponentValid (d.ev s.mem) = true
      · have hx : ¬ d.x s.mem < Spec.Rsa.os2ip nB := fun hx => hb (by simp [he, hx])
        simp only [he, hv, hx, ↓reduceIte, Option.map_none]
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
    simp only [PD.ev, PD.x] at hnone
    rw [hnone]
    refine ⟨by rw [t3]; simp only [hb]; rfl,
      zero_bytes fun i hi => by rw [ob i hi]; simp only [hb, Bool.false_eq_true, ↓reduceIte]⟩

/-- From `setup` to the output. -/
theorem mid_ok {d : PD} {s : State} {Q : State → Prop} (h : Mid d s)
    (hQ : ∀ t, MidPost d s t → WP isa (.block PublicChecked.restore) t Q) :
    WP isa (.seq prep (.seq power (.seq output (.block PublicChecked.restore)))) s Q :=
  WP.seq (WP.mono (prep_ok h) fun _ ⟨_, h5, h7⟩ => WP.seq (mid8_ok h h5 h7 fun _ _ h8 => midOut_ok h h8 hQ))

end VG.Proof.Bignum.RISCV64.Pub

end

end

/-!
# The RSA public-key operation on RISC-V: the function

`fnContract`: `vg_rsa_public_precomputed_checked` on the registers and the
stack, its working space and length the arguments in memory.

`fn_correct`: `publicChecked` reads the working space's address from the
stack, saves the callee-saved registers in its header, runs `mid_ok` from
the state `setup` leaves (`Mid`), and restores them.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pub

open VG VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Bignum.RISCV64.PublicChecked
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

/-- The arguments on the stack: `scratch` and `scratch_len`. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- `vg_rsa_public_precomputed_checked`, on the registers and the stack. -/
def fnContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let pre : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat * 8⟩
    let e : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
    let inp : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.rd = [pre, e, inp, stackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint pre ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint (stackArgs s) ∧
      pre.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .a1).toNat ∧ (s.gpr .a3).toNat = Spec.Rsa.precomputedWords (s.gpr .a1).toNat ∧
      (s.gpr .a7).toNat = (s.gpr .a1).toNat ∧ 1 ≤ (s.gpr .a5).toNat ∧
      (s.gpr .a5).toNat ≤ (s.gpr .a1).toNat ∧ Spec.Rsa.publicScratchWords (s.gpr .a1).toNat ≤ (stackArg s 1).toNat ∧
      (s.gpr .a2).toNat % 8 = 0 ∧ (stackArg s 0).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s s' :=
    ∀ nB : List Byte, nB.length = (s.gpr .a1).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .a0) (s.gpr .a1).toNat ((s'.gpr .a0).setWidth 32)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
          (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a1).toNat))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      (Spec.Rsa.wordsAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a4) (s₁.gpr .a5).toNat).map (·.toNat) =
        (Spec.Rsa.wordsAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a4) (s₂.gpr .a5).toNat).map (·.toNat)

/-- The public data of a state on entry. -/
def dataOf (s : State) : PD :=
  ⟨s.gpr .a0, (s.gpr .a1).toNat, s.gpr .a2, s.gpr .a4, (s.gpr .a5).toNat, s.gpr .a6, stackArg s 0,
    (stackArg s 1).toNat * 8⟩

theorem sep_of_disjoint {A S : Addr} {n Z : Nat} (h : (⟨A, n⟩ : Region).Disjoint ⟨S, Z⟩) :
    ∀ x, ofs A x < n → Z ≤ ofs S x := fun x hx => by
  by_contra hc
  exact h x (by simp only [Region.Contains]; simp only [ofs] at hx; omega_arith)
    (by simp only [Region.Contains]; simp only [ofs] at hc; omega_arith)

theorem ne_of_disjoint {A S : Addr} {n Z : Nat} (h : (⟨A, n⟩ : Region).Disjoint ⟨S, Z⟩) (hn : n ≤ 2 ^ 64) :
    ∀ i < n, ∀ x, ofs S x < Z → off A i ≠ x := fun i hi x hx e => by
  subst e
  exact h _ (Offset.contains_base (d := i) _ (by omega_arith) (by omega_arith))
    (by simp only [Region.Contains]; simp only [ofs, off] at hx; omega_arith)

theorem saved_ne_t0 : ∀ i < 12, PublicChecked.saved i ≠ .t0 := by decide

theorem sav_al {S : Addr} (hS : S.toNat % 8 = 0) (hn : S.toNat + 256 ≤ 2 ^ 64) {i : Nat} (hi : i < 12) :
    (off (savW S) (8 * i)).toNat % 8 = 0 := by
  have e : off (savW S) (8 * i) = S + BitVec.ofNat 64 (128 + 8 * i) := by
    show S + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i) = _
    rw [Offset.add_add]
  have h2 : (S + BitVec.ofNat 64 (128 + 8 * i)).toNat = S.toNat + (128 + 8 * i) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [hn, hi]
  rw [e, h2]
  omega_using [hS]

/-- `save` and `setup`: `Mid`, with the callee-saved registers saved. -/
theorem front_ok {s : State} (h : fnContract.pre s) :
    WP isa (.block (PublicChecked.save ++ setup)) s fun s₃ =>
      Mid (dataOf s) s₃ ∧
        (∀ i < 12, s₃.mem.readW (off (savW (stackArg s 0)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
        Keep (([.t0, .s6] : List Reg) ++ ([.a7, .s5, .s10, .s11, .t0] : List Reg)) s s₃ ∧
        Frame [savR (savW (stackArg s 0))] s.mem s₃.mem := by
  obtain ⟨hrd, hwr, dOP, dOE, dOX, dOS, dOA, dPS, dES, dXS, dSA, nwO, nwP, nwE, nwX, nwS, ⟨hk, hk'⟩, hpl,
    hxl, hL1, hLk, hsl, alP, alS, alsp⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  unfold PublicChecked.save
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp),
    by simp [Region.Contains]⟩ (by omega_arith)) fun s₁ ⟨⟨a0', m1, sp1⟩, k1⟩ => ?_)
  have hin : ∀ i < 12, InRegions s₁.wr (off (savW (s₁.gpr .t0)) (8 * i)) 8 := fun i hi => by
    rw [a0', k1.2.2, hwr]
    show InRegions _ (stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.block_append (WP.mono (save_ok s₁ hin (fun i hi => by
    rw [a0']; exact sav_al alS (by omega_arith) hi)) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have e1 : s₂.gpr .a1 = BitVec.ofNat 64 (s.gpr .a1).toNat :=
    (k12.gpr (by decide)).trans (by simp)
  refine WP.mono (setup_ok (O := s.gpr .a0) (k := (s.gpr .a1).toNat) (k12.gpr (by decide)) e1
    (hS.s6.trans a0') hk') fun s₃ ⟨⟨j10, j11, j0, j5, j7, jm⟩, k₃⟩ => ?_
  have k := k12.trans k₃
  have hrd₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k.2.1, k.2.2]
  have hh : hdrBytes = 256 := rfl
  have hwd : (dataOf s).w = ((s.gpr .a1).toNat + 7) / 8 := rfl
  have hk1 : (s.gpr .a1).toNat < 2 ^ 64 := (s.gpr .a1).isLt
  refine ⟨⟨Scr.of_mem (by rw [k.2.2, hwr]; simp [dataOf]) nwS alS,
    fun i hi => ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩, by rw [k.2.2, hwr]; simp,
      Offset.contains_base _ (by change i < (s.gpr .a1).toNat at hi; omega_arith)
        (by change i < (s.gpr .a1).toNat at hi; omega_arith)⟩, nwO,
    hk, hk', by show slot (((s.gpr .a1).toNat + 7) / 8) 8 ≤ (stackArg s 1).toNat * 8; unfold slot; rw [hh]; omega_arith,
    hL1, hLk, by show (s.gpr .a2).toNat + 16 * (((s.gpr .a1).toNat + 7) / 8) ≤ 2 ^ 64; omega_arith, alP,
    fun x hx => sep_of_disjoint dPS x (by
      change ofs (s.gpr .a2) x < 16 * (((s.gpr .a1).toNat + 7) / 8) at hx; omega_arith), sep_of_disjoint dOS,
    ne_of_disjoint dES (Nat.le_of_lt (s.gpr .a5).isLt),
    fun i hi => ne_of_disjoint dXS (Nat.le_of_lt (s.gpr .a7).isLt) i (by
      change i < (s.gpr .a1).toNat at hi; omega_arith),
    fun i hi => ⟨⟨s.gpr .a2, (s.gpr .a3).toNat * 8⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < 2 * (((s.gpr .a1).toNat + 7) / 8) at hi; omega_arith) (by
      change i < 2 * (((s.gpr .a1).toNat + 7) / 8) at hi; omega_arith)⟩,
    fun i hi => ⟨⟨s.gpr .a4, (s.gpr .a5).toNat⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < (s.gpr .a5).toNat at hi; omega_arith) (by change i < (s.gpr .a5).toNat at hi; omega_arith)⟩,
    fun i hi => ⟨⟨s.gpr .a6, (s.gpr .a7).toNat⟩, by rw [hrd₃, hrd]; simp, Offset.contains_base _ (by
      change i < (s.gpr .a1).toNat at hi; omega_arith) (by change i < (s.gpr .a1).toNat at hi; omega_arith)⟩,
    by rw [k.gpr (by decide)]; simp [dataOf, off], by rw [k.gpr (by decide)]; simp [dataOf, off],
    by rw [k.gpr (by decide)]; simp [dataOf], k.gpr (by decide),
    (k₃.gpr (by decide)).trans (hS.s6.trans a0'),
    by rw [j10]; simp [dataOf, off], j11, j7, j0,
    by rw [j5, hwd, Nat.mul_add]⟩, fun i hi => ?_, k, ?_⟩
  · rw [jm, ← a0', hS.saved i hi, k1.gpr fun h => saved_ne_t0 i hi (List.mem_singleton.mp h)]
  · rw [jm, ← m1, ← a0']; exact hS.frame

/-- `e`'s bytes, apart from the saved registers. -/
theorem front_e {s s₃ : State} (h : fnContract.pre s) (fr : Frame [savR (savW (stackArg s 0))] s.mem s₃.mem) :
    Spec.Rsa.bytesAt s₃.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat := by
  obtain ⟨-, -, -, -, -, -, -, -, dES, -, -, -, -, -, -, nwS, -, -, -, -, -, hsl, -, -, -⟩ := h
  simp only [Spec.Rsa.publicScratchWords] at hsl
  have savR_sub : Region.Sub (savR (savW (stackArg s 0))) ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    Offset.sub_base _ (by omega_arith)
  refine VG.Proof.Rsa.rsa_bytes_frame fr (s.gpr .a5).isLt fun r hr => ?_
  simp only [List.mem_singleton] at hr
  subst hr
  exact dES.sub_right savR_sub

theorem ra_free : Reg.ra ∉ midRegs ∧ Reg.ra ∉ (([.t0, .s6] : List Reg) ++ ([.a7, .s5, .s10, .s11, .t0] : List Reg)) ∧
    ∀ i < 12, Reg.ra ≠ PublicChecked.saved i := by decide

theorem pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ tr t, Exec isa publicChecked s tr t ∧ abiPreserved s t ∧ fnContract.post s t := by
  show WP isa publicChecked s fun t => abiPreserved s t ∧ fnContract.post s t
  suffices main : WP isa publicChecked s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ fnContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  have hpre := h
  obtain ⟨hrd, hwr, dOP, dOE, dOX, dOS, dOA, dPS, dES, dXS, dSA, nwO, nwP, nwE, nwX, nwS, ⟨hk, hk'⟩, hpl,
    hxl, hL1, hLk, hsl, alP, alS, alsp⟩ := h
  simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, Spec.Rsa.publicScratchWords] at hpl hsl
  have hh : hdrBytes = 256 := rfl
  have sav_sub : ∀ i < 12, Region.Sub ⟨off (savW (stackArg s 0)) (8 * i), 8⟩
      ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ := fun i hi => by
    show Region.Sub ⟨stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i), 8⟩ _
    rw [Offset.add_add]; exact Offset.sub_base _ (by omega_arith)
  have savR_sub : Region.Sub (savR (savW (stackArg s 0))) ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ :=
    Offset.sub_base _ (by omega_arith)
  unfold publicChecked
  refine WP.seq (WP.mono (front_ok hpre) fun s₃ ⟨hM, hsv, k3, fr3⟩ => ?_)
  refine mid_ok hM fun t ⟨hpost, hfr, kt⟩ => ?_
  have hin : ∀ i < 12, InRegions t.wr (off (savW (stackArg s 0)) (8 * i)) 8 := fun i hi => by
    rw [kt.2.2, k3.2.2, hwr]
    show InRegions _ (stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 12, t.mem.readW (off (savW (stackArg s 0)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
    fun i hi => by
      rw [hfr.readW (r := ⟨off (savW (stackArg s 0)) (8 * i), 8⟩) (by simp [Region.Contains]) ?_ (by decide)]
      · exact hsv i hi
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl
        · show Region.Disjoint ⟨stackArg s 0 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i), 8⟩
            ⟨stackArg s 0 + BitVec.ofNat 64 (slot (dataOf s).w 0), _⟩
          rw [Offset.add_add]
          exact Offset.disjoint _ (Or.inl (by unfold slot; rw [hh]; omega_arith)) (by omega_arith)
            (by have := hM.hZ; unfold slot at this ⊢; rw [hh] at this ⊢; show _ ≤ 2 ^ 64
                have := hM.scr.nowrap; omega_arith)
        · exact (dOS.symm.sub_left (sav_sub i hi))
  refine WP.mono (restore_ok t (S := stackArg s 0) (v := fun i => s.gpr (PublicChecked.saved i))
    (by rw [kt.gpr (by decide)]; exact hM.s6) hin (fun i hi => sav_al alS (by omega_arith) hi) hsav)
    fun u ⟨urs, uot, um, _, _, _⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pres_saved r hr
    exact urs i hi
  · rw [uot .ra ra_free.2.2, kt.gpr ra_free.1, k3.gpr ra_free.2.1]
  · intro nB hl hpp
    rw [uot .a0 (by decide), um]
    have hP : Spec.Rsa.wordsAt s₃.mem (s.gpr .a2) (2 * (dataOf s).w) =
        Spec.Rsa.wordsAt s.mem (s.gpr .a2) (s.gpr .a3).toNat := by
      rw [show 2 * (dataOf s).w = (s.gpr .a3).toNat by show 2 * (((s.gpr .a1).toNat + 7) / 8) = _; omega_arith]
      refine VG.Proof.Rsa.wordsAt_frame fr3 (by omega_arith) fun r hr => ?_
      simp only [List.mem_singleton] at hr
      subst hr
      exact (dPS.sub_left (Region.sub_prefix (by omega_arith))).sub_right savR_sub
    have hE := front_e hpre fr3
    have hX : Spec.Rsa.bytesAt s₃.mem (s.gpr .a6) (s.gpr .a1).toNat =
        Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a1).toNat := by
      refine VG.Proof.Rsa.rsa_bytes_frame fr3 (s.gpr .a1).isLt fun r hr => ?_
      simp only [List.mem_singleton] at hr
      subst hr
      exact (dXS.sub_left (Region.sub_prefix (by omega_arith))).sub_right savR_sub
    have := hpost nB hl (by rw [hpp]; exact congrArg some hP.symm)
    simp only [dataOf] at this
    rw [hE, hX] at this
    exact this

end VG.Proof.Bignum.RISCV64.Pub
