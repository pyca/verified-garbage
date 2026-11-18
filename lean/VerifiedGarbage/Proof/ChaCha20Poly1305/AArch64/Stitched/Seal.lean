module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Rest
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Main
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Correct
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.AArch64.Backends
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Counter
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Check
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Last
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.LoopRounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Save
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Tail
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rotate
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Transpose
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xor
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.CachedAdd
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.ContractPost
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.AArch64.Init
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.AddS
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Finalize
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Reduce
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Update
import VerifiedGarbage.Proof.Poly1305.Limbs64
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Spec.ChaCha20Poly1305.Contract
import VerifiedGarbage.Impl.ChaCha20.AArch64.Rows6
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Loop
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Lit
public import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Zero
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xar

/-! ### `ChaCha20Poly1305.AArch64.Tail.Kernel`, which this module and modules that import it used -/

section

/-! ### `ChaCha20Poly1305.AArch64.Tail.Round`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 on AArch64, the rest when encrypting: the rounds

`Tail.rounds`: ten double rounds of the four-block kernel (`Neon4`, with
SVE2's XAR if `sve`), and after each three blocks of Poly1305 (`Stitch.absorb3`) of
the 512 bytes from `W`, two of which `Tail.start` absorbed. The rounds write
only vector registers, and the blocks only `Poly.regs`; neither writes
memory, so each keeps what the other computes.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Tail

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20 (CState)
open VG.Impl.ChaCha20.AArch64.Neon4 (Op rol8Table)
open VG.Proof.ChaCha20.AArch64.Neon4 (Holds RoundSame step op_ok_for innerBlock_eq)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc bytesAt_succ)
open VG.Spec.ChaCha20 (innerBlock)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-- The operations, with SVE2 if `sve`. -/
theorem ops_ok (sve : Bool) : ∀ (ops : List Op) {vs : Nat → CState} {s : State}, Holds vs s →
    s.v .v30 = rol8Table →
    WP isa (.block (ops.flatMap (Op.codeFor sve))) s fun s' =>
      Holds (fun j => ops.foldl step (vs j)) s' ∧ RoundSame s s'
  | [], _, _, h, _ => WP.block_nil ⟨h, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  | op :: ops, _, _, h, ht => by
    exact WP.block_append ((op_ok_for sve op h ht).mono fun _ ⟨h', hs⟩ =>
      (ops_ok sve ops h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

/-- A double round. -/
theorem doubleRound_ok (sve : Bool) {vs : Nat → CState} {s : State} (h : Holds vs s)
    (ht : s.v .v30 = rol8Table) :
    WP isa (.block (Tail.doubleRound sve)) s fun s' =>
      Holds (fun j => innerBlock (vs j)) s' ∧ RoundSame s s' := by
  have e : (fun j => (VG.Impl.ChaCha20.AArch64.Mixed5.roundOps).foldl step (vs j)) =
      fun j => innerBlock (vs j) := funext fun j => innerBlock_eq (vs j)
  exact (ops_ok sve _ h ht).mono fun _ ⟨h', hs⟩ => ⟨e ▸ h', hs⟩

/-- The 512 bytes from `W` are readable, and so is the key. -/
structure Readable (W : Addr) (s : State) : Prop where
  blk : ∀ d, d + 8 ≤ 512 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) 8
  k0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r0Off) 8
  k1 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 Poly.r1Off) 8

theorem Readable.of {W : Addr} {s u : State} (h : Readable W s) (hrd : u.rd = s.rd)
    (hwr : u.wr = s.wr) (hx0 : u.gpr .x0 = s.gpr .x0) : Readable W u :=
  ⟨fun d hd => by rw [hrd, hwr]; exact h.blk d hd, by rw [hrd, hwr, hx0]; exact h.k0,
    by rw [hrd, hwr, hx0]; exact h.k1⟩

/-- The `n + 1`st block from `W`. -/
theorem absorb_next {R a : Nat} {W : Addr} {n : Nat} (hn : 16 * n + 16 ≤ 512) {s : State}
    (ha : Acc R (absorbAll R a (bytesAt s.mem W (16 * n))) s)
    (hp : s.gpr .x20 = W + BitVec.ofNat 64 (16 * n)) (hr : Readable W s) :
    WP isa (.block Poly.block) s fun u =>
      Acc R (absorbAll R a (bytesAt s.mem W (16 * (n + 1)))) u ∧
      u.gpr .x20 = W + BitVec.ofNat 64 (16 * (n + 1)) ∧ Keeps Poly.regs s u := by
  have hb (d : Nat) (hd : d + 8 ≤ 16) :
      InRegions (s.rd ++ s.wr) (s.gpr .x20 + BitVec.ofNat 64 d) 8 := by
    rw [hp, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hr.blk _ (by omega_using [hn, hd])
  refine (Poly.block_absorb s ha (hb 0 (by decide)) (hb 8 (by decide)) hr.k0 hr.k1).mono
    fun u ⟨hu, hx, hk⟩ => ⟨?_, ?_, hk⟩
  · have hl : (bytesAt s.mem W (16 * n)).length % 16 = 0 := by
      rw [Poly1305.length_bytesAt]; omega_using []
    rw [bytesAt_succ, Poly1305.absorbAll_append hl, ← hp]
    exact hu
  · rw [hx, hp, BitVec.add_assoc]
    change W + (BitVec.ofNat 64 (16 * n) + BitVec.ofNat 64 16) = _
    rw [← BitVec.ofNat_add, Nat.mul_succ]

/-- `k` blocks, from the `n + 1`st. -/
theorem absorbN_ok {R a : Nat} {W : Addr} (k : Nat) {n : Nat} (hn : 16 * n + 16 * k ≤ 512)
    {s : State} (ha : Acc R (absorbAll R a (bytesAt s.mem W (16 * n))) s)
    (hp : s.gpr .x20 = W + BitVec.ofNat 64 (16 * n)) (hr : Readable W s) :
    WP isa (.block ((List.replicate k Poly.block).flatten)) s fun u =>
      Acc R (absorbAll R a (bytesAt s.mem W (16 * (n + k)))) u ∧
      u.gpr .x20 = W + BitVec.ofNat 64 (16 * (n + k)) ∧ Keeps Poly.regs s u := by
  induction k generalizing n s with
  | zero => exact WP.block_nil ⟨ha, hp, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    rw [List.replicate_succ, List.flatten_cons]
    refine WP.block_append ((absorb_next (by omega_using [hn]) ha hp hr).mono fun s₁ ⟨a₁, p₁, k₁⟩ => ?_)
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    rw [← hm₁] at a₁
    refine (ih (n := n + 1) (by omega_using [hn]) a₁ p₁
      (hr.of k₁.2.2.1 k₁.2.2.2 (k₁.gpr' (r := .x0)))).mono fun u ⟨a, p, k'⟩ => ?_
    rw [hm₁, show n + 1 + k = n + (k + 1) by omega_using []] at a
    rw [show n + 1 + k = n + (k + 1) by omega_using []] at p
    exact ⟨a, p, (k₁.trans k').mono (by
      intro r h; simp only [List.mem_append] at h; rcases h with h | h <;> exact h)⟩

/-- After `i` iterations of the loop. -/
structure TI (vs : Nat → CState) (R a : Nat) (W : Addr) (s₀ s : State) (i : Nat) : Prop where
  vec : Holds (fun j => Nat.repeat innerBlock i (vs j)) s
  table : s.v .v30 = rol8Table
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ≠ .x4 → r ∉ Poly.regs → s.gpr r = s₀.gpr r
  ptr : s.gpr .x20 = W + BitVec.ofNat 64 (16 * (2 + 3 * i))
  acc : Acc R (absorbAll R a (bytesAt s₀.mem W (16 * (2 + 3 * i)))) s
  cnt : s.gpr .x4 = BitVec.ofNat 64 (10 - i)

theorem absorb3_eq : Stitch.absorb3 = (List.replicate 3 Poly.block).flatten := by
  simp only [Impl.ChaCha20Poly1305.AArch64.Stitch.absorb3, List.replicate, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.append_assoc]

/-- The loop body, from `TI … i` to `TI … (i + 1)`. -/
theorem iter_ok (sve : Bool) {vs : Nat → CState} {R a : Nat} {W : Addr} {s₀ s : State} {i : Nat}
    (hi : i < 10) (hr : Readable W s₀) (h : TI vs R a W s₀ s i) :
    WP isa (Tail.round sve) s fun u => TI vs R a W s₀ u (i + 1) := by
  unfold Tail.round
  apply WP.seq
  refine (doubleRound_ok sve h.vec h.table).mono fun b ⟨hb, hsb⟩ => ?_
  have hbacc : Acc R (absorbAll R a (bytesAt b.mem W (16 * (2 + 3 * i)))) b := by
    rw [hsb.mem, h.mem]
    exact h.acc.of (fun r _ => by rw [hsb.gpr]) hsb.mem
  have hbp : b.gpr .x20 = W + BitVec.ofNat 64 (16 * (2 + 3 * i)) := by rw [hsb.gpr]; exact h.ptr
  have hbr : Readable W b := hr.of (by rw [hsb.rd, h.rd]) (by rw [hsb.wr, h.wr])
    (by rw [hsb.gpr, h.keep _ (by decide) (by decide)])
  have hv : ∀ i ∈ (List.replicate 3 Poly.block).flatten, vdstOf i = none := by decide +kernel
  apply WP.block_append
  rw [absorb3_eq]
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv
    (absorbN_ok 3 (n := 2 + 3 * i) (by omega_using [hi]) hbacc hbp hbr)).mono
    fun c ⟨⟨hca, hcp, hck⟩, hcv, hcsp, hcr, hcw⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨c.write .x .x4 (c.gpr .x4 - BitVec.ofNat 64 1), ?_, WP.block_nil ?_⟩
  · simpa only [State.read, BitVec.setWidth_eq] using
      exec_subImm_x (s := c) (d := .x4) (n := .x4) (imm := 1) (by decide)
  have hcm : c.mem = s₀.mem := hck.2.1.trans (hsb.mem.trans h.mem)
  have hx4 : c.gpr .x4 = b.gpr .x4 := hck.gpr' (r := .x4)
  refine ⟨?_, ?_, hcm, hcr.trans (hsb.rd.trans h.rd), hcw.trans (hsb.wr.trans h.wr),
    hcsp.trans (hsb.sp.trans h.sp), ?_, ?_, ?_, ?_⟩
  · intro k j hj
    rw [Stitch.write_v, hcv]
    exact hb k j hj
  · rw [Stitch.write_v, hcv, hsb.v30, h.table]
  · intro r h4 hp
    rw [RegUpd.gpr_write_of_ne c .x _ h4, hck.gpr' (r := r) hp, hsb.gpr]
    exact h.keep r h4 hp
  · rw [RegUpd.gpr_write_of_ne c .x _ (by decide), hcp, show 2 + 3 * i + 3 = 2 + 3 * (i + 1) by omega_using []]
  · have e : 16 * (2 + 3 * i + 3) = 16 * (2 + 3 * (i + 1)) := by omega_using []
    rw [hsb.mem, h.mem, e] at hca
    exact hca.of (fun r hr' => RegUpd.gpr_write_of_ne c .x _ (by
      intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hx4, hsb.gpr, h.cnt,
      Offset.ofNat_sub_ofNat (by omega_using [hi] : 1 ≤ 10 - i)]
    simp only [Nat.sub_sub]

/-- The loop: ten iterations. -/
theorem rounds_ok (sve : Bool) {vs : Nat → CState} {R a : Nat} {W : Addr} {s₀ s : State}
    (hr : Readable W s₀) (h : TI vs R a W s₀ s 0) :
    WP isa (Tail.rounds sve) s fun u => TI vs R a W s₀ u 10 := by
  let Inv : Nat → State → Prop := fun n u => ∃ i, i < 10 ∧ n = 10 - i ∧ TI vs R a W s₀ u i
  have hstep : ∀ n u, Inv n u → WP isa (Tail.round sve) u (fun w =>
      (eval (.nonzero .x .x4) w = some false ∧ TI vs R a W s₀ w 10) ∨
      (eval (.nonzero .x .x4) w = some true ∧ ∃ m < n, Inv m w)) := by
    rintro n u ⟨i, hi, rfl, hu⟩
    refine (iter_ok sve hi hr hu).mono fun w hw => ?_
    have he : eval (.nonzero .x .x4) w = some (BitVec.ofNat 64 (10 - (i + 1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hw.cnt]
    by_cases hl : i + 1 = 10
    · exact .inl ⟨by rw [he, hl]; rfl, hl ▸ hw⟩
    · have hn0 : BitVec.ofNat 64 (10 - (i + 1)) ≠ 0 := by
        intro hz
        have hz' := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [] : 10 - (i + 1) < 2 ^ 64)] at hz'
        change 10 - (i + 1) = 0 at hz'
        omega_using [hi, hl, hz']
      exact .inr ⟨by rw [he]; simpa using hn0, 10 - (i + 1), by omega_using [hi], i + 1, by omega_using [hi, hl], rfl, hw⟩
  exact WP.loop (M := isa) Inv hstep 10 s ⟨0, by decide, rfl, h⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Tail

end

end

/-!
# ChaCha20-Poly1305 on AArch64, the rest when encrypting: the kernel

`Tail.kernel`, from the state after the chunks: the keystream of the four
blocks from the stream's counter in the buffer `x3[0, 256)`, and the 512
bytes before the rest absorbed into the accumulator in `x21`–`x23`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Tail

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.ChaCha20.AArch64.Neon4 (Holds LoadSame input input_same input_eq)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_mov wp_subImm)
open VG.Proof.Poly1305.AArch64.Radix64 (Keeps)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc)
open VG.Spec.ChaCha20 (innerBlock stateAt serialize block)
open VG.Spec.Poly1305 (bytesAt)
open VG.Proof.Poly1305 (absorbAll)

/-! ## The buffer zeroed -/

/-- `c[0, 16 j)` is zero, and `m` is `m₀` elsewhere. -/
def Zeroed (c : Addr) (j : Nat) (m₀ m : Mem) : Prop :=
  ∀ x, m x = if (x - c).toNat < 16 * j then 0 else m₀ x

theorem zeroStores_step (j : Nat) :
    (List.range (j + 1)).map (fun i => Instr.strq .v28 .x3 (16 * i)) =
      (List.range j).map (fun i => Instr.strq .v28 .x3 (16 * i)) ++
        ([.strq .v28 .x3 (16 * j)] : List Instr) := by
  simp [List.range_succ]

/-- The first `j` stores of zeros. -/
theorem zeroStores_ok {c : Addr} {j : Nat} (hj : j ≤ 16) {s : State} (hx3 : s.gpr .x3 = c)
    (hv : s.v .v28 = 0) (hw : ∀ a, a + 16 ≤ 256 → InRegions s.wr (c + BitVec.ofNat 64 a) 16) :
    WP isa (.block ((List.range j).map fun i => .strq .v28 .x3 (16 * i))) s fun s' =>
      Short.Same s s' ∧ Zeroed c j s.mem s'.mem := by
  induction j with
  | zero =>
    refine WP.block_nil (M := isa) ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun x => ?_⟩
    rw [ite_eq_right_iff.mpr fun h => absurd h (by omega_using [])]
  | succ j ih =>
    rw [zeroStores_step]
    refine WP.block_append (WP.mono (ih (by omega_using [hj])) fun s₁ ⟨g₁, z₁⟩ => ?_)
    have ho : InRegions s₁.wr (s₁.gpr .x3 + BitVec.ofNat 64 (16 * j)) 16 := by
      rw [g₁.wr, g₁.gpr, hx3]; exact hw (16 * j) (by omega_using [hj])
    refine WP.block_cons_iff.mpr ⟨_, Short.exec_strq (by omega_using [hj]) ho,
      WP.block_nil ⟨⟨g₁.gpr, g₁.v, g₁.rd, g₁.wr, g₁.sp⟩, fun x => ?_⟩⟩
    show (if (x - (s₁.gpr .x3 + BitVec.ofNat 64 (16 * j))).toNat < 16 then
      (s₁.v .v28).extractLsb' (8 * (x - (s₁.gpr .x3 + BitVec.ofNat 64 (16 * j))).toNat) 8
      else s₁.mem x) = _
    rw [g₁.gpr, hx3, g₁.v, hv]
    by_cases h : (x - (c + BitVec.ofNat 64 (16 * j))).toNat < 16
    · have h' := (Offset.lt_iff x c (by omega_using [hj])).mp h
      have h2 : (x - c).toNat < 16 * (j + 1) := by omega_using [h']
      simp only [h, h2, ite_true]
      ext i hi
      simp
    · have h' := mt (Offset.lt_iff x c (d := 16 * j) (n := 16) (by omega_using [hj])).mpr h
      simp only [h, ite_false]
      rw [z₁ x]
      by_cases h'' : (x - c).toNat < 16 * j
      · have h2 : (x - c).toNat < 16 * (j + 1) := by omega_using [h'']
        simp only [h'', h2, ite_true]
      · have h2 : ¬ (x - c).toNat < 16 * (j + 1) := by omega_using [h', h'']
        simp only [h'', h2, ite_false]

/-- The buffer zeroed. -/
theorem zero_ok {c : Addr} {s : State} (hx3 : s.gpr .x3 = c)
    (hw : ∀ a, a + 16 ≤ 256 → InRegions s.wr (c + BitVec.ofNat 64 a) 16) :
    WP isa (.block (([.vop (.logic .eor .v28 .v28 .v28)] : List Instr) ++
        (List.range 16).map (fun i => .strq .v28 .x3 (16 * i)))) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .v28 → s'.v r = s.v r) ∧ Zeroed c 16 s.mem s'.mem := by
  refine WP.block_cons_iff.mpr ⟨s.setV .v28 (s.v .v28 ^^^ s.v .v28), rfl, ?_⟩
  have hv : (s.setV .v28 (s.v .v28 ^^^ s.v .v28)).v .v28 = 0 := by
    rw [RegUpd.v_setV_self, BitVec.xor_self]; rfl
  refine WP.mono (zeroStores_ok (j := 16) (Nat.le_refl _) (by rw [RegUpd.gpr_setV]; exact hx3) hv
    (by rw [RegUpd.wr_setV]; exact hw)) fun s' ⟨g, z⟩ => ⟨by rw [g.gpr, RegUpd.gpr_setV],
      by rw [g.rd, RegUpd.rd_setV], by rw [g.wr, RegUpd.wr_setV], by rw [g.sp, RegUpd.sp_setV],
      fun r hr => by rw [g.v, RegUpd.v_setV_of_ne (s := s) _ hr], z⟩

theorem Zeroed.byte {c : Addr} {m₀ m : Mem} (h : Zeroed c 16 m₀ m) {k : Nat} (hk : k < 256) :
    m (c + BitVec.ofNat 64 k) = 0 := by
  rw [h, Mem.sub_ofNat_toNat c (by omega_using [hk])]
  simp only [show k < 16 * 16 by omega_using [hk], ite_true]

theorem Zeroed.frame {c : Addr} {m₀ m : Mem} (h : Zeroed c 16 m₀ m) :
    Frame [⟨c, 256⟩] m₀ m := by
  intro x hx
  have hx' := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hx'
  rw [h x, ite_eq_right_iff.mpr fun h' => absurd (by omega_using [h']) hx']

/-! ## The kernel -/

theorem block_eq (S : CState) (k : Fin 16) :
    (block S)[k] = (Nat.repeat innerBlock 10 S)[k] + S[k] := by
  simp only [block, Fin.getElem_fin, Vector.getElem_zipWith]

theorem kernel_ok (sve : Bool) {R a : Nat} {W : Addr} {s : State}
    (hx20 : s.gpr .x20 = W)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (hw : ∀ d, d + 16 ≤ 256 → InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16)
    (hst : (⟨s.gpr .x0, 64⟩ : Region).Disjoint ⟨s.gpr .x3, 256⟩)
    (hr : Readable W s) (ha : Acc R a s) :
    WP isa (Tail.kernel sve) s fun u =>
      (∀ k < 256, u.mem (s.gpr .x3 + BitVec.ofNat 64 k) =
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x3, 256⟩] s.mem u.mem ∧
      Poly.hval u % Spec.Poly1305.P = absorbAll R a (bytesAt s.mem W 512) % Spec.Poly1305.P ∧
      (u.gpr .x23).toNat ≤ 4 ∧
      (∀ r, r ∉ [Reg.x1, .x4] → r ∉ Poly.regs → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  unfold Tail.kernel
  -- The four blocks' states.
  refine WP.seq ((VG.Proof.ChaCha20.AArch64.Neon4.setup_ok s hin).mono
    fun s₂ ⟨h₂, l₂, t₂⟩ => ?_)
  -- Two blocks, and the count.
  have m₂ : s₂.mem = s.mem := l₂.mem
  have ha₂ : Acc R (absorbAll R a (bytesAt s₂.mem W (16 * 0))) s₂ := by
    have e : bytesAt s₂.mem W (16 * 0) = [] := rfl
    rw [e, Poly1305.absorbAll_nil]
    refine ha.of (fun r hr => ?_) m₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact l₂.gpr _ (by decide)
  have hp₂ : s₂.gpr .x20 = W + BitVec.ofNat 64 (16 * 0) := by
    rw [l₂.gpr _ (by decide), hx20, Nat.mul_zero, BitVec.add_zero]
  have hr₂ : Readable W s₂ := hr.of l₂.rd l₂.wr (l₂.gpr _ (by decide))
  have hvs : ∀ i ∈ (List.replicate 2 Poly.block).flatten, vdstOf i = none := by decide +kernel
  apply WP.seq
  rw [Tail.start, show Poly.block ++ Poly.block = (List.replicate 2 Poly.block).flatten by
    simp only [List.replicate, List.flatten_cons, List.flatten_nil, List.append_nil]]
  apply WP.block_append
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hvs
    (absorbN_ok 2 (n := 0) (by decide) ha₂ hp₂ hr₂)).mono
    fun s₃ ⟨⟨a₃, p₃, k₃⟩, v₃, sp₃, rd₃, wr₃⟩ => ?_
  apply WP.block_cons_iff.mpr
  refine ⟨s₃.write .x .x4 ((10 : BitVec 16).setWidth 64), ?_, WP.block_nil ?_⟩
  · simp only [exec, Size.bits, Nat.mul_zero, BitVec.shiftLeft_zero, show 0 < 64 from by decide,
      ite_true]
  -- The loop, from its invariant.
  let s₄ := s₃.write .x .x4 ((10 : BitVec 16).setWidth 64)
  have m₃ : s₃.mem = s.mem := k₃.2.1.trans m₂
  let vs : Nat → CState := fun j => ctr (stateAt s.mem (s.gpr .x0)) j
  have h₄ : TI vs R a W s₄ s₄ 0 := by
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, ?_, ?_, ?_⟩
    · intro k j hj
      rw [Stitch.write_v, v₃]
      exact h₂ k j hj
    · rw [Stitch.write_v, v₃, t₂]
    · rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), p₃]
    · have e : bytesAt s₄.mem W (16 * (2 + 3 * 0)) = bytesAt s₂.mem W (16 * (0 + 2)) := by
        show bytesAt s₃.mem W _ = _
        rw [k₃.2.1]
      rw [e]
      exact a₃.of (fun r hr => RegUpd.gpr_write_of_ne s₃ .x _ (by
        intro he; rw [he] at hr; exact absurd hr (by decide))) rfl
    · rw [RegUpd.gpr_write_self]; rfl
  have hr₄ : Readable W s₄ := hr₂.of (by show s₃.rd = _; rw [rd₃]) (by show s₃.wr = _; rw [wr₃])
    (by rw [RegUpd.gpr_write_of_ne s₃ .x _ (by decide), k₃.gpr' (r := .x0)])
  refine WP.seq ((rounds_ok sve hr₄ h₄).mono fun s₅ h₅ => ?_)
  have x3₅ : s₅.gpr .x3 = s.gpr .x3 := by
    rw [h₅.keep _ (by decide) (by decide), RegUpd.gpr_write_of_ne s₃ .x _ (by decide),
      k₃.gpr' (r := .x3), l₂.gpr _ (by decide)]
  have wr₅ : s₅.wr = s.wr := by rw [h₅.wr]; show s₃.wr = _; rw [wr₃, l₂.wr]
  have rd₅ : s₅.rd = s.rd := by rw [h₅.rd]; show s₃.rd = _; rw [rd₃, l₂.rd]
  have sp₅ : s₅.sp = s.sp := by rw [h₅.sp]; show s₃.sp = _; rw [sp₃, l₂.sp]
  have mm₅ : s₅.mem = s.mem := by rw [h₅.mem]; exact m₃
  -- The buffer zeroed, then the keystream XORed into it.
  rw [Tail.finish, List.append_assoc]
  apply WP.block_append
  refine (zero_ok x3₅ (by rw [wr₅]; exact hw)).mono fun s₆ ⟨g₆, rd₆, wr₆, sp₆, v₆, z₆⟩ => ?_
  let s₇ := s₆.write .x .x1 (s₆.gpr .x3)
  have hx₇ : exec (VG.Impl.ChaCha20.AArch64.Xor.mov .x1 .x3) s₆ = some s₇ := by
    show exec (.addImm .x .x1 .x3 0) s₆ = some s₇
    simpa only [State.read, BitVec.setWidth_eq, BitVec.add_zero] using
      exec_addImm_x (s := s₆) (d := .x1) (n := .x3) (imm := 0) (by decide)
  refine WP.block_cons_iff.mpr ⟨s₇, hx₇, ?_⟩
  show WP isa (.block VG.Impl.ChaCha20.AArch64.Neon4.finish) s₇ _
  have u₇ := VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 s₆ .x1 (s₆.gpr .x3)
  have x1₇ : s₇.gpr .x1 = s.gpr .x3 := by rw [u₇.gpr, g₆, x3₅]
  have x0₇ : s₇.gpr .x0 = s.gpr .x0 := by
    rw [u₇.other _ (by decide), g₆, h₅.keep _ (by decide) (by decide),
      RegUpd.gpr_write_of_ne s₃ .x _ (by decide), k₃.gpr' (r := .x0), l₂.gpr _ (by decide)]
  have f₆ : Frame [⟨s.gpr .x3, 256⟩] s.mem s₇.mem := by
    rw [u₇.mem, ← mm₅]; exact z₆.frame
  have st₇ : stateAt s₇.mem (s.gpr .x0) = stateAt s.mem (s.gpr .x0) :=
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hst
  have hv₇ : Holds (fun j => Nat.repeat innerBlock 10 (vs j)) s₇ := by
    intro k j hj
    rw [show s₇.v = s₆.v from rfl, v₆ _ (fun e => absurd e
      ((show ∀ k : Fin 16, VG.Impl.ChaCha20.AArch64.Neon4.vreg k ≠ .v28 by decide) k))]
    exact h₅.vec k j hj
  have hin₇ : ∀ k : Fin 16, InRegions (s₇.rd ++ s₇.wr) (s₇.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [u₇.rd, u₇.wr, rd₆, wr₆, rd₅, wr₅, x0₇]; exact hin k
  unfold VG.Impl.ChaCha20.AArch64.Neon4.finish
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Neon4.feed_ok hv₇ hin₇).mono
    fun s₈ ⟨h₈, l₈⟩ => ?_)
  have hc₈ : Holds (fun j => block (vs j)) s₈ := by
    intro k j hj
    rw [h₈ k j hj, input_eq, x0₇, st₇, block_eq]
  have ho : ∀ r j : Fin 4, InRegions s₈.wr
      (s₈.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j
    rw [l₈.wr, l₈.gpr _ (by decide), u₇.wr, wr₆, wr₅, x1₇]
    exact hw _ (by omega_using [])
  refine (VG.Proof.ChaCha20.AArch64.Neon4.finishBlocks_ok hc₈ ho).mono
    fun s₉ ⟨d₉, f₉, k₉⟩ => ?_
  have x1₈ : s₈.gpr .x1 = s.gpr .x3 := by rw [l₈.gpr _ (by decide), x1₇]
  have g₉ (r : Reg) (h4 : r ≠ .x4) : s₉.gpr r = s₇.gpr r := by rw [k₉.gpr, l₈.gpr _ h4]
  have g₅ (r : Reg) (h4 : r ≠ .x4) (hp : r ∉ Poly.regs) : s₅.gpr r = s₃.gpr r := by
    rw [h₅.keep _ h4 hp, RegUpd.gpr_write_of_ne s₃ .x _ h4]
  have acc₅ := h₅.acc
  rw [show 16 * (2 + 3 * 10) = 512 from rfl, show s₄.mem = s.mem from m₃] at acc₅
  have e21 : ∀ r ∈ [Reg.x21, .x22, .x23], s₉.gpr r = s₅.gpr r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [g₉ _ (by decide), u₇.other _ (by decide), g₆]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun r hr hp => ?_, ?_, ?_, ?_⟩
  · have e := d₉ k hk
    have z : ∀ x : BitVec 8, (0 : BitVec 8) ^^^ x = x := fun x => by ext i; simp
    rw [x1₈, show s₈.mem = s₇.mem from l₈.mem, u₇.mem, z₆.byte hk, z] at e
    exact e
  · rw [← x1₈]
    have f₈ : Frame [⟨s.gpr .x3, 256⟩] s.mem s₈.mem := by rw [l₈.mem]; exact f₆
    rw [x1₈] at f₉ ⊢
    exact f₈.trans f₉
  · rw [show Poly.hval s₉ = Poly.hval s₅ by
      simp only [Poly.hval, e21 .x21 (by simp), e21 .x22 (by simp), e21 .x23 (by simp)]]
    exact acc₅.h
  · rw [e21 .x23 (by simp)]; exact acc₅.h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h4⟩ := hr
    rw [g₉ _ h4, u₇.other _ h1, g₆, g₅ _ h4 hp, k₃.gpr' (r := r) hp, l₂.gpr _ h4]
  · rw [k₉.rd, l₈.rd, u₇.rd, rd₆, rd₅]
  · rw [k₉.wr, l₈.wr, u₇.wr, wr₆, wr₅]
  · rw [k₉.sp, l₈.sp, show s₇.sp = s₆.sp from rfl, sp₆, sp₅]

end VG.Proof.ChaCha20Poly1305.AArch64.Tail

end

end

/-! ### `ChaCha20Poly1305.AArch64.Tail.Rest`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 on AArch64, the rest when encrypting

`Tail.rest`, from what `cryptStitched` leaves after `T ≥ 1` chunks with a rest
of `L - 512 T > 0` bytes (`Crypted`): the last chunk absorbed while the
keystream of the next four blocks is computed (`kernel_ok`), and the first
`m = min(L - 512 T, 256)` bytes of the rest encrypted with it: the data's first
`512 T + m` bytes encrypted and its first `512 T` absorbed (`Sealed`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.Tail

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Proof.ChaCha20.AArch64.Xor (Upd wp_mov wp_movz wp_lsr wp_sub wp_addImm wp_ldr32
  wp_addImm32 wp_str32)
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Acc)
open VG.Spec.ChaCha20 (stateAt serialize block keystream)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Proof.Poly1305 (absorbAll)

variable {e : Bool}

/-- The clamped key's value. -/
abbrev Rk (key : List Byte) : Nat := Spec.Poly1305.clamp (Spec.Poly1305.leNum (key.take 16))

/-- `load`: our caller's `x20` in `x8`, the rest in `x7`, the last chunk in
`x20`, and the accumulator and the clamped key as before the chunks. -/
theorem load_ok {s₀ s w₀ u : State} (hp : APre true s₀) {key msg : List Byte} {o T : Nat}
    (hc : Crypted true o s₀ s w₀ key msg T u) (hx21 : u.gpr .x21 = cx s₀) :
    WP isa (.block Tail.load) u fun s₂ =>
      Acc (Rk key) (Spec.Poly1305.accumulate (Rk key)
        (msg ++ bytesAt u.mem (dp s₀) ((o + 512 * (T - 1))))) s₂ ∧
      s₂.gpr .x20 = u.gpr .x22 ∧ s₂.gpr .x8 = u.gpr .x20 ∧ s₂.gpr .x7 = u.gpr .x1 ∧
      s₂.mem = memIn u.mem (cx s₀) (u.gpr .x27) (u.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x7, .x8, .x20, .x21, .x22, .x23, .x24, .x25] → s₂.gpr r = u.gpr r) ∧
      s₂.v = u.v ∧ s₂.sp = u.sp ∧ s₂.rd = u.rd ∧ s₂.wr = u.wr := by
  unfold Tail.load
  obtain hv : ∀ i ∈ [mov .x8 .x20, mov .x20 .x22, mov .x7 .x1], vdstOf i = none := by decide
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv (Q := fun s₁ =>
      s₁.gpr .x8 = u.gpr .x20 ∧ s₁.gpr .x20 = u.gpr .x22 ∧ s₁.gpr .x7 = u.gpr .x1 ∧
      (∀ r, r ≠ .x8 → r ≠ .x20 → r ≠ .x7 → s₁.gpr r = u.gpr r) ∧ s₁.mem = u.mem)
    (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
        by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
        fun r h8 h20 h7 => by rw [u₃.other _ h7, u₂.other _ h20, u₁.other _ h8],
        by rw [u₃.mem, u₂.mem, u₁.mem]⟩)).mono
    fun s₁ ⟨⟨x8₁, x20₁, x7₁, g₁, m₁⟩, v₁, sp₁, rd₁, wr₁⟩ => ?_)
  refine (polyIn_ok hp (by rw [g₁ _ (by decide) (by decide) (by decide), hx21])
    (by rw [rd₁, hc.inv.rd]) (by rw [wr₁, hc.inv.wr])).mono
    fun s₂ ⟨⟨a21, a22, a23, m₂, g₂, _, _⟩, v₂, sp₂, rd₂, wr₂⟩ => ?_
  obtain hr : Repr s₁.mem (off (cx s₀) 448) key (msg ++ bytesAt u.mem (dp s₀) ((o + 512 * (T - 1)))) := by
    have e := hc.mac
    simp only [ite_true, pre] at e
    rw [m₁]; exact e
  obtain x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by
    rw [g₂ _ (by decide), g₁ _ (by decide) (by decide) (by decide), hc.x0]
  refine ⟨acc_in hr x0₂ a21 a22 a23 m₂, by rw [g₂ _ (by decide), x20₁], by rw [g₂ _ (by decide), x8₁],
    by rw [g₂ _ (by decide), x7₁], by rw [m₂, m₁, g₁ _ (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide)], fun r hr' => ?_, by rw [v₂, v₁], by rw [sp₂, sp₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
  obtain ⟨h7, h8, h20, h21, h22, h23, h24, h25⟩ := hr'
  rw [g₂ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
    ⟨h21, h22, h23, h24, h25⟩), g₁ r h8 h20 h7]

/-- `out`: the accumulator stored, `x22` set to the rest, our caller's `x20`
restored, and the counter advanced past the four blocks. -/
theorem out_ok {s₀ s : State} (hp : APre e s₀) (hx0 : s.gpr .x0 = off (cx s₀) 64)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block Tail.out) s fun u =>
      ((s.gpr .x23).toNat ≤ 4 → Spec.Poly1305.leNum (bytesAt u.mem (off (cx s₀) 448) 24) =
        hacc s % Spec.Poly1305.P) ∧
      Frame [sub s₀ 448 24, sub s₀ 112 4] s.mem u.mem ∧
      stateAt u.mem (off (cx s₀) 64) = ctr (stateAt s.mem (off (cx s₀) 64)) 4 ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 40) 64 ∧
      u.gpr .x22 = s.gpr .x7 ∧ u.gpr .x20 = s.gpr .x8 ∧ u.gpr .x23 = s.gpr .x2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x20, .x21, .x22, .x23, .x27,
        .x28] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.v = s.v := by
  unfold Tail.out
  rw [List.append_assoc]
  refine WP.block_append ((polyOut_ok hp false hx0 hrd hwr).mono
    fun s₁ ⟨⟨hv₁, m₁, x21₁, x27₁, x28₁, x22₁, x23₁, g₁, rd₁, wr₁⟩, v₁, sp₁, _, _⟩ => ?_)
  obtain hv : ∀ i ∈ [mov .x22 .x7, mov .x20 .x8], vdstOf i = none := by decide
  refine WP.block_append ((VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors hv (Q := fun s₂ =>
      s₂.gpr .x22 = s₁.gpr .x7 ∧ s₂.gpr .x20 = s₁.gpr .x8 ∧
      (∀ r, r ≠ .x22 → r ≠ .x20 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem)
    (wp_mov fun t₁ u₁ => wp_mov fun t₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h20 => by rw [u₂.other _ h20, u₁.other _ h22], by rw [u₂.mem, u₁.mem]⟩)).mono
    fun s₂ ⟨⟨x22₂, x20₂, g₂, m₂⟩, v₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by
    rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), hx0]
  obtain p48 : s₂.gpr .x0 + BitVec.ofNat 64 48 = off (cx s₀) 112 := by rw [x0₂]; exact off_off _ 64 48
  obtain hi : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [p48, rd₂, wr₂, rd₁, wr₁, hrd, hwr]; exact hp.in_ctx' (by lit_omega)
  obtain ho : InRegions s₂.wr (s₂.gpr .x0 + BitVec.ofNat 64 48) 4 := by
    rw [p48, wr₂, wr₁, hwr]; exact hp.in_ctx (by lit_omega)
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.counter_ok s₂ (by decide) false hi ho).mono
    fun s₃ ⟨m₃, g₃, rd₃, wr₃, v₃, sp₃⟩ => ?_
  simp only [Bool.false_eq_true, ite_false] at m₃
  obtain fs : Frame [sub s₀ 448 24] s.mem s₂.mem := by rw [m₂, m₁]; exact storeHm_frame _ _ _ _ _
  obtain fc : Frame [sub s₀ 112 4] s₂.mem s₃.mem := by
    rw [m₃, p48]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (contains_sub s₀ (by decide) (by decide)
      (by lit_omega))
  have hg (r : Reg) (h : r ≠ .x4 ∧ r ≠ .x20 ∧ r ≠ .x22) :
      s₃.gpr r = s₁.gpr r := by
    obtain ⟨h4, h20, h22⟩ := h
    rw [g₃ r h4, g₂ r h22 h20]
  refine ⟨fun h23 => ?_, ?_, ?_, by rw [hg _ (by decide), x21₁],
    by rw [hg _ (by decide), x27₁],
    by rw [hg _ (by decide), x28₁],
    by rw [g₃ _ (by decide), x22₂, g₁ _ (by decide)], by rw [g₃ _ (by decide), x20₂, g₁ _ (by decide)],
    by rw [hg _ (by decide), x23₁]; rfl, fun r hr => ?_,
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], by rw [sp₃, sp₂, sp₁], by rw [v₃, v₂, v₁]⟩
  · rw [bytesAt_frame fc (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) (by lit_omega),
      m₂, m₁, Poly1305.AArch64.storeHm_acc]
    exact hv₁ h23
  · intro x hx
    rw [fc x fun r hr => hx r (by simp only [List.mem_singleton] at hr; simp [hr]),
      fs x fun r hr => hx r (by simp only [List.mem_singleton] at hr; simp [hr])]
  · rw [m₃, x0₂, VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_ctr,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame fs (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h20, h21, h22, h23, h27, h28⟩ := hr
    rw [hg r ⟨h4, h20, h22⟩, g₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
      ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h21, h22, h23, h27, h28⟩)]

theorem shr8_ofNat {r : Nat} (h : r < 2 ^ 64) : BitVec.ofNat 64 r >>> 8 = BitVec.ofNat 64 (r / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, VG.Proof.ChaCha20.AArch64.toNat_ofNat_lt h,
    VG.Proof.ChaCha20.AArch64.toNat_ofNat_lt (by omega_using [h]), Nat.shiftRight_eq_div_pow]

/-- `take`: `x23 = min(x2, 256)`. -/
theorem take_ok {s : State} {r : Nat} (hr : r < 2 ^ 64) (hx2 : s.gpr .x2 = BitVec.ofNat 64 r) :
    WP isa Tail.take s fun u =>
      u.gpr .x23 = BitVec.ofNat 64 (min r 256) ∧
      (∀ q, q ≠ .x9 → q ≠ .x23 → u.gpr q = s.gpr q) ∧ u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  unfold Tail.take
  refine WP.seq (wp_lsr (by decide) fun s₁ u₁ => WP.block_nil ?_)
  obtain x9₁ : s₁.gpr .x9 = BitVec.ofNat 64 (r / 256) := by rw [u₁.gpr, hx2, shr8_ofNat hr]
  refine WP.ite (decide (r / 256 = 0)) (by
      rw [show isa.eval (.zero .x .x9) s₁ = some (s₁.gpr .x9 == 0) from
        VG.Proof.ChaCha20.AArch64.Xor.eval_zero s₁ .x9, x9₁,
        VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega_using [hr])]) (fun h => ?_) (fun h => ?_)
  · have h' : r < 256 := by have := of_decide_eq_true h; omega_using [this]
    refine wp_mov fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u₁.other _ (by decide), hx2,
      Nat.min_eq_left (by omega_using [h'])], fun q h9 h23 => by rw [u₂.other _ h23, u₁.other _ h9],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  · have h' : 256 ≤ r := by have := of_decide_eq_false h; omega_using [this]
    refine wp_movz fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, Nat.min_eq_right h']; rfl,
      fun q h9 h23 => by rw [u₂.other _ h23, u₁.other _ h9],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩

theorem wp_add {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n + s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

/-- `args`: the stream's arguments after the `m` bytes XORed, and `x23` the
rest's length again. -/
theorem args_ok {s₀ s : State} {D : Addr} {m r : Nat} (hm : m ≤ r)
    (hx21 : s.gpr .x21 = cx s₀) (hx22 : s.gpr .x22 = D) (hx23 : s.gpr .x23 = BitVec.ofNat 64 m)
    (hx2 : s.gpr .x2 = BitVec.ofNat 64 r) :
    WP isa (.block Tail.args) s fun u =>
      u.gpr .x0 = off (cx s₀) 64 ∧ u.gpr .x1 = D + BitVec.ofNat 64 m ∧
      u.gpr .x2 = BitVec.ofNat 64 (r - m) ∧ u.gpr .x3 = off (cx s₀) 128 ∧
      u.gpr .x23 = BitVec.ofNat 64 r ∧
      (∀ q, q ∉ [Reg.x0, .x1, .x2, .x3, .x23] → u.gpr q = s.gpr q) ∧
      u.mem = s.mem ∧ u.rd = s.rd ∧ u.wr = s.wr := by
  unfold Tail.args
  refine wp_add fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_add fun s₃ u₃ => wp_addImm (by decide)
    fun s₄ u₄ => wp_addImm (by decide) fun s₅ u₅ => WP.block_nil ?_
  obtain x2₂ : s₂.gpr .x2 = BitVec.ofNat 64 (r - m) := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hx2, hx23,
      VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hm]
  refine ⟨by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hx21],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hx22, hx23],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x2₂],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hx21],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, x2₂,
      u₂.other _ (by decide), u₁.other _ (by decide), hx23, ← BitVec.ofNat_add,
      Nat.sub_add_cancel hm], fun q hq => ?_,
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  obtain ⟨h0, h1, h2, h3, h23⟩ := hq
  rw [u₅.other _ h3, u₄.other _ h0, u₃.other _ h23, u₂.other _ h2, u₁.other _ h1]

/-- A byte of the data outside `[a, a + n)` is outside that region. -/
theorem not_in {D : Addr} {a n k : Nat} (h : k < a ∨ a + n ≤ k) (hk : k < 2 ^ 64) (han : a + n ≤ 2 ^ 64) :
    ¬ (⟨D + BitVec.ofNat 64 a, n⟩ : Region).Contains (D + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  intro hc
  have := (Offset.lt_iff (D + BitVec.ofNat 64 k) D han).mp (by omega_using [hc])
  rw [Mem.sub_ofNat_toNat D hk] at this
  omega_using [h, this]

/-- `Tail.rest`, after `T ≥ 1` chunks with a rest. -/
theorem rest_ok (sve : Bool) {s₀ s w₀ u : State} (hp : APre true s₀) {key msg : List Byte} {o T : Nat}
    (hc : Crypted true o s₀ s w₀ key msg T u) (ho : o % 64 = 0) (hT : 1 ≤ T) (hr : (o + 512 * T) < L s₀) :
    WP isa (Tail.rest sve) u fun w => ∃ P, Sealed s₀ s w₀ key msg P ((o + 512 * T)) w := by
  obtain hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have wd := hp.wrap_d
  have pre_eq : pre o true T = (o + 512 * (T - 1)) := rfl
  obtain oo : ∀ a b, off (cx s₀) a + BitVec.ofNat 64 b = off (cx s₀) (a + b) := fun a b => off_off _ a b
  refine (WP.withSp (WP.preservedV (c := Tail.rest sve) (Q := fun w => ∃ P,
      (∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64) → w.sp = u.sp →
        Sealed s₀ s w₀ key msg P ((o + 512 * T)) w) ?_ (by cases sve <;> lit_decide))).mono
    fun w ⟨⟨⟨P, hw⟩, vw⟩, spw⟩ => ⟨P, hw vw spw⟩
  unfold Tail.rest
  refine WP.seq ((load_ok hp hc hc.inv.x21).mono
    fun s₂ ⟨a₂, x20₂, x8₂, x7₂, m₂, g₂, v₂, sp₂, rd₂, wr₂⟩ => ?_)
  -- The kernel, on the last chunk.
  let W := dp s₀ + BitVec.ofNat 64 ((o + 512 * (T - 1)))
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, hc.inv.rd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, hc.inv.wr]
  obtain x0₂ : s₂.gpr .x0 = off (cx s₀) 64 := by rw [g₂ _ (by decide), hc.x0]
  obtain x3₂ : s₂.gpr .x3 = off (cx s₀) 128 := by rw [g₂ _ (by decide), hc.x3]
  obtain hin : ∀ k : Fin 16, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [x0₂, oo, rd₂', wr₂']; exact hp.in_ctx' (by omega_arith)
  obtain hw : ∀ d, d + 16 ≤ 256 → InRegions s₂.wr (s₂.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    intro d hd; rw [x3₂, oo, wr₂']; exact hp.in_ctx (by omega_arith)
  obtain hst : (⟨s₂.gpr .x0, 64⟩ : Region).Disjoint ⟨s₂.gpr .x3, 256⟩ := by
    rw [x0₂, x3₂]; exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  obtain hrd : Readable W s₂ := by
    refine ⟨fun d hd => ?_, ?_, ?_⟩
    · rw [rd₂', wr₂', VG.Proof.ChaCha20.AArch64.Xor.add_ofNat]
      exact ⟨dR s₀, List.mem_append_right _ hp.d_wr, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    · rw [rd₂', wr₂', x0₂, oo]; exact hp.in_ctx' (by lit_omega)
    · rw [rd₂', wr₂', x0₂, oo]; exact hp.in_ctx' (by lit_omega)
  obtain x20₂' : s₂.gpr .x20 = W := by rw [x20₂, hc.x22, pre_eq]
  refine WP.seq ((kernel_ok sve x20₂' hin hw hst hrd a₂).mono
    fun s₃ ⟨ks₃, f₃, hv₃, h2₃, g₃, rd₃, wr₃, sp₃⟩ => ?_)
  have g₃' (r : Reg) (h : r ≠ .x1 ∧ r ≠ .x4 ∧ r ∉ Poly.regs) :
      s₃.gpr r = s₂.gpr r :=
    have ⟨h1, h4, hp'⟩ := h
    g₃ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h4⟩) hp'
  obtain x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by rw [g₃' _ (by decide), x0₂]
  rw [x3₂] at ks₃ f₃
  -- The accumulator stored.
  refine WP.seq ((out_ok hp x0₃ (by rw [rd₃, rd₂']) (by rw [wr₃, wr₂'])).mono
    fun s₄ ⟨acc₄, f₄, st₄, x21₄, x27₄, x28₄, x22₄, x20₄, x23₄, g₄, rd₄, wr₄, sp₄, v₄⟩ => ?_)
  obtain x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (L s₀ - (o + 512 * T)) := by
    rw [g₄ _ (by decide), g₃' _ (by decide), g₂ _ (by decide), hc.x2]
  -- `m` bytes of the rest.
  refine WP.seq ((take_ok (r := L s₀ - (o + 512 * T)) (by omega_arith) x2₄).mono
    fun s₅ ⟨x23₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  obtain x21₅ : s₅.gpr .x21 = cx s₀ := by rw [g₅ _ (by decide) (by decide), x21₄]
  obtain x22₅ : s₅.gpr .x22 = dp s₀ + BitVec.ofNat 64 ((o + 512 * T)) := by
    rw [g₅ _ (by decide) (by decide), x22₄, g₃' _ (by decide), x7₂, hc.x1]
  obtain rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄, rd₃, rd₂']
  obtain wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄, wr₃, wr₂']
  refine WP.seq ((Short.xorKsAt_ok hp (o := (o + 512 * T)) (n := min (L s₀ - (o + 512 * T)) 256) (by omega_arith)
    (by omega_arith) x21₅ x22₅ x23₅ rd₅' wr₅').mono fun s₆ ⟨k₆, d₆, f₆, g₆⟩ => ?_)
  -- The stream's arguments.
  have g₆' (r : Reg) (h : r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x15) :
      s₆.gpr r = s₅.gpr r :=
    have ⟨h9, h10, h11, h12, h13, h15⟩ := h
    g₆ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h9, h10, h11, h12, h13, h15⟩)
  refine (args_ok (s₀ := s₀) (D := dp s₀ + BitVec.ofNat 64 ((o + 512 * T)))
    (m := min (L s₀ - (o + 512 * T)) 256) (r := L s₀ - (o + 512 * T)) (Nat.min_le_left _ _)
    (by rw [g₆' _ (by decide), x21₅])
    (by rw [g₆' _ (by decide), x22₅])
    (by rw [g₆' _ (by decide), x23₅])
    (by rw [g₆' _ (by decide),
      g₅ _ (by decide) (by decide), x2₄])).mono
    fun s₇ ⟨x0₇, x1₇, x2₇, x3₇, x23₇, g₇, m₇, rd₇, wr₇⟩ =>
      ⟨(o + 512 * T) + min (L s₀ - (o + 512 * T)) 256, fun vw spw => ?_⟩
  -- The frames.
  obtain hM : (o + 512 * T) + min (L s₀ - (o + 512 * T)) 256 ≤ L s₀ := by omega_arith
  obtain dsub : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 ((o + 512 * T)), min (L s₀ - (o + 512 * T)) 256⟩ (dR s₀) :=
    Offset.sub_base _ hM
  let tgt := [sub s₀ 64 408, sub s₀ 32 16, dR s₀]
  have c64 (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) : ∃ r' ∈ tgt, Region.Sub (sub s₀ k n) r' :=
    ⟨sub s₀ 64 408, List.mem_cons_self, sub_sub s₀ h₁ (by omega_arith) (by lit_omega)⟩
  obtain F₁ : Frame tgt u.mem s₂.mem := by
    rw [m₂]
    refine (memIn_frame (s₀ := s₀) _ _ _).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c64 288 16 (by decide) (by decide)
    · exact ⟨sub s₀ 32 16, by simp [tgt], fun _ h => h⟩
  obtain F₂ : Frame tgt s₂.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact c64 128 256 (by decide) (by decide)
  obtain F₃ : Frame tgt s₃.mem s₄.mem := f₄.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact c64 448 24 (by decide) (by decide)
    · exact c64 112 4 (by decide) (by decide)
  obtain F₄ : Frame tgt s₅.mem s₇.mem := by
    rw [m₇]
    exact f₆.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp [tgt], dsub⟩
  obtain F : Frame tgt u.mem s₇.mem := F₁.trans (F₂.trans (F₃.trans (by rw [m₅] at F₄; exact F₄)))
  -- The context frames keep the data.
  obtain dctx : ∀ k < L s₀, s₅.mem (dp s₀ + BitVec.ofNat 64 k) = u.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    obtain e₁ := data_frame (s₀ := s₀) f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk
    obtain e₂ := data_frame (s₀ := s₀) f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega)) hk
    obtain e₃ := data_frame (s₀ := s₀) (memIn_frame (s₀ := s₀) u.mem (u.gpr .x27) (u.gpr .x28))
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) hk
    rw [m₅, e₁, e₂, m₂, e₃]
  obtain dout : ∀ k < L s₀, (k < (o + 512 * T) ∨ (o + 512 * T) + min (L s₀ - (o + 512 * T)) 256 ≤ k) →
      s₇.mem (dp s₀ + BitVec.ofNat 64 k) = u.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk hout
    rw [m₇, f₆ _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact not_in hout (by omega_arith) (by omega_arith),
      dctx k hk]
  -- Registers.
  have g₇' (r : Reg) (h : r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x23) :
      s₇.gpr r = s₆.gpr r :=
    have ⟨h0, h1, h2, h3, h23⟩ := h
    g₇ r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h0, h1, h2, h3, h23⟩)
  have to₄ (r : Reg) (h : r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x23 ∧ r ≠ .x9 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧
      r ≠ .x15) :
      s₇.gpr r = s₄.gpr r := by
    obtain ⟨h0, h1, h2, h3, h23, h9, h10, h11, h12, h13, h15⟩ := h
    rw [g₇' r ⟨h0, h1, h2, h3, h23⟩, g₆' r ⟨h9, h10, h11, h12, h13, h15⟩, g₅ r h9 h23]
  have r32 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₃.mem.readW (off (cx s₀) d) 64 = s₂.mem.readW (off (cx s₀) d) 64 :=
    f₃.readW (r := sub s₀ d 8) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by omega_arith) (by omega_arith) (by lit_omega)) (by decide)
  obtain un₇ : ∀ r ∈ untouched, s₇.gpr r = s₀.gpr r := by
    intro r hr
    obtain hu := hc.inv.un r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [to₄ _ (by decide), g₄ _ (by decide), g₃' _ (by decide),
        g₂ _ (by decide), hu]
    · rw [to₄ _ (by decide), x20₄, g₃' _ (by decide), x8₂, hu]
    · rw [to₄ _ (by decide), g₄ _ (by decide), g₃' _ (by decide),
        g₂ _ (by decide), hu]
    · rw [to₄ _ (by decide), x27₄, r32 32 (.inl rfl), m₂, memIn_800, hu]
    · rw [to₄ _ (by decide), x28₄, r32 40 (.inr rfl), m₂, memIn_808, hu]
  obtain x21₇ : s₇.gpr .x21 = cx s₀ := by
    rw [g₇' _ (by decide),
      g₆' _ (by decide), x21₅]
  obtain x22₇ : s₇.gpr .x22 = dp s₀ + BitVec.ofNat 64 ((o + 512 * T)) := by
    rw [g₇' _ (by decide),
      g₆' _ (by decide), x22₅]
  obtain rd₇' : s₇.rd = s₀.rd := by rw [rd₇, k₆.rd, rd₅']
  obtain wr₇' : s₇.wr = s₀.wr := by rw [wr₇, k₆.wr, wr₅']
  -- The counter.
  obtain st₂ : stateAt s₂.mem (off (cx s₀) 64) = stateAt u.mem (off (cx s₀) 64) := by
    rw [m₂]
    exact VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame (memIn_frame (s₀ := s₀) _ _ _) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  obtain st₃ : stateAt s₃.mem (off (cx s₀) 64) = stateAt s₂.mem (off (cx s₀) 64) :=
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame f₃ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  obtain st₇ : stateAt s₇.mem (off (cx s₀) 64) = stateAt s₄.mem (off (cx s₀) 64) := by
    rw [m₇, ← m₅]
    exact VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right dsub
  -- The data before the rest is kept.
  obtain pfx : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' → (∀ r ∈ rs, (dR s₀).Disjoint r) →
      bytesAt m' (dp s₀) ((o + 512 * T)) = bytesAt m (dp s₀) ((o + 512 * T)) :=
    fun hf hd => prefix_frame hf hd (by omega_arith)
  obtain b₅ : bytesAt s₅.mem (dp s₀) ((o + 512 * T)) = bytesAt s₂.mem (dp s₀) ((o + 512 * T)) := by
    rw [m₅, pfx f₄ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)),
      pfx f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact data_ctx hp (by lit_omega))]
  obtain b₇ : bytesAt s₇.mem (dp s₀) ((o + 512 * T)) = bytesAt s₂.mem (dp s₀) ((o + 512 * T)) := by
    rw [m₇, ← b₅]
    exact bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_arith)) (by omega_arith)
  obtain b₂ : ∀ n ≤ (o + 512 * T), bytesAt s₂.mem (dp s₀) n = bytesAt u.mem (dp s₀) n := fun n hn => by
    rw [m₂]
    exact prefix_frame (memIn_frame (s₀ := s₀) _ _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact data_ctx hp (by lit_omega)) (by omega_arith)
  obtain hsplit : bytesAt s₂.mem (dp s₀) ((o + 512 * T)) =
      bytesAt s₂.mem (dp s₀) ((o + 512 * (T - 1))) ++ bytesAt s₂.mem W 512 := by
    rw [← Poly1305.bytesAt_add, show (o + 512 * (T - 1)) + 512 = (o + 512 * T) by omega_arith]
  have hmac := hc.mac
  simp only [ite_true, pre] at hmac
  obtain hml : msg.length % 16 = 0 := by
    have := hmac.1
    rw [List.length_append, Poly1305.length_bytesAt] at this
    omega_arith
  refine ⟨⟨x21₇, un₇, by rw [spw, hc.inv.sp], rd₇', wr₇', hc.inv.saved.frame F (fun r hr => ?_),
      hc.inv.frame.trans (F.sub fun r hr => ?_)⟩, hM, by omega_arith, by omega_arith, fun h => by omega_arith,
    x0₇, by rw [x1₇, VG.Proof.ChaCha20.AArch64.Xor.add_ofNat],
    by rw [x2₇, show L s₀ - (o + 512 * T) - min (L s₀ - (o + 512 * T)) 256 =
      L s₀ - ((o + 512 * T) + min (L s₀ - (o + 512 * T)) 256) by omega_arith], x3₇, x22₇, x23₇, fun hlt => ?_,
    fun k hk => ?_, hc.frame.trans F, ⟨?_, ?_, ?_⟩, fun r hr => (vw r hr).trans (hc.vec r hr)⟩
  · simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
  · simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
  · -- The counter, past the four blocks.
    obtain h256 : min (L s₀ - (o + 512 * T)) 256 = 256 := by omega_arith
    rw [st₇, st₄, st₃, st₂, hc.cnt, VG.Proof.ChaCha20.AArch64.Neon4.ctr_add, h256,
      show ((o + 512 * T) + 256) / 64 = o / 64 + 8 * T + 4 by omega_arith]
  · -- The data.
    by_cases h₁ : k < (o + 512 * T)
    · rw [dout k hk (.inl h₁), hc.dataAt k hk, ite_eq_left h₁, ite_eq_left (by omega_arith)]
    by_cases h₂ : k < (o + 512 * T) + min (L s₀ - (o + 512 * T)) 256
    · have hi : k - (o + 512 * T) < min (L s₀ - (o + 512 * T)) 256 := by omega_arith
      obtain e := d₆ (k - (o + 512 * T)) hi
      rw [show (o + 512 * T) + (k - (o + 512 * T)) = k by omega_arith] at e
      rw [m₇, e, dctx k hk, hc.dataAt k hk, ite_eq_right h₁, ite_eq_left h₂]
      congr 1
      obtain k₅ : s₅.mem (Short.kp' s₀ + BitVec.ofNat 64 (k - (o + 512 * T))) =
          s₃.mem (off (cx s₀) 128 + BitVec.ofNat 64 (k - (o + 512 * T))) := by
        rw [m₅]
        exact f₄.bytes (R := ⟨off (cx s₀) 128, 256⟩) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega))
          (show 256 ≤ 2 ^ 64 by decide) (show k - (o + 512 * T) < 256 by omega_arith)
      rw [k₅, ks₃ _ (by omega_arith), x0₂, st₂, hc.cnt, KS1,
        ks_shift _ hk (q := o / 64 + 8 * T) (by omega_arith), show 64 * (o / 64 + 8 * T) = (o + 512 * T) by omega_arith]
    · rw [dout k hk (.inr (by omega_arith)), hc.dataAt k hk, ite_eq_right h₁, ite_eq_right h₂]
  · -- The message's length.
    show (msg ++ bytesAt s₇.mem (dp s₀) ((o + 512 * T))).length % 16 = 0
    rw [List.length_append, Poly1305.length_bytesAt]; omega_arith
  · -- The key.
    obtain k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
    have e := hmac.2.1
    rw [k24] at e ⊢
    rw [bytesAt_frame F (fun r hr => by
        simp only [tgt, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
        · exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))))
      (by lit_omega)]
    exact e
  · -- The accumulator.
    obtain l₇ : Spec.Poly1305.leNum (bytesAt s₇.mem (off (cx s₀) 448) 24) =
        Spec.Poly1305.leNum (bytesAt s₄.mem (off (cx s₀) 448) 24) := by
      rw [m₇, ← m₅, bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))).sub_right dsub) (by lit_omega)]
    obtain hlt := Poly1305.accumulate_lt (Rk key) (msg ++ bytesAt u.mem (dp s₀) ((o + 512 * (T - 1))))
    rw [l₇, acc₄ h2₃, show hacc s₃ = Poly.hval s₃ from rfl, hv₃,
      Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _), b₇, hsplit, ← List.append_assoc,
      b₂ _ (by omega_arith)]
    exact (Poly1305.accumulate_append (r := Rk key) (a := msg ++ bytesAt u.mem (dp s₀) ((o + 512 * (T - 1))))
      (by rw [List.length_append, Poly1305.length_bytesAt]; omega_arith)).symm

theorem wp_seq3 {a b c x : Prog isa} {s : State} {Q' Q : State → Prop}
    (h : WP isa (.seq a (.seq b c)) s Q') (hx : ∀ t, Q' t → WP isa x t Q) :
    WP isa (.seq a (.seq b (.seq c x))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine h.mono fun t ht => ?_
  rw [WP.seq_iff] at ht ⊢
  exact ht.mono fun t' ht' => WP.seq (ht'.mono hx)

/-- `cryptStitched` when encrypting, from byte `o`. -/
theorem cryptStitchedSeal_ok (sve : Bool) {s₀ : State} (hp : APre true s₀) {o : Nat} {s w₀ : State}
    {key msg : List Byte} (E : Entry true o s₀ s key msg w₀) :
    WP isa (cryptStitched sve true false) w₀ fun u => ∃ P A, Sealed s₀ s w₀ key msg P A u := by
  unfold cryptStitched afterBulk
  simp only [ite_true]
  obtain hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  obtain hLo : L s₀ - o < 2 ^ 64 := by omega_using [hL]
  refine WP.seq ((setup_ok E.inv.x21).mono fun s₂ ⟨x0₂, x1₂, x2₂, x3₂, x5₂, k₂, m₂, v₂⟩ => ?_)
  rw [E.x23, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLo] at x5₂
  apply WP.ite (decide (L s₀ - o < 512)) (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short x5₂)
  · intro hs
    exact WP.block_nil ⟨_, _, (short_crypted true E x0₂ x1₂ x2₂ x3₂ k₂ m₂ v₂
      (of_decide_eq_true hs)).sealed E.o64⟩
  · intro hs
    refine wp_seq3 (long_crypted (sve := sve) true hp E x0₂ x1₂ x2₂ x3₂ k₂ m₂ v₂
      (by have := of_decide_eq_false hs; omega_using [this])) fun u ⟨T, hT, hc⟩ => ?_
    refine WP.ite (decide (L s₀ - (o + 512 * T) = 0)) (by
        rw [show isa.eval (.zero .x .x2) u = some (u.gpr .x2 == 0) from
          VG.Proof.ChaCha20.AArch64.Xor.eval_zero u .x2, hc.x2,
          VG.Proof.ChaCha20.AArch64.Xor.ofNat_beq_zero (by omega_using [hL])]) (fun _ => ?_) (fun hz => ?_)
    · exact WP.block_nil ⟨_, _, hc.sealed E.o64⟩
    · have h₁ := of_decide_eq_false hz
      have hle := hc.le
      exact (rest_ok sve hp hc E.o64 hT (by omega_using [h₁])).mono fun w ⟨P, hw⟩ => ⟨P, _, hw⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Tail

end

end

/-! ### `ChaCha20Poly1305.AArch64.Stitched.Wide`, which this module and modules that import it used -/

section

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the first 256 bytes

For the lengths `route` picks, `Short.lean`'s pass of five blocks computes the one-time key
with the keystream of the first 256 bytes, which `ShortRest.first` XORs in
(`ShortRest.lean`'s proofs); `absorbFirst` absorbs them (`absorbFirst_ok`), and
`skipFirst` points `x22` and `x23` at the data after them (`skipFirst_ok`),
from where `cryptStitched` continues (`Crypted.lean`'s `Entry`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_subImm wp_mov wp_movz)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

/-- The data's first 256 bytes absorbed. -/
theorem absorbFirst_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv e s₀ s) (hL : 256 ≤ L s₀) :
    WP isa absorbFirst s fun s' => Inv e s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (dp s₀) 256) := by
  unfold absorbFirst
  have core : WP isa (.block [.addImm .x .x0 .x21 448, mov .x1 .x22, .movz .x .x2 16 0]) s fun s₁ =>
      s₁.gpr .x0 = off (cx s₀) 448 ∧ s₁.gpr .x1 = dp s₀ ∧ s₁.gpr .x2 = BitVec.ofNat 64 16 ∧
      s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_movz fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.x21],
        by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.x22],
        by rw [u₃.gpr]; rfl, by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd],
        by rw [u₃.wr, u₂.wr, u₁.wr]⟩
  refine WP.seq ((WP.kept core (by rfl)).mono
    fun s₁ ⟨⟨h0, h1, h2, m₁, rd₁, wr₁⟩, g₁, sp₁⟩ => ?_)
  have k₁ : Kept [] s s₁ := Kept.of g₁ sp₁ rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _)
  have hs := srcD hp
  have hsub : Region.Sub ⟨dp s₀, 16 * 16⟩ ⟨dp s₀, L s₀⟩ := Region.sub_prefix hL
  refine blocks_call (P := off (cx s₀) 448) (p := dp s₀) (n := 16) h0 h1 h2 (by decide)
    ((hs.ctx.sub_left (sub_ctx s₀ (by lit_omega))).sub_right hsub)
    (by have := hs.wrap; omega_using [hL, this])
    (fun a w ⟨r, hr', hc⟩ => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · rw [rd₁, wr₁, h.rd, h.wr]
        exact hs.cov a w ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hL, hc]⟩
      · exact covers1 hp (by rw [wr₁, h.wr]) (a := 448) (n := 128) (by lit_omega) a w
          ⟨_, List.mem_singleton_self _, hc⟩ |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (covers1 hp (by rw [wr₁, h.wr]) (a := 448) (n := 128) (by lit_omega))
    fun s₂ k₂ repr₂ => ?_
  have hk : Kept (macR s₀) s s₂ :=
    (kept_mac0 k₁).trans (kept_mac (k := 448) (n := 128) (by lit_omega) (by lit_omega) k₂)
  exact ⟨mac_inv h hk, hk, fun key msg hr => by rw [← m₁]; exact repr₂ key msg (by rw [m₁]; exact hr)⟩

/-- `x22` and `x23` past the first 256 bytes: `Inv` without them. -/
theorem skipFirst_ok {s₀ : State} {s : State} (h : Inv e s₀ s) (hL : 256 ≤ L s₀) :
    WP isa (.block skipFirst) s fun s' => Inv0 e s₀ s' ∧
      s'.gpr .x22 = dp s₀ + BitVec.ofNat 64 256 ∧ s'.gpr .x23 = BitVec.ofNat 64 (L s₀ - 256) ∧
      s'.mem = s.mem ∧
      ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have core : WP isa (.block skipFirst) s fun s' =>
      s'.gpr .x22 = s.gpr .x22 + BitVec.ofNat 64 256 ∧ s'.gpr .x23 = s.gpr .x23 - BitVec.ofNat 64 256 ∧
      (∀ r, r ≠ .x22 → r ≠ .x23 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_subImm (by decide) fun s₂ u₂ => WP.block_nil
      ⟨by rw [u₂.other _ (by decide), u₁.gpr], by rw [u₂.gpr, u₁.other _ (by decide)],
        fun r h22 h23 => by rw [u₂.other _ h23, u₁.other _ h22], by rw [u₂.mem, u₁.mem],
        by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  refine (WP.preservedV (WP.withSp core) (by lit_decide)).mono
    fun s' ⟨⟨⟨x22, x23, g, m, rd, wr⟩, sp⟩, hv⟩ => ⟨?_, by rw [x22, h.x22], ?_, m, hv⟩
  · have hu : ∀ r ∈ untouched, r ≠ .x22 ∧ r ≠ .x23 := by decide
    exact ⟨by rw [g _ (by decide) (by decide), h.x21],
      fun r hr => by rw [g r (hu r hr).1 (hu r hr).2, h.un r hr], by rw [sp, h.sp], by rw [rd, h.rd],
      by rw [wr, h.wr], by rw [m]; exact h.saved, by rw [m]; exact h.frame⟩
  · rw [x23, h.x23, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀, VG.Proof.ChaCha20.AArch64.Xor.sub_ofNat hL]

end VG.Proof.ChaCha20Poly1305.AArch64

end

end

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `seal`

With the one-time key from the scalar block function (`sealStitchedMain`,
`entry_zero`), or, for the lengths `route` picks, with the first 256 bytes'
keystream from `Short.lean`'s prologue, which encrypts them before they are absorbed
(`Wide.lean`), the stitched code continues (`Entry`): the chunks encrypt the data's whole
chunks and absorb all but the last of them (and, if a rest remains, also the
last while the next 256 bytes' keystream is computed, of which up to the
rest's length is used: `Tail.rest`); whatever is left is encrypted by
`vg_chacha20_xor`, and absorbed with what was not.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Spec.Poly1305 (Repr bytesAt mac leBytes)
open VG.Spec.ChaCha20 (stateAt)
open VG.Spec.ChaCha20Poly1305 (pad16 macData polyKeyGen)

variable {e : Bool}

/-- The data from `p`. -/
theorem srcAt {s₀ : State} (hp : APre e s₀) {p : Nat} (hle : p ≤ L s₀) :
    Src s₀ (dp s₀ + BitVec.ofNat 64 p) (L s₀ - p) := by
  obtain hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  refine ⟨by omega_using [hL], ?_, hp.c_d.sub_right (Offset.sub_base _ (by omega_using [hle])),
    (srcD hp).cov_sub (a := p) (n := L s₀ - p) (by omega_using [hle]) rfl rfl⟩
  have := hp.wrap_d
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [this]

/-- The data absorbed in two parts, at a multiple of 16 bytes, padded. -/
theorem split_pad {m : Mem} {p : Addr} {a n : Nat} (ha : a % 16 = 0) (hn : a ≤ n) :
    bytesAt m p a ++ (bytesAt m (p + BitVec.ofNat 64 a) (n - a) ++
      pad16 (bytesAt m (p + BitVec.ofNat 64 a) (n - a))) = bytesAt m p n ++ pad16 (bytesAt m p n) := by
  obtain hp : pad16 (bytesAt m (p + BitVec.ofNat 64 a) (n - a)) = pad16 (bytesAt m p n) := by
    simp only [pad16, VG.Proof.Poly1305.length_bytesAt]
    rw [show (n - a) % 16 = n % 16 by omega_using [ha, hn]]
  rw [hp, ← List.append_assoc, ← VG.Proof.Poly1305.bytesAt_add, Nat.add_sub_cancel' hn]

/-- The Poly1305 state after the chunks, from that before, through `rs`. -/
theorem sealed_inv {s₀ : State} (hp : APre true s₀) {s w u : State} {key msg : List Byte} {P A : Nat}
    (hc : Sealed s₀ s w key msg P A u) {s' : State} (hk : Kept [sub s₀ 64 384, dR s₀] u s') :
    Inv0 true s₀ s' :=
  hc.inv.step hk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
      · exact ⟨dR s₀, by simp, fun _ h => h⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega)))

theorem sealStitchedMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀) :
    WP isa (sealStitchedMain v.callee) s₀ (MainS s₀) := by
  obtain hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  unfold sealStitchedMain
  refine WP.seq (WP.mono (WP.preservedV (prologue_ok hp) (by lit_decide)) fun s₁ ⟨h₁, v₁⟩ => ?_)
  obtain hA : bytesAt s₁.mem (ad s₀) (AL s₀) = A s₀ :=
    bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) h₁.inv.x21 h₁.inv.rd h₁.inv.wr h₁.inv.x24 (by rw [h₁.inv.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₂ ⟨⟨k₂, r₂⟩, v₂⟩ => ?_)
  obtain i₂ := mac_inv h₁.inv k₂
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₂) (by lit_decide)) fun s₃ ⟨⟨i₃, k₃, len₃⟩, v₃⟩ => ?_)
  obtain st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame k₃.frame (by rdisj_all), stateAt_frame k₂.frame (by rdisj_all), h₁.st]
  obtain D₃ : bytesAt s₃.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃.frame (by rdisj_all) hL', bytesAt_frame k₂.frame (by rdisj_all) hL',
      bytesAt_frame h₁.fine (by rdisj_all) hL']
  obtain R₃ := Repr.frame k₃.frame (by rdisj_all) (r₂ (otk s₀) [] h₁.poly)
  refine WP.seq (WP.mono (counterOne_ok hp i₃) fun s₃' ⟨m₃', k₃', v₃'⟩ => ?_)
  obtain D₃' : bytesAt s₃'.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₃'.frame (by rdisj_all) hL', D₃]
  refine WP.seq ((Tail.cryptStitchedSeal_ok v.callee.sve hp (entry_zero true i₃ st₃ R₃ m₃' k₃')).mono
    fun s₄ ⟨P, A, hc⟩ => ?_)
  refine WP.seq (rest_call v hp hc.le hc.p64 hc.x0 hc.x1 hc.x2 hc.x3 hc.inv.rd hc.inv.wr (hc.inv.un .x28 (by decide)) hc.cnt hc.data
    |>.mono fun s₅ ⟨v₅, k₅, f₅, ct₅⟩ => ?_)
  rw [D₃'] at ct₅
  obtain i₅ := sealed_inv hp hc k₅
  have hpre := hc.aP
  have hle := hc.le
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := A) (by omega_using [hpre, hle])) i₅.x21 i₅.rd i₅.wr
    (by rw [k₅.cs _ (pres .x22) (pres30 .x22), hc.x22])
    (by rw [k₅.cs _ (pres .x23) (pres30 .x23), hc.x23])) (by lit_decide)) fun s₆ ⟨⟨k₆, r₆⟩, v₆⟩ => ?_)
  obtain i₆ := mac_inv0 i₅ k₆
  refine WP.mono (WP.preservedV (absorbLengths_ok0 hp i₆) (by lit_decide)) fun s₇ ⟨⟨i₇, k₇, r₇⟩, v₇⟩ => ?_
  -- The message absorbed.
  have R₄ := hc.mac
  obtain X₄ : bytesAt s₄.mem (dp s₀) A = bytesAt s₅.mem (dp s₀) A :=
    (prefix_rest hp f₅ hpre hle).symm
  rw [X₄] at R₄
  obtain R₆ := r₆ _ _ (Repr.frame k₅.frame (by rdisj_all) R₄)
  rw [List.append_assoc, split_pad hc.a16 (by omega_using [hpre, hle]), ct₅] at R₆
  obtain R₇ := r₇ _ _ R₆
  obtain L₆ : bytesAt s₆.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₆.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₃'.frame (by rdisj_all) (by lit_omega), len₃]
  rw [L₆, hA] at R₇
  refine ⟨i₇, fun r hr => (v₇ r hr).trans ((v₆ r hr).trans ((v₅ r hr).trans ((hc.vec r hr).trans ((v₃' r hr).trans
      ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))), ?_, ?_⟩
  · refine (congrArg (Repr s₇.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₇
    simp only [macData, List.nil_append, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₇.frame (by rdisj_all) hL', bytesAt_frame k₆.frame (by rdisj_all) hL', ct₅]

/-- The data's first 256 bytes are outside a part of the context. -/
theorem first_ctx {s₀ : State} (hp : APre e s₀) (hL : 256 ≤ L s₀) {k n : Nat} (h : k + n ≤ 1280) :
    (⟨dp s₀, 256⟩ : Region).Disjoint (sub s₀ k n) :=
  (data_ctx hp h).sub_left (Region.sub_prefix hL)

theorem sealWideMain_ok (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre true s₀)
    (hL : 512 ≤ L s₀) :
    WP isa (sealWideMain v.callee) s₀ (MainS s₀) := by
  obtain hL' := (Nat.le_of_lt (s₀.gpr .x5).isLt)
  obtain hL256 : 256 ≤ L s₀ := by omega_using [hL]
  unfold sealWideMain
  refine WP.seq (WP.mono (WP.preservedV (Short.prologue_ok hp) (Short.prologue_keepsV v.callee.sve))
    fun s₁ ⟨h₁, v₁⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (ShortRest.stash_ok hp h₁.inv h₁.st0) (by lit_decide))
    fun s₂ ⟨⟨i₂, k₂, st₂⟩, v₂⟩ => ?_)
  obtain hA : bytesAt s₂.mem (ad s₀) (AL s₀) = A s₀ := by
    rw [bytesAt_frame k₂.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt),
      bytesAt_frame h₁.inv.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt)]
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x24) (n := .x25) ⟨.inl rfl, .inl rfl⟩
    (srcA hp) i₂.x21 i₂.rd i₂.wr i₂.x24 (by rw [i₂.x25]; exact hRDX s₀)) (by lit_decide))
    fun s₃ ⟨⟨k₃, r₃⟩, v₃⟩ => ?_)
  obtain i₃ := mac_inv i₂ k₃
  refine WP.seq (WP.mono (WP.preservedV (lengths_ok hp i₃) (by lit_decide))
    fun s₄ ⟨⟨i₄, k₄, len₄⟩, v₄⟩ => ?_)
  obtain K₄ : ∀ i < 256, s₄.mem (Short.kp' s₀ + BitVec.ofNat 64 i) = Short.ks5 s₀ (64 + i) :=
    fun i hi => by
      rw [Short.ks_frame k₄.frame (by rdisj_all) hi, Short.ks_frame k₃.frame (by rdisj_all) hi,
        Short.ks_frame k₂.frame (by rdisj_all) hi]
      exact Short.ks_post h₁.ks hi
  obtain D₄ : bytesAt s₄.mem (dp s₀) (L s₀) = D s₀ := by
    rw [bytesAt_frame k₄.frame (by rdisj_all) hL', bytesAt_frame k₃.frame (by rdisj_all) hL',
      bytesAt_frame k₂.frame (by rdisj_all) hL', bytesAt_frame h₁.fine (by rdisj_all) hL']
  obtain R₄ : Repr s₄.mem (off (cx s₀) 448) (otk s₀) (A s₀ ++ pad16 (A s₀)) := by
    have := Repr.frame k₄.frame (by rdisj_all) (r₃ _ _ (Repr.frame k₂.frame (by rdisj_all) h₁.poly))
    rwa [List.nil_append, hA] at this
  refine WP.seq (WP.mono (WP.preservedV (ShortRest.first_ok hp i₄ hL256) (by lit_decide))
    fun s₅ ⟨⟨i₅, k₅, x₅, f₅⟩, v₅⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (absorbFirst_ok hp i₅ hL256) (by lit_decide))
    fun s₆ ⟨⟨i₆, k₆, r₆⟩, v₆⟩ => ?_)
  refine WP.seq (WP.mono (skipFirst_ok i₆ hL256) fun s₇ ⟨i₇, x22₇, x23₇, m₇, v₇⟩ => ?_)
  obtain f₆ : ∀ r ∈ macR s₀, (⟨dp s₀, 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [macR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact first_ctx hp hL256 (by lit_omega)
  obtain E : Entry true 256 s₀ s₄ (otk s₀) (A s₀ ++ pad16 (A s₀)) s₇ := by
    simp only [op_true] at x₅ f₅
    refine Entry.ofAt i₇ (by decide) hL256 x22₇ x23₇ ?_ (fun k hk => ?_) ?_ (fun r hr => ?_)
    · rw [m₇, stateAt_frame k₆.frame (by rdisj_all), stateAt_frame k₅.frame (by rdisj_all),
        stateAt_frame k₄.frame (by rdisj_all), stateAt_frame k₃.frame (by rdisj_all), st₂,
        VG.Proof.ChaCha20Poly1305.ctr_initState,
        show (1 : BitVec 32) + BitVec.ofNat 32 (256 / 64) = 5 by decide]
    · rw [m₇, data_frame k₆.frame (by rdisj_all) hk]
      by_cases h : k < 256
      · rw [x₅ k h, K₄ k h, Short.ks5_eq s₀ hk, ite_eq_left h]
      · rw [f₅ _ (ShortRest.rest_out hp.o (by omega_using [h]) hk), ite_eq_right h]
    · rw [m₇, bytesAt_frame k₆.frame f₆ (by omega_using [])]
      exact r₆ _ _ (Repr.frame k₅.frame (by rdisj_all) R₄)
    · exact (v₇ r hr).trans ((v₆ r hr).trans (v₅ r hr))
  refine WP.seq ((Tail.cryptStitchedSeal_ok v.callee.sve hp E).mono fun s₈ ⟨P, A', hc⟩ => ?_)
  refine WP.seq (rest_call v hp hc.le hc.p64 hc.x0 hc.x1 hc.x2 hc.x3 hc.inv.rd hc.inv.wr (hc.inv.un .x28 (by decide)) hc.cnt hc.data
    |>.mono fun s₉ ⟨v₉, k₉, f₉, ct₉⟩ => ?_)
  rw [D₄] at ct₉
  obtain i₉ := sealed_inv hp hc k₉
  have hpre := hc.aP
  have hle := hc.le
  refine WP.seq (WP.mono (WP.preservedV (macPad_ok hp (p := .x22) (n := .x23) ⟨.inr rfl, .inr rfl⟩
    (srcAt hp (p := A') (by omega_using [hpre, hle])) i₉.x21 i₉.rd i₉.wr
    (by rw [k₉.cs _ (pres .x22) (pres30 .x22), hc.x22])
    (by rw [k₉.cs _ (pres .x23) (pres30 .x23), hc.x23])) (by lit_decide)) fun s₁₀ ⟨⟨k₁₀, r₁₀⟩, v₁₀⟩ => ?_)
  obtain i₁₀ := mac_inv0 i₉ k₁₀
  refine WP.mono (WP.preservedV (absorbLengths_ok0 hp i₁₀) (by lit_decide))
    fun s₁₁ ⟨⟨i₁₁, k₁₁, r₁₁⟩, v₁₁⟩ => ?_
  -- The message absorbed.
  have R₈ := hc.mac
  obtain X₈ : bytesAt s₈.mem (dp s₀) A' = bytesAt s₉.mem (dp s₀) A' :=
    (prefix_rest hp f₉ hpre hle).symm
  rw [X₈] at R₈
  obtain R₁₀ := r₁₀ _ _ (Repr.frame k₉.frame (by rdisj_all) R₈)
  rw [List.append_assoc, split_pad hc.a16 (by omega_using [hpre, hle]), ct₉] at R₁₀
  obtain R₁₁ := r₁₁ _ _ R₁₀
  obtain L₁₀ : bytesAt s₁₀.mem (off (cx s₀) 0) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame k₁₀.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₉.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame hc.frame (by rdisj_all) (by lit_omega), m₇,
      bytesAt_frame k₆.frame (by rdisj_all) (by lit_omega),
      bytesAt_frame k₅.frame (by rdisj_all) (by lit_omega), len₄]
  obtain hA₄ : A s₀ = bytesAt s₄.mem (ad s₀) (AL s₀) := by
    rw [bytesAt_frame k₄.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt),
      bytesAt_frame k₃.frame (by rdisj_all) (Nat.le_of_lt (s₀.gpr .x3).isLt), hA]
  rw [L₁₀] at R₁₁
  refine ⟨i₁₁, fun r hr => (v₁₁ r hr).trans ((v₁₀ r hr).trans ((v₉ r hr).trans ((hc.vec r hr).trans
      ((v₄ r hr).trans ((v₃ r hr).trans ((v₂ r hr).trans (v₁ r hr))))))), ?_, ?_⟩
  · refine (congrArg (Repr s₁₁.mem (off (cx s₀) 448) (otk s₀)) ?_).mp R₁₁
    simp only [macData, List.append_assoc, VG.Proof.Poly1305.length_bytesAt, length_encrypt]
  · rw [bytesAt_frame k₁₁.frame (by rdisj_all) hL', bytesAt_frame k₁₀.frame (by rdisj_all) hL', ct₉]

end VG.Proof.ChaCha20Poly1305.AArch64
