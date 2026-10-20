module

public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Phase
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Xar
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Scalar
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ChaCha20-Poly1305 on AArch64, the rest when encrypting: the rounds

`Tail.rounds`: ten double rounds of the four-block kernel (`Neon4`, with
SVE2's XAR), and after each three blocks of Poly1305 (`Stitch.absorb3`) of
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

/-- The operations with SVE2. -/
theorem ops_ok : ∀ (ops : List Op) {vs : Nat → CState} {s : State}, Holds vs s →
    s.v .v30 = rol8Table →
    WP isa (.block (ops.flatMap (Op.codeFor true))) s fun s' =>
      Holds (fun j => ops.foldl step (vs j)) s' ∧ RoundSame s s'
  | [], _, _, h, _ => WP.block_nil ⟨h, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩
  | op :: ops, _, _, h, ht => by
    exact WP.block_append ((op_ok_for true op h ht).mono fun _ ⟨h', hs⟩ =>
      (ops_ok ops h' (hs.v30.trans ht)).mono fun _ ⟨h'', hs'⟩ => ⟨h'', hs.trans hs'⟩)

/-- A double round. -/
theorem doubleRound_ok {vs : Nat → CState} {s : State} (h : Holds vs s) (ht : s.v .v30 = rol8Table) :
    WP isa (.block Tail.doubleRound) s fun s' =>
      Holds (fun j => innerBlock (vs j)) s' ∧ RoundSame s s' := by
  have e : (fun j => (VG.Impl.ChaCha20.AArch64.Mixed5.roundOps).foldl step (vs j)) =
      fun j => innerBlock (vs j) := funext fun j => innerBlock_eq (vs j)
  exact (ops_ok _ h ht).mono fun _ ⟨h', hs⟩ => ⟨e ▸ h', hs⟩

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
    rw [hp, BitVec.add_assoc, ← BitVec.ofNat_add]; exact hr.blk _ (by omega)
  refine (Poly.block_absorb s ha (hb 0 (by decide)) (hb 8 (by decide)) hr.k0 hr.k1).mono
    fun u ⟨hu, hx, hk⟩ => ⟨?_, ?_, hk⟩
  · have hl : (bytesAt s.mem W (16 * n)).length % 16 = 0 := by
      rw [Poly1305.length_bytesAt]; omega
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
    refine WP.block_append ((absorb_next (by omega) ha hp hr).mono fun s₁ ⟨a₁, p₁, k₁⟩ => ?_)
    have hm₁ : s₁.mem = s.mem := k₁.2.1
    rw [← hm₁] at a₁
    refine (ih (n := n + 1) (by omega) a₁ p₁
      (hr.of k₁.2.2.1 k₁.2.2.2 (k₁.gpr' (r := .x0)))).mono fun u ⟨a, p, k'⟩ => ?_
    rw [hm₁, show n + 1 + k = n + (k + 1) by omega] at a
    rw [show n + 1 + k = n + (k + 1) by omega] at p
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
theorem iter_ok {vs : Nat → CState} {R a : Nat} {W : Addr} {s₀ s : State} {i : Nat} (hi : i < 10)
    (hr : Readable W s₀) (h : TI vs R a W s₀ s i) :
    WP isa Tail.round s fun u => TI vs R a W s₀ u (i + 1) := by
  unfold Tail.round
  apply WP.seq
  refine (doubleRound_ok h.vec h.table).mono fun b ⟨hb, hsb⟩ => ?_
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
    (absorbN_ok 3 (n := 2 + 3 * i) (by omega) hbacc hbp hbr)).mono
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
  · rw [RegUpd.gpr_write_of_ne c .x _ (by decide), hcp, show 2 + 3 * i + 3 = 2 + 3 * (i + 1) by omega]
  · have e : 16 * (2 + 3 * i + 3) = 16 * (2 + 3 * (i + 1)) := by omega
    rw [hsb.mem, h.mem, e] at hca
    exact hca.of (fun r hr' => RegUpd.gpr_write_of_ne c .x _ (by
      intro he; rw [he] at hr'; exact absurd hr' (by decide))) rfl
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hx4, hsb.gpr, h.cnt,
      Offset.ofNat_sub_ofNat (by omega : 1 ≤ 10 - i)]
    simp only [Nat.sub_sub]

/-- The loop: ten iterations. -/
theorem rounds_ok {vs : Nat → CState} {R a : Nat} {W : Addr} {s₀ s : State}
    (hr : Readable W s₀) (h : TI vs R a W s₀ s 0) :
    WP isa Tail.rounds s fun u => TI vs R a W s₀ u 10 := by
  let Inv : Nat → State → Prop := fun n u => ∃ i, i < 10 ∧ n = 10 - i ∧ TI vs R a W s₀ u i
  have hstep : ∀ n u, Inv n u → WP isa Tail.round u (fun w =>
      (eval (.nonzero .x .x4) w = some false ∧ TI vs R a W s₀ w 10) ∨
      (eval (.nonzero .x .x4) w = some true ∧ ∃ m < n, Inv m w)) := by
    rintro n u ⟨i, hi, rfl, hu⟩
    refine (iter_ok hi hr hu).mono fun w hw => ?_
    have he : eval (.nonzero .x .x4) w = some (BitVec.ofNat 64 (10 - (i + 1)) != 0) := by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hw.cnt]
    by_cases hl : i + 1 = 10
    · exact .inl ⟨by rw [he, hl]; rfl, hl ▸ hw⟩
    · have hn0 : BitVec.ofNat 64 (10 - (i + 1)) ≠ 0 := by
        intro hz
        have hz' := congrArg BitVec.toNat hz
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 10 - (i + 1) < 2 ^ 64)] at hz'
        change 10 - (i + 1) = 0 at hz'
        omega
      exact .inr ⟨by rw [he]; simpa using hn0, 10 - (i + 1), by omega, i + 1, by omega, rfl, hw⟩
  exact WP.loop (M := isa) Inv hstep 10 s ⟨0, by decide, rfl, h⟩

end VG.Proof.ChaCha20Poly1305.AArch64.Tail
