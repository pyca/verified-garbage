module

public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# The precomputed values of an RSA modulus on RISC-V: the contract and the
states of a run

`fnContract`: `vg_rsa_public_precompute` on the registers; `PD`, the public
data of a run; `Base`, what holds from `setup` on, and `C1`, the state after
`setup`, for the proofs of correctness and constant time.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Pre

open VG VG.RISCV64 VG.Impl.Bignum VG.Proof.Mont
open VG.Proof.Bignum (slot)

/-- The postcondition on `pre` and the return value. -/
def preOut (nb : List Byte) (P : Addr) (pl : Nat) (r : BitVec 64) (m : Mem) : Prop :=
  match Spec.Rsa.publicPrecompute nb with
  | some ws => r.setWidth 32 = 1 ∧ Spec.Rsa.wordsAt m P pl = ws
  | none => r.setWidth 32 = 0 ∧ Spec.Rsa.wordsAt m P pl = List.replicate pl 0

/-- The arrays 0–3 of a working space at `S`. -/
abbrev arrR (S : Addr) (w : Nat) : Region := ⟨off S hdrBytes, 32 * (w + 2)⟩

/-- `pre`, `pre_len` words at `a0`. -/
abbrev preR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat * 8⟩

/-- `n`, `n_len` bytes at `a2`. -/
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩

/-- The working space, `scratch_len` words at `a4`. -/
abbrev scrR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩

/-- `vg_rsa_public_precompute(pre = a0, pre_len = a1, n = a2, n_len = a3,
scratch = a4, scratch_len = a5)`. -/
def fnContract : Contract isa where
  pre s :=
    s.rd = [nR s] ∧ s.wr = [preR s, scrR s] ∧ (preR s).Disjoint (nR s) ∧ (preR s).Disjoint (scrR s) ∧
      (nR s).Disjoint (scrR s) ∧ (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .a3).toNat ∧ (s.gpr .a1).toNat = Spec.Rsa.precomputedWords (s.gpr .a3).toNat ∧
      Spec.Rsa.publicScratchWords (s.gpr .a3).toNat ≤ (s.gpr .a5).toNat ∧
      (s.gpr .a0).toNat % 8 = 0 ∧ (s.gpr .a4).toNat % 8 = 0
  post s s' :=
    preOut (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (s.gpr .a0) (s.gpr .a1).toNat (s'.gpr .a0)
      s'.mem
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat).map (·.toNat) ∧
      s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5

/-! ## The public data of a run, and the state after `setup` -/

/-- The public data of a run: `pre`, `n`, the working space, `n_len`, the
working space's size in bytes and `n`'s bytes. -/
structure PD where
  P : Addr
  N : Addr
  S : Addr
  k : Nat
  Z : Nat
  nb : List Byte

/-- The words of a number of `n_len` bytes. -/
abbrev PD.w (d : PD) : Nat := (d.k + 7) / 8

/-- The registers `setup` sets for the rest of the function. -/
def baseRegs : List Reg := [.s5, .a7, .a2, .a5, .a6, .t0, .s6, .s8, .s7]

/-- What holds from `setup` on. -/
structure Base (d : PD) (s : State) : Prop where
  scr : Scr s d.S d.Z
  pre : Scr s d.P (16 * d.w)
  k64 : 64 ≤ d.k
  k1024 : d.k ≤ 1024
  hZ : slot d.w 8 ≤ d.Z
  hPS : ∀ x, ofs d.S x < d.Z → 16 * d.w ≤ ofs d.P x
  len : d.nb.length = d.k
  s5 : s.gpr .s5 = d.P
  a7 : s.gpr .a7 = off d.S (slot d.w 0)
  a2 : s.gpr .a2 = off d.S (slot d.w 1)
  a5 : s.gpr .a5 = off d.S (slot d.w 2)
  a6 : s.gpr .a6 = off d.S (slot d.w 3)
  t0 : s.gpr .t0 = BitVec.ofNat 64 d.w
  s6 : s.gpr .s6 = d.S
  s8 : s.gpr .s8 = BitVec.ofNat 64 d.k
  s7 : s.gpr .s7 = d.N

theorem Base.keep {d : PD} {s t : State} {rs : List Reg} (h : Base d s) (k : Keep rs s t)
    (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : Base d t where
  scr := h.scr.congr k.2.2
  pre := h.pre.congr k.2.2
  k64 := h.k64
  k1024 := h.k1024
  hZ := h.hZ
  hPS := h.hPS
  len := h.len
  s5 := (k.gpr (hr _ (by decide))).trans h.s5
  a7 := (k.gpr (hr _ (by decide))).trans h.a7
  a2 := (k.gpr (hr _ (by decide))).trans h.a2
  a5 := (k.gpr (hr _ (by decide))).trans h.a5
  a6 := (k.gpr (hr _ (by decide))).trans h.a6
  t0 := (k.gpr (hr _ (by decide))).trans h.t0
  s6 := (k.gpr (hr _ (by decide))).trans h.s6
  s8 := (k.gpr (hr _ (by decide))).trans h.s8
  s7 := (k.gpr (hr _ (by decide))).trans h.s7

/-- The state after `setup`: `n`'s bytes are readable, apart from the working
space and still in memory. -/
structure C1 (d : PD) (s : State) : Prop where
  base : Base d s
  rd : ∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.N i) 1
  sep : ∀ i < d.k, ∀ x, ofs d.S x < d.Z → off d.N i ≠ x
  bytes : ∀ i (h : i < d.nb.length), s.mem (off d.N i) = d.nb[i]

theorem C1.bytesAt {d : PD} {s : State} (h : C1 d s) : Spec.Rsa.bytesAt s.mem d.N d.k = d.nb :=
  List.ext_getElem (by simp [Spec.Rsa.bytesAt, h.base.len]) fun i h1 h2 => by
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact h.bytes i h2

end VG.Proof.Bignum.RISCV64.Pre
