module

import VerifiedGarbage.Proof.MlKem.X86_64.TopBase
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlKem.X86_64.FragC
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.MlKem.X86_64.Frag
public import VerifiedGarbage.Proof.MlKem.KPke
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.MlKem.X86_64.S4Base
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.MlKem.X86_64.Lay
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.MlKem.X86_64.S4Loop
import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.MlKem.X86_64.Frag
meta import VerifiedGarbage.Proof.MlKem.KPke
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Base
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lay
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Sha3.Arith
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Loop
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Squeeze
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlKem.X86_64.PrfBatch`, which this module and modules that import it used -/

section

/-!
# ML-KEM on x86-64: four instances of `PRF₂` at once

`Prf4.batch m wl` (`Impl/MlKem/X86_64/Frag.lean`) writes `PRF₂(σ, N₀ + k)`
to `scratch + o + 128 k` for each `k < m`, with `σ` at `scratch + 1056`,
`scratch` in `rbx`, `scratch + o` in `r8` and `N₀` in `r9` (`batch_ok`). The input `σ ‖ N` is one block, whose
padded state (`P0`) the code writes into each of the four states, byte by byte
as `vg_mlkem_sample_ntt4_avx2` does (`S4Absorb.lean`); the permutation is
`permute4` (`permute4_ok`), and the output the first 128 bytes of each
permuted state (`prf_byte`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.Prf4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Prf4
open VG.Spec.MlKem
open VG.Spec.Sha3 (keccakF RC bytesAt)
open VG.Proof.Sha3 (byteOf Rep xorByte byteOf_xorByte byteOf_xorBytes absorb_pad iterF)
open VG.Proof.MlKem (padded prf_eq prf_length)
open VG.Proof.Sha3.X86_64.X4 (q4 la ba la_byte Lanes4 lanes4_of_bytes byte_of_lanes4 Pre4 permute4_ok wp_vmovq wp_vbcast
  wp_vst wp_vxor readW_write256 q4_ymm)
open VG.Proof.MlKem.X86_64.S4 (bytes_write wb_in wb_out byte_setWidth vz_ok)
open VG.Proof.Sha3.X86_64 (wp_movi64 wp_movm wp_store wp_store8 wp_mov32i wp_nil)

/-! ## The padded input and the output -/

/-- The state whose permutation is the padded `σ ‖ n` (one block of SHAKE256). -/
def P0 (σ : List Byte) (n : Byte) : Spec.Sha3.State :=
  xorByte (xorByte (Rep 136 (σ ++ [n])) 33 0x1f) 135 0x80

theorem padded_P0 {σ : List Byte} (h : σ.length = 32) (n : Byte) :
    padded 136 Spec.Sha3.shakeSuffix (σ ++ [n]) = keccakF (P0 σ n) := by
  rw [padded, absorb_pad (by decide) (by decide), List.length_append, h]; rfl

/-- Byte `q` of the padded state. -/
abbrev PF (σ : List Byte) (n : Byte) (q : Nat) : Byte :=
  if q < 32 then σ.getD q 0 else if q = 32 then n else if q = 33 then 0x1f else if q = 135 then 0x80 else 0

theorem byteOf_P0 {σ : List Byte} (h : σ.length = 32) (n : Byte) {q : Nat} (hq : q < 200) :
    byteOf (P0 σ n) q = PF σ n q := by
  have hz : byteOf Spec.Sha3.zero q = 0 := by
    simp only [byteOf, Spec.Sha3.zero, getElem!_pos (Vector.replicate 25 (0 : BitVec 64)) (q / 8) (by bdd_omega),
      Vector.getElem_replicate]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  have hl : (σ ++ [n]).length = 33 := by rw [List.length_append, h]; rfl
  have ha : Spec.Sha3.absorb 136 (σ ++ [n]) = Spec.Sha3.zero := by simp [Spec.Sha3.absorb, hl]
  have hr : byteOf (Rep 136 (σ ++ [n])) q = (σ ++ [n]).getD q 0 := by
    rw [Rep, ha, byteOf_xorBytes _ _ hq, hz, hl, show 136 * (33 / 136) = 0 from rfl, List.drop_zero]
    exact BitVec.zero_xor
  have hg : (σ ++ [n]).getD q 0 = if q < 32 then σ.getD q 0 else if q = 32 then n else 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append]
    by_cases e1 : q < 32
    · rw [ifp (show q < σ.length by bdd_omega), ifp e1, List.getD_eq_getElem?_getD]
    · rw [ifn (show ¬ q < σ.length by bdd_omega), ifn e1, h]
      by_cases e2 : q = 32
      · subst e2; rw [ifp rfl]; rfl
      · rw [ifn e2, List.getElem?_singleton, ifn (by bdd_omega)]; rfl
  rw [P0, byteOf_xorByte _ _ _ hq, byteOf_xorByte _ _ _ hq, hr, hg, PF]
  by_cases e1 : q < 32
  · rw [ifn (show ¬ q = 135 by bdd_omega), ifn (show ¬ q = 33 by bdd_omega), ifp e1, ifp e1]
  · rw [ifn e1, ifn e1]
    by_cases e2 : q = 32
    · rw [ifn (show ¬ q = 135 by bdd_omega), ifn (show ¬ q = 33 by bdd_omega), ifp e2, ifp e2]
    · rw [ifn e2, ifn e2]
      by_cases e3 : q = 33
      · rw [ifn (show ¬ q = 135 by bdd_omega), ifp e3, ifp e3]; exact BitVec.zero_xor
      · rw [ifn e3, ifn e3]
        by_cases e4 : q = 135
        · rw [ifp e4, ifp e4]; exact BitVec.zero_xor
        · rw [ifn e4, ifn e4]

/-- Byte `j` of `PRF₂(σ, n)`: of the permuted padded state. -/
theorem prf_byte {σ : List Byte} (h : σ.length = 32) (n : Byte) {j : Nat} (hj : j < 128) :
    (prf 2 σ n)[j]'(by rw [prf_length]; exact hj) = byteOf (keccakF (P0 σ n)) j := by
  have e := Proof.Sha3.squeezeFrom_getElem (rate := 136) (by decide) (by decide)
    (padded 136 Spec.Sha3.shakeSuffix (σ ++ [n])) (pos := 0) (d := 64 * 2) (i := j) (by bdd_omega)
  rw [List.getElem_of_eq (prf_eq 2 σ n), e, show (0 + j) / 136 = 0 by bdd_omega, show (0 + j) % 136 = j by bdd_omega,
    padded_P0 h]
  rfl

/-- `PRF₂(σ, n)` in memory, from its bytes. -/
theorem bytes_prf {m : Mem} {p : Addr} {σ : List Byte} (h : σ.length = 32) {n : Byte}
    (hb : ∀ j < 128, m (p + BitVec.ofNat 64 j) = byteOf (keccakF (P0 σ n)) j) :
    bytesAt m p 128 = prf 2 σ n := by
  apply List.ext_getElem (by rw [prf_length]; simp [bytesAt])
  intro j h₁ _
  simp only [bytesAt, List.length_map, List.length_range] at h₁
  rw [prf_byte h n h₁]
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  exact hb j h₁

/-! ## Where the code works -/

section
variable (b : Addr) (wl o m : Nat)
/-- The four states, from lane `wl` of `scratch` (at `b`). -/
abbrev sP : Addr := b + BitVec.ofNat 64 (32 * wl)
/-- `σ`. -/
abbrev sS : Addr := b + BitVec.ofNat 64 (oG + 32)
/-- The working space. -/
abbrev wR : Region := ⟨sP b wl, 2368⟩
/-- The outputs. -/
abbrev oR : Region := ⟨b + BitVec.ofNat 64 o, 128 * m⟩
abbrev sR : Region := ⟨sS b, 32⟩
end

/-- What `batch N₀ m o wl` needs of the state `s₀` it starts from, with
`scratch` at `b`. -/
structure BPre (b : Addr) (wl o m : Nat) (s₀ : State) : Prop where
  rbx : s₀.gpr .rbx = b
  w : InRegions s₀.wr (sP b wl) 2368
  out : InRegions s₀.wr (b + BitVec.ofNat 64 o) (128 * m)
  sig : InRegions (s₀.rd ++ s₀.wr) (sS b) 32
  dWO : (wR b wl).Disjoint (oR b o m)
  dWS : (wR b wl).Disjoint (sR b)
  dOS : (oR b o m).Disjoint (sR b)
  hm : m ≤ 4
  small : 32 * wl + 2368 < 2 ^ 31

/-- The registers `batch` keeps: the callee-saved ones and those of the
loop of batches (`r8`–`r10`). -/
def kept : List Reg := calleeSaved ++ [.r8, .r9, .r10]

/-- Between the pieces of `batch`, from `s₀`. -/
structure BEnv (b : Addr) (wl o m : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cs : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  frame : Frame [wR b wl, oR b o m] s₀.mem s.mem

theorem rax_ncs : ∀ r ∈ kept, r ≠ .rax := by decide

/-- `σ`, from `s₀`. -/
abbrev sig (b : Addr) (s₀ : State) : List Byte := bytesAt s₀.mem (sS b) 32

theorem sig_length (b : Addr) (s₀ : State) : (sig b s₀).length = 32 := by simp [bytesAt]

theorem sig_getD (b : Addr) (s₀ : State) {q : Nat} (hq : q < 32) :
    (sig b s₀).getD q 0 = s₀.mem (sS b + BitVec.ofNat 64 q) := by
  simp [bytesAt, hq]

/-- An address of the working space. -/
theorem at_w (b : Addr) {wl x d : Nat} (h : x = 32 * wl + d) :
    b + BitVec.ofNat 64 x = sP b wl + BitVec.ofNat 64 d := by
  rw [sP, Offset.add_add, h]

section
variable {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀)
include hp

theorem BEnv.rbx {s : State} (he : BEnv b wl o m s₀ s) : s.gpr .rbx = b := (he.cs .rbx (by decide)).trans hp.rbx

omit hp in
theorem BEnv.refl : BEnv b wl o m s₀ s₀ := ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem in_w {s : State} (he : BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 2368) :
    InRegions s.wr (sP b wl + BitVec.ofNat 64 a) n := by
  rw [he.wr]; exact inRegions_sub hp.w h (by decide)

theorem in_w' {s : State} (he : BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 2368) :
    InRegions (s.rd ++ s.wr) (sP b wl + BitVec.ofNat 64 a) n :=
  VG.Proof.Sha3.X86_64.X4.in_append (in_w hp he h)

theorem in_o {s : State} (he : BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 128 * m) :
    InRegions s.wr (b + BitVec.ofNat 64 o + BitVec.ofNat 64 a) n := by
  rw [he.wr]; exact inRegions_sub hp.out h (by have := hp.hm; omega_using [this])

theorem in_s {s : State} (he : BEnv b wl o m s₀ s) {a n : Nat} (h : a + n ≤ 32) :
    InRegions (s.rd ++ s.wr) (sS b + BitVec.ofNat 64 a) n := by
  rw [he.rd, he.wr]; exact inRegions_sub hp.sig h (by decide)

/-- `σ` is not written. -/
theorem sig_readW {s : State} (he : BEnv b wl o m s₀ s) {i : Nat} (hi : i < 4) :
    s.mem.readW (sS b + BitVec.ofNat 64 (8 * i)) 64 = s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * i)) 64 :=
  he.frame.readW (r := sR b) (Offset.contains_base _ (by bdd_omega) (by bdd_omega))
    (by simpa using ⟨hp.dWS.symm, hp.dOS.symm⟩) (by decide)

omit hp in
/-- A write within the working space. -/
theorem BEnv.write {s s' : State} (he : BEnv b wl o m s₀ s) {e n : Nat} (hn : e + n ≤ 2368)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 e) v) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ kept, s'.gpr r = s.gpr r) : BEnv b wl o m s₀ s' := by
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, fun r hr => (hg r hr).trans (he.cs r hr), ?_⟩
  rw [hm]
  exact he.frame.writeW (List.mem_cons_self ..) v (by
    rw [show 8 * n / 8 = n by bdd_omega]; exact Offset.contains_base _ hn (by bdd_omega))

/-- A write within the outputs. -/
theorem BEnv.writeO {s s' : State} (he : BEnv b wl o m s₀ s) {e n : Nat} (hn : e + n ≤ 128 * m)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (b + BitVec.ofNat 64 o + BitVec.ofNat 64 e) v)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r ∈ kept, s'.gpr r = s.gpr r) :
    BEnv b wl o m s₀ s' := by
  have := hp.hm
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, fun r hr => (hg r hr).trans (he.cs r hr), ?_⟩
  rw [hm]
  exact he.frame.writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) v (by
    rw [show 8 * n / 8 = n by bdd_omega]; exact Offset.contains_base _ hn (by bdd_omega))

end

/-! ## The round constants -/

/-- The table of the round constants, from lane 50 of the states. -/
abbrev Tbl (p : Addr) (n : Nat) (mem : Mem) : Prop := ∀ r < n, ∀ k < 4, mem.readW (la p (50 + r) k) 64 = RC r

theorem rc_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {r : Nat} (hr : r < 24) {s : State}
    (h : BEnv b wl o m s₀ s ∧ Tbl (sP b wl) r s.mem) :
    WP isa (.block [.movImm64 .rax (RC r), .vop (.vmovq .xmm0 .rax),
      .vop (.vpbroadcastq .l256 .xmm0 .xmm0), Impl.Sha3.X86_64.X4.st .rbx (wl + 50 + r) .xmm0]) s
      (fun s' => BEnv b wl o m s₀ s' ∧ Tbl (sP b wl) (r + 1) s'.mem) := by
  obtain ⟨he, ht⟩ := h
  have hbx := he.rbx hp
  have := hp.small
  refine wp_movi64 fun s₁ u₁ => wp_vmovq fun s₂ u₂ => wp_vbcast fun s₃ u₃ =>
    wp_vst (a := sP b wl + BitVec.ofNat 64 (32 * (50 + r)))
      (by rw [VG.Proof.Sha3.X86_64.ea_at, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hbx]; exact at_w b (by bdd_omega))
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact in_w hp he (by bdd_omega))
      fun s₄ g₄ _ m₄ r₄ w₄ => wp_nil ?_
  have hv : ∀ k < 4, q4 s₃ .xmm0 k = RC r := fun k hk => by
    rw [u₃.val k hk, u₂.val 0 (by decide), ite_eq_left rfl, u₁.gpr]
  have hm : s₄.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 (32 * (50 + r))) (s₃.ymm .xmm0) := by
    rw [m₄, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨he.write (n := 32) (by bdd_omega) hm (by rw [r₄, u₃.rd, u₂.rd, u₁.rd]) (by rw [w₄, u₃.wr, u₂.wr, u₁.wr])
    fun g hg => by rw [g₄, u₃.gpr, u₂.gpr, u₁.other g (rax_ncs g hg)], fun r' hr' k hk => ?_⟩
  rw [hm]
  by_cases e : r' = r
  · subst e
    rw [la, ← Offset.add_add, readW_write256 _ _ _ hk, q4_ymm _ _ hk, hv k hk]
  · have e := readW_writeW_off s.mem (sP b wl) (s₃.ymm .xmm0) (d := 32 * (50 + r') + 8 * k)
      (e := 32 * (50 + r)) (n := 8) (by bdd_omega) (by bdd_omega) (by bdd_omega)
    exact e.trans (ht r' (by bdd_omega) k hk)

theorem rcTable_eq (wl : Nat) : Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50) = (List.range 24).flatMap fun r =>
    [.movImm64 .rax (Spec.Sha3.RC r), .vop (.vmovq .xmm0 .rax), .vop (.vpbroadcastq .l256 .xmm0 .xmm0),
      Impl.Sha3.X86_64.X4.st .rbx (wl + 50 + r) .xmm0] := rfl

theorem rc_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {s : State}
    (he : BEnv b wl o m s₀ s) :
    WP isa (.block (Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50))) s
      (fun s' => BEnv b wl o m s₀ s' ∧ Tbl (sP b wl) 24 s'.mem) := by
  rw [rcTable_eq]
  exact wp_range_flatMap (M := isa) (fun r s => BEnv b wl o m s₀ s ∧ Tbl (sP b wl) r s.mem)
    (fun r s hr h => rc_step hp hr h) 24 (Nat.le_refl _) s ⟨he, fun _ h => absurd h (by bdd_omega)⟩

/-! ## The padded inputs, byte by byte -/

/-- The four states at `p` hold `F`. -/
def SB (p : Addr) (mem : Mem) (F : Nat → Nat → Byte) : Prop := ∀ k < 4, ∀ q < 200, mem (ba p k q) = F k q

/-- While the states are written, after the table (in `m₁`). -/
structure AI (b : Addr) (wl o m : Nat) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  env : BEnv b wl o m s₀ s
  fr : Frame [⟨sP b wl, 800⟩] m₁ s.mem

theorem AI.write {b : Addr} {wl o m : Nat} {s₀ : State} {m₁ : Mem} {s s' : State}
    (h : AI b wl o m s₀ m₁ s) {e n : Nat} (hn : e + n ≤ 800)
    {v : BitVec (8 * n)} (hm : s'.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 e) v) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ kept, s'.gpr r = s.gpr r) : AI b wl o m s₀ m₁ s' :=
  ⟨h.env.write (by bdd_omega) hm hrd hwr hg, by
    rw [hm]
    exact h.fr.writeW (List.mem_singleton_self _) v (by
      rw [show 8 * n / 8 = n by bdd_omega]; exact Offset.contains_base _ hn (by bdd_omega))⟩

/-- A step that writes no memory and no callee-saved register. -/
theorem AI.keep {b : Addr} {wl o m : Nat} {s₀ : State} {m₁ : Mem} {s s' : State}
    (h : AI b wl o m s₀ m₁ s) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hg : ∀ r ∈ kept, s'.gpr r = s.gpr r) : AI b wl o m s₀ m₁ s' :=
  h.write (e := 0) (n := 0) (v := 0) (by bdd_omega) (by rw [hm]; funext x; simp [Mem.writeW, Mem.write]) hrd hwr hg

/-! ### Zeroing -/

structure ZInv (b : Addr) (wl o m : Nat) (s₀ : State) (m₁ : Mem) (n : Nat) (s : State) : Prop where
  ai : AI b wl o m s₀ m₁ s
  x0 : ∀ k < 4, q4 s .xmm0 k = 0
  bytes : ∀ k < 4, ∀ q < 200, q / 8 < n → s.mem (ba (sP b wl) k q) = 0

theorem zero_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {i : Nat}
    (hi : i < 25) {s : State} (h : ZInv b wl o m s₀ m₁ i s) :
    WP isa (.block [Impl.Sha3.X86_64.X4.st .rbx (wl + i) .xmm0]) s (ZInv b wl o m s₀ m₁ (i + 1)) := by
  have := hp.small
  refine wp_vst (a := sP b wl + BitVec.ofNat 64 (32 * i))
    (by rw [VG.Proof.Sha3.X86_64.ea_at, h.ai.env.rbx hp]; exact at_w b (by bdd_omega))
    (in_w hp h.ai.env (by bdd_omega)) fun s' g' q' m' r' w' => wp_nil ?_
  refine ⟨h.ai.write (e := 32 * i) (n := 32) (by bdd_omega) m' r' w' fun r _ => by rw [g'],
    fun k hk => by rw [q', h.x0 k hk], fun k hk q hq hn => ?_⟩
  rw [m']
  have hb := bytes_write (m := s.mem) (p := sP b wl) (F := fun k q => s.mem (ba (sP b wl) k q))
    (fun _ _ _ _ => rfl) (s.ymm .xmm0) (e := 32 * i) (by decide) (by bdd_omega) hk hq
  rw [hb]
  split
  · rename_i hc
    simp only [S4.off4] at hc ⊢
    rw [show 8 * (32 * (q / 8) + 8 * k + q % 8 - 32 * i) = 64 * k + 8 * (q % 8) by bdd_omega,
      ← extract_extract (s.ymm .xmm0) (64 * k) 64 (8 * (q % 8)) 8 (by bdd_omega), q4_ymm _ _ hk, h.x0 k hk]
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  · rename_i hc
    simp only [S4.off4] at hc
    exact h.bytes k hk q hq (by bdd_omega)

theorem zero_eq (wl : Nat) : zero wl = Impl.Sha3.X86_64.X4.vb .vpxor .xmm0 .xmm0 .xmm0 ::
    (List.range 25).flatMap fun i => [Impl.Sha3.X86_64.X4.st .rbx (wl + i) .xmm0] := rfl

theorem zero_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {s : State}
    (h : AI b wl o m s₀ m₁ s) :
    WP isa (.block (zero wl)) s (fun s' => AI b wl o m s₀ m₁ s' ∧ SB (sP b wl) s'.mem fun _ _ => 0) := by
  rw [zero_eq]
  refine wp_vxor fun s₁ u₁ => WP.mono (wp_range_flatMap (M := isa) (ZInv b wl o m s₀ m₁)
    (fun i s hi h => zero_step hp hi h) 25 (Nat.le_refl _) s₁
    ⟨h.keep u₁.mem u₁.rd u₁.wr fun r _ => by rw [u₁.gpr],
      fun k hk => by rw [u₁.val k hk, BitVec.xor_self]; rfl, fun _ _ _ _ h => absurd h (by bdd_omega)⟩)
    fun s' h' => ⟨h'.ai, fun k hk q hq => h'.bytes k hk q hq (by bdd_omega)⟩

/-! ### `σ` -/

/-- The states after the first `I` lanes of `σ` (and the first `K` states of lane `I`). -/
def GF (b : Addr) (s₀ : State) (I K : Nat) (k q : Nat) : Byte :=
  if q < 8 * I ∨ (q / 8 = I ∧ k < K) then s₀.mem (sS b + BitVec.ofNat 64 q) else 0

theorem sig_store {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {I K : Nat}
    (hI : I < 4) (hK : K < 4) {s : State}
    (h : AI b wl o m s₀ m₁ s ∧ s.gpr .rax = s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * I)) 64 ∧
      SB (sP b wl) s.mem (GF b s₀ I K)) :
    WP isa (.block [.store (at_ .rbx (32 * (wl + I) + 8 * K)) .rax]) s (fun s' => AI b wl o m s₀ m₁ s' ∧
      s'.gpr .rax = s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * I)) 64 ∧ SB (sP b wl) s'.mem (GF b s₀ I (K + 1))) := by
  obtain ⟨ha, hx, hb⟩ := h
  have := hp.small
  refine wp_store (a := sP b wl + BitVec.ofNat 64 (32 * I + 8 * K))
    (by rw [ea_at, ha.env.rbx hp]; exact at_w b (by bdd_omega)) (in_w hp ha.env (by bdd_omega))
    fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 (32 * I + 8 * K))
      (s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * I)) 64) := by rw [m₂, hx]
  refine ⟨ha.write (n := 8) (by bdd_omega) hm r₂ w₂ fun r _ => by rw [g₂], by rw [g₂, hx], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [S4.off4]
  by_cases hc : 32 * I + 8 * K ≤ 32 * (q / 8) + 8 * k + q % 8 ∧ 32 * (q / 8) + 8 * k + q % 8 < 32 * I + 8 * K + 64 / 8
  · have hk' : k = K := by bdd_omega
    have hq' : q / 8 = I := by bdd_omega
    subst hk'
    rw [ifp hc, GF, ifp (.inr ⟨hq', by bdd_omega⟩),
      show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * I + 8 * k)) = 8 * (q % 8) by bdd_omega,
      byte_readW _ _ (by bdd_omega), Offset.add_add, show 8 * I + q % 8 = q by bdd_omega]
  · rw [ifn hc, GF, GF]
    by_cases hc' : q < 8 * I ∨ (q / 8 = I ∧ k < K)
    · rw [ifp hc', ifp (by bdd_omega)]
    · rw [ifn hc', ifn (by bdd_omega)]

theorem sig_lane {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {I : Nat}
    (hI : I < 4) {s : State} (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (GF b s₀ I 0)) :
    WP isa (.block (.mov .rax (.mem (at_ .rbx (oG + 32 + 8 * I))) ::
      (List.range 4).flatMap fun k => [.store (at_ .rbx (32 * (wl + I) + 8 * k)) .rax])) s
      (fun s' => AI b wl o m s₀ m₁ s' ∧ SB (sP b wl) s'.mem (GF b s₀ (I + 1) 0)) := by
  obtain ⟨ha, hb⟩ := h
  refine wp_movm (a := sS b + BitVec.ofNat 64 (8 * I)) (by rw [ea_at, ha.env.rbx hp, Offset.add_add])
    (in_s hp ha.env (by bdd_omega)) fun s₁ u₁ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => AI b wl o m s₀ m₁ s ∧
      s.gpr .rax = s₀.mem.readW (sS b + BitVec.ofNat 64 (8 * I)) 64 ∧ SB (sP b wl) s.mem (GF b s₀ I K))
    (fun K s hK h => sig_store hp hI hK h) 4 (Nat.le_refl _) s₁
    ⟨ha.keep u₁.mem u₁.rd u₁.wr fun r hr => u₁.other r (rax_ncs r hr), by
      rw [u₁.gpr, sig_readW hp ha.env hI], by rw [u₁.mem]; exact hb⟩) fun s' ⟨ha', _, hb'⟩ =>
    ⟨ha', fun k hk q hq => ?_⟩
  rw [hb' k hk q hq, GF, GF]
  by_cases hc : q < 8 * I ∨ (q / 8 = I ∧ k < 4)
  · rw [ifp hc, ifp (by bdd_omega)]
  · rw [ifn hc, ifn (by bdd_omega)]

theorem sigLanes_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {s : State}
    (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem fun _ _ => 0) :
    WP isa (.block (sigLanes wl)) s (fun s' => AI b wl o m s₀ m₁ s' ∧ SB (sP b wl) s'.mem (GF b s₀ 4 0)) :=
  wp_range_flatMap (M := isa) (fun I s => AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (GF b s₀ I 0))
    (fun I s hI h => sig_lane hp hI h) 4 (Nat.le_refl _) s
    ⟨h.1, fun k hk q hq => by rw [h.2 k hk q hq, GF, ifn (by bdd_omega)]⟩

/-! ### The indices and the padding -/

/-- The byte `c` (in `rax`) to byte `q₀` of state `K`. -/
theorem cbyte_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem}
    {F : Nat → Nat → Byte} {K q₀ : Nat} (hK : K < 4) (hq₀ : q₀ < 200) {c : Byte} {s : State}
    (hax : s.gpr .rax = c.setWidth 64) (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem F) :
    WP isa (.block [.store8 (at_ .rbx (32 * (wl + q₀ / 8) + 8 * K + q₀ % 8)) .rax]) s
      (fun s' => AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        SB (sP b wl) s'.mem fun k q => if k = K ∧ q = q₀ then c else F k q) := by
  obtain ⟨ha, hb⟩ := h
  have := hp.small
  refine wp_store8 (a := sP b wl + BitVec.ofNat 64 (32 * (q₀ / 8) + 8 * K + q₀ % 8))
    (by rw [ea_at, ha.env.rbx hp]; exact at_w b (by bdd_omega)) (in_w hp ha.env (by bdd_omega))
    fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (sP b wl + BitVec.ofNat 64 (32 * (q₀ / 8) + 8 * K + q₀ % 8)) c := by
    rw [m₂, hax, byte_setWidth]
  refine ⟨ha.write (n := 1) (by bdd_omega) hm r₂ w₂ fun r _ => by rw [g₂], by rw [g₂], fun k hk q hq => ?_⟩
  rw [hm, bytes_write hb _ (by decide) (by bdd_omega) hk hq]
  simp only [S4.off4]
  by_cases hc : 32 * (q₀ / 8) + 8 * K + q₀ % 8 ≤ 32 * (q / 8) + 8 * k + q % 8 ∧
      32 * (q / 8) + 8 * k + q % 8 < 32 * (q₀ / 8) + 8 * K + q₀ % 8 + 8 / 8
  · have e : k = K ∧ q = q₀ := by bdd_omega
    rw [ifp hc, ifp e, show 8 * (32 * (q / 8) + 8 * k + q % 8 - (32 * (q₀ / 8) + 8 * K + q₀ % 8)) = 0 by bdd_omega,
      Proof.Sha3.extractLsb'_byte]
  · rw [ifn hc, ifn (by bdd_omega)]

/-- The states after the indices of the first `K`. -/
def NF (b : Addr) (s₀ : State) (N₀ K : Nat) (k q : Nat) : Byte :=
  if q = 32 ∧ k < K then BitVec.ofNat 8 (N₀ + k) else GF b s₀ 4 0 k q

theorem b8_of64 {n : Nat} (hn : n < 256) : (BitVec.ofNat 64 n : BitVec 64) = (BitVec.ofNat 8 n).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by bdd_omega : n < 18446744073709551616), Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by bdd_omega : n < 18446744073709551616)]

theorem nonces_eq (wl : Nat) : nonces wl = ([.mov .rax (.reg .r9)] : List Instr) ++ (List.range 4).flatMap fun k =>
    ([.store8 (at_ .rbx (32 * (wl + 32 / 8) + 8 * k + 32 % 8)) .rax] : List Instr) ++
      ([.alu .add .rax (.imm 1)] : List Instr) := rfl

theorem nonces_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {N₀ : Nat}
    (hN : N₀ + 4 ≤ 256) {s : State} (h9 : s.gpr .r9 = BitVec.ofNat 64 N₀)
    (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (GF b s₀ 4 0)) :
    WP isa (.block (nonces wl)) s (fun s' => AI b wl o m s₀ m₁ s' ∧ SB (sP b wl) s'.mem (NF b s₀ N₀ 4)) := by
  rw [nonces_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s₁ => s₁.gpr .rax = BitVec.ofNat 64 N₀ ∧ s₁.mem = s.mem)
    (by xrun [h9]) rfl) fun s₁ ⟨⟨hax, hm⟩, k₁⟩ => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => (AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (NF b s₀ N₀ K)) ∧
      s.gpr .rax = BitVec.ofNat 64 (N₀ + K))
    (fun K s hK ⟨⟨ha, hb⟩, hr⟩ => ?_) 4 (Nat.le_refl _) s₁
    ⟨⟨h.1.keep hm k₁.2.1 k₁.2.2 fun r hr => k₁.gpr (by simpa using rax_ncs r hr),
      fun k hk q hq => by rw [hm, h.2 k hk q hq, NF, ifn (by bdd_omega)]⟩, by rw [hax, Nat.add_zero]⟩)
    fun s' h' => h'.1
  rw [WP.block_append_iff]
  refine WP.mono (cbyte_step hp (F := NF b s₀ N₀ K) (q₀ := 32) (c := BitVec.ofNat 8 (N₀ + K)) hK (by decide)
    (by rw [hr, b8_of64 (by bdd_omega)]) ⟨ha, hb⟩) fun s₂ ⟨ha₂, hr₂, hb₂⟩ => ?_
  refine WP.mono (WP.keep [.rax] (Q := fun s₃ => s₃.gpr .rax = BitVec.ofNat 64 (N₀ + K + 1) ∧ s₃.mem = s₂.mem)
    (by xrun [hr₂, hr, ← VG.Proof.Sha3.ofNat_succ]) rfl) fun s₃ ⟨⟨hax₃, hm₃⟩, k₃⟩ =>
      ⟨⟨ha₂.keep hm₃ k₃.2.1 k₃.2.2 fun r hr => k₃.gpr (by simpa using rax_ncs r hr), fun k hk q hq => ?_⟩,
        by rw [hax₃, Nat.add_assoc]⟩
  rw [hm₃, hb₂ k hk q hq]
  simp only [NF]
  by_cases e : k = K ∧ q = 32
  · rw [ifp e, ifp ⟨e.2, by bdd_omega⟩, e.1]
  · rw [ifn e]
    by_cases e' : q = 32 ∧ k < K
    · rw [ifp e', ifp ⟨e'.1, by bdd_omega⟩]
    · rw [ifn e', ifn (by bdd_omega)]

/-- The byte `c` to byte `q₀` of each state. -/
theorem cbytes_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem}
    {F : Nat → Nat → Byte} {q₀ : Nat} (hq₀ : q₀ < 200) {c : Byte} {s : State} (hax : s.gpr .rax = c.setWidth 64)
    (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem F) :
    WP isa (.block ((List.range 4).flatMap fun k => [.store8 (at_ .rbx (32 * (wl + q₀ / 8) + 8 * k + q₀ % 8)) .rax])) s
      (fun s' => AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = s.gpr .rax ∧
        SB (sP b wl) s'.mem fun k q => if q = q₀ then c else F k q) := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s' => AI b wl o m s₀ m₁ s' ∧ s'.gpr .rax = c.setWidth 64 ∧
      SB (sP b wl) s'.mem fun k q => if k < K ∧ q = q₀ then c else F k q)
    (fun K s' hK ⟨ha, hx, hb⟩ => WP.mono (cbyte_step hp hK hq₀ hx ⟨ha, hb⟩) fun s'' ⟨ha', hx', hb'⟩ =>
      ⟨ha', hx'.trans hx, fun k hk q hq => ?_⟩) 4 (Nat.le_refl _) s ⟨h.1, hax, fun k hk q hq => ?_⟩)
    fun s' ⟨ha, hx, hb⟩ => ⟨ha, hx.trans hax.symm, fun k hk q hq => ?_⟩
  · rw [hb' k hk q hq]
    dsimp only
    by_cases e : k = K ∧ q = q₀
    · rw [ifp e, ifp (by bdd_omega)]
    · rw [ifn e]
      by_cases e' : k < K ∧ q = q₀
      · rw [ifp e', ifp (by bdd_omega)]
      · rw [ifn e', ifn (by bdd_omega)]
  · rw [h.2 k hk q hq]; dsimp only; rw [ifn (by bdd_omega)]
  · rw [hb k hk q hq]
    dsimp only
    by_cases e : q = q₀
    · rw [ifp e, ifp ⟨hk, e⟩]
    · rw [ifn e, ifn (by bdd_omega)]

theorem pads_eq (wl : Nat) : pads wl = ([.mov32 .rax (.imm 0x1f)] : List Instr) ++
    ((List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (wl + 33 / 8) + 8 * k + 33 % 8)) .rax]) ++
    (([.mov32 .rax (.imm 0x80)] : List Instr) ++
      (List.range 4).flatMap (fun k => [Instr.store8 (at_ .rbx (32 * (wl + 135 / 8) + 8 * k + 135 % 8)) .rax]))) :=
  rfl

/-- The padded inputs, from the states that hold `σ` and the indices. -/
theorem pads_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {m₁ : Mem} {N₀ : Nat}
    {s : State} (h : AI b wl o m s₀ m₁ s ∧ SB (sP b wl) s.mem (NF b s₀ N₀ 4)) :
    WP isa (.block (pads wl)) s (fun s' => AI b wl o m s₀ m₁ s' ∧
      SB (sP b wl) s'.mem fun k q => PF (sig b s₀) (BitVec.ofNat 8 (N₀ + k)) q) := by
  rw [pads_eq, WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₁ u₁ => wp_nil
    (Q := fun s₁ => AI b wl o m s₀ m₁ s₁ ∧ s₁.gpr .rax = (0x1f : Byte).setWidth 64 ∧ SB (sP b wl) s₁.mem (NF b s₀ N₀ 4))
    ⟨h.1.keep u₁.mem u₁.rd u₁.wr fun r hr => u₁.other r (rax_ncs r hr), by rw [u₁.gpr]; rfl,
      by rw [u₁.mem]; exact h.2⟩) fun s₁ ⟨a₁, x₁, b₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cbytes_ok hp (by decide) x₁ ⟨a₁, b₁⟩) fun s₂ ⟨a₂, _, b₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (wp_mov32i (is := []) fun s₃ u₃ => wp_nil
    (Q := fun s₃ => AI b wl o m s₀ m₁ s₃ ∧ s₃.gpr .rax = (0x80 : Byte).setWidth 64 ∧
      SB (sP b wl) s₃.mem fun k q => if q = 33 then 0x1f else NF b s₀ N₀ 4 k q)
    ⟨a₂.keep u₃.mem u₃.rd u₃.wr fun r hr => u₃.other r (rax_ncs r hr), by rw [u₃.gpr]; rfl,
      by rw [u₃.mem]; exact b₂⟩) fun s₃ ⟨a₃, x₃, b₃⟩ => ?_
  refine WP.mono (cbytes_ok hp (by decide) x₃ ⟨a₃, b₃⟩) fun s₄ ⟨a₄, _, b₄⟩ => ⟨a₄, fun k hk q hq => ?_⟩
  rw [b₄ k hk q hq]
  dsimp only [PF]
  rw [NF, GF]
  by_cases e1 : q < 32
  · rw [ifn (show ¬ q = 135 by bdd_omega), ifn (show ¬ q = 33 by bdd_omega), ifn (show ¬ (q = 32 ∧ k < 4) by bdd_omega),
      ifp (show q < 8 * 4 ∨ (q / 8 = 4 ∧ k < 0) by bdd_omega), ifp e1, sig_getD b s₀ e1]
  · rw [ifn e1]
    by_cases e2 : q = 32
    · rw [ifn (show ¬ q = 135 by bdd_omega), ifn (show ¬ q = 33 by bdd_omega), ifp ⟨e2, hk⟩, ifp e2]
    · rw [ifn e2, ifn (show ¬ (q = 32 ∧ k < 4) by bdd_omega), ifn (show ¬ (q < 8 * 4 ∨ (q / 8 = 4 ∧ k < 0)) by bdd_omega)]
      by_cases e3 : q = 33
      · rw [ifn (show ¬ q = 135 by bdd_omega), ifp e3, ifp e3]
      · rw [ifn e3, ifn e3]

/-! ## The setup -/

theorem setup_eq (wl : Nat) : setup wl =
    Impl.Sha3.X86_64.X4.rcTable .rbx (wl + 50) ++ (zero wl ++ (sigLanes wl ++ (nonces wl ++ (pads wl ++ args wl)))) := by
  simp only [setup, List.append_assoc]

theorem args_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {s : State}
    (he : BEnv b wl o m s₀ s) :
    WP isa (.block (args wl)) s fun s' => (s'.mem = s.mem ∧ s'.gpr .rdi = sP b wl ∧
      s'.gpr .rsi = sP b wl + BitVec.ofNat 64 800 ∧ s'.gpr .rdx = sP b wl + BitVec.ofNat 64 1600 ∧
      s'.gpr .rcx = sP b wl + BitVec.ofNat 64 2368) ∧ Keep [.rdi, .rsi, .rdx, .rcx] s s' := by
  have := hp.small
  have e1 : b + BitVec.ofNat 64 (32 * (wl + 25)) = sP b wl + BitVec.ofNat 64 800 := at_w b (by bdd_omega)
  have e2 : b + BitVec.ofNat 64 (32 * (wl + 50)) = sP b wl + BitVec.ofNat 64 1600 := at_w b (by bdd_omega)
  have e3 : b + BitVec.ofNat 64 (32 * (wl + 74)) = sP b wl + BitVec.ofNat 64 2368 := at_w b (by bdd_omega)
  refine WP.keep _ ?_ (by kernel_rfl)
  unfold args
  xrun [he.rbx hp, sx_ofNat (show 32 * wl < 2 ^ 31 by bdd_omega), sx_ofNat (show 32 * (wl + 25) < 2 ^ 31 by bdd_omega),
    sx_ofNat (show 32 * (wl + 50) < 2 ^ 31 by bdd_omega), sx_ofNat (show 32 * (wl + 74) < 2 ^ 31 by bdd_omega), e1, e2, e3]

/-- After the setup: the table, the padded inputs, and the arguments of the permutation. -/
structure SetupPost (b : Addr) (wl o m N₀ : Nat) (s₀ s : State) : Prop where
  env : BEnv b wl o m s₀ s
  tbl : Tbl (sP b wl) 24 s.mem
  lanes : Lanes4 s.mem (sP b wl) fun k => P0 (sig b s₀) (BitVec.ofNat 8 (N₀ + k))
  rdi : s.gpr .rdi = sP b wl
  rsi : s.gpr .rsi = sP b wl + BitVec.ofNat 64 800
  rdx : s.gpr .rdx = sP b wl + BitVec.ofNat 64 1600
  rcx : s.gpr .rcx = sP b wl + BitVec.ofNat 64 2368

theorem setup_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {N₀ : Nat} (hN : N₀ + 4 ≤ 256)
    (h9 : s₀.gpr .r9 = BitVec.ofNat 64 N₀) :
    WP isa (.block (setup wl)) s₀ (SetupPost b wl o m N₀ s₀) := by
  rw [setup_eq, WP.block_append_iff]
  refine WP.mono (rc_ok hp (BEnv.refl (b := b) (wl := wl) (o := o) (m := m) (s₀ := s₀))) fun s₁ ⟨e₁, t₁⟩ => ?_
  have a₁ : AI b wl o m s₀ s₁.mem s₁ := ⟨e₁, Frame.refl _ _⟩
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok hp a₁) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sigLanes_ok hp h₂) fun s₃ h₃ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nonces_ok hp hN ((h₃.1.env.cs .r9 (by decide)).trans h9) h₃) fun s₄ h₄ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pads_ok hp h₄) fun s₅ ⟨a₅, b₅⟩ => ?_
  refine WP.mono (args_ok hp a₅.env) fun s₆ ⟨⟨hm, hdi, hsi, hdx, hcx⟩, k⟩ => ?_
  refine ⟨⟨k.2.1.trans a₅.env.rd, k.2.2.trans a₅.env.wr,
      fun r hr => (k.gpr (by revert hr; decide +revert)).trans (a₅.env.cs r hr), by rw [hm]; exact a₅.env.frame⟩,
    fun r hr j hj => ?_, ?_, hdi, hsi, hdx, hcx⟩
  · rw [hm, a₅.fr.readW (Region.contains_self _ _) (by
      simpa using Offset.disjoint_base (sP b wl) (k := 800) (d := 32 * (50 + r) + 8 * j) (n := 8) (by bdd_omega)
        (by bdd_omega)) (by decide)]
    exact t₁ r hr j hj
  · rw [hm]
    exact lanes4_of_bytes fun k hk q hq => by rw [b₅ k hk q hq, byteOf_P0 (sig_length b s₀) _ hq]

/-! ## The permutation -/

theorem perm_ok {fast : Bool} {b : Addr} {wl o m N₀ : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {s : State}
    (h : SetupPost b wl o m N₀ s₀ s) :
    WP isa (Impl.Sha3.X86_64.X4.permute4 fast) s fun s' => BEnv b wl o m s₀ s' ∧
      Lanes4 s'.mem (sP b wl) fun k => keccakF (P0 (sig b s₀) (BitVec.ofNat 8 (N₀ + k))) := by
  have := hp.small
  have pre : Pre4 s (sP b wl) (sP b wl + BitVec.ofNat 64 800) (sP b wl + BitVec.ofNat 64 1600) :=
    ⟨fun i _ => in_w hp h.env (by bdd_omega),
      fun i _ => by rw [Offset.add_add]; exact in_w hp h.env (by bdd_omega),
      fun r _ => by rw [Offset.add_add]; exact in_w' hp h.env (by bdd_omega),
      Offset.base_disjoint _ (by bdd_omega) (by bdd_omega),
      Offset.base_disjoint _ (by bdd_omega) (by bdd_omega),
      Offset.disjoint _ (by bdd_omega) (by bdd_omega) (by bdd_omega),
      fun r hr k hk => by
        rw [la, Offset.add_add, show 1600 + (32 * r + 8 * k) = 32 * (50 + r) + 8 * k by bdd_omega]
        exact h.tbl r hr k hk⟩
  refine WP.mono (permute4_ok (fast := fast) pre h.rdi h.rsi h.rdx (by rw [h.rcx, Offset.add_add (sP b wl) 1600 768]) h.lanes)
    fun s' ⟨hl, hf, hrd, hwr, _, hg⟩ => ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, fun r hr => ?_,
      h.env.frame.trans (hf.sub fun r hr => ⟨wR b wl, by simp, ?_⟩)⟩, hl⟩
  · rw [hg r (rax_ncs r hr) (by revert hr; decide +revert)]; exact h.env.cs r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by bdd_omega)
    · exact Offset.sub_base _ (by bdd_omega)

/-! ## The outputs -/

/-- During the copies: the first `I` lanes of state `K` copied, and all of the states before it. -/
structure EXI (b : Addr) (wl o m : Nat) (s₀ : State) (L : Nat → Spec.Sha3.State) (K I : Nat) (s : State) : Prop where
  env : BEnv b wl o m s₀ s
  r8 : s.gpr .r8 = b + BitVec.ofNat 64 o
  lanes : Lanes4 s.mem (sP b wl) L
  out : ∀ k < m, ∀ j < 128, (k < K ∨ (k = K ∧ j < 8 * I)) →
    s.mem (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * k + j)) = byteOf (L k) j

theorem ext_step {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {L : Nat → Spec.Sha3.State}
    {K I : Nat} (hK : K < m) (hI : I < 16) {s : State} (h : EXI b wl o m s₀ L K I s) :
    WP isa (.block [.mov .rax (.mem (at_ .rbx (32 * (wl + I) + 8 * K))),
      .store (at_ .r8 (128 * K + 8 * I)) .rax]) s (EXI b wl o m s₀ L K (I + 1)) := by
  have := hp.small
  have hm4 := hp.hm
  refine wp_movm (a := la (sP b wl) I K) (by rw [ea_at, h.env.rbx hp, la]; exact at_w b (by bdd_omega))
    (in_w' hp h.env (by bdd_omega)) fun s₁ u₁ => wp_store (a := b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * K + 8 * I))
      (by rw [ea_at, u₁.other _ (by decide), h.r8])
      (by rw [u₁.wr]; exact in_o hp h.env (by bdd_omega)) fun s₂ g₂ m₂ r₂ w₂ => wp_nil ?_
  have hm : s₂.mem = s.mem.writeW (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * K + 8 * I))
      (s.mem.readW (la (sP b wl) I K) 64) := by rw [m₂, u₁.mem, u₁.gpr]
  refine ⟨h.env.writeO hp (n := 8) (by bdd_omega) hm (r₂.trans u₁.rd) (w₂.trans u₁.wr)
      fun r hr => by rw [g₂, u₁.other r (rax_ncs r hr)], by rw [g₂, u₁.other _ (by decide)]; exact h.r8,
      fun i hi k hk => ?_, fun k hk j hj hc => ?_⟩
  · rw [hm, Mem.readW_writeW_sep (((hp.dWO.sub_left (Offset.sub_base (sP b wl) (d := 32 * i + 8 * k) (n := 8)
      (k := 2368) (by bdd_omega))).sub_right (Offset.sub_base (b + BitVec.ofNat 64 o) (d := 128 * K + 8 * I) (n := 8)
      (k := 128 * m) (by bdd_omega))).sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
    exact h.lanes i hi k hk
  · rw [hm]
    by_cases hw : k = K ∧ 8 * I ≤ j ∧ j < 8 * I + 8
    · obtain ⟨rfl, h₁, h₂⟩ := hw
      rw [wb_in _ _ _ (by bdd_omega) (by bdd_omega) (by decide),
        show 8 * (128 * k + j - (128 * k + 8 * I)) = 8 * (j - 8 * I) by bdd_omega,
        byte_readW _ _ (by bdd_omega), la_byte _ (by bdd_omega), byte_of_lanes4 h.lanes (by bdd_omega) (by bdd_omega),
        show 8 * I + (j - 8 * I) = j by bdd_omega]
    · rw [wb_out _ _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega)]
      exact h.out k hk j hj (by bdd_omega)

theorem extract_eq (m wl : Nat) : extract m wl = (List.range m).flatMap fun K => (List.range 16).flatMap fun I =>
    [.mov .rax (.mem (at_ .rbx (32 * (wl + I) + 8 * K))), .store (at_ .r8 (128 * K + 8 * I)) .rax] := rfl

theorem extract_ok {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {L : Nat → Spec.Sha3.State}
    {s : State} (he : BEnv b wl o m s₀ s) (h8 : s.gpr .r8 = b + BitVec.ofNat 64 o) (hl : Lanes4 s.mem (sP b wl) L) :
    WP isa (.block (extract m wl)) s fun s' => BEnv b wl o m s₀ s' ∧
      ∀ k < m, ∀ j < 128, s'.mem (b + BitVec.ofNat 64 o + BitVec.ofNat 64 (128 * k + j)) = byteOf (L k) j := by
  rw [extract_eq]
  refine WP.mono (wp_range_flatMap (M := isa) (fun K s => EXI b wl o m s₀ L K 0 s) (fun K s hK h => ?_) m
    (Nat.le_refl _) s ⟨he, h8, hl, fun _ _ _ _ hc => absurd hc (by bdd_omega)⟩)
    fun s' h' => ⟨h'.env, fun k hk j hj => h'.out k hk j hj (by bdd_omega)⟩
  exact WP.mono (wp_range_flatMap (M := isa) (fun I s => EXI b wl o m s₀ L K I s)
    (fun I s hI h => ext_step hp hK hI h) 16 (Nat.le_refl _) s h)
    fun s' h' => ⟨h'.env, h'.r8, h'.lanes, fun k hk j hj hc => h'.out k hk j hj (by bdd_omega)⟩

/-! ## The whole -/

/-- `batch m wl`, with `scratch + o` in `r8` and `N₀` in `r9`: `PRF₂(σ, N₀ + k)`
to `scratch + o + 128 k` for each `k < m`. -/
theorem batch_ok {fast : Bool} {b : Addr} {wl o m : Nat} {s₀ : State} (hp : BPre b wl o m s₀) {N₀ : Nat} (hN : N₀ + 4 ≤ 256)
    (h8 : s₀.gpr .r8 = b + BitVec.ofNat 64 o) (h9 : s₀.gpr .r9 = BitVec.ofNat 64 N₀) :
    WP isa (batch m wl fast) s₀ fun s => BEnv b wl o m s₀ s ∧
      ∀ k < m, bytesAt s.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 = prf 2 (sig b s₀) (BitVec.ofNat 8 (N₀ + k)) := by
  unfold batch
  refine WP.seq (WP.mono (setup_ok hp hN h9) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (perm_ok (fast := fast) hp h₁) fun s₂ ⟨e₂, l₂⟩ => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (extract_ok hp e₂ ((e₂.cs .r8 (by decide)).trans h8) l₂) fun s₃ ⟨e₃, o₃⟩ => WP.mono (vz_ok s₃) fun s₄ ⟨hm, k⟩ =>
    ⟨⟨k.2.1.trans e₃.rd, k.2.2.trans e₃.wr, fun r hr => (k.gpr List.not_mem_nil).trans (e₃.cs r hr),
      by rw [hm]; exact e₃.frame⟩, fun k hk => ?_⟩
  rw [hm]
  refine bytes_prf (sig_length b s₀) fun j hj => ?_
  have e := o₃ k hk j hj
  rw [Offset.add_add, ← Nat.add_assoc] at e
  rw [Offset.add_add]
  exact e

/-! ## Constant time -/

/-- `batch` leaks only the addresses in `rbx` and `r8`: the immediates (the
offsets) are the same in every run, and no address or branch depends on the
data. -/
theorem batch_tr {fast : Bool} {P : State → State → Prop}
    (hP : ∀ x y, P x y → ∀ r ∈ [Reg.rbx, .r8, .r9], x.gpr r = y.gpr r) (wl : Nat)
    {m : Nat} (hm : m ≤ 4) : RelCT isa P (batch m wl fast) fun x y => ∀ r ∈ [Reg.rbx, .r8, .r9], x.gpr r = y.gpr r := by
  cases fast <;> (
    have hx : ((taint.check (X86_64.Taint.ofRegs [.rbx, .r8, .r9]) (.block (extract m wl ++ ([.vop .vzeroupper] : List Instr)))
        (.block [])).map fun τ' => (RegSet.ofList [Reg.rbx, .r8, .r9]).subset τ'.regs) = some true := by
      rcases (by bdd_omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl | rfl <;> kernel_rfl
    unfold batch
    refine RelCT.seq (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .r8, .r9])
      (fun x y h => X86_64.Taint.agree_ofRegs (hP x y h)) [.rbx, .r8, .r9, .rdi, .rsi, .rdx, .rcx]
      (hc := .block []) (by kernel_rfl)) ?_
    refine RelCT.seq (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .r8, .r9, .rdi, .rsi, .rdx, .rcx])
      (fun x y h => X86_64.Taint.agree_ofRegs h) [.rbx, .r8, .r9] (by taint_decide)) ?_
    exact RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx, .r8, .r9]) (fun x y h => X86_64.Taint.agree_ofRegs h)
      [.rbx, .r8, .r9] hx
  )

end VG.Proof.MlKem.X86_64.Prf4

end

end

/-!
# ML-KEM on x86-64: several outputs of `PRF₂`

In a layout: `PRF₂(σ, N₀ + i)` to `scratch + o + 128 i` for each `i < n`, with
`σ` at `G + 32` (`PrfsPost`), one at a time (`prfsScalar_ok`, `prfsScalar_tr`)
or four at a time with AVX2, but for the first `prfsLead n`, one at a time
(`prfsAvx2_ok`, `prfsAvx2_tr`), whichever implementation of
`vg_mlkem_sample_ntt4` the top-level functions call goes with
(`Callee4.prfs`). Both write within `prfsW` and need what `prfsChk` checks of
the layout.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {rbs wbs : List (Reg × Nat)}

/-! ## Properties of every instruction, piece by piece -/

theorem ctlOk_seq {a b : Prog isa} (ha : ctlOk a = true) (hb : ctlOk b = true) : ctlOk (.seq a b) = true := by
  simp only [ctlOk, ha, hb, Bool.and_self, Bool.or_true]

theorem ctlOk_call {n : String} {c : Prog isa} (h : ctlOk c = true) : ctlOk (.call n c) = true := h

theorem all_call {p : Instr → Bool} {n : String} {c : Prog isa} (h : c.all p = true) :
    (Code.call n c : Prog isa).all p = true := h

theorem ctlOk_ite {c : Cond} {t e : Prog isa} (ht : ctlOk t = true) (he : ctlOk e = true) :
    ctlOk (.ite c t e) = true := by
  simp only [ctlOk, ht, he, Bool.and_self]

theorem all_ite {p : Instr → Bool} {c : Cond} {t e : Prog isa} (ht : t.all p = true) (he : e.all p = true) :
    (Code.ite c t e : Prog isa).all p = true := by
  simp only [Code.all, ht, he, Bool.and_self]

theorem ctlOk_loop {c : Cond} {b : Prog isa} (h : ctlOk b = true) : ctlOk (.loop b c) = true := h

theorem all_loop {p : Instr → Bool} {c : Cond} {b : Prog isa} (h : b.all p = true) :
    (Code.loop b c : Prog isa).all p = true := h

theorem all_seq {p : Instr → Bool} {a b : Prog isa} (ha : a.all p = true) (hb : b.all p = true) :
    (Code.seq a b : Prog isa).all p = true := by
  simp only [Code.all, ha, hb, Bool.and_self]

/-! ## What a piece writes, weakened -/

/-- `PPost` for larger regions. -/
theorem PPost.weaken {s s' : State} {ws ws' : List (Ptr × Nat)} (h : PPost s s' ws)
    (hs : ∀ w ∈ ws, ∃ w' ∈ ws', Region.Sub (toR s w) (toR s w')) : PPost s s' ws' :=
  ⟨h.rd, h.wr, h.cs, h.frame.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
      obtain ⟨w', hw', hsub⟩ := hs w hw
      exact ⟨toR s w', List.mem_append_left _ (List.mem_map_of_mem hw'), hsub⟩
    · exact ⟨r, List.mem_append_right _ hr, fun _ h => h⟩⟩

/-! ## One output -/

/-- What `prf1 N out` writes. -/
abbrev prf1W (out : Ptr) : List (Ptr × Nat) := [(sc oNB, 1), (sc 0, 200), (sc 200, 640), (out, 128)]

def prf1Chk (bs wbs : List (Reg × Nat)) (out : Ptr) : Bool :=
  inB bs (sc oNB) 1 && inB wbs (sc oNB) 1 && hashChk bs wbs [(sigP, 32), (sc oNB, 1)] 136 out 128 &&
    keepB bs [(sc oNB, 1)] sigP 32

theorem prf1Chk_spec {bs wbs : List (Reg × Nat)} {out : Ptr} (h : prf1Chk bs wbs out = true) :
    inB bs (sc oNB) 1 = true ∧ inB wbs (sc oNB) 1 = true ∧
      hashChk bs wbs [(sigP, 32), (sc oNB, 1)] 136 out 128 = true ∧ keepB bs [(sc oNB, 1)] sigP 32 = true := by
  simp only [prf1Chk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  exact ⟨h0, h1, h2, h3⟩

theorem prf1_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N : Nat} (hN : N < 256)
    {out : Ptr} (hc : prf1Chk (rbs ++ wbs) wbs out = true) :
    WP isa (prf1 N out) s fun s' => PPost s s' (prf1W out) ∧
      bytesAt s'.mem (pa s out) 128 = prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 N) := by
  obtain ⟨_, hNB, hh, hk⟩ := prf1Chk_spec hc
  have hocs : out.1 ∈ calleeSaved := (hashChk_spec hh).2.2.2.2.2
  unfold prf1
  refine WP.seq (WP.mono (setB_okL L (by decide) hN hNB) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (hash_ok hcs hh (by decide) L₁) fun s₂ ⟨hP₂, ho₂⟩ =>
    ⟨PPost.app hP₁ hP₂ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro w (rfl | rfl | rfl) <;>
      first | decide | exact hocs), ?_⟩
  have e1 : pa s₁ (sc oNB) = pa s (sc oNB) := hP₁.pa rbx_cs
  have eo : pa s₁ out = pa s out := hP₁.pa hocs
  have hσ : bytesAt s₁.mem (pa s₁ sigP) 32 = bytesAt s.mem (pa s sigP) 32 := L.keepBytes hP₁.b hk
  rw [← eo, ho₂, prf_pieces (by rw [e1]; exact hb₁), hσ, shake31]
  exact (prf_eq 2 _ _).symm

theorem setNB_taint (N : Nat) :
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc oNB) N)) (.block [])).isSome = true := by
  kernel_rfl

theorem prf1_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N : Nat} (hN : N < 256) {out : Ptr}
    (hc : prf1Chk (rbs ++ wbs) wbs out = true) : RelCT isa (LRel rbs wbs) (prf1 N out) (LRel rbs wbs) := by
  obtain ⟨hin, hNB, hh, _⟩ := prf1Chk_spec hc
  unfold prf1
  exact RelCT.seq (LRel.step hcs (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.eq hin) (setNB_taint N))
    fun x Lx => WP.mono (setB_okL Lx (by decide) hN hNB) fun _ h => ⟨_, h.1⟩)
    (LRel.step hcs (hash_tr hcs hh (by decide)) fun x Lx => WP.mono (hash_ok hcs hh (by decide) Lx) fun _ h => ⟨_, h.1⟩)

theorem prf1_ctl (N : Nat) (out : Ptr) : ctlOk (prf1 N out) = true := by kernel_rfl

theorem prf1_sp (N : Nat) (out : Ptr) : (prf1 N out).all (fun i => !isa.writesSp i) = true := by kernel_rfl

/-- Its calls use 16 bytes of stack. -/
theorem prf1_xd (N : Nat) (out : Ptr) : (prf1 N out).x86_64Depth ≤ 16 :=
  Nat.le_of_ble_eq_true (by kernel_rfl)

/-! ## Several outputs -/

/-- What `prfs N₀ n o wl` writes, of either implementation: the index `N`,
the Keccak state and the sponge functions' working space, 2368 bytes of
working space from lane `wl`, and the outputs. -/
abbrev prfsW (n o wl : Nat) : List (Ptr × Nat) :=
  [(sc oNB, 1), (sc 0, 200), (sc 200, 640), (sc (32 * wl), 2368), (sc o, 128 * n)]

/-- What `prfs N₀ n o wl` needs of the layout, of either implementation:
for each output, what computing it on its own needs, and that this keeps `σ`
and the outputs before it; and that the working space, the outputs and `σ`
are apart. -/
def prfsChk (bs wbs : List (Reg × Nat)) (n o wl : Nat) : Bool :=
  (List.range n).all (fun i => prf1Chk bs wbs (sc (o + 128 * i)) && keepB bs (prf1W (sc (o + 128 * i))) sigP 32 &&
    (List.range i).all fun j => keepB bs (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128) &&
  wrOk bs wbs (sc (32 * wl)) 2368 && wrOk bs wbs (sc o) (128 * n) && rdOk bs sigP 32 &&
  sepB bs (sc (32 * wl)) 2368 (sc o) (128 * n) && sepB bs (sc (32 * wl)) 2368 sigP 32 &&
  sepB bs (sc o) (128 * n) sigP 32 && decide (32 * wl + 2368 < 2 ^ 31) && decide (o + 128 * n < 2 ^ 31)

theorem prfsChk_spec {bs wbs : List (Reg × Nat)} {n o wl : Nat} (h : prfsChk bs wbs n o wl = true) :
    (∀ i < n, prf1Chk bs wbs (sc (o + 128 * i)) = true ∧ keepB bs (prf1W (sc (o + 128 * i))) sigP 32 = true ∧
      ∀ j < i, keepB bs (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128 = true) ∧
    wrOk bs wbs (sc (32 * wl)) 2368 = true ∧ wrOk bs wbs (sc o) (128 * n) = true ∧ rdOk bs sigP 32 = true ∧
    sepB bs (sc (32 * wl)) 2368 (sc o) (128 * n) = true ∧ sepB bs (sc (32 * wl)) 2368 sigP 32 = true ∧
    sepB bs (sc o) (128 * n) sigP 32 = true ∧ 32 * wl + 2368 < 2 ^ 31 ∧ o + 128 * n < 2 ^ 31 := by
  simp only [prfsChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨fun i hi => ⟨(h0 i hi).1.1, (h0 i hi).1.2, (h0 i hi).2⟩, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- What `prfs N₀ n o wl` leaves, from `s`. -/
def PrfsPost (s : State) (N₀ n o wl : Nat) (s' : State) : Prop :=
  PPost s s' (prfsW n o wl) ∧
    ∀ i < n, bytesAt s'.mem (pa s (sc (o + 128 * i))) 128 =
      prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 (N₀ + i))

/-! ## One at a time -/

/-- Output `i` lies within the outputs. -/
theorem out_sub (s : State) {n o i : Nat} (hi : i < n) :
    Region.Sub (toR s (sc (o + 128 * i), 128)) (toR s (sc o, 128 * n)) :=
  show Region.Sub ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩ ⟨s.gpr .rbx + BitVec.ofNat 64 o, 128 * n⟩ from
    Offset.sub _ (by omega_arith) (by omega_arith)

/-- After the first `k` outputs. -/
structure ScInv (s : State) (N₀ n o wl k : Nat) (s' : State) : Prop where
  post : PPost s s' (prfsW n o wl)
  sig : bytesAt s'.mem (pa s' sigP) 32 = bytesAt s.mem (pa s sigP) 32
  outs : ∀ j < k, bytesAt s'.mem (pa s (sc (o + 128 * j))) 128 =
    prf 2 (bytesAt s.mem (pa s sigP) 32) (BitVec.ofNat 8 (N₀ + j))

/-- The first `r` of `n` outputs, one at a time. -/
theorem prfsScalar_lead {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ r n o wl : Nat}
    (hN : N₀ + r ≤ 256) (hr : r ≤ n)
    (hs : ∀ i < r, prf1Chk (rbs ++ wbs) wbs (sc (o + 128 * i)) = true ∧
      keepB (rbs ++ wbs) (prf1W (sc (o + 128 * i))) sigP 32 = true ∧
      ∀ j < i, keepB (rbs ++ wbs) (prf1W (sc (o + 128 * i))) (sc (o + 128 * j)) 128 = true) :
    WP isa (prfsScalar N₀ r o wl) s (ScInv s N₀ n o wl r) := by
  have h := seqR_ok (f := fun i => prf1 (N₀ + i) (sc (o + 128 * i))) (I := ScInv s N₀ n o wl) r 0
    (fun k _ hk s₁ h₁ => by
      obtain ⟨c1, cs, cj⟩ := hs k (by omega_arith)
      have L₁ := L.post h₁.post.b hcs
      refine WP.mono (prf1_ok L₁ hcs (by omega_arith) c1) fun s₂ ⟨hP, hb⟩ => ?_
      have e₁ : ∀ x, pa s₁ (sc x) = pa s (sc x) := fun x => h₁.post.pa rbx_cs
      refine ⟨PPost.trans h₁.post (hP.weaken fun w hw => ?_) (fun w hw => by
          simp only [prfsW, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact rbx_cs) (fun w hw => hw) (fun w hw => hw),
        by rw [L₁.keepBytes hP.b cs]; exact h₁.sig, fun j hj => ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
        · exact ⟨_, by simp, out_sub s₁ (o := o) (show k < n by omega_arith)⟩
      · rcases (by omega_arith : j < k ∨ j = k) with hj | rfl
        · rw [← e₁, ← hP.pa rbx_cs, L₁.keepBytes hP.b (cj j hj), e₁]; exact h₁.outs j hj
        · rw [← e₁, hb, h₁.sig])
    s ⟨Post.refl _ _, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact WP.mono h fun s' h' => by rwa [Nat.zero_add] at h'

theorem prfsScalar_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat}
    (hN : N₀ + n + 4 ≤ 256) (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    WP isa (prfsScalar N₀ n o wl) s (PrfsPost s N₀ n o wl) :=
  WP.mono (prfsScalar_lead L hcs (by omega_arith) (Nat.le_refl n) (prfsChk_spec hc).1) fun _ h' => ⟨h'.post, h'.outs⟩

theorem prfsScalar_trL (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ r o wl : Nat} (hN : N₀ + r ≤ 256)
    (hs : ∀ i < r, prf1Chk (rbs ++ wbs) wbs (sc (o + 128 * i)) = true) :
    RelCT isa (LRel rbs wbs) (prfsScalar N₀ r o wl) (LRel rbs wbs) := by
  have := seqR_tr (f := fun i => prf1 (N₀ + i) (sc (o + 128 * i))) (R := fun _ => LRel rbs wbs) r 0 fun k _ hk =>
    prf1_tr hcs (by omega_arith) (hs k (by omega_arith))
  exact this

theorem prfsScalar_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat} (hN : N₀ + n + 4 ≤ 256)
    (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    RelCT isa (LRel rbs wbs) (prfsScalar N₀ n o wl) fun _ _ => True :=
  RelCT.mono (prfsScalar_trL hcs (by omega_arith) fun i hi => ((prfsChk_spec hc).1 i hi).1) (fun _ _ h => h)
    fun _ _ _ => trivial

theorem ctlOk_seqR {f : Nat → Prog isa} (h : ∀ k, ctlOk (f k) = true) : ∀ n a, ctlOk (seqR f a n) = true
  | 0, _ => rfl
  | n + 1, a => ctlOk_seq (h a) (ctlOk_seqR h n (a + 1))

theorem all_seqR {p : Instr → Bool} {f : Nat → Prog isa} (h : ∀ k, (f k).all p = true) :
    ∀ n a, (seqR f a n).all p = true
  | 0, _ => rfl
  | n + 1, a => all_seq (h a) (all_seqR h n (a + 1))

theorem xd_seq {a b : Prog isa} {k : Nat} (ha : a.x86_64Depth ≤ k) (hb : b.x86_64Depth ≤ k) :
    (Code.seq a b).x86_64Depth ≤ k :=
  Nat.max_le.2 ⟨ha, hb⟩

theorem xd_seqR {f : Nat → Prog isa} {k : Nat} (h : ∀ i, (f i).x86_64Depth ≤ k) :
    ∀ n a, (seqR f a n).x86_64Depth ≤ k
  | 0, _ => Nat.zero_le _
  | n + 1, a => xd_seq (h a) (xd_seqR h n (a + 1))

theorem prfsScalar_ctl (N₀ n o wl : Nat) : ctlOk (prfsScalar N₀ n o wl) = true :=
  ctlOk_seqR (fun _ => prf1_ctl _ _) n 0

theorem prfsScalar_sp (N₀ n o wl : Nat) : (prfsScalar N₀ n o wl).all (fun i => !isa.writesSp i) = true :=
  all_seqR (fun _ => prf1_sp _ _) n 0

theorem prfsScalar_xd (N₀ n o wl : Nat) : (prfsScalar N₀ n o wl).x86_64Depth ≤ 16 :=
  xd_seqR (fun _ => prf1_xd _ _) n 0

/-! ## Four at a time -/

namespace Prf4

open VG.Impl.MlKem.X86_64.Prf4

/-- What `prfsX4 N₀ n o wl` needs, with `scratch` at `b`. -/
structure RawPre (b : Addr) (n o wl : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = b
  w : InRegions s.wr (sP b wl) 2368
  out : InRegions s.wr (b + BitVec.ofNat 64 o) (128 * n)
  sig : InRegions (s.rd ++ s.wr) (sS b) 32
  dWO : (wR b wl).Disjoint (oR b o n)
  dWS : (wR b wl).Disjoint (sR b)
  dOS : (oR b o n).Disjoint (sR b)
  small : 32 * wl + 2368 < 2 ^ 31
  so : o + 128 * n < 2 ^ 31

theorem lt64 {a o : Nat} (h : o + a < 2 ^ 32) : a < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_trans h (by decide))

theorem RawPre.bpre {b : Addr} {n o wl : Nat} {s : State} (h : RawPre b n o wl s) {m : Nat} (hm : m ≤ 4)
    (hmn : m ≤ n) : BPre b wl o m s := by
  have hs : Region.Sub (oR b o m) (oR b o n) := Region.sub_prefix (by omega_arith)
  refine ⟨h.rbx, h.w, ?_, h.sig, h.dWO.sub_right hs, h.dWS, h.dOS.sub_left hs, hm, h.small⟩
  have := inRegions_sub h.out (off := 0) (l := 128 * m) (by omega_arith) (lt64 (o := o) (a := 128 * n) (by have := h.so; omega_arith))
  rwa [add_ofNat_zero] at this

/-- Between the pieces of `prfsX4`, from `s₀`: `BEnv` but for `r8`–`r10`,
which hold the loop's pointer, index and count. -/
structure XEnv (b : Addr) (wl o n : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cs : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  frame : Frame [wR b wl, oR b o n] s₀.mem s.mem

theorem XEnv.refl {b : Addr} {wl o n : Nat} {s : State} : XEnv b wl o n s s :=
  ⟨rfl, rfl, fun _ _ => rfl, Frame.refl _ _⟩

theorem XEnv.keep {b : Addr} {wl o n : Nat} {s₀ s s' : State} (h : XEnv b wl o n s₀ s) (hm : s'.mem = s.mem)
    {rs : List Reg} (k : Keep rs s s') (hrs : ∀ r ∈ calleeSaved, r ∉ rs) : XEnv b wl o n s₀ s' :=
  ⟨k.2.1.trans h.rd, k.2.2.trans h.wr, fun r hr => (k.gpr (hrs r hr)).trans (h.cs r hr), by rw [hm]; exact h.frame⟩

/-- `XEnv` after a batch writing outputs `d, …, d + m - 1` of `n`. -/
theorem XEnv.batch {b : Addr} {wl o n d m : Nat} {s₀ s s' : State} (h : XEnv b wl o n s₀ s)
    (e : BEnv b wl (o + 128 * d) m s s') (hs : d + m ≤ n) : XEnv b wl o n s₀ s' := by
  have hsub : Region.Sub (oR b (o + 128 * d) m) (oR b o n) := Offset.sub _ (by omega_arith) (by omega_arith)
  refine ⟨e.rd.trans h.rd, e.wr.trans h.wr, fun r hr => (e.cs r (List.mem_append_left _ hr)).trans (h.cs r hr),
    h.frame.trans (e.frame.sub fun r hr => ?_)⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), hsub⟩

/-- What a part of `prfsX4` needs: `RawPre` for outputs `d, …, d + m - 1`
of `n`. -/
theorem RawPre.shift {b : Addr} {n o wl : Nat} {s₀ s : State} (h : RawPre b n o wl s₀) (he : XEnv b wl o n s₀ s)
    {d m : Nat} (hle : d + m ≤ n) : RawPre b m (o + 128 * d) wl s := by
  have so := h.so
  have hsub : Region.Sub (oR b (o + 128 * d) m) (oR b o n) := Offset.sub _ (by omega_arith) (by omega_arith)
  refine ⟨(he.cs .rbx (by decide)).trans h.rbx, by rw [he.wr]; exact h.w, ?_, by rw [he.rd, he.wr]; exact h.sig,
    h.dWO.sub_right hsub, h.dWS, h.dOS.sub_left hsub, h.small, by omega_arith⟩
  have := inRegions_sub h.out (off := 128 * d) (l := 128 * m) (by omega_arith) (lt64 (o := o) (a := 128 * n) (by omega_arith))
  rw [he.wr, ← Offset.add_add]; exact this

theorem XEnv.sig {b : Addr} {n o wl : Nat} {s₀ s : State} (h : RawPre b n o wl s₀) (he : XEnv b wl o n s₀ s) :
    sig b s = sig b s₀ :=
  bytesAt_frame he.frame (by simpa using ⟨h.dWS.symm, h.dOS.symm⟩) (by decide)

/-- An output written before a batch of outputs `d, …, d + m - 1`, and not by it. -/
theorem out_kept {b : Addr} {n o wl : Nat} {s₀ s s' : State} (h : RawPre b n o wl s₀) {d m k : Nat}
    (e : BEnv b wl (o + 128 * d) m s s') (hs : d + m ≤ n) (hk : k < d) :
    bytesAt s'.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 = bytesAt s.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 := by
  have so := h.so
  have hk' : Region.Sub ⟨b + BitVec.ofNat 64 (o + 128 * k), 128⟩ (oR b o n) := Offset.sub _ (by omega_arith) (by omega_arith)
  have hd : Region.Disjoint ⟨b + BitVec.ofNat 64 (o + 128 * k), 128⟩ (oR b (o + 128 * d) m) :=
    Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  exact bytesAt_frame e.frame (by simpa using ⟨(h.dWO.sub_right hk').symm, hd⟩) (by decide)

theorem zx_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- `regs N₀ o`: `r8 := scratch + o`, `r9 := N₀`. -/
theorem regs_ok {b : Addr} {s : State} (hb : s.gpr .rbx = b) {N₀ o : Nat} (ho : o < 2 ^ 31) (hN : N₀ < 2 ^ 31) :
    WP isa (.block (regs N₀ o)) s fun s' => (s'.gpr .r8 = b + BitVec.ofNat 64 o ∧
      s'.gpr .r9 = BitVec.ofNat 64 N₀ ∧ s'.mem = s.mem) ∧ Keep [.r8, .r9] s s' :=
  WP.keep _ (by unfold regs; xrun [hb, sx_ofNat ho, zx_ofNat (show N₀ < 2 ^ 32 by omega_arith)]) rfl

/-- After `i` batches of four of `quads N₀ q o wl`, from `s₀`. -/
structure QInv (b : Addr) (wl N₀ q o : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  env : XEnv b wl o (4 * q) s₀ s
  r8 : s.gpr .r8 = b + BitVec.ofNat 64 (o + 128 * (4 * i))
  r9 : s.gpr .r9 = BitVec.ofNat 64 (N₀ + 4 * i)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (q - i)
  out : ∀ k < 4 * i, bytesAt s.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
    prf 2 (sig b s₀) (BitVec.ofNat 8 (N₀ + k))

theorem quads_ok {fast : Bool} {b : Addr} {wl N₀ q o : Nat} {s : State} (h : RawPre b (4 * q) o wl s)
    (hq : 0 < q) (hN : N₀ + 4 * q + 4 ≤ 256) :
    WP isa (quads N₀ q o wl fast) s fun s' => XEnv b wl o (4 * q) s s' ∧
      ∀ k < 4 * q, bytesAt s'.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
        prf 2 (sig b s) (BitVec.ofNat 8 (N₀ + k)) := by
  have so := h.so
  unfold quads
  refine WP.seq (WP.mono (show WP isa (.block (regs N₀ o ++ ([.mov32 .r10 (.imm (BitVec.ofNat 32 q))] : List Instr))) s
    (QInv b wl N₀ q o s 0) from ?_) fun t h0 => ?_)
  · rw [WP.block_append_iff]
    refine WP.mono (regs_ok h.rbx (N₀ := N₀) (o := o) (by omega_arith) (by omega_arith)) fun s₁ ⟨⟨h8, h9, hm₁⟩, k₁⟩ => ?_
    refine WP.mono (WP.keep [.r10] (Q := fun s₂ => s₂.gpr .r10 = BitVec.ofNat 64 q ∧ s₂.mem = s₁.mem)
      (by xrun [zx_ofNat (show q < 2 ^ 32 by omega_arith)]) rfl) fun s₂ ⟨⟨h10, hm₂⟩, k₂⟩ => ?_
    refine ⟨(XEnv.refl.keep hm₁ k₁ (by decide)).keep hm₂ k₂ (by decide), ?_, ?_, by rw [h10, Nat.sub_zero],
      fun k hk => absurd hk (by omega_arith)⟩
    · rw [k₂.gpr (by decide), h8]; simp only [Nat.mul_zero, Nat.add_zero]
    · rw [k₂.gpr (by decide), h9]; simp only [Nat.mul_zero, Nat.add_zero]
  refine VG.Proof.Bignum.X86_64.wp_upto (a := 0) (N := q) hq (QInv b wl N₀ q o s) (fun i _ hi t hI => ?_)
    (fun t hI => ⟨hI.env, hI.out⟩) h0
  have raw := h.shift hI.env (d := 4 * i) (m := 4) (by omega_arith)
  have hsig := XEnv.sig h hI.env
  refine WP.seq (WP.mono (batch_ok (fast := fast) (raw.bpre (by decide) (by decide)) (N₀ := N₀ + 4 * i) (by omega_arith)
    hI.r8 hI.r9) fun t₁ ⟨e₁, r₁⟩ => ?_)
  have h8 : t₁.gpr .r8 = b + BitVec.ofNat 64 (o + 128 * (4 * i)) := (e₁.cs .r8 (by decide)).trans hI.r8
  have h9 : t₁.gpr .r9 = BitVec.ofNat 64 (N₀ + 4 * i) := (e₁.cs .r9 (by decide)).trans hI.r9
  have h10 : t₁.gpr .r10 = BitVec.ofNat 64 (q - i) := (e₁.cs .r10 (by decide)).trans hI.r10
  have env₁ := hI.env.batch e₁ (by omega_arith)
  refine WP.mono (WP.keep [.r8, .r9, .r10] (Q := fun t₂ => (t₂.gpr .r8 = b + BitVec.ofNat 64 (o + 128 * (4 * (i + 1))) ∧
      t₂.gpr .r9 = BitVec.ofNat 64 (N₀ + 4 * (i + 1)) ∧ t₂.gpr .r10 = BitVec.ofNat 64 (q - (i + 1)) ∧
      t₂.zf = some (decide (i + 1 = q))) ∧ t₂.mem = t₁.mem) (by
    unfold next
    xrun [h8, h9, h10]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show BitVec.signExtend 64 (512 : BitVec 32) = BitVec.ofNat 64 512 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        show o + 128 * (4 * i) + 512 = o + 128 * (4 * (i + 1)) by omega_arith]
    · rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat,
        show N₀ + 4 * i + 4 = N₀ + 4 * (i + 1) by omega_arith]
    · rw [ofNat64_pred (by omega_arith) (by omega_arith), show q - i - 1 = q - (i + 1) by omega_arith]
    · rw [ofNat64_pred (by omega_arith) (by omega_arith), ofNat64_beq_zero (by omega_arith)]
      exact decide_eq_decide.mpr (by omega_arith)) rfl) fun t₂ ⟨⟨⟨h8', h9', h10', hz⟩, hm⟩, k⟩ => ⟨hz, env₁.keep hm k (by decide), h8', h9', h10', fun k hk => ?_⟩
  rw [hm]
  rcases (by omega_arith : k < 4 * i ∨ 4 * i ≤ k) with hk' | hk'
  · rw [out_kept h e₁ (by omega_arith) hk']; exact hI.out k hk'
  · have := r₁ (k - 4 * i) (by omega_arith)
    rwa [hsig, show o + 128 * (4 * i) + 128 * (k - 4 * i) = o + 128 * k by omega_arith,
      show N₀ + 4 * i + (k - 4 * i) = N₀ + k by omega_arith] at this

/-- `prfsX4 N₀ n o wl`: `PRF₂(σ, N₀ + k)` to `scratch + o + 128 k` for each `k < n`. -/
theorem prfsX4_ok {fast : Bool} {b : Addr} {wl N₀ n o : Nat} {s : State} (h : RawPre b n o wl s)
    (hN : N₀ + n + 4 ≤ 256) :
    WP isa (prfsX4 fast N₀ n o wl) s fun s' => XEnv b wl o n s s' ∧
      ∀ k < n, bytesAt s'.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
        prf 2 (sig b s) (BitVec.ofNat 8 (N₀ + k)) := by
  have so := h.so
  have hn := Nat.div_add_mod n 4
  have hr := Nat.mod_lt n (show 0 < 4 by decide)
  unfold prfsX4
  generalize n / 4 = q at hn ⊢
  generalize n % 4 = r at hn hr ⊢
  subst hn
  -- The batches of four.
  refine WP.seq (WP.mono (show WP isa (if q = 0 then .block [] else quads N₀ q o wl fast) s (fun s₁ =>
      XEnv b wl o (4 * q + r) s s₁ ∧ ∀ k < 4 * q, bytesAt s₁.mem (b + BitVec.ofNat 64 (o + 128 * k)) 128 =
        prf 2 (sig b s) (BitVec.ofNat 8 (N₀ + k))) from ?_) fun s₁ ⟨e₁, o₁⟩ => ?_)
  · split
    · exact WP.block_nil ⟨XEnv.refl, fun k hk => absurd hk (by omega_arith)⟩
    · have h₀ := h.shift (s := s) XEnv.refl (d := 0) (m := 4 * q) (by omega_arith)
      rw [Nat.mul_zero, Nat.add_zero] at h₀
      refine WP.mono (quads_ok (fast := fast) h₀ (by omega_arith) (by omega_arith)) fun s₁ ⟨e₁, o₁⟩ =>
        ⟨⟨e₁.rd, e₁.wr, e₁.cs, e₁.frame.sub fun r' hr' => ?_⟩, o₁⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by omega_arith)⟩
  -- The last `r`.
  have hsig := XEnv.sig h e₁
  split
  · exact WP.block_nil ⟨e₁, fun k hk => o₁ k (by omega_arith)⟩
  · have raw := h.shift e₁ (d := 4 * q) (m := r) (by omega_arith)
    refine WP.seq (WP.mono (regs_ok raw.rbx (N₀ := N₀ + 4 * q) (o := o + 512 * q) (by omega_arith) (by omega_arith))
      fun s₂ ⟨⟨h8, h9, hm₂⟩, k₂⟩ => show WP isa (batch r wl fast) s₂ _ from ?_)
    · have raw₂ : RawPre b r (o + 128 * (4 * q)) wl s₂ := raw.shift (XEnv.refl.keep hm₂ k₂ (by decide)) (d := 0) (m := r)
        (by omega_arith) |> fun h => by rwa [Nat.mul_zero, Nat.add_zero] at h
      refine WP.mono (batch_ok (fast := fast) (raw₂.bpre (by omega_arith) (Nat.le_refl _)) (N₀ := N₀ + 4 * q) (by omega_arith)
        (by rw [h8]; congr 2; omega_arith) h9) fun s₃ ⟨e₃, r₃⟩ => ?_
      have e₂ := (e₁.keep hm₂ k₂ (by decide)).batch e₃ (by omega_arith)
      refine ⟨e₂, fun k hk => ?_⟩
      rcases (by omega_arith : k < 4 * q ∨ 4 * q ≤ k) with hk' | hk'
      · rw [out_kept h e₃ (by omega_arith) hk', hm₂]; exact o₁ k hk'
      · have := r₃ (k - 4 * q) (by omega_arith)
        rwa [show sig b s₂ = sig b s by rw [show sig b s₂ = sig b s₁ by simp only [sig, hm₂]]; exact hsig,
          show o + 128 * (4 * q) + 128 * (k - 4 * q) = o + 128 * k by omega_arith,
          show N₀ + 4 * q + (k - 4 * q) = N₀ + k by omega_arith] at this

theorem quads_tr {fast : Bool} (N₀ q o wl : Nat) :
    RelCT isa (fun x y => x.gpr .rbx = y.gpr .rbx) (quads N₀ q o wl fast) fun x y => x.gpr .rbx = y.gpr .rbx := by
  cases fast
  · exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx])
      (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) [.rbx]
      (hc := taint.hintOfSize Taint.chunk (X86_64.Taint.ofRegs [.rbx]) (quads 0 1 0 0 false)) (by kernel_rfl))
      (fun _ _ h => h) fun _ _ h => h _ (List.mem_singleton_self _)
  · exact RelCT.mono (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx])
      (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) [.rbx]
      (hc := taint.hintOfSize Taint.chunk (X86_64.Taint.ofRegs [.rbx]) (quads 0 1 0 0 true)) (by kernel_rfl))
      (fun _ _ h => h) fun _ _ h => h _ (List.mem_singleton_self _)

theorem prfsX4_rtr {fast : Bool} {wl : Nat} (n N₀ o : Nat) :
    RelCT isa (fun x y => x.gpr .rbx = y.gpr .rbx) (prfsX4 fast N₀ n o wl) fun x y => x.gpr .rbx = y.gpr .rbx := by
  unfold prfsX4
  refine RelCT.seq (by split; exacts [nil_tr, quads_tr _ _ _ _]) ?_
  split
  · exact nil_tr
  · refine RelCT.seq (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rbx])
      (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h) [.rbx, .r8, .r9] (hc := .block []) (by kernel_rfl)) ?_
    exact RelCT.mono (batch_tr (fun _ _ h => h) wl (Nat.le_of_lt (Nat.mod_lt n (by decide)))) (fun _ _ h => h)
      fun _ _ h => h _ (List.mem_cons_self ..)

/-- The permutation never loads MXCSR: evaluated once for each implementation. -/
theorem permute4_ctl (fast : Bool) : ctlOk (Impl.Sha3.X86_64.X4.permute4 fast) = true := by
  cases fast <;> kernel_rfl

/-- The permutation never writes the stack pointer: evaluated once for each implementation. -/
theorem permute4_sp (fast : Bool) : (Impl.Sha3.X86_64.X4.permute4 fast).all (fun i => !isa.writesSp i) = true := by
  cases fast <;> kernel_rfl

theorem permute4_xd (fast : Bool) : (Impl.Sha3.X86_64.X4.permute4 fast).x86_64Depth = 0 := by
  cases fast <;> kernel_rfl

theorem batch_xd {fast : Bool} (m wl : Nat) : (batch m wl fast).x86_64Depth = 0 := by
  simp only [batch, Code.x86_64Depth, permute4_xd]; rfl

theorem batch_ctl {fast : Bool} {m : Nat} (wl : Nat) (hm : m < 5) : ctlOk (batch m wl fast) = true :=
  ctlOk_seq (by kernel_rfl) (ctlOk_seq (permute4_ctl fast) (by
    rcases (by omega_arith : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl | rfl <;> kernel_rfl))

theorem batch_sp {fast : Bool} {m : Nat} (wl : Nat) (hm : m < 5) :
    (batch m wl fast).all (fun i => !isa.writesSp i) = true :=
  all_seq (by kernel_rfl) (all_seq (permute4_sp fast) (by
    rcases (by omega_arith : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl | rfl <;> kernel_rfl))

theorem quads_ctl {fast : Bool} (N₀ q o wl : Nat) : ctlOk (quads N₀ q o wl fast) = true := by
  unfold quads
  exact ctlOk_seq (by kernel_rfl) (ctlOk_loop (ctlOk_seq (batch_ctl wl (by decide)) (by kernel_rfl)))

theorem quads_sp {fast : Bool} (N₀ q o wl : Nat) : (quads N₀ q o wl fast).all (fun i => !isa.writesSp i) = true := by
  unfold quads
  exact all_seq (by kernel_rfl) (all_loop (all_seq (batch_sp wl (by decide)) (by kernel_rfl)))

theorem quads_xd {fast : Bool} (N₀ q o wl : Nat) : (quads N₀ q o wl fast).x86_64Depth = 0 := by
  simp only [quads, Code.x86_64Depth, batch_xd]; rfl

theorem prfsX4_xd {fast : Bool} {wl : Nat} (n N₀ o : Nat) : (prfsX4 fast N₀ n o wl).x86_64Depth = 0 := by
  unfold prfsX4
  simp only [Code.x86_64Depth]
  split <;> split <;> simp only [Code.x86_64Depth, quads_xd, batch_xd] <;> rfl

theorem prfsX4_ctl {fast : Bool} {wl : Nat} (n N₀ o : Nat) : ctlOk (prfsX4 fast N₀ n o wl) = true := by
  unfold prfsX4
  refine ctlOk_seq (by split; exacts [rfl, quads_ctl _ _ _ _]) ?_
  split
  · rfl
  · exact ctlOk_seq (by kernel_rfl) (batch_ctl wl (by have := Nat.mod_lt n (show 0 < 4 by decide); omega_arith))

theorem prfsX4_sp {fast : Bool} {wl : Nat} (n N₀ o : Nat) : (prfsX4 fast N₀ n o wl).all (fun i => !isa.writesSp i) = true := by
  unfold prfsX4
  refine all_seq (by split; exacts [rfl, quads_sp _ _ _ _]) ?_
  split
  · rfl
  · exact all_seq (by kernel_rfl) (batch_sp wl (by have := Nat.mod_lt n (show 0 < 4 by decide); omega_arith))

end Prf4

theorem cover_in {X : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] X) : InRegions X a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem prfsLead_le (n : Nat) : prfsLead n ≤ n := by
  unfold prfsLead; split <;> omega_arith

theorem prfsAvx2_ok {fast : Bool} {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat}
    (hN : N₀ + n + 4 ≤ 256) (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    WP isa (prfsAvx2 (fast := fast) N₀ n o wl) s (PrfsPost s N₀ n o wl) := by
  obtain ⟨hs, hw, ho, hsg, dwo, dws, dos, hsm, hso⟩ := prfsChk_spec hc
  have hw' : inB wbs (sc (32 * wl)) 2368 = true := ((Bool.and_eq_true _ _).mp hw).2
  have ho' : inB wbs (sc o) (128 * n) = true := ((Bool.and_eq_true _ _).mp ho).2
  obtain ⟨n₀, hn₀, hl⟩ := inB_spec (rdOk_in ((Bool.and_eq_true _ _).mp ho).1)
  have := L.small _ hn₀
  have hb : o + 128 * n < 2 ^ 32 := Nat.lt_of_le_of_lt (show o + 128 * n ≤ n₀ from hl) this
  have i1 := cover_in (L.cW hw')
  have i2 := cover_in (L.cW ho')
  have i3 := cover_in (L.cR (rdOk_in hsg))
  have d1 := L.disj dwo
  have d2 := L.disj dws
  have d3 := L.disj dos
  have hr := prfsLead_le n
  unfold prfsAvx2
  generalize prfsLead n = r at hr ⊢
  refine WP.seq (WP.mono (prfsScalar_lead L hcs (by omega_arith) hr fun i hi => hs i (by omega_arith)) fun s₁ h₁ => ?_)
  have e₁ : s₁.gpr .rbx = s.gpr .rbx := h₁.post.cs .rbx (by decide)
  have hsub : Region.Sub (Prf4.oR (s.gpr .rbx) (o + 128 * r) (n - r)) (Prf4.oR (s.gpr .rbx) o n) :=
    Offset.sub _ (by omega_arith) (by omega_arith)
  have raw : Prf4.RawPre (s.gpr .rbx) (n - r) (o + 128 * r) wl s₁ := by
    refine ⟨e₁, by rw [h₁.post.wr]; exact i1, ?_, by rw [h₁.post.rd, h₁.post.wr]; exact i3, d1.sub_right hsub, d2,
      d3.sub_left hsub, hsm, by omega_arith⟩
    have := inRegions_sub i2 (off := 128 * r) (l := 128 * (n - r)) (by omega_arith) (Prf4.lt64 hb)
    rw [h₁.post.wr, ← Offset.add_add]; exact this
  have hsig : Prf4.sig (s.gpr .rbx) s₁ = bytesAt s.mem (pa s sigP) 32 := by
    rw [← h₁.sig]; simp only [Prf4.sig, Prf4.sS, pa, e₁]
  refine WP.mono (Prf4.prfsX4_ok (fast := fast) raw (by omega_arith)) fun s' ⟨e, out⟩ =>
    ⟨PPost.trans h₁.post ⟨e.rd, e.wr, e.cs, e.frame.sub fun r' hr' => ?_⟩ (fun w hw => by
      simp only [prfsW, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact rbx_cs) (fun w hw => hw) (fun w hw => hw), fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · refine ⟨toR s₁ (sc (32 * wl), 2368), List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))), ?_⟩
      simp only [toR, pa, e₁]; exact fun _ h => h
    · refine ⟨toR s₁ (sc o, 128 * n), List.mem_append_left _ (List.mem_map_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _)))))), ?_⟩
      simp only [toR, pa, e₁]; exact hsub
  · rcases (by omega_arith : i < r ∨ r ≤ i) with hi' | hi'
    · rw [bytesAt_frame e.frame (by
        have hk : Region.Sub ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩ (Prf4.oR (s.gpr .rbx) o n) :=
          Offset.sub _ (by omega_arith) (by omega_arith)
        have hd : Region.Disjoint ⟨s.gpr .rbx + BitVec.ofNat 64 (o + 128 * i), 128⟩
            (Prf4.oR (s.gpr .rbx) (o + 128 * r) (n - r)) := Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
        simpa using ⟨(d1.sub_right hk).symm, hd⟩) (by decide)]
      exact h₁.outs i hi'
    · have := out (i - r) (by omega_arith)
      rwa [hsig, show o + 128 * r + 128 * (i - r) = o + 128 * i by omega_arith,
        show N₀ + r + (i - r) = N₀ + i by omega_arith] at this

theorem prfsAvx2_tr {fast : Bool} (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {N₀ n o wl : Nat} (hN : N₀ + n + 4 ≤ 256)
    (hc : prfsChk (rbs ++ wbs) wbs n o wl = true) :
    RelCT isa (LRel rbs wbs) (prfsAvx2 (fast := fast) N₀ n o wl) fun _ _ => True := by
  obtain ⟨hs, -, -, hsg, -⟩ := prfsChk_spec hc
  have hr := prfsLead_le n
  unfold prfsAvx2
  generalize prfsLead n = r at hr ⊢
  exact RelCT.seq (prfsScalar_trL hcs (by omega_arith) fun i hi => (hs i (by omega_arith)).1)
    (RelCT.mono (Prf4.prfsX4_rtr _ _ _) (fun _ _ h => h.eq (rdOk_in hsg)) fun _ _ _ => trivial)

theorem prfsAvx2_ctl {fast : Bool} (N₀ n o wl : Nat) : ctlOk (prfsAvx2 (fast := fast) N₀ n o wl) = true :=
  ctlOk_seq (prfsScalar_ctl _ _ _ _) (Prf4.prfsX4_ctl _ _ _)

theorem prfsAvx2_sp {fast : Bool} (N₀ n o wl : Nat) : (prfsAvx2 (fast := fast) N₀ n o wl).all (fun i => !isa.writesSp i) = true :=
  all_seq (prfsScalar_sp _ _ _ _) (Prf4.prfsX4_sp _ _ _)

theorem prfsAvx2_xd {fast : Bool} (N₀ n o wl : Nat) : (prfsAvx2 (fast := fast) N₀ n o wl).x86_64Depth ≤ 16 :=
  xd_seq (prfsScalar_xd _ _ _ _) (by rw [Prf4.prfsX4_xd]; decide)

end VG.Proof.MlKem.X86_64
