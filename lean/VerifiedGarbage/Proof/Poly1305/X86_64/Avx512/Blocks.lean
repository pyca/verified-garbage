module

import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
public import VerifiedGarbage.Proof.Poly1305.X86_64.Variant
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Group
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.VKeep
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Gpr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mcdt.X86_64.Op
meta import VerifiedGarbage.Proof.Mcdt.X86_64.Op
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Blocks
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Variant
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Group
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.VKeep
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Gpr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Poly1305.Contract
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Final
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Final
public import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Load
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Powers
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Gpr
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Setup
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Load
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Powers
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Gpr
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Taint

/-! ### `Poly1305.X86_64.Avx512.StoreY`, which this module and modules that import it used -/

section

/-!
# Poly1305 on x86-64 with AVX-512: the multipliers into the state

`storeY` computes five times the limbs of `Y` (`fiveY`), stores lane 0 of
`Y_i` at `rdi + 56 + 4 i` and of `5 Y_i` at `rdi + 72 + 4 i` (`1 ≤ i ≤ 4`),
each 16-byte store overwriting all but the first doubleword of the one before,
then the mask and the pad bit at `rdi + 104` and `rdi + 112`. The doubleword
at each of these addresses is then the low doubleword of quadword 0 of the
register stored there, which is all that the loop's `vpmuludq`s read (`MemM`).
Everything it writes is working space of the state (`wR`), below byte 120.
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64 (off wR wR_contains sep_off)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_keep)

/-! ## `fiveY` -/

def fvS : Sym := (Sym.init.run false fiveY).get (by decide +kernel)
theorem fvS_eq : Sym.init.run false fiveY = some fvS := (Option.some_get _).symm

theorem fvS_shape : (∀ i < 5, fvS.reg (xi (hreg i)) = .reg (xi (hreg i)) ∧
    fvS.reg (xi (yreg i)) = .reg (xi (yreg i))) ∧
    ∀ k < 4, fvS.reg (xi (dreg k)) = .add (.shl (.reg (xi (yreg (k + 1)))) 2) (.reg (xi (yreg (k + 1)))) := by
  decide +kernel

theorem five_lo (y : Nat) : (y * 2 ^ 2 % 2 ^ 64 + y) % 2 ^ 64 % 2 ^ 32 = 5 * (y % 2 ^ 32) % 2 ^ 32 := by
  omega_arith

theorem fiveY_ok (s : State) :
    WP isa (.block fiveY) s fun s' => vec s s' = s' ∧
      (∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k) ∧
      ∀ k < 4, (qz s' (dreg k) 0).toNat % 2 ^ 32 = 5 * yl s 0 (k + 1) % 2 ^ 32 := by
  refine WP.mono (run_ok (fun h => by cases h) fvS_eq) fun s' h => ⟨h.eq, fun i hi k hk => ⟨?_, ?_⟩, fun k hk => ?_⟩
  · rw [h.reg _ k hk, (fvS_shape.1 i hi).1]; simp only [Q.eval, xr_xi]
  · rw [h.reg _ k hk, (fvS_shape.1 i hi).2]; simp only [Q.eval, xr_xi]
  · rw [h.natw _ (by decide), fvS_shape.2 k hk]
    simp only [Q.natw, envOf_v, yl]
    exact five_lo _

/-! ## The stores -/

/-- 16-byte stores of `xmm` registers at `rdi + d`. -/
def stores (L : List (Nat × XReg)) : List Instr := L.map fun e => .vmovdquStore .l128 (at_ .rdi e.1) e.2

/-- The memory after `stores L` from `m`, at `p`, with the registers `x`. -/
def wrAll (m : Mem) (p : Addr) (x : XReg → BitVec 128) : List (Nat × XReg) → Mem
  | [] => m
  | e :: L => wrAll (m.writeW (off p e.1) (x e.2)) p x L

theorem stores_ok : ∀ (L : List (Nat × XReg)) (s : State),
    (∀ e ∈ L, InRegions s.wr (off (s.gpr .rdi) e.1) 16) →
    WP isa (.block (stores L)) s fun s' => s' = { s with mem := wrAll s.mem (s.gpr .rdi) s.xmm L }
  | [], s, _ => WP.block_nil rfl
  | e :: L, s, hw => by
    have h₀ := hw e (List.mem_cons_self ..)
    refine WP.block_cons_iff.2 ⟨{ s with mem := s.mem.writeW (off (s.gpr .rdi) e.1) (s.xmm e.2) }, ?_, ?_⟩
    · show s.store128 (off (s.gpr .rdi) e.1) (s.xmm e.2) = _
      simp only [State.store128, h₀, ite_true]
    · exact WP.mono (stores_ok L _ fun e' he => hw e' (List.mem_cons_of_mem _ he)) fun s' h => h

/-- The registers `storeY` stores, at their displacements: `Y_i` at
`56 + 4 i`, and `5 Y_(k+1)` (in `D_k`) at `76 + 4 k`. -/
def stL : List (Nat × XReg) :=
  [(56, yreg 0), (60, yreg 1), (64, yreg 2), (68, yreg 3), (72, yreg 4),
   (76, dreg 0), (80, dreg 1), (84, dreg 2), (88, dreg 3)]

theorem storeY_eq : storeY = fiveY ++ (stores stL ++ ([.store mMask .r8, .store mPad .r9] : List Instr)) := rfl

theorem wrAll_frame {p : Addr} {x : XReg → BitVec 128} :
    ∀ (L : List (Nat × XReg)) {m m' : Mem}, (∀ e ∈ L, 56 ≤ e.1 ∧ e.1 + 16 ≤ 128) →
      Frame [wR p] m m' → Frame [wR p] m (wrAll m' p x L)
  | [], _, _, _, h => h
  | e :: L, _, _, hL, h => by
    have he := hL e (List.mem_cons_self ..)
    exact wrAll_frame L (fun e' h' => hL e' (List.mem_cons_of_mem _ h'))
      (h.writeW (List.mem_singleton_self _) _ (wR_contains p he.1 he.2))

theorem rd_sep (m : Mem) (p : Addr) {w n : Nat} (v : BitVec w) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (hn : n / 8 ≤ 16) (hk : w / 8 ≤ 16) (h : d + n / 8 ≤ e ∨ e + w / 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) n = m.readW (off p d) n :=
  Mem.readW_writeW_sep (sep_off p hd he hn hk h) (by omega_arith)

theorem rd32_self (m : Mem) (p : Addr) (d : Nat) (v : BitVec 128) :
    (m.writeW (off p d) v).readW (off p d) 32 = v.extractLsb' 0 32 := by
  have h := readW_writeW_inside m (off p d) v (k := 0) (n := 4) (by decide) (by decide)
  rwa [show off p d + BitVec.ofNat 64 0 = off p d from BitVec.add_zero _] at h

theorem lo32_rd (m : Mem) (a : Addr) : (m.readW a 64).toNat % 2 ^ 32 = (m.readW a 32).toNat := by
  have h := readW_extract m a (w := 64) (k := 0) (n := 4) (by decide)
  rw [show a + BitVec.ofNat 64 0 = a from BitVec.add_zero _] at h
  rw [← h, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

/-- The memory `storeY` leaves. -/
def yMem (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) : Mem :=
  ((wrAll m p x stL).writeW (off p 104) a).writeW (off p 112) b

theorem yMem_lo (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    ∀ e ∈ stL, ((yMem m p x a b).readW (off p e.1) 64).toNat % 2 ^ 32 = ((x e.2).extractLsb' 0 32).toNat := by
  intro e he
  rw [lo32_rd]
  simp only [stL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega_arith) only [yMem, stL, wrAll, rd_sep, rd32_self]

theorem yMem_mask (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (yMem m p x a b).readW (off p 104) 64 = a := by
  rw [yMem, rd_sep _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

theorem yMem_pad (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (yMem m p x a b).readW (off p 112) 64 = b := by
  rw [yMem, Mem.readW_writeW_self64]

theorem yMem_mx (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    (yMem m p x a b).readW (off p 120) 32 = m.readW (off p 120) 32 := by
  simp (disch := omega_arith) only [yMem, stL, wrAll, rd_sep]

theorem yMem_frame (m : Mem) (p : Addr) (x : XReg → BitVec 128) (a b : BitVec 64) :
    Frame [wR p] m (yMem m p x a b) :=
  ((wrAll_frame stL (by decide) (Frame.refl _ _)).writeW (List.mem_singleton_self _) _
    (wR_contains p (d := 104) (n := 8) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
    (wR_contains p (d := 112) (n := 8) (by decide) (by decide))

theorem xmm_lo32 (s : State) (r : XReg) : ((s.xmm r).extractLsb' 0 32).toNat = (qz s r 0).toNat % 2 ^ 32 := by
  have e : qz s r 0 = (s.xmm r).extractLsb' 0 64 := rfl
  rw [e, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega_arith

/-- What `storeY` leaves. -/
structure StoreYPost (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mxcsr : s'.mxcsr = s.mxcsr
  hy : ∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k
  frame : Frame [wR (s.gpr .rdi)] s.mem s'.mem
  mx : s'.mem.readW (off (s.gpr .rdi) 120) 32 = s.mem.readW (off (s.gpr .rdi) 120) 32
  r : ∀ i < 5, mr s' i = yl s 0 i
  five : ∀ i, 1 ≤ i → i < 5 → ms s' i = 5 * yl s 0 i % 2 ^ 32
  mask : (envOf s').mb 104 = (s.gpr .r8).toNat
  pad : (envOf s').mb 112 = (s.gpr .r9).toNat

theorem storeY_ok (s : State) (hw : ∀ d, 56 ≤ d → d + 16 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 16)
    (hw8 : ∀ d, 56 ≤ d → d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8) :
    WP isa (.block storeY) s (StoreYPost s) := by
  rw [storeY_eq]
  refine WP.block_append (WP.mono (fiveY_ok s) fun s₁ ⟨v₁, hy₁, f₁⟩ => ?_)
  obtain ⟨g₁, m₁, rd₁, wr₁, mx₁⟩ := vec_keep v₁
  have hw₁ : ∀ d, 56 ≤ d → d + 16 ≤ 128 → InRegions s₁.wr (off (s₁.gpr .rdi) d) 16 := by
    rw [g₁, wr₁]; exact hw
  have hw₁8 : ∀ d, 56 ≤ d → d + 8 ≤ 128 → InRegions s₁.wr (off (s₁.gpr .rdi) d) 8 := by
    rw [g₁, wr₁]; exact hw8
  refine WP.block_append (WP.mono (stores_ok stL s₁ fun e he => ?_) fun s₂ e₂ => ?_)
  · have b := (show ∀ e ∈ stL, 56 ≤ e.1 ∧ e.1 + 16 ≤ 128 by decide) e he
    exact hw₁ e.1 b.1 b.2
  subst e₂
  refine WP.block_cons_iff.2 ⟨_, (show State.store64 _ (off (s₁.gpr .rdi) 104) (s₁.gpr .r8) = _ by
    simp only [State.store64, hw₁8 104 (by decide) (by decide), ite_true]; rfl), ?_⟩
  refine WP.block_cons_iff.2 ⟨_, (show State.store64 _ (off (s₁.gpr .rdi) 112) (s₁.gpr .r9) = _ by
    simp only [State.store64, hw₁8 112 (by decide) (by decide), ite_true]; rfl), WP.block_nil ?_⟩
  show StoreYPost s { s₁ with mem := yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9) }
  have M : ∀ d, (envOf { s₁ with mem := yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9) }).mb d =
      ((yMem s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9)).readW (off (s₁.gpr .rdi) d) 64).toNat :=
    fun d => rfl
  have L := yMem_lo s₁.mem (s₁.gpr .rdi) s₁.xmm (s₁.gpr .r8) (s₁.gpr .r9)
  refine ⟨by rw [← g₁], by rw [← rd₁], by rw [← wr₁], by rw [← mx₁], fun i hi k hk => hy₁ i hi k hk, ?_, ?_, fun i hi => ?_, fun i h₁ hi => ?_, ?_, ?_⟩
  · rw [← g₁, ← m₁]; exact yMem_frame _ _ _ _ _
  · rw [← g₁, ← m₁]; exact yMem_mx _ _ _ _ _
  · simp only [mr]
    rw [M]
    rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
    · rw [L (56, yreg 0) (by decide), xmm_lo32, (hy₁ 0 (by decide) 0 (by decide)).2]; rfl
    · rw [L (60, yreg 1) (by decide), xmm_lo32, (hy₁ 1 (by decide) 0 (by decide)).2]; rfl
    · rw [L (64, yreg 2) (by decide), xmm_lo32, (hy₁ 2 (by decide) 0 (by decide)).2]; rfl
    · rw [L (68, yreg 3) (by decide), xmm_lo32, (hy₁ 3 (by decide) 0 (by decide)).2]; rfl
    · rw [L (72, yreg 4) (by decide), xmm_lo32, (hy₁ 4 (by decide) 0 (by decide)).2]; rfl
  · simp only [ms]
    rw [M]
    rcases (by omega_arith : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl
    · rw [L (76, dreg 0) (by decide), xmm_lo32]; exact f₁ 0 (by decide)
    · rw [L (80, dreg 1) (by decide), xmm_lo32]; exact f₁ 1 (by decide)
    · rw [L (84, dreg 2) (by decide), xmm_lo32]; exact f₁ 2 (by decide)
    · rw [L (88, dreg 3) (by decide), xmm_lo32]; exact f₁ 3 (by decide)
  · rw [M, yMem_mask, g₁]
  · rw [M, yMem_pad, g₁]

end VG.Proof.Poly1305.X86_64.Avx512

end

end

/-! ### `Poly1305.X86_64.Avx512.Final`, which this module and modules that import it used -/

section

/-!
# Poly1305 on x86-64 with AVX-512: the accumulator in, and the lanes summed

`loadH` splits the accumulator into quadword 0 of `H`; after the last group,
`sumLanes` adds the quadwords into quadword 0 and carries. The rest
(`fullCarry`, `reduce` and `storeH`) is `vg_poly1305_blocks_avx2`'s code, on
quadword 0 (see `Avx2/Final.lean`), whose quadwords are those of `Avx2.qw`
(`qz_qw`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec vec_trans vec_gpr hN)
open VG.Spec.Poly1305 (P)

/-! ## `loadH` -/

def ldS : Sym := (Sym.init.run false loadH).get (by decide +kernel)
theorem ldS_eq : Sym.init.run false loadH = some ldS := (Option.some_get _).symm
theorem ldS_y : ∀ i < 5, ldS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env)
theorem ldS_0 : ∀ k < 8, (ldS.reg (xi (hreg 0))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_1 : ∀ k < 8, (ldS.reg (xi (hreg 1))).natw E k =
    (if k = 0 then E.g .r10 else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_2 : ∀ k < 8, (ldS.reg (xi (hreg 2))).natw E k =
    ((if k = 0 then E.g .r11 else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
      (if k = 0 then E.g .r10 else 0) / 2 ^ 52) := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_3 : ∀ k < 8, (ldS.reg (xi (hreg 3))).natw E k =
    (if k = 0 then E.g .r11 else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem ldS_4 : ∀ k < 8, (ldS.reg (xi (hreg 4))).natw E k =
    ((if k = 0 then E.g .r11 else 0) / 2 ^ 40 ||| (if k = 0 then E.g .rax else 0) * 2 ^ 24 % 2 ^ 64) := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
end

/-- What `loadH` leaves: the accumulator in quadword 0 of `H`, zeros in the
others, and `Y` as it was. -/
structure LoadHPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, hval s' k = if k = 0 then hN s else 0
  hb : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 26

theorem loadH_ok {s : State} (hax : (s.gpr .rax).toNat < 4) : WP isa (.block loadH) s (LoadHPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) ldS_eq) fun s' h => ?_
  have e : ∀ k < 8, hv s' k 0 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 1 = (if k = 0 then (s.gpr .r10).toNat else 0) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 2 = ((if k = 0 then (s.gpr .r11).toNat else 0) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
        (if k = 0 then (s.gpr .r10).toNat else 0) / 2 ^ 52) ∧
      hv s' k 3 = (if k = 0 then (s.gpr .r11).toNat else 0) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 4 = ((if k = 0 then (s.gpr .r11).toNat else 0) / 2 ^ 40 |||
        (if k = 0 then (s.gpr .rax).toNat else 0) * 2 ^ 24 % 2 ^ 64) := fun k hk =>
    ⟨by rw [hv, h.natw _ hk, ldS_0 _ k hk]; rfl, by rw [hv, h.natw _ hk, ldS_1 _ k hk]; rfl,
      by rw [hv, h.natw _ hk, ldS_2 _ k hk]; rfl, by rw [hv, h.natw _ hk, ldS_3 _ k hk]; rfl,
      by rw [hv, h.natw _ hk, ldS_4 _ k hk]; rfl⟩
  have l := (s.gpr .r10).isLt
  have m := (s.gpr .r11).isLt
  have e4 : ((s.gpr .r11).toNat / 2 ^ 40 ||| (s.gpr .rax).toNat * 2 ^ 24 % 2 ^ 64) =
      (s.gpr .r11).toNat / 2 ^ 40 + 2 ^ 24 * (s.gpr .rax).toNat := by
    rw [show (s.gpr .rax).toNat * 2 ^ 24 % 2 ^ 64 = 2 ^ 24 * (s.gpr .rax).toNat by omega_arith, Nat.or_comm,
      ← Nat.two_pow_add_eq_or_of_lt (by omega_arith)]
    omega_arith
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, ldS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4 ⊢
      rw [e4] at a4
      have := Limbs26.split_val l (s.gpr .r11).toNat
      rw [hval, Limbs26.val, a0, a1, a2, a3, a4, hN]
      omega_arith
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4 ⊢
      rw [hval, Limbs26.val, a0, a1, a2, a3, a4]
  · obtain ⟨a0, a1, a2, a3, a4⟩ := e k hk
    by_cases hk0 : k = 0
    · subst hk0
      simp only [ite_true] at a0 a1 a2 a3 a4
      rw [e4] at a4
      rw [Limbs26.split_or l] at a2
      rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; omega_arith
      · rw [a1]; omega_arith
      · rw [a2]; omega_arith
      · rw [a3]; omega_arith
      · rw [a4]; omega_arith
    · simp only [hk0, ite_false, Nat.zero_mul, Nat.zero_mod, Nat.zero_div, Nat.or_self] at a0 a1 a2 a3 a4
      rcases cases5 hi with rfl | rfl | rfl | rfl | rfl
      · rw [a0]; decide
      · rw [a1]; decide
      · rw [a2]; decide
      · rw [a3]; decide
      · rw [a4]; decide

/-! ## `sumLanes` -/

def sumB : Bnds :=
  ⟨fun r => match r with
    | .xmm0 | .xmm1 | .xmm2 | .xmm3 | .xmm4 => 2 ^ 27 - 1
    | _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1,
   fun g => if g = .r8 then 2 ^ 26 - 1 else 2 ^ 64 - 1,
   fun _ => 2 ^ 64 - 1,
   fun _ => 2 ^ 32 - 1⟩

def smS : Sym := (Sym.init.run false sumLanes).get (by decide +kernel)
theorem smS_eq : Sym.init.run false sumLanes = some smS := (Option.some_get _).symm

theorem smS_ok : ∀ i < 5, ∀ k < 8, (smS.reg (xi (hreg i))).ok sumB k = true ∧
    (smS.reg (xi (hreg i))).bnd sumB k < (if i = 1 then 2 ^ 27 else 2 ^ 26) := by
  decide +kernel

/-- The sum of the quadwords of `H`, limb by limb, as `sumLanes` adds them. -/
def lsum (h : Nat → Nat → Nat) (i : Nat) : Nat :=
  h 0 i + h 4 i + (h 2 i + h 6 i) + (h 1 i + h 5 i + (h 3 i + h 7 i))

theorem smS_nat (E : Env) : ∀ i < 5, (smS.reg (xi (hreg i))).nat E 0 =
    Limbs26.carry (lsum fun k j => E.v (xi (hreg j)) k) (E.g .r8) i
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl

theorem sumB_env {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27) :
    EnvOK s sumB := by
  refine ⟨fun r k hk => ?_, fun r k hk => ?_, fun g => ?_, fun _ => Nat.le_sub_one_of_lt (BitVec.isLt _),
    fun _ => Nat.le_sub_one_of_lt (Nat.mod_lt _ (by decide))⟩
  · have := BitVec.isLt (qz s r k)
    cases r <;> simp only [sumB] <;> first
      | omega_arith
      | exact Nat.le_sub_one_of_lt (hb k hk 0 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 1 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 2 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 3 (by decide))
      | exact Nat.le_sub_one_of_lt (hb k hk 4 (by decide))
  · have := Nat.mod_lt (qz s r k).toNat (show 2 ^ 32 > 0 by decide)
    simp only [sumB]; omega_arith
  · have := BitVec.isLt (s.gpr g)
    simp only [sumB]
    split
    · subst g; rw [hr8]; decide
    · omega_arith

theorem lsum_val (h : Nat → Nat → Nat) :
    Limbs26.val (lsum h) = Limbs26.val (h 0) + Limbs26.val (h 2) + Limbs26.val (h 4) + Limbs26.val (h 6) +
      Limbs26.val (h 1) + Limbs26.val (h 3) + Limbs26.val (h 5) + Limbs26.val (h 7) := by
  simp only [Limbs26.val, lsum]; omega_arith

/-- What `sumLanes` leaves in quadword 0 of `H`: the sum of the quadwords,
carried. -/
structure SumPost (s s' : State) : Prop where
  vec : vec s s' = s'
  h : hval s' 0 ≡ bsum s [MOD P]
  hb : ∀ i < 5, hv s' 0 i < if i = 1 then 2 ^ 27 else 2 ^ 26
  hball : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 27

theorem sumLanes_ok {s : State} (hr8 : s.gpr .r8 = 0x3ffffff) (hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27) :
    WP isa (.block sumLanes) s (SumPost s) := by
  refine WP.mono (run_ok (by intro h; cases h) smS_eq) fun s' h => ?_
  have hE := sumB_env hr8 hb
  have e : ∀ i < 5, hv s' 0 i = Limbs26.carry (lsum (hv s)) 0x3ffffff i := fun i hi => by
    obtain ⟨e, -⟩ := h.nat hE (by decide) (smS_ok i hi 0 (by decide)).1
    simp only [hv] at e ⊢
    rw [e, smS_nat _ i hi]
    simp only [envOf, hr8, xr_xi]
    rfl
  refine ⟨h.eq, ?_, fun i hi => ?_, fun k hk i hi => ?_⟩
  · rw [hval, Avx2.val_congr e, bsum]
    have := Limbs26.carry_val (lsum (hv s))
    rw [lsum_val] at this
    simp only [hval]
    rw [← this, Nat.ModEq, Nat.add_mul_mod_self_left]
  · obtain ⟨-, b⟩ := h.nat hE (by decide) (smS_ok i hi 0 (by decide)).1
    exact Nat.lt_of_le_of_lt b (smS_ok i hi 0 (by decide)).2
  · obtain ⟨-, b⟩ := h.nat hE hk (smS_ok i hi k hk).1
    have := (smS_ok i hi k hk).2
    simp only [hv]
    split at this <;> omega_arith

/-! ## Quadword 0 as `vg_poly1305_blocks_avx2` sees it -/

theorem hv_avx2 (s : State) {k : Nat} (hk : k < 4) (i : Nat) : Avx2.hv s k i = hv s k i := by
  simp only [Avx2.hv, hv, qz_qw _ _ hk]

end VG.Proof.Poly1305.X86_64.Avx512

end

end

/-!
# Poly1305 on x86-64 with AVX-512: `vg_poly1305_blocks_avx512`

The whole function: with fewer than 40 blocks it runs the code of
`vg_poly1305_blocks_avx2`; otherwise, once its call of `vg_mcdt_enter` has
returned 1 (`Avx2.guard_ok`), it absorbs the blocks eight at a time
(see `Impl/Poly1305/X86_64/Avx512.lean`), and calls `vg_poly1305_blocks` for
the last `n mod 8`.

As for AVX2 (`Avx2/Blocks.lean`), the vector code computes the right numbers
only if the accumulator on entry is below `2¹⁹⁴`, which holds whenever the
state represents a message: each block's effect on the vector registers is
established under that assumption, and its execution without it (`guard`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64 (at_)
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Spec.Poly1305 (P leNum bytesAt accumulate Repr clamp)
open VG.Proof.Poly1305.X86_64.Avx2 (guard and_exec TailPre Post tail_ok done_ok cs_ne
  H2_lt bytesAt_frame vec vec_trans vec_gpr vec_keep repr_frame ret_stk
  ret_frame consts_ok storeH_ok finish_ok ext5)

/-- The contract the proof is written against (also `blocksIfma`'s):
`blocksX86_64`'s, with 16 bytes of stack below the return address that its
calls use, and MXCSR public. -/
def blocksAvx512X86_64 : Contract X86_64.isa := Proof.Poly1305.blocksStack 16

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀]
  wr : s₀.wr = [sR (st s₀)]
  st_bl : (sR (st s₀)).Disjoint (blR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  stk_st : (below (s₀.gpr .rsp) 16).Disjoint (sR (st s₀))
  stk_bl : (below (s₀.gpr .rsp) 16).Disjoint (blR s₀)
  nowrap : (bp s₀).toNat + 16 * nb s₀ ≤ 2 ^ 64

theorem below8_16 (sp : Addr) : Region.Sub (below sp 8) (below sp 16) := below_sub (by omega_arith) (by omega_arith)

theorem APre.avx2 {s₀ : State} (hp : APre s₀) : Avx2.APre s₀ :=
  ⟨hp.rd, hp.wr, hp.st_bl, hp.ret_st, hp.stk_st.sub_left (below8_16 _), hp.stk_bl.sub_left (below8_16 _),
    hp.nowrap⟩

theorem APre.g16 {s₀ : State} (hp : APre s₀) (hS : 16 ≤ (s₀.gpr .rsp).toNat) : Avx2.G16 s₀ :=
  ⟨hp.stk_st, hp.stk_bl, hS⟩

/-- `APre`, of a state with the arguments, `rsp` and the regions of `s₀`. -/
theorem APre.congr {s₀ v : State} (hp : APre s₀) (hv : Avx2.Like s₀ v) : APre v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [st, blR, bp, nb, retR, hv.rdi, hv.rsi, hv.rdx, hv.rsp, hv.rd, hv.wr] <;>
    with_reducible assumption

/-! ## Registers, memory and the vector state -/

theorem LaneInv.of_qz {R X : Nat} {s s' : State} (h : ∀ r k, qz s' r k = qz s r k)
    (hI : LaneInv R X s) : LaneInv R X s' := by
  obtain e₁ : hv s' = hv s := by funext k i; simp only [hv, h]
  obtain e₂ : yl s' = yl s := by funext k i; simp only [yl, h]
  obtain e₃ : yh s' = yh s := by funext k i; simp only [yh, h]
  obtain ⟨⟨lo, hi, lob, hib⟩, hb, acc⟩ := hI
  refine ⟨⟨by rw [e₂]; exact lo, by rw [e₃]; exact hi, by rw [e₂]; exact lob, by rw [e₃]; exact hib⟩,
    by rw [e₁]; exact hb, ?_⟩
  simp only [wsum, hval, e₁] at acc ⊢; exact acc

theorem rcx_val (x : BitVec 64) (h : 8 ≤ x.toNat) : (x >>> 3) - 1 = BitVec.ofNat 64 (x.toNat / 8 - 1) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    show (1 : BitVec 64).toNat = 1 from rfl]
  omega_arith

theorem and7_toNat (x : BitVec 64) : (x &&& 7).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem LaneInv.of_hy {R X : Nat} {s s' : State}
    (h : ∀ i < 5, ∀ k < 8, qz s' (hreg i) k = qz s (hreg i) k ∧ qz s' (yreg i) k = qz s (yreg i) k)
    (hI : LaneInv R X s) : LaneInv R X s' := by
  obtain eh : ∀ k < 8, hv s' k = hv s k := fun k hk => ext5 (fun _ h => hv_ge _ _ h) (fun _ h => hv_ge _ _ h)
    fun i hi => by simp only [hv, (h i hi k hk).1]
  refine ⟨hI.y.of_y fun i hi k hk => (h i hi k hk).2, fun k hk i hi => by rw [eh k hk]; exact hI.hb k hk i hi, ?_⟩
  obtain e : wsum R s' = wsum R s := by
    simp only [wsum, hval, eh 0 (by decide), eh 1 (by decide), eh 2 (by decide), eh 3 (by decide),
      eh 4 (by decide), eh 5 (by decide), eh 6 (by decide), eh 7 (by decide)]
  rw [e]; exact hI.acc

theorem mr_congr {s s' : State} (hg : s'.gpr .rdi = s.gpr .rdi) (hm : s'.mem = s.mem) : mr s' = mr s := by
  funext i; simp only [mr, envOf, hg, hm]

theorem MemY.of_mem {R : Nat} {s s' : State} (h : MemY R s) (hg : s'.gpr .rdi = s.gpr .rdi)
    (hm : s'.mem = s.mem) : MemY R s' :=
  ⟨h.m.of_mem hg hm, by rw [mr_congr hg hm]; exact h.val⟩

/-! ## The prologue -/

/-- What the prologue leaves in memory for the rest: nothing written outside
the working space `wR`. -/
structure MemOK (s₀ : State) (m₁ : Mem) : Prop where
  frame : Frame [wR (st s₀)] s₀.mem m₁

/-- Before group `j` of eight blocks (the loop's invariant), with the memory
`m₁` the prologue leaves. -/
structure LInv (s₀ : State) (m₁ : Mem) (j : Nat) (s : State) : Prop where
  lt : j < nb s₀ / 8
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = blkAddr s₀ (8 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 8 - 1 - j)
  rdx : s.gpr .rdx = s₀.gpr .rdx
  r8 : s.gpr .r8 = 0x3ffffff
  r9 : s.gpr .r9 = 0x1000000
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  mxcsr : s.mxcsr = s₀.mxcsr
  acc : H2 s₀ < 4 → LaneInv (Rn s₀) (Poly1305.absorbAll (Rn s₀) (A0 s₀) (blks s₀ (8 * j))) s ∧
    MemY (Rn s₀) s

theorem powers_split : Impl.Poly1305.X86_64.Avx2.consts ++ powers ++
    Impl.Poly1305.X86_64.Avx2.loadHw ++ loadH ++ storeY ++
    ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr) =
    Impl.Poly1305.X86_64.Avx2.consts ++ (loadRg ++ (powersV ++
      (Impl.Poly1305.X86_64.Avx2.loadHw ++ (loadH ++ (storeY ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr)))))) := by
  simp only [powers_eq, List.append_assoc]

theorem pro_ok {s₀ : State} (hp : APre s₀) (hbig : 40 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa (.block (Impl.Poly1305.X86_64.Avx2.consts ++ powers ++
      Impl.Poly1305.X86_64.Avx2.loadHw ++ loadH ++ storeY ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr))) s
      (fun s' => MemOK s₀ s'.mem ∧ LInv s₀ s'.mem 0 s') := by
  have hp2 := hp.avx2
  rw [powers_split]
  refine WP.block_append (WP.mono (consts_ok s) fun s₁ ⟨r8₁, r9₁, g₁, m₁, k₁⟩ => ?_)
  obtain rdi₁ : s₁.gpr .rdi = st s₀ := by rw [g₁ _ (by decide) (by decide), hg]
  obtain wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, hk.wr]
  obtain mm₁ : s₁.mem = s₀.mem := by rw [m₁, hm]
  refine WP.block_append (WP.mono (loadRg_ok s₁ (hp2.inRW wr₁ rdi₁ (by omega_arith)) (hp2.inRW wr₁ rdi₁ (by omega_arith)))
    fun s₃ ⟨r10₃, r11₃, ax₃, g₃, m₃, k₃⟩ => ?_)
  obtain r8₃ : s₃.gpr .r8 = 0x3ffffff := by rw [g₃ _ (by decide) (by decide) (by decide), r8₁]
  refine WP.block_append (WP.mono (powersV_ok r8₃ ax₃) fun s₄ ⟨v₄, Y₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, vx₄⟩ := vec_keep v₄
  obtain rdi₄ : s₄.gpr .rdi = st s₀ := by rw [vg₄, g₃ _ (by decide) (by decide) (by decide), rdi₁]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, k₃.wr, wr₁]
  refine WP.block_append (WP.mono (loadHw_ok s₄ (hp2.inRW wr₄ rdi₄ (by omega_arith)) (hp2.inRW wr₄ rdi₄ (by omega_arith))
    (hp2.inRW wr₄ rdi₄ (by omega_arith))) fun s₅ ⟨a₅, b₅, c₅, g₅, m₅, k₅⟩ => ?_)
  obtain mm₄ : s₄.mem = s₀.mem := by rw [vm₄, m₃, mm₁]
  obtain ax₅ : (s₅.gpr .rax).toNat = H2 s₀ := by
    rw [c₅, rdi₄, mm₄]
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₅ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) ldS_eq) fun _ h => h.eq)
    fun hA => loadH_ok (by rw [ax₅]; exact hA)) fun s₆ ⟨v₆, L₆⟩ => ?_)
  obtain ⟨vg₆, vm₆, vrd₆, vwr₆, vx₆⟩ := vec_keep v₆
  obtain rdi₆ : s₆.gpr .rdi = st s₀ := by rw [vg₆, g₅ _ (by decide) (by decide) (by decide), rdi₄]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [vwr₆, k₅.wr, wr₄]
  refine WP.block_append (WP.mono (storeY_ok s₆ (fun _ _ h => hp2.inW wr₆ rdi₆ h)
    (fun _ _ h => hp2.inW wr₆ rdi₆ h)) fun s₇ Y₇ => ?_)
  refine WP.mono (rcx_ok s₇) fun s₈ ⟨c₈, g₈, m₈, k₈⟩ => ?_
  obtain gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
      s₈.gpr r = s₀.gpr r := by
    intro r a c e f g h
    rw [g₈ r c, Y₇.gpr, vg₆, g₅ r a g h, vg₄, g₃ r a g h, g₁ r e f, hg]
  obtain r8₆ : s₆.gpr .r8 = 0x3ffffff := by rw [vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄, r8₃]
  obtain r9₆ : s₆.gpr .r9 = 0x1000000 := by
    rw [vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄, g₃ _ (by decide) (by decide) (by decide), r9₁]
  obtain mm₆ : s₆.mem = s₀.mem := by rw [vm₆, m₅, mm₄]
  have hb' := hbig
  simp only [nb] at hb'
  obtain F₇ : Frame [wR (st s₀)] s₆.mem s₇.mem := by rw [← rdi₆]; exact Y₇.frame
  refine ⟨⟨by rw [m₈, ← mm₆]; exact F₇⟩, ?_⟩
  refine ⟨by simp only [nb]; omega_arith, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, rfl, ?_, fun hA => ?_⟩
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp [blkAddr]
  · rw [c₈, Y₇.gpr, vg₆, g₅ _ (by decide) (by decide) (by decide), vg₄,
      g₃ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide), hg,
      rcx_val _ (by omega_arith), nb, Nat.sub_zero]
  · exact gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [g₈ _ (by decide), Y₇.gpr, r8₆]
  · rw [g₈ _ (by decide), Y₇.gpr, r9₆]
  · obtain ⟨a, c, -, -, e, f, g, h⟩ := cs_ne hr
    exact gk r a c e f g h
  · rw [k₈.rd, Y₇.rd, vrd₆, k₅.rd, vrd₄, k₃.rd, k₁.rd, hk.rd]
  · rw [k₈.wr, Y₇.wr, wr₆]
  · rw [k₈.mxcsr, Y₇.mxcsr, vx₆, k₅.mxcsr, vx₄, k₃.mxcsr, k₁.mxcsr, hk.mxcsr]
  · -- The accumulator in quadword 0, `Y` from `powers`, and its limbs in memory.
    obtain L := L₆ hA
    obtain rN₃ : Avx2.rN s₃ = Rn s₀ := by
      simp only [Avx2.rN, Rn, R0, R1]
      rw [r10₃, r11₃, rdi₁, mm₁]
    obtain hN₅ : Avx2.hN s₅ = A0 s₀ := by
      simp only [Avx2.hN, A0]
      rw [a₅, b₅, c₅, rdi₄, mm₄, leNum_acc]
    obtain Y₆ : YInv s₆ (Rn s₀) := by
      rw [← rN₃]
      exact (Y₄.of_y fun i hi k hk => k₅.qz_eq _ _).of_y L.y
    obtain rdi₈ : s₈.gpr .rdi = s₇.gpr .rdi := g₈ _ (by decide)
    obtain M₇ : MemM s₇ := by
      refine ⟨fun i hi => by rw [Y₇.r i hi]; exact Y₆.lob 0 (by decide) i hi, fun i h₁ hi => ?_,
        by rw [Y₇.mask, r8₆]; rfl, by rw [Y₇.pad, r9₆]; rfl⟩
      rw [Y₇.five i h₁ hi, Y₇.r i hi]
      have := Y₆.lob 0 (by decide) i hi
      omega_arith
    obtain V₇ : Limbs26.val (mr s₇) = Limbs26.val (yl s₆ 0) := by
      simp only [Limbs26.val, Y₇.r 0 (by decide), Y₇.r 1 (by decide), Y₇.r 2 (by decide),
        Y₇.r 3 (by decide), Y₇.r 4 (by decide)]
    refine ⟨LaneInv.of_qz (fun r k => k₈.qz_eq r k) (LaneInv.of_hy Y₇.hy
      ⟨Y₆, fun k hk i hi => by have := L.hb k hk i hi; omega_arith, ?_⟩),
      MemY.of_mem ⟨M₇, by rw [V₇]; exact Y₆.lo 0 (by decide)⟩ rdi₈ m₈⟩
    simp only [Nat.mul_zero, blks_zero, Poly1305.absorbAll_nil, wsum]
    rw [L.h 0 (by decide), L.h 1 (by decide), L.h 2 (by decide), L.h 3 (by decide), L.h 4 (by decide),
      L.h 5 (by decide), L.h 6 (by decide), L.h 7 (by decide), hN₅]
    simp only [reduceCtorEq, ↓reduceIte, Poly1305.lanes8, Nat.mul_zero,
      Nat.add_zero]
    exact Nat.ModEq.refl _

/-! ## The loop -/

theorem grp_sub {s₀ : State} {j : Nat} (hj : 8 * j + 8 ≤ nb s₀) :
    Region.Sub ⟨blkAddr s₀ (8 * j), 128⟩ (blR s₀) :=
  Offset.sub_base _ (by omega_arith)

theorem ctx_of {s₀ : State} (hp : APre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hdi : s.gpr .rdi = st s₀) {j : Nat} (hsi : s.gpr .rsi = blkAddr s₀ (8 * j)) (hj : 8 * j + 8 ≤ nb s₀) :
    Ctx s := by
  refine ⟨fun i hi => ?_, fun d _ h => hp.avx2.inRW hwr hdi (by omega_arith)⟩
  have := hp.avx2.bpre.nb_lt
  refine ⟨blR s₀, by rw [hrd, hp.rd]; simp, ?_⟩
  rw [hsi, blkAddr, Offset.add_add]
  exact Offset.contains_base _ (by rcases hi with rfl | rfl <;> omega_arith) (by rcases hi with rfl | rfl <;> omega_arith)

/-- The group of blocks at `rsi`, from the memory the prologue leaves. -/
theorem grp_bytes {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : MemOK s₀ m₁) {j : Nat}
    (hj : 8 * j + 8 ≤ nb s₀) :
    bytesAt m₁ (blkAddr s₀ (8 * j)) 128 = bytesAt s₀.mem (blkAddr s₀ (8 * j)) 128 :=
  bytesAt_frame hm.frame (by
    simpa using (hp.st_bl.symm.sub_left (grp_sub hj)).sub_right (sub_sR _ (by omega_arith))) (by omega_arith)

theorem absorb_grp (s₀ : State) (R X : Nat) (j : Nat) :
    Poly1305.absorbAll R (Poly1305.absorbAll R X (blks s₀ (8 * j))) (bytesAt s₀.mem (blkAddr s₀ (8 * j)) 128) =
      Poly1305.absorbAll R X (blks s₀ (8 * (j + 1))) := by
  rw [← Poly1305.absorbAll_append (by simp only [blks, Poly1305.length_bytesAt]; omega_arith)]
  simp only [blks, blkAddr]
  rw [← Poly1305.bytesAt_add, show 16 * (8 * j) + 128 = 16 * (8 * (j + 1)) by omega_arith]

theorem add128 (s₀ : State) (j : Nat) : blkAddr s₀ (8 * j) + 128 = blkAddr s₀ (8 * (j + 1)) := by
  simp only [blkAddr]
  rw [show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, Offset.add_add,
    show 16 * (8 * j) + 128 = 16 * (8 * (j + 1)) by omega_arith]

theorem group_body_ok {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : MemOK s₀ m₁) {j : Nat}
    (hj : j + 1 < nb s₀ / 8) {s : State} (h : LInv s₀ m₁ j s) :
    WP isa groupBody s fun s' => LInv s₀ m₁ (j + 1) s' ∧ s'.zf = some (decide (nb s₀ / 8 - 1 - j = 1)) := by
  have hb := hp.avx2.bpre.nb_lt
  obtain hc := ctx_of hp h.rd h.wr h.rdi h.rsi (j := j) (by omega_arith)
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s s' = s') (A := H2 s₀ < 4) ?_
    fun hA => group_ok hc (h.acc hA).2 (h.acc hA).1) fun s₁ ⟨v₁, G₁⟩ => ?_)
  · exact WP.block_append (WP.mono (run_ok (fun _ => hc) addMS_eq) fun s₁ h₁ =>
      WP.mono (run_ok (fun _ => hc.of_vec h₁.eq) mulMS_eq) fun s₂ h₂ => vec_trans h₁.eq h₂.eq)
  obtain ⟨vg₁, vm₁, vrd₁, vwr₁, vx₁⟩ := vec_keep v₁
  refine WP.mono (adv_ok s₁) fun s₂ ⟨si₂, cx₂, zf₂, g₂, m₂, k₂⟩ => ?_
  obtain gk : ∀ r, r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r a b => by rw [g₂ r a b, vg₁]
  obtain hcx : s₁.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 8 - 1 - j) := by rw [vg₁, h.rcx]
  refine ⟨⟨hj, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, fun hA => ?_⟩, ?_⟩
  · rw [gk _ (by decide) (by decide), h.rdi]
  · rw [si₂, vg₁, h.rsi, add128]
  · rw [cx₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith),
      Nat.sub_sub]
  · rw [gk _ (by decide) (by decide), h.rdx]
  · rw [gk _ (by decide) (by decide), h.r8]
  · rw [gk _ (by decide) (by decide), h.r9]
  · obtain ⟨-, c, -, e, -⟩ := cs_ne hr
    rw [gk r e c, h.keep r hr]
  · rw [k₂.rd, vrd₁, h.rd]
  · rw [k₂.wr, vwr₁, h.wr]
  · rw [m₂, vm₁, h.mem]
  · rw [k₂.mxcsr, vx₁, h.mxcsr]
  · have G := (G₁ hA).2
    rw [h.mem, h.rsi, grp_bytes hp hm (by omega_arith), absorb_grp] at G
    exact ⟨LaneInv.of_qz (fun r k => k₂.qz_eq r k) G,
      (h.acc hA).2.of_mem (by rw [gk _ (by decide) (by decide)]) (by rw [m₂, vm₁])⟩
  · rw [zf₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]

theorem loop_ok {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : MemOK s₀ m₁) (hG : 1 < nb s₀ / 8) {s : State}
    (h₀ : LInv s₀ m₁ 0 s) : WP isa (.loop groupBody .ne) s (LInv s₀ m₁ (nb s₀ / 8 - 1)) := by
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = nb s₀ / 8 - 1 - j ∧ j < nb s₀ / 8 - 1 ∧ LInv s₀ m₁ j s
  obtain hstep : ∀ n s, Inv n s → WP isa groupBody s (fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ m₁ (nb s₀ / 8 - 1) s') ∨
      (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI⟩
    refine WP.mono (group_body_ok hp hm (by omega_arith) hI) fun s' ⟨h', hz⟩ => ?_
    by_cases e : nb s₀ / 8 - 1 - j = 1
    · have e' : j + 1 = nb s₀ / 8 - 1 := by omega_arith
      exact .inl ⟨by simp [eval, hz, e], e' ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, e], nb s₀ / 8 - 1 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, h'⟩
  exact WP.loop (M := isa) Inv hstep _ s ⟨0, rfl, by omega_arith, h₀⟩

/-! ## The epilogue -/

theorem epi_eq : Impl.Poly1305.X86_64.Avx2.consts2 ++ last ++ sumLanes ++ Impl.Poly1305.X86_64.Avx2.fullCarry ++
    Impl.Poly1305.X86_64.Avx2.reduce ++
    Impl.Poly1305.X86_64.Avx2.storeH ++
    ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr) =
    Impl.Poly1305.X86_64.Avx2.consts2 ++ (last ++ (sumLanes ++ ((Impl.Poly1305.X86_64.Avx2.fullCarry ++
      Impl.Poly1305.X86_64.Avx2.reduce) ++
      (Impl.Poly1305.X86_64.Avx2.storeH ++
        ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr))))) := by
  simp only [List.append_assoc]

theorem epi_ok {s₀ : State} (hp : APre s₀) {M₁ : Mem} (hm : MemOK s₀ M₁) {s : State}
    (h : LInv s₀ M₁ (nb s₀ / 8 - 1) s) :
    WP isa (.block (Impl.Poly1305.X86_64.Avx2.consts2 ++ last ++ sumLanes ++
      Impl.Poly1305.X86_64.Avx2.fullCarry ++ Impl.Poly1305.X86_64.Avx2.reduce ++
      Impl.Poly1305.X86_64.Avx2.storeH ++
      ([.vop .vzeroupper, .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr))) s
      (TailPre s₀ (8 * (nb s₀ / 8))) := by
  have hp2 := hp.avx2
  have hb := hp2.bpre.nb_lt
  have hlt := h.lt
  obtain h1 : 1 ≤ nb s₀ / 8 := by omega_arith
  rw [epi_eq]
  refine WP.block_append (WP.mono (consts2_ok s) fun s₁ ⟨ax₁, r10₁, g₁, m₁, k₁⟩ => ?_)
  have gk₁ : ∀ r, r ≠ .rax → r ≠ .r10 → s₁.gpr r = s.gpr r := g₁
  obtain hc : Ctx s₁ := ctx_of hp (by rw [k₁.rd, h.rd]) (by rw [k₁.wr, h.wr])
    (by rw [gk₁ _ (by decide) (by decide), h.rdi]) (by rw [gk₁ _ (by decide) (by decide), h.rsi]) (by omega_arith)
  obtain r8₁ : s₁.gpr .r8 = 0x3ffffff := by rw [gk₁ _ (by decide) (by decide), h.r8]
  obtain r9₁ : s₁.gpr .r9 = 0x1000000 := by rw [gk₁ _ (by decide) (by decide), h.r9]
  -- The last group.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₁ s' = s') (A := H2 s₀ < 4) ?_
    fun hA => last_ok r8₁ r9₁ hc ((h.acc hA).1.of_qz fun r k => k₁.qz_eq r k)) fun s₂ ⟨v₂, L₂⟩ => ?_)
  · rw [last_eq]
    exact WP.block_append (WP.mono (run_ok (fun _ => hc) addS_eq) fun _ h₁ =>
      WP.block_append (WP.mono (run_ok (fun h => by cases h) shS_eq) fun _ h₂ =>
        WP.mono (run_ok (fun h => by cases h) mulS_eq) fun _ h₃ => vec_trans h₁.eq (vec_trans h₂.eq h₃.eq)))
  obtain ⟨vg₂, vm₂, vrd₂, vwr₂, vx₂⟩ := vec_keep v₂
  obtain r8₂ : s₂.gpr .r8 = 0x3ffffff := by rw [vg₂, r8₁]
  -- The sum of the quadwords.
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₂ s' = s') (A := H2 s₀ < 4)
    (WP.mono (run_ok (fun h => by cases h) smS_eq) fun _ h => h.eq)
    fun hA => sumLanes_ok r8₂ (L₂ hA).2.1) fun s₃ ⟨v₃, S₃⟩ => ?_)
  obtain ⟨vg₃, vm₃, vrd₃, vwr₃, vx₃⟩ := vec_keep v₃
  -- `h mod p`, on quadword 0 (`vg_poly1305_blocks_avx2`'s code).
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s₃ s' = s') (A := H2 s₀ < 4)
    (WP.mono (Avx2.run_ok (fun h => by cases h) Avx2.fnS_eq) fun _ h => h.eq)
    fun hA => finish_ok (by rw [vg₃, r8₂]) (by rw [vg₃, vg₂, ax₁]) (by rw [vg₃, vg₂, r10₁])
      (fun k hk i hi => by rw [hv_avx2 _ hk]; exact (S₃ hA).hball k (by omega_arith) i hi)
      (fun i hi => by rw [hv_avx2 _ (by decide)]; exact (S₃ hA).hb i hi)) fun s₄ ⟨v₄, F₄⟩ => ?_)
  obtain ⟨vg₄, vm₄, vrd₄, vwr₄, vx₄⟩ := vec_keep v₄
  obtain g₄ : ∀ r, r ≠ .rax → r ≠ .r10 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [vg₄, vg₃, vg₂, gk₁ r a b]
  obtain rdi₄ : s₄.gpr .rdi = st s₀ := by rw [g₄ _ (by decide) (by decide), h.rdi]
  obtain wr₄ : s₄.wr = s₀.wr := by rw [vwr₄, vwr₃, vwr₂, k₁.wr, h.wr]
  obtain mm₄ : s₄.mem = M₁ := by rw [vm₄, vm₃, vm₂, m₁, h.mem]
  -- The accumulator stored.
  refine WP.block_append (WP.mono (storeH_ok fun d hd => hp2.inW wr₄ rdi₄ (by omega_arith)) fun s₆ sp₆ => ?_)
  refine WP.mono (fin3_ok s₆) fun s₇ ⟨si₇, dx₇, g₇, m₇, mx₇, rd₇, wr₇⟩ => ?_
  obtain g₆ : ∀ r, r ≠ .rax → r ≠ .r10 → s₆.gpr r = s.gpr r := fun r a b => by
    rw [sp₆.gpr, g₄ r a b]
  obtain hmx : s₇.mxcsr = s₀.mxcsr := by
    rw [mx₇, sp₆.mxcsr, vx₄, vx₃, vx₂, k₁.mxcsr, h.mxcsr]
  obtain hframe : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₇.mem := by
    rw [m₇]
    refine (hm.frame.mono (by simp)).trans ?_
    rw [← mm₄]
    exact sp₆.frame.mono (by rw [rdi₄]; simp)
  refine ⟨by omega_arith, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, hframe, by rw [hmx], fun key msg hr => ?_⟩
  · rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), h.rdi]
  · rw [si₇, g₆ _ (by decide) (by decide), h.rsi, add128, Nat.sub_add_cancel h1]
  · rw [dx₇, g₆ _ (by decide) (by decide), h.rdx]
    apply BitVec.eq_of_toNat_eq
    rw [and7_toNat, toNat_ofNat_lt (by omega_arith)]
    simp only [nb]
    omega_arith
  · obtain ⟨a, -, c, d, -, -, g, -⟩ := cs_ne hr
    rw [g₇ r d c, g₆ r a g, h.keep r hr]
  · rw [rd₇, sp₆.rd, vrd₄, vrd₃, vrd₂, k₁.rd, h.rd]
  · rw [wr₇, sp₆.wr, wr₄]
  · -- The accumulator represents the blocks absorbed.
    obtain hA := H2_lt hr
    obtain ⟨hlen, hkey, hacc⟩ := hr
    obtain hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := by rw [off_24]; exact hkey
    obtain hA0 : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
    obtain hlt : A0 s₀ < P := by rw [← hA0]; exact Poly1305.accumulate_lt _ _
    obtain L := (L₂ hA).2.2
    obtain S := (S₃ hA).h
    obtain ⟨-, F, Fb⟩ := F₄ hA
    rw [gk₁ _ (by decide) (by decide), h.rsi, m₁, h.mem, grp_bytes hp hm (by omega_arith), absorb_grp,
      Nat.sub_add_cancel h1] at L
    obtain e₅ : Avx2.h0 s₄ = Avx2.hv s₄ 0 := by
      funext i; simp only [Avx2.h0, Avx2.hv]
    obtain e₃ : Limbs26.val (Avx2.hv s₃ 0) = hval s₃ 0 :=
      congrArg Limbs26.val (funext fun i => hv_avx2 _ (by decide) i)
    obtain ⟨W, -, -⟩ := Limbs26.words_val (o := Avx2.h0 s₄) (by rw [e₅]; exact Fb)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega_arith
    · rw [← off_24, key_frame hframe, hkey']
    · rw [leNum_acc, m₇, ← rdi₄, sp₆.w0, sp₆.w1, sp₆.w2, W, e₅, F, e₃, ← hkey', clamp_key,
        Poly1305.accumulate_append hlen]
      change _ = Poly1305.absorbAll (Rn s₀) (accumulate (Rn s₀) msg) _
      rw [hA0, (S.trans L : _ ≡ _ [MOD P]),
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]

/-! ## The whole function -/

theorem body_ok {s₀ : State} (hp : APre s₀) (hbig : 40 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa body s (TailPre s₀ (8 * (nb s₀ / 8))) :=
  WP.seq (WP.mono (pro_ok hp hbig hg hm hk) fun _ h₁ =>
    WP.seq (WP.mono (loop_ok hp h₁.1 (by omega_arith) h₁.2) fun _ h₂ => epi_ok hp h₁.1 h₂))

/-- The vector code, from at least 40 blocks. -/
theorem big_ok {s₀ : State} (hp : APre s₀) (hge : 40 ≤ nb s₀) : WP isa big s₀ (Post s₀) := by
  have hb := hp.avx2.bpre.nb_lt
  refine WP.seq (WP.mono (body_ok hp hge rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (Avx2.test_ok s₂) fun s₃ ⟨z₃, g₃, m₃, mx₃, rd₃, wr₃⟩ => ?_)
  have h₃ := h₂.congr g₃ m₃ mx₃ rd₃ wr₃
  refine WP.ite (s₃.gpr .rdx &&& s₃.gpr .rdx == 0) (by simp [eval, z₃, g₃]) (fun h => ?_)
    (fun _ => tail_ok hp.avx2 h₃)
  have e : 8 * (nb s₀ / 8) = nb s₀ := by
    have := h₃.rdx
    simp only [BitVec.and_self, beq_iff_eq] at h
    rw [h] at this
    have := congrArg BitVec.toNat this
    rw [toNat_ofNat_lt (by omega_arith)] at this
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
    simp only [nb] at this ⊢
    omega_arith
  exact WP.block_nil (M := isa) (done_ok hp.avx2 (e ▸ h₃))

theorem correct {s₀ : State} (hp : APre s₀) (hS : 16 ≤ (s₀.gpr .rsp).toNat) :
    WP isa blocksAvx512 s₀ (Post s₀) := by
  refine WP.seq (WP.mono (cmp_ok s₀) fun s₁ ⟨g₁, m₁, k₁, cf₁⟩ => ?_)
  have k₁' : Avx2.VKeep s₀ s₁ := ⟨k₁.xmm, k₁.ymmHi, k₁.mxcsr, k₁.rd, k₁.wr⟩
  refine WP.ite (decide (nb s₀ < 40)) (by simp [eval, cf₁]) (fun _ => ?_) (fun hge => ?_)
  · -- The code of `vg_poly1305_blocks_avx2`, from `s₁`, which has the registers and memory of `s₀`.
    have l₁ : Avx2.Like s₀ s₁ := ⟨k₁.rd, k₁.wr, by rw [g₁], by rw [g₁], by rw [g₁], by rw [g₁]⟩
    have hp₁ := hp.congr l₁
    refine WP.mono (Avx2.correct hp₁.avx2 (hp₁.g16 (by rw [l₁.rsp]; exact hS))) fun s' h => ?_
    exact Avx2.post_congr (hp.g16 hS) hp.avx2 (fun r _ => by rw [g₁]) l₁.rdi l₁.rsi l₁.rdx
      (by rw [m₁]; exact Frame.refl _ _) (by rw [k₁.mxcsr]) h
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    exact Avx2.guard_ok hp.avx2 (hp.g16 hS) g₁ m₁ k₁' fun u hu =>
      big_ok (hp.congr hu) (by simp only [nb, hu.rdx]; omega_arith)

theorem blocksAvx512_ok (s : State) (hs : blocksAvx512X86_64.pre s) :
    ∃ t s', Exec isa blocksAvx512 s t s' ∧ abiPreserved s s' ∧ blocksAvx512X86_64.post s s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  exact correct ⟨h1, h2, h3, h4, h5, h6, h7⟩ h8

/-! ## Constant time -/

theorem blocksAvx512_ct : ConstantTime isa blocksAvx512X86_64.pre blocksAvx512X86_64.pub blocksAvx512 := by
  refine VG.Taint.constantTime_of_sem (A := taintMx) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_
    (by taint_decide_ops [Mcdt.X86_64.enterOpMx_ok])
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3⟩, h4, h5⟩
  refine ⟨Taint.agree_ofRegs fun r hr => ?_, h5⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Poly1305.X86_64.Avx512
