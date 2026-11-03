module

public import VerifiedGarbage.Impl.Weierstrass.RISCV64.GenWide
public import VerifiedGarbage.Proof.Framework.RISCV64.Wide
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Product
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.FieldRV
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Words
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad64
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Ed25519.RISCV64.Packed
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Fn
import VerifiedGarbage.Proof.Mont.Read

/-!
# Arithmetic modulo any odd modulus of seven words or more on RISC-V: the proofs

The functions of `Impl/Weierstrass/RISCV64/GenWide.lean`, for numbers of `k`
words (`7 ≤ k ≤ 30`) and an odd modulus `m < 2^(64 k)`, meet the contracts by
register of `Proof/Weierstrass/RISCV64/FieldRV.lean` (`mul_rv`, `add_rv`,
`sub_rv`), whatever `k` and `m`, from the steps up:

* a row of multiply-accumulate steps, of differences with borrows and of sums
  with carries, each by induction on its words;
* the rounds of Montgomery's multiplication by operand scanning (CIOS), whose
  invariant `V 2^(64 i) = a (b mod 2^(64 i)) + Q m` with `Q < 2^(64 i)` keeps
  `V` below `2^(64 k) + m`, so that the last value is below `2 m`;
* the final subtraction by a mask, the modulus's words and `T = 0`;
* the operations on aligned pointers, the byte-wise copies, and the entry.

Each modulus's proof (`Proof/Weierstrass/RISCV64/P521Field/Verified.lean`)
adds the facts of its modulus (`WideOk`), and constant time by taint analysis
of its code (`Proof/Weierstrass/RISCV64/GenWide/CT.lean`).
-/

@[expose] public section

/-!
## Arithmetic modulo a wide modulus on RISC-V: a multiply-accumulate step

The arithmetic of `macStep` (`Impl/Weierstrass/RISCV64/GenWide.lean`) on
registers: `t0 + 2⁶⁴ a5 := a6 · a4 + a7 + a5` (`mac_ok`), which cannot
overflow two words.
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Wide

variable {s : State}

/-- The two words of `x y + t + c` for words `x`, `y`, `t`, `c`, by `mul`,
`mulhu` and two sums with `sltu` carries. -/
theorem mac_nat {x y t c lo hi c₁ u c₂ : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (ht : t < 2 ^ 64)
    (hc : c < 2 ^ 64) (hp : lo + 2 ^ 64 * hi = x * y)
    (h₁ : u + 2 ^ 64 * c₁ = lo + t) {v : Nat} (h₂ : v + 2 ^ 64 * c₂ = u + c) :
    v + 2 ^ 64 * (hi + c₁ + c₂) = x * y + t + c ∧ hi + c₁ + c₂ < 2 ^ 64 := by
  have hxy : x * y ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  constructor
  · omega
  · have hv : v + 2 ^ 64 * (hi + c₁ + c₂) = x * y + t + c := by omega
    omega

set_option linter.unusedSimpArgs false in
/-- `t0 + 2⁶⁴ a5 := a6 · a4 + a7 + a5`, through `a1` and `t3`. -/
theorem mac_ok :
    WP isa (.block [.mul .t0 .a6 .a4, .mulhu .a1 .a6 .a4, .add .t0 .t0 .a7, .sltu .t3 .t0 .a7,
        .add .a1 .a1 .t3, .add .t0 .t0 .a5, .sltu .t3 .t0 .a5, .add .a5 .a1 .t3]) s fun s' =>
      (s'.gpr .t0).toNat + 2 ^ 64 * (s'.gpr .a5).toNat =
        (s.gpr .a6).toNat * (s.gpr .a4).toNat + (s.gpr .a7).toNat + (s.gpr .a5).toNat ∧
      Keeps [.t0, .a1, .t3, .a5] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mul, exec_mulhu, exec_add, exec_sltu,
    RegUpd.gpr_write, ite_true, ite_false, Option.some.injEq, exists_eq_left', reduceCtorEq]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · generalize hX : s.gpr .a6 = X at *
    generalize hY : s.gpr .a4 = Y at *
    generalize hT : s.gpr .a7 = Tw at *
    generalize hC : s.gpr .a5 = C at *
    have hp := mul_words X Y
    generalize BitVec.ofNat 64 (X.toNat * Y.toNat / 2 ^ 64) = H at *
    have e₁ := carry (X * Y) Tw
    have l₁ := carry_le (X * Y + Tw < Tw)
    generalize (if X * Y + Tw < Tw then (1 : BitVec 64) else 0) = k₁ at *
    have e₂ := carry (X * Y + Tw) C
    have l₂ := carry_le (X * Y + Tw + C < C)
    generalize (if X * Y + Tw + C < C then (1 : BitVec 64) else 0) = k₂ at *
    have m := mac_nat X.isLt Y.isLt Tw.isLt C.isLt hp e₁ e₂
    have hA : (H + k₁).toNat = H.toNat + k₁.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have hB : (H + k₁ + k₂).toNat = H.toNat + k₁.toNat + k₂.toNat := by
      rw [BitVec.toNat_add, hA, Nat.mod_eq_of_lt (by omega)]
    rw [hB]; exact m.1
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: a row of multiply-accumulate steps

`macRow k xb xo δ n` (`Impl/Weierstrass/RISCV64/GenWide.lean`) from a state
with `a3 = b` (`Ctx`): word `j < n` of `T` becomes word `j` of
`T[δ …] + x · a4 + a5`, for the words `x` at `X + xo + 8 δ …` (`X` in `xb`),
with the carry out in `a5` (`row_ok`). Only the first `n` words of `T` are
written.
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- The registers a step writes. -/
abbrev clobS : List Reg := [.t0, .a1, .t3, .a5, .a6, .a7]

/-- After `j` steps of a row from `s0`. -/
structure RowInv (k : Nat) (b X : Addr) (xo δ : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobS → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * j⟩] s0.mem s.mem
  val : colsV (fun i => dw s.mem b (T k + 8 * i)) j + (2 ^ 64) ^ j * (s.gpr .a5).toNat =
    colsV (fun i => dw s0.mem b (T k + 8 * (i + δ)) + dw s0.mem X (xo + 8 * (i + δ)) * (s0.gpr .a4).toNat) j +
      (s0.gpr .a5).toNat

theorem RowInv.zero {k : Nat} {b X : Addr} {xo δ : Nat} (s0 : State) : RowInv k b X xo δ s0 0 s0 :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, by simp [colsV]⟩

theorem colsV_congr {f g : Nat → Nat} : ∀ {n}, (∀ i < n, f i = g i) → colsV f n = colsV g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [colsV]; rw [colsV_congr (fun i hi => h i (by omega)), h n (by omega)]

theorem ctx_of {b : Addr} {s0 s : State} (hc : Ctx b s0) (h3 : s.gpr .a3 = s0.gpr .a3) (hw : s.wr = s0.wr) :
    Ctx b s :=
  ⟨h3.trans hc.a3, hc.al, by rw [hw]; exact hc.wr⟩

/-- What a row needs of its operands. -/
structure RowOk (k : Nat) (b X : Addr) (xb : Reg) (xo δ n : Nat) (s0 : State) : Prop where
  ctx : Ctx b s0
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  hx : s0.gpr xb = X
  hxb : xb ∉ clobS
  hxo : ∀ i < n, xo + 8 * (i + δ) < 2048
  xal : ∀ i < n, (X + BitVec.ofNat 64 (xo + 8 * (i + δ))).toNat % 8 = 0
  xin : ∀ i < n, InRegions (s0.rd ++ s0.wr) (X + BitVec.ofNat 64 (xo + 8 * (i + δ))) 8
  xdis : ∀ i < n, ∀ j ≤ n,
    Region.Disjoint ⟨X + BitVec.ofNat 64 (xo + 8 * (i + δ)), 8⟩ ⟨b + BitVec.ofNat 64 (T k), 8 * j⟩
  top : T k + 8 * (n + δ) ≤ 2048
  t8 : T k % 8 = 0

set_option linter.unusedSimpArgs false in
/-- Step `j` of a row. -/
theorem rowStep_ok {k : Nat} {b X : Addr} {xb : Reg} {xo δ n : Nat} {s0 : State} (hR : RowOk k b X xb xo δ n s0)
    {j : Nat} (hj : j < n) {s : State} (h : RowInv k b X xo δ s0 j s) :
    WP isa (.block (macStep xb (xo + 8 * (j + δ)) (T k + 8 * (j + δ)) (T k + 8 * j))) s
      (RowInv k b X xo δ s0 (j + 1)) := by
  have hc : Ctx b s := ctx_of hR.ctx (h.gpr _ (by decide)) h.wr
  have hT := hR.top
  have ht8 := hR.t8
  have hxo := hR.hxo j hj
  have hb := hR.nowrap
  unfold macStep
  -- The word `x`.
  refine wp_ld (by omega) (by rw [h.gpr _ hR.hxb, hR.hx]) (hR.xal j hj)
    (by rw [h.rd, h.wr]; exact hR.xin j hj) fun s1 u1 => ?_
  refine ld_ok (ctx_of hc (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 => ?_
  show WP isa (.block ([.mul .t0 .a6 .a4, .mulhu .a1 .a6 .a4, .add .t0 .t0 .a7, .sltu .t3 .t0 .a7,
    .add .a1 .a1 .t3, .add .t0 .t0 .a5, .sltu .t3 .t0 .a5, .add .a5 .a1 .t3] ++
    [Instr.store .d .t0 .a3 (T k + 8 * j)])) s2 _
  refine WP.block_append (WP.mono mac_ok fun s3 ⟨e3, k3⟩ => ?_)
  have hc3 : Ctx b s3 := ctx_of hc (by rw [k3.1 _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [k3.2.2.2.1, u2.wr, u1.wr])
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  -- Facts.
  have m3 : s3.mem = s.mem := by rw [k3.2.1, u2.mem, u1.mem]
  have g3 : ∀ r, r ∉ clobS → s3.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k3.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), u2.other r hr.2.2.2.2.2,
      u1.other r hr.2.2.2.2.1]
  have a6 : s2.gpr .a6 = s.mem.readW (X + BitVec.ofNat 64 (xo + 8 * (j + δ))) 64 := by
    rw [u2.other _ (by decide), u1.gpr]
  have a7 : s2.gpr .a7 = s.mem.readW (b + BitVec.ofNat 64 (T k + 8 * (j + δ))) 64 := by
    rw [u2.gpr, u1.mem]
  have a4 : s2.gpr .a4 = s.gpr .a4 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have a5 : s2.gpr .a5 = s.gpr .a5 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  have hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * j)) (s3.gpr .t0) := by
    rw [u4.mem, m3]
  -- The words read are those of `s0`.
  have hX0 : dw s.mem X (xo + 8 * (j + δ)) = dw s0.mem X (xo + 8 * (j + δ)) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact hR.xdis j hj j (by omega)
  have hT0 : dw s.mem b (T k + 8 * (j + δ)) = dw s0.mem b (T k + 8 * (j + δ)) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
  refine ⟨fun r hr => by rw [u4.gpr, g3 r hr, h.gpr r hr], by rw [u4.rd, k3.2.2.1, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, k3.2.2.2.1, u2.wr, u1.wr, h.wr], by rw [u4.sp, k3.2.2.2.2, u2.sp, u1.sp, h.sp], ?_, ?_⟩
  · rw [hm4]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : colsV (fun i => dw s4.mem b (T k + 8 * i)) j = colsV (fun i => dw s.mem b (T k + 8 * i)) j :=
      colsV_congr fun i hi => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have e3' : (s3.gpr .t0).toNat + 2 ^ 64 * (s3.gpr .a5).toNat =
        dw s0.mem X (xo + 8 * (j + δ)) * (s0.gpr .a4).toNat + dw s0.mem b (T k + 8 * (j + δ)) +
          (s.gpr .a5).toNat := by
      rw [e3, a6, a7, a4, a5, ← hX0, ← hT0, h.gpr _ (by decide)]; rfl
    show colsV (fun i => dw s4.mem b (T k + 8 * i)) j + (2 ^ 64) ^ j * dw s4.mem b (T k + 8 * j) +
        (2 ^ 64) ^ (j + 1) * (s4.gpr .a5).toNat =
      colsV (fun i => dw s0.mem b (T k + 8 * (i + δ)) + dw s0.mem X (xo + 8 * (i + δ)) * (s0.gpr .a4).toNat) j +
        (2 ^ 64) ^ j * (dw s0.mem b (T k + 8 * (j + δ)) + dw s0.mem X (xo + 8 * (j + δ)) * (s0.gpr .a4).toNat) +
        (s0.gpr .a5).toNat
    rw [hcw, hm4, dw_write_self, u4.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    generalize colsV (fun i => dw s.mem b (T k + 8 * i)) j = C at *
    have key : E * (s3.gpr .t0).toNat + E * 2 ^ 64 * (s3.gpr .a5).toNat =
        E * (s.gpr .a5).toNat + E * (dw s0.mem b (T k + 8 * (j + δ)) +
          dw s0.mem X (xo + 8 * (j + δ)) * (s0.gpr .a4).toNat) := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e3']; congr 1; omega
    omega

/-- The row. -/
theorem row_ok {k : Nat} {b X : Addr} {xb : Reg} {xo δ n : Nat} {s0 : State}
    (hR : RowOk k b X xb xo δ n s0) :
    ∀ j ≤ n, WP isa (.block ((List.range j).flatMap fun i =>
      macStep xb (xo + 8 * (i + δ)) (T k + 8 * (i + δ)) (T k + 8 * i))) s0 (RowInv k b X xo δ s0 j)
  | 0, _ => WP.block_nil (RowInv.zero s0)
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (row_ok hR j (by omega)) fun s h => rowStep_ok hR (j := j) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: a round of the multiplication

`mulRound k i` (`Impl/Weierstrass/RISCV64/GenWide.lean`): the `k + 2` words of
`T` become the `k + 1` words of `T` before plus `a bᵢ` (`mulRound_ok`).
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- The `n` words of `T`. -/
abbrev tv (k : Nat) (m : Mem) (b : Addr) (n : Nat) : Nat := colsV (fun i => dw m b (T k + 8 * i)) n

/-- The `n` words at `X`. -/
abbrev xv (m : Mem) (X : Addr) (n : Nat) : Nat := colsV (fun i => dw m X (8 * i)) n

theorem colsV_add' (f g : Nat → Nat) : ∀ n, colsV (fun i => f i + g i) n = colsV f n + colsV g n
  | 0 => rfl
  | n + 1 => by simp only [colsV]; rw [colsV_add' f g n, Nat.mul_add]; omega

theorem colsV_mul (f : Nat → Nat) (c : Nat) : ∀ n, colsV (fun i => f i * c) n = colsV f n * c
  | 0 => by simp [colsV]
  | n + 1 => by simp only [colsV]; rw [colsV_mul f c n, Nat.add_mul, Nat.mul_assoc]

theorem colsV_succ (f : Nat → Nat) (n : Nat) : colsV f (n + 1) = colsV f n + (2 ^ 64) ^ n * f n := rfl

/-- What a round needs of the working space and of `a`. -/
structure MulOk (k : Nat) (b A : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  a : s.gpr .t4 = A
  aal : A.toNat % 8 = 0
  ain : ∀ i < k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  adis : ∀ i < k, ∀ j ≤ k + 2,
    Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ ⟨b + BitVec.ofNat 64 (T k), 8 * j⟩
  k7 : 7 ≤ k
  k32 : k ≤ 30

theorem MulOk.of {k : Nat} {b A : Addr} {s s' : State} (h : MulOk k b A s) (h3 : s'.gpr .a3 = s.gpr .a3)
    (h4 : s'.gpr .t4 = s.gpr .t4) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : MulOk k b A s' :=
  ⟨ctx_of h.ctx h3 hwr, h.nowrap, h4.trans h.a, h.aal, by rw [hrd, hwr]; exact h.ain, h.adis, h.k7, h.k32⟩

theorem T_facts (k : Nat) (h₁ : 1 ≤ k) (h : k ≤ 30) : T k % 8 = 0 ∧ T k + 8 * (k + 2) ≤ 2048 := by
  unfold T; omega

/-- `T` after a round of `a bᵢ`: only `T`'s `k + 2` words written. -/
theorem mulRound_ok {k : Nat} {b A B : Addr} {i : Nat} {s : State} (h : MulOk k b A s)
    (h5 : s.gpr .t5 = B) (hBal : (B + BitVec.ofNat 64 (8 * i)).toNat % 8 = 0) (hi : 8 * i < 2048)
    (hBin : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8) :
    WP isa (.block (mulRound k i)) s fun s' =>
      (∀ r, r ∉ .a4 :: clobS → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s.mem s'.mem ∧
      tv k s'.mem b (k + 2) = tv k s.mem b (k + 1) + xv s.mem A k * dw s.mem B (8 * i) := by
  obtain ⟨t8, ttop⟩ := T_facts k (by have := h.k7; omega) h.k32
  have hb := h.nowrap
  unfold mulRound
  refine wp_ld hi (by rw [h5]) hBal hBin fun s1 u1 => wp_li (by decide) fun s2 u2 => ?_
  show WP isa (.block (macRow k .t4 0 0 k ++ [.load .d .a7 .a3 (T k + 8 * k), .add .t0 .a7 .a5,
    .sltu .t3 .t0 .a5, .store .d .t0 .a3 (T k + 8 * k), .store .d .t3 .a3 (T k + 8 * (k + 1))])) s2 _
  -- The row.
  have hR : RowOk k b A .t4 0 0 k s2 :=
    { ctx := ctx_of h.ctx (by rw [u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u2.wr, u1.wr])
      nowrap := hb
      hx := by rw [u2.other _ (by decide), u1.other _ (by decide), h.a]
      hxb := by decide
      hxo := fun i hi => by omega
      xal := fun i _ => al8 h.aal (by omega)
      xin := fun i hi => by rw [u2.rd, u2.wr, u1.rd, u1.wr, Nat.zero_add, Nat.add_zero]; exact h.ain i hi
      xdis := fun i hi j hj => by rw [Nat.zero_add, Nat.add_zero]; exact h.adis i hi j (by omega)
      top := by omega
      t8 := t8 }
  refine WP.block_append (WP.mono (row_ok hR k (Nat.le_refl _)) fun s3 h3 => ?_)
  have hc3 : Ctx b s3 := ctx_of hR.ctx (h3.gpr _ (by decide)) h3.wr
  refine ld_ok hc3 (by omega) (by omega) fun s4 u4 => wp_add fun s5 u5 => wp_sltu fun s6 u6 => ?_
  have hc6 : Ctx b s6 := ctx_of hc3 (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide)])
    (by rw [u6.wr, u5.wr, u4.wr])
  refine sd_ok hc6 (by omega) (by omega) fun s7 u7 => ?_
  have hc7 : Ctx b s7 := ctx_of hc6 (by rw [u7.gpr]) u7.wr
  refine sd_ok hc7 (by omega) (by omega) fun s8 u8 => WP.block_nil ?_
  -- Registers.
  have m2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have g2 : ∀ r, r ∉ .a4 :: clobS → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other r hr.2.2.2.2.1, u1.other r hr.1]
  have g6 : ∀ r, r ∉ .a4 :: clobS → s6.gpr r = s3.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u6.other r hr.2.2.2.1, u5.other r hr.2.1, u4.other r hr.2.2.2.2.2.2]
  have m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have hm8 : s8.mem = (s3.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * k)) (s6.gpr .t0)).writeW
      (b + BitVec.ofNat 64 (T k + 8 * (k + 1))) (s6.gpr .t3) := by
    rw [u8.mem, u7.mem, u7.gpr, m6]
  refine ⟨fun r hr => by
      rw [u8.gpr, u7.gpr, g6 r hr, h3.gpr r (fun h' => hr (List.mem_cons_of_mem _ h')), g2 r hr],
    by rw [u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, h3.rd, u2.rd, u1.rd],
    by rw [u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, h3.wr, u2.wr, u1.wr],
    by rw [u8.sp, u7.sp, u6.sp, u5.sp, u4.sp, h3.sp, u2.sp, u1.sp], ?_, ?_⟩
  · rw [hm8, ← m2]
    refine ((h3.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · -- The words of the row, then the top two.
    have hv := h3.val
    have hTk : dw s3.mem b (T k + 8 * k) = dw s2.mem b (T k + 8 * k) :=
      dw_frame h3.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
    have a7 : (s4.gpr .a7).toNat = dw s2.mem b (T k + 8 * k) := by rw [u4.gpr, ← hTk]; rfl
    have a5 : s4.gpr .a5 = s3.gpr .a5 := u4.other _ (by decide)
    have e6 := carry (s4.gpr .a7) (s4.gpr .a5)
    have t0 : s6.gpr .t0 = s4.gpr .a7 + s4.gpr .a5 := by rw [u6.other _ (by decide), u5.gpr]
    have t3 : s6.gpr .t3 = if s4.gpr .a7 + s4.gpr .a5 < s4.gpr .a5 then 1 else 0 := by
      rw [u6.gpr, u5.gpr, u5.other _ (by decide)]
    have hlow : tv k s8.mem b k = tv k s3.mem b k :=
      colsV_congr fun j hj => by
        rw [hm8, dw_write_other _ _ _ (by omega) (by omega) (by omega),
          dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have hk0 : dw s8.mem b (T k + 8 * k) = (s6.gpr .t0).toNat := by
      rw [hm8, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self]
    have hk1 : dw s8.mem b (T k + 8 * (k + 1)) = (s6.gpr .t3).toNat := by rw [hm8, dw_write_self]
    have hrow : colsV (fun i => dw s2.mem b (T k + 8 * (i + 0)) + dw s2.mem A (0 + 8 * (i + 0)) *
        (s2.gpr .a4).toNat) k = tv k s.mem b k + xv s.mem A k * dw s.mem B (8 * i) := by
      rw [colsV_add', colsV_mul, m2]
      simp only [Nat.add_zero, Nat.zero_add]
      rw [u2.other _ (by decide), u1.gpr]; rfl
    have a50 : (s2.gpr .a5).toNat = 0 := by rw [u2.gpr]; rfl
    rw [hrow, a50, Nat.add_zero] at hv
    show tv k s8.mem b k + (2 ^ 64) ^ k * dw s8.mem b (T k + 8 * k) +
        (2 ^ 64) ^ (k + 1) * dw s8.mem b (T k + 8 * (k + 1)) =
      tv k s.mem b k + (2 ^ 64) ^ k * dw s.mem b (T k + 8 * k) + xv s.mem A k * dw s.mem B (8 * i)
    rw [hlow, hk0, hk1, t0, t3, show (2 ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 from Nat.pow_succ .., ← m2]
    rw [m2] at a7 ⊢
    rw [a5] at e6
    rw [← m2] at hv
    generalize (2 ^ 64) ^ k = E at *
    have key : E * (s4.gpr .a7 + s3.gpr .a5).toNat +
        E * 2 ^ 64 * (if s4.gpr .a7 + s3.gpr .a5 < s3.gpr .a5 then (1 : BitVec 64) else 0).toNat =
        E * (s4.gpr .a7).toNat + E * (s3.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, e6]
    rw [m2] at hv
    change tv k s3.mem b k + E * (s3.gpr .a5).toNat = _ at hv
    rw [a5, ← a7]
    omega

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: a round of the reduction

`redRound k` (`Impl/Weierstrass/RISCV64/GenWide.lean`): for the quotient word
`q = T₀ m' mod 2⁶⁴`, `T + q m` is a multiple of `2⁶⁴`, and the `k + 1` words of
`T` become `(T + q m) / 2⁶⁴` (`redRound_ok`), but for a carry out of the top
word, which the caller's bounds rule out.
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_mul)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- `T₀ + q m₀ = 2⁶⁴ ([T₀ ≠ 0] + ⌊q m₀ / 2⁶⁴⌋)` for `q = T₀ m' mod 2⁶⁴`, as `m₀ m' ≡ -1`. -/
theorem quot_nat {t m' n0 : Nat} (ht : t < 2 ^ 64) (hinv : n0 * m' % 2 ^ 64 = 2 ^ 64 - 1) :
    t * m' % 2 ^ 64 * n0 % 2 ^ 64 + t = if t = 0 then 0 else 2 ^ 64 := by
  have e : t * m' % 2 ^ 64 * n0 % 2 ^ 64 = t * (2 ^ 64 - 1) % 2 ^ 64 := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, Nat.mul_comm m' n0, hinv, Nat.mod_mul_mod]
  rw [e]
  by_cases h0 : t = 0
  · subst h0; simp
  · simp only [h0, ↓reduceIte]
    have : t * (2 ^ 64 - 1) = (2 ^ 64 - t) + 2 ^ 64 * (t - 1) := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_sub, Nat.mul_one]
      have : 2 ^ 64 ≤ t * 2 ^ 64 := Nat.le_mul_of_pos_left _ (by omega)
      rw [Nat.mul_comm (2 ^ 64) t]
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A number's words from the second. -/
theorem colsV_shift (f : Nat → Nat) : ∀ n, colsV f (n + 1) = f 0 + 2 ^ 64 * colsV (fun i => f (i + 1)) n
  | 0 => by simp [colsV]
  | n + 1 => by
    have e : ((2 : Nat) ^ 64) ^ (n + 1) = 2 ^ 64 * (2 ^ 64) ^ n := Nat.pow_succ'
    rw [colsV_succ, colsV_shift f n, colsV_succ, Nat.mul_add, e, Nat.mul_assoc]
    omega

theorem wp_mulhu {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.mulhu d n m :: is)) s Q :=
  WP.cons exec_mulhu (k _ (Upd.write _ _ _))

/-- The modulus's `k` words at `N`. -/
abbrev nv (k : Nat) (m : Mem) (b : Addr) : Nat := colsV (fun i => dw m b (N k + 8 * i)) k

/-- What a round of the reduction needs. -/
structure RedOk (k : Nat) (b : Addr) (m' : Nat) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  t6 : s.gpr .t6 = BitVec.ofNat 64 m'
  m'lt : m' < 2 ^ 64
  inv : dw s.mem b (N k) * m' % 2 ^ 64 = 2 ^ 64 - 1
  k7 : 7 ≤ k
  k30 : k ≤ 30

theorem N_facts (k : Nat) (h₁ : 1 ≤ k) (h : k ≤ 30) :
    N k = T k + 8 * (k + 2) ∧ N k % 8 = 0 ∧ N k + 8 * k ≤ 2048 := by
  unfold N T; omega

theorem red_alg {E R C C0 Tc Nc q Tw0 Nw0 Tj1 Tj2 a b c w : Nat}
    (hrow : R + E * C = Tc + Nc * q + C0) (h0 : 2 ^ 64 * C0 = Tw0 + q * Nw0)
    (h1 : a + 2 ^ 64 * c = Tj1 + C) (h2 : b + 2 ^ 64 * w = Tj2 + c) :
    2 ^ 64 * (R + E * a + E * (2 ^ 64 * b) + E * (2 ^ 64 * (2 ^ 64 * w))) =
      Tw0 + 2 ^ 64 * (Tc + E * Tj1 + E * (2 ^ 64 * Tj2)) + q * (Nw0 + 2 ^ 64 * Nc) := by
  have m1 := congrArg (E * ·) h1
  have m2 := congrArg (fun x => E * (2 ^ 64 * x)) h2
  simp only [Nat.mul_add] at m1 m2
  rw [show q * (Nw0 + 2 ^ 64 * Nc) = q * Nw0 + 2 ^ 64 * (q * Nc) by rw [Nat.mul_add, Nat.mul_left_comm]]
  rw [Nat.mul_comm Nc q] at hrow
  omega

/-- The carry word of the quotient's first product: `2⁶⁴ C₀ = T₀ + q m₀`. -/
theorem c0_nat {t m' n0 : Nat} (ht : t < 2 ^ 64) (hn : n0 < 2 ^ 64) (hinv : n0 * m' % 2 ^ 64 = 2 ^ 64 - 1)
    {hi c : Nat} (hp : t * m' % 2 ^ 64 * n0 % 2 ^ 64 + 2 ^ 64 * hi = t * m' % 2 ^ 64 * n0)
    (hc : c = if t = 0 then 0 else 1) :
    2 ^ 64 * (hi + c) = t + t * m' % 2 ^ 64 * n0 ∧ hi + c < 2 ^ 64 := by
  have hq := quot_nat ht hinv
  have hql : t * m' % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hxy : t * m' % 2 ^ 64 * n0 ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  subst hc
  generalize t * m' % 2 ^ 64 * n0 = P at *
  by_cases h0 : t = 0 <;> simp only [h0, ↓reduceIte] at hq ⊢ <;> omega

theorem sltu0_toNat (x : BitVec 64) :
    (if BitVec.ofNat 64 0 < x then (1 : BitVec 64) else 0).toNat = if x.toNat = 0 then 0 else 1 := by
  by_cases h : x.toNat = 0
  · have : ¬ BitVec.ofNat 64 0 < x := by rw [BitVec.lt_def]; simp [h]
    simp only [this, h, ↓reduceIte]; rfl
  · have : BitVec.ofNat 64 0 < x := by rw [BitVec.lt_def]; simp; omega
    simp only [this, h, ↓reduceIte]; rfl

/-- A round of the reduction. -/
theorem redRound_ok {k : Nat} {b : Addr} {m' : Nat} {s : State} (h : RedOk k b m' s) :
    WP isa (.block (redRound k)) s fun s' =>
      (∀ r, r ∉ .a4 :: clobS → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 1)⟩] s.mem s'.mem ∧
      ∃ w, 2 ^ 64 * (tv k s'.mem b (k + 1) + (2 ^ 64) ^ (k + 1) * w) =
        tv k s.mem b (k + 2) + dw s.mem b (T k) * m' % 2 ^ 64 * nv k s.mem b := by
  obtain ⟨t8, ttop⟩ := T_facts k (by have := h.k7; omega) h.k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by have := h.k7; omega) h.k30
  have hb := h.nowrap
  have hc := h.ctx
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := h.k7; omega⟩
  unfold redRound
  simp only [Nat.add_sub_cancel]
  refine ld_ok hc (by omega) (by omega) fun s1 u1 => wp_mul fun s2 u2 => ?_
  refine ld_ok (ctx_of hc (by rw [u2.other _ (by decide), u1.other _ (by decide)]) (by rw [u2.wr, u1.wr]))
    (by omega) (by omega) fun s3 u3 => wp_mulhu fun s4 u4 => wp_li (by decide) fun s5 u5 =>
      wp_sltu fun s6 u6 => wp_add fun s7 u7 => ?_
  show WP isa (.block (macRow (j + 1) .a3 (N (j + 1)) 1 j ++ [.load .d .a7 .a3 (T (j + 1) + 8 * (j + 1)),
    .add .t0 .a7 .a5, .sltu .t3 .t0 .a5, .store .d .t0 .a3 (T (j + 1) + 8 * j),
    .load .d .a7 .a3 (T (j + 1) + 8 * (j + 1 + 1)), .add .a7 .a7 .t3, .store .d .a7 .a3 (T (j + 1) + 8 * (j + 1))])) s7 _
  -- What the quotient block leaves.
  have m7 : s7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have g7 : ∀ r, r ∉ .a4 :: clobS → s7.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u7.other r hr.2.2.2.2.1, u6.other r hr.2.2.2.1, u5.other r hr.2.2.2.1, u4.other r hr.2.2.2.2.1,
      u3.other r hr.2.2.2.2.2.1, u2.other r hr.1, u1.other r hr.2.2.2.2.2.2]
  have hc7 : Ctx b s7 := ctx_of hc (g7 _ (by decide)) (by rw [u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
  have hT0 : (s1.gpr .a7).toNat = dw s.mem b (T (j + 1)) := by rw [u1.gpr]; rfl
  have hq : (s7.gpr .a4).toNat = dw s.mem b (T (j + 1)) * m' % 2 ^ 64 := by
    rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, BitVec.toNat_mul, hT0, u1.other _ (by decide), h.t6,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.m'lt]
  have hn0 : (s3.gpr .a6).toNat = dw s.mem b (N (j + 1)) := by
    rw [u3.gpr, u2.mem, u1.mem, show N (j + 1) = N (j + 1) + 8 * 0 by rfl]; rfl
  have hC0 : 2 ^ 64 * (s7.gpr .a5).toNat = dw s.mem b (T (j + 1)) +
      dw s.mem b (T (j + 1)) * m' % 2 ^ 64 * dw s.mem b (N (j + 1)) := by
    have hp := mul_words (s4.gpr .a4) (s3.gpr .a6)
    have e4a : s4.gpr .a4 = s3.gpr .a4 := u4.other _ (by decide)
    have e3a : (s3.gpr .a4).toNat = dw s.mem b (T (j + 1)) * m' % 2 ^ 64 := by
      rw [u3.other _ (by decide), u2.gpr, BitVec.toNat_mul, hT0, u1.other _ (by decide), h.t6,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.m'lt]
    have e4 : s4.gpr .a5 = BitVec.ofNat 64 ((s3.gpr .a4).toNat * (s3.gpr .a6).toNat / 2 ^ 64) := by
      rw [u4.gpr]
    have e6 : (s6.gpr .t3).toNat = if dw s.mem b (T (j + 1)) = 0 then 0 else 1 := by
      rw [u6.gpr, u5.gpr, u5.other _ (by decide), u4.other _ (by decide),
        u3.other _ (by decide), u2.other _ (by decide), sltu0_toNat, hT0]
    rw [e4a, e3a, hn0] at hp
    rw [BitVec.toNat_mul, e3a, hn0] at hp
    obtain ⟨c1, c2⟩ := c0_nat (dw_lt _ _ _) (dw_lt _ _ _) h.inv
      hp e6
    rw [u7.gpr, BitVec.toNat_add, u6.other _ (by decide), u5.other _ (by decide), e4, e3a, hn0,
      Nat.mod_eq_of_lt c2]
    exact c1
  -- The row.
  have hR : RowOk (j + 1) b b .a3 (N (j + 1)) 1 j s7 :=
    { ctx := hc7
      nowrap := hb
      hx := hc7.a3
      hxb := by decide
      hxo := fun i hi => by omega
      xal := fun i _ => al8 hc7.al (by omega)
      xin := fun i hi => hc7.inR (by omega)
      xdis := fun i hi j' hj' => Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
      top := by omega
      t8 := t8 }
  refine WP.block_append (WP.mono (row_ok hR j (Nat.le_refl _)) fun s8 h8 => ?_)
  have hc8 : Ctx b s8 := ctx_of hc7 (h8.gpr _ (by decide)) h8.wr
  refine ld_ok hc8 (by omega) (by omega) fun s9 u9 => wp_add fun s10 u10 => wp_sltu fun s11 u11 => ?_
  have hc11 : Ctx b s11 := ctx_of hc8 (by rw [u11.other _ (by decide), u10.other _ (by decide),
    u9.other _ (by decide)]) (by rw [u11.wr, u10.wr, u9.wr])
  refine sd_ok hc11 (by omega) (by omega) fun s12 u12 => ?_
  have hc12 : Ctx b s12 := ctx_of hc11 (by rw [u12.gpr]) u12.wr
  refine ld_ok hc12 (by omega) (by omega) fun s13 u13 => wp_add fun s14 u14 => ?_
  have hc14 : Ctx b s14 := ctx_of hc12 (by rw [u14.other _ (by decide), u13.other _ (by decide)])
    (by rw [u14.wr, u13.wr])
  refine sd_ok hc14 (by omega) (by omega) fun s15 u15 => WP.block_nil ?_
  -- Memory.
  have m11 : s11.mem = s8.mem := by rw [u11.mem, u10.mem, u9.mem]
  have m12 : s12.mem = s8.mem.writeW (b + BitVec.ofNat 64 (T (j + 1) + 8 * j)) (s11.gpr .t0) := by
    rw [u12.mem, m11]
  have m15 : s15.mem = s12.mem.writeW (b + BitVec.ofNat 64 (T (j + 1) + 8 * (j + 1))) (s14.gpr .a7) := by
    rw [u15.mem, u14.mem, u13.mem]
  -- Words of `T` the tail reads, as they were.
  have fr : ∀ d, T (j + 1) + 8 * j ≤ d → d + 8 ≤ 2048 → dw s8.mem b d = dw s.mem b d := fun d hd hd' => by
    rw [dw_frame h8.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint b (.inr hd) (by omega) (by omega), m7]
  have hw1 : (s9.gpr .a7).toNat = dw s.mem b (T (j + 1) + 8 * (j + 1)) := by
    rw [u9.gpr, ← fr _ (by omega) (by omega)]; rfl
  have hw2 : (s13.gpr .a7).toNat = dw s.mem b (T (j + 1) + 8 * (j + 1 + 1)) := by
    rw [u13.gpr, m12, show dw s.mem b (T (j + 1) + 8 * (j + 1 + 1)) = dw s8.mem b (T (j + 1) + 8 * (j + 1 + 1))
      from (fr _ (by omega) (by omega)).symm]
    show dw _ b _ = _
    rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]
  refine ⟨fun r hr => ?_, by rw [u15.rd, u14.rd, u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, h8.rd, u7.rd, u6.rd, u5.rd,
      u4.rd, u3.rd, u2.rd, u1.rd],
    by rw [u15.wr, u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, h8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr],
    by rw [u15.sp, u14.sp, u13.sp, u12.sp, u11.sp, u10.sp, u9.sp, h8.sp, u7.sp, u6.sp, u5.sp, u4.sp, u3.sp, u2.sp,
      u1.sp], ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u15.gpr, u14.other r hr.2.2.2.2.2.2, u13.other r hr.2.2.2.2.2.2, u12.gpr, u11.other r hr.2.2.2.1,
      u10.other r hr.2.1, u9.other r hr.2.2.2.2.2.2, h8.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1,
        hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2]), g7 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
        hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2])]
  · rw [m15, m12, ← m7]
    refine (((h8.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_).writeW
      (List.mem_singleton_self _) _ ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · -- The value.
    have hv := h8.val
    rw [colsV_add', colsV_mul, m7, hq] at hv
    have hlow : colsV (fun i => dw s15.mem b (T (j + 1) + 8 * i)) j = colsV (fun i => dw s8.mem b (T (j + 1) + 8 * i)) j :=
      colsV_congr fun i hi => by
        rw [m15, m12, dw_write_other _ _ _ (by omega) (by omega) (by omega),
          dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    have hj0 : dw s15.mem b (T (j + 1) + 8 * j) = (s11.gpr .t0).toNat := by
      rw [m15, m12, dw_write_other _ _ _ (by omega) (by omega) (by omega), dw_write_self]
    have hj1 : dw s15.mem b (T (j + 1) + 8 * (j + 1)) = (s14.gpr .a7).toNat := by rw [m15, dw_write_self]
    -- The tail's sums.
    have e10 := carry (s9.gpr .a7) (s9.gpr .a5)
    have t0v : s11.gpr .t0 = s9.gpr .a7 + s9.gpr .a5 := by rw [u11.other _ (by decide), u10.gpr]
    have t3v : s11.gpr .t3 = if s9.gpr .a7 + s9.gpr .a5 < s9.gpr .a5 then 1 else 0 := by
      rw [u11.gpr, u10.gpr, u10.other _ (by decide)]
    have a5v : s9.gpr .a5 = s8.gpr .a5 := u9.other _ (by decide)
    have a7v : s14.gpr .a7 = s13.gpr .a7 + s11.gpr .t3 := by
      rw [u14.gpr, u13.other .t3 (by decide), u12.gpr]
    have h1 : (s11.gpr .t0).toNat + 2 ^ 64 * (s11.gpr .t3).toNat =
        dw s.mem b (T (j + 1) + 8 * (j + 1)) + (s8.gpr .a5).toNat := by
      rw [t0v, t3v, e10, hw1, a5v]
    have h2 : (s14.gpr .a7).toNat + 2 ^ 64 * (((s13.gpr .a7).toNat + (s11.gpr .t3).toNat) / 2 ^ 64) =
        dw s.mem b (T (j + 1) + 8 * (j + 1 + 1)) + (s11.gpr .t3).toNat := by
      rw [a7v, BitVec.toNat_add, Nat.mod_add_div, hw2]
    refine ⟨((s13.gpr .a7).toNat + (s11.gpr .t3).toNat) / 2 ^ 64, ?_⟩
    have alg := red_alg hv hC0 h1 h2
    show 2 ^ 64 * (colsV (fun i => dw s15.mem b (T (j + 1) + 8 * i)) (j + 1 + 1) + _) = _
    rw [colsV_succ, colsV_succ, hlow, hj0, hj1]
    simp only [nv, tv]
    rw [colsV_shift (fun i => dw s.mem b (T (j + 1) + 8 * i)) (j + 1 + 1), colsV_succ, colsV_succ,
      colsV_shift (fun i => dw s.mem b (N (j + 1) + 8 * i)) j]
    have p1 : ((2 : Nat) ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 := Nat.pow_succ ..
    have p2 : ((2 : Nat) ^ 64) ^ (j + 1 + 1) = (2 ^ 64) ^ j * (2 ^ 64 * 2 ^ 64) := by
      rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc]
    simp only [Nat.mul_zero, Nat.add_zero] at alg ⊢
    rw [p1, p2]
    simp only [Nat.mul_assoc] at alg ⊢
    exact alg


end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: the rounds of the multiplication

The `k` rounds of `mulCore` (`Impl/Weierstrass/RISCV64/GenWide.lean`) from
`T = 0`: after round `i`, the `k + 1` words of `T` are `V` with
`V 2^(64 i) = a (b mod 2^(64 i)) + Q m` for some `Q < 2^(64 i)`, and
`V < 2^(64 k) + m` (`loop_ok`), Montgomery's operand scanning (CIOS).
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_frame al8 colsV)

theorem cios_step {V a Bi Bc Q M q E W : Nat} (hinv : V * E = a * Bc + Q * M)
    (hW : 2 ^ 64 * W = V + a * Bi + q * M) :
    W * (E * 2 ^ 64) = a * (Bc + E * Bi) + (Q + E * q) * M := by
  have h1 : W * (E * 2 ^ 64) = (V + a * Bi + q * M) * E := by
    rw [← hW, Nat.mul_comm (2 ^ 64) W, Nat.mul_comm E, Nat.mul_assoc]
  rw [h1, Nat.add_mul, Nat.add_mul, hinv, Nat.mul_add, Nat.add_mul]
  simp only [Nat.mul_comm, Nat.mul_left_comm]
  omega

theorem cios_bound {V a Bc Q M E R : Nat} (hinv : V * E = a * Bc + Q * M) (ha : a < R) (hB : Bc < E)
    (hQ : Q < E) : V < R + M := by
  have hE : 0 < E := by omega
  apply Nat.lt_of_mul_lt_mul_right (a := E)
  have h1 : a * Bc ≤ a * E := Nat.mul_le_mul_left _ (by omega)
  have h2 : a * E < R * E := Nat.mul_lt_mul_of_pos_right ha hE
  have h3 : Q * M ≤ E * M := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, hinv]
  rw [Nat.mul_comm E M] at h3
  omega

theorem colsV_lt (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 64) : ∀ n, colsV f n < (2 ^ 64) ^ n
  | 0 => by simp [colsV]
  | n + 1 => by
    have e : ((2 : Nat) ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 := Nat.pow_succ ..
    rw [colsV_succ, e]
    have := colsV_lt f hf n
    have := hf n
    have : (2 ^ 64) ^ n * f n ≤ (2 ^ 64) ^ n * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, Nat.mul_one] at this
    omega

/-- The words of `b`'s operand, `B`. -/
abbrev bv (m : Mem) (B : Addr) (i : Nat) : Nat := colsV (fun j => dw m B (8 * j)) i

/-- What the rounds need. -/
structure LoopOk (k : Nat) (b A B : Addr) (m' : Nat) (s0 : State) : Prop where
  mo : MulOk k b A s0
  t5 : s0.gpr .t5 = B
  bal : B.toNat % 8 = 0
  bin : ∀ i < k, InRegions (s0.rd ++ s0.wr) (B + BitVec.ofNat 64 (8 * i)) 8
  bdis : ∀ i < k, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ ⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩
  t6 : s0.gpr .t6 = BitVec.ofNat 64 m'
  m'lt : m' < 2 ^ 64
  inv : dw s0.mem b (N k) * m' % 2 ^ 64 = 2 ^ 64 - 1
  zero : tv k s0.mem b (k + 1) = 0

/-- After round `i`. -/
structure LoopInv (k : Nat) (b A B : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ .a4 :: clobS → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s0.mem s.mem
  val : ∃ Q < (2 ^ 64) ^ i, tv k s.mem b (k + 1) * (2 ^ 64) ^ i = xv s0.mem A k * bv s0.mem B i + Q * nv k s0.mem b
  lt : tv k s.mem b (k + 1) < 2 ^ (64 * k) + nv k s0.mem b

/-- The words outside `T` are as they were. -/
theorem frame_dw {k : Nat} {b : Addr} {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] m m')
    {P : Addr} {d : Nat} (hd : Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ ⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩) :
    dw m' P d = dw m P d :=
  dw_frame hf fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd

theorem nv_frame {k : Nat} {b : Addr} {m m' : Mem} (hk : 1 ≤ k) (hk' : k ≤ 30)
    (hf : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] m m') {d : Nat} (hd : N k ≤ d) (hd' : d + 8 ≤ 2048) :
    dw m' b d = dw m b d := by
  obtain ⟨hNT, -, -⟩ := N_facts k hk hk'
  exact frame_dw hf (Offset.disjoint b (.inr (by omega)) (by omega) (by omega))

/-- Round `i`. -/
theorem loopStep_ok {k : Nat} {b A B : Addr} {m' : Nat} {s0 : State} (hL : LoopOk k b A B m' s0) {i : Nat}
    (hi : i < k) {s : State} (h : LoopInv k b A B s0 i s) :
    WP isa (.block (mulRound k i ++ redRound k)) s (LoopInv k b A B s0 (i + 1)) := by
  have k7 := hL.mo.k7
  have k30 := hL.mo.k32
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  have hb := hL.mo.nowrap
  have hmo : MulOk k b A s := hL.mo.of (h.gpr _ (by decide)) (h.gpr _ (by decide)) h.rd h.wr
  refine WP.block_append (WP.mono (mulRound_ok hmo (B := B) (i := i) (by rw [h.gpr _ (by decide), hL.t5])
    (al8 hL.bal (by omega)) (by omega) (by rw [h.rd, h.wr]; exact hL.bin i hi)) fun s1 ⟨g1, rd1, wr1, sp1, f1, v1⟩ => ?_)
  have hred : RedOk k b m' s1 :=
    { ctx := ctx_of hmo.ctx (g1 _ (by decide)) wr1
      nowrap := hb
      t6 := by rw [g1 _ (by decide), h.gpr _ (by decide), hL.t6]
      m'lt := hL.m'lt
      inv := by
        rw [nv_frame (by omega) k30 f1 (Nat.le_refl _) (by omega),
          nv_frame (by omega) k30 h.frame (Nat.le_refl _) (by omega)]
        exact hL.inv
      k7 := k7
      k30 := k30 }
  refine WP.mono (redRound_ok hred) fun s2 ⟨g2, rd2, wr2, sp2, f2, w, v2⟩ => ?_
  -- The numbers, all as in `s0`.
  have fT : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s0.mem s2.mem :=
    (h.frame.trans f1).trans (f2.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩)
  have hA : xv s.mem A k = xv s0.mem A k :=
    colsV_congr fun j hj => frame_dw h.frame (hL.mo.adis j hj (k + 2) (Nat.le_refl _))
  have hB : dw s.mem B (8 * i) = dw s0.mem B (8 * i) := frame_dw h.frame (hL.bdis i hi)
  have hN1 : nv k s1.mem b = nv k s0.mem b :=
    colsV_congr fun j hj => by
      rw [nv_frame (by omega) k30 f1 (by omega) (by omega),
        nv_frame (by omega) k30 h.frame (by omega) (by omega)]
  rw [hA, hB] at v1
  rw [hN1] at v2
  obtain ⟨Q, hQ, hv⟩ := h.val
  generalize hq : dw s1.mem b (T k) * m' % 2 ^ 64 = q at v2
  have hq64 : q < 2 ^ 64 := by rw [← hq]; exact Nat.mod_lt _ (by decide)
  -- The top word does not carry.
  have hw : w = 0 := by
    by_contra hw0
    have hw1 : (2 ^ 64) ^ (k + 1) ≤ (2 ^ 64) ^ (k + 1) * w := Nat.le_mul_of_pos_right _ (by omega)
    have hAk : xv s0.mem A k < (2 ^ 64) ^ k := colsV_lt _ (fun j => dw_lt _ _ _) k
    have hNk : nv k s0.mem b < (2 ^ 64) ^ k := colsV_lt _ (fun j => dw_lt _ _ _) k
    have hp : xv s0.mem A k * dw s0.mem B (8 * i) ≤ (2 ^ 64) ^ k * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by have := dw_lt s0.mem B (8 * i); omega)
    have hqN : q * nv k s0.mem b ≤ (2 ^ 64 - 1) * (2 ^ 64) ^ k := Nat.mul_le_mul (by omega) (by omega)
    have hlt := h.lt
    rw [show 2 ^ (64 * k) = (2 ^ 64) ^ k from Nat.pow_mul ..] at hlt
    rw [Nat.mul_sub, Nat.mul_one] at hp
    rw [Nat.sub_mul, Nat.one_mul] at hqN
    have e1 : (2 ^ 64) ^ (k + 1) = (2 ^ 64) ^ k * 2 ^ 64 := Nat.pow_succ ..
    have e2 : (2 ^ 64) ^ k * 2 ^ 64 = 2 ^ 64 * (2 ^ 64) ^ k := Nat.mul_comm ..
    rw [v1] at v2
    generalize (2 ^ 64) ^ k = E at *
    generalize (2 ^ 64) ^ (k + 1) = F at *
    omega
  subst hw
  rw [Nat.mul_zero, Nat.add_zero, v1] at v2
  obtain ⟨Q', hQ', hv'⟩ : ∃ Q' < (2 ^ 64) ^ (i + 1),
      tv k s2.mem b (k + 1) * (2 ^ 64) ^ (i + 1) =
        xv s0.mem A k * bv s0.mem B (i + 1) + Q' * nv k s0.mem b := by
    have inv' := cios_step hv v2
    have e : ((2 : Nat) ^ 64) ^ (i + 1) = (2 ^ 64) ^ i * 2 ^ 64 := Nat.pow_succ ..
    refine ⟨Q + (2 ^ 64) ^ i * q, ?_, ?_⟩
    · rw [e]
      have : (2 ^ 64) ^ i * q ≤ (2 ^ 64) ^ i * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_sub, Nat.mul_one] at this
      omega
    · rw [e]
      show _ = xv s0.mem A k * colsV _ (i + 1) + _
      rw [colsV_succ]
      exact inv'
  refine ⟨fun r hr => by rw [g2 r hr, g1 r hr, h.gpr r hr], by rw [rd2, rd1, h.rd], by rw [wr2, wr1, h.wr],
    by rw [sp2, sp1, h.sp], fT, ⟨Q', hQ', hv'⟩, ?_⟩
  rw [Nat.pow_mul]
  exact cios_bound hv' (colsV_lt _ (fun j => dw_lt _ _ _) k) (colsV_lt _ (fun j => dw_lt _ _ _) _) hQ'

/-- The rounds. -/
theorem loop_ok {k : Nat} {b A B : Addr} {m' : Nat} {s0 : State} (hL : LoopOk k b A B m' s0) :
    ∀ i ≤ k, WP isa (.block ((List.range i).flatMap fun i => mulRound k i ++ redRound k)) s0
      (LoopInv k b A B s0 i)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      ⟨0, by decide, by rw [hL.zero]; simp [bv, colsV]⟩, by rw [hL.zero]; exact Nat.add_pos_left (Nat.two_pow_pos _) _⟩
  | i + 1, hi => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (loop_ok hL i (by omega)) fun s h => loopStep_ok hL (i := i) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: a difference with borrows

`n` steps of `sbbStep xb xo yb yo d` (`Impl/Weierstrass/RISCV64/GenWide.lean`)
from a state with `a3 = b` (`Ctx`): the words at `b + d` become those of
`X - Y - a5` for the words `X` at `xb + xo` and `Y` at `yb + yo`, with the
borrow out in `a5` (`sbbRow_ok`). Only those `n` words are written.
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)
open VG.Proof.Weierstrass.RISCV64.P256Field (sbb_ok)

/-- The registers a step writes. -/
abbrev clobB : List Reg := [.t0, .t3, .a1, .a5, .a6, .a7]

/-- An operand of a row: its words at `X + xo + 8 j`, through `xb`. -/
structure OpOk (b X : Addr) (xb : Reg) (xo d n : Nat) (s0 : State) : Prop where
  hx : s0.gpr xb = X
  hxb : xb ∉ clobB
  hxo : ∀ j < n, xo + 8 * j < 2048
  al : ∀ j < n, (X + BitVec.ofNat 64 (xo + 8 * j)).toNat % 8 = 0
  inR : ∀ j < n, InRegions (s0.rd ++ s0.wr) (X + BitVec.ofNat 64 (xo + 8 * j)) 8
  dis : ∀ j < n, Region.Disjoint ⟨X + BitVec.ofNat 64 (xo + 8 * j), 8⟩ ⟨b + BitVec.ofNat 64 d, 8 * j⟩

/-- After `j` steps of a difference from `s0`. -/
structure SbbInv (b X Y : Addr) (xo yo d : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobB → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 d, 8 * j⟩] s0.mem s.mem
  cy : (s.gpr .a5).toNat ≤ 1
  val : colsV (fun i => dw s.mem b (d + 8 * i)) j + colsV (fun i => dw s0.mem Y (yo + 8 * i)) j +
      (s0.gpr .a5).toNat = colsV (fun i => dw s0.mem X (xo + 8 * i)) j + (2 ^ 64) ^ j * (s.gpr .a5).toNat

set_option linter.unusedSimpArgs false in
/-- Step `j` of a difference. -/
theorem sbbStep_ok {b X Y : Addr} {xb yb : Reg} {xo yo d n : Nat} {s0 : State} (hc : Ctx b s0)
    (hd : d + 8 * n ≤ 2048) (hd8 : d % 8 = 0)
    (hX : OpOk b X xb xo d n s0) (hY : OpOk b Y yb yo d n s0) {j : Nat} (hj : j < n) {s : State}
    (h : SbbInv b X Y xo yo d s0 j s) :
    WP isa (.block (sbbStep xb xo yb yo d j)) s (SbbInv b X Y xo yo d s0 (j + 1)) := by
  have hcs : Ctx b s := ctx_of hc (h.gpr _ (by decide)) h.wr
  have hxo := hX.hxo j hj
  have hyo := hY.hxo j hj
  unfold sbbStep
  refine wp_ld (by omega) (by rw [h.gpr _ hX.hxb, hX.hx]) (hX.al j hj)
    (by rw [h.rd, h.wr]; exact hX.inR j hj) fun s1 u1 => ?_
  refine wp_ld (by omega) (by rw [u1.other _ (fun e => hY.hxb (by rw [e]; decide)), h.gpr _ hY.hxb, hY.hx])
    (hY.al j hj) (by rw [u1.rd, u1.wr, h.rd, h.wr]; exact hY.inR j hj) fun s2 u2 => ?_
  show WP isa (.block ([.sltu .t3 .a7 .a6, .sub .t0 .a7 .a6, .sltu .a1 .t0 .a5, .sub .t0 .t0 .a5, .add .a5 .t3 .a1] ++
    [Instr.store .d .t0 .a3 (d + 8 * j)])) s2 _
  refine WP.block_append (WP.mono (sbb_ok (d := .t0) (x := .a7) (y := .a6) (c := .a5) (u := .t3) (v := .a1))
    fun s3 ⟨e3, k3⟩ => ?_)
  have hc3 : Ctx b s3 := ctx_of hcs (by rw [k3.1 _ (by decide), u2.other _ (by decide), u1.other _ (by decide)])
    (by rw [k3.2.2.2.1, u2.wr, u1.wr])
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have a5 : s2.gpr .a5 = s.gpr .a5 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  obtain ⟨e3v, e3c⟩ := e3 (by rw [a5]; exact h.cy)
  have hX0 : dw s.mem X (xo + 8 * j) = dw s0.mem X (xo + 8 * j) :=
    dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hX.dis j hj
  have hY0 : dw s.mem Y (yo + 8 * j) = dw s0.mem Y (yo + 8 * j) :=
    dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hY.dis j hj
  have a7 : (s2.gpr .a7).toNat = dw s0.mem X (xo + 8 * j) := by
    rw [u2.other _ (by decide), u1.gpr, ← hX0]; rfl
  have a6 : (s2.gpr .a6).toNat = dw s0.mem Y (yo + 8 * j) := by
    rw [u2.gpr, u1.mem, ← hY0]; rfl
  have hm4 : s4.mem = s.mem.writeW (b + BitVec.ofNat 64 (d + 8 * j)) (s3.gpr .t0) := by
    rw [u4.mem, k3.2.1, u2.mem, u1.mem]
  refine ⟨fun r hr => ?_, by rw [u4.rd, k3.2.2.1, u2.rd, u1.rd, h.rd],
    by rw [u4.wr, k3.2.2.2.1, u2.wr, u1.wr, h.wr], by rw [u4.sp, k3.2.2.2.2, u2.sp, u1.sp, h.sp], ?_,
    by rw [u4.gpr]; exact e3c, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.gpr, k3.1 r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), u2.other r hr.2.2.2.2.1,
      u1.other r hr.2.2.2.2.2, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  · rw [hm4]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains b (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : colsV (fun i => dw s4.mem b (d + 8 * i)) j = colsV (fun i => dw s.mem b (d + 8 * i)) j :=
      colsV_congr fun i hi => by rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    rw [a7, a6, a5] at e3v
    show colsV (fun i => dw s4.mem b (d + 8 * i)) j + (2 ^ 64) ^ j * dw s4.mem b (d + 8 * j) +
        (colsV (fun i => dw s0.mem Y (yo + 8 * i)) j + (2 ^ 64) ^ j * dw s0.mem Y (yo + 8 * j)) +
        (s0.gpr .a5).toNat =
      colsV (fun i => dw s0.mem X (xo + 8 * i)) j + (2 ^ 64) ^ j * dw s0.mem X (xo + 8 * j) +
        (2 ^ 64) ^ (j + 1) * (s4.gpr .a5).toNat
    rw [hcw, hm4, dw_write_self, u4.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    have key : E * (s3.gpr .t0).toNat + E * dw s0.mem Y (yo + 8 * j) + E * (s.gpr .a5).toNat =
        E * dw s0.mem X (xo + 8 * j) + E * 2 ^ 64 * (s3.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e3v]
    omega

/-- The difference. -/
theorem sbbRow_ok {b X Y : Addr} {xb yb : Reg} {xo yo d n : Nat} {s0 : State} (hc : Ctx b s0)
    (hd : d + 8 * n ≤ 2048) (hd8 : d % 8 = 0)
    (hX : OpOk b X xb xo d n s0) (hY : OpOk b Y yb yo d n s0) (hc0 : (s0.gpr .a5).toNat ≤ 1) :
    ∀ j ≤ n, WP isa (.block ((List.range j).flatMap (sbbStep xb xo yb yo d))) s0 (SbbInv b X Y xo yo d s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, hc0, by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (sbbRow_ok hc hd hd8 hX hY hc0 j (by omega)) fun s h =>
      sbbStep_ok hc hd hd8 hX hY (j := j) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: the final subtraction

`csub k` (`Impl/Weierstrass/RISCV64/GenWide.lean`): for the `k + 1` words of
`T` below `2 m`, `[o]` becomes `T mod m` (`csub_ok`): `T - m` over `N`
(`sbbRow_ok`), the mask `T_k - borrow`, then each word of `T` or of the
difference by the mask (`selRow_ok`).
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx wp_and)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- A mask: all zeros or all ones. -/
def IsMask (m : BitVec 64) : Prop := m = 0 ∨ m = BitVec.allOnes 64

/-- `x ⊕ ((e ⊕ x) ∧ m)`: `e` under the mask all ones, `x` under zero. -/
theorem sel_mask {x e m : BitVec 64} (hm : IsMask m) :
    x ^^^ ((e ^^^ x) &&& m) = if m = BitVec.allOnes 64 then e else x := by
  rcases hm with rfl | rfl
  · have : (0 : BitVec 64) ≠ BitVec.allOnes 64 := by decide
    simp only [this, ↓reduceIte]
    ext i hi
    simp
  · simp only [BitVec.and_allOnes, ↓reduceIte]
    rw [BitVec.xor_comm e x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem wp_xor' {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- After `j` words of the selection from `s0`. -/
structure SelInv (k : Nat) (b O : Addr) (sel : Bool) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [.t0, .a6] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨O, 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem O (8 * i) = if sel then dw s0.mem b (T k + 8 * i) else dw s0.mem b (N k + 8 * i)

/-- What the selection needs. -/
structure SelOk (k : Nat) (b O : Addr) (sel : Bool) (s0 : State) : Prop where
  ctx : Ctx b s0
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  t2 : s0.gpr .t2 = O
  oal : O.toNat % 8 = 0
  onw : O.toNat + 8 * k ≤ 2 ^ 64
  ow : ∀ i < k, InRegions s0.wr (O + BitVec.ofNat 64 (8 * i)) 8
  tdis : ∀ i < k, Region.Disjoint ⟨b + BitVec.ofNat 64 (T k + 8 * i), 8⟩ ⟨O, 8 * k⟩
  ndis : ∀ i < k, Region.Disjoint ⟨b + BitVec.ofNat 64 (N k + 8 * i), 8⟩ ⟨O, 8 * k⟩
  mask : IsMask (s0.gpr .a7)
  sel : (s0.gpr .a7 = BitVec.allOnes 64) = (sel = true)
  k7 : 7 ≤ k
  k30 : k ≤ 30

theorem disj_mono {r : Region} {O : Addr} {n m : Nat} (h : Region.Disjoint r ⟨O, m⟩) (hn : n ≤ m) :
    Region.Disjoint r ⟨O, n⟩ := fun x h₁ h₂ => h x h₁ (by simp only [Region.Contains] at h₂ ⊢; omega)

set_option linter.unusedSimpArgs false in
theorem selStep_ok {k : Nat} {b O : Addr} {sel : Bool} {s0 : State} (hS : SelOk k b O sel s0) {j : Nat}
    (hj : j < k) {s : State} (h : SelInv k b O sel s0 j s) :
    WP isa (.block (selStep k j)) s (SelInv k b O sel s0 (j + 1)) := by
  obtain ⟨t8, ttop⟩ := T_facts k (by have := hS.k7; omega) hS.k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by have := hS.k7; omega) hS.k30
  have hcs : Ctx b s := ctx_of hS.ctx (h.gpr _ (by decide)) h.wr
  have hb := hS.nowrap
  have hon := hS.onw
  unfold selStep
  refine ld_ok hcs (by omega) (by omega) fun s1 u1 => ?_
  refine ld_ok (ctx_of hcs (u1.other _ (by decide)) u1.wr) (by omega) (by omega) fun s2 u2 =>
    wp_xor' fun s3 u3 => wp_and fun s4 u4 => wp_xor' fun s5 u5 => ?_
  refine wp_sd (by omega) (by rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
    u2.other _ (by decide), u1.other _ (by decide), h.gpr _ (by decide), hS.t2]) (al8 hS.oal (by omega))
    (by rw [u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, h.wr]; exact hS.ow j hj) fun s6 u6 => WP.block_nil ?_
  have hT0 : dw s.mem b (T k + 8 * j) = dw s0.mem b (T k + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact disj_mono (hS.tdis j hj) (by omega)
  have hN0 : dw s.mem b (N k + 8 * j) = dw s0.mem b (N k + 8 * j) :=
    dw_frame h.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact disj_mono (hS.ndis j hj) (by omega)
  have a7 : s4.gpr .a7 = s0.gpr .a7 := by
    rw [u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide),
      h.gpr _ (by decide)]
  have v5 : s5.gpr .t0 = s1.gpr .t0 ^^^ ((s2.gpr .a6 ^^^ s1.gpr .t0) &&& s0.gpr .a7) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide), a7.symm,
      u4.other .a7 (by decide), u3.other .a7 (by decide)]
  rw [sel_mask hS.mask] at v5
  have hm6 : s6.mem = s.mem.writeW (O + BitVec.ofNat 64 (8 * j)) (s5.gpr .t0) := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  refine ⟨fun r hr => ?_, by rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, h.rd],
    by rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, h.wr],
    by rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp, h.sp], ?_, fun i hi => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u6.gpr, u5.other r hr.1, u4.other r hr.2, u3.other r hr.2, u2.other r hr.2, u1.other r hr.1,
      h.gpr r (by simp [hr.1, hr.2])]
  · rw [hm6]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, by
        rw [show O = O + BitVec.ofNat 64 0 by simp]; exact Offset.sub O (Nat.le_refl _) (by omega)⟩
    · rw [show (⟨O, 8 * (j + 1)⟩ : Region) = ⟨O + BitVec.ofNat 64 0, 8 * (j + 1)⟩ by simp]
      exact Offset.contains O (by omega) (by omega) (by omega)
  · rw [hm6]
    by_cases hij : i = j
    · subst hij
      rw [dw_write_self, v5]
      cases sel
      · have : ¬ s0.gpr .a7 = BitVec.allOnes 64 := by rw [hS.sel]; decide
        simp only [this, ↓reduceIte, u1.gpr, ← hN0]; rfl
      · have : s0.gpr .a7 = BitVec.allOnes 64 := by rw [hS.sel]
        simp only [this, ↓reduceIte, u2.gpr, u1.mem, ← hT0]; rfl
    · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.val i (by omega)

theorem selRow_ok {k : Nat} {b O : Addr} {sel : Bool} {s0 : State} (hS : SelOk k b O sel s0) :
    ∀ j ≤ k, WP isa (.block ((List.range j).flatMap (selStep k))) s0 (SelInv k b O sel s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (selRow_ok hS j (by omega)) fun s h => selStep_ok hS (j := j) (by omega) h)

/-- What the final subtraction needs. -/
structure CsubOk (k : Nat) (b O : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  t2 : s.gpr .t2 = O
  oal : O.toNat % 8 = 0
  onw : O.toNat + 8 * k ≤ 2 ^ 64
  ow : ∀ i < k, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8
  tdis : ∀ i ≤ k, Region.Disjoint ⟨b + BitVec.ofNat 64 (T k + 8 * i), 8⟩ ⟨O, 8 * k⟩
  ndis : ∀ i < k, Region.Disjoint ⟨b + BitVec.ofNat 64 (N k + 8 * i), 8⟩ ⟨O, 8 * k⟩
  k7 : 7 ≤ k
  k30 : k ≤ 30

/-- The words of `[o]`. -/
abbrev ov (m : Mem) (O : Addr) (k : Nat) : Nat := colsV (fun i => dw m O (8 * i)) k

theorem csub_nat {D Mv L E Tk c V : Nat} (hD : D < E) (hM : Mv < E) (hV : V = L + E * Tk) (hV2 : V < 2 * Mv)
    (hs : D + Mv + 0 = L + E * c) (hc : c ≤ 1) :
    Tk ≤ 1 ∧ ¬ (Tk = 1 ∧ c = 0) ∧ (Tk = 0 ∧ c = 1 → V % Mv = L) ∧ (¬ (Tk = 0 ∧ c = 1) → V % Mv = D) := by
  have hT : Tk ≤ 1 := by
    by_contra h
    have : E * 2 ≤ E * Tk := Nat.mul_le_mul_left _ (by omega)
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hT with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;>
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hV hs <;> subst hV
  · refine ⟨by omega, by omega, by omega, fun _ => ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · refine ⟨by omega, by omega, fun _ => Nat.mod_eq_of_lt (by omega), fun h => absurd ⟨rfl, rfl⟩ h⟩
  · omega
  · refine ⟨by omega, by omega, by omega, fun _ => ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem toNat_sub_bits {x c : BitVec 64} (hx : x.toNat ≤ 1) (hc : c.toNat ≤ 1) (h : ¬ (x.toNat = 1 ∧ c.toNat = 0)) :
    IsMask (x - c) ∧ (x - c = BitVec.allOnes 64 ↔ x.toNat = 0 ∧ c.toNat = 1) := by
  have hx' : x = 0 ∨ x = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hx with e | e
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  have hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with e | e
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  rcases hx' with rfl | rfl <;> rcases hc' with rfl | rfl
  all_goals first | (exfalso; exact h ⟨rfl, rfl⟩) | (unfold IsMask; decide)

/-- `[o] = T mod m`. -/
theorem csub_ok {k : Nat} {b O : Addr} {s : State} (hC : CsubOk k b O s)
    (hV : tv k s.mem b (k + 1) < 2 * nv k s.mem b) :
    WP isa (.block (csub k)) s fun s' =>
      (∀ r, r ∉ clobB → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (N k), 8 * k⟩, ⟨O, 8 * k⟩] s.mem s'.mem ∧
      ov s'.mem O k = tv k s.mem b (k + 1) % nv k s.mem b := by
  obtain ⟨t8, ttop⟩ := T_facts k (by have := hC.k7; omega) hC.k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by have := hC.k7; omega) hC.k30
  have hb := hC.nowrap
  have hc := hC.ctx
  unfold csub
  refine wp_li (by decide) fun s1 u1 => ?_
  show WP isa (.block (((List.range k).flatMap (sbbStep .a3 (T k) .a3 (N k) (N k)) ++
    [.load .d .a7 .a3 (T k + 8 * k), .sub .a7 .a7 .a5]) ++ (List.range k).flatMap (selStep k))) s1 _
  have hc1 : Ctx b s1 := ctx_of hc (u1.other _ (by decide)) u1.wr
  have hXo : OpOk b b .a3 (T k) (N k) k s1 :=
    ⟨hc1.a3, by decide, fun j hj => by omega, fun j _ => al8 hc1.al (by omega), fun j _ => hc1.inR (by omega),
      fun j hj => Offset.disjoint b (.inl (by omega)) (by omega) (by omega)⟩
  have hYo : OpOk b b .a3 (N k) (N k) k s1 :=
    ⟨hc1.a3, by decide, fun j hj => by omega, fun j _ => al8 hc1.al (by omega), fun j _ => hc1.inR (by omega),
      fun j hj => Offset.disjoint b (.inr (by omega)) (by omega) (by omega)⟩
  have a50 : (s1.gpr .a5).toNat = 0 := by rw [u1.gpr]; rfl
  refine WP.block_append (WP.block_append (WP.mono (sbbRow_ok hc1 (by omega) n8 hXo hYo (by omega) k
    (Nat.le_refl _)) fun s2 h2 => ?_))
  have hc2 : Ctx b s2 := ctx_of hc1 (h2.gpr _ (by decide)) h2.wr
  refine ld_ok hc2 (by omega) (by omega) fun s3 u3 => wp_sub fun s4 u4 => WP.block_nil ?_
  -- The difference's facts.
  have m1 : s1.mem = s.mem := u1.mem
  have hTk : dw s2.mem b (T k + 8 * k) = dw s.mem b (T k + 8 * k) := by
    rw [dw_frame h2.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inl (by omega)) (by omega) (by omega), m1]
  have hTlow : ∀ i < k, dw s2.mem b (T k + 8 * i) = dw s.mem b (T k + 8 * i) := fun i hi => by
    rw [dw_frame h2.frame fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inl (by omega)) (by omega) (by omega), m1]
  have hsv := h2.val
  rw [a50, m1] at hsv
  have hD : colsV (fun i => dw s2.mem b (N k + 8 * i)) k < (2 ^ 64) ^ k := colsV_lt _ (fun _ => dw_lt _ _ _) k
  have hM : nv k s.mem b < (2 ^ 64) ^ k := colsV_lt _ (fun _ => dw_lt _ _ _) k
  have hVs : tv k s.mem b (k + 1) = colsV (fun i => dw s.mem b (T k + 8 * i)) k +
      (2 ^ 64) ^ k * dw s.mem b (T k + 8 * k) := rfl
  obtain ⟨hT1, hno, hsel1, hsel0⟩ := csub_nat hD hM hVs hV hsv h2.cy
  -- The mask.
  have a7 : s4.gpr .a7 = s3.gpr .a7 - s3.gpr .a5 := u4.gpr
  have a7x : (s3.gpr .a7).toNat = dw s.mem b (T k + 8 * k) := by rw [u3.gpr, ← hTk]; rfl
  have a5x : s3.gpr .a5 = s2.gpr .a5 := u3.other _ (by decide)
  obtain ⟨hmask, hall⟩ := toNat_sub_bits (x := s3.gpr .a7) (c := s3.gpr .a5) (by rw [a7x]; exact hT1)
    (by rw [a5x]; exact h2.cy) (by rw [a7x, a5x]; exact hno)
  rw [← a7] at hmask hall
  -- The selection.
  have m4 : s4.mem = s2.mem := by rw [u4.mem, u3.mem]
  have g4 : ∀ r, r ∉ clobB → s4.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u4.other r hr.2.2.2.2.2, u3.other r hr.2.2.2.2.2, h2.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2]), u1.other r hr.2.2.2.1]
  have wr4 : s4.wr = s.wr := by rw [u4.wr, u3.wr, h2.wr, u1.wr]
  have hS : SelOk k b O (decide (s4.gpr .a7 = BitVec.allOnes 64)) s4 :=
    { ctx := ctx_of hc (g4 _ (by decide)) wr4
      nowrap := hb
      t2 := by rw [g4 _ (by decide), hC.t2]
      oal := hC.oal
      onw := hC.onw
      ow := by rw [wr4]; exact hC.ow
      tdis := fun i hi => hC.tdis i (by omega)
      ndis := hC.ndis
      mask := hmask
      sel := by simp
      k7 := hC.k7
      k30 := hC.k30 }
  refine WP.mono (selRow_ok hS k (Nat.le_refl _)) fun s5 h5 => ?_
  refine ⟨fun r hr => by rw [h5.gpr r (fun h' => hr (by simp at h' ⊢; rcases h' with h' | h' <;> simp [h'])), g4 r hr],
    by rw [h5.rd, u4.rd, u3.rd, h2.rd, u1.rd], by rw [h5.wr, wr4],
    by rw [h5.sp, u4.sp, u3.sp, h2.sp, u1.sp], ?_, ?_⟩
  · have f2 : Frame [⟨b + BitVec.ofNat 64 (N k), 8 * k⟩, ⟨O, 8 * k⟩] s.mem s4.mem := by
      rw [m4, ← m1]; exact h2.frame.mono fun r hr => by simp at hr; simp [hr]
    exact f2.trans (h5.frame.mono fun r hr => by simp at hr; simp [hr])
  · have hov : ov s5.mem O k = colsV (fun i => if decide (s4.gpr .a7 = BitVec.allOnes 64) then
        dw s4.mem b (T k + 8 * i) else dw s4.mem b (N k + 8 * i)) k :=
      colsV_congr fun i hi => h5.val i hi
    rw [hov, m4]
    by_cases hsel : (s4.gpr .a7 = BitVec.allOnes 64)
    · have hTc := hall.mp hsel
      rw [a7x, a5x] at hTc
      simp only [hsel, decide_true, ↓reduceIte]
      rw [hsel1 hTc]
      exact colsV_congr fun i hi => hTlow i hi
    · have hTc : ¬ (dw s.mem b (T k + 8 * k) = 0 ∧ (s2.gpr .a5).toNat = 1) := fun h' =>
        hsel (hall.mpr (by rw [a7x, a5x]; exact h'))
      simp only [hsel, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [hsel0 hTc]

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: a sum with carries

`n` steps of `adcStep mk xb xo yb yo db d` (`Impl/Weierstrass/RISCV64/GenWide.lean`),
for `mk` nothing or the mask `a2` (`mkOf`): the words at `Dst + d` (`Dst` in
`db`) become those of `X + Y + a5`, for the words `X` at `xb + xo` and the
words at `yb + yo`, under the mask if `mk` takes it, with the carry out in `a5`
(`adcRow_ok`). Only those `n` words are written.
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_write_self dw_write_other dw_frame al8 colsV)
open VG.Proof.Weierstrass.RISCV64.P256Field (adc_ok)

/-- Nothing, or the mask `a2` on `a7`. -/
def mkOf (msk : Bool) : List Instr := if msk then [.logic .and .a7 .a7 .a2] else []

/-- A word of the second operand, under the mask `M` or not. -/
def yw (msk : Bool) (M : BitVec 64) (y : Nat) : Nat := if msk then (BitVec.ofNat 64 y &&& M).toNat else y

theorem yw_lt (msk : Bool) (M : BitVec 64) (y : Nat) (hy : y < 2 ^ 64) : yw msk M y < 2 ^ 64 := by
  unfold yw; split
  · exact BitVec.isLt _
  · exact hy

/-- The destination of a row: `n` words at `Dst + d + 8 j`, through `db`. -/
structure DstOk (Dst : Addr) (db : Reg) (d n : Nat) (s0 : State) : Prop where
  hd : s0.gpr db = Dst
  hdb : db ∉ clobB
  al : Dst.toNat % 8 = 0
  d8 : d % 8 = 0
  hdo : d + 8 * n ≤ 2048
  nowrap : Dst.toNat + d + 8 * n ≤ 2 ^ 64
  w : ∀ j < n, InRegions s0.wr (Dst + BitVec.ofNat 64 (d + 8 * j)) 8

/-- After `j` steps of a sum from `s0`. -/
structure AdcInv (Dst X Y : Addr) (xo yo d : Nat) (msk : Bool) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ clobB → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨Dst + BitVec.ofNat 64 d, 8 * j⟩] s0.mem s.mem
  cy : (s.gpr .a5).toNat ≤ 1
  val : colsV (fun i => dw s.mem Dst (d + 8 * i)) j + (2 ^ 64) ^ j * (s.gpr .a5).toNat =
    colsV (fun i => dw s0.mem X (xo + 8 * i)) j + colsV (fun i => yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * i))) j +
      (s0.gpr .a5).toNat

/-- `mk`: `a7` under the mask or not, nothing else written. -/
theorem wp_mk {msk : Bool} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', (s'.gpr .a7).toNat = yw msk (s.gpr .a2) (s.gpr .a7).toNat → (∀ r, r ≠ .a7 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (mkOf msk ++ is)) s Q := by
  cases msk
  · exact k s (by simp [yw]) (fun _ _ => rfl) rfl rfl rfl rfl
  · refine WP.cons exec_logic ?_
    refine k _ ?_ (fun r hr => ?_) rfl rfl rfl rfl
    · simp only [yw, ↓reduceIte, RegUpd.gpr_write, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · simp only [RegUpd.gpr_write, hr, ite_false]

set_option linter.unusedSimpArgs false in
/-- Step `j` of a sum. -/
theorem adcStep_ok {Dst X Y : Addr} {xb yb db : Reg} {xo yo d n : Nat} {msk : Bool} {s0 : State}
    (hD : DstOk Dst db d n s0) (hX : OpOk Dst X xb xo d n s0) (hY : OpOk Dst Y yb yo d n s0)
    {j : Nat} (hj : j < n) {s : State}
    (h : AdcInv Dst X Y xo yo d msk s0 j s) :
    WP isa (.block (adcStep (mkOf msk) xb xo yb yo db d j)) s (AdcInv Dst X Y xo yo d msk s0 (j + 1)) := by
  have hxo := hX.hxo j hj
  have hyo := hY.hxo j hj
  have hdo := hD.hdo
  have hnw := hD.nowrap
  unfold adcStep
  rw [List.append_assoc, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  refine wp_ld (by omega) (by rw [h.gpr _ hX.hxb, hX.hx]) (hX.al j hj)
    (by rw [h.rd, h.wr]; exact hX.inR j hj) fun s1 u1 => ?_
  refine wp_ld (by omega) (by rw [u1.other _ (fun e => hY.hxb (by rw [e]; decide)), h.gpr _ hY.hxb, hY.hx])
    (hY.al j hj) (by rw [u1.rd, u1.wr, h.rd, h.wr]; exact hY.inR j hj) fun s2 u2 => ?_
  refine wp_mk fun s3 e3 g3 m3 rd3 wr3 sp3 => ?_
  refine WP.block_append (WP.mono (adc_ok (d := .t0) (x := .a6) (y := .a7) (c := .a5) (u := .t3))
    fun s4 ⟨e4, k4⟩ => ?_)
  have hk4 : db ∉ [Reg.t0, Reg.t3, Reg.a5] := fun e => hD.hdb (by
    revert e; simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (h | h | h) <;> simp [h])
  refine wp_sd (by omega) (by rw [k4.1 _ hk4, g3 _ (fun e => hD.hdb (by rw [e]; decide)),
      u2.other _ (fun e => hD.hdb (by rw [e]; decide)), u1.other _ (fun e => hD.hdb (by rw [e]; decide)),
      h.gpr _ hD.hdb, hD.hd]) (al8 hD.al (by have := hD.d8; omega))
    (by rw [k4.2.2.2.1, wr3, u2.wr, u1.wr, h.wr]; exact hD.w j hj) fun s5 u5 => WP.block_nil ?_
  have a5 : s3.gpr .a5 = s.gpr .a5 := by rw [g3 _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
  have e4v := e4 (by rw [a5]; exact h.cy)
  have hX0 : dw s.mem X (xo + 8 * j) = dw s0.mem X (xo + 8 * j) :=
    dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hX.dis j hj
  have hY0 : dw s.mem Y (yo + 8 * j) = dw s0.mem Y (yo + 8 * j) :=
    dw_frame h.frame fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hY.dis j hj
  have a6 : (s3.gpr .a6).toNat = dw s0.mem X (xo + 8 * j) := by
    rw [g3 _ (by decide), u2.other _ (by decide), u1.gpr, ← hX0]; rfl
  have a7 : (s3.gpr .a7).toNat = yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * j)) := by
    rw [e3, u2.other _ (by decide), u1.other _ (by decide), h.gpr _ (by decide), u2.gpr, u1.mem, ← hY0]; rfl
  have hm5 : s5.mem = s.mem.writeW (Dst + BitVec.ofNat 64 (d + 8 * j)) (s4.gpr .t0) := by
    rw [u5.mem, k4.2.1, m3, u2.mem, u1.mem]
  refine ⟨fun r hr => ?_, by rw [u5.rd, k4.2.2.1, rd3, u2.rd, u1.rd, h.rd],
    by rw [u5.wr, k4.2.2.2.1, wr3, u2.wr, u1.wr, h.wr], by rw [u5.sp, k4.2.2.2.2, sp3, u2.sp, u1.sp, h.sp], ?_,
    by
      rw [u5.gpr]
      have := (s3.gpr .a6).isLt; have := (s3.gpr .a7).isLt; have := h.cy
      rw [← a5] at this
      omega, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u5.gpr, k4.1 r (by simp [hr.1, hr.2.1, hr.2.2.2.1]), g3 r hr.2.2.2.2.2, u2.other r hr.2.2.2.2.2,
      u1.other r hr.2.2.2.2.1, h.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2])]
  · rw [hm5]
    refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub Dst (Nat.le_refl _) (by omega)⟩
    · exact Offset.contains Dst (by omega) (by omega) (by omega)
  · have hv := h.val
    have hcw : colsV (fun i => dw s5.mem Dst (d + 8 * i)) j = colsV (fun i => dw s.mem Dst (d + 8 * i)) j :=
      colsV_congr fun i hi => by rw [hm5, dw_write_other _ _ _ (by omega) (by omega) (by omega)]
    rw [a6, a7, a5] at e4v
    show colsV (fun i => dw s5.mem Dst (d + 8 * i)) j + (2 ^ 64) ^ j * dw s5.mem Dst (d + 8 * j) +
        (2 ^ 64) ^ (j + 1) * (s5.gpr .a5).toNat =
      colsV (fun i => dw s0.mem X (xo + 8 * i)) j + (2 ^ 64) ^ j * dw s0.mem X (xo + 8 * j) +
        (colsV (fun i => yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * i))) j +
          (2 ^ 64) ^ j * yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * j))) + (s0.gpr .a5).toNat
    rw [hcw, hm5, dw_write_self, u5.gpr, show (2 ^ 64) ^ (j + 1) = (2 ^ 64) ^ j * 2 ^ 64 from Nat.pow_succ ..]
    generalize (2 ^ 64) ^ j = E at *
    have key : E * (s4.gpr .t0).toNat + E * 2 ^ 64 * (s4.gpr .a5).toNat =
        E * dw s0.mem X (xo + 8 * j) + E * yw msk (s0.gpr .a2) (dw s0.mem Y (yo + 8 * j)) + E * (s.gpr .a5).toNat := by
      rw [Nat.mul_assoc, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add, e4v]
    omega

/-- The sum. -/
theorem adcRow_ok {Dst X Y : Addr} {xb yb db : Reg} {xo yo d n : Nat} {msk : Bool} {s0 : State}
    (hD : DstOk Dst db d n s0) (hX : OpOk Dst X xb xo d n s0) (hY : OpOk Dst Y yb yo d n s0)
    (hc0 : (s0.gpr .a5).toNat ≤ 1) :
    ∀ j ≤ n, WP isa (.block ((List.range j).flatMap (adcStep (mkOf msk) xb xo yb yo db d))) s0
      (AdcInv Dst X Y xo yo d msk s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, hc0, by simp [colsV]⟩
  | j + 1, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (adcRow_ok hD hX hY hc0 j (by omega)) fun s h =>
      adcStep_ok hD hX hY (j := j) (by omega) h)

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: the modulus's words and `T = 0`

`fillN k m` (`Impl/Weierstrass/RISCV64/GenWide.lean`) stores the `k` words of
`m` at `N` (`fillN_ok`), and `mulInit k m` the `k + 1` zero words of `T` and
`m'` into `t6` (`mulInit_ok`).
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Impl.Words.RISCV64 (li64)
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt ld_ok sd_ok dw_write_self dw_write_other dw_frame al8 colsV)

/-- `li64 d tmp v`. -/
theorem wp_li64 {is : List Instr} {s : State} {Q : State → Prop} {d tmp : Reg} (hdt : d ≠ tmp) (v : BitVec 64)
    (k : ∀ s', s'.gpr d = v → Keeps [d, tmp] s s' → WP isa (.block is) s' Q) :
    WP isa (.block (li64 d tmp v ++ is)) s Q :=
  WP.block_append (WP.mono (ByteLoad.li64_ok hdt v) fun s' h => by
    subst h
    exact k _ (RegUpd.gpr_write_self _ _ _)
      (((Keeps.refl [d, tmp] s).write _ (by simp)).write _ (by simp)))

/-- A number's `n` words. -/
theorem colsV_wordOf (m : Nat) : ∀ n, colsV (fun j => (wordOf m j).toNat) n = m % (2 ^ 64) ^ n
  | 0 => by simp [colsV, Nat.mod_one]
  | n + 1 => by
    have e : ((2 : Nat) ^ 64) ^ (n + 1) = (2 ^ 64) ^ n * 2 ^ 64 := Nat.pow_succ ..
    rw [colsV_succ, colsV_wordOf m n, e, Nat.mod_mul]
    simp only [wordOf, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- After `j` words of `m`. -/
structure FillInv (k : Nat) (b : Addr) (m : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : ∀ r, r ∉ [.a6, .a7] → s.gpr r = s0.gpr r
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (N k), 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem b (N k + 8 * i) = (wordOf m i).toNat

theorem fill_ok {k : Nat} {b : Addr} {m : Nat} {s0 : State} (hc : Ctx b s0) (hk : 1 ≤ k) (hk' : k ≤ 30) :
    ∀ j ≤ k, WP isa (.block ((List.range j).flatMap fun j =>
      li64 .a6 .a7 (wordOf m j) ++ ([.store .d .a6 .a3 (N k + 8 * j)] : List Instr))) s0 (FillInv k b m s0 j)
  | 0, _ => WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    obtain ⟨hNT, n8, ntop⟩ := N_facts k hk hk'
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (fill_ok hc hk hk' j (by omega)) fun s h => ?_)
    refine wp_li64 (by decide) _ fun s1 e1 k1 => ?_
    have hc1 : Ctx b s1 := ctx_of hc (by rw [k1.1 _ (by decide), h.gpr _ (by decide)]) (by rw [k1.2.2.2.1, h.wr])
    refine sd_ok hc1 (by omega) (by omega) fun s2 u2 => WP.block_nil ?_
    have hm2 : s2.mem = s.mem.writeW (b + BitVec.ofNat 64 (N k + 8 * j)) (wordOf m j) := by
      rw [u2.mem, k1.2.1, e1]
    refine ⟨fun r hr => by rw [u2.gpr, k1.1 r hr, h.gpr r hr], by rw [u2.rd, k1.2.2.1, h.rd],
      by rw [u2.wr, k1.2.2.2.1, h.wr], by rw [u2.sp, k1.2.2.2.2, h.sp], ?_, fun i hi => ?_⟩
    · rw [hm2]
      refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
      · exact Offset.contains b (by omega) (by omega) (by have := hc.al; omega)
    · rw [hm2]
      by_cases hij : i = j
      · subst hij; rw [dw_write_self]
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.val i (by omega)

/-- `m`'s words at `N`. -/
theorem fillN_ok {k : Nat} {b : Addr} {m : Nat} {s0 : State} (hc : Ctx b s0) (hk : 1 ≤ k) (hk' : k ≤ 30)
    (hm : m < 2 ^ (64 * k)) {is : List Instr} {Q : State → Prop}
    (h : ∀ s, (∀ r, r ∉ [.a6, .a7] → s.gpr r = s0.gpr r) → s.rd = s0.rd → s.wr = s0.wr → s.sp = s0.sp →
      Frame [⟨b + BitVec.ofNat 64 (N k), 8 * k⟩] s0.mem s.mem → nv k s.mem b = m →
      (∀ i < k, dw s.mem b (N k + 8 * i) = (wordOf m i).toNat) → WP isa (.block is) s Q) :
    WP isa (.block (fillN k m ++ is)) s0 Q := by
  refine WP.block_append (WP.mono (fill_ok hc hk hk' k (Nat.le_refl _)) fun s hs => ?_)
  refine h s hs.gpr hs.rd hs.wr hs.sp hs.frame ?_ hs.val
  rw [show nv k s.mem b = colsV (fun j => (wordOf m j).toNat) k from colsV_congr fun i hi => hs.val i hi,
    colsV_wordOf, Nat.mod_eq_of_lt (by rw [← Nat.pow_mul]; exact hm)]

/-- After `j` zero words of `T`. -/
structure ZeroInv (k : Nat) (b : Addr) (s0 : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = s0.gpr
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  frame : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * j⟩] s0.mem s.mem
  val : ∀ i < j, dw s.mem b (T k + 8 * i) = 0

theorem zero_ok {k : Nat} {b : Addr} {s0 : State} (hc : Ctx b s0) (hk : 1 ≤ k) (hk' : k ≤ 30)
    (h7 : s0.gpr .a7 = 0) :
    ∀ j ≤ k + 1, WP isa (.block ((List.range j).map fun j => .store .d .a7 .a3 (T k + 8 * j))) s0
      (ZeroInv k b s0 j)
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | j + 1, hj => by
    obtain ⟨t8, ttop⟩ := T_facts k hk hk'
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (zero_ok hc hk hk' h7 j (by omega)) fun s h => ?_)
    have hcs : Ctx b s := ctx_of hc (by rw [h.gpr]) h.wr
    refine sd_ok hcs (by omega) (by omega) fun s1 u1 => WP.block_nil ?_
    have hm1 : s1.mem = s.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * j)) (0 : BitVec 64) := by rw [u1.mem, h.gpr, h7]
    refine ⟨by rw [u1.gpr, h.gpr], by rw [u1.rd, h.rd], by rw [u1.wr, h.wr], by rw [u1.sp, h.sp], ?_,
      fun i hi => ?_⟩
    · rw [hm1]
      refine (h.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
      · exact Offset.contains b (by omega) (by omega) (by have := hc.al; omega)
    · rw [hm1]
      by_cases hij : i = j
      · subst hij; rw [dw_write_self]; rfl
      · rw [dw_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h.val i (by omega)

/-- `T = 0` and `m'` in `t6`. -/
theorem mulInit_ok {k : Nat} {b : Addr} {m : Nat} {s0 : State} (hc : Ctx b s0) (hk : 1 ≤ k) (hk' : k ≤ 30) :
    WP isa (.block (mulInit k m)) s0 fun s =>
      (∀ r, r ∉ [.a7, .t6] → s.gpr r = s0.gpr r) ∧ s.rd = s0.rd ∧ s.wr = s0.wr ∧ s.sp = s0.sp ∧
      Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩] s0.mem s.mem ∧ tv k s.mem b (k + 1) = 0 ∧
      s.gpr .t6 = BitVec.ofNat 64 (negInv m) := by
  obtain ⟨t8, ttop⟩ := T_facts k hk hk'
  unfold mulInit
  refine wp_li (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := ctx_of hc (u1.other _ (by decide)) u1.wr
  refine WP.block_append (WP.mono (zero_ok hc1 hk hk' (by rw [u1.gpr]; rfl) (k + 1) (Nat.le_refl _))
    fun s2 h2 => ?_)
  refine WP.mono (ByteLoad.li64_ok (s := s2) (d := .t6) (tmp := .a7) (by decide) _) fun s3 h3 => ?_
  subst h3
  refine ⟨fun r hr => ?_, h2.rd.trans u1.rd, h2.wr.trans u1.wr, h2.sp.trans u1.sp, ?_, ?_,
    RegUpd.gpr_write_self _ _ _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ hr.2, RegUpd.gpr_write_of_ne _ _ hr.1, h2.gpr, u1.other r hr.1]
  · show Frame _ s0.mem s2.mem
    rw [← u1.mem]
    exact h2.frame.sub fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
  · show colsV (fun i => dw s2.mem b (T k + 8 * i)) (k + 1) = 0
    rw [colsV_congr (g := fun _ => 0) fun i hi => h2.val i hi]
    clear h2; induction (k + 1) with
    | zero => rfl
    | succ n ih => simp [colsV, ih]

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: the operations on aligned pointers

`mulCore`, `addCore` and `subCore` (`Impl/Weierstrass/RISCV64/GenWide.lean`)
from a state with `a3 = b`, `t4`, `t5` and `t2` pointing to `[a]`, `[b]` and
`[o]` (`CoreOk`): `[o]` becomes `[a] [b] R⁻¹`, `[a] + [b]` or `[a] - [b]`
modulo `m` (`mulCore_ok`, `addCore_ok`, `subCore_ok`), and only `[o]` and the
own working space at `b + T` are written.
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx)
open VG.Proof.X448.RISCV64.R64 (dw dw_lt dw_frame al8 colsV sd_ok dw_write_self dw_write_other)

/-- The registers the operations write. -/
abbrev clobW : List Reg := [.t0, .t3, .t6, .a1, .a2, .a4, .a5, .a6, .a7]

/-- The own working space used: `T` and `N`. -/
abbrev ownR (k : Nat) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (T k), 8 * (2 * k + 2)⟩

/-- What the operations need. -/
structure CoreOk (k : Nat) (b A B O : Addr) (s : State) : Prop where
  ctx : Ctx b s
  nowrap : b.toNat + 2048 ≤ 2 ^ 64
  a : s.gpr .t4 = A
  b' : s.gpr .t5 = B
  o : s.gpr .t2 = O
  aal : A.toNat % 8 = 0
  bal : B.toNat % 8 = 0
  oal : O.toNat % 8 = 0
  ain : ∀ i < k, InRegions (s.rd ++ s.wr) (A + BitVec.ofNat 64 (8 * i)) 8
  bin : ∀ i < k, InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 (8 * i)) 8
  ow : ∀ i < k, InRegions s.wr (O + BitVec.ofNat 64 (8 * i)) 8
  onw : O.toNat + 8 * k ≤ 2 ^ 64
  adis : ∀ i < k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownR k b)
  bdis : ∀ i < k, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (ownR k b)
  odis : Region.Disjoint ⟨O, 8 * k⟩ (ownR k b)
  k7 : 7 ≤ k
  k30 : k ≤ 30

theorem own_facts (k : Nat) (h₁ : 1 ≤ k) (h : k ≤ 30) : T k + 8 * (2 * k + 2) ≤ 2048 ∧ N k + 8 * k = T k + 8 * (2 * k + 2) := by
  unfold N T; omega

/-- A part of the own working space within it. -/
theorem own_sub {k : Nat} {b : Addr} {d n : Nat} (hd : T k ≤ d)
    (hn : d + n ≤ T k + 8 * (2 * k + 2)) : Region.Sub ⟨b + BitVec.ofNat 64 d, n⟩ (ownR k b) :=
  Offset.sub b hd hn

theorem disj_sub {r r₁ r₂ : Region} (h : Region.Disjoint r r₂) (hs : Region.Sub r₁ r₂) : Region.Disjoint r r₁ :=
  fun x h₁ h₂ => h x h₁ (hs x h₂)

theorem disj_symm {r₁ r₂ : Region} (h : Region.Disjoint r₁ r₂) : Region.Disjoint r₂ r₁ :=
  fun x h₁ h₂ => h x h₂ h₁

theorem mont_nat {V a Bv Q M R : Nat} (hinv : V * R = a * Bv + Q * M) (ha : a < R) (hB : Bv < M) (hQ : Q < R) :
    V < 2 * M ∧ V % M * R % M = a * Bv % M := by
  have hR : 0 < R := by omega
  refine ⟨?_, ?_⟩
  · apply Nat.lt_of_mul_lt_mul_right (a := R)
    have h1 : a * Bv < R * M := Nat.mul_lt_mul_of_lt_of_le ha (by omega) (by omega)
    have h2 : Q * M ≤ R * M := Nat.mul_le_mul_right _ (by omega)
    rw [hinv, Nat.mul_assoc, Nat.two_mul]
    rw [Nat.mul_comm R M] at h1 h2
    omega
  · rw [Nat.mod_mul_mod, hinv, Nat.add_mul_mod_self_right]

/-- `[o] = [a] [b] R⁻¹ mod m`, below `m`. -/
theorem mulCore_ok {k m : Nat} {b A B O : Addr} {s : State} (hC : CoreOk k b A B O s)
    (hm : m < 2 ^ (64 * k)) (hinv : (wordOf m 0).toNat * negInv m % 2 ^ 64 = 2 ^ 64 - 1)
    (hB : xv s.mem B k < m) :
    WP isa (.block (mulCore k m)) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧
      ov s'.mem O k < m ∧ ov s'.mem O k * 2 ^ (64 * k) % m = xv s.mem A k * xv s.mem B k % m := by
  have k7 := hC.k7
  have k30 := hC.k30
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  obtain ⟨otop, onk⟩ := own_facts k (by omega) k30
  have hb := hC.nowrap
  unfold mulCore
  rw [List.append_assoc, List.append_assoc]
  refine fillN_ok hC.ctx (by omega) k30 hm fun s1 g1 rd1 wr1 sp1 f1 nv1 w1 => ?_
  have hc1 : Ctx b s1 := ctx_of hC.ctx (g1 _ (by decide)) wr1
  refine WP.block_append (WP.mono (mulInit_ok (m := m) hc1 (by omega) k30) fun s2 ⟨g2, rd2, wr2, sp2, f2, z2, t6⟩ => ?_)
  -- The rounds.
  have hc2 : Ctx b s2 := ctx_of hc1 (g2 _ (by decide)) wr2
  have m02 : ∀ {P : Addr} {d : Nat}, Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ (ownR k b) →
      dw s2.mem P d = dw s.mem P d := fun hd => by
    rw [dw_frame f2 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact disj_sub hd (own_sub (Nat.le_refl _) (by omega)),
      dw_frame f1 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact disj_sub hd (own_sub (by omega) (by omega))]
  have hN2 : ∀ i < k, dw s2.mem b (N k + 8 * i) = dw s1.mem b (N k + 8 * i) := fun i hi =>
    dw_frame f2 fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega)
  have hL : LoopOk k b A B (negInv m) s2 :=
    { mo := ⟨hc2, hb, by rw [g2 _ (by decide), g1 _ (by decide), hC.a], hC.aal,
        by rw [rd2, wr2, rd1, wr1]; exact hC.ain,
        fun i hi j hj => disj_sub (hC.adis i hi) (own_sub (Nat.le_refl _) (by omega)), k7, k30⟩
      t5 := by rw [g2 _ (by decide), g1 _ (by decide), hC.b']
      bal := hC.bal
      bin := by rw [rd2, wr2, rd1, wr1]; exact hC.bin
      bdis := fun i hi => disj_sub (hC.bdis i hi) (own_sub (Nat.le_refl _) (by omega))
      t6 := t6
      m'lt := Nat.mod_lt _ (by decide)
      inv := by
        rw [show N k = N k + 8 * 0 by rfl, hN2 0 (by omega), w1 0 (by omega)]
        unfold negInv at hinv ⊢; exact hinv
      zero := z2 }
  refine WP.block_append (WP.mono (loop_ok hL k (Nat.le_refl _)) fun s3 h3 => ?_)
  -- The final subtraction.
  have hc3 : Ctx b s3 := ctx_of hc2 (h3.gpr _ (by decide)) h3.wr
  have hA : xv s2.mem A k = xv s.mem A k := colsV_congr fun i hi => m02 (hC.adis i hi)
  have hBv : bv s2.mem B k = xv s.mem B k := colsV_congr fun i hi => m02 (hC.bdis i hi)
  have hNv : nv k s2.mem b = m := by
    rw [← nv1]; exact colsV_congr fun i hi => hN2 i hi
  obtain ⟨Q, hQ, hv⟩ := h3.val
  rw [hA, hBv, hNv] at hv
  have hNv3 : nv k s3.mem b = m := by
    rw [← hNv]
    exact colsV_congr fun i hi => frame_dw h3.frame (Offset.disjoint b (.inr (by omega)) (by omega) (by omega))
  have hR : (2 ^ 64) ^ k = 2 ^ (64 * k) := (Nat.pow_mul ..).symm
  rw [hR] at hv hQ
  obtain ⟨hV2, hVm⟩ := mont_nat hv (by rw [← hR]; exact colsV_lt _ (fun _ => dw_lt _ _ _) k) hB hQ
  have hCs : CsubOk k b O s3 :=
    { ctx := hc3
      nowrap := hb
      t2 := by rw [h3.gpr _ (by decide), g2 _ (by decide), g1 _ (by decide), hC.o]
      oal := hC.oal
      onw := hC.onw
      ow := by rw [h3.wr, wr2, wr1]; exact hC.ow
      tdis := fun i hi => disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))
      ndis := fun i hi => disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))
      k7 := k7
      k30 := k30 }
  refine WP.mono (csub_ok hCs (by rw [hNv3]; exact hV2)) fun s4 ⟨g4, rd4, wr4, sp4, f4, v4⟩ => ?_
  rw [hNv3] at v4
  refine ⟨fun r hr => ?_, by rw [rd4, h3.rd, rd2, rd1], by rw [wr4, h3.wr, wr2, wr1],
    by rw [sp4, h3.sp, sp2, sp1], ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g4 r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      h3.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2]), g2 r (by simp [hr.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g1 r (by simp [hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · have sub1 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (N k), 8 * k⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩], Region.Sub r r' :=
      fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., own_sub (by omega) (by omega)⟩
    have subT : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (T k), 8 * (k + 2)⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., own_sub (Nat.le_refl _) (by omega)⟩
    have sub4 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (N k), 8 * k⟩ : Region), ⟨O, 8 * k⟩], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., own_sub (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun x h => h⟩
    exact (((f1.sub sub1).trans (f2.sub subT)).trans (h3.frame.sub subT)).trans (f4.sub sub4)
  · rw [v4]; exact Nat.mod_lt _ (by omega)
  · rw [v4]; exact hVm

theorem colsV_yw_false (M : BitVec 64) (f : Nat → Nat) (n : Nat) :
    colsV (fun i => yw false M (f i)) n = colsV f n := by simp [yw]

theorem add_zero_addr (O : Addr) : O + BitVec.ofNat 64 0 = O := by simp

/-- The own working space's frames within it. -/
theorem sub_own {k : Nat} {b O : Addr} (hk : 1 ≤ k) (hk' : k ≤ 30) {d n : Nat} (hd : T k ≤ d)
    (hn : d + n ≤ T k + 8 * (2 * k + 2)) :
    ∀ r ∈ [(⟨b + BitVec.ofNat 64 d, n⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩], Region.Sub r r' :=
  fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    have := own_facts k hk hk'
    exact ⟨_, List.mem_cons_self .., own_sub hd hn⟩

/-- `[o] = [a] + [b] mod m`, for `[a] + [b] < 2 m`. -/
theorem addCore_ok {k m : Nat} {b A B O : Addr} {s : State} (hC : CoreOk k b A B O s)
    (hm : m < 2 ^ (64 * k)) (hAB : xv s.mem A k + xv s.mem B k < 2 * m) :
    WP isa (.block (addCore k m)) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧
      ov s'.mem O k = (xv s.mem A k + xv s.mem B k) % m := by
  have k7 := hC.k7
  have k30 := hC.k30
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  obtain ⟨otop, onk⟩ := own_facts k (by omega) k30
  have hb := hC.nowrap
  unfold addCore addSum
  rw [List.append_assoc]
  refine fillN_ok hC.ctx (by omega) k30 hm fun s1 g1 rd1 wr1 sp1 f1 nv1 w1 => ?_
  have hc1 : Ctx b s1 := ctx_of hC.ctx (g1 _ (by decide)) wr1
  refine wp_li (by decide) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := ctx_of hc1 (u2.other _ (by decide)) u2.wr
  have g2 : ∀ r, r ∉ [.a5, .a6, .a7] → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other r hr.1, g1 r (by simp [hr.2.1, hr.2.2])]
  have m2 : s2.mem = s1.mem := u2.mem
  have hD : DstOk b .a3 (T k) k s2 :=
    ⟨hc2.a3, by decide, hc2.al, t8, by omega, by omega, fun j hj => hc2.inW (by omega)⟩
  have hXo : OpOk b A .t4 0 (T k) k s2 :=
    ⟨by rw [g2 _ (by decide), hC.a], by decide, fun j hj => by omega,
      fun j _ => by rw [Nat.zero_add]; exact al8 hC.aal (by omega),
      fun j hj => by rw [Nat.zero_add, u2.rd, u2.wr, rd1, wr1]; exact hC.ain j hj,
      fun j hj => by rw [Nat.zero_add]; exact disj_sub (hC.adis j hj) (own_sub (by omega) (by omega))⟩
  have hYo : OpOk b B .t5 0 (T k) k s2 :=
    ⟨by rw [g2 _ (by decide), hC.b'], by decide, fun j hj => by omega,
      fun j _ => by rw [Nat.zero_add]; exact al8 hC.bal (by omega),
      fun j hj => by rw [Nat.zero_add, u2.rd, u2.wr, rd1, wr1]; exact hC.bin j hj,
      fun j hj => by rw [Nat.zero_add]; exact disj_sub (hC.bdis j hj) (own_sub (by omega) (by omega))⟩
  show WP isa (.block (((List.range k).flatMap (adcStep (mkOf false) .t4 0 .t5 0 .a3 (T k)) ++
    [.store .d .a5 .a3 (T k + 8 * k)]) ++ csub k)) s2 _
  refine WP.block_append (WP.block_append (WP.mono (adcRow_ok hD hXo hYo (by rw [u2.gpr]; decide) k
    (Nat.le_refl _)) fun s3 h3 => ?_))
  have hc3 : Ctx b s3 := ctx_of hc2 (h3.gpr _ (by decide)) h3.wr
  refine sd_ok hc3 (by omega) (by omega) fun s4 u4 => WP.block_nil ?_
  have hc4 : Ctx b s4 := ctx_of hc3 (by rw [u4.gpr]) u4.wr
  -- The sum.
  have m01 : ∀ {P : Addr} {d : Nat}, Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ (ownR k b) →
      dw s1.mem P d = dw s.mem P d := fun hd => by
    rw [dw_frame f1 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact disj_sub hd (own_sub (by omega) (by omega))]
  have hv := h3.val
  rw [colsV_yw_false, m2, u2.gpr] at hv
  have hA : colsV (fun i => dw s1.mem A (0 + 8 * i)) k = xv s.mem A k :=
    colsV_congr fun i hi => by rw [Nat.zero_add]; exact m01 (hC.adis i hi)
  have hB : colsV (fun i => dw s1.mem B (0 + 8 * i)) k = xv s.mem B k :=
    colsV_congr fun i hi => by rw [Nat.zero_add]; exact m01 (hC.bdis i hi)
  rw [hA, hB] at hv
  have hm4 : s4.mem = s3.mem.writeW (b + BitVec.ofNat 64 (T k + 8 * k)) (s3.gpr .a5) := u4.mem
  have hT4 : tv k s4.mem b (k + 1) = xv s.mem A k + xv s.mem B k := by
    show colsV _ k + (2 ^ 64) ^ k * dw s4.mem b (T k + 8 * k) = _
    rw [colsV_congr (g := fun i => dw s3.mem b (T k + 8 * i)) fun i hi => by
      rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega)], hm4, dw_write_self]
    have : (BitVec.ofNat 64 0).toNat = 0 := rfl
    rw [this, Nat.add_zero] at hv
    exact hv
  have hNv4 : nv k s4.mem b = m := by
    rw [← nv1]
    refine colsV_congr fun i hi => ?_
    rw [hm4, dw_write_other _ _ _ (by omega) (by omega) (by omega),
      dw_frame h3.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega), m2]
  have hCs : CsubOk k b O s4 :=
    { ctx := hc4
      nowrap := hb
      t2 := by rw [u4.gpr, h3.gpr _ (by decide), g2 _ (by decide), hC.o]
      oal := hC.oal
      onw := hC.onw
      ow := by rw [u4.wr, h3.wr, u2.wr, wr1]; exact hC.ow
      tdis := fun i hi => disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))
      ndis := fun i hi => disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))
      k7 := k7
      k30 := k30 }
  refine WP.mono (csub_ok hCs (by rw [hT4, hNv4]; exact hAB)) fun s5 ⟨g5, rd5, wr5, sp5, f5, v5⟩ => ?_
  rw [hT4, hNv4] at v5
  refine ⟨fun r hr => ?_, by rw [rd5, u4.rd, h3.rd, u2.rd, rd1], by rw [wr5, u4.wr, h3.wr, u2.wr, wr1],
    by rw [sp5, u4.sp, h3.sp, u2.sp, sp1], ?_, v5⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g5 r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]), u4.gpr,
      h3.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g2 r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · have fT : Frame [⟨b + BitVec.ofNat 64 (T k), 8 * (k + 1)⟩] s1.mem s4.mem := by
      rw [hm4, ← m2]
      refine (h3.frame.sub fun r hr => ?_).writeW (List.mem_singleton_self _) _ ?_
      · rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub b (Nat.le_refl _) (by omega)⟩
      · exact Offset.contains b (by omega) (by omega) (by omega)
    have sub5 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (N k), 8 * k⟩ : Region), ⟨O, 8 * k⟩], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., own_sub (by omega) (by omega)⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun x h => h⟩
    exact ((f1.sub (sub_own (by omega) k30 (by omega) (by omega))).trans
      (fT.sub (sub_own (by omega) k30 (Nat.le_refl _) (by omega)))).trans (f5.sub sub5)

theorem sub_nat {D a b m E c c' ov Y : Nat} (hs : D + b + 0 = a + E * c) (hc : c ≤ 1) (hc' : c' ≤ 1)
    (hY : Y = if c = 1 then m else 0) (hadd : ov + E * c' = D + Y + 0) (hD : D < E) (hov : ov < E)
    (ha : a < m) (hb : b < m) : ov = (a + m - b) % m := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc' with rfl | rfl <;>
    simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero, show (0 : Nat) = 1 ↔ False by decide,
      ↓reduceIte] at hs hadd hY <;> subst hY
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · omega
  · omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem colsV_mask (f : Nat → Nat) (hf : ∀ i, f i < 2 ^ 64) {c : BitVec 64} (hc : c.toNat ≤ 1) (n : Nat) :
    colsV (fun i => yw true (BitVec.ofNat 64 0 - c) (f i)) n = if c.toNat = 1 then colsV f n else 0 := by
  have hc' : c = 0 ∨ c = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with e | e
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  rcases hc' with rfl | rfl
  · simp only [yw, ↓reduceIte, show (BitVec.ofNat 64 0 - 0 : BitVec 64) = 0 by decide,
      show ((0 : BitVec 64).toNat = 1) = False by decide]
    induction n with
    | zero => rfl
    | succ n ih => rw [colsV_succ, ih]; simp
  · have e : (BitVec.ofNat 64 0 - 1 : BitVec 64) = BitVec.allOnes 64 := by decide
    simp only [yw, ↓reduceIte, e, BitVec.and_allOnes, BitVec.toNat_ofNat, show ((1 : BitVec 64).toNat = 1) = True by decide]
    exact colsV_congr fun i _ => Nat.mod_eq_of_lt (hf i)

/-- `[o] = [a] - [b] mod m`, for `[a]` and `[b]` below `m`. -/
theorem subCore_ok {k m : Nat} {b A B O : Addr} {s : State} (hC : CoreOk k b A B O s)
    (hm : m < 2 ^ (64 * k)) (hA : xv s.mem A k < m) (hB : xv s.mem B k < m) :
    WP isa (.block (subCore k m)) s fun s' =>
      (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [ownR k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧
      ov s'.mem O k = (xv s.mem A k + m - xv s.mem B k) % m := by
  have k7 := hC.k7
  have k30 := hC.k30
  obtain ⟨t8, ttop⟩ := T_facts k (by omega) k30
  obtain ⟨hNT, n8, ntop⟩ := N_facts k (by omega) k30
  obtain ⟨otop, onk⟩ := own_facts k (by omega) k30
  have hb := hC.nowrap
  have honw := hC.onw
  unfold subCore subDiff
  refine fillN_ok hC.ctx (by omega) k30 hm fun s1 g1 rd1 wr1 sp1 f1 nv1 w1 => ?_
  have hc1 : Ctx b s1 := ctx_of hC.ctx (g1 _ (by decide)) wr1
  refine wp_li (by decide) fun s2 u2 => ?_
  have hc2 : Ctx b s2 := ctx_of hc1 (u2.other _ (by decide)) u2.wr
  have g2 : ∀ r, r ∉ [.a5, .a6, .a7] → s2.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u2.other r hr.1, g1 r (by simp [hr.2.1, hr.2.2])]
  have m2 : s2.mem = s1.mem := u2.mem
  have hXo : OpOk b A .t4 0 (T k) k s2 :=
    ⟨by rw [g2 _ (by decide), hC.a], by decide, fun j hj => by omega,
      fun j _ => by rw [Nat.zero_add]; exact al8 hC.aal (by omega),
      fun j hj => by rw [Nat.zero_add, u2.rd, u2.wr, rd1, wr1]; exact hC.ain j hj,
      fun j hj => by rw [Nat.zero_add]; exact disj_sub (hC.adis j hj) (own_sub (by omega) (by omega))⟩
  have hYo : OpOk b B .t5 0 (T k) k s2 :=
    ⟨by rw [g2 _ (by decide), hC.b'], by decide, fun j hj => by omega,
      fun j _ => by rw [Nat.zero_add]; exact al8 hC.bal (by omega),
      fun j hj => by rw [Nat.zero_add, u2.rd, u2.wr, rd1, wr1]; exact hC.bin j hj,
      fun j hj => by rw [Nat.zero_add]; exact disj_sub (hC.bdis j hj) (own_sub (by omega) (by omega))⟩
  show WP isa (.block (((List.range k).flatMap (sbbStep .t4 0 .t5 0 (T k)) ++
    [.li .a2 0, .sub .a2 .a2 .a5, .li .a5 0]) ++
    (List.range k).flatMap (adcStep (mkOf true) .a3 (T k) .a3 (N k) .t2 0))) s2 _
  refine WP.block_append (WP.block_append (WP.mono (sbbRow_ok hc2 (by omega) t8 hXo hYo
    (by rw [u2.gpr]; decide) k (Nat.le_refl _)) fun s3 h3 => ?_))
  refine wp_li (by decide) fun s4 u4 => wp_sub fun s5 u5 => wp_li (by decide) fun s6 u6 => WP.block_nil ?_
  have g6 : ∀ r, r ∉ clobW → s6.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u6.other r hr.2.2.2.2.2.2.1, u5.other r hr.2.2.2.2.1, u4.other r hr.2.2.2.2.1,
      h3.gpr r (by simp [hr.1, hr.2.1, hr.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      g2 r (by simp [hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  have m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have wr6 : s6.wr = s.wr := by rw [u6.wr, u5.wr, u4.wr, h3.wr, u2.wr, wr1]
  have rd6 : s6.rd = s.rd := by rw [u6.rd, u5.rd, u4.rd, h3.rd, u2.rd, rd1]
  have hc6 : Ctx b s6 := ctx_of hC.ctx (g6 _ (by decide)) wr6
  have a2v : s6.gpr .a2 = BitVec.ofNat 64 0 - s3.gpr .a5 := by
    rw [u6.other _ (by decide), u5.gpr, u4.gpr, u4.other _ (by decide)]
  have hD : DstOk O .t2 0 k s6 :=
    ⟨by rw [g6 _ (by decide), hC.o], by decide, hC.oal, by decide, by omega, by omega,
      fun j hj => by rw [Nat.zero_add, wr6]; exact hC.ow j hj⟩
  have osub : ∀ j ≤ k, Region.Sub ⟨O + BitVec.ofNat 64 0, 8 * j⟩ ⟨O, 8 * k⟩ := fun j hj => Offset.sub_base O (by omega)
  have hTo : OpOk O b .a3 (T k) 0 k s6 :=
    ⟨hc6.a3, by decide, fun j hj => by omega, fun j _ => al8 hc6.al (by omega), fun j _ => hc6.inR (by omega),
      fun j hj => disj_sub (disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))) (osub j (by omega))⟩
  have hNo : OpOk O b .a3 (N k) 0 k s6 :=
    ⟨hc6.a3, by decide, fun j hj => by omega, fun j _ => al8 hc6.al (by omega), fun j _ => hc6.inR (by omega),
      fun j hj => disj_sub (disj_symm (disj_sub hC.odis (own_sub (by omega) (by omega)))) (osub j (by omega))⟩
  refine WP.mono (adcRow_ok hD hTo hNo (by rw [u6.gpr]; decide) k (Nat.le_refl _)) fun s7 h7 => ?_
  -- The numbers.
  have m01 : ∀ {P : Addr} {d : Nat}, Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ (ownR k b) →
      dw s1.mem P d = dw s.mem P d := fun hd => by
    rw [dw_frame f1 fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact disj_sub hd (own_sub (by omega) (by omega))]
  have hsv := h3.val
  rw [m2, u2.gpr] at hsv
  have hAv : colsV (fun i => dw s1.mem A (0 + 8 * i)) k = xv s.mem A k :=
    colsV_congr fun i hi => by rw [Nat.zero_add]; exact m01 (hC.adis i hi)
  have hBv : colsV (fun i => dw s1.mem B (0 + 8 * i)) k = xv s.mem B k :=
    colsV_congr fun i hi => by rw [Nat.zero_add]; exact m01 (hC.bdis i hi)
  rw [hAv, hBv, show (BitVec.ofNat 64 0).toNat = 0 from rfl] at hsv
  have hav := h7.val
  rw [a2v, u6.gpr, show (BitVec.ofNat 64 0).toNat = 0 from rfl, m6,
    colsV_mask _ (fun _ => dw_lt _ _ _) h3.cy] at hav
  have hNv : colsV (fun i => dw s3.mem b (N k + 8 * i)) k = m := by
    rw [← nv1]
    refine colsV_congr fun i hi => ?_
    rw [dw_frame h3.frame fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint b (.inr (by omega)) (by omega) (by omega), m2]
  rw [hNv] at hav
  have hov : ov s7.mem O k = colsV (fun i => dw s7.mem O (0 + 8 * i)) k :=
    colsV_congr fun i _ => by rw [Nat.zero_add]
  have hE : (2 ^ 64) ^ k = 2 ^ (64 * k) := (Nat.pow_mul ..).symm
  have hres := sub_nat hsv h3.cy h7.cy rfl hav (colsV_lt _ (fun _ => dw_lt _ _ _) k)
    (by rw [← hov]; exact colsV_lt _ (fun _ => dw_lt _ _ _) k) hA hB
  refine ⟨fun r hr => by
      rw [h7.gpr r (fun h' => hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
        rcases h' with h | h | h | h | h | h <;> simp [h])), g6 r hr],
    by rw [h7.rd, rd6], by rw [h7.wr, wr6], by rw [h7.sp, u6.sp, u5.sp, u4.sp, h3.sp, u2.sp, sp1], ?_,
    by rw [hov]; exact hres⟩
  · have sub3 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (T k), 8 * k⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := sub_own (by omega) k30 (Nat.le_refl _) (by omega)
    have sub7 : ∀ r ∈ [(⟨O + BitVec.ofNat 64 0, 8 * k⟩ : Region)], ∃ r' ∈ [ownR k b, ⟨O, 8 * k⟩],
        Region.Sub r r' := fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), osub k (Nat.le_refl _)⟩
    have f3 : Frame [ownR k b, ⟨O, 8 * k⟩] s1.mem s3.mem := by rw [← m2]; exact h3.frame.sub sub3
    have f7 : Frame [ownR k b, ⟨O, 8 * k⟩] s3.mem s7.mem := by rw [← m6]; exact h7.frame.sub sub7
    exact ((f1.sub (sub_own (by omega) k30 (by omega) (by omega))).trans f3).trans f7

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: the byte-wise copies

`pack k p a dst` and `unpack k p o src` (`Impl/Weierstrass/RISCV64/GenWide.lean`),
as P-384's (`Proof/Weierstrass/RISCV64/P384Field/Fn.lean`) for `2 k` words of 32
bits: the `8 k` bytes of the element at `a` (from `a3`) to `p + dst`
(`pack_ok`), and back (`unpack_ok`), any of them unaligned.
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Weierstrass.RISCV64.GenWide VG.Proof.X25519.RISCV64
open VG.Proof.Ed25519.RISCV64 (not_a4_a5)
open VG.Proof.X448.RISCV64.R64 (dw dw_split colsV)

/-- After `j` words of `pack k p a dst` from `s0`. -/
structure PackInv (b q : Addr) (a dst : Nat) (s0 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨q + BitVec.ofNat 64 dst, 4 * j⟩] s0.mem s.mem
  outs : ∀ i < j, wd s.mem q (dst + 4 * i) = limb s0.mem b a i

theorem pack_ok {k : Nat} {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {a dst : Nat}
    (ha : a + 8 * k ≤ 2048) (ha4 : a % 4 = 0) (hdst : dst + 8 * k < 2048)
    (hw : ∀ j < 2 * k, InRegions s0.wr (q + BitVec.ofNat 64 (dst + 4 * j)) 4)
    (hd : (⟨q + BitVec.ofNat 64 dst, 8 * k⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 a, 8 * k⟩) :
    WP isa (.block (pack k p a dst)) s0 (PackInv b q a dst s0 (2 * k)) := by
  have hp' := not_a4_a5 hp
  refine wp_range_flatMap (M := isa) (PackInv b q a dst s0) (fun j s hj h => ?_)
    (2 * k) (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩
  have hcs : Ctx b s := hc.of_rest h.rest (by decide)
  refine lw0_ok hcs (d := a + 4 * j) (by omega) (by omega) fun t1 v1 => ?_
  have hq1 : t1.gpr p = q := by rw [v1.other _ hp'.1, h.rest.gpr _ hp, h14]
  refine WP.mono (ByteLoad.storeLE32_ok (v := .a4) (tmp := .a5) (n := p) (off := dst + 4 * j)
    (by decide) hp'.2.symm (by omega) (by rw [hq1, v1.wr, h.rest.wr]; exact hw j hj)) fun t2 e2 => ?_
  have em : t2.mem = s.mem.writeW (q + BitVec.ofNat 64 (dst + 4 * j)) ((t1.gpr .a4).setWidth 32) := by
    rw [e2, RegUpd.mem_write, hq1]
    show t1.mem.writeW _ _ = _
    rw [v1.mem]
  have hr2 : Rest [.a4, .a5] t1 t2 := by
    rw [e2]
    exact ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr).2, rfl, rfl, rfl⟩
  have hsrc : wd s.mem b (a + 4 * j) = limb s0.mem b a j := by
    refine wd_frame h.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    refine fun x hx hx' => hd x ?_ ?_
    · exact Region.sub_prefix (by omega) x hx'
    · exact Offset.sub b (d := a + 4 * j) (n := 4) (e := a) (k := 8 * k) (by omega) (by omega) x hx
  refine ⟨h.rest.trans ((v1.rest (by decide)).trans hr2), ?_, fun i hi => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs i hi
    · rw [wd_write_self, toNat_lo32, v1.gpr, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _)]
      exact hsrc

/-- After `j` words of `unpack k p o src` from `s0`. -/
structure UnpackInv (b : Addr) (o : Nat) (s0 : State) (f : Nat → Nat) (j : Nat) (s : State) : Prop where
  rest : Rest [.a4, .a5] s0 s
  frame : Frame [⟨b + BitVec.ofNat 64 o, 4 * j⟩] s0.mem s.mem
  outs : ∀ i < j, limb s.mem b o i = f i

/-- `unpack k p o src`: the words at `src` from `p` into the element at `o`. -/
theorem unpack_ok {k : Nat} {b q : Addr} {s0 : State} (hc : Ctx b s0) {p : Reg}
    (hp : p ∉ [Reg.a4, .a5]) (h14 : s0.gpr p = q) {o src : Nat}
    (ho : o + 8 * k ≤ 2048) (ho4 : o % 4 = 0) (hsrc : src + 8 * k < 2048)
    (hr : ∀ j < 2 * k, InRegions (s0.rd ++ s0.wr) (q + BitVec.ofNat 64 (src + 4 * j)) 4)
    (hd : (⟨q + BitVec.ofNat 64 src, 8 * k⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 o, 8 * k⟩) :
    WP isa (.block (unpack k p o src)) s0 fun t =>
      Rest [.a4, .a5] s0 t ∧ Frame [⟨b + BitVec.ofNat 64 o, 8 * k⟩] s0.mem t.mem ∧
      ∀ i < 2 * k, limb t.mem b o i = wd s0.mem q (src + 4 * i) := by
  have hp' := not_a4_a5 hp
  let f := fun j => wd s0.mem q (src + 4 * j)
  refine WP.mono (wp_range_flatMap (M := isa) (UnpackInv b o s0 f) (fun j s hj h => ?_)
    (2 * k) (Nat.le_refl _) s0 ⟨Rest.refl _ _, Frame.refl _ _, fun i hi => by omega⟩)
    fun t ht => ⟨ht.rest, by rw [show 8 * k = 4 * (2 * k) by omega]; exact ht.frame, ht.outs⟩
  have hq' : s.gpr p = q := by rw [h.rest.gpr _ hp, h14]
  refine WP.append (ByteLoad.loadLE32_ok (d := .a4) (tmp := .a5) (n := p) (off := src + 4 * j)
    hp'.1.symm hp'.2.symm (by decide) (by omega)
    (by rw [hq', h.rest.rd, h.rest.wr]; exact hr j hj)) fun t1 e1 => ?_
  have hr1 : Rest [.a4, .a5] s t1 := by
    rw [e1]
    refine ⟨fun r hr' => ?_, rfl, rfl, rfl⟩
    rw [RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').1, RegUpd.gpr_write_of_ne _ _ (not_a4_a5 hr').2]
  have hm1 : t1.mem = s.mem := by rw [e1]; rfl
  have hv : (t1.gpr .a4).toNat % 2 ^ 32 = f j := by
    rw [e1, RegUpd.gpr_write_self, toNat_ext32, Nat.mod_eq_of_lt (BitVec.isLt _), hq']
    show wd s.mem q (src + 4 * j) = _
    refine wd_frame h.frame fun r hr' => ?_
    rw [List.mem_singleton.mp hr']
    refine fun x hx hx' => hd x ?_ ?_
    · exact Offset.sub q (d := src + 4 * j) (n := 4) (e := src) (k := 8 * k) (by omega) (by omega) x hx
    · exact Region.sub_prefix (by omega) x hx'
  refine sw0_ok ((hc.of_rest h.rest (by decide)).of_rest hr1 (by decide))
    (by omega) (by omega) fun u hu => WP.block_nil ?_
  have em : u.mem = s.mem.writeW (b + BitVec.ofNat 64 (o + 4 * j)) ((t1.gpr .a4).setWidth 32) := by
    rw [hu.mem, hm1]
  refine ⟨h.rest.trans (hr1.trans (hu.rest _)), ?_, fun i hi => ?_⟩
  · rw [em]
    refine (h.frame.sub fun r hmem => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (Nat.le_add_right _ _) (by omega) (by omega))
    rw [List.mem_singleton.mp hmem]
    exact Region.sub_prefix (by omega)
  · rw [limb, em]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]
      exact h.outs i hi
    · rw [wd_write_self, toNat_lo32, hv]

/-- `k` doublewords are their `2 k` words. -/
theorem dv_congr_wd {k : Nat} {m m' : Mem} {O O' : Addr} (h : ∀ j < 2 * k, wd m' O' (4 * j) = wd m O (4 * j)) :
    colsV (fun i => dw m' O' (8 * i)) k = colsV (fun i => dw m O (8 * i)) k := by
  have e : ∀ {n}, n ≤ k → colsV (fun i => dw m' O' (8 * i)) n = colsV (fun i => dw m O (8 * i)) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [colsV]
      rw [ih (by omega), dw_split, dw_split, show 8 * n = 4 * (2 * n) by omega,
        show 4 * (2 * n) + 4 = 4 * (2 * n + 1) by omega, h _ (by omega), h _ (by omega)]
  exact e (Nat.le_refl _)

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: the functions

`fn k core` (`Impl/Weierstrass/RISCV64/GenWide.lean`) from a state with the
working space at `W` in `a0` and the offsets' low words in `a1`–`a3`, each
number below the own working space at `8192 - 64 k` (`fn_ok`): `core` on the
pointers if they are multiples of 8, else on byte-wise copies in the own
working space, as P-384's (`Proof/Weierstrass/RISCV64/P384Field/Fn.lean`).
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X25519.RISCV64 (Ctx Rest limb wd wd_shift in_base)
open VG.Proof.X448.RISCV64.R64 (dw al8 colsV)
open VG.Proof.Weierstrass.RISCV64.P256Field (ptr_mod8 aligned_of zext_ok)

theorem off_add (W : Addr) (e o : Nat) :
    W + BitVec.ofNat 64 e + BitVec.ofNat 64 o = W + BitVec.ofNat 64 (e + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- The working space at `W`, `a3 = W + 6144`. -/
structure WsW (W : Addr) (s : State) : Prop where
  al : W.toNat % 8 = 0
  wr : (⟨W, 8192⟩ : Region) ∈ s.wr
  nowrap : W.toNat + 8192 ≤ 2 ^ 64
  a3 : s.gpr .a3 = W + BitVec.ofNat 64 6144

theorem WsW.ctx {W : Addr} {s : State} (h : WsW W s) : Ctx (W + BitVec.ofNat 64 6144) s :=
  ⟨h.a3, by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; have := h.al; omega, fun d n hd => by
    rw [off_add]; exact in_base h.wr (by omega) (by omega)⟩

theorem WsW.bnowrap {W : Addr} {s : State} (h : WsW W s) :
    (W + BitVec.ofNat 64 6144).toNat + 2048 ≤ 2 ^ 64 := by
  have := h.nowrap
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 6144 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega)]
  omega

/-- An offset argument: the low word of its register. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- What the pointers' block leaves, after the zero-extension from `σ`. -/
theorem ptrs_ok {W : Addr} {σ s : State} (hz : VG.Proof.Ed25519.RISCV64.zextF σ s) (h0 : σ.gpr .a0 = W) :
    WP isa (.block ptrs) s fun t =>
      t.gpr .t2 = W + BitVec.ofNat 64 (lo σ .a1) ∧ t.gpr .t4 = W + BitVec.ofNat 64 (lo σ .a2) ∧
      t.gpr .t5 = W + BitVec.ofNat 64 (lo σ .a3) ∧ t.gpr .a3 = W + BitVec.ofNat 64 6144 ∧
      t.gpr .t0 = ((W + BitVec.ofNat 64 (lo σ .a1)) ||| (W + BitVec.ofNat 64 (lo σ .a2)) |||
        (W + BitVec.ofNat 64 (lo σ .a3))) &&& BitVec.ofInt 64 7 ∧
      Rest [.a3, .t0, .t2, .t4, .t5] s t ∧ t.mem = s.mem := by
  obtain ⟨-, e0, ek⟩ := hz
  have e1 := ek .a1 (by simp)
  have e2 := ek .a2 (by simp)
  have e3 := ek .a3 (by simp)
  rw [h0] at e0
  simp only [ptrs]
  refine wp_add fun s7 u7 => wp_add fun s8 u8 => wp_add fun s9 u9 => wp_addi (by decide) fun s10 u10 =>
    wp_addi (by decide) fun s11 u11 => wp_addi (by decide) fun s12 u12 => wp_addi (by decide) fun s13 u13 =>
    wp_or fun s14 u14 => wp_or fun s15 u15 =>
    wp_andi (by decide) fun s16 u16 => WP.block_nil ?_
  have p2 : s9.gpr .t2 = W + BitVec.ofNat 64 (lo σ .a1) := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr, e0, e1]
  have p4 : s9.gpr .t4 = W + BitVec.ofNat 64 (lo σ .a2) := by
    rw [u9.other _ (by decide), u8.gpr, u7.other _ (by decide), u7.other .a2 (by decide), e0, e2]
  have p5 : s9.gpr .t5 = W + BitVec.ofNat 64 (lo σ .a3) := by
    rw [u9.gpr, u8.other _ (by decide), u8.other .a3 (by decide), u7.other _ (by decide),
      u7.other .a3 (by decide), e0, e3]
  have g16 : ∀ r, r ≠ .t0 → r ≠ .a3 → s16.gpr r = s9.gpr r := fun r h0 h3 => by
    rw [u16.other _ h0, u15.other _ h0, u14.other _ h0, u13.other _ h3, u12.other _ h3, u11.other _ h3,
      u10.other _ h3]
  refine ⟨by rw [g16 _ (by decide) (by decide), p2], by rw [g16 _ (by decide) (by decide), p4],
    by rw [g16 _ (by decide) (by decide), p5], ?_, ?_, ?_, ?_⟩
  · rw [u16.other _ (by decide), u15.other _ (by decide), u14.other _ (by decide), u13.gpr, u12.gpr, u11.gpr,
      u10.gpr, u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), e0, BitVec.add_assoc,
      BitVec.add_assoc, BitVec.add_assoc]
    rfl
  · rw [u16.gpr, u15.gpr, u14.gpr, u14.other .t5 (by decide)]
    rw [u13.other .t2 (by decide), u13.other .t4 (by decide), u13.other .t5 (by decide),
      u12.other .t2 (by decide), u12.other .t4 (by decide), u12.other .t5 (by decide),
      u11.other .t2 (by decide), u11.other .t4 (by decide), u11.other .t5 (by decide), u10.other .t2 (by decide),
      u10.other .t4 (by decide), u10.other .t5 (by decide), p2, p4, p5]
  · exact (u7.rest (by decide)).trans ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans
      ((u10.rest (by decide)).trans ((u11.rest (by decide)).trans ((u12.rest (by decide)).trans
      ((u13.rest (by decide)).trans ((u14.rest (by decide)).trans ((u15.rest (by decide)).trans
      (u16.rest (by decide))))))))))
  · rw [u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]

/-! ## The operations as specifications -/

/-- What an operation on the pointers `t4`, `t5` and `t2` does, for operands
satisfying `pre`: its result `res`, written at `[t2]`. -/
def CoreSpec (k : Nat) (core : List Instr) (pre : Nat → Nat → Prop) (res : Nat → Nat → Nat → Prop) : Prop :=
  ∀ {b A B O : Addr} {s : State}, CoreOk k b A B O s → pre (xv s.mem A k) (xv s.mem B k) →
    WP isa (.block core) s fun s' => res (xv s.mem A k) (xv s.mem B k) (ov s'.mem O k) ∧
      Frame [ownR k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem mulCore_spec {k m : Nat} (hm : m < 2 ^ (64 * k))
    (hinv : (wordOf m 0).toNat * negInv m % 2 ^ 64 = 2 ^ 64 - 1) :
    CoreSpec k (mulCore k m) (fun _ B => B < m) (fun A B r => r < m ∧ r * 2 ^ (64 * k) % m = A * B % m) :=
  fun hC hB => WP.mono (mulCore_ok hC hm hinv hB) fun _ ⟨g, rd, wr, sp, f, v1, v2⟩ => ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_spec {k m : Nat} (hm : m < 2 ^ (64 * k)) :
    CoreSpec k (addCore k m) (fun A B => A + B < 2 * m) (fun A B r => r = (A + B) % m) :=
  fun hC hAB => WP.mono (addCore_ok hC hm hAB) fun _ ⟨g, rd, wr, sp, f, v⟩ => ⟨v, f, g, rd, wr, sp⟩

theorem subCore_spec {k m : Nat} (hm : m < 2 ^ (64 * k)) :
    CoreSpec k (subCore k m) (fun A B => A < m ∧ B < m) (fun A B r => r = (A + m - B) % m) :=
  fun hC hAB => WP.mono (subCore_ok hC hm hAB.1 hAB.2) fun _ ⟨g, rd, wr, sp, f, v⟩ => ⟨v, f, g, rd, wr, sp⟩

/-- The whole own working space. -/
abbrev ownA (k : Nat) (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (T k), 64 * k⟩

/-- What an operation on the pointers does for operands and a result apart
from the whole own working space: as `CoreSpec`, writing any of it. -/
def FastSpec (k : Nat) (fast : Prog isa) (pre : Nat → Nat → Prop) (res : Nat → Nat → Nat → Prop) : Prop :=
  ∀ {b A B O : Addr} {s : State}, CoreOk k b A B O s →
    (∀ i < k, Region.Disjoint ⟨A + BitVec.ofNat 64 (8 * i), 8⟩ (ownA k b)) →
    (∀ i < k, Region.Disjoint ⟨B + BitVec.ofNat 64 (8 * i), 8⟩ (ownA k b)) →
    Region.Disjoint ⟨O, 8 * k⟩ (ownA k b) → pre (xv s.mem A k) (xv s.mem B k) →
    WP isa fast s fun s' => res (xv s.mem A k) (xv s.mem B k) (ov s'.mem O k) ∧
      Frame [ownA k b, ⟨O, 8 * k⟩] s.mem s'.mem ∧ (∀ r, r ∉ clobW → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

theorem ownR_sub (k : Nat) (h₁ : 1 ≤ k) (b : Addr) {O : Addr} :
    ∀ r ∈ [ownR k b, ⟨O, 8 * k⟩], ∃ r' ∈ [ownA k b, ⟨O, 8 * k⟩], Region.Sub r r' := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub b (Nat.le_refl _) (by omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

/-- An operation on the pointers as a fast path. -/
theorem CoreSpec.fast {k : Nat} {core : List Instr} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (h : CoreSpec k core pre res) : FastSpec k (.block core) pre res :=
  fun hC _ _ _ hp => WP.mono (h hC hp) fun _ ⟨v, f, g, rd, wr, sp⟩ =>
    ⟨v, f.sub (ownR_sub k (by have := hC.k7; omega) _), g, rd, wr, sp⟩

/-! ## The byte-wise copies -/

theorem layout_facts (k : Nat) (h₁ : 1 ≤ k) (h : k ≤ 30) :
    6144 + T k = 8192 - 64 * k ∧ SA k = N k + 8 * k ∧ SB k = SA k + 8 * k ∧ SO k = SB k + 8 * k ∧
      SO k + 8 * k ≤ 2048 ∧ N k + 8 * k = T k + 8 * (2 * k + 2) := by
  unfold SO SB SA N T; omega

/-- The `k` doublewords at `b + o` are the words that `unpack` or `pack` copied. -/
theorem xv_of_limbs {k : Nat} {m m' : Mem} {b P : Addr} {o : Nat}
    (h : ∀ i < 2 * k, limb m' b o i = wd m P (0 + 4 * i)) : xv m' (b + BitVec.ofNat 64 o) k = xv m P k :=
  dv_congr_wd fun j hj => by rw [wd_shift, ← limb, h j hj, Nat.zero_add]

theorem xv_of_wds {k : Nat} {m m' : Mem} {b P : Addr} {o : Nat}
    (h : ∀ i < 2 * k, wd m' P (0 + 4 * i) = limb m b o i) : xv m' P k = xv m (b + BitVec.ofNat 64 o) k :=
  dv_congr_wd fun j hj => by rw [← Nat.zero_add (4 * j), h j hj, limb, wd_shift, Nat.zero_add]

theorem dw_frame1 {m m' : Mem} {R : Region} (hf : Frame [R] m m') {P : Addr} {d : Nat}
    (hd : Region.Disjoint ⟨P + BitVec.ofNat 64 d, 8⟩ R) : dw m' P d = dw m P d :=
  VG.Proof.X448.RISCV64.R64.dw_frame hf fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd

/-- The `k` doublewords at `W + x` through a frame of a region `W + e` apart from them. -/
theorem xv_frame {k : Nat} {m m' : Mem} {W : Addr} {x e n : Nat} (hf : Frame [⟨W + BitVec.ofNat 64 e, n⟩] m m')
    (hd : x + 8 * k ≤ e ∨ e + n ≤ x) (hx : x + 8 * k ≤ 2 ^ 64) (he : e + n ≤ 2 ^ 64) :
    xv m' (W + BitVec.ofNat 64 x) k = xv m (W + BitVec.ofNat 64 x) k :=
  colsV_congr fun i hi => dw_frame1 hf (by rw [off_add]; exact Offset.disjoint W (by omega) (by omega) he)

/-- The slow branch's copies in, and its pointers. -/
theorem slowIn_ok {k : Nat} {W : Addr} {s : State} (hw : WsW W s) (hk : 7 ≤ k) (hk' : k ≤ 30) {a bb o : Nat}
    (h4 : s.gpr .t4 = W + BitVec.ofNat 64 a) (h5 : s.gpr .t5 = W + BitVec.ofNat 64 bb)
    (h2 : s.gpr .t2 = W + BitVec.ofNat 64 o) (ha : a + 8 * k ≤ 8192 - 64 * k) (hb : bb + 8 * k ≤ 8192 - 64 * k) :
    WP isa (.block (([.addi .t1 .t2 0] : List Instr) ++ unpack k .t4 (SA k) 0 ++
        unpack k .t5 (SB k) 0 ++ ([.addi .t4 .a3 (SA k), .addi .t5 .a3 (SB k), .addi .t2 .a3 (SO k)] : List Instr))) s
      fun t => WsW W t ∧ t.gpr .t1 = W + BitVec.ofNat 64 o ∧
        t.gpr .t4 = W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k) ∧
        t.gpr .t5 = W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k) ∧
        t.gpr .t2 = W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SO k) ∧
        xv t.mem (W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k)) k = xv s.mem (W + BitVec.ofNat 64 a) k ∧
        xv t.mem (W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k)) k = xv s.mem (W + BitVec.ofNat 64 bb) k ∧
        Frame [⟨W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k), 8 * k⟩,
          ⟨W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k), 8 * k⟩] s.mem t.mem ∧
        Rest [.t1, .t2, .t4, .t5, .a4, .a5] s t := by
  obtain ⟨e6, eA, eB, eO, otop, -⟩ := layout_facts k (by omega) hk'
  obtain ⟨hNT, -, -⟩ := N_facts k (by omega) hk'
  obtain ⟨t8, -⟩ := T_facts k (by omega) hk'
  have hnw := hw.nowrap
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mv fun s1 u1 => ?_
  have hw1 : WsW W s1 := ⟨hw.al, by rw [u1.wr]; exact hw.wr, hnw, by rw [u1.other _ (by decide), hw.a3]⟩
  refine WP.block_append (WP.mono (unpack_ok (k := k) hw1.ctx (p := .t4) (q := W + BitVec.ofNat 64 a) (by decide)
    (by rw [u1.other _ (by decide), h4]) (o := SA k) (src := 0) (by omega) (by unfold SA N T; omega) (by omega)
    (fun j hj => by
      rw [Nat.zero_add, off_add]
      obtain ⟨r, hr, hc⟩ := in_base (n := 4) hw1.wr (d := a + 4 * j) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [off_add, Nat.add_zero, off_add]; exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)))
    fun s2 ⟨r2, f2, v2⟩ => ?_)
  have hw2 : WsW W s2 := ⟨hw.al, by rw [r2.wr]; exact hw1.wr, hnw, by rw [r2.gpr _ (by decide), hw1.a3]⟩
  refine WP.block_append (WP.mono (unpack_ok (k := k) hw2.ctx (p := .t5) (q := W + BitVec.ofNat 64 bb) (by decide)
    (by rw [r2.gpr _ (by decide), u1.other _ (by decide), h5]) (o := SB k) (src := 0) (by omega)
    (by unfold SB SA N T; omega) (by omega)
    (fun j hj => by
      rw [Nat.zero_add, off_add]
      obtain ⟨r, hr, hc⟩ := in_base (n := 4) hw2.wr (d := bb + 4 * j) (by omega) (by omega)
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [off_add, Nat.add_zero, off_add]; exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)))
    fun s3 ⟨r3, f3, v3⟩ => ?_)
  have hw3 : WsW W s3 := ⟨hw.al, by rw [r3.wr]; exact hw2.wr, hnw, by rw [r3.gpr _ (by decide), hw2.a3]⟩
  refine wp_addi (by omega) fun s4 u4 => wp_addi (by omega) fun s5 u5 => wp_addi (by omega) fun s6 u6 =>
    WP.block_nil ?_
  have r6 : Rest [.t1, .t2, .t4, .t5, .a4, .a5] s s6 :=
    (u1.rest (by decide)).trans ((r2.mono (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  have m6 : s6.mem = s3.mem := by rw [u6.mem, u5.mem, u4.mem]
  have sep : Region.Disjoint ⟨W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k), 8 * k⟩
      ⟨W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k), 8 * k⟩ := by
    rw [off_add, off_add]; exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)
  refine ⟨⟨hw.al, by rw [r6.wr]; exact hw.wr, hnw, by rw [r6.gpr _ (by decide), hw.a3]⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, r6⟩
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), r3.gpr _ (by decide),
      r2.gpr _ (by decide), u1.gpr, h2]
  · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, hw3.a3]
  · rw [u6.other _ (by decide), u5.gpr, u4.other _ (by decide), hw3.a3]
  · rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), hw3.a3]
  · rw [m6, off_add, xv_frame (k := k) (by rw [off_add] at f3; exact f3) (by omega) (by omega) (by omega),
      ← off_add, xv_of_limbs (k := k) v2, u1.mem]
  · rw [m6, xv_of_limbs (k := k) v3,
      xv_frame (k := k) (by rw [off_add] at f2; exact f2) (by omega) (by omega) (by omega), u1.mem]
  · rw [m6, ← u1.mem]
    exact (f2.mono (by simp)).trans (f3.mono (by simp))

/-- The slow branch's copy out: `[o]` from `SO`. -/
theorem slowOut_ok {k : Nat} {W : Addr} {s : State} (hw : WsW W s) (hk : 7 ≤ k) (hk' : k ≤ 30) {o : Nat}
    (h1 : s.gpr .t1 = W + BitVec.ofNat 64 o) (ho : o + 8 * k ≤ 8192 - 64 * k) :
    WP isa (.block (pack k .t1 (SO k) 0)) s fun t =>
      Rest [.a4, .a5] s t ∧ Frame [⟨W + BitVec.ofNat 64 o, 8 * k⟩] s.mem t.mem ∧
      xv t.mem (W + BitVec.ofNat 64 o) k = xv s.mem (W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SO k)) k := by
  obtain ⟨e6, eA, eB, eO, otop, -⟩ := layout_facts k (by omega) hk'
  obtain ⟨hNT, -, -⟩ := N_facts k (by omega) hk'
  have hnw := hw.nowrap
  refine WP.mono (pack_ok (k := k) hw.ctx (p := .t1) (q := W + BitVec.ofNat 64 o) (by decide) h1 (a := SO k)
    (dst := 0) (by omega) (by unfold SO SB SA N T; omega) (by omega) (fun j hj => by
      rw [Nat.zero_add, off_add]
      exact in_base (n := 4) hw.wr (by omega) (by omega))
    (by
      rw [off_add, Nat.add_zero, off_add]
      exact Offset.disjoint W (.inl (by omega)) (by omega) (by omega)))
    fun t ht => ⟨ht.rest, ?_, xv_of_wds (k := k) ht.outs⟩
  have f := ht.frame
  rw [off_add, Nat.add_zero, show 4 * (2 * k) = 8 * k by omega] at f
  exact f

/-! ## The functions -/

/-- The registers the functions write. -/
abbrev clobF : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The regions the functions write: their own working space and the result. -/
abbrev fnW (k : Nat) (W : Addr) (o : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 (8192 - 64 * k), 64 * k⟩, ⟨W + BitVec.ofNat 64 o, 8 * k⟩]

theorem fnW_sub (k : Nat) (hk : 1 ≤ k) (hk' : k ≤ 30) (W : Addr) (o : Nat) {d n : Nat} (hd : 8192 - 64 * k ≤ d)
    (hn : d + n ≤ 8192) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, n⟩ : Region)], ∃ r' ∈ fnW k W o, Region.Sub r r' := fun r hr => by
  rw [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self .., Offset.sub W hd (by omega)⟩

theorem core_fnW {k : Nat} (hk : 1 ≤ k) (hk' : k ≤ 30) (W : Addr) {o : Nat} (O : Addr)
    (hO : O = W + BitVec.ofNat 64 o ∨ ∃ e, 8192 - 64 * k ≤ e ∧ e + 8 * k ≤ 8192 ∧ O = W + BitVec.ofNat 64 e) :
    ∀ r ∈ [ownR k (W + BitVec.ofNat 64 6144), ⟨O, 8 * k⟩], ∃ r' ∈ fnW k W o, Region.Sub r r' := fun r hr => by
  obtain ⟨e6, -, -, -, -, onk⟩ := layout_facts k hk hk'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨_, List.mem_cons_self .., ?_⟩
    rw [ownR, off_add]
    exact Offset.sub W (by omega) (by unfold T at *; omega)
  · rcases hO with rfl | ⟨e, he, he', rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W he (by omega)⟩

/-- The fast path's regions within the function's. -/
theorem fast_fnW {k : Nat} (hk : 1 ≤ k) (hk' : k ≤ 30) (W : Addr) (o : Nat) :
    ∀ r ∈ [ownA k (W + BitVec.ofNat 64 6144), ⟨W + BitVec.ofNat 64 o, 8 * k⟩], ∃ r' ∈ fnW k W o,
      Region.Sub r r' := fun r hr => by
  obtain ⟨e6, -, -, -, -, -⟩ := layout_facts k hk hk'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨_, List.mem_cons_self .., ?_⟩
    rw [ownA, off_add]
    exact Offset.sub W (by omega) (by unfold T at *; omega)
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

/-- `fnWith k fast core`, from the working space at `W` and offsets below the own working space. -/
theorem fnWith_ok {k : Nat} (hk : 7 ≤ k) (hk' : k ≤ 30) {fast : Prog isa} {core : List Instr}
    {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop} (hfast : FastSpec k fast pre res)
    (hcore : CoreSpec k core pre res) {W : Addr} {s : State}
    (h0 : s.gpr .a0 = W) (hal : W.toNat % 8 = 0)
    (hwr : (⟨W, 8192⟩ : Region) ∈ s.wr) (hfit : W.toNat + 8192 ≤ 2 ^ 64)
    (ho : lo s .a1 + 8 * k ≤ 8192 - 64 * k) (ha : lo s .a2 + 8 * k ≤ 8192 - 64 * k)
    (hb : lo s .a3 + 8 * k ≤ 8192 - 64 * k)
    (hpre : pre (xv s.mem (W + BitVec.ofNat 64 (lo s .a2)) k) (xv s.mem (W + BitVec.ofNat 64 (lo s .a3)) k)) :
    WP isa (fnWith k fast core) s fun s' =>
      res (xv s.mem (W + BitVec.ofNat 64 (lo s .a2)) k) (xv s.mem (W + BitVec.ofNat 64 (lo s .a3)) k)
        (xv s'.mem (W + BitVec.ofNat 64 (lo s .a1)) k) ∧
      Frame (fnW k W (lo s .a1)) s.mem s'.mem ∧ (∀ r, r ∉ clobF → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨e6, eA, eB, eO, otop, onk⟩ := layout_facts k (by omega) hk'
  obtain ⟨hNT, -, -⟩ := N_facts k (by omega) hk'
  obtain ⟨t8, -⟩ := T_facts k (by omega) hk'
  unfold fnWith
  refine WP.seq (WP.mono (zext_ok s) fun s0 ⟨z0, r0, m0⟩ => ?_)
  refine WP.seq (WP.mono (ptrs_ok z0 h0) fun s1 ⟨p2, p4, p5, p3, p0, r1', m1'⟩ => ?_)
  have r1 : Rest [.a1, .a2, .a3, .t0, .t2, .t4, .t5] s s1 := (r0.mono (by decide)).trans (r1'.mono (by decide))
  have m1 : s1.mem = s.mem := by rw [m1', m0]
  have hw1 : WsW W s1 := ⟨hal, by rw [r1.wr]; exact hwr, hfit, p3⟩
  have sub1 : ∀ x ∈ [Reg.a1, .a2, .a3, .t0, .t2, .t4, .t5], x ∈ clobF := by decide
  have subW : ∀ x ∈ clobW, x ∈ clobF := by decide
  have hlt : ∀ x, x + 8 * k ≤ 8192 - 64 * k → (W + BitVec.ofNat 64 x).toNat = W.toNat + x := fun x hx => by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  -- Words at `W + x` are apart from the own working space.
  have wdis : ∀ x, x + 8 * k ≤ 8192 - 64 * k → ∀ i < k,
      Region.Disjoint ⟨W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * i), 8⟩ (ownR k (W + BitVec.ofNat 64 6144)) :=
    fun x hx i hi => by
      rw [ownR, off_add, off_add]; exact Offset.disjoint W (.inl (by unfold T at *; omega)) (by omega) (by omega)
  refine WP.ite (s1.gpr .t0 == 0) rfl (fun hz => ?_) (fun _ => ?_)
  · -- The offsets are multiples of 8.
    rw [p0] at hz
    obtain ⟨al1, al2, al3⟩ := aligned_of (beq_iff_eq.mp hz)
    have hC : CoreOk k (W + BitVec.ofNat 64 6144) (W + BitVec.ofNat 64 (lo s .a2)) (W + BitVec.ofNat 64 (lo s .a3))
        (W + BitVec.ofNat 64 (lo s .a1)) s1 :=
      { ctx := hw1.ctx
        nowrap := hw1.bnowrap
        a := p4
        b' := p5
        o := p2
        aal := al2
        bal := al3
        oal := al1
        ain := fun i hi => by
          rw [off_add]
          obtain ⟨r, hr, hc⟩ := in_base (n := 8) hw1.wr (d := lo s .a2 + 8 * i) (by omega) (by omega)
          exact ⟨r, List.mem_append_right _ hr, hc⟩
        bin := fun i hi => by
          rw [off_add]
          obtain ⟨r, hr, hc⟩ := in_base (n := 8) hw1.wr (d := lo s .a3 + 8 * i) (by omega) (by omega)
          exact ⟨r, List.mem_append_right _ hr, hc⟩
        ow := fun i hi => by rw [off_add]; exact in_base (n := 8) hw1.wr (by omega) (by omega)
        onw := by rw [hlt _ ho]; omega
        adis := wdis _ ha
        bdis := wdis _ hb
        odis := by
          rw [ownR, off_add]; exact Offset.disjoint W (.inl (by unfold T at *; omega)) (by omega) (by omega)
        k7 := hk
        k30 := hk' }
    have adis : ∀ x, x + 8 * k ≤ 8192 - 64 * k → ∀ i < k,
        Region.Disjoint ⟨W + BitVec.ofNat 64 x + BitVec.ofNat 64 (8 * i), 8⟩ (ownA k (W + BitVec.ofNat 64 6144)) :=
      fun x hx i hi => by
        rw [ownA, off_add, off_add]; exact Offset.disjoint W (.inl (by unfold T at *; omega)) (by omega) (by omega)
    have odis : Region.Disjoint ⟨W + BitVec.ofNat 64 (lo s .a1), 8 * k⟩ (ownA k (W + BitVec.ofNat 64 6144)) := by
      rw [ownA, off_add]; exact Offset.disjoint W (.inl (by unfold T at *; omega)) (by omega) (by omega)
    refine WP.mono (hfast hC (adis _ ha) (adis _ hb) odis (by rw [m1]; exact hpre))
      fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ⟨by rw [← m1]; exact v2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m1]; exact f2.sub (fast_fnW (by omega) hk' W _)
    · intro r hr
      rw [g2 r (fun h => hr (subW r h)), r1.gpr r (fun h => hr (sub1 r h))]
    · rw [rd2, r1.rd]
    · rw [wr2, r1.wr]
    · rw [sp2, r1.sp]
  · -- The byte-wise copies.
    refine WP.seq (WP.mono (slowIn_ok hw1 hk hk' p4 p5 p2 ha hb) fun s2 ⟨hw2, q1, q4, q5, q2, v4, v5, f2, r2⟩ => ?_)
    have bw := hw2.ctx
    have hC : CoreOk k (W + BitVec.ofNat 64 6144) (W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SA k))
        (W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SB k)) (W + BitVec.ofNat 64 6144 + BitVec.ofNat 64 (SO k)) s2 :=
      { ctx := bw
        nowrap := hw2.bnowrap
        a := q4
        b' := q5
        o := q2
        aal := al8 bw.al (by unfold SA N T; omega)
        bal := al8 bw.al (by unfold SB SA N T; omega)
        oal := al8 bw.al (by unfold SO SB SA N T; omega)
        ain := fun i hi => by rw [off_add (W + _)]; exact bw.inR (by omega)
        bin := fun i hi => by rw [off_add (W + _)]; exact bw.inR (by omega)
        ow := fun i hi => by rw [off_add (W + _)]; exact bw.inW (by omega)
        onw := by
          have := hw2.bnowrap
          rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : SO k < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega)]
          omega
        adis := fun i hi => by
          rw [off_add (W + _), ownR]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
        bdis := fun i hi => by
          rw [off_add (W + _), ownR]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
        odis := by rw [ownR]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
        k7 := hk
        k30 := hk' }
    refine WP.seq (WP.mono (hcore hC (by rw [v4, v5, m1]; exact hpre)) fun s3 ⟨v3, f3, g3, rd3, wr3, sp3⟩ => ?_)
    have hw3 : WsW W s3 := ⟨hal, by rw [wr3]; exact hw2.wr, hfit, by rw [g3 _ (by decide), hw2.a3]⟩
    refine WP.mono (slowOut_ok hw3 hk hk' (by rw [g3 _ (by decide), q1]) ho) fun s4 ⟨r4, f4, v4'⟩ =>
      ⟨by rw [v4']; rw [v4, v5, m1] at v3; exact v3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m1]
      refine (f2.sub fun r hr => ?_).trans ((f3.sub (core_fnW (by omega) hk' W _ (.inr ⟨6144 + SO k, by omega,
        by omega, by rw [off_add]⟩))).trans (f4.sub fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., by rw [off_add]; exact Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., by rw [off_add]; exact Offset.sub W (by omega) (by omega)⟩
      · rw [List.mem_singleton.mp hr]
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · intro r hr
      have s2' : ∀ x ∈ [Reg.t1, .t2, .t4, .t5, .a4, .a5], x ∈ clobF := by decide
      have s4' : ∀ x ∈ [Reg.a4, .a5], x ∈ clobF := by decide
      rw [r4.gpr r (fun h => hr (s4' r h)), g3 r (fun h => hr (subW r h)), r2.gpr r (fun h => hr (s2' r h)),
        r1.gpr r (fun h => hr (sub1 r h))]
    · rw [r4.rd, rd3, r2.rd, r1.rd]
    · rw [r4.wr, wr3, r2.wr, r1.wr]
    · rw [r4.sp, sp3, r2.sp, r1.sp]


/-- `fn k core`, from the working space at `W` and offsets below the own working space. -/
theorem fn_ok {k : Nat} (hk : 7 ≤ k) (hk' : k ≤ 30) {core : List Instr} {pre : Nat → Nat → Prop}
    {res : Nat → Nat → Nat → Prop} (hcore : CoreSpec k core pre res) {W : Addr} {s : State}
    (h0 : s.gpr .a0 = W) (hal : W.toNat % 8 = 0)
    (hwr : (⟨W, 8192⟩ : Region) ∈ s.wr) (hfit : W.toNat + 8192 ≤ 2 ^ 64)
    (ho : lo s .a1 + 8 * k ≤ 8192 - 64 * k) (ha : lo s .a2 + 8 * k ≤ 8192 - 64 * k)
    (hb : lo s .a3 + 8 * k ≤ 8192 - 64 * k)
    (hpre : pre (xv s.mem (W + BitVec.ofNat 64 (lo s .a2)) k) (xv s.mem (W + BitVec.ofNat 64 (lo s .a3)) k)) :
    WP isa (fn k core) s fun s' =>
      res (xv s.mem (W + BitVec.ofNat 64 (lo s .a2)) k) (xv s.mem (W + BitVec.ofNat 64 (lo s .a3)) k)
        (xv s'.mem (W + BitVec.ofNat 64 (lo s .a1)) k) ∧
      Frame (fnW k W (lo s .a1)) s.mem s'.mem ∧ (∀ r, r ∉ clobF → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  fnWith_ok hk hk' hcore.fast hcore h0 hal hwr hfit ho ha hb hpre

end VG.Proof.Weierstrass.RISCV64.GenWide

/-!
## Arithmetic modulo a wide modulus on RISC-V: the contracts by register

For a modulus `S` of `k ≥ 7` words, `mulFn k m`, `addFn k m` and `subFn k m`
(`Impl/Weierstrass/RISCV64/GenWide.lean`) meet the contracts by register of
`Proof/Weierstrass/RISCV64/FieldRV.lean` (`mul_rv`, `add_rv`, `sub_rv`), from
`fn_ok`: `numAt` of an offset is the `k` doublewords there (`numAt_xv`), and
the regions the functions write, the top `64 k` bytes of the working space
(`rvOwn k`) and the result, keep every other byte (`keeps_of_frame`).
-/


namespace VG.Proof.Weierstrass.RISCV64.GenWide

open VG VG.RISCV64 VG.Impl.Weierstrass.RISCV64.GenWide
open VG.Proof.X448.RISCV64.R64 (dw colsV)
open VG.Impl.Weierstrass.Mont (numAt Keeps Modulus Fits)
open VG.Proof.Weierstrass.RISCV64 (offArg rvPre arg res rvPub mulRV addRV subRV rvOwn rvOwnEnd)

theorem wordsVal_colsV (m : Mem) (P : Addr) : ∀ (k d : Nat),
    VG.Proof.Mont.wordsVal m P d k = colsV (fun i => dw m P (d + 8 * i)) k
  | 0, _ => rfl
  | k + 1, d => by
    rw [VG.Proof.Mont.wordsVal, wordsVal_colsV m P k (d + 8), colsV_shift]
    simp only [Nat.mul_zero, Nat.add_zero, show ∀ i, d + 8 + 8 * i = d + 8 * (i + 1) from fun i => by omega]
    rfl

theorem numAt_xv (m : Mem) (W : Addr) (o : BitVec 32) (k : Nat) :
    numAt m W o k = xv m (W + BitVec.ofNat 64 o.toNat) k := by
  have h := VG.Proof.Mont.read_eq_wordsVal m (W + BitVec.ofNat 64 o.toNat) k 0
  simp only [VG.Proof.Mont.off, BitVec.add_zero] at h
  rw [numAt, h, wordsVal_colsV]
  simp only [Nat.zero_add]

theorem rvOwn_gt {k : Nat} (h : 6 < k) : rvOwn k = 8192 - 64 * k := by
  simp [rvOwn, show ¬ k ≤ 6 by omega, Impl.Weierstrass.Mont.wsBytes, Impl.Weierstrass.Mont.ownBytes]

theorem rvOwnEnd_gt {k : Nat} (h : 6 < k) : rvOwnEnd k = 8192 := by
  simp [rvOwnEnd, show ¬ k ≤ 6 by omega, Impl.Weierstrass.Mont.wsBytes]

/-- A byte of the working space outside a range of it. -/
theorem byte_out {W : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Contains (W + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint W (d := i) (n := 1) (e := e) (k := k) (by omega) (by omega) (by omega) _
    (Region.contains_self _ _) hc

/-- The regions the functions write keep every byte the contracts do. -/
theorem keeps_of_frame {k : Nat} (hk : 6 < k) (hk' : k ≤ 30) {W : Addr} {o : BitVec 32}
    (ho : o.toNat + 8 * k ≤ 8192 - 64 * k) {m m' : Mem} (hf : Frame (fnW k W o.toNat) m m') :
    Keeps k W o m m' (rvOwn k) (rvOwnEnd k) := by
  intro i hi hown hoi
  rw [rvOwn_gt hk, rvOwnEnd_gt hk] at hown
  simp only [Impl.Weierstrass.Mont.wsBytes] at hi
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact byte_out (by omega) (by omega) (by omega)
  · exact byte_out (by omega) (by omega) hoi

/-- `fn k core` meets a contract by register, from `fn_ok`. -/
theorem fn_rv {S : Modulus} (hk : 7 ≤ S.k) (hk' : S.k ≤ 30) {core : List Instr} {pre : Nat → Nat → Prop}
    {res : Nat → Nat → Nat → Prop} (hcore : CoreSpec S.k core pre res) {s : State} (hs : rvPre S s)
    (hp : pre (arg S s .a2) (arg S s .a3)) :
    ∃ t s', Exec isa (fn S.k core) s t s' ∧ abiPreserved s s' ∧
      res (arg S s .a2) (arg S s .a3) (numAt s'.mem (s.gpr .a0) (offArg s .a1) S.k) ∧
      Keeps S.k (s.gpr .a0) (offArg s .a1) s.mem s'.mem (rvOwn S.k) (rvOwnEnd S.k) := by
  obtain ⟨-, hwr, hfit, ⟨fo, fa, fb⟩, hal⟩ := hs
  simp only [Fits, rvOwn_gt (show 6 < S.k by omega)] at fo fa fb
  simp only [arg, numAt_xv] at hp ⊢
  obtain ⟨t, s', he, v, f, g, -, -, sp⟩ := fn_ok hk hk' hcore rfl hal (by rw [hwr]; simp) hfit fo fa fb hp
  refine ⟨t, s', he, ⟨fun r hr => g r (by revert hr; revert r; decide), sp, g _ (by decide)⟩, v,
    keeps_of_frame (by omega) hk' fo f⟩

/-- What a wide modulus needs: its words, and `m'`. -/
structure WideOk (S : Modulus) : Prop where
  k7 : 7 ≤ S.k
  k30 : S.k ≤ 30
  lt : S.m < 2 ^ (64 * S.k)
  inv : (wordOf S.m 0).toNat * negInv S.m % 2 ^ 64 = 2 ^ 64 - 1

theorem mul_rv {S : Modulus} (hS : WideOk S) (s : State) (hs : (mulRV S).pre s) :
    ∃ t s', Exec isa (mulFn S.k S.m) s t s' ∧ abiPreserved s s' ∧ (mulRV S).post s s' := by
  obtain ⟨t, s', he, a, ⟨v1, v2⟩, k⟩ := fn_rv hS.k7 hS.k30 (@mulCore_spec S.k S.m hS.lt hS.inv) hs.1 hs.2
  exact ⟨t, s', he, a, v1, v2, k⟩

theorem add_rv {S : Modulus} (hS : WideOk S) (s : State) (hs : (addRV S).pre s) :
    ∃ t s', Exec isa (addFn S.k S.m) s t s' ∧ abiPreserved s s' ∧ (addRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hS.k7 hS.k30 (@addCore_spec S.k S.m hS.lt) hs.1 hs.2
  exact ⟨t, s', he, a, v, k⟩

theorem sub_rv {S : Modulus} (hS : WideOk S) (s : State) (hs : (subRV S).pre s) :
    ∃ t s', Exec isa (subFn S.k S.m) s t s' ∧ abiPreserved s s' ∧ (subRV S).post s s' := by
  obtain ⟨t, s', he, a, v, k⟩ := fn_rv hS.k7 hS.k30 (@subCore_spec S.k S.m hS.lt) hs.1 hs.2
  exact ⟨t, s', he, a, v, k⟩

end VG.Proof.Weierstrass.RISCV64.GenWide
