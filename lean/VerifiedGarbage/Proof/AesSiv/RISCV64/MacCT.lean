module

import VerifiedGarbage.Proof.AesSiv.RISCV64.Rel
import VerifiedGarbage.Proof.AesSiv.RISCV64.Long
import VerifiedGarbage.Proof.AesSiv.RISCV64.Short
import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Rel
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Long
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.Short
meta import VerifiedGarbage.Proof.AesSiv.RISCV64.CtrLoop
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.AesSiv.Long
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
public import VerifiedGarbage.Proof.AesSiv.RISCV64.S2v
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps

/-!
# AES-SIV on RISC-V: S2V in two runs

Untrusted: everything here is checked by Lean. Each piece of S2V, run from
two states satisfying its correctness proof's hypotheses in the same
environment, leaks the same: the code between calls by the taint analysis
(`rel_env`), from the environment's registers and those on which the two
runs agree (the descriptor pointer and count `s4` and `s5`, the string's
address and length `s6` and `s7`, and what the code derives from the
length, `s8` and `s0`), and each call of `vg_cmac_aes_update` and
`vg_cmac_aes_finalize` by its proof (`rel_upd`, `rel_fin`), from the
arguments the correctness proofs give it. The loop over the components of
associated data relates two runs after the same number of components
(`AInv`), whose descriptors are public. As on PPC64LE
(`Proof/AesSiv/PPC64LE/MacCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Proof.CmacAes.Stream.RISCV64 (UArgs upd_call FArgs)
open VG.Proof.AesCcm.RISCV64 (Runs Runs.of_wp rel_seqR rel_of_eq2 rel_post)
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Spec.Aes (bytesAt)

/-! ## What the pieces set before the calls -/

/-- `cmacArgs₁`: the arguments of the update over the whole blocks. -/
theorem cmacArgs₁_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {st : Nat} (hst : st + 16 ≤ 384)
    {P : Addr} {n : Nat} (hP : Buf c s P n) (h19 : s.gpr .s6 = P)
    (h21 : s.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) :
    WP isa (.block (cmacArgs₁ st)) s fun s₂ => MacKeep s s₂ ∧ s₂.gpr .s8 = s.gpr .s8 ∧
      UArgs s₂ c.C (c.W + BitVec.ofNat 64 st) P (c.W + BitVec.ofNat 64 384) c.R (Spec.Cmac.chainedLen 16 n / 16) := by
  have hn := hP.lt
  have hcl := chainedLen_le n
  have hcd := chainedLen_div n
  unfold cmacArgs₁ macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_mv fun t₅ v₅ => wp_srl (by decide) fun t₆ v₆ =>
    WP.block_nil ?_
  have K : MacKeep s t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  have E₆ := E.of_pk K.pk
  have hq := (hP.take hcl).of_eq K.pk.rd K.pk.wr
  rw [← hcd] at hq
  refine ⟨K, by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide)], ?_⟩
  exact uargs L E₆ hst hq.src (hq.wd (d := st) (k := 16) (by omega_arith)) (by omega_arith)
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h19])
    (by rw [v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), h21, ofNat_lsr4' (by omega_arith)])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E.s1]; rfl)

/-- `cmacArgs₂`: the arguments of the finalization of the last bytes. -/
theorem cmacArgs₂_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {st : Nat} (hst : st + 16 ≤ 384)
    {P : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hq : Buf c s (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n))
    (h19 : s.gpr .s6 = P) (h20 : s.gpr .s7 = BitVec.ofNat 64 n)
    (h21 : s.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) :
    WP isa (.block (cmacArgs₂ st)) s fun s₄ => MacKeep s s₄ ∧
      FArgs s₄ c.C (c.W + BitVec.ofNat 64 st) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n))
        (c.W + BitVec.ofNat 64 384) (n - Spec.Cmac.chainedLen 16 n) c.R := by
  have hcl := chainedLen_le n
  have hrest := chainedLen_rest n
  unfold cmacArgs₂ macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_add fun t₅ v₅ => wp_sub fun t₆ v₆ =>
    WP.block_nil ?_
  have K : MacKeep s t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  have E₆ := E.of_pk K.pk
  have hq' := hq.of_eq K.pk.rd K.pk.wr
  refine ⟨K, ?_⟩
  exact fargs L E₆ hst hrest hq'.src (hq'.wd (by omega_arith))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E.s1])
    (by simp (disch := decide) only [v₆.other, v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, h19, h21])
    (by
      simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, h20, h21]
      exact ofNat_sub' hcl hn)
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E.s1]; rfl)

/-- `shortArgs out`: the state at `W + out` zeroed, and the arguments of the
finalization of the tail. -/
theorem shortArgs_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (.block (shortArgs out)) s fun s' => PK s s' ∧
      FArgs s' c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) 16 c.R := by
  have ho : out + 16 ≤ tailO ∨ tailO + 16 ≤ out := by rcases hout with rfl | rfl <;> decide
  have ho' : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  have ho8 : out % 8 = 0 := by rcases hout with rfl | rfl <;> decide
  unfold shortArgs
  rw [List.append_assoc]
  refine zero16_wp L E (d := out) (by omega_arith) ho8 fun s₁ pk₁ _ _ => ?_
  have E₁ := E.of_pk pk₁
  unfold macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_li (by decide) fun t₆ v₆ => WP.block_nil ?_
  have pk₆ : PK s₁ t₆ := (PK.ofUpd v₁).trans ((PK.ofUpd v₂).trans ((PK.ofUpd v₃).trans ((PK.ofUpd v₄).trans
    ((PK.ofUpd v₅).trans (PK.ofUpd v₆)))))
  have E₆ := E₁.of_pk pk₆
  exact ⟨pk₁.trans pk₆, fargs L E₆ (y := out) ho' (Nat.le_refl 16) (L.srcW E₆.perm (t := tailO) (k := 16) (by decide))
    (L.w_w (by omega_arith) (by decide) (by omega_arith))
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₁.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₁.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
    (by rw [v₆.gpr])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1]; rfl)⟩

/-- `longArgs₁ out`: the state at `W + out` zeroed, and the arguments of the
update over the `k` blocks of `P`. -/
theorem longArgs₁_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Addr} {n k : Nat} (hP : Buf c s P n)
    (hk : 16 * k ≤ n) (h19 : s.gpr .s6 = P) (h21 : s.gpr .s8 = BitVec.ofNat 64 (16 * k)) {out : Nat}
    (hout : out = 0 ∨ out = tO) :
    WP isa (.block (longArgs₁ out)) s fun s₁ => MacKeep s s₁ ∧ s₁.gpr .s8 = s.gpr .s8 ∧
      UArgs s₁ c.C (c.W + BitVec.ofNat 64 out) P (c.W + BitVec.ofNat 64 384) c.R k := by
  have hn := hP.lt
  have ho : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  have ho8 : out % 8 = 0 := by rcases hout with rfl | rfl <;> decide
  unfold longArgs₁
  refine zero16_wp L E (d := out) (by omega_arith) ho8 fun s₀ pk₀ g₀ _ => ?_
  simp only [List.append_eq, List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_mv fun t₅ v₅ => wp_srl (by decide) fun t₆ v₆ =>
    WP.block_nil ?_
  have K₀ : MacKeep s s₀ := ⟨pk₀, g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide), g₀ _ (by decide)⟩
  have K : MacKeep s₀ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  have E₀ := E.of_pk pk₀
  have E₆ := E₀.of_pk K.pk
  have hq := (hP.take hk).of_eq (by rw [K.pk.rd, pk₀.rd]) (by rw [K.pk.wr, pk₀.wr])
  have r21₆ : t₆.gpr .s8 = s.gpr .s8 := by
    simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, g₀]
  refine ⟨K₀.trans K, r21₆, ?_⟩
  exact uargs L E₆ ho hq.src (hq.wd (d := out) (k := 16) (by omega_arith)) (by omega_arith)
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.gpr, E₀.s2])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.gpr, v₁.other _ (by decide), E₀.s3])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
      v₂.other _ (by decide), v₁.other _ (by decide), E₀.s1])
    (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), g₀ _ (by decide), h19])
    (by
      simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, g₀, h21]
      rw [ofNat_lsr4' (by omega_arith), show 16 * k / 16 = k by omega_arith])
    (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide), E₀.s1]; rfl)

/-- `longArgs₂ out`: the arguments of the update over the first `j` blocks of
the tail. -/
theorem longArgs₂_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {n : Nat}
    (h25 : s.gpr .s0 = BitVec.ofNat 64 (jOf n)) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (.block (longArgs₂ out)) s fun s₄ => MacKeep s s₄ ∧ s₄.gpr .s8 = s.gpr .s8 ∧
      s₄.gpr .s0 = s.gpr .s0 ∧
      UArgs s₄ c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) c.R
        (jOf n) := by
  have hj1 := jOf_le n
  have ho : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  unfold longArgs₂ macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_mv fun t₆ v₆ => WP.block_nil ?_
  have K : MacKeep s t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
  have E₆ := E.of_pk K.pk
  refine ⟨K, by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other],
    by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other], ?_⟩
  exact uargs L E₆ ho (L.srcW E₆.perm (t := tailO) (k := 16 * jOf n) (by simp only [tailO]; omega_arith))
    (out_tail L hout (by decide) (by simp only [tailO]; omega_arith)) (by omega_arith)
    (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.gpr, E.s2])
    (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.gpr, v₁.other, E.s3])
    (by simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.gpr, v₂.other, v₁.other, E.s1])
    (by simp (disch := decide) only [v₆.other, v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, E.s1])
    (by simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, h25])
    (by simp (disch := decide) only [v₆.other, v₅.other, v₄.gpr, v₃.other, v₂.other, v₁.other, E.s1]; rfl)

/-- `longArgs₃ out`: the arguments of the finalization of the rest of the
tail. -/
theorem longArgs₃_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {n : Nat} (hn : n < 2 ^ 64) (h16 : 16 ≤ n)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n) (h21 : s.gpr .s8 = BitVec.ofNat 64 (16 * kOf n))
    (h25 : s.gpr .s0 = BitVec.ofNat 64 (jOf n)) {out : Nat} (hout : out = 0 ∨ out = tO) :
    WP isa (.block (longArgs₃ out)) s fun s₆ => MacKeep s s₆ ∧
      FArgs s₆ c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 (tailO + 16 * jOf n))
        (c.W + BitVec.ofNat 64 384) (n - 16 * kOf n - 16 * jOf n) c.R := by
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le n
  have hk : 16 * kOf n ≤ n := by omega_arith
  have ho : out + 16 ≤ 384 := by rcases hout with rfl | rfl <;> decide
  unfold longArgs₃ macArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
    wp_addi (by decide) fun t₄ v₄ => wp_addi (by decide) fun t₅ v₅ =>
    wp_sll (by decide) fun t₆ v₆ => wp_add fun t₇ v₇ => wp_sub fun t₈ v₈ => wp_sub fun t₉ v₉ =>
    WP.block_nil ?_
  have K : MacKeep s t₉ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
    ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans ((MacKeep.ofUpd v₆).trans ((MacKeep.ofUpd v₇).trans
      ((MacKeep.ofUpd v₈).trans (MacKeep.ofUpd v₉))))))))
  have E₉ := E.of_pk K.pk
  have sh : t₆.gpr .t0 = BitVec.ofNat 64 (16 * jOf n) := by
    simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, h25]
    exact ofNat_shl4 (by omega_arith)
  refine ⟨K, ?_⟩
  exact fargs L E₉ ho hJ.2.2 (L.srcW E₉.perm (t := tailO + 16 * jOf n) (k := n - 16 * kOf n - 16 * jOf n)
      (by simp only [tailO]; omega_arith))
    (out_tail L hout (by simp only [tailO]; omega_arith) (by simp only [tailO]; omega_arith))
    (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other,
      v₂.other, v₁.gpr, E.s2])
    (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.other,
      v₂.gpr, v₁.other, E.s3])
    (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.other, v₃.gpr,
      v₂.other, v₁.other, E.s1])
    (by
      simp (disch := decide) only [v₉.other, v₈.other, v₇.gpr, v₆.other, sh]
      simp (disch := decide) only [v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, E.s1]
      exact Offset.add_add _ _ _)
    (by
      simp (disch := decide) only [v₉.gpr, v₈.gpr, v₈.other, v₇.other, sh]
      simp (disch := decide) only [v₆.other, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, h20, h21]
      rw [ofNat_sub' hk hn, ofNat_sub' (by omega_arith) (by omega_arith)])
    (by simp (disch := decide) only [v₉.other, v₈.other, v₇.other, v₆.other, v₅.other, v₄.gpr, v₃.other,
      v₂.other, v₁.other, E.s1]; rfl)

/-- `(L − 1) / 16` tested: `L / 16` in `r9`. -/
theorem finLsr_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa (.block [.shift .srl .d .t0 .s7 4]) s fun s₁ => MacKeep s s₁ ∧ s₁.gpr .t0 = BitVec.ofNat 64 (n / 16) :=
  wp_srl (by decide) fun _ u₁ => WP.block_nil ⟨MacKeep.ofUpd u₁, by rw [u₁.gpr, h20, ofNat_lsr4' hn]⟩

/-- What a call of `vg_cmac_aes_update` keeps. -/
theorem upd_keep {s : State} {K C D S : Addr} {R n : Nat} (U : UArgs s K C D S R n) :
    Runs Impl.CmacAes.Stream.RISCV64.updCall s fun t => MacKeep s t ∧ t.gpr .s8 = s.gpr .s8 ∧
      t.gpr .s0 = s.gpr .s0 :=
  Runs.of_wp (WP.mono (upd_call U) fun _ h =>
    ⟨MacKeep.ofSaved h.rd h.wr h.sp h.saved, h.saved _ (by decide), h.saved _ (by decide)⟩)

/-! ## S2V's first state -/

/-- `D = AES-CMAC(K1, <zero>)`. -/
theorem start_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block startPre) Impl.CmacAes.Stream.RISCV64.finCall) TT :=
  rel_seqR (rel_env [] E₁ E₂ hsp agree_nil ⟨_, by taint_decide⟩) (Runs.of_wp (startPre_wp L E₁))
    (Runs.of_wp (startPre_wp L E₂)) fun _ _ ⟨K₁, _, F₁⟩ ⟨K₂, _, F₂⟩ =>
      rel_fin F₁ F₂ (by rw [K₁.pk.sp, K₂.pk.sp, hsp])

/-! ## The CMAC of a string -/

/-- `cmacOf stO`, for the same string (`n` bytes at `P`) in both runs. -/
theorem cmacOf_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
    {P : Addr} {n : Nat} (hP₁ : Buf c σ₁ P n) (hP₂ : Buf c σ₂ P n) (h19₁ : σ₁.gpr .s6 = P)
    (h19₂ : σ₂.gpr .s6 = P) (h20₁ : σ₁.gpr .s7 = BitVec.ofNat 64 n) (h20₂ : σ₂.gpr .s7 = BitVec.ofNat 64 n) :
    RelCT isa (Eq2 σ₁ σ₂) (cmacOf stO) TT := by
  have hn := hP₁.lt
  have hcl := chainedLen_le n
  have head : ∀ {σ : State}, Env c σ → Buf c σ P n → σ.gpr .s6 = P → σ.gpr .s7 = BitVec.ofNat 64 n →
      Runs (.seq (cmacLen stO) (.block (cmacArgs₁ stO))) σ fun t => MacKeep σ t ∧
        t.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) ∧
        UArgs t c.C (c.W + BitVec.ofNat 64 stO) P (c.W + BitVec.ofNat 64 384) c.R
          (Spec.Cmac.chainedLen 16 n / 16) := fun E hP h19 h20 =>
    Runs.of_wp (WP.seq (WP.mono (cmacLen_wp L E (st := stO) (by decide) (by decide) hn h20) fun s₁ ⟨K₁, h21₁, _⟩ =>
      WP.mono (cmacArgs₁_wp L (E.of_pk K₁.pk) (st := stO) (by decide) (hP.of_eq K₁.pk.rd K₁.pk.wr)
        (by rw [K₁.s6, h19]) h21₁) fun _ ⟨K₂, r21₂, U⟩ => ⟨K₁.trans K₂, by rw [r21₂, h21₁], U⟩))
  have tail : ∀ {σ ρ : State}, Env c σ → Buf c σ P n → σ.gpr .s6 = P → σ.gpr .s7 = BitVec.ofNat 64 n →
      MacKeep σ ρ → ρ.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) →
      Runs (.block (cmacArgs₂ stO)) ρ fun t => MacKeep ρ t ∧
        FArgs t c.C (c.W + BitVec.ofNat 64 stO) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n))
          (c.W + BitVec.ofNat 64 384) (n - Spec.Cmac.chainedLen 16 n) c.R := fun E hP h19 h20 G h21 =>
    Runs.of_wp (cmacArgs₂_wp L (E.of_pk G.pk) (by decide) hn ((hP.drop hcl).of_eq G.pk.rd G.pk.wr)
      (by rw [G.s6, h19]) (by rw [G.s7, h20]) h21)
  unfold cmacOf
  refine RelCT.assoc (rel_seqR (rel_env [.s6, .s7] E₁ E₂ hsp
      (agree_cons (h19₁.trans h19₂.symm) (agree_cons (h20₁.trans h20₂.symm) agree_nil)) ⟨_, by taint_decide⟩)
    (head E₁ hP₁ h19₁ h20₁) (head E₂ hP₂ h19₂ h20₂) fun τ₁ τ₂ ⟨K₁, r21₁, U₁⟩ ⟨K₂, r21₂, U₂⟩ => ?_)
  have hspτ : τ₁.sp = τ₂.sp := by rw [K₁.pk.sp, K₂.pk.sp, hsp]
  refine rel_seqR (rel_upd U₁ U₂ hspτ) (upd_keep U₁) (upd_keep U₂) fun ρ₁ ρ₂ ⟨G₁, q21₁, _⟩ ⟨G₂, q21₂, _⟩ => ?_
  have M₁ := K₁.trans G₁
  have M₂ := K₂.trans G₂
  have hspρ : ρ₁.sp = ρ₂.sp := by rw [M₁.pk.sp, M₂.pk.sp, hsp]
  refine rel_seqR (rel_env [.s6, .s7, .s8] (E₁.of_pk M₁.pk) (E₂.of_pk M₂.pk) hspρ
      (agree_cons (by rw [M₁.s6, M₂.s6, h19₁, h19₂]) (agree_cons (by rw [M₁.s7, M₂.s7, h20₁, h20₂])
        (agree_cons (by rw [q21₁, q21₂, r21₁, r21₂]) agree_nil))) ⟨_, by taint_decide⟩)
    (tail E₁ hP₁ h19₁ h20₁ M₁ (by rw [q21₁, r21₁])) (tail E₂ hP₂ h19₂ h20₂ M₂ (by rw [q21₂, r21₂]))
    fun ω₁ ω₂ ⟨N₁, F₁⟩ ⟨N₂, F₂⟩ => ?_
  exact rel_fin F₁ F₂ (by rw [N₁.pk.sp, N₂.pk.sp, hspρ])

/-! ## The associated data -/

/-- The descriptors, public: the same in both runs. -/
abbrev DescAgree (c : Cx) (m₁ m₂ : Mem) : Prop :=
  ∀ i < c.N, descW m₁ c.A i 0 = descW m₂ c.A i 0 ∧ descW m₁ c.A i 1 = descW m₂ c.A i 1

/-- One component, from two runs after the same number `i` of them. -/
theorem aStep_rel {c : Cx} (L : Lay c) {σ₁ σ₂ s₁ s₂ : State} {i : Nat} (hi : i < c.N) (I₁ : AInv c σ₁ i s₁)
    (I₂ : AInv c σ₂ i s₂) (hsp : s₁.sp = s₂.sp) (hd : DescAgree c σ₁.mem σ₂.mem) :
    RelCT isa (Eq2 s₁ s₂) (.seq (.block adNext) (.seq (cmacOf stO) (.block adStep))) TT := by
  obtain ⟨d0, d1⟩ := hd i hi
  refine rel_seqR (rel_env [.s4] I₁.env I₂.env hsp (agree_cons (I₁.s4.trans I₂.s4.symm) agree_nil)
      ⟨_, by taint_decide⟩)
    (Runs.of_wp (adNext_wp L I₁ hi)) (Runs.of_wp (adNext_wp L I₂ hi)) fun τ₁ τ₂ ⟨a19₁, a20₁, k₁⟩ ⟨a19₂, a20₂, k₂⟩ => ?_
  have E₁ := I₁.env.of_pk k₁.pk
  have E₂ := I₂.env.of_pk k₂.pk
  have hP₁ : Buf c τ₁ (descW σ₁.mem c.A i 0) (descW σ₁.mem c.A i 1).toNat := (I₁.ads i hi).of_eq k₁.pk.rd k₁.pk.wr
  have hP₂ : Buf c τ₂ (descW σ₁.mem c.A i 0) (descW σ₁.mem c.A i 1).toNat := by
    rw [d0, d1]; exact (I₂.ads i hi).of_eq k₂.pk.rd k₂.pk.wr
  have b19₂ : τ₂.gpr .s6 = descW σ₁.mem c.A i 0 := by rw [a19₂, d0]
  have b20₁ : τ₁.gpr .s7 = BitVec.ofNat 64 (descW σ₁.mem c.A i 1).toNat := by rw [a20₁]; simp
  have b20₂ : τ₂.gpr .s7 = BitVec.ofNat 64 (descW σ₁.mem c.A i 1).toNat := by rw [a20₂, d1]; simp
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [k₁.pk.sp, k₂.pk.sp, hsp]
  refine rel_seqR (cmacOf_rel L E₁ E₂ hsp₁ hP₁ hP₂ a19₁ b19₂ b20₁ b20₂)
    (Runs.of_wp (cmacOf_wp L E₁ (st := stO) (by decide) (by decide) hP₁ a19₁ b20₁))
    (Runs.of_wp (cmacOf_wp L E₂ (st := stO) (by decide) (by decide) hP₂ b19₂ b20₂))
    fun ρ₁ ρ₂ ⟨K₁, _, _⟩ ⟨K₂, _, _⟩ => ?_
  exact rel_env [.s4, .s5] (E₁.of_pk K₁.pk) (E₂.of_pk K₂.pk) (by rw [K₁.pk.sp, K₂.pk.sp, hsp₁])
    (agree_cons (by rw [K₁.s4, K₂.s4, k₁.s4, k₂.s4, I₁.s4, I₂.s4])
      (agree_cons (by rw [K₁.s5, K₂.s5, k₁.s5, k₂.s5, I₁.s5, I₂.s5]) agree_nil)) ⟨_, by taint_decide⟩

/-- S2V over all the components, from two runs at S2V's first state whose
descriptors agree. -/
theorem s2vAds_rel {c : Cx} (L : Lay c) {σ₁ σ₂ s₁ s₂ : State} (I₁ : AInv c σ₁ 0 s₁) (I₂ : AInv c σ₂ 0 s₂)
    (hsp : s₁.sp = s₂.sp) (hd : DescAgree c σ₁.mem σ₂.mem) : RelCT isa (Eq2 s₁ s₂) s2vAds TT := by
  have aw := L.aw
  have hN : c.N < 2 ^ 64 := by omega_arith
  have hσ : σ₁.sp = σ₂.sp := I₁.pk.sp.symm.trans (hsp.trans I₂.pk.sp)
  have h18₁ : s₁.gpr .s5 = BitVec.ofNat 64 c.N := by rw [I₁.s5, Nat.sub_zero]
  have h18₂ : s₂.gpr .s5 = BitVec.ofNat 64 c.N := by rw [I₂.s5, Nat.sub_zero]
  unfold s2vAds
  refine rel_ite (evalZ h18₁ hN) (evalZ h18₂ hN) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] I₁.env I₂.env hsp agree_nil ⟨_, by taint_decide⟩
  have h0 : c.N ≠ 0 := by simpa using hf
  refine (RelCT.loop (Q := TT) (fun k (a b : State) => ∃ j, k = c.N - j ∧ j < c.N ∧
      AInv c σ₁ j a ∧ AInv c σ₂ j b) (fun k => ?_) (c.N - 0)).mono
    (fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨0, rfl, by omega_arith, I₁, I₂⟩) fun _ _ h => h
  refine rel_of_eq2 fun a b ⟨j, hk, hj, J₁, J₂⟩ => ?_
  refine (rel_post (aStep_rel L hj J₁ J₂ (by rw [J₁.pk.sp, J₂.pk.sp, hσ]) hd) (Runs.of_wp (aStep_wp L J₁ hj))
    (Runs.of_wp (aStep_wp L J₂ hj))).mono (fun _ _ h => h) fun a' b' ⟨J₁', J₂'⟩ => ?_
  have ev₁ := evalNZ J₁'.s5 (by omega_arith)
  have ev₂ := evalNZ J₂'.s5 (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.N - (j + 1), ?_, j + 1, rfl, ?_, J₁', J₂'⟩⟩
  · rw [ev₁] at ht; simp at ht; omega_arith
  · rw [ev₁] at ht; simp at ht; omega_arith

/-! ## Finishing S2V -/

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
  {P : Addr} {n : Nat} (hP₁ : Buf c σ₁ P n) (hP₂ : Buf c σ₂ P n) (h19₁ : σ₁.gpr .s6 = P)
  (h19₂ : σ₂.gpr .s6 = P) (h20₁ : σ₁.gpr .s7 = BitVec.ofNat 64 n) (h20₂ : σ₂.gpr .s7 = BitVec.ofNat 64 n)
  {out : Nat} (hout : out = 0 ∨ out = tO)
include L E₁ E₂ hsp hP₁ hP₂ h19₁ h19₂ h20₁ h20₂ hout

/-- The short case, `L < 16`. -/
theorem short_rel (hn : n < 16) : RelCT isa (Eq2 σ₁ σ₂) (.seq shortTail (shortMac out)) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s6, .s7]))
      (.seq shortTail (.block (shortArgs out))) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have head : ∀ {σ : State}, Env c σ → Buf c σ P n → σ.gpr .s6 = P → σ.gpr .s7 = BitVec.ofNat 64 n →
      Runs (.seq shortTail (.block (shortArgs out))) σ fun t => PK σ t ∧
        FArgs t c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) 16 c.R :=
    fun E hP h19 h20 => Runs.of_wp (WP.seq (WP.mono (shortTail_wp L E hP hn h19 h20) fun _ ⟨pk₁, _, _⟩ =>
      WP.mono (shortArgs_wp L (E.of_pk pk₁) hout) fun _ ⟨pk, F⟩ => ⟨pk₁.trans pk, F⟩))
  unfold shortMac
  exact RelCT.assoc (rel_seqR (rel_env [.s6, .s7] E₁ E₂ hsp
      (agree_cons (h19₁.trans h19₂.symm) (agree_cons (h20₁.trans h20₂.symm) agree_nil)) t)
    (head E₁ hP₁ h19₁ h20₁) (head E₂ hP₂ h19₂ h20₂) fun _ _ ⟨pk₁, F₁⟩ ⟨pk₂, F₂⟩ =>
      rel_fin F₁ F₂ (by rw [pk₁.sp, pk₂.sp, hsp]))

/-- The long case, `L ≥ 16`. -/
theorem long_rel (h16 : 16 ≤ n) : RelCT isa (Eq2 σ₁ σ₂) (.seq longTail (longMac out)) TT := by
  have hn := hP₁.lt
  have hT := kOf_tail h16
  have hk : 16 * kOf n ≤ n := by omega_arith
  have t₁ : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s6, .s7]))
      (.seq longTail (.block (longArgs₁ out))) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₂ : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s7]))
      (.seq jBlock (.block (longArgs₂ out))) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have t₃ : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s7, .s8, .s0]))
      (.block (longArgs₃ out)) h).isSome = true := by
    rcases hout with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  -- The tail, and the arguments of the update over the `k` blocks.
  have head : ∀ {σ : State}, Env c σ → Buf c σ P n → σ.gpr .s6 = P → σ.gpr .s7 = BitVec.ofNat 64 n →
      Runs (.seq longTail (.block (longArgs₁ out))) σ fun t => MacKeep σ t ∧
        t.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) ∧
        UArgs t c.C (c.W + BitVec.ofNat 64 out) P (c.W + BitVec.ofNat 64 384) c.R (kOf n) := by
    intro σ E hP h19 h20
    unfold longTail
    refine Runs.of_wp (WP.seq (WP.seq (WP.mono (kBlock_wp hn h16 h20) fun s₁ ⟨K₁, _, r21₁⟩ => ?_)))
    refine WP.mono (tailCopy_wp L (E.of_pk K₁.pk) (hP.of_eq K₁.pk.rd K₁.pk.wr) hk hT.1 hT.2
      (by rw [K₁.s6, h19]) (by rw [K₁.s7, h20]) r21₁) fun s₂ ⟨K₂, r21₂, _, _⟩ => ?_
    have K₁₂ := K₁.trans K₂
    exact WP.mono (longArgs₁_wp L (E.of_pk K₁₂.pk) (hP.of_eq K₁₂.pk.rd K₁₂.pk.wr) hk (by rw [K₁₂.s6, h19])
      (by rw [r21₂, r21₁]) hout) fun _ ⟨K₃, r21₃, U⟩ => ⟨K₁₂.trans K₃, by rw [r21₃, r21₂, r21₁], U⟩
  -- `j`, and the arguments of the update over the first `j` blocks of the tail.
  have head₂ : ∀ {ρ : State}, Env c ρ → ρ.gpr .s7 = BitVec.ofNat 64 n →
      ρ.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) →
      Runs (.seq jBlock (.block (longArgs₂ out))) ρ fun t => MacKeep ρ t ∧
        t.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) ∧ t.gpr .s0 = BitVec.ofNat 64 (jOf n) ∧
        UArgs t c.C (c.W + BitVec.ofNat 64 out) (c.W + BitVec.ofNat 64 tailO) (c.W + BitVec.ofNat 64 384) c.R
          (jOf n) := fun E h20 h21 =>
    Runs.of_wp (WP.seq (WP.mono (jBlock_wp hn h16 h20) fun _ ⟨K₃, _, r21₃, r25₃⟩ =>
      WP.mono (longArgs₂_wp L (E.of_pk K₃.pk) r25₃ hout) fun _ ⟨K₄, r21₄, r25₄, U⟩ =>
        ⟨K₃.trans K₄, by rw [r21₄, r21₃, h21], by rw [r25₄, r25₃], U⟩))
  unfold longMac
  refine RelCT.assoc (rel_seqR (rel_env [.s6, .s7] E₁ E₂ hsp
      (agree_cons (h19₁.trans h19₂.symm) (agree_cons (h20₁.trans h20₂.symm) agree_nil)) t₁)
    (head E₁ hP₁ h19₁ h20₁) (head E₂ hP₂ h19₂ h20₂) fun τ₁ τ₂ ⟨K₁, r21₁, U₁⟩ ⟨K₂, r21₂, U₂⟩ => ?_)
  have hspτ : τ₁.sp = τ₂.sp := by rw [K₁.pk.sp, K₂.pk.sp, hsp]
  refine rel_seqR (rel_upd U₁ U₂ hspτ) (upd_keep U₁) (upd_keep U₂) fun ρ₁ ρ₂ ⟨G₁, q21₁, _⟩ ⟨G₂, q21₂, _⟩ => ?_
  have M₁ := K₁.trans G₁
  have M₂ := K₂.trans G₂
  have hspρ : ρ₁.sp = ρ₂.sp := by rw [M₁.pk.sp, M₂.pk.sp, hsp]
  have q20₁ : ρ₁.gpr .s7 = BitVec.ofNat 64 n := by rw [M₁.s7, h20₁]
  have q20₂ : ρ₂.gpr .s7 = BitVec.ofNat 64 n := by rw [M₂.s7, h20₂]
  have p21₁ : ρ₁.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by rw [q21₁, r21₁]
  have p21₂ : ρ₂.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by rw [q21₂, r21₂]
  refine RelCT.assoc (rel_seqR (rel_env [.s7] (E₁.of_pk M₁.pk) (E₂.of_pk M₂.pk) hspρ
      (agree_cons (q20₁.trans q20₂.symm) agree_nil) t₂)
    (head₂ (E₁.of_pk M₁.pk) q20₁ p21₁) (head₂ (E₂.of_pk M₂.pk) q20₂ p21₂)
    fun ω₁ ω₂ ⟨N₁, w21₁, w25₁, V₁⟩ ⟨N₂, w21₂, w25₂, V₂⟩ => ?_)
  have hspω : ω₁.sp = ω₂.sp := by rw [N₁.pk.sp, N₂.pk.sp, hspρ]
  refine rel_seqR (rel_upd V₁ V₂ hspω) (upd_keep V₁) (upd_keep V₂) fun υ₁ υ₂ ⟨G₁', x21₁, x25₁⟩ ⟨G₂', x21₂, x25₂⟩ => ?_
  have Q₁ := (M₁.trans N₁).trans G₁'
  have Q₂ := (M₂.trans N₂).trans G₂'
  have hspυ : υ₁.sp = υ₂.sp := by rw [Q₁.pk.sp, Q₂.pk.sp, hsp]
  have y20₁ : υ₁.gpr .s7 = BitVec.ofNat 64 n := by rw [Q₁.s7, h20₁]
  have y20₂ : υ₂.gpr .s7 = BitVec.ofNat 64 n := by rw [Q₂.s7, h20₂]
  have y21₁ : υ₁.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by rw [x21₁, w21₁]
  have y21₂ : υ₂.gpr .s8 = BitVec.ofNat 64 (16 * kOf n) := by rw [x21₂, w21₂]
  have y25₁ : υ₁.gpr .s0 = BitVec.ofNat 64 (jOf n) := by rw [x25₁, w25₁]
  have y25₂ : υ₂.gpr .s0 = BitVec.ofNat 64 (jOf n) := by rw [x25₂, w25₂]
  have H₁ := E₁.of_pk Q₁.pk
  have H₂ := E₂.of_pk Q₂.pk
  refine rel_seqR (rel_env [.s7, .s8, .s0] H₁ H₂ hspυ
      (agree_cons (y20₁.trans y20₂.symm) (agree_cons (y21₁.trans y21₂.symm)
        (agree_cons (y25₁.trans y25₂.symm) agree_nil))) t₃)
    (Runs.of_wp (longArgs₃_wp L H₁ hn h16 y20₁ y21₁ y25₁ hout))
    (Runs.of_wp (longArgs₃_wp L H₂ hn h16 y20₂ y21₂ y25₂ hout)) fun φ₁ φ₂ ⟨R₁, A₁⟩ ⟨R₂, A₂⟩ => ?_
  exact rel_fin A₁ A₂ (by rw [R₁.pk.sp, R₂.pk.sp, hspυ])

/-- `finish out`: S2V finished with the same string (`n` bytes at `P`) in both
runs. -/
theorem finish_rel : RelCT isa (Eq2 σ₁ σ₂) (finish out) TT := by
  have hn := hP₁.lt
  unfold finish
  refine rel_seqR (rel_env [.s7] E₁ E₂ hsp (agree_cons (h20₁.trans h20₂.symm) agree_nil) ⟨_, by taint_decide⟩)
    (Runs.of_wp (finLsr_wp hn h20₁)) (Runs.of_wp (finLsr_wp hn h20₂)) fun τ₁ τ₂ ⟨K₁, r9₁⟩ ⟨K₂, r9₂⟩ => ?_
  have hspτ : τ₁.sp = τ₂.sp := by rw [K₁.pk.sp, K₂.pk.sp, hsp]
  have F₁ := E₁.of_pk K₁.pk
  have F₂ := E₂.of_pk K₂.pk
  have q19₁ : τ₁.gpr .s6 = P := by rw [K₁.s6, h19₁]
  have q19₂ : τ₂.gpr .s6 = P := by rw [K₂.s6, h19₂]
  have q20₁ : τ₁.gpr .s7 = BitVec.ofNat 64 n := by rw [K₁.s7, h20₁]
  have q20₂ : τ₂.gpr .s7 = BitVec.ofNat 64 n := by rw [K₂.s7, h20₂]
  have B₁ := hP₁.of_eq K₁.pk.rd K₁.pk.wr
  have B₂ := hP₂.of_eq K₂.pk.rd K₂.pk.wr
  refine rel_ite (evalZ r9₁ (by omega_arith)) (evalZ r9₂ (by omega_arith)) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n / 16 = 0 := by simpa using ht
    exact short_rel L F₁ F₂ hspτ B₁ B₂ q19₁ q19₂ q20₁ q20₂ hout (by omega_arith)
  · have h0 : n / 16 ≠ 0 := by simpa using hf
    exact long_rel L F₁ F₂ hspτ B₁ B₂ q19₁ q19₂ q20₁ q20₂ hout (by omega_arith)

end

end VG.Proof.AesSiv.RISCV64
