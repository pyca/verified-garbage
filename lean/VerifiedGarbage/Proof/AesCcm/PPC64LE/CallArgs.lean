module

public import VerifiedGarbage.Proof.AesCcm.PPC64LE.Rel
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Wp
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesCcm.PPC64LE.Callee
public import VerifiedGarbage.Impl.AesCcm.PPC64LE
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# AES-CCM on PPC64LE: the arguments of the calls

Untrusted: everything here is checked by Lean. For the constant-time
proofs, what each call is given, after the instructions that set its
arguments from the environment and from the registers the pieces keep
(`updArgs1_wp`, `absArgs_wp`, `ctrArgsW_wp`, `ctrArgsD_wp`); and what every
run of code in sequence, or of a block in two parts, leaves (`Runs.seq`,
`Runs.block_append`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.PPC64LE

open VG VG.Impl.AesCcm.PPC64LE
open VG.PPC64LE hiding wp_add wp_addi wp_and wp_ld wp_li wp_lsl wp_lsr wp_lwz wp_std wp_stw wp_sub wp_subi
  wp_xor
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_addi wp_li wp_lsr)
open VG.Proof.CmacAes.Stream.PPC64LE (UArgs)
open VG.Proof.AesCtr.PPC64LE (CtrCall)
open VG.Impl.AesCbc.PPC64LE (mov)

theorem Runs.seq {a b : Prog isa} {s : State} {F G : State → Prop} (ha : Runs a s G)
    (hb : ∀ s', G s' → Runs b s' F) : Runs (.seq a b) s F := by
  intro t s' he
  cases he with
  | seq e₁ e₂ => exact hb _ (ha _ _ e₁) _ _ e₂

theorem Runs.block_append {l₁ l₂ : List Instr} {s : State} {F G : State → Prop} (h₁ : Runs (.block l₁) s G)
    (h₂ : ∀ s', G s' → Runs (.block l₂) s' F) : Runs (.block (l₁ ++ l₂)) s F := by
  intro t s' he
  rw [Exec.block_iff, execBlock_append] at he
  obtain ⟨⟨a, u⟩, ha, hb⟩ := Option.bind_eq_some_iff.mp he
  obtain ⟨⟨b, w⟩, hc, he'⟩ := Option.map_eq_some_iff.mp hb
  simp only [Prod.mk.injEq] at he'
  obtain ⟨rfl, rfl⟩ := he'
  exact h₂ _ (h₁ _ _ (.block ha)) _ _ (.block hc)

/-- What a call leaves to the next piece: the environment, the stack pointer
and our registers. -/
abbrev Kept (c : Cx) (s s' : State) : Prop :=
  Env c s' ∧ s'.sp = s.sp ∧ ∀ r ∈ [Reg.r18, .r19, .r20, .r21], s'.gpr r = s.gpr r

/-- Code without calls that writes none of the environment's registers, nor
`r18`–`r21`. -/
theorem Runs.kept {c : Cx} {code : Prog isa} {s : State} (E : Env c s) (rs : List Reg)
    (hc : writesOnly rs code = true) (hd : ∀ r ∈ keepRegs ++ ([.r18, .r19, .r20, .r21] : List Reg), r ∉ rs := by decide)
    (hn : code.noCalls = true := by decide +kernel) : Runs code s (Kept c s) :=
  (Runs.keep rs hc hn).mono fun _ ⟨k, sp⟩ =>
    ⟨E.of_pk (PK.ofKeep k sp fun r hr => hd r (List.mem_append_left _ hr)), sp, fun r hr =>
      k.gpr (hd r (List.mem_append_right _ hr))⟩

theorem Kept.trans {c : Cx} {s t u : State} (h₁ : Kept c s t) (h₂ : Kept c t u) : Kept c s u :=
  ⟨h₂.1, h₂.2.1.trans h₁.2.1, fun r hr => (h₂.2.2 r hr).trans (h₁.2.2 r hr)⟩

/-- `updBlock`'s arguments: the block `B` at `W + 32`. -/
theorem updArgs1_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (updArgs y ++ ([.addi .r6 .r14 bO, .li .r7 1] : List Instr))) s fun s' =>
      UArgs s' c.K (c.W + BitVec.ofNat 64 y) (c.W + BitVec.ofNat 64 32) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
        Kept c s s' := by
  unfold updArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by decide) (by omega) fun s₃ u₃ =>
    wp_addi (by decide) (by decide) fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ =>
    wp_li (by decide) fun s₆ u₆ => WP.block_nil ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have E₆ := E.of_pk pk₆
  refine ⟨uargs L E₆ (y := y) (by omega) (Q := c.W + BitVec.ofNat 64 32) (k := 1)
    (L.srcW E₆.perm (by decide)) (L.w_w (by omega) (by decide) (by omega)) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, E.r16])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), E.r17])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl)
    (by rw [u₆.gpr])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl), E₆, pk₆.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]

/-- `absorbPad`'s arguments: the whole blocks of the `len` bytes at `P`. -/
theorem absArgs_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (h18 : s.gpr .r18 = P) (h19 : s.gpr .r19 = BitVec.ofNat 64 len) :
    WP isa (.block (updArgs y ++ ([mov .r6 .r18, .lsr .d .r7 .r19 4] : List Instr))) s fun s' =>
      UArgs s' c.K (c.W + BitVec.ofNat 64 y) P (c.W + BitVec.ofNat 64 384) c.R (len / 16) ∧ Kept c s s' := by
  have hl := hP.lt
  have hw : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  unfold updArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by decide) (by omega) fun s₃ u₃ =>
    wp_addi (by decide) (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_lsr (by decide) fun s₆ u₆ =>
    WP.block_nil ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have E₆ := E.of_pk pk₆
  have hq := hP.take hw
  refine ⟨uargs L E₆ (y := y) (by omega) (Q := P) (k := len / 16) (hq.of_eq pk₆.rd pk₆.wr).src
    (hq.wd (by omega)) (by omega)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, E.r16])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), E.r17])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h18])
    (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), h19, VG.Proof.CmacAes.Stream.PPC64LE.shr_ofNat hl])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.r14]; rfl), E₆, pk₆.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]

/-- `vg_aes_ctr32`'s arguments for one block of `W` at `W + d`, from the
counter block at `W + 64`. -/
theorem ctrArgsW_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {d : Nat} (hd : d + 16 ≤ 384)
    (hod : 80 ≤ d ∨ d + 16 ≤ 64) :
    WP isa (.block (ctrArgs ++ ([.addi .r6 .r14 d, .li .r7 1] : List Instr))) s fun s' =>
      CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 d) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
        Kept c s s' := by
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) (by decide) fun s₅ u₅ =>
    wp_addi (by decide) (by decide) fun s₆ u₆ => wp_addi (by decide) (by omega) fun s₇ u₇ =>
    wp_li (by decide) fun s₈ u₈ => WP.block_nil ?_
  have pk₈ : PK s s₈ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))
  have E₈ := E.of_pk pk₈
  refine ⟨cargsW L E₈ (o := 64) (d := d) (by decide) hd (by omega)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, E.r16])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), E.r17])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), E.r14]; rfl)
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), E.r14])
    (by rw [u₈.gpr])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), E.r14]; rfl), E₈, pk₈.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]

/-- `vg_aes_ctr32`'s arguments for `k` blocks of the data, from block `b`. -/
theorem ctrArgsD_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {b k : Nat} (hk1 : 1 ≤ k)
    (hkb : b + k ≤ c.n / 16) (h18 : s.gpr .r18 = c.D + BitVec.ofNat 64 (16 * b))
    (h21 : s.gpr .r21 = BitVec.ofNat 64 k) :
    WP isa (.block (ctrArgs ++ ([mov .r6 .r18, mov .r7 .r21] : List Instr))) s fun s' =>
      CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384)
        c.R k ∧ Kept c s s' := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₅ u₅ => wp_mv fun t₆ u₆ => wp_addi (by decide) (by decide) fun t₇ u₇ =>
    wp_addi (by decide) (by decide) fun t₈ u₈ => wp_mv fun t₉ u₉ => wp_mv fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk₁₀ : PK s t₁₀ := (PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans (PK.ofUpd u₁₀)))))
  have E₁₀ := E.of_pk pk₁₀
  have hB := (L.bufD E₁₀.perm).drop (k := 16 * b) (by omega)
  have hQ := hB.take (k := 16 * k) (by omega)
  refine ⟨cargs L E₁₀ (o := 64) (by decide) (Q := c.D + BitVec.ofNat 64 (16 * b)) (k := k) hQ.src
    (hQ.wd (by decide)) (L.k_d.sub_right (Offset.sub_base c.D (by omega)))
    (VG.Proof.Gather.PPC64LE.covers_off E₁₀.perm.d (by omega) hn64)
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.gpr, E.r16])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.gpr, u₅.other _ (by decide), E.r17])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), u₅.other _ (by decide), E.r14]; rfl)
    (by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), h18])
    (by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), h21])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), E.r14]; rfl), E₁₀, pk₁₀.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide)]

end VG.Proof.AesCcm.PPC64LE
