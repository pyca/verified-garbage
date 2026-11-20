module

public import VerifiedGarbage.Proof.AesCcm.Scratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCcm.RISCV64
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesCcm.BytesAt
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.AesCcm.RISCV64.B0
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Crypt
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.Gather.RISCV64.LoopCT
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.B0
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Crypt
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
meta import VerifiedGarbage.Impl.AesCcm.RISCV64
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
import VerifiedGarbage.Proof.AesCcm.Compare
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesCcm.Mac
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Spec.Cmac
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.Ccm
meta import VerifiedGarbage.Proof.AesCcm.Compare
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesCcm.Mac
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.AesCcm.Ctr
meta import VerifiedGarbage.Spec.Cmac
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.Ccm
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Rel
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.AesCcm.RISCV64.Callee
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.AesCcm.RISCV64.Callee

/-! ### `AesCcm.RISCV64.CallArgs`, which only this module used -/

section

/-!
# AES-CCM on RISCV64: the arguments of the calls

Untrusted: everything here is checked by Lean. For the constant-time
proofs, what each call is given, after the instructions that set its
arguments from the environment and from the registers the pieces keep
(`updArgs1_wp`, `absArgs_wp`, `ctrArgsW_wp`, `ctrArgsD_wp`); and what every
run of code in sequence, or of a block in two parts, leaves (`Runs.seq`,
`Runs.block_append`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.Impl.AesCcm.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.CmacAes.Stream.RISCV64 (UArgs)
open VG.Proof.AesCtr.RISCV64 (CtrCall)
open VG.Impl.AesCbc.RISCV64 (mov)

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
  Env c s' ∧ s'.sp = s.sp ∧ ∀ r ∈ [Reg.s5, .s6, .s7, .s8], s'.gpr r = s.gpr r

/-- Code without calls that writes none of the environment's registers, nor
`s5`–`s8`. -/
theorem Runs.kept {c : Cx} {code : Prog isa} {s : State} (E : Env c s) (rs : List Reg)
    (hc : writesOnly rs code = true) (hd : ∀ r ∈ keepRegs ++ ([.s5, .s6, .s7, .s8] : List Reg), r ∉ rs := by decide)
    (hn : code.noCalls = true := by decide +kernel) : Runs code s (Kept c s) :=
  (Runs.keep rs hc hn).mono fun _ ⟨k, sp⟩ =>
    ⟨E.of_pk (PK.ofKeep k sp fun r hr => hd r (List.mem_append_left _ hr)), sp, fun r hr =>
      k.gpr (hd r (List.mem_append_right _ hr))⟩

theorem Kept.trans {c : Cx} {s t u : State} (h₁ : Kept c s t) (h₂ : Kept c t u) : Kept c s u :=
  ⟨h₂.1, h₂.2.1.trans h₁.2.1, fun r hr => (h₂.2.2 r hr).trans (h₁.2.2 r hr)⟩

/-- `updBlock`'s arguments: the block `B` at `W + 32`. -/
theorem updArgs1_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (.block (updArgs y ++ ([.addi .a3 .s1 (bO : Int), .li .a4 1] : List Instr))) s fun s' =>
      UArgs s' c.K (c.W + BitVec.ofNat 64 y) (c.W + BitVec.ofNat 64 32) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
        Kept c s s' := by
  unfold updArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by omega_using [hy]) fun s₃ u₃ =>
    wp_addi (by decide) fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_li (by decide) fun s₆ u₆ => WP.block_nil ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have E₆ := E.of_pk pk₆
  refine ⟨uargs L E₆ (y := y) (by omega_using [hy]) (Q := c.W + BitVec.ofNat 64 32) (k := 1)
    (L.srcW E₆.perm (by decide)) (L.w_w (by omega_using [hy]) (by decide) (by omega_using [hy])) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, E.s3])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), E.s4])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl)
    (by rw [u₆.gpr])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl), E₆, pk₆.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]

/-- `absorbPad`'s arguments: the whole blocks of the `len` bytes at `P`. -/
theorem absArgs_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    {P : Addr} {len : Nat} (hP : Buf c s P len) (hs5 : s.gpr .s5 = P) (hs6 : s.gpr .s6 = BitVec.ofNat 64 len) :
    WP isa (.block (updArgs y ++ ([mov .a3 .s5, .shift .srl .d .a4 .s6 4] : List Instr))) s fun s' =>
      UArgs s' c.K (c.W + BitVec.ofNat 64 y) P (c.W + BitVec.ofNat 64 384) c.R (len / 16) ∧ Kept c s s' := by
  have hl := hP.lt
  have hw : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  unfold updArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_addi (by omega_using [hy]) fun s₃ u₃ =>
    wp_addi (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_srl (by decide) fun s₆ u₆ =>
    WP.block_nil ?_
  have pk₆ : PK s s₆ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans (PK.ofUpd u₆)))))
  have E₆ := E.of_pk pk₆
  have hq := hP.take hw
  refine ⟨uargs L E₆ (y := y) (by omega_using [hy]) (Q := P) (k := len / 16) (hq.of_eq pk₆.rd pk₆.wr).src
    (hq.wd (by omega_using [hy])) (by omega_using [hl])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, E.s3])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, u₁.other _ (by decide), E.s4])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1])
    (by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hs5])
    (by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hs6, ofNat_lsr4 hl])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl), E₆, pk₆.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]

/-- `vg_aes_ctr32`'s arguments for one block of `W` at `W + d`, from the
counter block at `W + 64`. -/
theorem ctrArgsW_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {d : Nat} (hd : d + 16 ≤ 384)
    (hod : 80 ≤ d ∨ d + 16 ≤ 64) :
    WP isa (.block (ctrArgs ++ ([.addi .a3 .s1 (d : Int), .li .a4 1] : List Instr))) s fun s' =>
      CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 d) (c.W + BitVec.ofNat 64 384) c.R 1 ∧
        Kept c s s' := by
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_addi (by decide) fun s₅ u₅ =>
    wp_addi (by decide) fun s₆ u₆ => wp_addi (by omega_using [hd]) fun s₇ u₇ =>
    wp_li (by decide) fun s₈ u₈ => WP.block_nil ?_
  have pk₈ : PK s s₈ := (PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans
    ((PK.ofUpd u₇).trans (PK.ofUpd u₈)))))
  have E₈ := E.of_pk pk₈
  refine ⟨cargsW L E₈ (o := 64) (d := d) (by decide) hd (by omega_using [hod])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, E.s3])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), E.s4])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), E.s1]; rfl)
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), E.s1])
    (by rw [u₈.gpr])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), E.s1]; rfl), E₈, pk₈.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide)]

/-- `vg_aes_ctr32`'s arguments for `k` blocks of the data, from block `b`. -/
theorem ctrArgsD_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {b k : Nat} (hk1 : 1 ≤ k)
    (hkb : b + k ≤ c.n / 16) (hs5 : s.gpr .s5 = c.D + BitVec.ofNat 64 (16 * b))
    (hs8 : s.gpr .s8 = BitVec.ofNat 64 k) :
    WP isa (.block (ctrArgs ++ ([mov .a3 .s5, mov .a4 .s8] : List Instr))) s fun s' =>
      CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b)) (c.W + BitVec.ofNat 64 384)
        c.R k ∧ Kept c s s' := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  unfold ctrArgs
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun t₅ u₅ => wp_mv fun t₆ u₆ => wp_addi (by decide) fun t₇ u₇ =>
    wp_addi (by decide) fun t₈ u₈ => wp_mv fun t₉ u₉ => wp_mv fun t₁₀ u₁₀ => WP.block_nil ?_
  have pk₁₀ : PK s t₁₀ := (PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans (PK.ofUpd u₁₀)))))
  have E₁₀ := E.of_pk pk₁₀
  have hB := (L.bufD E₁₀.perm).drop (k := 16 * b) (by omega)
  have hQ := hB.take (k := 16 * k) (by omega_using [hkb])
  refine ⟨cargs L E₁₀ (o := 64) (by decide) (Q := c.D + BitVec.ofNat 64 (16 * b)) (k := k) hQ.src
    (hQ.wd (by decide)) (L.k_d.sub_right (Offset.sub_base c.D (by omega_using [hkb])))
    (covers_off E₁₀.perm.d (by omega_using [hkb]) hn64)
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.gpr, E.s3])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.gpr, u₅.other _ (by decide), E.s4])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), u₅.other _ (by decide), E.s1]; rfl)
    (by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), hs5])
    (by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), hs8])
    (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide), E.s1]; rfl), E₁₀, pk₁₀.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), u₅.other _ (by decide)]

end VG.Proof.AesCcm.RISCV64

end

end

/-! ### `AesCcm.RISCV64.Mac`, which only this module used -/

section

/-!
# AES-CCM on RISCV64: the CBC-MAC (`mac y`)

Untrusted: everything here is checked by Lean. `mac y` chains `B₀`, the
blocks of the associated data (none if there is none) and those of the
payload padded into the MAC state at `W + y`, which then holds the chaining
of the formatted blocks (A.2) from a zero block (`mac_wp`), whose first
`t` bytes are the MAC (`Proof.AesCcm.mac_eq`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt bytesAt_suffix adataBlocks headLen)

/-- The blocks of the associated data, by `aadHead` and `absorbPad`. -/
theorem aad_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96)
    (hs5 : s.gpr .s5 = c.A) (hs6 : s.gpr .s6 = BitVec.ofNat 64 c.al) :
    WP isa (.ite (.zero .s6) (.block []) (.seq (aadHead y) (absorbPad y))) s fun s' =>
      Absorbed c y s (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R)
        (bytesAt s.mem (c.W + BitVec.ofNat 64 y) 16) (adataBlocks (bytesAt s.mem c.A c.al))) s' := by
  have hl := L.al_lt
  have hA := L.bufA E.perm
  refine WP.ite (decide (c.al = 0)) (eval_z hs6 hl) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.al = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨PK.refl _, Frame.refl _ _, ?_⟩
    simp [adataBlocks, length_bytesAt, h0, Spec.Cmac.chain]
  · have h0 : c.al ≠ 0 := by simpa using hf
    refine WP.seq (WP.mono (aadHead_wp L E hy hA hs5 hs6 (by omega_using [h0])) fun s₁ H => ?_)
    have hk : headLen c.al ≤ c.al := Nat.min_le_left _ _
    have hB := (hA.drop hk).of_eq H.abs.pk.rd H.abs.pk.wr
    refine WP.mono (absorbPad_wp L (E.of_pk H.abs.pk) hy hB H.s5 H.s6) fun s₂ A =>
      ⟨H.abs.pk.trans A.pk, H.abs.frame.trans A.frame, ?_⟩
    rw [A.out, H.abs.out, ciph_keep L hy H.abs.frame, buf_keep (hA.drop hk) hy H.abs.frame,
      bytesAt_suffix _ _ hk, ← Proof.Cmac.chain_append]
    simp only [adataBlocks, length_bytesAt, h0, ite_false, List.singleton_append]

/-- `Yᵣ`, the chaining of the formatted blocks from a zero block, at `W + y`. -/
theorem mac_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem) {nonce : List Byte}
    (hnl : nonce.length = c.nl) (hc0 : bytesAt s.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {y : Nat} (hy : y = 0 ∨ y = 96) :
    WP isa (mac y) s (Absorbed c y s
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem c.K c.R) (Spec.Ccm.zeros 16)
        (Spec.Ccm.format c.tl nonce (bytesAt s.mem c.A c.al) (bytesAt s.mem c.D c.n)))) := by
  have hn15 : nonce.length ≤ 15 := by have := L.h13; omega_using [hnl, this]
  unfold mac
  refine WP.seq (wp_ld (a := c.W + BitVec.ofNat 64 216) (by decide) (by rw [E.s1]; rfl)
    (L.alW (by decide) (by decide)) (E.perm.wR (by decide)) fun s₁ u₁ => ?_)
  refine wp_ld (a := c.W + BitVec.ofNat 64 224) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide)) (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have E₂ := E.of_pk pk₂
  have s5₂ : s₂.gpr .s5 = c.A := by rw [u₂.other _ (by decide), u₁.gpr, S.aad]
  have s6₂ : s₂.gpr .s6 = BitVec.ofNat 64 c.al := by rw [u₂.gpr, u₁.mem, S.alen]
  refine WP.seq (WP.mono (b0_wp L E₂ (by rw [m₂]; exact S) s6₂ hnl (by rw [m₂]; exact hc0) hy)
    fun s₃ ⟨A₃, k₃⟩ => ?_)
  have f₃ : Frame (macR c.W y) s.mem s₃.mem := by have := A₃.frame; rwa [m₂] at this
  have o₃ := A₃.out
  rw [m₂] at o₃
  refine WP.seq (WP.mono (aad_wp L (E.of_pk (pk₂.trans A₃.pk)) hy (by rw [k₃ .s5 (by simp), s5₂])
    (by rw [k₃ .s6 (by simp), s6₂])) fun s₄ A₄ => ?_)
  refine WP.seq (wp_mv fun s₅ u₅ => wp_mv fun s₆ u₆ => WP.block_nil ?_)
  have pk₆ : PK s s₆ := pk₂.trans (A₃.pk.trans (A₄.pk.trans ((PK.ofUpd u₅).trans (PK.ofUpd u₆))))
  have m₆ : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have f₄ : Frame (macR c.W y) s.mem s₄.mem := f₃.trans A₄.frame
  have hD := L.bufD (E.of_pk pk₆).perm
  refine WP.mono (absorbPad_wp L (E.of_pk pk₆) hy hD
    (by rw [u₆.other _ (by decide), u₅.gpr, (pk₂.trans (A₃.pk.trans A₄.pk)).gpr .s9 (by decide), E.s9])
    (by rw [u₆.gpr, u₅.other _ (by decide), (pk₂.trans (A₃.pk.trans A₄.pk)).gpr .s10 (by decide), E.s10]))
    fun s₇ A₇ => ?_
  have o₇ := A₇.out
  have f₇ := A₇.frame
  rw [m₆] at o₇ f₇
  refine ⟨pk₆.trans A₇.pk, f₄.trans f₇, ?_⟩
  have hD₀ := L.bufD E.perm
  have hA₀ := L.bufA E.perm
  rw [o₇, A₄.out, o₃, ciph_keep L hy f₄, ciph_keep L hy f₃, buf_keep hD₀ hy f₄, buf_keep hA₀ hy f₃,
    Proof.AesCcm.format_eq c.tl hn15, Proof.Cmac.chain_append, Proof.Cmac.chain_append, length_bytesAt,
    length_bytesAt]

end VG.Proof.AesCcm.RISCV64

end

end

/-! ### `AesCcm.RISCV64.TopCT`, which only this module used -/

section

/-! ### `AesCcm.RISCV64.CtrCT`, which only this module used -/

section

/-!
# AES-CCM on RISCV64: the tag and counter mode in two runs

Untrusted: everything here is checked by Lean. `tag y`, `ctrChunk`,
`ctrTail` and `ctr`, run from two states in the same environment, leak the
same: the code between calls by the taint analysis (`rel_env`), and each
call of `vg_aes_ctr32` by its proof (`rel_ctr`). The loop over the chunks
relates two runs after the same number of blocks, which the correctness
proofs describe (`CtrInv`): the registers it branches on and the arguments
of the calls are functions of the public values.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.Impl.AesCcm.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Spec.Aes (bytesAt)

/-- Before the chunks: `s5`, `s6` and `s7` at the start of the data. -/
theorem ctrHeadBlk_wp {c : Cx} (L : Lay c) {nonce : List Byte} {s : State} (E : Env c s) :
    WP isa (.block [mov .s5 .s9, .shift .srl .d .s6 .s10 4, .li .s7 1]) s (CtrInv c nonce s 0) := by
  have hn64 := L.n_lt
  refine wp_mv fun s₁ u₁ => wp_srl (by decide) fun s₂ u₂ => wp_li (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ?_
  exact
    { pk := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
      s5 := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, E.s9]; exact (BitVec.add_zero _).symm
      s6 := by
        rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s10,
          ofNat_lsr4 hn64, Nat.sub_zero]
      s7 := u₃.gpr
      le := Nat.zero_le _
      frame := by rw [u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _
      done := rfl
      rest := by rw [u₃.mem, u₂.mem, u₁.mem] }

/-- The length of the data's last bytes. -/
theorem lastLen_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [.logicImm .and .s8 .s10 15]) s fun s' =>
      s'.gpr .s8 = s.gpr .s10 &&& BitVec.ofInt 64 15 ∧ Env c s' ∧ s'.sp = s.sp ∧
        ∀ r ∈ [Reg.s5, .s7], s'.gpr r = s.gpr r := by
  refine wp_andi (by decide) fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := PK.ofUpd u₂
  refine ⟨u₂.gpr, E.of_pk pk₂, pk₂.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [u₂.other _ (by decide)]

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
include L E₁ E₂ hsp

/-- `tag y`. -/
theorem tag_rel {y : Nat} (hy : y = 0 ∨ y = 96) : RelCT isa (Eq2 σ₁ σ₂) (tag y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block ([.li .t3 0] ++ ctrAt ++ ctrArgs ++ [.addi .a3 .s1 (y : Int), .li .a4 1])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have run : ∀ {σ : State}, Env c σ →
      Runs (.block ([.li .t3 0] ++ ctrAt ++ ctrArgs ++ [.addi .a3 .s1 (y : Int), .li .a4 1])) σ fun s' =>
        Proof.AesCtr.RISCV64.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 y)
          (c.W + BitVec.ofNat 64 384) c.R 1 ∧ Kept c σ s' := fun E => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept E [.t1, .t2, .t3] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsW_wp L K.1 (d := y) (by omega_using [hy]) (by omega_using [hy]))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  unfold tag
  exact rel_seqR (rel_env [] E₁ E₂ hsp (by simp) t) (run E₁) (run E₂)
    fun τ₁ τ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => rel_ctr C₁ C₂ (by rw [K₁.2.1, K₂.2.1, hsp])

/-- `ctrTail`, from two states that agree on where the last bytes are, how
many there are, and the counter. -/
theorem ctrTail_rel (hr : ∀ r ∈ [Reg.s5, .s7, .s8], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) ctrTail TT := by
  have run : ∀ {σ : State}, Env c σ →
      Runs (.block ([mov .t3 .s7] ++ ctrAt ++ zero16 ksO ++ ctrArgs ++ [.addi .a3 .s1 (ksO : Int), .li .a4 1])) σ
        fun s' => Proof.AesCtr.RISCV64.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.W + BitVec.ofNat 64 80)
          (c.W + BitVec.ofNat 64 384) c.R 1 ∧ Kept c σ s' := fun E => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept E [.t0, .t1, .t2, .t3] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsW_wp L K.1 (d := 80) (by decide) (by decide))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  unfold ctrTail
  refine rel_seqR (rel_env [.s7] E₁ E₂ hsp (by simpa using hr .s7 (by simp)) ⟨_, by taint_decide⟩)
    (run E₁) (run E₂) fun τ₁ τ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => ?_
  refine rel_seqR (rel_ctr C₁ C₂ (by rw [K₁.2.1, K₂.2.1, hsp])) (ctr_runs K₁.1 C₁) (ctr_runs K₂.1 C₂)
    fun ρ₁ ρ₂ G₁ G₂ => ?_
  have a₁ := K₁.trans G₁
  have a₂ := K₂.trans G₂
  refine rel_env [.s5, .s8] G₁.1 G₂.1 (by rw [a₁.2.1, a₂.2.1, hsp]) (fun r hr' => ?_) ⟨_, by taint_decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · rw [a₁.2.2 .s5 (by simp), a₂.2.2 .s5 (by simp), hr .s5 (by simp)]
  · rw [a₁.2.2 .s8 (by simp), a₂.2.2 .s8 (by simp), hr .s8 (by simp)]

/-- One chunk, from two states after the same number `b` of blocks. -/
theorem chunk_rel {b : Nat} (hb : b < c.n / 16)
    (h18₁ : σ₁.gpr .s5 = c.D + BitVec.ofNat 64 (16 * b)) (h18₂ : σ₂.gpr .s5 = c.D + BitVec.ofNat 64 (16 * b))
    (h19₁ : σ₁.gpr .s6 = BitVec.ofNat 64 (c.n / 16 - b)) (h19₂ : σ₂.gpr .s6 = BitVec.ofNat 64 (c.n / 16 - b))
    (h20₁ : σ₁.gpr .s7 = BitVec.ofNat 64 (1 + b)) (h20₂ : σ₂.gpr .s7 = BitVec.ofNat 64 (1 + b)) :
    RelCT isa (Eq2 σ₁ σ₂) ctrChunk TT := by
  have hn64 : c.n < 2 ^ 64 := L.n_lt
  unfold ctrChunk
  refine RelCT.assoc (rel_seqR (rel_env [.s6, .s7] E₁ E₂ hsp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h19₁, h19₂]
      · rw [h20₁, h20₂]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (kSel_wp (b := b) h19₁ h20₁ (by omega_using [hn64]) (by omega_using [hb, hn64])))
    (Runs.of_wp (kSel_wp (b := b) h19₂ h20₂ (by omega_using [hn64]) (by omega_using [hb, hn64])))
    fun τ₁ τ₂ ⟨s8₁, pk₁, _, k₁⟩ ⟨s8₂, pk₂, _, k₂⟩ => ?_)
  obtain ⟨k, hk⟩ : ∃ k, k = min (c.n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at s8₁ s8₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_using [hb]
  have hkb : b + k ≤ c.n / 16 := by rw [hk]; omega_using [hb]
  have F₁ := E₁.of_pk pk₁
  have F₂ := E₂.of_pk pk₂
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [pk₁.sp, pk₂.sp, hsp]
  have run : ∀ {σ τ : State}, Env c τ → σ.gpr .s5 = c.D + BitVec.ofNat 64 (16 * b) →
      (∀ r ∈ [Reg.s5, .s6, .s7], τ.gpr r = σ.gpr r) → τ.gpr .s8 = BitVec.ofNat 64 k →
      Runs (.block ([mov .t3 .s7] ++ ctrAt ++ ctrArgs ++ [mov .a3 .s5, mov .a4 .s8])) τ fun s' =>
        Proof.AesCtr.RISCV64.CtrCall s' c.K (c.W + BitVec.ofNat 64 64) (c.D + BitVec.ofNat 64 (16 * b))
          (c.W + BitVec.ofNat 64 384) c.R k ∧ Kept c τ s' := fun F hs5 kk hs8 => by
    rw [List.append_assoc]
    exact Runs.block_append (Runs.kept F [.t1, .t2, .t3] (by decide +kernel)) fun s' K =>
      (Runs.of_wp (ctrArgsD_wp L K.1 hk1 hkb (by rw [K.2.2 .s5 (by simp), kk .s5 (by simp), hs5])
        (by rw [K.2.2 .s8 (by simp), hs8]))).mono fun _ ⟨C, K'⟩ => ⟨C, K.trans K'⟩
  refine rel_seqR (rel_env [] F₁ F₂ hsp₁ (by simp) ⟨_, by taint_decide⟩) (run F₁ h18₁ k₁ s8₁)
    (run F₂ h18₂ k₂ s8₂) fun ρ₁ ρ₂ ⟨C₁, K₁⟩ ⟨C₂, K₂⟩ => ?_
  refine rel_seqR (rel_ctr C₁ C₂ (by rw [K₁.2.1, K₂.2.1, hsp₁])) (ctr_runs K₁.1 C₁) (ctr_runs K₂.1 C₂)
    fun ω₁ ω₂ G₁ G₂ => ?_
  exact rel_env [] G₁.1 G₂.1 (by rw [G₁.2.1, G₂.2.1, K₁.2.1, K₂.2.1, hsp₁]) (by simp) ⟨_, by taint_decide⟩

end

/-- `ctr`. -/
theorem ctr_rel {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
    {n₁ n₂ : List Byte} (hn₁ : n₁.length = c.nl) (hn₂ : n₂.length = c.nl)
    (hc₁ : bytesAt σ₁.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₁ 0)
    (hc₂ : bytesAt σ₂.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock n₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) ctr TT := by
  have hn64 := L.n_lt
  unfold ctr
  refine RelCT.assoc (rel_seqR ?_ (Runs.of_wp (ctrHead_wp L hn₁ E₁ hc₁)) (Runs.of_wp (ctrHead_wp L hn₂ E₂ hc₂))
    fun τ₁ τ₂ I₁ I₂ => ?_)
  · refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩)
      (Runs.of_wp (ctrHeadBlk_wp L (nonce := n₁) E₁)) (Runs.of_wp (ctrHeadBlk_wp L (nonce := n₂) E₂))
      fun τ₁ τ₂ I₁ I₂ => ?_
    have e₁ := eval_z (a := c.n / 16) (by rw [I₁.s6, Nat.sub_zero]) (by omega_using [hn64])
    have e₂ := eval_z (a := c.n / 16) (by rw [I₂.s6, Nat.sub_zero]) (by omega_using [hn64])
    refine rel_ite e₁ e₂ (fun _ => ?_) (fun hf => ?_)
    · exact rel_env [] (E₁.of_pk I₁.pk) (E₂.of_pk I₂.pk) (by rw [I₁.pk.sp, I₂.pk.sp, hsp]) (by simp)
        ⟨_, by taint_decide⟩
    have h0 : c.n / 16 ≠ 0 := by simpa using hf
    refine (RelCT.loop (Q := TT) (fun m a b => ∃ j, m = c.n / 16 - j ∧ j < c.n / 16 ∧
        CtrInv c n₁ σ₁ j a ∧ CtrInv c n₂ σ₂ j b) (fun m => ?_) (c.n / 16 - 0)).mono
      (fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨0, rfl, by omega_using [h0], I₁, I₂⟩) fun _ _ h => h
    refine rel_of_eq2 fun a b ⟨j, hm, hj, J₁, J₂⟩ => ?_
    refine (rel_post (chunk_rel L (E₁.of_pk J₁.pk) (E₂.of_pk J₂.pk) (by rw [J₁.pk.sp, J₂.pk.sp, hsp]) hj
        J₁.s5 J₂.s5 J₁.s6 J₂.s6 J₁.s7 J₂.s7)
      (Runs.of_wp (chunk_wp L hn₁ E₁ hc₁ J₁ hj)) (Runs.of_wp (chunk_wp L hn₂ E₂ hc₂ J₂ hj))).mono
      (fun _ _ h => h) fun a' b' ⟨⟨k, hk, hk1, hkb, K₁⟩, ⟨k', hk', _, _, K₂⟩⟩ => ?_
    have e : k = k' := by rw [hk, hk']
    subst e
    have ev₁ := eval_nz (r := .s6) (a := c.n / 16 - (j + k)) K₁.s6 (by omega_using [hn64])
    have ev₂ := eval_nz (r := .s6) (a := c.n / 16 - (j + k)) K₂.s6 (by omega_using [hn64])
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ⟨c.n / 16 - (j + k), ?_, j + k, rfl, ?_, K₁, K₂⟩⟩
    · rw [ev₁] at ht; simp at ht; omega_using [hm, hj, hk]
    · rw [ev₁] at ht; simp at ht; omega_using [ht]
  · have F₁ := E₁.of_pk I₁.pk
    have F₂ := E₂.of_pk I₂.pk
    have hsp₁ : τ₁.sp = τ₂.sp := by rw [I₁.pk.sp, I₂.pk.sp, hsp]
    refine rel_seqR (rel_env [] F₁ F₂ hsp₁ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (lastLen_wp F₁))
      (Runs.of_wp (lastLen_wp F₂)) fun ρ₁ ρ₂ ⟨s8₁, G₁, sp₁, k₁⟩ ⟨s8₂, G₂, sp₂, k₂⟩ => ?_
    have hsp₂ : ρ₁.sp = ρ₂.sp := by rw [sp₁, sp₂, hsp₁]
    have q21 : ρ₁.gpr .s8 = ρ₂.gpr .s8 := by rw [s8₁, s8₂, F₁.s10, F₂.s10]
    refine rel_iteZ q21 (rel_env [] G₁ G₂ hsp₂ (by simp) ⟨_, by taint_decide⟩) ?_
    refine ctrTail_rel L G₁ G₂ hsp₂ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [k₁ .s5 (by simp), k₂ .s5 (by simp), I₁.s5, I₂.s5]
    · rw [k₁ .s7 (by simp), k₂ .s7 (by simp), I₁.s7, I₂.s7]
    · exact q21

end VG.Proof.AesCcm.RISCV64

end

end

/-! ### `AesCcm.RISCV64.Open`, which this module and modules that import it used -/

section

/-! ### `AesCcm.RISCV64.Seal`, which this module and modules that import it used -/

section

/-! ### `AesCcm.RISCV64.Entry`, which this module and modules that import it used -/

section

/-! ### `AesCcm.RISCV64.Contract`, which this module and modules that import it used -/

section

/-!
# AES-CCM on RISC-V: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ccm/Contract.lean`, which imply these
(`Verified.lean`), with a 2560-byte `work` buffer appended
(`Proof/AesCcm/Scratch.lean`). A call (`jal`) stores nothing in memory, so no
stack is used; `seal` and `open` read their last three arguments from the
stack, which they may only read, at the stack pointer, which is aligned, as
`work` is (`Abi.alignsU64`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (ctxCiph encryptWith decryptWith valid zeros)

/-- The three arguments on the stack. -/
abbrev args (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- What `vg_aes_ccm_seal` and `vg_aes_ccm_open` both need, but for the
permissions: `(schedule = a0, rounds = a1, nonce = a2, nonce_len = a3,
aad = a4, aad_len = a5, data = a6, len = a7, tag = [sp], tag_len = [sp + 8],
work = [sp + 16])`, the stack pointer and `work` aligned. -/
def oneLay (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  sch.Disjoint data ∧ sch.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧ tag.Disjoint data ∧ tag.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s) ∧ work.Disjoint (args s) ∧
    (s.gpr .a0).toNat + 240 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧ (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ (stackArgAddr s 0).toNat + 24 ≤ 2 ^ 64 ∧ s.sp.toNat % 16 = 0 ∧
    (stackArg s 2).toNat % 8 = 0 ∧ rounds (s.gpr .a1) ∧
    valid (stackArg s 1).toNat (s.gpr .a3).toNat (s.gpr .a5).toNat (s.gpr .a7).toNat = true

/-- What `vg_aes_ccm_seal` needs: `oneLay`, with `tag` the `tag_len` bytes to
write. -/
def sealPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [sch, nonce, aad, args s] ∧ s.wr = [data, tag, work] ∧ oneLay s

/-- What `vg_aes_ccm_open` needs: `oneLay`, with the received tag the
`tag_len` bytes at `tag`, to read. -/
def openPre (s : State) : Prop :=
  let sch : Region := ⟨s.gpr .a0, 240⟩
  let nonce : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
  let aad : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
  let data : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
  let tag : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
  let work : Region := ⟨stackArg s 2, 2560⟩
  s.rd = [sch, nonce, aad, tag, args s] ∧ s.wr = [data, work] ∧ oneLay s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ccm_seal`. -/
def sealRISCV64 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (stackArg s 1).toNat
        (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
        (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) =
      (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat, bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := onePub

/-- What `vg_aes_ccm_open` computes, for the arguments of `s`. -/
def openRes (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .a0) (s.gpr .a1).toNat) (stackArg s 1).toNat
    (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat)
    (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- The result of `vg_aes_ccm_open`: `a0` and the `n` bytes of `out` for the
result `r` of the decryption-verification. -/
def openOut (r : Option (List Byte)) (a0 : BitVec 64) (out : List Byte) (n : Nat) : Prop :=
  match r with
  | some pt => a0.setWidth 32 = 1 ∧ out = pt
  | none => a0.setWidth 32 = 0 ∧ out = zeros n

/-- What `vg_aes_ccm_open` may leak (`Spec.Ccm.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds (s.gpr .a1) then [] else [if (openRes s).isSome = true then 1 else 0]

/-- `vg_aes_ccm_open`. -/
def openRISCV64 : Contract isa where
  pre := openPre
  post s s' := openOut (openRes s) (s'.gpr .a0) (bytesAt s'.mem (s.gpr .a6) (s.gpr .a7).toNat) (s.gpr .a7).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesCcm.RISCV64

end

end

/-!
# AES-CCM on RISC-V: the arguments and the entry

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesCcm/PPC64LE/Entry.lean`): the preconditions `sealPre` and
`openPre` give the facts the proofs use about the arguments (`Args`,
`args_of_seal`, `args_of_open`). `entry` loads `work` from the stack, saves
our caller's registers and the return address at `W + 128`, then loads the
tag length and `tag` and keeps the arguments in registers and in `W`
(`entry_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.RISCV64.Spill (saveCode saveMem Saved saveMem_saved save_ok)

/-- The public values of the arguments of `s`. -/
def cxOf (s : State) : Cx where
  K := s.gpr .a0
  W := stackArg s 2
  D := s.gpr .a6
  A := s.gpr .a4
  R := (s.gpr .a1).toNat
  tl := (stackArg s 1).toNat
  n := (s.gpr .a7).toNat
  al := (s.gpr .a5).toNat
  nl := (s.gpr .a3).toNat
  T := stackArg s 0

/-- What `seal` and `open` are given: the public values `c`, and the nonce at
`N`. -/
structure Args (c : Cx) (N : Addr) (s : State) : Prop where
  lay : Lay c
  a0 : s.gpr .a0 = c.K
  a1 : s.gpr .a1 = BitVec.ofNat 64 c.R
  a2 : s.gpr .a2 = N
  a3 : s.gpr .a3 = BitVec.ofNat 64 c.nl
  a4 : s.gpr .a4 = c.A
  a5 : s.gpr .a5 = BitVec.ofNat 64 c.al
  a6 : s.gpr .a6 = c.D
  a7 : s.gpr .a7 = BitVec.ofNat 64 c.n
  w : stackArg s 2 = c.W
  tl : stackArg s 1 = BitVec.ofNat 64 c.tl
  t : stackArg s 0 = c.T
  perm : Perm c s
  nonce : Buf c s N c.nl
  nd : (⟨N, c.nl⟩ : Region).Disjoint ⟨c.D, c.n⟩
  argsC : Covers [args s] (s.rd ++ s.wr)
  argsW : (args s).Disjoint ⟨c.W, 2560⟩
  argsD : (args s).Disjoint ⟨c.D, c.n⟩
  argsFit : (stackArgAddr s 0).toNat + 24 ≤ 2 ^ 64
  spal : s.sp.toNat % 8 = 0

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem covers_of_mem {r : Region} {rs : List Region} (h : r ∈ rs) : Covers [r] rs := fun _ _ ⟨r', hr', hc⟩ => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨_, h, hc⟩

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .a0, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .a2, (s.gpr .a3).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .a4, (s.gpr .a5).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s] (s.rd ++ s.wr))
    (hT : Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] (s.rd ++ s.wr))
    (hD : Covers [⟨s.gpr .a6, (s.gpr .a7).toNat⟩] s.wr) (hW : Covers [⟨stackArg s 2, 2560⟩] s.wr) :
    Args (cxOf s) (s.gpr .a2) s := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, b1, b2, b3, b4, b5, b6, b7, hsp, hwal, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact {
    lay := ⟨b1, b6, hwal, b4, b3, d2, d1, d9, d6, d5, hR, BitVec.isLt _, BitVec.isLt _, ht4, ht16, hte, hn7, hn13,
      hp, b5, d8, d7⟩
    a0 := rfl
    a1 := (ofNat_toNat64 _).symm
    a2 := rfl
    a3 := (ofNat_toNat64 _).symm
    a4 := rfl
    a5 := (ofNat_toNat64 _).symm
    a6 := rfl
    a7 := (ofNat_toNat64 _).symm
    w := rfl
    tl := (ofNat_toNat64 _).symm
    t := rfl
    perm := ⟨hk, hW, hD, hA, hT⟩
    nonce := ⟨hN, BitVec.isLt _, b2, d4⟩
    nd := d3
    argsC := ha
    argsW := d11.symm
    argsD := d10.symm
    argsFit := b7
    spal := by omega_using [hsp] }

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    Args (cxOf s) (s.gpr .a2) s ∧ Covers [⟨stackArg s 0, (stackArg s 1).toNat⟩] s.wr := by
  obtain ⟨hrd, hwr, hl⟩ := h
  obtain mrd : ∀ r ∈ [(⟨s.gpr .a0, 240⟩ : Region), ⟨s.gpr .a2, (s.gpr .a3).toNat⟩, ⟨s.gpr .a4, (s.gpr .a5).toNat⟩,
      args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  obtain mwr : ∀ r ∈ [(⟨s.gpr .a6, (s.gpr .a7).toNat⟩ : Region), ⟨stackArg s 0, (stackArg s 1).toNat⟩,
      ⟨stackArg s 2, 2560⟩], Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (Covers.right (mwr _ (by simp))) (mwr _ (by simp)) (mwr _ (by simp)), mwr _ (by simp)⟩

/-- `open`'s arguments, with the received tag to read. -/
theorem args_of_open {s : State} (h : openPre s) : Args (cxOf s) (s.gpr .a2) s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  obtain mrd : ∀ r ∈ [(⟨s.gpr .a0, 240⟩ : Region), ⟨s.gpr .a2, (s.gpr .a3).toNat⟩, ⟨s.gpr .a4, (s.gpr .a5).toNat⟩,
      ⟨stackArg s 0, (stackArg s 1).toNat⟩, args s], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  obtain mwr : ∀ r ∈ [(⟨s.gpr .a6, (s.gpr .a7).toNat⟩ : Region), ⟨stackArg s 2, 2560⟩], Covers [r] s.wr :=
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp))
    (mwr _ (by simp)) (mwr _ (by simp))

/-! ## The entry -/

/-- What the entry writes: the saved registers, the return address and the
slots. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 128, 120⟩

/-- The slots of our caller's registers and of the return address, in the
order the entry saves them. -/
abbrev savedL : List (Reg × Nat) := saved ++ [(.ra, raO)]

/-- Our caller's registers the entry does not save, since nothing writes them. -/
abbrev otherRegs : List Reg := [.s0, .s11]

/-- What the entry leaves. -/
structure Entered (c : Cx) (N : Addr) (s s₁ : State) : Prop where
  env : Env c s₁
  slots : Slots c s₁.mem
  saved : Saved c.W s.gpr savedL s₁.mem
  frame : Frame [entryR c.W] s.mem s₁.mem
  a2 : s₁.gpr .a2 = N
  a3 : s₁.gpr .a3 = BitVec.ofNat 64 c.nl
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  others : ∀ r ∈ otherRegs, s₁.gpr r = s.gpr r

theorem stackArgAddr_succ (s : State) (i : Nat) :
    stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) := by
  unfold stackArgAddr; rw [Offset.add_add]; congr 2; omega_using []

theorem savedL_bound : ∀ p ∈ savedL, 128 ≤ p.2 ∧ p.2 + 8 ≤ 128 + 120 := by decide

theorem savedL_fits : Spill.Fits savedL := by decide

theorem savedL_off : ∀ p ∈ savedL, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem entry_code : entry = ([.addSp .t0 0, .load .d .t1 .t0 16] : List Instr) ++ saveCode .t1 savedL ++
    ([Impl.AesCbc.RISCV64.mov .s1 .t1, .load .d .s2 .t0 8, .load .d .t1 .t0 0,
      Impl.AesCbc.RISCV64.mov .s3 .a0, Impl.AesCbc.RISCV64.mov .s4 .a1, .store .d .a4 .s1 aadO,
      .store .d .a5 .s1 alenO, .store .d .a3 .s1 nlenO, .store .d .t1 .s1 tagO,
      Impl.AesCbc.RISCV64.mov .s9 .a6, Impl.AesCbc.RISCV64.mov .s10 .a7] : List Instr) := rfl

theorem entry_wp {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block entry) s (Entered c N s) := by
  have L := Ar.lay
  have hww := L.ww
  obtain inA : ∀ {t : State} {i : Nat}, t.rd = s.rd → t.wr = s.wr → i < 3 →
      InRegions (t.rd ++ t.wr) (stackArgAddr s i) 8 := fun hrd hwr hi => by
    rw [hrd, hwr, stackArgAddr_succ]; exact in_off Ar.argsC (by omega_using [hi]) (by decide)
  obtain alA : ∀ i, (stackArgAddr s i).toNat % 8 = 0 := fun i => Spill.al8 Ar.spal (by omega_using [])
  rw [entry_code]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  obtain t0₁ : s₁.gpr .t0 = s.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 2) (by decide) (by rw [t0₁]; rfl) (alA 2) (inA u₁.rd u₁.wr (by decide))
    fun s₂ u₂ => ?_
  obtain W₂ : s₂.gpr .t1 = c.W := by rw [u₂.gpr, u₁.mem, ← Ar.w]; rfl
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  obtain m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine save_ok (b := .t1) (by rw [W₂]; exact L.wal) savedL_off (fun p hp => by
    rw [W₂, wr₂]; exact Ar.perm.wW (by have := savedL_bound p hp; omega_using [this])) ?_
  rw [W₂]
  generalize hs₃ : ({ s₂ with mem := saveMem s₂.mem c.W s₂.gpr savedL } : State) = s₃
  obtain g₃ : s₃.gpr = s₂.gpr := by rw [← hs₃]
  obtain rd₃ : s₃.rd = s.rd := by rw [← hs₃]; exact rd₂
  obtain wr₃ : s₃.wr = s.wr := by rw [← hs₃]; exact wr₂
  obtain sp₃ : s₃.sp = s.sp := by rw [← hs₃]; show s₂.sp = _; rw [u₂.sp, u₁.sp]
  obtain mS : s₃.mem = saveMem s.mem c.W s₂.gpr savedL := by rw [← hs₃, m₂]
  obtain fS : Frame [entryR c.W] s.mem s₃.mem := by
    rw [mS]; exact Spill.saveMem_frame savedL_bound (by omega_using []) _ _ _
  obtain svS : Saved c.W s₂.gpr savedL s₃.mem := by rw [mS]; exact saveMem_saved savedL_fits _ _ _
  obtain hAW : ∀ r ∈ [entryR c.W], (args s).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Ar.argsW.sub_right (Offset.sub_base _ (by decide))
  refine wp_mv fun s₄ u₄ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by decide)
    (by rw [u₄.other _ (by decide), g₃, u₂.other _ (by decide), t0₁]; rfl) (alA 1)
    (by rw [u₄.rd, u₄.wr]; exact inA rd₃ wr₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_ld (a := stackArgAddr s 0) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃, u₂.other _ (by decide), t0₁]; rfl) (alA 0)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr]; exact inA rd₃ wr₃ (by decide)) fun s₆ u₆ => ?_
  refine wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => ?_
  obtain m₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain rdA : ∀ {i : Nat}, i < 3 → s₃.mem.readW (stackArgAddr s i) 64 = stackArg s i := fun hi => by
    rw [fS.readW (r := args s) (by rw [stackArgAddr_succ]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
      hAW (by decide)]; rfl
  obtain g₈ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → r ≠ .s4 → s₈.gpr r = s.gpr r := by
    intro r h0 h1 h11 h2 h3 h4
    rw [u₈.other _ h4, u₇.other _ h3, u₆.other _ h1, u₅.other _ h2, u₄.other _ h11, g₃, u₂.other _ h1,
      u₁.other _ h0]
  obtain s1₈ : s₈.gpr .s1 = c.W := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g₃, W₂]
  obtain t1₈ : s₈.gpr .t1 = c.T := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, rdA (by decide), Ar.t]
  obtain s2₈ : s₈.gpr .s2 = BitVec.ofNat 64 c.tl := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, rdA (by decide),
      Ar.tl]
  obtain s3₈ : s₈.gpr .s3 = c.K := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, u₂.other _ (by decide), u₁.other _ (by decide), Ar.a0]
  obtain s4₈ : s₈.gpr .s4 = BitVec.ofNat 64 c.R := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g₃, u₂.other _ (by decide), u₁.other _ (by decide), Ar.a1]
  obtain wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃]
  obtain inW : ∀ {d : Nat}, d + 8 ≤ 2560 → InRegions s₈.wr (c.W + BitVec.ofNat 64 d) 8 := fun hd => by
    rw [wr₈]; exact Ar.perm.wW hd
  refine wp_sd (a := c.W + BitVec.ofNat 64 216) (by decide) (by rw [s1₈]; rfl) (L.alW (by decide) (by decide))
    (inW (by decide)) fun s₉ u₉ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 224) (by decide) (by rw [u₉.gpr, s1₈]; rfl)
    (L.alW (by decide) (by decide)) (by rw [u₉.wr]; exact inW (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 232) (by decide) (by rw [u₁₀.gpr, u₉.gpr, s1₈]; rfl)
    (L.alW (by decide) (by decide)) (by rw [u₁₀.wr, u₉.wr]; exact inW (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [u₁₁.gpr, u₁₀.gpr, u₉.gpr, s1₈]; rfl)
    (L.alW (by decide) (by decide)) (by rw [u₁₁.wr, u₁₀.wr, u₉.wr]; exact inW (by decide)) fun s₁₂ u₁₂ => ?_
  refine wp_mv fun s₁₃ u₁₃ => wp_mv fun s₁₄ u₁₄ => WP.block_nil ?_
  obtain g₁₂ : s₁₂.gpr = s₈.gpr := by rw [u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₉.gpr]
  obtain gF : ∀ r, r ≠ .s9 → r ≠ .s10 → s₁₄.gpr r = s₈.gpr r := fun r h9 h10 => by
    rw [u₁₄.other _ h10, u₁₃.other _ h9, g₁₂]
  -- The memory.
  obtain mF : s₁₄.mem = (((s₃.mem.writeW (c.W + BitVec.ofNat 64 216) c.A).writeW (c.W + BitVec.ofNat 64 224)
      (BitVec.ofNat 64 c.al)).writeW (c.W + BitVec.ofNat 64 232) (BitVec.ofNat 64 c.nl)).writeW
      (c.W + BitVec.ofNat 64 240) c.T := by
    rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₁₁.gpr, u₁₀.gpr, u₉.gpr, t1₈,
      g₈ .a4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₈ .a5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₈ .a3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), Ar.a4, Ar.a5, Ar.a3, m₈]
  obtain cE : ∀ d, 128 ≤ d → d + 8 ≤ 248 → (entryR c.W).Contains (c.W + BitVec.ofNat 64 d) (64 / 8) := fun d h₁ h₂ =>
    Offset.contains c.W h₁ (by omega_using [h₂]) (by omega_using [])
  obtain fF : Frame [entryR c.W] s.mem s₁₄.mem := by
    rw [mF]
    exact (((fS.writeW (List.mem_singleton_self _) _ (cE 216 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 224 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 232 (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (cE 240 (by decide) (by decide))
  obtain sep : ∀ {a b : Nat}, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 2560 → b + 8 ≤ 2560 →
      Mem.Sep (c.W + BitVec.ofNat 64 a) (64 / 8) (c.W + BitVec.ofNat 64 b) (64 / 8) := fun h ha hb =>
    (L.w_w (n := 8) (k := 8) h ha hb).sep (Region.contains_self _ _) (Region.contains_self _ _)
  obtain rdF : s₁₄.rd = s.rd := by
    rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃]
  obtain wrF : s₁₄.wr = s.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, wr₈]
  refine ⟨⟨by rw [gF _ (by decide) (by decide), s1₈], by rw [gF _ (by decide) (by decide), s2₈],
      by rw [gF _ (by decide) (by decide), s3₈], by rw [gF _ (by decide) (by decide), s4₈], ?_, ?_,
      Ar.perm.of_eq rdF wrF⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, fF, ?_, ?_, rdF, wrF, ?_, ?_⟩
  · rw [u₁₄.other _ (by decide), u₁₃.gpr, g₁₂, g₈ .a6 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), Ar.a6]
  · rw [u₁₄.gpr, u₁₃.other _ (by decide), g₁₂, g₈ .a7 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), Ar.a7]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 216) (b := 240) (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sep (a := 216) (b := 232) (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sep (a := 216) (b := 224) (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 224) (b := 240) (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sep (a := 224) (b := 232) (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_sep (sep (a := 232) (b := 240) (by omega_using []) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_self64]
  · rw [mF, Mem.readW_writeW_self64]
  · -- The slots, which the later stores miss.
    obtain fT : Frame [⟨c.W + BitVec.ofNat 64 216, 32⟩] s₃.mem s₁₄.mem := by
      rw [mF]
      obtain c' : ∀ d, 216 ≤ d → d + 8 ≤ 248 →
          (⟨c.W + BitVec.ofNat 64 216, 32⟩ : Region).Contains (c.W + BitVec.ofNat 64 d) (64 / 8) :=
        fun d h₁ h₂ => Offset.contains c.W h₁ (by omega_using [h₂]) (by omega_using [])
      exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c' 216 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c' 224 (by decide) (by decide))).writeW
        (List.mem_singleton_self _) _ (c' 232 (by decide) (by decide)) |>.writeW
        (List.mem_singleton_self _) _ (c' 240 (by decide) (by decide))
    obtain sv := svS.frame fT fun q hq r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have := savedL_bound q hq
      obtain h216 : q.2 + 8 ≤ 216 := (show ∀ p ∈ savedL, p.2 + 8 ≤ 216 by decide) q hq
      exact L.w_w (.inl h216) (by omega_using [this]) (by decide)
    intro p hp
    rw [sv p hp]
    obtain h1 : p.1 ≠ .t0 ∧ p.1 ≠ .t1 := (show ∀ q ∈ savedL, q.1 ≠ .t0 ∧ q.1 ≠ .t1 by decide) p hp
    rw [u₂.other _ h1.2, u₁.other _ h1.1]
  · rw [gF _ (by decide) (by decide), g₈ .a2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), Ar.a2]
  · rw [gF _ (by decide) (by decide), g₈ .a3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), Ar.a3]
  · rw [u₁₄.sp, u₁₃.sp, u₁₂.sp, u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃]
  · intro r hr
    simp only [otherRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [gF _ (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)]

end VG.Proof.AesCcm.RISCV64

end

end

/-! ### `AesCcm.RISCV64.Exit`, which this module and modules that import it used -/

section

/-!
# AES-CCM on RISC-V: the exit

Untrusted: everything here is checked by Lean. `restore` reloads the return
address and our caller's registers from the slots the entry filled at
`W + 128` (`exit_wp`), `s1`, the base, last.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesCcm.RISCV64
open VG.RISCV64.Spill (Saved restoreCode restore_wp)

/-- The slots `restore` reloads, in its order. -/
abbrev restoreL : List (Reg × Nat) := (.ra, raO) :: saved

theorem restore_code : restore = restoreCode .s1 restoreL := rfl

theorem restoreL_sub : ∀ p ∈ restoreL, p ∈ savedL := by decide

theorem other_of_preserved : ∀ r ∈ preserved, r ∉ restoreL.map Prod.fst → r ∈ otherRegs := by decide

/-- `restore`: our caller's registers and return address back, for `s₀` the
state at the entry. -/
theorem exit_wp {c : Cx} (L : Lay c) {s₀ s : State} (E : Env c s) (sv : Saved c.W s₀.gpr savedL s.mem)
    (hsp : s.sp = s₀.sp) (ho : ∀ r ∈ otherRegs, s.gpr r = s₀.gpr r) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .a0 = s.gpr .a0 := by
  rw [restore_code]
  refine WP.mono (restore_wp (b := .s1) (B := c.W) L.wal E.s1 (by decide) (by decide) (fun p hp => by
      have := savedL_bound p (restoreL_sub p hp)
      exact E.perm.wR (by omega_using [this])) (sv.sub restoreL_sub)) fun s' R => ?_
  refine ⟨⟨fun r hr => ?_, by rw [R.sp, hsp], R.gpr (.ra, raO) List.mem_cons_self⟩, R.mem,
    R.other _ (by decide)⟩
  by_cases hs : r ∈ restoreL.map Prod.fst
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
    exact R.gpr p hp
  · rw [R.other r hs, ho r (other_of_preserved r hr hs)]

end VG.Proof.AesCcm.RISCV64

end

end

/-!
# AES-CCM on RISCV64: `vg_aes_ccm_seal`

Untrusted: everything here is checked by Lean. `seal` is `entry`, `Ctr₀`
(`ctrs`), the MAC of the payload (`mac 0`), encrypted at `W` (`tag 0`),
counter mode over the data (`ctr`), the tag copied to `tag` (`tagOut`) and
`restore` (`seal_wp`). The lemmas about what each piece keeps serve `open`
too.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.RISCV64.Spill (Saved)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher)

theorem other_keep : ∀ r ∈ otherRegs, r ∈ keepRegs := by decide

/-- The entry keeps a buffer missing `W`. -/
theorem entry_buf {c : Cx} {s s₁ : State} (hf : Frame [entryR c.W] s.mem s₁.mem) {P : Addr} {len : Nat}
    (hP : Buf c s P len) : bytesAt s₁.mem P len = bytesAt s.mem P len :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP.wd (by decide)) (by have := hP.lt; omega_using [this])

theorem entry_ciph {c : Cx} (L : Lay c) {s s₁ : State} (hf : Frame [entryR c.W] s.mem s₁.mem) :
    Spec.Ccm.ctxCiph s₁.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w' (by decide)).sub_left (Region.sub_prefix L.rb)) (by have := L.rb; omega_using [this])]

theorem c0_mut (c : Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 48, 16⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_lo (by decide)

theorem ctrR_mut (c : Cx) {y : Nat} (hy : y = 0 ∨ y = 96) : ∀ r ∈ ctrR c.W y, ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_lo (by decide)
  · exact sub_lo (by omega_using [hy])
  · exact sub_hi (by decide) (by decide)

/-- A part of `W` missing the regions `rs` the pieces write in `W`. -/
theorem w_keep {c : Cx} (L : Lay c) {rs : List (Nat × Nat)} {d k : Nat}
    (h : ∀ q ∈ rs, (d + k ≤ q.1 ∨ q.1 + q.2 ≤ d) ∧ q.1 + q.2 ≤ 2560) (hd : d + k ≤ 2560) :
    ∀ r ∈ rs.map (fun q => (⟨c.W + BitVec.ofNat 64 q.1, q.2⟩ : Region)),
      (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact L.w_w (h q hq).1 hd (h q hq).2

/-- A buffer missing `W` is kept by the regions `rs` in `W`. -/
theorem bufW_keep {c : Cx} {s : State} {P : Addr} {len : Nat} (hP : Buf c s P len) {rs : List (Nat × Nat)}
    (h : ∀ q ∈ rs, q.1 + q.2 ≤ 2560) :
    ∀ r ∈ rs.map (fun q => (⟨c.W + BitVec.ofNat 64 q.1, q.2⟩ : Region)), (⟨P, len⟩ : Region).Disjoint r := by
  intro r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact hP.wd (h q hq)

theorem c0_list (W : Addr) : [(⟨W + BitVec.ofNat 64 48, 16⟩ : Region)] =
    [(48, 16)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem macR_list (W : Addr) (y : Nat) : macR W y =
    [(y, 16), (32, 16), (384, 2176)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem ctrR_list (W : Addr) (y : Nat) : ctrR W y =
    [(64, 16), (y, 16), (384, 2048)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

/-- Our caller's registers, kept in their slots by writes to `mutR`. -/
theorem saved_mut {c : Cx} (L : Lay c) {g : Reg → BitVec 64} {m m' : Mem} (hf : Frame (mutR c) m m')
    (h : Saved c.W g savedL m) : Saved c.W g savedL m' :=
  h.frame_in savedL_bound hf (kept_mut L ⟨by decide, by decide⟩)

/-- `vg_aes_ccm_seal`, for its arguments. -/
theorem seal_wp' {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) (hTw : Covers [⟨c.T, c.tl⟩] s.wr) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧
      Spec.Ccm.encryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n)
        (bytesAt s.mem c.A c.al) = (bytesAt s'.mem c.D c.n, bytesAt s'.mem c.T c.tl) := by
  have L := Ar.lay
  have ht16 := L.t16
  have hn := L.n_lt
  unfold «seal»
  refine WP.seq (WP.mono (entry_wp Ar) fun s₁ En => ?_)
  have hN₁ : Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (ctrs_wp L En.env hN₁ En.a2 En.a3) fun s₂ ⟨pk₂, f₂, c₂⟩ => ?_)
  rw [entry_buf En.frame Ar.nonce] at c₂
  have hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  have f₂' : Frame (mutR c) s₁.mem s₂.mem := f₂.sub (c0_mut c)
  have E₂ := En.env.of_pk pk₂
  refine WP.seq (WP.mono (mac_wp L E₂ (En.slots.mut L f₂') hnl c₂ (.inl rfl)) fun s₃ M => ?_)
  have c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    have fM := M.frame
    rw [macR_list] at fM
    rw [Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide), c₂]
  have E₃ := E₂.of_pk M.pk
  refine WP.seq (WP.mono (tag_wp L E₃ hnl c₃ (.inl rfl)) fun s₄ ⟨pk₄, _, f₄, h₄⟩ => ?_)
  have c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [ctrR_list] at f₄
    rw [Proof.Cmac.bytesAt_frame f₄ (w_keep L (by decide) (by decide)) (by decide), c₃]
  have E₄ := E₃.of_pk pk₄
  refine WP.seq (WP.mono (ctr_wp L E₄ hnl c₄) fun s₅ ⟨pk₅, f₅, h₅⟩ => ?_)
  have E₅ := E₄.of_pk pk₅
  have f₁₃ : Frame (mutR c) s₁.mem s₃.mem := f₂'.trans (M.frame.sub (macR_mut (.inl rfl)))
  have f₁₄ : Frame (mutR c) s₁.mem s₄.mem := f₁₃.trans (f₄.sub (ctrR_mut c (.inl rfl)))
  have f₁₅ : Frame (mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (crR_mut c))
  have pk₁₅ : PK s₁ s₅ := pk₂.trans (M.pk.trans (pk₄.trans pk₅))
  have wr₅ : s₅.wr = s.wr := by rw [pk₁₅.wr, En.wr]
  refine WP.seq (WP.mono (tagOut_wp L E₅ (En.slots.mut L f₁₅) (by rw [wr₅]; exact hTw))
    fun s₆ ⟨pk₆, f₆, t₆⟩ => ?_)
  have pk₁₆ : PK s₁ s₆ := pk₁₅.trans pk₆
  have sv₆ : Saved c.W s.gpr savedL s₆.mem :=
    (saved_mut L f₁₅ En.saved).frame_in savedL_bound f₆ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.t_w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (exit_wp L (E₅.of_pk pk₆) sv₆ (by rw [pk₁₆.sp, En.sp])
    (fun r hr => by rw [pk₁₆.gpr r (other_keep r hr), En.others r hr])) fun s' ⟨abi, hm, _⟩ => ⟨abi, ?_⟩
  -- The ciphertext and the tag.
  have hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  have k₁ := entry_ciph L En.frame
  have k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₂', k₁]
  have k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₃, k₁]
  have k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₄, k₁]
  have bD := L.bufD Ar.perm
  have bD₁ : Buf c s₁ c.D c.n := bD.of_eq En.rd En.wr
  have hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [c0_list] at f₂
    rw [Proof.Cmac.bytesAt_frame f₂ (bufW_keep bD₁ (by decide)) (by omega_using [hn]), entry_buf En.frame bD]
  have ha₂ : bytesAt s₂.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [aad_mut L f₂', entry_buf En.frame (L.bufA Ar.perm)]
  have hd₄ : bytesAt s₄.mem c.D c.n = bytesAt s.mem c.D c.n := by
    have fM := M.frame
    rw [macR_list] at fM
    rw [ctrR_list] at f₄
    rw [Proof.Cmac.bytesAt_frame f₄ (bufW_keep bD₁ (by decide)) (by omega_using [hn]),
      Proof.Cmac.bytesAt_frame fM (bufW_keep bD₁ (by decide)) (by omega_using [hn]), hd₂]
  have w₅ : bytesAt s₅.mem c.W c.tl = bytesAt s₄.mem c.W c.tl := by
    have h := Proof.Cmac.bytesAt_frame (p := c.W + BitVec.ofNat 64 0) (n := c.tl) f₅
      (crR_disj L (.inl (by omega_using [ht16]))) (by omega_using [ht16])
    rwa [BitVec.add_zero] at h
  have e0 : c.W + BitVec.ofNat 64 0 = c.W := BitVec.add_zero c.W
  have M' := M.out
  rw [e0] at h₄ M'
  have hY : (bytesAt s₃.mem c.W 16).length = 16 := length_bytesAt _ _ _
  have d₆ : bytesAt s₆.mem c.D c.n = bytesAt s₅.mem c.D c.n :=
    Proof.Cmac.bytesAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_d.symm) (by omega_using [hn])
  simp only [Spec.Ccm.encryptWith, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [hm, d₆, h₅, k₄, hd₄, crypt_eq (hBC _)]
  · rw [hm, t₆, w₅, Proof.AesCcm.bytesAt_prefix s₄.mem c.W L.t16, h₄, k₃,
      take_xorFrom_zero (hBC _) _ hY L.t16, M', k₂, ha₂, hd₂, mac_eq _ _ (by rw [hnl]; have := L.h13; omega_using [this])]
    rfl

/-- `vg_aes_ccm_seal`. -/
theorem seal_wp {s : State} (h : sealRISCV64.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealRISCV64.post s s' := by
  have A := args_of_seal h
  refine WP.mono (seal_wp' A.1 A.2) fun s' ⟨ga, hp⟩ => ⟨ga, ?_⟩
  simp only [sealRISCV64]
  simpa only [cxOf] using hp

end VG.Proof.AesCcm.RISCV64

end

end

/-!
# AES-CCM on RISCV64: `vg_aes_ccm_open`

Untrusted: everything here is checked by Lean. `open` is `entry`, `Ctr₀`
(`ctrs`), counter mode over the data (`ctr`), which decrypts it, the MAC of
the plaintext (`mac uO`), encrypted at `W + 96` (`tag uO`), the comparison
with the received tag, whose address the entry keeps in `W` (`cmp`), the
plaintext zeroed unless they are equal (`mask`), the result in `a0` and
`restore` (`open_wp`). `cmp` copies the first `tag_len` bytes of the
received tag (at `s5`) and of the computed one (at `W + 96`) over zeros at
`W + 272` and `W + 256`, and leaves 1 in `s8` iff the two padded blocks are
equal, without a branch (`cmp_wp`); `mask` ANDs every byte of the data with
`0 − s8` (`mask_wp`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesCcm.RISCV64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.RISCV64.Spill (Saved)
open VG.Proof.AesCcm (xorFrom length_bytesAt crypt_eq take_xorFrom_zero mac_eq length_xorFrom BlockCipher
  cryptTag_eq_iff)

/-! ## Checking the received tag -/

theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `1 − (0 <ᵤ d)`: 1 if `d` is 0, else 0. -/
theorem zero_test (d : BitVec 64) :
    BitVec.ofNat 64 1 - (if BitVec.ofNat 64 0 < d then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if d = 0 then 1 else 0) := by
  by_cases hd : d = 0
  · subst hd; decide
  · have h : BitVec.ofNat 64 0 < d := by
      rw [BitVec.lt_def]
      have : d.toNat ≠ 0 := fun h => hd (BitVec.eq_of_toNat_eq (by simpa using h))
      simp only [BitVec.toNat_ofNat]; omega_using [this]
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_right_of_eq_false _ _ (eq_false hd)]; decide

/-- The comparison's last block: `s8` is 1 iff the 16 bytes at `W + 256` and
at `W + 272` are equal. -/
theorem cmpTail_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) :
    WP isa (.block [.load .d .t0 .s1 vO, .load .d .t1 .s1 rO, .logic .xor .t0 .t0 .t1,
      .load .d .t1 .s1 (vO + 8), .load .d .t2 .s1 (rO + 8), .logic .xor .t1 .t1 .t2,
      .logic .or .t0 .t0 .t1, .li .t1 0, .sltu .t0 .t1 .t0, .li .s8 1, .sub .s8 .s8 .t0]) s fun s' =>
      PK s s' ∧ s'.mem = s.mem ∧
      s'.gpr .s8 = BitVec.ofNat 64 (if bytesAt s.mem (c.W + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (c.W + BitVec.ofNat 64 272) 16 then 1 else 0) := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 256) (by decide) (by rw [E.s1]; rfl)
    (L.alW (by decide) (by decide)) (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 272) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₂ u₂ => wp_xor fun s₃ u₃ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 264) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s1]; rfl)
    (L.alW (by decide) (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 280) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      E.s1]; rfl)
    (L.alW (by decide) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact E.perm.wR (by decide))
    fun s₅ u₅ => ?_
  refine wp_xor fun s₆ u₆ => wp_or fun s₇ u₇ => wp_li (by decide) fun s₈ u₈ => wp_sltu fun s₉ u₉ =>
    wp_li (by decide) fun s₁₀ u₁₀ => wp_sub fun s₁₁ u₁₁ => WP.block_nil ?_
  refine ⟨(PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofUpd u₅).trans ((PK.ofUpd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans
    ((PK.ofUpd u₉).trans ((PK.ofUpd u₁₀).trans (PK.ofUpd u₁₁)))))))))),
    by rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem,
      u₂.mem, u₁.mem], ?_⟩
  obtain hd : s₇.gpr .t0 =
      (s.mem.readW (c.W + BitVec.ofNat 64 256) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 272) 64) |||
      (s.mem.readW (c.W + BitVec.ofNat 64 264) 64 ^^^ s.mem.readW (c.W + BitVec.ofNat 64 280) 64) := by
    rw [u₇.gpr, u₆.gpr, u₆.other .t0 (by decide), u₅.gpr, u₅.other .t1 (by decide), u₄.gpr,
      u₅.other .t0 (by decide), u₄.other .t0 (by decide), u₃.gpr, u₂.gpr, u₂.other .t0 (by decide), u₁.gpr,
      u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  rw [u₁₁.gpr, u₁₀.gpr, u₁₀.other .t0 (by decide), u₉.gpr, u₈.gpr, u₈.other .t0 (by decide), hd, zero_test]
  obtain hw := Proof.AesCcm.words_eq s.mem (c.W + BitVec.ofNat 64 256) (c.W + BitVec.ofNat 64 272)
  rw [Offset.add_add, Offset.add_add] at hw
  congr 2
  exact propext hw

/-- `cmp`: 1 in `s8` iff the `tag_len` bytes at `T` (`s5`) are the first
`tag_len` of the computed tag at `W + 96`. -/
theorem cmp_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (hs5 : s.gpr .s5 = c.T) :
    WP isa cmp s fun s' => PK s s' ∧ Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s'.mem ∧
      s'.gpr .s8 = BitVec.ofNat 64
        (if bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem c.T c.tl then 1 else 0) := by
  have ht4 := L.t4
  have ht16 := L.t16
  unfold cmp zero16
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => ?_)
  refine wp_sd (a := c.W + BitVec.ofNat 64 256) (by decide)
    (by rw [u₁.other _ (by decide), E.s1]; rfl) (L.alW (by decide) (by decide)) (by rw [u₁.wr]; exact E.perm.wW (by decide)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.alW (by decide) (by decide))
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₃ u₃ => ?_
  refine wp_li (by decide) fun s₄ u₄ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 272) (by decide)
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1]; rfl)
    (L.alW (by decide) (by decide))
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact E.perm.wW (by decide)) fun s₅ u₅ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (by decide)
    (by rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add]; rfl)
    (by rw [Offset.add_add]; exact L.alW (by decide) (by decide))
    (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by decide)) fun s₆ u₆ => ?_
  refine wp_mv fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ => wp_mv fun s₉ u₉ => WP.block_nil ?_
  obtain pk₉ : PK s s₉ := (PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans ((PK.ofMupd u₃).trans ((PK.ofUpd u₄).trans
    ((PK.ofMupd u₅).trans ((PK.ofMupd u₆).trans ((PK.ofUpd u₇).trans ((PK.ofUpd u₈).trans (PK.ofUpd u₉))))))))
  obtain E₉ := E.of_pk pk₉
  obtain m₉ : s₉.mem = (((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
      (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272)
      (0 : BitVec 64)).writeW (c.W + BitVec.ofNat 64 272 + BitVec.ofNat 64 8) (0 : BitVec 64) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.mem, u₁.gpr]
    rfl
  obtain g₉ : ∀ r, r ≠ .t0 → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s₉.gpr r = s.gpr r := fun r h0 h3 h9 h4 => by
    rw [u₉.other _ h4, u₈.other _ h9, u₇.other _ h3, u₆.gpr, u₅.gpr, u₄.other _ h0, u₃.gpr, u₂.gpr, u₁.other _ h0]
  obtain f256 : Frame [⟨c.W + BitVec.ofNat 64 256, 16⟩] s.mem
      ((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) := Proof.Cmac.frame_store2 _ _ _
  obtain f272 : Frame [⟨c.W + BitVec.ofNat 64 272, 16⟩]
      ((s.mem.writeW (c.W + BitVec.ofNat 64 256) (0 : BitVec 64)).writeW
        (c.W + BitVec.ofNat 64 256 + BitVec.ofNat 64 8) (0 : BitVec 64)) s₉.mem := by
    rw [m₉]; exact Proof.Cmac.frame_store2 _ _ _
  obtain z272 : bytesAt s₉.mem (c.W + BitVec.ofNat 64 272) 16 = Spec.Ccm.zeros 16 := by
    rw [m₉]; exact zeros16_bytes _ _
  obtain z256 : bytesAt s₉.mem (c.W + BitVec.ofNat 64 256) 16 = Spec.Ccm.zeros 16 := by
    rw [Proof.Cmac.bytesAt_frame f272 (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]
    exact zeros16_bytes _ _
  obtain hdT : (⟨c.T, c.tl⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 272, c.tl⟩ :=
    L.t_w.sub_right (Lay.wSub (by omega_using [ht16]))
  obtain hb₁ : BytesPre s₉ c.T (c.W + BitVec.ofNat 64 272) c.tl :=
    { a0 := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), hs5]
      a1 := by rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s1]; rfl
      a2 := by rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.other _ (by decide),
        u₃.gpr, u₂.gpr, u₁.other _ (by decide), E.s2]
      pos := by omega_using [ht4]
      lt := by omega_using [ht16]
      rd := by rw [pk₉.rd, pk₉.wr]; exact E.perm.t
      wr := E₉.perm.wC (by omega_using [ht16])
      disj := hdT }
  refine WP.seq (WP.mono (copy_wp s₉ hb₁) fun s₁₀ ⟨hm₁₀, _, k₁₀⟩ => ?_)
  refine WP.seq (wp_addi (by decide) fun s₁₁ u₁₁ => wp_addi (by decide) fun s₁₂ u₁₂ =>
    wp_mv fun s₁₃ u₁₃ => WP.block_nil ?_)
  obtain pk₁₃ : PK s s₁₃ := pk₉.trans ((PK.ofKeeps k₁₀).trans ((PK.ofUpd u₁₁).trans ((PK.ofUpd u₁₂).trans
    (PK.ofUpd u₁₃))))
  obtain E₁₃ := E.of_pk pk₁₃
  obtain m₁₃ : s₁₃.mem = s₁₀.mem := by rw [u₁₃.mem, u₁₂.mem, u₁₁.mem]
  obtain hb₂ : BytesPre s₁₃ (c.W + BitVec.ofNat 64 96) (c.W + BitVec.ofNat 64 256) c.tl :=
    { a0 := by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, k₁₀.gpr _ (by decide),
        E₉.s1]; rfl
      a1 := by rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), k₁₀.gpr _ (by decide), E₉.s1]; rfl
      a2 := by rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), k₁₀.gpr _ (by decide), E₉.s2]
      pos := by omega_using [ht4]
      lt := by omega_using [ht16]
      rd := E₁₃.perm.wCR (by omega_using [ht16])
      wr := E₁₃.perm.wC (by omega_using [ht16])
      disj := L.w_w (.inl (by omega_using [ht16])) (by omega_using [ht16]) (by omega_using [ht16]) }
  refine WP.seq (WP.mono (copy_wp s₁₃ hb₂) fun s₁₄ ⟨hm₁₄, _, k₁₄⟩ => ?_)
  obtain E₁₄ := E₁₃.of_pk (PK.ofKeeps k₁₄)
  refine WP.mono (cmpTail_wp L E₁₄) fun s₁₅ ⟨pk₁₅, m₁₅, s8₁₅⟩ => ?_
  -- What `cmp` writes: the two padded blocks at `W + 256`.
  obtain s256 : Region.Sub ⟨c.W + BitVec.ofNat 64 256, 16⟩ ⟨c.W + BitVec.ofNat 64 256, 32⟩ :=
    Region.sub_prefix (by decide)
  obtain s272 : Region.Sub ⟨c.W + BitVec.ofNat 64 272, 16⟩ ⟨c.W + BitVec.ofNat 64 256, 32⟩ :=
    Offset.sub c.W (by decide) (by decide)
  obtain one : ∀ {r : Region}, Region.Sub r ⟨c.W + BitVec.ofNat 64 256, 32⟩ →
      ∀ x ∈ [r], ∃ r' ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], Region.Sub x r' := fun h x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact ⟨_, List.mem_singleton_self _, h⟩
  obtain f₉ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₉.mem := (f256.sub (one s256)).trans (f272.sub (one s272))
  obtain w₁₀ : Frame [⟨c.W + BitVec.ofNat 64 272, 16⟩] s₉.mem s₁₃.mem := by
    rw [m₁₃, hm₁₀]
    exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Offset.contains c.W (Nat.le_refl _) (by omega_using [ht16]) (by decide))
  obtain w₁₄ : Frame [⟨c.W + BitVec.ofNat 64 256, 16⟩] s₁₃.mem s₁₄.mem := by
    rw [hm₁₄]
    exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Offset.contains c.W (Nat.le_refl _) (by omega_using [ht16]) (by decide))
  obtain f₁₃ : Frame [⟨c.W + BitVec.ofNat 64 256, 32⟩] s.mem s₁₃.mem := f₉.trans (w₁₀.sub (one s272))
  refine ⟨pk₁₃.trans ((PK.ofKeeps k₁₄).trans pk₁₅), ?_, ?_⟩
  · rw [m₁₅]; exact f₁₃.trans (w₁₄.sub (one s256))
  · have hA : bytesAt s₁₃.mem (c.W + BitVec.ofNat 64 96) c.tl = bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl :=
      Proof.Cmac.bytesAt_frame f₁₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by omega_using [ht16])) (by omega_using [ht16]) (by decide))
        (by omega_using [ht16])
    obtain hB : bytesAt s₉.mem c.T c.tl = bytesAt s.mem c.T c.tl :=
      Proof.Cmac.bytesAt_frame f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.t_w.sub_right (Lay.wSub (by decide)))
        (by omega_using [ht16])
    obtain z256' : bytesAt s₁₃.mem (c.W + BitVec.ofNat 64 256) 16 = Spec.Ccm.zeros 16 := by
      rw [Proof.Cmac.bytesAt_frame w₁₀ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
        (by decide)]
      exact z256
    obtain h256 : bytesAt s₁₄.mem (c.W + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (c.W + BitVec.ofNat 64 96) c.tl ++ Spec.Ccm.zeros (16 - c.tl) := by
      rw [hm₁₄, Proof.AesCcm.pad_bytes z256' _ (by rw [length_bytesAt]; omega_using [ht16]), length_bytesAt, hA]
    obtain h272 : bytesAt s₁₄.mem (c.W + BitVec.ofNat 64 272) 16 = bytesAt s.mem c.T c.tl ++ Spec.Ccm.zeros (16 - c.tl) := by
      rw [Proof.Cmac.bytesAt_frame w₁₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), m₁₃, hm₁₀, Proof.AesCcm.pad_bytes z272 _ (by rw [length_bytesAt]; omega_using [ht16]), length_bytesAt, hB]
    rw [s8₁₅, h256, h272]
    congr 2
    exact propext (Proof.AesCcm.pad_eq (by rw [length_bytesAt, length_bytesAt]))

/-- One byte ANDed with `0 − s8`: the byte if `P`, else 0. -/
theorem mask_byte (b : Byte) (P : Prop) [Decidable P] :
    ((b.setWidth 64 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0))).setWidth 8 : Byte) =
      if P then b else 0 := by
  rw [BitVec.setWidth_and, byte_rt]
  by_cases hP : P <;> simp only [hP, ite_true, ite_false]
  · rw [show ((BitVec.ofNat 64 0 - BitVec.ofNat 64 1).setWidth 8 : Byte) = BitVec.allOnes 8 by decide,
      BitVec.and_allOnes]
  · rw [show ((BitVec.ofNat 64 0 - BitVec.ofNat 64 0).setWidth 8 : Byte) = 0 by decide]
    simp

/-- The byte just past what `writeBytes` writes is unchanged. -/
theorem writeBytes_end (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 xs.length) = m (q + BitVec.ofNat 64 xs.length) := by
  simp only [writeBytes]
  rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp

/-- `mask`: every byte of the data kept if `P`, zeroed if not, for `s8` the
indicator of `P`. -/
theorem mask_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {P : Prop} [Decidable P]
    (hs8 : s.gpr .s8 = BitVec.ofNat 64 (if P then 1 else 0)) :
    WP isa mask s fun s' => PK s s' ∧ s'.gpr .s8 = s.gpr .s8 ∧
      s'.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D c.n).map fun b => if P then b else 0) := by
  have hn := L.n_lt
  unfold mask
  refine WP.seq (wp_li (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    WP.block_nil ?_)
  obtain pk₄ : PK s s₄ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofUpd u₃).trans (PK.ofUpd u₄)))
  obtain m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain s8₄ : s₄.gpr .s8 = s.gpr .s8 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain r9₄ : s₄.gpr .t1 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if P then 1 else 0) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hs8]
  obtain r3₄ : s₄.gpr .a0 = c.D := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s9]
  obtain r4₄ : s₄.gpr .a2 = BitVec.ofNat 64 c.n := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), E.s10]
  obtain E₄ := E.of_pk pk₄
  let f : Byte → Byte := fun b => if P then b else 0
  refine WP.ite (decide (c.n = 0)) (eval_z r4₄ hn) (fun ht => ?_) (fun hf => ?_)
  · have h0 : c.n = 0 := of_decide_eq_true ht
    refine WP.block_nil ⟨pk₄, s8₄, ?_⟩
    rw [m₄, h0]
    simp [bytesAt, writeBytes_nil]
  · have h0 : c.n ≠ 0 := by simpa using hf
    refine WP.loop (M := isa)
      (fun (w : Nat) (t : State) => ∃ i, w = c.n - i ∧ i < c.n ∧ t.gpr .a0 = c.D + BitVec.ofNat 64 i ∧
        t.gpr .a2 = BitVec.ofNat 64 (c.n - i) ∧ t.gpr .t1 = s₄.gpr .t1 ∧ t.gpr .s8 = s.gpr .s8 ∧
        t.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D i).map f) ∧ PK s t) ?_ (c.n - 0) _
      ⟨0, rfl, by omega_using [h0], by rw [r3₄]; exact (BitVec.add_zero _).symm, by rw [r4₄, Nat.sub_zero], rfl, s8₄,
        by rw [m₄]; simp [bytesAt, writeBytes_nil], pk₄⟩
    rintro w t ⟨i, rfl, hi, r3, r4, r9, s8, mem, pk⟩
    obtain Et := E.of_pk pk
    obtain hin : i + 1 ≤ c.n := by omega_using [hi]
    have hD : Covers [⟨c.D, c.n⟩] t.wr := Et.perm.d
    unfold maskBody
    refine wp_lbu (a := c.D + BitVec.ofNat 64 i) (by decide)
      (by rw [r3]; exact BitVec.add_zero _)
      (in_off (Covers.right hD) hin hn) fun t₁ u₁ => ?_
    refine wp_and fun t₂ u₂ => ?_
    refine wp_sb (a := c.D + BitVec.ofNat 64 i) (by decide)
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide), r3]; exact BitVec.add_zero _)
      (by rw [u₂.wr, u₁.wr]; exact in_off hD hin hn) fun t₃ u₃ => ?_
    refine wp_addi (by decide) fun t₄ u₄ => wp_subi (by decide) fun t₅ u₅ =>
      WP.block_nil ?_
    obtain pk₅ : PK s t₅ := pk.trans ((PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans ((PK.ofMupd u₃).trans
      ((PK.ofUpd u₄).trans (PK.ofUpd u₅)))))
    obtain hlen : ((bytesAt s.mem c.D i).map f).length = i := by rw [List.length_map, length_bytesAt]
    obtain hb : t.mem (c.D + BitVec.ofNat 64 i) = s.mem (c.D + BitVec.ofNat 64 i) := by
      rw [mem]
      have := writeBytes_end s.mem c.D ((bytesAt s.mem c.D i).map f) (by rw [hlen]; omega_using [hn, hi])
      rwa [hlen] at this
    obtain hmem : t₅.mem = writeBytes s.mem c.D ((bytesAt s.mem c.D (i + 1)).map f) := by
      rw [u₅.mem, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₁.other .t1 (by decide), r9, r9₄, u₂.mem,
        u₁.mem, mask_byte, hb, mem, Proof.Cmac.Stream.bytesAt_append, bytesAt_one,
        List.map_append, List.map_singleton]
      rw [writeBytes_snoc _ _ _ _ (by rw [hlen]; omega_using [hn, hi]), hlen]
    obtain hstep : c.D + BitVec.ofNat 64 i + BitVec.ofNat 64 1 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    obtain r3' : t₅.gpr .a0 = c.D + BitVec.ofNat 64 (i + 1) := by
      rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r3, hstep]
    obtain r4' : t₅.gpr .a2 = BitVec.ofNat 64 (c.n - (i + 1)) := by
      rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r4,
        ofNat_sub_one (by omega_using [hi]), Nat.sub_sub]
    obtain r9' : t₅.gpr .t1 = s₄.gpr .t1 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), r9]
    obtain s8' : t₅.gpr .s8 = s.gpr .s8 := by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
        s8]
    obtain ev := eval_nz (r := .a2) (a := c.n - (i + 1)) r4' (by omega_using [hn])
    by_cases he : i + 1 = c.n
    · left
      exact ⟨by rw [ev]; simp [he], pk₅, s8', by rw [hmem, he]⟩
    · right
      exact ⟨by rw [ev]; simp; omega_using [hi, he], c.n - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], r3', r4', r9', s8', hmem, pk₅⟩

/-! ## The function -/

theorem cmpR_mut (c : Cx) : ∀ r ∈ [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_hi (by decide) (by decide)

theorem maskR_mut (c : Cx) : ∀ r ∈ [(⟨c.D, c.n⟩ : Region)], ∃ r' ∈ mutR c, Region.Sub r r' := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact sub_data

theorem cmpR_list (W : Addr) : [(⟨W + BitVec.ofNat 64 256, 32⟩ : Region)] =
    [(256, 32)].map (fun q => (⟨W + BitVec.ofNat 64 q.1, q.2⟩ : Region)) := rfl

theorem length_chain {ciph : Spec.Ccm.Cipher} (hc : BlockCipher ciph) :
    ∀ (ms : List (List Byte)) (c : List Byte), c.length = 16 → (Spec.Cmac.chain ciph c ms).length = 16
  | [], _, h => h
  | _ :: ms, _, _ => length_chain hc ms _ (hc _)

/-- The data masked: itself if `P`, zeros if not. -/
theorem masked {m : Mem} {D : Addr} {n : Nat} (hn : n < 2 ^ 64) (P : Prop) [Decidable P] :
    bytesAt (writeBytes m D ((bytesAt m D n).map fun b => if P then b else 0)) D n =
      if P then bytesAt m D n else Spec.Ccm.zeros n := by
  rw [Proof.AesCcm.bytesAt_writeBytes_base _ _ _ (by rw [List.length_map, length_bytesAt]) hn,
    List.length_map, length_bytesAt, List.drop_eq_nil_of_le (by rw [length_bytesAt]), List.append_nil]
  by_cases hP : P
  · simp [hP]
  · simp only [hP, ite_false, Spec.Ccm.zeros]
    rw [List.map_const', length_bytesAt]

/-- `vg_aes_ccm_open`, for its arguments. -/
theorem open_wp' {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧
      openOut (Spec.Ccm.decryptWith (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n) (bytesAt s.mem c.A c.al) (bytesAt s.mem c.T c.tl)) (s'.gpr .a0)
        (bytesAt s'.mem c.D c.n) c.n := by
  have L := Ar.lay
  have ht16 := L.t16
  have hn := L.n_lt
  unfold «open»
  refine WP.seq (WP.mono (entry_wp Ar) fun s₁ En => ?_)
  obtain hN₁ : Buf c s₁ N c.nl := Ar.nonce.of_eq En.rd En.wr
  refine WP.seq (WP.mono (ctrs_wp L En.env hN₁ En.a2 En.a3) fun s₂ ⟨pk₂, f₂, c₂⟩ => ?_)
  rw [entry_buf En.frame Ar.nonce] at c₂
  obtain hnl : (bytesAt s.mem N c.nl).length = c.nl := length_bytesAt _ _ _
  obtain f₂' : Frame (mutR c) s₁.mem s₂.mem := f₂.sub (c0_mut c)
  obtain E₂ := En.env.of_pk pk₂
  refine WP.seq (WP.mono (ctr_wp L E₂ hnl c₂) fun s₃ ⟨pk₃, f₃, h₃⟩ => ?_)
  obtain E₃ := E₂.of_pk pk₃
  obtain f₁₃ : Frame (mutR c) s₁.mem s₃.mem := f₂'.trans (f₃.sub (crR_mut c))
  obtain c₃ : bytesAt s₃.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.Cmac.bytesAt_frame f₃ (crR_disj L (.inl (by decide))) (by decide), c₂]
  refine WP.seq (WP.mono (mac_wp L E₃ (En.slots.mut L f₁₃) hnl c₃ (.inr rfl)) fun s₄ M => ?_)
  have fM := M.frame
  rw [macR_list] at fM
  obtain c₄ : bytesAt s₄.mem (c.W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock (bytesAt s.mem N c.nl) 0 := by
    rw [Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide), c₃]
  obtain E₄ := E₃.of_pk M.pk
  refine WP.seq (WP.mono (tag_wp L E₄ hnl c₄ (.inr rfl)) fun s₅ ⟨pk₅, _, f₅, h₅⟩ => ?_)
  obtain E₅ := E₄.of_pk pk₅
  obtain f₁₄ : Frame (mutR c) s₁.mem s₄.mem := f₁₃.trans (M.frame.sub (macR_mut (.inr rfl)))
  obtain f₁₅ : Frame (mutR c) s₁.mem s₅.mem := f₁₄.trans (f₅.sub (ctrR_mut c (.inr rfl)))
  -- The address of the received tag, from its slot.
  refine WP.seq (wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E₅.s1]; rfl)
    (L.alW (by decide) (by decide)) (E₅.perm.wR (by decide)) fun s₆ u₆ => WP.block_nil ?_)
  obtain pk₆ : PK s₅ s₆ := PK.ofUpd u₆
  have m₆ : s₆.mem = s₅.mem := u₆.mem
  obtain s5₆ : s₆.gpr .s5 = c.T := by rw [u₆.gpr]; exact (En.slots.mut L f₁₅).tag
  refine WP.seq (WP.mono (cmp_wp L (E₅.of_pk pk₆) s5₆) fun s₇ ⟨pk₇, f₇, s8₇⟩ => ?_)
  rw [m₆] at s8₇ f₇
  -- What the comparison compares.
  obtain hBC : ∀ m : Mem, BlockCipher (Spec.Ccm.ctxCiph m c.K c.R) := fun _ x => Proof.Cmac.aesWith_length _ _ x
  obtain k₁ := entry_ciph L En.frame
  obtain k₂ : Spec.Ccm.ctxCiph s₂.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₂', k₁]
  obtain k₃ : Spec.Ccm.ctxCiph s₃.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₃, k₁]
  obtain k₄ : Spec.Ccm.ctxCiph s₄.mem c.K c.R = Spec.Ccm.ctxCiph s.mem c.K c.R := by rw [ciph_mut L f₁₄, k₁]
  obtain bD := L.bufD Ar.perm
  obtain bD₁ : Buf c s₁ c.D c.n := bD.of_eq En.rd En.wr
  obtain hd₂ : bytesAt s₂.mem c.D c.n = bytesAt s.mem c.D c.n := by
    rw [c0_list] at f₂
    rw [Proof.Cmac.bytesAt_frame f₂ (bufW_keep bD₁ (by decide)) (by omega_using [hn]), entry_buf En.frame bD]
  obtain ha₃ : bytesAt s₃.mem c.A c.al = bytesAt s.mem c.A c.al := by
    rw [aad_mut L f₁₃, entry_buf En.frame (L.bufA Ar.perm)]
  obtain hpt : bytesAt s₃.mem c.D c.n =
      Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n) := by
    rw [h₃, k₂, hd₂, crypt_eq (hBC _)]
  obtain hd₇ : bytesAt s₇.mem c.D c.n = bytesAt s₃.mem c.D c.n := by
    rw [cmpR_list] at f₇
    rw [ctrR_list] at f₅
    rw [Proof.Cmac.bytesAt_frame f₇ (bufW_keep bD₁ (by decide)) (by omega_using [hn]),
      Proof.Cmac.bytesAt_frame f₅ (bufW_keep bD₁ (by decide)) (by omega_using [hn]),
      Proof.Cmac.bytesAt_frame fM (bufW_keep bD₁ (by decide)) (by omega_using [hn])]
  obtain hrecv : bytesAt s₅.mem c.T c.tl = bytesAt s.mem c.T c.tl := by
    rw [tag_mut L f₁₅, Proof.Cmac.bytesAt_frame En.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.t_w.sub_right (Lay.wSub (by decide))) (by omega_using [ht16])]
  obtain hcomp : bytesAt s₅.mem (c.W + BitVec.ofNat 64 96) c.tl =
      Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
          (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))) := by
    rw [show c.W + BitVec.ofNat 64 96 = c.W + BitVec.ofNat 64 uO from rfl, Proof.AesCcm.bytesAt_prefix s₅.mem _ L.t16,
      h₅, k₄, take_xorFrom_zero (hBC _) _ (length_bytesAt _ _ _) L.t16, M.out, k₃,
      ha₃, hpt, mac_eq _ _ (by rw [hnl]; have := L.h13; omega_using [this])]
    rfl
  rw [hcomp, hrecv] at s8₇
  refine WP.seq (WP.mono (mask_wp L (E₅.of_pk (pk₆.trans pk₇)) s8₇) fun s₈ ⟨pk₈, s8₈, m₈⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_mv fun s₉ u₉ => ?_
  obtain f₈ : Frame [⟨c.D, c.n⟩] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_frame _ _ _ (by rw [List.length_map, length_bytesAt]; exact Region.contains_self _ _)
  obtain f₁₈ : Frame (mutR c) s₁.mem s₈.mem :=
    (f₁₅.trans ((m₆ ▸ (show Frame [(⟨c.W + BitVec.ofNat 64 256, 32⟩ : Region)] s₆.mem s₇.mem by
      rw [m₆]; exact f₇)).sub (cmpR_mut c))).trans (f₈.sub (maskR_mut c))
  obtain pk₁₉ : PK s₁ s₉ := pk₂.trans (pk₃.trans (M.pk.trans (pk₅.trans (pk₆.trans (pk₇.trans (pk₈.trans
    (PK.ofUpd u₉)))))))
  obtain sv₉ : Saved c.W s.gpr savedL s₉.mem := by rw [u₉.mem]; exact saved_mut L f₁₈ En.saved
  refine WP.mono (exit_wp L (En.env.of_pk pk₁₉) sv₉ (by rw [pk₁₉.sp, En.sp])
    (fun r hr => by rw [pk₁₉.gpr r (other_keep r hr), En.others r hr])) fun s' ⟨abi, hm, r3'⟩ => ⟨abi, ?_⟩
  -- The result.
  obtain hmlen : (Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl) (bytesAt s.mem c.A c.al)
      (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl) (bytesAt s.mem c.D c.n))).length =
      c.tl := by
    rw [mac_eq _ _ (by rw [hnl]; have := L.h13; omega_using [this]), List.length_take,
      length_chain (hBC _) _ _ (by simp [Spec.Cmac.zeros])]
    omega_using [ht16]
  obtain hiff := cryptTag_eq_iff (hBC s.mem) L.t16 (bytesAt s.mem N c.nl) hmlen (length_bytesAt s.mem c.T c.tl)
  obtain hr3 : s'.gpr .a0 = s₇.gpr .s8 := by rw [r3', u₉.gpr, s8₈]
  simp only [openOut, Spec.Ccm.decryptWith]
  rw [hr3, s8₇, hm, u₉.mem, m₈, masked hn, hd₇, hpt]
  by_cases he : Spec.Ccm.cryptTag (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
      (bytesAt s.mem c.T c.tl) = Spec.Ccm.mac (Spec.Ccm.ctxCiph s.mem c.K c.R) c.tl (bytesAt s.mem N c.nl)
        (bytesAt s.mem c.A c.al) (Spec.Ccm.crypt (Spec.Ccm.ctxCiph s.mem c.K c.R) (bytesAt s.mem N c.nl)
          (bytesAt s.mem c.D c.n))
  · have hq := hiff.mpr he.symm
    simp only [he, hq, ite_true]
    exact ⟨by decide, trivial⟩
  · have hq : ¬ _ := fun h => he (hiff.mp h).symm
    simp only [he, hq, ite_false]
    exact ⟨by decide, trivial⟩

/-- `vg_aes_ccm_open`. -/
theorem open_wp {s : State} (h : openRISCV64.pre s) :
    WP isa «open» s fun s' => abiPreserved s s' ∧ openRISCV64.post s s' :=
  WP.mono (open_wp' (args_of_open h)) fun _ hp => hp

end VG.Proof.AesCcm.RISCV64

end

end

/-! ### `AesCcm.RISCV64.MacCT`, which only this module used -/

section

/-!
# AES-CCM on RISCV64: the CBC-MAC in two runs

Untrusted: everything here is checked by Lean. Each piece of `mac y`, run
from two states in the same environment, leaks the same: the code between
calls by the taint analysis (`rel_env`), from the environment's registers
and those on which the two runs agree (the pointer and the length of the
string being absorbed, in `s5` and `s6`, which the correctness proofs pin),
and each call of `vg_cmac_aes_update` by its proof (`rel_upd`), from the
arguments `CallArgs.lean` gives it.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.Impl.AesCcm.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_ite)
open VG.Impl.AesCbc.RISCV64 (mov)

/-- Code without calls that writes none of the environment's registers. -/
theorem Runs.env {c : Cx} {code : Prog isa} {s : State} (E : Env c s) (rs : List Reg)
    (hc : writesOnly rs code = true) (hd : ∀ r ∈ keepRegs, r ∉ rs := by decide)
    (hn : code.noCalls = true := by decide +kernel) : Runs code s fun s' => Env c s' ∧ s'.sp = s.sp :=
  (Runs.keep rs hc hn).mono fun _ ⟨k, sp⟩ => ⟨E.of_pk (PK.ofKeep k sp hd), sp⟩

/-! ## What the pieces set -/

/-- The pointer to and the length of the associated data, from their slots. -/
theorem aadLd_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .s5 .s1 aadO, .load .d .s6 .s1 alenO]) s fun s' =>
      s'.gpr .s5 = c.A ∧ s'.gpr .s6 = BitVec.ofNat 64 c.al ∧ Env c s' ∧ s'.sp = s.sp := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 216) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := c.W + BitVec.ofNat 64 224) (by decide) (by rw [u₁.other _ (by decide), E.s1]; rfl)
    (L.alW (by decide) (by decide))
    (by rw [u₁.rd, u₁.wr]; exact E.perm.wR (by decide)) fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr, S.aad], by rw [u₂.gpr, u₁.mem, S.alen], E.of_pk pk₂, pk₂.sp⟩

/-- The pointer to and the length of the data. -/
theorem dataArgs_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [mov .s5 .s9, mov .s6 .s10]) s fun s' =>
      s'.gpr .s5 = c.D ∧ s'.gpr .s6 = BitVec.ofNat 64 c.n ∧ Env c s' ∧ s'.sp = s.sp := by
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := (PK.ofUpd u₁).trans (PK.ofUpd u₂)
  exact ⟨by rw [u₂.other _ (by decide), u₁.gpr, E.s9], by rw [u₂.gpr, u₁.other _ (by decide), E.s10],
    E.of_pk pk₂, pk₂.sp⟩

/-- The length's last 4 bits. -/
theorem mask15_wp {c : Cx} {s : State} (E : Env c s) :
    WP isa (.block [.logicImm .and .s8 .s6 15]) s fun s' =>
      s'.gpr .s8 = s.gpr .s6 &&& BitVec.ofInt 64 15 ∧ Env c s' ∧ s'.sp = s.sp ∧
        ∀ r ∈ [Reg.s5, .s6], s'.gpr r = s.gpr r := by
  refine wp_andi (by decide) fun s₂ u₂ => WP.block_nil ?_
  have pk₂ : PK s s₂ := PK.ofUpd u₂
  refine ⟨u₂.gpr, E.of_pk pk₂, pk₂.sp, fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rw [u₂.other _ (by decide)]

/-! ## What every run of a piece keeps -/

theorem updBlock_runs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    Runs (updBlock y) s (Kept c s) := by
  unfold updBlock
  exact Runs.seq (Runs.of_wp (updArgs1_wp L E hy)) fun _ ⟨U, K⟩ => (upd_runs K.1 U).mono fun _ K' => K.trans K'

theorem b0_runs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y = 0 ∨ y = 96) :
    Runs (b0 y) s (Kept c s) := by
  unfold b0
  refine Runs.seq (Runs.kept E [.t1, .t2, .t3] (by decide +kernel)) fun _ K => ?_
  refine Runs.seq (Runs.kept K.1 [.t0, .t1, .t2] (by rcases hy with rfl | rfl <;> decide +kernel)
    (hn := by rcases hy with rfl | rfl <;> decide +kernel)) fun _ K' => ?_
  exact (updBlock_runs L K'.1 hy).mono fun _ K'' => K.trans (K'.trans K'')

/-! ## Two runs -/

section
variable {c : Cx} (L : Lay c) {σ₁ σ₂ : State} (E₁ : Env c σ₁) (E₂ : Env c σ₂) (hsp : σ₁.sp = σ₂.sp)
  {y : Nat} (hy : y = 0 ∨ y = 96)
include L E₁ E₂ hsp hy

/-- `updBlock y`. -/
theorem updBlock_rel : RelCT isa (Eq2 σ₁ σ₂) (updBlock y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ []))
      (.block (updArgs y ++ [.addi .a3 .s1 (bO : Int), .li .a4 1])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact rel_seqR (rel_env [] E₁ E₂ hsp (by simp) t) (Runs.of_wp (updArgs1_wp L E₁ hy))
    (Runs.of_wp (updArgs1_wp L E₂ hy)) fun τ₁ τ₂ ⟨U₁, K₁⟩ ⟨U₂, K₂⟩ => rel_upd U₁ U₂ (by rw [K₁.2.1, K₂.2.1, hsp])

/-- `absTail y`, from two states that agree on the string and the length of
its tail. -/
theorem absTail_rel (hr : ∀ r ∈ [Reg.s5, .s6, .s8], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (absTail y) TT := by
  unfold absTail
  exact RelCT.assoc (rel_seqR (rel_env [.s5, .s6, .s8] E₁ E₂ hsp hr ⟨_, by taint_decide⟩)
    (Runs.env E₁ [.t0, .a0, .a1, .a2] (by decide +kernel))
    (Runs.env E₂ [.t0, .a0, .a1, .a2] (by decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy)

/-- `absorbPad y`, for the `len` bytes at `P`. -/
theorem absorbPad_rel {P : Addr} {len : Nat} (hP₁ : Buf c σ₁ P len) (hP₂ : Buf c σ₂ P len)
    (h18₁ : σ₁.gpr .s5 = P) (h18₂ : σ₂.gpr .s5 = P) (h19₁ : σ₁.gpr .s6 = BitVec.ofNat 64 len)
    (h19₂ : σ₂.gpr .s6 = BitVec.ofNat 64 len) :
    RelCT isa (Eq2 σ₁ σ₂) (absorbPad y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s5, .s6]))
      (.block (updArgs y ++ [mov .a3 .s5, .shift .srl .d .a4 .s6 4])) h).isSome = true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold absorbPad
  refine rel_seqR (rel_env [.s5, .s6] E₁ E₂ hsp (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h18₁, h18₂]
      · rw [h19₁, h19₂]) t)
    (Runs.of_wp (absArgs_wp L E₁ hy hP₁ h18₁ h19₁)) (Runs.of_wp (absArgs_wp L E₂ hy hP₂ h18₂ h19₂))
    fun τ₁ τ₂ ⟨U₁, K₁⟩ ⟨U₂, K₂⟩ => ?_
  refine rel_seqR (rel_upd U₁ U₂ (by rw [K₁.2.1, K₂.2.1, hsp])) (upd_runs K₁.1 U₁) (upd_runs K₂.1 U₂)
    fun ρ₁ ρ₂ G₁ G₂ => ?_
  have a₁ := K₁.trans G₁
  have a₂ := K₂.trans G₂
  have q : ∀ r ∈ [Reg.s5, .s6], ρ₁.gpr r = ρ₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [a₁.2.2 .s5 (by simp), a₂.2.2 .s5 (by simp), h18₁, h18₂]
    · rw [a₁.2.2 .s6 (by simp), a₂.2.2 .s6 (by simp), h19₁, h19₂]
  refine rel_seqR (rel_env [.s5, .s6] G₁.1 G₂.1 (by rw [a₁.2.1, a₂.2.1, hsp]) q ⟨_, by taint_decide⟩)
    (Runs.of_wp (mask15_wp G₁.1)) (Runs.of_wp (mask15_wp G₂.1)) fun κ₁ κ₂ ⟨s8₁, F₁, sp₁, k₁⟩ ⟨s8₂, F₂, sp₂, k₂⟩ => ?_
  have hsp' : κ₁.sp = κ₂.sp := by rw [sp₁, sp₂, a₁.2.1, a₂.2.1, hsp]
  have q21 : κ₁.gpr .s8 = κ₂.gpr .s8 := by rw [s8₁, s8₂, q .s6 (by simp)]
  refine rel_iteZ q21 (rel_env [] F₁ F₂ hsp' (by simp) ⟨_, by taint_decide⟩) ?_
  refine absTail_rel L F₁ F₂ hsp' hy fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [k₁ .s5 (by simp), k₂ .s5 (by simp), q .s5 (by simp)]
  · rw [k₁ .s6 (by simp), k₂ .s6 (by simp), q .s6 (by simp)]
  · exact q21

/-- `aadHead y`, from two states that agree on the associated data. -/
theorem aadHead_rel (hr : ∀ r ∈ [Reg.s5, .s6], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (aadHead y) TT := by
  unfold aadHead
  exact RelCT.assoc (RelCT.assoc (RelCT.assoc (RelCT.assoc (rel_seqR
    (rel_env [.s5, .s6] E₁ E₂ hsp hr ⟨_, by taint_decide⟩)
    (Runs.env E₁ [.t0, .t1, .t2, .t3, .a0, .a1, .a2, .s5, .s6, .s7, .s8] (by decide +kernel))
    (Runs.env E₂ [.t0, .t1, .t2, .t3, .a0, .a1, .a2, .s5, .s6, .s7, .s8] (by decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy))))

/-- The associated data, if there is any. -/
theorem aadPart_rel (h18₁ : σ₁.gpr .s5 = c.A) (h18₂ : σ₂.gpr .s5 = c.A)
    (h19₁ : σ₁.gpr .s6 = BitVec.ofNat 64 c.al) (h19₂ : σ₂.gpr .s6 = BitVec.ofNat 64 c.al) :
    RelCT isa (Eq2 σ₁ σ₂) (.ite (.zero .s6) (.block []) (.seq (aadHead y) (absorbPad y))) TT := by
  have ha := L.al_lt
  refine rel_ite (eval_z h19₁ ha) (eval_z h19₂ ha) (fun _ => ?_) (fun hf => ?_)
  · exact rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩
  have h0 : c.al ≠ 0 := by simpa using hf
  have hA₁ := L.bufA E₁.perm
  have hA₂ := L.bufA E₂.perm
  refine rel_seqR (aadHead_rel L E₁ E₂ hsp hy fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h18₁, h18₂]
      · rw [h19₁, h19₂])
    (Runs.of_wp (aadHead_wp L E₁ hy hA₁ h18₁ h19₁ (by omega_using [h0])))
    (Runs.of_wp (aadHead_wp L E₂ hy hA₂ h18₂ h19₂ (by omega_using [h0]))) fun τ₁ τ₂ A₁ A₂ => ?_
  have hn1 : Proof.AesCcm.headLen c.al ≤ c.al := by unfold Proof.AesCcm.headLen; omega_using []
  exact absorbPad_rel L (E₁.of_pk A₁.abs.pk) (E₂.of_pk A₂.abs.pk) (by rw [A₁.abs.pk.sp, A₂.abs.pk.sp, hsp]) hy
    ((hA₁.drop hn1).of_eq A₁.abs.pk.rd A₁.abs.pk.wr) ((hA₂.drop hn1).of_eq A₂.abs.pk.rd A₂.abs.pk.wr)
    A₁.s5 A₂.s5 A₁.s6 A₂.s6

/-- `b0 y`, from two states that agree on the length of the associated data. -/
theorem b0_rel (hs6 : σ₁.gpr .s6 = σ₂.gpr .s6) : RelCT isa (Eq2 σ₁ σ₂) (b0 y) TT := by
  have t : ∃ h, (taint.check (Taint.ofRegs (envRegs ++ [.s6])) (.seq flagsSeg (.block (b0Seg y))) h).isSome =
      true := by
    rcases hy with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  unfold b0
  exact RelCT.assoc (rel_seqR (rel_env [.s6] E₁ E₂ hsp (by simpa using hs6) t)
    (Runs.env E₁ [.t0, .t1, .t2, .t3] (by rcases hy with rfl | rfl <;> decide +kernel)
      (hn := by rcases hy with rfl | rfl <;> decide +kernel))
    (Runs.env E₂ [.t0, .t1, .t2, .t3] (by rcases hy with rfl | rfl <;> decide +kernel)
      (hn := by rcases hy with rfl | rfl <;> decide +kernel))
    fun τ₁ τ₂ F₁ F₂ => updBlock_rel L F₁.1 F₂.1 (by rw [F₁.2, F₂.2, hsp]) hy)

/-- `mac y`. -/
theorem mac_rel (S₁ : Slots c σ₁.mem) (S₂ : Slots c σ₂.mem) : RelCT isa (Eq2 σ₁ σ₂) (mac y) TT := by
  unfold mac
  refine rel_seqR (rel_env [] E₁ E₂ hsp (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (aadLd_wp L E₁ S₁))
    (Runs.of_wp (aadLd_wp L E₂ S₂)) fun τ₁ τ₂ ⟨x18₁, x19₁, F₁, sp₁⟩ ⟨x18₂, x19₂, F₂, sp₂⟩ => ?_
  have hsp₁ : τ₁.sp = τ₂.sp := by rw [sp₁, sp₂, hsp]
  refine rel_seqR (b0_rel L F₁ F₂ hsp₁ hy (by rw [x19₁, x19₂])) (b0_runs L F₁ hy) (b0_runs L F₂ hy)
    fun κ₁ κ₂ B₁ B₂ => ?_
  have hsp₂ : κ₁.sp = κ₂.sp := by rw [B₁.2.1, B₂.2.1, hsp₁]
  have y18₁ : κ₁.gpr .s5 = c.A := by rw [B₁.2.2 .s5 (by simp), x18₁]
  have y18₂ : κ₂.gpr .s5 = c.A := by rw [B₂.2.2 .s5 (by simp), x18₂]
  have y19₁ : κ₁.gpr .s6 = BitVec.ofNat 64 c.al := by rw [B₁.2.2 .s6 (by simp), x19₁]
  have y19₂ : κ₂.gpr .s6 = BitVec.ofNat 64 c.al := by rw [B₂.2.2 .s6 (by simp), x19₂]
  refine rel_seqR (aadPart_rel L B₁.1 B₂.1 hsp₂ hy y18₁ y18₂ y19₁ y19₂)
    (Runs.of_wp (aad_wp L B₁.1 hy y18₁ y19₁)) (Runs.of_wp (aad_wp L B₂.1 hy y18₂ y19₂)) fun ρ₁ ρ₂ P₁ P₂ => ?_
  have G₁ := B₁.1.of_pk P₁.pk
  have G₂ := B₂.1.of_pk P₂.pk
  have hsp₃ : ρ₁.sp = ρ₂.sp := by rw [P₁.pk.sp, P₂.pk.sp, hsp₂]
  refine rel_seqR (rel_env [] G₁ G₂ hsp₃ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (dataArgs_wp G₁))
    (Runs.of_wp (dataArgs_wp G₂)) fun ω₁ ω₂ ⟨z18₁, z19₁, H₁, sp₁'⟩ ⟨z18₂, z19₂, H₂, sp₂'⟩ => ?_
  exact absorbPad_rel L H₁ H₂ (by rw [sp₁', sp₂', hsp₃]) hy (L.bufD H₁.perm) (L.bufD H₂.perm) z18₁ z18₂ z19₁ z19₂

end

end VG.Proof.AesCcm.RISCV64

end

end

/-!
# AES-CCM on RISCV64: constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments have the same public values (`args_two`). The entry loads `work`
from the stack, which the taint analysis takes as secret (it reads memory):
the block is split after the load, and the rest runs from `t1` and `t0`,
which hold `work` and the stack pointer in both runs (`entry_rel`). So do the
loads of the tag's address from its slot in `W`, before `tagOut` and `cmp`.
The other pieces are related by `MacCT.lean` and `CtrCT.lean` (`seal_rel`,
`open_rel`). `open` compares the tags and masks the plaintext without a
branch: whether it succeeds is not leaked.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.Impl.AesCcm.RISCV64 VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.Gather.RISCV64 (Eq2 TT rel_taint ct_of)
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm (length_bytesAt)

/-- Two runs with the same public arguments: both from the public values of
the first. -/
theorem args_two {σ₁ σ₂ : State} (A₂ : Args (cxOf σ₂) (σ₂.gpr .a2) σ₂)
    (hq : onePub σ₁ σ₂) : Args (cxOf σ₁) (σ₁.gpr .a2) σ₂ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  obtain hcx : cxOf σ₂ = cxOf σ₁ := by
    simp only [cxOf, q0, q1, q3, q4, q5, q6, q7, qa 0 (by decide), qa 1 (by decide), qa 2 (by decide)]
  rw [hcx, ← q2] at A₂
  exact A₂

/-- `work` and the stack pointer. -/
theorem entryLd_wp {c : Cx} {N : Addr} {s : State} (Ar : Args c N s) :
    WP isa (.block [.addSp .t0 0, .load .d .t1 .t0 16]) s fun s' =>
      s'.gpr .t1 = c.W ∧ s'.gpr .t0 = s.sp ∧ s'.sp = s.sp := by
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  obtain t0₁ : s₁.gpr .t0 = s.sp := by rw [u₁.gpr, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 2) (by decide) (by rw [t0₁]; rfl) (Spill.al8 Ar.spal (by omega_using []))
    (by rw [u₁.rd, u₁.wr, stackArgAddr_succ]; exact in_off Ar.argsC (by omega_using []) (by decide))
    fun s₂ u₂ => WP.block_nil ⟨by rw [u₂.gpr, u₁.mem, ← Ar.w]; rfl, by rw [u₂.other _ (by decide), t0₁],
      by rw [u₂.sp, u₁.sp]⟩

/-- The entry in two runs. -/
theorem entry_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂)
    (hsp : σ₁.sp = σ₂.sp) : RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  have e : entry = [.addSp .t0 0, .load .d .t1 .t0 16] ++ entry.drop 2 := rfl
  rw [e]
  refine RelCT.block_append (rel_seqR (rel_taint [] hsp (by simp) (by taint_decide))
    (Runs.of_wp (entryLd_wp A₁)) (Runs.of_wp (entryLd_wp A₂)) fun τ₁ τ₂ ⟨a₁, b₁, c₁⟩ ⟨a₂, b₂, c₂⟩ => ?_)
  refine rel_taint [.t1, .t0] (by rw [c₁, c₂, hsp]) (fun r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂, hsp]

/-- The tag's address, from its slot. -/
theorem ldT_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .s5 .s1 tagO]) s fun s' => s'.gpr .s5 = c.T ∧ Env c s' ∧ s'.sp = s.sp :=
  wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, S.tag], E.of_pk (PK.ofUpd u₁), u₁.sp⟩

/-- `tagOut`'s arguments. -/
theorem tagOutBlk_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) (S : Slots c s.mem) :
    WP isa (.block [.load .d .a1 .s1 tagO, Impl.AesCbc.RISCV64.mov .a0 .s1, Impl.AesCbc.RISCV64.mov .a2 .s2]) s
      fun s' => s'.gpr .a1 = c.T ∧ s'.gpr .a0 = c.W ∧ s'.gpr .a2 = BitVec.ofNat 64 c.tl ∧ Env c s' ∧
        s'.sp = s.sp := by
  refine wp_ld (a := c.W + BitVec.ofNat 64 240) (by decide) (by rw [E.s1]; rfl) (L.alW (by decide) (by decide))
    (E.perm.wR (by decide)) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  obtain pk₃ : PK s s₃ := (PK.ofUpd u₁).trans ((PK.ofUpd u₂).trans (PK.ofUpd u₃))
  exact ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, S.tag],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s1],
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), E.s2], E.of_pk pk₃, pk₃.sp⟩

/-- `vg_aes_ccm_seal` in two runs. -/
theorem seal_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂) (hsp : σ₁.sp = σ₂.sp)
    (hT₁ : Covers [⟨c.T, c.tl⟩] σ₁.wr) (hT₂ : Covers [⟨c.T, c.tl⟩] σ₂.wr) :
    RelCT isa (Eq2 σ₁ σ₂) «seal» TT := by
  have L := A₁.lay
  unfold «seal»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  obtain h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (rel_env [.a2, .a3] En.env En'.env h₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [En.a2, En'.a2]
      · rw [En.a3, En'.a3]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (ctrs_wp L En.env (A₁.nonce.of_eq En.rd En.wr) En.a2 En.a3))
    (Runs.of_wp (ctrs_wp L En'.env (A₂.nonce.of_eq En'.rd En'.wr) En'.a2 En'.a3))
    fun s₂ t₂ ⟨pk₂, f₂, c₂⟩ ⟨pk₂', f₂', c₂'⟩ => ?_
  obtain E₂ := En.env.of_pk pk₂
  obtain E₂' := En'.env.of_pk pk₂'
  obtain h₂ : s₂.sp = t₂.sp := by rw [pk₂.sp, pk₂'.sp, h₁]
  obtain hnl : ∀ m, (bytesAt m N c.nl).length = c.nl := fun m => length_bytesAt _ _ _
  refine rel_seqR (mac_rel L E₂ E₂' h₂ (.inl rfl) (En.slots.mut L (f₂.sub (c0_mut c)))
      (En'.slots.mut L (f₂'.sub (c0_mut c))))
    (Runs.of_wp (mac_wp L E₂ (En.slots.mut L (f₂.sub (c0_mut c))) (hnl _) c₂ (.inl rfl)))
    (Runs.of_wp (mac_wp L E₂' (En'.slots.mut L (f₂'.sub (c0_mut c))) (hnl _) c₂' (.inl rfl)))
    fun s₃ t₃ M M' => ?_
  obtain E₃ := E₂.of_pk M.pk
  obtain E₃' := E₂'.of_pk M'.pk
  obtain h₃ : s₃.sp = t₃.sp := by rw [M.pk.sp, M'.pk.sp, h₂]
  have fM := M.frame
  have fM' := M'.frame
  rw [macR_list] at fM fM'
  obtain c₃ := (Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide)).trans c₂
  obtain c₃' := (Proof.Cmac.bytesAt_frame fM' (w_keep L (by decide) (by decide)) (by decide)).trans c₂'
  refine rel_seqR (tag_rel L E₃ E₃' h₃ (.inl rfl)) (Runs.of_wp (tag_wp L E₃ (hnl _) c₃ (.inl rfl)))
    (Runs.of_wp (tag_wp L E₃' (hnl _) c₃' (.inl rfl))) fun s₄ t₄ ⟨pk₄, _, f₄, _⟩ ⟨pk₄', _, f₄', _⟩ => ?_
  obtain E₄ := E₃.of_pk pk₄
  obtain E₄' := E₃'.of_pk pk₄'
  obtain h₄ : s₄.sp = t₄.sp := by rw [pk₄.sp, pk₄'.sp, h₃]
  have f₄l := f₄
  have f₄l' := f₄'
  rw [ctrR_list] at f₄l f₄l'
  obtain c₄ := (Proof.Cmac.bytesAt_frame f₄l (w_keep L (by decide) (by decide)) (by decide)).trans c₃
  obtain c₄' := (Proof.Cmac.bytesAt_frame f₄l' (w_keep L (by decide) (by decide)) (by decide)).trans c₃'
  refine rel_seqR (ctr_rel L E₄ E₄' h₄ (hnl _) (hnl _) c₄ c₄') (Runs.of_wp (ctr_wp L E₄ (hnl _) c₄))
    (Runs.of_wp (ctr_wp L E₄' (hnl _) c₄')) fun s₅ t₅ ⟨pk₅, f₅, _⟩ ⟨pk₅', f₅', _⟩ => ?_
  obtain E₅ := E₄.of_pk pk₅
  obtain E₅' := E₄'.of_pk pk₅'
  obtain h₅ : s₅.sp = t₅.sp := by rw [pk₅.sp, pk₅'.sp, h₄]
  obtain S₅ := En.slots.mut L ((((f₂.sub (c0_mut c)).trans (M.frame.sub (macR_mut (.inl rfl)))).trans
    (f₄.sub (ctrR_mut c (.inl rfl)))).trans (f₅.sub (crR_mut c)))
  obtain S₅' := En'.slots.mut L ((((f₂'.sub (c0_mut c)).trans (M'.frame.sub (macR_mut (.inl rfl)))).trans
    (f₄'.sub (ctrR_mut c (.inl rfl)))).trans (f₅'.sub (crR_mut c)))
  obtain wr₅ : s₅.wr = σ₁.wr := by rw [pk₅.wr, pk₄.wr, M.pk.wr, pk₂.wr, En.wr]
  obtain wr₅' : t₅.wr = σ₂.wr := by rw [pk₅'.wr, pk₄'.wr, M'.pk.wr, pk₂'.wr, En'.wr]
  refine rel_seqR ?_ (Runs.of_wp (tagOut_wp L E₅ S₅ (by rw [wr₅]; exact hT₁)))
    (Runs.of_wp (tagOut_wp L E₅' S₅' (by rw [wr₅']; exact hT₂))) fun s₆ t₆ ⟨pk₆, _⟩ ⟨pk₆', _⟩ => ?_
  · unfold tagOut
    refine rel_seqR (rel_env [] E₅ E₅' h₅ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (tagOutBlk_wp L E₅ S₅))
      (Runs.of_wp (tagOutBlk_wp L E₅' S₅')) fun τ₁ τ₂ ⟨a₁, b₁, c₁', F₁, sp₁⟩ ⟨a₂, b₂, c₂', F₂, sp₂⟩ => ?_
    refine rel_env [.a0, .a2, .a1] F₁ F₂ (by rw [sp₁, sp₂, h₅]) (fun r hr => ?_) ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [c₁', c₂']
    · rw [a₁, a₂]
  · exact rel_env [] (E₅.of_pk pk₆) (E₅'.of_pk pk₆') (by rw [pk₆.sp, pk₆'.sp, h₅]) (by simp) ⟨_, by taint_decide⟩

/-- `vg_aes_ccm_open` in two runs. -/
theorem open_rel {c : Cx} {N : Addr} {σ₁ σ₂ : State} (A₁ : Args c N σ₁) (A₂ : Args c N σ₂) (hsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) «open» TT := by
  have L := A₁.lay
  unfold «open»
  refine rel_seqR (entry_rel A₁ A₂ hsp) (Runs.of_wp (entry_wp A₁)) (Runs.of_wp (entry_wp A₂))
    fun s₁ t₁ En En' => ?_
  obtain h₁ : s₁.sp = t₁.sp := by rw [En.sp, En'.sp, hsp]
  refine rel_seqR (rel_env [.a2, .a3] En.env En'.env h₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [En.a2, En'.a2]
      · rw [En.a3, En'.a3]) ⟨_, by taint_decide⟩)
    (Runs.of_wp (ctrs_wp L En.env (A₁.nonce.of_eq En.rd En.wr) En.a2 En.a3))
    (Runs.of_wp (ctrs_wp L En'.env (A₂.nonce.of_eq En'.rd En'.wr) En'.a2 En'.a3))
    fun s₂ t₂ ⟨pk₂, f₂, c₂⟩ ⟨pk₂', f₂', c₂'⟩ => ?_
  obtain E₂ := En.env.of_pk pk₂
  obtain E₂' := En'.env.of_pk pk₂'
  obtain h₂ : s₂.sp = t₂.sp := by rw [pk₂.sp, pk₂'.sp, h₁]
  obtain hnl : ∀ m, (bytesAt m N c.nl).length = c.nl := fun m => length_bytesAt _ _ _
  refine rel_seqR (ctr_rel L E₂ E₂' h₂ (hnl _) (hnl _) c₂ c₂') (Runs.of_wp (ctr_wp L E₂ (hnl _) c₂))
    (Runs.of_wp (ctr_wp L E₂' (hnl _) c₂')) fun s₃ t₃ ⟨pk₃, f₃, _⟩ ⟨pk₃', f₃', _⟩ => ?_
  obtain E₃ := E₂.of_pk pk₃
  obtain E₃' := E₂'.of_pk pk₃'
  obtain h₃ : s₃.sp = t₃.sp := by rw [pk₃.sp, pk₃'.sp, h₂]
  obtain g₁₃ := (f₂.sub (c0_mut c)).trans (f₃.sub (crR_mut c))
  obtain g₁₃' := (f₂'.sub (c0_mut c)).trans (f₃'.sub (crR_mut c))
  obtain c₃ := (Proof.Cmac.bytesAt_frame f₃ (crR_disj L (.inl (by decide))) (by decide)).trans c₂
  obtain c₃' := (Proof.Cmac.bytesAt_frame f₃' (crR_disj L (.inl (by decide))) (by decide)).trans c₂'
  refine rel_seqR (mac_rel L E₃ E₃' h₃ (.inr rfl) (En.slots.mut L g₁₃) (En'.slots.mut L g₁₃'))
    (Runs.of_wp (mac_wp L E₃ (En.slots.mut L g₁₃) (hnl _) c₃ (.inr rfl)))
    (Runs.of_wp (mac_wp L E₃' (En'.slots.mut L g₁₃') (hnl _) c₃' (.inr rfl))) fun s₄ t₄ M M' => ?_
  obtain E₄ := E₃.of_pk M.pk
  obtain E₄' := E₃'.of_pk M'.pk
  obtain h₄ : s₄.sp = t₄.sp := by rw [M.pk.sp, M'.pk.sp, h₃]
  have fM := M.frame
  have fM' := M'.frame
  rw [macR_list] at fM fM'
  obtain c₄ := (Proof.Cmac.bytesAt_frame fM (w_keep L (by decide) (by decide)) (by decide)).trans c₃
  obtain c₄' := (Proof.Cmac.bytesAt_frame fM' (w_keep L (by decide) (by decide)) (by decide)).trans c₃'
  refine rel_seqR (tag_rel L E₄ E₄' h₄ (.inr rfl)) (Runs.of_wp (tag_wp L E₄ (hnl _) c₄ (.inr rfl)))
    (Runs.of_wp (tag_wp L E₄' (hnl _) c₄' (.inr rfl))) fun s₅ t₅ ⟨pk₅, _, f₅, _⟩ ⟨pk₅', _, f₅', _⟩ => ?_
  obtain E₅ := E₄.of_pk pk₅
  obtain E₅' := E₄'.of_pk pk₅'
  obtain h₅ : s₅.sp = t₅.sp := by rw [pk₅.sp, pk₅'.sp, h₄]
  obtain S₅ := En.slots.mut L ((g₁₃.trans (M.frame.sub (macR_mut (.inr rfl)))).trans (f₅.sub (ctrR_mut c (.inr rfl))))
  obtain S₅' := En'.slots.mut L ((g₁₃'.trans (M'.frame.sub (macR_mut (.inr rfl)))).trans
    (f₅'.sub (ctrR_mut c (.inr rfl))))
  refine rel_seqR (rel_env [] E₅ E₅' h₅ (by simp) ⟨_, by taint_decide⟩) (Runs.of_wp (ldT_wp L E₅ S₅))
    (Runs.of_wp (ldT_wp L E₅' S₅')) fun s₆ t₆ ⟨a₁, F₁, sp₁⟩ ⟨a₂, F₂, sp₂⟩ => ?_
  exact rel_env [.s5] F₁ F₂ (by rw [sp₁, sp₂, h₅]) (by simp [a₁, a₂]) ⟨_, by taint_decide⟩

theorem seal_ct : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» :=
  ct_of fun σ₁ σ₂ h₁ h₂ hq => by
    obtain B₁ := args_of_seal h₁
    obtain B₂ := args_of_seal h₂
    obtain A₂ := args_two B₂.1 hq
    obtain ⟨-, -, -, -, -, -, -, -, qsp, qa⟩ := hq
    exact seal_rel B₁.1 A₂ qsp B₁.2 (by
      simpa only [cxOf, qa 0 (by decide), qa 1 (by decide)] using B₂.2)

theorem open_ct : ConstantTime isa openRISCV64.pre openRISCV64.pub «open» :=
  ct_of fun _ _ h₁ h₂ hq => open_rel (args_of_open h₁) (args_two (args_of_open h₂) hq.1)
    hq.1.2.2.2.2.2.2.2.2.1

end VG.Proof.AesCcm.RISCV64

end

end

/-!
# AES-CCM on RISCV64: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, states satisfying the preconditions, and the shared contracts of
`Spec/Ccm/Contract.lean` with the working space as a last argument
(`Proof/AesCcm/Scratch.lean`), with no stack: a call (`jal`) stores nothing
in memory, and each function saves the return address in the working
space. Then the code in a frame that allocates the working space
(`Verified.stackScratchArgs`): it is the third stack argument, after `tag`
and `tag_len`, so the frame of 2592 bytes holds a copy of those two, the
address of the working space and the working space.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.Impl.AesCcm.RISCV64

/-! ## Correctness and constant time -/

theorem seal_correct (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := seal_wp hs
  exact ⟨t, s', he, ha, hp⟩

theorem open_correct (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := open_wp hs
  exact ⟨t, s', he, ha, hp⟩

/-- A state satisfying the precondition of `vg_aes_ccm_seal`: a 7-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at 0, the
three at `sp`. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 7 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8001 then 0x50 else bif Nat.beq a.toNat 0x8008 then 4 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ccm_open`: as `sealSat`,
with the tag read only. -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 24⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified :
    Verified RISCV64.target «seal» (Proof.AesCcm.sealScratchContract RISCV64.abi) :=
  Verified.of_correct seal_correct seal_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega_arith
        post := by
          sig_implies_post [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesCcm.sealScratchContract, Proof.AesCcm.sealScratchSig, Spec.Ccm.sealPre,
            Proof.AesCcm.sealRoundsPost, sealRISCV64, sealPre, oneLay, onePub, args, rounds, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
            [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

theorem open_verified :
    Verified RISCV64.target «open» (Proof.AesCcm.openScratchContract RISCV64.abi) :=
  Verified.of_correct open_correct open_ct
      { pre := by
          intro s h
          sig_pre [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openRISCV64, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range,
            List.range.loop] at h
          sig_split h
          sig_reduce [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openRISCV64, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range,
            List.range.loop]
          sig_and_intros
          sig_close
          all_goals first
            | with_reducible assumption
            | sig_disjoint_symm
            | omega
            | bv_omega_arith
        post := by
          sig_implies_post [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openRISCV64, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range,
            List.range.loop]
        pub := by
          sig_implies_pub [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openRISCV64, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range,
            List.range.loop]
        sat := by
          sig_implies_sat [Proof.AesCcm.openScratchContract, Proof.AesCcm.openScratchSig, Spec.Ccm.openPre,
            Proof.AesCcm.openRoundsPost, Spec.Ccm.openLeak, openRISCV64, openPre, oneLay, onePub, openRes, openLeak, args,
            rounds, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range,
            List.range.loop]
            [openSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openSat }

/-! ## The working space on the stack -/

/-- A state satisfying `vg_aes_ccm_seal`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesCcm.sealRoundsContract RISCV64.abi 2592).pre s := by
  implies_sat [Proof.AesCcm.sealRoundsContract, Spec.Ccm.sealSig, Spec.Ccm.sealPre, Proof.AesCcm.sealRoundsPost,
    RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range,
    List.range.loop] [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using sealFrameSat

theorem seal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «seal»)
      (Proof.AesCcm.sealRoundsContract RISCV64.abi 2592) :=
  Verified.stackScratchArgs (sig := Spec.Ccm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.sealPre RISCV64.abi.ptrBits)
    (post := Proof.AesCcm.sealRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592) (m := 2)
    seal_verified (by decide) (by decide) (Proof.AesCcm.sealPre_local _) (Proof.AesCcm.sealPost_local _)
    (Proof.AesCcm.sealPostOut_local _) sealFrameSat_pre

/-- A state satisfying `vg_aes_ccm_open`'s precondition, without the working
space: `tag` and `tag_len`, its two stack arguments. -/
def openFrameSat : State :=
  { openSat with rd := [⟨0x1000, 240⟩, ⟨0x2000, 7⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x8000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesCcm.openRoundsContract RISCV64.abi 2592).pre s := by
  implies_sat [Proof.AesCcm.openRoundsContract, Spec.Ccm.openSig, Spec.Ccm.openPre, Proof.AesCcm.openRoundsPost,
    Spec.Ccm.openLeak, RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr,
    List.getD, List.range, List.range.loop] [openFrameSat, openSat, sealSat, stackArg, stackArgAddr,
    Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «open»)
      (Proof.AesCcm.openRoundsContract RISCV64.abi 2592) :=
  Verified.stackScratchArgs (sig := Spec.Ccm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Ccm.openPre RISCV64.abi.ptrBits)
    (post := Proof.AesCcm.openRoundsPost RISCV64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 2592) (m := 2)
    (leak := some (Spec.Ccm.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesCcm.openPre_local _) (Proof.AesCcm.openPost_local _)
    (Proof.AesCcm.openPostOut_local _) openFrameSat_pre (hleak := Proof.AesCcm.openLeak_local _)

end VG.Proof.AesCcm.RISCV64

/-! ## AES-CCM on RISC-V, without secret residue

`vg_aes_ccm_seal` and `vg_aes_ccm_open`, each followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.scrubOf`), which clears the
caller-saved registers and the whole 2592-byte frame (`withStackScratchArgs`)
that holds their working space, the key schedule and their callees' working
space among it: the residue analysis (`RISCV64.rtaint`) finds that all of it
may hold secrets. Their postconditions read the memory on return only within
the data and the tag, as on PPC64LE (`Proof/AesCcm/PPC64LE/Scrub.lean`). -/

namespace VG.Proof.AesCcm.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.AesCcm.RISCV64

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ccm.sealContract RISCV64.abi stack) (Spec.Ccm.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of0 hb.2.2.2.1 (by simp), bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ccm.openContract RISCV64.abi stack) (Spec.Ccm.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ccm.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ccm.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ccm.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (by simp)]
      exact h key hk

/-- `Spec.Ccm.sealApi`. -/
def sealReg : Registration Spec.Ccm.sealApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesCcm.RISCV64.«seal»
      verified := Proof.AesCcm.seal_keyed seal_framed }
    (sealOut _)

/-- `Spec.Ccm.openApi`. -/
def openReg : Registration Spec.Ccm.openApi RISCV64.target :=
  scrubOf {
      code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesCcm.RISCV64.«open»
      verified := Proof.AesCcm.open_keyed open_framed }
    (openOut _)

end VG.Proof.AesCcm.RISCV64.Scrub
