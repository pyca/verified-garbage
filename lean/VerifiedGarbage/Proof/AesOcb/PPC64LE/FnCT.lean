module

meta import VerifiedGarbage.Impl.AesOcb.PPC64LE
meta import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Body
import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Hash
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneEntry
meta import VerifiedGarbage.Proof.Ocb.Bytes
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Args
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Spec.Ocb
public import VerifiedGarbage.Spec.TripleDes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Aes.PPC64LE.Blocks
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Args
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Spec.Ocb
meta import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Hash
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Nonce
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Words
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
meta import VerifiedGarbage.Proof.AesOcb.PPC64LE.Nonce
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Taint
public meta import Lean.Elab.Tactic.Basic
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Taint

/-! ### `AesOcb.PPC64LE.CTBase`, which only this module used -/

section

/-!
# AES-OCB on PPC64LE: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2 σ₁ σ₂`) piece by piece, as on AArch64
(`Proof/AesOcb/AArch64/CTBase.lean`): the code between calls by the taint
analysis, from the registers the environments fix to the same public values
in both runs (`pubR`: the arguments, `W` and the key context) and others the
correctness proofs pin (`rel_env`); each call of `vg_aes_encrypt_blocks` or
`vg_aes_decrypt_blocks` with the same arguments in both runs
(`callBlocks_rel`); a branch both runs take the same way (`rel_ite`); and the
next piece from the states the correctness proofs describe (`rel_seq`), or,
after code without calls that writes none of the registers the environment
fixes, from the environment alone (`rel_seqEnv`). The environments of the
two runs fix their registers to values `V₁` and `V₂` that agree on `pubR`
(`Agree`). The taint analysis takes memory as secret, so a block that loads a
public value (a count kept in `W`) and uses it as an address or a count is
split after the load.
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Proof.AesGcm.PPC64LE (frozen Keeps)

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hsp : σ₁.sp = σ₂.sp)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) (hc : ∃ h, (VG.Taint.check taint (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT := by
  obtain ⟨_, hc⟩ := hc
  exact RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hsp, fun r h' => hr r (Taint.mem_ofRegs.mp h')⟩) hc

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT :=
  RelCT.block_nil fun _ _ _ => trivial

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- Two runs from states related by `P`, from each pair. -/
theorem rel_of_pt {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, P σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c Q) : RelCT isa P c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

/-- Then: the next piece, from what holds of every run of the first. -/
theorem rel_seqE {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (hF₁ : ∀ t s', Exec isa c₁ σ₁ t s' → F₁ s')
    (hF₂ : ∀ t s', Exec isa c₁ σ₂ t s' → F₂ s')
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) : RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) (fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => ?_) (rel_of_pt fun τ₁ τ₂ h =>
    h₂ τ₁ τ₂ h.1 h.2)
  obtain ⟨rfl, rfl⟩ := hp
  exact ⟨(h₁ _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hF₁ _ _ e₁, hF₂ _ _ e₂⟩

/-! ## The public registers -/

/-- The registers that hold public values throughout: the nonce's length,
the tag and its length, the associated data and its length, the data and its
length, the rounds, the key context and `W`. -/
abbrev pubR : List Reg := [.r18, .r19, .r20, .r21, .r22, .r23, .r27, .r28, .r29, .r31]

/-- The values the environments of two runs fix agree on the public registers. -/
def Agree (V₁ V₂ : Reg → BitVec 64) : Prop := ∀ r ∈ pubR, V₁ r = V₂ r

theorem pubR_frozen : ∀ r ∈ pubR, r ∈ frozen := by decide

/-- Two states in environments that agree, on a public register. -/
theorem Agree.gpr {V₁ V₂ : Reg → BitVec 64} {sp₁ sp₂ : Addr} {σ₁ σ₂ : State} (hV : Agree V₁ V₂)
    (E₁ : Env V₁ sp₁ σ₁) (E₂ : Env V₂ sp₂ σ₂) {r : Reg} (hr : r ∈ pubR) : σ₁.gpr r = σ₂.gpr r := by
  rw [E₁.fr r (pubR_frozen r hr), E₂.fr r (pubR_frozen r hr), hV r hr]

/-- Code the taint analysis checks, from the registers `rs` the two runs
agree on and the public registers. -/
theorem rel_env {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {σ₁ σ₂ : State} {c : Prog isa}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (hV : Agree V₁ V₂) (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check taint (Taint.ofRegs (rs ++ pubR)) c h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  rel_taint _ (by rw [E₁.sp, E₂.sp]) (fun r hr' => by
    rcases List.mem_append.mp hr' with h | h
    · exact hr r h
    · exact hV.gpr E₁ E₂ h) hc

/-! ## Code without calls -/

/-- Code without calls whose instructions write only `rs` keeps the other
registers and the permissions. -/
theorem exec_keep {c : Prog isa} (rs : List Reg) (hc : writesOnly rs c = true) (hn : c.noCalls = true)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : Keep rs s s' ∧ s'.sp = s.sp := by
  refine ⟨⟨fun r hr => Exec.gpr (fun i hi => ?_) h (.inl hn), (Exec.rdwr h).1, (Exec.rdwr h).2.1⟩,
    (Exec.rdwr h).2.2⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have hh := hc i hi
  intro hd
  rw [hd] at hh
  exact hr (List.contains_iff_mem.mp hh)

/-- An environment, after code without calls that writes none of its registers. -/
theorem Env.exec {V : Reg → BitVec 64} {sp : Addr} {s s' : State} {c : Prog isa} {t : List Leak} (E : Env V sp s)
    (h : Exec isa c s t s') (rs : List Reg) (hc : writesOnly rs c = true) (hn : c.noCalls = true)
    (hd : ∀ r ∈ frozen, r ∉ rs := by decide) : Env V sp s' :=
  let ⟨k, sp⟩ := exec_keep rs hc hn h
  E.others k.1 sp k.2.1 k.2.2 hd

/-- Then: the next piece, in the environments, after code without calls that
writes only `rs`, none of their registers. -/
theorem rel_seqEnv {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {c₁ c₂ : Prog isa} {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (rs : List Reg)
    (hc : writesOnly rs c₁ = true) (hn : c₁.noCalls = true) (hd : ∀ r ∈ frozen, r ∉ rs)
    (h₂ : ∀ τ₁ τ₂, Env V₁ sp τ₁ → Env V₂ sp τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT :=
  rel_seqE h₁ (fun _ _ h => E₁.exec h rs hc hn hd) (fun _ _ h => E₂.exec h rs hc hn hd) h₂

/-! ## Calls -/

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .r29) (V₁ .r31)) (hV : Agree V₁ V₂)
include L hV

theorem Agree.lay : Lay (V₂ .r29) (V₂ .r31) := by
  rw [← hV .r29 (by decide), ← hV .r31 (by decide)]; exact L

/-- A call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on the same
`k` blocks at `D` in both runs. -/
theorem callBlocks_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LEF f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LEF f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LEF f).pre (Proof.Aes.blocksPPC64LEF f).pub c)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R) {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {args : List Instr} (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check taint (Taint.ofRegs (rs ++ pubR)) (.block (callArgs ++ args)) h).isSome = true)
    {D : Addr} {k : Nat}
    (ha₁ : ∀ s₁, (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₁.gpr r = σ₁.gpr r) → Keeps σ₁ s₁ → ArgsOk args s₁ D k)
    (ha₂ : ∀ s₁, (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₁.gpr r = σ₂.gpr r) → Keeps σ₂ s₁ → ArgsOk args s₁ D k)
    (hD₁ : Dst (V₁ .r29) (V₁ .r31) σ₁ D k) (hD₂ : Dst (V₁ .r29) (V₁ .r31) σ₂ D k) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block (callArgs ++ args)) (.call name c)) TT := by
  have e29 := hV .r29 (by decide)
  have e31 := hV .r31 (by decide)
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  refine rel_seq (rel_env E₁ E₂ hV rs hr hc) (callArgs_ok L hR h28 E₁ ha₁ hD₁)
    (callArgs_ok (hV.lay L) hR h28₂ E₂ ha₂ (by rw [← e29, ← e31]; exact hD₂)) fun τ₁ τ₂ h₁ h₂ => ?_
  refine blk_rel ok ct fun a b hab => ?_
  obtain ⟨rfl, rfl⟩ := hab
  rw [← e29] at h₂
  exact ⟨V₁ .r29, D, R, k, h₁.1, h₂.1,
    by rw [h₁.2.2.sp, h₂.2.2.sp, E₁.sp, E₂.sp]⟩

/-- `encOne d`, in two runs. -/
theorem encOne_rel {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R) {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {d : Nat} (hd : d + 16 ≤ 512)
    (hc : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR))
      (.block (callArgs ++ ([.addi .r5 .r31 d, .li .r6 1] : List Instr))) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (encOne d) TT :=
  callBlocks_rel L hV Proof.Aes.PPC64LE.encryptBlocksF_correct Proof.Aes.PPC64LE.encryptBlocksF_ct hR h28 E₁ E₂ []
    (fun _ h => absurd h List.not_mem_nil) hc
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E₁.r31]) (by omega_using [hd]))
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E₂.r31, ← hV .r31 (by decide)])
      (by omega_using [hd]))
    (dstW L E₁.perm (by omega_using [hd])) (dstW L (by rw [hV .r29 (by decide), hV .r31 (by decide)]; exact E₂.perm) (by omega_using [hd]))

end

/-- Proves `∀ r ∈ [r₁, …], σ₁.gpr r = σ₂.gpr r` by rewriting each side with `ts`. -/
tactic_template "agree_ppc" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  plain_simp_names simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true,
    and_self, $ts,*])

end VG.Proof.AesOcb.PPC64LE

end

end

/-! ### `AesOcb.PPC64LE.FrontCT`, which this module and modules that import it used -/

section

/-! ### `AesOcb.PPC64LE.HashCT`, which only this module used -/

section

/-!
# AES-OCB on PPC64LE: `HASH` is constant time

Untrusted: everything here is checked by Lean. The two runs hash associated
data of the same length at the same address `A`. The counts of blocks a
chunk loads from `W` (the blocks left, at `W + hlO`, and the chunk's, at
`W + cnO`), which the taint analysis takes as secret, are the same in both
runs by the correctness proofs (`HInv`, `FillInv`), which also pin the
pointer `r24` and the index `r26`: the blocks are split after each load
(`chunkLd_ok`, `sumArgs_ok`). Each chunk fills its buffer and adds it to the
sum by code the taint analysis checks, with the call between on the same
arguments (`chunk_rel`); both runs are at the same chunk at each iteration
(`hashLoop_rel`); the rest, if any, likewise (`hashRest_rel`). As on AArch64
(`Proof/AesOcb/AArch64/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Ocb (Block Cipher)
open VG.Proof.AesGcm.PPC64LE (frozen Keeps eval_zero)

/-- An environment, after code that writes only `a` and `b` among the registers. -/
theorem Env.keep2 {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (E : Env V sp s) {a b : Reg}
    (g : ∀ r, r ≠ a → r ≠ b → s'.gpr r = s.gpr r) (k : Keeps s s') (ha : a ∉ frozen := by decide)
    (hb : b ∉ frozen := by decide) : Env V sp s' :=
  E.keep (fun r hr => g r (fun h => ha (h ▸ hr)) (fun h => hb (h ▸ hr))) k.sp k.rd k.wr

/-- An environment, after code that writes only `a`, `b` and `c` among the registers. -/
theorem Env.keep3 {V : Reg → BitVec 64} {sp : Addr} {s s' : State} (E : Env V sp s) {a b c : Reg}
    (g : ∀ r, r ≠ a → r ≠ b → r ≠ c → s'.gpr r = s.gpr r) (k : Keeps s s') (ha : a ∉ frozen := by decide)
    (hb : b ∉ frozen := by decide) (hc : c ∉ frozen := by decide) : Env V sp s' :=
  E.keep (fun r hr => g r (fun h => ha (h ▸ hr)) (fun h => hb (h ▸ hr)) (fun h => hc (h ▸ hr))) k.sp k.rd k.wr

/-- What the second run may access, with the first run's key context and `W`. -/
theorem Agree.perm {V₁ V₂ : Reg → BitVec 64} (hV : Agree V₁ V₂) {s : State} (h : Perm (V₂ .r29) (V₂ .r31) s) :
    Perm (V₁ .r29) (V₁ .r31) s := by
  rw [hV .r29 (by decide), hV .r31 (by decide)]; exact h

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (hV : Agree V₁ V₂)
include hV

/-- The rest of the associated data, in two runs from the same `r24` and `r25`. -/
theorem hashRest_rel (L : Lay (V₁ .r29) (V₁ .r31)) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h28 : V₁ .r28 = BitVec.ofNat 64 R) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂)
    (h24 : σ₁.gpr .r24 = σ₂.gpr .r24) (h25 : σ₁.gpr .r25 = σ₂.gpr .r25) :
    RelCT isa (Eq2 σ₁ σ₂) hashRest TT := by
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  unfold hashRest
  refine RelCT.assoc (RelCT.assoc (rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [.r24, .r25] (by agree_ppc [h24, h25])
    ⟨_, by taint_decide⟩) [.r0, .r3, .r4, .r5, .r6] (by decide +kernel) (by decide +kernel) (by decide)
    fun τ₁ τ₂ F₁ F₂ => ?_))
  refine rel_seq (encOne_rel L hV hR h28 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR h28 F₁ (by decide))
    (encOne_ok (hV.lay L) hR h28₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) ⟨_, by taint_decide⟩

variable {D : Addr} {n R : Nat} {A : Addr} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {a₁ a₂ : List Byte}
  {s₁ s₂ : State} (C₁ : HCtx (V₁ .r29) (V₁ .r31) D n R ciph₁ l₁ A a₁ s₁)
  (C₂ : HCtx (V₂ .r29) (V₂ .r31) D n R ciph₂ l₂ A a₂ s₂) (h28 : V₁ .r28 = BitVec.ofNat 64 R)
  (hlen : a₂.length = a₁.length)
include C₁ C₂ h28 hlen

/-- A chunk, in two runs at the same block `j`. -/
theorem chunk_rel {τ₁ τ₂ : State} {j : Nat} (H₁ : HInv V₁ sp ciph₁ l₁ A a₁ s₁ τ₁ j)
    (H₂ : HInv V₂ sp ciph₂ l₂ A a₂ s₂ τ₂ j) (hj : j < a₁.length / 16) : RelCT isa (Eq2 τ₁ τ₂) hashChunk TT := by
  have hs := C₁.short
  have L := C₁.lay
  have e31 := hV .r31 (by decide)
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  have hl₂ := H₂.hl
  rw [hlen] at hl₂
  unfold hashChunk
  refine RelCT.assoc (rel_seq ?_ (chunkHead_ok (L := a₁.length / 16 - j) H₁.env.r31 H₁.env.perm.w (by omega_arith) H₁.hl)
    (chunkHead_ok (L := a₁.length / 16 - j) H₂.env.r31 H₂.env.perm.w (by omega_arith) hl₂)
    fun t₁ t₂ ⟨h25₁, g₁, k₁⟩ ⟨h25₂, g₂, k₂⟩ => ?_)
  · -- the number of blocks of the chunk, from those left
    refine rel_seq (rel_env H₁.env H₂.env hV [] (by agree_ppc []) ⟨_, by taint_decide⟩)
      (chunkLd_ok (L := a₁.length / 16 - j) H₁.env.r31 H₁.env.perm.w (by omega_arith) H₁.hl)
      (chunkLd_ok (L := a₁.length / 16 - j) H₂.env.r31 H₂.env.perm.w (by omega_arith) hl₂)
      fun u₁ u₂ ⟨r3₁, r4₁, _, k₁⟩ ⟨r3₂, r4₂, _, k₂⟩ => ?_
    have hsp : u₁.sp = u₂.sp := by rw [k₁.sp, k₂.sp, H₁.env.sp, H₂.env.sp]
    refine rel_ite (eval_zero r4₁ (by omega_arith)) (eval_zero r4₂ (by omega_arith)) (fun _ => ?_) (fun _ => ?_)
    · exact rel_taint [.r3] hsp (by agree_ppc [r3₁, r3₂]) ⟨_, by taint_decide⟩
    · exact rel_taint [] hsp (by agree_ppc []) ⟨_, by taint_decide⟩
  have E₁ := H₁.env.keep3 g₁ k₁
  have E₂ := H₂.env.keep3 g₂ k₂
  -- the counts stored
  refine rel_seq (rel_env E₁ E₂ hV [.r25] (by agree_ppc [h25₁, h25₂]) ⟨_, by taint_decide⟩)
    (chunkMid_ok C₁ H₁ (c := min 8 (a₁.length / 16 - j)) (by omega_arith) g₁ k₁ h25₁)
    (chunkMid_ok C₂ H₂ (c := min 8 (a₁.length / 16 - j)) (by omega_arith) g₂ k₂ h25₂) fun w₁ w₂ F₁ F₂ => ?_
  -- the buffer filled
  refine rel_seq (rel_env F₁.env F₂.env hV [.r11, .r24, .r25, .r26]
      (by agree_ppc [F₁.r11, F₂.r11, F₁.r24, F₂.r24, F₁.r25, F₂.r25, F₁.r26, F₂.r26, e31]) ⟨_, by taint_decide⟩)
    (fill_ok C₁ (by omega_arith) (by omega_arith) (by omega_arith) F₁) (fill_ok C₂ (by omega_arith) (by omega_arith) (by omega_arith) F₂)
    fun y₁ y₂ G₁ G₂ => ?_
  -- enciphered
  let c := min 8 (a₁.length / 16 - j)
  refine RelCT.assoc (rel_seq (F₁ := fun z => Env V₁ sp z ∧
      z.mem.readW (V₁ .r31 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c)
    (F₂ := fun z => Env V₂ sp z ∧ z.mem.readW (V₂ .r31 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c)
    (callBlocks_rel L hV Proof.Aes.PPC64LE.encryptBlocksF_correct
      Proof.Aes.PPC64LE.encryptBlocksF_ct C₁.rounds h28 G₁.env G₂.env [] (by agree_ppc []) ⟨_, by taint_decide⟩
      (fun s g k => bufArgs_ok (by rw [g _ (by decide) (by decide) (by decide), G₁.env.r31])
        (by rw [k.wr]; exact G₁.env.perm.w) (by rw [k.mem, G₁.cn]))
      (fun s g k => bufArgs_ok (by rw [g _ (by decide) (by decide) (by decide), G₂.env.r31, e31])
        (by rw [k.wr, e31]; exact G₂.env.perm.w) (by rw [k.mem, e31, G₂.cn]))
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith))
      (dstW L (hV.perm G₂.env.perm) (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
    (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) L Proof.Aes.PPC64LE.encryptBlocksF_correct encryptBlocks_noFrames
      C₁.rounds h28 G₁.env
      (fun s g k => bufArgs_ok (by rw [g _ (by decide) (by decide) (by decide), G₁.env.r31])
        (by rw [k.wr]; exact G₁.env.perm.w) (by rw [k.mem, G₁.cn]))
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
      fun z P => ⟨P.env G₁.env, (bufCall_readW L P (by omega_arith) (d := cnO) (by decide)).trans G₁.cn⟩)
    (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (hV.lay L) Proof.Aes.PPC64LE.encryptBlocksF_correct
      encryptBlocks_noFrames C₁.rounds h28₂ G₂.env
      (fun s g k => bufArgs_ok (by rw [g _ (by decide) (by decide) (by decide), G₂.env.r31])
        (by rw [k.wr]; exact G₂.env.perm.w) (by rw [k.mem, G₂.cn]))
      (dstW (hV.lay L) G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
      fun z P => ⟨P.env G₂.env, (bufCall_readW (hV.lay L) P (by omega_arith) (d := cnO) (by decide)).trans G₂.cn⟩)
    fun z₁ z₂ ⟨Z₁, cn₁⟩ ⟨Z₂, cn₂⟩ => ?_)
  -- the buffer added to the sum
  refine rel_seq (rel_env Z₁ Z₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩)
    (sumArgs_ok Z₁.r31 Z₁.perm.w cn₁) (sumArgs_ok Z₂.r31 Z₂.perm.w cn₂)
    fun x₁ x₂ ⟨r11₁, r25₁, g₁', k₁'⟩ ⟨r11₂, r25₂, g₂', k₂'⟩ => ?_
  have X₁ := Z₁.keep2 g₁' k₁'
  have X₂ := Z₂.keep2 g₂' k₂'
  refine rel_seqEnv X₁ X₂ (rel_env X₁ X₂ hV [.r11, .r25] (by agree_ppc [r11₁, r11₂, r25₁, r25₂, e31])
    ⟨_, by taint_decide⟩) sumRegs (by decide +kernel) (by decide +kernel) (by decide) fun _ _ e₁ e₂ => ?_
  exact rel_env e₁ e₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩

/-- The chunks, in two runs. -/
theorem hashLoop_rel {τ₁ τ₂ : State} (H₁ : HInv V₁ sp ciph₁ l₁ A a₁ s₁ τ₁ 0)
    (H₂ : HInv V₂ sp ciph₂ l₂ A a₂ s₂ τ₂ 0) (hm : 0 < a₁.length / 16) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop hashChunk (.nonzero .d .r3)) TT := by
  have hs := C₁.short
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  refine (RelCT.loop (Q := TT)
    (fun (k : Nat) (u₁ u₂ : State) => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      HInv V₁ sp ciph₁ l₁ A a₁ s₁ u₁ j ∧ HInv V₂ sp ciph₂ l₂ A a₂ s₂ u₂ j) (fun k => ?_)
    (a₁.length / 16 - 0)).mono (fun x y hxy => by obtain ⟨rfl, rfl⟩ := hxy; exact ⟨0, rfl, hm, H₁, H₂⟩)
    fun _ _ h => h
  refine rel_of_pt fun σ₁ σ₂ ⟨j, hk, hj, G₁, G₂⟩ => ?_
  refine ((chunk_rel hV C₁ C₂ h28 hlen G₁ G₂ hj).wp
    (F₁ := fun u => HInv V₁ sp ciph₁ l₁ A a₁ s₁ u (j + min 8 (a₁.length / 16 - j)))
    (F₂ := fun u => HInv V₂ sp ciph₂ l₂ A a₂ s₂ u (j + min 8 (a₂.length / 16 - j))) fun x y hxy => by
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hashChunk_ok C₁ h28 G₁ hj, hashChunk_ok C₂ h28₂ G₂ (by rw [hlen]; exact hj)⟩).mono (fun _ _ h => h)
    fun u₁ u₂ ⟨_, F₁, F₂⟩ => ?_
  rw [hlen] at F₂
  have ev₁ := eval_nonzero F₁.r3 (by omega_arith)
  have r3₂ := F₂.r3
  rw [hlen] at r3₂
  have ev₂ := eval_nonzero r3₂ (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun h => ?_⟩
  rw [ev₁] at h
  have he : ¬ a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)) = 0 := by simpa using h
  exact ⟨a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)), by omega_arith, j + min 8 (a₁.length / 16 - j), rfl,
    by omega_arith, F₁, F₂⟩

/-- `HASH`, in two runs. -/
theorem hash_rel (E₁ : Env V₁ sp s₁) (E₂ : Env V₂ sp s₂) (h21 : V₁ .r21 = A)
    (h22 : V₁ .r22 = BitVec.ofNat 64 a₁.length)
    (hl0₁ : Spec.Ocb.blockAtMem s₁.mem (V₁ .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l₁ 0)
    (hl0₂ : Spec.Ocb.blockAtMem s₂.mem (V₂ .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l₂ 0) :
    RelCT isa (Eq2 s₁ s₂) Impl.AesOcb.PPC64LE.hash TT := by
  have hs := C₁.short
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  have h21₂ : V₂ .r21 = A := (hV .r21 (by decide)).symm.trans h21
  have h22₂ : V₂ .r22 = BitVec.ofNat 64 a₂.length := by rw [← hV .r22 (by decide), h22, hlen]
  unfold Impl.AesOcb.PPC64LE.hash
  refine rel_seq (rel_env E₁ E₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) (hashHead_ok C₁ E₁ h21 h22 hl0₁)
    (hashHead_ok C₂ E₂ h21₂ h22₂ hl0₂) fun t₁ t₂ H₁ H₂ => ?_
  have r3₂ := H₂.r3
  rw [hlen] at r3₂
  refine rel_seq (rel_ite (eval_zero H₁.r3 (by omega_arith)) (eval_zero r3₂ (by omega_arith)) (fun _ => rel_skip)
      (fun hb => hashLoop_rel hV C₁ C₂ h28 hlen H₁ H₂ (Nat.pos_of_ne_zero (of_decide_eq_false hb))))
    (hashBody_ok C₁ h28 H₁) (hashBody_ok C₂ h28₂ H₂) fun u₁ u₂ G₁ G₂ => ?_
  refine rel_seq (rel_env G₁.env G₂.env hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) (tailHead_ok C₁ h22 G₁)
    (tailHead_ok C₂ h22₂ G₂) fun w₁ w₂ ⟨T₁, h25₁⟩ ⟨T₂, h25₂⟩ => ?_
  rw [hlen] at h25₂
  exact rel_ite (eval_zero h25₁ (by omega_arith)) (eval_zero h25₂ (by omega_arith)) (fun _ => rel_skip)
    fun _ => hashRest_rel hV C₁.lay C₁.rounds h28 T₁.env T₂.env (by rw [T₁.r24, T₂.r24, hlen]) (by rw [h25₁, h25₂])

end

end VG.Proof.AesOcb.PPC64LE

end

end

/-! ### `AesOcb.PPC64LE.Seal`, which this module and modules that import it used -/

section

/-! ### `AesOcb.PPC64LE.Contract`, which this module and modules that import it used -/

section

/-!
# AES-OCB on PPC64LE: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Ocb/Contract.lean`, with the working space as a
last argument (`Proof/AesOcb/Scratch.lean`), which imply these
(`Verified.lean`). As on AArch64 (`Proof/AesOcb/AArch64/Env.lean`): a
call (`bl`) stores nothing in memory, so no stack is used; `seal` and `open`
read `tag`, `tag_len` and `work` from the Parameter Save Area, at
`sp + 96`, which they may only read.
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (ctxCiph ctxInv ctxLstar encryptWith decryptWith lengthsOk zeros)

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (r : BitVec 64) : Prop := r.toNat = 10 ∨ r.toNat = 12 ∨ r.toNat = 14

/-- The key context. -/
abbrev aCtx (s : State) : Region := ⟨s.gpr .r3, 256⟩

/-- The nonce. -/
abbrev aNonce (s : State) : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩

/-- The associated data. -/
abbrev aAad (s : State) : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩

/-- The data. -/
abbrev aData (s : State) : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩

/-- The tag. -/
abbrev aTag (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩

/-- The working space. -/
abbrev aWork (s : State) : Region := ⟨stackArg s 2, 512⟩

/-- What `vg_aes_ocb_seal` and `vg_aes_ocb_open` need of their arguments
`(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6, aad = r7, aad_len = r8,
data = r9, len = r10, tag = [sp + 96], tag_len = [sp + 104], work = [sp + 112])`, but
for what they may access. -/
def oneFacts (s : State) : Prop :=
  (aCtx s).Disjoint (aData s) ∧ (aCtx s).Disjoint (aWork s) ∧ (aNonce s).Disjoint (aData s) ∧
    (aNonce s).Disjoint (aWork s) ∧ (aAad s).Disjoint (aData s) ∧ (aAad s).Disjoint (aWork s) ∧
    (aTag s).Disjoint (aData s) ∧ (aTag s).Disjoint (aWork s) ∧
    (aData s).Disjoint (aWork s) ∧ (aData s).Disjoint (args s 3) ∧ (aWork s).Disjoint (args s 3) ∧
    (s.gpr .r3).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
    (stackArg s 2).toNat + 512 ≤ 2 ^ 64 ∧ s.sp.toNat + 120 ≤ 2 ^ 64 ∧ rounds (s.gpr .r4) ∧
    lengthsOk (stackArg s 1).toNat (s.gpr .r6).toNat = true

/-- What `vg_aes_ocb_seal` needs: it may write the data, the tag and the
working space. -/
def sealPreA (s : State) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, args s 3] ∧ s.wr = [aData s, aTag s, aWork s] ∧
    (aTag s).Disjoint (args s 3) ∧ (aCtx s).Disjoint (aTag s) ∧ (aNonce s).Disjoint (aTag s) ∧
    (aAad s).Disjoint (aTag s) ∧ oneFacts s

/-- What `vg_aes_ocb_open` needs: it may write the data and the working
space, and read the tag. -/
def openPreA (s : State) : Prop :=
  s.rd = [aCtx s, aNonce s, aAad s, aTag s, args s 3] ∧ s.wr = [aData s, aWork s] ∧ oneFacts s

def onePub (s₁ s₂ : State) : Prop :=
  s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.sp = s₂.sp ∧ ∀ i < 3, stackArg s₁ i = stackArg s₂ i

/-- `vg_aes_ocb_seal`. -/
def sealPPC64LE : Contract isa where
  pre := sealPreA
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (ctxLstar s.mem (s.gpr .r3)) (stackArg s 1).toNat
        (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) =
      (bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat, bytesAt s'.mem (stackArg s 0) (stackArg s 1).toNat)
  pub := onePub

/-- `OCB-DECRYPT` of what `vg_aes_ocb_open` is given. -/
def openOut (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (ctxInv s.mem (s.gpr .r3) (s.gpr .r4).toNat)
    (ctxLstar s.mem (s.gpr .r3)) (stackArg s 1).toNat (bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat)
    (bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)

/-- What `vg_aes_ocb_open` may leak (`Spec.Ocb.openLeak`): whether it succeeds. -/
def openLeak (s : State) : List Nat :=
  if ¬rounds (s.gpr .r4) then [] else [if (openOut s).isSome then 1 else 0]

/-- `vg_aes_ocb_open`. -/
def openPPC64LE : Contract isa where
  pre := openPreA
  post s s' :=
    match openOut s with
    | some pt => (s'.gpr .r3).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat = pt
    | none => (s'.gpr .r3).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .r9) (s.gpr .r10).toNat = zeros (s.gpr .r10).toNat
  pub s₁ s₂ := onePub s₁ s₂ ∧ openLeak s₁ = openLeak s₂

end VG.Proof.AesOcb.PPC64LE

end

end

/-! ### `AesOcb.PPC64LE.Entry`, which only this module used -/

section

/-!
# AES-OCB on PPC64LE: the entry (`entry`)

Untrusted: everything here is checked by Lean. `entry` is AES-GCM's
(`Proof.AesGcm.PPC64LE.one1_wp`: our caller's registers and return address
saved in `W`, the arguments in their registers, `tag_len` in `r19`), then
`L_$ = double(L_*)`, `L_0 = double(L_$)` and the checksum zeroed
(`entry_ok`). The environment after it is the state's own registers
(`EntryPost.env`), as AES-GCM's (`Proof.AesGcm.PPC64LE.one_env`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxLstar lDollar lAt)
open VG.Proof.AesGcm.PPC64LE (SO1 SavedAt savedR one1_wp ld_ok Keeps Keeps' in_left in_off)
open VG.Proof.Ocb (blockAtMem_frame)

/-- What `entry` leaves, from `s₀`, with `W` and the tag's address `T`. -/
structure EntryPost (W T : Addr) (s₀ s : State) : Prop where
  env : Env s.gpr s₀.sp s
  r31 : s.gpr .r31 = W
  r29 : s.gpr .r29 = s₀.gpr .r3
  r28 : s.gpr .r28 = s₀.gpr .r4
  r24 : s.gpr .r24 = s₀.gpr .r5
  r25 : s.gpr .r25 = s₀.gpr .r6
  r18 : s.gpr .r18 = s₀.gpr .r6
  r21 : s.gpr .r21 = s₀.gpr .r7
  r22 : s.gpr .r22 = s₀.gpr .r8
  r27 : s.gpr .r27 = s₀.gpr .r9
  r23 : s.gpr .r23 = s₀.gpr .r10
  r20 : s.gpr .r20 = T
  r19 : s.gpr .r19 = stackArg s₀ 1
  low : ∀ r ∈ [Reg.r2, .r14, .r15, .r16, .r17], s.gpr r = s₀.gpr r
  keeps : Keeps' s₀ s
  saved : SavedAt s.mem W s₀
  ld : blockAtMem s.mem (W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s₀.mem (s₀.gpr .r3))
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₀.mem (s₀.gpr .r3)) 0
  ck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0
  frame : Frame [savedR W, ⟨W + BitVec.ofNat 64 32, 64⟩] s₀.mem s.mem

theorem stackArg_eq' (s : State) (i : Nat) :
    stackArg s i = s.mem.readW (s.sp + BitVec.ofNat 64 (96 + 8 * i)) 64 := by
  show s.mem.readW (s.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 = _
  rw [show 32 + 8 * (8 + i) = 96 + 8 * i by omega_using []]

/-- `entry`. -/
theorem entry_ok {s₀ : State} {W T : Addr} (L : Lay (s₀.gpr .r3) W) (hW : Covers [⟨W, 512⟩] s₀.wr)
    (hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr)) (hWv : stackArg s₀ 2 = W) (hTv : stackArg s₀ 0 = T)
    (hA : Covers [⟨s₀.sp + BitVec.ofNat 64 96, 24⟩] (s₀.rd ++ s₀.wr))
    (hAW : (⟨s₀.sp + BitVec.ofNat 64 96, 24⟩ : Region).Disjoint ⟨W, 512⟩) :
    WP isa (.block entry) s₀ (EntryPost W T s₀) := by
  have hAi : ∀ {i : Nat}, i < 3 → InRegions (s₀.rd ++ s₀.wr) (s₀.sp + BitVec.ofNat 64 (96 + 8 * i)) 8 :=
    fun {i} hi => by
      have := in_off hA (d := 8 * i) (n := 8) (by omega_using [hi]) (by decide)
      rwa [Proof.AesGcm.PPC64LE.add_ofNat_assoc] at this
  have hAs : ∀ {i : Nat}, i < 3 → (⟨s₀.sp + BitVec.ofNat 64 (96 + 8 * i), 8⟩ : Region).Disjoint (savedR W) :=
    fun {i} hi => by
      have := (hAW.sub_left (Offset.sub_base _ (d := 8 * i) (n := 8) (k := 24) (by omega_using [hi]))).sub_right
        (Lay.wSub (W := W) (d := 128) (n := 120) (by decide))
      rwa [Proof.AesGcm.PPC64LE.add_ofNat_assoc] at this
  simp only [entry, Impl.AesGcm.PPC64LE.openEntry, lsetup, List.append_assoc]
  refine WP.block_append (WP.mono (one1_wp (off := 112) (W := W) (T := T) (.inr rfl) hW (hAi (i := 2) (by decide))
    (by rw [← hWv, stackArg_eq']) (hAi (i := 0) (by decide)) (by rw [← hTv, stackArg_eq'])
    (hAs (i := 0) (by decide))) fun s₁ h1 => ?_)
  have k₁ := h1.en.keeps
  have hv : s₁.mem.readW (s₁.gpr .r12 + BitVec.ofNat 64 104) 64 = stackArg s₀ 1 := by
    rw [h1.r12, stackArg_eq', h1.en.frame.readW (r := ⟨s₀.sp + BitVec.ofNat 64 (96 + 8 * 1), 8⟩)
      (Region.contains_self _ _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hAs (by decide))
      (by decide)]
  refine WP.block_append (WP.mono (ld_ok (t := .r19) (b := .r12) (off := 104) (by decide) (by decide) (by decide)
    (by rw [h1.r12, k₁.rd, k₁.wr]; exact hAi (i := 1) (by decide)) hv) fun s₂ ⟨r19₂, g₂, k₂⟩ => ?_)
  have e : ∀ r, r ≠ .r19 → s₂.gpr r = s₁.gpr r := g₂
  have h31₂ : s₂.gpr .r31 = W := by rw [e _ (by decide), h1.r31]
  have h29₂ : s₂.gpr .r29 = s₀.gpr .r3 := by rw [e _ (by decide), h1.r29]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.wr, k₁.wr]
  have rd₂ : s₂.rd = s₀.rd := by rw [k₂.rd, k₁.rd]
  have hw₂ : Covers [⟨W, 512⟩] s₂.wr := by rw [wr₂]; exact hW
  have hc₂ : Covers [⟨s₀.gpr .r3, 256⟩] (s₂.rd ++ s₂.wr) := by rw [rd₂, wr₂]; exact hC
  have m₂ : s₂.mem = s₁.mem := k₂.mem
  -- `L_$`
  refine WP.block_append (WP.mono (dbl_ok (s := s₂) (b := .r29) (a := 240) (d := ldO) (by decide) (by decide)
    h31₂ h29₂ (by decide) (in_off hc₂ (by decide) (by decide)) (in_off hc₂ (by decide) (by decide))
    (in_off hw₂ (by decide) (by decide)) (in_off hw₂ (by decide) (by decide))) fun s₃ B₃ => ?_)
  have h31₃ : s₃.gpr .r31 = W := by rw [B₃.gpr _ (by decide), h31₂]
  have hw₃ : Covers [⟨W, 512⟩] s₃.wr := by rw [B₃.wr]; exact hw₂
  -- `L_0`
  refine WP.block_append (WP.mono (dbl_ok (s := s₃) (b := .r31) (a := ldO) (d := l0O) (by decide) (by decide)
    h31₃ h31₃ (by decide) (in_left (in_off hw₃ (by decide) (by decide))) (in_left (in_off hw₃ (by decide) (by decide)))
    (in_off hw₃ (by decide) (by decide)) (in_off hw₃ (by decide) (by decide))) fun s₄ B₄ => ?_)
  have h31₄ : s₄.gpr .r31 = W := by rw [B₄.gpr _ (by decide), h31₃]
  have hw₄ : Covers [⟨W, 512⟩] s₄.wr := by rw [B₄.wr]; exact hw₃
  -- the checksum
  refine WP.mono (zero16_ok (s := s₄) (d := ckO) (by decide) h31₄ (in_off hw₄ (by decide) (by decide))
    (in_off hw₄ (by decide) (by decide))) fun s₅ B₅ => ?_
  have g₅ : ∀ r, r ≠ .r0 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r19 → s₅.gpr r = s₁.gpr r :=
    fun r a b c d f g => by
      rw [B₅.gpr r (by simp [a]), B₄.gpr r (by simp [a, b, c, d, f]), B₃.gpr r (by simp [a, b, c, d, f]), e r g]
  have rd₅ : s₅.rd = s₀.rd := by rw [B₅.rd, B₄.rd, B₃.rd, rd₂]
  have wr₅ : s₅.wr = s₀.wr := by rw [B₅.wr, B₄.wr, B₃.wr, wr₂]
  have frW : Frame [⟨W + BitVec.ofNat 64 32, 64⟩] s₂.mem s₅.mem :=
    ((B₃.frame.sub fun r hr => ?_).trans (B₄.frame.sub fun r hr => ?_)).trans (B₅.frame.sub fun r hr => ?_)
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  have lst : blockAtMem s₂.mem (s₀.gpr .r3 + BitVec.ofNat 64 240) = ctxLstar s₀.mem (s₀.gpr .r3) := by
    rw [m₂, blockAtMem_frame h1.en.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (W := W) (d := 128) (n := 120)
        (by decide)))]
    rfl
  have perm : Perm (s₀.gpr .r3) W s₅ := (⟨hC, hW⟩ : Perm (s₀.gpr .r3) W s₀).of_eq rd₅ wr₅
  refine
    { env := ⟨fun _ _ => rfl, by rw [B₅.sp, B₄.sp, B₃.sp, k₂.sp, k₁.sp], by
        rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r29,
          g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r31]; exact perm⟩
      r31 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r31]
      r29 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r29]
      r28 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r28]
      r24 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r24]
      r25 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r25]
      r18 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r18]
      r21 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r21]
      r22 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r22]
      r27 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r27]
      r23 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r23]
      r20 := by rw [g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1.r20]
      r19 := by rw [B₅.gpr _ (by decide), B₄.gpr _ (by decide), B₃.gpr _ (by decide), r19₂]
      low := fun r hr => by
        rw [g₅ r (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
          (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)]
        exact h1.en.low r hr
      keeps := ⟨rd₅, wr₅, by rw [B₅.sp, B₄.sp, B₃.sp, k₂.sp, k₁.sp], by rw [B₅.lr, B₄.lr, B₃.lr, k₂.lr, k₁.lr]⟩
      saved := by
        have sv := h1.en.saved
        rw [← m₂] at sv
        exact sv.frame frW fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Proof.AesGcm.PPC64LE.saved_w (by decide) (.inl (by decide))
      ld := by
        rw [blockAtMem_frame B₅.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
          B₃.val, lst]
        rfl
      l0 := by
        rw [blockAtMem_frame B₅.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          B₄.val, B₃.val, lst]
        rfl
      ck := B₅.val
      frame := by
        have f := h1.en.frame
        rw [← m₂] at f
        exact (f.mono (by simp)).trans (frW.mono (by simp)) }

end VG.Proof.AesOcb.PPC64LE

end

end


/-!
# AES-OCB on PPC64LE: `vg_aes_ocb_seal`

Untrusted: everything here is checked by Lean. The preconditions `sealPreA`
and `openPreA` give the facts the proofs use about the arguments (`FnArgs`,
`sealArgs_of`, `openArgs_of`). `seal` is `front`: `entry`, `Offset_0`
(`nonce`), `HASH` (`hash`), the data (`body`) and the tag at `W` (`tag`);
then the copy of the tag to `tag` (`tagOut`), and `restore` (`seal_wp`). The
environment after the entry is the state's own registers (`EntryPost`). As
on AArch64 (`Proof/AesOcb/AArch64/InitCT.lean`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.AesGcm.PPC64LE (covers_mem covers_left in_left in_off SavedAt savedR Keeps Keeps')
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_or → cwp_or

/-- What `seal` and `open` are given: the key context at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`) and the
working space at `W`. -/
structure FnArgs (s : State) (K W N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  lay : Lay K W
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf W s N nl
  aad : Buf W s A al
  data : DBuf K W s D n
  tag : Buf W s T tl
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  td : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  n1 : 1 ≤ nl
  n15 : nl ≤ 15
  t1 : 1 ≤ tl
  t16 : tl ≤ 16
  args : Covers [⟨s.sp + BitVec.ofNat 64 96, 24⟩] (s.rd ++ s.wr)
  argsW : (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Disjoint ⟨W, 512⟩
  argsD : (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Disjoint ⟨D, n⟩

/-- `FnArgs` from the facts both preconditions give, for a state that may
read the key context, the nonce, the associated data, the arguments on the
stack and the tag, and write the data and `W`. -/
theorem args_of {s : State} (h : oneFacts s)
    (mrd : ∀ r ∈ [aCtx s, aNonce s, aAad s, args s 3, aTag s], Covers [r] (s.rd ++ s.wr))
    (mwr : ∀ r ∈ [aData s, aWork s], Covers [r] s.wr) :
    FnArgs s (s.gpr .r3) (stackArg s 2) (s.gpr .r5) (s.gpr .r7) (s.gpr .r9) (s.gpr .r4).toNat (s.gpr .r6).toNat
      (s.gpr .r8).toNat (s.gpr .r10).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨d3, d4, d5, d6, d7, d8, t1, t2, d9, d10, d11, b12, b13, b14, b15, bt, b16, _, hR, hv⟩ := h
  simp only [Spec.Ocb.lengthsOk, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨ht1, ht16⟩, hn1⟩, hn15⟩ := hv
  have sp0 : stackArgAddr s 0 = s.sp + BitVec.ofNat 64 96 := rfl
  obtain ha := mrd (args s 3) (by simp)
  simp only [args, sp0] at ha d10 d11
  exact {
    lay := ⟨b12, b16, d4⟩
    perm := ⟨mrd _ (by simp), mwr _ (by simp)⟩
    rounds := hR
    nonce := ⟨mrd _ (by simp), BitVec.isLt _, b13, d6⟩
    aad := ⟨mrd _ (by simp), BitVec.isLt _, b14, d8⟩
    data := ⟨⟨covers_left (mwr _ (by simp)), BitVec.isLt _, b15, d9⟩, mwr _ (by simp), d3⟩
    tag := ⟨mrd _ (by simp), BitVec.isLt _, bt, t2⟩
    nd := d5
    ad := d7
    td := t1
    n1 := hn1
    n15 := hn15
    t1 := ht1
    t16 := ht16
    args := ha
    argsW := d11.symm
    argsD := d10.symm }

theorem sealArgs_of {s : State} (h : sealPreA s) :
    FnArgs s (s.gpr .r3) (stackArg s 2) (s.gpr .r5) (s.gpr .r7) (s.gpr .r9) (s.gpr .r4).toNat (s.gpr .r6).toNat
      (s.gpr .r8).toNat (s.gpr .r10).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, -, -, -, -, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_mem (by simp))

theorem openArgs_of {s : State} (h : openPreA s) :
    FnArgs s (s.gpr .r3) (stackArg s 2) (s.gpr .r5) (s.gpr .r7) (s.gpr .r9) (s.gpr .r4).toNat (s.gpr .r6).toNat
      (s.gpr .r8).toNat (s.gpr .r10).toNat (stackArg s 1).toNat (stackArg s 0) := by
  obtain ⟨hrd, hwr, hf⟩ := h
  refine args_of hf (fun r hr => ?_) (fun r hr => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> (rw [hrd, hwr]; exact covers_mem (by simp))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (rw [hwr]; exact covers_mem (by simp))

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-! ## Frames -/

/-- A frame within `W`. -/
theorem frameW {W : Addr} {rs : List Region} {m m' : Mem} (h : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨W, 512⟩) : Frame [⟨W, 512⟩] m m' :=
  h.sub fun r hr => ⟨_, List.mem_singleton_self _, hs r hr⟩

theorem entryR_W (W : Addr) : ∀ r ∈ [savedR W, ⟨W + BitVec.ofNat 64 32, 64⟩], Region.Sub r ⟨W, 512⟩ :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem nonceR_W (W : Addr) : ∀ r ∈ nonceR W, Region.Sub r ⟨W, 512⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact Lay.wSub (by decide)

theorem hashR_W (W : Addr) : ∀ r ∈ hashR W, Region.Sub r ⟨W, 512⟩ := fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Lay.wSub (by decide)

/-- A buffer apart from `W`, after a frame within `W`. -/
theorem bytesAt_W {W P : Addr} {k : Nat} (hP : (⟨P, k⟩ : Region).Disjoint ⟨W, 512⟩) (hk : k < 2 ^ 64)
    {m m' : Mem} (h : Frame [⟨W, 512⟩] m m') : bytesAt m' P k = bytesAt m P k :=
  Proof.Cmac.bytesAt_frame h (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hP) (by omega_arith)

theorem ctxCiph_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 512⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : ctxCiph m' K R = ctxCiph m K R := by
  unfold ctxCiph
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega_arith) h]

theorem ctxInv_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 512⟩] m m') {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : Spec.Ocb.ctxInv m' K R = Spec.Ocb.ctxInv m K R := by
  unfold Spec.Ocb.ctxInv
  obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
  rw [bytesAt_W (L.k_w.sub_left (Region.sub_prefix hRb)) (by omega_arith) h]

theorem ctxLstar_W {K W : Addr} (L : Lay K W) {m m' : Mem} (h : Frame [⟨W, 512⟩] m m') :
    ctxLstar m' K = ctxLstar m K := by
  show blockAtMem m' (K + BitVec.ofNat 64 240) = blockAtMem m (K + BitVec.ofNat 64 240)
  exact blockAtMem_frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_left (Lay.kSub (by decide))

/-- What `tag d` writes, within the parts the pieces write. -/
theorem tagR_mut {W D : Addr} {n d : Nat} (hd : d + 16 ≤ 128 ∨ (256 ≤ d ∧ d + 16 ≤ 512)) {m m' : Mem}
    (h : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩] m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutW hd

/-- Our caller's registers saved in `W`, after a frame within the parts the pieces write. -/
theorem saved_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 512⟩)
    {s₀ : State} {m m' : Mem} (h : SavedAt m W s₀) (hf : Frame (mutR W D n) m m') : SavedAt m' W s₀ :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa using L.w_w (a := 128) (n := 120) (d := 0) (k := 128) (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (a := 128) (n := 120) (d := 256) (k := 256) (.inl (by decide)) (by decide) (by decide)
    · exact (hD.sub_right (Lay.wSub (W := W) (d := 128) (n := 120) (by decide))).symm

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ _), show (16 : Nat) = t + (16 - t) by omega_arith,
    Proof.Ocb.bytesAt_append, List.take_left' (length_bytesAt _ _ _)]

/-! ## Before the data -/

/-- What the pieces before the data leave, from `s₀` and with `V` the
registers after the entry: the offset, the checksum, `L_$`, `L_0` and
`HASH`. -/
structure Pre (V : Reg → BitVec 64) (K W N A : Addr) (R nl al tl : Nat) (s₀ s' : State) : Prop where
  env : Env V s₀.sp s'
  frame : Frame [⟨W, 512⟩] s₀.mem s'.mem
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  saved : SavedAt s'.mem W s₀
  ofs : blockAtMem s'.mem (W + BitVec.ofNat 64 ofsO) = Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)
  o0 : blockAtMem s'.mem (W + BitVec.ofNat 64 o0O) = Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)
  ck : blockAtMem s'.mem (W + BitVec.ofNat 64 ckO) = 0
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K)
  l0 : blockAtMem s'.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₀.mem K) 0
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al)

/-- `nonce` and `hash`, after the entry (in `s₁`, whose registers are `V`). -/
theorem preRest_wp {s₀ s₁ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (P₁ : EntryPost W T s₀ s₁) (htl : stackArg s₀ 1 = BitVec.ofNat 64 tl)
    (h3 : s₀.gpr .r3 = K) (h4 : s₀.gpr .r4 = BitVec.ofNat 64 R) (h5 : s₀.gpr .r5 = N)
    (h6 : s₀.gpr .r6 = BitVec.ofNat 64 nl) (h7 : s₀.gpr .r7 = A) (h8 : s₀.gpr .r8 = BitVec.ofNat 64 al) :
    WP isa (.seq nonce Impl.AesOcb.PPC64LE.hash) s₁ (Pre s₁.gpr K W N A R nl al tl s₀) := by
  obtain L : Lay (s₁.gpr .r29) (s₁.gpr .r31) := by rw [P₁.r29, P₁.r31, h3]; exact Ar.lay
  have E₁ := P₁.env
  obtain h28 : s₁.gpr .r28 = BitVec.ofNat 64 R := P₁.r28.trans h4
  obtain F₁ : Frame [⟨W, 512⟩] s₀.mem s₁.mem := frameW P₁.frame (entryR_W W)
  have rd₁ := P₁.keeps.rd
  have wr₁ := P₁.keeps.wr
  have hW₁ : s₁.gpr .r31 = W := P₁.r31
  obtain hK₁ : s₁.gpr .r29 = K := P₁.r29.trans h3
  obtain hKD : (⟨s₁.gpr .r29, 256⟩ : Region).Disjoint ⟨D, n⟩ := by rw [hK₁]; exact Ar.data.k
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok L Ar.rounds h28 E₁ (P₁.r24.trans h5) (P₁.r25.trans h6) (P₁.r19.trans htl)
    Ar.n1 Ar.n15 (by have := Ar.t16; omega_arith) (by rw [hW₁]; exact Ar.nonce.of_eq rd₁ wr₁) hKD) fun s₂ P₂ => ?_)
  obtain pf₂ : Frame (nonceR W) s₁.mem s₂.mem := by have := P₂.frame; rwa [hW₁] at this
  have ofs₂ := P₂.ofs
  have o0₂ := P₂.o0
  rw [hW₁] at ofs₂ o0₂
  obtain keep₂ : ∀ {d : Nat}, 32 ≤ d → d + 16 ≤ 112 →
      blockAtMem s₂.mem (W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (W + BitVec.ofNat 64 d) := fun h₁ h₂ => by
    have := P₂.keep h₁ h₂; rwa [hW₁] at this
  obtain F₂ : Frame [⟨W, 512⟩] s₁.mem s₂.mem := frameW pf₂ (nonceR_W W)
  -- `HASH`.
  obtain F₁₂ := F₁.trans F₂
  obtain C : HCtx (s₁.gpr .r29) (s₁.gpr .r31) D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al)
      s₂ :=
    { lay := L, rounds := Ar.rounds
      ciph := by rw [hK₁, ctxCiph_W Ar.lay F₁₂ Ar.rounds]
      lstar := by rw [hK₁, ctxLstar_W Ar.lay F₁₂]
      buf := by rw [length_bytesAt, hW₁]; exact Ar.aad.of_eq (P₂.rd.trans rd₁) (P₂.wr.trans wr₁)
      aad := by rw [length_bytesAt, bytesAt_W Ar.aad.w Ar.aad.lt F₁₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := hKD, dw := by rw [hW₁]; exact Ar.data.w }
  refine WP.mono (hash_ok C P₂.env h28 (P₁.r21.trans h7) (by rw [P₁.r22, h8, length_bytesAt])
    (by rw [hW₁, keep₂ (by decide) (by decide), P₁.l0, h3])) fun s₃ H₃ => ?_
  obtain F₃ : Frame [⟨W, 512⟩] s₂.mem s₃.mem := by have := H₃.frame; rw [hW₁] at this; exact frameW this (hashR_W W)
  obtain k₃ : ∀ {d : Nat}, (d + 16 ≤ 48 ∨ (64 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 272) ∨
      (288 ≤ d ∧ d + 16 ≤ 296) ∨ (312 ≤ d ∧ d + 16 ≤ 384)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun {d} hd =>
    blockAtMem_frame (by have := H₃.frame; rwa [hW₁] at this) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Ar.lay.w_w (by omega_arith) (by omega_arith) (by decide)
  obtain sv₂ : SavedAt s₂.mem W s₀ := saved_mut Ar.lay Ar.data.w P₁.saved (nonceR_mut (D := D) (n := n) pf₂)
  obtain sv₃ : SavedAt s₃.mem W s₀ := saved_mut Ar.lay Ar.data.w sv₂ (hashR_mut (D := D) (n := n)
    (by have := H₃.frame; rwa [hW₁] at this))
  obtain nonce₁ : bytesAt s₁.mem N nl = bytesAt s₀.mem N nl := bytesAt_W Ar.nonce.w Ar.nonce.lt F₁
  refine ⟨H₃.env, F₁₂.trans F₃, by rw [H₃.rd, P₂.rd, rd₁], by rw [H₃.wr, P₂.wr, wr₁], sv₃, ?_, ?_, ?_, ?_, ?_,
    by have := H₃.sum; rwa [hW₁] at this⟩
  · rw [k₃ (d := ofsO) (by decide), ofs₂, hK₁, ctxCiph_W Ar.lay F₁ Ar.rounds, nonce₁]
  · rw [k₃ (d := o0O) (by decide), o0₂, hK₁, ctxCiph_W Ar.lay F₁ Ar.rounds, nonce₁]
  · rw [k₃ (d := ckO) (by decide), keep₂ (by decide) (by decide), P₁.ck]
  · rw [k₃ (d := ldO) (by decide), keep₂ (by decide) (by decide), P₁.ld, h3]
  · rw [k₃ (d := l0O) (by decide), keep₂ (by decide) (by decide), P₁.l0, h3]

/-- `body`'s frame misses a block of `W` outside the offset, the checksum,
`[96, 128)` and `[256, 272)`. -/
theorem body_keep {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 512⟩)
    {m m' : Mem} (h : Frame (bodyR W D n) m m') {d : Nat}
    (hd : d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (128 ≤ d ∧ d + 16 ≤ 256) ∨ (272 ≤ d ∧ d + 16 ≤ 512)) :
    blockAtMem m' (W + BitVec.ofNat 64 d) = blockAtMem m (W + BitVec.ofNat 64 d) :=
  blockAtMem_frame h fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact L.w_w (by omega_arith) (by omega_arith) (by decide)
    · exact (hD.sub_right (Lay.wSub (by omega_arith))).symm

/-- `tag d`'s frame misses the data. -/
theorem tag_data {W D : Addr} {n d : Nat} (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 512⟩) (hd : d + 16 ≤ 512) :
    ∀ r ∈ [(⟨W + BitVec.ofNat 64 tmpO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 d, 16⟩], (⟨D, n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact hD.sub_right (Lay.wSub (by first | omega_arith | (simp only [tmpO]; omega_arith)))

/-- `tagOut`: the first `tl` bytes at `W` copied to the tag at `T` (in `r20`),
`tl` in `r19`, which the state may write. -/
theorem tagOut_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {tl : Nat} (h1 : 1 ≤ tl)
    (h16 : tl ≤ 16) (h19 : V .r19 = BitVec.ofNat 64 tl) (hTw : Covers [⟨V .r20, tl⟩] s.wr)
    (hTW : (⟨V .r20, tl⟩ : Region).Disjoint ⟨V .r31, 512⟩) :
    WP isa tagOut s fun t => t.mem = writeBytes s.mem (V .r20) (bytesAt s.mem (V .r31) tl) ∧
      (∀ r, r ∉ xpRegs → t.gpr r = s.gpr r) ∧ t.sp = s.sp ∧ t.lr = s.lr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain hA : WP isa (.block [Impl.AesGcm.PPC64LE.mov .r3 .r31, Impl.AesGcm.PPC64LE.mov .r4 .r20,
      Impl.AesGcm.PPC64LE.mov .r5 .r19]) s fun s₃ =>
      s₃.gpr .r3 = V .r31 ∧ s₃.gpr .r4 = V .r20 ∧ s₃.gpr .r5 = BitVec.ofNat 64 tl ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → s₃.gpr r = s.gpr r) ∧ Keeps s s₃ :=
    cwp_or fun s₁ u₁ => cwp_or fun s₂ u₂ => cwp_or fun s₃ u₃ => WP.block_nil
      ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, BitVec.or_self, E.r31],
        by rw [u₃.other _ (by decide), u₂.gpr, BitVec.or_self, u₁.other _ (by decide), E.r20],
        by rw [u₃.gpr, BitVec.or_self, u₂.other _ (by decide), u₁.other _ (by decide), E.r19, h19],
        fun q a b c => by rw [u₃.other _ c, u₂.other _ b, u₁.other _ a],
        ⟨by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr],
          by rw [u₃.sp, u₂.sp, u₁.sp], by rw [u₃.lr, u₂.lr, u₁.lr]⟩⟩
  unfold tagOut
  refine WP.seq (WP.mono hA fun s₁ ⟨r3₁, r4₁, r5₁, g₁, k₁⟩ => ?_)
  refine WP.mono (Proof.AesGcm.PPC64LE.copyLoop_ok s₁ ⟨r3₁, r4₁, r5₁, h1, by omega_arith,
    by rw [k₁.rd, k₁.wr]; exact covers_left (Proof.AesGcm.PPC64LE.covers_prefix E.perm.w (by omega_arith)),
    by rw [k₁.wr]; exact hTw, (hTW.sub_right (Region.sub_prefix (by omega_arith))).symm⟩) fun t ⟨mt, ot⟩ => ?_
  obtain ⟨rdt, wrt, spt, lrt⟩ := ot.keeps
  refine ⟨by rw [mt, k₁.mem], fun q hq => ?_, by rw [spt, k₁.sp], by rw [lrt, k₁.lr], by rw [rdt, k₁.rd],
    by rw [wrt, k₁.wr]⟩
  simp only [xpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  rw [ot.other q hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.1 hq.2.2.2.2, g₁ q hq.2.1 hq.2.2.1 hq.2.2.2.1]

/-- `vg_aes_ocb_seal`, for its arguments. -/
theorem seal_wp' {s₀ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (hTw : Covers [⟨T, tl⟩] s₀.wr) (hW : stackArg s₀ 2 = W)
    (hT : stackArg s₀ 0 = T) (htl : stackArg s₀ 1 = BitVec.ofNat 64 tl)
    (h3 : s₀.gpr .r3 = K) (h4 : s₀.gpr .r4 = BitVec.ofNat 64 R) (h5 : s₀.gpr .r5 = N)
    (h6 : s₀.gpr .r6 = BitVec.ofNat 64 nl) (h7 : s₀.gpr .r7 = A) (h8 : s₀.gpr .r8 = BitVec.ofNat 64 al)
    (h9 : s₀.gpr .r9 = D) (h10 : s₀.gpr .r10 = BitVec.ofNat 64 n) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧
      Spec.Ocb.encryptWith (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) tl (bytesAt s₀.mem N nl)
        (bytesAt s₀.mem A al) (bytesAt s₀.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  obtain L₀ : Lay (s₀.gpr .r3) W := by rw [h3]; exact Ar.lay
  obtain hC : Covers [⟨s₀.gpr .r3, 256⟩] (s₀.rd ++ s₀.wr) := by rw [h3]; exact Ar.perm.k
  unfold «seal» front
  refine WP.seq (WP.seq (WP.mono (entry_ok L₀ Ar.perm.w hC hW hT Ar.args Ar.argsW) fun s₁ P₁ => ?_))
  have hW₁ : s₁.gpr .r31 = W := P₁.r31
  obtain hK₁ : s₁.gpr .r29 = K := P₁.r29.trans h3
  obtain hD₁ : s₁.gpr .r27 = D := P₁.r27.trans h9
  obtain h28 : s₁.gpr .r28 = BitVec.ofNat 64 R := P₁.r28.trans h4
  obtain h23 : s₁.gpr .r23 = BitVec.ofNat 64 n := P₁.r23.trans h10
  obtain L : Lay (s₁.gpr .r29) (s₁.gpr .r31) := by rw [hK₁, hW₁]; exact Ar.lay
  refine WP.assoc (WP.seq (WP.mono (preRest_wp Ar P₁ htl h3 h4 h5 h6 h7 h8) fun s₃ P₃ => ?_))
  obtain hD₃ : DBuf (s₁.gpr .r29) (s₁.gpr .r31) s₃ (s₁.gpr .r27) n := by
    rw [hK₁, hW₁, hD₁]; exact Ar.data.of_eq P₃.rd P₃.wr
  obtain c₃ : ctxCiph s₃.mem K R = ctxCiph s₀.mem K R := ctxCiph_W Ar.lay P₃.frame Ar.rounds
  obtain l₃ : ctxLstar s₃.mem K = ctxLstar s₀.mem K := ctxLstar_W Ar.lay P₃.frame
  obtain d₃ : bytesAt s₃.mem D n = bytesAt s₀.mem D n := bytesAt_W Ar.data.w Ar.data.lt P₃.frame
  refine WP.seq (WP.mono (bodySeal_ok L P₃.env Ar.rounds h28 h23 hD₃
    (O0 := Spec.Ocb.offset0 (ctxCiph s₀.mem K R) tl (bytesAt s₀.mem N nl)) (by rw [hW₁]; exact P₃.ofs)
    (by rw [hW₁]; exact P₃.o0) (by rw [hW₁]; exact P₃.ck) (by rw [hW₁, hK₁, P₃.l0, l₃])) fun s₄ B => ?_)
  obtain Bf : Frame (bodyR W D n) s₃.mem s₄.mem := by have := B.frame; rwa [hW₁, hD₁] at this
  obtain F₄ : Frame (mutR W D n) s₃.mem s₄.mem := bodyR_mut Bf
  obtain cK₄ : ctxCiph s₄.mem K R = ctxCiph s₀.mem K R := (ctxCiph_mut Ar.lay Ar.data.k F₄ Ar.rounds).trans c₃
  obtain ld₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s₀.mem K) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := ldO) (by decide), P₃.ld]
  obtain sum₄ : blockAtMem s₄.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) (bytesAt s₀.mem A al) := by
    rw [body_keep Ar.lay Ar.data.w Bf (d := sumO) (by decide), P₃.sum]
  -- The tag.
  refine WP.mono (tag_ok L B.env Ar.rounds h28 (.inl rfl)) fun s₅ T₅ => ?_
  obtain Tf : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 tagO, 16⟩]
      s₄.mem s₅.mem := by have := T₅.frame; rwa [hW₁] at this
  obtain F₅ : Frame (mutR W D n) s₄.mem s₅.mem := tagR_mut (.inl (by decide)) Tf
  obtain sv₅ := saved_mut Ar.lay Ar.data.w (saved_mut Ar.lay Ar.data.w P₃.saved F₄) F₅
  -- The copy of the tag.
  have E₅ := T₅.env
  obtain hTd : (⟨s₁.gpr .r20, tl⟩ : Region).Disjoint ⟨s₁.gpr .r31, 512⟩ := by rw [P₁.r20, hW₁]; exact Ar.tag.w
  refine WP.seq (WP.mono (tagOut_ok E₅ Ar.t1 Ar.t16 (P₁.r19.trans htl)
    (by rw [P₁.r20, T₅.wr, B.wr, P₃.wr]; exact hTw) hTd) fun s₆ ⟨m₆, g₆, sp₆, lr₆, rd₆, wr₆⟩ => ?_)
  obtain E₆ := E₅.others g₆ sp₆ rd₆ wr₆
  rw [P₁.r20, hW₁] at m₆
  obtain F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  obtain sv₆ : SavedAt s₆.mem W s₀ := sv₅.frame F₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (Ar.tag.w.sub_right (Lay.wSub (W := W) (d := 128) (n := 120) (by decide))).symm
  -- `restore`.
  refine WP.mono (Proof.AesGcm.PPC64LE.restore_ok (E₆.r31.trans hW₁)
    (by rw [rd₆, wr₆, T₅.rd, T₅.wr, B.rd, B.wr, P₃.rd, P₃.wr]; exact covers_left Ar.perm.w) sv₆
    (by rw [E₆.sp]) (fun r hr => by
      rw [E₆.fr r (by revert hr; revert r; decide), P₁.low r hr])) fun s₇ ⟨abi, m₇, _, _, _⟩ => ⟨abi, ?_⟩
  have hout := B.out
  rw [hK₁, hD₁, c₃, l₃, d₃] at hout
  have hofs := B.ofs
  rw [hW₁, hK₁, l₃] at hofs
  have hck := B.ck
  rw [hW₁, hD₁, d₃] at hck
  have hn := Ar.data.lt
  have ht := Ar.tag.lt
  obtain d₇ : bytesAt s₇.mem D n = bytesAt s₄.mem D n := by
    rw [m₇, Proof.Cmac.bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega_arith)]
    exact Proof.Cmac.bytesAt_frame Tf (tag_data Ar.data.w (by decide)) (by omega_arith)
  have tv := T₅.val
  rw [hW₁, hK₁, show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
  obtain t₇ : bytesAt s₇.mem T tl = (Spec.Ocb.toBytes (blockAtMem s₅.mem W)).take tl := by
    rw [m₇, m₆, Proof.Ocb.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, bytesAt_take_block _ _ Ar.t16]
  rw [Proof.Ocb.encryptWith_eq, d₇, hout, t₇, tv, hck, hofs, ld₄, sum₄, cK₄]
  simp only [length_bytesAt, List.length_drop]
  by_cases hr : 0 < n % 16
  · have h' : n - 16 * (n / 16) > 0 := by omega_arith
    simp only [h', hr, ↓reduceIte]
  · have h' : ¬ (n - 16 * (n / 16) > 0) := by omega_arith
    simp only [h', hr, ↓reduceIte]

/-- `vg_aes_ocb_seal`. -/
theorem seal_wp {s : State} (h : sealPPC64LE.pre s) :
    WP isa «seal» s fun s' => abiPreserved s s' ∧ sealPPC64LE.post s s' :=
  seal_wp' (sealArgs_of h) (covers_mem (by rw [h.2.1]; simp)) rfl rfl (ofNat_toNat64 _).symm rfl
    (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm rfl (ofNat_toNat64 _).symm

end VG.Proof.AesOcb.PPC64LE

end

end

/-! ### `AesOcb.PPC64LE.BodyCT`, which only this module used -/

section

/-!
# AES-OCB on PPC64LE: the data and the tag are constant time

Untrusted: everything here is checked by Lean. Between the calls, the code
runs from the public registers (the data's address and length among them)
and, for the rest of the data, its address and length (`r24`, `r25`), which
are the same in both runs; what each piece keeps of them is read off its
instructions (`exec_keep`) or from its correctness proof. The calls have the
same arguments in both runs (`callBlocks_rel`). As on AArch64
(`Proof/AesOcb/AArch64/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxLstar)
open VG.Proof.Ocb (offAt)
open VG.Proof.AesGcm.PPC64LE (frozen Keeps eval_zero shr4)
open VG.Proof.ChaCha20Poly1305.PPC64LE renaming wp_lsr → cwp_lsr

/-- Then: the next piece, in the environments, after code without calls that
writes only `rs`, none of their registers, which keeps the others. -/
theorem rel_seqKeep {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {c₁ c₂ : Prog isa} {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (rs : List Reg)
    (hc : writesOnly rs c₁ = true) (hn : c₁.noCalls = true) (hd : ∀ r ∈ frozen, r ∉ rs)
    (h₂ : ∀ τ₁ τ₂, Env V₁ sp τ₁ ∧ Keep rs σ₁ τ₁ → Env V₂ sp τ₂ ∧ Keep rs σ₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT :=
  rel_seqE h₁ (fun _ _ h => ⟨E₁.exec h rs hc hn hd, (exec_keep rs hc hn h).1⟩)
    (fun _ _ h => ⟨E₂.exec h rs hc hn hd, (exec_keep rs hc hn h).1⟩) h₂

/-- The data of the second run, with the first run's registers. -/
theorem Agree.dbuf {V₁ V₂ : Reg → BitVec 64} (hV : Agree V₁ V₂) {s : State} {n : Nat}
    (h : DBuf (V₂ .r29) (V₂ .r31) s (V₂ .r27) n) : DBuf (V₁ .r29) (V₁ .r31) s (V₁ .r27) n := by
  rw [hV .r29 (by decide), hV .r31 (by decide), hV .r27 (by decide)]; exact h

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .r29) (V₁ .r31)) (hV : Agree V₁ V₂) {R : Nat}
  (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R)
include L hV hR h28

/-- The tag at `W + d`, in two runs. -/
theorem tag_rel {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    RelCT isa (Eq2 σ₁ σ₂) (tag d) TT := by
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  unfold tag
  refine rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) [.r3, .r4]
    (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ F₁ F₂ => ?_
  refine rel_seq (encOne_rel L hV hR h28 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR h28 F₁ (by decide))
    (encOne_ok (hV.lay L) hR h28₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  rcases hd with rfl | rfl
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) ⟨_, by taint_decide⟩
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) ⟨_, by taint_decide⟩

/-- The rest of the data (at `r24`, `r25` bytes), in two runs. -/
theorem rest_rel (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂)
    (h24 : σ₁.gpr .r24 = σ₂.gpr .r24) (h25 : σ₁.gpr .r25 = σ₂.gpr .r25) :
    RelCT isa (Eq2 σ₁ σ₂) (rest enc) TT := by
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  unfold rest
  refine rel_seqKeep E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) [.r3, .r4]
    (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ ⟨F₁, K₁⟩ ⟨F₂, K₂⟩ => ?_
  refine rel_seq (encOne_rel L hV hR h28 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR h28 F₁ (by decide))
    (encOne_ok (hV.lay L) hR h28₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  have a₁ : u₁.gpr .r24 = σ₁.gpr .r24 := (P₁.saved _ (by decide)).trans (K₁.gpr (by decide))
  have a₂ : u₂.gpr .r24 = σ₂.gpr .r24 := (P₂.saved _ (by decide)).trans (K₂.gpr (by decide))
  have b₁ : u₁.gpr .r25 = σ₁.gpr .r25 := (P₁.saved _ (by decide)).trans (K₁.gpr (by decide))
  have b₂ : u₂.gpr .r25 = σ₂.gpr .r25 := (P₂.saved _ (by decide)).trans (K₂.gpr (by decide))
  cases enc <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [.r24, .r25] (by agree_ppc [a₁, a₂, b₁, b₂, h24, h25])
      ⟨_, by taint_decide⟩
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [.r24, .r25] (by agree_ppc [a₁, a₂, b₁, b₂, h24, h25])
      ⟨_, by taint_decide⟩

/-- The whole blocks (`n / 16 > 0` of them), in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LEF f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LEF f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LEF f).pre (Proof.Aes.blocksPPC64LEF f).pub c)
    (nf : c.noFrames = true) {pre post : List Instr} (rs : List Reg)
    (hpre : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR)) (.seq (.block passStart) (pass pre)) h).isSome = true)
    (hpost : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR))
      (.seq (.block (copy16 o0O ofsO ++ passStart)) (pass post)) h).isSome = true)
    (hk : writesOnly rs (.seq (.block passStart) (pass pre)) = true)
    (hn : (Code.seq (.block passStart) (pass pre) : Prog isa).noCalls = true) (hd : ∀ r ∈ frozen, r ∉ rs)
    {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {n : Nat} (h23 : V₁ .r23 = BitVec.ofNat 64 n)
    (hD₁ : DBuf (V₁ .r29) (V₁ .r31) σ₁ (V₁ .r27) n) (hD₂ : DBuf (V₂ .r29) (V₂ .r31) σ₂ (V₂ .r27) n) :
    RelCT isa (Eq2 σ₁ σ₂) (whole (.call name c) pre post) TT := by
  have hl := hD₁.lt
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  have h23₂ : V₂ .r23 = BitVec.ofNat 64 n := (hV .r23 (by decide)).symm.trans h23
  have e27 := hV .r27 (by decide)
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  unfold whole
  refine RelCT.assoc (rel_seqKeep E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_ppc []) hpre) rs hk hn hd
    fun τ₁ τ₂ ⟨F₁, K₁⟩ ⟨F₂, K₂⟩ => ?_)
  refine RelCT.assoc (rel_seq (callBlocks_rel L hV ok ct hR h28 F₁ F₂ [] (by agree_ppc []) ⟨_, by taint_decide⟩
      (fun s g _ => dataArgs_ok (by rw [g _ (by decide) (by decide) (by decide), F₁.r27]) hl
        (by rw [g _ (by decide) (by decide) (by decide), F₁.r23, h23]))
      (fun s g _ => dataArgs_ok (by rw [g _ (by decide) (by decide) (by decide), F₂.r27, e27]) hl
        (by rw [g _ (by decide) (by decide) (by decide), F₂.r23, h23₂]))
      (dstD ((hD₁.take' hmn).of_eq K₁.2.1 K₁.2.2)) (dstD ((hV.dbuf (hD₂.take' hmn)).of_eq K₂.2.1 K₂.2.2)))
    (callBlocks_ok L ok nf hR h28 F₁ (fun s g _ => dataArgs_ok (by rw [g _ (by decide) (by decide) (by decide), F₁.r27])
        hl (by rw [g _ (by decide) (by decide) (by decide), F₁.r23, h23]))
      (dstD ((hD₁.take' hmn).of_eq K₁.2.1 K₁.2.2)))
    (callBlocks_ok (hV.lay L) ok nf hR h28₂ F₂
      (fun s g _ => dataArgs_ok (by rw [g _ (by decide) (by decide) (by decide), F₂.r27]) hl
        (by rw [g _ (by decide) (by decide) (by decide), F₂.r23, h23₂]))
      (dstD ((hD₂.take' hmn).of_eq K₂.2.1 K₂.2.2))) fun u₁ u₂ P₁ P₂ => ?_)
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) hpost

end

/-- `r3 ← n / 16`, the number of whole blocks. -/
theorem bodyHead_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {n : Nat} (hn : n < 2 ^ 64)
    (h23 : V .r23 = BitVec.ofNat 64 n) :
    WP isa (.block [.lsr .d .r3 .r23 4]) s fun s₁ =>
      s₁.gpr .r3 = BitVec.ofNat 64 (n / 16) ∧ Env V sp s₁ ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr :=
  cwp_lsr (by decide) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, E.r23, h23, shr4 hn],
    E.others (rs := [.r3]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr, u₁.rd, u₁.wr⟩

/-- The whole blocks of `seal`, if any: the environment after them. -/
theorem wholeEnv_seal {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .r29)) 0) :
    WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block []) (whole encCall (addCk ++ xorOfs) xorOfs)))
      s fun t => Env V sp t ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .r29))
    (ckF1 := ckOf fun i => blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.PPC64LE.encryptBlocksF_correct encryptBlocks_noFrames hcall_enc sealPre_ok xorOfs_ok L E hR h28 h23 hD
    hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun _ P => ⟨P.env, P.rd, P.wr⟩

/-- The whole blocks of `open`, if any: the environment after them. -/
theorem wholeEnv_open {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {n : Nat}
    (h23 : V .r23 = BitVec.ofNat 64 n) (hD : DBuf (V .r29) (V .r31) s (V .r27) n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .r31 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .r29)) 0) :
    WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block []) (whole decCall xorOfs (xorOfs ++ addCk))))
      s fun t => Env V sp t ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .r29)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .r29) (16 * (R + 1)))
      (blockAtMem s.mem ((V .r27) + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .r29)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .r29)) (i + 1))
    Proof.Aes.PPC64LE.decryptBlocksF_correct decryptBlocks_noFrames hcall_dec xorOfs_ok openPost_ok L E hR h28 h23 hD
    hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun _ P => ⟨P.env, P.rd, P.wr⟩

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .r29) (V₁ .r31)) (hV : Agree V₁ V₂) {R : Nat}
  (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R)
include L hV hR h28

/-- `body`, in two runs, from what its whole blocks leave in each. -/
theorem body_rel (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {n : Nat}
    (h23 : V₁ .r23 = BitVec.ofNat 64 n) (hD₁ : DBuf (V₁ .r29) (V₁ .r31) σ₁ (V₁ .r27) n)
    (hD₂ : DBuf (V₂ .r29) (V₂ .r31) σ₂ (V₂ .r27) n)
    (W₁ : WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block [])
      (if enc then whole encCall (addCk ++ xorOfs) xorOfs else whole decCall xorOfs (xorOfs ++ addCk)))) σ₁
      fun t => Env V₁ sp t ∧ t.rd = σ₁.rd ∧ t.wr = σ₁.wr)
    (W₂ : WP isa (.seq (.block [.lsr .d .r3 .r23 4]) (.ite (.zero .d .r3) (.block [])
      (if enc then whole encCall (addCk ++ xorOfs) xorOfs else whole decCall xorOfs (xorOfs ++ addCk)))) σ₂
      fun t => Env V₂ sp t ∧ t.rd = σ₂.rd ∧ t.wr = σ₂.wr) :
    RelCT isa (Eq2 σ₁ σ₂) (body enc) TT := by
  have hn := hD₁.lt
  have h23₂ : V₂ .r23 = BitVec.ofNat 64 n := (hV .r23 (by decide)).symm.trans h23
  unfold body
  refine RelCT.assoc (rel_seq ?_ W₁ W₂ fun τ₁ τ₂ ⟨F₁, _⟩ ⟨F₂, _⟩ => ?_)
  · refine rel_seq (rel_env E₁ E₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) (bodyHead_ok E₁ hn h23)
      (bodyHead_ok E₂ hn h23₂) fun u₁ u₂ ⟨r3₁, U₁, rd₁, wr₁⟩ ⟨r3₂, U₂, rd₂, wr₂⟩ => ?_
    refine rel_ite (eval_zero r3₁ (by omega_using [hn])) (eval_zero r3₂ (by omega_using [hn])) (fun _ => rel_skip) fun _ => ?_
    cases enc <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact whole_rel L hV hR h28 Proof.Aes.PPC64LE.decryptBlocksF_correct Proof.Aes.PPC64LE.decryptBlocksF_ct
        decryptBlocks_noFrames [.r0, .r3, .r4, .r5, .r6, .r12, .r24, .r25, .r26] ⟨_, by taint_decide⟩
        ⟨_, by taint_decide⟩ (by decide +kernel) (by decide +kernel) (by decide) U₁ U₂ h23
        (hD₁.of_eq rd₁ wr₁) (hD₂.of_eq rd₂ wr₂)
    · exact whole_rel L hV hR h28 Proof.Aes.PPC64LE.encryptBlocksF_correct Proof.Aes.PPC64LE.encryptBlocksF_ct
        encryptBlocks_noFrames [.r0, .r3, .r4, .r5, .r6, .r12, .r24, .r25, .r26] ⟨_, by taint_decide⟩
        ⟨_, by taint_decide⟩ (by decide +kernel) (by decide +kernel) (by decide) U₁ U₂ h23
        (hD₁.of_eq rd₁ wr₁) (hD₂.of_eq rd₂ wr₂)
  refine rel_seq (rel_env F₁ F₂ hV [] (by agree_ppc []) ⟨_, by taint_decide⟩) (bodyTail_ok F₁ hn h23)
    (bodyTail_ok F₂ hn h23₂) fun w₁ w₂ ⟨r24₁, r25₁, g₁, k₁⟩ ⟨r24₂, r25₂, g₂, k₂⟩ => ?_
  exact rel_ite (eval_zero r25₁ (by omega_using [])) (eval_zero r25₂ (by omega_using [])) (fun _ => rel_skip) fun _ =>
    rest_rel L hV hR h28 enc (F₁.others g₁ k₁.sp k₁.rd k₁.wr) (F₂.others g₂ k₂.sp k₂.rd k₂.wr)
      (by rw [r24₁, r24₂, hV .r27 (by decide)]) (by rw [r25₁, r25₂])

end

end VG.Proof.AesOcb.PPC64LE

end

end

/-!
# AES-OCB on PPC64LE: `seal` and `open` up to the tag are constant time

Untrusted: everything here is checked by Lean. The entry loads `W` from the
stack argument at `sp + 112`, a public address, and then saves our caller's
registers through it: its head is checked on its own, and the rest from the
arguments and `W` (`entry_rel`). After it, the environment of each run is
its own registers (`EntryPost`), which agree on the public ones
(`agree_entry`). Then `nonce_rel`, `hash_rel`, `body_rel` and `tag_rel`,
each from the states the correctness proofs describe (`Seal.lean`), and the
code after the tag, which has no calls, from the public registers
(`front_rel`). As on AArch64 (`Proof/AesOcb/AArch64/Frame.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.AesGcm.PPC64LE (oneA_ok in_off add_ofNat_assoc)

/-- Two runs of `front; tail` are two runs of `front`'s pieces, then `tail`. -/
theorem rel_front {P Q : State → State → Prop} {e n h b t tail : Prog isa}
    (hr : RelCT isa P (.seq e (.seq n (.seq h (.seq b (.seq t tail))))) Q) :
    RelCT isa P (.seq (.seq e (.seq n (.seq h (.seq b t)))) tail) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq f₁ r₁ => cases f₁ with | seq a₁ f₁ => cases f₁ with | seq b₁ f₁ =>
  cases f₁ with | seq c₁ f₁ => cases f₁ with | seq d₁ g₁ =>
  cases e₂ with | seq f₂ r₂ => cases f₂ with | seq a₂ f₂ => cases f₂ with | seq b₂ f₂ =>
  cases f₂ with | seq c₂ f₂ => cases f₂ with | seq d₂ g₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq g₁ r₁)))))
    (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq g₂ r₂)))))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- The entry's stack arguments are where the state may read them. -/
theorem argsIn {s : State} (hA : Covers [⟨s.sp + BitVec.ofNat 64 96, 24⟩] (s.rd ++ s.wr)) {i : Nat} (hi : i < 3) :
    InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (96 + 8 * i)) 8 := by
  have := in_off hA (d := 8 * i) (n := 8) (by omega_using [hi]) (by decide)
  rwa [add_ofNat_assoc] at this

/-- The entry of `seal` and `open`, in two runs with the same arguments. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} (hW₁ : stackArg σ₁ 2 = W) (hW₂ : stackArg σ₂ 2 = W)
    (hA₁ : Covers [⟨σ₁.sp + BitVec.ofNat 64 96, 24⟩] (σ₁.rd ++ σ₁.wr))
    (hA₂ : Covers [⟨σ₂.sp + BitVec.ofNat 64 96, 24⟩] (σ₂.rd ++ σ₂.wr)) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  simp only [entry, Impl.AesGcm.PPC64LE.openEntry, Impl.AesGcm.PPC64LE.oneEntry, List.append_assoc]
  refine RelCT.block_append (rel_seq (rel_taint [] qsp (by agree_ppc []) ⟨_, by taint_decide⟩)
    (oneA_ok (off := 112) (W := W) (.inr rfl) (argsIn hA₁ (i := 2) (by decide)) (by rw [← hW₁, stackArg_eq']))
    (oneA_ok (off := 112) (W := W) (.inr rfl) (argsIn hA₂ (i := 2) (by decide)) (by rw [← hW₂, stackArg_eq']))
    fun τ₁ τ₂ ⟨a₁, g₁, k₁⟩ ⟨a₂, g₂, k₂⟩ => ?_)
  refine rel_taint [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12] (by rw [k₁.sp, k₂.sp, qsp]) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases h12 : r = .r12
  · subst h12; rw [a₁, a₂]
  · rw [g₁ r h12, g₂ r h12]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h12] at hr ⊢; exact hr)

/-- `nonce`, in two runs with the same nonce's address and length. -/
theorem nonce_rel {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .r29) (V₁ .r31)) (hV : Agree V₁ V₂) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R) {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h24 : σ₁.gpr .r24 = σ₂.gpr .r24) (h25 : σ₁.gpr .r25 = σ₂.gpr .r25) :
    RelCT isa (Eq2 σ₁ σ₂) nonce TT := by
  have h28₂ : V₂ .r28 = BitVec.ofNat 64 R := (hV .r28 (by decide)).symm.trans h28
  unfold nonce
  refine rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [.r24, .r25] (by agree_ppc [h24, h25]) ⟨_, by taint_decide⟩)
    [.r0, .r3, .r4, .r5, .r6] (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ F₁ F₂ => ?_
  refine rel_seq (encOne_rel L hV hR h28 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR h28 F₁ (by decide))
    (encOne_ok (hV.lay L) hR h28₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_ppc []) ⟨_, by taint_decide⟩

/-- The registers after the entry agree on the public ones in two runs with
the same arguments. -/
theorem agree_entry {σ₁ σ₂ τ₁ τ₂ : State} {W T : Addr} (P₁ : EntryPost W T σ₁ τ₁) (P₂ : EntryPost W T σ₂ τ₂)
    (hq : ∀ r ∈ [Reg.r3, .r4, .r6, .r7, .r8, .r9, .r10], σ₁.gpr r = σ₂.gpr r) (ht : stackArg σ₁ 1 = stackArg σ₂ 1) :
    Agree τ₁.gpr τ₂.gpr := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true] at hq
  obtain ⟨q3, q4, q6, q7, q8, q9, q10⟩ := hq
  simp only [Agree, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
  exact ⟨by rw [P₁.r18, P₂.r18, q6], by rw [P₁.r19, P₂.r19, ht], by rw [P₁.r20, P₂.r20],
    by rw [P₁.r21, P₂.r21, q7], by rw [P₁.r22, P₂.r22, q8], by rw [P₁.r23, P₂.r23, q10],
    by rw [P₁.r27, P₂.r27, q9], by rw [P₁.r28, P₂.r28, q4], by rw [P₁.r29, P₂.r29, q3],
    by rw [P₁.r31, P₂.r31]⟩

/-- What `HASH` needs after the entry and `nonce`. -/
theorem hctx_of {s₀ s₁ s₂ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (P₁ : EntryPost W T s₀ s₁) (h3 : s₀.gpr .r3 = K) {o : Block}
    (P₂ : NonceOk s₁.gpr s₀.sp o s₁ s₂) :
    HCtx (s₁.gpr .r29) (s₁.gpr .r31) D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al) s₂ ∧
      blockAtMem s₂.mem (s₁.gpr .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar s₀.mem K) 0 := by
  have hW₁ : s₁.gpr .r31 = W := P₁.r31
  have hK₁ : s₁.gpr .r29 = K := P₁.r29.trans h3
  have F₁ : Frame [⟨W, 512⟩] s₀.mem s₁.mem := frameW P₁.frame (entryR_W W)
  have pf₂ : Frame (nonceR W) s₁.mem s₂.mem := by have := P₂.frame; rwa [hW₁] at this
  have F₁₂ := F₁.trans (frameW pf₂ (nonceR_W W))
  refine ⟨{
      lay := by rw [hK₁, hW₁]; exact Ar.lay
      rounds := Ar.rounds
      ciph := by rw [hK₁, ctxCiph_W Ar.lay F₁₂ Ar.rounds]
      lstar := by rw [hK₁, ctxLstar_W Ar.lay F₁₂]
      buf := by rw [length_bytesAt, hW₁]; exact Ar.aad.of_eq (P₂.rd.trans P₁.keeps.rd) (P₂.wr.trans P₁.keeps.wr)
      aad := by rw [length_bytesAt, bytesAt_W Ar.aad.w Ar.aad.lt F₁₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := by rw [hK₁]; exact Ar.data.k
      dw := by rw [hW₁]; exact Ar.data.w }, ?_⟩
  rw [P₂.keep (by decide) (by decide), hW₁, P₁.l0, h3]

/-- `front enc d` and then code without calls, in two runs with the same
arguments. -/
theorem front_rel (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) {k : Prog isa}
    (hk : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR)) k h).isSome = true)
    {σ₁ σ₂ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (A₁ : FnArgs σ₁ K W N A D R nl al n tl T) (A₂ : FnArgs σ₂ K W N A D R nl al n tl T)
    (hW₁ : stackArg σ₁ 2 = W) (hT₁ : stackArg σ₁ 0 = T) (htl₁ : stackArg σ₁ 1 = BitVec.ofNat 64 tl)
    (h3₁ : σ₁.gpr .r3 = K) (h4₁ : σ₁.gpr .r4 = BitVec.ofNat 64 R) (h5₁ : σ₁.gpr .r5 = N)
    (h6₁ : σ₁.gpr .r6 = BitVec.ofNat 64 nl) (h7₁ : σ₁.gpr .r7 = A) (h8₁ : σ₁.gpr .r8 = BitVec.ofNat 64 al)
    (h9₁ : σ₁.gpr .r9 = D) (h10₁ : σ₁.gpr .r10 = BitVec.ofNat 64 n)
    (hW₂ : stackArg σ₂ 2 = W) (hT₂ : stackArg σ₂ 0 = T) (htl₂ : stackArg σ₂ 1 = BitVec.ofNat 64 tl)
    (h3₂ : σ₂.gpr .r3 = K) (h4₂ : σ₂.gpr .r4 = BitVec.ofNat 64 R) (h5₂ : σ₂.gpr .r5 = N)
    (h6₂ : σ₂.gpr .r6 = BitVec.ofNat 64 nl) (h7₂ : σ₂.gpr .r7 = A) (h8₂ : σ₂.gpr .r8 = BitVec.ofNat 64 al)
    (h9₂ : σ₂.gpr .r9 = D) (h10₂ : σ₂.gpr .r10 = BitVec.ofNat 64 n) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (front enc d) k) TT := by
  have L₁ : Lay (σ₁.gpr .r3) W := by rw [h3₁]; exact A₁.lay
  have L₂ : Lay (σ₂.gpr .r3) W := by rw [h3₂]; exact A₂.lay
  have hC₁ : Covers [⟨σ₁.gpr .r3, 256⟩] (σ₁.rd ++ σ₁.wr) := by rw [h3₁]; exact A₁.perm.k
  have hC₂ : Covers [⟨σ₂.gpr .r3, 256⟩] (σ₂.rd ++ σ₂.wr) := by rw [h3₂]; exact A₂.perm.k
  unfold front
  refine rel_front (rel_seq (entry_rel hW₁ hW₂ A₁.args A₂.args qsp
      (by agree_ppc [h3₁, h3₂, h4₁, h4₂, h5₁, h5₂, h6₁, h6₂, h7₁, h7₂, h8₁, h8₂, h9₁, h9₂, h10₁, h10₂]))
    (entry_ok L₁ A₁.perm.w hC₁ hW₁ hT₁ A₁.args A₁.argsW) (entry_ok L₂ A₂.perm.w hC₂ hW₂ hT₂ A₂.args A₂.argsW)
    fun τ₁ τ₂ P₁ P₂ => ?_)
  have hV : Agree τ₁.gpr τ₂.gpr := agree_entry P₁ P₂
    (by agree_ppc [h3₁, h3₂, h4₁, h4₂, h6₁, h6₂, h7₁, h7₂, h8₁, h8₂, h9₁, h9₂, h10₁, h10₂]) (by rw [htl₁, htl₂])
  have E₁ := P₁.env
  have E₂ := P₂.env
  rw [← qsp] at E₂
  have L : Lay (τ₁.gpr .r29) (τ₁.gpr .r31) := by rw [P₁.r29, P₁.r31, h3₁]; exact A₁.lay
  have h28 : τ₁.gpr .r28 = BitVec.ofNat 64 R := P₁.r28.trans h4₁
  have h28₂ : τ₂.gpr .r28 = BitVec.ofNat 64 R := P₂.r28.trans h4₂
  have L₂' : Lay (τ₂.gpr .r29) (τ₂.gpr .r31) := hV.lay L
  have hn1 := A₁.n1
  have hn15 := A₁.n15
  have ht : tl < 2 ^ 64 := by have := A₁.t16; omega_using [this]
  -- `nonce` and `HASH`
  refine RelCT.assoc (rel_seq (rel_seq (nonce_rel L hV A₁.rounds h28 E₁ E₂ (by rw [P₁.r24, P₂.r24, h5₁, h5₂])
      (by rw [P₁.r25, P₂.r25, h6₁, h6₂]))
    (nonce_ok L A₁.rounds h28 E₁ (P₁.r24.trans h5₁) (P₁.r25.trans h6₁) (P₁.r19.trans htl₁) hn1 hn15 ht
      (by rw [P₁.r31]; exact A₁.nonce.of_eq P₁.keeps.rd P₁.keeps.wr) (by rw [P₁.r29, h3₁]; exact A₁.data.k))
    (nonce_ok L₂' A₁.rounds h28₂ E₂ (P₂.r24.trans h5₂) (P₂.r25.trans h6₂) (P₂.r19.trans htl₂) hn1 hn15 ht
      (by rw [P₂.r31]; exact A₂.nonce.of_eq P₂.keeps.rd P₂.keeps.wr) (by rw [P₂.r29, h3₂]; exact A₂.data.k))
    fun u₁ u₂ Q₁ Q₂ => ?_) (preRest_wp A₁ P₁ htl₁ h3₁ h4₁ h5₁ h6₁ h7₁ h8₁)
    (preRest_wp A₂ P₂ htl₂ h3₂ h4₂ h5₂ h6₂ h7₂ h8₂) fun w₁ w₂ R₁ R₂ => ?_)
  · have E₂' := Q₂.env
    rw [qsp] at Q₂
    obtain ⟨C₁, l0₁⟩ := hctx_of A₁ P₁ h3₁ Q₁
    obtain ⟨C₂, l0₂⟩ := hctx_of A₂ P₂ h3₂ Q₂
    exact hash_rel hV C₁ C₂ h28 (by rw [length_bytesAt, length_bytesAt]) Q₁.env E₂'
      (P₁.r21.trans h7₁) (by rw [P₁.r22, h8₁, length_bytesAt]) l0₁ l0₂
  -- the data and the tag
  have F₁ := R₁.env
  have F₂ := R₂.env
  rw [← qsp] at F₂
  have h23 : τ₁.gpr .r23 = BitVec.ofNat 64 n := P₁.r23.trans h10₁
  have h23₂ : τ₂.gpr .r23 = BitVec.ofNat 64 n := P₂.r23.trans h10₂
  have hD₁ : DBuf (τ₁.gpr .r29) (τ₁.gpr .r31) w₁ (τ₁.gpr .r27) n := by
    rw [P₁.r29, P₁.r31, P₁.r27, h3₁, h9₁]; exact A₁.data.of_eq R₁.rd R₁.wr
  have hD₂ : DBuf (τ₂.gpr .r29) (τ₂.gpr .r31) w₂ (τ₂.gpr .r27) n := by
    rw [P₂.r29, P₂.r31, P₂.r27, h3₂, h9₂]; exact A₂.data.of_eq R₂.rd R₂.wr
  have l0₁ : blockAtMem w₁.mem (τ₁.gpr .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar w₁.mem (τ₁.gpr .r29)) 0 := by
    rw [P₁.r31, P₁.r29, R₁.l0, h3₁, ctxLstar_W A₁.lay R₁.frame]
  have l0₂ : blockAtMem w₂.mem (τ₂.gpr .r31 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar w₂.mem (τ₂.gpr .r29)) 0 := by
    rw [P₂.r31, P₂.r29, R₂.l0, h3₂, ctxLstar_W A₂.lay R₂.frame]
  have o₁ := R₁.ofs
  have o₂ := R₂.ofs
  have z₁ := R₁.o0
  have z₂ := R₂.o0
  have c₁ := R₁.ck
  have c₂ := R₂.ck
  rw [← P₁.r31] at o₁ z₁ c₁
  rw [← P₂.r31] at o₂ z₂ c₂
  cases enc
  · refine rel_seq (body_rel L hV A₁.rounds h28 false F₁ F₂ h23 hD₁ hD₂
        (wholeEnv_open L F₁ A₁.rounds h28 h23 hD₁ o₁ z₁ c₁ l0₁)
        (wholeEnv_open L₂' F₂ A₁.rounds h28₂ h23₂ hD₂ o₂ z₂ c₂ l0₂))
      (WP.mono (bodyOpen_ok L F₁ A₁.rounds h28 h23 hD₁ o₁ z₁ c₁ l0₁) fun _ B => B.env)
      (WP.mono (bodyOpen_ok L₂' F₂ A₁.rounds h28₂ h23₂ hD₂ o₂ z₂ c₂ l0₂) fun _ B => B.env) fun y₁ y₂ G₁ G₂ => ?_
    refine rel_seq (tag_rel L hV A₁.rounds h28 G₁ G₂ hd) (tag_ok L G₁ A₁.rounds h28 hd)
      (tag_ok L₂' G₂ A₁.rounds h28₂ hd) fun x₁ x₂ T₁ T₂ => ?_
    exact rel_env T₁.env T₂.env hV [] (by agree_ppc []) hk
  · refine rel_seq (body_rel L hV A₁.rounds h28 true F₁ F₂ h23 hD₁ hD₂
        (wholeEnv_seal L F₁ A₁.rounds h28 h23 hD₁ o₁ z₁ c₁ l0₁)
        (wholeEnv_seal L₂' F₂ A₁.rounds h28₂ h23₂ hD₂ o₂ z₂ c₂ l0₂))
      (WP.mono (bodySeal_ok L F₁ A₁.rounds h28 h23 hD₁ o₁ z₁ c₁ l0₁) fun _ B => B.env)
      (WP.mono (bodySeal_ok L₂' F₂ A₁.rounds h28₂ h23₂ hD₂ o₂ z₂ c₂ l0₂) fun _ B => B.env) fun y₁ y₂ G₁ G₂ => ?_
    refine rel_seq (tag_rel L hV A₁.rounds h28 G₁ G₂ hd) (tag_ok L G₁ A₁.rounds h28 hd)
      (tag_ok L₂' G₂ A₁.rounds h28₂ hd) fun x₁ x₂ T₁ T₂ => ?_
    exact rel_env T₁.env T₂.env hV [] (by agree_ppc []) hk

end VG.Proof.AesOcb.PPC64LE

end

end

/-!
# AES-OCB on PPC64LE: `vg_aes_ocb_seal` and `vg_aes_ocb_open` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments (`onePub`) have the same arguments of `front_rel` (`FnArgs`, with
the values of the first run). After `front`, `seal` copies the tag out and
restores our caller's registers; `open` copies the received tag, compares
it with the one it computed and masks the data without a branch, and
restores them: code without calls, which the taint analysis checks from the
public registers. `open` leaks nothing more than `seal`, in particular not
whether the tag is right.
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE

/-- `FnArgs` in two runs with the same public arguments, with the values of
the first. -/
theorem args₂_of {σ₁ σ₂ : State} (hq : onePub σ₁ σ₂)
    (A₂ : FnArgs σ₂ (σ₂.gpr .r3) (stackArg σ₂ 2) (σ₂.gpr .r5) (σ₂.gpr .r7) (σ₂.gpr .r9) (σ₂.gpr .r4).toNat
      (σ₂.gpr .r6).toNat (σ₂.gpr .r8).toNat (σ₂.gpr .r10).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0)) :
    FnArgs σ₂ (σ₁.gpr .r3) (stackArg σ₁ 2) (σ₁.gpr .r5) (σ₁.gpr .r7) (σ₁.gpr .r9) (σ₁.gpr .r4).toNat
      (σ₁.gpr .r6).toNat (σ₁.gpr .r8).toNat (σ₁.gpr .r10).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0) := by
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, -, qa⟩ := hq
  rw [← q3, ← q4, ← q5, ← q6, ← q7, ← q8, ← q9, ← q10, ← qa 0 (by decide), ← qa 1 (by decide),
    ← qa 2 (by decide)] at A₂
  exact A₂

/-- `front enc d; k` in two runs with the same public arguments. -/
theorem front_relq (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) {k : Prog isa}
    (hk : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR)) k h).isSome = true) {σ₁ σ₂ : State}
    (A₁ : FnArgs σ₁ (σ₁.gpr .r3) (stackArg σ₁ 2) (σ₁.gpr .r5) (σ₁.gpr .r7) (σ₁.gpr .r9) (σ₁.gpr .r4).toNat
      (σ₁.gpr .r6).toNat (σ₁.gpr .r8).toNat (σ₁.gpr .r10).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (A₂ : FnArgs σ₂ (σ₂.gpr .r3) (stackArg σ₂ 2) (σ₂.gpr .r5) (σ₂.gpr .r7) (σ₂.gpr .r9) (σ₂.gpr .r4).toNat
      (σ₂.gpr .r6).toNat (σ₂.gpr .r8).toNat (σ₂.gpr .r10).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0))
    (hq : onePub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.seq (front enc d) k) TT := by
  have A₂' := args₂_of hq A₂
  obtain ⟨q3, q4, q5, q6, q7, q8, q9, q10, qsp, qa⟩ := hq
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have o' : ∀ {x y : BitVec 64}, x = y → y = BitVec.ofNat 64 x.toNat := fun h => by rw [h]; exact o _
  exact front_rel enc hd hk A₁ A₂' rfl rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _)
    (qa 2 (by decide)).symm (qa 0 (by decide)).symm (o' (qa 1 (by decide))) q3.symm (o' q4) q5.symm (o' q6)
    q7.symm (o' q8) q9.symm (o' q10) qsp

theorem seal_ct : ConstantTime isa sealPPC64LE.pre sealPPC64LE.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  unfold «seal»
  refine front_relq true (.inl rfl) ?_ (sealArgs_of h₁) (sealArgs_of h₂) hq
  exact ⟨_, by taint_decide⟩

theorem open_ct : ConstantTime isa openPPC64LE.pre openPPC64LE.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  unfold «open»
  refine front_relq false (.inr rfl) ?_ (openArgs_of h₁) (openArgs_of h₂) hq.1
  exact ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.PPC64LE
