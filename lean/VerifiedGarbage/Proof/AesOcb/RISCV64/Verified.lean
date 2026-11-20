module

public import VerifiedGarbage.Proof.AesOcb.Scratch
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Open
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesOcb.RISCV64
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Impl.StackScratch.RISCV64.Args
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgs
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Open
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.Spill
meta import VerifiedGarbage.Impl.AesOcb.RISCV64
meta import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.Ocb.Bytes
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
import VerifiedGarbage.Proof.AesOcb.RISCV64.RestTag
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ocb.Spec
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Words
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.RestTag
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Hash
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Hash
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Args
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.AesOcb.RISCV64.Fn
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
public meta import Lean.Elab.Tactic.Basic
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Args
meta import VerifiedGarbage.Proof.Framework.RISCV64.Keep
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.Taint

/-! ### `AesOcb.RISCV64.CTBase`, which only this module used -/

section

/-!
# AES-OCB on RISC-V: relating two runs

Untrusted: everything here is checked by Lean. The constant-time proofs
relate two runs from given states (`Eq2 σ₁ σ₂`) piece by piece, as on
PPC64LE (`Proof/AesOcb/PPC64LE/FnCT.lean`): the code between calls by the
taint analysis, from the registers the environments fix to the same public
values in both runs (`pubR`: the lengths, the tag, the rounds, the key
context and `W`) and others the correctness proofs pin (`rel_env`); each
call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` with the same
arguments in both runs (`callBlocks_rel`); a branch both runs take the same
way (`rel_ite`); and the next piece from the states the correctness proofs
describe (`rel_seq`), or, after code without calls that writes none of the
registers the environment fixes, from the environment alone (`rel_seqEnv`).
The environments of the two runs fix their registers to values `V₁` and
`V₂` that agree on `pubR` (`Agree`). The taint analysis takes memory as
secret, so a block that loads a public value (a count kept in `W`, or the
address of the associated data or the data, kept in their slots) and uses it
as an address or a count is split after the load.
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64
open VG.Proof.AesGcm.RISCV64 (frozen Keeps)

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

/-- The registers that hold public values throughout: `W`, the key context,
the rounds, the nonce's length, the tag's length, the tag, the length of
the associated data and the length of the data. -/
abbrev pubR : List Reg := [.s0, .s2, .s3, .s7, .s8, .s9, .s10, .s11]

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
registers, the permissions and the stack pointer. -/
theorem exec_keep {c : Prog isa} (rs : List Reg) (hc : writesOnly rs c = true) (hn : callFree c = true)
    {s s' : State} {t : List Leak} (h : Exec isa c s t s') : Keep rs s s' ∧ s'.sp = s.sp := by
  refine ⟨⟨fun r hr => Exec.gpr_callFree (fun i hi => ?_) h hn, (Exec.rdwr h).1, (Exec.rdwr h).2.1⟩,
    (Exec.rdwr h).2.2⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have hh := hc i hi
  intro hd
  rw [hd] at hh
  exact hr (List.contains_iff_mem.mp hh)

/-- An environment, after code without calls that writes none of its registers. -/
theorem Env.exec {V : Reg → BitVec 64} {sp : Addr} {s s' : State} {c : Prog isa} {t : List Leak} (E : Env V sp s)
    (h : Exec isa c s t s') (rs : List Reg) (hc : writesOnly rs c = true) (hn : callFree c = true)
    (hd : ∀ r ∈ frozen, r ∉ rs := by decide) : Env V sp s' :=
  let ⟨k, sp⟩ := exec_keep rs hc hn h
  E.others k.1 sp k.2.1 k.2.2 hd

/-- Then: the next piece, in the environments, after code without calls that
writes only `rs`, none of their registers. -/
theorem rel_seqEnv {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {c₁ c₂ : Prog isa} {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (rs : List Reg)
    (hc : writesOnly rs c₁ = true) (hn : callFree c₁ = true) (hd : ∀ r ∈ frozen, r ∉ rs)
    (h₂ : ∀ τ₁ τ₂, Env V₁ sp τ₁ → Env V₂ sp τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT :=
  rel_seqE h₁ (fun _ _ h => E₁.exec h rs hc hn hd) (fun _ _ h => E₂.exec h rs hc hn hd) h₂

/-! ## Calls -/

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .s2) (V₁ .s0)) (hV : Agree V₁ V₂)
include L hV

theorem Agree.lay : Lay (V₂ .s2) (V₂ .s0) := by
  rw [← hV .s2 (by decide), ← hV .s0 (by decide)]; exact L

/-- A call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on the same
`k` blocks at `D` in both runs. -/
theorem callBlocks_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksRISCV64 f).pre (Proof.Aes.blocksRISCV64 f).pub c)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V₁ .s3 = BitVec.ofNat 64 R) {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {args : List Instr} (rs : List Reg)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ h, (VG.Taint.check taint (Taint.ofRegs (rs ++ pubR)) (.block (callArgs ++ args)) h).isSome = true)
    {D : Addr} {k : Nat}
    (ha₁ : ∀ s₁, (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₁.gpr r = σ₁.gpr r) → Keeps σ₁ s₁ → ArgsOk args s₁ D k)
    (ha₂ : ∀ s₁, (∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₁.gpr r = σ₂.gpr r) → Keeps σ₂ s₁ → ArgsOk args s₁ D k)
    (hD₁ : Dst (V₁ .s2) (V₁ .s0) σ₁ D k) (hD₂ : Dst (V₁ .s2) (V₁ .s0) σ₂ D k) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block (callArgs ++ args)) (.call name c)) TT := by
  have e2 := hV .s2 (by decide)
  have e0 := hV .s0 (by decide)
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  refine rel_seq (rel_env E₁ E₂ hV rs hr hc) (callArgs_ok L hR hs3 E₁ ha₁ hD₁)
    (callArgs_ok (hV.lay L) hR hs3₂ E₂ ha₂ (by rw [← e2, ← e0]; exact hD₂)) fun τ₁ τ₂ h₁ h₂ => ?_
  refine blk_rel ok ct fun a b hab => ?_
  obtain ⟨rfl, rfl⟩ := hab
  rw [← e2, ← e0] at h₂
  exact ⟨V₁ .s2, D, V₁ .s0 + BitVec.ofNat 64 512, R, k, h₁.1, h₂.1,
    by rw [h₁.2.2.sp, h₂.2.2.sp, E₁.sp, E₂.sp]⟩

/-- `encOne d`, in two runs. -/
theorem encOne_rel {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V₁ .s3 = BitVec.ofNat 64 R) {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {d : Nat} (hd : d + 16 ≤ 512)
    (hc : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR))
      (.block (callArgs ++ ([.addi .a2 .s0 (d : Int), .li .a3 1] : List Instr))) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (encOne d) TT :=
  callBlocks_rel L hV Proof.Aes.RISCV64.encryptBlocks_correct Proof.Aes.RISCV64.encryptBlocks_ct hR hs3 E₁ E₂ []
    (fun _ h => absurd h List.not_mem_nil) hc
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E₁.s0]) (by omega_using [hd]))
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E₂.s0, ← hV .s0 (by decide)])
      (by omega_using [hd]))
    (dstW L E₁.perm (by omega_using [hd])) (dstW L (by rw [hV .s2 (by decide), hV .s0 (by decide)]; exact E₂.perm) (by omega_using [hd]))

end

/-- Proves `∀ r ∈ [r₁, …], σ₁.gpr r = σ₂.gpr r` by rewriting each side with `ts`. -/
tactic_template "agree_rv64" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  plain_simp_names simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true,
    and_self, $ts,*])

end VG.Proof.AesOcb.RISCV64

end

end

/-! ### `AesOcb.RISCV64.FnCT`, which only this module used -/

section

/-! ### `AesOcb.RISCV64.FrontCT`, which only this module used -/

section

/-! ### `AesOcb.RISCV64.HashCT`, which only this module used -/

section

/-!
# AES-OCB on RISC-V: `HASH` is constant time

Untrusted: everything here is checked by Lean. The two runs hash associated
data of the same length at the same address `A`, which each loads from its
slot in `W`. That address and the counts of blocks a chunk loads from `W`
(the blocks left, at `W + hlO`, and the chunk's, at `W + cnO`), which the
taint analysis takes as secret, are the same in both runs by the correctness
proofs (`HInv`, `FillInv`), which also pin the pointer `s4` and the index
`s6`: the blocks are split after each load (`chunkLd_ok`, `sumArgs_ok`).
Each chunk fills its buffer and adds it to the sum by code the taint
analysis checks, with the call between on the same arguments (`chunk_rel`);
both runs are at the same chunk at each iteration (`hashLoop_rel`); the
rest, if any, likewise (`hashRest_rel`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/FnCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64
open VG.Spec.Ocb (Block Cipher)
open VG.Proof.AesGcm.RISCV64 (frozen Keeps)

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
theorem Agree.perm {V₁ V₂ : Reg → BitVec 64} (hV : Agree V₁ V₂) {s : State} (h : Perm (V₂ .s2) (V₂ .s0) s) :
    Perm (V₁ .s2) (V₁ .s0) s := by
  rw [hV .s2 (by decide), hV .s0 (by decide)]; exact h

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (hV : Agree V₁ V₂)
include hV

/-- The rest of the associated data, in two runs from the same `s4` and `s5`. -/
theorem hashRest_rel (L : Lay (V₁ .s2) (V₁ .s0)) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hs3 : V₁ .s3 = BitVec.ofNat 64 R) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂)
    (h4 : σ₁.gpr .s4 = σ₂.gpr .s4) (h5 : σ₁.gpr .s5 = σ₂.gpr .s5) :
    RelCT isa (Eq2 σ₁ σ₂) hashRest TT := by
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  unfold hashRest
  refine RelCT.assoc (RelCT.assoc (rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [.s4, .s5] (by agree_rv64 [h4, h5])
    ⟨_, by taint_decide⟩) [.t0, .t1, .t2, .t3, .a0, .a1, .a2, .a3] (by decide +kernel) (by decide +kernel)
    (by decide) fun τ₁ τ₂ F₁ F₂ => ?_))
  refine rel_seq (encOne_rel L hV hR hs3 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR hs3 F₁ (by decide))
    (encOne_ok (hV.lay L) hR hs3₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

variable {D : Addr} {n R : Nat} {A : Addr} {ciph₁ ciph₂ : Cipher} {l₁ l₂ : Block} {a₁ a₂ : List Byte}
  {s₁ s₂ : State} (C₁ : HCtx (V₁ .s2) (V₁ .s0) D n R ciph₁ l₁ A a₁ s₁)
  (C₂ : HCtx (V₂ .s2) (V₂ .s0) D n R ciph₂ l₂ A a₂ s₂) (hs3 : V₁ .s3 = BitVec.ofNat 64 R)
  (hlen : a₂.length = a₁.length)
include C₁ C₂ hs3 hlen

/-- A chunk, in two runs at the same block `j`. -/
theorem chunk_rel {τ₁ τ₂ : State} {j : Nat} (H₁ : HInv V₁ sp ciph₁ l₁ A a₁ s₁ τ₁ j)
    (H₂ : HInv V₂ sp ciph₂ l₂ A a₂ s₂ τ₂ j) (hj : j < a₁.length / 16) : RelCT isa (Eq2 τ₁ τ₂) hashChunk TT := by
  have hs := C₁.short
  have L := C₁.lay
  have e0 := hV .s0 (by decide)
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  have hl₂ := H₂.hl
  rw [hlen] at hl₂
  unfold hashChunk
  refine RelCT.assoc (rel_seq ?_ (chunkHead_ok (k := a₁.length / 16 - j) L H₁.env.s0 H₁.env.perm.w
      (by omega_arith) H₁.hl)
    (chunkHead_ok (k := a₁.length / 16 - j) C₂.lay H₂.env.s0 H₂.env.perm.w (by omega_arith) hl₂)
    fun t₁ t₂ ⟨h5₁, g₁, k₁⟩ ⟨h5₂, g₂, k₂⟩ => ?_)
  · -- the number of blocks of the chunk, from those left
    refine rel_seq (rel_env H₁.env H₂.env hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
      (chunkLd_ok (k := a₁.length / 16 - j) L H₁.env.s0 H₁.env.perm.w (by omega_arith) H₁.hl)
      (chunkLd_ok (k := a₁.length / 16 - j) C₂.lay H₂.env.s0 H₂.env.perm.w (by omega_arith) hl₂)
      fun u₁ u₂ ⟨r1₁, r2₁, _, k₁⟩ ⟨r1₂, r2₂, _, k₂⟩ => ?_
    have hsp : u₁.sp = u₂.sp := by rw [k₁.sp, k₂.sp, H₁.env.sp, H₂.env.sp]
    refine rel_ite (eval_zero r2₁ (by omega_arith)) (eval_zero r2₂ (by omega_arith)) (fun _ => ?_) (fun _ => ?_)
    · exact rel_taint [.t1] hsp (by agree_rv64 [r1₁, r1₂]) ⟨_, by taint_decide⟩
    · exact rel_taint [] hsp (by agree_rv64 []) ⟨_, by taint_decide⟩
  have E₁ := H₁.env.keep3 g₁ k₁
  have E₂ := H₂.env.keep3 g₂ k₂
  -- the counts stored
  refine rel_seq (rel_env E₁ E₂ hV [.s5] (by agree_rv64 [h5₁, h5₂]) ⟨_, by taint_decide⟩)
    (chunkMid_ok C₁ H₁ (c := min 8 (a₁.length / 16 - j)) (by omega_arith) g₁ k₁ h5₁)
    (chunkMid_ok C₂ H₂ (c := min 8 (a₁.length / 16 - j)) (by omega_arith) g₂ k₂ h5₂) fun w₁ w₂ F₁ F₂ => ?_
  -- the buffer filled
  refine rel_seq (rel_env F₁.env F₂.env hV [.a7, .s4, .s5, .s6]
      (by agree_rv64 [F₁.a7, F₂.a7, F₁.s4, F₂.s4, F₁.s5, F₂.s5, F₁.s6, F₂.s6, e0]) ⟨_, by taint_decide⟩)
    (fill_ok C₁ (by omega_arith) (by omega_arith) (by omega_arith) F₁)
    (fill_ok C₂ (by omega_arith) (by omega_arith) (by omega_arith) F₂)
    fun y₁ y₂ G₁ G₂ => ?_
  -- enciphered
  let c := min 8 (a₁.length / 16 - j)
  refine RelCT.assoc (rel_seq (F₁ := fun z => Env V₁ sp z ∧
      z.mem.readW (V₁ .s0 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c)
    (F₂ := fun z => Env V₂ sp z ∧ z.mem.readW (V₂ .s0 + BitVec.ofNat 64 cnO) 64 = BitVec.ofNat 64 c)
    (callBlocks_rel L hV Proof.Aes.RISCV64.encryptBlocks_correct
      Proof.Aes.RISCV64.encryptBlocks_ct C₁.rounds hs3 G₁.env G₂.env [] (by agree_rv64 []) ⟨_, by taint_decide⟩
      (fun s g k => bufArgs_ok L (by rw [g _ (by decide) (by decide) (by decide), G₁.env.s0])
        (by rw [k.wr]; exact G₁.env.perm.w) (by rw [k.mem, G₁.cn]))
      (fun s g k => bufArgs_ok L (by rw [g _ (by decide) (by decide) (by decide), G₂.env.s0, e0])
        (by rw [k.wr, e0]; exact G₂.env.perm.w) (by rw [k.mem, e0, G₂.cn]))
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith))
      (dstW L (hV.perm G₂.env.perm) (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
    (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) L Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames
      C₁.rounds hs3 G₁.env
      (fun s g k => bufArgs_ok L (by rw [g _ (by decide) (by decide) (by decide), G₁.env.s0])
        (by rw [k.wr]; exact G₁.env.perm.w) (by rw [k.mem, G₁.cn]))
      (dstW L G₁.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
      fun z P => ⟨P.env G₁.env, (bufCall_readW L P (by omega_arith) (d := cnO) (by decide)).trans G₁.cn⟩)
    (WP.mono (callBlocks_ok (f := Spec.Aes.cipher) (hV.lay L) Proof.Aes.RISCV64.encryptBlocks_correct
      encryptBlocks_noFrames C₁.rounds hs3₂ G₂.env
      (fun s g k => bufArgs_ok (hV.lay L) (by rw [g _ (by decide) (by decide) (by decide), G₂.env.s0])
        (by rw [k.wr]; exact G₂.env.perm.w) (by rw [k.mem, G₂.cn]))
      (dstW (hV.lay L) G₂.env.perm (d := 384) (n := min 8 (a₁.length / 16 - j)) (by omega_arith)))
      fun z P => ⟨P.env G₂.env, (bufCall_readW (hV.lay L) P (by omega_arith) (d := cnO) (by decide)).trans G₂.cn⟩)
    fun z₁ z₂ ⟨Z₁, cn₁⟩ ⟨Z₂, cn₂⟩ => ?_)
  -- the buffer added to the sum
  refine rel_seq (rel_env Z₁ Z₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (sumArgs_ok L Z₁.s0 Z₁.perm.w cn₁) (sumArgs_ok (hV.lay L) Z₂.s0 Z₂.perm.w cn₂)
    fun x₁ x₂ ⟨a7₁, s5₁, g₁', k₁'⟩ ⟨a7₂, s5₂, g₂', k₂'⟩ => ?_
  have X₁ := Z₁.keep2 g₁' k₁'
  have X₂ := Z₂.keep2 g₂' k₂'
  refine rel_seqEnv X₁ X₂ (rel_env X₁ X₂ hV [.a7, .s5] (by agree_rv64 [a7₁, a7₂, s5₁, s5₂, e0])
    ⟨_, by taint_decide⟩) sumRegs (by decide +kernel) (by decide +kernel) (by decide) fun _ _ e₁ e₂ => ?_
  exact rel_env e₁ e₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

/-- The chunks, in two runs. -/
theorem hashLoop_rel {τ₁ τ₂ : State} (H₁ : HInv V₁ sp ciph₁ l₁ A a₁ s₁ τ₁ 0)
    (H₂ : HInv V₂ sp ciph₂ l₂ A a₂ s₂ τ₂ 0) (hm : 0 < a₁.length / 16) :
    RelCT isa (Eq2 τ₁ τ₂) (.loop hashChunk (.nonzero .t1)) TT := by
  have hs := C₁.short
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  refine (RelCT.loop (Q := TT)
    (fun (k : Nat) (u₁ u₂ : State) => ∃ j, k = a₁.length / 16 - j ∧ j < a₁.length / 16 ∧
      HInv V₁ sp ciph₁ l₁ A a₁ s₁ u₁ j ∧ HInv V₂ sp ciph₂ l₂ A a₂ s₂ u₂ j) (fun k => ?_)
    (a₁.length / 16 - 0)).mono (fun x y hxy => by obtain ⟨rfl, rfl⟩ := hxy; exact ⟨0, rfl, hm, H₁, H₂⟩)
    fun _ _ h => h
  refine rel_of_pt fun σ₁ σ₂ ⟨j, hk, hj, G₁, G₂⟩ => ?_
  refine ((chunk_rel hV C₁ C₂ hs3 hlen G₁ G₂ hj).wp
    (F₁ := fun u => HInv V₁ sp ciph₁ l₁ A a₁ s₁ u (j + min 8 (a₁.length / 16 - j)))
    (F₂ := fun u => HInv V₂ sp ciph₂ l₂ A a₂ s₂ u (j + min 8 (a₂.length / 16 - j))) fun x y hxy => by
      obtain ⟨rfl, rfl⟩ := hxy
      exact ⟨hashChunk_ok C₁ hs3 G₁ hj, hashChunk_ok C₂ hs3₂ G₂ (by rw [hlen]; exact hj)⟩).mono (fun _ _ h => h)
    fun u₁ u₂ ⟨_, F₁, F₂⟩ => ?_
  rw [hlen] at F₂
  have ev₁ := eval_nonzero F₁.t1 (by omega_arith)
  have t1₂ := F₂.t1
  rw [hlen] at t1₂
  have ev₂ := eval_nonzero t1₂ (by omega_arith)
  refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun h => ?_⟩
  rw [ev₁] at h
  have he : ¬ a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)) = 0 := by simpa using h
  exact ⟨a₁.length / 16 - (j + min 8 (a₁.length / 16 - j)), by omega_arith, j + min 8 (a₁.length / 16 - j), rfl,
    by omega_arith, F₁, F₂⟩

/-- `HASH`, in two runs, each with `A` in its slot of `W`. -/
theorem hash_rel (E₁ : Env V₁ sp s₁) (E₂ : Env V₂ sp s₂)
    (hA₁ : s₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 Impl.AesGcm.RISCV64.aadO) 64 = A)
    (hA₂ : s₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 Impl.AesGcm.RISCV64.aadO) 64 = A)
    (h10 : V₁ .s10 = BitVec.ofNat 64 a₁.length)
    (hl0₁ : Spec.Ocb.blockAtMem s₁.mem (V₁ .s0 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l₁ 0)
    (hl0₂ : Spec.Ocb.blockAtMem s₂.mem (V₂ .s0 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt l₂ 0) :
    RelCT isa (Eq2 s₁ s₂) Impl.AesOcb.RISCV64.hash TT := by
  have hs := C₁.short
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  have h10₂ : V₂ .s10 = BitVec.ofNat 64 a₂.length := by rw [← hV .s10 (by decide), h10, hlen]
  unfold Impl.AesOcb.RISCV64.hash
  refine rel_seq (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) (hashHead_ok C₁ E₁ hA₁ h10 hl0₁)
    (hashHead_ok C₂ E₂ hA₂ h10₂ hl0₂) fun t₁ t₂ H₁ H₂ => ?_
  have t1₂ := H₂.t1
  rw [hlen] at t1₂
  refine rel_seq (rel_ite (eval_zero H₁.t1 (by omega_arith)) (eval_zero t1₂ (by omega_arith)) (fun _ => rel_skip)
      (fun hb => hashLoop_rel hV C₁ C₂ hs3 hlen H₁ H₂ (Nat.pos_of_ne_zero (of_decide_eq_false hb))))
    (hashBody_ok C₁ hs3 H₁) (hashBody_ok C₂ hs3₂ H₂) fun u₁ u₂ G₁ G₂ => ?_
  refine rel_seq (rel_env G₁.env G₂.env hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) (tailHead_ok C₁ h10 G₁)
    (tailHead_ok C₂ h10₂ G₂) fun w₁ w₂ ⟨T₁, h5₁⟩ ⟨T₂, h5₂⟩ => ?_
  rw [hlen] at h5₂
  exact rel_ite (eval_zero h5₁ (by omega_arith)) (eval_zero h5₂ (by omega_arith)) (fun _ => rel_skip)
    fun _ => hashRest_rel hV C₁.lay C₁.rounds hs3 T₁.env T₂.env (by rw [T₁.s4, T₂.s4, hlen]) (by rw [h5₁, h5₂])

end

end VG.Proof.AesOcb.RISCV64

end

end

/-! ### `AesOcb.RISCV64.BodyCT`, which only this module used -/

section

/-!
# AES-OCB on RISC-V: the data and the tag are constant time

Untrusted: everything here is checked by Lean. Between the calls, the code
runs from the public registers (the data's length among them) and from
registers the correctness proofs pin to the same values in both runs. The
data's address is not in a register but in its slot in `W`, which the taint
analysis takes as secret: each block that loads it (the start of a pass,
the arguments of the call, the start of the rest) is checked on its own,
and the next piece from the address it loads, which is the same in both
runs (`passA_ok`, `callB_ok`, `bodyTail_ok`). The calls have the same
arguments in both runs (`callBlocks_rel`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/FnCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxLstar)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.RISCV64 (frozen Keeps shr4)
open VG.Impl.AesGcm.RISCV64 (dataO)

/-- Then: the next piece, in the environments, after code without calls that
writes only `rs`, none of their registers, which keeps the others. -/
theorem rel_seqKeep {V₁ V₂ : Reg → BitVec 64} {sp : Addr} {c₁ c₂ : Prog isa} {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (rs : List Reg)
    (hc : writesOnly rs c₁ = true) (hn : callFree c₁ = true) (hd : ∀ r ∈ frozen, r ∉ rs)
    (h₂ : ∀ τ₁ τ₂, Env V₁ sp τ₁ ∧ Keep rs σ₁ τ₁ → Env V₂ sp τ₂ ∧ Keep rs σ₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT :=
  rel_seqE h₁ (fun _ _ h => ⟨E₁.exec h rs hc hn hd, (exec_keep rs hc hn h).1⟩)
    (fun _ _ h => ⟨E₂.exec h rs hc hn hd, (exec_keep rs hc hn h).1⟩) h₂

/-- The data of the second run, with the first run's registers. -/
theorem Agree.dbuf {V₁ V₂ : Reg → BitVec 64} (hV : Agree V₁ V₂) {s : State} {D : Addr} {n : Nat}
    (h : DBuf (V₂ .s2) (V₂ .s0) s D n) : DBuf (V₁ .s2) (V₁ .s0) s D n := by
  rw [hV .s2 (by decide), hV .s0 (by decide)]; exact h

/-! ## The whole blocks, run by run -/

/-- A checksum for each block, from `fC`: what a pass computes. -/
def ckRec (fC : Block → Block → Block → Block) (X : Nat → Block) (O0 l c0 : Block) : Nat → Block
  | 0 => c0
  | i + 1 => fC (ckRec fC X O0 l c0 i) (X i) (offAt O0 l (i + 1))

/-- The start of the first pass, then the pass: what each leaves. -/
theorem passA_ok {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {pre : Prog isa}
    {fC : Block → Block → Block → Block} (hB : BodyOk (V .s0) pre (fun b o => b ^^^ o) fC) {s : State}
    (E : Env V sp s) {n : Nat} (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) (hD : DBuf (V .s2) (V .s0) s D n)
    (hm0 : 0 < n / 16) {l : Block} (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt l 0) :
    WP isa (.block passStart) s fun s₁ => Env V sp s₁ ∧ s₁.gpr .s4 = D ∧
      s₁.gpr .s5 = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .s6 = BitVec.ofNat 64 1 ∧
      WP isa (pass pre) s₁ fun t => Env V sp t ∧ Frame (wholeR (V .s0) D (16 * (n / 16))) s.mem t.mem ∧
        t.rd = s.rd ∧ t.wr = s.wr := by
  have hl := hD.lt
  have hDm := hD.take' (Nat.mul_div_le n 16)
  refine WP.mono (passStart_ok E.s0 (L.alW (by decide)) (E.perm.wR (by decide)) hS hl (E.s11.trans h11))
    fun s₁ ⟨s4₁, s5₁, s6₁, g₁, k₁⟩ => ?_
  have E₁ := E.others g₁ k₁.sp k₁.rd k₁.wr
  refine ⟨E₁, by rw [s4₁]; simp, by rw [s5₁, Nat.sub_zero], s6₁, ?_⟩
  rw [Nat.sub_zero] at s5₁
  have P₀ : PassInv V sp D (n / 16) (blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 ofsO)) l
      (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k))) (fun b o => b ^^^ o)
      (ckRec fC (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k)))
        (blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 ofsO)) l (blockAtMem s₁.mem (V .s0 + BitVec.ofNat 64 ckO)))
      s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, s4 := s4₁, s6 := s6₁, s5 := s5₁
      ofs := rfl
      ck := rfl
      blk := fun k _ => by simp
      l0 := by rw [k₁.mem, hl0]
      gpr := fun _ _ => rfl }
  refine WP.mono (pass_ok L hB (fun i _ => rfl) (hDm.of_eq k₁.rd k₁.wr) hm0 P₀) fun t P => ?_
  exact ⟨P.env, by rw [← k₁.mem]; exact P.frame.sub pass_sub, by rw [P.rd, k₁.rd], by rw [P.wr, k₁.wr]⟩

/-- The arguments of the call on the whole blocks, from the slot. -/
theorem dataArgs_at {V : Reg → BitVec 64} {sp : Addr} {K : Addr} (L : Lay K (V .s0)) {t : State}
    (E : Env V sp t) {n : Nat} (hl : n < 2 ^ 64) (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D) (s₃ : State)
    (g₃ : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a4 → s₃.gpr r = t.gpr r) (k₃ : Keeps t s₃) :
    ArgsOk [.load .d .a2 .s0 dataO, .shift .srl .d .a3 .s11 4] s₃ D (n / 16) :=
  dataArgs_ok (t := s₃) (by rw [g₃ _ (by decide) (by decide) (by decide), E.s0]) (L.alW (by decide))
    (by rw [k₃.rd, k₃.wr]; exact E.perm.wR (by decide)) (by rw [k₃.mem, hS]) hl
    (by rw [g₃ _ (by decide) (by decide) (by decide), E.s11, h11])

/-- The call on the whole blocks, then `Offset_0` back and the start of the
second pass: what each leaves. -/
theorem callB_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (nf : c.noFrames = true) {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {s t : State} (E : Env V sp t) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) (F : Frame (wholeR (V .s0) D (16 * (n / 16))) s.mem t.mem)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) :
    WP isa (.seq (.block (callArgs ++ ([.load .d .a2 .s0 dataO, .shift .srl .d .a3 .s11 4] : List Instr)))
      (.call name c)) t fun s₃ => Env V sp s₃ ∧
      WP isa (.block (copy16 o0O ofsO ++ passStart)) s₃ fun s₄ => Env V sp s₄ ∧ s₄.gpr .s4 = D ∧
        s₄.gpr .s5 = BitVec.ofNat 64 (n / 16) ∧ s₄.gpr .s6 = BitVec.ofNat 64 1 := by
  have hl := hD.lt
  have hDm := hD.take' (Nat.mul_div_le n 16)
  have hal := L.alW (d := dataO) (by decide)
  have hDt := hDm.of_eq hrd hwr
  have S₂ : t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm.w F, hS]
  refine WP.mono (callBlocks_ok (f := f) L ok nf hR hs3 E (dataArgs_at L E hl h11 S₂) (dstD hDt))
    fun s₃ P₃ => ?_
  have E₃ := P₃.env E
  refine ⟨E₃, ?_⟩
  have F₃ : Frame (wholeR (V .s0) D (16 * (n / 16))) s.mem s₃.mem :=
    F.trans (P₃.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * (n / 16)⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
  refine WP.block_append (WP.mono (copy16_ok (s := s₃) (a := o0O) (d := ofsO) L.wal (by decide)
    (by decide) E₃.s0 (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide))
    (E₃.perm.wW (by decide))) fun s₄a B₄ => ?_)
  have F₄a : Frame (wholeR (V .s0) D (16 * (n / 16))) s.mem s₄a.mem :=
    F₃.trans (B₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (d := 16) (n := 16) (e := 16) (k := 32) (by decide)
        (by decide)⟩)
  have E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  refine WP.mono (passStart_ok (t := s₄a) (D := D) E₄a.s0 hal (E₄a.perm.wR (by decide))
    (by rw [slot_kept L hDm.w F₄a, hS]) hl (E₄a.s11.trans h11)) fun s₄ ⟨s4₄, s5₄, s6₄, g₄, k₄⟩ => ?_
  exact ⟨E₄a.others g₄ k₄.sp k₄.rd k₄.wr, by rw [s4₄]; simp, by rw [s5₄, Nat.sub_zero], s6₄⟩

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .s2) (V₁ .s0)) (hV : Agree V₁ V₂) {R : Nat}
  (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V₁ .s3 = BitVec.ofNat 64 R)
include L hV hR hs3

/-- The tag at `W + d`, in two runs. -/
theorem tag_rel {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    RelCT isa (Eq2 σ₁ σ₂) (tag d) TT := by
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  unfold tag
  refine rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) [.t1, .t2]
    (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ F₁ F₂ => ?_
  refine rel_seq (encOne_rel L hV hR hs3 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR hs3 F₁ (by decide))
    (encOne_ok (hV.lay L) hR hs3₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  rcases hd with rfl | rfl
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

/-- The rest of the data (at `s4`, `s5` bytes), in two runs. -/
theorem rest_rel (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂)
    (h4 : σ₁.gpr .s4 = σ₂.gpr .s4) (h5 : σ₁.gpr .s5 = σ₂.gpr .s5) :
    RelCT isa (Eq2 σ₁ σ₂) (rest enc) TT := by
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  unfold rest
  refine rel_seqKeep E₁ E₂ (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) [.t1, .t2]
    (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ ⟨F₁, K₁⟩ ⟨F₂, K₂⟩ => ?_
  refine rel_seq (encOne_rel L hV hR hs3 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR hs3 F₁ (by decide))
    (encOne_ok (hV.lay L) hR hs3₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  have a₁ : u₁.gpr .s4 = σ₁.gpr .s4 := (P₁.saved _ (by decide)).trans (K₁.gpr (by decide))
  have a₂ : u₂.gpr .s4 = σ₂.gpr .s4 := (P₂.saved _ (by decide)).trans (K₂.gpr (by decide))
  have b₁ : u₁.gpr .s5 = σ₁.gpr .s5 := (P₁.saved _ (by decide)).trans (K₁.gpr (by decide))
  have b₂ : u₂.gpr .s5 = σ₂.gpr .s5 := (P₂.saved _ (by decide)).trans (K₂.gpr (by decide))
  cases enc <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [.s4, .s5] (by agree_rv64 [a₁, a₂, b₁, b₂, h4, h5])
      ⟨_, by taint_decide⟩
  · exact rel_env (P₁.env F₁) (P₂.env F₂) hV [.s4, .s5] (by agree_rv64 [a₁, a₂, b₁, b₂, h4, h5])
      ⟨_, by taint_decide⟩

/-- The whole blocks (`n / 16 > 0` of them, at the address `D` in the slot
of each run), in two runs. -/
theorem whole_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksRISCV64 f).pre (Proof.Aes.blocksRISCV64 f).pub c)
    (nf : c.noFrames = true) {pre post : Prog isa} {fC : Block → Block → Block → Block}
    (hB : ∀ {W : Addr}, W.toNat % 8 = 0 → BodyOk W pre (fun b o => b ^^^ o) fC)
    (hpre : ∃ h, (VG.Taint.check taint (Taint.ofRegs (([.s4, .s5, .s6] : List Reg) ++ pubR)) (pass pre) h).isSome = true)
    (hpost : ∃ h, (VG.Taint.check taint (Taint.ofRegs (([.s4, .s5, .s6] : List Reg) ++ pubR)) (pass post) h).isSome = true)
    {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {n : Nat} (h11 : V₁ .s11 = BitVec.ofNat 64 n)
    {D : Addr} (hS₁ : σ₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hS₂ : σ₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD₁ : DBuf (V₁ .s2) (V₁ .s0) σ₁ D n) (hD₂ : DBuf (V₂ .s2) (V₂ .s0) σ₂ D n) (hm0 : 0 < n / 16)
    {l₁ l₂ : Block} (hl0₁ : blockAtMem σ₁.mem (V₁ .s0 + BitVec.ofNat 64 l0O) = lAt l₁ 0)
    (hl0₂ : blockAtMem σ₂.mem (V₂ .s0 + BitVec.ofNat 64 l0O) = lAt l₂ 0) :
    RelCT isa (Eq2 σ₁ σ₂) (whole (.call name c) pre post) TT := by
  have hl := hD₁.lt
  have L₂ := hV.lay L
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  have h11₂ : V₂ .s11 = BitVec.ofNat 64 n := (hV .s11 (by decide)).symm.trans h11
  have hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  unfold whole
  -- the first pass
  refine rel_seq (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (passA_ok L (hB L.wal) E₁ h11 hS₁ hD₁ hm0 hl0₁) (passA_ok L₂ (hB L₂.wal) E₂ h11₂ hS₂ hD₂ hm0 hl0₂)
    fun τ₁ τ₂ ⟨G₁, a4₁, a5₁, a6₁, W₁⟩ ⟨G₂, a4₂, a5₂, a6₂, W₂⟩ => ?_
  refine rel_seq (rel_env G₁ G₂ hV [.s4, .s5, .s6] (by agree_rv64 [a4₁, a4₂, a5₁, a5₂, a6₁, a6₂]) hpre) W₁ W₂
    fun u₁ u₂ ⟨U₁, Fu₁, rd₁, wr₁⟩ ⟨U₂, Fu₂, rd₂, wr₂⟩ => ?_
  -- the call
  have hDm₁ := hD₁.take' hmn
  have hDm₂ := hD₂.take' hmn
  have S₁ : u₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L hDm₁.w Fu₁, hS₁]
  have S₂ : u₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [slot_kept L₂ hDm₂.w Fu₂, hS₂]
  refine RelCT.assoc (rel_seq (callBlocks_rel L hV ok ct hR hs3 U₁ U₂ [] (by agree_rv64 []) ⟨_, by taint_decide⟩
      (dataArgs_at L U₁ hl h11 S₁) (dataArgs_at L₂ U₂ hl h11₂ S₂)
      (dstD (hDm₁.of_eq rd₁ wr₁)) (dstD (hV.dbuf (hDm₂.of_eq rd₂ wr₂))))
    (callB_ok ok nf L hR hs3 U₁ h11 hS₁ hD₁ Fu₁ rd₁ wr₁) (callB_ok ok nf L₂ hR hs3₂ U₂ h11₂ hS₂ hD₂ Fu₂ rd₂ wr₂)
    fun v₁ v₂ ⟨X₁, Y₁⟩ ⟨X₂, Y₂⟩ => ?_)
  -- `Offset_0` back and the second pass
  refine rel_seq (rel_env X₁ X₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) Y₁ Y₂
    fun w₁ w₂ ⟨Z₁, b4₁, b5₁, b6₁⟩ ⟨Z₂, b4₂, b5₂, b6₂⟩ => ?_
  exact rel_env Z₁ Z₂ hV [.s4, .s5, .s6] (by agree_rv64 [b4₁, b4₂, b5₁, b5₂, b6₁, b6₂]) hpost

end

/-- `t1 ← n / 16`, the number of whole blocks. -/
theorem bodyHead_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) {n : Nat} (hn : n < 2 ^ 64)
    (h11 : V .s11 = BitVec.ofNat 64 n) :
    WP isa (.block [.shift .srl .d .t1 .s11 4]) s fun s₁ =>
      s₁.gpr .t1 = BitVec.ofNat 64 (n / 16) ∧ Env V sp s₁ ∧ Keeps s s₁ :=
  wp_srl (by decide) fun s₁ u₁ => WP.block_nil ⟨by rw [u₁.gpr, E.s11, h11, shr4 hn],
    E.others (rs := [.t1]) (fun r hr => u₁.other r (by simpa using hr)) u₁.sp u₁.rd u₁.wr,
    ⟨u₁.mem, u₁.rd, u₁.wr, u₁.sp⟩⟩

/-- What the whole blocks leave, for the rest: the environment and the slot. -/
abbrev WholeEnv (V : Reg → BitVec 64) (sp D : Addr) (s t : State) : Prop :=
  Env V sp t ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D

/-- The whole blocks of `seal`, if any: the environment after them. -/
theorem wholeEnv_seal {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (.seq (.block [.shift .srl .d .t1 .s11 4])
      (.ite (.zero .t1) (.block []) (whole encCall (.seq addCk xorOfs) xorOfs))) s (WholeEnv V sp D s) :=
  WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2))
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    Proof.Aes.RISCV64.encryptBlocks_correct encryptBlocks_noFrames hcall_enc (sealPre_ok L.wal) xorOfs_ok L E hR hs3
    h11 hS hD hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun _ P =>
    ⟨P.env, P.rd, P.wr, by rw [slot_kept L (hD.take' (Nat.mul_div_le n 16)).w P.frame, hS]⟩

/-- The whole blocks of `open`, if any: the environment after them. -/
theorem wholeEnv_open {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .s2) (V .s0)) {s : State} (E : Env V sp s)
    {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V .s3 = BitVec.ofNat 64 R) {n : Nat}
    (h11 : V .s11 = BitVec.ofNat 64 n) {D : Addr} (hS : s.mem.readW (V .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD : DBuf (V .s2) (V .s0) s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ofsO) = O0)
    (ho0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (V .s0 + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem (V .s2)) 0) :
    WP isa (.seq (.block [.shift .srl .d .t1 .s11 4])
      (.ite (.zero .t1) (.block []) (whole decCall xorOfs (.seq xorOfs addCk)))) s (WholeEnv V sp D s) :=
  WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem (V .s2)) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem (V .s2) (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem (V .s2)) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem (V .s2)) (i + 1))
    Proof.Aes.RISCV64.decryptBlocks_correct decryptBlocks_noFrames hcall_dec xorOfs_ok (openPost_ok L.wal) L E hR
    hs3 h11 hS hD hofs ho0 hck hl0 (fun _ => rfl) rfl (fun _ => rfl)) fun _ P =>
    ⟨P.env, P.rd, P.wr, by rw [slot_kept L (hD.take' (Nat.mul_div_le n 16)).w P.frame, hS]⟩

section
variable {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .s2) (V₁ .s0)) (hV : Agree V₁ V₂) {R : Nat}
  (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V₁ .s3 = BitVec.ofNat 64 R)
include L hV hR hs3

/-- `body`, in two runs, from what its whole blocks leave in each. -/
theorem body_rel (enc : Bool) {σ₁ σ₂ : State} (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {n : Nat}
    (h11 : V₁ .s11 = BitVec.ofNat 64 n) {D : Addr}
    (hS₁ : σ₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hS₂ : σ₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 dataO) 64 = D)
    (hD₁ : DBuf (V₁ .s2) (V₁ .s0) σ₁ D n) (hD₂ : DBuf (V₂ .s2) (V₂ .s0) σ₂ D n)
    {l₁ l₂ : Block} (hl0₁ : blockAtMem σ₁.mem (V₁ .s0 + BitVec.ofNat 64 l0O) = lAt l₁ 0)
    (hl0₂ : blockAtMem σ₂.mem (V₂ .s0 + BitVec.ofNat 64 l0O) = lAt l₂ 0)
    (W₁ : WP isa (.seq (.block [.shift .srl .d .t1 .s11 4]) (.ite (.zero .t1) (.block [])
      (if enc then whole encCall (.seq addCk xorOfs) xorOfs else whole decCall xorOfs (.seq xorOfs addCk)))) σ₁
      (WholeEnv V₁ sp D σ₁))
    (W₂ : WP isa (.seq (.block [.shift .srl .d .t1 .s11 4]) (.ite (.zero .t1) (.block [])
      (if enc then whole encCall (.seq addCk xorOfs) xorOfs else whole decCall xorOfs (.seq xorOfs addCk)))) σ₂
      (WholeEnv V₂ sp D σ₂)) :
    RelCT isa (Eq2 σ₁ σ₂) (body enc) TT := by
  have hn := hD₁.lt
  have L₂ := hV.lay L
  have h11₂ : V₂ .s11 = BitVec.ofNat 64 n := (hV .s11 (by decide)).symm.trans h11
  unfold body
  refine RelCT.assoc (rel_seq ?_ W₁ W₂ fun τ₁ τ₂ ⟨F₁, _, _, T₁⟩ ⟨F₂, _, _, T₂⟩ => ?_)
  · refine rel_seq (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) (bodyHead_ok E₁ hn h11)
      (bodyHead_ok E₂ hn h11₂) fun u₁ u₂ ⟨t1₁, U₁, k₁⟩ ⟨t1₂, U₂, k₂⟩ => ?_
    refine rel_ite (eval_zero t1₁ (by omega_using [hn])) (eval_zero t1₂ (by omega_using [hn])) (fun _ => rel_skip) fun h0 => ?_
    have hm0 : 0 < n / 16 := Nat.pos_of_ne_zero (of_decide_eq_false h0)
    have hu₁ : u₁.mem.readW (V₁ .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [k₁.mem, hS₁]
    have hu₂ : u₂.mem.readW (V₂ .s0 + BitVec.ofNat 64 dataO) 64 = D := by rw [k₂.mem, hS₂]
    have l₁' : blockAtMem u₁.mem (V₁ .s0 + BitVec.ofNat 64 l0O) = lAt l₁ 0 := by rw [k₁.mem, hl0₁]
    have l₂' : blockAtMem u₂.mem (V₂ .s0 + BitVec.ofNat 64 l0O) = lAt l₂ 0 := by rw [k₂.mem, hl0₂]
    cases enc <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact whole_rel L hV hR hs3 Proof.Aes.RISCV64.decryptBlocks_correct Proof.Aes.RISCV64.decryptBlocks_ct
        decryptBlocks_noFrames (fun _ => xorOfs_ok) ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ U₁ U₂ h11 hu₁ hu₂
        (hD₁.of_eq k₁.rd k₁.wr) (hD₂.of_eq k₂.rd k₂.wr) hm0 l₁' l₂'
    · exact whole_rel L hV hR hs3 Proof.Aes.RISCV64.encryptBlocks_correct Proof.Aes.RISCV64.encryptBlocks_ct
        encryptBlocks_noFrames sealPre_ok ⟨_, by taint_decide⟩ ⟨_, by taint_decide⟩ U₁ U₂ h11 hu₁ hu₂
        (hD₁.of_eq k₁.rd k₁.wr) (hD₂.of_eq k₂.rd k₂.wr) hm0 l₁' l₂'
  refine rel_seq (rel_env F₁ F₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩) (bodyTail_ok L F₁ hn h11 T₁)
    (bodyTail_ok L₂ F₂ hn h11₂ T₂) fun w₁ w₂ ⟨s4₁, s5₁, g₁, k₁⟩ ⟨s4₂, s5₂, g₂, k₂⟩ => ?_
  exact rel_ite (eval_zero s5₁ (by omega_using [])) (eval_zero s5₂ (by omega_using [])) (fun _ => rel_skip) fun _ =>
    rest_rel L hV hR hs3 enc (F₁.others g₁ k₁.sp k₁.rd k₁.wr) (F₂.others g₂ k₂.sp k₂.rd k₂.wr)
      (by rw [s4₁, s4₂]) (by rw [s5₁, s5₂])

end

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISC-V: `seal` and `open` up to the tag are constant time

Untrusted: everything here is checked by Lean. The entry loads `W` from the
stack argument at `sp + 16`, a public address, and then saves our caller's
registers through it: its head is checked on its own, and the rest from the
arguments and `W` (`entry_rel`). After it, the environment of each run is
its own registers (`EntryPost`), which agree on the public ones
(`agree_entry`). Then `nonce_rel`, `hash_rel`, `body_rel` and `tag_rel`,
each from the states the correctness proofs describe (`Seal.lean`), and then
whatever follows the tag, from what they leave (`FrontOut`), the data's
address in its slot among it (`front_rel`). As on PPC64LE
(`Proof/AesOcb/PPC64LE/FnCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Ocb (length_bytesAt)

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

/-- The entry of `seal` and `open`, in two runs with the same arguments. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} (hW₁ : stackArg σ₁ 2 = W) (hW₂ : stackArg σ₂ 2 = W)
    (hA₁ : Covers [⟨stackArgAddr σ₁ 0, 24⟩] (σ₁.rd ++ σ₁.wr))
    (hA₂ : Covers [⟨stackArgAddr σ₂ 0, 24⟩] (σ₂.rd ++ σ₂.wr)) (hsa₁ : σ₁.sp.toNat % 16 = 0)
    (hsa₂ : σ₂.sp.toNat % 16 = 0) (qsp : σ₁.sp = σ₂.sp)
    (hq : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  simp only [entry, Impl.AesGcm.RISCV64.openEntry, Proof.AesGcm.RISCV64.oneEntry_eq, List.append_assoc]
  refine RelCT.block_append (rel_seq (rel_taint [] qsp (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (Proof.AesGcm.RISCV64.oneA_ok (off := 16) (W := W) (.inr rfl) hsa₁ (stk_in hA₁ (i := 2) (by decide))
      (by rw [← hW₁]; rfl))
    (Proof.AesGcm.RISCV64.oneA_ok (off := 16) (W := W) (.inr rfl) hsa₂ (stk_in hA₂ (i := 2) (by decide))
      (by rw [← hW₂]; rfl))
    fun τ₁ τ₂ ⟨a₁, g₁, k₁⟩ ⟨a₂, g₂, k₂⟩ => ?_)
  refine rel_taint [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t1] (by rw [k₁.sp, k₂.sp, qsp]) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases ht : r = .t1
  · subst ht; rw [a₁, a₂]
  · rw [g₁ r ht, g₂ r ht]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, ht] at hr ⊢; exact hr)

/-- `nonce`, in two runs with the same nonce's address and length. -/
theorem nonce_rel {V₁ V₂ : Reg → BitVec 64} {sp : Addr} (L : Lay (V₁ .s2) (V₁ .s0)) (hV : Agree V₁ V₂) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hs3 : V₁ .s3 = BitVec.ofNat 64 R) {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) (h4 : σ₁.gpr .s4 = σ₂.gpr .s4) (h5 : σ₁.gpr .s5 = σ₂.gpr .s5) :
    RelCT isa (Eq2 σ₁ σ₂) nonce TT := by
  have hs3₂ : V₂ .s3 = BitVec.ofNat 64 R := (hV .s3 (by decide)).symm.trans hs3
  unfold nonce
  refine rel_seqEnv E₁ E₂ (rel_env E₁ E₂ hV [.s4, .s5] (by agree_rv64 [h4, h5]) ⟨_, by taint_decide⟩)
    [.t0, .t1, .t2, .a0, .a1, .a2, .a3] (by decide +kernel) (by decide +kernel) (by decide) fun τ₁ τ₂ F₁ F₂ => ?_
  refine rel_seq (encOne_rel L hV hR hs3 F₁ F₂ (by decide) ⟨_, by taint_decide⟩) (encOne_ok L hR hs3 F₁ (by decide))
    (encOne_ok (hV.lay L) hR hs3₂ F₂ (by decide)) fun u₁ u₂ P₁ P₂ => ?_
  exact rel_env (P₁.env F₁) (P₂.env F₂) hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

/-- The registers after the entry agree on the public ones in two runs with
the same arguments. -/
theorem agree_entry {σ₁ σ₂ τ₁ τ₂ : State} {W T : Addr} (P₁ : EntryPost W T σ₁ τ₁) (P₂ : EntryPost W T σ₂ τ₂)
    (hq : ∀ r ∈ [Reg.a0, .a1, .a3, .a5, .a7], σ₁.gpr r = σ₂.gpr r) (ht : stackArg σ₁ 1 = stackArg σ₂ 1) :
    Agree τ₁.gpr τ₂.gpr := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true] at hq
  obtain ⟨q0, q1, q3, q5, q7⟩ := hq
  simp only [Agree, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true]
  exact ⟨by rw [P₁.s0, P₂.s0], by rw [P₁.s2, P₂.s2, q0], by rw [P₁.s3, P₂.s3, q1], by rw [P₁.s7, P₂.s7, q3],
    by rw [P₁.s8, P₂.s8, ht], by rw [P₁.s9, P₂.s9], by rw [P₁.s10, P₂.s10, q5], by rw [P₁.s11, P₂.s11, q7]⟩

/-- What `HASH` needs after the entry and `nonce`. -/
theorem hctx_of {s₀ s₁ s₂ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (Ar : FnArgs s₀ K W N A D R nl al n tl T) (P₁ : EntryPost W T s₀ s₁) (ha0 : s₀.gpr .a0 = K)
    (ha4 : s₀.gpr .a4 = A) (ha6 : s₀.gpr .a6 = D) {o : Block} (P₂ : NonceOk s₁.gpr s₀.sp o s₁ s₂) :
    HCtx (s₁.gpr .s2) (s₁.gpr .s0) D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al) s₂ ∧
      s₂.mem.readW (s₁.gpr .s0 + BitVec.ofNat 64 Impl.AesGcm.RISCV64.aadO) 64 = A ∧
      blockAtMem s₂.mem (s₁.gpr .s0 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar s₀.mem K) 0 := by
  have hW₁ : s₁.gpr .s0 = W := P₁.s0
  have hK₁ : s₁.gpr .s2 = K := P₁.s2.trans ha0
  have F₁ : Frame [⟨W, 2560⟩] s₀.mem s₁.mem := frameW P₁.frame (entryR_W W)
  have pf₂ : Frame (nonceR W) s₁.mem s₂.mem := by have := P₂.frame; rwa [hW₁] at this
  have F₁₂ := F₁.trans (frameW pf₂ (nonceR_W W))
  have S₁ : Slots W A D s₁.mem := by have := P₁.slots; rwa [ha4, ha6] at this
  have S₂ : Slots W A D s₂.mem := Slots.mut Ar.lay Ar.data.w (nonceR_mut (D := D) (n := n) pf₂) S₁
  refine ⟨{
      lay := by rw [hK₁, hW₁]; exact Ar.lay
      rounds := Ar.rounds
      ciph := by rw [hK₁, ctxCiph_W Ar.lay F₁₂ Ar.rounds]
      lstar := by rw [hK₁, ctxLstar_W Ar.lay F₁₂]
      buf := by rw [length_bytesAt, hW₁]; exact Ar.aad.of_eq (P₂.rd.trans P₁.keeps.rd) (P₂.wr.trans P₁.keeps.wr)
      aad := by rw [length_bytesAt, bytesAt_W Ar.aad.w Ar.aad.lt F₁₂]
      ad := by rw [length_bytesAt]; exact Ar.ad
      kd := by rw [hK₁]; exact Ar.data.k
      dw := by rw [hW₁]; exact Ar.data.w }, by rw [hW₁]; exact S₂.aad, ?_⟩
  rw [P₂.keep (by decide) (by decide), hW₁, P₁.l0, ha0]

/-- What `front` leaves, in the environment `V`: the tag's address and
length, the data's length, and the slots. -/
structure FrontOut (V : Reg → BitVec 64) (sp W A D T : Addr) (n tl : Nat) (σ τ : State) : Prop where
  env : Env V sp τ
  rd : τ.rd = σ.rd
  wr : τ.wr = σ.wr
  s0 : V .s0 = W
  s8 : V .s8 = BitVec.ofNat 64 tl
  s9 : V .s9 = T
  s11 : V .s11 = BitVec.ofNat 64 n
  slots : Slots W A D τ.mem

/-- The data and the tag of one run: what they leave. -/
theorem bodyTag_ok (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) {σ τ w : State} {K W N A D T : Addr}
    {R nl al n tl : Nat} (Ar : FnArgs σ K W N A D R nl al n tl T) (P : EntryPost W T σ τ)
    (htl : stackArg σ 1 = BitVec.ofNat 64 tl) (ha0 : σ.gpr .a0 = K) (ha1 : σ.gpr .a1 = BitVec.ofNat 64 R)
    (ha7 : σ.gpr .a7 = BitVec.ofNat 64 n) (Q : Pre τ.gpr K W N A D R nl al tl σ w) :
    WP isa (body enc) w fun y => Env τ.gpr σ.sp y ∧
      WP isa (tag d) y fun x => FrontOut τ.gpr σ.sp W A D T n tl σ x := by
  have hW : τ.gpr .s0 = W := P.s0
  have hK : τ.gpr .s2 = K := P.s2.trans ha0
  have hs3 : τ.gpr .s3 = BitVec.ofNat 64 R := P.s3.trans ha1
  have h11 : τ.gpr .s11 = BitVec.ofNat 64 n := P.s11.trans ha7
  have L : Lay (τ.gpr .s2) (τ.gpr .s0) := by rw [hK, hW]; exact Ar.lay
  have hD : DBuf (τ.gpr .s2) (τ.gpr .s0) w D n := by rw [hK, hW]; exact Ar.data.of_eq Q.rd Q.wr
  have l₃ : ctxLstar w.mem K = ctxLstar σ.mem K := ctxLstar_W Ar.lay Q.frame
  have hS : w.mem.readW (τ.gpr .s0 + BitVec.ofNat 64 Impl.AesGcm.RISCV64.dataO) 64 = D := by
    rw [hW]; exact Q.slots.data
  have hofs : blockAtMem w.mem (τ.gpr .s0 + BitVec.ofNat 64 ofsO) =
      Spec.Ocb.offset0 (ctxCiph σ.mem K R) tl (bytesAt σ.mem N nl) := by rw [hW]; exact Q.ofs
  have ho0 : blockAtMem w.mem (τ.gpr .s0 + BitVec.ofNat 64 o0O) =
      Spec.Ocb.offset0 (ctxCiph σ.mem K R) tl (bytesAt σ.mem N nl) := by rw [hW]; exact Q.o0
  have hck : blockAtMem w.mem (τ.gpr .s0 + BitVec.ofNat 64 ckO) = 0 := by rw [hW]; exact Q.ck
  have hl0 : blockAtMem w.mem (τ.gpr .s0 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar w.mem (τ.gpr .s2)) 0 := by
    rw [hW, hK, Q.l0, l₃]
  have post : ∀ y, BodyOut τ.gpr σ.sp D n (bytesAt y.mem D n) (blockAtMem y.mem (τ.gpr .s0 + BitVec.ofNat 64 ofsO))
      (blockAtMem y.mem (τ.gpr .s0 + BitVec.ofNat 64 ckO)) w y → Env τ.gpr σ.sp y ∧
      WP isa (tag d) y fun x => FrontOut τ.gpr σ.sp W A D T n tl σ x := fun y B => by
    have Bf : Frame (bodyR W D n) w.mem y.mem := by have := B.frame; rwa [hW] at this
    have S₄ : Slots W A D y.mem := Slots.mut Ar.lay Ar.data.w (bodyR_mut Bf) Q.slots
    refine ⟨B.env, WP.mono (tag_ok L B.env Ar.rounds hs3 hd) fun x T₅ => ?_⟩
    have Tf : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 d, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩]
        y.mem x.mem := by have := T₅.frame; rwa [hW] at this
    have hd' : d + 16 ≤ 128 ∨ (256 ≤ d ∧ d + 16 ≤ 2560) := by
      rcases hd with rfl | rfl
      · exact .inl (by decide)
      · exact .inr ⟨by decide, by decide⟩
    exact ⟨T₅.env, by rw [T₅.rd, B.rd, Q.rd], by rw [T₅.wr, B.wr, Q.wr], hW, P.s8.trans htl, P.s9, h11,
      Slots.mut Ar.lay Ar.data.w (tagR_mut hd' Tf) S₄⟩
  cases enc
  · exact WP.mono (bodyOpen_ok L Q.env Ar.rounds hs3 h11 hS hD hofs ho0 hck hl0) fun y B =>
      post y { B with out := rfl, ofs := rfl, ck := rfl }
  · exact WP.mono (bodySeal_ok L Q.env Ar.rounds hs3 h11 hS hD hofs ho0 hck hl0) fun y B =>
      post y { B with out := rfl, ofs := rfl, ck := rfl }

/-- `front enc d` and then `k`, in two runs with the same arguments, `k`
from what `front` leaves in each. -/
theorem front_rel (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) {k : Prog isa}
    {σ₁ σ₂ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (hk : ∀ (V₁ V₂ : Reg → BitVec 64) (τ₁ τ₂ : State), Agree V₁ V₂ →
      FrontOut V₁ σ₁.sp W A D T n tl σ₁ τ₁ → FrontOut V₂ σ₁.sp W A D T n tl σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) k TT)
    (A₁ : FnArgs σ₁ K W N A D R nl al n tl T) (A₂ : FnArgs σ₂ K W N A D R nl al n tl T)
    (hW₁ : stackArg σ₁ 2 = W) (hT₁ : stackArg σ₁ 0 = T) (htl₁ : stackArg σ₁ 1 = BitVec.ofNat 64 tl)
    (h0₁ : σ₁.gpr .a0 = K) (h1₁ : σ₁.gpr .a1 = BitVec.ofNat 64 R) (h2₁ : σ₁.gpr .a2 = N)
    (h3₁ : σ₁.gpr .a3 = BitVec.ofNat 64 nl) (h4₁ : σ₁.gpr .a4 = A) (h5₁ : σ₁.gpr .a5 = BitVec.ofNat 64 al)
    (h6₁ : σ₁.gpr .a6 = D) (h7₁ : σ₁.gpr .a7 = BitVec.ofNat 64 n)
    (hW₂ : stackArg σ₂ 2 = W) (hT₂ : stackArg σ₂ 0 = T) (htl₂ : stackArg σ₂ 1 = BitVec.ofNat 64 tl)
    (h0₂ : σ₂.gpr .a0 = K) (h1₂ : σ₂.gpr .a1 = BitVec.ofNat 64 R) (h2₂ : σ₂.gpr .a2 = N)
    (h3₂ : σ₂.gpr .a3 = BitVec.ofNat 64 nl) (h4₂ : σ₂.gpr .a4 = A) (h5₂ : σ₂.gpr .a5 = BitVec.ofNat 64 al)
    (h6₂ : σ₂.gpr .a6 = D) (h7₂ : σ₂.gpr .a7 = BitVec.ofNat 64 n) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (front enc d) k) TT := by
  have L₁ : Lay (σ₁.gpr .a0) W := by rw [h0₁]; exact A₁.lay
  have L₂ : Lay (σ₂.gpr .a0) W := by rw [h0₂]; exact A₂.lay
  have hC₁ : Covers [⟨σ₁.gpr .a0, 256⟩] (σ₁.rd ++ σ₁.wr) := by rw [h0₁]; exact A₁.perm.k
  have hC₂ : Covers [⟨σ₂.gpr .a0, 256⟩] (σ₂.rd ++ σ₂.wr) := by rw [h0₂]; exact A₂.perm.k
  unfold front
  refine rel_front (rel_seq (entry_rel hW₁ hW₂ A₁.args A₂.args A₁.sa A₂.sa qsp
      (by agree_rv64 [h0₁, h0₂, h1₁, h1₂, h2₁, h2₂, h3₁, h3₂, h4₁, h4₂, h5₁, h5₂, h6₁, h6₂, h7₁, h7₂]))
    (entry_ok L₁ A₁.perm.w hC₁ A₁.sa hW₁ hT₁ A₁.args A₁.argsW)
    (entry_ok L₂ A₂.perm.w hC₂ A₂.sa hW₂ hT₂ A₂.args A₂.argsW) fun τ₁ τ₂ P₁ P₂ => ?_)
  have hV : Agree τ₁.gpr τ₂.gpr := agree_entry P₁ P₂
    (by agree_rv64 [h0₁, h0₂, h1₁, h1₂, h3₁, h3₂, h5₁, h5₂, h7₁, h7₂]) (by rw [htl₁, htl₂])
  have E₁ := P₁.env
  have E₂ := P₂.env
  rw [← qsp] at E₂
  have L : Lay (τ₁.gpr .s2) (τ₁.gpr .s0) := by rw [P₁.s2, P₁.s0, h0₁]; exact A₁.lay
  have hs3 : τ₁.gpr .s3 = BitVec.ofNat 64 R := P₁.s3.trans h1₁
  have hs3₂ : τ₂.gpr .s3 = BitVec.ofNat 64 R := P₂.s3.trans h1₂
  have L₂' : Lay (τ₂.gpr .s2) (τ₂.gpr .s0) := hV.lay L
  have hn1 := A₁.n1
  have hn15 := A₁.n15
  have ht : tl < 2 ^ 64 := by have := A₁.t16; omega_using [this]
  -- `nonce` and `HASH`
  refine RelCT.assoc (rel_seq (rel_seq (nonce_rel L hV A₁.rounds hs3 E₁ E₂ (by rw [P₁.s4, P₂.s4, h2₁, h2₂])
      (by rw [P₁.s5, P₂.s5, h3₁, h3₂]))
    (nonce_ok L A₁.rounds hs3 E₁ (P₁.s4.trans h2₁) (P₁.s5.trans h3₁) (P₁.s8.trans htl₁) hn1 hn15 ht
      (by rw [P₁.s0]; exact A₁.nonce.of_eq P₁.keeps.rd P₁.keeps.wr) (by rw [P₁.s2, h0₁]; exact A₁.data.k))
    (nonce_ok L₂' A₁.rounds hs3₂ E₂ (P₂.s4.trans h2₂) (P₂.s5.trans h3₂) (P₂.s8.trans htl₂) hn1 hn15 ht
      (by rw [P₂.s0]; exact A₂.nonce.of_eq P₂.keeps.rd P₂.keeps.wr) (by rw [P₂.s2, h0₂]; exact A₂.data.k))
    fun u₁ u₂ Q₁ Q₂ => ?_) (preRest_wp A₁ P₁ htl₁ h0₁ h1₁ h2₁ h3₁ h4₁ h5₁ h6₁)
    (preRest_wp A₂ P₂ htl₂ h0₂ h1₂ h2₂ h3₂ h4₂ h5₂ h6₂) fun w₁ w₂ R₁ R₂ => ?_)
  · have E₂' := Q₂.env
    rw [qsp] at Q₂
    obtain ⟨C₁, a₁, l0₁⟩ := hctx_of A₁ P₁ h0₁ h4₁ h6₁ Q₁
    obtain ⟨C₂, a₂, l0₂⟩ := hctx_of A₂ P₂ h0₂ h4₂ h6₂ Q₂
    exact hash_rel hV C₁ C₂ hs3 (by rw [length_bytesAt, length_bytesAt]) Q₁.env E₂' a₁ a₂
      (by rw [P₁.s10, h5₁, length_bytesAt]) l0₁ l0₂
  -- the data and the tag
  have F₁ := R₁.env
  have F₂ := R₂.env
  rw [← qsp] at F₂
  have h11 : τ₁.gpr .s11 = BitVec.ofNat 64 n := P₁.s11.trans h7₁
  have h11₂ : τ₂.gpr .s11 = BitVec.ofNat 64 n := P₂.s11.trans h7₂
  have hD₁ : DBuf (τ₁.gpr .s2) (τ₁.gpr .s0) w₁ D n := by
    rw [P₁.s2, P₁.s0, h0₁]; exact A₁.data.of_eq R₁.rd R₁.wr
  have hD₂ : DBuf (τ₂.gpr .s2) (τ₂.gpr .s0) w₂ D n := by
    rw [P₂.s2, P₂.s0, h0₂]; exact A₂.data.of_eq R₂.rd R₂.wr
  have hS₁ : w₁.mem.readW (τ₁.gpr .s0 + BitVec.ofNat 64 Impl.AesGcm.RISCV64.dataO) 64 = D := by
    rw [P₁.s0]; exact R₁.slots.data
  have hS₂ : w₂.mem.readW (τ₂.gpr .s0 + BitVec.ofNat 64 Impl.AesGcm.RISCV64.dataO) 64 = D := by
    rw [P₂.s0]; exact R₂.slots.data
  have l0₁ : blockAtMem w₁.mem (τ₁.gpr .s0 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar w₁.mem (τ₁.gpr .s2)) 0 := by
    rw [P₁.s0, P₁.s2, R₁.l0, h0₁, ctxLstar_W A₁.lay R₁.frame]
  have l0₂ : blockAtMem w₂.mem (τ₂.gpr .s0 + BitVec.ofNat 64 l0O) = Spec.Ocb.lAt (ctxLstar w₂.mem (τ₂.gpr .s2)) 0 := by
    rw [P₂.s0, P₂.s2, R₂.l0, h0₂, ctxLstar_W A₂.lay R₂.frame]
  have o₁ := R₁.ofs
  have o₂ := R₂.ofs
  have z₁ := R₁.o0
  have z₂ := R₂.o0
  have c₁ := R₁.ck
  have c₂ := R₂.ck
  rw [← P₁.s0] at o₁ z₁ c₁
  rw [← P₂.s0] at o₂ z₂ c₂
  have B₁ := bodyTag_ok enc hd A₁ P₁ htl₁ h0₁ h1₁ h7₁ R₁
  have B₂ := bodyTag_ok enc hd A₂ P₂ htl₂ h0₂ h1₂ h7₂ R₂
  rw [← qsp] at B₂
  refine rel_seq (body_rel L hV A₁.rounds hs3 enc F₁ F₂ h11 hS₁ hS₂ hD₁ hD₂ l0₁ l0₂ ?_ ?_) B₁ B₂
    fun y₁ y₂ ⟨G₁, X₁⟩ ⟨G₂, X₂⟩ => ?_
  · cases enc
    · exact wholeEnv_open L F₁ A₁.rounds hs3 h11 hS₁ hD₁ o₁ z₁ c₁ l0₁
    · exact wholeEnv_seal L F₁ A₁.rounds hs3 h11 hS₁ hD₁ o₁ z₁ c₁ l0₁
  · cases enc
    · exact wholeEnv_open L₂' F₂ A₁.rounds hs3₂ h11₂ hS₂ hD₂ o₂ z₂ c₂ l0₂
    · exact wholeEnv_seal L₂' F₂ A₁.rounds hs3₂ h11₂ hS₂ hD₂ o₂ z₂ c₂ l0₂
  refine rel_seq (tag_rel L hV A₁.rounds hs3 G₁ G₂ hd) X₁ X₂ fun x₁ x₂ T₁ T₂ => ?_
  exact hk _ _ _ _ hV T₁ T₂

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISC-V: `vg_aes_ocb_seal` and `vg_aes_ocb_open` are constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments (`onePub`) have the same arguments of `front_rel` (`FnArgs`, with
the values of the first run). After `front`, `seal` copies the tag out and
restores our caller's registers: code without calls, which the taint
analysis checks from the public registers. `open` copies the received tag
and compares it with the one it computed, by code the taint analysis checks,
then masks the data without a branch: the mask loads the data's address
from its slot, the same in both runs by the correctness proofs, so its head
is checked on its own (`maskHead_ok`), and the rest, and `restore`, from
that address and the public registers (`openTail_rel`). `open` leaks nothing
more than `seal`, in particular not whether the tag is right. As on PPC64LE
(`Proof/AesOcb/PPC64LE/FnCT.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesOcb.RISCV64
open VG.Proof.AesGcm.RISCV64 (Keeps)
open VG.Impl.AesGcm.RISCV64 (restore)

/-- A relation of two runs of `(a; b); c`, from one of `a; (b; c)`. -/
theorem RelCT.assoc' {P Q : State → State → Prop} {a b c : Prog isa}
    (h : RelCT isa P (.seq a (.seq b c)) Q) : RelCT isa P (.seq (.seq a b) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq e₁ c₁ => cases e₁ with | seq a₁ b₁ =>
  cases e₂ with | seq e₂ c₂ => cases e₂ with | seq a₂ b₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `FnArgs` in two runs with the same public arguments, with the values of
the first. -/
theorem args₂_of {σ₁ σ₂ : State} (hq : onePub σ₁ σ₂)
    (A₂ : FnArgs σ₂ (σ₂.gpr .a0) (stackArg σ₂ 2) (σ₂.gpr .a2) (σ₂.gpr .a4) (σ₂.gpr .a6) (σ₂.gpr .a1).toNat
      (σ₂.gpr .a3).toNat (σ₂.gpr .a5).toNat (σ₂.gpr .a7).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0)) :
    FnArgs σ₂ (σ₁.gpr .a0) (stackArg σ₁ 2) (σ₁.gpr .a2) (σ₁.gpr .a4) (σ₁.gpr .a6) (σ₁.gpr .a1).toNat
      (σ₁.gpr .a3).toNat (σ₁.gpr .a5).toNat (σ₁.gpr .a7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0) := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, qa⟩ := hq
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qa 0 (by decide), ← qa 1 (by decide),
    ← qa 2 (by decide)] at A₂
  exact A₂

/-- `front enc d; k` in two runs with the same public arguments. -/
theorem front_relq (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) {k : Prog isa} {σ₁ σ₂ : State}
    (hk : ∀ (V₁ V₂ : Reg → BitVec 64) (τ₁ τ₂ : State), Agree V₁ V₂ →
      FrontOut V₁ σ₁.sp (stackArg σ₁ 2) (σ₁.gpr .a4) (σ₁.gpr .a6) (stackArg σ₁ 0) (σ₁.gpr .a7).toNat
        (stackArg σ₁ 1).toNat σ₁ τ₁ →
      FrontOut V₂ σ₁.sp (stackArg σ₁ 2) (σ₁.gpr .a4) (σ₁.gpr .a6) (stackArg σ₁ 0) (σ₁.gpr .a7).toNat
        (stackArg σ₁ 1).toNat σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) k TT)
    (A₁ : FnArgs σ₁ (σ₁.gpr .a0) (stackArg σ₁ 2) (σ₁.gpr .a2) (σ₁.gpr .a4) (σ₁.gpr .a6) (σ₁.gpr .a1).toNat
      (σ₁.gpr .a3).toNat (σ₁.gpr .a5).toNat (σ₁.gpr .a7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (A₂ : FnArgs σ₂ (σ₂.gpr .a0) (stackArg σ₂ 2) (σ₂.gpr .a2) (σ₂.gpr .a4) (σ₂.gpr .a6) (σ₂.gpr .a1).toNat
      (σ₂.gpr .a3).toNat (σ₂.gpr .a5).toNat (σ₂.gpr .a7).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0))
    (hq : onePub σ₁ σ₂) : RelCT isa (Eq2 σ₁ σ₂) (.seq (front enc d) k) TT := by
  have A₂' := args₂_of hq A₂
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have o' : ∀ {x y : BitVec 64}, x = y → y = BitVec.ofNat 64 x.toNat := fun h => by rw [h]; exact o _
  exact front_rel enc hd hk A₁ A₂' rfl rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _)
    (qa 2 (by decide)).symm (qa 0 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3)
    q4.symm (o' q5) q6.symm (o' q7) qsp

theorem seal_ct : ConstantTime isa sealRISCV64.pre sealRISCV64.pub «seal» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  unfold «seal»
  refine front_relq true (.inl rfl) (fun _ _ _ _ hV O₁ O₂ => ?_) (sealArgs_of h₁) (sealArgs_of h₂) hq
  exact rel_env O₁.env O₂.env hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩

/-- The head of `mask`: the data's address, from its slot, and its length. -/
theorem maskHead_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (E : Env V sp s) (hal : (V .s0).toNat % 8 = 0)
    {A D : Addr} (hS : Slots (V .s0) A D s.mem) :
    WP isa (.block [.load .d .s4 .s0 Impl.AesGcm.RISCV64.dataO, Impl.AesGcm.RISCV64.mov .s5 .s11,
      .li .t2 0, .sub .t5 .t2 .a0]) s fun s₁ =>
      s₁.gpr .s4 = D ∧ s₁.gpr .s5 = V .s11 ∧ (∀ r, r ∉ maskRegs → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ :=
  wp_ld (off := 240) (a := V .s0 + BitVec.ofNat 64 240) (by decide) (by rw [E.s0]) (Spill.al8 hal (by decide))
    (E.perm.wR (by decide)) fun t₁ u₁ => wp_mv fun t₂ u₂ => wp_li (imm := 0) (by decide) fun t₃ u₃ =>
    wp_sub fun t₄ u₄ => WP.block_nil
    ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hS.data],
      by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), E.s11],
      fun r hr => by
        rw [u₄.other _ (ne_of_not_mem hr), u₃.other _ (ne_of_not_mem hr), u₂.other _ (ne_of_not_mem hr),
          u₁.other _ (ne_of_not_mem hr)],
      ⟨by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr], by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩⟩

/-- What `open` runs after `front`, in two runs, from what `front` leaves. -/
theorem openTail_rel {σ₁ σ₂ : State} {K W N A D T : Addr} {R nl al n tl : Nat}
    (A₁ : FnArgs σ₁ K W N A D R nl al n tl T) (A₂ : FnArgs σ₂ K W N A D R nl al n tl T) {sp : Addr}
    {V₁ V₂ : Reg → BitVec 64} {τ₁ τ₂ : State} (hV : Agree V₁ V₂) (O₁ : FrontOut V₁ sp W A D T n tl σ₁ τ₁)
    (O₂ : FrontOut V₂ sp W A D T n tl σ₂ τ₂) :
    RelCT isa (Eq2 τ₁ τ₂) (.seq recv (.seq cmp (.seq mask (.block restore)))) TT := by
  have hal₁ : (V₁ .s0).toNat % 8 = 0 := by rw [O₁.s0]; exact A₁.lay.wal
  have hal₂ : (V₂ .s0).toNat % 8 = 0 := by rw [O₂.s0]; exact A₂.lay.wal
  have E₁ := O₁.env
  have E₂ := O₂.env
  -- the received tag
  refine rel_seq (rel_env E₁ E₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (recv_ok E₁ hal₁ O₁.s8 A₁.t1 A₁.t16 (by rw [O₁.s9, O₁.rd, O₁.wr]; exact A₁.tag.rd)
      (by rw [O₁.s9, O₁.s0]; exact A₁.tag.w))
    (recv_ok E₂ hal₂ O₂.s8 A₂.t1 A₂.t16 (by rw [O₂.s9, O₂.rd, O₂.wr]; exact A₂.tag.rd)
      (by rw [O₂.s9, O₂.s0]; exact A₂.tag.w))
    fun u₁ u₂ ⟨_, f₁, g₁, sp₁, rd₁, wr₁⟩ ⟨_, f₂, g₂, sp₂, rd₂, wr₂⟩ => ?_
  have U₁ := E₁.others g₁ sp₁ rd₁ wr₁
  have U₂ := E₂.others g₂ sp₂ rd₂ wr₂
  rw [O₁.s0] at f₁
  rw [O₂.s0] at f₂
  have S₁ : Slots W A D u₁.mem := Slots.mut A₁.lay A₁.data.w (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide)) O₁.slots
  have S₂ : Slots W A D u₂.mem := Slots.mut A₂.lay A₂.data.w (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact in_mutA (by decide)) O₂.slots
  -- the comparison
  refine rel_seq (rel_env U₁ U₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (cmp_ok U₁ hal₁ O₁.s8 A₁.t1 A₁.t16) (cmp_ok U₂ hal₂ O₂.s8 A₂.t1 A₂.t16)
    fun v₁ v₂ ⟨_, f₁', g₁', sp₁', rd₁', wr₁'⟩ ⟨_, f₂', g₂', sp₂', rd₂', wr₂'⟩ => ?_
  have Y₁ := U₁.others g₁' sp₁' rd₁' wr₁'
  have Y₂ := U₂.others g₂' sp₂' rd₂' wr₂'
  rw [O₁.s0] at f₁'
  rw [O₂.s0] at f₂'
  have S₁' : Slots (V₁ .s0) A D v₁.mem := by
    rw [O₁.s0]; exact Slots.mut A₁.lay A₁.data.w (f₁'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact in_mutB (by decide) (by decide)) S₁
  have S₂' : Slots (V₂ .s0) A D v₂.mem := by
    rw [O₂.s0]; exact Slots.mut A₂.lay A₂.data.w (f₂'.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact in_mutB (by decide) (by decide)) S₂
  -- the mask, then `restore`
  unfold mask
  refine RelCT.assoc' (rel_seq (rel_env Y₁ Y₂ hV [] (by agree_rv64 []) ⟨_, by taint_decide⟩)
    (maskHead_ok Y₁ hal₁ S₁') (maskHead_ok Y₂ hal₂ S₂') fun w₁ w₂ ⟨a4₁, a5₁, g₁'', k₁⟩ ⟨a4₂, a5₂, g₂'', k₂⟩ => ?_)
  exact rel_env (Y₁.others g₁'' k₁.sp k₁.rd k₁.wr) (Y₂.others g₂'' k₂.sp k₂.rd k₂.wr) hV [.s4, .s5]
    (by agree_rv64 [a4₁, a4₂, a5₁, a5₂, hV .s11 (by decide)]) ⟨_, by taint_decide⟩

theorem open_ct : ConstantTime isa openRISCV64.pre openRISCV64.pub «open» := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  unfold «open»
  exact front_relq false (.inr rfl) (fun _ _ _ _ hV O₁ O₂ =>
    openTail_rel (openArgs_of h₁) (args₂_of hq.1 (openArgs_of h₂)) hV O₁ O₂) (openArgs_of h₁) (openArgs_of h₂) hq.1

end VG.Proof.AesOcb.RISCV64

end

end

/-!
# AES-OCB on RISC-V: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant time,
a state satisfying each precondition, and the shared contracts of
`Spec/Ocb/Contract.lean` with the working space as a last argument
(`Proof/AesOcb/Scratch.lean`; with no stack: a call keeps the return address
in `ra`, which each function saves in the working space).
The working space is then allocated on the stack (`seal_framed`,
`open_framed`); `init` is AES-GCM's (`Init.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.RISCV64

open VG VG.RISCV64 VG.Impl.AesOcb.RISCV64

theorem seal_correct (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa «seal» s t s' ∧ abiPreserved s s' ∧ sealRISCV64.post s s' :=
  seal_wp hs

theorem open_correct (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa «open» s t s' ∧ abiPreserved s s' ∧ openRISCV64.post s s' :=
  open_wp hs

/-! ## States satisfying the preconditions -/

/-- A state satisfying the precondition of `vg_aes_ocb_seal`: a 1-byte nonce,
no associated data, no data, a 4-byte tag at `0x5000` and `work` at
`0x6000`, with the stack arguments at `0x9000`. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 10 | .a2 => 0x2000 | .a3 => 1 | .a4 => 0x3000 | .a6 => 0x4000 | _ => 0
  sp := 0x9000
  mem a := bif Nat.beq a.toNat 0x9001 then 0x50 else bif Nat.beq a.toNat 0x9008 then 4 else
    bif Nat.beq a.toNat 0x9011 then 0x60 else 0
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩, ⟨0x6000, 2560⟩]

/-- A state satisfying the precondition of `vg_aes_ocb_open`: as `sealSat`,
with the tag read only. -/
def openSat : State := { sealSat with
  rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x9000, 24⟩]
  wr := [⟨0x4000, 0⟩, ⟨0x6000, 2560⟩] }

/-! ## The shared contracts -/

theorem seal_verified :
    Verified RISCV64.target «seal» (Proof.AesOcb.sealScratchContract RISCV64.abi) :=
  Verified.of_correct seal_correct seal_ct
    { pre := by sig_implies_pre [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop, BitVec.add_zero]
      post := by sig_implies_post [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop]
      pub := by sig_implies_pub [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop]
      sat := by sig_implies_sat [Proof.AesOcb.sealScratchContract, Proof.AesOcb.sealScratchSig, Spec.Ocb.sealPre,
      Proof.AesOcb.sealRoundsPost, sealRISCV64, sealPreA, oneFacts, aCtx, aNonce, aAad, aData, aTag, aWork, onePub, args,
      rounds, RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range,
      List.range.loop] [sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealSat }

/-- `open`'s public data include its leak, from which `pub` has whether it
succeeds. -/
theorem open_verified :
    Verified RISCV64.target «open» (Proof.AesOcb.openScratchContract RISCV64.abi) :=
  Verified.of_correct open_correct open_ct
    { pre := by sig_implies_pre [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop, BitVec.add_zero]
      post := by sig_implies_post [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop]
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
        sig_simp [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
          Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
          aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
          stackArgAddr, List.getD, List.range, List.range.loop]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      sat := by sig_implies_sat [Proof.AesOcb.openScratchContract, Proof.AesOcb.openScratchSig, Spec.Ocb.openPre,
        Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak, openRISCV64, openLeak, openPreA, oneFacts, aCtx, aNonce, aAad, aData,
        aTag, aWork, onePub, openOut, args, rounds, RISCV64.abi, RISCV64.argRegs, stackArg,
        stackArgAddr, List.getD, List.range, List.range.loop] [openSat, sealSat, stackArg, stackArgAddr, Mem.readW,
        Mem.read] using openSat }

/-! ## With the working space on the stack

`seal` and `open` run their code, proved with the working space as their
last argument (above), in a frame that allocates it
(`Verified.stackScratchArgs`): `tag` and `tag_len` arrive on the stack, so
the frame of 2592 bytes copies them, then the working space's address, above
its stack pointer. The copies are read only where the pre- and
postconditions read the buffers, and `open`'s leak, whether it succeeds,
reads only its buffers (`Proof/AesOcb/Scratch.lean`). As AES-GCM's `open`
(`Proof/AesGcm/RISCV64/Verified.lean`).
-/

/-- A state satisfying `vg_aes_ocb_seal`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩, ⟨0x5000, 4⟩] }

theorem sealFrameSat_pre : ∃ s, (Proof.AesOcb.sealRoundsContract RISCV64.abi 2592).pre s := by
  implies_sat [Proof.AesOcb.sealRoundsContract, Spec.Ocb.sealSig, Spec.Ocb.sealPre, Proof.AesOcb.sealRoundsPost, RISCV64.abi,
    RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [sealFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using sealFrameSat

theorem seal_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «seal»)
      (Proof.AesOcb.sealRoundsContract RISCV64.abi 2592) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Ocb.sealSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.sealPre RISCV64.abi.ptrBits) (post := Proof.AesOcb.sealRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) (m := 2) seal_verified (by decide) (by decide)
    (Proof.AesOcb.sealPre_local _) (Proof.AesOcb.sealPost_local _) (Proof.AesOcb.sealPostOut_local _)
    sealFrameSat_pre

/-- A state satisfying `vg_aes_ocb_open`'s precondition, without the working
space: `tag` and `tag_len` alone on the stack. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 256⟩, ⟨0x2000, 1⟩, ⟨0x3000, 0⟩, ⟨0x5000, 4⟩, ⟨0x9000, 16⟩],
                 wr := [⟨0x4000, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Proof.AesOcb.openRoundsContract RISCV64.abi 2592).pre s := by
  implies_sat [Proof.AesOcb.openRoundsContract, Spec.Ocb.openSig, Spec.Ocb.openPre, Proof.AesOcb.openRoundsPost, Spec.Ocb.openLeak,
    RISCV64.abi, RISCV64.argRegs, stackArg, stackArgAddr, List.getD, List.range, List.range.loop]
    [openFrameSat, sealSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using openFrameSat

theorem open_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 «open»)
      (Proof.AesOcb.openRoundsContract RISCV64.abi 2592) :=
  RISCV64.Verified.stackScratchArgs (sig := Spec.Ocb.openSig) (nm := "work") (e := .u64) (n := 320)
    (pre := Spec.Ocb.openPre RISCV64.abi.ptrBits) (post := Proof.AesOcb.openRoundsPost RISCV64.abi.ptrBits)
    (wa := true) (stack := 0) (bytes := 2592) (m := 2) (leak := some (Spec.Ocb.openLeak RISCV64.abi.ptrBits))
    open_verified (by decide) (by decide) (Proof.AesOcb.openPre_local _) (Proof.AesOcb.openPost_local _)
    (Proof.AesOcb.openPostOut_local _) openFrameSat_pre (hleak := Proof.AesOcb.openLeak_local _)

end VG.Proof.AesOcb.RISCV64

/-! ## AES-OCB on RISC-V, without secret residue

`vg_aes_ocb_seal` and `vg_aes_ocb_open`, each followed by
`Impl.Scrub.RISCV64.scrubTail` (`RISCV64.Scrub.verifiedScrubbed`), which clears the
caller-saved registers and the whole 2592-byte frame (`withStackScratchArgs`)
that holds their working space, the offsets and the key schedule among it:
the residue analysis (`RISCV64.rtaint`) finds that all of it may hold
secrets. Their postconditions read the memory on return only within the
data and the tag, as on PPC64LE (`Proof/AesOcb/PPC64LE/Scrub.lean`). -/

namespace VG.Proof.AesOcb.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.AesOcb.RISCV64

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ocb.sealContract RISCV64.abi stack) (Spec.Ocb.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of0 hb.2.2.2.1 (by simp), bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ocb.openContract RISCV64.abi stack) (Spec.Ocb.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (by simp)]
      exact h key hk

/-- What the cleanup needs of `vg_aes_ocb_seal`'s code (`scrubSide`), by the kernel's
evaluation, stated apart from the registration record so that `lit_decide` sees only the
code. -/
theorem seal_scrubSide :
    scrubSide (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesOcb.RISCV64.«seal») 2592 0 []
      = true := by
  lit_decide

/-- `vg_aes_ocb_seal` as emitted (`Impl.AesOcb.RISCV64.Fn.«seal»`) meets its contract in constant
time and returns without secret residue: the theorem its registration binds. -/
theorem seal_scrubbed :
    VerifiedScrubbed target Impl.AesOcb.RISCV64.Fn.«seal»
      (Spec.Ocb.sealContract RISCV64.abi 2592) 0 :=
  verifiedScrubbed (api := Spec.Ocb.sealApi) (W := 2592)
    { code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesOcb.RISCV64.«seal»
      verified := Proof.AesOcb.seal_keyed seal_framed }
    (sealOut _) seal_scrubSide

/-- What the cleanup needs of `vg_aes_ocb_open`'s code (`scrubSide`), by the kernel's
evaluation, stated apart from the registration record so that `lit_decide` sees only the
code. -/
theorem open_scrubSide :
    scrubSide (Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesOcb.RISCV64.«open») 2592 32 []
      = true := by
  lit_decide

/-- `vg_aes_ocb_open` as emitted (`Impl.AesOcb.RISCV64.Fn.«open»`) meets its contract in constant
time and returns without secret residue: the theorem its registration binds. -/
theorem open_scrubbed :
    VerifiedScrubbed target Impl.AesOcb.RISCV64.Fn.«open»
      (Spec.Ocb.openContract RISCV64.abi 2592) 32 :=
  verifiedScrubbed (api := Spec.Ocb.openApi) (W := 2592)
    { code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesOcb.RISCV64.«open»
      verified := Proof.AesOcb.open_keyed open_framed }
    (openOut _) open_scrubSide

end VG.Proof.AesOcb.RISCV64.Scrub
