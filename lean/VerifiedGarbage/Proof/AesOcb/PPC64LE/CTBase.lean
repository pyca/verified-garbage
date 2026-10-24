module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Args
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LE f).pre (Proof.Aes.blocksPPC64LE f).pub c)
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
  rw [← e29, ← e31] at h₂
  exact ⟨V₁ .r29, D, V₁ .r31 + BitVec.ofNat 64 512, R, k, h₁.1, h₂.1,
    by rw [h₁.2.2.sp, h₂.2.2.sp, E₁.sp, E₂.sp]⟩

/-- `encOne d`, in two runs. -/
theorem encOne_rel {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V₁ .r28 = BitVec.ofNat 64 R) {σ₁ σ₂ : State}
    (E₁ : Env V₁ sp σ₁) (E₂ : Env V₂ sp σ₂) {d : Nat} (hd : d + 16 ≤ 512)
    (hc : ∃ h, (VG.Taint.check taint (Taint.ofRegs ([] ++ pubR))
      (.block (callArgs ++ [.addi .r5 .r31 d, .li .r6 1])) h).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) (encOne d) TT :=
  callBlocks_rel L hV Proof.Aes.PPC64LE.encryptBlocks_correct Proof.Aes.PPC64LE.encryptBlocks_ct hR h28 E₁ E₂ []
    (fun _ h => absurd h List.not_mem_nil) hc
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E₁.r31]) (by omega))
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E₂.r31, ← hV .r31 (by decide)])
      (by omega))
    (dstW L E₁.perm (by omega)) (dstW L (by rw [hV .r29 (by decide), hV .r31 (by decide)]; exact E₂.perm) (by omega))

end

/-- Proves `∀ r ∈ [r₁, …], σ₁.gpr r = σ₂.gpr r` by rewriting each side with `ts`. -/
tactic_template "agree_ppc" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  plain_simp_names simp only [List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true,
    and_self, $ts,*])

end VG.Proof.AesOcb.PPC64LE
