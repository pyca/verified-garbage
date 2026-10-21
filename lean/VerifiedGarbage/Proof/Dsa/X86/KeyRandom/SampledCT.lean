module
public meta import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.InvokeTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallArgs
import VerifiedGarbage.Proof.Dsa.X86.RandomAttempt
public import VerifiedGarbage.Impl.Dsa.X86.GenerateKey
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CallResult
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.DrawCT
import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Sample

/-! # The accepted draw calls derivation with only its permitted leak -/
@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.KeyRandom VG.Impl.Dsa.X86.GenerateKey

theorem post_of_exec {c : Prog isa} {s t : State} {tr : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (e : Exec isa c s tr t) : Q t := by
  obtain ⟨_, u, he, hq⟩ := h
  obtain ⟨_, rfl⟩ := Exec.det e he
  exact hq

theorem deriveArgs_step {s t : State} (A : KeyABI s) (h : Ready s t) {k : Nat}
    (hn : Spec.Rsa.bytesAt t.mem (off (rBase s) oNonce) (rQBytes s).length =
      Spec.Dsa.encodeBE (rQBytes s).length k) :
    WP isa (.block deriveArgs) t fun u => Ready s u ∧ CallSlots s u ∧
      callResult s u = Spec.Dsa.deriveKeyBytes (rInput s).pLen (rInput s).qLen (rInput s).key
        (Spec.Dsa.encodeBE (rInput s).qLen k) ∧ Outs (rBase s) [(0,36)] t.mem u.mem := by
  have hql := rQBytes_le A
  change WP isa (.block (deriveArgs ++ [])) t _
  refine deriveArgs_ok A h fun u hu mu ku => WP.block_nil ⟨hu, ?_, ?_, ?_⟩
  · intro i hi
    rw [mu, ku.1 .esp (by decide)]
    exact argsMem_slots s _ _ i hi
  · apply callResult_eq A hu
    have ou := argsMem_outs s t.mem (t.gpr .esp)
    rw [← mu] at ou
    rw [outs_frame_bytes ou (by decide) (by unfold oNonce; omega)]
    exact hn
  · have ou := argsMem_outs s t.mem (t.gpr .esp)
    rw [←mu] at ou
    exact ou

theorem sampleCmp {s t : State} (A : KeyABI s) (O : SampleOut s 0 (draw s) t)
    (ax : t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (draw s))) :
    WP isa (.block [.alu .cmp .eax (.imm 1)]) t fun u =>
      SampleOut s 0 (draw s) u ∧
      u.zf = some (decide (VG.Proof.Dsa.Random.sampleStatus (draw s) = 1)) := by
  have h := O.smp.choose_spec.ready
  have hl := sampleStatus_le (draw s)
  refine wp_cmpi fun u fu _ zu => WP.block_nil ⟨O.mem A (h.fupd fu) fu.mem, ?_⟩
  rw [zu, ax, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]

theorem scalar_of_status {S : Spec.Dsa.Random.Sample} (h : VG.Proof.Dsa.Random.sampleStatus S = 1) :
    ∃ k, S.scalar = some k := by
  cases hx : S.scalar with
  | some k => exact ⟨k, rfl⟩
  | none => simp only [VG.Proof.Dsa.Random.sampleStatus, hx] at h; split at h <;> contradiction

theorem sampledWith_ct {I : State → Mem → Prop} (F : DeriveInvoke I) (stable : StableScratch I)
    (timing : DeriveInvokeCT F) {s₁ s₂ t₁ t₂ : State}
    (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : keyLeak s₁ = keyLeak s₂) (hc₁ : checked s₁ = true) (hc₂ : checked s₂ = true)
    (hr : (rResult s₁).status = (rResult s₂).status)
    (hs : VG.Proof.Dsa.Random.sampleStatus (draw s₁) = VG.Proof.Dsa.Random.sampleStatus (draw s₂))
    (O₁ : SampleOut s₁ 0 (draw s₁) t₁) (O₂ : SampleOut s₂ 0 (draw s₂) t₂)
    (ax₁ : t₁.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (draw s₁)))
    (ax₂ : t₂.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (draw s₂)))
    (inv₁ : I s₁ t₁.mem) (inv₂ : I s₂ t₂.mem)
    {tr₁ tr₂ : List Leak} {u₁ u₂ : State}
    (x₁ : Exec isa (sampledWith F.code) t₁ tr₁ u₁)
    (x₂ : Exec isa (sampledWith F.code) t₂ tr₂ u₂) : tr₁ = tr₂ := by
  unfold sampledWith at x₁ x₂
  cases x₁ with | seq c₁ b₁ =>
  cases x₂ with | seq c₂ b₂ =>
  have ct : RelCT isa (fun _ _ => True) (.block [.alu .cmp .eax (.imm 1)]) (fun _ _ => True) :=
    RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (by taint_decide)
  have ec := (ct _ _ _ _ _ _ trivial c₁ c₂).1
  obtain ⟨P₁, z₁⟩ := post_of_exec (sampleCmp A₁ O₁ ax₁) c₁
  obtain ⟨P₂, z₂⟩ := post_of_exec (sampleCmp A₂ O₂ ax₂) c₂
  have branch : ∀ {a b : State}, a.zf = some (decide (VG.Proof.Dsa.Random.sampleStatus (draw s₁) = 1)) →
      b.zf = some (decide (VG.Proof.Dsa.Random.sampleStatus (draw s₂) = 1)) → eval .e a = eval .e b := by
    intro a b ha hb; simp only [eval, ha, hb, hs]
  cases b₁ with
  | iteF f₁ b₁ =>
    cases b₂ with
    | iteT f₂ b₂ => have bad := f₁.symm.trans ((branch z₁ z₂).trans f₂); cases bad
    | iteF _ b₂ => cases b₁ with | block b₁ => cases b₁; cases b₂ with | block b₂ => cases b₂; simp only [ec]
  | iteT f₁ b₁ =>
    cases b₂ with
    | iteF f₂ b₂ => have bad := f₁.symm.trans ((branch z₁ z₂).trans f₂); cases bad
    | iteT f₂ b₂ =>
      have st₁ : VG.Proof.Dsa.Random.sampleStatus (draw s₁) = 1 := by simpa only [eval, z₁, Option.some.injEq, decide_eq_true_eq] using f₁
      have st₂ : VG.Proof.Dsa.Random.sampleStatus (draw s₂) = 1 := hs ▸ st₁
      obtain ⟨k₁, h₁⟩ := scalar_of_status st₁
      obtain ⟨k₂, h₂⟩ := scalar_of_status st₂
      cases b₁ with | seq a₁ d₁ => cases d₁ with | seq d₁ w₁ =>
      cases b₂ with | seq a₂ d₂ => cases d₂ with | seq d₂ w₂ =>
      have ra := P₁.smp.choose_spec.ready
      have rb := P₂.smp.choose_spec.ready
      have ca : RelCT isa (Two (At Ready)) (.block deriveArgs) (fun _ _ => True) :=
        two_taint [.esp] (pins_at id fun _ _ _ h => h) (by taint_decide)
      have ea := (ca _ _ _ _ _ _ ⟨pubOf s₁, ⟨s₁, A₁, rfl, ra⟩, s₂, A₂, e.symm, rb⟩ a₁ a₂).1
      obtain ⟨rd₁, sl₁, res₁, args₁⟩ := post_of_exec (deriveArgs_step A₁ ra (P₁.nonce k₁ h₁)) a₁
      obtain ⟨rd₂, sl₂, res₂, args₂⟩ := post_of_exec (deriveArgs_step A₂ rb (P₂.nonce k₂ h₂)) a₂
      have rst := hr
      rw [result_eq A₁, result_eq A₂, hc₁, hc₂] at rst
      simp only [ite_true, h₁, h₂] at rst
      have rst' := (congrArg Spec.Dsa.signStatus res₁).trans
        (rst.trans (congrArg Spec.Dsa.signStatus res₂).symm)
      have i₁ := stable args₁ (by decide) ((post_of_exec (compare_mem 1 t₁) c₁).symm ▸ inv₁)
      have i₂ := stable args₂ (by decide) ((post_of_exec (compare_mem 1 t₂) c₂).symm ▸ inv₂)
      have ed := (timing _ _ _ _ _ _ ⟨s₁,s₂,A₁,A₂,e,hk,rd₁,rd₂,sl₁,sl₂,rst',hc₁,hc₂,i₁,i₂⟩ d₁ d₂).1
      obtain ⟨rw₁, _⟩ := post_of_exec (F.correct A₁ rd₁ sl₁ hc₁ i₁) d₁
      obtain ⟨rw₂, _⟩ := post_of_exec (F.correct A₂ rd₂ sl₂ hc₂ i₂) d₂
      have cw : RelCT isa (Two (At Ready)) (.block [.store (sp oStatus) .eax]) (fun _ _ => True) :=
        two_taint [.esp] (pins_at id fun _ _ _ h => h) (by taint_decide)
      have ew := (cw _ _ _ _ _ _ ⟨pubOf s₁, ⟨s₁, A₁, rfl, rw₁⟩, s₂, A₂, e.symm, rw₂⟩ w₁ w₂).1
      simp only [ec, ea, ed, ew]
theorem sampled_ct (F : DeriveFn) {s₁ s₂ t₁ t₂ : State}
    (A₁ : KeyABI s₁) (A₂ : KeyABI s₂) (e : pubOf s₁ = pubOf s₂)
    (hk : keyLeak s₁ = keyLeak s₂) (hc₁ : checked s₁ = true) (hc₂ : checked s₂ = true)
    (hr : (rResult s₁).status = (rResult s₂).status)
    (hs : VG.Proof.Dsa.Random.sampleStatus (draw s₁) = VG.Proof.Dsa.Random.sampleStatus (draw s₂))
    (O₁ : SampleOut s₁ 0 (draw s₁) t₁) (O₂ : SampleOut s₂ 0 (draw s₂) t₂)
    (ax₁ : t₁.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (draw s₁)))
    (ax₂ : t₂.gpr .eax = BitVec.ofNat 32 (VG.Proof.Dsa.Random.sampleStatus (draw s₂)))
    {tr₁ tr₂ : List Leak} {u₁ u₂ : State}
    (x₁ : Exec isa (sampled F.name F.code) t₁ tr₁ u₁)
    (x₂ : Exec isa (sampled F.name F.code) t₂ tr₂ u₂) : tr₁ = tr₂ :=
  sampledWith_ct F.invoke (fun _ _ _ => trivial) F.invoke_ct A₁ A₂ e hk hc₁ hc₂ hr hs O₁ O₂ ax₁ ax₂ trivial trivial x₁ x₂

end VG.Proof.Dsa.X86.KeyRandom
