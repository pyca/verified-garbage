module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCalls
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecPost
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PrivCheck

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time, the frame of the proof

Two runs with the same public data (`dataOf`) satisfy the same facts about
it (`Same`); from the entry states `s₁` and `s₂` (an `Env`), two runs are
related at each step by `Rel e P`: run `i` satisfies `P sᵢ`, a predicate
correctness gives, which fixes as functions of the entry state the registers
the next step's addresses depend on (`rel_step`, `rel_call`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

/-- The public data. -/
abbrev Data := List (BitVec 64) × List (BitVec 64) × List Nat × Addr

def dataOf (s : State) : Data :=
  (argRegs.map s.gpr, (List.range 15).map (stackArg s),
    (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat ++ Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat).map
      (·.toNat), s.sp)

theorem pub_data {s₁ s₂ : State} (h : (Spec.RsaPkcs1Enc.decryptContract abi stackBytes).pub s₁ s₂) :
    dataOf s₁ = dataOf s₂ := by
  have e : stackBytes = 3631 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_fifteen,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14⟩ := h
  unfold dataOf
  rw [hl]
  simp only [argRegs, List.map_cons, List.map_nil, stackArgs_fifteen, h3, h4, h5, h6, h7, h8, h9, h10, a0,
    a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, hsp]

/-- The public data's facts. -/
structure Same (s₁ s₂ : State) : Prop where
  gpr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  arg : ∀ i < 15, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r6) (s₁.gpr .r7).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r6) (s₂.gpr .r7).toNat
  e : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

theorem same_of {s₁ s₂ : State} (h : dataOf s₁ = dataOf s₂) : Same s₁ s₂ := by
  simp only [dataOf, Prod.mk.injEq] at h
  obtain ⟨hr, ha, hb, hsp⟩ := h
  have gr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r := List.map_inj_left.mp hr
  have h7 : s₁.gpr .r7 = s₂.gpr .r7 := gr _ (by decide)
  rw [List.map_append, List.map_append] at hb
  obtain ⟨hn, he⟩ := List.append_inj hb (by simp [Proof.Rsa.bytesAt_length', h7])
  exact ⟨gr, fun i hi => List.map_inj_left.mp ha i (List.mem_range.mpr hi), hsp,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn,
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he⟩

/-- Two entry states with the same public data. -/
structure Env where
  s₁ : State
  s₂ : State
  h₁ : DPre s₁
  h₂ : DPre s₂
  S : Same s₁ s₂

/-- Run `i` satisfies `P sᵢ`. -/
def Rel (e : Env) (P : State → State → Prop) (a b : State) : Prop := P e.s₁ a ∧ P e.s₂ b

section
variable {e : Env}

theorem Env.r (e : Env) {r : Reg} (hr : r ∈ argRegs := by decide) : e.s₁.gpr r = e.s₂.gpr r := e.S.gpr r hr
theorem Env.arg (e : Env) {i : Nat} (hi : i < 15 := by decide) : stackArg e.s₁ i = stackArg e.s₂ i := e.S.arg i hi
theorem Env.fb_eq (e : Env) : fb e.s₁ = fb e.s₂ := by
  show e.s₁.sp - _ = e.s₂.sp - _; rw [e.S.sp]
theorem Env.scA_eq (e : Env) (a : Nat) : scA e.s₁ a = scA e.s₂ a := by
  show stackArg e.s₁ 13 + _ = stackArg e.s₂ 13 + _; rw [e.arg]

/-- A step, from what correctness gives of each run. -/
theorem rel_post {P P' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Rel e P) c fun _ _ => True)
    (hw : ∀ s u, DPre s → P s u → WP isa c u (P' s)) : RelCT isa (Rel e P) c (Rel e P') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ e.h₁ hp.1
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ e.h₂ hp.2
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, y₁, y₂⟩

/-- A step the taint analysis checks from the registers `rs`, which `P` fixes. -/
theorem rel_step {P P' : State → State → Prop} {c : Prog isa} (rs : List Reg) {hc : VG.Taint.Hint T}
    (h : (taint.check (ofRegs rs) c hc).isSome = true) (hpin : ∀ a b, P e.s₁ a → P e.s₂ b → AgreeOn rs a b)
    (hw : ∀ s u, DPre s → P s u → WP isa c u (P' s)) : RelCT isa (Rel e P) c (Rel e P') :=
  rel_post (rel_of h fun a b hab => hpin a b hab.1 hab.2) hw

theorem rel_mono {P P' : State → State → Prop} {c : Prog isa} {Q : State → State → Prop}
    (h : RelCT isa (Rel e P) c (Rel e Q)) (hq : ∀ s u, Q s u → P' s u) : RelCT isa (Rel e P) c (Rel e P') :=
  h.mono (fun _ _ h => h) fun _ _ ⟨a, b⟩ => ⟨hq _ _ a, hq _ _ b⟩

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
