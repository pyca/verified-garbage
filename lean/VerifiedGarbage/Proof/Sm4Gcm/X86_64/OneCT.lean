module

import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Seal
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.TagCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
import VerifiedGarbage.Proof.AesGcm.X86_64.J0
import VerifiedGarbage.Proof.AesGcm.X86_64.J0CT
import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Seal
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptCT
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.AesGcm.X86_64.J0
meta import VerifiedGarbage.Proof.AesGcm.X86_64.J0CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.TagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Flush
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.X86_64
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Crypt
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OneShot

/-!
# SM4-GCM on x86-64: `seal` and its pieces in two runs

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/OneCT.lean`, `SealCT.lean`): what stays in `W` between
the pieces (`OneS`: the additional data's address and length, the data's
address and length) is the same in both runs, so each piece (`oneAad`,
`oneCrypt`, `oneTag`) leaks the same; `seal` copies the tag to the same
address, on the stack.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm oneAad absorbPad j0 aadO alenO dataO lenO tlenO tagOut restore)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env DataOk AbsIn J0In rel_taint rel_wp env_agree TagAt tagOut_rel
  fn_rel₂ ct_of_rel j0_ok j0_rel absorbPad_ok absorbPad_rel)

/-- What stays in `W` and the buffers between the pieces of `seal` and `open`. -/
structure OneS (Ctx W SP : Addr) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 n
  dA : DataOk (W + BitVec.ofNat 64 16) W SP s A al
  dD : DataW4 Ctx (W + BitVec.ofNat 64 16) W SP s D n

section
variable {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

theorem OneS.frame {A : Addr} {al : Nat} {D : Addr} {n : Nat} {s s' : State}
    (h : OneS Ctx W SP A al D n s) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s') (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (oneFrame W D SP n) s.mem s'.mem) : OneS Ctx W SP A al D n s' := by
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd)
      (by decide)
  exact ⟨he, by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact h.aad,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact h.alen,
    by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact h.dat, by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact h.len,
    by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact h.tlen, h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr⟩

omit L in
theorem OneS.keep {A : Addr} {al : Nat} {D : Addr} {n : Nat} {s s' : State}
    (h : OneS Ctx W SP A al D n s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OneS Ctx W SP A al D n s' :=
  ⟨h.env.keep hg hrd hwr, by rw [hm]; exact h.aad, by rw [hm]; exact h.alen, by rw [hm]; exact h.dat,
    by rw [hm]; exact h.len, by rw [hm]; exact h.tlen, h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr⟩

omit L in
/-- Two slots of `W` loaded, and a constant. -/
theorem load2_ok {A : Addr} {al : Nat} {D : Addr} {n : Nat} {s : State}
    (h : OneS Ctx W SP A al D n s) {o₁ o₂ : Nat} {P : Addr} {k : Nat}
    (h₁ : s.mem.readW (W + BitVec.ofNat 64 o₁) 64 = P) (h₂ : s.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 k)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₁) 8) (q₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₂) 8) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)]) s
      fun s₁ => OneS Ctx W SP A al D n s₁ ∧ s₁.gpr .r12 = P ∧ s₁.gpr .rbp = BitVec.ofNat 64 k ∧
        s₁.gpr .rbx = BitVec.ofNat 64 0 := by
  have h15 := h.env.r15
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 o₁)),
      .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)] s = some s₁ ∧ s₁.gpr .r12 = P ∧
      s₁.gpr .rbp = BitVec.ofNat 64 k ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h₁]
    · simp [gpr_setReg, h₂]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, h12, hbp, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)

end

theorem w_one {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (AesGcm.X86_64.wFrame W SP) m m') :
    Frame (oneFrame W D SP n) m m' :=
  wFrame_one (o := 0) (.inl rfl) (wFrame_cons (wFrame_of_aes h))

/-- Two runs in `OneS` for the same parameters. -/
abbrev OneS₂ (Ctx W SP : Addr) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (s₁ s₂ : State) : Prop :=
  OneS Ctx W SP A al D n s₁ ∧ OneS Ctx W SP A al D n s₂

theorem OneS₂.env {Ctx W SP A : Addr} {al : Nat} {D : Addr} {n : Nat} {s₁ s₂ : State}
    (h : OneS₂ Ctx W SP A al D n s₁ s₂) : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r :=
  env_agree h.1.env h.2.env

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- The additional data, absorbed and padded. -/
theorem aadRest_rel {A : Addr} {al : Nat} {D : Addr} {n : Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP A al D n)
      (.seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)])
      (absorbPad v.callees 16)) (OneS₂ Ctx W SP A al D n) := by
  have La := L.lay
  have hL : ∀ s, OneS Ctx W SP A al D n s → WP isa (.block [.mov .r12 (.mem (at_ .r15 aadO)),
      .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP A al D n s₁ ∧
      s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.aad h.alen (h.env.perm.wR (show 232 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 184 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => OneS Ctx W SP A al D n s ∧ s.gpr .r12 = A ∧
    s.gpr .rbp = BitVec.ofNat 64 al ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] A al s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dA, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorbPad v.callees 16) s (OneS Ctx W SP A al D n) := fun s h =>
    WP.mono (AesGcm.X86_64.WP.with_rdwr (absorbPad_ok v La (.inr rfl) (ai s h) rfl)) fun _ ⟨o, hrd, hwr⟩ => by
      obtain ⟨m, fa, ft⟩ := o.frame
      exact h.1.frame L o.env hrd hwr hDW
        (w_one ((AesGcm.X86_64.absFrame_one fa).trans (AesGcm.X86_64.tFrame_one ft)))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorbPad_rel v La (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := A) (n := al) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  exact (RelCT.seq a b).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `J₀` of the nonce, and the additional data. -/
theorem oneAad_rel {Np A : Addr} {nl al : Nat} {D : Addr} {n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => (OneS Ctx W SP A al D n s₁ ∧ s₁.gpr .r12 = Np ∧ s₁.gpr .rbp = BitVec.ofNat 64 nl ∧
        DataOk (W + BitVec.ofNat 64 16) W SP s₁ Np nl) ∧ (OneS Ctx W SP A al D n s₂ ∧ s₂.gpr .r12 = Np ∧
        s₂.gpr .rbp = BitVec.ofNat 64 nl ∧ DataOk (W + BitVec.ofNat 64 16) W SP s₂ Np nl))
      (oneAad v.callees) (OneS₂ Ctx W SP A al D n) := by
  have La := L.lay
  have ji : ∀ s, (OneS Ctx W SP A al D n s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) →
      J0In Ctx (W + BitVec.ofNat 64 16) W SP (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) Np nl s :=
    fun s h => ⟨h.1.env, rfl, h.2.1, h.2.2.1, h.2.2.2⟩
  have hJ : ∀ s, (OneS Ctx W SP A al D n s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) → WP isa (j0 v.callees) s (OneS Ctx W SP A al D n) :=
    fun s h => WP.mono (AesGcm.X86_64.WP.with_rdwr (j0_ok v La (ji s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (w_one (AesGcm.X86_64.j0Frame_one o.frame))
  have a := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      j0_rel v La (H₁ := H₁) (H₂ := H₂) (Np := Np) (n := nl)).mono
      (fun _ _ h => ⟨_, _, ji _ h.1, ji _ h.2⟩) fun _ _ h => h) (fun _ _ h => h) hJ hJ
  exact RelCT.seq a ((aadRest_rel v L hDW).mono (fun _ _ h => h.2) fun _ _ h => h)

omit v in
/-- The data encrypted or decrypted. -/
theorem oneCrypt_rel {A : Addr} {al : Nat} {D : Addr} {n : Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP A al D n) oneCrypt (OneS₂ Ctx W SP A al D n) := by
  have hL : ∀ s, OneS Ctx W SP A al D n s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP A al D n s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let CI : State → Prop := fun s => OneS Ctx W SP A al D n s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ci : ∀ s, CI s → CrIn Ctx (W + BitVec.ofNat 64 16) W SP 0 0 D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD⟩
  have hC : ∀ s, CI s → WP isa cryptAl s (OneS Ctx W SP A al D n) := fun s h =>
    WP.mono (AesGcm.X86_64.WP.with_rdwr (cryptAl_ok L (ci s h) rfl)) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (crFrame_one o.frame)
  have b := rel_wp ((cryptAl_rel L (icb₁ := 0) (icb₂ := 0) (P₁ := 0) (P₂ := 0) (D := D) (n := n) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ CI s₁ ∧ CI s₂) (fun _ _ h => ⟨ci _ h.2.1, ci _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hC hC
  exact (RelCT.seq a b).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The tag of the data (as ciphertext) into `W + o`. -/
theorem oneTag_rel {A : Addr} {al : Nat} {D : Addr} {n : Nat} {o : Nat} (ho : o = 0 ∨ o = 112)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP A al D n) (oneTag v.callees o) fun _ _ => True := by
  have La := L.lay
  have hL : ∀ s, OneS Ctx W SP A al D n s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP A al D n s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => OneS Ctx W SP A al D n s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD.dw.ok, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorbPad v.callees 16) s (OneS Ctx W SP A al D n) := fun s h =>
    WP.mono (AesGcm.X86_64.WP.with_rdwr (absorbPad_ok v La (.inr rfl) (ai s h) rfl)) fun _ ⟨o, hrd, hwr⟩ => by
      obtain ⟨m, fa, ft⟩ := o.frame
      exact h.1.frame L o.env hrd hwr hDW
        (w_one ((AesGcm.X86_64.absFrame_one fa).trans (AesGcm.X86_64.tFrame_one ft)))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorbPad_rel v La (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := D) (n := n) rfl rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  -- The lengths, for `tag`.
  have hT : ∀ s, OneS Ctx W SP A al D n s → WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))]) s fun s₁ => OneS Ctx W SP A al D n s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 n := fun s h => by
    have q₁ := h.env.perm.wR (show 184 + 8 ≤ 2560 by decide)
    have q₂ := h.env.perm.wR (show 192 + 8 ≤ 2560 by decide)
    have h15 := h.env.r15
    obtain ⟨s₁, run₁, hbx, hbp, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .mov .rbp (.mem (at_ .r15 tlenO))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧
        s₁.gpr .rbp = BitVec.ofNat 64 n ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h.alen]
      · simp [gpr_setReg, h.tlen]
      · intro r a b; simp [gpr_setReg, a, b]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hbx, hbp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)
  have e := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ OneS₂ Ctx W SP A al D n s₁ s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hT hT
  have t := (tag_rel v L ho).mono (P' := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP A al D n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 n) ∧
      (OneS Ctx W SP A al D n s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 al ∧ s₂.gpr .rbp = BitVec.ofNat 64 n))
    (fun _ _ h => ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) fun _ _ h => h
  exact RelCT.seq a (RelCT.seq b (RelCT.seq e t))

end

theorem one_pub {k : Nat} {s₀ s₀' : State} (hq : Proof.Sm4Gcm.onePub k s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `oneAad`'s precondition, after the entry. -/
theorem OneEntry.aadPre {s₀ s : State} {k : Nat} {Ctx W SP Np A D : Addr}
    {nl al n : Nat} (C : OneCtx s₀ k Ctx W SP Np A D nl al n)
    (E : OneEntry s₀ Ctx W SP A D n s) (hNp : s₀.gpr .rsi = Np)
    (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al) :
    OneS Ctx W SP A al D n s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl :=
  ⟨⟨E.env, E.aad, by rw [E.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len, E.tlen,
    C.aad.of_eq E.rd E.wr, C.data.of_eq E.rd E.wr⟩, by rw [E.r12, hNp],
    by rw [E.rbp, ← hnl, BitVec.ofNat_toNat, BitVec.setWidth_eq], C.nonce.of_eq E.rd E.wr⟩

/-- After the entry, `seal` up to the tag in two runs: `oneAad`, `oneCrypt`
and `oneTag 0`. -/
theorem sealRun_rel (v : GcmImpl) {s₀ s₀' : State} {Ctx W SP Np A D : Addr} {nl al n : Nat}
    (C : OneCtx s₀ 3 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 3 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al)
    (hNp' : s₀'.gpr .rsi = Np) (hnl' : (s₀'.gpr .rdx).toNat = nl) (hal' : (s₀'.gpr .r8).toNat = al) :
    RelCT isa (fun s₁ s₂ => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
      (.seq (oneAad v.callees) (.seq oneCrypt (oneTag v.callees 0))) fun _ _ => True := by
  have L := C.lay
  have hDW := C.dE
  have a := (oneAad_rel v L hDW (Np := Np) (nl := nl)).mono
    (P' := fun (s₁ s₂ : State) => True ∧ OneEntry s₀ Ctx W SP A D n s₁ ∧ OneEntry s₀' Ctx W SP A D n s₂)
    (fun _ _ h => ⟨h.2.1.aadPre C hNp hnl hal, h.2.2.aadPre C' hNp' hnl' hal'⟩) fun _ _ h => h
  exact (RelCT.seq a (RelCT.seq (oneCrypt_rel L hDW) (oneTag_rel v L (.inl rfl) hDW))).mono (fun _ _ h => h)
    fun _ _ _ => trivial

/-- `e; (m; (o; f))`, related as `e; ((m; o); f)`. -/
theorem rel_reassoc_mid {P Q : State → State → Prop} {e m o f : Prog isa}
    (h : RelCT isa P (.seq e (.seq (.seq m o) f)) Q) : RelCT isa P (.seq e (.seq m (.seq o f))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq m₁ e₁ => cases e₁ with | seq o₁ f₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq m₂ e₂ => cases e₂ with | seq o₂ f₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq m₁ o₁) f₁)) (.seq x₂ (.seq (.seq m₂ o₂) f₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `x; (a; (b; ((c; d); f)))`, related as `x; ((a; (b; c)); (d; f))`. -/
theorem rel_reassoc_seal {P Q : State → State → Prop} {x a b c d f : Prog isa}
    (h : RelCT isa P (.seq x (.seq (.seq a (.seq b c)) (.seq d f))) Q) :
    RelCT isa P (.seq x (.seq a (.seq b (.seq (.seq c d) f)))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with
    | seq e₁ f₁ => cases e₁ with | seq c₁ d₁ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with
    | seq e₂ f₂ => cases e₂ with | seq c₂ d₂ =>
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq x₁ (.seq (.seq a₁ (.seq b₁ c₁)) (.seq d₁ f₁)))
    (.seq x₂ (.seq (.seq a₂ (.seq b₂ c₂)) (.seq d₂ f₂)))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

theorem seal_rel (v : GcmImpl) {s₀ s₀' : State}
    (hp : Proof.Sm4Gcm.sealX86_64.pre s₀) (hp' : Proof.Sm4Gcm.sealX86_64.pre s₀')
    (hq : Proof.Sm4Gcm.sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callees) fun _ _ => True := by
  have C := (OneCtx.ofSeal hp).1
  have C' := (OneCtx.ofSeal hp').1
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩ := hq'
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  simp only [Proof.Sm4Gcm.arg] at a₀ a₁ a₂
  have ha₂ := C.args 2 (by decide); have ha₂' := C'.args 2 (by decide)
  have hw24 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 24) 64 := a₂
  have hT₁ : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s₀ 1 := rfl
  have hT₂ : s₀'.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s₀ 1 := by rw [q₇, a₁]; rfl
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₂] at C'
  have hE : ∀ {s : State} (C : OneCtx s 3 (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi) (s₀.gpr .rcx)
      (s₀.gpr .r9) (s₀.gpr .rdx).toNat (s₀.gpr .r8).toNat (stackArg s₀ 0).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .rcx = s₀.gpr .rcx →
      s.gpr .r9 = s₀.gpr .r9 → (stackArg s 0).toNat = (stackArg s₀ 0).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s₀ 2 →
      InRegions (s.rd ++ s.wr) (s₀.gpr .rsp + BitVec.ofNat 64 24) 8 →
      WP isa (.block (oneEntry 24)) s
        (OneEntry s (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rcx) (s₀.gpr .r9) (stackArg s₀ 0).toNat) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ => oneEntry_ok (by decide) C h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hE₁ := hE C rfl rfl rfl rfl rfl rfl ha₂
  have hE₂ := hE C' q₁.symm q₇.symm q₄.symm q₆.symm (by rw [a₀]) (by rw [q₇, a₂]; rfl) (by rw [q₇]; exact ha₂')
  rw [oneEntry, List.append_assoc, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [«seal», oneEntry, List.append_assoc, List.append_assoc, List.append_assoc]
  refine rel_reassoc_seal (rel_reassoc_mid (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 2 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 2) (SP := s₀.gpr .rsp) (k := 24) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub hq) hw24 ha₂ ha₂' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_))
  -- The address of `tag`, at `[SP + 16]`, after the tag: by correctness.
  have dA : ∀ r : Region, r.Sub ⟨stackArg s₀ 2, 2560⟩ ∨ r.Sub ⟨s₀.gpr .r9, (stackArg s₀ 0).toNat⟩ ∨
      r.Sub (below (s₀.gpr .rsp) stkN) → (⟨s₀.gpr .rsp + BitVec.ofNat 64 16, 8⟩ : Region).Disjoint r :=
    fun _ hr => arg16_disj (by decide) C.dA C.dAD hr
  have hW : ∀ {s₀'' s : State} (C : OneCtx s₀'' 3 (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi)
      (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .rdx).toNat (s₀.gpr .r8).toNat (stackArg s₀ 0).toNat),
      s₀''.gpr .rsi = s₀.gpr .rsi → (s₀''.gpr .rdx).toNat = (s₀.gpr .rdx).toNat →
      (s₀''.gpr .r8).toNat = (s₀.gpr .r8).toNat →
      s₀''.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s₀ 1 →
      OneEntry s₀'' (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rcx) (s₀.gpr .r9) (stackArg s₀ 0).toNat s →
      WP isa (.seq (oneAad v.callees) (.seq oneCrypt (oneTag v.callees 0))) s
        (TagAt (s₀.gpr .rdi) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) (s₀.gpr .rsp) .rsp 16
          (stackArg s₀ 1)) :=
    fun C h₁ h₂ h₃ hT E => WP.mono (sealRun_ok v C E h₁ h₂ h₃) fun _ ⟨he, hrd, hwr, _, f, _⟩ => ⟨he, by
      rw [he.rsp, f.readW (r := ⟨s₀.gpr .rsp + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dA _ (.inl fun _ h => h)
        · exact dA _ (.inr (.inl fun _ h => h))
        · exact dA _ (.inr (.inr fun _ h => h))) (by decide), hT], by
      rw [he.rsp, hrd, hwr]; exact C.args 1 (by decide)⟩
  have m := rel_wp (sealRun_rel v C C' rfl rfl rfl q₂.symm (by rw [q₃]) (by rw [q₅]))
    (fun _ _ h => h.2) (fun _ h => hW C rfl rfl rfl hT₁ h) (fun _ h => hW C' q₂.symm (by rw [q₃]) (by rw [q₅]) hT₂ h)
  exact RelCT.seq m (tagOut_rel (b := .rsp) (d := 16) (by simp) ⟨_, by taint_decide⟩ (fun _ _ h => h.2))

theorem seal_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.sealX86_64.pre Proof.Sm4Gcm.sealX86_64.pub («seal» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => seal_rel v hp hp' hq

end VG.Proof.Sm4Gcm.X86_64
