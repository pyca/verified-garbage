module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptCT
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
public import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamText
import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptCT
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Contract
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.CryptOk
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamText
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.StreamCrypt
meta import VerifiedGarbage.Proof.AesGcm.X86_64.AbsorbCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.StreamText
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Absorb
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.X86_64

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_stream_encrypt` and `_decrypt` are constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/StreamCryptCT.lean`): the branches are on the length
of the data and of the text so far, the same in both runs; the padding of
the additional data is AES-GCM's (`start_rel`); `crypt` and `absorb` are on
data at the same address, of the same length (`crypt_rel`, `absorb_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ tlenO streamLoad partWith absorb firstFlush restore)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env AbsIn rel_taint rel_wp rel_ite_e rel_reassoc2 rel_both rel_envT
  env_agree absRegs absorb_ok absorb_rel start_rel load_ok load_env toNat_mod16 test_ok fn_rel₂ ct_of_rel)

/-- Between `crypt` and `absorb`, in either order. -/
def PartM (Ctx St W SP : Addr) (P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  Env Ctx St W SP s ∧ DataW4 Ctx St W SP s D n ∧ s.mem.readW (W + BitVec.ofNat 64 200) 64 = D ∧
    s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n ∧
    s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀

/-- `PartM` with the registers `crypt` and `absorb` start from. -/
abbrev PartI (Ctx St W SP : Addr) (P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop :=
  PartM Ctx St W SP P₀ D n s ∧ s.gpr .r12 = D ∧ s.gpr .rbp = BitVec.ofNat 64 n ∧
    s.gpr .rbx = BitVec.ofNat 64 (P₀ % 16)

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP) {P₀ : Nat} {D : Addr} {n : Nat}
include L

omit L in
theorem PartI.crIn {s : State} (h : PartI Ctx St W SP P₀ D n s) : CrIn Ctx St W SP 0 P₀ D n s :=
  ⟨h.1.1, h.2.1, h.2.2.1, h.2.2.2, h.1.2.1⟩

omit L in
theorem PartI.absIn {s : State} (h : PartI Ctx St W SP P₀ D n s) :
    AbsIn Ctx St W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) (List.replicate P₀ 0) D n s :=
  ⟨h.1.1, h.2.1, h.2.2.1, by rw [List.length_replicate]; exact h.2.2.2, h.1.2.1.dw.ok, rfl⟩

omit L in
theorem PartI.agree {s₁ s₂ : State} (h₁ : PartI Ctx St W SP P₀ D n s₁) (h₂ : PartI Ctx St W SP P₀ D n s₂) :
    ∀ r ∈ absRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [absRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]
  · rw [h₁.1.1.r13, h₂.1.1.r13]
  · rw [h₁.1.1.r14, h₂.1.1.r14]
  · rw [h₁.1.1.r15, h₂.1.1.r15]
  · rw [h₁.1.1.rsp, h₂.1.1.rsp]

omit L in
/-- The data reloaded. -/
theorem partM_load {s : State} (h : PartM Ctx St W SP P₀ D n s) :
    WP isa (.block streamLoad) s (PartI Ctx St W SP P₀ D n) := by
  obtain ⟨he, hd, hdat, hlen, htl⟩ := h
  obtain ⟨s', run, h12, hbp, hbx, hg, hm, hrd, hwr⟩ := load_ok he hdat hlen htl
  rw [toNat_mod16] at hbx
  exact WP.of_runBlock ⟨s', run, ⟨he.keep (load_env hg) hrd hwr, hd.of_eq hrd hwr, hm ▸ hdat, hm ▸ hlen,
    hm ▸ htl⟩, h12, hbp, hbx⟩

/-- After `crypt`. -/
theorem partI_crypt {s : State} (h : PartI Ctx St W SP P₀ D n s) :
    WP isa crypt s (PartM Ctx St W SP P₀ D n) := by
  have hd := h.1.2.1
  refine WP.mono (AesGcm.X86_64.WP.with_rdwr (crypt_ok L (icb := 0) h.crIn)) fun s' ⟨co, hrd, hwr⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    co.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_crFrame L hd h₁ (by omega))
      (by decide)
  exact ⟨co.env, hd.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2⟩

/-- After `absorb`. -/
theorem partI_absorb {s : State} (h : PartI Ctx St W SP P₀ D n s) :
    WP isa (absorb v.callees 16) s (PartM Ctx St W SP P₀ D n) := by
  have hd := h.1.2.1
  refine WP.mono (AesGcm.X86_64.WP.with_rdwr (absorb_ok v L.lay (.inr rfl) h.absIn)) fun s' ⟨ao, hrd, hwr⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 240 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    ao.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_absFrame L h₁ (by omega))
      (by decide)
  exact ⟨ao.env, hd.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.1.2.2.1,
    by rw [sl 208 (by decide) (by decide)]; exact h.1.2.2.2.1, by rw [sl 192 (by decide) (by decide)]; exact h.1.2.2.2.2⟩

/-- `partWith`, in one run. -/
theorem partI_part (enc : Bool) {s : State} (h : PartI Ctx St W SP P₀ D n s) :
    WP isa (partWith enc crypt (absorb v.callees 16)) s (PartM Ctx St W SP P₀ D n) := by
  cases enc
  · simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    exact WP.seq (WP.mono (partI_absorb v L h) fun _ h => WP.seq (WP.mono (partM_load h) fun _ h => partI_crypt L h))
  · simp only [partWith, ↓reduceIte]
    exact WP.seq (WP.mono (partI_crypt L h) fun _ h => WP.seq (WP.mono (partM_load h) fun _ h => partI_absorb v L h))

/-- `crypt` and `absorb` over the same data in both runs. -/
theorem part_rel (enc : Bool) :
    RelCT isa (fun s₁ s₂ => PartI Ctx St W SP P₀ D n s₁ ∧ PartI Ctx St W SP P₀ D n s₂)
      (partWith enc crypt (absorb v.callees 16)) fun _ _ => True := by
  have crR : RelCT isa (fun s₁ s₂ => PartI Ctx St W SP P₀ D n s₁ ∧ PartI Ctx St W SP P₀ D n s₂) crypt
      fun _ _ => True :=
    (crypt_rel L (icb₁ := 0) (icb₂ := 0) (P₁ := P₀) (P₂ := P₀) rfl).mono (fun _ _ h => ⟨h.1.crIn, h.2.crIn⟩)
      fun _ _ h => h
  have abR : RelCT isa (fun s₁ s₂ => PartI Ctx St W SP P₀ D n s₁ ∧ PartI Ctx St W SP P₀ D n s₂)
      (absorb v.callees 16) fun _ _ => True :=
    (RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ => absorb_rel v L.lay (yo := 16) (.inr rfl) (H₁ := H₁)
      (H₂ := H₂) (x₁ := List.replicate P₀ 0) (x₂ := List.replicate P₀ 0) (D := D) (n := n) rfl).mono
      (fun _ _ h => ⟨_, _, h.1.absIn, h.2.absIn⟩) fun _ _ h => h
  have ld := rel_both (rel_envT (F := PartM Ctx St W SP P₀ D n) [] (fun _ h => h.1) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) (fun _ h => partM_load h) (fun _ h => partM_load h)
  cases enc
  · simp only [partWith, Bool.false_eq_true, ↓reduceIte]
    exact RelCT.seq (rel_both abR (fun _ h => partI_absorb v L h) (fun _ h => partI_absorb v L h)) (RelCT.seq ld crR)
  · simp only [partWith, ↓reduceIte]
    exact RelCT.seq (rel_both crR (fun _ h => partI_crypt L h) (fun _ h => partI_crypt L h)) (RelCT.seq ld abR)

end

/-- Before `streamText`: what the entry leaves, in each run. -/
structure TPre (Ctx St W SP : Addr) (aL P₀ : Nat) (D : Addr) (n : Nat) (s : State) : Prop where
  env : Env Ctx St W SP s
  data : DataW4 Ctx St W SP s D n
  rbp : s.gpr .rbp = BitVec.ofNat 64 n
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 aL
  tlen : s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 P₀
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n

section
variable (v : GcmImpl) {Ctx St W SP : Addr} (L : Lay4 Ctx St W SP) {aL P₀ : Nat} {D : Addr} {n : Nat}
include L

/-- The additional data padded if there is no text yet, in one run. -/
theorem tpre_start (hP : P₀ < 2 ^ 64) {s : State} (h : TPre Ctx St W SP aL P₀ D n s) :
    WP isa (.seq (.block [.mov .rax (.mem (at_ .r15 tlenO)), .alu .test .rax (.reg .rax)])
      (.ite .e (firstFlush v.callees) (.block []))) s (PartM Ctx St W SP P₀ D n) := by
  refine WP.mono (start_ok v L (Hyp := False) (a := List.replicate aL 0) (c₀ := List.replicate P₀ 0) h.env rfl
    (by rw [List.length_replicate]; exact hP) rfl (by rw [List.length_replicate]; exact h.alen)
    (by rw [List.length_replicate]; exact h.tlen) (fun f => f.elim)) fun s' ⟨he, hrd, hwr, f, _⟩ => ?_
  have sl : ∀ d, 176 ≤ d → d + 8 ≤ 512 →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    f.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (slot_tFrame L h₁ h₂) (by decide)
  exact ⟨he, h.data.of_eq hrd hwr, by rw [sl 200 (by decide) (by decide)]; exact h.dat,
    by rw [sl 208 (by decide) (by decide)]; exact h.len, by rw [sl 192 (by decide) (by decide)]; exact h.tlen⟩

/-- `streamText` in two runs, with the same data and lengths. -/
theorem streamText_rel (enc : Bool) (hP : P₀ < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => TPre Ctx St W SP aL P₀ D n s₁ ∧ TPre Ctx St W SP aL P₀ D n s₂)
      (streamText v.callees enc) fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂ := by
  have hlt := fun {s} (h : TPre Ctx St W SP aL P₀ D n s) => h.data.dw.ok.lt
  -- Whether there is any data.
  let T1 : State → Prop := fun s => TPre Ctx St W SP aL P₀ D n s ∧ s.zf = some (decide (n = 0))
  have g₁ : ∀ s, TPre Ctx St W SP aL P₀ D n s → WP isa (.block [.alu .test .rbp (.reg .rbp)]) s T1 := fun s h => by
    obtain ⟨s₁, run₁, hz₁, hg₁, hm₁, hrd₁, hwr₁⟩ := test_ok s .rbp h.rbp (hlt h)
    exact WP.of_runBlock ⟨s₁, run₁, ⟨h.env.keep (fun r _ => by rw [hg₁]) hrd₁ hwr₁, h.data.of_eq hrd₁ hwr₁,
      by rw [hg₁]; exact h.rbp, hm₁ ▸ h.alen, hm₁ ▸ h.tlen, hm₁ ▸ h.dat, hm₁ ▸ h.len⟩, hz₁⟩
  have a := rel_both (rel_envT (F := TPre Ctx St W SP aL P₀ D n) [.rbp] (fun _ h => h.env)
    (fun _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rbp, h₂.rbp]) ⟨_, by taint_decide⟩) g₁ g₁
  simp only [streamText]
  refine RelCT.seq a (rel_ite_e (Q := fun s₁ s₂ => Env Ctx St W SP s₁ ∧ Env Ctx St W SP s₂)
    (fun _ _ h => by rw [h.1.2, h.2.2])
    (RelCT.block_nil fun _ _ h => ⟨h.1.1.1.env, h.1.2.1.env⟩) ?_)
  by_cases hn0 : n = 0
  · exact RelCT.of_false fun _ _ h => by have := h.1.1.2.symm.trans h.2; simp [hn0] at this
  -- The additional data padded, then the data.
  have st := rel_both ((start_rel v L.lay (aL := aL) (P := P₀) hP (F := TPre Ctx St W SP aL P₀ D n)
      fun s h => ⟨h.env, h.tlen, h.alen⟩).mono (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h)
    (F₁ := fun s => T1 s) (F₂ := fun s => T1 s) (G₁ := PartM Ctx St W SP P₀ D n) (G₂ := PartM Ctx St W SP P₀ D n)
    (fun s h => tpre_start v L hP h.1) (fun s h => tpre_start v L hP h.1)
  have ld := rel_both (rel_envT (F := PartM Ctx St W SP P₀ D n) [] (fun _ h => h.1) (fun _ _ _ _ _ h => by
    cases h) ⟨_, by taint_decide⟩) (fun _ h => partM_load h) (fun _ h => partM_load h)
  have pt := rel_both (part_rel v L (P₀ := P₀) (D := D) (n := n) enc)
    (fun _ h => partI_part v L enc h) (fun _ h => partI_part v L enc h)
  exact (rel_reassoc2 (RelCT.seq st (RelCT.seq ld pt))).mono (fun _ _ h => ⟨h.1.1, h.1.2⟩)
    fun _ _ h => ⟨h.1.1, h.2.1⟩

end

/-- After the entry, what `streamText` needs. -/
theorem cryptEntry_tpre {s : State} (hp : Proof.Sm4Gcm.streamCryptPre s) :
    WP isa (.block cryptEntry) s (TPre (s.gpr .rdi) (s.gpr .rsi) (stackArg s 0) (s.gpr .rsp) (s.gpr .rdx).toNat
      (s.gpr .rcx).toNat (s.gpr .r8) (s.gpr .r9).toNat) := by
  have C := CryptCtx.of hp
  refine WP.mono (cryptEntry_ok rfl rfl rfl rfl rfl rfl C.perm C.args) fun s₁ E => ?_
  exact ⟨E.env, C.data.of_eq E.rd E.wr, E.rbp, by rw [E.alen, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [E.tlen, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len⟩

theorem stream_pub {s₀ s₀' : State} (hq : Proof.Sm4Gcm.streamCryptPub s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- `stream_encrypt` (`enc`) or `stream_decrypt` from two states with the
same public values. -/
theorem stream_rel (v : GcmImpl) (enc : Bool) {s₀ s₀' : State}
    (hp : Proof.Sm4Gcm.streamCryptPre s₀) (hp' : Proof.Sm4Gcm.streamCryptPre s₀')
    (hq : Proof.Sm4Gcm.streamCryptPub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
      (.seq (.block cryptEntry) (.seq (streamText v.callees enc) (.block restore))) fun _ _ => True := by
  have L := (CryptCtx.of hp).lay
  have hE₂ := cryptEntry_tpre hp'
  have hq' := hq
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈⟩ := hq'
  simp only [Proof.Sm4Gcm.arg] at q₈
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← q₈] at hE₂
  have hE₁ := cryptEntry_tpre hp
  rw [cryptEntry, List.append_assoc] at hE₁ hE₂
  rw [cryptEntry, List.append_assoc]
  exact fn_rel₂ (Ctx := s₀.gpr .rdi) (St := s₀.gpr .rsi) (W := stackArg s₀ 0) (SP := s₀.gpr .rsp)
    [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (k := 8) (by simp) ⟨_, by taint_decide⟩ (stream_pub hq) q₈
    (CryptCtx.of hp).args (CryptCtx.of hp').args ⟨_, by taint_decide⟩ hE₁ hE₂
    ((streamText_rel v L enc (s₀.gpr .rcx).isLt).mono (fun _ _ h => ⟨h.2.1, h.2.2⟩) fun _ _ h => h)

theorem streamEncrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.streamEncryptX86_64.pre Proof.Sm4Gcm.streamEncryptX86_64.pub
      (streamEncrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v true hp hp' hq

theorem streamDecrypt_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.streamDecryptX86_64.pre Proof.Sm4Gcm.streamDecryptX86_64.pub
      (streamDecrypt v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => stream_rel v false hp hp' hq

end VG.Proof.Sm4Gcm.X86_64
