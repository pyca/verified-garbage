module

public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OneCT
public import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Open
import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.OneCT
meta import VerifiedGarbage.Proof.Sm4Gcm.X86_64.Open
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Cmp
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Arith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Impl.Sm4Gcm.X86_64
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.TCB.X86_64.State

/-!
# SM4-GCM on x86-64: `vg_sm4_gcm_open` is constant time

Untrusted: everything here is checked by Lean. As AES-GCM's
(`Proof/AesGcm/X86_64/OpenCT.lean`): the first branch is on the tag length
(public); then both runs go through `oneAad` and `oneTag` with the same
public data, as in `seal`, and copy and compare the tags without a branch
(the taint analysis). The second branch is on the comparison, which `open`
may leak: correctness says it is whether `openResult` succeeds
(`openPre_ok`), the same in both runs by `pub`; then both runs decrypt the
data (`oneCrypt`) or leave it.
-/

@[expose] public section

namespace VG.Proof.Sm4Gcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Sm4Gcm.X86_64 VG.WriteBytes
open VG.Impl.AesGcm.X86_64 (at_ imm oneAad tagLenOk recv cmp uO tlO auxO restore)
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ghashFrom ghash blocks ofBytes toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Proof.Gcm (lensBlock padded)
open VG.Proof.AesGcm.X86_64 (GcmImpl Lay Env rel_regs rel_taint rel_wp rel_ite_e rel_env rel_reassoc_inner
  EnvAgree EnvAgree.regs env_agree fn_rel₂ ct_of_rel tagLenOk_ok bytesAt_frame padded_eq length_bytesAt
  leak_bool)

/-- `a; (b; (c; (d; (e; (f; g)))))`, related as `(a; (b; (c; (d; (e; f))))); g`. -/
theorem rel_reassoc6 {P Q : State → State → Prop} {a b c d e f g : Prog isa}
    (hr : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d (.seq e f))))) g) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f g)))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with
    | seq d₁ e₁ => cases e₁ with | seq x₁ e₁ => cases e₁ with | seq f₁ g₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with
    | seq d₂ e₂ => cases e₂ with | seq x₂ e₂ => cases e₂ with | seq f₂ g₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq x₁ f₁))))) g₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq x₂ f₂))))) g₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

/-- What `open`'s entry leaves, for a tag length `t`. -/
abbrev OpenIn (s₀ : State) (Ctx W SP A D : Addr) (n t : Nat) (s : State) : Prop :=
  OneEntry s₀ Ctx W SP A D n s ∧ s.gpr .rbx = BitVec.ofNat 64 t ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t

/-- The address `T` of the received tag, in the argument at `[SP + 16]`. -/
abbrev ArgT (SP T : Addr) (s : State) : Prop := s.mem.readW (SP + BitVec.ofNat 64 16) 64 = T

/-- `ArgT`, and the argument may be read. -/
abbrev ArgR (SP T : Addr) (s : State) : Prop :=
  ArgT SP T s ∧ InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 16) 8

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- `oneAad` keeps `OneS`, the tag length, and the address of the received tag. -/
theorem aadTl_ok {s₀ s : State} {Np A D T : Addr} {nl al n t : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al)
    (hT : ArgT SP T s₀) (h : OpenIn s₀ Ctx W SP A D n t s) :
    WP isa (oneAad v.callees) s fun s' => OneS Ctx W SP A al D n s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP T s' :=
  WP.mono (oneMid_ok v C h.1 hNp hnl hal) fun _ Mi => by
    have La := L.lay
    refine ⟨(h.1.aadPre C hNp hnl hal).1.frame L Mi.env (Mi.rd.trans h.1.rd.symm) (Mi.wr.trans h.1.wr.symm)
      C.dE (wFrame_one (.inl rfl) (wFrame_cons Mi.fr)), ?_, ?_, by rw [Mi.rd, Mi.wr]; exact C.args 1 (by decide)⟩
    · rw [Mi.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact La.w_w (.inr (by decide)) (by decide) (by decide)
        · exact La.w_w (.inr (by decide)) (by decide) (by decide)
        · exact La.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), h.2.2]
    · rw [ArgT, Mi.frame.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact arg16_disj (by decide) C.dA C.dAD (.inl fun _ h => h)
        · exact arg16_disj (by decide) C.dA C.dAD (.inr (.inr fun _ h => h))) (by decide), hT]

/-- `oneTag 112` keeps `OneS` and the tag length. -/
theorem tagTl_ok {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {Tp : Addr} {s : State} (hN : n < 2 ^ 64)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (oA : OutWS W SP ⟨SP + BitVec.ofNat 64 16, 8⟩)
    (h : OneS Ctx W SP A al D n s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s) :
    WP isa (oneTag v.callees uO) s fun s' => OneS Ctx W SP A al D n s' ∧
      s'.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s' :=
  WP.mono (oneTag_ok v L (o := 112) (.inr rfl) (x := []) (by decide) h.1.env rfl h.1.dat h.1.len h.1.tlen hN
    h.1.alen h.1.dD.dw.ok hDW h.1.dD.dw.ctx) fun _ ⟨he, f, hrd, hwr, _⟩ => by
    have f' := wFrame_one (D := D) (n := n) (.inr rfl) f
    exact ⟨h.1.frame L he hrd hwr hDW f', by
      rw [f'.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrame L hDW (.inr ⟨by decide, by decide⟩)) (by decide), h.2.1], by
      rw [ArgT, f.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _)
        (oA.tagFrame (o := 112) (by decide)) (by decide), h.2.2.1], by rw [hrd, hwr]; exact h.2.2.2⟩

omit L in
/-- The tag length loaded into `rbx`, and the address of the received tag into `rsi`. -/
theorem loadTl_ok {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {Tp : Addr} {s : State}
    (h : OneS Ctx W SP A al D n s ∧ s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))]) s fun s' =>
      OneS Ctx W SP A al D n s' ∧ s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.gpr .rsi = Tp := by
  have r₁ := h.1.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have r₂ := h.2.2.2
  obtain ⟨s₁, run₁, hbx, hsi, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 16))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.env.r15, h.1.env.rsp, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.1]
    · simp [gpr_setReg, h.2.2.1]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hm hrd hwr, hbx, hsi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

omit L in
/-- The result loaded from `W + 216`. -/
theorem loadAux_ok {s : State} (h : Env Ctx (W + BitVec.ofNat 64 16) W SP s) :
    WP isa (.block [.mov .rax (.mem (at_ .r15 auxO))]) s (Env Ctx (W + BitVec.ofNat 64 16) W SP) := by
  have r₁ := h.perm.wR (show 216 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, hg, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rax (.mem (at_ .r15 auxO))] s = some s₁ ∧
      (∀ r, r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.r15, r₁], ?_, ?_, ?_⟩
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hrd hwr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide)

end

/-- From the entry, for an allowed tag length: ZF says whether
`openResult` fails. -/
theorem openPre_ok (v : GcmImpl) {s s₁ : State} {Ctx W SP Np A D Tp : Addr} {nl al n t : Nat}
    (C : OneCtx s 4 Ctx W SP Np A D nl al n) (h : OpenIn s Ctx W SP A D n t s₁)
    (hNp : s.gpr .rsi = Np) (hnl : (s.gpr .rdx).toNat = nl) (hal : (s.gpr .r8).toNat = al)
    (hok : Spec.Gcm.tagLenOk t = true) (hT : ArgT SP Tp s)
    (hTr : Covers [⟨Tp, t⟩] (s.rd ++ s.wr)) (oT : OutWDS W D SP n ⟨Tp, t⟩) :
    WP isa (.seq (oneAad v.callees) (.seq (oneTag v.callees uO)
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
      (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))))) s₁
      fun s' => OneS Ctx W SP A al D n s' ∧
        s'.zf = some (!(Spec.Gcm.openResult (ctxCiph s.mem Ctx) (ctxH s.mem Ctx) t
          (bytesAt s.mem Np nl) (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem Tp t)).isSome) := by
  have L := C.lay
  have La := L.lay
  have E := h.1
  have hS := (E.aadPre C hNp hnl hal).1
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  have hlt := C.data.dw.ok.lt
  refine WP.seq (WP.mono (oneMid_ok v C E hNp hnl hal) fun s₃ Mi => ?_)
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [Mi.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [Mi.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact La.w_w (.inr (by decide)) (by decide) (by decide)
      · exact La.w_w (.inr (by decide)) (by decide) (by decide)
      · exact La.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.kw.sub_right (Lay.wSub (by decide))).symm) (by decide), h.2.2]
  have hd₃ := C.data.of_eq Mi.rd Mi.wr
  have hS₃ : OneS Ctx W SP A al D n s₃ := hS.frame L Mi.env (Mi.rd.trans E.rd.symm) (Mi.wr.trans E.wr.symm) C.dE
    (wFrame_one (.inl rfl) (wFrame_cons Mi.fr))
  have oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 16, 8⟩ := fun _ hr => arg16_disj (by decide) C.dA C.dAD hr
  have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 16) 64 = Tp := by
    rw [Mi.frame.readW (r := ⟨SP + BitVec.ofNat 64 16, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oA _ (.inl fun _ h => h)
      · exact oA _ (.inr (.inr fun _ h => h))) (by decide), hT]
  have hx16 : (bytesAt s.mem A al ++ Spec.Gcm.zeros (Spec.Gcm.padLen (bytesAt s.mem A al).length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.mono (openCheck_ok v L (al := al) hx16 Mi.env Mi.hH Mi.dat Mi.len Mi.tlen hlt hal₃ htl₃
    hb.1 hb.2 hd₃.dw.ok C.dE C.data.dw.ctx Mi.abs Mi.j0 hTa₃ (by rw [Mi.rd, Mi.wr]; exact C.args 1 (by decide))
    (by rw [Mi.rd, Mi.wr]; exact hTr) oT.ws oA.ws) fun s' O => ⟨hS₃.frame L O.env O.rd O.wr C.dE
      (wFrame_one (.inr rfl) O.frame), ?_⟩
  -- From the entry to `s₃`.
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP stkN).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP stkN], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hc₃ : ciphOf s₃.mem Ctx = ctxCiph s.mem Ctx := ciph_frame Mi.frame (fun r hr => dM _ _ La.cw' L.kc r hr)
  have hp₃ : bytesAt s₃.mem D n = bytesAt s.mem D n :=
    bytesAt_frame Mi.frame (dM _ _ C.dE C.data.stk) (by omega)
  have hw₃ : bytesAt s₃.mem Tp t = bytesAt s.mem Tp t := bytesAt_frame Mi.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact oT _ (.inl fun _ h => h)
    · exact oT _ (.inr (.inr fun _ h => h))) (by omega)
  have hz := O.zf
  rw [padded_eq, hc₃, hp₃, hw₃] at hz
  rw [hz]
  simp only [Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq, length_bytesAt]
  split <;> simp

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay4 Ctx (W + BitVec.ofNat 64 16) W SP)
include L

/-- From the entry to the comparison, for an allowed tag length. -/
theorem openPre_rel {s₀ s₀' : State} {Np A D Tp : Addr} {nl al n t : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al)
    (hNp' : s₀'.gpr .rsi = Np) (hnl' : (s₀'.gpr .rdx).toNat = nl) (hal' : (s₀'.gpr .r8).toNat = al)
    (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀') :
    RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq (oneAad v.callees) (.seq (oneTag v.callees uO)
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
        (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))))
      fun _ _ => True := by
  have hDW := C.dE
  have hlt := C.data.dw.ok.lt
  have oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 16, 8⟩ := fun _ hr => arg16_disj (by decide) C.dA C.dAD hr
  have a := rel_wp ((oneAad_rel v L hDW (Np := Np) (nl := nl)).mono
      (P' := fun (s₁ s₂ : State) => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (fun _ _ h => ⟨h.1.1.aadPre C hNp hnl hal, h.2.1.aadPre C' hNp' hnl' hal'⟩) fun _ _ _ => trivial)
    (fun _ _ h => h) (fun _ h => aadTl_ok v L C hNp hnl hal hT h) (fun _ h => aadTl_ok v L C' hNp' hnl' hal' hT' h)
  have b := rel_wp ((oneTag_rel v L (.inr rfl) hDW).mono (P' := fun (s₁ s₂ : State) =>
        (OneS Ctx W SP A al D n s₁ ∧ s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s₁) ∧
        (OneS Ctx W SP A al D n s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s₂))
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => tagTl_ok v L hlt hDW oA.ws h) (fun _ h => tagTl_ok v L hlt hDW oA.ws h)
  have c := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP A al D n s₁ ∧ s₁.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s₁) ∧
      (OneS Ctx W SP A al D n s₂ ∧ s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s₂))
      [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env ⟨h.2.1.1, h.2.2.1⟩) ⟨_, by taint_decide⟩) (fun _ _ h => h.2)
    (fun _ h => loadTl_ok h) (fun _ h => loadTl_ok h)
  have d := rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP A al D n s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp) ∧
      (OneS Ctx W SP A al D n s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t ∧ s₂.gpr .rsi = Tp))
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))
    ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq (a.mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩)
    (RelCT.seq (b.mono (fun _ _ h => h) fun _ _ h => ⟨trivial, h.2⟩) (RelCT.seq c d))

omit v in
/-- After the comparison: the data decrypted if the tags match, and the
result loaded. -/
theorem openPost_rel {A : Addr} {al : Nat} {D : Addr} {n : Nat} {b₁ b₂ : Bool} (hb : b₁ = b₂)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => True ∧ (OneS Ctx W SP A al D n s₁ ∧ s₁.zf = some b₁) ∧
        (OneS Ctx W SP A al D n s₂ ∧ s₂.zf = some b₂))
      (.seq (.ite .e (.block []) oneCrypt) (.block [.mov .rax (.mem (at_ .r15 auxO))]))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have e := (oneCrypt_rel L (A := A) (al := al) hDW).mono
    (P' := fun (s₁ s₂ : State) => (True ∧ (OneS Ctx W SP A al D n s₁ ∧ s₁.zf = some b₁) ∧
        (OneS Ctx W SP A al D n s₂ ∧ s₂.zf = some b₂)) ∧ s₁.zf = some false)
    (Q' := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂)
    (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => ⟨h.1.env, h.2.env⟩
  have f := rel_wp (rel_taint (P := fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧
      Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => env_agree h.1 h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h)
    (fun _ h => loadAux_ok h) (fun _ h => loadAux_ok h)
  exact RelCT.seq (rel_ite_e (fun _ _ h => by rw [h.2.1.2, h.2.2.2, hb])
    (RelCT.block_nil fun _ _ h => ⟨h.1.2.1.1.env, h.1.2.2.1.env⟩) e)
    (f.mono (fun _ _ h => h) fun _ _ h => h.2)

/-- After the entry: the tag length checked, then, if it is allowed, `mid`. -/
theorem openBody_relOf {s₀ s₀' : State} {A D : Addr} {n t : Nat} {mid : Prog isa} (ht : t < 2 ^ 64)
    (hrel : Spec.Gcm.tagLenOk t = true →
      RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂) mid
        fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂) :
    RelCT isa (fun s₁ s₂ => True ∧ OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq tagLenOk (.ite .e (.block [.mov32 .rax (imm 0)]) mid))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have hK : ∀ {s₀ s : State}, OpenIn s₀ Ctx W SP A D n t s → WP isa tagLenOk s fun s' =>
      OpenIn s₀ Ctx W SP A D n t s' ∧ s'.zf = some (!Spec.Gcm.tagLenOk t) := fun h =>
    WP.mono (tagLenOk_ok _ h.2.1 ht) fun _ ⟨hz, k⟩ =>
      ⟨⟨h.1.keep L (fun r hr => k.gpr r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) k.rd k.wr
          (by rw [k.mem]; exact Frame.refl _ _), by rw [k.gpr _ (by decide), h.2.1], by rw [k.mem]; exact h.2.2⟩, hz⟩
  have a := rel_wp (rel_regs (P := fun (s₁ s₂ : State) => True ∧ OpenIn s₀ Ctx W SP A D n t s₁ ∧
      OpenIn s₀' Ctx W SP A D n t s₂) ([.rbx] ++ [.r13, .r14, .r15, .rsp]) [] true
      (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2.1, h.2.2.2.1]⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => h.2) (fun _ h => hK h) (fun _ h => hK h)
  refine RelCT.seq a (rel_ite_e (fun _ _ h => (h.1.2 rfl).2.1) ?_ ?_)
  · -- A length `tagLenOk` does not allow.
    exact (rel_env (by decide) (fun _ _ h => ⟨h.1.2.1.1.1.env, h.1.2.2.1.1.env⟩)
      (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => env_agree h.1.2.1.1.1.env h.1.2.2.1.1.env)
        ⟨_, by taint_decide⟩)).mono (fun _ _ h => h) fun _ _ h => h.2
  · by_cases hok : Spec.Gcm.tagLenOk t = true
    swap
    · exact RelCT.of_false fun _ _ h => by have := h.1.2.1.2.symm.trans h.2; simp [hok] at this
    exact (hrel hok).mono (fun _ _ h => ⟨h.1.2.1.1, h.1.2.2.1⟩) fun _ _ h => h

end

/-- For an allowed tag length: `oneAad`, the tags compared, and the data
decrypted if they match. -/
theorem openOk_rel (v : GcmImpl) {s₀ s₀' : State} {Ctx W SP Np A D Tp : Addr} {nl al n t : Nat}
    (C : OneCtx s₀ 4 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 4 Ctx W SP Np A D nl al n)
    (hNp : s₀.gpr .rsi = Np) (hnl : (s₀.gpr .rdx).toNat = nl) (hal : (s₀.gpr .r8).toNat = al)
    (hNp' : s₀'.gpr .rsi = Np) (hnl' : (s₀'.gpr .rdx).toNat = nl) (hal' : (s₀'.gpr .r8).toNat = al)
    (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀')
    (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr)) (hTr' : Covers [⟨Tp, t⟩] (s₀'.rd ++ s₀'.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩)
    (hres : (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem D n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem Tp t)).isSome)
    (hok : Spec.Gcm.tagLenOk t = true) :
    RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq (oneAad v.callees)
        (.seq (oneTag v.callees uO)
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 16))])
        (.seq recv
        (.seq (cmp uO)
        (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
        (.seq (.ite .e (.block []) oneCrypt)
          (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have L := C.lay
  refine rel_reassoc6 (RelCT.seq ?_ (openPost_rel L (A := A) (al := al) (congrArg (!·) hres) C.dE))
  exact rel_wp ((openPre_rel v L C C' hNp hnl hal hNp' hnl' hal' hT hT').mono
      (fun _ _ h => h) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => openPre_ok v C h hNp hnl hal hok hT hTr oT)
    (fun _ h => openPre_ok v C' h hNp' hnl' hal' hok hT' hTr' oT)

theorem open_rel (v : GcmImpl) {s₀ s₀' : State}
    (hp : Proof.Sm4Gcm.openX86_64.pre s₀) (hp' : Proof.Sm4Gcm.openX86_64.pre s₀')
    (hq : Proof.Sm4Gcm.openX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callees) fun _ _ => True := by
  obtain ⟨C, hTr, d_td, d_tw, t_t⟩ := OneCtx.ofOpen hp
  obtain ⟨C', hTr', -, -, -⟩ := OneCtx.ofOpen hp'
  have L := C.lay
  obtain ⟨⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩, hres⟩ := hq
  simp only [Proof.Sm4Gcm.openLeak, Proof.Sm4Gcm.arg] at hres
  have hres := leak_bool hres
  have a₀ := qa 0 (by decide); have a₁ := qa 1 (by decide); have a₂ := qa 2 (by decide)
  have a₃ := qa 3 (by decide)
  simp only [Proof.Sm4Gcm.arg] at a₀ a₁ a₂ a₃
  have ha₃ := C.args 3 (by decide); have ha₃' := C'.args 3 (by decide)
  have hw32 : s₀.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 =
      s₀'.mem.readW (s₀'.gpr .rsp + BitVec.ofNat 64 32) 64 := a₃
  have hT₁ : ArgT (s₀.gpr .rsp) (stackArg s₀ 1) s₀ := rfl
  have hT₂ : ArgT (s₀.gpr .rsp) (stackArg s₀ 1) s₀' := by rw [ArgT, q₇, a₁]; rfl
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← q₇, ← a₀, ← a₃] at C'
  rw [← a₁, ← a₂] at hTr'
  rw [← q₁, ← q₂, ← q₃, ← q₄, ← q₅, ← q₆, ← a₀, ← a₁, ← a₂] at hres
  generalize ht : (stackArg s₀ 2).toNat = t at hres hTr hTr' d_td d_tw t_t
  have oT : OutWDS (stackArg s₀ 3) (s₀.gpr .r9) (s₀.gpr .rsp) (stackArg s₀ 0).toNat ⟨stackArg s₀ 1, t⟩ :=
    fun r hr => hr.elim d_tw.sub_right fun h => h.elim d_td.sub_right t_t.symm.sub_right
  have hE : ∀ {s : State} (C : OneCtx s 4 (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .rsi) (s₀.gpr .rcx)
      (s₀.gpr .r9) (s₀.gpr .rdx).toNat (s₀.gpr .r8).toNat (stackArg s₀ 0).toNat),
      s.gpr .rdi = s₀.gpr .rdi → s.gpr .rsp = s₀.gpr .rsp → s.gpr .rcx = s₀.gpr .rcx →
      s.gpr .r9 = s₀.gpr .r9 → (stackArg s 0).toNat = (stackArg s₀ 0).toNat →
      s.mem.readW (s₀.gpr .rsp + BitVec.ofNat 64 32) 64 = stackArg s₀ 3 → stackArg s 2 = stackArg s₀ 2 →
      WP isa (.block (oneEntry 32 ++ [.mov .rbx (.mem (at_ .rsp 24)), .store (at_ .r15 tlO) .rbx])) s
        (OpenIn s (s₀.gpr .rdi) (stackArg s₀ 3) (s₀.gpr .rsp) (s₀.gpr .rcx) (s₀.gpr .r9) (stackArg s₀ 0).toNat t) :=
    fun C h₁ h₂ h₃ h₄ h₅ h₆ h₇ => WP.mono (openEntry_ok C h₁ h₂ h₃ h₄ h₅ h₆) fun _ ⟨E, hbx, htl, _⟩ =>
      ⟨E, by rw [hbx, h₇, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by rw [htl, h₇, ← ht, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hE₁ := hE C rfl rfl rfl rfl rfl rfl rfl
  have hE₂ := hE C' q₁.symm q₇.symm q₄.symm q₆.symm (by rw [a₀]) (by rw [q₇, a₃]; rfl) a₂.symm
  rw [oneEntry] at hE₁ hE₂
  simp only [List.append_assoc] at hE₁ hE₂
  rw [«open», oneEntry]
  simp only [List.append_assoc]
  refine rel_reassoc_inner (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 3 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 3) (SP := s₀.gpr .rsp) (k := 32) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩) hw32 ha₃ ha₃' ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  exact openBody_relOf L (by rw [← ht]; exact (stackArg s₀ 2).isLt) fun hok =>
    openOk_rel v C C' rfl rfl rfl q₂.symm (by rw [← q₃]) (by rw [← q₅]) hT₁ hT₂ hTr hTr' oT hres hok

theorem open_ct (v : GcmImpl) :
    ConstantTime isa Proof.Sm4Gcm.openX86_64.pre Proof.Sm4Gcm.openX86_64.pub («open» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => open_rel v hp hp' hq

end VG.Proof.Sm4Gcm.X86_64
