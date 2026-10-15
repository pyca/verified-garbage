module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenI
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.OpenI
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenCT
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CTI
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.CTI
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FinTagCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on x86-64: `open`'s body calling the function given the block index, in two runs

Untrusted: everything here is checked by Lean. As `openOkW_rel`, for the
body of `FastOpen.runI`: both runs push the same index, then go through the
whole blocks (`oneBlocksDI_rel`), the tag and the comparison a word lower
with the same public data (`preI_rel`); the comparison is whether
`openResult` succeeds (`preI_ok`), the same in both runs; then both decrypt
the rest or encrypt the whole blocks again (`openPost_rel`), and pop the
index (`openOkWI_rel`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph ctrIndex)
open Gcm.X86_64.Stitch (CtxMode)

/-- After the push of the index: `OneS` a word below `SP`, the tag length, and
the received tag's address in the argument at `SP + 24`. -/
abbrev InI (M : CtxMode) (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (T : Option Nat)
    (t : Nat) (Tp : Addr) (s : State) : Prop :=
  OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al D n T s ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s

/-- `a; (b; (c; (d; (e; (f; g)))))`, related as `(a; (b; (c; (d; (e; f))))); g`. -/
theorem rel_reassoc6 {P Q : State → State → Prop} {a b c d e f g : Prog isa}
    (hr : RelCT isa P (.seq (.seq a (.seq b (.seq c (.seq d (.seq e f))))) g) Q) :
    RelCT isa P (.seq a (.seq b (.seq c (.seq d (.seq e (.seq f g)))))) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq a₁ e₁ => cases e₁ with | seq b₁ e₁ => cases e₁ with | seq c₁ e₁ => cases e₁ with | seq d₁ e₁ =>
  cases e₁ with | seq x₁ e₁ => cases e₁ with | seq f₁ g₁ =>
  cases e₂ with | seq a₂ e₂ => cases e₂ with | seq b₂ e₂ => cases e₂ with | seq c₂ e₂ => cases e₂ with | seq d₂ e₂ =>
  cases e₂ with | seq x₂ e₂ => cases e₂ with | seq f₂ g₂ =>
  obtain ⟨ht, hq⟩ := hr _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ (.seq c₁ (.seq d₁ (.seq x₁ f₁))))) g₁)
    (.seq (.seq a₂ (.seq b₂ (.seq c₂ (.seq d₂ (.seq x₂ f₂))))) g₂)
  simp only [List.append_assoc] at ht
  exact ⟨ht, hq⟩

section
variable {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W (SP - BitVec.ofNat 64 8)) {M : CtxMode}
include L

/-- `oneBlocks` given the block index keeps the tag length and the received
tag's address. -/
theorem blocksTlI_ok (F : DecFnI M) {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {Tp : Addr} {s : State}
    (t_c : (below (SP - BitVec.ofNat 64 8) 24).Disjoint ⟨Ctx, 256⟩)
    (t_w : (below (SP - BitVec.ofNat 64 8) 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below (SP - BitVec.ofNat 64 8) 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ (SP - BitVec.ofNat 64 8).toNat)
    (a_w : (⟨SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (a_d : (⟨SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, n⟩)
    (w_sp : (SP - BitVec.ofNat 64 8).toNat + 8 ≤ 2 ^ 64)
    (oA : OutWDS W D (SP - BitVec.ofNat 64 8) n ⟨SP + BitVec.ofNat 64 24, 8⟩)
    (h : InI M Ctx W SP R A al D n none t Tp s ∧ IdxAt W (SP - BitVec.ofNat 64 8) s) :
    WP isa (oneBlocks F.fn) s
      (InI M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) t Tp) :=
  WP.mono (oneBlocksDI_ok L F ⟨h.1.1.env, h.1.1.rounds, h.1.1.dat, h.1.1.len, h.1.1.dD, t_c, t_w, t_d, sp24,
      h.1.1.ext⟩ h.2.hidx a_w a_d h.2.r w_sp) fun _ ⟨P, _⟩ =>
    ⟨ObPost.oneS L t_w h.1.1 P, by
      rw [(obFrame_B P.frame).readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrameB L h.1.1.dD.ok.w t_w (.inr ⟨by decide, by decide⟩)) (by decide), h.1.2.1], by
      rw [ArgT, (obFrame_B P.frame).readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
        oA.oneFrameB (by decide), h.1.2.2.1], by rw [P.rd, P.wr]; exact h.1.2.2.2⟩

/-- The tag's code `tg` keeps `OneS`, the tag length and the received tag's
address. -/
theorem tagTlI_ok {tg : Prog isa} (htg : TagOk M tg) {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n N t : Nat}
    {Tp : Addr} {s : State} (hN : N < 2 ^ 64) (hn16 : n < 16)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (oA : OutWS W (SP - BitVec.ofNat 64 8) ⟨SP + BitVec.ofNat 64 24, 8⟩)
    (h : InI M Ctx W SP R A al D n (some N) t Tp s) :
    WP isa tg s (InI M Ctx W SP R A al D n (some N) t Tp) :=
  WP.mono (htg L (x := []) (by decide) h.1.env rfl h.1.rounds h.1.dat h.1.len hn16 (h.1.tlen N rfl) hN
    h.1.alen h.1.dD.ok hDW h.1.dD.ctx h.1.ext) fun _ ⟨he, f, hrd, hwr, _⟩ => by
    have f' := wFrame_one (D := D) (n := n) (.inr rfl) f
    exact ⟨h.1.frame L he hrd hwr hDW f', by
      rw [f'.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _)
        (kept_oneFrame L hDW (.inr ⟨by decide, by decide⟩)) (by decide), h.2.1], by
      rw [ArgT, f.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
        (oA.tagFrame (o := 112) (by decide)) (by decide), h.2.2.1], by rw [hrd, hwr]; exact h.2.2.2⟩

omit L in
/-- The tag length loaded into `rbx`, and the received tag's address, 32 bytes
above `rsp`, into `rsi`. -/
theorem loadTlI_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n t : Nat} {T : Option Nat} {Tp : Addr} {s : State}
    (h : InI M Ctx W SP R A al D n T t Tp s) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 32))]) s fun s' =>
      OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al D n T s' ∧ s'.gpr .rbx = BitVec.ofNat 64 t ∧
        s'.gpr .rsi = Tp := by
  have r₁ := h.1.env.perm.wR (show 224 + 8 ≤ 2560 by decide)
  have r₂ : InRegions (s.rd ++ s.wr) (SP - BitVec.ofNat 64 8 + BitVec.ofNat 64 32) 8 := by
    rw [e32]; exact h.2.2.2
  have hT : s.mem.readW (SP - BitVec.ofNat 64 8 + BitVec.ofNat 64 32) 64 = Tp := by rw [e32]; exact h.2.2.1
  obtain ⟨s₁, run₁, hbx, hsi, hg, hm, hrd, hwr⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 tlO)),
      .mov .rsi (.mem (at_ .rsp 32))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp ∧
      (∀ r, r ≠ .rbx → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h.1.env.r15, h.1.env.rsp, r₁, r₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h.2.1]
    · simp [gpr_setReg, h.1.env.rsp, hT]
    · intro r a b; simp [gpr_setReg, a, b]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.1.keep (fun r hr => ?_) hm hrd hwr, hbx, hsi⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- After the push, up to the comparison, in two runs. -/
theorem preI_rel (F : DecFnI M) {tg : Prog isa} (htr : TagRel M tg) (htg : TagOk M tg) {R : Nat} {A : Addr}
    {al : Nat} {D : Addr} {n t : Nat} {Tp : Addr}
    (t_c : (below (SP - BitVec.ofNat 64 8) 24).Disjoint ⟨Ctx, 256⟩)
    (t_w : (below (SP - BitVec.ofNat 64 8) 24).Disjoint ⟨W, 2560⟩)
    (t_d : (below (SP - BitVec.ofNat 64 8) 24).Disjoint ⟨D, n⟩) (sp24 : 24 ≤ (SP - BitVec.ofNat 64 8).toNat)
    (a_w : (⟨SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (a_d : (⟨SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 8, 16⟩ : Region).Disjoint ⟨D, n⟩)
    (w_sp : (SP - BitVec.ofNat 64 8).toNat + 8 ≤ 2 ^ 64)
    (oA : OutWDS W D (SP - BitVec.ofNat 64 8) n ⟨SP + BitVec.ofNat 64 24, 8⟩)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) (hlt : n < 2 ^ 64) :
    RelCT isa (fun s₁ s₂ => (InI M Ctx W SP R A al D n none t Tp s₁ ∧ IdxAt W (SP - BitVec.ofNat 64 8) s₁) ∧
        (InI M Ctx W SP R A al D n none t Tp s₂ ∧ IdxAt W (SP - BitVec.ofNat 64 8) s₂))
      (.seq (oneBlocks F.fn) (.seq tg
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 32))])
        (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)]))))))
      fun _ _ => True := by
  have hDW' := hDW.sub_left (Offset.sub_base D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega))
  have bl := rel_wp ((oneBlocksDI_rel L a_w F (R := R) (A := A) (al := al) (T := none) t_c t_w t_d sp24 a_d
      w_sp).mono
      (P' := fun (s₁ s₂ : State) =>
        (InI M Ctx W SP R A al D n none t Tp s₁ ∧ IdxAt W (SP - BitVec.ofNat 64 8) s₁) ∧
        (InI M Ctx W SP R A al D n none t Tp s₂ ∧ IdxAt W (SP - BitVec.ofNat 64 8) s₂))
      (fun _ _ h => ⟨⟨h.1.1.1, h.2.1.1⟩, h.1.2, h.2.2⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => blocksTlI_ok L F t_c t_w t_d sp24 a_w a_d w_sp oA h)
    (fun _ h => blocksTlI_ok L F t_c t_w t_d sp24 a_w a_d w_sp oA h)
  have b := rel_wp ((htr L hDW' (N := n)).mono (P' := fun (s₁ s₂ : State) =>
        InI M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) t Tp s₁ ∧
        InI M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) t Tp s₂)
      (fun _ _ h => ⟨h.1.1, h.2.1⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => tagTlI_ok L htg hlt (by omega) hDW' oA.ws h) (fun _ h => tagTlI_ok L htg hlt (by omega) hDW' oA.ws h)
  have c := rel_wp (rel_taint (P := fun (s₁ s₂ : State) => True ∧
      InI M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) t Tp s₁ ∧
      InI M Ctx W SP R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) (some n) t Tp s₂)
      [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env ⟨h.2.1.1, h.2.2.1⟩) ⟨_, by taint_decide⟩) (fun _ _ h => h.2)
    (fun _ h => loadTlI_ok h) (fun _ h => loadTlI_ok h)
  have d := rel_taint (P := fun (s₁ s₂ : State) => True ∧
      (OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
        (some n) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 t ∧ s₁.gpr .rsi = Tp) ∧
      (OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al (D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16))
        (some n) s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 t ∧ s₂.gpr .rsi = Tp))
    (c := .seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))
    ([.rbx, .rsi] ++ [.r13, .r14, .r15, .rsp])
    (fun _ _ h => EnvAgree.regs ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩) ⟨_, by taint_decide⟩
  exact RelCT.seq (bl.mono (fun _ _ h => h) fun _ _ h => h.2) (RelCT.seq b (RelCT.seq c d))

end

end VG.Proof.AesGcm.X86_64
