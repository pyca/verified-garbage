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

section
variable {M : CtxMode} {s : State} {Ctx W SP Np A D T : Addr} {nl al n t R : Nat}
  (C : OneCtx s 5 Ctx W SP Np A D nl al n) (K : Stk32 Ctx W SP A D T M.len al n t)
  (oT : OutWDS W D SP n ⟨T, t⟩)
include C K oT

omit oT in
/-- The facts a word lower, from those at `SP` and `PushedI`, the additional
data's slot kept by the push. -/
theorem inI_of {s₄ : State} (h : OneS M Ctx W SP R A al D n none s₄) {H : Block} {iv a : List Byte}
    (hivl : iv.length = 12) (P : PushedI M s Ctx W SP D T R al n t H iv a (pushed [.rax] s₄)) :
    InI M Ctx W SP R A al D n none t T (pushed [.rax] s₄) ∧ IdxAt W (SP - BitVec.ofNat 64 8) (pushed [.rax] s₄) := by
  have L := C.lay
  have sp := K.sp
  obtain ⟨f₀, -⟩ := Split.push_frame h.env (by omega)
  have b8 : Region.Sub (below SP 8) (below SP 32) := below_sub (by decide) (by decide)
  refine ⟨⟨⟨P.ob.env, P.ob.rounds, ?_, P.alen, P.ob.dat, P.ob.len,
    ⟨by rw [pushed_rd, pushed_wr]; exact Split.covers_ins h.dA.rd, h.dA.lt, h.dA.wrap, h.dA.st, h.dA.w,
      K.a.sub_left (below8_sub32 (by decide))⟩, P.ob.data, fun _ hN => absurd hN (by simp), P.ob.ext⟩, P.tlen,
    P.ta, P.tar⟩, ⟨by rw [P.cb]; exact ctrIndex_first H hivl, by rw [P.idx]; rfl, P.idxR⟩⟩
  rw [f₀.readW (r := ⟨W + BitVec.ofNat 64 232, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((K.w.sub_left b8).sub_right (Lay.wSub (by decide))).symm) (by decide)]
  exact h.aad

/-- After the push, up to the comparison: ZF says whether `openResult` fails. -/
theorem preI_ok (F : DecFnI M) {tg : Prog isa} (htg : TagOk M tg) (hok : Spec.Gcm.tagLenOk t = true) {u : State}
    (P : PushedI M s Ctx W SP D T R al n t (ctxH s.mem Ctx) (bytesAt s.mem Np nl) (bytesAt s.mem A al) u)
    (hI : InI M Ctx W SP R A al D n none t T u ∧ IdxAt W (SP - BitVec.ofNat 64 8) u) :
    WP isa (.seq (oneBlocks F.fn) (.seq tg
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 32))])
      (.seq recv (.seq (cmp uO) (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])))))) u
      fun u' => (OneS M Ctx W (SP - BitVec.ofNat 64 8) R A al (D + BitVec.ofNat 64 (16 * (n / 16)))
          (n - 16 * (n / 16)) (some n) u' ∧ DataW Ctx (W + BitVec.ofNat 64 16) W (SP - BitVec.ofNat 64 8) u' D n) ∧
        u'.zf = some (!(Spec.Gcm.openResult (ctxCiph s.mem Ctx R) (ctxH s.mem Ctx) t
          (bytesAt s.mem Np nl) (bytesAt s.mem D n) (bytesAt s.mem A al) (bytesAt s.mem T t)).isSome) := by
  have L := C.lay
  have hlt := C.data.ok.lt
  have sp := K.sp
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  have kc : (below SP 32).Disjoint ⟨Ctx, 256⟩ := K.c.sub_right (Region.sub_prefix M.ge)
  have L' := lay_pushed32 L kc K.w
  have t_w' : (below (SP - BitVec.ofNat 64 8) 24).Disjoint ⟨W, 2560⟩ := K.w.sub_left (below8_sub32 (by decide))
  have hob := oneBlocksDI_ok L' F P.ob hI.2.hidx (K.w.sub_left (two_sub32 SP)) (K.d.sub_left (two_sub32 SP)) hI.2.r
    (by rw [toNat_sub_ofNat (by omega)]; have := L.ww; omega)
  have oT' : OutWDS W D (SP - BitVec.ofNat 64 8) n ⟨T, t⟩ := fun r hr =>
    hr.elim (fun h => oT r (.inl h)) fun h => h.elim (fun h => oT r (.inr (.inl h)))
      fun h => (K.t.sub_left fun a ha => below8_sub32 (by decide) a (h a ha)).symm
  have oA := C.arg24 (by decide)
  have oA' : OutWDS W D (SP - BitVec.ofNat 64 8) n ⟨SP - BitVec.ofNat 64 8 + BitVec.ofNat 64 32, 8⟩ := by
    rw [e32]
    exact fun r hr => hr.elim (fun h => oA r (.inl h)) fun h => h.elim (fun h => oA r (.inr (.inl h)))
      fun h => (Offset.disjoint_below SP (n := 32) (d := 24) (k := 8) (by decide)).sub_right
        fun a ha => below8_sub32 (by decide) a (h a ha)
  have hS₃ := hI.1.1
  refine WP.mono (openFront_ok L' htg (al := al) P.ob hob P.hH P.alen P.tlen hb.1 hb.2 P.abs P.j0 P.cb
    (by rw [e32]; exact P.ta) (by rw [e32]; exact P.tar) P.tr oT' oA') fun u' F => ?_
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 192) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      u'.mem.readW (W + BitVec.ofNat 64 d) 64 = u.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => F.frame.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
      (kept_oneFrameB L' C.dE t_w' hd) (by decide)
  refine ⟨⟨⟨F.env, F.rounds, by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact hS₃.aad,
    by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact hS₃.alen, F.dat, F.len, hS₃.dA.of_eq F.rd F.wr,
    (hS₃.dD.of_eq F.rd F.wr).drop (by omega), fun N hN => by cases hN; exact F.tlen,
    hS₃.ext.oneB (by omega) F.rd F.wr F.frame⟩, P.ob.data.of_eq F.rd F.wr⟩, ?_⟩
  have hz := F.zf
  rw [P.ciph, P.data, P.tag] at hz
  rw [hz]
  simp only [Spec.Gcm.openResult, hok, ↓reduceIte, Spec.Gcm.decryptWith, Proof.Gcm.fullTag_eq, length_bytesAt]
  split <;> simp

end

/-- What a run holds after the additional data and the index into `rax`. -/
abbrev MovI (M : CtxMode) (s₀ : State) (Ctx W SP Np A D Tp : Addr) (R nl al n t : Nat) (s₄ : State) : Prop :=
  ∃ s₃, ((OneS M Ctx W SP R A al D n none s₃ ∧ s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧
      ArgR SP Tp s₃) ∧ ∃ mE, OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) mE s₃) ∧
    s₄.gpr .rax = BitVec.ofNat 64 2 ∧ (∀ r, r ≠ .rax → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
    s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr

theorem MovI.rsp {M : CtxMode} {s₀ : State} {Ctx W SP Np A D Tp : Addr} {R nl al n t : Nat} {s₄ : State}
    (h : MovI M s₀ Ctx W SP Np A D Tp R nl al n t s₄) : s₄.gpr .rsp = SP := by
  obtain ⟨s₃, ⟨h₃, -⟩, -, hg, -⟩ := h
  rw [hg _ (by decide)]; exact h₃.1.env.rsp

/-- For an allowed tag length and a 12-byte nonce: the additional data
(`aadP`, which leaves what `oneAad` does), then, in a frame pushing the index
of the first counter block, the whole blocks decrypted by `F`, the tag
(`tg`), the tags compared, and the rest decrypted or the whole blocks
encrypted again. -/
theorem openOkWI_rel (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (F : DecFnI M) {aadP tg : Prog isa}
    (htr : TagRel M tg) (htg : TagOk M tg) {s₀ s₀' : State}
    {Ctx W SP Np A D Tp : Addr} {nl al n R t : Nat}
    (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n) (C' : OneCtx s₀' 5 Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀) (X' : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀')
    (hNp : s₀.gpr .rdx = Np) (hnl : (s₀.gpr .rcx).toNat = nl) (hal : (s₀.gpr .r9).toNat = al)
    (hR : (s₀.gpr .rsi).toNat = R)
    (hNp' : s₀'.gpr .rdx = Np) (hnl' : (s₀'.gpr .rcx).toNat = nl) (hal' : (s₀'.gpr .r9).toNat = al)
    (hR' : (s₀'.gpr .rsi).toNat = R) (hT : ArgT SP Tp s₀) (hT' : ArgT SP Tp s₀')
    (hTr : Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr)) (hTr' : Covers [⟨Tp, t⟩] (s₀'.rd ++ s₀'.wr))
    (oT : OutWDS W D SP n ⟨Tp, t⟩)
    (hres : (Spec.Gcm.openResult (ctxCiph s₀.mem Ctx R) (ctxH s₀.mem Ctx) t (bytesAt s₀.mem Np nl)
        (bytesAt s₀.mem D n) (bytesAt s₀.mem A al) (bytesAt s₀.mem Tp t)).isSome =
      (Spec.Gcm.openResult (ctxCiph s₀'.mem Ctx R) (ctxH s₀'.mem Ctx) t (bytesAt s₀'.mem Np nl)
        (bytesAt s₀'.mem D n) (bytesAt s₀'.mem A al) (bytesAt s₀'.mem Tp t)).isSome)
    (hok : Spec.Gcm.tagLenOk t = true) (K : Stk32 Ctx W SP A D Tp M.len al n t) (h12 : nl = 12)
    (har : RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂) aadP
      fun _ _ => True)
    (ha : ∀ s, OpenIn s₀ Ctx W SP A D n t s → WP isa aadP s
      (OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) s.mem))
    (ha' : ∀ s, OpenIn s₀' Ctx W SP A D n t s → WP isa aadP s
      (OneMid s₀' Ctx W SP D n (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al) s.mem)) :
    RelCT isa (fun s₁ s₂ => OpenIn s₀ Ctx W SP A D n t s₁ ∧ OpenIn s₀' Ctx W SP A D n t s₂)
      (.seq aadP (.seq (.block [.mov32 .rax (imm 2)]) (.frame (.push [.rax])
        (.seq (oneBlocks F.fn) (.seq tg
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 32))])
        (.seq recv (.seq (cmp uO) (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
        (.seq (.ite .e (oneUndo (v.withBlk B)) (oneCrypt (v.withBlk B)))
          (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))
        (.pop .r10 1))))
      fun s₁ s₂ => Env Ctx (W + BitVec.ofNat 64 16) W SP s₁ ∧ Env Ctx (W + BitVec.ofNat 64 16) W SP s₂ := by
  have L := C.lay
  have hlt := C.data.ok.lt
  have sp := K.sp
  have hb : t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok
    omega
  have oA := C.arg24 (by decide)
  have kc : (below SP 32).Disjoint ⟨Ctx, 256⟩ := K.c.sub_right (Region.sub_prefix M.ge)
  have L' := lay_pushed32 L kc K.w
  have b8 : ∀ {k : Nat}, k + 8 ≤ 32 → Region.Sub (below (SP - BitVec.ofNat 64 8) k) (below SP 32) :=
    fun hk => below8_sub32 hk
  -- The additional data.
  let G : State → Prop := fun s => OneS M Ctx W SP R A al D n none s ∧
    s.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t ∧ ArgR SP Tp s
  have a₁ := rel_wp har (fun _ _ h => h) (G₁ := G) (G₂ := G)
    (fun _ h => aadTlW_ok L C X hNp hnl hal hR hT h (ha _ h))
    (fun _ h => aadTlW_ok L C' X' hNp' hnl' hal' hR' hT' h (ha' _ h))
  have a := rel_wp a₁ (fun _ _ h => h)
    (G₁ := fun s => ∃ mE, OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) mE s)
    (G₂ := fun s => ∃ mE, OneMid s₀' Ctx W SP D n (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al)
      mE s)
    (fun s h => WP.mono (ha s h) fun _ m => ⟨_, m⟩) (fun s h => WP.mono (ha' s h) fun _ m => ⟨_, m⟩)
  -- The index into `rax`.
  have hmv : ∀ {s₀ : State}, ∀ s, (G s ∧ ∃ mE, OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl)
      (bytesAt s₀.mem A al) mE s) → WP isa (.block [.mov32 .rax (imm 2)]) s (MovI M s₀ Ctx W SP Np A D Tp R nl al n t) :=
    fun s h => by
      obtain ⟨s₄, run₄, hax, hg, hm, hrd, hwr⟩ := movIdx_ok s
      exact WP.of_runBlock ⟨s₄, run₄, s, h, hax, hg, hm, hrd, hwr⟩
  have m := rel_wp (rel_taint (P := fun s₁ s₂ => (True ∧ G s₁ ∧ G s₂) ∧
      (∃ mE, OneMid s₀ Ctx W SP D n (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) mE s₁) ∧
      (∃ mE, OneMid s₀' Ctx W SP D n (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al) mE s₂))
      (c := .block [.mov32 .rax (imm 2)]) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env ⟨h.1.2.1.1, h.1.2.2.1⟩) ⟨_, by taint_decide⟩)
    (fun _ _ h => ⟨⟨h.1.2.1, h.2.1⟩, ⟨h.1.2.2, h.2.2⟩⟩) (hmv (s₀ := s₀)) (hmv (s₀ := s₀'))
  -- After the push.
  have hP : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n)
      (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀), (s₀.gpr .r9).toNat = al →
      (s₀.gpr .rsi).toNat = R → ArgT SP Tp s₀ → Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr) →
      ∀ s₄, MovI M s₀ Ctx W SP Np A D Tp R nl al n t s₄ →
      PushedI M s₀ Ctx W SP D Tp R al n t (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al)
        (pushed [.rax] s₄) ∧
      InI M Ctx W SP R A al D n none t Tp (pushed [.rax] s₄) ∧ IdxAt W (SP - BitVec.ofNat 64 8) (pushed [.rax] s₄) :=
    fun C X hal hR hT hTr s₄ ⟨s₃, ⟨G₃, mE, M₃⟩, hax, hg, hm, hrd, hwr⟩ => by
      have P := pushedI_of C K oT (C.arg24 (by decide)) X hR hal hT (C.args 2 (by decide)) hTr hb M₃ G₃.2.1 hax hg hm hrd hwr
      exact ⟨P, inI_of C K (G₃.1.keep (fun r hr => hg r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> decide)) hm hrd hwr) (by rw [length_bytesAt]; exact h12) P⟩
  -- The body, a word lower.
  have oA'' : OutWDS W D (SP - BitVec.ofNat 64 8) n ⟨SP + BitVec.ofNat 64 24, 8⟩ :=
    fun r hr => hr.elim (fun h => oA r (.inl h)) fun h => h.elim (fun h => oA r (.inr (.inl h)))
      fun h => (Offset.disjoint_below SP (n := 32) (d := 24) (k := 8) (by decide)).sub_right
        fun a ha => b8 (by decide) a (h a ha)
  have sp24' : 24 ≤ (SP - BitVec.ofNat 64 8).toNat := by rw [toNat_sub_ofNat (by omega)]; omega
  have w_sp' : (SP - BitVec.ofNat 64 8).toNat + 8 ≤ 2 ^ 64 := by rw [toNat_sub_ofNat (by omega)]; have := L.ww; omega
  have hDW' := C.dE.sub_left (Offset.sub_base D (d := 16 * (n / 16)) (n := n - 16 * (n / 16)) (by omega))
  have pre := rel_wp ((preI_rel L' F (R := R) (A := A) (al := al) (t := t) (Tp := Tp) htr htg
      (kc.sub_left (b8 (by decide))) (K.w.sub_left (b8 (by decide))) (K.d.sub_left (b8 (by decide))) sp24'
      (K.w.sub_left (two_sub32 SP)) (K.d.sub_left (two_sub32 SP)) w_sp' oA'' C.dE hlt).mono
      (P' := fun u₁ u₂ =>
        (PushedI M s₀ Ctx W SP D Tp R al n t (ctxH s₀.mem Ctx) (bytesAt s₀.mem Np nl) (bytesAt s₀.mem A al) u₁ ∧
          InI M Ctx W SP R A al D n none t Tp u₁ ∧ IdxAt W (SP - BitVec.ofNat 64 8) u₁) ∧
        (PushedI M s₀' Ctx W SP D Tp R al n t (ctxH s₀'.mem Ctx) (bytesAt s₀'.mem Np nl) (bytesAt s₀'.mem A al) u₂ ∧
          InI M Ctx W SP R A al D n none t Tp u₂ ∧ IdxAt W (SP - BitVec.ofNat 64 8) u₂))
      (fun _ _ h => ⟨h.1.2, h.2.2⟩) fun _ _ h => h) (fun _ _ h => h)
    (fun _ h => preI_ok C K oT F htg hok h.1 h.2) (fun _ h => preI_ok C' K oT F htg hok h.1 h.2)
  have body := rel_reassoc6 (RelCT.seq pre (openPost_rel v L' (M := M) (R := R) (A := A) (al := al)
    (congrArg (!·) hres) hDW'))
  have fr := RelCT.frame (rs := [.rax]) (r := .r10) (k := 1)
    (P := fun s₁ s₂ => True ∧ MovI M s₀ Ctx W SP Np A D Tp R nl al n t s₁ ∧
      MovI M s₀' Ctx W SP Np A D Tp R nl al n t s₂)
    (fun _ _ h => by rw [h.2.1.rsp, h.2.2.rsp])
    (body.mono (fun _ _ ⟨s₁, s₂, h, ha, hb⟩ => by
      subst ha hb
      exact ⟨hP C X hal hR hT hTr s₁ h.2.1, hP C' X' hal' hR' hT' hTr' s₂ h.2.2⟩) fun _ _ h => h)
  have hwF : ∀ {s₀ : State} {Np : Addr} (C : OneCtx s₀ 5 Ctx W SP Np A D nl al n)
      (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s₀), (s₀.gpr .r9).toNat = al →
      (s₀.gpr .rsi).toNat = R → ArgT SP Tp s₀ → Covers [⟨Tp, t⟩] (s₀.rd ++ s₀.wr) →
      ∀ s₄, MovI M s₀ Ctx W SP Np A D Tp R nl al n t s₄ →
      WP isa (.frame (.push [.rax])
        (.seq (oneBlocks F.fn) (.seq tg
        (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 32))])
        (.seq recv (.seq (cmp uO) (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
        (.seq (.ite .e (oneUndo (v.withBlk B)) (oneCrypt (v.withBlk B)))
          (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))
        (.pop .r10 1)) s₄ (Env Ctx (W + BitVec.ofNat 64 16) W SP) :=
    fun C X hal hR hT hTr s₄ h => by
      have P := (hP C X hal hR hT hTr s₄ h).1
      have hn8 : 8 * [Reg.rax].length ≤ (s₄.gpr .rsp).toNat := by rw [h.rsp]; simp; omega
      exact WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (bodyI_ok C K oT (C.arg24 (by decide)) v B F htg
        hok (by rw [length_bytesAt]; exact h12) (length_bytesAt _ _ _) rfl rfl rfl hR P)
        fun _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃.1⟩)
  exact RelCT.seq a (RelCT.seq m ((rel_wp fr (fun _ _ h => ⟨h.2.1, h.2.2⟩) (hwF C X hal hR hT hTr)
    (hwF C' X' hal' hR' hT' hTr')).mono (fun _ _ h => h) fun _ _ h => h.2))

end VG.Proof.AesGcm.X86_64
