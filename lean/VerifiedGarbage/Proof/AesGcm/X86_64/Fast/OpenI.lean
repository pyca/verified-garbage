module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Open
public import VerifiedGarbage.Proof.AesGcm.X86_64.OneBlocks.OkI
public import VerifiedGarbage.Proof.AesGcm.X86_64.Split.Body
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on x86-64: `open`'s body calling the function given the block index

Untrusted: everything here is checked by Lean. For a 12-byte nonce, the
first counter block's index is 2 (`ctrIndex_first`). After the additional
data, the body pushes it in a frame of one word, and runs `open`'s body
(`openBody_ok`) a word lower, with its whole blocks decrypted by
`vg_aes_gcm_decrypt_blocks_prepared_iv96` (`oneBlocksDI_ok`), which finds the
index above `scratch`: it leaves what `openOkW_ok`'s body does
(`openOkWI_ok`), in the 32 bytes of stack below `SP` that `open` may use
(`Stk32`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ctxH ctxCiph inc32 zeros padLen ghashFrom ghash blocks ofBytes toBytes ctrIndex)
open VG.Proof.Gcm (Absorbed xorKs lensBlock padded)
open Gcm.X86_64.Stitch (CtxMode)

/-- The stack below `SP - 8`, in the 32 bytes below `SP`. -/
theorem below8_sub32 {SP : Addr} {k : Nat} (hk : k + 8 ≤ 32) :
    Region.Sub (below (SP - BitVec.ofNat 64 8) k) (below SP 32) :=
  fun a h => below_sub (by omega) (by decide) a (below_below SP 8 k a h)

/-- The two words below `SP - 8`, in the 32 bytes below `SP`. -/
theorem two_sub32 (SP : Addr) : Region.Sub ⟨SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 8, 16⟩ (below SP 32) := by
  have e : SP - BitVec.ofNat 64 8 - BitVec.ofNat 64 8 = SP - BitVec.ofNat 64 16 := by
    rw [← Offset.sub_add_eq, ← BitVec.ofNat_add]
  rw [e]; exact below_sub (by decide) (by decide)

/-- The layout, a word lower, within the 32 bytes below `SP`. -/
theorem lay_pushed32 {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
    (kc : (below SP 32).Disjoint ⟨Ctx, 256⟩) (kw : (below SP 32).Disjoint ⟨W, 2560⟩) :
    Lay Ctx (W + BitVec.ofNat 64 16) W (SP - BitVec.ofNat 64 8) :=
  ⟨L.cw, L.sw, L.ww, L.cs, L.cw', L.sa, L.sb, kc.sub_left (below8_sub32 (by decide)),
    (kw.sub_right (Lay.wSub (by decide))).sub_left (below8_sub32 (by decide)), kw.sub_left (below8_sub32 (by decide))⟩

theorem e32 (SP : Addr) : SP - BitVec.ofNat 64 8 + BitVec.ofNat 64 32 = SP + BitVec.ofNat 64 24 := by
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl

/-- What the state `u` after the push of the index holds, from the entry state
`s`, with the hash subkey `H`, the nonce `iv` and the additional data `a`. -/
structure PushedI (M : CtxMode) (s : State) (Ctx W SP D T : Addr) (R al n t : Nat) (H : Block)
    (iv a : List Byte) (u : State) : Prop where
  ob : ObPre M Ctx W (SP - BitVec.ofNat 64 8) R D n u
  hH : blockAt u.mem (Ctx + BitVec.ofNat 64 240) = H
  alen : u.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  tlen : u.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t
  abs : Absorbed u.mem (yA W) (W + BitVec.ofNat 64 16 + BitVec.ofNat 64 32) H (a ++ zeros (padLen a.length))
  j0 : blockAt u.mem (W + BitVec.ofNat 64 16) = Spec.Gcm.j0 H iv
  cb : blockAt u.mem (cbA W) = inc32 (Spec.Gcm.j0 H iv)
  idx : u.mem.readW (SP - BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 2
  idxR : InRegions (u.rd ++ u.wr) (SP - BitVec.ofNat 64 8) 8
  ta : u.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  tar : InRegions (u.rd ++ u.wr) (SP + BitVec.ofNat 64 24) 8
  tr : Covers [⟨T, t⟩] (u.rd ++ u.wr)
  ciph : ciphOf u.mem Ctx R = ctxCiph s.mem Ctx R
  data : bytesAt u.mem D n = bytesAt s.mem D n
  tag : bytesAt u.mem T t = bytesAt s.mem T t
  saved : SavedAt u.mem W s
  ret : u.mem.readW SP 64 = s.mem.readW SP 64
  rd : u.rd = s.rd
  wr : u.wr.tail = s.wr

section
variable {M : CtxMode} {s : State} {Ctx W SP Np A D T : Addr} {nl al n t R : Nat}
  (C : OneCtx s 5 Ctx W SP Np A D nl al n) (K : Stk32 Ctx W SP A D T M.len al n t)
  (oT : OutWDS W D SP n ⟨T, t⟩) (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩)
include C K oT oA

/-- The state after the additional data and the index into `rax` (`s₄`, from
`s₃`), pushed. -/
theorem pushedI_of (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s) (hR : (s.gpr .rsi).toNat = R)
    (hal : (s.gpr .r9).toNat = al) (hTa : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8) (hTr : Covers [⟨T, t⟩] (s.rd ++ s.wr))
    (ht : t ≤ 16) {H : Block} {iv a : List Byte} {mE : Mem} {s₃ s₄ : State} (M₃ : OneMid s Ctx W SP D n H iv a mE s₃)
    (htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t)
    (hax₄ : s₄.gpr .rax = BitVec.ofNat 64 2) (hg₄ : ∀ r, r ≠ .rax → s₄.gpr r = s₃.gpr r) (hm₄ : s₄.mem = s₃.mem)
    (hrd₄ : s₄.rd = s₃.rd) (hwr₄ : s₄.wr = s₃.wr) :
    PushedI M s Ctx W SP D T R al n t H iv a (pushed [.rax] s₄) := by
  have L := C.lay
  have hR' : R = 10 ∨ R = 12 ∨ R = 14 := hR ▸ C.rounds
  have sp := K.sp
  have kc : (below SP 32).Disjoint ⟨Ctx, 256⟩ := K.c.sub_right (Region.sub_prefix M.ge)
  have hal₃ : s₃.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al := by
    rw [M₃.alen, ← hal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hTa₃ : s₃.mem.readW (SP + BitVec.ofNat 64 24) 64 = T := by
    rw [M₃.frame.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oA _ (.inl fun _ h => h)
      · exact oA _ (.inr (.inr (below_sub (by decide) (by decide))))) (by decide), hTa]
  have X₃ := X.keep M₃.rd M₃.wr M₃.frame fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact X.cw
    · exact (X.ct.sub_left (below_sub (by decide) (by decide))).symm
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := M₃.env.keep (fun r hr => hg₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₄ hwr₄
  have hd₄ : DataW Ctx (W + BitVec.ofNat 64 16) W SP s₄ D n := C.data.of_eq (hrd₄.trans M₃.rd) (hwr₄.trans M₃.wr)
  have hn8 : 8 * [Reg.rax].length ≤ (s₄.gpr .rsp).toNat := by rw [he₄.rsp]; simp; omega
  obtain ⟨f₀, -⟩ := Split.push_frame he₄ (by omega)
  obtain ⟨-, hpj⟩ := pushRegs_mem s₄ [.rax] (by decide) hn8
  have b8 : Region.Sub (below SP 8) (below SP 32) := below_sub (by decide) (by decide)
  have one : ∀ {r : Region}, (below SP 32).Disjoint r → ∀ r' ∈ [below SP 8], r.Disjoint r' := fun hd r' hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (hd.sub_left b8).symm
  have rW : ∀ d, d + 8 ≤ 2560 →
      (pushed [.rax] s₄).mem.readW (W + BitVec.ofNat 64 d) 64 = s₃.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => by
      rw [f₀.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
        (one (K.w.sub_right (Lay.wSub hd))) (by decide), hm₄]
  have bA : ∀ {p : Addr}, Region.Sub ⟨p, 16⟩ ⟨W, 2560⟩ → blockAt (pushed [.rax] s₄).mem p = blockAt s₃.mem p :=
    fun hs => by rw [blockAt_frame f₀ (one (K.w.sub_right hs)), hm₄]
  have cbW : Region.Sub ⟨cbA W, 16⟩ ⟨W, 2560⟩ := by
    simp only [cbA]; rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have yW : Region.Sub ⟨yA W, 16⟩ ⟨W, 2560⟩ := by
    simp only [yA]; rw [add_ofNat_assoc]; exact Lay.wSub (by decide)
  have dM : ∀ (p : Addr) (k : Nat), (⟨p, k⟩ : Region).Disjoint ⟨W, 2560⟩ → (below SP 8).Disjoint ⟨p, k⟩ →
      ∀ r ∈ [(⟨W, 2560⟩ : Region), below SP 8], (⟨p, k⟩ : Region).Disjoint r := by
    intro p k h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h₁
    · exact h₂.symm
  have hlt := C.data.ok.lt
  have ins : ∀ {a : Addr} {k : Nat}, InRegions (s.rd ++ s.wr) a k →
      InRegions ((pushed [.rax] s₄).rd ++ (pushed [.rax] s₄).wr) a k := fun h => by
    rw [pushed_rd, pushed_wr, hrd₄, hwr₄, M₃.rd, M₃.wr]
    obtain ⟨r, hr, hc⟩ := h
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ hr, List.mem_append_right _ (List.mem_cons_of_mem _ hr)]
  refine ⟨⟨Split.env_pushed he₄,
     ⟨by rw [rW 176 (by decide)]; exact hR ▸ M₃.rounds.1, hR'⟩, by rw [rW 200 (by decide)]; exact M₃.dat,
     by rw [rW 208 (by decide)]; exact M₃.len,
     ⟨⟨by rw [pushed_rd, pushed_wr]; exact Split.covers_ins hd₄.ok.rd, hd₄.ok.lt, hd₄.ok.wrap, hd₄.ok.st, hd₄.ok.w,
        K.d.sub_left (below8_sub32 (by decide))⟩, by rw [pushed_wr]; exact Split.covers_tail hd₄.wr, hd₄.ctx⟩,
     kc.sub_left (below8_sub32 (by decide)), K.w.sub_left (below8_sub32 (by decide)),
     K.d.sub_left (below8_sub32 (by decide)),
     by rw [toNat_sub_ofNat (by omega)]; omega,
     ⟨X.w, X.cs, X.cw, X.cd, K.c.sub_left (below8_sub32 (by decide)),
      by rw [pushed_rd, pushed_wr, hrd₄, hwr₄]; exact Split.covers_ins X₃.cov,
      M.frame f₀ (one K.c) X.w (by rw [hm₄]; exact X₃.ok)⟩⟩,
    by rw [blockAt_frame f₀ (one (kc.sub_right (Offset.sub_base (d := 240) _ (by decide)))), hm₄]; exact M₃.hH,
    by rw [rW 184 (by decide)]; exact hal₃, by rw [rW 224 (by decide)]; exact htl₃, ?_,
    by rw [bA (Lay.wSub (by decide))]; exact M₃.j0, by rw [bA cbW]; exact M₃.cb,
    by have := hpj 0 (by decide); rw [he₄.rsp] at this; rw [← hax₄]; exact this,
    ⟨_, List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_self ..),
      by rw [he₄.rsp]; exact Region.contains_self _ _⟩,
    by rw [f₀.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact oA _ (.inr (.inr (below_sub (by decide) (by decide))))) (by decide), hm₄, hTa₃],
    ins hTar,
    by rw [pushed_rd, pushed_wr, hrd₄, hwr₄, M₃.rd, M₃.wr]; exact Split.covers_ins hTr,
    by rw [ciph_frame f₀ (one kc) hR', hm₄]; exact ciph_frame M₃.frame (fun r hr => dM _ _ L.cw' L.kc r hr) hR',
    by rw [bytesAt_frame f₀ (one K.d) (by have := C.data.ok.wrap; omega), hm₄]
       exact bytesAt_frame M₃.frame (dM _ _ C.dE C.data.ok.stk) (by omega),
    by rw [bytesAt_frame f₀ (one K.t) (by omega), hm₄]
       exact bytesAt_frame M₃.frame (fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl
         · exact oT _ (.inl fun _ h => h)
         · exact oT _ (.inr (.inr (below_sub (by decide) (by decide))))) (by omega),
    (hm₄ ▸ M₃.saved : SavedAt s₄.mem W s).frame f₀ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((K.w.sub_left b8).sub_right (Lay.wSub (by decide))).symm,
    by rw [ret_kept f₀ (fun r hr => by
         simp only [List.mem_singleton] at hr; subst hr; exact ret_below SP), hm₄, ret_kept M₃.frame (fun r hr => by
         simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
         rcases hr with rfl | rfl
         · exact C.rW
         · exact ret_below SP)],
    by rw [pushed_rd, hrd₄, M₃.rd], by rw [pushed_wr, hwr₄, M₃.wr]; rfl⟩
  · have hm := Nat.mod_lt (a ++ zeros (padLen a.length)).length (show 16 > 0 by decide)
    refine ⟨by rw [bA yW]; exact M₃.abs.1, ?_⟩
    rw [bytesAt_frame f₀ (one (K.w.sub_right (by
      rw [add_ofNat_assoc]; exact Lay.wSub (d := 48) (n := (a ++ zeros (padLen a.length)).length % 16) (by omega))))
      (by have := L.ww; omega), hm₄]
    exact M₃.abs.2

/-- After the push, the body: the whole blocks decrypted by `F`, the tag
(`tg`), the tags compared, and the rest decrypted or the whole blocks
encrypted again; then, after the pop, what `open` leaves. -/
theorem bodyI_ok (v : GcmImpl) (B : BlkFn M) (F : DecFnI M) {tg : Prog isa} (htg : TagOk M tg)
    (hok' : Spec.Gcm.tagLenOk t = true) {H : Block} {iv a : List Byte} (hivl : iv.length = 12)
    (hal' : a.length = al) (hH : ctxH s.mem Ctx = H) (hiv : bytesAt s.mem Np nl = iv)
    (ha : bytesAt s.mem A al = a) (hR : (s.gpr .rsi).toNat = R) {u : State}
    (P : PushedI M s Ctx W SP D T R al n t H iv a u) :
    WP isa (.seq (oneBlocks F.fn) (.seq tg
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 32))])
      (.seq recv (.seq (cmp uO) (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (oneUndo (v.withBlk B)) (oneCrypt (v.withBlk B)))
        (.block [.mov .rax (.mem (at_ .r15 auxO))])))))))) u
      fun u' => u'.gpr .rsp = u.gpr .rsp ∧ u'.wr = u.wr ∧
        OpenOkPost s Ctx W SP Np A D T nl al n t (popped .r10 1 u') := by
  have L := C.lay
  have hlt := C.data.ok.lt
  have sp := K.sp
  have hb : 1 ≤ t ∧ t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok'
    omega
  have kc : (below SP 32).Disjoint ⟨Ctx, 256⟩ := K.c.sub_right (Region.sub_prefix M.ge)
  have L' := lay_pushed32 L kc K.w
  have hob := oneBlocksDI_ok L' F P.ob
    (by rw [P.cb, ctrIndex_first H hivl, P.idx]; rfl)
    (K.w.sub_left (two_sub32 SP)) (K.d.sub_left (two_sub32 SP)) P.idxR
    (by rw [toNat_sub_ofNat (by omega)]; have := L.ww; omega)
  have oT' : OutWDS W D (SP - BitVec.ofNat 64 8) n ⟨T, t⟩ := fun r hr =>
    hr.elim (fun h => oT r (.inl h)) fun h => h.elim (fun h => oT r (.inr (.inl h)))
      fun h => (K.t.sub_left fun a ha => below8_sub32 (by decide) a (h a ha)).symm
  have oA' : OutWDS W D (SP - BitVec.ofNat 64 8) n ⟨SP - BitVec.ofNat 64 8 + BitVec.ofNat 64 32, 8⟩ := by
    rw [e32]
    exact fun r hr => hr.elim (fun h => oA r (.inl h)) fun h => h.elim (fun h => oA r (.inr (.inl h)))
      fun h => (Offset.disjoint_below SP (n := 32) (d := 24) (k := 8) (by decide)).sub_right
        fun a ha => below8_sub32 (by decide) a (h a ha)
  refine WP.mono (openBody_ok v L' htg (al := al) P.ob hob P.hH P.alen P.tlen hb.1 hb.2 P.abs P.j0 P.cb
    (by rw [e32]; exact P.ta) (by rw [e32]; exact P.tar) P.tr oT' oA')
    fun u' ⟨he', f', rd', wr', ax', d'⟩ => ⟨he'.rsp.trans P.ob.env.rsp.symm, wr', ?_⟩
  rw [← hal'] at ax' d'
  have t_w' : (below (SP - BitVec.ofNat 64 8) 24).Disjoint ⟨W, 2560⟩ := K.w.sub_left (below8_sub32 (by decide))
  have dRet : ∀ r ∈ oneFrameB W D (SP - BitVec.ofNat 64 8) n, (⟨SP, 8⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact C.rW.sub_right (Region.sub_prefix (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rW.sub_right (Lay.wSub (by decide))
    · exact C.rD
    · exact (Offset.base_disjoint_below SP (n := 32) (k := 8) (by decide)).sub_right (below8_sub32 (by decide))
  have prd : (popped .r10 1 u').rd = s.rd := by rw [popped_rd, rd', P.rd]
  have pwr : (popped .r10 1 u').wr = s.wr := by rw [popped_wr, wr', P.wr]
  unfold OpenOkPost
  rw [hR, hH, hiv, ha]
  refine ⟨⟨by rw [popped_gpr _ _ _ (by decide) (by decide)]; exact he'.r13,
    by rw [popped_gpr _ _ _ (by decide) (by decide)]; exact he'.r14,
    by rw [popped_gpr _ _ _ (by decide) (by decide)]; exact he'.r15,
    by rw [popped_rsp, he'.rsp]; exact BitVec.sub_add_cancel _ _, C.perm.of_eq prd pwr⟩, ?_, ?_, ?_⟩
  · rw [popped_mem]; exact P.saved.frame f' (saved_oneFrameB L' C.dE t_w')
  · rw [popped_mem, ret_kept f' dRet, P.ret]
  · rw [P.ciph, P.data, P.tag] at ax'
    rw [P.ciph, P.data, P.tag, ← Proof.Gcm.gctr_eq] at d'
    simp only [OpenRes, Spec.Gcm.openResult, hok', ↓reduceIte, Spec.Gcm.decryptWith,
      Proof.Gcm.fullTag_eq, length_bytesAt, ← Proof.Gcm.gctr_eq, popped_mem]
    rw [popped_gpr _ _ _ (by decide) (by decide)]
    split at ax'
    · next e => simp only [e, ↓reduceIte] at d' ⊢; exact ⟨ax', d'⟩
    · next e => simp only [e, ↓reduceIte] at d' ⊢; exact ⟨ax', d'⟩

end

/-- `open`'s body for a tag length it allows and a 12-byte nonce, after the
entry: the additional data (`aadP`, which leaves what `oneAad` does), then,
in a frame pushing the index of the first counter block, the whole blocks
decrypted by `F`, the tag (`tg`), the tags compared, and the rest decrypted
or the whole blocks encrypted again. -/
theorem openOkWI_ok (v : GcmImpl) {M : CtxMode} (B : BlkFn M) (F : DecFnI M) {aadP tg : Prog isa}
    (htg : TagOk M tg) {s s₂ : State}
    {Ctx W SP Np A D T : Addr} {nl al n t : Nat} (C : OneCtx s 5 Ctx W SP Np A D nl al n)
    (X : CtxExt M Ctx (W + BitVec.ofNat 64 16) W SP D n s) (hal : (s.gpr .r9).toNat = al)
    (hTa : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T) (hTar : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 24) 8)
    (hTr : Covers [⟨T, t⟩] (s.rd ++ s.wr)) (oT : OutWDS W D SP n ⟨T, t⟩)
    (oA : OutWDS W D SP n ⟨SP + BitVec.ofNat 64 24, 8⟩)
    (htl : s₂.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t) (hok' : Spec.Gcm.tagLenOk t = true)
    (K : Stk32 Ctx W SP A D T M.len al n t) (hnl : nl = 12)
    (ha : WP isa aadP s₂
      (OneMid s Ctx W SP D n (ctxH s.mem Ctx) (bytesAt s.mem Np nl) (bytesAt s.mem A al) s₂.mem)) :
    WP isa (.seq aadP (.seq (.block [.mov32 .rax (imm 2)]) (.frame (.push [.rax])
      (.seq (oneBlocks F.fn) (.seq tg
      (.seq (.block [.mov .rbx (.mem (at_ .r15 tlO)), .mov .rsi (.mem (at_ .rsp 32))])
      (.seq recv (.seq (cmp uO) (.seq (.block [.store (at_ .r15 auxO) .rax, .alu .test .rax (.reg .rax)])
      (.seq (.ite .e (oneUndo (v.withBlk B)) (oneCrypt (v.withBlk B)))
        (.block [.mov .rax (.mem (at_ .r15 auxO))]))))))))
      (.pop .r10 1)))) s₂
      (OpenOkPost s Ctx W SP Np A D T nl al n t) := by
  have L := C.lay
  refine WP.seq (WP.mono ha fun s₃ M₃ => ?_)
  have htl₃ : s₃.mem.readW (W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 t := by
    rw [M₃.fr.readW (r := ⟨W + BitVec.ofNat 64 224, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w (by decide)).symm) (by decide), htl]
  obtain ⟨s₄, run₄, hax₄, hg₄, hm₄, hrd₄, hwr₄⟩ := movIdx_ok s₃
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env Ctx (W + BitVec.ofNat 64 16) W SP s₄ := M₃.env.keep (fun r hr => hg₄ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)) hrd₄ hwr₄
  have hn8 : 8 * [Reg.rax].length ≤ (s₄.gpr .rsp).toNat := by rw [he₄.rsp]; have := K.sp; simp; omega
  have hb : t ≤ 16 := by
    simp only [Spec.Gcm.tagLenOk, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hok'
    omega
  have P := pushedI_of C K oT oA X rfl hal hTa hTar hTr hb M₃ htl₃ hax₄ hg₄ hm₄ hrd₄ hwr₄
  refine WP.frame (by simp) (by decide) (by decide) hn8 (WP.mono (bodyI_ok C K oT oA v B F htg hok'
    (by rw [length_bytesAt, hnl]) (length_bytesAt _ _ _) rfl rfl rfl rfl P) fun u ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩)

end VG.Proof.AesGcm.X86_64
