module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.CTBase
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Seal
import VerifiedGarbage.Proof.AesOcb.RISCV64.HashCT
import VerifiedGarbage.Proof.AesOcb.RISCV64.BodyCT
import VerifiedGarbage.Proof.AesOcb.RISCV64.Body
import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.CTBase
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Seal
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.HashCT
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.BodyCT
meta import VerifiedGarbage.Proof.AesOcb.RISCV64.Body
meta import VerifiedGarbage.Proof.AesGcm.RISCV64.CTSeal
meta import VerifiedGarbage.Proof.Ocb.Bytes
meta import VerifiedGarbage.Proof.Ocb.State
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.AesOcb.RISCV64
meta import VerifiedGarbage.TCB.RISCV64.Isa

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
(`Proof/AesOcb/PPC64LE/FrontCT.lean`).
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
  have ht : tl < 2 ^ 64 := by have := A₁.t16; omega
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
