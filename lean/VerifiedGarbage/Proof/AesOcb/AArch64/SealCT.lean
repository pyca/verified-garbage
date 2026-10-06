import VerifiedGarbage.Proof.AesOcb.AArch64.NonceCT
import VerifiedGarbage.Proof.AesOcb.AArch64.HashCT
import VerifiedGarbage.Proof.AesOcb.AArch64.BodyCT
import VerifiedGarbage.Proof.AesOcb.AArch64.Seal

/-!
# AES-OCB on AArch64: `vg_aes_ocb_seal` is constant time

Untrusted: everything here is checked by Lean. The entry loads `work` from
the stack, which the taint analysis takes as secret (it reads memory): the
block is split after the load, and the rest runs from `x9`, which holds
`work` (public) in both runs (`entry_rel`). Then `nonce_rel`, `hash_rel`
(`pre_rel`), `bodySeal_rel`, `tag_rel`, the copy of the tag, whose first
block loads the tag's address from the stack and is split there
(`tagOut_rel`), and `restore`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxCiph ctxLstar)
open VG.Proof.Ocb (length_bytesAt)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint ct_of in_off RelCT.block_split)

/-- The entry of `seal` and `open`, in two runs. -/
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} (hW₁ : stackArg σ₁ 2 = W) (hW₂ : stackArg σ₂ 2 = W)
    (hargs₁ : Covers [⟨σ₁.sp, 24⟩] (σ₁.rd ++ σ₁.wr)) (hargs₂ : Covers [⟨σ₂.sp, 24⟩] (σ₂.rd ++ σ₂.wr))
    (qsp : σ₁.sp = σ₂.sp) (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨_, run₁, rfl⟩ := ldrSp_ok (t := .x9) (s := σ₁) (i := 2) (by decide) (in_off hargs₁ (by decide) (by decide))
  obtain ⟨_, run₂, rfl⟩ := ldrSp_ok (t := .x9) (s := σ₂) (i := 2) (by decide) (in_off hargs₂ (by decide) (by decide))
  simp only [Nat.reduceMul] at run₁ run₂
  rw [entry]
  simp only [List.append_assoc]
  refine RelCT.block_split (rel_seq (rel_taint [] qsp (by agree_tac []) ⟨_, by taint_decide⟩)
    (WP.of_runBlock ⟨_, run₁, rfl⟩) (WP.of_runBlock ⟨_, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_)
  subst h₁ h₂
  refine rel_taint [.x9, .x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (by simp only [sp_write]; exact qsp) ?_
    ⟨_, by taint_decide⟩
  intro r hr
  by_cases h9 : r = .x9
  · subst h9; simp [gpr_write, hW₁, hW₂]
  · simp only [gpr_write, h9, ite_false]
    exact hq r (by simp only [List.mem_cons, List.not_mem_nil, or_false, h9, false_or] at hr ⊢; exact hr)

/-- `entry`, `nonce` and `hash`, in two runs with the same public arguments. -/
theorem pre_rel (v : BlocksImpl) {σ₁ σ₂ : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (A₁ : Args σ₁ K W N A D R nl al n tl T) (A₂ : Args σ₂ K W N A D R nl al n tl T)
    (hW₁ : stackArg σ₁ 2 = W) (htl₁ : stackArg σ₁ 1 = BitVec.ofNat 64 tl)
    (h0₁ : σ₁.gpr .x0 = K) (h1₁ : σ₁.gpr .x1 = BitVec.ofNat 64 R) (h2₁ : σ₁.gpr .x2 = N)
    (h3₁ : σ₁.gpr .x3 = BitVec.ofNat 64 nl) (h4₁ : σ₁.gpr .x4 = A) (h5₁ : σ₁.gpr .x5 = BitVec.ofNat 64 al)
    (h6₁ : σ₁.gpr .x6 = D) (h7₁ : σ₁.gpr .x7 = BitVec.ofNat 64 n)
    (hW₂ : stackArg σ₂ 2 = W) (htl₂ : stackArg σ₂ 1 = BitVec.ofNat 64 tl)
    (h0₂ : σ₂.gpr .x0 = K) (h1₂ : σ₂.gpr .x1 = BitVec.ofNat 64 R) (h2₂ : σ₂.gpr .x2 = N)
    (h3₂ : σ₂.gpr .x3 = BitVec.ofNat 64 nl) (h4₂ : σ₂.gpr .x4 = A) (h5₂ : σ₂.gpr .x5 = BitVec.ofNat 64 al)
    (h6₂ : σ₂.gpr .x6 = D) (h7₂ : σ₂.gpr .x7 = BitVec.ofNat 64 n) (qsp : σ₁.sp = σ₂.sp) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block entry) (.seq (nonce (callees v)) (hash (callees v)))) TT := by
  have L := A₁.lay
  refine rel_seq (entry_rel hW₁ hW₂ A₁.args A₂.args qsp
      (by agree_tac [h0₁, h0₂, h1₁, h1₂, h2₁, h2₂, h3₁, h3₂, h4₁, h4₂, h5₁, h5₂, h6₁, h6₂, h7₁, h7₂]))
    (entry_ok L A₁.perm hW₁ htl₁ A₁.args A₁.argsW h0₁ h1₁ h2₁ h3₁ h4₁ h5₁ h6₁ h7₁)
    (entry_ok L A₂.perm hW₂ htl₂ A₂.args A₂.argsW h0₂ h1₂ h2₂ h3₂ h4₂ h5₂ h6₂ h7₂) fun s₁ s₂ P₁ P₂ => ?_
  have E₂ := P₂.env
  rw [← qsp] at E₂
  have ht : tl < 2 ^ 64 := by have := A₁.t16; omega
  refine rel_seq (nonce_rel v L P₁.env E₂ A₁.rounds P₁.slots.nonce P₂.slots.nonce P₁.slots.nlen P₂.slots.nlen
      P₁.slots.tl P₂.slots.tl A₁.n1 A₁.n15 ht (A₁.nonce.of_eq P₁.rd P₁.wr) (A₂.nonce.of_eq P₂.rd P₂.wr))
    (nonce_ok v L P₁.env A₁.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl A₁.n1 A₁.n15 ht
      (A₁.nonce.of_eq P₁.rd P₁.wr) A₁.data.k)
    (nonce_ok v L E₂ A₁.rounds P₂.slots.nonce P₂.slots.nlen P₂.slots.tl A₁.n1 A₁.n15 ht
      (A₂.nonce.of_eq P₂.rd P₂.wr) A₁.data.k) fun t₁ t₂ Q₁ Q₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w (nonceR_mut Q₁.frame) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w (nonceR_mut Q₂.frame) P₂.slots
  exact hash_rel v (hctx_of A₁ P₁ Q₁) (hctx_of A₂ P₂ Q₂) (by rw [length_bytesAt, length_bytesAt]) Q₁.env Q₂.env
    S₁.aad S₂.aad (by rw [length_bytesAt]; exact S₁.alen) (by rw [length_bytesAt]; exact S₂.alen)
    (by rw [Q₁.keep (by decide) (by decide), P₁.l0]) (by rw [Q₂.keep (by decide) (by decide), P₂.l0])

/-- `Args` in two runs with the same public arguments, with the values of the
first. -/
theorem args₂_of {σ₁ σ₂ : State} (hq : onePub σ₁ σ₂)
    (A₂ : Args σ₂ (σ₂.gpr .x0) (stackArg σ₂ 2) (σ₂.gpr .x2) (σ₂.gpr .x4) (σ₂.gpr .x6) (σ₂.gpr .x1).toNat
      (σ₂.gpr .x3).toNat (σ₂.gpr .x5).toNat (σ₂.gpr .x7).toNat (stackArg σ₂ 1).toNat (stackArg σ₂ 0)) :
    Args σ₂ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0) := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, qa⟩ := hq
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qa 0 (by decide), ← qa 1 (by decide),
    ← qa 2 (by decide)] at A₂
  exact A₂

/-- `pre_rel` and `pre_wp'` in two runs with the same public arguments, then
`k`. -/
theorem pre_relk (v : BlocksImpl) {σ₁ σ₂ : State}
    (A₁ : Args σ₁ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (A₂ : Args σ₂ (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat (stackArg σ₁ 0))
    (hq : onePub σ₁ σ₂) {k : Prog isa}
    (hk : ∀ τ₁ τ₂, Pre (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat (σ₁.gpr .x7).toNat (σ₁.gpr .x2)
      (σ₁.gpr .x4) (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (stackArg σ₁ 1).toNat σ₁ τ₁ →
      Pre (σ₁.gpr .x0) (stackArg σ₁ 2) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat (σ₁.gpr .x7).toNat (σ₁.gpr .x2)
      (σ₁.gpr .x4) (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (stackArg σ₁ 1).toNat σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) k TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block entry) (.seq (nonce (callees v)) (.seq (hash (callees v)) k))) TT := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have o' : ∀ {x y : BitVec 64}, x = y → y = BitVec.ofNat 64 x.toNat := fun h => by rw [h]; exact o _
  refine RelCT.assoc_in (RelCT.assoc (rel_seq (pre_rel v A₁ A₂ rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _)
      (qa 2 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3) q4.symm (o' q5) q6.symm
      (o' q7) qsp)
    (pre_wp' v A₁ rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _))
    (pre_wp' v A₂ (qa 2 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3) q4.symm (o' q5)
      q6.symm (o' q7)) hk))

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

/-- `tagOut` in two runs: its first block loads the tag's address from the
stack, and the copy runs from it. -/
theorem tagOut_rel {K W D : Addr} {R n : Nat} {SP : Addr} {σ₁ σ₂ : State} (E₁ : Env K W D R n SP σ₁)
    (E₂ : Env K W D R n SP σ₂) {T : Addr} {tl : Nat}
    (htl₁ : σ₁.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl)
    (htl₂ : σ₂.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl) (hT₁ : stackArg σ₁ 0 = T)
    (hT₂ : stackArg σ₂ 0 = T) (ha₁ : InRegions (σ₁.rd ++ σ₁.wr) (σ₁.sp + BitVec.ofNat 64 (8 * 0)) 8)
    (ha₂ : InRegions (σ₂.rd ++ σ₂.wr) (σ₂.sp + BitVec.ofNat 64 (8 * 0)) 8) : RelCT isa (Eq2 σ₁ σ₂) tagOut TT := by
  obtain ⟨s₁, run₁, x11₁, x12₁, x13₁, -, g₁, sp₁, rd₁, wr₁⟩ := tagOutHead_ok E₁ htl₁ hT₁ ha₁
  obtain ⟨s₂, run₂, x11₂, x12₂, x13₂, -, g₂, sp₂, rd₂, wr₂⟩ := tagOutHead_ok E₂ htl₂ hT₂ ha₂
  unfold tagOut
  refine rel_seq (rel_env E₁ E₂ [] (by agree_tac []) ⟨_, by taint_decide⟩) (WP.of_runBlock ⟨s₁, run₁, rfl⟩)
    (WP.of_runBlock ⟨s₂, run₂, rfl⟩) fun τ₁ τ₂ h₁ h₂ => ?_
  subst h₁ h₂
  exact rel_env (E₁.others g₁ sp₁ rd₁ wr₁) (E₂.others g₂ sp₂ rd₂ wr₂) [.x11, .x12, .x13]
    (by agree_tac [x11₁, x11₂, x12₁, x12₂, x13₁, x13₂]) ⟨_, by taint_decide⟩

/-- The state after `front`, in a run with the arguments: the address of the
tag on the stack, where the state may read it. -/
theorem front_tag {s : State} {K W N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W N A D R nl al n tl T) (hT : stackArg s 0 = T) {s₃ s₄ s₅ : State} {d : Nat} (hd : d + 16 ≤ 160)
    (P : Pre K W D R n N A nl al tl s s₃) {out : List Byte} {ofs ck : Spec.Ocb.Block}
    {SP SP' : Addr} (B : BodyPost K W D R n SP' out ofs ck s₃ s₄) (T₅ : TagPost K W D R n SP d s₄ s₅)
    (hsp : SP = s.sp) :
    stackArg s₅ 0 = T ∧ InRegions (s₅.rd ++ s₅.wr) (s₅.sp + BitVec.ofNat 64 (8 * 0)) 8 := by
  have sp₅ : s₅.sp = s.sp := T₅.env.sp.trans hsp
  refine ⟨?_, ?_⟩
  · rw [← hT]; simp only [stackArg, stackArgAddr, sp₅]
    exact args_kept Ar.argsW Ar.argsD (front_frame hd P.frame B.frame T₅.frame) (i := 0) (by decide)
  · rw [T₅.rd, B.rd, P.rd, T₅.wr, B.wr, P.wr, sp₅]
    exact in_off Ar.args (by decide) (by decide)

theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» (callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have A₁ := sealArgs_of h₁
  have A₂ := args₂_of hq (sealArgs_of h₂)
  have qsp := hq.2.2.2.2.2.2.2.2.1
  have qT : stackArg σ₂ 0 = stackArg σ₁ 0 := (hq.2.2.2.2.2.2.2.2.2 0 (by decide)).symm
  have L := A₁.lay
  unfold «seal» front
  refine rel_front (pre_relk v A₁ A₂ hq fun τ₁ τ₂ P₁ P₂ => ?_)
  have E₂ := P₂.env
  rw [← qsp] at E₂
  refine rel_seq (bodySeal_rel L A₁.rounds v P₁.env E₂ (A₁.data.of_eq P₁.rd P₁.wr) (A₂.data.of_eq P₂.rd P₂.wr)
      P₁.ofs P₁.o0 P₁.ck (by rw [P₁.l0, ctxLstar_W L P₁.frame]) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, ctxLstar_W L P₂.frame]))
    (bodySeal_ok v L P₁.env A₁.rounds (A₁.data.of_eq P₁.rd P₁.wr) P₁.ofs P₁.o0 P₁.ck
      (by rw [P₁.l0, ctxLstar_W L P₁.frame]))
    (bodySeal_ok v L E₂ A₁.rounds (A₂.data.of_eq P₂.rd P₂.wr) P₂.ofs P₂.o0 P₂.ck
      (by rw [P₂.l0, ctxLstar_W L P₂.frame])) fun u₁ u₂ B₁ B₂ => ?_
  refine rel_seq (tag_rel L A₁.rounds v B₁.env B₂.env (.inl rfl)) (tag_ok v L B₁.env A₁.rounds (.inl rfl))
    (tag_ok v L B₂.env A₁.rounds (.inl rfl)) fun w₁ w₂ T₁ T₂ => ?_
  have S₁ := Slots.of_mut L A₁.data.w ((bodyR_mut B₁.frame).trans (tagR_mut (by decide) T₁.frame)) P₁.slots
  have S₂ := Slots.of_mut L A₁.data.w ((bodyR_mut B₂.frame).trans (tagR_mut (by decide) T₂.frame)) P₂.slots
  obtain ⟨t₁, a₁⟩ := front_tag A₁ rfl (by decide) P₁ B₁ T₁ rfl
  obtain ⟨t₂, a₂⟩ := front_tag A₂ qT (by decide) P₂ B₂ T₂ qsp
  refine rel_seq (tagOut_rel T₁.env T₂.env S₁.tl S₂.tl t₁ t₂ a₁ a₂)
    (tagOut_ok T₁.env A₁.t1 A₁.t16 S₁.tl t₁ a₁ (by
      rw [T₁.wr, B₁.wr, P₁.wr, h₁.2.1]; exact Proof.AesGcm.AArch64.covers_of_mem (by simp)) A₁.tag.w)
    (tagOut_ok T₂.env A₁.t1 A₁.t16 S₂.tl t₂ a₂ (by
      rw [T₂.wr, B₂.wr, P₂.wr, h₂.2.1, ← qT, hq.2.2.2.2.2.2.2.2.2 1 (by decide)]
      exact Proof.AesGcm.AArch64.covers_of_mem (by simp)) A₂.tag.w)
    fun y₁ y₂ ⟨_, g₁, sp₁, rd₁, wr₁⟩ ⟨_, g₂, sp₂, rd₂, wr₂⟩ => ?_
  exact rel_env (T₁.env.others g₁ sp₁ rd₁ wr₁) (T₂.env.others g₂ sp₂ rd₂ wr₂) [] (by agree_tac [])
    ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64
