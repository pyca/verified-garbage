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
(`pre_rel`), `bodySeal_rel`, `tag_rel` and `restore`.
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
theorem entry_rel {σ₁ σ₂ : State} {W : Addr} (hW₁ : stackArg σ₁ 0 = W) (hW₂ : stackArg σ₂ 0 = W)
    (hargs₁ : Covers [⟨σ₁.sp, 16⟩] (σ₁.rd ++ σ₁.wr)) (hargs₂ : Covers [⟨σ₂.sp, 16⟩] (σ₂.rd ++ σ₂.wr))
    (qsp : σ₁.sp = σ₂.sp) (hq : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r) :
    RelCT isa (Eq2 σ₁ σ₂) (.block entry) TT := by
  obtain ⟨_, run₁, rfl⟩ := ldrSp_ok (t := .x9) (s := σ₁) (i := 0) (by decide) (in_off hargs₁ (by decide) (by decide))
  obtain ⟨_, run₂, rfl⟩ := ldrSp_ok (t := .x9) (s := σ₂) (i := 0) (by decide) (in_off hargs₂ (by decide) (by decide))
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
theorem pre_rel (v : BlocksImpl) {σ₁ σ₂ : State} {K W N A D : Addr} {R nl al n tl : Nat}
    (A₁ : Args σ₁ K W N A D R nl al n tl) (A₂ : Args σ₂ K W N A D R nl al n tl)
    (hW₁ : stackArg σ₁ 0 = W) (htl₁ : stackArg σ₁ 1 = BitVec.ofNat 64 tl)
    (h0₁ : σ₁.gpr .x0 = K) (h1₁ : σ₁.gpr .x1 = BitVec.ofNat 64 R) (h2₁ : σ₁.gpr .x2 = N)
    (h3₁ : σ₁.gpr .x3 = BitVec.ofNat 64 nl) (h4₁ : σ₁.gpr .x4 = A) (h5₁ : σ₁.gpr .x5 = BitVec.ofNat 64 al)
    (h6₁ : σ₁.gpr .x6 = D) (h7₁ : σ₁.gpr .x7 = BitVec.ofNat 64 n)
    (hW₂ : stackArg σ₂ 0 = W) (htl₂ : stackArg σ₂ 1 = BitVec.ofNat 64 tl)
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

/-- What `onePre` gives in two runs with the same public arguments, with the
values of the first. -/
theorem args₂_of {σ₁ σ₂ : State} (h₂ : onePre σ₂) (hq : onePub σ₁ σ₂) :
    Args σ₂ (σ₁.gpr .x0) (stackArg σ₁ 0) (σ₁.gpr .x2) (σ₁.gpr .x4) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat
      (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (σ₁.gpr .x7).toNat (stackArg σ₁ 1).toNat := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, qa⟩ := hq
  have A₂ := args_of h₂
  rw [← q0, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7, ← qa 0 (by decide), ← qa 1 (by decide)] at A₂
  exact A₂

/-- `pre_rel` and `pre_wp'` from `onePre` in two runs, then `k`. -/
theorem pre_relk (v : BlocksImpl) {σ₁ σ₂ : State} (h₁ : onePre σ₁) (h₂ : onePre σ₂) (hq : onePub σ₁ σ₂)
    {k : Prog isa}
    (hk : ∀ τ₁ τ₂, Pre (σ₁.gpr .x0) (stackArg σ₁ 0) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat (σ₁.gpr .x7).toNat (σ₁.gpr .x2)
      (σ₁.gpr .x4) (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (stackArg σ₁ 1).toNat σ₁ τ₁ →
      Pre (σ₁.gpr .x0) (stackArg σ₁ 0) (σ₁.gpr .x6) (σ₁.gpr .x1).toNat (σ₁.gpr .x7).toNat (σ₁.gpr .x2)
      (σ₁.gpr .x4) (σ₁.gpr .x3).toNat (σ₁.gpr .x5).toNat (stackArg σ₁ 1).toNat σ₂ τ₂ →
      RelCT isa (Eq2 τ₁ τ₂) k TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq (.block entry) (.seq (nonce (callees v)) (.seq (hash (callees v)) k))) TT := by
  have A₁ := args_of h₁
  have A₂ := args₂_of h₂ hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp, qa⟩ := hq
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have o' : ∀ {x y : BitVec 64}, x = y → y = BitVec.ofNat 64 x.toNat := fun h => by rw [h]; exact o _
  refine RelCT.assoc_in (RelCT.assoc (rel_seq (pre_rel v A₁ A₂ rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _)
      (qa 0 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3) q4.symm (o' q5) q6.symm
      (o' q7) qsp)
    (pre_wp' v A₁ rfl (o _) rfl (o _) rfl (o _) rfl (o _) rfl (o _))
    (pre_wp' v A₂ (qa 0 (by decide)).symm (o' (qa 1 (by decide))) q0.symm (o' q1) q2.symm (o' q3) q4.symm (o' q5)
      q6.symm (o' q7)) hk))

theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealAArch64.pre sealAArch64.pub («seal» (callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  have A₁ := args_of h₁
  have A₂ := args₂_of h₂ hq
  have qsp := hq.2.2.2.2.2.2.2.2.1
  have L := A₁.lay
  unfold «seal»
  refine pre_relk v h₁ h₂ hq fun τ₁ τ₂ P₁ P₂ => ?_
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
  exact rel_env T₁.env T₂.env [] (by agree_tac []) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64
