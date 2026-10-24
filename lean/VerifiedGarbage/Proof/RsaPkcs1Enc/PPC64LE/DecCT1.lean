module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCTBase
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecD
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecCTBase
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecD
import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivCT

/-!
# `vg_rsa_pkcs1_decrypt` on PPC64LE: constant time up to `D`

The setup and `D`'s blocks and loops, by the taint analysis from the
registers correctness fixes (`setup_ct`, `dBuild_ct`), and the call of
`vg_rsa_private_checked`, by its constant time (`priv_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Dec

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Impl.RsaPkcs1Enc.PPC64LE.Decrypt

section
variable {e : Env}

/-- After the frame's push. -/
def PEnt (s u : State) : Prop := u = allocated frameBytes s

theorem setup_ct : RelCT isa (Rel e PEnt) (.block setup) (Rel e AtPriv) :=
  rel_step [] (by taint_decide)
    (fun a b ha hb => ⟨by rw [ha, hb]; show e.s₁.sp - _ = e.s₂.sp - _; rw [e.S.sp], fun _ h => nomatch h⟩)
    fun _ _ h hu => hu ▸ setup_ok h

omit e in
theorem bytes_priv {s u : State} (A : AtPriv s u) {p : Addr} {n : Nat} (hd : Region.Disjoint ⟨p, n⟩ (kR s))
    (hl : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt u.mem p n = Spec.Rsa.bytesAt s.mem p n :=
  bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl

theorem priv_pub {u₁ u₂ : State} (A₁ : AtPriv e.s₁ u₁) (A₂ : AtPriv e.s₂ u₂) :
    Rsa.PPC64LE.Priv.fnContract.pub (callE e.s₁ u₁) (callE e.s₂ u₂) := by
  have m : ∀ {s u : State}, (callE s u).mem = u.mem := fun {_ _} => rfl
  refine Rsa.PPC64LE.Priv.pub_of (by rw [show (callE e.s₁ u₁).sp = fb e.s₁ from A₁.sp,
    show (callE e.s₂ u₂).sp = fb e.s₂ from A₂.sp, e.fb_eq]) (fun r hr => ?_)
    (fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, e.arg (by omega)]) ?_ ?_
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.r3, A₂.r3, e.r]
    · rw [A₁.r4, A₂.r4, e.r]
    · rw [A₁.r5, A₂.r5, e.r]
    · rw [A₁.r6, A₂.r6, e.r]
    · rw [A₁.r7, A₂.r7, e.r]
    · rw [A₁.r8, A₂.r8, e.r]
    · rw [A₁.r9, A₂.r9, e.arg]
    · rw [A₁.r10, A₂.r10, e.r]
  · rw [m, m, callE_gpr _ _ (r := .r5), callE_gpr _ _ (r := .r6), callE_gpr _ _ (r := .r5),
      callE_gpr _ _ (r := .r6), A₁.r5, A₁.r6, A₂.r5, A₂.r6,
      bytes_priv A₁ e.h₁.kn.symm (by have := e.h₁.wn; omega), bytes_priv A₂ e.h₂.kn.symm (by have := e.h₂.wn; omega), e.S.n]
  · rw [m, m, callE_gpr _ _ (r := .r7), callE_gpr _ _ (r := .r8), callE_gpr _ _ (r := .r7),
      callE_gpr _ _ (r := .r8), A₁.r7, A₁.r8, A₂.r7, A₂.r8,
      bytes_priv A₁ e.h₁.ke.symm (by have := e.h₁.we; omega), bytes_priv A₂ e.h₂.ke.symm (by have := e.h₂.we; omega), e.S.e]

theorem priv_ct : RelCT isa (Rel e AtPriv) privCall (Rel e AtD) := by
  refine rel_post ?_ fun s u h A => call_ok h A fun v hv => hv
  unfold privCall
  exact VG.PPC64LE.RelCT.callEx (k := Rsa.PPC64LE.Priv.fnContract) Rsa.PPC64LE.Priv.code_correct Rsa.PPC64LE.Priv.code_ct
    fun u₁ u₂ ⟨A₁, A₂⟩ => ⟨callRd e.s₁, callWr e.s₁, callRd e.s₂, callWr e.s₂,
      Rsa.PPC64LE.Priv.pre_of_preP (preP_entry e.h₁ A₁), Rsa.PPC64LE.Priv.pre_of_preP (preP_entry e.h₂ A₂),
      priv_pub A₁ A₂, (call_covers e.h₁ A₁).1, (call_covers e.h₁ A₁).2, (call_covers e.h₂ A₂).1,
      (call_covers e.h₂ A₂).2⟩

/-! ## `D` -/

def PZ0 (s u : State) : Prop := ∃ R EM, ZInv s R EM 0 u ∧ u.gpr .r9 = s.gpr .r7
def PZ (s u : State) : Prop := ∃ R EM, ZInv s R EM (s.gpr .r7).toNat u
def PC0 (s u : State) : Prop := ∃ R EM, CInv s R EM 0 u ∧ u.gpr .r9 = stackArg s 0
def PDB (s u : State) : Prop := ∃ R EM, DB s R EM u

theorem dBuild_ct : RelCT isa (Rel e AtD) dBuild (Rel e PDB) := by
  refine RelCT.seq (rel_step [] (by taint_decide)
    (fun a b A B => ⟨by rw [A.sp, B.sp, e.fb_eq], fun _ h => nomatch h⟩)
    fun s u h A => WP.mono (dPtrs₁_inv h A) fun v ⟨z, z9⟩ => (⟨_, _, z, z9⟩ : PZ0 s v)) ?_
  refine RelCT.seq (rel_step [.r11, .r9] (by taint_decide)
    (fun a b ⟨_, _, za, a9⟩ ⟨_, _, zb, b9⟩ => ⟨by rw [za.post.sp, zb.post.sp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [za.r11, zb.r11, e.scA_eq]
      · rw [a9, b9, e.r]⟩)
    fun s u h ⟨_, _, z, z9⟩ => WP.mono (zeroLoop_ok h z z9) fun v hv => (⟨_, _, hv⟩ : PZ s v)) ?_
  refine RelCT.seq (rel_step [.r12] (by taint_decide)
    (fun a b ⟨_, _, za⟩ ⟨_, _, zb⟩ => ⟨by rw [za.post.sp, zb.post.sp, e.fb_eq], fun r hr => by
      rw [List.mem_singleton.mp hr, za.r12, zb.r12, e.fb_eq]⟩)
    fun s u h ⟨_, _, z⟩ => WP.mono (dPtrs₂_inv h z) fun v ⟨c, c9⟩ => (⟨_, _, c, c9⟩ : PC0 s v)) ?_
  refine rel_step [.r10, .r11, .r9] (by taint_decide)
    (fun a b ⟨_, _, ca, a9⟩ ⟨_, _, cb, b9⟩ => ⟨by rw [ca.post.sp, cb.post.sp, e.fb_eq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [ca.r10, cb.r10, e.r]
      · rw [ca.r11, cb.r11, e.r, e.arg, e.scA_eq]
      · rw [a9, b9, e.arg]⟩)
    fun s u h ⟨_, _, c, c9⟩ => WP.mono (copyLoop_ok h c c9) fun v hv => (⟨_, _, cinv_db h hv⟩ : PDB s v)

end

end VG.Proof.RsaPkcs1Enc.PPC64LE.Dec
