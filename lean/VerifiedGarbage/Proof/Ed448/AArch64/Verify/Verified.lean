import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Main
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Ed448 verification on AArch64: `Verified`

Correctness including the ABI (`verify_ok`), for any implementation `v` of
the Keccak permutation, given `EqOk` (which the generic file passes in, from
`VerifyVerified.lean`). Constant time in everything but the pointers and lengths:
the branch on `ctxlen` is on a public length; in the frame's body, two runs
whose pointers and lengths agree have the same layout, so they are related
by `Whole.Two`. The blocks address only the stack and `scratch`, from
registers that agree (the taint analysis); each call is of constant-time
code (the sponge functions for `v`, `vg_ed448_scalar_reduce`,
`vg_ed448_verify_equation`, all constant time in their buffers' contents)
whose public data, its pointers, lengths and the sponge's positions, agree.
-/

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Two WCtx srcValue zeroSt_ct kabs_ct kpad_ct ksqz_ct reduce_ct equation_ct
  ofNat_toNat64 st_within ks_within)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

/-- The arguments of `vg_ed448_scalar_reduce`. -/
def reduceVal (L : Lay) : Reg → Addr
  | .x0 => L.E + BitVec.ofNat 64 fK
  | .x1 => L.E + BitVec.ofNat 64 fH
  | _ => L.scr

/-- The arguments of `vg_ed448_verify_equation`. -/
def equationVal (L : Lay) : Reg → Addr
  | .x0 => L.pk
  | .x1 => L.sig
  | .x2 => L.E + BitVec.ofNat 64 fK
  | _ => L.scr

/-- The positions of the sponge after each absorption. -/
abbrev q1 : Nat := (0 + 10) % 136
abbrev q2 (L : Lay) : Nat := (q1 + L.ctxLen.toNat) % 136
abbrev q3 (L : Lay) : Nat := (q2 L + 57) % 136
abbrev q4 (L : Lay) : Nat := (q3 L + 57) % 136
abbrev q5 (L : Lay) : Nat := (q4 L + L.len.toNat) % 136

theorem hash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (Impl.Ed448.AArch64.Verify.hash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := env_ok hL
  have hs := scrOk hL
  have z := zeroSt_ct hV hs ha₁ ha₂ (P := fun _ => True) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (by taint_decide)
  have k1 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := .val (.frame fHdr))
    (len := .val (.const 10)) (pos := .val (.const 0)) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl (by taint_decide) (P := fun _ => True)
    (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (q := 0) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (by decide) (by decide) (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
  have k2 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aCtx)
    (len := aCtxLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.ctx) (n := L.ctxLen.toNat) (q := q1)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 1) (by decide) _)
    (fun hm hc _ => (arg_src hL hc.1 hm (j := 2) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm)
    (fun _ _ hp => hp) (by decide) L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs]))
    (hL.cc.sub_right (st_within L.scr).sub) (hL.cc.sub_right (ks_within L.scr).sub) hL.cx
  have k3 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aSig)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.sig) (n := 57) (q := q2 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 5) (by decide) _) (fun _ _ _ => rfl)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) (by decide)
    (.inr ⟨L.SIG, by simp [Lay.env, Lay.inputs], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩)
    ((hL.sc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    ((hL.sc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    (hL.cs.sub_right (Region.sub_prefix (by decide)))
  have k4 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aPk)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.pk) (n := 57) (q := q3 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 0) (by decide) _) (fun _ _ _ => rfl)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) (by decide) (in_readable L.PK (by simp [Lay.inputs]))
    (hL.pc.sub_right (st_within L.scr).sub) (hL.pc.sub_right (ks_within L.scr).sub) hL.cp
  have k5 := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aMsg)
    (len := aLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.msg) (n := L.len.toNat) (q := q4 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 3) (by decide) _)
    (fun hm hc _ => (arg_src hL hc.1 hm (j := 4) (by decide) _).trans (ofNat_toNat64 L.len).symm)
    (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) L.len.isLt (in_readable L.MSG (by simp [Lay.inputs]))
    (hL.mc.sub_right (st_within L.scr).sub) (hL.mc.sub_right (ks_within L.scr).sub) hL.cm
  have p := kpad_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (pos := .ret) trivial
    (by taint_decide) (q := q5 L) (fun _ _ hp => hp) (Nat.mod_lt _ (by decide))
  have q := ksqz_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (out := .val (.frame fH))
    (show fH < 4096 by decide) rfl (by taint_decide) (P := fun _ => True) (op := L.E + BitVec.ofNat 64 fH)
    (fun _ _ _ => rfl)
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fScr, fHdr, fH]) (by simp [fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
  exact z.seq (k1.seq (k2.seq (k3.seq (k4.seq (k5.seq (p.seq q))))))

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk)
    (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.scr ∧
        a.syms Impl.X448.AArch64.Base.combSym = L.T) ∧
      (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.scr ∧ b.syms Impl.X448.AArch64.Base.combSym = L.T))
      (body v.callee) fun _ _ => True := by
  have hV := env_ok hL
  have hs := scrOk hL
  have e : RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.scr ∧
        a.syms Impl.X448.AArch64.Base.combSym = L.T) ∧
      (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.scr ∧ b.syms Impl.X448.AArch64.Base.combSym = L.T))
      (.block entry) (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
    VG.Proof.Ed25519.AArch64.Whole.rel_wp
      (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide))
      (fun _ h => WP.mono (entry_ok hL h.1 ha₁ h.2.1 h.2.2) fun _ hu => ⟨hu, trivial⟩)
      (fun _ h => WP.mono (entry_ok hL h.1 ha₂ h.2.1 h.2.2) fun _ hu => ⟨hu, trivial⟩)
  have r := reduce_ct hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := reduceArgs)
    (by decide) (by simp [reduceArgs, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fK, fH, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (reduceVal L)
    (fun _ hc _ p hp => by
      simp only [reduceArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rfl
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (k_apart L)) (scr_writable L) (Q := fun _ => True)
    (fun _ hc _ => WP.mono (reduce_step hL hc) fun _ hu => ⟨hu.1, trivial⟩)
  have q := equation_ct hQ hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := equationArgs)
    (by decide) (by simp [equationArgs, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, aPk, aSig, fK, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (equationVal L)
    (fun hm hc _ p hp => by
      simp only [equationArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact arg_src hL hc.1 hm (j := 0) (by decide) _
      · exact arg_src hL hc.1 hm (j := 5) (by decide) _
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) hL.pc hL.sc (fr_scr hL (by decide)) hL.nc
    (in_readable L.PK (by simp [Lay.inputs])) (in_readable L.SIG (by simp [Lay.inputs]))
    (.inl ⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩) (scr_writable L) (fun h => h.2) (Q := fun _ => True)
    (fun hm hc _ => WP.mono (equation_step hQ hL hc hm) fun _ hu => ⟨hu.1, trivial⟩)
  exact (e.seq ((hash_ct v hL ha₁ ha₂).seq (r.seq q))).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem lay_eq {s t : State} (hp : vLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5, h6, hsy⟩ := hp
  simp only [lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2, h3, h4, h5, h6, hsy]

/-- The frame and its body, for a context shorter than 256 bytes. -/
theorem wrap_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk) :
    ConstantTime isa (fun s => vLocal.pre s ∧ (s.gpr .x2).toNat < 256) vLocal.pub
      (Impl.Ed25519.AArch64.Whole.wrap (body v.callee)) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v hQ (lay_ok hs.1 hs.2) (entry_ctx hs.1 hp) (entry_args hs.1 hp) (entry_x6 hp)
      (entry_syms hp)) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx0 (lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) := he ▸ entry_ctx ht.1 hqb
    have hqa : Args (lay s) q.mem := he ▸ entry_args ht.1 hqb
    have hq6 : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).gpr .x6 = (lay s).scr := he ▸ entry_x6 hqb
    have hqs : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).syms Impl.X448.AArch64.Base.combSym = (lay s).T :=
      he ▸ entry_syms hqb
    exact ⟨(body_ct v hQ (lay_ok hs.1 hs.2) (entry_args hs.1 hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs.1 hpa, entry_x6 hpa, entry_syms hpa⟩, ⟨hq, hq6, hqs⟩⟩ ea eb).1, trivial⟩

theorem verify_ct (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk) :
    ConstantTime isa vLocal.pre vLocal.pub (verifyWith v.callee) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have hl := (RelCT.taint (A := taint) (P := fun s₁ s₂ => vLocal.pre s₁ ∧ vLocal.pre s₂ ∧ vLocal.pub s₁ s₂)
    (c := .block [.lsr .x .x9 .x2 8]) (Taint.ofRegs [.x2])
    (fun _ _ h => ⟨h.2.2.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst hr
      exact h.2.2.2.2.2.1⟩) (by taint_decide)).wpDep (F := LsrPost) fun s₁ s₂ _ => ⟨lsr_ok s₁, lsr_ok s₂⟩
  refine hl.seq (RelCT.ite (fun a b ⟨_, σ₁, σ₂, ⟨_, _, hp⟩, h₁, h₂⟩ => ?_) ?_ ?_)
  · simp only [eval, State.read, h₁.1, h₂.1, hp.2.2.2.1]
  · intro a b ta tb a' b' ⟨⟨_, σ₁, σ₂, ⟨p₁, p₂, hp⟩, h₁, h₂⟩, hc⟩ ea eb
    have hz : ∀ {σ t : State}, LsrPost σ t → isa.eval (.zero .x .x9) t = some true →
        (t.gpr .x2).toNat < 256 := fun h hc => by
      rw [lsr_x2 h]
      refine (lsr_zero h).1 ?_
      simpa [eval, State.read] using hc
    have hc₂ : isa.eval (.zero .x .x9) b = some true := by
      rw [← hc]; simp only [eval, State.read, h₁.1, h₂.1, hp.2.2.2.1]
    exact ⟨wrap_ct v hQ _ _ _ _ _ _ ⟨lsr_pre p₁ h₁, hz h₁ hc⟩ ⟨lsr_pre p₂ h₂, hz h₂ hc₂⟩
      (lsr_pub hp h₁ h₂) ea eb, trivial⟩
  · exact VG.Proof.Ed25519.AArch64.Whole.block_rel
      (fun _ _ ⟨⟨_, _, _, ⟨_, _, hp⟩, h₁, h₂⟩, _⟩ => h₁.2.2.2.2.2.1.trans (hp.1.trans h₂.2.2.2.2.2.1.symm))
      (by taint_decide)

open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)
open VG.Proof.X448.AArch64.Base (combWords_length satMem satMem_held)

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0 | .x3 => 0x3000 | .x4 => 0 | .x5 => 0x4000
    | .x6 => 0x6000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := [⟨0x1000, 57⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 114⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x6000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x0, 57⟩, ⟨s.gpr .x1, (s.gpr .x2).toNat⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.gpr .x5, 114⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x6, 8192⟩])
    (hheld : ∀ i < combWords.length,
      s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0)
    (hfit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hrest : (⟨s.gpr .x0, 57⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (⟨s.gpr .x1, (s.gpr .x2).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (⟨s.gpr .x5, 114⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 57⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, (s.gpr .x2).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x5, 114⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x6, 8192⟩ ∧
      (s.gpr .x0).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧ (s.gpr .x5).toNat + 114 ≤ 2 ^ 64 ∧
      (s.gpr .x6).toNat + 8192 ≤ 2 ^ 64) :
    (Spec.Ed448.verifyContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
    Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
    VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14⟩ := hrest
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, by rw [hrd]; rfl, hw, r1, r2, r3, r4, r5, r6, r7,
    r8, r9, r10, r11, r12, r13, r14⟩

theorem sat : ∃ s, (Spec.Ed448.verifyContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  have hl := combWords_length
  refine ⟨satState, spec_pre (by decide) (by rw [hl]; rfl) rfl satMem_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) ?_⟩
  · rw [hl]
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide

theorem verify_implies : vLocal.Implies
    (Spec.Ed448.verifyContract (AArch64.abi.withConsts combConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, ht, hw, pc, cc, mc, sc, kp, kx, km, ks, kc, np, -, -, ns, nc⟩ := h
    refine ⟨?_, hw, pc, cc, mc, sc, kp, kx, km, ks, kc, np, ns, nc, hsp, held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post s t _ h := by
    sig_post [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts]
    change t.gpr .x0 = _ at h
    rw [h]
    split <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed448.verifyContract, Spec.Ed448.verifySig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts] at h
    obtain ⟨sp, hsy, -, h0, h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨sp, h0, h1, h2, h3, h4, h5, h6, hsy⟩
  sat := sat

theorem verify_verified (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.EqOk) :
    Verified AArch64.target (verifyWith v.callee)
      (Spec.Ed448.verifyContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => verify_ok v hQ h) (verify_ct v hQ) (.refl verify_implies.sat_left))
    verify_implies

end VG.Proof.Ed448.AArch64.Verify
