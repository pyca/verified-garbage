import VerifiedGarbage.Proof.Ed448.AArch64.SignCached.Main
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.CallsCT
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ConstMem

/-!
# Ed448 signing with a cached public key on AArch64: `Verified`

Correctness including the ABI (`signCached_ok`), for any implementation `v`
of the Keccak permutation, given that `vg_ed448_scalar_base` meets
its contract in constant time (`BaseOk`, which the generic file passes in). Constant time in every buffer's contents: two runs whose
pointers and lengths agree have the same layout, so in the frame's body they
are related by `Whole.Two`. The blocks address only the stack and
`scratch`, from registers that agree (the taint analysis); each call is of
constant-time code (the sponge functions for `v`, `vg_ed448_scalar_reduce`,
`vg_ed448_scalar_base`, `vg_ed448_scalar_mul_add`) whose public data, its
pointers, lengths and the sponge's positions, agree.
-/

namespace VG.Proof.Ed448.AArch64.SignCached

open VG VG.AArch64 VG.Impl.Ed448.AArch64.SignCached
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Two WCtx srcValue zeroSt_ct kabs_ct kpad_ct ksqz_ct reduce_ct base_ct
  mulAdd_ct block_ct ofNat_toNat64 st_within ks_within)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK ck_frame)

variable {L : Lay} {g₁ g₂ : Reg → Addr} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

/-- The positions of the sponge after each absorption. -/
abbrev q1 : Nat := (0 + 10) % 136
abbrev q2 (L : Lay) : Nat := (q1 + L.ctxLen.toNat) % 136
abbrev q3 (L : Lay) : Nat := (q2 L + 57) % 136
abbrev q4 (L : Lay) : Nat := (q3 L + 57) % 136

theorem sqz_apart (L : Lay) : VG.Proof.Ed448.AArch64.Whole.Apart L.env ⟨L.E + BitVec.ofNat 64 fH, 114⟩ :=
  fr_apart (by decide) (by decide)

theorem seedHash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (seedHash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := env_ok hL
  have hs := scrOk hL
  have z := zeroSt_ct hV hs ha₁ ha₂ (P := fun _ => True) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂)
    (by taint_decide)
  have k := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aSeed)
    (len := .val (.const 57)) (pos := .val (.const 0)) ⟨by decide, by decide⟩ (show 57 < 65536 by decide)
    (show 0 < 65536 by decide) rfl rfl (by taint_decide) (P := fun _ => True) (dp := L.seed) (n := 57) (q := 0)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 1) (by decide) _) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (by decide) (by decide) (in_readable L.SEED (by simp [Lay.inputs]))
    (hL.sc.sub_right (st_within L.scr).sub) (hL.sc.sub_right (ks_within L.scr).sub) hL.cs
  have p := kpad_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (pos := .ret) trivial
    (by taint_decide) (q := (0 + 57) % 136) (fun _ _ hp => hp) (by decide)
  have q := ksqz_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (out := .val (.frame fH))
    (show fH < 4096 by decide) rfl (by taint_decide) (P := fun _ => True) (op := L.E + BitVec.ofNat 64 fH)
    (fun _ _ _ => rfl) (.inl (sqz_apart L)) (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
  exact z.seq (k.seq (p.seq q))

/-- The state zeroed, then `dom4(0, C)`: the header and the context, then `rest`. -/
theorem dom_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂)
    {rest : Prog isa}
    (hr : RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun u => u.gpr .x0 = BitVec.ofNat 64 (q2 L)) rest
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True)
      (.seq (VG.Impl.Ed448.AArch64.Whole.zeroSt fScr) <|
        .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr (.val (.frame fHdr)) (.val (.const 10))
          (.val (.const 0))) <|
        .seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr aCtx aCtxLen .ret) rest)
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
    (fun hm hc _ => arg_src hL hc.1 hm (j := 3) (by decide) _)
    (fun hm hc _ => (arg_src hL hc.1 hm (j := 4) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm)
    (fun _ _ hp => hp) (by decide) L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs]))
    (hL.xc.sub_right (st_within L.scr).sub) (hL.xc.sub_right (ks_within L.scr).sub) hL.cx
  exact z.seq (k1.seq (k2.seq hr))

/-- The message, the padding and the output, from the position `q`. -/
theorem tail_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂)
    {q : Nat} (hq : q < 136) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun u => u.gpr .x0 = BitVec.ofNat 64 q)
      (.seq (VG.Impl.Ed448.AArch64.Whole.kabs v.callee fScr aMsg aLen .ret) <|
        .seq (VG.Impl.Ed448.AArch64.Whole.kpad v.callee fScr .ret)
          (VG.Impl.Ed448.AArch64.Whole.ksqz v.callee fScr (.val (.frame fH))))
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := env_ok hL
  have hs := scrOk hL
  have k := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aMsg)
    (len := aLen) (pos := .ret) ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide⟩ trivial rfl rfl
    (by taint_decide) (dp := L.msg) (n := L.len.toNat) (q := q)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 5) (by decide) _) (fun _ hc _ => len_src hc)
    (fun _ _ hp => hp) hq L.len.isLt (in_readable L.MSG (by simp [Lay.inputs]))
    (hL.mc.sub_right (st_within L.scr).sub) (hL.mc.sub_right (ks_within L.scr).sub) hL.cm
  have p := kpad_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (pos := .ret) trivial
    (by taint_decide) (q := (q + L.len.toNat) % 136) (fun _ _ hp => hp) (Nat.mod_lt _ (by decide))
  have o := ksqz_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (out := .val (.frame fH))
    (show fH < 4096 by decide) rfl (by taint_decide) (P := fun _ => True) (op := L.E + BitVec.ofNat 64 fH)
    (fun _ _ _ => rfl) (.inl (sqz_apart L)) (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
  exact k.seq (p.seq o)

theorem nonceHash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (nonceHash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := env_ok hL
  have hs := scrOk hL
  have x := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := .val (.frame (fH + 57)))
    (len := .val (.const 57)) (pos := .ret) (show fH + 57 < 4096 by decide) (show 57 < 65536 by decide) trivial
    rfl rfl (by taint_decide) (dp := L.E + BitVec.ofNat 64 (fH + 57)) (n := 57) (q := q2 L)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ hp => hp) (Nat.mod_lt _ (by decide)) (by decide)
    (.inl ⟨fH + 57, rfl, show fH + 57 + 57 ≤ 256 by decide⟩) (fr_st hL (by decide)) (fr_ks hL (by decide))
    (ck_frame (by decide))
  have t := tail_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) v hL ha₁ ha₂ (q := q3 L) (Nat.mod_lt _ (by decide))
  exact dom_ct v hL ha₁ ha₂ (x.seq t)

theorem chalHash_ct (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (chalHash v.callee)
      (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  have hV := env_ok hL
  have hs := scrOk hL
  have r := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aOut)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.out) (n := 57) (q := q2 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 0) (by decide) _) (fun _ _ _ => rfl) (fun _ _ hp => hp)
    (Nat.mod_lt _ (by decide)) (by decide) (.inr ⟨L.OUT, by simp [Lay.env], outR_within L⟩)
    (hL.oc.sub_left (outR_within L).sub |>.sub_right (st_within L.scr).sub)
    (hL.oc.sub_left (outR_within L).sub |>.sub_right (ks_within L.scr).sub)
    (hL.co.sub_right (outR_within L).sub)
  have k := kabs_ct v hV hs ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (src := aPk)
    (len := .val (.const 57)) (pos := .ret) ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl
    (by taint_decide) (dp := L.pk) (n := 57) (q := q3 L)
    (fun hm hc _ => arg_src hL hc.1 hm (j := 2) (by decide) _) (fun _ _ _ => rfl) (fun _ _ hp => hp)
    (Nat.mod_lt _ (by decide)) (by decide) (in_readable L.PK (by simp [Lay.inputs]))
    (hL.pc.sub_right (st_within L.scr).sub) (hL.pc.sub_right (ks_within L.scr).sub) hL.cp
  have t := tail_ct (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) v hL ha₁ ha₂ (q := q4 L) (Nat.mod_lt _ (by decide))
  exact dom_ct v hL ha₁ ha₂ (r.seq (k.seq t))

/-- The arguments of the calls. -/
def reduceRVal (L : Lay) : Reg → Addr
  | .x0 => L.out + BitVec.ofNat 64 57
  | .x1 => L.E + BitVec.ofNat 64 fH
  | _ => L.scr

def baseVal (L : Lay) : Reg → Addr
  | .x0 => L.out
  | .x1 => L.out + BitVec.ofNat 64 57
  | _ => L.scr

def reduceKVal (L : Lay) : Reg → Addr
  | .x0 => L.E + BitVec.ofNat 64 fH
  | .x1 => L.E + BitVec.ofNat 64 fH
  | _ => L.scr

def mulAddVal (L : Lay) : Reg → Addr
  | .x0 => L.out + BitVec.ofNat 64 57
  | .x1 => L.out + BitVec.ofNat 64 57
  | .x2 => L.E + BitVec.ofNat 64 fH
  | .x3 => L.E + BitVec.ofNat 64 fS
  | _ => L.scr

theorem body_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) (hL : L.Ok)
    (ha₁ : Args L m₁) (ha₂ : Args L m₂) :
    RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.len ∧ a.gpr .x7 = L.scr ∧
        a.syms Impl.X448.AArch64.Base.combSym = L.T) ∧
      (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.len ∧ b.gpr .x7 = L.scr ∧
        b.syms Impl.X448.AArch64.Base.combSym = L.T)) (body v.callee) fun _ _ => True := by
  have hV := env_ok hL
  have hs := scrOk hL
  have e : RelCT isa (fun a b => (Ctx0 L g₁ v₁ m₁ a ∧ a.gpr .x6 = L.len ∧ a.gpr .x7 = L.scr ∧
        a.syms Impl.X448.AArch64.Base.combSym = L.T) ∧
      (Ctx0 L g₂ v₂ m₂ b ∧ b.gpr .x6 = L.len ∧ b.gpr .x7 = L.scr ∧
        b.syms Impl.X448.AArch64.Base.combSym = L.T))
      (.block entry) (Two L.env g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) :=
    VG.Proof.Ed25519.AArch64.Whole.rel_wp
      (VG.Proof.Ed25519.AArch64.Whole.block_rel (fun _ _ h => h.1.1.sp.trans h.2.1.sp.symm) (by taint_decide))
      (fun _ h => WP.mono (entry_ok hL h.1 ha₁ h.2.1 h.2.2.1 h.2.2.2) fun _ hu => ⟨hu, trivial⟩)
      (fun _ h => WP.mono (entry_ok hL h.1 ha₂ h.2.1 h.2.2.1 h.2.2.2) fun _ hu => ⟨hu, trivial⟩)
  have pr := block_ct (V := L.env) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) ha₁ ha₂
    (P := fun _ => True) (Q := fun _ => True) (is := prune) (by taint_decide)
    fun _ hc _ => WP.mono (prune_step hL hc (hb := Spec.Sha3.bytesAt _ (L.E + BitVec.ofNat 64 fH) 114) rfl)
      fun _ hu => ⟨hu.1, trivial⟩
  have rr := reduce_ct hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := reduceRArgs)
    (by decide) (by simp [reduceRArgs, aR, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (reduceRVal L)
    (fun hm hc _ p hp => by
      simp only [reduceRArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact outS_src hL hc hm _
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (outS_writable L) (scr_writable L) (Q := fun _ => True)
    (fun hm hc _ => WP.mono (reduceR_step hL hc hm) fun _ hu => ⟨hu.1, trivial⟩)
  have bs := base_ct hb hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := baseArgs)
    (by decide) (by simp [baseArgs, aOut, aR, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (baseVal L)
    (fun hm hc _ p hp => by
      simp only [baseArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact arg_src hL hc.1 hm (j := 0) (by decide) _
      · exact outS_src hL hc hm _
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (hL.oc.sub_left (outR_within L).sub) (hL.oc.sub_left (outS_within L).sub) hL.nc
    (.inr ⟨L.OUT, by simp [Lay.env], outS_within L⟩) (outR_writable L) (scr_writable L) (fun h => h.2)
    (Q := fun _ => True) (fun hm hc _ => WP.mono (base_step hb hL hc hm) fun _ hu => ⟨hu.1, trivial⟩)
  have rk := reduce_ct hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := reduceKArgs)
    (by decide) (by simp [reduceKArgs, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fH, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (reduceKVal L)
    (fun _ hc _ p hp => by
      simp only [reduceKArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · rfl
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (fr_apart (by decide) (by decide))) (scr_writable L) (Q := fun _ => True)
    (fun _ hc _ => WP.mono (reduceK_step hL hc) fun _ hu => ⟨hu.1, trivial⟩)
  have ma := mulAdd_ct hV ha₁ ha₂ (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) (args := mulAddArgs)
    (by decide) (by simp [mulAddArgs, aR, VG.Proof.Ed448.AArch64.Whole.srcValid,
      VG.Proof.Ed25519.AArch64.Whole.valid, fH, fS, fScr]) rfl (by decide)
    (by decide) (by taint_decide) (P := fun _ => True) (mulAddVal L)
    (fun hm hc _ p hp => by
      simp only [mulAddArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact outS_src hL hc hm _
      · exact outS_src hL hc hm _
      · rfl
      · rfl
      · exact (hs.loc hc _ 0).trans (BitVec.add_zero _))
    (by decide) (hL.oc.sub_left (outS_within L).sub) (fr_scr hL (by decide)) (fr_scr hL (by decide))
    (.inr ⟨L.OUT, by simp [Lay.env], outS_within L⟩) (.inl ⟨fH, rfl, show fH + 57 ≤ 256 by decide⟩)
    (.inl ⟨fS, rfl, show fS + 57 ≤ 256 by decide⟩) (outS_writable L) (scr_writable L) (Q := fun _ => True)
    (fun hm hc _ => WP.mono (mulAdd_step hL hc hm) fun _ hu => ⟨hu.1, trivial⟩)
  have wp := block_ct (V := L.env) (g₁ := g₁) (g₂ := g₂) (v₁ := v₁) (v₂ := v₂) ha₁ ha₂
    (P := fun _ => True) (Q := fun _ => True) (is := wipe) (by taint_decide)
    fun _ hc _ => WP.mono (wipe_step hL hc) fun _ hu => ⟨hu.1, trivial⟩
  exact (e.seq ((seedHash_ct v hL ha₁ ha₂).seq (pr.seq ((nonceHash_ct v hL ha₁ ha₂).seq (rr.seq (bs.seq
    ((chalHash_ct v hL ha₁ ha₂).seq (rk.seq (ma.seq wp))))))))).mono (fun _ _ h => h) fun _ _ _ => trivial

theorem lay_eq {s t : State} (hp : scLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5, h6, h7, hsy⟩ := hp
  simp only [lay, VG.Proof.Ed25519.AArch64.Whole.base, sp, h0, h1, h2, h3, h4, h5, h6, h7, hsy]

theorem signCached_ct (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    ConstantTime isa scLocal.pre scLocal.pub (signCachedWith v.callee) := by
  refine VG.Proof.Ed25519.AArch64.Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (signCached_ok_body v hb hs hp) fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx0 (lay s) t.gpr t.v q.mem (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)) := he ▸ entry_ctx ht hqb
    have hqa : Args (lay s) q.mem := he ▸ entry_args ht hqb
    have hq6 : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).gpr .x6 = (lay s).len := he ▸ entry_x6 hqb
    have hq7 : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).gpr .x7 = (lay s).scr := he ▸ entry_x7 hqb
    have hqs : (q.withRegions (VG.Proof.Ed25519.AArch64.Whole.bodyRd t)
        (VG.Proof.Ed25519.AArch64.Whole.bodyWr t)).syms Impl.X448.AArch64.Base.combSym = (lay s).T :=
      he ▸ entry_syms hqb
    exact ⟨(body_ct v hb (lay_ok hs) (entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨⟨entry_ctx hs hpa, entry_x6 hpa, entry_x7 hpa, entry_syms hpa⟩, ⟨hq, hq6, hq7, hqs⟩⟩ ea eb).1, trivial⟩

/-! ## A state satisfying the precondition -/

def satSeed : List Byte := Spec.Ed448.bytesAt (fun _ => 0) 0x2000 57
def satKey : List Byte := Spec.Ed448.publicKey satSeed

theorem satKey_length : satKey.length = 57 := by
  simp only [satKey, Spec.Ed448.publicKey, Spec.Ed448.encodePoint, Spec.Ed448.encodeLE, List.length_map,
    List.length_range]

/-- The public key at `0x3000`, and 0 elsewhere. -/
def satMem (a : Addr) : Byte :=
  if a.toNat < 0x3000 ∨ 0x3039 ≤ a.toNat then 0 else satKey[a.toNat - 0x3000]?.getD 0

theorem sat_seed : Spec.Ed448.bytesAt satMem 0x2000 57 = satSeed := by
  unfold satSeed Spec.Ed448.bytesAt
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have ha : ((0x2000 : Addr) + BitVec.ofNat 64 i).toNat = 0x2000 + i := by
    change (0x2000 + i % 2 ^ 64) % 2 ^ 64 = 0x2000 + i
    omega
  simp only [satMem, ha, show 0x2000 + i < 0x3000 from by omega, true_or, ↓reduceIte]

theorem sat_key : Spec.Ed448.bytesAt satMem 0x3000 57 = satKey := by
  apply List.ext_getElem
  · simp only [Spec.Ed448.bytesAt, List.length_map, List.length_range, satKey_length]
  · intro i hi hj
    have hi' : i < 57 := by simpa only [Spec.Ed448.bytesAt, List.length_map, List.length_range] using hi
    have ha : ((0x3000 : Addr) + BitVec.ofNat 64 i).toNat = 0x3000 + i := by
      change (0x3000 + i % 2 ^ 64) % 2 ^ 64 = 0x3000 + i
      omega
    simp only [Spec.Ed448.bytesAt, List.getElem_map, List.getElem_range, satMem, ha,
      show ¬ (0x3000 + i < 0x3000 ∨ 0x3039 ≤ 0x3000 + i) from by omega, ↓reduceIte, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem hj, Option.getD_some]

open VG.Impl.X448.AArch64.Base (combSym combWords combConsts)
open VG.Proof.X448.AArch64.Base (combWords_length)

/-- The public key at `0x3000` and the comb's tables at `0x100000` (irreducible: unfolding it in a
definitional check would evaluate the tables). -/
@[irreducible] def satMemT : Mem := fun a =>
  if 0x100000 ≤ a.toNat then constMem 0x100000 combWords a else satMem a

theorem satMemT_low {a : Addr} (h : a.toNat < 0x100000) : satMemT a = satMem a := by
  unfold satMemT; simp only [show ¬ 0x100000 ≤ a.toNat by omega, ↓reduceIte]

theorem satMemT_held : ∀ i < combWords.length,
    satMemT.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0 := by
  intro i hi
  have hl := combWords_length
  rw [← constMem_held 0x100000 combWords (by omega) i hi]
  refine Mem.readW_congr fun b hb => ?_
  have e : ((0x100000 : Addr) + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b).toNat = 0x100000 + 8 * i + b := by
    have h0 : (0x100000 : Addr).toNat = 0x100000 := rfl
    rw [Offset.add_add, BitVec.toNat_add, BitVec.toNat_ofNat, h0,
      Nat.mod_eq_of_lt (a := 8 * i + b) (by omega)]
    omega
  unfold satMemT
  simp only [e, show 0x100000 ≤ 0x100000 + 8 * i + b by omega, ↓reduceIte]

theorem satT_bytes {p : Addr} (hp : p.toNat + 57 < 0x100000) :
    Spec.Ed448.bytesAt satMemT p 57 = Spec.Ed448.bytesAt satMem p 57 := by
  unfold Spec.Ed448.bytesAt
  refine List.map_congr_left fun i hi => satMemT_low ?_
  have := List.mem_range.mp hi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega)]
  omega

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x5 => 0x5000 | .x7 => 0x10000
    | _ => 0
  sp := 0x20000
  mem := satMemT
  rd := [⟨0x2000, 57⟩, ⟨0x3000, 57⟩, ⟨0x4000, 0⟩, ⟨0x5000, 0⟩, ⟨0x100000, 58368⟩]
  wr := [⟨0x1000, 114⟩, ⟨0x10000, 8192⟩]
  syms _ := 0x100000

/-- The shared contract's precondition, from its facts. -/
theorem spec_pre {s : State} (hsp : 352 ≤ s.sp.toNat)
    (hrd : s.rd = [⟨s.gpr .x1, 57⟩, ⟨s.gpr .x2, 57⟩, ⟨s.gpr .x3, (s.gpr .x4).toNat⟩,
      ⟨s.gpr .x5, (s.gpr .x6).toNat⟩, ⟨s.syms combSym, 8 * combWords.length⟩])
    (hw : s.wr = [⟨s.gpr .x0, 114⟩, ⟨s.gpr .x7, 8192⟩])
    (hheld : ∀ i < combWords.length,
      s.mem.readW (s.syms combSym + BitVec.ofNat 64 (8 * i)) 64 = combWords.getD i 0)
    (hfit : (s.syms combSym).toNat + 8 * combWords.length ≤ 2 ^ 64)
    (hdw : ∀ r ∈ s.wr, Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ r)
    (hds : Region.Disjoint ⟨s.syms combSym, 8 * combWords.length⟩ ⟨s.sp - 352#64, 352⟩)
    (hrest : (⟨s.gpr .x0, 114⟩ : Region).Disjoint ⟨s.gpr .x1, 57⟩ ∧
      (⟨s.gpr .x0, 114⟩ : Region).Disjoint ⟨s.gpr .x2, 57⟩ ∧
      (⟨s.gpr .x0, 114⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
      (⟨s.gpr .x0, 114⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩ ∧
      (⟨s.gpr .x0, 114⟩ : Region).Disjoint ⟨s.gpr .x7, 8192⟩ ∧
      (⟨s.gpr .x1, 57⟩ : Region).Disjoint ⟨s.gpr .x7, 8192⟩ ∧
      (⟨s.gpr .x2, 57⟩ : Region).Disjoint ⟨s.gpr .x7, 8192⟩ ∧
      (⟨s.gpr .x3, (s.gpr .x4).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, 8192⟩ ∧
      (⟨s.gpr .x5, (s.gpr .x6).toNat⟩ : Region).Disjoint ⟨s.gpr .x7, 8192⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x0, 114⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x1, 57⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x2, 57⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x5, (s.gpr .x6).toNat⟩ ∧
      (⟨s.sp - 352#64, 352⟩ : Region).Disjoint ⟨s.gpr .x7, 8192⟩ ∧
      (s.gpr .x0).toNat + 114 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 57 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + 57 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + 8192 ≤ 2 ^ 64)
    (hpk : Spec.Ed448.bytesAt s.mem (s.gpr .x2) 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt s.mem (s.gpr .x1) 57))
    (hcl : (s.gpr .x4).toNat ≤ 255) :
    (Spec.Ed448.signCachedContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
    Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
    VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
    stackBelow]
  exact ⟨hsp, by rw [hrd]; rfl, hheld, hfit, hdw, hds, by rw [hrd]; rfl, hw, hrest.1, hrest.2.1, hrest.2.2.1,
    hrest.2.2.2.1, hrest.2.2.2.2.1, hrest.2.2.2.2.2.1, hrest.2.2.2.2.2.2.1, hrest.2.2.2.2.2.2.2.1,
    hrest.2.2.2.2.2.2.2.2.1, hrest.2.2.2.2.2.2.2.2.2.1, hrest.2.2.2.2.2.2.2.2.2.2.1,
    hrest.2.2.2.2.2.2.2.2.2.2.2.1, hrest.2.2.2.2.2.2.2.2.2.2.2.2.1, hrest.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hrest.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hrest.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hrest.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hrest.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hrest.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hrest.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hrest.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hpk, hcl⟩

theorem sat : ∃ s, (Spec.Ed448.signCachedContract (AArch64.abi.withConsts combConsts) 352).pre s := by
  have hl := combWords_length
  refine ⟨satState, spec_pre (by decide) (by rw [hl]; rfl) rfl satMemT_held (by rw [hl]; decide) ?_
    (by rw [hl]; exact Region.disjoint_of_sep (by decide)) ?_ ?_ (by decide)⟩
  · rw [hl]
    simp only [satState, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact Region.disjoint_of_sep (by decide)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide
  · change Spec.Ed448.bytesAt satMemT 0x3000 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt satMemT 0x2000 57)
    rw [satT_bytes (by decide), satT_bytes (by decide), sat_seed, sat_key]
    rfl

theorem signCached_implies : scLocal.Implies
    (Spec.Ed448.signCachedContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts) 352) where
  pre s h := by
    sig_pre [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld,
      stackBelow] at h
    obtain ⟨hsp, hd, held, fit, hdw, hds, ht, hw, os, op, ox, om, oc, sc, pc, xc, mc, ko, ks, kp, kx, km, kc,
      no, ns, np, -, -, nc, hpk, cl⟩ := h
    refine ⟨?_, hw, os, op, ox, om, oc, sc, pc, xc, mc, ko, ks, kp, kx, km, kc, no, ns, np, nc, hsp, hpk, cl,
      held, fit, ?_⟩
    · rw [← List.take_append_drop (s.rd.length - 1) s.rd, ht, hd]; rfl
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hdw _ (by rw [hw]; simp)
      · exact hdw _ (by rw [hw]; simp)
      · exact hds
  post := by
    sig_implies_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, scLocal, below, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts]
  pub := by
    sig_implies_pub [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig,
      Spec.Ed448.scratchWords, scLocal, below, AArch64.abi, AArch64.argRegs,
      VG.Proof.X448.AArch64.Base.combConsts_eq, Abi.withConsts]
  sat := sat

theorem signCached_verified (v : Proof.Sha3.AArch64.Permutation) (hb : Proof.Ed448.AArch64.BaseOk) :
    Verified AArch64.target (signCachedWith v.callee)
      (Spec.Ed448.signCachedContract (AArch64.abi.withConsts Impl.X448.AArch64.Base.combConsts) 352) :=
  Verified.of_implies
    (Verified.of_correct (fun _ h => signCached_ok v hb h) (signCached_ct v hb)
      (.refl signCached_implies.sat_left))
    signCached_implies

end VG.Proof.Ed448.AArch64.SignCached
