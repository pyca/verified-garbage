module

public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed448.AArch64.Scalar
public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Local
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
public import VerifiedGarbage.Proof.Ed448.AArch64.Verify.Body
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Sponge
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! ### `Ed448.AArch64.Verify.Calls`, which this module and modules that import it used -/

section

/-! The public verifier's call of the sparse equation, with its smaller static table. -/

@[expose] public section
namespace VG.Proof.Ed448.AArch64.Verify
open VG VG.AArch64
open VG.Proof.Ed448.AArch64.Whole
open VG.Impl.Ed448.AArch64.Sparse (baseSym baseWords)
open VG.Proof.Ed448.AArch64.Sparse (BaseHeld)
open VG.Proof.Ed25519.AArch64.Whole (FR CK Within)
variable {V:Env} {g:Reg → Addr} {vec:VReg → BitVec 128} {m₀:Mem} {u:State}

theorem baseHeld_of (hV : V.Ok) (hcfg:V.sym=baseSym ∧ V.words=baseWords) (hu : WCtx V g vec m₀ u) (hm : TblWords V.T m₀ baseWords) {ws : List Region}
    (hw : ∀ r ∈ ws, Writable V r) (rd wr : List Region) :
    BaseHeld (u.callEntry.withRegions rd wr) ws := by
  have hT : (u.callEntry.withRegions rd wr).syms baseSym = V.T := by rw [←hcfg.1];exact hu.2.2
  refine ⟨fun i hi => ?_, ?_, fun r hr => ?_⟩
  · rw [hT]; have hh:=hu.tbl hV (by rw [hcfg.2];exact hm)
    rw [hcfg.2] at hh
    exact hh i hi
  · rw [hT]; simpa only [hcfg.2] using hV.tfit
  · rw [hT]; simpa only [hcfg.2] using (hw r hr).tbl hV

theorem equation_pre {pk sig ch scr T : Addr} (h0 : u.gpr .x0 = pk) (h1 : u.gpr .x1 = sig)
    (h2 : u.gpr .x2 = ch) (h3 : u.gpr .x3 = scr)
    (hp : Region.Disjoint ⟨pk, 57⟩ ⟨scr, 8192⟩) (hs : Region.Disjoint ⟨sig, 114⟩ ⟨scr, 8192⟩)
    (hc : Region.Disjoint ⟨ch, 57⟩ ⟨scr, 8192⟩) (hn : scr.toNat + 8192 ≤ 2 ^ 64) (hT : u.syms baseSym = T)
    (ht : BaseHeld (u.callEntry.withRegions [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩, TBL T baseWords] [⟨scr, 8192⟩])
      [⟨scr, 8192⟩]) :
    Proof.Ed448.AArch64.Sparse.verifyEquationLocal.pre
      (u.callEntry.withRegions [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩, TBL T baseWords] [⟨scr, 8192⟩]) := by
  have e3 := State.callEntry_gpr u (by decide : Reg.x3 ∉ linkRegs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3, syms_entry, hT]
  exacts [hp, hs, hc, hn, by rw [e3, h3] at *; exact ht]

theorem equation_call (hQ : Proof.Ed448.AArch64.Sparse.EqOk) (hV : V.Ok) (hcfg:V.sym=baseSym ∧ V.words=baseWords)
    (hu : WCtx V g vec m₀ u) {pk sig ch scr : Addr}
    (h0 : u.gpr .x0 = pk) (h1 : u.gpr .x1 = sig) (h2 : u.gpr .x2 = ch) (h3 : u.gpr .x3 = scr)
    (hdp : Region.Disjoint ⟨pk, 57⟩ ⟨scr, 8192⟩) (hds : Region.Disjoint ⟨sig, 114⟩ ⟨scr, 8192⟩)
    (hdc : Region.Disjoint ⟨ch, 57⟩ ⟨scr, 8192⟩) (hn : scr.toNat + 8192 ≤ 2 ^ 64)
    (hrp : Readable V ⟨pk, 57⟩) (hrs : Readable V ⟨sig, 114⟩) (hrc : Readable V ⟨ch, 57⟩)
    (hws : Writable V ⟨scr, 8192⟩) (hm : TblWords V.T m₀ baseWords) :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.AArch64.Sparse.verifyEquation) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      w.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem pk 57)
        (Spec.Ed448.bytesAt u.mem sig 114) (Spec.Ed448.bytesAt u.mem ch 57) then 1 else 0 := by
  have hw : ∀ r ∈ [(⟨scr, 8192⟩ : Region)], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; exact hws
  have hrd : ∀ r ∈ [(⟨pk, 57⟩ : Region), ⟨sig, 114⟩, ⟨ch, 57⟩, TBL V.T baseWords], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    exact hrp
    · exact hrs
    · exact hrc
    · simpa only [hcfg.2] using tbl_readable hV
  refine wcall hV hu (hQ.ok) (noFrames_depth Proof.Ed448.AArch64.Sparse.verifyEquation_noFrames)
    (equation_pre h0 h1 h2 h3 hdp hds hdc hn (by simpa only [hcfg.1] using hu.2.2) (baseHeld_of hV hcfg hu hm hw _ _))
    (covers_rw hrd hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change w.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x0) 57)
    (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 114)
    (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x2) 57) then 1 else 0 at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2] at hp
  exact hp

end VG.Proof.Ed448.AArch64.Verify

end

end

/-! ### `Ed448.AArch64.Verify.Hash`, which this module and modules that import it used -/

section

/-!
# Ed448 verification on AArch64: the hash

`H(dom4(0, C) ‖ R ‖ A ‖ M)` into the locals at `fH` (`hash_ok`): the state
zeroed, the header of `dom4` (kept in the locals), the context, `R`, the
public key and the message absorbed in turn, each from the position the
previous one returned, the padding, and 114 bytes squeezed.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx Kept sigWord srcValue srcValid noRet ScrOk ST KS
  st_within ks_within kabs_chain kpad_ok ksqz_ok zeroSt_ok repr_nil hdr_bytes shake256_eq ofNat_toNat64
  readW_eq_read Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR ARGS CK ck_frame)

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

/-- `"SigEd448" ‖ 0 ‖ ctx_len`, the first ten bytes of `dom4(0, context)`. -/
abbrev hdrBytes (L : Lay) : List Byte :=
  "SigEd448".toList.map (fun ch => BitVec.ofNat 8 ch.toNat) ++ [BitVec.ofNat 8 0, BitVec.ofNat 8 L.ctxLen.toNat]

/-- What is hashed: `dom4(0, C) ‖ R ‖ A ‖ M`. -/
abbrev hashIn (L : Lay) (m : Mem) : List Byte :=
  hdrBytes L ++ Spec.Sha3.bytesAt m L.ctx L.ctxLen.toNat ++ Spec.Sha3.bytesAt m L.sig 57 ++
    Spec.Sha3.bytesAt m L.pk 57 ++ Spec.Sha3.bytesAt m L.msg L.len.toNat

theorem scrOk (hL : L.Ok) : ScrOk L.env fScr L.scr := ⟨by simp [Lay.env], by simp [Lay.env], hL.nc⟩

/-- A region of the locals misses `scratch`. -/
theorem fr_st (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ (ST L.scr) :=
  (hL.kc.sub_left (Offset.sub_base _ h)).sub_right (st_within L.scr).sub
theorem fr_ks (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ (KS L.scr) :=
  (hL.kc.sub_left (Offset.sub_base _ h)).sub_right (ks_within L.scr).sub

theorem within_self (p : Addr) (n : Nat) : Within ⟨p, n⟩ ⟨p, n⟩ := ⟨0, (BitVec.add_zero _).symm, by simp⟩

theorem in_readable (R : Region) (hR : R ∈ L.inputs) :
    Within R (FR L.E) ∨ ∃ R' ∈ L.env.ins ++ L.env.outs, Within R R' :=
  .inr ⟨R, by simp [Lay.env, hR], within_self R.base R.len⟩

/-- The hash. -/
theorem hash_ok (v : Proof.Sha3.AArch64.Permutation) (hL : L.Ok) (hc : WCtx L.env g vec m₀ t)
    (ha : Args L m₀) :
    WP isa (Impl.Ed448.AArch64.Verify.hash v.callee) t fun u => WCtx L.env g vec m₀ u ∧
      Spec.Sha3.bytesAt u.mem (L.E + BitVec.ofNat 64 fH) 114 = Spec.Sha3.shake256 (hashIn L m₀) 114 := by
  have hV := env_ok hL
  have hs := scrOk hL
  -- The state zeroed.
  refine WP.seq (WP.mono (zeroSt_ok hV hs hc) fun t₁ ⟨hc₁, _, hz₁⟩ => ?_)
  -- The header.
  have k0 := hc₁.2.1 (fHdr, sigWord) (by simp [Lay.env])
  have k8 := hc₁.2.1 (fHdr + 8, L.ctxLen <<< 8) (by simp [Lay.env])
  simp only [Lay.env] at k0 k8
  have hb₁ : Spec.Sha3.bytesAt t₁.mem (L.E + BitVec.ofNat 64 fHdr) 10 = hdrBytes L :=
    hdr_bytes _ _ _ hL.cl k0 (by rw [Offset.add_add]; exact k8)
  refine WP.seq (WP.mono (kabs_chain (msg := []) v hV hs hc₁ (src := .val (.frame fHdr)) (len := .val (.const 10))
    (pos := .val (.const 0)) (dp := L.E + BitVec.ofNat 64 fHdr) (n := 10) (show fHdr < 4096 by decide)
    (show 10 < 65536 by decide) (show 0 < 65536 by decide) rfl rfl rfl rfl rfl (by decide)
    (.inl ⟨fHdr, rfl, show fHdr + 10 ≤ 256 by decide⟩) (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))
    (repr_nil hz₁)) fun t₂ ⟨hc₂, _, hr₂, hx₂⟩ => ?_)
  rw [hb₁, List.nil_append] at hr₂ hx₂
  -- The context.
  have a1 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtx = L.ctx := arg_src hL hc₂.1 ha (j := 1) (by decide) _
  have a2 : srcValue L.env.E t₂.mem (t₂.gpr .x0) aCtxLen = BitVec.ofNat 64 L.ctxLen.toNat :=
    (arg_src hL hc₂.1 ha (j := 2) (by decide) _).trans (ofNat_toNat64 L.ctxLen).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₂ (src := aCtx) (len := aCtxLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a1 a2
    hx₂ L.ctxLen.isLt (in_readable L.CTX (by simp [Lay.inputs])) (hL.cc.sub_right (st_within L.scr).sub)
    (hL.cc.sub_right (ks_within L.scr).sub) hL.cx hr₂) fun t₃ ⟨hc₃, _, hr₃, hx₃⟩ => ?_)
  have eC : Spec.Sha3.bytesAt t₂.mem L.ctx L.ctxLen.toNat = Spec.Sha3.bytesAt m₀ L.ctx L.ctxLen.toNat :=
    in_bytes hL hc₂.1 (R := L.CTX) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.ctxLen.isLt)
  rw [eC] at hr₃ hx₃
  -- `R`.
  have a5 : srcValue L.env.E t₃.mem (t₃.gpr .x0) aSig = L.sig := arg_src hL hc₃.1 ha (j := 5) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₃ (src := aSig) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a5 rfl hx₃ (by decide)
    (.inr ⟨L.SIG, by simp [Lay.env, Lay.inputs], ⟨0, (BitVec.add_zero _).symm, by show 0 + 57 ≤ 114; decide⟩⟩)
    ((hL.sc.sub_right (st_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    ((hL.sc.sub_right (ks_within L.scr).sub).sub_left (Region.sub_prefix (by decide)))
    (hL.cs.sub_right (Region.sub_prefix (by decide))) hr₃)
    fun t₄ ⟨hc₄, _, hr₄, hx₄⟩ => ?_)
  have eS : Spec.Sha3.bytesAt t₃.mem L.sig 57 = Spec.Sha3.bytesAt m₀ L.sig 57 :=
    in_bytes hL hc₃.1 (R := L.SIG) (by simp [Lay.inputs]) (show 57 ≤ 114 by decide) (show 114 ≤ 2 ^ 64 by decide)
  rw [eS] at hr₄ hx₄
  -- The public key.
  have a0 : srcValue L.env.E t₄.mem (t₄.gpr .x0) aPk = L.pk := arg_src hL hc₄.1 ha (j := 0) (by decide) _
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₄ (src := aPk) (len := .val (.const 57)) (pos := .ret)
    ⟨by decide, by decide⟩ (show 57 < 65536 by decide) trivial rfl rfl a0 rfl hx₄ (by decide)
    (in_readable L.PK (by simp [Lay.inputs])) (hL.pc.sub_right (st_within L.scr).sub)
    (hL.pc.sub_right (ks_within L.scr).sub) hL.cp hr₄) fun t₅ ⟨hc₅, _, hr₅, hx₅⟩ => ?_)
  have eP : Spec.Sha3.bytesAt t₄.mem L.pk 57 = Spec.Sha3.bytesAt m₀ L.pk 57 :=
    in_bytes hL hc₄.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  rw [eP] at hr₅ hx₅
  -- The message.
  have a3 : srcValue L.env.E t₅.mem (t₅.gpr .x0) aMsg = L.msg := arg_src hL hc₅.1 ha (j := 3) (by decide) _
  have a4 : srcValue L.env.E t₅.mem (t₅.gpr .x0) aLen = BitVec.ofNat 64 L.len.toNat :=
    (arg_src hL hc₅.1 ha (j := 4) (by decide) _).trans (ofNat_toNat64 L.len).symm
  refine WP.seq (WP.mono (kabs_chain v hV hs hc₅ (src := aMsg) (len := aLen) (pos := .ret)
    ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ trivial rfl rfl a3 a4
    hx₅ L.len.isLt (in_readable L.MSG (by simp [Lay.inputs])) (hL.mc.sub_right (st_within L.scr).sub)
    (hL.mc.sub_right (ks_within L.scr).sub) hL.cm hr₅) fun t₆ ⟨hc₆, _, hr₆, hx₆⟩ => ?_)
  have eM : Spec.Sha3.bytesAt t₅.mem L.msg L.len.toNat = Spec.Sha3.bytesAt m₀ L.msg L.len.toNat :=
    in_bytes hL hc₅.1 (R := L.MSG) (by simp [Lay.inputs]) (Nat.le_refl _) (Nat.le_of_lt L.len.isLt)
  rw [eM] at hr₆ hx₆
  -- The padding.
  refine WP.seq (WP.mono (kpad_ok v hV hs hc₆ (pos := .ret) trivial hx₆ (Nat.mod_lt _ (by decide)))
    fun t₇ ⟨hc₇, _, hp₇⟩ => ?_)
  have hst := hp₇ _ hr₆ rfl
  -- The output.
  refine WP.mono (ksqz_ok v hV hs hc₇ (out := .val (.frame fH)) (op := L.E + BitVec.ofNat 64 fH)
    (show fH < 4096 by decide) rfl rfl
    (.inl ⟨⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩, fun p hp => by
      simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;>
        exact Offset.disjoint _ (by simp [fScr, fHdr, fH]) (by simp [fScr, fHdr]) (by simp [fH])⟩)
    (fr_st hL (by decide)) (fr_ks hL (by decide)) (ck_frame (by decide))) fun u ⟨hu, _, hb⟩ => ⟨hu, ?_⟩
  rw [hb, hst, ← shake256_eq]

end VG.Proof.Ed448.AArch64.Verify

end

end

/-!
# Ed448 verification on AArch64: the frame's body

After the hash: `k`, the hash reduced modulo `L` (`reduce_step`), and the
verification equation's result in `x0` (`equation_step`), for the inputs as
on entry (`body_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Verify

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Verify
open VG.Impl.Ed448.AArch64.Whole (Src setupS callS)
open VG.Proof.Ed448.AArch64.Whole (Env WCtx srcValue srcValid ScrOk wsetup_ok reduce_call
  Readable Writable Apart)
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

attribute [local irreducible] VG.Impl.X448.AArch64.Base.combWords VG.Impl.Ed448.AArch64.Sparse.baseWords

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem scr_writable (L : Lay) : Writable L.env L.SCR := .inr ⟨L.SCR, by simp [Lay.env], within_self _ _⟩

theorem fr_scr (hL : L.Ok) {d n : Nat} (h : d + n ≤ 336) :
    Region.Disjoint ⟨L.E + BitVec.ofNat 64 d, n⟩ L.SCR :=
  hL.kc.sub_left (Offset.sub_base _ h)

theorem k_apart (L : Lay) : Apart L.env ⟨L.E + BitVec.ofNat 64 fK, 57⟩ :=
  ⟨⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩, fun p hp => by
    simp only [Lay.env, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact Offset.disjoint _ (by simp [fScr, fHdr, fK]) (by simp [fScr, fHdr]) (by simp [fK])⟩

theorem reduce_step (hL : L.Ok) (hc : WCtx L.env g vec m₀ t) :
    WP isa (callS reduceArgs "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) t fun u =>
      WCtx L.env g vec m₀ u ∧ Spec.Ed448.bytesAt u.mem (L.E + BitVec.ofNat 64 fK) 57 =
        Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fH) 114) := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := reduceArgs) (by decide)
    (by simp [reduceArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, fK, fH, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.E + BitVec.ofNat 64 fK := hv (.x0, .val (.frame fK)) (List.mem_of_getElem? (i := 0) rfl)
  have h1 : u.gpr .x1 = L.E + BitVec.ofNat 64 fH := hv (.x1, .val (.frame fH)) (List.mem_of_getElem? (i := 1) rfl)
  have h2 : u.gpr .x2 = L.scr := by
    rw [hv (.x2, .loc fScr 0) (List.mem_of_getElem? (i := 2) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (reduce_call hV hu h0 h1 h2 (fr_scr hL (by decide)) (.inl ⟨fH, rfl, show fH + 114 ≤ 256 by decide⟩)
    (.inl (k_apart L)) (scr_writable L)) fun w ⟨hw, _, hk⟩ => ⟨hw, by rw [hk, hm]⟩

theorem equation_step (hQ : Proof.Ed448.AArch64.Sparse.EqOk) (hL : L.Ok)
    (hc : WCtx L.env g vec m₀ t) (ha : Args L m₀) :
    WP isa (callS equationArgs "vg_ed448_verify_equation" Impl.Ed448.AArch64.Sparse.verifyEquation) t fun u =>
      WCtx L.env g vec m₀ u ∧ u.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m₀ L.pk 57)
        (Spec.Ed448.bytesAt m₀ L.sig 114) (Spec.Ed448.bytesAt t.mem (L.E + BitVec.ofNat 64 fK) 57) then 1 else 0 := by
  have hV := env_ok hL
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := equationArgs) (by decide)
    (by simp [equationArgs, srcValid, VG.Proof.Ed25519.AArch64.Whole.valid, aPk, aSig, fK, fScr]) rfl
    (by decide)) fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 : u.gpr .x0 = L.pk := (hv (.x0, aPk) (List.mem_of_getElem? (i := 0) rfl)).trans
    (arg_src hL hc.1 ha (j := 0) (by decide) _)
  have h1 : u.gpr .x1 = L.sig := (hv (.x1, aSig) (List.mem_of_getElem? (i := 1) rfl)).trans
    (arg_src hL hc.1 ha (j := 5) (by decide) _)
  have h2 : u.gpr .x2 = L.E + BitVec.ofNat 64 fK := hv (.x2, .val (.frame fK)) (List.mem_of_getElem? (i := 2) rfl)
  have h3 : u.gpr .x3 = L.scr := by
    rw [hv (.x3, .loc fScr 0) (List.mem_of_getElem? (i := 3) rfl), (scrOk hL).loc hc, BitVec.add_zero]
  refine WP.mono (equation_call hQ hV ⟨rfl,rfl⟩ hu h0 h1 h2 h3 hL.pc hL.sc (fr_scr hL (by decide)) hL.nc
    (in_readable L.PK (by simp [Lay.inputs])) (in_readable L.SIG (by simp [Lay.inputs]))
    (.inl ⟨fK, rfl, show fK + 57 ≤ 256 by decide⟩) (scr_writable L) ha.2) fun w ⟨hw, _, hx⟩ => ⟨hw, ?_⟩
  have eP : Spec.Ed448.bytesAt u.mem L.pk 57 = Spec.Ed448.bytesAt m₀ L.pk 57 :=
    in_bytes hL hu.1 (R := L.PK) (by simp [Lay.inputs]) (Nat.le_refl _) (show 57 ≤ 2 ^ 64 by decide)
  have eS : Spec.Ed448.bytesAt u.mem L.sig 114 = Spec.Ed448.bytesAt m₀ L.sig 114 :=
    in_bytes hL hu.1 (R := L.SIG) (by simp [Lay.inputs]) (Nat.le_refl _) (show 114 ≤ 2 ^ 64 by decide)
  rw [hx, eP, eS, hm]

/-- The frame's body: `x0` is the verification equation's result for the
reduced hash. -/
theorem body_ok (v : Proof.Sha3.AArch64.Permutation) (hQ : Proof.Ed448.AArch64.Sparse.EqOk)
    (hL : L.Ok) (hc : Ctx0 L g vec m₀ t) (ha : Args L m₀) (h6 : t.gpr .x6 = L.scr)
    (hsy : t.syms Impl.Ed448.AArch64.Sparse.baseSym = L.T) :
    WP isa (body v.callee) t fun u => Ctx0 L g vec m₀ u ∧
      u.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt m₀ L.pk 57) (Spec.Ed448.bytesAt m₀ L.sig 114)
        (Spec.Ed448.scalarReduce (Spec.Sha3.shake256 (hashIn L m₀) 114)) then 1 else 0 := by
  refine WP.seq (WP.mono (entry_ok hL hc ha h6 hsy) fun t₁ hc₁ => ?_)
  refine WP.seq (WP.mono (hash_ok v hL hc₁ ha) fun t₂ ⟨hc₂, hh₂⟩ => ?_)
  refine WP.seq (WP.mono (reduce_step hL hc₂) fun t₃ ⟨hc₃, hk₃⟩ => ?_)
  refine WP.mono (equation_step hQ hL hc₃ ha) fun u ⟨hu, hx⟩ => ⟨hu.1, ?_⟩
  rw [hx, hk₃, show Spec.Ed448.bytesAt t₂.mem (L.E + BitVec.ofNat 64 fH) 114 =
    Spec.Sha3.bytesAt t₂.mem (L.E + BitVec.ofNat 64 fH) 114 from rfl, hh₂]

end VG.Proof.Ed448.AArch64.Verify
