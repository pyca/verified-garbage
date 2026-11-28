module

-- separate module: verify's constant-time proof, kept apart from the scrub and registration's kernel evaluation of the code

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTopLoop
public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTopCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `verify`: constant time

Two runs whose public data agree (`vgK`'s `pub`), with a signature of
`sigLen` bytes, have the same values (`Same`): the digest, its indices, FORS's
public key, the layers' roots and the result. So they test `ctx_len` and
`sig_len` alike and return 0 alike or run the body (`verify_ct_of`), whose
runs leak the same (`body_ct`): the blocks by the taint analysis
(`VerifyTopCT`), the digest by `hashM_ct`, and the calls of `forsPk` and
`xmssPk` by their contracts (`RelCT.call`), whose public data, the
arguments, the signature's part and the digest or the root at `oMsg`, are
the same values of the inputs in both runs, as the correctness proofs'
states say (`VerifyTopFors`, `VerifyTopLoop`). Then `verify_ct`, against
`vgK`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa (layerTree)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar)
open VG.Proof.MlKem.AArch64 (Only)
open VG.Proof.SlhDsa.AArch64.KeyGen (Shake6 relSeq)

/-! ## Two runs' values -/

/-- Two runs' entry states whose public data agree, with a signature of
`sigLen` bytes. -/
structure Same (p : Params) (σ₁ σ₂ : State) : Prop where
  x0 : σ₁.gpr .x0 = σ₂.gpr .x0
  x1 : σ₁.gpr .x1 = σ₂.gpr .x1
  x2 : σ₁.gpr .x2 = σ₂.gpr .x2
  x3 : σ₁.gpr .x3 = σ₂.gpr .x3
  x4 : σ₁.gpr .x4 = σ₂.gpr .x4
  x5 : σ₁.gpr .x5 = σ₂.gpr .x5
  x6 : σ₁.gpr .x6 = σ₂.gpr .x6
  x7 : σ₁.gpr .x7 = σ₂.gpr .x7
  sp : σ₁.sp = σ₂.sp
  pk : pkI p σ₁ = pkI p σ₂
  msg : msgI σ₁ = msgI σ₂
  ctx : ctxI σ₁ = ctxI σ₂
  sig : sigI σ₁ = sigI σ₂
  sl : (σ₁.gpr .x6).toNat = p.sigLen

theorem Same.of_pub {p : Params} {σ₁ σ₂ : State} (h : (vgK p).pub σ₁ σ₂) (hsl : (σ₁.gpr .x6).toNat = p.sigLen) :
    Same p σ₁ σ₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2, hsl⟩

theorem sub_eq {m₁ m₂ : Mem} {a₁ a₂ : Addr} {L : Nat} (h : bytesAt m₁ a₁ L = bytesAt m₂ a₂ L) (ea : a₁ = a₂)
    {o k : Nat} (hk : o + k ≤ L) : bytesAt m₁ (a₁ + BitVec.ofNat 64 o) k = bytesAt m₂ (a₂ + BitVec.ofNat 64 o) k := by
  subst ea
  have e := congrArg (fun l => (l.drop o).take k) h
  rw [bytesAt_drop _ _ (show o ≤ L by omega), bytesAt_drop _ _ (show o ≤ L by omega),
    bytesAt_take _ _ (show k ≤ L - o by omega), bytesAt_take _ _ (show k ≤ L - o by omega)] at e
  exact e

section
variable {p : Params} (hp : VPar p) {σ₁ σ₂ : State} (h : Same p σ₁ σ₂)
include hp h

omit hp in
theorem Same.sig' {o k : Nat} (hk : o + k ≤ p.sigLen) :
    bytesAt σ₁.mem (σ₁.gpr .x5 + BitVec.ofNat 64 o) k = bytesAt σ₂.mem (σ₂.gpr .x5 + BitVec.ofNat 64 o) k := by
  have e := h.sig
  simp only [sigI] at e
  rw [← h.x6, h.sl] at e
  exact sub_eq e h.x5 hk

theorem Same.pks : PKs p σ₁ = PKs p σ₂ := by
  have e := sub_eq (o := 0) (k := p.n) h.pk h.x0 (by rw [hp.pk]; omega)
  simp only [BitVec.add_zero] at e
  exact e

theorem Same.pkr : PKr p σ₁ = PKr p σ₂ :=
  sub_eq (o := p.n) (k := p.n) h.pk h.x0 (by rw [hp.pk]; omega)

theorem Same.rv : Rv p σ₁ = Rv p σ₂ := by
  have e := h.sig' (o := 0) (k := p.n) (by rw [hp.sigLen]; omega)
  simp only [BitVec.add_zero] at e
  exact e

omit hp in
theorem Same.mp : Sign.mPrime σ₁ = Sign.mPrime σ₂ := by
  have ec : ctxI σ₁ = ctxI σ₂ := h.ctx
  have em : msgI σ₁ = msgI σ₂ := h.msg
  simp only [ctxI, msgI] at ec em
  simp only [Sign.mPrime]
  rw [ec, em, h.x4]

theorem Same.dv : Dv p σ₁ = Dv p σ₂ := by
  simp only [Dv, h.rv hp, h.pks hp, h.pkr hp, h.mp]

theorem Same.tv : Tv p σ₁ = Tv p σ₂ := by
  show (splitDigest p (Dv p σ₁)).2.1 = (splitDigest p (Dv p σ₂)).2.1
  rw [h.dv hp]

theorem Same.iv : Iv p σ₁ = Iv p σ₂ := by
  show (splitDigest p (Dv p σ₁)).2.2 = (splitDigest p (Dv p σ₂)).2.2
  rw [h.dv hp]

theorem Same.sigf : sigF p σ₁ = sigF p σ₂ := h.sig' (by rw [hp.sigLen]; omega)

theorem Same.sigh : sigH p σ₁ = sigH p σ₂ := h.sig' (Nat.le_of_eq hp.sigLen.symm)

theorem Same.pkf : pkF p σ₁ = pkF p σ₂ := by
  simp only [pkF, h.sigf hp, h.dv hp, h.pks hp, h.tv hp, h.iv hp]

theorem Same.htv (j : Nat) : htV p σ₁ j = htV p σ₂ j := by
  simp only [htV, h.pkf hp, h.sigh hp, h.pks hp, h.tv hp, h.iv hp]

theorem Same.vok : vOk p σ₁ = vOk p σ₂ := by
  simp only [vOk, h.htv hp, h.pkr hp]

end

/-- `verify` in constant time, from its body's: two runs whose public data
agree test the lengths alike, and return 0 alike or run the body. -/
theorem verify_ct_of {p : Params} (hS : Shake6 p) {f : Impl.SlhDsa.AArch64.Shake.Fns}
    {g : Impl.SlhDsa.AArch64.Verify.VFns}
    (hbody : ∀ {σ₁ σ₂ : State}, VG p σ₁ → VG p σ₂ → Same p σ₁ σ₂ → (σ₁.gpr .x4).toNat < 256 →
      RelCT isa (fun a b => Only [.x9, .x10] σ₁ a ∧ Only [.x9, .x10] σ₂ b)
        (Impl.SlhDsa.AArch64.Verify.verifyBody p f g) fun _ _ => True) :
    ConstantTime isa (vgK p).pre (vgK p).pub (Impl.SlhDsa.AArch64.Verify.verify p f g) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hsl : p.sigLen < 2 ^ 31 := by rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have e4 : s₁.gpr .x4 = s₂.gpr .x4 := hpub.2.2.2.2.1
  have e6 : s₁.gpr .x6 = s₂.gpr .x6 := hpub.2.2.2.2.2.2.1
  have esp : s₁.sp = s₂.sp := hpub.2.2.2.2.2.2.2.2.1
  have hct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (Impl.SlhDsa.AArch64.Verify.verify p f g) fun _ _ => True := by
    unfold Impl.SlhDsa.AArch64.Verify.verify
    refine KeyGen.relSeq (ct_chk hS fun x y ⟨hx, hy⟩ => ⟨by rw [hx, hy, esp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hx hy; rcases hr with rfl | rfl
        · exact e4
        · exact e6⟩)
      (fun a ha => by rw [ha]; exact chk_wp (by omega) s₁) (fun b hb => by rw [hb]; exact chk_wp (by omega) s₂) ?_
    refine RelCT.ite (fun a b ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ => by
        rw [MlKem.AArch64.eval_nonzero, MlKem.AArch64.eval_nonzero, ha, hb, e4, e6])
      (ct_ret0 fun x y ⟨⟨⟨ox, _⟩, ⟨oy, _⟩⟩, _⟩ => ⟨by rw [ox.sp, oy.sp, esp], fun _ h => absurd h List.not_mem_nil⟩) ?_
    by_cases hl : (s₁.gpr .x4).toNat < 256 ∧ s₁.gpr .x6 = BitVec.ofNat 64 p.sigLen
    · have h6 : (s₁.gpr .x6).toNat = p.sigLen := by rw [hl.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact RelCT.mono (hbody h₁ h₂ (Same.of_pub hpub h6) hl.1)
        (fun a b ⟨⟨⟨oa, _⟩, ⟨ob, _⟩⟩, _⟩ => ⟨oa, ob⟩) fun _ _ h => h
    · refine RelCT.of_false fun a b ⟨⟨⟨_, ha⟩, _⟩, hc⟩ => hl (chk_zero ?_)
      rw [MlKem.AArch64.eval_nonzero, ha, Option.some.injEq, bne_eq_false_iff_eq] at hc
      exact hc
  exact (hct _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem ce_gpr (u : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (u.callEntry.withRegions rd wr).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem ce_mem (u : State) (rd wr : List Region) : (u.callEntry.withRegions rd wr).mem = u.mem := by
  rw [State.withRegions_mem, State.callEntry_mem]

theorem ce_sp (u v : State) (rd wr rd' wr' : List Region) (h : u.sp = v.sp) :
    (u.callEntry.withRegions rd wr).sp = (v.callEntry.withRegions rd' wr').sp := by
  simp only [State.withRegions, State.callEntry]; rw [h]

/-! ## `forsPk` -/

/-- The call of `forsPk`: its precondition, narrowed to the signature's part
and `scratch`. -/
theorem fors_pre {p : Params} (hp : VPar p) {σ u : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    (hu : FPre p σ u) :
    (forsPkContract p).pre (u.callEntry.withRegions [⟨σ.gpr .x5 + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
      [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩]) ∧
    Covers ([⟨σ.gpr .x5 + BitVec.ofNat 64 p.n, p.forsSigLen⟩] ++ [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩])
      (u.rd ++ u.wr) ∧
    Covers [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩] u.wr := by
  have hsl31 := hp.sigLt
  have hfsl : p.n + p.forsSigLen ≤ p.sigLen := by rw [hp.sigLen]; omega
  have hI := Iv_lt hp σ
  have hpow : 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hp.hp9
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions [⟨σ.gpr .x5 + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
      [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩]).gpr r = u.gpr r := fun r h => ce_gpr u _ _ h
  obtain ⟨hcv, hcw, hfo, hdo⟩ := part_ok hK hu.ctx hsl (off := p.n) (l := p.forsSigLen) hfsl hp.fpos
  refine ⟨⟨⟨by rw [State.withRegions_rd, hg _ (by decide), hu.x1],
      by rw [State.withRegions_wr, hg _ (by decide), hu.x0], by rw [hg _ (by decide), hu.x0]; exact hK.f_scr,
      by rw [hg _ (by decide), hu.x0]; have := hK.f_scr; simp only [scratchLen] at this; simp; omega,
      by rw [hg _ (by decide), hu.x0]; exact empty_disj _ _,
      fun r hr => by
        rw [hg _ (by decide), hu.x1] at hr; simp only [List.mem_singleton] at hr; subst hr; exact hfo,
      fun r hr => by
        rw [hg _ (by decide), hu.x1] at hr; simp only [List.mem_singleton] at hr; subst hr
        rw [hg _ (by decide), hu.x0]; exact hdo⟩,
    ⟨_, _, by rw [hg _ (by decide), hu.x0]; exact hu.env⟩,
    by rw [hg _ (by decide), hu.x2, BitVec.toNat_ofNat]; omega⟩, hcv, hcw⟩

/-- FORS's signature, at the call of `forsPk`. -/
theorem fors_sig {p : Params} (hp : VPar p) {σ u : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    (hu : FPre p σ u) : bytesAt u.mem (σ.gpr .x5 + BitVec.ofNat 64 p.n) p.forsSigLen = sigF p σ := by
  have hfsl : p.n + p.forsSigLen ≤ p.sigLen := by rw [hp.sigLen]; omega
  have hsl31 := hp.sigLt
  obtain ⟨-, -, -, hdo⟩ := part_ok hK hu.ctx hsl (off := p.n) (l := p.forsSigLen) hfsl hp.fpos
  exact hu.ctx.bytes_out (by omega) hdo (hK.stk_sig.sub_right (Offset.sub_base _ (by rw [hsl]; exact hfsl))).symm

/-- Two runs' calls of `forsPk` leak the same. -/
theorem fors_ct {p : Params} (hp : VPar p) {f : Impl.SlhDsa.AArch64.Shake.Fns} (T : Thash4Impl p.n)
    (ht : f.t4 = T.code) (fn : String) {σ₁ σ₂ : State} (hK₁ : VG p σ₁) (hK₂ : VG p σ₂) (hS : Same p σ₁ σ₂) :
    RelCT isa (fun a b => FPre p σ₁ a ∧ FPre p σ₂ b) (.call fn (Impl.SlhDsa.AArch64.Verify.forsPk p f))
      fun _ _ => True := by
  have hv := ForsPk.forsPk_verified (Sz.of_vpar hp) hp.p6 T ht
  have hsl₁ := hS.sl
  have hsl₂ : (σ₂.gpr .x6).toNat = p.sigLen := by rw [← hS.x6]; exact hsl₁
  have hmd : p.mdLen + 2 ≤ p.m := by have := hp.m; have := hp.ti7; omega
  refine RelCT.call hv.1 hv.2.1 [⟨σ₁.gpr .x5 + BitVec.ofNat 64 p.n, p.forsSigLen⟩]
    [⟨σ₁.gpr .x7, scratchLen⟩, ⟨σ₁.gpr .x7, 0⟩] fun a b ⟨ha, hb⟩ => ?_
  obtain ⟨q₁, c₁, w₁⟩ := fors_pre hp hK₁ hsl₁ ha
  obtain ⟨q₂, c₂, w₂⟩ := fors_pre hp hK₂ hsl₂ hb
  rw [← hS.x5, ← hS.x7] at q₂ c₂
  rw [← hS.x7] at w₂
  refine ⟨q₁, q₂, ?_, c₁, w₁, c₂, w₂⟩
  have dg : ∀ {σ u : State}, FPre p σ u →
      bytesAt u.mem (at' (σ.gpr .x7) Layout.oDigest) (p.mdLen + 2) = (Dv p σ).take (p.mdLen + 2) :=
    fun hu => by rw [← hu.dig, bytesAt_take _ _ hmd]
  refine ⟨?_, ?_, ?_, ce_sp _ _ _ _ _ _ (by rw [ha.ctx.sp, hb.ctx.sp, hS.sp]), ?_, ?_⟩
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ha.x0, hb.x0, hS.x7]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ha.x1, hb.x1, hS.x5]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ha.x2, hb.x2, hS.iv hp]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_mem, ce_mem, ha.x1, hb.x1,
      fors_sig hp hK₁ hsl₁ ha, fors_sig hp hK₂ hsl₂ hb, hS.sigf hp]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_mem, ce_mem, ha.x0, hb.x0, dg ha, dg hb, hS.dv hp]

/-! ## The layers -/

/-- At a layer's call of `xmssPk`. -/
structure LB (p : Params) (σ : State) (j : Nat) (u : State) : Prop where
  ctx : Ctx p σ u
  env : Env p u.mem (σ.gpr .x7) (PKs p σ) (layerTree j (htV p σ j).2.1)
  x0 : u.gpr .x0 = σ.gpr .x7
  x1 : u.gpr .x1 = BitVec.ofNat 64 (htV p σ j).2.2
  x2 : u.gpr .x2 = σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  x20 : u.gpr .x20 = σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  x21 : u.gpr .x21 = BitVec.ofNat 64 j
  msg : bytesAt u.mem (at' (σ.gpr .x7) Layout.oMsg) p.n = (htV p σ j).1

theorem lb_wp {p : Params} (hp : VPar p) {σ t : State} (hK : VG p σ) {j : Nat} (hj : j < p.d)
    (hL : LI p σ j t) :
    WP isa (.block (Impl.SlhDsa.AArch64.Shake.treeLanes p .x21 .x22 ++
      ([Impl.SlhDsa.AArch64.Thash4.mov .x0 .x19, Impl.SlhDsa.AArch64.Thash4.mov .x1 .x23,
        Impl.SlhDsa.AArch64.Thash4.mov .x2 .x20] : List Instr))) t (LB p σ j) := by
  have hz := Sz.of_vpar hp
  have hn := hz.n32
  have hd := hp.d22
  obtain ⟨a, he⟩ := hL.env
  have hT' : (htV p σ j).2.1 < 2 ^ 64 := Nat.lt_of_le_of_lt (htV_tree σ j) (Tv_lt hp σ)
  refine lblock_ok hz hK hL.ctx he (by rw [hL.x21, BitVec.toNat_ofNat]; omega)
    fun u hcu heu hgu h0 h1 h2 hfu => ⟨hcu, ?_, h0, by rw [h1, hL.x23], by rw [h2, hL.x20],
      by rw [hgu .x20 (by decide), hL.x20], by rw [hgu .x21 (by decide), hL.x21], ?_⟩
  · rw [hL.x21, hL.x22, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt hT'] at heu
    exact heu
  · rw [bytesAt_frame hfu (fun r hr => ?_) (by omega)]
    · exact hL.msg
    exact (lane_disj hn (.inr hr) (by simp only [Layout.oMsg, Layout.oA]; omega))

theorem xoff {p : Params} (hp : VPar p) {j : Nat} (hj : j < p.d) :
    p.n + p.forsSigLen + j * p.xmssSigLen + p.xmssSigLen ≤ p.sigLen := by
  rw [hp.sigLen]; have := Nat.mul_le_mul_right p.xmssSigLen (show j + 1 ≤ p.d by omega)
  rw [Nat.add_mul, Nat.one_mul] at this; omega

/-- The call of `xmssPk`: its precondition, narrowed to the layer's XMSS
signature and `scratch`. -/
theorem xmss_pre {p : Params} (hp : VPar p) {σ u : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    {j : Nat} (hj : j < p.d) (hu : LB p σ j u) :
    (xmssPkContract p).pre (u.callEntry.withRegions
      [⟨σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen), p.xmssSigLen⟩]
      [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩]) ∧
    Covers ([⟨σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen), p.xmssSigLen⟩] ++
      [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩]) (u.rd ++ u.wr) ∧
    Covers [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩] u.wr := by
  have hI' := htV_leaf hp σ j
  have hpow : 2 ^ p.hp ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) hp.hp9
  have hu1 : (u.gpr .x1).toNat = (htV p σ j).2.2 := by
    rw [hu.x1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hcv, hcw, hfo, hdo⟩ := part_ok hK hu.ctx hsl (xoff hp hj) hp.xpos
  have hg : ∀ r, r ∉ linkRegs → (u.callEntry.withRegions
      [⟨σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen), p.xmssSigLen⟩]
      [⟨σ.gpr .x7, scratchLen⟩, ⟨σ.gpr .x7, 0⟩]).gpr r = u.gpr r := fun r h => ce_gpr u _ _ h
  refine ⟨⟨⟨by rw [State.withRegions_rd, hg _ (by decide), hu.x2],
      by rw [State.withRegions_wr, hg _ (by decide), hu.x0], by rw [hg _ (by decide), hu.x0]; exact hK.f_scr,
      by rw [hg _ (by decide), hu.x0]; have := hK.f_scr; simp only [scratchLen] at this; simp; omega,
      by rw [hg _ (by decide), hu.x0]; exact empty_disj _ _,
      fun r hr => by
        rw [hg _ (by decide), hu.x2] at hr; simp only [List.mem_singleton] at hr; subst hr; exact hfo,
      fun r hr => by
        rw [hg _ (by decide), hu.x2] at hr; simp only [List.mem_singleton] at hr; subst hr
        rw [hg _ (by decide), hu.x0]; exact hdo⟩,
    ⟨_, _, by rw [hg _ (by decide), hu.x0]; exact hu.env⟩,
    by rw [hg _ (by decide), hu1]; exact hI'⟩, hcv, hcw⟩

/-- The layer's XMSS signature, at the call of `xmssPk`. -/
theorem xmss_sig {p : Params} (hp : VPar p) {σ u : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen)
    {j : Nat} (hj : j < p.d) (hu : LB p σ j u) :
    bytesAt u.mem (σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)) p.xmssSigLen =
      chunk (sigH p σ) p.xmssSigLen j := by
  have hsl31 := hp.sigLt
  have hoff := xoff hp hj
  obtain ⟨-, -, -, hdo⟩ := part_ok hK hu.ctx hsl hoff hp.xpos
  rw [hu.ctx.bytes_out (by omega) hdo
    (hK.stk_sig.sub_right (Offset.sub_base _ (by rw [hsl]; exact hoff))).symm, sigH,
    KeyGen.chunk_bytesAt _ _ hj, addr_add, Nat.mul_comm p.xmssSigLen j]

/-- After a layer's call of `xmssPk`. -/
structure LC (p : Params) (σ : State) (j : Nat) (w : State) : Prop where
  sp : w.sp = σ.sp
  x20 : w.gpr .x20 = σ.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen)
  x21 : w.gpr .x21 = BitVec.ofNat 64 j

theorem xmss_wp {p : Params} (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code) (fn : String)
    {σ u : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen) {j : Nat} (hj : j < p.d) (hu : LB p σ j u) :
    WP isa (.call fn (Impl.SlhDsa.AArch64.Verify.xmssPk p f)) u (LC p σ j) := by
  obtain ⟨q, c, w⟩ := xmss_pre hp hK hsl hj hu
  exact XmssPk.xmssPkcall_ok (Sz.of_vpar hp) hh T ht fn q c w fun s' _ _ hsp _ hpres _ _ =>
    ⟨by rw [hsp, hu.ctx.sp], by rw [hpres .x20 (by decide) (by decide), hu.x20],
      by rw [hpres .x21 (by decide) (by decide), hu.x21]⟩

/-- Two runs' calls of `xmssPk` leak the same. -/
theorem xmss_ct {p : Params} (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code) (fn : String)
    {σ₁ σ₂ : State} (hK₁ : VG p σ₁) (hK₂ : VG p σ₂) (hS : Same p σ₁ σ₂) {j : Nat} (hj : j < p.d) :
    RelCT isa (fun a b => LB p σ₁ j a ∧ LB p σ₂ j b) (.call fn (Impl.SlhDsa.AArch64.Verify.xmssPk p f))
      fun _ _ => True := by
  have hv := XmssPk.xmssPk_verified (Sz.of_vpar hp) hh T ht
  have hsl₁ := hS.sl
  have hsl₂ : (σ₂.gpr .x6).toNat = p.sigLen := by rw [← hS.x6]; exact hsl₁
  refine RelCT.call hv.1 hv.2.1
    [⟨σ₁.gpr .x5 + BitVec.ofNat 64 (p.n + p.forsSigLen + j * p.xmssSigLen), p.xmssSigLen⟩]
    [⟨σ₁.gpr .x7, scratchLen⟩, ⟨σ₁.gpr .x7, 0⟩] fun a b ⟨ha, hb⟩ => ?_
  obtain ⟨q₁, c₁, w₁⟩ := xmss_pre hp hK₁ hsl₁ hj ha
  obtain ⟨q₂, c₂, w₂⟩ := xmss_pre hp hK₂ hsl₂ hj hb
  rw [← hS.x5, ← hS.x7] at q₂ c₂
  rw [← hS.x7] at w₂
  refine ⟨q₁, q₂, ?_, c₁, w₁, c₂, w₂⟩
  refine ⟨?_, ?_, ?_, ce_sp _ _ _ _ _ _ (by rw [ha.ctx.sp, hb.ctx.sp, hS.sp]), ?_, ?_⟩
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ha.x0, hb.x0, hS.x7]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ha.x1, hb.x1, hS.htv hp]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ha.x2, hb.x2, hS.x5]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_mem, ce_mem, ha.x2, hb.x2,
      xmss_sig hp hK₁ hsl₁ hj ha, xmss_sig hp hK₂ hsl₂ hj hb, hS.sigh hp]
  · rw [ce_gpr _ _ _ (by decide), ce_gpr _ _ _ (by decide), ce_mem, ce_mem, ha.x0, hb.x0, ha.msg, hb.msg,
      hS.htv hp]

/-! ## The layers -/

theorem layer_ct {p : Params} (hS6 : Shake6 p) (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (g : Impl.SlhDsa.AArch64.Verify.VFns) {σ₁ σ₂ : State} (hK₁ : VG p σ₁) (hK₂ : VG p σ₂) (hS : Same p σ₁ σ₂)
    {j : Nat} (hj : j < p.d) :
    RelCT isa (fun a b => LI p σ₁ j a ∧ LI p σ₂ j b) (Impl.SlhDsa.AArch64.Verify.layerBody p f g)
      fun _ _ => True := by
  have hsl₁ := hS.sl
  have hsl₂ : (σ₂.gpr .x6).toNat = p.sigLen := by rw [← hS.x6]; exact hsl₁
  unfold Impl.SlhDsa.AArch64.Verify.layerBody
  refine relSeq (ct_lblock hS6 fun x y ⟨hx, hy⟩ => ⟨by rw [hx.ctx.sp, hy.ctx.sp, hS.sp], fun r hr => ?_⟩)
    (fun a ha => lb_wp hp hK₁ hj ha) (fun b hb => lb_wp hp hK₂ hj hb) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hx.ctx.x19, hy.ctx.x19, hS.x7]
    · rw [hx.x20, hy.x20, hS.x5]
    · rw [hx.x21, hy.x21]
  refine relSeq (xmss_ct hp hh T ht g.xmssPkName hK₁ hK₂ hS hj)
    (fun a ha => xmss_wp hp hh T ht _ hK₁ hsl₁ hj ha) (fun b hb => xmss_wp hp hh T ht _ hK₂ hsl₂ hj hb)
    (ct_next hS6 fun x y ⟨hx, hy⟩ => ⟨by rw [hx.sp, hy.sp, hS.sp], fun r hr => ?_⟩)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hx.x20, hy.x20, hS.x5]
  · rw [hx.x21, hy.x21]

theorem loop_ct {p : Params} (hS6 : Shake6 p) (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (T : Thash4Impl p.n) (ht : f.t4 = T.code)
    (g : Impl.SlhDsa.AArch64.Verify.VFns) {σ₁ σ₂ : State} (hK₁ : VG p σ₁) (hK₂ : VG p σ₂) (hS : Same p σ₁ σ₂) :
    RelCT isa (fun a b => LI p σ₁ 0 a ∧ LI p σ₂ 0 b)
      (.loop (Impl.SlhDsa.AArch64.Verify.layerBody p f g) (.nonzero .x .x9)) fun _ _ => True := by
  have hd := hp.d22
  have hd1 := hp.d1
  have hsl₁ := hS.sl
  have hsl₂ : (σ₂.gpr .x6).toNat = p.sigLen := by rw [← hS.x6]; exact hsl₁
  refine RelCT.mono (RelCT.loop (I := fun n a b => ∃ j, j < p.d ∧ n = p.d - j ∧
      LI p σ₁ j a ∧ LI p σ₂ j b) (fun n => RelCT.exists_ fun j => ?_) p.d)
    (fun a b ⟨h₁, h₂⟩ => ⟨0, by omega, by omega, h₁, h₂⟩) fun _ _ h => h
  by_cases hjn : j < p.d ∧ n = p.d - j
  · obtain ⟨hj, hn⟩ := hjn
    refine RelCT.mono (RelCT.wp (layer_ct hS6 hp hh T ht g hK₁ hK₂ hS hj) (F₁ := fun (w : State) =>
        LI p σ₁ (j + 1) w ∧ w.gpr .x9 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 p.d)
      (F₂ := fun (w : State) => LI p σ₂ (j + 1) w ∧ w.gpr .x9 = BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 p.d)
      fun a b ⟨ha, hb⟩ => ⟨layer_ok hp hh T ht g hK₁ hsl₁ hj ha, layer_ok hp hh T ht g hK₂ hsl₂ hj hb⟩)
      (fun a b h => ⟨h.2.2.1, h.2.2.2⟩) fun a b ⟨_, ⟨ha, h9a⟩, ⟨hb, h9b⟩⟩ => ?_
    rw [MlKem.AArch64.eval_nonzero, MlKem.AArch64.eval_nonzero, h9a, h9b]
    refine ⟨rfl, fun _ => trivial, fun h => ⟨p.d - (j + 1), ?_, j + 1, ?_, rfl, ha, hb⟩⟩ <;>
    · by_cases e : j + 1 = p.d
      · rw [e, BitVec.sub_self] at h; simp at h
      · omega
  · exact RelCT.of_false fun a b ⟨h, h', _⟩ => hjn ⟨h, h'⟩

/-! ## The body -/

theorem notx910 : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], r ∉ [Reg.x9, .x10] := by decide

/-- Two runs of the body from entry states with the same public data leak the same. -/
theorem body_ct {p : Params} (hS6 : Shake6 p) (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) (g : Impl.SlhDsa.AArch64.Verify.VFns)
    {σ₁ σ₂ : State} (hK₁ : VG p σ₁) (hK₂ : VG p σ₂) (hS : Same p σ₁ σ₂) :
    RelCT isa (fun a b => Only [.x9, .x10] σ₁ a ∧ Only [.x9, .x10] σ₂ b)
      (Impl.SlhDsa.AArch64.Verify.verifyBody p f g) fun _ _ => True := by
  have hz := Sz.of_vpar hp
  have hn := hz.n32
  have hsl₁ := hS.sl
  have hsl₂ : (σ₂.gpr .x6).toNat = p.sigLen := by rw [← hS.x6]; exact hsl₁
  have e : ∀ r ∈ [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7], σ₁.gpr r = σ₂.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hS.x0, hS.x1, hS.x2, hS.x3, hS.x4, hS.x5, hS.x6, hS.x7]
  unfold Impl.SlhDsa.AArch64.Verify.verifyBody
  -- the first block
  refine relSeq (ct_pro hS6 fun x y ⟨hx, hy⟩ => ⟨by rw [hx.sp, hy.sp, hS.sp], fun r hr => by
      rw [hx.get r (notx910 r hr), hy.get r (notx910 r hr), e r hr]⟩)
    (fun a ha => pro_ok hz hK₁ ha) (fun b hb => pro_ok hz hK₂ hb) ?_
  -- the digest
  refine relSeq (hashM_ct p hn v hv (S := σ₁.gpr .x7) fun a b ⟨⟨ca, ra⟩, ⟨cb, rb⟩⟩ =>
      ⟨hashIn hz hp.m64 hK₁ hsl₁ ca ra, by rw [hS.x7]; exact hashIn hz hp.m64 hK₂ hsl₂ cb rb,
        ⟨by rw [ca.sp, cb.sp, hS.sp], by rw [ra.x20, rb.x20, hS.x1], by rw [ra.x21, rb.x21, hS.x2],
          by rw [ra.x22, rb.x22, hS.x3], by rw [ra.x23, rb.x23, hS.x4], fun x hx => ?_,
          by simp only [argVal, ca.x19, cb.x19, hS.x7]⟩⟩)
    (fun a ⟨ca, ra⟩ => hash_ok hz hp.m64 v hv hK₁ hsl₁ ca ra)
    (fun b ⟨cb, rb⟩ => hash_ok hz hp.m64 v hv hK₂ hsl₂ cb rb) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · show a.gpr .x24 = b.gpr .x24; rw [ca.x24, cb.x24, hS.x5]
    · simp only [argVal, ca.x19, cb.x19, hS.x7]
    · simp only [argVal, ca.x19, cb.x19, hS.x7]
  -- the indices and the lanes
  refine relSeq (ct_fblock hS6 fun x y ⟨⟨cx, _⟩, ⟨cy, _⟩⟩ => ⟨by rw [cx.sp, cy.sp, hS.sp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [cx.x19, cy.x19, hS.x7]
      · rw [cx.x24, cy.x24, hS.x5]⟩)
    (fun a ⟨ca, da⟩ => fblock_ok hp hK₁ ca da) (fun b ⟨cb, db⟩ => fblock_ok hp hK₂ cb db) ?_
  -- FORS
  refine relSeq (fors_ct hp T ht g.forsPkName hK₁ hK₂ hS)
    (fun a ha => fors_ok hp T ht _ hK₁ hsl₁ ha) (fun b hb => fors_ok hp T ht _ hK₂ hsl₂ hb) ?_
  -- the layers
  refine relSeq (ct_init hS6 fun x y ⟨hx, hy⟩ => ⟨by rw [hx.ctx.sp, hy.ctx.sp, hS.sp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hx.ctx.x24, hy.ctx.x24, hS.x5]⟩)
    (fun a ha => init_wp hp hK₁ ha) (fun b hb => init_wp hp hK₂ hb) ?_
  refine relSeq (loop_ct hS6 hp hh T ht g hK₁ hK₂ hS)
    (fun a ha => loop_ok hp hh T ht g hK₁ hsl₁ ha) (fun b hb => loop_ok hp hh T ht g hK₂ hsl₂ hb) ?_
  exact ct_tail hS6 fun x y ⟨hx, hy⟩ => ⟨by rw [hx.ctx.sp, hy.ctx.sp, hS.sp], fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [hx.ctx.x19, hy.ctx.x19, hS.x7]⟩

/-- `verify` is constant time: its timing depends only on its public data,
the pointers, the lengths and the bytes of its inputs. -/
theorem verify_ct {p : Params} (hS6 : Shake6 p) (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) (g : Impl.SlhDsa.AArch64.Verify.VFns) :
    ConstantTime isa (vgK p).pre (vgK p).pub (Impl.SlhDsa.AArch64.Verify.verify p f g) :=
  verify_ct_of hS6 fun hK₁ hK₂ hS _ => body_ct hS6 hp hh v hv T ht g hK₁ hK₂ hS

end VG.Proof.SlhDsa.AArch64.VerifyTop
