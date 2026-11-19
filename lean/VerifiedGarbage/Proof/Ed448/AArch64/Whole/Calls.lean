module

public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified
public import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow
public import VerifiedGarbage.Proof.X448.AArch64.Base.Comb
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Spec.Ed448.Contract
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Zero
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Ed448.AArch64.Whole.Sponge`, which the modules that import this one used -/

section

/-!
# Ed448's complete operations on AArch64: the sponge's calls

With `scratch` kept in the locals at `d` (`ScrOk`), and any implementation
`v` of the Keccak permutation: the state zeroed (`zeroSt_ok`), a buffer
absorbed (`kabs_ok`: its bytes appended to the represented message, and the
new position in `x0`), the padding absorbed (`kpad_ok`) and 114 bytes
squeezed (`ksqz_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64 VG.Impl.Ed448.AArch64.Whole
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)
open VG.Spec.Sha3 (stateAt)

/-- `scratch` is kept in the locals at `d`, and written. -/
structure ScrOk (V : Env) (d : Nat) (scr : Addr) : Prop where
  kept : (d, scr) ∈ V.ls
  out : (⟨scr, 8192⟩ : Region) ∈ V.outs
  nc : scr.toNat + 8192 ≤ 2 ^ 64

abbrev ST (scr : Addr) : Region := ⟨scr, 200⟩
abbrev KS (scr : Addr) : Region := ⟨scr + BitVec.ofNat 64 256, 640⟩

theorem st_ks (scr : Addr) : (ST scr).Disjoint (KS scr) := Offset.base_disjoint _ (by decide) (by decide)

variable {V : Env} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State} {d : Nat} {scr : Addr}

theorem st_within (scr : Addr) : Within (ST scr) ⟨scr, 8192⟩ :=
  ⟨0, (BitVec.add_zero _).symm, by show 0 + 200 ≤ 8192; decide⟩
theorem ks_within (scr : Addr) : Within (KS scr) ⟨scr, 8192⟩ := ⟨256, rfl, by show 256 + 640 ≤ 8192; decide⟩

theorem ScrOk.ck_st (hV : V.Ok) (h : ScrOk V d scr) : (CK V.E).Disjoint (ST scr) :=
  (hV.co _ h.out).sub_right (st_within scr).sub
theorem ScrOk.ck_ks (hV : V.Ok) (h : ScrOk V d scr) : (CK V.E).Disjoint (KS scr) :=
  (hV.co _ h.out).sub_right (ks_within scr).sub

theorem ScrOk.sponge_writes (h : ScrOk V d scr) :
    ∀ r ∈ [ST scr, KS scr], Apart V r ∨ ∃ R ∈ V.outs, Within r R := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr ⟨_, h.out, st_within scr⟩
  · exact .inr ⟨_, h.out, ks_within scr⟩

theorem ScrOk.loc (hc : WCtx V g vec m₀ t) (h : ScrOk V d scr) (x0 : BitVec 64) (o : Nat) :
    srcValue V.E t.mem x0 (.loc d o) = scr + BitVec.ofNat 64 o :=
  srcValue_loc hc.2.1 h.kept o

theorem toNat_ofNat64 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-! ## The state zeroed -/

theorem zeroSt_ok (hV : V.Ok) (hs : ScrOk V d scr) (hc : WCtx V g vec m₀ t) :
    WP isa (zeroSt d) t fun u => WCtx V g vec m₀ u ∧ Frame [ST scr] t.mem u.mem ∧
      stateAt u.mem scr = Spec.Sha3.zero := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  rw [zeroSt, WP.seq_iff]
  refine WP.mono (wsetup_ok hV hc (args := [(.x15, .loc d 0)]) (by simp)
    (by simp [srcValid, hd.1]; omega_using [hd]) rfl (by simp [preserved])) fun u ⟨hu, hm, hvs⟩ => ?_
  have h15 : u.gpr .x15 = scr := by
    rw [hvs _ List.mem_cons_self, hs.loc hc, BitVec.add_zero]
  have hw : (⟨scr, 8192⟩ : Region) ∈ u.wr := by
    rw [hu.1.wr]; exact List.mem_cons_of_mem _ hs.out
  refine WP.mono_syms (zeroStores_run h15 hw) fun x ⟨xrd, xwr, xsp, xv, xg, xf, xz⟩ xsy => ⟨?_, ?_, xz⟩
  · refine hu.of_frame hV xrd xwr xsp (fun r hr _ => xg r (by rintro rfl; simp [preserved] at hr))
      (fun r _ => by rw [xv]) xf ?_ xsy
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact .inr ⟨_, hs.out, st_within scr⟩
  · rw [← hm]; exact xf

/-! ## Absorbing -/

/-- The arguments of `vg_keccak_absorb_scratch`. -/
abbrev absArgs (d : Nat) (src len pos : Src) : List (Reg × Src) :=
  [(.x2, pos), (.x0, .loc d 0), (.x1, .val (.const 136)), (.x3, src), (.x4, len), (.x5, .loc d 256)]

theorem absorb_pre (hV : V.Ok) (hs : ScrOk V d scr) {u : State} (hsp : u.sp = V.E) {dp : Addr} {n q : Nat}
    (h0 : u.gpr .x0 = scr) (h1 : u.gpr .x1 = BitVec.ofNat 64 136) (h2 : u.gpr .x2 = BitVec.ofNat 64 q)
    (h3 : u.gpr .x3 = dp) (h4 : u.gpr .x4 = BitVec.ofNat 64 n) (h5 : u.gpr .x5 = scr + BitVec.ofNat 64 256)
    (hql : q < 136) (hnl : n < 2 ^ 64)
    (dS : Region.Disjoint ⟨dp, n⟩ (ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) :
    Proof.Sha3.absorbAArch64.pre (u.callEntry.withRegions [⟨dp, n⟩] [ST scr, KS scr]) := by
  have hn' := toNat_ofNat64 hnl
  have hq' := toNat_ofNat64 (show q < 2 ^ 64 by omega_using [hql])
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x5 ∉ linkRegs), h0, h1, h2, h3, h4, h5, hsp, hn', hq']
  exact ⟨trivial, trivial, st_ks scr, dS, dK, hV.e16, hs.ck_st hV, kD, hs.ck_ks hV, by decide, hql⟩

theorem kabs_ok (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (hc : WCtx V g vec m₀ t) {src len pos : Src} (hvs : srcValid src) (hvl : srcValid len)
    (hvp : srcValid pos) (hrs : noRet src = true) (hrl : noRet len = true)
    {dp : Addr} {n q : Nat} (hdp : srcValue V.E t.mem (t.gpr .x0) src = dp)
    (hn : srcValue V.E t.mem (t.gpr .x0) len = BitVec.ofNat 64 n)
    (hq : srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q) (hql : q < 136) (hnl : n < 2 ^ 64)
    (hin : Within ⟨dp, n⟩ (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ (ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) :
    WP isa (kabs v.callee d src len pos) t fun u => WCtx V g vec m₀ u ∧
      Frame [ST scr, KS scr, CK V.E] t.mem u.mem ∧
      (∀ msg, Spec.Sha3.Repr t.mem scr 136 msg → q = msg.length % 136 →
        Spec.Sha3.Repr u.mem scr 136 (msg ++ Spec.Sha3.bytesAt t.mem dp n)) ∧
      (u.gpr .x0).toNat = (q + n) % 136 := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := absArgs d src len pos)
    (by simp) (fun p hp => by
      simp only [absArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · exact hvs
      · exact hvl
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil, hrs, hrl]; rfl) (by simp [preserved]))
    fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 := hv (.x0, .loc d 0) (by simp)
  have h1 := hv (.x1, .val (.const 136)) (by simp)
  have h2 := hv (.x2, pos) (by simp)
  have h3 := hv (.x3, src) (by simp)
  have h4 := hv (.x4, len) (by simp)
  have h5 := hv (.x5, .loc d 256) (by simp)
  rw [hs.loc hc, BitVec.add_zero] at h0
  rw [hs.loc hc] at h5
  rw [hq] at h2
  rw [hdp] at h3
  rw [hn] at h4
  simp only [srcValue, VG.Proof.Ed25519.AArch64.Whole.value] at h1
  have hn' := toNat_ofNat64 hnl
  have hq' := toNat_ofNat64 (show q < 2 ^ 64 by omega_using [hql])
  have hpre := absorb_pre hV hs hu.1.sp h0 h1 h2 h3 h4 h5 hql hnl dS dK kD
  refine wcall hV hu (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v) (Nat.le_of_eq v.absorb_depth)
    hpre (covers_of fun r hr => ?_) hs.sponge_writes fun w hw hf hp => ⟨hw, ?_, fun msg hr hpos => ?_, ?_⟩
  · rcases List.mem_append.mp hr with hr | hr
    · rw [List.mem_singleton.mp hr]
      rcases hin with h | ⟨R, hR, hs⟩
      · exact .inl h
      · exact .inr ⟨R, hR, hs⟩
    · rcases hs.sponge_writes r hr with ⟨h, _⟩ | ⟨R, hR, hs⟩
      · exact .inl h
      · exact .inr ⟨R, List.mem_append_right _ hR, hs⟩
  · rw [← hm]
    exact hf.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  · have hh := hp.1 msg (by
      simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm, toNat_ofNat64 (show 136 < 2 ^ 64 by decide)]
      exact hr) (by
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h1, h2, hq',
        toNat_ofNat64 (show 136 < 2 ^ 64 by decide)]
      exact hpos)
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h3, h4, hn', hm,
      toNat_ofNat64 (show 136 < 2 ^ 64 by decide)] at hh
    exact hh
  · have hh := hp.2
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h1, h2, h4, hn', hq',
      toNat_ofNat64 (show 136 < 2 ^ 64 by decide)] at hh
    exact hh

/-! ## Padding -/

abbrev padArgs (d : Nat) (pos : Src) : List (Reg × Src) :=
  [(.x2, pos), (.x0, .loc d 0), (.x1, .val (.const 136)), (.x3, .val (.const 0x1f)), (.x4, .loc d 256)]

theorem pad_pre (hV : V.Ok) (hs : ScrOk V d scr) {u : State} (hsp : u.sp = V.E) {q : Nat}
    (h0 : u.gpr .x0 = scr) (h1 : u.gpr .x1 = BitVec.ofNat 64 136) (h2 : u.gpr .x2 = BitVec.ofNat 64 q)
    (h4 : u.gpr .x4 = scr + BitVec.ofNat 64 256) (hql : q < 136) :
    Proof.Sha3.padAArch64.pre (u.callEntry.withRegions [] [ST scr, KS scr]) := by
  have hq' := toNat_ofNat64 (show q < 2 ^ 64 by omega_using [hql])
  simp only [Proof.Sha3.padAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h4, hsp, hq']
  exact ⟨trivial, trivial, st_ks scr, hV.e16, hs.ck_st hV, hs.ck_ks hV, by decide, hql⟩

theorem kpad_ok (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (hc : WCtx V g vec m₀ t) {pos : Src} (hvp : srcValid pos) {q : Nat}
    (hq : srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 q) (hql : q < 136) :
    WP isa (kpad v.callee d pos) t fun u => WCtx V g vec m₀ u ∧
      Frame [ST scr, KS scr, CK V.E] t.mem u.mem ∧
      (∀ msg, Spec.Sha3.Repr t.mem scr 136 msg → q = msg.length % 136 →
        stateAt u.mem scr = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg)) := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := padArgs d pos)
    (by simp) (fun p hp => by
      simp only [padArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · exact hvp
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0x1f : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil]; rfl) (by simp [preserved]))
    fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 := hv (.x0, .loc d 0) (by simp)
  have h1 := hv (.x1, .val (.const 136)) (by simp)
  have h2 := hv (.x2, pos) (by simp)
  have h3 := hv (.x3, .val (.const 0x1f)) (by simp)
  have h4 := hv (.x4, .loc d 256) (by simp)
  rw [hs.loc hc, BitVec.add_zero] at h0
  rw [hs.loc hc] at h4
  rw [hq] at h2
  simp only [srcValue, VG.Proof.Ed25519.AArch64.Whole.value] at h1 h3
  have hq' := toNat_ofNat64 (show q < 2 ^ 64 by omega_using [hql])
  have hpre := pad_pre hV hs hu.1.sp h0 h1 h2 h4 hql
  refine wcall hV hu (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Nat.le_of_eq v.pad_depth)
    hpre (covers_of fun r hr => ?_) hs.sponge_writes fun w hw hf hp => ⟨hw, ?_, fun msg hr hpos => ?_⟩
  · rcases hs.sponge_writes r (by simpa using hr) with ⟨h, _⟩ | ⟨R, hR, hs⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, hs⟩
  · rw [← hm]
    exact hf.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  · have hh := hp msg (by
      simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
        State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1, hm,
        toNat_ofNat64 (show 136 < 2 ^ 64 by decide)]
      exact hr) (by
      simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
        State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h1, h2, hq',
        toNat_ofNat64 (show 136 < 2 ^ 64 by decide)]
      exact hpos)
    simp only [State.withRegions_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h3,
      toNat_ofNat64 (show 136 < 2 ^ 64 by decide)] at hh
    exact hh

/-! ## Squeezing -/

abbrev sqzArgs (d : Nat) (out : Src) : List (Reg × Src) :=
  [(.x0, .loc d 0), (.x1, .val (.const 136)), (.x2, .val (.const 0)), (.x3, out), (.x4, .val (.const 114)),
    (.x5, .loc d 256)]

theorem squeeze_pre (hV : V.Ok) (hs : ScrOk V d scr) {u : State} (hsp : u.sp = V.E) {op : Addr}
    (h0 : u.gpr .x0 = scr) (h1 : u.gpr .x1 = BitVec.ofNat 64 136) (h2 : u.gpr .x2 = BitVec.ofNat 64 0)
    (h3 : u.gpr .x3 = op) (h4 : u.gpr .x4 = BitVec.ofNat 64 114) (h5 : u.gpr .x5 = scr + BitVec.ofNat 64 256)
    (dS : Region.Disjoint ⟨op, 114⟩ (ST scr)) (dK : Region.Disjoint ⟨op, 114⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨op, 114⟩) :
    Proof.Sha3.squeezeAArch64.pre (u.callEntry.withRegions [] [ST scr, ⟨op, 114⟩, KS scr]) := by
  simp only [Proof.Sha3.squeezeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x5 ∉ linkRegs), h0, h1, h2, h3, h4, h5, hsp,
    toNat_ofNat64 (show 114 < 2 ^ 64 by decide)]
  exact ⟨trivial, trivial, dS.symm, st_ks scr, dK, hV.e16, hs.ck_st hV, kD, hs.ck_ks hV, by decide,
    by decide⟩

theorem ksqz_ok (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (hc : WCtx V g vec m₀ t) {out : Src} (hvo : srcValid out) (hro : noRet out = true) {op : Addr}
    (hop : srcValue V.E t.mem (t.gpr .x0) out = op)
    (hw : Apart V ⟨op, 114⟩ ∨ ∃ R ∈ V.outs, Within ⟨op, 114⟩ R)
    (dS : Region.Disjoint ⟨op, 114⟩ (ST scr)) (dK : Region.Disjoint ⟨op, 114⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨op, 114⟩) :
    WP isa (ksqz v.callee d out) t fun u => WCtx V g vec m₀ u ∧
      Frame [ST scr, ⟨op, 114⟩, KS scr, CK V.E] t.mem u.mem ∧
      Spec.Sha3.bytesAt u.mem op 114 = Spec.Sha3.squeezeFrom 136 (stateAt t.mem scr) 0 114 := by
  have hd := hV.ls _ hs.kept
  simp only at hd
  refine WP.seq (WP.mono (wsetup_ok hV hc (args := sqzArgs d out)
    (by simp) (fun p hp => by
      simp only [sqzArgs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨hd.1, hd.2, by decide⟩
      · show (136 : Nat) < 65536; decide
      · show (0 : Nat) < 65536; decide
      · exact hvo
      · show (114 : Nat) < 65536; decide
      · exact ⟨hd.1, hd.2, by decide⟩)
    (by simp only [retOk, List.all_cons, List.all_nil, hro]; rfl) (by simp [preserved]))
    fun u ⟨hu, hm, hv⟩ => ?_)
  have h0 := hv (.x0, .loc d 0) (by simp)
  have h1 := hv (.x1, .val (.const 136)) (by simp)
  have h2 := hv (.x2, .val (.const 0)) (by simp)
  have h3 := hv (.x3, out) (by simp)
  have h4 := hv (.x4, .val (.const 114)) (by simp)
  have h5 := hv (.x5, .loc d 256) (by simp)
  rw [hs.loc hc, BitVec.add_zero] at h0
  rw [hs.loc hc] at h5
  rw [hop] at h3
  simp only [srcValue, VG.Proof.Ed25519.AArch64.Whole.value] at h1 h2 h4
  have hws : ∀ r ∈ [ST scr, ⟨op, 114⟩, KS scr], Apart V r ∨ ∃ R ∈ V.outs, Within r R := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inr ⟨_, hs.out, st_within scr⟩
    · exact hw
    · exact .inr ⟨_, hs.out, ks_within scr⟩
  have hpre := squeeze_pre hV hs hu.1.sp h0 h1 h2 h3 h4 h5 dS dK kD
  refine wcall hV hu (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v) (Nat.le_of_eq v.squeeze_depth)
    hpre (covers_of fun r hr => ?_) hws fun w hw' hf hp => ⟨hw', ?_, ?_⟩
  · rcases hws r (by simpa using hr) with ⟨h, _⟩ | ⟨R, hR, hs⟩
    · exact .inl h
    · exact .inr ⟨R, List.mem_append_right _ hR, hs⟩
  · rw [← hm]
    exact hf.mono fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  · have hh := hp.1
    simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr,
      State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
      State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3, h4, hm,
      toNat_ofNat64 (show 136 < 2 ^ 64 by decide), toNat_ofNat64 (show 114 < 2 ^ 64 by decide),
      toNat_ofNat64 (show 0 < 2 ^ 64 by decide)] at hh
    exact hh

/-! ## Chained absorptions -/

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Spec.Sha3.Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem sha3_bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha3.bytesAt m p n).length = n := by
  simp [Spec.Sha3.bytesAt]

/-- `kabs_ok` after earlier absorptions of `msg`: the position in `x0` is that
of the message with the buffer appended. -/
theorem kabs_chain (v : Proof.Sha3.AArch64.Permutation) (hV : V.Ok) (hs : ScrOk V d scr)
    (hc : WCtx V g vec m₀ t) {src len pos : Src} (hvs : srcValid src) (hvl : srcValid len)
    (hvp : srcValid pos) (hrs : noRet src = true) (hrl : noRet len = true)
    {dp : Addr} {n : Nat} {msg : List Byte} (hdp : srcValue V.E t.mem (t.gpr .x0) src = dp)
    (hn : srcValue V.E t.mem (t.gpr .x0) len = BitVec.ofNat 64 n)
    (hq : srcValue V.E t.mem (t.gpr .x0) pos = BitVec.ofNat 64 (msg.length % 136)) (hnl : n < 2 ^ 64)
    (hin : Within ⟨dp, n⟩ (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, Within ⟨dp, n⟩ R)
    (dS : Region.Disjoint ⟨dp, n⟩ (ST scr)) (dK : Region.Disjoint ⟨dp, n⟩ (KS scr))
    (kD : (CK V.E).Disjoint ⟨dp, n⟩) (hr : Spec.Sha3.Repr t.mem scr 136 msg) :
    WP isa (kabs v.callee d src len pos) t fun u => WCtx V g vec m₀ u ∧
      Frame [ST scr, KS scr, CK V.E] t.mem u.mem ∧
      Spec.Sha3.Repr u.mem scr 136 (msg ++ Spec.Sha3.bytesAt t.mem dp n) ∧
      u.gpr .x0 = BitVec.ofNat 64 ((msg ++ Spec.Sha3.bytesAt t.mem dp n).length % 136) := by
  refine WP.mono (kabs_ok v hV hs hc hvs hvl hvp hrs hrl hdp hn hq (Nat.mod_lt _ (by decide)) hnl hin dS dK kD)
    fun u ⟨hu, hf, hp, hx⟩ => ⟨hu, hf, hp msg hr rfl, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [hx, toNat_ofNat64 (by omega_using []), List.length_append, sha3_bytesAt_length, Nat.mod_add_mod]

theorem shake256_eq (m : List Byte) (d : Nat) :
    Spec.Sha3.shake256 m d =
      Spec.Sha3.squeezeFrom 136 (Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix m)) 0 d := by
  simp only [Spec.Sha3.squeezeFrom, Nat.zero_add, List.drop_zero]
  rfl

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

end VG.Proof.Ed448.AArch64.Whole

end

end

/-!
# Ed448's complete operations on AArch64: calls of the Ed448 primitives

`vg_ed448_scalar_reduce`, `vg_ed448_scalar_base`, `vg_ed448_scalar_mul_add` and
`vg_ed448_verify_equation`, called from the frame's body with their arguments
in their registers: the callee's precondition (`*_pre`), and its
postcondition after the call (`*_call`), which keeps `WCtx`.
-/

@[expose] public section

namespace VG.Proof.Ed448.AArch64.Whole

open VG VG.AArch64
open VG.Proof.Ed25519.AArch64.Whole (Within FR CK)

variable {V : Env} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {u : State}

/-- A region the body may read: within the locals, or a buffer. -/
abbrev Readable (V : Env) (r : Region) : Prop := Within r (FR V.E) ∨ ∃ R ∈ V.ins ++ V.outs, Within r R

/-- A region the body may write: within the locals but the kept words, or a written buffer. -/
abbrev Writable (V : Env) (r : Region) : Prop := Apart V r ∨ ∃ R ∈ V.outs, Within r R

theorem Writable.readable {r : Region} (h : Writable V r) : Readable V r := by
  rcases h with ⟨h, _⟩ | ⟨R, hR, hs⟩
  · exact .inl h
  · exact .inr ⟨R, List.mem_append_right _ hR, hs⟩

theorem syms_entry (s : State) (rd wr : List Region) : (s.callEntry.withRegions rd wr).syms = s.syms := rfl

open VG.Impl.X448.AArch64.Base (combSym combWords)
open VG.Proof.X448.AArch64.Base (CombHeld)

/-- A writable region is apart from the comb's tables. -/
theorem Writable.tbl (hV : V.Ok) {r : Region} (h : Writable V r) : (TBL V.T V.words).Disjoint r := by
  rcases h with ⟨⟨off, hb, hl⟩, _⟩ | ⟨R, hR, hs⟩
  · exact hV.tfr.sub_right (Within.sub ⟨off, hb, hl⟩)
  · exact (hV.tout R hR).sub_right hs.sub

/-- The comb's tables are readable. -/
theorem tbl_readable (hV : V.Ok) : Readable V (TBL V.T V.words) :=
  .inr ⟨TBL V.T V.words, List.mem_append_left _ hV.tin, 0, (BitVec.add_zero _).symm, by simp⟩

/-- The comb's tables, as a callee's contract states them, from the body's. -/
theorem combHeld_of (hV : V.Ok) (hcfg:V.sym=combSym ∧ V.words=combWords) (hu : WCtx V g vec m₀ u) (hm : TblWords V.T m₀) {ws : List Region}
    (hw : ∀ r ∈ ws, Writable V r) (rd wr : List Region) :
    CombHeld (u.callEntry.withRegions rd wr) ws := by
  have hT : (u.callEntry.withRegions rd wr).syms combSym = V.T := by rw [←hcfg.1];exact hu.2.2
  refine ⟨fun i hi => ?_, ?_, fun r hr => ?_⟩
  · rw [hT]; have hh:=hu.tbl hV (by rw [hcfg.2];exact hm)
    rw [hcfg.2] at hh
    exact hh i hi
  · rw [hT]; simpa only [hcfg.2] using hV.tfit
  · rw [hT]; simpa only [hcfg.2] using (hw r hr).tbl hV

theorem covers_rw {rd wr : List Region} (hr : ∀ r ∈ rd, Readable V r) (hw : ∀ r ∈ wr, Writable V r) :
    Covers (rd ++ wr) (V.ins ++ FR V.E :: V.outs) :=
  covers_of fun r h => by
    rcases List.mem_append.mp h with h | h
    · exact hr r h
    · exact (hw r h).readable

theorem noFrames_depth {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth ≤ 1 :=
  VG.Proof.Ed25519.AArch64.Whole.depth_of_noFrames h

theorem reduce_noFrames : Impl.Ed448.AArch64.scalarReduce.noFrames = true := by lit_decide
theorem base_noFrames : Impl.Ed448.AArch64.scalarBase.noFrames = true :=
  Proof.Ed448.AArch64.scalarBase_noFrames
theorem mulAdd_noFrames : Impl.Ed448.AArch64.scalarMulAdd.noFrames = true := by lit_decide
/-! ## `vg_ed448_scalar_reduce(out, wide, scratch)` -/

theorem reduce_pre {op wp scr : Addr} (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = wp) (h2 : u.gpr .x2 = scr)
    (hd : Region.Disjoint ⟨wp, 114⟩ ⟨scr, 8192⟩) :
    Proof.Ed448.AArch64.scalarReduceLocal.pre
      (u.callEntry.withRegions [⟨wp, 114⟩] [⟨op, 57⟩, ⟨scr, 8192⟩]) := by
  simp only [Proof.Ed448.AArch64.scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨trivial, trivial, hd⟩

theorem reduce_call (hV : V.Ok) (hu : WCtx V g vec m₀ u) {op wp scr : Addr}
    (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = wp) (h2 : u.gpr .x2 = scr)
    (hd : Region.Disjoint ⟨wp, 114⟩ ⟨scr, 8192⟩) (hr : Readable V ⟨wp, 114⟩)
    (hwo : Writable V ⟨op, 57⟩) (hws : Writable V ⟨scr, 8192⟩) :
    WP isa (.call "vg_ed448_scalar_reduce" Impl.Ed448.AArch64.scalarReduce) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨op, 57⟩, ⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      Spec.Ed448.bytesAt w.mem op 57 = Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem wp 114) := by
  have hw : ∀ r ∈ [(⟨op, 57⟩ : Region), ⟨scr, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  refine wcall hV hu Proof.Ed448.AArch64.scalarReduce_ok (noFrames_depth reduce_noFrames)
    (reduce_pre h0 h1 h2 hd) (covers_rw (by simpa using hr) hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarReduce (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 114) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1] at hp
  exact hp

/-! ## `vg_ed448_scalar_base(out, scalar, scratch)` -/

theorem base_pre {op sp scr T : Addr} (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = sp) (h2 : u.gpr .x2 = scr)
    (hos : Region.Disjoint ⟨op, 57⟩ ⟨scr, 8192⟩) (hss : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩)
    (hn : scr.toNat + 8192 ≤ 2 ^ 64) (hT : u.syms combSym = T)
    (ht : CombHeld (u.callEntry.withRegions [⟨sp, 57⟩, TBL T] [⟨op, 57⟩, ⟨scr, 8192⟩])
      [⟨op, 57⟩, ⟨scr, 8192⟩]) :
    Proof.Ed448.AArch64.scalarBaseLocal.pre
      (u.callEntry.withRegions [⟨sp, 57⟩, TBL T] [⟨op, 57⟩, ⟨scr, 8192⟩]) := by
  have e0 := State.callEntry_gpr u (by decide : Reg.x0 ∉ linkRegs)
  have e2 := State.callEntry_gpr u (by decide : Reg.x2 ∉ linkRegs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2, syms_entry, hT,
    Proof.Ed448.AArch64.tblRegion]
  exacts [hos, hss, hn, by rw [e0, e2, h0, h2] at *; exact ht]

theorem base_call (hb : Proof.Ed448.AArch64.BaseOk) (hV : V.Ok) (hcfg:V.sym=combSym ∧ V.words=combWords) (hu : WCtx V g vec m₀ u) {op sp scr : Addr}
    (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = sp) (h2 : u.gpr .x2 = scr)
    (hos : Region.Disjoint ⟨op, 57⟩ ⟨scr, 8192⟩) (hss : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩)
    (hn : scr.toNat + 8192 ≤ 2 ^ 64) (hr : Readable V ⟨sp, 57⟩)
    (hwo : Writable V ⟨op, 57⟩) (hws : Writable V ⟨scr, 8192⟩) (hm : TblWords V.T m₀) :
    WP isa (.call "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨op, 57⟩, ⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      Spec.Ed448.bytesAt w.mem op 57 = Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem sp 57) := by
  have hw : ∀ r ∈ [(⟨op, 57⟩ : Region), ⟨scr, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  refine wcall hV hu hb.ok (noFrames_depth base_noFrames)
    (base_pre h0 h1 h2 hos hss hn (by simpa only [hcfg.1] using hu.2.2) (combHeld_of hV hcfg hu hm hw _ _))
    (covers_rw (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exact hr
      · simpa only [hcfg.2] using tbl_readable hV) hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), h0, h1] at hp
  exact hp

/-! ## `vg_ed448_scalar_mul_add(out, r, k, s, scratch)` -/

theorem mulAdd_pre {op rp kp sp scr : Addr} (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = rp)
    (h2 : u.gpr .x2 = kp) (h3 : u.gpr .x3 = sp) (h4 : u.gpr .x4 = scr)
    (hr : Region.Disjoint ⟨rp, 57⟩ ⟨scr, 8192⟩) (hk : Region.Disjoint ⟨kp, 57⟩ ⟨scr, 8192⟩)
    (hs : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩) :
    Proof.Ed448.AArch64.scalarMulAddLocal.pre
      (u.callEntry.withRegions [⟨rp, 57⟩, ⟨kp, 57⟩, ⟨sp, 57⟩] [⟨op, 57⟩, ⟨scr, 8192⟩]) := by
  simp only [Proof.Ed448.AArch64.scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3, h4]
  exact ⟨trivial, trivial, hr, hk, hs⟩

theorem mulAdd_call (hV : V.Ok) (hu : WCtx V g vec m₀ u) {op rp kp sp scr : Addr}
    (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = rp) (h2 : u.gpr .x2 = kp) (h3 : u.gpr .x3 = sp)
    (h4 : u.gpr .x4 = scr)
    (hdr : Region.Disjoint ⟨rp, 57⟩ ⟨scr, 8192⟩) (hdk : Region.Disjoint ⟨kp, 57⟩ ⟨scr, 8192⟩)
    (hds : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩)
    (hrr : Readable V ⟨rp, 57⟩) (hrk : Readable V ⟨kp, 57⟩) (hrs : Readable V ⟨sp, 57⟩)
    (hwo : Writable V ⟨op, 57⟩) (hws : Writable V ⟨scr, 8192⟩) :
    WP isa (.call "vg_ed448_scalar_mul_add" Impl.Ed448.AArch64.scalarMulAdd) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨op, 57⟩, ⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      Spec.Ed448.bytesAt w.mem op 57 = Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt u.mem rp 57)
        (Spec.Ed448.bytesAt u.mem kp 57) (Spec.Ed448.bytesAt u.mem sp 57) := by
  have hw : ∀ r ∈ [(⟨op, 57⟩ : Region), ⟨scr, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  have hrd : ∀ r ∈ [(⟨rp, 57⟩ : Region), ⟨kp, 57⟩, ⟨sp, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrr, hrk, hrs]
  refine wcall hV hu Proof.Ed448.AArch64.scalarMulAdd_ok (noFrames_depth mulAdd_noFrames)
    (mulAdd_pre h0 h1 h2 h3 h4 hdr hdk hds) (covers_rw hrd hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change Spec.Ed448.bytesAt w.mem (u.callEntry.gpr .x0) 57 =
    Spec.Ed448.scalarMulAdd (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 57)
      (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x2) 57) (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x3) 57) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3] at hp
  exact hp

end VG.Proof.Ed448.AArch64.Whole
