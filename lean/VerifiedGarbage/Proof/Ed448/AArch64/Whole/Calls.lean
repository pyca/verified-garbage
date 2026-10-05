import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Ctx
import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.AArch64.BaseContract
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyVerified

/-!
# Ed448's complete operations on AArch64: calls of the Ed448 primitives

`vg_ed448_scalar_reduce`, `vg_ed448_scalar_base`, `vg_ed448_scalar_mul_add` and
`vg_ed448_verify_equation`, called from the frame's body with their arguments
in their registers: the callee's precondition (`*_pre`), and its
postcondition after the call (`*_call`), which keeps `WCtx`.
-/

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
theorem equation_noFrames : Impl.Ed448.AArch64.verifyEquation.noFrames = true :=
  Proof.Ed448.AArch64.verifyEquation_noFrames

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

theorem base_pre {op sp scr : Addr} (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = sp) (h2 : u.gpr .x2 = scr)
    (hos : Region.Disjoint ⟨op, 57⟩ ⟨scr, 8192⟩) (hss : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩)
    (hn : scr.toNat + 8192 ≤ 2 ^ 64) :
    Proof.Ed448.AArch64.scalarBaseLocal.pre (u.callEntry.withRegions [⟨sp, 57⟩] [⟨op, 57⟩, ⟨scr, 8192⟩]) := by
  simp only [Proof.Ed448.AArch64.scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2]
  exact ⟨trivial, trivial, hos, hss, hn⟩

theorem base_call (hb : Proof.Ed448.AArch64.BaseOk) (hV : V.Ok) (hu : WCtx V g vec m₀ u) {op sp scr : Addr}
    (h0 : u.gpr .x0 = op) (h1 : u.gpr .x1 = sp) (h2 : u.gpr .x2 = scr)
    (hos : Region.Disjoint ⟨op, 57⟩ ⟨scr, 8192⟩) (hss : Region.Disjoint ⟨sp, 57⟩ ⟨scr, 8192⟩)
    (hn : scr.toNat + 8192 ≤ 2 ^ 64) (hr : Readable V ⟨sp, 57⟩)
    (hwo : Writable V ⟨op, 57⟩) (hws : Writable V ⟨scr, 8192⟩) :
    WP isa (.call "vg_ed448_scalar_base" Impl.Ed448.AArch64.scalarBase) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨op, 57⟩, ⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      Spec.Ed448.bytesAt w.mem op 57 = Spec.Ed448.scalarBase (Spec.Ed448.bytesAt u.mem sp 57) := by
  have hw : ∀ r ∈ [(⟨op, 57⟩ : Region), ⟨scr, 8192⟩], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [hwo, hws]
  refine wcall hV hu hb.ok (noFrames_depth base_noFrames)
    (base_pre h0 h1 h2 hos hss hn) (covers_rw (by simpa using hr) hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
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

/-! ## `vg_ed448_verify_equation(pk, signature, challenge, scratch)` -/

theorem equation_pre {pk sig ch scr : Addr} (h0 : u.gpr .x0 = pk) (h1 : u.gpr .x1 = sig)
    (h2 : u.gpr .x2 = ch) (h3 : u.gpr .x3 = scr)
    (hp : Region.Disjoint ⟨pk, 57⟩ ⟨scr, 8192⟩) (hs : Region.Disjoint ⟨sig, 114⟩ ⟨scr, 8192⟩)
    (hc : Region.Disjoint ⟨ch, 57⟩ ⟨scr, 8192⟩) (hn : scr.toNat + 8192 ≤ 2 ^ 64) :
    Proof.Ed448.AArch64.verifyEquationLocal.pre
      (u.callEntry.withRegions [⟨pk, 57⟩, ⟨sig, 114⟩, ⟨ch, 57⟩] [⟨scr, 8192⟩]) := by
  simp only [Proof.Ed448.AArch64.verifyEquationLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3]
  exact ⟨trivial, trivial, hp, hs, hc, hn⟩

theorem equation_call (hR : Proof.Ed448.RecoverOk) (hE : Proof.Ed448.VerifyEqOk) (hV : V.Ok)
    (hu : WCtx V g vec m₀ u) {pk sig ch scr : Addr}
    (h0 : u.gpr .x0 = pk) (h1 : u.gpr .x1 = sig) (h2 : u.gpr .x2 = ch) (h3 : u.gpr .x3 = scr)
    (hdp : Region.Disjoint ⟨pk, 57⟩ ⟨scr, 8192⟩) (hds : Region.Disjoint ⟨sig, 114⟩ ⟨scr, 8192⟩)
    (hdc : Region.Disjoint ⟨ch, 57⟩ ⟨scr, 8192⟩) (hn : scr.toNat + 8192 ≤ 2 ^ 64)
    (hrp : Readable V ⟨pk, 57⟩) (hrs : Readable V ⟨sig, 114⟩) (hrc : Readable V ⟨ch, 57⟩)
    (hws : Writable V ⟨scr, 8192⟩) :
    WP isa (.call "vg_ed448_verify_equation" Impl.Ed448.AArch64.verifyEquation) u fun w =>
      WCtx V g vec m₀ w ∧ Frame ([⟨scr, 8192⟩] ++ [CK V.E]) u.mem w.mem ∧
      w.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem pk 57)
        (Spec.Ed448.bytesAt u.mem sig 114) (Spec.Ed448.bytesAt u.mem ch 57) then 1 else 0 := by
  have hw : ∀ r ∈ [(⟨scr, 8192⟩ : Region)], Writable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; exact hws
  have hrd : ∀ r ∈ [(⟨pk, 57⟩ : Region), ⟨sig, 114⟩, ⟨ch, 57⟩], Readable V r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [hrp, hrs, hrc]
  refine wcall hV hu (Proof.Ed448.AArch64.verifyEquation_ok hR hE) (noFrames_depth equation_noFrames)
    (equation_pre h0 h1 h2 h3 hdp hds hdc hn) (covers_rw hrd hw) hw fun w hw' hf hp => ⟨hw', hf, ?_⟩
  change w.gpr .x0 = if Spec.Ed448.verifyEquation (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x0) 57)
    (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x1) 114)
    (Spec.Ed448.bytesAt u.mem (u.callEntry.gpr .x2) 57) then 1 else 0 at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), h0, h1, h2] at hp
  exact hp

end VG.Proof.Ed448.AArch64.Whole
