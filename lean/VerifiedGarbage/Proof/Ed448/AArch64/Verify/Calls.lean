module

public import VerifiedGarbage.Proof.Ed448.AArch64.Sparse.Local
public import VerifiedGarbage.Proof.Ed448.AArch64.Whole.Calls
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Contract

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
