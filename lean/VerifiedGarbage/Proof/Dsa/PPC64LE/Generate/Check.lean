module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key generation on PPC64LE: the call of `vg_dsa_check_parameters`

`checkArgs` passes the domain, its lengths and `scratch`, so
`vg_dsa_check_parameters`'s contract on the registers (`pcContract`) holds
with the domain to read and `scratch` to write (`check_pre`); `check_ok`
runs the call by `WP.call` from `checkParameters_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont

/-- The regions on entry, by the call's data. -/
theorem regions_eq {s₀ : State} (h : gkContract.pre s₀) :
    s₀.rd = [(glOf s₀).parR, (glOf s₀).randR, gkStackArgs s₀] ∧
      s₀.wr = [(glOf s₀).outR, (glOf s₀).usedR, (glOf s₀).scrR] := by
  obtain ⟨-, -, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, hkl, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hrd]; simp only [glOf, GL.parR, GL.randR, GL.kl, hkl]
  · rw [hwr]; simp only [glOf, GL.outR, GL.usedR, GL.scrR, GL.ol, hol]

/-- The registers `checkArgs` writes. -/
def checkRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8]

/-- The state after `checkArgs`. -/
structure CArgs (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r3 : t.gpr .r3 = L.par
  r4 : t.gpr .r4 = BitVec.ofNat 64 L.kl
  r5 : t.gpr .r5 = BitVec.ofNat 64 L.pl
  r6 : t.gpr .r6 = BitVec.ofNat 64 L.ql
  r7 : t.gpr .r7 = L.scr
  r8 : t.gpr .r8 = BitVec.ofNat 64 L.sl

theorem checkArgs_ok {L : GL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    WP isa (.block checkArgs) t fun t' => CArgs L s₀ t' ∧ t'.mem = t.mem ∧ Keep checkRegs t t' := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ checkRegs := by decide
  refine WP.mono (WP.keep checkRegs (Q := fun t' => t'.gpr .r3 = L.par ∧ t'.gpr .r4 = BitVec.ofNat 64 L.kl ∧
    t'.gpr .r5 = BitVec.ofNat 64 L.pl ∧ t'.gpr .r6 = BitVec.ofNat 64 L.ql ∧ t'.gpr .r7 = L.scr ∧
    t'.gpr .r8 = BitVec.ofNat 64 L.sl ∧ t'.mem = t.mem)
    ?_ (by decide)) fun t' ⟨⟨a3, a4, a5, a6, a7, a8, am⟩, k⟩ =>
      ⟨⟨hc.step hL k.sp k.rd k.wr (fun r hr => k.gpr r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a3, a4, a5, a6, a7, a8⟩, am, k⟩
  unfold checkArgs
  prun [hc.r19, hc.r20, hc.r21, hc.r22, hc.r26, add0, ← BitVec.ofNat_add]
  congr 1; simp only [GL.kl]; omega

/-- `vg_dsa_check_parameters`'s contract on the registers holds when it is called. -/
theorem check_pre {s₀ t : State} (h : gkContract.pre s₀) (ha : CArgs (glOf s₀) s₀ t) :
    pcContract.pre (t.callEntry.withRegions [(glOf s₀).parR] [(glOf s₀).scrR]) := by
  have hL := glOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have hsw := hL.sw
  have hsl := hL.sl
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  unfold pcContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  rw [g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide), g .r7 (by decide),
    g .r8 (by decide), ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, tn _ (by simp only [GL.kl]; omega),
    tn (glOf s₀).pl (by omega), tn (glOf s₀).ql (by omega), tn _ hsl]
  refine ⟨rfl, rfl, hL.dKS, hL.nwPar, hL.nwScr, hL.lv, rfl, by simp only [Spec.Dsa.scratchWords]; omega⟩

theorem check_cov {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    Covers ([(glOf s₀).parR] ++ [(glOf s₀).scrR]) (t.rd ++ t.wr) ∧ Covers [(glOf s₀).scrR] t.wr := by
  obtain ⟨hrd, hwr⟩ := regions_eq h
  refine ⟨VG.Covers.of_mem fun r hr => ?_, VG.Covers.of_mem fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
  · simp only [List.mem_singleton] at hr; subst hr
    rw [hc.wr, hwr]; simp

/-- Whether the domain is valid, on entry. -/
abbrev chkOf (s₀ : State) : Bool :=
  Spec.Dsa.checkParametersBytes (glOf s₀).pl (glOf s₀).ql (Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl)

/-- What the call leaves. -/
structure Checked (L : GL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame [L.scrR] t.mem t'.mem
  r3 : ((t'.gpr .r3).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem check_ok {s₀ t : State} (h : gkContract.pre s₀) (ha : CArgs (glOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_check_parameters" Impl.Dsa.PPC64LE.Params.checkParameters) t (Checked (glOf s₀) s₀ t) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := check_cov h hc
  refine WP.call (k := pcContract) checkParameters_correct (check_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, ?_⟩
  have hpost' := hpost
  simp only [pcContract, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem] at hpost'
  have e4 : (BitVec.ofNat 64 (glOf s₀).kl).toNat = (glOf s₀).kl := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [GL.kl]; omega)]
  have e5 : (BitVec.ofNat 64 (glOf s₀).pl).toNat = (glOf s₀).pl := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have e6 : (BitVec.ofNat 64 (glOf s₀).ql).toNat = (glOf s₀).ql := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide), ha.r3, ha.r4, ha.r5,
    ha.r6, e4, e5, e6, hc.par] at hpost'
  exact hpost'

end VG.Proof.Dsa.PPC64LE.GK
