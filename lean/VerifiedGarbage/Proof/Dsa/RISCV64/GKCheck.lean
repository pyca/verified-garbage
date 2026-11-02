module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKEntry
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key generation on RISC-V: the check of the domain

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Check.lean`). `checkArgs` passes
the domain, its length, the lengths and `scratch` with `scratch_len` (from
the frame), so `vg_dsa_check_parameters`'s contract on the registers
(`pcContract`) holds; `check_ok` runs the call by `WP.call` from
`checkParameters_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- The regions on entry, by the call's data. -/
theorem regions_eq {s₀ : State} (h : gkContract.pre s₀) :
    s₀.rd = [(glOf s₀).parR, (glOf s₀).randR, gkStackArgs s₀] ∧
      s₀.wr = [(glOf s₀).outR, (glOf s₀).usedR, (glOf s₀).scrR] := by
  obtain ⟨-, -, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, hkl, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hrd]; simp only [glOf, GL.parR, GL.randR, GL.kl, hkl]
  · rw [hwr]; simp only [glOf, GL.outR, GL.usedR, GL.scrR, GL.ol, hol]

/-- A word of the frame is readable and aligned. -/
theorem Ctx.word {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) (hc : Ctx L s₀ t) {d : Nat}
    (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) :
    InRegions (t.rd ++ t.wr) (off L.F d) 8 ∧ (off L.F d).toNat % 8 = 0 :=
  have ⟨⟨r, hr, hc'⟩, ha⟩ := frame_word hL hsp hc.wr hd h8
  ⟨⟨r, List.mem_append_right _ hr, hc'⟩, ha⟩

/-- The registers `checkArgs` writes. -/
def checkRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .t3]

/-- The state after `checkArgs`. -/
structure CArgs (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  a0 : t.gpr .a0 = L.par
  a1 : t.gpr .a1 = BitVec.ofNat 64 L.kl
  a2 : t.gpr .a2 = BitVec.ofNat 64 L.pl
  a3 : t.gpr .a3 = BitVec.ofNat 64 L.ql
  a4 : t.gpr .a4 = L.scr
  a5 : t.gpr .a5 = BitVec.ofNat 64 L.sl

theorem checkArgs_ok {L : GL} {s₀ t : State} (hL : L.Ok) (hsp₀ : s₀.sp = L.sp) (hc : Ctx L s₀ t) :
    WP isa (.block checkArgs) t fun t' => (CArgs L s₀ t' ∧ t'.mem = t.mem ∧ Keep checkRegs t t') ∧
      t'.sp = t.sp := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ checkRegs := by decide
  obtain ⟨i0, l0⟩ := hc.word hL hsp₀ (d := 0) (by decide) (by decide)
  have o0 := hc.a0
  simp only [off, BitVec.add_zero] at i0 l0 o0
  have e1 := lenP_eq (pl := L.pl) (ql := L.ql) (by omega) (by omega)
  have e2 := lenQ_eq (pl := L.pl) (ql := L.ql) (by omega) (by omega)
  refine WP.mono (wp_sp (WP.keep checkRegs (Q := fun t' => t'.gpr .a0 = L.par ∧
    t'.gpr .a1 = BitVec.ofNat 64 L.kl ∧ t'.gpr .a2 = BitVec.ofNat 64 L.pl ∧ t'.gpr .a3 = BitVec.ofNat 64 L.ql ∧
    t'.gpr .a4 = L.scr ∧ t'.gpr .a5 = BitVec.ofNat 64 L.sl ∧ t'.mem = t.mem) ?_ (by decide) (by rfl)))
    fun t' ⟨⟨⟨a0, a1, a2, a3, a4, a5, am⟩, k⟩, hsp⟩ =>
      ⟨⟨⟨hc.step hL hsp k.2.1 k.2.2 (fun r hr => k.1 r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a0, a1, a2, a3, a4, a5⟩, am, k⟩, hsp⟩
  unfold checkArgs
  brun [lenP, lenQ, hc.s1, hc.s2, hc.s6, e1, e2, hc.sp, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero,
    i0, l0, o0, ← BitVec.ofNat_add]
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
  have hsp16 : (glOf s₀).F.toNat % 16 = 0 := by
    have h1 := hL.F_toNat; have h2 := hL.spF; have h3 := hL.sp16; simp only [frameBytes] at h1 h2; omega
  unfold pcContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ha.ctx.sp]
  rw [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
    g .a5 (by decide), ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, tn _ (by simp only [GL.kl]; omega),
    tn (glOf s₀).pl (by omega), tn (glOf s₀).ql (by omega), tn _ hsl]
  exact ⟨rfl, rfl, hL.dKS, hL.nwPar, hL.nwScr, hL.lv, rfl, by simp only [Spec.Dsa.scratchWords]; omega,
    hL.alS, hsp16⟩

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
  a0 : ((t'.gpr .a0).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem check_ok {s₀ t : State} (h : gkContract.pre s₀) (ha : CArgs (glOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_check_parameters" Impl.Dsa.RISCV64.Params.checkParameters) t
      (Checked (glOf s₀) s₀ t) := by
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
  simp only [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), ha.a0, ha.a1, ha.a2,
    ha.a3, e4, e5, e6, hc.par] at hpost'
  exact hpost'

end VG.Proof.Dsa.RISCV64.GK
