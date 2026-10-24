module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Sampler
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Front
import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Fn
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Ctx
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.RsaPss

/-!
# DSA key generation on PPC64LE: the call of `vg_dsa_derive_key`

`deriveArgs` passes `out`, the domain, x (the nonce, in the frame) and
`scratch`, with their lengths, and the frame holds `scratch_len` on the
stack, so `vg_dsa_derive_key`'s contract on the registers (`dContract`)
holds, with the regions it is given (`derRd`, `derWr`): `derive_ok` runs the
call by `WP.call` from `deriveKey_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

/-- The regions `vg_dsa_derive_key` may read. -/
abbrev derRd (L : GL) : List Region := [L.parR, ⟨off L.F oNonce, L.ql⟩, ⟨off L.F oArgs, 8⟩]

/-- The regions `vg_dsa_derive_key` may write. -/
abbrev derWr (L : GL) : List Region := [L.outR, L.scrR]

/-- The registers `deriveArgs` writes. -/
def derRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The state after `deriveArgs`. -/
structure DArgs (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r3 : t.gpr .r3 = L.out
  r4 : t.gpr .r4 = BitVec.ofNat 64 L.ol
  r5 : t.gpr .r5 = L.par
  r6 : t.gpr .r6 = BitVec.ofNat 64 L.kl
  r7 : t.gpr .r7 = BitVec.ofNat 64 L.pl
  r8 : t.gpr .r8 = off L.F oNonce
  r9 : t.gpr .r9 = BitVec.ofNat 64 L.ql
  r10 : t.gpr .r10 = L.scr

theorem deriveArgs_ok {L : GL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    WP isa (.block deriveArgs) t fun t' => DArgs L s₀ t' ∧ t'.mem = t.mem ∧ Keep derRegs t t' := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ derRegs := by decide
  refine WP.mono (WP.keep derRegs (Q := fun t' => t'.gpr .r3 = L.out ∧ t'.gpr .r4 = BitVec.ofNat 64 L.ol ∧
    t'.gpr .r5 = L.par ∧ t'.gpr .r6 = BitVec.ofNat 64 L.kl ∧ t'.gpr .r7 = BitVec.ofNat 64 L.pl ∧
    t'.gpr .r8 = off L.F oNonce ∧ t'.gpr .r9 = BitVec.ofNat 64 L.ql ∧ t'.gpr .r10 = L.scr ∧ t'.mem = t.mem)
    ?_ (by decide)) fun t' ⟨⟨a3, a4, a5, a6, a7, a8, a9, a10, am⟩, k⟩ =>
      ⟨⟨hc.step hL k.sp k.rd k.wr (fun r hr => k.gpr r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a3, a4, a5, a6, a7, a8, a9, a10⟩, am, k⟩
  unfold deriveArgs
  prun [hc.r18, hc.r19, hc.r20, hc.r21, hc.r22, hc.sp, exec_addSp (show oNonce < 2 ^ 15 by decide), add0,
    ← BitVec.ofNat_add]
  refine ⟨by simp only [GL.ol]; congr 1; omega, by simp only [GL.kl]; congr 1; omega⟩

theorem dentry_stackArg (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 := rfl

/-- `vg_dsa_derive_key`'s contract on the registers holds when it is called. -/
theorem derive_pre {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t) :
    dContract.pre (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  have hF := hL.fnw
  have hsw := hL.sw
  have hk := hL.nwPar
  simp only [frameBytes] at hF
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  have sa0 : stackArg (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) 0 =
      BitVec.ofNat 64 (glOf s₀).sl := by rw [dentry_stackArg, hc.sp]; exact hc.a0
  have ssp : (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))).sp = (glOf s₀).F := hc.sp
  have sargs : dStackArgs (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) =
      ⟨off (glOf s₀).F oArgs, 8⟩ := by
    simp only [dStackArgs, stackArgAddr, ssp]; rfl
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hsl := hL.sl
  have nwN : (off (glOf s₀).F oNonce).toNat + (glOf s₀).ql ≤ 2 ^ 64 := by
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega)]
    simp only [oNonce]; omega
  unfold dContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  rw [g .r3 (by decide), g .r4 (by decide), g .r5 (by decide), g .r6 (by decide), g .r7 (by decide),
    g .r8 (by decide), g .r9 (by decide), g .r10 (by decide), ha.r3, ha.r4, ha.r5, ha.r6, ha.r7, ha.r8, ha.r9,
    ha.r10, sa0, sargs, ssp, tn (glOf s₀).ol (by simp only [GL.ol]; omega),
    tn (glOf s₀).kl (by simp only [GL.kl]; omega), tn (glOf s₀).ql (by omega), tn (glOf s₀).pl (by omega),
    tn _ hsl]
  refine ⟨by omega, rfl, rfl, hL.dOK, ?_, hL.dOS, ?_, hL.dKS, ?_, ?_, hL.nwOut, hk, nwN,
    hL.nwScr, hL.lv, by simp only [GL.ol], by simp only [GL.kl], by simp only [Spec.Dsa.scratchWords]; omega⟩
  · exact (GL.Ok.frame_disj (d := oNonce) (n := (glOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega)).symm
  · exact (GL.Ok.frame_disj (d := oArgs) (n := 8) hL.dFO (by decide)).symm
  · exact GL.Ok.frame_disj (d := oNonce) (n := (glOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega)
  · exact (GL.Ok.frame_disj (d := oArgs) (n := 8) hL.dFS (by decide)).symm

/-- The regions given to `vg_dsa_derive_key` are within the caller's. -/
theorem derive_cov {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    Covers (derRd (glOf s₀) ++ derWr (glOf s₀)) (t.rd ++ t.wr) ∧ Covers (derWr (glOf s₀)) t.wr := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨hrd, hwr⟩ := regions_eq h
  have inF : ∀ d n, 32 ≤ d → d + n ≤ frameBytes → InRegions (t.rd ++ t.wr) (off (glOf s₀).F d) n :=
    fun d n h₁ h₂ =>
      ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), frameR_contains hL rfl h₁ h₂⟩
  refine ⟨VG.Covers.of_forall fun r hr => ?_, VG.Covers.of_mem fun r hr => ?_⟩
  · simp only [derRd, derWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact VG.Covers.one (inF _ _ (by decide) (by simp only [oNonce, frameBytes]; omega))
    · exact VG.Covers.one (inF _ _ (by decide) (by decide))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
  · rw [hc.wr, hwr]
    simp only [derWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp

/-- The key `vg_dsa_derive_key` computes from the state `t` it is called in. -/
abbrev dresOf (L : GL) (m : Mem) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m L.par L.kl) (Spec.Rsa.bytesAt m (off L.F oNonce) L.ql)

/-- The key `vg_dsa_derive_key` computes, from the state the call enters. -/
theorem dres_eq {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t) :
    dRes (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) = dresOf (glOf s₀) t.mem := by
  have hL := glOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  simp only [dRes, State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr]
  rw [g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide),
    ha.r5, ha.r6, ha.r7, ha.r8, ha.r9]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (glOf s₀).pl) (by omega), Nat.mod_eq_of_lt (a := (glOf s₀).ql) (by omega),
    Nat.mod_eq_of_lt (a := (glOf s₀).kl) (by simp only [GL.kl]; omega)]

/-- What the call leaves. -/
structure Derived (L : GL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame (derWr L) t.mem t'.mem
  r3 : ((t'.gpr .r3).setWidth 32).toNat = Spec.Dsa.signStatus (dresOf L t.mem)
  out : Spec.Rsa.bytesAt t'.mem L.out L.ol = (dresOf L t.mem).getD (List.replicate L.ol 0)

theorem derive_ok {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_derive_key" Impl.Dsa.PPC64LE.Derive.derive) t (Derived (glOf s₀) s₀ t) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := derive_cov h hc
  refine WP.call (k := dContract) deriveKey_correct (derive_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p3, pout⟩ := hpost
  have es := dres_eq h ha
  rw [es] at p3 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p3, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .r3) (by decide), State.callEntry_gpr t (r := .r4) (by decide), ha.r3, ha.r4,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (glOf s₀).ol) (by simp only [GL.ol]; omega)] at pout
  exact pout

end VG.Proof.Dsa.PPC64LE.GK
