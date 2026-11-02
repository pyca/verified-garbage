module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCheck
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFront
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key generation on RISC-V: the call of `vg_dsa_derive_key`

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/DeriveCall.lean`). `deriveArgs`
passes `out`, the domain, x (the nonce, in the frame) and `scratch`, with
their lengths, and the frame holds `scratch_len` on the stack, so
`vg_dsa_derive_key`'s contract on the registers (`dContract`) holds, with
the regions it is given (`derRd`, `derWr`): `derive_ok` runs the call by
`WP.call` from `deriveKey_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- The regions `vg_dsa_derive_key` may read. -/
abbrev derRd (L : GL) : List Region := [L.parR, ⟨off L.F oNonce, L.ql⟩, ⟨off L.F 0, 8⟩]

/-- The regions `vg_dsa_derive_key` may write. -/
abbrev derWr (L : GL) : List Region := [L.outR, L.scrR]

/-- The registers `deriveArgs` writes. -/
def derRegs : List Reg := [.t3, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The state after `deriveArgs`. -/
structure DArgs (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  a0 : t.gpr .a0 = L.out
  a1 : t.gpr .a1 = BitVec.ofNat 64 L.ol
  a2 : t.gpr .a2 = L.par
  a3 : t.gpr .a3 = BitVec.ofNat 64 L.kl
  a4 : t.gpr .a4 = BitVec.ofNat 64 L.pl
  a5 : t.gpr .a5 = off L.F oNonce
  a6 : t.gpr .a6 = BitVec.ofNat 64 L.ql
  a7 : t.gpr .a7 = L.scr

theorem deriveArgs_ok {L : GL} {s₀ t : State} (hL : L.Ok) (hsp₀ : s₀.sp = L.sp) (hc : Ctx L s₀ t) :
    WP isa (.block deriveArgs) t fun t' => (DArgs L s₀ t' ∧ t'.mem = t.mem ∧ Keep derRegs t t') ∧
      t'.sp = t.sp := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ derRegs := by decide
  obtain ⟨i64, l64⟩ := hc.word hL hsp₀ (d := 64) (by decide) (by decide)
  have o64 := hc.out
  simp only [oOut] at o64
  have e1 := lenP_eq (pl := L.pl) (ql := L.ql) (by omega) (by omega)
  have e2 := lenQ_eq (pl := L.pl) (ql := L.ql) (by omega) (by omega)
  refine WP.mono (wp_sp (WP.keep derRegs (Q := fun t' => t'.gpr .a0 = L.out ∧
    t'.gpr .a1 = BitVec.ofNat 64 L.ol ∧ t'.gpr .a2 = L.par ∧ t'.gpr .a3 = BitVec.ofNat 64 L.kl ∧
    t'.gpr .a4 = BitVec.ofNat 64 L.pl ∧ t'.gpr .a5 = off L.F oNonce ∧ t'.gpr .a6 = BitVec.ofNat 64 L.ql ∧
    t'.gpr .a7 = L.scr ∧ t'.mem = t.mem) ?_ (by decide) (by rfl)))
    fun t' ⟨⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, am⟩, k⟩, hsp⟩ =>
      ⟨⟨⟨hc.step hL hsp k.2.1 k.2.2 (fun r hr => k.1 r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a0, a1, a2, a3, a4, a5, a6, a7⟩, am, k⟩, hsp⟩
  unfold deriveArgs
  brun [lenP, lenQ, hc.s1, hc.s2, hc.s6, e1, e2, hc.sp, exec_addSp (show 0 < 2048 by decide),
    exec_addSp (show 32 < 2048 by decide), BitVec.add_zero, oOut, oNonce, i64, l64, o64, ← BitVec.ofNat_add]
  exact ⟨by simp only [GL.ol]; congr 1; omega, by simp only [GL.kl]; congr 1; omega⟩

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
      BitVec.ofNat 64 (glOf s₀).sl := by
    show t.mem.readW (t.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
    rw [hc.sp]; exact hc.a0
  have ssp : (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))).sp = (glOf s₀).F := hc.sp
  have sargs : dStackArgs (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) =
      ⟨off (glOf s₀).F 0, 8⟩ := by
    simp only [dStackArgs, stackArgAddr, ssp]
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hsl := hL.sl
  have nwN : (off (glOf s₀).F oNonce).toNat + (glOf s₀).ql ≤ 2 ^ 64 := by
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega)]
    simp only [oNonce]; omega
  have hsp16 : (glOf s₀).F.toNat % 16 = 0 := by
    have h1 := hL.F_toNat; have h2 := hL.spF; have h3 := hL.sp16; simp only [frameBytes] at h1 h2; omega
  unfold dContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  rw [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
    g .a5 (by decide), g .a6 (by decide), g .a7 (by decide), ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6,
    ha.a7, sa0, sargs, ssp, tn (glOf s₀).ol (by simp only [GL.ol]; omega),
    tn (glOf s₀).kl (by simp only [GL.kl]; omega), tn (glOf s₀).ql (by omega), tn (glOf s₀).pl (by omega),
    tn _ hsl]
  refine ⟨rfl, rfl, hL.dOK, ?_, hL.dOS, ?_, hL.dKS, ?_, ?_, hL.nwOut, hk, nwN,
    hL.nwScr, hL.lv, by simp only [GL.ol], by simp only [GL.kl], by simp only [Spec.Dsa.scratchWords]; omega,
    hL.alS, hsp16⟩
  · exact (GL.Ok.frame_disj (d := oNonce) (n := (glOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega)).symm
  · exact (GL.Ok.frame_disj (d := 0) (n := 8) hL.dFO (by decide)).symm
  · exact GL.Ok.frame_disj (d := oNonce) (n := (glOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega)
  · exact (GL.Ok.frame_disj (d := 0) (n := 8) hL.dFS (by decide)).symm

/-- The regions given to `vg_dsa_derive_key` are within the caller's. -/
theorem derive_cov {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    Covers (derRd (glOf s₀) ++ derWr (glOf s₀)) (t.rd ++ t.wr) ∧ Covers (derWr (glOf s₀)) t.wr := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨hrd, hwr⟩ := regions_eq h
  have inF : ∀ d n, d + n ≤ frameBytes → InRegions (t.rd ++ t.wr) (off (glOf s₀).F d) n :=
    fun d n h₂ =>
      ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), frameR_contains hL rfl h₂⟩
  refine ⟨VG.Covers.of_forall fun r hr => ?_, VG.Covers.of_mem fun r hr => ?_⟩
  · simp only [derRd, derWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact VG.Covers.one (inF _ _ (by simp only [oNonce, frameBytes]; omega))
    · exact VG.Covers.one (inF _ _ (by decide))
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
  rw [g .a2 (by decide), g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), g .a6 (by decide),
    ha.a2, ha.a3, ha.a4, ha.a5, ha.a6]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (glOf s₀).pl) (by omega), Nat.mod_eq_of_lt (a := (glOf s₀).ql) (by omega),
    Nat.mod_eq_of_lt (a := (glOf s₀).kl) (by simp only [GL.kl]; omega)]

/-- What the call leaves. -/
structure Derived (L : GL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame (derWr L) t.mem t'.mem
  a0 : ((t'.gpr .a0).setWidth 32).toNat = Spec.Dsa.signStatus (dresOf L t.mem)
  out : Spec.Rsa.bytesAt t'.mem L.out L.ol = (dresOf L t.mem).getD (List.replicate L.ol 0)

theorem derive_ok {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_derive_key" Impl.Dsa.RISCV64.Derive.derive) t (Derived (glOf s₀) s₀ t) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := derive_cov h hc
  refine WP.call (k := dContract) deriveKey_correct (derive_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p0, pout⟩ := hpost
  have es := dres_eq h ha
  rw [es] at p0 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p0, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .a0) (by decide), State.callEntry_gpr t (r := .a1) (by decide), ha.a0, ha.a1,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (glOf s₀).ol) (by simp only [GL.ol]; omega)] at pout
  exact pout

end VG.Proof.Dsa.RISCV64.GK
