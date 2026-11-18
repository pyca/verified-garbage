module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RndSample
public import VerifiedGarbage.Proof.Dsa.RandomResult
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCheck
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSSampler
public import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveChecked
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `Dsa.RISCV64.GKDerive`, which only this module used -/

section

/-!
# DSA key generation on RISC-V: the call of `vg_dsa_derive_key_checked`

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/DeriveCall.lean`). `deriveArgs`
passes `out`, the domain, x (the nonce, in the frame) and `scratch`, with
their lengths, and the frame holds `scratch_len` on the stack, so
`vg_dsa_derive_key`'s contract on the registers (`dContract`) holds, with
the regions it is given (`derRd`, `derWr`), and, once the domain's check has
passed, the domain is unchanged, so `vg_dsa_derive_key_checked`'s
(`dcContract`) holds too (`derivec_pre`): `derive_ok` runs the call by
`WP.call` from `deriveChecked_correct`.
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
  have e1 := lenP_eq (pl := L.pl) (ql := L.ql) (by omega_using [hp]) (by omega_using [hq])
  have e2 := lenQ_eq (pl := L.pl) (ql := L.ql) (by omega_using [hp]) (by omega_using [hq])
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
  exact ⟨by simp only [GL.ol]; congr 1; omega_using [], by simp only [GL.kl]; congr 1; omega_using []⟩

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
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega_using [hF])]
    simp only [oNonce]; omega_using [hq, hF]
  have hsp16 : (glOf s₀).F.toNat % 16 = 0 := by
    have h1 := hL.F_toNat; have h2 := hL.spF; have h3 := hL.sp16; simp only [frameBytes] at h1 h2; omega_using [h1, h3]
  unfold dContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr]
  rw [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
    g .a5 (by decide), g .a6 (by decide), g .a7 (by decide), ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6,
    ha.a7, sa0, sargs, ssp, tn (glOf s₀).ol (by simp only [GL.ol]; omega_using [hp, hq]),
    tn (glOf s₀).kl (by simp only [GL.kl]; omega_using [hp, hq]), tn (glOf s₀).ql (by omega_using [hq]), tn (glOf s₀).pl (by omega_using [hp]),
    tn _ hsl]
  refine ⟨rfl, rfl, hL.dOK, ?_, hL.dOS, ?_, hL.dKS, ?_, ?_, hL.nwOut, hk, nwN,
    hL.nwScr, hL.lv, by simp only [GL.ol], by simp only [GL.kl], by simp only [Spec.Dsa.scratchWords]; omega_using [hsw],
    hL.alS, hsp16⟩
  · exact (GL.Ok.frame_disj (d := oNonce) (n := (glOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega_using [hq])).symm
  · exact (GL.Ok.frame_disj (d := 0) (n := 8) hL.dFO (by decide)).symm
  · exact GL.Ok.frame_disj (d := oNonce) (n := (glOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega_using [hq])
  · exact (GL.Ok.frame_disj (d := 0) (n := 8) hL.dFS (by decide)).symm

/-- `vg_dsa_derive_key_checked`'s contract on the registers holds when it is
called after the domain's check has passed. -/
theorem derivec_pre {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t)
    (hchk : chkOf s₀ = true) :
    dcContract.pre (t.callEntry.withRegions (derRd (glOf s₀)) (derWr (glOf s₀))) := by
  refine ⟨derive_pre h ha, ?_⟩
  have hL := glOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => State.callEntry_gpr t (r := r) hr
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr]
  rw [g .a2 (by decide), g .a3 (by decide), g .a4 (by decide), g .a6 (by decide), ha.a2, ha.a3, ha.a4, ha.a6]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (glOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (glOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (glOf s₀).kl) (by simp only [GL.kl]; omega_using [hp, hq]), ha.ctx.par]
  exact hchk

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
    · exact VG.Covers.one (inF _ _ (by simp only [oNonce, frameBytes]; omega_using [hq]))
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
  rw [Nat.mod_eq_of_lt (a := (glOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (glOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (glOf s₀).kl) (by simp only [GL.kl]; omega_using [hp, hq])]

/-- What the call leaves. -/
structure Derived (L : GL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame (derWr L) t.mem t'.mem
  a0 : ((t'.gpr .a0).setWidth 32).toNat = Spec.Dsa.signStatus (dresOf L t.mem)
  out : Spec.Rsa.bytesAt t'.mem L.out L.ol = (dresOf L t.mem).getD (List.replicate L.ol 0)

theorem derive_ok {s₀ t : State} (h : gkContract.pre s₀) (ha : DArgs (glOf s₀) s₀ t) (hchk : chkOf s₀ = true) :
    WP isa (.call "vg_dsa_derive_key_checked" deriveChecked) t (Derived (glOf s₀) s₀ t) := by
  have hL := glOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := derive_cov h hc
  refine WP.call (k := dcContract) deriveChecked_correct (derivec_pre h ha hchk) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p0, pout⟩ := hpost
  have es := dres_eq h ha
  rw [es] at p0 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p0, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .a0) (by decide), State.callEntry_gpr t (r := .a1) (by decide), ha.a0, ha.a1,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := (glOf s₀).ol) (by simp only [GL.ol]; omega_using [hp, hq])] at pout
  exact pout

end VG.Proof.Dsa.RISCV64.GK

end

end

/-! ### `Dsa.RISCV64.GKFinish`, which only this module used -/

section

/-! ### `Dsa.RISCV64.GKSampler`, which only this module used -/

section

/-!
# DSA key generation on RISC-V: the sampler's data

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Sampler.lean`). q's octets
`qbOf` (on entry); the sampler's data `seOf` for them, which are `SE.Ok`
and `SE.Q` when `q > 1`; `prepareQ_ok`: the scan of q keeps `Ctx` and
leaves its data in `s7`–`s9` (`Scanned`), from which `SEnv` follows
(`Scanned.env`), with the tape `randOf` (on entry).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Dsa.RISCV64.RS (bytesAt_drop)
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa (significant qSigOf)

/-- q's octets, on entry. -/
abbrev qbOf (L : GL) (m : Mem) : List Byte := Spec.Rsa.bytesAt m (off L.par L.pl) L.ql

/-- The tape, on entry. -/
abbrev randOf (L : GL) (m : Mem) : List Byte := Spec.Rsa.bytesAt m L.rand L.rl

/-- The sampler's data. -/
def seOf (L : GL) (qb : List Byte) : SE :=
  ⟨L.F, L.rand, L.rl, off (off L.par L.pl) (L.ql - (significant qb).1), L.pl, L.ql, (significant qb).1,
    maskOf (significant qb).2.toNat, qSigOf qb⟩

theorem qs_eq (L : GL) (m : Mem) :
    qSigOf (qbOf L m) = Spec.Rsa.bytesAt m (off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1))
      (significant (qbOf L m)).1 := by
  have hf := Dsa.significant_fits (qbOf L m)
  rw [VG.Proof.Bignum.bytesAt_length] at hf
  rw [qSigOf, VG.Proof.Bignum.bytesAt_length, bytesAt_drop _ _ (by omega_using []),
    show L.ql - (L.ql - (significant (qbOf L m)).1) = (significant (qbOf L m)).1 by omega_using [hf]]

theorem seOf_Q {L : GL} (m : Mem) (hq : 1 < Spec.Dsa.decodeBE (qbOf L m)) : (seOf L (qbOf L m)).Q (qbOf L m) :=
  ⟨VG.Proof.Bignum.bytesAt_length _ _ _, rfl, rfl, rfl, hq⟩

theorem seOf_ok {L : GL} (hL : L.Ok) (m : Mem) (hq : 1 < Spec.Dsa.decodeBE (qbOf L m)) :
    (seOf L (qbOf L m)).Ok := by
  have hQ := seOf_Q m hq
  have hW := hQ.W_pos
  have hf := Dsa.significant_fits (qbOf L m)
  rw [VG.Proof.Bignum.bytesAt_length] at hf
  have hqb := hL.ql
  have hpl := hL.pl
  have hk := hL.nwPar
  have ht : 0 < (significant (qbOf L m)).2.toNat := by
    have hn : (significant (qbOf L m)).2 ≠ 0 := fun h0 => by
      have := (Dsa.significant_nonzero (qbOf L m)).mpr h0
      simp only [seOf] at hW; omega_using [hW, this]
    exact Nat.pos_of_ne_zero fun h0 => hn (BitVec.eq_of_toNat_eq h0)
  have qoff : (off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1)) =
      off L.par (L.pl + (L.ql - (significant (qbOf L m)).1)) := off_off _ _ _
  have qsub : Region.Sub ⟨off (off L.par L.pl) (L.ql - (significant (qbOf L m)).1), (significant (qbOf L m)).1⟩
      L.parR := by
    rw [qoff]; exact VG.Offset.sub_base _ (by simp only [GL.kl]; omega_using [hf])
  refine ⟨by simp only [seOf]; omega_using [hpl], hqb.2, hW, hf, maskOf_lt (significant (qbOf L m)).2.isLt ht,
    VG.Proof.Dsa.qSigOf_length _, hL.nwRand, ?_, ?_, hL.fnw, hL.fal, ?_, ?_⟩
  · exact hL.rl
  · simp only [seOf]
    rw [qoff, off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [GL.kl] at hk; omega_using [hpl, hk])]
    simp only [GL.kl] at hk
    rw [Nat.mod_eq_of_lt (by omega_using [hqb, hpl])]; omega_using [hf, hk]
  · exact (GL.Ok.frame_disj (d := oNonce) (n := 32) hL.dFR (by decide)).symm
  · exact (GL.Ok.frame_disj (d := oNonce) (n := 32) hL.dFK (by decide)).symm.sub_left qsub

/-- After the scan of q. -/
structure Scanned (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  s7 : t.gpr .s7 = (seOf L (qbOf L s₀.mem)).qp
  s8 : t.gpr .s8 = BitVec.ofNat 64 (seOf L (qbOf L s₀.mem)).W
  s9 : 1 < Spec.Dsa.decodeBE (qbOf L s₀.mem) → t.gpr .s9 = BitVec.ofNat 64 (seOf L (qbOf L s₀.mem)).M

/-- q's octets as the key holds them in a state of the body. -/
theorem Ctx.qb {L : GL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    Spec.Rsa.bytesAt t.mem (off L.par L.pl) L.ql = qbOf L s₀.mem := by
  have := hL.ql
  rw [← VG.Proof.Dsa.bytesAt_slice t.mem L.par (total := L.kl) (by simp only [GL.kl]; omega_using []), hc.par,
    VG.Proof.Dsa.bytesAt_slice s₀.mem L.par (total := L.kl) (by simp only [GL.kl]; omega_using [])]

theorem prepareQ_ok {s₀ t : State} (h : gkContract.pre s₀) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa prepareQ t fun t' => (Scanned (glOf s₀) s₀ t' ∧
      (t'.gpr .a0 = 0 ↔ ¬ 1 < Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)) ∧ t'.mem = t.mem ∧
      Keep (([.t3, .s7, .s8] : List Reg) ++ prepRegs) t t') ∧ t'.sp = t.sp := by
  have hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  obtain ⟨hrd, -⟩ := regions_eq h
  refine wp_sp ?_
  unfold prepareQ
  refine WP.seq (WP.mono (wp_sp (WP.keep [.t3, .s7, .s8] (Q := fun t₁ => t₁.gpr .s7 = off (glOf s₀).par (glOf s₀).pl ∧
    t₁.gpr .s8 = BitVec.ofNat 64 (glOf s₀).ql ∧ t₁.mem = t.mem)
    (by
      have e1 := lenP_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
      have e2 := lenQ_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
      brun [lenP, lenQ, hc.s1, hc.s2, e1, e2])
    (by decide) (by rfl))) fun t₁ ⟨⟨⟨a7, a8, m1⟩, k1⟩, sp1⟩ => ?_)
  refine WP.mono (wp_sp (prepare_ok a7 a8 (by omega_using [hq]) hq.2 fun i hi => ?_))
    fun t' ⟨⟨⟨b8, b7, b0, b9, m2⟩, k2⟩, sp2⟩ => ?_
  · rw [k1.2.1, k1.2.2, hc.rd, off_off]
    exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
      VG.Offset.contains_base _ (by simp only [GL.kl]; omega_using [hp, hi]) (by omega_using [hq, hp, hi])⟩
  have kk := k1.trans k2
  have eqb : Spec.Rsa.bytesAt t₁.mem (off (glOf s₀).par (glOf s₀).pl) (glOf s₀).ql = qbOf (glOf s₀) s₀.mem := by
    rw [m1]; exact hc.qb hL
  rw [eqb] at b8 b7 b0 b9
  have hdis : ∀ r ∈ ctxRegs, r ∉ ([.t3, .s7, .s8] ++ prepRegs : List Reg) := by decide
  refine ⟨⟨hc.step hL (by rw [sp2, sp1]) kk.2.1 kk.2.2 (fun r hr => kk.1 r (hdis r hr))
    (by rw [m2, m1]; exact Frame.refl _ _), b7, b8, b9⟩, b0, by rw [m2, m1], kk⟩

/-- The sampler's state, after the scan, for `q > 1`. -/
theorem Scanned.env {s₀ t : State} (h : gkContract.pre s₀) (hs : Scanned (glOf s₀) s₀ t)
    (hq : 1 < Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)) :
    SEnv (seOf (glOf s₀) (qbOf (glOf s₀) s₀.mem)) (randOf (glOf s₀) s₀.mem) t := by
  have hL := glOf_ok h
  have hE := seOf_ok hL s₀.mem hq
  obtain ⟨hrd, -⟩ := regions_eq h
  have hc := hs.ctx
  have hW := hE.Wq
  have hk := hL.nwPar
  have hpl := hL.pl
  have hql := hL.ql
  refine ⟨hc.sp, hc.s2, hc.s3, hc.s4, hs.s7, hs.s8, hs.s9 hq, scr_nonce hL rfl hc.wr, fun i hi => ?_,
    fun i hi => ?_, hc.rand, ?_⟩
  · rw [hc.rd, hc.wr]
    exact ⟨(glOf s₀).randR, List.mem_append_left _ (by rw [hrd]; simp),
      VG.Offset.contains_base _ (by simp only [seOf] at hi ⊢; omega_using [hi]) (by have := hL.rl; simp only [seOf] at hi; omega_using [hi, this])⟩
  · rw [hc.rd, hc.wr]
    simp only [seOf, off_off]
    simp only [seOf] at hW hi
    have ekl : (glOf s₀).kl = 2 * (glOf s₀).pl + (glOf s₀).ql := rfl
    exact ⟨(glOf s₀).parR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
      VG.Offset.contains_base _ (by omega_using [hW, hi, ekl]) (by omega_using [hW, hpl, hql, hi])⟩
  · have := qs_eq (glOf s₀) s₀.mem
    simp only [seOf] at this ⊢
    rw [this, off_off]
    simp only [seOf] at hW
    have e1 := VG.Proof.Dsa.bytesAt_slice t.mem (glOf s₀).par (total := (glOf s₀).kl)
      (offset := (glOf s₀).pl + ((glOf s₀).ql - (significant (qbOf (glOf s₀) s₀.mem)).1))
      (len := (significant (qbOf (glOf s₀) s₀.mem)).1) (by simp only [GL.kl]; omega_using [hW])
    have e2 := VG.Proof.Dsa.bytesAt_slice s₀.mem (glOf s₀).par (total := (glOf s₀).kl)
      (offset := (glOf s₀).pl + ((glOf s₀).ql - (significant (qbOf (glOf s₀) s₀.mem)).1))
      (len := (significant (qbOf (glOf s₀) s₀.mem)).1) (by simp only [GL.kl]; omega_using [hW])
    rw [hc.par] at e1
    exact e1.symm.trans e2

end VG.Proof.Dsa.RISCV64.GK

end

end

/-!
# DSA key generation on RISC-V: the exit

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Finish.lean`). `finish_ok`:
unless the status is 1, `out` is zeroed; the nonce is zeroed, the octets
consumed are written to `used`, the status returned and the registers
restored (`Fin`); after the frame is freed, that meets the contract
(`fin_post`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.RISCV64.RS (frameR sub1_beq zeroLoopA_ok preserved_cs bytes_frame)

/-- A change within the nonce is one within `Ctx`'s regions. -/
theorem outside_frame {L : GL} (hL : L.Ok) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
    (ho : Outside L.F (oNonce + o) n m m') : Frame [L.outR, L.scrR, L.nR] m m' := by
  intro x hx
  have hF := hL.fnw
  refine ho x ?_
  obtain hn := hx L.nR (by simp)
  simp only [Region.Contains, off] at hn
  rw [VG.Offset.toNat_sub_add x L.F (by simp only [oNonce]; omega_using [])] at hn
  simp only [ofs, oNonce, frameBytes] at hn hF ⊢
  have := (x - L.F).isLt
  by_contra hc
  rw [show 2 ^ 64 - 32 + (x - L.F).toNat = (x - L.F).toNat - 32 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])] at hn
  omega

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  a0 : t.gpr .a0 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
    R.key.getD (List.replicate (glOf s₀).ol 0)
  used : t.mem.readW (glOf s₀).used 64 = BitVec.ofNat 64 R.used
  cs : ∀ i < 12, t.gpr (cs i) = s₀.gpr (cs i)
  ra : t.gpr .ra = s₀.gpr .ra
  sp : t.sp = (glOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.GenerateKeyResult} (h : gkContract.pre s₀)
    (hc : Ctx (glOf s₀) s₀ t) (h5 : t.gpr .s5 = BitVec.ofNat 64 R.used)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
      R.key.getD (List.replicate (glOf s₀).ol 0))
    (hnone : R.status ≠ 1 → R.key = none) :
    WP isa (finish outLen) t (Fin s₀ R) := by
  obtain hL := glOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (wp_sp (WP.keep (c := .block [.addi .a0 .s10 (-1)]) [.a0] (Q := fun t₁ =>
    t₁.mem = t.mem ∧ t₁.gpr .a0 = t.gpr .s10 - BitVec.ofNat 64 1) (by brun) (by decide) (by rfl)))
    fun t₁ ⟨⟨⟨m1, a0⟩, k1⟩, sp1⟩ => ?_)
  obtain hc₁ : Ctx (glOf s₀) s₀ t₁ := hc.step hL sp1 k1.2.1 k1.2.2
    (fun r hr => k1.1 r (by revert r hr; decide)) (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  obtain hout : ∀ (P : State → Prop), (∀ t₂, Ctx (glOf s₀) s₀ t₂ → Keep [.a0, .t1, .t2, .t3, .t4, .t5] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (glOf s₀).out (glOf s₀).ol =
        R.key.getD (List.replicate (glOf s₀).ol 0) → P t₂) →
      WP isa (.ite (.zero .a0) (.block []) (zeroOut outLen)) t₁ P := by
    intro P hP
    refine WP.ite (decide (R.status = 1)) (by rw [Steps.eval_zero, a0, h10, sub1_beq _ (by omega_using [hst])])
      (fun hs => ?_) (fun hs => ?_)
    · simp only [decide_eq_true_eq] at hs
      exact WP.block_nil (hP t₁ hc₁ (Keep.refl _ _) (by rw [m1]; exact hsig hs))
    · simp only [decide_eq_false_iff_not] at hs
      unfold zeroOut
      obtain ⟨i64, l64⟩ := hc₁.word hL rfl (d := 64) (by decide) (by decide)
      have o64 := hc₁.out
      simp only [oOut] at o64
      obtain e1 := lenP_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
      obtain e2 := lenQ_eq (pl := (glOf s₀).pl) (ql := (glOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
      refine WP.seq (WP.mono (wp_sp (WP.keep [.t3, .t4, .t5, .a0, .t2, .t1] (Q := fun t₂ => t₂.gpr .a0 = 0 ∧
        t₂.gpr .t4 = (glOf s₀).out ∧ t₂.gpr .t5 = BitVec.ofNat 64 (glOf s₀).ol ∧ t₂.mem = t₁.mem)
        (by
          brun [outLen, lenP, lenQ, hc₁.sp, hc₁.s2, e1, e2, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, oOut, i64, l64,
            o64, exec_li_zero, ← BitVec.ofNat_add]
          simp only [GL.ol]; congr 1; omega_using []) (by decide) (by rfl)))
        fun t₂ ⟨⟨⟨b0, b4, b5, m2⟩, k2⟩, sp2⟩ => ?_)
      obtain ho : ∀ i < (glOf s₀).ol, InRegions t₂.wr (off (glOf s₀).out i) 1 := fun i hi =>
        ⟨(glOf s₀).outR, by rw [k2.2.2, hc₁.wr, hwr]; simp,
          VG.Offset.contains_base _ (by omega_using [hi]) (by have := hL.nwOut; simp only [GL.ol] at hi this ⊢; omega_using [hq, hp, hi])⟩
      refine WP.mono (wp_sp (zeroLoopA_ok (by simp only [GL.ol]; omega_using [hq]) (by simp only [GL.ol]; omega_using [hq, hp]) ho hL.nwOut
        b0 b4 b5))
        fun t₃ ⟨⟨⟨z3, o3⟩, k3⟩, sp3⟩ => ?_
      obtain k23 := k2.trans k3
      refine hP t₃ (hc₁.step hL (sp3.trans sp2) k23.2.1 k23.2.2
        (fun r hr => k23.1 r (by revert r hr; decide)) ?_) (k23.mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega_using [hc'])
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  obtain c5 : t₂.gpr .s5 = BitVec.ofNat 64 R.used := (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans h5)
  obtain c10 : t₂.gpr .s10 = BitVec.ofNat 64 R.status :=
    (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans h10)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (wp_sp (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)))
    fun t₃ ⟨⟨⟨t0, _, o3⟩, k3⟩, sp3⟩ => ?_
  obtain hc₃ : Ctx (glOf s₀) s₀ t₃ := hc₂.step hL sp3 k3.2.1 k3.2.2 (fun r hr => k3.1 r (by revert r hr; decide))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  obtain hus : InRegions t₃.wr (glOf s₀).used 8 := by
    rw [hc₃.wr, hwr]
    exact ⟨(glOf s₀).usedR, by simp, Region.contains_self _ _⟩
  have hal := hL.alU
  obtain ⟨i72, l72⟩ := hc₃.word hL rfl (d := 72) (by decide) (by decide)
  have o72 := hc₃.used
  simp only [oUsed] at o72
  refine WP.mono (wp_sp (WP.keep (c := .block [.load .d .t4 .t0 oUsed, .store .d .s5 .t4 0, .addi .a0 .s10 0])
    [.t4, .a0] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW (glOf s₀).used (BitVec.ofNat 64 R.used) ∧ t₄.gpr .a0 = BitVec.ofNat 64 R.status)
    (by
      brun [t0, oUsed, i72, l72, o72, BitVec.add_zero, (k3.1 _ (by decide)).trans c5,
        (k3.1 _ (by decide)).trans c10, hus, hal]) (by decide) (by rfl)))
    fun t₄ ⟨⟨⟨m4, a4⟩, k4⟩, sp4⟩ => ?_
  -- The used word apart from the frame and `out`.
  obtain huR : (glOf s₀).usedR.Contains (glOf s₀).used 8 := Region.contains_self _ _
  obtain fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (glOf s₀).F d) 64 = t₃.mem.readW (off (glOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (GL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  obtain hsw : SaveW t₄ (glOf s₀).F := fun i hi =>
    frame_word hL rfl (by rw [k4.2.2, hc₃.wr]) (by simp only [oSave, frameBytes]; omega_using [hi])
      (by simp only [oSave]; omega_using [])
  refine WP.mono (restoreRegs_ok t₄ (sp4.trans hc₃.sp) hsw (v := fun i => if i < 12 then s₀.gpr (cs i) else s₀.gpr .ra)
    (fun i hi => by rw [ite_eq_left hi]; exact (fw _ (by simp only [oSave, frameBytes]; omega_using [hi])).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.ra)) fun t₅ ⟨r5, ra5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, fun i hi => by rw [r5 i hi, ite_eq_left hi], ra5, sp5.trans (sp4.trans hc₃.sp),
    rd5.trans (k4.2.1.trans hc₃.rd), wr5.trans (k4.2.2.trans hc₃.wr)⟩
  · rw [o5 .a0 (by decide) (by decide) (by decide)]; exact a4
  · rw [m5, m4, bytes_frame (rs := [(glOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by simp only [GL.ol]; omega_using [hq, hp])]
    rw [bytes_outside (o3.mono (by omega_using []) (by simp only [oNonce, frameBytes]; omega_using [])) hL.dFO
      (by simp only [GL.ol]; omega_using [hq, hp])]
    exact o2
  · rw [m5, m4, Mem.readW_writeW_self64]

/-- The exit's state, after the frame is freed and its bytes lost, meets the contract. -/
theorem fin_post {s₀ t : State} (h : gkContract.pre s₀) (hst : (gkRes s₀).status ≤ 2) (hf : Fin s₀ (gkRes s₀) t)
    (m : Mem) (u : Nat → BitVec 64) (fl : Frame [(glOf s₀).frR] t.mem m) :
    abiPreserved s₀ { freed frameBytes t with mem := m, unknowns := u } ∧
      gkContract.post s₀ { freed frameBytes t with mem := m, unknowns := u } := by
  obtain hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hol, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.ra⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    obtain ⟨i, hi, rfl⟩ := preserved_cs r hr
    exact hf.cs i hi
  · simp only [freed, hf.sp, GL.F, glOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.a0, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hst])]
  · have e0 : s₀.gpr .a0 = (glOf s₀).out := rfl
    have e1 : (s₀.gpr .a1).toNat = (glOf s₀).ol := hol
    rw [e0, e1]
    -- The `free` loses the frame's bytes, which lie apart from the output and `used`.
    exact Eq.trans (List.map_congr_left fun i hi =>
      lost_byte fl (R := (glOf s₀).outR) hL.dFO.symm (List.mem_range.mp hi)) hf.out
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) ((fl.readW (r := (glOf s₀).usedR) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hL.dFU.symm) (by decide)).trans hf.used)

end VG.Proof.Dsa.RISCV64.GK

end

end

/-!
# DSA key generation on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Fn.lean`). `generate_correct`:
`vg_dsa_generate_key` meets `gkContract`. In its frame, the entry
(`entry_ok`), the check of the domain (`checked_ok`), then for a valid
domain the scan of q (`prepareQ_ok`), the sampling (`sample_ok`) and the
derivation (`derive_wp`), and the exit (`finish_ok`) follow one another;
the callees' results are zero-extended before they are tested; the result
is `generateKeyBytes`'s (`gkRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.Random (sampleStatus)
open VG.Proof.Dsa.RISCV64.RS (sub1_beq sampleStatus_some nonce_eq zx_beq_zero)

/-- q, on entry. -/
abbrev qOf (s₀ : State) : Nat := Spec.Dsa.decodeBE (qbOf (glOf s₀) s₀.mem)

/-- The sampler's data, on entry. -/
abbrev eOf (s₀ : State) : SE := seOf (glOf s₀) (qbOf (glOf s₀) s₀.mem)

/-- The draw of x. -/
abbrev drawOf (s₀ : State) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (qOf s₀) 128 (randOf (glOf s₀) s₀.mem)

/-- The domain, on entry. -/
abbrev parOf (s₀ : State) : List Byte := Spec.Rsa.bytesAt s₀.mem (glOf s₀).par (glOf s₀).kl

/-- The key derived from `x`. -/
abbrev dkOf (s₀ : State) (x : Nat) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀) (Spec.Dsa.encodeBE (glOf s₀).ql x)

/-- The result, by the domain's check and the draw. -/
abbrev resOf (s₀ : State) : Spec.Dsa.GenerateKeyResult :=
  if chkOf s₀ then
    match (drawOf s₀).scalar with
    | none => ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used, (drawOf s₀).trace⟩
    | some x => ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩
  else ⟨none, 0, 0, [4]⟩

theorem gkRes_eq {s₀ : State} (h : gkContract.pre s₀) : gkRes s₀ = resOf s₀ := by
  have hL := glOf_ok h
  have hq := hL.ql
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hkl, -⟩ := h
  have e7 : (s₀.gpr .a4).toNat = (glOf s₀).kl := hkl
  have hq' : (Spec.Dsa.paramsBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀)).q = qOf s₀ := by
    rw [VG.Proof.Dsa.paramsBytes_eq]
    show Spec.Dsa.decodeBE _ = Spec.Dsa.decodeBE _
    rw [VG.Proof.Dsa.bytesAt_slice s₀.mem _ (by simp only [GL.kl]; omega_using [])]
  unfold gkRes
  rw [e7]
  show Spec.Dsa.generateKeyBytes (glOf s₀).pl (glOf s₀).ql (parOf s₀) (randOf (glOf s₀) s₀.mem) = _
  rw [VG.Proof.Dsa.generateKeyBytes_eq hL.lv (by rw [VG.Proof.Bignum.bytesAt_length])]
  simp only [hq']
  rfl

theorem resOf_status (s₀ : State) : (resOf s₀).status ≤ 2 := by
  unfold resOf
  split
  · split
    · dsimp only; split <;> omega_using []
    · dsimp only; unfold Spec.Dsa.signStatus; split <;> omega_using []
  · dsimp only; omega_using []

theorem resOf_none {s₀ : State} (hs : (resOf s₀).status ≠ 1) : (resOf s₀).key = none := by
  revert hs
  unfold resOf
  split
  · split
    · intro _; rfl
    · dsimp only
      intro hs
      unfold Spec.Dsa.signStatus at hs
      split at hs
      · exact absurd rfl hs
      · rename_i hn; simpa using hn
  · intro _; rfl

/-- A frame's octet is kept by a call that writes regions apart from the frame. -/
theorem frame_byte {L : GL} (hL : L.Ok) {rs : List Region} (hd : ∀ r ∈ rs, L.frR.Disjoint r) {m m' : Mem}
    (hf : Frame rs m m') {d : Nat} (hdl : d < frameBytes) : m' (off L.F d) = m (off L.F d) := by
  have hF := hL.fnw
  refine hf _ fun r hr hc => ?_
  have hin : L.frR.Contains (off L.F d) 1 :=
    VG.Offset.contains_base _ (by omega_using [hdl]) (by simp only [frameBytes] at hdl; omega_using [hdl])
  exact hd r hr _ hin hc

/-- After the check of the domain. -/
structure Chk (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off (glOf s₀).F (oNonce + j)) = 0
  a0 : ((t.gpr .a0).setWidth 32).toNat = if chkOf s₀ then 1 else 0

theorem checked_ok {s₀ t : State} (h : gkContract.pre s₀) (he : Entered (glOf s₀) s₀ t) :
    WP isa (.seq (.block checkArgs) (.call "vg_dsa_check_parameters" Impl.Dsa.RISCV64.Params.checkParameters)) t
      (Chk s₀) := by
  have hL := glOf_ok h
  refine WP.seq (WP.mono (checkArgs_ok hL rfl he.ctx) fun t₂ ⟨⟨ca, m2, k2⟩, _⟩ =>
    WP.mono (check_ok h ca) fun t₃ ck => ?_)
  refine ⟨ck.ctx, (ck.pres _ (by decide)).trans ((k2.1 _ (by decide)).trans he.s5), fun j hj => ?_, ck.a0⟩
  rw [frame_byte hL (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dFS) ck.frame
    (by simp only [oNonce, frameBytes]; omega_using [hj]), m2]
  exact he.nonce j hj

/-- The nonce's first `q_len − W` octets are zero. -/
abbrev NZero (s₀ : State) (m : Mem) : Prop :=
  ∀ j < (glOf s₀).ql - (eOf s₀).W, m (off (glOf s₀).F (oNonce + j)) = 0

/-- `s10 := 0`. -/
theorem li0_ok {s₀ t : State} (hL : (glOf s₀).Ok) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block [.li .s10 0]) t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .s10 = BitVec.ofNat 64 0 ∧ (∀ r, r ≠ .s10 → t'.gpr r = t.gpr r) ∧
        t'.mem = t.mem :=
  WP.mono (wp_sp (WP.keep (c := .block [.li .s10 0]) [.s10]
    (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .s10 = BitVec.ofNat 64 0) (by brun [exec_li_zero]; rfl) (by decide)
      (by rfl)))
    fun t' ⟨⟨⟨m', a'⟩, k⟩, sp'⟩ => ⟨hc.step hL sp' k.2.1 k.2.2 (fun r hr => k.1 r (by revert r hr; decide))
      (by rw [m']; exact Frame.refl _ _), a', fun r hr => k.1 r (by simp [hr]), m'⟩

/-- `s10 := 1`. -/
theorem li1_ok {s₀ t : State} (hL : (glOf s₀).Ok) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block [.li .s10 1]) t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .s10 = BitVec.ofNat 64 1 ∧ (∀ r, r ≠ .s10 → t'.gpr r = t.gpr r) ∧
        t'.mem = t.mem :=
  WP.mono (wp_sp (WP.keep (c := .block [.li .s10 1]) [.s10]
    (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .s10 = BitVec.ofNat 64 1)
      (by brun [exec_li_lit (show 1 < 2048 by decide)]) (by decide) (by rfl)))
    fun t' ⟨⟨⟨m', a'⟩, k⟩, sp'⟩ => ⟨hc.step hL sp' k.2.1 k.2.2 (fun r hr => k.1 r (by revert r hr; decide))
      (by rw [m']; exact Frame.refl _ _), a', fun r hr => k.1 r (by simp [hr]), m'⟩

/-- `zx`: the low word of `a0`, zero-extended. -/
theorem zx_ok {s₀ t : State} (hL : (glOf s₀).Ok) (hc : Ctx (glOf s₀) s₀ t) :
    WP isa (.block zx) t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .a0 = (t.gpr .a0 <<< 32) >>> 32 ∧ t'.mem = t.mem ∧
        ∀ r, r ≠ .a0 → t'.gpr r = t.gpr r :=
  WP.mono (wp_sp (WP.keep (c := .block zx) [.a0]
    (Q := fun t' => t'.mem = t.mem ∧ t'.gpr .a0 = (t.gpr .a0 <<< 32) >>> 32) (by brun [zx]) (by decide)
      (by rfl)))
    fun t' ⟨⟨⟨m', a'⟩, k⟩, sp'⟩ => ⟨hc.step hL sp' k.2.1 k.2.2 (fun r hr => k.1 r (by revert r hr; decide))
      (by rw [m']; exact Frame.refl _ _), a', m', fun r hr => k.1 r (by simp [hr])⟩

/-- The derivation, from the sampler's result. -/
theorem derive_wp {s₀ t : State} (h : gkContract.pre s₀) (hq : 1 < qOf s₀) (hc : Ctx (glOf s₀) s₀ t)
    (hz : NZero s₀ t.mem) (h5 : t.gpr .s5 = BitVec.ofNat 64 (drawOf s₀).used)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 (sampleStatus (drawOf s₀)))
    (hk : ∀ x, (drawOf s₀).scalar = some x → Spec.Dsa.decodeBE (cands (eOf s₀) t.mem) = x)
    (hchk : chkOf s₀ = true) :
    WP isa Impl.Dsa.RISCV64.Generate.derive t fun t' =>
      Ctx (glOf s₀) s₀ t' ∧ t'.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used ∧
        t'.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status ∧
        ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t'.mem (glOf s₀).out (glOf s₀).ol =
          (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) := by
  have hL := glOf_ok h
  have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hst := sampleStatus_le (drawOf s₀)
  unfold Impl.Dsa.RISCV64.Generate.derive
  refine WP.seq (WP.mono (wp_sp (WP.keep [.a0] (Q := fun t₂ => t₂.mem = t.mem ∧
    t₂.gpr .a0 = t.gpr .s10 - BitVec.ofNat 64 1) (by brun) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨m2, a0⟩, k2⟩, sp2⟩ => ?_)
  have c₂ : Ctx (glOf s₀) s₀ t₂ :=
    hc.step hL sp2 k2.2.1 k2.2.2 (fun r hr => k2.1 r (by revert r hr; decide)) (by rw [m2]; exact Frame.refl _ _)
  have b5 : t₂.gpr .s5 = BitVec.ofNat 64 (drawOf s₀).used := (k2.1 _ (by decide)).trans h5
  refine WP.ite (decide (sampleStatus (drawOf s₀) = 1))
    (by rw [Steps.eval_zero, a0, h10, sub1_beq _ (by omega_using [hst])]) (fun hs => ?_) (fun hs => ?_)
  · simp only [decide_eq_true_eq] at hs
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hs)
    have hR : resOf s₀ = ⟨dkOf s₀ x, Spec.Dsa.signStatus (dkOf s₀ x), (drawOf s₀).used,
        (drawOf s₀).trace ++ [if (dkOf s₀ x).isSome then 5 else 6]⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    have hnonce : Spec.Rsa.bytesAt t₂.mem (off (glOf s₀).F oNonce) (glOf s₀).ql =
        Spec.Dsa.encodeBE (glOf s₀).ql x := by
      rw [m2]
      exact nonce_eq (W := (eOf s₀).W) hE.Wq hz (hk x hx)
    refine WP.seq (WP.mono (deriveArgs_ok hL rfl c₂) fun t₃ ⟨⟨da, m3, k3⟩, _⟩ => ?_)
    refine WP.seq (WP.mono (derive_ok h da hchk) fun t₄ dv => ?_)
    have es : dresOf (glOf s₀) t₃.mem = dkOf s₀ x := by
      simp only [dresOf, dkOf, parOf]; rw [m3, c₂.par, hnonce]
    have hr0 := dv.a0
    rw [es] at hr0
    have b5' : t₄.gpr .s5 = BitVec.ofNat 64 (drawOf s₀).used :=
      (dv.pres _ (by decide)).trans ((k3.1 _ (by decide)).trans b5)
    unfold deriveFinish
    refine WP.seq (WP.mono (zx_ok hL dv.ctx) fun t₅ ⟨c₅, z5, m5, g5⟩ => ?_)
    refine WP.ite (decide (Spec.Dsa.signStatus (dkOf s₀ x) = 0))
      (by rw [Steps.eval_zero, z5, zx_beq_zero hr0]) (fun hz' => ?_) (fun hz' => ?_)
    · simp only [decide_eq_true_eq] at hz'
      refine WP.mono (li0_ok hL c₅) fun t₆ ⟨c₆, a10, g6, m6⟩ => ⟨c₆, ?_, ?_, fun _ => ?_⟩
      · rw [g6 _ (by decide), g5 _ (by decide), b5', hR]
      · rw [a10, hR]; dsimp only; rw [hz']
      · rw [m6, m5, dv.out, es, hR]
    · simp only [decide_eq_false_iff_not] at hz'
      refine WP.mono (li1_ok hL c₅) fun t₆ ⟨c₆, a10, g6, m6⟩ => ⟨c₆, ?_, ?_, fun _ => ?_⟩
      · rw [g6 _ (by decide), g5 _ (by decide), b5', hR]
      · rw [a10, hR]; dsimp only
        unfold Spec.Dsa.signStatus at hz' ⊢
        split at hz' <;> simp_all
      · rw [m6, m5, dv.out, es, hR]
  · simp only [decide_eq_false_iff_not] at hs
    have hx : (drawOf s₀).scalar = none := by
      cases hc' : (drawOf s₀).scalar with
      | none => rfl
      | some k => exact absurd (sampleStatus_some.mpr (by rw [hc']; rfl)) hs
    have hR : resOf s₀ = ⟨none, if (drawOf s₀).trace.getLast? == some 2 then 2 else 0, (drawOf s₀).used,
        (drawOf s₀).trace⟩ := by
      simp only [resOf, hchk, ite_true, hx]
    refine WP.block_nil ⟨c₂, by rw [b5, hR], ?_, fun h1 => ?_⟩
    · rw [(k2.1 _ (by decide)).trans h10, hR]
      simp only [sampleStatus, hx]
    · rw [hR] at h1 ⊢
      exact absurd h1 (by dsimp only; split <;> decide)

/-- After the steps for a valid domain. -/
structure VOut (s₀ : State) (t : State) : Prop where
  ctx : Ctx (glOf s₀) s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used
  s10 : t.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status
  out : (resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
    (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)

theorem valid_ok {s₀ t₂ : State} (h : gkContract.pre s₀) (ck : Chk s₀ t₂) (hchk : chkOf s₀ = true) :
    WP isa valid t₂ (VOut s₀) := by
  have hL := glOf_ok h
  have hql := hL.ql
  unfold valid
  refine WP.seq (WP.mono (prepareQ_ok h ck.ctx) fun t₃ ⟨⟨sc, h0, m3, k3⟩, _⟩ => ?_)
  have c5 : t₃.gpr .s5 = BitVec.ofNat 64 0 := (k3.1 _ (by decide)).trans ck.s5
  refine WP.ite (decide (¬ 1 < qOf s₀)) (by rw [Steps.eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_)
  · -- q ≤ 1: no draw.
    simp only [decide_eq_true_eq] at hq
    have hd : drawOf s₀ = ⟨none, 0, [4]⟩ := by
      show Spec.Dsa.Random.sample (qOf s₀) (127 + 1) _ = _
      rw [Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega_using [hq])]
    have hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk, hd]; rfl
    refine WP.mono (li0_ok hL sc.ctx) fun t₄ ⟨c₄, a10, g4, _⟩ => ⟨c₄, ?_, ?_, fun h1 => ?_⟩
    · rw [g4 _ (by decide), c5, hR]
    · rw [a10, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- q > 1: the draw and the derivation.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    have hQ := seOf_Q (L := glOf s₀) s₀.mem hq
    have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
    have hql' : (eOf s₀).ql ≤ 32 := hE.ql
    have hF := hL.fnw
    refine WP.seq (WP.mono (sample_ok hE hQ (sc.env h hq) c5 (Nat.zero_le _)) fun t₄ so => ?_)
    rw [List.drop_zero] at so
    have c₄ : Ctx (glOf s₀) s₀ t₄ := sc.ctx.step hL (so.env.sp.trans sc.ctx.sp.symm) so.keep.2.1 so.keep.2.2
      (fun r hr => so.keep.1 r (by revert r hr; decide))
      (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega_using [hW, hql']) so.out)
    have nz : NZero s₀ t₄.mem := fun j hj => by
      have e : ofs (eOf s₀).F (off (glOf s₀).F (oNonce + j)) = oNonce + j :=
        Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega_using [hql, hj])
      have hj' : oNonce + j < (eOf s₀).o := by
        have e2 : (eOf s₀).ql = (glOf s₀).ql := rfl
        simp only [SE.o]; omega_using [hj, e2]
      rw [so.out _ (.inl (by rw [e]; exact hj')), m3]
      exact ck.nonce j (by omega_using [hql, hj])
    have r5 : t₄.gpr .s5 = BitVec.ofNat 64 (drawOf s₀).used := by rw [so.s5, Nat.zero_add]
    exact WP.mono (derive_wp h hq c₄ nz r5 so.s10 so.cand hchk) fun t₅ ⟨c, a, b, d⟩ => ⟨c, a, b, d⟩

theorem generate_correct (s₀ : State) (h : gkContract.pre s₀) :
    ∃ tr t, Exec isa Impl.Dsa.RISCV64.Generate.code s₀ tr t ∧ abiPreserved s₀ t ∧ gkContract.post s₀ t := by
  show WP isa Impl.Dsa.RISCV64.Generate.code s₀ fun t => abiPreserved s₀ t ∧ gkContract.post s₀ t
  have hL := glOf_ok h
  have hql := hL.ql
  have hfin : ∀ t, Ctx (glOf s₀) s₀ t → t.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (glOf s₀).out (glOf s₀).ol =
        (resOf s₀).key.getD (List.replicate (glOf s₀).ol 0)) →
      WP isa (finish outLen) t fun t' =>
        ∀ m u, Frame [⟨s₀.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩] t'.mem m →
          abiPreserved s₀ { freed frameBytes t' with mem := m, unknowns := u } ∧
            gkContract.post s₀ { freed frameBytes t' with mem := m, unknowns := u } :=
    fun t hc h5 h10 hsig => WP.mono (finish_ok h hc h5 h10 (resOf_status s₀) hsig resOf_none) fun t' hf m u fl =>
      fin_post h (by rw [gkRes_eq h]; exact resOf_status s₀) (by rw [gkRes_eq h]; exact hf) m u fl
  unfold Impl.Dsa.RISCV64.Generate.code
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.RISCV64.Generate.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (checked_ok h he) fun t₂ ck => ?_)
  refine WP.seq (WP.seq (WP.mono (zx_ok hL ck.ctx) fun t₃ ⟨c₃, z3, m3, g3⟩ => ?_))
  refine WP.ite (decide ((if chkOf s₀ then 1 else 0) = 0))
    (by rw [Steps.eval_zero, z3, zx_beq_zero ck.a0]) (fun hc => ?_) (fun hc => ?_)
  · -- An invalid domain.
    have hchk : chkOf s₀ = false := by
      cases hc' : chkOf s₀ <;> simp_all
    have hR : resOf s₀ = ⟨none, 0, 0, [4]⟩ := by simp only [resOf, hchk]; rfl
    refine WP.mono (li0_ok hL c₃) fun t₄ ⟨c₄, a10, g4, _⟩ => ?_
    refine hfin t₄ c₄ ?_ ?_ fun h1 => ?_
    · rw [g4 _ (by decide), g3 _ (by decide), ck.s5, hR]
    · rw [a10, hR]
    · rw [hR] at h1; exact absurd h1 (by decide)
  · -- A valid domain.
    have hchk : chkOf s₀ = true := by
      cases hc' : chkOf s₀ <;> simp_all
    have ck₃ : Chk s₀ t₃ := ⟨c₃, by rw [g3 _ (by decide)]; exact ck.s5,
      fun j hj => by rw [m3]; exact ck.nonce j hj, by
      rw [z3, BitVec.toNat_setWidth, RS.zx_toNat, Nat.mod_eq_of_lt (BitVec.isLt _)]; exact ck.a0⟩
    exact WP.mono (valid_ok h ck₃ hchk) fun t₄ v => hfin t₄ v.ctx v.s5 v.s10 v.out

end VG.Proof.Dsa.RISCV64.GK
