module

public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubOut
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult
public import VerifiedGarbage.Proof.Dsa.RISCV64.RndSample
import VerifiedGarbage.Proof.Dsa.Random
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCtx
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSSampler
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.RandomBytes
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Covers

/-! ### `Dsa.RISCV64.RSAttempt`, which this module and modules that import it used -/

section

/-! ### `Dsa.RISCV64.RSCall`, which this module and modules that import it used -/

section

/-!
# Randomized DSA signing on RISC-V: the call of `vg_dsa_sign`

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Attempt.lean`). `callArgs`
passes `out`, the key, the nonce (in the frame) and the digest, with their
lengths, and the frame holds the arguments on the stack (`digest_len`,
`scratch`, `scratch_len`, at its start), so `vg_dsa_sign`'s contract on the
registers (`sContract`) holds, with the regions it is given (`signRd`,
`signWr`): `sign_ok` runs the call of a signer `S` (`Signer`: `vg_dsa_sign`,
or `vg_dsa_sign_prevalidated` for a validated key) by `WP.call` from its
correctness, for a key that passes the signer's precondition (`RandomValid`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- The regions `vg_dsa_sign` may read. -/
abbrev signRd (L : RL) : List Region :=
  [L.keyR, ⟨off L.F oNonce, L.ql⟩, L.digR, ⟨off L.F 0, 24⟩]

/-- The regions `vg_dsa_sign` may write. -/
abbrev signWr (L : RL) : List Region := [L.outR, L.scrR]

/-- The registers `callArgs` writes. -/
def argRegs' : List Reg := [.t3, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The state after `callArgs`. -/
structure Args (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  a0 : t.gpr .a0 = L.out
  a1 : t.gpr .a1 = BitVec.ofNat 64 (2 * L.ql)
  a2 : t.gpr .a2 = L.key
  a3 : t.gpr .a3 = BitVec.ofNat 64 L.kl
  a4 : t.gpr .a4 = BitVec.ofNat 64 L.pl
  a5 : t.gpr .a5 = off L.F oNonce
  a6 : t.gpr .a6 = BitVec.ofNat 64 L.ql
  a7 : t.gpr .a7 = L.dig

/-- A word of the frame is readable and aligned. -/
theorem Ctx.word {L : RL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) (hc : Ctx L s₀ t) {d : Nat} (hd : d + 8 ≤ frameBytes)
    (h8 : d % 8 = 0) : InRegions (t.rd ++ t.wr) (off L.F d) 8 ∧ (off L.F d).toNat % 8 = 0 :=
  have ⟨⟨r, hr, hc'⟩, ha⟩ := frame_word hL hsp hc.wr hd h8
  ⟨⟨r, List.mem_append_right _ hr, hc'⟩, ha⟩

theorem callArgs_ok {L : RL} {s₀ t : State} (hL : L.Ok) (hsp₀ : s₀.sp = L.sp) (hc : Ctx L s₀ t) :
    WP isa (.block callArgs) t fun t' => (Args L s₀ t' ∧ t'.mem = t.mem ∧ Keep argRegs' t t') ∧ t'.sp = t.sp := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ argRegs' := by decide
  obtain ⟨i64, l64⟩ := hc.word hL hsp₀ (d := 64) (by decide) (by decide)
  obtain ⟨i80, l80⟩ := hc.word hL hsp₀ (d := 80) (by decide) (by decide)
  have o64 := hc.out
  have o80 := hc.dig
  simp only [oOut, oDig] at o64 o80
  have e1 := lenP_eq (pl := L.pl) (ql := L.ql) (by omega_using [hp]) (by omega_using [hq])
  have e2 := lenQ_eq (pl := L.pl) (ql := L.ql) (by omega_using [hp]) (by omega_using [hq])
  refine WP.mono (wp_sp (WP.keep argRegs' (Q := fun t' => t'.gpr .a0 = L.out ∧
    t'.gpr .a1 = BitVec.ofNat 64 (2 * L.ql) ∧ t'.gpr .a2 = L.key ∧ t'.gpr .a3 = BitVec.ofNat 64 L.kl ∧
    t'.gpr .a4 = BitVec.ofNat 64 L.pl ∧ t'.gpr .a5 = off L.F oNonce ∧ t'.gpr .a6 = BitVec.ofNat 64 L.ql ∧
    t'.gpr .a7 = L.dig ∧ t'.mem = t.mem) ?_ (by decide) (by rfl)))
    fun t' ⟨⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, am⟩, k⟩, hsp⟩ =>
      ⟨⟨⟨hc.step hL hsp k.2.1 k.2.2 (fun r hr => k.1 r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a0, a1, a2, a3, a4, a5, a6, a7⟩, am, k⟩, hsp⟩
  unfold callArgs
  brun [lenP, lenQ, hc.s1, hc.s2, e1, e2, hc.sp, exec_addSp (show 0 < 2048 by decide),
    exec_addSp (show 32 < 2048 by decide), BitVec.add_zero, oOut, oDig, oNonce, i64, l64, i80, l80, o64, o80,
    ← BitVec.ofNat_add]
  exact ⟨by congr 1; omega_using [], by simp only [RL.kl]; congr 1; omega_using []⟩

/-- The arguments' values in the state `vg_dsa_sign` is entered in. -/
theorem entry_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := State.callEntry_gpr t h

theorem entry_stackArg (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (off t.sp (8 * i)) 64 := rfl

/-- The signature `vg_dsa_sign` computes from the state `t` it is called in. -/
abbrev sresOf (L : RL) (m : Mem) : Option (List Byte) :=
  Spec.Dsa.signBytes L.pl L.ql (Spec.Rsa.bytesAt m L.key L.kl) (Spec.Rsa.bytesAt m (off L.F oNonce) L.ql)
    (Spec.Rsa.bytesAt m L.dig L.dl)

/-- `vg_dsa_sign`'s contract on the registers holds when it is called. -/
theorem sign_pre {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    sContract.pre (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  have hF := hL.fnw
  have hsw := hL.sw
  have hk := hL.nwKey
  simp only [frameBytes] at hF
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  have sa0 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 0 =
      BitVec.ofNat 64 (rlOf s₀).dl := by rw [entry_stackArg, hc.sp]; exact hc.a0
  have sa1 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 1 = (rlOf s₀).scr := by
    rw [entry_stackArg, hc.sp]; exact hc.a1
  have sa2 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 2 =
      BitVec.ofNat 64 (rlOf s₀).sl := by rw [entry_stackArg, hc.sp]; exact hc.a2
  have ssp : (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).sp = (rlOf s₀).F := hc.sp
  have sargs : sStackArgs (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) =
      ⟨off (rlOf s₀).F 0, 24⟩ := by
    simp only [sStackArgs, stackArgAddr, ssp]
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hdl := hL.dl
  have hsl := hL.sl
  have ekl : (rlOf s₀).kl = 3 * (rlOf s₀).pl + 2 * (rlOf s₀).ql := rfl
  have nwN : (off (rlOf s₀).F oNonce).toNat + (rlOf s₀).ql ≤ 2 ^ 64 := by
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega_using [hF])]
    simp only [oNonce]; omega_using [hq, hF]
  have hsp16 : (rlOf s₀).F.toNat % 16 = 0 := by
    have h1 := hL.F_toNat; have h2 := hL.spF; have h3 := hL.sp16; simp only [frameBytes] at h1 h2; omega_using [h1, h3]
  unfold sContract
  dsimp only
  rw [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
    g .a5 (by decide), g .a6 (by decide), g .a7 (by decide), ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6,
    ha.a7, sa0, sa1, sa2, sargs, ssp, tn (2 * (rlOf s₀).ql) (by omega_using [hq]),
    tn (rlOf s₀).kl (by omega_using [hp, hq, ekl]), tn (rlOf s₀).ql (by omega_using [hq]), tn (rlOf s₀).pl (by omega_using [hp]), tn _ hdl, tn _ hsl]
  refine ⟨rfl, rfl, hL.dOK, ?_, hL.dOD, hL.dOS, ?_, hL.dKS, ?_, hL.dDS, ?_, hL.nwOut, hk, nwN, hL.nwDig,
    hL.nwScr, hL.lv, by omega_using [], by omega_using [ekl], by simp only [Spec.Dsa.scratchWords]; omega_using [hsw], hL.alS, hsp16⟩
  · exact (RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega_using [hq])).symm
  · exact (RL.Ok.frame_disj (d := 0) (n := 24) hL.dFO (by decide)).symm
  · exact RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega_using [hq])
  · exact (RL.Ok.frame_disj (d := 0) (n := 24) hL.dFS (by decide)).symm

/-- What the call leaves. -/
structure Signed (L : RL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame (signWr L) t.mem t'.mem
  a0 : ((t'.gpr .a0).setWidth 32).toNat = Spec.Dsa.signStatus (sresOf L t.mem)
  out : Spec.Rsa.bytesAt t'.mem L.out (2 * L.ql) = (sresOf L t.mem).getD (List.replicate (2 * L.ql) 0)

/-- The regions given to `vg_dsa_sign` are within the caller's. -/
theorem sign_cov {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    Covers (signRd (rlOf s₀) ++ signWr (rlOf s₀)) (t.rd ++ t.wr) ∧ Covers (signWr (rlOf s₀)) t.wr := by
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hrd, hwr⟩ := regions_eq h
  have inF : ∀ d n, d + n ≤ frameBytes → InRegions (t.rd ++ t.wr) (off (rlOf s₀).F d) n := fun d n h₂ =>
    ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), frameR_contains hL rfl h₂⟩
  have hcov : Covers (signRd (rlOf s₀) ++ signWr (rlOf s₀)) (t.rd ++ t.wr) := by
    refine VG.Covers.of_forall fun r hr => ?_
    simp only [signRd, signWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact VG.Covers.one (inF _ _ (by simp only [oNonce, frameBytes]; omega_using [hq]))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; simp)
    · exact VG.Covers.one (inF _ _ (by decide))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
  have hcovw : Covers (signWr (rlOf s₀)) t.wr := VG.Covers.of_mem fun r hr => by
    rw [hc.wr, hwr]
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  exact ⟨hcov, hcovw⟩

/-- The result `vg_dsa_sign` computes, from the state the call enters. -/
theorem sres_eq {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    sRes (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) = sresOf (rlOf s₀) t.mem := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  have hdl := hL.dl
  simp only [sRes, State.withRegions_mem, State.callEntry_mem]
  rw [g .a2 (by decide), g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), g .a6 (by decide),
    g .a7 (by decide), ha.a2, ha.a3, ha.a4, ha.a5, ha.a6, ha.a7, entry_stackArg, hc.sp]
  have a0' : t.mem.readW (off (rlOf s₀).F (8 * 0)) 64 = BitVec.ofNat 64 (rlOf s₀).dl := hc.a0
  rw [a0']
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega_using [hp, hq]), Nat.mod_eq_of_lt hdl]

/-- A signer the randomized wrapper may call: a function with `vg_dsa_sign`'s
arguments, result and public data, for a key that passes `valid`. -/
structure Signer where
  name : String
  code : Prog isa
  valid : Nat → Nat → List Byte → Bool
  correct : ∀ s, (sContractWith valid).pre s →
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (sContractWith valid).post s t
  ct : ConstantTime isa (sContractWith valid).pre (sContractWith valid).pub code
  noFrames : code.noFrames = true

/-- The call's key passes the signer's precondition. -/
def RandomValid (S : Signer) (s₀ : State) : Prop :=
  S.valid (rlOf s₀).pl (rlOf s₀).ql (Spec.Rsa.bytesAt s₀.mem (rlOf s₀).key (rlOf s₀).kl) = true

/-- The signer's contract on the registers holds when it is called. -/
theorem signWith_pre (S : Signer) {s₀ t : State} (h : rsContract.pre s₀) (hv : RandomValid S s₀)
    (ha : Args (rlOf s₀) s₀ t) :
    (sContractWith S.valid).pre (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) := by
  refine ⟨sign_pre h ha, ?_⟩
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  simp only [State.withRegions_mem, State.callEntry_mem]
  rw [g .a2 (by decide), g .a3 (by decide), g .a4 (by decide), g .a6 (by decide), ha.a2, ha.a3, ha.a4, ha.a6]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega_using [hp, hq]), ha.ctx.key]
  exact hv

theorem sign_ok (S : Signer) {s₀ t : State} (h : rsContract.pre s₀) (hv : RandomValid S s₀)
    (ha : Args (rlOf s₀) s₀ t) :
    WP isa (.call S.name S.code) t (Signed (rlOf s₀) s₀ t) := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := sign_cov h hc
  refine WP.call (k := sContractWith S.valid) (hn := S.noFrames) S.correct (signWith_pre S h hv ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p0, pout⟩ := hpost
  have es := sres_eq h ha
  rw [es] at p0 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p0, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .a0) (by decide), State.callEntry_gpr t (r := .a1) (by decide), ha.a0, ha.a1,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * (rlOf s₀).ql) (by omega_using [hq])] at pout
  exact pout

end VG.Proof.Dsa.RISCV64.RS

end

end

/-! ### `Dsa.RISCV64.RSSpec`, which this module and modules that import it used -/

section

/-!
# Randomized DSA signing on RISC-V: the specification's input

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Attempt.lean`). `inpOf`: the specification's input of a call, on entry; its subgroup order
is q's octets' (`inp_q`), its draws are the sampler's (`draw_eq`), and a
nonce of zeros then the candidate is the candidate's encoding (`nonce_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa (RandomSignInput randomSignDraw randomSignRemaining significant)

/-- The specification's input, on entry. -/
def inpOf (L : RL) (m : Mem) : RandomSignInput :=
  ⟨L.pl, L.ql, Spec.Rsa.bytesAt m L.key L.kl, Spec.Rsa.bytesAt m L.dig L.dl, randOf L m⟩

theorem inp_q {L : RL} (hL : L.Ok) (m : Mem) :
    (Spec.Dsa.privateKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m L.key L.kl)).params.q =
      Spec.Dsa.decodeBE (qbOf L m) := by
  have := hL.ql
  simp only [Spec.Dsa.privateKeyBytes, Spec.Dsa.publicKeyBytes]
  rw [VG.Proof.Dsa.bytesAt_slice m L.key (by simp only [RL.kl]; omega_using [])]

theorem draw_eq {L : RL} (hL : L.Ok) (m : Mem) (u : Nat) :
    randomSignDraw (inpOf L m) u = Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (qbOf L m)) 128 ((randOf L m).drop u) := by
  simp only [randomSignDraw, inpOf]
  rw [inp_q hL m]

theorem bytesAt_add' (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (off p a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The nonce: zeros, then a candidate `k` in its last `W` octets. -/
theorem nonce_eq {F : Addr} {m : Mem} {ql W k : Nat} (hW : W ≤ ql)
    (hz : ∀ j < ql - W, m (off F (oNonce + j)) = 0)
    (hk : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W) = k) :
    Spec.Rsa.bytesAt m (off F oNonce) ql = Spec.Dsa.encodeBE ql k := by
  have e1 : Spec.Rsa.bytesAt m (off F oNonce) (ql - W) = List.replicate (ql - W) 0 := by
    apply List.ext_getElem
    · simp [VG.Proof.Bignum.bytesAt_length]
    · intro j h₁ _
      rw [VG.Proof.Bignum.bytesAt_length] at h₁
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [show off F oNonce + BitVec.ofNat 64 j = off F (oNonce + j) by simp only [off, BitVec.add_assoc,
        BitVec.ofNat_add]]
      exact hz j h₁
  have e2 : Spec.Rsa.bytesAt m (off F oNonce) ql = List.replicate (ql - W) 0 ++
      Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W := by
    rw [show ql = (ql - W) + W by omega_using [hW], bytesAt_add', e1, Nat.add_sub_cancel]
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  rw [e2, ← hk, ← Dsa.decode_padding _ (ql - W)]
  have hl : (List.replicate (ql - W) 0 ++ Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W).length = ql := by
    simp [VG.Proof.Bignum.bytesAt_length]; omega_using [hW]
  have := Dsa.encodeBE_decodeBE (List.replicate (ql - W) 0 ++ Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W)
  rw [hl] at this
  exact this.symm

end VG.Proof.Dsa.RISCV64.RS

end

end

/-! ### `Dsa.RISCV64.RSFinish`, which this module and modules that import it used -/

section

/-!
# Randomized DSA signing on RISC-V: after a call of `vg_dsa_sign`

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Finish.lean`). `callFinish_ok`:
the result, a `u32`, zero-extended, is tested; a signature leaves the
status 1; a zero result spends an attempt, and leaves the status 4 while
one is left, else 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign

/-- The zero extension of a register's low word. -/
theorem zx_toNat (x : BitVec 64) : ((x <<< 32) >>> 32).toNat = (x.setWidth 32).toNat := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, show 2 ^ 64 = 2 ^ 32 * 2 ^ 32 by rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide)]

theorem zx_beq_zero {x : BitVec 64} {st : Nat} (h : (x.setWidth 32).toNat = st) :
    ((x <<< 32) >>> 32 == 0) = decide (st = 0) := by
  rw [← zx_toNat] at h
  by_cases hs : st = 0
  · subst hs
    simp only [decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq h
  · simp only [hs, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    rw [e] at h
    exact hs h.symm

/-- What `callFinish` leaves, after a call whose result's low word is `st`. -/
theorem callFinish_ok {s : State} {a st : Nat} (h6 : s.gpr .s6 = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ha' : a ≤ 8)
    (h0 : ((s.gpr .a0).setWidth 32).toNat = st) :
    WP isa callFinish s fun t =>
      t.mem = s.mem ∧ Keep [.a0, .s6, .s10] s t ∧
        (st ≠ 0 → t.gpr .s10 = BitVec.ofNat 64 1 ∧ t.gpr .s6 = s.gpr .s6) ∧
        (st = 0 → t.gpr .s6 = BitVec.ofNat 64 (a - 1) ∧
          t.gpr .s10 = BitVec.ofNat 64 (if a - 1 = 0 then 0 else 4)) := by
  unfold callFinish
  refine WP.seq (WP.mono (WP.keep [.a0] (Q := fun t => t.mem = s.mem ∧ t.gpr .s6 = s.gpr .s6 ∧
    t.gpr .a0 = (s.gpr .a0 <<< 32) >>> 32) (by brun) (by decide) (by rfl)) fun t₀ ⟨⟨m0, b6, b0⟩, k0⟩ => ?_)
  refine WP.ite (decide (st = 0)) (by rw [Steps.eval_zero, b0, zx_beq_zero h0]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.seq (WP.mono (WP.keep [.s6] (Q := fun t => t.mem = t₀.mem ∧ t.gpr .s6 = BitVec.ofNat 64 (a - 1))
      (by brun [b6, h6, VG.Offset.ofNat_sub_ofNat ha]) (by decide) (by rfl)) fun t₁ ⟨⟨m1, a6⟩, k1⟩ => ?_)
    refine WP.ite (decide (a - 1 ≠ 0)) (Steps.eval_nonzero_ofNat _ _ (by omega_using [ha']) a6) (fun hn => ?_) (fun hn => ?_)
    · simp only [decide_eq_true_eq] at hn
      refine WP.mono (WP.keep [.s10] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .s10 = BitVec.ofNat 64 4)
        (by brun [exec_li_lit (show 4 < 2048 by decide)]) (by decide) (by rfl))
        fun t ⟨⟨tm, t10⟩, k2⟩ => ⟨tm.trans (m1.trans m0), ((k0.trans k1).trans k2).mono (by decide),
          fun h => absurd hz h, fun _ => ⟨(k2.1 .s6 (by decide)).trans a6, by rw [t10, ite_eq_right hn]⟩⟩
    · simp only [decide_eq_false_iff_not, Decidable.not_not] at hn
      refine WP.mono (WP.keep [.s10] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .s10 = BitVec.ofNat 64 0)
        (by brun [exec_li_zero]; rfl) (by decide) (by rfl))
        fun t ⟨⟨tm, t10⟩, k2⟩ => ⟨tm.trans (m1.trans m0), ((k0.trans k1).trans k2).mono (by decide),
          fun h => absurd hz h, fun _ => ⟨(k2.1 .s6 (by decide)).trans a6, by rw [t10, ite_eq_left hn]⟩⟩
  · simp only [decide_eq_false_iff_not] at hz
    refine WP.mono (WP.keep [.s10] (Q := fun t => t.mem = t₀.mem ∧ t.gpr .s10 = BitVec.ofNat 64 1)
      (by brun [exec_li_lit (show 1 < 2048 by decide)]) (by decide) (by rfl))
      fun t ⟨⟨tm, t10⟩, k⟩ => ⟨tm.trans m0, (k0.trans k).mono (by decide),
        fun _ => ⟨t10, (k.1 .s6 (by decide)).trans b6⟩, fun h => absurd h hz⟩

end VG.Proof.Dsa.RISCV64.RS

end

end

/-!
# Randomized DSA signing on RISC-V: the attempts

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Attempt.lean`). `attempt_ok`:
from `AttInv` (the specification's remaining attempts from `u` octets
consumed, with `a` attempts left, give the result `resOf`), an attempt
either ends the loop in `AttOut` (the result's status and consumption in
`s10` and `s5`, and its signature in `out` when the status is 1) or leaves
`AttInv` with one attempt fewer.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

/-- The result, on entry. -/
abbrev resOf (s₀ : State) : Spec.Dsa.RandomSignResult := randomSignRemaining (inpOf (rlOf s₀) s₀.mem) 0 8

/-- The sampler's data, on entry. -/
abbrev eOf (s₀ : State) : SE := seOf (rlOf s₀) (qbOf (rlOf s₀) s₀.mem)

/-- q, on entry. -/
abbrev qOf (s₀ : State) : Nat := Spec.Dsa.decodeBE (qbOf (rlOf s₀) s₀.mem)

/-- The nonce's first `q_len − W` octets are zero. -/
abbrev NZero (s₀ : State) (m : Mem) : Prop :=
  ∀ j < (rlOf s₀).ql - (eOf s₀).W, m (off (rlOf s₀).F (oNonce + j)) = 0

/-- At the head of the attempts' loop, with `a` attempts left and `u` octets consumed. -/
structure AttInv (s₀ : State) (a u : Nat) (t : State) : Prop where
  sc : Scanned (rlOf s₀) s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 u
  hu : u ≤ (rlOf s₀).rl
  s6 : t.gpr .s6 = BitVec.ofNat 64 a
  ha1 : 1 ≤ a
  ha8 : a ≤ 8
  zero : NZero s₀ t.mem
  rel : RandomSignResultRel (inpOf (rlOf s₀) s₀.mem) 0 (resOf s₀) u a

/-- After the attempts. -/
structure AttOut (s₀ : State) (t : State) : Prop where
  sc : Scanned (rlOf s₀) s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used
  s10 : t.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status
  out : (resOf s₀).status = 1 →
    Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
      (resOf s₀).signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)

theorem sub1_beq : ∀ st < 3, (BitVec.ofNat 64 st - BitVec.ofNat 64 1 == 0) = decide (st = 1) := by decide

theorem sub4_beq : ∀ st < 5, (BitVec.ofNat 64 st - BitVec.ofNat 64 4 == 0) = decide (st = 4) := by decide

theorem sampleStatus_some {S : Spec.Dsa.Random.Sample} : sampleStatus S = 1 ↔ S.scalar.isSome := by
  unfold sampleStatus
  split
  · simp_all
  · rename_i h; simp only [h, Option.isSome_none, Bool.false_eq_true, iff_false]; split <;> decide

/-- The registers of `Scanned` other than `Ctx`'s. -/
theorem Scanned.step {s₀ t t' : State} (hs : Scanned (rlOf s₀) s₀ t) (hc : Ctx (rlOf s₀) s₀ t')
    (h7 : t'.gpr .s7 = t.gpr .s7) (h8 : t'.gpr .s8 = t.gpr .s8) (h9 : t'.gpr .s9 = t.gpr .s9) :
    Scanned (rlOf s₀) s₀ t' :=
  ⟨hc, h7.trans hs.s7, h8.trans hs.s8, fun hq => h9.trans (hs.s9 hq)⟩

/-- `Scanned` across a change that keeps `Ctx`'s and the scan's registers, the
stack pointer, the regions and the memory. -/
theorem Scanned.keep {s₀ t t' : State} {rs : List Reg} (hL : (rlOf s₀).Ok) (hs : Scanned (rlOf s₀) s₀ t)
    (k : Keep rs t t') (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hd : ∀ r ∈ ctxRegs ++ ([.s7, .s8, .s9] : List Reg), r ∉ rs := by decide) : Scanned (rlOf s₀) s₀ t' :=
  hs.step (hs.ctx.step hL hsp k.2.1 k.2.2 (fun r hr => k.1 r (hd r (List.mem_append_left _ hr)))
    (by rw [hm]; exact Frame.refl _ _))
    (k.1 _ (hd _ (by decide))) (k.1 _ (hd _ (by decide))) (k.1 _ (hd _ (by decide)))

/-- A change within the nonce is one within `Ctx`'s regions. -/
theorem outside_frame {L : RL} (hL : L.Ok) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
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

/-- The sampler's run keeps `Scanned` and the nonce's zeros. -/
theorem sampled {s₀ t t₁ : State} {u : Nat} {S : Spec.Dsa.Random.Sample} (h : rsContract.pre s₀)
    (hs : Scanned (rlOf s₀) s₀ t) (hz : NZero s₀ t.mem) (so : SampleOut (eOf s₀) (randOf (rlOf s₀) s₀.mem) u S t t₁)
    (hq : 1 < qOf s₀) : Scanned (rlOf s₀) s₀ t₁ ∧ NZero s₀ t₁.mem := by
  obtain hL := rlOf_ok h
  obtain hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
  have hql : (eOf s₀).ql ≤ 32 := hE.ql
  have hql' := hL.ql
  obtain hdis : ∀ r ∈ ctxRegs, r ∉ drawRegs := by decide
  refine ⟨hs.step (hs.ctx.step hL (so.env.sp.trans hs.ctx.sp.symm) so.keep.2.1 so.keep.2.2
    (fun r hr => so.keep.1 r (hdis r hr))
    (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega_using [hW, hql]) so.out))
    (so.keep.1 _ (by decide)) (so.keep.1 _ (by decide)) (so.keep.1 _ (by decide)), fun j hj => ?_⟩
  have hF := hL.fnw
  obtain e : ofs (eOf s₀).F (off (rlOf s₀).F (oNonce + j)) = oNonce + j :=
    Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega_using [hql', hj])
  obtain hj' : oNonce + j < (eOf s₀).o := by
    have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
    simp only [SE.o]; omega_using [hj, e2]
  rw [so.out _ (.inl (by rw [e]; exact hj'))]
  exact hz j hj

/-- After `[addi a0 s10 -4]`, the loop goes on exactly when the status is 4. -/
theorem tail_ok {t : State} {st : Nat} (h10 : t.gpr .s10 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [.addi .a0 .s10 (-4)]) t fun t' =>
      ((isa.eval (.zero .a0) t' = some (decide (st = 4)) ∧ t'.mem = t.mem) ∧ Keep [.a0] t t') ∧
        t'.sp = t.sp := by
  refine wp_sp (WP.keep (c := .block [.addi .a0 .s10 (-4)]) [.a0] ?_ (by decide) (by rfl))
  brun [h10]
  show some ((t.write .a0 (BitVec.ofNat 64 st - 4#64)).gpr .a0 == 0) = _
  gsimp
  rw [sub4_beq st hst]

/-- A frame's octet is kept by the call, which writes `out` and `scratch` only. -/
theorem frame_byte {L : RL} (hL : L.Ok) {m m' : Mem} (hf : Frame (signWr L) m m') {d : Nat} (hd : d < frameBytes) :
    m' (off L.F d) = m (off L.F d) := by
  have hF := hL.fnw
  refine hf _ fun r hr hc => ?_
  obtain hin : L.frR.Contains (off L.F d) 1 := VG.Offset.contains_base _ (by omega_using [hd]) (by simp only [frameBytes] at hd; omega_using [hd])
  simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hL.dFO _ hin hc
  · exact hL.dFS _ hin hc

/-- One attempt. -/
theorem attempt_ok (S : Signer) {s₀ t : State} {a u : Nat} (h : rsContract.pre s₀) (hv : RandomValid S s₀)
    (hq : 1 < qOf s₀) (hi : AttInv s₀ a u t) :
    WP isa (.seq (attempt S.name S.code) (.block [.addi .a0 .s10 (-4)])) t fun t' =>
      isa.eval (.zero .a0) t' = some (decide (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a = 4)) ∧
        (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a ≠ 4 → AttOut s₀ t') ∧
        (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a = 4 → 1 < a ∧
          AttInv s₀ (a - 1) (u + (randomSignDraw (inpOf (rlOf s₀) s₀.mem) u).used) t') := by
  obtain hL := rlOf_ok h
  obtain hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  obtain hQ := seOf_Q (L := rlOf s₀) s₀.mem hq
  obtain henv := hi.sc.env h hq
  have hql := hL.ql
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := hi.ha1; omega_using [this]⟩
  generalize hD : randomSignDraw (inpOf (rlOf s₀) s₀.mem) u = D
  obtain hD' : Spec.Dsa.Random.sample (qOf s₀) 128 ((randOf (rlOf s₀) s₀.mem).drop u) = D := by
    rw [← hD, draw_eq hL]
  obtain hDu : u + D.used ≤ (rlOf s₀).rl := by
    have := Dsa.Random.sample_used_le (qOf s₀) 128 ((randOf (rlOf s₀) s₀.mem).drop u)
    rw [hD', List.length_drop, VG.Proof.Bignum.bytesAt_length] at this
    have := hi.hu; omega_arith
  unfold attempt
  refine WP.seq (WP.seq (WP.mono (sample_ok hE hQ henv hi.s5 hi.hu) fun t₁ so => ?_))
  rw [hD'] at so
  obtain ⟨sc₁, z₁⟩ := sampled h hi.sc hi.zero so hq
  obtain hst := sampleStatus_le D
  refine WP.seq (WP.mono (wp_sp (WP.keep [.a0] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .a0 = t₁.gpr .s10 - BitVec.ofNat 64 1) (by brun) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨m2, a3⟩, k2⟩, sp2⟩ => ?_)
  obtain sc₂ : Scanned (rlOf s₀) s₀ t₂ := sc₁.keep hL k2 sp2 m2
  obtain b10 : t₂.gpr .s10 = BitVec.ofNat 64 (sampleStatus D) := (k2.1 _ (by decide)).trans so.s10
  obtain b5 : t₂.gpr .s5 = BitVec.ofNat 64 (u + D.used) := (k2.1 _ (by decide)).trans so.s5
  obtain b6 : t₂.gpr .s6 = BitVec.ofNat 64 (a' + 1) :=
    (k2.1 _ (by decide)).trans ((so.keep.1 _ (by decide)).trans hi.s6)
  refine WP.ite (decide (sampleStatus D = 1)) (by rw [Steps.eval_zero, a3, so.s10, sub1_beq _ (by omega_using [hst])])
    (fun hs => ?_) (fun hs => ?_)
  · -- A nonce: the call.
    simp only [decide_eq_true_eq] at hs
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hs)
    obtain hnonce : Spec.Rsa.bytesAt t₂.mem (off (rlOf s₀).F oNonce) (rlOf s₀).ql = Spec.Dsa.encodeBE (rlOf s₀).ql k := by
      rw [m2]
      exact nonce_eq (W := (eOf s₀).W) hE.Wq z₁ (so.cand k hk)
    refine WP.seq (WP.mono (callArgs_ok hL rfl sc₂.ctx) fun t₃ ⟨⟨ha3, m3, k3⟩, sp3⟩ => ?_)
    refine WP.seq (WP.mono (sign_ok S h hv ha3) fun t₄ sg => ?_)
    obtain es : sresOf (rlOf s₀) t₃.mem = Spec.Dsa.signBytes (rlOf s₀).pl (rlOf s₀).ql
        (inpOf (rlOf s₀) s₀.mem).key (Spec.Dsa.encodeBE (rlOf s₀).ql k) (inpOf (rlOf s₀) s₀.mem).digest := by
      simp only [sresOf, inpOf]; rw [m3, sc₂.ctx.key, sc₂.ctx.digB, hnonce]
    obtain b6' : t₄.gpr .s6 = BitVec.ofNat 64 (a' + 1) :=
      (sg.pres _ (by decide)).trans ((k3.1 _ (by decide)).trans b6)
    obtain sc₄ : Scanned (rlOf s₀) s₀ t₄ := sc₂.step sg.ctx ((sg.pres _ (by decide)).trans (k3.1 _ (by decide)))
      ((sg.pres _ (by decide)).trans (k3.1 _ (by decide))) ((sg.pres _ (by decide)).trans (k3.1 _ (by decide)))
    obtain b5' : t₄.gpr .s5 = BitVec.ofNat 64 (u + D.used) :=
      (sg.pres _ (by decide)).trans ((k3.1 _ (by decide)).trans b5)
    obtain z₄ : NZero s₀ t₄.mem := fun j hj => by
      rw [frame_byte hL sg.frame (by simp only [oNonce, frameBytes]; omega_using [hql, hj]), m3, m2]; exact z₁ j hj
    have hr0 := sg.a0
    rw [es] at hr0
    refine WP.mono (wp_sp (callFinish_ok b6' (by omega_using []) hi.ha8 hr0)) fun t₅ ⟨⟨m5, k5, hs1, hs0⟩, sp5⟩ => ?_
    obtain sc₅ : Scanned (rlOf s₀) s₀ t₅ := sc₄.keep hL k5 sp5 m5
    obtain b5'' : t₅.gpr .s5 = BitVec.ofNat 64 (u + D.used) := (k5.1 _ (by decide)).trans b5'
    obtain hdk' : (randomSignDraw (inpOf (rlOf s₀) s₀.mem) u).scalar = some k := by rw [hD]; exact hk
    cases hsr : Spec.Dsa.signBytes (rlOf s₀).pl (rlOf s₀).ql (inpOf (rlOf s₀) s₀.mem).key
        (Spec.Dsa.encodeBE (rlOf s₀).ql k) (inpOf (rlOf s₀) s₀.mem).digest with
    | some sig =>
      obtain ⟨c10, -⟩ := hs1 (by rw [hsr]; exact Nat.one_ne_zero)
      obtain ⟨rsig, rst, ru⟩ := hi.rel.success hdk' hsr
      rw [hD] at ru
      obtain hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = 1 := by
        simp only [randomSignAttemptStatus, hdk']
        simp only [inpOf] at hsr ⊢
        simp [hsr]
      refine WP.mono (tail_ok c10 (by decide)) fun t₆ ⟨⟨⟨ev, m6⟩, k6⟩, sp6⟩ =>
        ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; cases h4⟩
      refine ⟨sc₅.keep hL k6 sp6 m6, ?_, ?_, fun _ => ?_⟩
      · rw [k6.1 _ (by decide), b5'', ← ru, Nat.zero_add]
      · rw [k6.1 _ (by decide), c10, rst]
      · rw [m6, m5, sg.out, es, hsr, rsig]
    | none =>
      obtain ⟨c6, c10⟩ := hs0 (by rw [hsr]; rfl)
      obtain rel' := hi.rel.retry hdk' hsr
      rw [hD] at rel'
      by_cases ha0 : a' = 0
      · subst ha0
        rw [ite_eq_left rfl] at c10
        obtain ⟨-, rst, ru⟩ := rel'.exhausted
        obtain hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (0 + 1) = 0 := by
          simp only [randomSignAttemptStatus, hdk']
          simp only [inpOf] at hsr ⊢
          simp [hsr]
        refine WP.mono (tail_ok c10 (by decide)) fun t₆ ⟨⟨⟨ev, m6⟩, k6⟩, sp6⟩ =>
          ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; cases h4⟩
        refine ⟨sc₅.keep hL k6 sp6 m6, ?_, ?_, fun h1 => absurd (rst ▸ h1) (by decide)⟩
        · rw [k6.1 _ (by decide), b5'', ← ru, Nat.zero_add]
        · rw [k6.1 _ (by decide), c10, rst]
      · rw [Nat.add_sub_cancel, ite_eq_right ha0] at c10
        obtain hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = 4 := by
          simp only [randomSignAttemptStatus, hdk']
          simp only [inpOf] at hsr ⊢
          simp [hsr, ha0]
        refine WP.mono (tail_ok c10 (by decide)) fun t₆ ⟨⟨⟨ev, m6⟩, k6⟩, sp6⟩ =>
          ⟨by rw [ev, hAS], fun h => absurd hAS h, fun _ => ⟨by omega_using [ha0], ?_⟩⟩
        rw [Nat.add_sub_cancel]
        refine ⟨sc₅.keep hL k6 sp6 m6, (k6.1 _ (by decide)).trans b5'', hDu,
          (k6.1 _ (by decide)).trans (c6.trans (by rw [Nat.add_sub_cancel])), by omega_using [ha0],
          by have := hi.ha8; omega_using [this], ?_, rel'⟩
        intro j hj
        rw [m6, m5]; exact z₄ j hj
  · -- No nonce: the sampler's status.
    simp only [decide_eq_false_iff_not] at hs
    obtain hk : D.scalar = none := by
      cases hc : D.scalar with
      | none => rfl
      | some k => exact absurd (sampleStatus_some.mpr (by rw [hc]; rfl)) hs
    obtain ⟨rs, rst, ru⟩ := hi.rel.sample_none (hD ▸ hk)
    rw [hD] at rst ru
    obtain hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = sampleStatus D := by
      unfold randomSignAttemptStatus
      rw [hD]
      simp only [hk]
    refine WP.mono (WP.block_nil rfl) fun t₃ e₃ => ?_
    subst e₃
    refine WP.mono (tail_ok b10 (by omega_using [hst])) fun t₄ ⟨⟨⟨ev, m4⟩, k4⟩, sp4⟩ =>
      ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; omega⟩
    · refine ⟨sc₂.keep hL k4 sp4 m4, ?_, ?_, fun h1 => absurd (rst ▸ h1) hs⟩
      · rw [k4.1 _ (by decide), b5, ← ru, Nat.zero_add]
      · rw [k4.1 _ (by decide), b10, rst]

end VG.Proof.Dsa.RISCV64.RS

end

end

/-!
# Randomized DSA signing on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/CT.lean`).
`randomSignWith_correct`: the randomized signer over a signer `S`
(`Signer`) meets `rsContract`, for a key `S` accepts. In its
frame, the entry (`entry_ok`), the scan of q (`prepareQ_ok`), the attempts
(`attempts_ok`, or none when `q ≤ 1`) and the exit (`finish_ok`) follow one
another; the result is `randomSignBytes`'s (`rsRes_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

theorem attempts_ok (S : Signer) {s₀ : State} (h : rsContract.pre s₀) (hv : RandomValid S s₀) (hq : 1 < qOf s₀) :
    ∀ a u t, AttInv s₀ a u t → WP isa (attempts S.name S.code) t (AttOut s₀) := by
  intro a u t hi
  unfold attempts
  refine WP.loop (M := isa) (fun n (t : State) => ∃ u, AttInv s₀ n u t) (fun n t ⟨u, hi⟩ =>
    WP.mono (attempt_ok S h hv hq hi) fun t' ⟨e, ho, hc⟩ => ?_) a t ⟨u, hi⟩
  by_cases h4 : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u n = 4
  · obtain ⟨hn, hi'⟩ := hc h4
    exact .inr ⟨by rw [e, decide_eq_true h4], n - 1, by omega_using [hn], _, hi'⟩
  · exact .inl ⟨by rw [e, decide_eq_false h4], ho h4⟩

/-- The specification's result is the attempts'. -/
theorem rsRes_eq {s₀ : State} (h : rsContract.pre s₀) : rsRes s₀ = resOf s₀ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    lv, -, hkl, -⟩ := h
  simp only [rsRes, resOf, randomSignRemaining, inpOf, randOf, Spec.Dsa.randomSignBytes, List.drop_zero]
  rw [ite_eq_right (by
    simp only [decide_eq_true lv, Bool.not_true, VG.Proof.Bignum.bytesAt_length, hkl, Bool.false_or,
      bne_self_eq_false, Bool.false_eq_true, not_false_eq_true])]
  simp only [rlOf, RL.kl, hkl]

/-- The count loop of `zeroOut`: the `N` octets at `dst` (`t4`) := 0 (`a0`). -/
theorem zeroLoopA_ok {s : State} {dst : Addr} {N : Nat} (hN : 0 < N) (hN' : N < 2 ^ 64)
    (ho : ∀ i < N, InRegions s.wr (off dst i) 1) (hno : dst.toNat + N ≤ 2 ^ 64)
    (h0 : s.gpr .a0 = 0) (h4 : s.gpr .t4 = dst) (h5 : s.gpr .t5 = BitVec.ofNat 64 N) :
    WP isa (Impl.Bignum.RISCV64.countLoop .t5 [.store .b .a0 .t4 0, .addi .t4 .t4 1]) s fun t =>
      (Spec.Rsa.bytesAt t.mem dst N = List.replicate N 0 ∧ Outside dst 0 N s.mem t.mem) ∧
        Keep [.t4, .t5] s t := by
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t4 = off dst i ∧ Outside dst 0 i s.mem t.mem ∧ (∀ i' < i, t.mem (off dst i') = 0) ∧
      Keep [.t4, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.store .b .a0 .t4 0, .addi .t4 .t4 1] ++
      ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := N) hN' hN Inv (fun i hi t ⟨t4, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [h4, off, BitVec.add_zero], Outside.refl _ _ _ _, fun _ h => absurd h (by omega_using []), Keep.refl _ _⟩ h5)
    fun t ⟨_, tout, tb, tk⟩ => ⟨⟨?_, tout⟩, tk⟩
  · have t0 : t.gpr .a0 = 0 := (tk.gpr (by decide)).trans h0
    have hw : InRegions t.wr (off dst i) 1 := by rw [tk.2.2]; exact ho i hi
    have hst : WP isa (.block [.store .b .a0 .t4 0, .addi .t4 .t4 1, .addi .t5 .t5 (-1)]) t fun t' =>
        t' = (({ t with mem := t.mem.write (off dst i) 1 ((0 : BitVec 64).setWidth 8) } : State).write .t4
          (off dst (i + 1))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1) := by
      brun [t4, t0, hw, add_ofNat_zero]
    refine WP.mono hst fun t' e => ?_
    subst e
    have hw1 := write1_outside t.mem dst (d := i) ((0 : BitVec 64).setWidth 8) (by omega_using [hN', hi])
    refine ⟨⟨by gsimp, ?_, ?_, ?_⟩, by gsimp⟩
    · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_using [])).trans (hw1.mono (by omega_using []) (by omega_using []))
    · intro i' hi'
      gsimp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
      · rw [hw1 _ (by rw [ofs_off0 dst (by omega_arith)]; omega_using [hi'])]; exact tb i' hi'
      · rw [write1_self]; rfl
    · exact Keep.trans' tk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))
  · rw [Spec.Rsa.bytesAt]
    refine List.eq_replicate_iff.mpr ⟨by simp, fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact tb i (List.mem_range.mp hi)

/-- What the exit leaves. -/
structure Fin (s₀ : State) (R : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  a0 : t.gpr .a0 = BitVec.ofNat 64 R.status
  out : Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
    R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)
  used : t.mem.readW (rlOf s₀).used 64 = BitVec.ofNat 64 R.used
  cs : ∀ i < 12, t.gpr (cs i) = s₀.gpr (cs i)
  ra : t.gpr .ra = s₀.gpr .ra
  sp : t.sp = (rlOf s₀).F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR s₀ :: s₀.wr

theorem finish_ok {s₀ t : State} {R : Spec.Dsa.RandomSignResult} (h : rsContract.pre s₀)
    (hc : Ctx (rlOf s₀) s₀ t) (h5 : t.gpr .s5 = BitVec.ofNat 64 R.used)
    (h10 : t.gpr .s10 = BitVec.ofNat 64 R.status) (hst : R.status ≤ 2)
    (hsig : R.status = 1 → Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
      R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0))
    (hnone : R.status ≠ 1 → R.signature = none) :
    WP isa (finish (lenQ .t5 ++ ([.add .t5 .t5 .t5] : List Instr))) t (Fin s₀ R) := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  have hF := hL.fnw
  obtain ⟨hrd, hwr⟩ := regions_eq h
  unfold finish
  refine WP.seq (WP.mono (wp_sp (WP.keep (c := .block [.addi .a0 .s10 (-1)]) [.a0] (Q := fun t₁ =>
    t₁.mem = t.mem ∧ t₁.gpr .a0 = t.gpr .s10 - BitVec.ofNat 64 1) (by brun) (by decide) (by rfl)))
    fun t₁ ⟨⟨⟨m1, a0⟩, k1⟩, sp1⟩ => ?_)
  have hc₁ : Ctx (rlOf s₀) s₀ t₁ := hc.step hL sp1 k1.2.1 k1.2.2
    (fun r hr => k1.1 r (by revert r hr; decide)) (by rw [m1]; exact Frame.refl _ _)
  -- `out` holds the result's octets.
  have hout : ∀ (P : State → Prop), (∀ t₂, Ctx (rlOf s₀) s₀ t₂ → Keep [.a0, .t3, .t4, .t5] t₁ t₂ →
      Spec.Rsa.bytesAt t₂.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
        R.signature.getD (List.replicate (2 * (rlOf s₀).ql) 0) → P t₂) →
      WP isa (.ite (.zero .a0) (.block []) (zeroOut (lenQ .t5 ++ [.add .t5 .t5 .t5]))) t₁ P := by
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
      have e2 := lenQ_eq (pl := (rlOf s₀).pl) (ql := (rlOf s₀).ql) (by omega_using [hp]) (by omega_using [hq])
      refine WP.seq (WP.mono (wp_sp (WP.keep [.t3, .t4, .t5, .a0] (Q := fun t₂ => t₂.gpr .a0 = 0 ∧
        t₂.gpr .t4 = (rlOf s₀).out ∧ t₂.gpr .t5 = BitVec.ofNat 64 (2 * (rlOf s₀).ql) ∧ t₂.mem = t₁.mem)
        (by
          brun [lenQ, hc₁.sp, hc₁.s2, e2, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero, oOut, i64, l64,
            o64, exec_li_zero, ← BitVec.ofNat_add]
          congr 1; omega_using []) (by decide) (by rfl)))
        fun t₂ ⟨⟨⟨b0, b4, b5, m2⟩, k2⟩, sp2⟩ => ?_)
      have ho : ∀ i < 2 * (rlOf s₀).ql, InRegions t₂.wr (off (rlOf s₀).out i) 1 := fun i hi =>
        ⟨(rlOf s₀).outR, by rw [k2.2.2, hc₁.wr, hwr]; simp,
          VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hq, hi])⟩
      refine WP.mono (wp_sp (zeroLoopA_ok (by omega_using [hq]) (by omega_using [hq]) ho hL.nwOut b0 b4 b5))
        fun t₃ ⟨⟨⟨z3, o3⟩, k3⟩, sp3⟩ => ?_
      have k23 := k2.trans k3
      refine hP t₃ (hc₁.step hL (sp3.trans sp2) k23.2.1 k23.2.2
        (fun r hr => k23.1 r (by revert r hr; decide)) ?_) (k23.mono (by decide)) ?_
      · rw [← m2]
        intro x hx
        refine o3 x ?_
        by_contra hc'
        exact hx _ (List.mem_cons_self ..) (by simp only [Region.Contains, ofs] at hc' ⊢; omega_using [hc'])
      · rw [z3, hnone hs]; rfl
  refine WP.seq (hout _ fun t₂ hc₂ k2 o2 => ?_)
  have c5 : t₂.gpr .s5 = BitVec.ofNat 64 R.used := (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans h5)
  have c10 : t₂.gpr .s10 = BitVec.ofNat 64 R.status :=
    (k2.1 _ (by decide)).trans ((k1.1 _ (by decide)).trans h10)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (wp_sp (clearNonce_ok t₂ hF hc₂.sp (scr_nonce hL rfl hc₂.wr)))
    fun t₃ ⟨⟨⟨t0, _, o3⟩, k3⟩, sp3⟩ => ?_
  have hc₃ : Ctx (rlOf s₀) s₀ t₃ := hc₂.step hL sp3 k3.2.1 k3.2.2 (fun r hr => k3.1 r (by revert r hr; decide))
    (outside_frame hL (o := 0) (n := 32) (by decide) o3)
  have hus : InRegions t₃.wr (rlOf s₀).used 8 := by
    rw [hc₃.wr, hwr]
    exact ⟨(rlOf s₀).usedR, by simp, Region.contains_self _ _⟩
  have hal := hL.alU
  obtain ⟨i72, l72⟩ := hc₃.word hL rfl (d := 72) (by decide) (by decide)
  have o72 := hc₃.used
  simp only [oUsed] at o72
  refine WP.mono (wp_sp (WP.keep (c := .block [.load .d .t4 .t0 oUsed, .store .d .s5 .t4 0, .addi .a0 .s10 0])
    [.t4, .a0] (Q := fun t₄ =>
    t₄.mem = t₃.mem.writeW (rlOf s₀).used (BitVec.ofNat 64 R.used) ∧ t₄.gpr .a0 = BitVec.ofNat 64 R.status)
    (by
      brun [t0, oUsed, i72, l72, o72, BitVec.add_zero, (k3.1 _ (by decide)).trans c5,
        (k3.1 _ (by decide)).trans c10, hus, hal]) (by decide) (by rfl)))
    fun t₄ ⟨⟨⟨m4, a4⟩, k4⟩, sp4⟩ => ?_
  -- The used word apart from the frame and `out`.
  have huR : (rlOf s₀).usedR.Contains (rlOf s₀).used 8 := Region.contains_self _ _
  have fw : ∀ d, d + 8 ≤ frameBytes → t₄.mem.readW (off (rlOf s₀).F d) 64 = t₃.mem.readW (off (rlOf s₀).F d) 64 :=
    fun d hd => by
      rw [m4, Mem.readW_writeW_sep (Region.Disjoint.sep (RL.Ok.frame_disj (d := d) (n := 8) hL.dFU hd)
        (Region.contains_self _ _) huR) (by decide)]
  have hsw : SaveW t₄ (rlOf s₀).F := fun i hi =>
    frame_word hL rfl (by rw [k4.2.2, hc₃.wr]) (by simp only [oSave, frameBytes]; omega_using [hi])
      (by simp only [oSave]; omega_using [])
  refine WP.mono (restoreRegs_ok t₄ (sp4.trans hc₃.sp) hsw (v := fun i => if i < 12 then s₀.gpr (cs i) else s₀.gpr .ra)
    (fun i hi => by rw [ite_eq_left hi]; exact (fw _ (by simp only [oSave, frameBytes]; omega_using [hi])).trans (hc₃.sav i hi))
    ((fw _ (by decide)).trans hc₃.ra)) fun t₅ ⟨r5, ra5, o5, m5, rd5, wr5, sp5⟩ => ?_
  refine ⟨?_, ?_, ?_, fun i hi => by rw [r5 i hi, ite_eq_left hi], ra5, sp5.trans (sp4.trans hc₃.sp),
    rd5.trans (k4.2.1.trans hc₃.rd), wr5.trans (k4.2.2.trans hc₃.wr)⟩
  · rw [o5 .a0 (by decide) (by decide) (by decide)]; exact a4
  · rw [m5, m4, bytes_frame (rs := [(rlOf s₀).usedR]) (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) _ huR)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hL.dOU) (by omega_using [hq])]
    rw [bytes_outside (o3.mono (by omega_using []) (by simp only [oNonce, frameBytes]; omega_using [])) hL.dFO (by omega_using [hq])]
    exact o2
  · rw [m5, m4, Mem.readW_writeW_self64]

theorem preserved_cs : ∀ r ∈ preserved, ∃ i < 12, r = cs i := by decide

/-- The exit's state, after the frame is freed and its bytes lost, meets the contract. -/
theorem fin_post {s₀ t : State} (h : rsContract.pre s₀) (hf : Fin s₀ (rsRes s₀) t)
    (m : Mem) (u : Nat → BitVec 64) (fl : Frame [(rlOf s₀).frR] t.mem m) :
    abiPreserved s₀ { freed frameBytes t with mem := m, unknowns := u } ∧
      rsContract.post s₀ { freed frameBytes t with mem := m, unknowns := u } := by
  have hL := rlOf_ok h
  have hq := hL.ql
  have hst : (rsRes s₀).status ≤ 2 := by
    rw [rsRes_eq h]; exact Dsa.randomSignLoop_status_le _ _ _ _ _ _
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hol, -, -⟩ := h
  refine ⟨⟨fun r hr => ?_, ?_, hf.ra⟩, ?_, ?_, ?_⟩
  · simp only [freed]
    obtain ⟨i, hi, rfl⟩ := preserved_cs r hr
    exact hf.cs i hi
  · simp only [freed, hf.sp, RL.F, rlOf]
    exact BitVec.sub_add_cancel _ _
  · simp only [freed]
    rw [hf.a0, BitVec.setWidth_ofNat_of_le (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hst])]
  · have e0 : s₀.gpr .a0 = (rlOf s₀).out := rfl
    have e1 : (s₀.gpr .a1).toNat = 2 * (rlOf s₀).ql := hol
    rw [e0, e1]
    -- The `free` loses the frame's bytes, which lie apart from the output and `used`.
    exact Eq.trans (List.map_congr_left fun i hi =>
      lost_byte fl (R := (rlOf s₀).outR) hL.dFO.symm (List.mem_range.mp hi)) hf.out
  · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
    exact congrArg (· :: []) ((fl.readW (r := (rlOf s₀).usedR) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hL.dFU.symm) (by decide)).trans hf.used)

theorem randomSignWith_correct (S : Signer) (s₀ : State) (h : rsContract.pre s₀) (hv : RandomValid S s₀) :
    ∃ tr t, Exec isa (Impl.Dsa.RISCV64.RandomSign.codeWith S.name S.code) s₀ tr t ∧ abiPreserved s₀ t ∧
      rsContract.post s₀ t := by
  show WP isa (Impl.Dsa.RISCV64.RandomSign.codeWith S.name S.code) s₀ fun t =>
    abiPreserved s₀ t ∧ rsContract.post s₀ t
  have hL := rlOf_ok h
  have hst : (resOf s₀).status ≤ 2 := Dsa.randomSignLoop_status_le _ _ _ _ _ _
  have hnone : (resOf s₀).status ≠ 1 → (resOf s₀).signature = none := fun hs => by
    have := Dsa.randomSignLoop_success (inpOf (rlOf s₀) s₀.mem).pLen (inpOf (rlOf s₀) s₀.mem).qLen
      (inpOf (rlOf s₀) s₀.mem).key (inpOf (rlOf s₀) s₀.mem).digest 8 ((inpOf (rlOf s₀) s₀.mem).rand.drop 0)
    cases hc : (resOf s₀).signature with
    | none => rfl
    | some _ => exact absurd (this.mpr (by simp only [resOf, randomSignRemaining] at hc ⊢; rw [hc]; rfl)) hs
  have hfin : ∀ t, Ctx (rlOf s₀) s₀ t → t.gpr .s5 = BitVec.ofNat 64 (resOf s₀).used →
      t.gpr .s10 = BitVec.ofNat 64 (resOf s₀).status →
      ((resOf s₀).status = 1 → Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
        (resOf s₀).signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)) →
      WP isa (finish (lenQ .t5 ++ [.add .t5 .t5 .t5])) t fun t' =>
        ∀ m u, Frame [⟨s₀.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩] t'.mem m →
          abiPreserved s₀ { freed frameBytes t' with mem := m, unknowns := u } ∧
            rsContract.post s₀ { freed frameBytes t' with mem := m, unknowns := u } :=
    fun t hc h5 h10 hsig => WP.mono (finish_ok h hc h5 h10 hst hsig hnone) fun t' hf m u fl =>
      fin_post h (by rw [rsRes_eq h]; exact hf) m u fl
  unfold Impl.Dsa.RISCV64.RandomSign.codeWith
  refine WP.alloc (by decide) hL.spF ?_
  unfold Impl.Dsa.RISCV64.RandomSign.body
  refine WP.seq (WP.mono (entry_ok h) fun t₁ he => ?_)
  refine WP.seq (WP.mono (prepareQ_ok h he.ctx) fun t₂ ⟨⟨sc, h0, m2, k2⟩, sp2⟩ => ?_)
  have c5 : t₂.gpr .s5 = BitVec.ofNat 64 0 := (k2.1 _ (by decide)).trans he.s5
  refine WP.seq (WP.ite (decide (¬ 1 < qOf s₀)) (by rw [Steps.eval_zero]; exact congrArg some (by
    by_cases hq : 1 < qOf s₀
    · simp only [hq, not_true_eq_false, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun e => (h0.mp e) hq
    · simp only [hq, not_false_eq_true, decide_true, beq_iff_eq]; exact h0.mpr hq)) (fun hq => ?_) (fun hq => ?_))
  · -- q ≤ 1: no attempt.
    simp only [decide_eq_true_eq] at hq
    refine WP.mono (wp_sp (WP.keep (c := .block [.li .s10 0]) [.s10] (Q := fun t₃ => t₃.mem = t₂.mem ∧
      t₃.gpr .s10 = BitVec.ofNat 64 0) (by brun [exec_li_zero]; rfl) (by decide) (by rfl)))
      fun t₃ ⟨⟨⟨m3, a10⟩, k3⟩, sp3⟩ => ?_
    have hd : (randomSignDraw (inpOf (rlOf s₀) s₀.mem) 0) = ⟨none, 0, [4]⟩ := by
      rw [draw_eq hL, show (128 : Nat) = 127 + 1 from rfl, Spec.Dsa.Random.sample, ite_eq_left (show qOf s₀ ≤ 1 by omega_using [hq])]
    obtain ⟨-, rst, ru⟩ := (RandomSignResultRel.refl (inpOf (rlOf s₀) s₀.mem) 0 8 :
      RandomSignResultRel (inpOf (rlOf s₀) s₀.mem) 0 (resOf s₀) 0 (7 + 1)).sample_none
      (show (randomSignDraw (inpOf (rlOf s₀) s₀.mem) 0).scalar = none by rw [hd])
    rw [hd] at rst ru
    refine hfin t₃ (sc.ctx.step hL sp3 k3.2.1 k3.2.2 (fun r hr => k3.1 r (by revert r hr; decide))
      (by rw [m3]; exact Frame.refl _ _)) ?_ ?_ fun h1 => absurd (rst ▸ h1) (by decide)
    · rw [k3.1 _ (by decide), c5]; congr 1; simp only [resOf] at ru ⊢; omega_using [ru]
    · rw [a10, rst]; rfl
  · -- q > 1: the attempts.
    simp only [decide_eq_false_iff_not, Decidable.not_not] at hq
    refine WP.mono (attempts_ok S h hv hq 8 0 t₂ ⟨sc, c5, by omega_using [], (k2.1 _ (by decide)).trans he.s6, by decide,
      by decide, fun j hj => ?_, RandomSignResultRel.refl _ _ _⟩) fun t₃ ao => hfin t₃ ao.sc.ctx ao.s5 ao.s10 ao.out
    rw [m2]
    have hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
    have := hE.Wq
    have := hL.ql
    have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
    exact he.nonce j (by omega_using [hj, this])

end VG.Proof.Dsa.RISCV64.RS
