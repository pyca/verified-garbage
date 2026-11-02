module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSSampler
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignFront
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.SignFn
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on RISC-V: the call of `vg_dsa_sign`

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Call.lean`). `callArgs`
passes `out`, the key, the nonce (in the frame) and the digest, with their
lengths, and the frame holds the arguments on the stack (`digest_len`,
`scratch`, `scratch_len`, at its start), so `vg_dsa_sign`'s contract on the
registers (`sContract`) holds, with the regions it is given (`signRd`,
`signWr`): `sign_ok` runs the call by `WP.call` from `sign_correct`.
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
  have e1 := lenP_eq (pl := L.pl) (ql := L.ql) (by omega) (by omega)
  have e2 := lenQ_eq (pl := L.pl) (ql := L.ql) (by omega) (by omega)
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
  exact ⟨by congr 1; omega, by simp only [RL.kl]; congr 1; omega⟩

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
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega)]
    simp only [oNonce]; omega
  have hsp16 : (rlOf s₀).F.toNat % 16 = 0 := by
    have h1 := hL.F_toNat; have h2 := hL.spF; have h3 := hL.sp16; simp only [frameBytes] at h1 h2; omega
  unfold sContract
  dsimp only
  rw [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
    g .a5 (by decide), g .a6 (by decide), g .a7 (by decide), ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, ha.a6,
    ha.a7, sa0, sa1, sa2, sargs, ssp, tn (2 * (rlOf s₀).ql) (by omega),
    tn (rlOf s₀).kl (by omega), tn (rlOf s₀).ql (by omega), tn (rlOf s₀).pl (by omega), tn _ hdl, tn _ hsl]
  refine ⟨rfl, rfl, hL.dOK, ?_, hL.dOD, hL.dOS, ?_, hL.dKS, ?_, hL.dDS, ?_, hL.nwOut, hk, nwN, hL.nwDig,
    hL.nwScr, hL.lv, by omega, by omega, by simp only [Spec.Dsa.scratchWords]; omega, hL.alS, hsp16⟩
  · exact (RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega)).symm
  · exact (RL.Ok.frame_disj (d := 0) (n := 24) hL.dFO (by decide)).symm
  · exact RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega)
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
    · exact VG.Covers.one (inF _ _ (by simp only [oNonce, frameBytes]; omega))
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
  rw [Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega), Nat.mod_eq_of_lt hdl]

theorem sign_ok {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_sign" Impl.Dsa.RISCV64.Sign.sign) t (Signed (rlOf s₀) s₀ t) := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := sign_cov h hc
  refine WP.call (k := sContract) sign_correct (sign_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p0, pout⟩ := hpost
  have es := sres_eq h ha
  rw [es] at p0 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p0, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .a0) (by decide), State.callEntry_gpr t (r := .a1) (by decide), ha.a0, ha.a1,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * (rlOf s₀).ql) (by omega)] at pout
  exact pout

end VG.Proof.Dsa.RISCV64.RS
