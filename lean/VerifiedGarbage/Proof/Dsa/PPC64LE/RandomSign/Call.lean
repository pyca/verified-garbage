module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Sampler
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Front
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Fn
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on PPC64LE: the call of `vg_dsa_sign`

`callArgs` passes `out`, the key, the nonce (in the frame) and the digest,
with their lengths, and the frame holds the arguments on the stack
(`digest_len`, `scratch`, `scratch_len`), so `vg_dsa_sign`'s contract on
the registers (`sContract`) holds, with the regions it is given (`signRd`,
`signWr`): `signCall_ok` runs the call by `WP.call` from `sign_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

/-- The regions `vg_dsa_sign` may read. -/
abbrev signRd (L : RL) : List Region :=
  [L.keyR, ⟨off L.F oNonce, L.ql⟩, L.digR, ⟨off L.F oArgs, 24⟩]

/-- The regions `vg_dsa_sign` may write. -/
abbrev signWr (L : RL) : List Region := [L.outR, L.scrR]

/-- The registers `callArgs` writes. -/
def argRegs' : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The state after `callArgs`. -/
structure Args (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r3 : t.gpr .r3 = L.out
  r4 : t.gpr .r4 = BitVec.ofNat 64 (2 * L.ql)
  r5 : t.gpr .r5 = L.key
  r6 : t.gpr .r6 = BitVec.ofNat 64 L.kl
  r7 : t.gpr .r7 = BitVec.ofNat 64 L.pl
  r8 : t.gpr .r8 = off L.F oNonce
  r9 : t.gpr .r9 = BitVec.ofNat 64 L.ql
  r10 : t.gpr .r10 = L.dig

theorem callArgs_ok {L : RL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    WP isa (.block callArgs) t fun t' => Args L s₀ t' ∧ t'.mem = t.mem ∧ Keep argRegs' t t' := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ argRegs' := by decide
  refine WP.mono (WP.keep argRegs' (Q := fun t' => t'.gpr .r3 = L.out ∧ t'.gpr .r4 = BitVec.ofNat 64 (2 * L.ql) ∧
    t'.gpr .r5 = L.key ∧ t'.gpr .r6 = BitVec.ofNat 64 L.kl ∧ t'.gpr .r7 = BitVec.ofNat 64 L.pl ∧
    t'.gpr .r8 = off L.F oNonce ∧ t'.gpr .r9 = BitVec.ofNat 64 L.ql ∧ t'.gpr .r10 = L.dig ∧ t'.mem = t.mem)
    ?_ (by decide)) fun t' ⟨⟨a3, a4, a5, a6, a7, a8, a9, a10, am⟩, k⟩ =>
      ⟨⟨hc.step hL k.sp k.rd k.wr (fun r hr => k.gpr r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a3, a4, a5, a6, a7, a8, a9, a10⟩, am, k⟩
  unfold callArgs
  prun [hc.r18, hc.r19, hc.r20, hc.r21, hc.r22, hc.sp, exec_addSp (show oNonce < 2 ^ 15 by decide), add0,
    ← BitVec.ofNat_add]
  refine ⟨by congr 1; omega, by simp only [RL.kl]; congr 1; omega⟩

/-- The arguments' values in the state `vg_dsa_sign` is entered in. -/
theorem entry_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := State.callEntry_gpr t h

theorem entry_stackArg (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 := rfl

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
  have g3 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r3) (by decide)).trans ha.r3
  have g4 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r4) (by decide)).trans ha.r4
  have g5 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r5) (by decide)).trans ha.r5
  have g6 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r6) (by decide)).trans ha.r6
  have g7 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r7) (by decide)).trans ha.r7
  have g8 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r8) (by decide)).trans ha.r8
  have g9 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r9) (by decide)).trans ha.r9
  have g10 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r10) (by decide)).trans ha.r10
  have sa0 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 0 =
      BitVec.ofNat 64 (rlOf s₀).dl := by rw [entry_stackArg, hc.sp]; exact hc.a0
  have sa1 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 1 = (rlOf s₀).scr := by
    rw [entry_stackArg, hc.sp]; exact hc.a1
  have sa2 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 2 =
      BitVec.ofNat 64 (rlOf s₀).sl := by rw [entry_stackArg, hc.sp]; exact hc.a2
  have ssp : (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).sp = (rlOf s₀).F := hc.sp
  have sargs : sStackArgs (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) =
      ⟨off (rlOf s₀).F oArgs, 24⟩ := by
    simp only [sStackArgs, stackArgAddr, ssp]; rfl
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hdl := hL.dl
  have hsl := hL.sl
  have ekl : (rlOf s₀).kl = 3 * (rlOf s₀).pl + 2 * (rlOf s₀).ql := rfl
  have nwN : (off (rlOf s₀).F oNonce).toNat + (rlOf s₀).ql ≤ 2 ^ 64 := by
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega)]
    simp only [oNonce]; omega
  unfold sContract
  dsimp only
  rw [g3, g4, g5, g6, g7, g8, g9, g10, sa0, sa1, sa2, sargs, ssp, tn (2 * (rlOf s₀).ql) (by omega),
    tn (rlOf s₀).kl (by omega), tn (rlOf s₀).ql (by omega), tn (rlOf s₀).pl (by omega), tn _ hdl, tn _ hsl]
  refine ⟨by omega, rfl, rfl, hL.dOK, ?_, hL.dOD, hL.dOS, ?_, hL.dKS, ?_, hL.dDS, ?_, hL.nwOut, hk, nwN, hL.nwDig,
    hL.nwScr, hL.lv, by omega, by omega, by simp only [Spec.Dsa.scratchWords]; omega⟩
  · exact (RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega)).symm
  · exact (RL.Ok.frame_disj (d := oArgs) (n := 24) hL.dFO (by decide)).symm
  · exact RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega)
  · exact (RL.Ok.frame_disj (d := oArgs) (n := 24) hL.dFS (by decide)).symm

/-- What the call leaves. -/
structure Signed (L : RL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame (signWr L) t.mem t'.mem
  r3 : ((t'.gpr .r3).setWidth 32).toNat = Spec.Dsa.signStatus (sresOf L t.mem)
  out : Spec.Rsa.bytesAt t'.mem L.out (2 * L.ql) = (sresOf L t.mem).getD (List.replicate (2 * L.ql) 0)

/-- The regions given to `vg_dsa_sign` are within the caller's. -/
theorem sign_cov {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    Covers (signRd (rlOf s₀) ++ signWr (rlOf s₀)) (t.rd ++ t.wr) ∧ Covers (signWr (rlOf s₀)) t.wr := by
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hrd, hwr⟩ := regions_eq h
  have inF : ∀ d n, 32 ≤ d → d + n ≤ frameBytes → InRegions (t.rd ++ t.wr) (off (rlOf s₀).F d) n := fun d n h₁ h₂ =>
    ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), frameR_contains hL rfl h₁ h₂⟩
  have hcov : Covers (signRd (rlOf s₀) ++ signWr (rlOf s₀)) (t.rd ++ t.wr) := by
    refine VG.Covers.of_forall fun r hr => ?_
    simp only [signRd, signWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact VG.Covers.one (inF _ _ (by decide) (by simp only [oNonce, frameBytes]; omega))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; simp)
    · exact VG.Covers.one (inF _ _ (by decide) (by decide))
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
  rw [g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide),
    g .r10 (by decide), ha.r5, ha.r6, ha.r7, ha.r8, ha.r9, ha.r10, entry_stackArg, hc.sp]
  have a0' : t.mem.readW ((rlOf s₀).F + BitVec.ofNat 64 (32 + 8 * (8 + 0))) 64 = BitVec.ofNat 64 (rlOf s₀).dl := hc.a0
  rw [a0']
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega), Nat.mod_eq_of_lt hdl]

theorem sign_ok {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_sign" Impl.Dsa.PPC64LE.Sign.sign) t (Signed (rlOf s₀) s₀ t) := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := sign_cov h hc
  refine WP.call (k := sContract) sign_correct (sign_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p3, pout⟩ := hpost
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  have es := sres_eq h ha
  rw [es] at p3 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p3, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .r3) (by decide), State.callEntry_gpr t (r := .r4) (by decide), ha.r3, ha.r4,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * (rlOf s₀).ql) (by omega)] at pout
  exact pout

end VG.Proof.Dsa.PPC64LE.RS
