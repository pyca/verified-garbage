module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Random
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Env
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Bignum.Octets

/-! ### `Dsa.PPC64LE.RandomSign.Ctx`, which the modules that import this one used -/

section

/-!
# Randomized DSA signing on PPC64LE: the layout of a call, and its context

`RL`: a call's public data (`rlOf`): the stack pointer on entry, the
buffers' addresses and the lengths; `RL.Ok`, what `rsContract.pre` says of
them (`rlOf_ok`). The frame is at `F`, 304 octets below the stack pointer.

`Ctx L s₀ t`: in the frame's body, the registers that hold the call's data,
the frame's saved registers, return address and `vg_dsa_sign_prevalidated`'s stack
arguments, and the key, the digest and the tape as on entry. A change of
memory in `out`, `scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

/-- A call's public data. -/
structure RL where
  sp : Addr
  out : Addr
  used : Addr
  key : Addr
  dig : Addr
  rand : Addr
  scr : Addr
  pl : Nat
  ql : Nat
  dl : Nat
  rl : Nat
  sl : Nat

def rlOf (s : State) : RL :=
  ⟨s.sp, s.gpr .r3, s.gpr .r5, s.gpr .r6, s.gpr .r10, stackArg s 1, stackArg s 3, (s.gpr .r8).toNat,
    (s.gpr .r9).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat, (stackArg s 4).toNat⟩

namespace RL

variable (L : RL)

abbrev F : Addr := L.sp - BitVec.ofNat 64 frameBytes
abbrev kl : Nat := 3 * L.pl + 2 * L.ql
abbrev outR : Region := ⟨L.out, 2 * L.ql⟩
abbrev usedR : Region := ⟨L.used, 8⟩
abbrev keyR : Region := ⟨L.key, L.kl⟩
abbrev digR : Region := ⟨L.dig, L.dl⟩
abbrev randR : Region := ⟨L.rand, L.rl⟩
abbrev scrR : Region := ⟨L.scr, L.sl * 8⟩
abbrev frR : Region := ⟨L.F, frameBytes⟩
/-- The nonce. -/
abbrev nR : Region := ⟨off L.F oNonce, 32⟩

end RL

/-- What the precondition says of a call's data. -/
structure RL.Ok (L : RL) : Prop where
  lv : Spec.Dsa.lengthsValid L.pl L.ql
  sw : 16 * L.pl + 64 ≤ L.sl
  spF : frameBytes ≤ L.sp.toNat
  spTop : L.sp.toNat + 136 ≤ 2 ^ 64
  nwOut : L.out.toNat + 2 * L.ql ≤ 2 ^ 64
  nwUsed : L.used.toNat + 8 ≤ 2 ^ 64
  nwKey : L.key.toNat + L.kl ≤ 2 ^ 64
  nwDig : L.dig.toNat + L.dl ≤ 2 ^ 64
  nwRand : L.rand.toNat + L.rl ≤ 2 ^ 64
  nwScr : L.scr.toNat + L.sl * 8 ≤ 2 ^ 64
  dl : L.dl < 2 ^ 64
  rl : L.rl < 2 ^ 64
  sl : L.sl < 2 ^ 64
  dOU : L.outR.Disjoint L.usedR
  dOK : L.outR.Disjoint L.keyR
  dOD : L.outR.Disjoint L.digR
  dOR : L.outR.Disjoint L.randR
  dOS : L.outR.Disjoint L.scrR
  dUK : L.usedR.Disjoint L.keyR
  dUD : L.usedR.Disjoint L.digR
  dUR : L.usedR.Disjoint L.randR
  dUS : L.usedR.Disjoint L.scrR
  dKS : L.keyR.Disjoint L.scrR
  dDS : L.digR.Disjoint L.scrR
  dRS : L.randR.Disjoint L.scrR
  dFO : L.frR.Disjoint L.outR
  dFU : L.frR.Disjoint L.usedR
  dFK : L.frR.Disjoint L.keyR
  dFD : L.frR.Disjoint L.digR
  dFR : L.frR.Disjoint L.randR
  dFS : L.frR.Disjoint L.scrR

theorem rlOf_ok {s : State} (h : rsContract.pre s) : (rlOf s).Ok := by
  obtain ⟨hF, hT, -, -, dOU, dOK, dOD, dOR, dOS, -, dUK, dUD, dUR, dUS, -, dKS, dDS, dRS, -,
    dFO, dFU, dFK, dFD, dFR, dFS, -, nO, nU, nK, nD, nR, nS, lv, hol, hkl, hsw, -⟩ := h
  simp only [Spec.Dsa.randomSignScratchWords, Spec.Dsa.scratchWords] at hsw
  have e4 : 2 * (s.gpr .r9).toNat = (s.gpr .r4).toNat := hol.symm
  have e7 : 3 * (s.gpr .r8).toNat + (s.gpr .r4).toNat = (s.gpr .r7).toNat := by omega_using [hol, hkl]
  have hT' : s.sp.toNat + 136 ≤ 2 ^ 64 := by omega_using [hT]
  refine ⟨lv, hsw, hF, hT', ?_, nU, ?_, nD, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
    (stackArg s 4).isLt, ?_, ?_, ?_, ?_, ?_, ?_, dUD, dUR, dUS, ?_, dDS, dRS, ?_, dFU, ?_, dFD, dFR, dFS⟩ <;>
  simp only [RL.outR, RL.keyR, RL.kl, RL.frR, RL.F, rlOf, e4, e7]
  · exact nO
  · exact nK
  · exact dOU
  · exact dOK
  · exact dOD
  · exact dOR
  · exact dOS
  · exact dUK
  · exact dKS
  · exact dFO
  · exact dFK

namespace RL.Ok

variable {L : RL} (hL : L.Ok)
include hL

theorem ql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem pl : L.pl = 128 ∨ L.pl = 256 ∨ L.pl = 384 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem F_toNat : L.F.toNat = L.sp.toNat - frameBytes := by
  have h1 := hL.spF
  have h2 := L.sp.isLt
  simp only [RL.F, frameBytes] at h1 ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [h1]

theorem fnw : L.F.toNat + frameBytes ≤ 2 ^ 64 := by
  have := hL.F_toNat; have := hL.spF; have := hL.spTop; omega_arith

omit hL in
/-- A range of the frame is apart from a region apart from the frame. -/
theorem frame_disj {r : Region} (hd : L.frR.Disjoint r) {d n : Nat} (h : d + n ≤ frameBytes) :
    (⟨off L.F d, n⟩ : Region).Disjoint r :=
  hd.sub_left (VG.Offset.sub_base _ h)

end RL.Ok

/-- In the frame's body. -/
structure Ctx (L : RL) (s₀ : State) (t : State) : Prop where
  sp : t.sp = L.F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr
  r2 : t.gpr .r2 = s₀.gpr .r2
  r18 : t.gpr .r18 = L.out
  r19 : t.gpr .r19 = L.key
  r20 : t.gpr .r20 = BitVec.ofNat 64 L.pl
  r21 : t.gpr .r21 = BitVec.ofNat 64 L.ql
  r22 : t.gpr .r22 = L.dig
  r23 : t.gpr .r23 = L.rand
  r24 : t.gpr .r24 = BitVec.ofNat 64 L.rl
  r30 : t.gpr .r30 = L.used
  sav : ∀ i < 18, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (nv i)
  lr : t.mem.readW (off L.F oLr) 64 = s₀.lr
  a0 : t.mem.readW (off L.F oArgs) 64 = BitVec.ofNat 64 L.dl
  a1 : t.mem.readW (off L.F (oArgs + 8)) 64 = L.scr
  a2 : t.mem.readW (off L.F (oArgs + 16)) 64 = BitVec.ofNat 64 L.sl
  key : Spec.Rsa.bytesAt t.mem L.key L.kl = Spec.Rsa.bytesAt s₀.mem L.key L.kl
  dig : Spec.Rsa.bytesAt t.mem L.dig L.dl = Spec.Rsa.bytesAt s₀.mem L.dig L.dl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.r2, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r30]

/-- The octets of a region apart from the regions a change is within are kept. -/
theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {A : Addr} {k : Nat}
    (hd : ∀ r ∈ rs, (⟨A, k⟩ : Region).Disjoint r) (hk : k ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  exact hf.bytes (R := ⟨A, k⟩) hd hk hi

/-- A change of memory in `out`, `scratch` or the nonce, with the registers
of `Ctx` kept, keeps `Ctx`. -/
theorem Ctx.step {L : RL} {s₀ t t' : State} (hL : L.Ok) (h : Ctx L s₀ t) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ ctxRegs, t'.gpr r = t.gpr r)
    (hf : Frame [L.outR, L.scrR, L.nR] t.mem t'.mem) : Ctx L s₀ t' := by
  have hF := hL.fnw
  have hq := hL.ql
  simp only [frameBytes] at hF
  -- The frame's words other than the nonce are apart from the three regions.
  have fw : ∀ d, d + 8 ≤ frameBytes → (d + 8 ≤ oNonce ∨ oNonce + 32 ≤ d) →
      t'.mem.readW (off L.F d) 64 = t.mem.readW (off L.F d) 64 := fun d hd hn =>
    hf.readW (r := ⟨off L.F d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact RL.Ok.frame_disj hL.dFO hd
      · exact RL.Ok.frame_disj hL.dFS hd
      · exact VG.Offset.disjoint L.F (by simp only [oNonce] at hn ⊢; omega_using [hn]) (by simp only [frameBytes] at hd; omega_using [hd])
          (by simp only [oNonce]; omega_using [])) (by decide)
  have nr : ∀ {A : Addr} {k : Nat}, L.frR.Disjoint ⟨A, k⟩ → (⟨A, k⟩ : Region).Disjoint L.nR := fun hd =>
    (RL.Ok.frame_disj hd (d := oNonce) (n := 32) (by decide)).symm
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.r2,
    (hg _ (by decide)).trans h.r18, (hg _ (by decide)).trans h.r19, (hg _ (by decide)).trans h.r20,
    (hg _ (by decide)).trans h.r21, (hg _ (by decide)).trans h.r22, (hg _ (by decide)).trans h.r23,
    (hg _ (by decide)).trans h.r24, (hg _ (by decide)).trans h.r30,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave, oNonce]; omega_using [])).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.lr, (fw _ (by decide) (by decide)).trans h.a0,
    (fw _ (by decide) (by decide)).trans h.a1, (fw _ (by decide) (by decide)).trans h.a2, ?_, ?_, ?_⟩
  · refine (bytes_frame hf (fun r hr => ?_) (by have := hL.nwKey; omega_using [this])).trans h.key
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.dl)).trans h.dig
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOD.symm
    · exact hL.dDS
    · exact nr hL.dFD
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.rl)).trans h.rand
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOR.symm
    · exact hL.dRS
    · exact nr hL.dFR

end VG.Proof.Dsa.PPC64LE.RS

end

end

/-!
# DSA on PPC64LE, randomized functions: saving and restoring the registers

In the frame at `F` (`r1`): `saveRegs_ok`, `saveRegs` stores `r14`–`r31` at
`F + oSave + 8 i` and the return address at `F + oLr`, changing memory only
there; `restoreRegs_ok`, `restoreRegs` loads them back.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Rnd

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

theorem nv_inj : ∀ i < 18, ∀ j < 18, nv i = nv j → i = j := by decide

theorem nv_ne0 : ∀ i < 18, nv i ≠ .r0 ∧ nv i ≠ .r12 := by decide

/-- The first `n` registers are saved. -/
structure SI (s₀ : State) (F : Addr) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  out : Outside F oSave (8 * 18) s₀.mem s.mem
  saved : ∀ i < n, s.mem.readW (off F (oSave + 8 * i)) 64 = s₀.gpr (nv i)

theorem save_sep {F : Addr} (_hF : F.toNat + frameBytes ≤ 2 ^ 64) {i j : Nat} (hi : i < 18) (hj : j < 18)
    (h : i ≠ j) : Mem.Sep (off F (oSave + 8 * i)) 8 (off F (oSave + 8 * j)) 8 :=
  VG.Offset.sep F (by simp only [oSave]; omega_using [h]) (by simp only [oSave]; omega_using [hi]) (by simp only [oSave]; omega_using [hj])

theorem save_step (s₀ : State) {F : Addr} (hF : F.toNat + frameBytes ≤ 2 ^ 64) (h12 : s₀.gpr .r12 = F)
    (hin : ∀ i < 18, InRegions s₀.wr (off F (oSave + 8 * i)) 8) {n : Nat} (hn : n < 18) {s : State}
    (h : SI s₀ F n s) : WP isa (.block [.store .d (nv n) .r12 (oSave + 8 * n)]) s (SI s₀ F (n + 1)) := by
  have hw : s.gpr .r12 = F := by rw [h.gpr, h12]
  have hout : InRegions s.wr (s.gpr .r12 + BitVec.ofNat 64 (oSave + 8 * n)) 8 := by
    rw [h.wr, hw]; exact hin n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_store_d (show Reg.r12 ≠ .r0 by decide) (show oSave + 8 * n < 2 ^ 15 ∧ (oSave + 8 * n) % 4 = 0 by
      simp only [oSave]; omega_using [hn]) hout, Option.some.injEq, exists_eq_left', hw]
  refine ⟨h.gpr, h.rd, h.wr, h.sp, h.lr, ?_, fun i hi => ?_⟩
  · simp only [frameBytes] at hF
    exact h.out.trans ((writeW_outside s.mem F (d := oSave + 8 * n) _ (by simp only [oSave]; omega_using [hn])).mono
      (by omega_using []) (by omega_using [hn]))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (save_sep hF (by omega_arith) hn (by omega_using [hi])) (by decide)]
      exact h.saved i hi
    · rw [Mem.readW_writeW_self64, h.gpr]

/-- What `saveRegs` leaves, from `s₀`. -/
structure Saved (s₀ : State) (F : Addr) (s : State) : Prop where
  r12 : s.gpr .r12 = F
  others : ∀ r, r ≠ .r0 → r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.lr = s₀.lr
  out : Outside F oSave (8 * 18 + 8) s₀.mem s.mem
  saved : ∀ i < 18, s.mem.readW (off F (oSave + 8 * i)) 64 = s₀.gpr (nv i)
  savedLr : s.mem.readW (off F oLr) 64 = s₀.lr

theorem saveRegs_ok (s₀ : State) {F : Addr} (hF : F.toNat + frameBytes ≤ 2 ^ 64) (hsp : s₀.sp = F)
    (hin : ∀ i < 19, InRegions s₀.wr (off F (oSave + 8 * i)) 8) :
    WP isa (.block saveRegs) s₀ (Saved s₀ F) := by
  have hF' := hF
  simp only [frameBytes] at hF'
  rw [saveRegs, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.r12] (Q := fun s => s.gpr .r12 = F ∧ s.mem = s₀.mem)
    (by prun [exec_addSp (show 0 < 2 ^ 15 by decide), hsp, BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a12, m1⟩, k1⟩ => ?_
  have hin1 : ∀ i < 18, InRegions s₁.wr (off F (oSave + 8 * i)) 8 := fun i hi => by
    rw [k1.wr]; exact hin i (by omega_using [hi])
  refine WP.mono (wp_range_flatMap (M := isa) (SI s₁ F) (fun k s hk h => save_step s₁ hF a12 hin1 hk h) 18
    (Nat.le_refl _) s₁ ⟨rfl, rfl, rfl, rfl, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s h => ?_
  have hw : s.gpr .r12 = F := by rw [h.gpr, a12]
  have hst : InRegions (s.write .r0 s.lr).wr ((s.write .r0 s.lr).gpr .r12 + BitVec.ofNat 64 oLr) 8 := by
    rw [wr_write, gpr_write, ite_eq_right_iff.mpr (fun e => by cases e), h.wr, k1.wr, hw]
    exact hin 18 (by decide)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mflr,
    exec_store_d (show Reg.r12 ≠ .r0 by decide) (show oLr < 2 ^ 15 ∧ oLr % 4 = 0 by decide) hst,
    Option.some.injEq, exists_eq_left']
  have h12' : (s.write .r0 s.lr).gpr .r12 = F := by rw [gpr_write, ite_eq_right_iff.mpr (fun e => by cases e), hw]
  refine ⟨by gsimp; exact hw, fun r h0 h12 => ?_, by gsimp; rw [h.rd, k1.rd], by gsimp; rw [h.wr, k1.wr],
    by gsimp; rw [h.sp, k1.sp], by gsimp; rw [h.lr, k1.lr], ?_, fun i hi => ?_, ?_⟩
  · gsimp
    rw [ite_eq_right_iff.mpr (fun e => absurd e h0), h.gpr]
    exact k1.gpr r (by simp [h12])
  · simp only [mem_write, h12']
    rw [← m1]
    exact (h.out.mono (by omega_using []) (by omega_using [])).trans ((writeW_outside s.mem F (d := oLr) _ (by simp only [oLr]; omega_using [])).mono
      (by simp only [oLr, oSave]; omega_using []) (by simp only [oLr, oSave]; omega_using []))
  · simp only [mem_write, h12']
    rw [Mem.readW_writeW_sep (VG.Offset.sep F (by simp only [oLr, oSave]; omega_using [hi]) (by simp only [oSave]; omega_using [hi])
      (by simp only [oLr]; omega_using [])) (by decide), h.saved i hi, k1.gpr _ (by have := nv_ne0 i hi; simp [this.2])]
  · simp only [mem_write, h12']
    rw [Mem.readW_writeW_self64]
    gsimp
    rw [h.lr, k1.lr]

/-- The first `n` registers are restored to `v`, from the state `sB` the
restoring starts in. -/
structure RI (sB : State) (F : Addr) (v : Nat → BitVec 64) (lr : BitVec 64) (n : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = F
  restored : ∀ i < n, s.gpr (nv i) = v i
  others : ∀ r, r ≠ .r0 → r ≠ .r12 → (∀ i < 18, r ≠ nv i) → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  sp : s.sp = sB.sp
  lr : s.lr = lr

theorem restore_step (sB : State) {F : Addr} {v : Nat → BitVec 64} {lr : BitVec 64}
    (hin : ∀ i < 18, InRegions (sB.rd ++ sB.wr) (off F (oSave + 8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off F (oSave + 8 * i)) 64 = v i)
    {n : Nat} (hn : n < 18) {s : State} (h : RI sB F v lr n s) :
    WP isa (.block [.load .d (nv n) .r12 (oSave + 8 * n)]) s (RI sB F v lr (n + 1)) := by
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .r12 + BitVec.ofNat 64 (oSave + 8 * n)) 8 := by
    rw [h.rd, h.wr, h.r12]; exact hin n hn
  have hv : s.mem.readW (F + BitVec.ofNat 64 (oSave + 8 * n)) 64 = v n := by rw [h.mem]; exact hsav n hn
  have hne := nv_ne0 n hn
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r12 ≠ .r0 by decide) (show oSave + 8 * n < 2 ^ 15 ∧ (oSave + 8 * n) % 4 = 0 by
      simp only [oSave]; omega_using [hn]) hin', Option.some.injEq, exists_eq_left', h.r12, hv]
  refine ⟨?_, fun i hi => ?_, fun r h0 h12 hr => ?_, h.mem, h.rd, h.wr, h.sp, h.lr⟩
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e.symm hne.2]; exact h.r12
  · rw [gpr_write]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have e : nv i ≠ nv n := fun e => absurd (nv_inj i (by omega_arith) n hn e) (by omega_using [hi])
      rw [ite_eq_right_iff.mpr fun e' => absurd e' e]; exact h.restored i hi
    · rw [ite_eq_left_iff.mpr fun e => absurd rfl e]
  · rw [gpr_write, ite_eq_right_iff.mpr fun e => absurd e (hr n hn)]
    exact h.others r h0 h12 hr

/-- `restoreRegs`, from a state whose saved words hold `v` and `lr`. -/
theorem restoreRegs_ok (sB : State) {F : Addr} {v : Nat → BitVec 64} {lr : BitVec 64} (hsp : sB.sp = F)
    (hin : ∀ i < 19, InRegions (sB.rd ++ sB.wr) (off F (oSave + 8 * i)) 8)
    (hsav : ∀ i < 18, sB.mem.readW (off F (oSave + 8 * i)) 64 = v i)
    (hlr : sB.mem.readW (off F oLr) 64 = lr) :
    WP isa (.block restoreRegs) sB fun s =>
      (∀ i < 18, s.gpr (nv i) = v i) ∧ s.lr = lr ∧
      (∀ r, r ≠ .r0 → r ≠ .r12 → (∀ i < 18, r ≠ nv i) → s.gpr r = sB.gpr r) ∧
      s.mem = sB.mem ∧ s.rd = sB.rd ∧ s.wr = sB.wr ∧ s.sp = sB.sp := by
  rw [restoreRegs, WP.block_append_iff]
  have hl : InRegions ((sB.write .r12 sB.sp).rd ++ (sB.write .r12 sB.sp).wr)
      ((sB.write .r12 sB.sp).gpr .r12 + BitVec.ofNat 64 oLr) 8 := by
    rw [rd_write, wr_write, gpr_write, ite_eq_left rfl, hsp]; exact hin 18 (by decide)
  have hlv : (sB.write .r12 sB.sp).mem.readW ((sB.write .r12 sB.sp).gpr .r12 + BitVec.ofNat 64 oLr) 64 = lr := by
    rw [mem_write, gpr_write, ite_eq_left rfl, hsp]; exact hlr
  refine WP.mono (Q := RI sB F v lr 0) ?_ fun s₁ h₁ => WP.mono (wp_range_flatMap (M := isa) (RI sB F v lr)
    (fun k s hk h => restore_step sB (fun i hi => hin i (by omega_using [hi])) hsav hk h) 18 (Nat.le_refl _) s₁ h₁)
    fun s h => ⟨h.restored, h.lr, h.others, h.mem, h.rd, h.wr, h.sp⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addSp (show 0 < 2 ^ 15 by decide), BitVec.add_zero,
    exec_load_d (show Reg.r12 ≠ .r0 by decide) (show oLr < 2 ^ 15 ∧ oLr % 4 = 0 by decide) hl, hlv,
    exec_mtlr, Option.some.injEq, exists_eq_left']
  refine ⟨by gsimp; exact hsp, fun _ h => absurd h (Nat.not_lt_zero _), fun r h0 h12 _ => ?_, by gsimp,
    by gsimp, by gsimp, by gsimp, by gsimp⟩
  gsimp
  rw [ite_eq_right_iff.mpr fun e => absurd e h0, ite_eq_right_iff.mpr fun e => absurd e h12]

/-- A byte after a zero doubleword is written at an offset of the same base. -/
theorem writeW_zero_byte (m : Mem) (p : Addr) {a d : Nat} (ha : a < 2 ^ 32) (hd : d < 2 ^ 32) :
    (m.writeW (off p a) (BitVec.ofNat 64 0)) (off p d) = if a ≤ d ∧ d < a + 8 then 0 else m (off p d) := by
  simp only [Mem.writeW, Mem.write, off]
  rw [VG.Offset.sub_toNat' p (by omega_using [ha]) (by omega_using [hd])]
  split
  · split
    · rename_i h1 h2
      rw [ite_eq_left ⟨h1, by omega_using [h2]⟩]
      apply BitVec.eq_of_toNat_eq
      simp
    · rename_i h1 h2
      rw [ite_eq_right (by omega_using [h2])]
  · split
    · omega
    · rename_i h1 h2
      rw [ite_eq_right (by omega_using [h1])]

/-- `clearNonce`: the nonce's 32 octets := 0. -/
theorem clearNonce_ok (s : State) {F : Addr} (hF : F.toNat + frameBytes ≤ 2 ^ 64) (hsp : s.sp = F)
    (hw : Scr s (off F oNonce) 32) :
    WP isa (.block clearNonce) s fun t =>
      (t.gpr .r12 = F ∧ (∀ j < 32, t.mem (off F (oNonce + j)) = 0) ∧ Outside F oNonce 32 s.mem t.mem) ∧
        Keep [.r0, .r12] s t := by
  have hF' := hF
  simp only [frameBytes] at hF'
  have st : ∀ k < 4, InRegions s.wr (off F (oNonce + 8 * k)) 8 := fun k hk => by
    have := hw.st (d := 8 * k) (n := 8) (by omega_using [hk]) (by decide)
    rwa [off_off] at this
  refine WP.keep _ ?_ (by decide)
  have s0 : InRegions s.wr (F + BitVec.ofNat 64 120) 8 := st 0 (by decide)
  have s1 : InRegions s.wr (F + BitVec.ofNat 64 128) 8 := st 1 (by decide)
  have s2 : InRegions s.wr (F + BitVec.ofNat 64 136) 8 := st 2 (by decide)
  have s3 : InRegions s.wr (F + BitVec.ofNat 64 144) 8 := st 3 (by decide)
  simp only [clearNonce, oNonce]
  prun [exec_addSp (show 0 < 2 ^ 15 by decide), hsp, BitVec.add_zero, s0, s1, s2, s3]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [writeW_zero_byte _ _ (a := 144) (d := 120 + j) (by omega_using []) (by omega_using [hj])]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 136) (d := 120 + j) (by omega_using []) (by omega_using [hj])]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 128) (d := 120 + j) (by omega_using []) (by omega_using [hj])]
    split
    · rfl
    rw [writeW_zero_byte _ _ (a := 120) (d := 120 + j) (by omega_using []) (by omega_using [hj])]
    split
    · rfl
    · omega
  · have w := fun (m : Mem) (d : Nat) (h : d + 8 ≤ 2 ^ 64) => writeW_outside m F (d := d) (BitVec.ofNat 64 0) h
    exact ((((w _ 120 (by omega_using [])).mono (by omega_using []) (by omega_using [])).trans ((w _ 128 (by omega_using [])).mono (by omega_using []) (by omega_using []))).trans
      ((w _ 136 (by omega_using [])).mono (by omega_using []) (by omega_using []))).trans ((w _ 144 (by omega_using [])).mono (by omega_using []) (by omega_using []))

end VG.Proof.Dsa.PPC64LE.Rnd
