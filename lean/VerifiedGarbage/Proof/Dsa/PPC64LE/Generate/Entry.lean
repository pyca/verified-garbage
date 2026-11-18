module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Generate
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Env
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-! ### `Dsa.PPC64LE.Generate.Ctx`, which this module and modules that import it used -/

section

/-!
# DSA key generation on PPC64LE: the layout of a call, and its context

`GL`: a call's public data (`glOf`): the stack pointer on entry, the
buffers' addresses and the lengths; `GL.Ok`, what `gkContract.pre` says of
them (`glOf_ok`). The frame is at `F`, 304 octets below the stack pointer.

`Ctx L s₀ t`: in the frame's body, the registers that hold the call's data,
the frame's saved registers, return address and `vg_dsa_derive_key`'s stack
argument, and the domain and the tape as on entry. A change of memory in
`out`, `scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont

/-- A call's public data. -/
structure GL where
  sp : Addr
  out : Addr
  used : Addr
  par : Addr
  rand : Addr
  scr : Addr
  pl : Nat
  ql : Nat
  rl : Nat
  sl : Nat

def glOf (s : State) : GL :=
  ⟨s.sp, s.gpr .r3, s.gpr .r5, s.gpr .r6, s.gpr .r10, stackArg s 1, (s.gpr .r8).toNat,
    (s.gpr .r9).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat⟩

namespace GL

variable (L : GL)

abbrev F : Addr := L.sp - BitVec.ofNat 64 frameBytes
/-- The domain's length. -/
abbrev kl : Nat := 2 * L.pl + L.ql
/-- The key's length. -/
abbrev ol : Nat := 3 * L.pl + 2 * L.ql
abbrev outR : Region := ⟨L.out, L.ol⟩
abbrev usedR : Region := ⟨L.used, 8⟩
abbrev parR : Region := ⟨L.par, L.kl⟩
abbrev randR : Region := ⟨L.rand, L.rl⟩
abbrev scrR : Region := ⟨L.scr, L.sl * 8⟩
abbrev frR : Region := ⟨L.F, frameBytes⟩
/-- The nonce. -/
abbrev nR : Region := ⟨off L.F oNonce, 32⟩

end GL

/-- What the precondition says of a call's data. -/
structure GL.Ok (L : GL) : Prop where
  lv : Spec.Dsa.lengthsValid L.pl L.ql
  sw : 64 * L.pl + 1024 ≤ L.sl
  spF : frameBytes ≤ L.sp.toNat
  spTop : L.sp.toNat + 120 ≤ 2 ^ 64
  nwOut : L.out.toNat + L.ol ≤ 2 ^ 64
  nwUsed : L.used.toNat + 8 ≤ 2 ^ 64
  nwPar : L.par.toNat + L.kl ≤ 2 ^ 64
  nwRand : L.rand.toNat + L.rl ≤ 2 ^ 64
  nwScr : L.scr.toNat + L.sl * 8 ≤ 2 ^ 64
  rl : L.rl < 2 ^ 64
  sl : L.sl < 2 ^ 64
  dOU : L.outR.Disjoint L.usedR
  dOK : L.outR.Disjoint L.parR
  dOR : L.outR.Disjoint L.randR
  dOS : L.outR.Disjoint L.scrR
  dUK : L.usedR.Disjoint L.parR
  dUR : L.usedR.Disjoint L.randR
  dUS : L.usedR.Disjoint L.scrR
  dKS : L.parR.Disjoint L.scrR
  dRS : L.randR.Disjoint L.scrR
  dFO : L.frR.Disjoint L.outR
  dFU : L.frR.Disjoint L.usedR
  dFK : L.frR.Disjoint L.parR
  dFR : L.frR.Disjoint L.randR
  dFS : L.frR.Disjoint L.scrR

theorem glOf_ok {s : State} (h : gkContract.pre s) : (glOf s).Ok := by
  obtain ⟨hF, hT, -, -, dOU, dOK, dOR, dOS, -, dUK, dUR, dUS, -, dKS, dRS, -,
    dFO, dFU, dFK, dFR, dFS, -, nO, nU, nK, nR, nS, lv, hol, hkl, hsw⟩ := h
  simp only [Spec.Dsa.generationScratchWords] at hsw
  have e4 : 3 * (s.gpr .r8).toNat + 2 * (s.gpr .r9).toNat = (s.gpr .r4).toNat := hol.symm
  have e7 : 2 * (s.gpr .r8).toNat + (s.gpr .r9).toNat = (s.gpr .r7).toNat := hkl.symm
  have hT' : s.sp.toNat + 120 ≤ 2 ^ 64 := by omega_using [hT]
  refine ⟨lv, hsw, hF, hT', ?_, nU, ?_, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
    ?_, ?_, ?_, ?_, ?_, dUR, dUS, ?_, dRS, ?_, dFU, ?_, dFR, dFS⟩ <;>
  simp only [GL.outR, GL.parR, GL.kl, GL.ol, GL.frR, GL.F, glOf, e4, e7]
  · exact nO
  · exact nK
  · exact dOU
  · exact dOK
  · exact dOR
  · exact dOS
  · exact dUK
  · exact dKS
  · exact dFO
  · exact dFK

namespace GL.Ok

variable {L : GL} (hL : L.Ok)
include hL

theorem ql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem pl : L.pl = 128 ∨ L.pl = 256 ∨ L.pl = 384 := by
  have := hL.lv; simp only [Spec.Dsa.lengthsValid] at this; omega_using [this]

theorem F_toNat : L.F.toNat = L.sp.toNat - frameBytes := by
  have h1 := hL.spF
  have h2 := L.sp.isLt
  simp only [GL.F, frameBytes] at h1 ⊢
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega_using [h1]

theorem fnw : L.F.toNat + frameBytes ≤ 2 ^ 64 := by
  have := hL.F_toNat; have := hL.spF; have := hL.spTop; omega_arith

omit hL in
/-- A range of the frame is apart from a region apart from the frame. -/
theorem frame_disj {r : Region} (hd : L.frR.Disjoint r) {d n : Nat} (h : d + n ≤ frameBytes) :
    (⟨off L.F d, n⟩ : Region).Disjoint r :=
  hd.sub_left (VG.Offset.sub_base _ h)

end GL.Ok

/-- In the frame's body. -/
structure Ctx (L : GL) (s₀ : State) (t : State) : Prop where
  sp : t.sp = L.F
  rd : t.rd = s₀.rd
  wr : t.wr = frameR frameBytes s₀ :: s₀.wr
  r2 : t.gpr .r2 = s₀.gpr .r2
  r18 : t.gpr .r18 = L.out
  r19 : t.gpr .r19 = L.par
  r20 : t.gpr .r20 = BitVec.ofNat 64 L.pl
  r21 : t.gpr .r21 = BitVec.ofNat 64 L.ql
  r22 : t.gpr .r22 = L.scr
  r23 : t.gpr .r23 = L.rand
  r24 : t.gpr .r24 = BitVec.ofNat 64 L.rl
  r26 : t.gpr .r26 = BitVec.ofNat 64 L.sl
  r30 : t.gpr .r30 = L.used
  sav : ∀ i < 18, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (nv i)
  lr : t.mem.readW (off L.F oLr) 64 = s₀.lr
  a0 : t.mem.readW (off L.F oArgs) 64 = BitVec.ofNat 64 L.sl
  par : Spec.Rsa.bytesAt t.mem L.par L.kl = Spec.Rsa.bytesAt s₀.mem L.par L.kl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.r2, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r26, .r30]

/-- A change of memory in `out`, `scratch` or the nonce, with the registers
of `Ctx` kept, keeps `Ctx`. -/
theorem Ctx.step {L : GL} {s₀ t t' : State} (hL : L.Ok) (h : Ctx L s₀ t) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ ctxRegs, t'.gpr r = t.gpr r)
    (hf : Frame [L.outR, L.scrR, L.nR] t.mem t'.mem) : Ctx L s₀ t' := by
  have hF := hL.fnw
  have hq := hL.ql
  simp only [frameBytes] at hF
  have fw : ∀ d, d + 8 ≤ frameBytes → (d + 8 ≤ oNonce ∨ oNonce + 32 ≤ d) →
      t'.mem.readW (off L.F d) 64 = t.mem.readW (off L.F d) 64 := fun d hd hn =>
    hf.readW (r := ⟨off L.F d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact GL.Ok.frame_disj hL.dFO hd
      · exact GL.Ok.frame_disj hL.dFS hd
      · exact VG.Offset.disjoint L.F (by simp only [oNonce] at hn ⊢; omega_using [hn]) (by simp only [frameBytes] at hd; omega_using [hd])
          (by simp only [oNonce]; omega_using [])) (by decide)
  have nr : ∀ {A : Addr} {k : Nat}, L.frR.Disjoint ⟨A, k⟩ → (⟨A, k⟩ : Region).Disjoint L.nR := fun hd =>
    (GL.Ok.frame_disj hd (d := oNonce) (n := 32) (by decide)).symm
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.r2,
    (hg _ (by decide)).trans h.r18, (hg _ (by decide)).trans h.r19, (hg _ (by decide)).trans h.r20,
    (hg _ (by decide)).trans h.r21, (hg _ (by decide)).trans h.r22, (hg _ (by decide)).trans h.r23,
    (hg _ (by decide)).trans h.r24, (hg _ (by decide)).trans h.r26, (hg _ (by decide)).trans h.r30,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave, oNonce]; omega_using [])).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.lr, (fw _ (by decide) (by decide)).trans h.a0, ?_, ?_⟩
  · refine (RS.bytes_frame hf (fun r hr => ?_) (by have := hL.nwPar; omega_using [this])).trans h.par
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (RS.bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.rl)).trans h.rand
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOR.symm
    · exact hL.dRS
    · exact nr hL.dFR

end VG.Proof.Dsa.PPC64LE.GK

end

end

/-!
# DSA key generation on PPC64LE: the entry

`entry_ok`: from the frame's push, `entry` saves the registers and the
return address, writes `vg_dsa_derive_key`'s argument on the stack, keeps
the call's data in the registers of `Ctx`, starts with no octets consumed,
and zeroes the nonce; memory changes in the frame only.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.GK

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

/-- The frame's local variable space contains its offsets from 32 on. -/
theorem frameR_contains {L : GL} {s₀ : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) {d n : Nat} (h₁ : 32 ≤ d)
    (h₂ : d + n ≤ frameBytes) : (frameR frameBytes s₀).Contains (off L.F d) n := by
  have hF := hL.fnw
  simp only [frameR, hsp, frameBytes] at hF h₂ ⊢
  rw [show L.sp - BitVec.ofNat 64 304 + 32 = off L.F 32 from rfl]
  exact VG.Offset.contains L.F h₁ (by omega_using [h₂]) (by omega_using [])

/-- The frame's offsets past it are the stack pointer's. -/
theorem F_add (L : GL) (d : Nat) : off L.F (frameBytes + d) = L.sp + BitVec.ofNat 64 d := by
  simp only [off, GL.F]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The octets of a region apart from the frame are kept by a change within it. -/
theorem bytes_outside {L : GL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : k ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  refine ho _ (.inr ?_)
  obtain hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega_using [hi]) (by omega_using [hk, hi])
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

theorem add0 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

/-- The nonce is a working space of the frame. -/
theorem scr_nonce {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR frameBytes s₀ :: s₀.wr) : Scr t (off L.F oNonce) 32 := by
  have hF := hL.fnw
  simp only [frameBytes] at hF
  refine ⟨⟨(frameR frameBytes s₀).base, 88, 272, by rw [hw]; exact List.mem_cons_self .., ?_, by decide,
    by decide⟩, ?_⟩
  · show L.sp - BitVec.ofNat 64 304 + BitVec.ofNat 64 120 = s₀.sp - BitVec.ofNat 64 304 + 32 + BitVec.ofNat 64 88
    rw [hsp, BitVec.add_assoc]
    rfl
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega_using [hF]

/-- What `entry` leaves. -/
structure Entered (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : gkContract.pre s₀) :
    WP isa (.block entry) (allocated frameBytes s₀) (Entered (glOf s₀) s₀) := by
  obtain hL := glOf_ok h
  generalize hLd : glOf s₀ = L at hL
  obtain hsp : s₀.sp = L.sp := by rw [← hLd]; rfl
  have hF := hL.fnw
  have hF' := hF
  simp only [frameBytes] at hF'
  obtain hE : (allocated frameBytes s₀).sp = L.F := by simp only [allocated, hsp]
  obtain hin : ∀ i < 19, InRegions (allocated frameBytes s₀).wr (off L.F (oSave + 8 * i)) 8 := fun i hi =>
    ⟨_, List.mem_cons_self .., frameR_contains hL hsp (by simp only [oSave]; omega_using [])
      (by simp only [oSave, frameBytes]; omega_using [hi])⟩
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok _ hF hE hin) fun t₁ h₁ => ?_
  -- The call's data.
  obtain eo : s₀.gpr .r3 = L.out := by rw [← hLd]; rfl
  obtain eu : s₀.gpr .r5 = L.used := by rw [← hLd]; rfl
  obtain ek : s₀.gpr .r6 = L.par := by rw [← hLd]; rfl
  obtain ep : s₀.gpr .r8 = BitVec.ofNat 64 L.pl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain eq : s₀.gpr .r9 = BitVec.ofNat 64 L.ql := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain ed : s₀.gpr .r10 = L.rand := by rw [← hLd]; rfl
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain a1 : stackArg s₀ 1 = L.scr := by rw [← hLd]; rfl
  obtain a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  -- Memory so far changed within the frame.
  obtain o₀ : Outside L.F 0 8 s₀.mem (allocated frameBytes s₀).mem := by
    intro x hx
    simp only [allocated, hsp, ofs] at hx ⊢
    apply Mem.write_apply
    show ¬ (x - L.F).toNat < 8
    omega_using [hx]
  obtain o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    (o₀.mono (by omega_using []) (by simp only [frameBytes]; omega_using [])).trans (h₁.out.mono (by omega_using [])
      (by simp only [oSave, frameBytes]; omega_using []))
  -- The arguments on the stack.
  obtain ⟨-, -, hrd, -⟩ := h
  obtain hargs : ∀ i < 3, InRegions (t₁.rd ++ t₁.wr) (L.F + BitVec.ofNat 64 (argOff i)) 8 ∧
      t₁.mem.readW (L.F + BitVec.ofNat 64 (argOff i)) 64 = stackArg s₀ i := fun i hi => by
    obtain e : L.F + BitVec.ofNat 64 (argOff i) = stackArgAddr s₀ 0 + BitVec.ofNat 64 (8 * i) := by
      rw [show L.F + BitVec.ofNat 64 (argOff i) = off L.F (frameBytes + (96 + 8 * i)) by
        simp only [argOff, frameBytes]; rw [show 304 + 96 + 8 * i = 304 + (96 + 8 * i) by omega_using []], F_add,
        stackArgAddr, hsp, show 32 + 8 * (8 + 0) = 96 by rfl, BitVec.add_assoc, BitVec.ofNat_add]
    refine ⟨?_, ?_⟩
    · rw [h₁.rd, e]
      exact ⟨gkStackArgs s₀, List.mem_append_left _ (show gkStackArgs s₀ ∈ s₀.rd by rw [hrd]; simp),
        VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
    · rw [show L.F + BitVec.ofNat 64 (argOff i) = off L.F (argOff i) from rfl,
        show t₁.mem.readW (off L.F (argOff i)) 64 = word t₁.mem L.F (argOff i) from rfl,
        o₁.word (.inr (by simp only [argOff, frameBytes]; omega_using [])) (by simp only [argOff, frameBytes]; omega_using [hi])]
      show s₀.mem.readW (L.F + BitVec.ofNat 64 (argOff i)) 64 = _
      rw [e]
      simp only [stackArg, stackArgAddr]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 + 8 * (8 + 0) + 8 * i = 32 + 8 * (8 + i) by omega_using []]
  obtain ⟨l0, v0⟩ := hargs 0 (by decide)
  obtain ⟨l1, v1⟩ := hargs 1 (by decide)
  obtain ⟨l2, v2⟩ := hargs 2 (by decide)
  simp only [argOff, frameBytes, Nat.reduceAdd, Nat.reduceMul] at l0 v0 l1 v1 l2 v2
  obtain st : InRegions t₁.wr (L.F + BitVec.ofNat 64 96) 8 := by
    rw [h₁.wr]; exact ⟨_, List.mem_cons_self .., frameR_contains hL hsp (by omega_using []) (by simp only [frameBytes]; omega_using [])⟩
  obtain hr : ∀ r, r ≠ .r0 → r ≠ .r12 → t₁.gpr r = s₀.gpr r := fun r h0 h12 => h₁.others r h0 h12
  simp only [argOff, oArgs, frameBytes, Nat.reduceAdd, Nat.reduceMul]
  refine WP.mono (WP.keep [.r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r30] (Q := fun t =>
    t.gpr .r18 = L.out ∧ t.gpr .r19 = L.par ∧ t.gpr .r20 = BitVec.ofNat 64 L.pl ∧ t.gpr .r21 = BitVec.ofNat 64 L.ql ∧
      t.gpr .r22 = L.scr ∧ t.gpr .r23 = L.rand ∧ t.gpr .r24 = BitVec.ofNat 64 L.rl ∧ t.gpr .r30 = L.used ∧
      t.gpr .r25 = BitVec.ofNat 64 0 ∧ t.gpr .r26 = BitVec.ofNat 64 L.sl ∧
      t.mem = t₁.mem.writeW (L.F + BitVec.ofNat 64 96) (BitVec.ofNat 64 L.sl))
    (by prun [h₁.r12, l0, l1, l2, v0, v1, v2, a0, a1, a2, st,
      hr .r3 (by decide) (by decide), hr .r5 (by decide) (by decide), hr .r6 (by decide) (by decide),
      hr .r8 (by decide) (by decide), hr .r9 (by decide) (by decide), hr .r10 (by decide) (by decide),
      eo, eu, ek, ep, eq, ed, add0])
    (by decide)) fun t₂ ⟨⟨b18, b19, b20, b21, b22, b23, b24, b30, b25, b26, bm⟩, k₂⟩ => ?_
  obtain e₂sp : t₂.sp = L.F := by rw [k₂.sp, h₁.sp, hE]
  obtain e₂wr : t₂.wr = frameR frameBytes s₀ :: s₀.wr := by rw [k₂.wr, h₁.wr]; rfl
  refine WP.mono (clearNonce_ok t₂ hF e₂sp (scr_nonce hL hsp e₂wr)) fun t ⟨⟨_, tz, tou⟩, k₃⟩ => ?_
  -- Memory on exit, from `t₁`'s.
  obtain o₂ : Outside L.F oArgs 8 t₁.mem t₂.mem := by
    rw [bm]
    exact (writeW_outside _ L.F (d := 96) _ (by omega_using [])).mono (by simp only [oArgs]; omega_using []) (by simp only [oArgs]; omega_using [])
  obtain o₃ : Outside L.F 0 frameBytes s₀.mem t.mem :=
    (o₁.trans (o₂.mono (by omega_using []) (by simp only [oArgs, frameBytes]; omega_using []))).trans
      (tou.mono (by omega_using []) (by simp only [oNonce, frameBytes]; omega_using []))
  obtain w₃ : ∀ d, (d + 8 ≤ oArgs ∨ oNonce + 32 ≤ d) → d + 8 ≤ frameBytes →
      t.mem.readW (off L.F d) 64 = t₁.mem.readW (off L.F d) 64 := fun d hd hd' => by
    obtain e1 := tou.word (d := d) (by simp only [oNonce, oArgs] at hd ⊢; omega_using [hd]) (by simp only [frameBytes] at hd'; omega_using [hd'])
    obtain e2 := o₂.word (d := d) (by simp only [oNonce, oArgs] at hd ⊢; omega_using [hd]) (by simp only [frameBytes] at hd'; omega_using [hd'])
    exact e1.trans e2
  obtain g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ∉ ([.r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
      .r30] : List Reg) → t.gpr r = s₀.gpr r := fun r h0 h12 hr =>
    (k₃.gpr r (by simp [h0, h12])).trans ((k₂.gpr r hr).trans (h₁.others r h0 h12))
  refine ⟨⟨k₃.sp.trans e₂sp, by rw [k₃.rd, k₂.rd, h₁.rd]; rfl, k₃.wr.trans e₂wr, g₃ .r2 (by decide) (by decide) (by decide),
    (k₃.gpr _ (by decide)).trans b18, (k₃.gpr _ (by decide)).trans b19, (k₃.gpr _ (by decide)).trans b20,
    (k₃.gpr _ (by decide)).trans b21, (k₃.gpr _ (by decide)).trans b22, (k₃.gpr _ (by decide)).trans b23,
    (k₃.gpr _ (by decide)).trans b24, (k₃.gpr _ (by decide)).trans b26, (k₃.gpr _ (by decide)).trans b30,
    fun i hi => ?_, ?_, ?_,
    bytes_outside o₃ hL.dFK (by have := hL.nwPar; omega_using [this]), bytes_outside o₃ hL.dFR (Nat.le_of_lt hL.rl)⟩,
    (k₃.gpr _ (by decide)).trans b25, tz⟩
  · rw [w₃ _ (.inr (by simp only [oSave, oNonce]; omega_using [])) (by simp only [oSave, frameBytes]; omega_using [hi])]
    exact h₁.saved i hi
  · rw [w₃ _ (.inr (by decide)) (by decide)]
    exact h₁.savedLr
  · rw [show t.mem.readW (off L.F oArgs) 64 = t₂.mem.readW (off L.F oArgs) 64 from
      tou.word (by simp only [oNonce, oArgs]; omega_using []) (by simp only [oArgs]; omega_using []), bm]
    simp only [off, oArgs]
    rw [Mem.readW_writeW_self64]

end VG.Proof.Dsa.PPC64LE.GK
