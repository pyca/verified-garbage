module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RndSample
public import VerifiedGarbage.Proof.Dsa.RandomResult
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSFn
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
public import VerifiedGarbage.Proof.Dsa.RandomBytes
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Dsa.DomainShape
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveChecked
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
public import VerifiedGarbage.Proof.Dsa.RISCV64.RSEntry
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public import VerifiedGarbage.Impl.Dsa.RISCV64.Generate
public import VerifiedGarbage.Spec.Dsa.Generate

/-! ### `Dsa.RISCV64.GKCheck`, which this module and modules that import it used -/

section

/-! ### `Dsa.RISCV64.GKEntry`, which this module and modules that import it used -/

section

/-! ### `Dsa.RISCV64.GKCtx`, which this module and modules that import it used -/

section

/-!
# DSA key generation on RISC-V: the contract on the registers, and the frame's state

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Fn.lean` and `Ctx.lean`).
`gkContract`: `vg_dsa_generate_key(out = a0, out_len = a1, used = a2,
params = a3, params_len = a4, p_len = a5, q_len = a6, rand = a7, rand_len,
scratch, scratch_len)`, the last three on the stack, with the 192 bytes of
stack below the stack pointer that its frame uses (the functions it calls
use none). `GL`: a call's public data (`glOf`); `Ctx`: what holds in the
frame's body: the registers `entry` sets, the saved registers, `out`,
`used` and `vg_dsa_derive_key`'s argument on the stack in the frame, and
the domain and the tape as on entry. A change of memory in `out`,
`scratch` or the nonce keeps it (`Ctx.step`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.RISCV64.RS (frameR bytes_frame)

/-- The bytes of stack below the stack pointer the function uses. -/
abbrev gkStack : Nat := 192

/-- The arguments on the stack. -/
abbrev gkStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The result `generateKeyBytes` gives, on entry. -/
def gkRes (s : State) : Spec.Dsa.GenerateKeyResult :=
  Spec.Dsa.generateKeyBytes (s.gpr .a5).toNat (s.gpr .a6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)

/-- `vg_dsa_generate_key`, on the registers and the stack. -/
def gkContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let used : Region := ⟨s.gpr .a2, 8⟩
    let ps : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let rnd : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 gkStack, gkStack⟩
    gkStack ≤ s.sp.toNat ∧ s.sp.toNat + 8 * 3 ≤ 2 ^ 64 ∧
      s.rd = [ps, rnd, gkStackArgs s] ∧ s.wr = [out, used, scr] ∧
      out.Disjoint used ∧ out.Disjoint ps ∧ out.Disjoint rnd ∧ out.Disjoint scr ∧
      out.Disjoint (gkStackArgs s) ∧ used.Disjoint ps ∧ used.Disjoint rnd ∧
      used.Disjoint scr ∧ used.Disjoint (gkStackArgs s) ∧ ps.Disjoint scr ∧
      rnd.Disjoint scr ∧ scr.Disjoint (gkStackArgs s) ∧
      stk.Disjoint out ∧ stk.Disjoint used ∧ stk.Disjoint ps ∧ stk.Disjoint rnd ∧
      stk.Disjoint scr ∧ stk.Disjoint (gkStackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a5).toNat (s.gpr .a6).toNat ∧
      (s.gpr .a1).toNat = 3 * (s.gpr .a5).toNat + 2 * (s.gpr .a6).toNat ∧
      (s.gpr .a4).toNat = 2 * (s.gpr .a5).toNat + (s.gpr .a6).toNat ∧
      Spec.Dsa.generationScratchWords (s.gpr .a5).toNat ≤ (stackArg s 2).toNat ∧
      (s.gpr .a2).toNat % 8 = 0 ∧ (stackArg s 1).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = (gkRes s).status ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat =
        (gkRes s).key.getD (List.replicate (s.gpr .a1).toNat 0) ∧
      Spec.Rsa.wordsAt t.mem (s.gpr .a2) 1 = [BitVec.ofNat 64 (gkRes s).used]
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat).map (·.toNat) ++
          [(gkRes s₁).status, (gkRes s₁).used] ++ (gkRes s₁).trace =
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat).map (·.toNat) ++
          [(gkRes s₂).status, (gkRes s₂).used] ++ (gkRes s₂).trace

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
  ⟨s.sp, s.gpr .a0, s.gpr .a2, s.gpr .a3, s.gpr .a7, stackArg s 1, (s.gpr .a5).toNat,
    (s.gpr .a6).toNat, (stackArg s 0).toNat, (stackArg s 2).toNat⟩

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
  spTop : L.sp.toNat + 24 ≤ 2 ^ 64
  sp16 : L.sp.toNat % 16 = 0
  alU : L.used.toNat % 8 = 0
  alS : L.scr.toNat % 8 = 0
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
    dFO, dFU, dFK, dFR, dFS, -, nO, nU, nK, nR, nS, lv, hol, hkl, hsw, alU, alS, sp16⟩ := h
  simp only [Spec.Dsa.generationScratchWords] at hsw
  have e4 : 3 * (s.gpr .a5).toNat + 2 * (s.gpr .a6).toNat = (s.gpr .a1).toNat := hol.symm
  have e7 : 2 * (s.gpr .a5).toNat + (s.gpr .a6).toNat = (s.gpr .a4).toNat := hkl.symm
  refine ⟨lv, hsw, hF, hT, sp16, alU, alS, ?_, nU, ?_, nR, nS, (stackArg s 0).isLt, (stackArg s 2).isLt,
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

theorem fal : L.F.toNat % 8 = 0 := by
  have := hL.F_toNat; have := hL.spF; have := hL.sp16; simp only [frameBytes] at *; omega_arith

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
  wr : t.wr = frameR s₀ :: s₀.wr
  s1 : t.gpr .s1 = L.par
  s2 : t.gpr .s2 = lens L.pl L.ql
  s3 : t.gpr .s3 = L.rand
  s4 : t.gpr .s4 = BitVec.ofNat 64 L.rl
  s6 : t.gpr .s6 = L.scr
  sav : ∀ i < 12, t.mem.readW (off L.F (oSave + 8 * i)) 64 = s₀.gpr (cs i)
  ra : t.mem.readW (off L.F (oSave + 96)) 64 = s₀.gpr .ra
  a0 : t.mem.readW (off L.F 0) 64 = BitVec.ofNat 64 L.sl
  out : t.mem.readW (off L.F oOut) 64 = L.out
  used : t.mem.readW (off L.F oUsed) 64 = L.used
  par : Spec.Rsa.bytesAt t.mem L.par L.kl = Spec.Rsa.bytesAt s₀.mem L.par L.kl
  rand : Spec.Rsa.bytesAt t.mem L.rand L.rl = Spec.Rsa.bytesAt s₀.mem L.rand L.rl

/-- The registers `Ctx` fixes. -/
def ctxRegs : List Reg := [.s1, .s2, .s3, .s4, .s6]

/-- A change of memory in `out`, `scratch` or the nonce, with the registers
of `Ctx` kept, keeps `Ctx`. -/
theorem Ctx.step {L : GL} {s₀ t t' : State} (hL : L.Ok) (h : Ctx L s₀ t) (hsp : t'.sp = t.sp)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hg : ∀ r ∈ ctxRegs, t'.gpr r = t.gpr r)
    (hf : Frame [L.outR, L.scrR, L.nR] t.mem t'.mem) : Ctx L s₀ t' := by
  have hF := hL.fnw
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
  refine ⟨hsp.trans h.sp, hrd.trans h.rd, hwr.trans h.wr, (hg _ (by decide)).trans h.s1,
    (hg _ (by decide)).trans h.s2, (hg _ (by decide)).trans h.s3, (hg _ (by decide)).trans h.s4,
    (hg _ (by decide)).trans h.s6,
    fun i hi => (fw _ (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave, oNonce]; omega_using [])).trans (h.sav i hi),
    (fw _ (by decide) (by decide)).trans h.ra, (fw _ (by decide) (by decide)).trans h.a0,
    (fw _ (by decide) (by decide)).trans h.out, (fw _ (by decide) (by decide)).trans h.used, ?_, ?_⟩
  · refine (bytes_frame hf (fun r hr => ?_) (by have := hL.nwPar; omega_using [this])).trans h.par
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOK.symm
    · exact hL.dKS
    · exact nr hL.dFK
  · refine (bytes_frame hf (fun r hr => ?_) (Nat.le_of_lt hL.rl)).trans h.rand
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.dOR.symm
    · exact hL.dRS
    · exact nr hL.dFR

end VG.Proof.Dsa.RISCV64.GK

end

end

/-!
# DSA key generation on RISC-V: the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Fn.lean`). `entry_ok`: in
the frame, `entry` saves `s0`–`s11` and `ra`, keeps `out` and `used` in the
frame, the domain, the lengths, the tape, its length and `scratch` in
`s1`–`s4` and `s6`, `vg_dsa_derive_key`'s argument on the stack
(`scratch_len`) in the frame, `s5 := 0`, and zeroes the nonce (`Entered`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.RISCV64.RS (frameR lens_entry word_wW)

/-- The frame contains its offsets. -/
theorem frameR_contains {L : GL} {s₀ : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) {d n : Nat}
    (h : d + n ≤ frameBytes) : (frameR s₀).Contains (off L.F d) n := by
  have hF := hL.fnw
  simp only [frameR, hsp]
  exact VG.Offset.contains_base _ h (by simp only [frameBytes] at h; omega_using [h])

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

/-- A word of a region apart from the frame is kept by a change within it. -/
theorem readW_outside {L : GL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : 8 ≤ k) (hk' : k ≤ 2 ^ 64) : m'.readW A 64 = m.readW A 64 := by
  refine Mem.readW_congr fun i hi => ho _ (.inr ?_)
  obtain hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega) (by omega_using [hi])
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

/-- The nonce is a working space of the frame. -/
theorem scr_nonce {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) : Scr t (off L.F oNonce) 32 := by
  have hF := hL.fnw
  have ha := hL.fal
  simp only [frameBytes] at hF
  refine ⟨⟨(frameR s₀).base, oNonce, frameBytes, by rw [hw]; exact List.mem_cons_self .., ?_, by decide,
    by decide⟩, ?_, ?_⟩
  · simp only [hsp]
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega_using [hF]
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega_using [ha]

/-- A word of the frame is writable and aligned. -/
theorem frame_word {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) {d : Nat} (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) :
    InRegions t.wr (off L.F d) 8 ∧ (off L.F d).toNat % 8 = 0 := by
  have hF := hL.fnw
  have ha := hL.fal
  refine ⟨⟨_, by rw [hw]; exact List.mem_cons_self .., frameR_contains hL hsp hd⟩, ?_⟩
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by simp only [frameBytes] at hd; omega_using [hd])]
  simp only [frameBytes] at hF hd
  omega_using [h8, ha]

/-- What `entry` leaves. -/
structure Entered (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : gkContract.pre s₀) :
    WP isa (.block entry) (allocd frameBytes s₀) (Entered (glOf s₀) s₀) := by
  obtain hL := glOf_ok h
  generalize hLd : glOf s₀ = L at hL
  obtain hsp : s₀.sp = L.sp := by rw [← hLd]; rfl
  have hF := hL.fnw
  have hF' := hF
  simp only [frameBytes] at hF'
  have hspT := hL.spTop
  have hsp16 := hL.sp16
  obtain hE : (allocd frameBytes s₀).sp = L.F := by simp only [allocd, hsp]
  have hwA : (allocd frameBytes s₀).wr = frameR s₀ :: s₀.wr := rfl
  obtain hsw : SaveW (allocd frameBytes s₀) L.F := fun i hi =>
    frame_word hL hsp hwA (by simp only [oSave, frameBytes]; omega_using [hi]) (by simp only [oSave]; omega_using [])
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok _ hF hE hsw) fun t₁ h₁ => ?_
  -- The call's data.
  obtain eo : s₀.gpr .a0 = L.out := by rw [← hLd]; rfl
  obtain eu : s₀.gpr .a2 = L.used := by rw [← hLd]; rfl
  obtain ek : s₀.gpr .a3 = L.par := by rw [← hLd]; rfl
  obtain ed : s₀.gpr .a7 = L.rand := by rw [← hLd]; rfl
  obtain el : s₀.gpr .a6 <<< 16 + s₀.gpr .a5 = lens L.pl L.ql := by
    rw [lens_entry _ _ (by have := hL.ql; rw [← hLd] at this; simp only [glOf] at this; omega_using [this])]
    rw [← hLd]; rfl
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain a1 : stackArg s₀ 1 = L.scr := by rw [← hLd]; rfl
  obtain a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain hr : ∀ r, r ≠ .t0 → t₁.gpr r = s₀.gpr r := fun r h0 => h₁.others r h0
  obtain o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    h₁.out.mono (by omega_using []) (by simp only [oSave, frameBytes]; omega_using [])
  obtain fw := fun (d : Nat) (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) => frame_word hL hsp (t := t₁)
    (by rw [h₁.wr]; rfl) hd h8
  obtain ⟨w64, l64⟩ := fw 64 (by decide) (by decide)
  obtain ⟨w72, l72⟩ := fw 72 (by decide) (by decide)
  obtain ⟨w0, l0⟩ := fw 0 (by decide) (by decide)
  rw [show ([.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .addi .s1 .a3 0, .shift .sll .d .s2 .a6 16,
      .add .s2 .s2 .a5, .addi .s3 .a7 0, .addSp .t6 frameBytes, .load .d .s4 .t6 0, .load .d .s6 .t6 8,
      .load .d .t1 .t6 16, .store .d .t1 .t0 0, .li .s5 0] : List Instr) =
    [.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .addi .s1 .a3 0, .shift .sll .d .s2 .a6 16,
      .add .s2 .s2 .a5, .addi .s3 .a7 0] ++ [.addSp .t6 frameBytes, .load .d .s4 .t6 0, .load .d .s6 .t6 8,
      .load .d .t1 .t6 16, .store .d .t1 .t0 0, .li .s5 0] from rfl, WP.block_append_iff]
  refine WP.mono (wp_sp (WP.keep [.s1, .s2, .s3] (Q := fun t =>
    t.gpr .s1 = L.par ∧ t.gpr .s2 = lens L.pl L.ql ∧ t.gpr .s3 = L.rand ∧
      t.mem = (t₁.mem.writeW (off L.F oOut) L.out).writeW (off L.F oUsed) L.used)
    (by
      brun [h₁.t0, hr .a0 (by decide), hr .a2 (by decide), hr .a3 (by decide), hr .a5 (by decide),
        hr .a6 (by decide), hr .a7 (by decide), eo, eu, ek, ed, el, oOut, oUsed, w64, l64, w72, l72,
        exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨b1, b2, b3, bm⟩, k₂⟩, sp₂⟩ => ?_
  obtain ⟨_, _, hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstk, _⟩ := h
  obtain hrd' : gkStackArgs s₀ ∈ s₀.rd := by rw [hrd]; simp
  obtain o₂ : Outside L.F 0 frameBytes s₀.mem t₂.mem := by
    rw [bm]
    refine o₁.trans (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_).trans
      ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_)) <;> decide
  obtain hstk' : L.frR.Disjoint (gkStackArgs s₀) := by
    simpa only [GL.frR, GL.F, hsp, show frameBytes = gkStack from rfl] using hstk
  obtain hsa0 : stackArgAddr s₀ 0 = L.sp := by simp only [stackArgAddr, hsp]; exact BitVec.add_zero _
  obtain sw : ∀ i < 3, t₂.mem.readW (off L.F (192 + 8 * i)) 64 = stackArg s₀ i ∧
      InRegions (t₂.rd ++ t₂.wr) (off L.F (192 + 8 * i)) 8 ∧
      (off L.F (192 + 8 * i)).toNat % 8 = 0 := by
    intro i hi
    rw [show 192 + 8 * i = frameBytes + 8 * i from rfl, F_add]
    obtain hsub : Region.Sub ⟨L.sp + BitVec.ofNat 64 (8 * i), 8⟩ (gkStackArgs s₀) := by
      simp only [gkStackArgs, hsa0]; exact VG.Offset.sub_base _ (by omega_using [hi])
    refine ⟨?_, ⟨_, List.mem_append_left _ (by rw [k₂.2.1, h₁.rd]; exact hrd'), ?_⟩, ?_⟩
    · rw [readW_outside o₂ (hstk'.sub_right hsub) (by omega_using []) (by omega_using [])]
      simp only [stackArg, stackArgAddr, hsp]
    · simp only [gkStackArgs, hsa0]; exact VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega_using [hi])]; omega_using [hsp16]
  obtain ⟨r0, i0, al0⟩ := sw 0 (by decide)
  obtain ⟨r1, i1, al1⟩ := sw 1 (by decide)
  obtain ⟨r2, i2, al2⟩ := sw 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at r0 i0 al0 r1 i1 al1 r2 i2 al2
  have hF192 : L.F + BitVec.ofNat 64 192 = off L.F 192 := rfl
  obtain sp₂' : t₂.sp = L.F := by rw [sp₂, h₁.sp, hE]
  obtain t0₂ : t₂.gpr .t0 = L.F := by rw [k₂.1 .t0 (by decide), h₁.t0]
  have wr₂ : t₂.wr = t₁.wr := k₂.2.2
  rw [← wr₂] at w0
  refine WP.mono (wp_sp (WP.keep [.t6, .s4, .s6, .t1, .s5] (Q := fun t =>
    t.gpr .s4 = BitVec.ofNat 64 L.rl ∧ t.gpr .s6 = L.scr ∧ t.gpr .s5 = BitVec.ofNat 64 0 ∧
      t.mem = t₂.mem.writeW (off L.F 0) (BitVec.ofNat 64 L.sl))
    (by
      brun [exec_addSp (show 192 < 2048 by decide), exec_li_zero, sp₂', t0₂, hF192, frameBytes, r0, i0, al0,
        r1, i1, al1, r2, i2, al2, a0, a1, a2, w0, l0]
      rfl) (by decide) (by rfl))) fun t₃ ⟨⟨⟨c4, c6, c5, cm⟩, k₃⟩, sp₃⟩ => ?_
  obtain sp₃' : t₃.sp = L.F := by rw [sp₃, sp₂']
  obtain wr₃ : t₃.wr = frameR s₀ :: s₀.wr := by rw [k₃.2.2, wr₂, h₁.wr]; rfl
  refine WP.mono (wp_sp (clearNonce_ok t₃ hF sp₃' (scr_nonce hL hsp wr₃)))
    fun t₄ ⟨⟨⟨_, nz, o₄⟩, k₄⟩, sp₄⟩ => ?_
  -- Memory.
  obtain o₃ : Outside L.F 0 8 t₂.mem t₃.mem := by
    rw [cm]; exact writeW_outside _ _ _ (by decide)
  obtain o₂' : Outside L.F 64 16 t₁.mem t₂.mem := by
    rw [bm]
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  obtain o₁₄ : Outside L.F 0 88 t₁.mem t₄.mem :=
    (o₂'.mono (Nat.zero_le _) (by decide)).trans ((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce]; omega_using [])))
  obtain o₀₄ : Outside L.F 0 frameBytes s₀.mem t₄.mem :=
    o₂.trans (((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce, frameBytes]; omega_using []))))
  obtain w₄ : ∀ d, 64 ≤ d → d + 8 ≤ 88 → t₄.mem.readW (off L.F d) 64 = t₂.mem.readW (off L.F d) 64 :=
    fun d hd hd' => (o₄.word (by simp only [oNonce]; omega_using [hd]) (by omega_using [hd'])).trans
      (o₃.word (by omega_using [hd]) (by omega_using [hd']))
  obtain g2 : ∀ r, r ∉ [Reg.t6, .s4, .s6, .t1, .s5] → r ∉ [Reg.t0, .t1] →
      t₄.gpr r = t₂.gpr r := fun r h h' => (k₄.1 r h').trans (k₃.1 r h)
  refine ⟨⟨by rw [sp₄, sp₃'], by rw [k₄.2.1, k₃.2.1, k₂.2.1, h₁.rd]; rfl,
    by rw [k₄.2.2, wr₃], by rw [g2 _ (by decide) (by decide), b1], by rw [g2 _ (by decide) (by decide), b2],
    by rw [g2 _ (by decide) (by decide), b3], by rw [k₄.1 _ (by decide), c4], by rw [k₄.1 _ (by decide), c6],
    fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [k₄.1 _ (by decide), c5], nz⟩
  · exact (o₁₄.word (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using [hi])).trans (h₁.saved i hi)
  · exact (o₁₄.word (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using [])).trans h₁.savedRa
  · rw [show t₄.mem.readW (off L.F 0) 64 = t₃.mem.readW (off L.F 0) 64 from
      o₄.word (d := 0) (by simp only [oNonce]; omega_using []) (by omega_using []), cm, Mem.readW_writeW_self64]
  · rw [w₄ oOut (by decide) (by decide), bm, word_wW _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [w₄ oUsed (by decide) (by decide), bm, Mem.readW_writeW_self64]
  · exact bytes_outside o₀₄ hL.dFK (by have := hL.nwPar; omega_using [this])
  · exact bytes_outside o₀₄ hL.dFR (by have := hL.nwRand; omega_using [this])
end VG.Proof.Dsa.RISCV64.GK

end

end

/-!
# DSA key generation on RISC-V: the check of the domain

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Fn.lean`). `checkArgs` passes
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
  have e1 := lenP_eq (pl := L.pl) (ql := L.ql) (by omega_using [hp]) (by omega_using [hq])
  have e2 := lenQ_eq (pl := L.pl) (ql := L.ql) (by omega_using [hp]) (by omega_using [hq])
  refine WP.mono (wp_sp (WP.keep checkRegs (Q := fun t' => t'.gpr .a0 = L.par ∧
    t'.gpr .a1 = BitVec.ofNat 64 L.kl ∧ t'.gpr .a2 = BitVec.ofNat 64 L.pl ∧ t'.gpr .a3 = BitVec.ofNat 64 L.ql ∧
    t'.gpr .a4 = L.scr ∧ t'.gpr .a5 = BitVec.ofNat 64 L.sl ∧ t'.mem = t.mem) ?_ (by decide) (by rfl)))
    fun t' ⟨⟨⟨a0, a1, a2, a3, a4, a5, am⟩, k⟩, hsp⟩ =>
      ⟨⟨⟨hc.step hL hsp k.2.1 k.2.2 (fun r hr => k.1 r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a0, a1, a2, a3, a4, a5⟩, am, k⟩, hsp⟩
  unfold checkArgs
  brun [lenP, lenQ, hc.s1, hc.s2, hc.s6, e1, e2, hc.sp, exec_addSp (show 0 < 2048 by decide), BitVec.add_zero,
    i0, l0, o0, ← BitVec.ofNat_add]
  congr 1; simp only [GL.kl]; omega_using []

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
    have h1 := hL.F_toNat; have h2 := hL.spF; have h3 := hL.sp16; simp only [frameBytes] at h1 h2; omega_using [h1, h3]
  unfold pcContract
  simp only [State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ha.ctx.sp]
  rw [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), g .a4 (by decide),
    g .a5 (by decide), ha.a0, ha.a1, ha.a2, ha.a3, ha.a4, ha.a5, tn _ (by simp only [GL.kl]; omega_using [hp, hq]),
    tn (glOf s₀).pl (by omega_using [hp]), tn (glOf s₀).ql (by omega_using [hq]), tn _ hsl]
  exact ⟨rfl, rfl, hL.dKS, hL.nwPar, hL.nwScr, hL.lv, rfl, by simp only [Spec.Dsa.scratchWords]; omega_using [hsw],
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
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [GL.kl]; omega_using [hp, hq])]
  have e5 : (BitVec.ofNat 64 (glOf s₀).pl).toNat = (glOf s₀).pl := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hp])]
  have e6 : (BitVec.ofNat 64 (glOf s₀).ql).toNat = (glOf s₀).ql := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hq])]
  simp only [g .a0 (by decide), g .a1 (by decide), g .a2 (by decide), g .a3 (by decide), ha.a0, ha.a1, ha.a2,
    ha.a3, e4, e5, e6, hc.par] at hpost'
  exact hpost'

end VG.Proof.Dsa.RISCV64.GK

end

end

/-! ### `Dsa.RISCV64.GKDerive`, which only this module used -/

section

/-!
# DSA key generation on RISC-V: the call of `vg_dsa_derive_key_checked`

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Fn.lean`). `deriveArgs`
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

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Fn.lean`). q's octets
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
