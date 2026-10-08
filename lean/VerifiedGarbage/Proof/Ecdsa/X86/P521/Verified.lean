import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Ecdsa.X86.Main
import VerifiedGarbage.Proof.Weierstrass.X86.MontModuli
import VerifiedGarbage.Proof.Ecdsa.X86.P521.Contract
import VerifiedGarbage.Proof.Ecdsa.X86.P521.Lit
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# ECDSA over P-521 on x86 (32-bit): `Verified`

P-521 is a curve the proof supports (`p521_ok`, and `Law` for its group law,
which the registration file supplies: `Proof.P521.law`), so `sign_ok` gives
the contract's postcondition; `ebx`, `esi`, `edi` and `ebp` are restored,
`esp` kept, and the return address too, as every write is in the working
space or `out`. Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a
counter.
-/

namespace VG.Proof.Ecdsa.X86.P521

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

theorem p521_nBits : Spec.Ecdsa.nBits p521.C = 521 := by
  show Spec.P521.curve.n.log2 + 1 = 521
  have h1 : 520 ≤ Spec.P521.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.P521.curve.n.log2 < 521 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- A hash of `66` bytes drops its last 7 bits. -/
theorem p521_sh : p521.sh = 7 := by
  unfold Cfg.sh
  rw [p521_nBits]
  rfl

theorem p521_ok : CfgOk p521 where
  n0 := by decide
  n10 := by decide
  onG := Proof.P521.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [p521_sh]; decide

  inv_p h := False.elim ((by decide : ¬ (p521.n = 4 ∧ p521.C.len = 32)) h)
  inv_n h := False.elim ((by decide : ¬ (p521.n = 4 ∧ p521.C.len = 32)) h)
  fp := ⟨rfl, rfl, Mont.p521p_ok⟩
  fn := ⟨rfl, rfl, Mont.p521n_ok⟩

theorem pre_of {s : State} (h : signX86.pre s) : Pre p521 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩

/-- No instruction writes `esp`, and the calls use 20 bytes of stack. -/
theorem sign_sp : SpOk signP521 p521.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem sign_x86 (hL : Weierstrass.Law Spec.P521.curve) (s : State) (hs : signX86.pre s) :
    ∃ t s', Exec isa signP521 s t s' ∧ abiPreserved s s' ∧ signX86.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := sign_ok p521_ok hL sign_sp hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, K.ret hp⟩, ?_⟩
  swap
  · simp only [signX86, BitVec.setWidth_append_eq_right]
    exact hpost
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact K.saved (.ebx, 0) (by decide)
  · exact K.saved (.esi, 4) (by decide)
  · exact K.saved (.edi, 8) (by decide)
  · exact K.saved (.ebp, 12) (by decide)
  · exact K.esp

/-- The hints of the constant-time checks forget the words known to hold base
addresses (`native_taint_decide_weak`): no address depends on a value loaded from
the working space, and the kernel evaluates every instruction faster with
less to look through. They keep the public slots of memory, unlike P-384's:
the setup stores the top 32-bit word of the hash's slot, past its 66 bytes,
as the constant 0, and the shift of the hash reads it into `edx`, which is
public at the end of a chunk of the hint only through that slot. -/
def weak (τ : VG.X86.Taint.T) : VG.X86.Taint.T := if τ.stk = [] then { τ with wbases := [] } else τ

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [132, 8192], argLen := 24, argBases := [(4, 0), (20, 1)],
    room := 20 }

theorem wf₀ {s : State} (hp : Pre p521 s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  have hn9 : p521.C.len = 66 := rfl
  rw [hn9] at ho
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀, hn9], by simpa [hp.wr, hn9] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hp.sp_lo, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth, hn9] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out
    · exact hp.stk_sc

theorem agree₀ {s₁ s₂ : State} (h₁ : signX86.pre s₁) (h₂ : signX86.pre s₂)
    (hpub : signX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3, a4⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, scR, ptr, a0, a4]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.sp_fit; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.sp_fit; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 ∨ (k - 4) / 4 = 4 := by
      omega_using [hk]
    rcases this with h | h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3
    · exact congrArg _ a4

theorem sign_ct : ConstantTime isa signX86.pre signX86.pub signP521 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by native_taint_decide_weak VG.Proof.Ecdsa.X86.P521.weak)

/-- The contract with the regions the shared one gives: the arguments'
slots writable rather than readable. -/
def signWide : Contract isa :=
  { signX86 with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 132⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 66⟩
    let digest : Region := ⟨(arg s 2).setWidth 64, 66⟩
    let k : Region := ⟨(arg s 3).setWidth 64, 66⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20, 20⟩
    s.rd = [d, digest, k] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint k ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧ k.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 132 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 66 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 66 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 66 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      20 ≤ (s.gpr .esp).toNat ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

def signRd (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 66⟩, ⟨(arg s 2).setWidth 64, 66⟩, ⟨(arg s 3).setWidth 64, 66⟩, ⟨argAddr s 0, 20⟩]
def signWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 132⟩, ⟨(arg s 4).setWidth 64, 8192⟩]

theorem signWide_pre (s : State) (h : signWide.pre s) : signX86.pre (s.withRegions (signRd s) (signWr s)) := by
  simp only [signX86, signRd, signWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000, 0x8000` at
`0x20004`. -/
def satMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x30 else
  if a = 0x20011 then 0x40 else if a = 0x20015 then 0x80 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 66⟩, ⟨0x3000, 66⟩, ⟨0x4000, 66⟩]
  wr := [⟨0x1000, 132⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 20⟩]

theorem signWide_implies : signWide.Implies (Spec.Ecdsa.P521.inst.signContract X86.abi 20) := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0x3000 := by decide
  have a3 : arg satState 3 = 0x4000 := by decide
  have a4 : arg satState 4 = 0x8000 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies [Spec.Ecdsa.P521.inst, Spec.Ecdsa.Instance.signContract, Spec.Ecdsa.Instance.signSig,
    Spec.P521.curve, Spec.Ecdsa.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow, signWide,
    signX86, sig] [a0, a1, a2, a3, a4, e, esp] using satState

theorem sign_verified (hL : Weierstrass.Law Spec.P521.curve) :
    Verified X86.target signP521 (Spec.Ecdsa.P521.inst.signContract X86.abi 20) := by
  have hsat := signWide_implies.sat_left
  have satLocal : ∃ s, signX86.pre s := hsat.elim fun s h => ⟨_, signWide_pre s h⟩
  have verifiedLocal : Verified X86.target signP521 signX86 :=
    Verified.of_correct (sign_x86 hL) sign_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal signRd signWr signWide_pre
    ?_ ?_ ?_ ?_ hsat) signWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [signRd, signWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [signWide, signX86, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [signWide, signX86, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ecdsa.X86.P521
