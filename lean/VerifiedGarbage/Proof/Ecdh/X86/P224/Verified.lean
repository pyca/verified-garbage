import VerifiedGarbage.Proof.Framework.NativeTaint
import VerifiedGarbage.Proof.Ecdh.X86.Main
import VerifiedGarbage.Proof.Ecdh.X86.P224.Contract
import VerifiedGarbage.Proof.Ecdh.X86.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.X86.P224.Verified
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# ECDH over P-224 on x86 (32-bit): `Verified`

`exchange_ok` for P-224 (`p224_ok`, and `Law` for its group law, which the
registration file supplies: `Proof.P224.law`) gives the contract's
postcondition; `ebx`, `esi`, `edi` and `ebp` are restored, `esp` kept, and
the return address too, as every write is in the working space or `out`.
Constant time by taint tracking, as for the signature
(`Proof/Ecdsa/X86/Verified.lean`). The proof is against `ecdhX86`, whose
arguments' slots are readable, and moves to the shared contract, which makes
them writable, by `Verified.narrowTo`.
-/

namespace VG.Proof.Ecdh.X86.P224

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdh.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.X86.P224

theorem pre_of {s : State} (h : ecdhX86.pre s) : EPre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

theorem post_of {s s' : State} (h : EPost p224 s s') : ecdhX86.post s s' := by
  unfold EPost at h
  show match ex s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) with
    | some z => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
        Spec.EcKey.bytesAt s'.mem ((arg s 0).setWidth 64) 28 = z
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
        Spec.EcKey.bytesAt s'.mem ((arg s 0).setWidth 64) 28 = List.replicate 28 0
  rw [BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : ex s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) = q
  rw [show Spec.Ecdh.exchange p224.C (dk p224 s)
      (Spec.Ecdsa.bytesAt s.mem (ptr s 2) (1 + 2 * p224.C.len)) = ex s.mem ((arg s 1).setWidth 64)
        ((arg s 2).setWidth 64) from rfl, hq]
  rcases q with _ | z <;> exact id

/-- No instruction writes `esp`, and the calls use 28 bytes of stack. -/
theorem ecdh_sp : SpOk exchangeP224 p224.stk := ⟨NoSp.of_all (by lit_decide), by lit_decide⟩

theorem ecdh_x86 (hL : Weierstrass.Law Spec.P224.curve) (s : State) (hs : ecdhX86.pre s) :
    ∃ t s', Exec isa exchangeP224 s t s' ∧ abiPreserved s s' ∧ ecdhX86.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := exchange_ok p224_ok hL rfl ecdh_sp hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, K.ret hp⟩, post_of hpost⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact K.saved (.ebx, 0) (by decide)
  · exact K.saved (.esi, 4) (by decide)
  · exact K.saved (.edi, 8) (by decide)
  · exact K.saved (.ebp, 12) (by decide)
  · exact K.esp

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [28, 8192], argLen := 20, argBases := [(4, 0), (16, 1)],
    room := 28 }

theorem wf₀ {s : State} (hp : EPre p224 s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  have hn9 : p224.C.len = 28 := rfl
  rw [hn9] at ho
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀, hn9], by simpa [hp.wr, hn9] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hp.sp_lo, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth, hn9] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out
    · exact hp.stk_sc

theorem agree₀ {s₁ s₂ : State} (h₁ : ecdhX86.pre s₁) (h₂ : ecdhX86.pre s₂)
    (hpub : ecdhX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [ptr, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.sp_fit; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.sp_fit; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega_using [hk]
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem ecdh_ct : ConstantTime isa ecdhX86.pre ecdhX86.pub exchangeP224 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by native_taint_decide_weak VG.Proof.Ecdsa.X86.P224.weak)

/-- The contract with the regions the shared one gives: the arguments'
slots writable rather than readable. -/
def ecdhWide : Contract isa :=
  { ecdhX86 with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 28⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 28⟩
    let peer : Region := ⟨(arg s 2).setWidth 64, 57⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [d, peer] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧
      out.Disjoint peer ∧ d.Disjoint scratch ∧ peer.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 28 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 28 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 57 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 8192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      28 ≤ (s.gpr .esp).toNat ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

def ecdhRd (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 28⟩, ⟨(arg s 2).setWidth 64, 57⟩, ⟨argAddr s 0, 16⟩]
def ecdhWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 28⟩, ⟨(arg s 3).setWidth 64, 8192⟩]

theorem ecdhWide_pre (s : State) (h : ecdhWide.pre s) : ecdhX86.pre (s.withRegions (ecdhRd s) (ecdhWr s)) := by
  simp only [ecdhX86, ecdhRd, ecdhWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x8000` at
`0x20004`. -/
def satMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x30 else
  if a = 0x20011 then 0x80 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 28⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x1000, 28⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 16⟩]

theorem ecdhWide_implies :
    ecdhWide.Implies (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst X86.abi 28) := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0x3000 := by decide
  have a3 : arg satState 3 = 0x8000 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract, Spec.Ecdh.Instance.exchangeSig,
    Spec.P224.curve, Spec.EcKey.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, stackBelow, ecdhWide,
    ecdhX86, ex] [a0, a1, a2, a3, e, esp] using satState

theorem ecdh_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified X86.target exchangeP224 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst X86.abi 28) := by
  have hsat := ecdhWide_implies.sat_left
  have satLocal : ∃ s, ecdhX86.pre s := hsat.elim fun s h => ⟨_, ecdhWide_pre s h⟩
  have verifiedLocal : Verified X86.target exchangeP224 ecdhX86 :=
    Verified.of_correct (ecdh_x86 hL) ecdh_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal ecdhRd ecdhWr ecdhWide_pre
    ?_ ?_ ?_ ?_ hsat) ecdhWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [ecdhRd, ecdhWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [ecdhWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [ecdhWide, ecdhX86, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [ecdhWide, ecdhX86, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.Ecdh.X86.P224
