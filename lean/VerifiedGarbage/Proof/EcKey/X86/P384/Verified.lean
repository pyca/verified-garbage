import VerifiedGarbage.Proof.EcKey.X86.Main
import VerifiedGarbage.Proof.EcKey.X86.P384.Contract
import VerifiedGarbage.Proof.EcKey.X86.P384.Lit
import VerifiedGarbage.Proof.Ecdsa.X86.P384.Verified
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline

/-!
# P-384 public keys on x86 (32-bit): `Verified`

`publicKey_ok` for P-384 (`p384_ok`, and `Law` for its group law, which the
registration file supplies: `Proof.P384.law`) gives the contract's
postcondition; `ebx`, `esi`, `edi` and `ebp` are restored, `esp` kept, and
the return address too, as every write is in the working space or `out`.
Constant time by taint tracking, as for the signature
(`Proof/Ecdsa/X86/Verified.lean`). The proof is against `pkX86`, whose
arguments' slots are readable, and moves to the shared contract, which makes
them writable, by `Verified.narrowTo`.
-/

namespace VG.Proof.EcKey.X86.P384

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.EcKey.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.X86.P384

theorem pre_of {s : State} (h : pkX86.pre s) : PkPre p384 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The return address is kept. -/
theorem ret_keep {s₀ s' : State} (hp : PkPre p384 s₀) (K : PkKeep p384 s₀ s') :
    s'.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 := by
  obtain ⟨m, hU, hO⟩ := K.frame
  have hU' : Outside (ptr s₀ 2) 0 size s₀.mem m :=
    hU.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine Mem.readW_congr fun i hi => ?_
  have h4 : i < 4 := by omega
  rw [← keep_of_disjoint' hU' hp.ret_sc (by decide) h4 (by decide),
    ← keep_of_disjoint' hO hp.ret_out (by decide) h4 (by decide)]

theorem post_of {s s' : State} (h : PkPost p384 s s') : pkX86.post s s' := by
  unfold PkPost at h
  show match pk s.mem ((arg s 1).setWidth 64) with
    | some (.affine x y) => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
        Spec.EcKey.bytesAt s'.mem ((arg s 0).setWidth 64) 97 = Spec.EcKey.encodePoint (.affine x y)
    | _ => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
        Spec.EcKey.bytesAt s'.mem ((arg s 0).setWidth 64) 97 = List.replicate 97 0
  rw [BitVec.setWidth_append_eq_right]
  revert h
  generalize hq : pk s.mem ((arg s 1).setWidth 64) = q
  rw [show Spec.EcKey.publicKey p384.C (dk p384 s) = pk s.mem ((arg s 1).setWidth 64) from rfl, hq]
  rcases q with _ | _ | ⟨x, y⟩ <;> exact id

theorem pk_x86 (hL : Weierstrass.Law Spec.P384.curve) (s : State) (hs : pkX86.pre s) :
    ∃ t s', Exec isa publicKeyP384 s t s' ∧ abiPreserved s s' ∧ pkX86.post s s' := by
  have hp := pre_of hs
  obtain ⟨t, s', he, K, hpost⟩ := publicKey_ok p384_ok rfl hL hp
  refine ⟨t, s', he, ⟨fun r hr => ?_, ret_keep hp K⟩, post_of hpost⟩
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
  { regs := .ofList [.esp], flags := false, lens := [97, 8192], argLen := 16, argBases := [(4, 0), (12, 1)] }

theorem wf₀ {s : State} (hp : PkPre p384 s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  have hn6 : p384.n = 6 := rfl
  rw [hn6] at ho
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀, hn6], by simpa [hp.wr, hn6] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth, hn6] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : pkX86.pre s₁) (h₂ : pkX86.pre s₂)
    (hpub : pkX86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2⟩ := hpub
  have hp₁ := pre_of h₁; have hp₂ := pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [ptr, a0, a2]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq (by have := hp₁.sp_fit; omega) h4 hk,
      VG.X86.Taint.argByte_eq (by have := hp₂.sp_fit; omega) h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 := by omega_using [hk]
    rcases this with h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2

theorem pk_ct : ConstantTime isa pkX86.pre pkX86.pub publicKeyP384 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide_weak VG.Proof.Ecdsa.X86.P384.weak)

/-- The contract with the regions the shared one gives: the arguments'
slots writable rather than readable. -/
def pkWide : Contract isa :=
  { pkX86 with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 97⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 48⟩
    let scratch : Region := ⟨(arg s 2).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 12⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [d] ∧ s.wr = [out, scratch, args] ∧ out.Disjoint scratch ∧ out.Disjoint d ∧ d.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 97 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 48 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 8192 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 16 ≤ 2 ^ 32 }

def pkRd (s : State) : List Region := [⟨(arg s 1).setWidth 64, 48⟩, ⟨argAddr s 0, 12⟩]
def pkWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 97⟩, ⟨(arg s 2).setWidth 64, 8192⟩]

theorem pkWide_pre (s : State) (h : pkWide.pre s) : pkX86.pre (s.withRegions (pkRd s) (pkWr s)) := by
  simp only [pkX86, pkRd, pkWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨True.intro, True.intro, h.2.2⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0x8000` at `0x20004`. -/
def satMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x80 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 48⟩]
  wr := [⟨0x1000, 97⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 12⟩]

theorem pkWide_implies : pkWide.Implies (Spec.EcKey.P384.inst.publicKeyContract X86.abi) := by
  have a0 : arg satState 0 = 0x1000 := by decide
  have a1 : arg satState 1 = 0x2000 := by decide
  have a2 : arg satState 2 = 0x8000 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  exact
    { pre := by sig_implies_pre [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
          Spec.P384.curve, Spec.EcKey.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, pkWide, pkX86, pk]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
          Spec.P384.curve, Spec.EcKey.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, pkWide, pkX86, pk]
        simp only [pkWide, pkX86, pk, Spec.P384.curve] at h
        revert h
        generalize Spec.EcKey.publicKey _ _ = q
        rcases q with _ | _ | ⟨x, y⟩ <;> exact id
      pub := by sig_implies_pub [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
          Spec.P384.curve, Spec.EcKey.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, pkWide, pkX86, pk]
      sat := by sig_implies_sat [Spec.EcKey.P384.inst, Spec.EcKey.Instance.publicKeyContract, Spec.EcKey.Instance.publicKeySig,
          Spec.P384.curve, Spec.EcKey.scratchWords, X86.abi, X86.argSlots, X86.argVal, X86.argBytes, pkWide, pkX86, pk] [a0, a1, a2, e, esp] using satState }

theorem pk_verified (hL : Weierstrass.Law Spec.P384.curve) :
    Verified X86.target publicKeyP384 (Spec.EcKey.P384.inst.publicKeyContract X86.abi) := by
  have hsat := pkWide_implies.sat_left
  have satLocal : ∃ s, pkX86.pre s := hsat.elim fun s h => ⟨_, pkWide_pre s h⟩
  have verifiedLocal : Verified X86.target publicKeyP384 pkX86 :=
    Verified.of_correct (pk_x86 hL) pk_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal pkRd pkWr pkWide_pre
    ?_ ?_ ?_ ?_ hsat) pkWide_implies
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.1, h.2.1]
    refine ⟨r, ?_, hc⟩
    simpa only [pkRd, pkWr, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, or_assoc, or_left_comm, or_comm] using hr
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [pkWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [pkWide, pkX86, arg_withRegions, State.withRegions_mem, State.withRegions_gpr] using h
  · intro s t _ _ h
    simpa only [pkWide, pkX86, arg_withRegions, State.withRegions_gpr] using h

end VG.Proof.EcKey.X86.P384
