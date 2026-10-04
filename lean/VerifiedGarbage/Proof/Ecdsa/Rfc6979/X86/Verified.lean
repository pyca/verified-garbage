import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.CT
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame

/-!
# Deterministic ECDSA over P-256 on x86 (32-bit): `Verified`

For any hash function `P`: `sign_ok` gives the contract's postcondition and
restores the callee-saved registers, `esp` and the return address
(`abiPreserved`); constant time up to the number of candidates: `sign_ct`.
No instruction of the function or of those it calls writes `esp` but the
frames' (`sign_spSafe`, from `body_nosp`). The proof is against `rfcX86`,
whose arguments' slots are readable, and moves to `rfcWide`, which makes
them writable as the shared contract does, by `Verified.narrowTo`; each
instance's file shows that the shared contract implies `rfcWide`
(`sign_verified`'s `himp`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86

/-- No instruction writes `esp` but the frames'. -/
theorem sign_spSafe (P : RfcHash) : (cfgOf P).sign.all (fun i => !isa.writesSp i) = true := by
  refine Code.all_of_allInstrs ?_
  have h := allInstrs_of_noSp (body_nosp P)
  simp only [Proof.Pbkdf2.Whole.X86.clobbers_esp] at h
  simp only [Cfg.sign, Code.allInstrs, h]
  decide

theorem sign_x86 (P : RfcHash) (s : State) (h : (rfcX86 P.I).pre s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧ (rfcX86 P.I).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sign_ok (P := P) h
  exact ⟨t, s', he, hg, hp⟩

/-- The contract with the regions the shared one gives: the arguments'
slots writable rather than readable. -/
def rfcWide (I : Spec.Ecdsa.Rfc6979.Instance) : Contract isa :=
  { rfcX86 I with
  pre := fun s =>
    let out : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let d : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let digest : Region := ⟨(arg s 2).setWidth 64, I.hashLen⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 8192⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 256, 256⟩
    256 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
    s.rd = [d, digest] ∧ s.wr = [out, scratch, args] ∧
      out.Disjoint d ∧ out.Disjoint digest ∧ out.Disjoint scratch ∧
      d.Disjoint scratch ∧ digest.Disjoint scratch ∧
      args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint out ∧ stack.Disjoint d ∧ stack.Disjoint digest ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + I.hashLen ≤ 2 ^ 32 ∧ (arg s 3).toNat + 8192 ≤ 2 ^ 32 }

def wideRd (I : Spec.Ecdsa.Rfc6979.Instance) (s : State) : List Region :=
  [⟨(arg s 1).setWidth 64, 32⟩, ⟨(arg s 2).setWidth 64, I.hashLen⟩, ⟨argAddr s 0, 16⟩]
def wideWr (s : State) : List Region := [⟨(arg s 0).setWidth 64, 64⟩, ⟨(arg s 3).setWidth 64, 8192⟩]

theorem wide_pre (I : Spec.Ecdsa.Rfc6979.Instance) (s : State) (h : (rfcWide I).pre s) :
    (rfcX86 I).pre (s.withRegions (wideRd I s) (wideWr s)) := by
  obtain ⟨h₁, h₂, -, -, h⟩ := h
  simp only [rfcX86, wideRd, wideWr, arg_withRegions, argAddr_withRegions, State.withRegions_gpr,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨h₁, h₂, trivial, trivial, h⟩

/-- The notes on the implementation, for the documentation of the function
with HMAC's `init` `hiN`, the streaming `update` `updN` and HMAC's
`finalize` `hfN`. -/
def signNotes (hiN updN hfN : String) : String :=
  "Computes `h = bits2octets(digest)` by a conditional subtraction of `n` from the digest's leftmost \
  32 bytes, and each HMAC with `" ++ hiN ++ "`, `" ++ updN ++ "` and `" ++ hfN ++ "`, using the start \
  of `scratch` for HMAC's states and working space and the message. Each candidate `k`, the leftmost \
  32 bytes of `V`, is tried with `vg_ecdsa_p256_sign`, which uses all of `scratch`; whether to try \
  another is computed without branches from its result and the count of candidates left, so the code \
  branches only on that. `K`, `V`, `h`, the count and our caller's registers are kept in a 180-byte \
  stack frame, whose secrets are cleared before it is released; the calls use the 76 bytes below it."

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x8000` at
`0x20004`. -/
def satMem : Mem := fun a =>
  if a = 0x20005 then 0x10 else if a = 0x20009 then 0x20 else if a = 0x2000d then 0x30 else
  if a = 0x20011 then 0x80 else 0

/-- A state satisfying the precondition, for a digest of `D` bytes. -/
def satState (D : Nat) : State where
  gpr r := match r with
    | .esp => 0x20000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, D⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 16⟩]

theorem sign_verified (P : RfcHash) (himp : (rfcWide P.I).Implies (P.I.signContract X86.abi 256)) :
    Verified X86.target (cfgOf P).sign (P.I.signContract X86.abi 256) := by
  have hsat := himp.sat_left
  have satLocal : ∃ s, (rfcX86 P.I).pre s := hsat.elim fun s h => ⟨_, wide_pre P.I s h⟩
  have verifiedLocal : Verified X86.target (cfgOf P).sign (rfcX86 P.I) :=
    Verified.of_correct (sign_x86 P) sign_ct (.refl satLocal)
  apply Verified.of_implies (Verified.narrowTo verifiedLocal (wideRd P.I) wideWr (wide_pre P.I)
    ?_ ?_ ?_ ?_ hsat) himp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.2.1, h.2.2.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [wideRd, wideWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (rfl | rfl | rfl) | (rfl | rfl) <;> simp
  · intro s h a n ⟨r, hr, hc⟩
    rw [h.2.2.2.1]
    refine ⟨r, ?_, hc⟩
    simp only [wideWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> simp
  · intro s t _ h
    simpa only [rfcWide, rfcX86, arg_withRegions, State.withRegions_gpr, State.withRegions_mem] using h
  · intro s t _ _ h
    simpa only [rfcWide, rfcX86, arg_withRegions, State.withRegions_gpr, State.withRegions_mem] using h

end VG.Proof.Ecdsa.Rfc6979.X86
