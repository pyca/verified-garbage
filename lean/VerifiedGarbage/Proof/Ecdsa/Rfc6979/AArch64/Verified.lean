module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.CT
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# Deterministic ECDSA on AArch64: `Verified`

The function of a curve `R` and a tier `t` of hash functions, for any hash
function the call names (`selOf`, in `hashIds`): `sign_ok`, for the
`RfcHash` of that one, gives the contract's postcondition and keeps the
callee-saved registers and the stack pointer; no instruction of the
function or of those it calls writes a callee-saved SIMD register
(`sign_keepsV`: the HMAC functions' and the streaming `update`'s, from what
the tier knows of each of them, and `core`'s, from what the curve knows of
it), so their low halves are kept too (`abiPreserved`). Constant time up to
the hash function and the number of candidates: two calls whose public data
agree name the same hash function, and `sign_ct` relates them. The
function's own code is checked for each size of hash function and of
scalars. Each curve's file shows that its contract implies `rfcAArch64`
(`sign_verified`'s `himp`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (Tier)

/-! ## No callee-saved SIMD register written -/

/-- A dispatch writes no callee-saved SIMD register if no case does. -/
theorem disp_keepsV (P : RfcHash) {f : Impl.Pbkdf2.Md.AArch64.Hash → Prog isa}
    (h : ∀ k (hk : k ∈ Spec.Ecdsa.Rfc6979.hashIds), (f ({ P with k, hk } : RfcHash).H).allInstrs keepsV = true) :
    ((cfgOf P).disp f).allInstrs keepsV = true := by
  refine Proof.Dispatch.chain_allInstrs keepsV (fun _ => rfl) (hashIds.map fun k => (k,
    match (cfgOf P).hs[k]? with | some H => f H | none => .block [])) fun kc hkc => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hkc
  have hk' : k ∈ Spec.Ecdsa.Rfc6979.hashIds := by
    simpa only [hashIds, Spec.Ecdsa.Rfc6979.hashIds] using hk
  show (match (cfgOf ({ P with k, hk := hk' } : RfcHash)).hs[k]? with
    | some H => f H | none => .block []).allInstrs keepsV = true
  rw [hs_k]
  exact h k hk'

variable (P : RfcHash)

theorem hmac_keepsV {dataA : List Instr} {ex dst : Nat}
    (hd : (Code.block (Cfg.hmacArgs₂ dataA ex) : Prog isa).allInstrs keepsV = true) :
    ((cfgOf P).hmac dataA ex dst).allInstrs keepsV = true := by
  have hi := disp_keepsV P (f := fun H => .call H.hmacInitN H.hmacInit) fun k hk =>
    ({ P with k, hk } : RfcHash).ok.hmacInit_keepsV
  have hu := disp_keepsV P (f := fun H => .call H.updN H.updC) fun k hk =>
    ({ P with k, hk } : RfcHash).ok.updKeepsV
  have hf := disp_keepsV P (f := fun H => .call H.hmacFinN H.hmacFin) fun k hk =>
    ({ P with k, hk } : RfcHash).ok.hmacFin_keepsV
  simp only [Cfg.hmac, Code.allInstrs.eq_2, Bool.and_eq_true]
  exact ⟨rfl, hi, hd, hu, rfl, hf⟩

theorem hmacV_keepsV : (cfgOf P).hmacV.allInstrs keepsV = true := hmac_keepsV P rfl

theorem msg_keepsV (b : Nat) (full : Bool) :
    (Code.block (Cfg.msg P.w P.Q b full) : Prog isa).allInstrs keepsV = true := by
  refine Code.allInstrs_keepsV_of_eraseImm (msg_erase _ _ b full) ?_
  rcases shape P with ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ <;>
    rw [hw, hq] <;> cases full <;> decide +kernel

theorem rekeyFull_keepsV (b : Nat) : ((cfgOf P).rekeyFull b).allInstrs keepsV = true := by
  simp only [Cfg.rekeyFull, Code.allInstrs.eq_2, Bool.and_eq_true]
  exact ⟨rfl, msg_keepsV P b true, hmac_keepsV P rfl, hmacV_keepsV P⟩

theorem rekey_keepsV : (cfgOf P).rekey.allInstrs keepsV = true := by
  simp only [Cfg.rekey, Code.allInstrs.eq_2, Bool.and_eq_true]
  exact ⟨rfl, msg_keepsV P 0 false, hmac_keepsV P rfl, hmacV_keepsV P⟩

theorem digG_keepsV : ((cfgOf P).disp fun H => .block ((cfgOf P).digG H.D)).allInstrs keepsV = true := by
  refine disp_keepsV P fun k hk => ?_
  have hv := (dlen_vals k hk).1
  rw [← RfcHash.dEq ({ P with k, hk } : RfcHash)] at hv
  have e₁ : (cfgOf P).len = P.Q := rfl
  have e₂ : (cfgOf P).wide = P.R.wide := rfl
  show (Code.block ((cfgOf P).digG ({ P with k, hk } : RfcHash).H.D) : Prog isa).allInstrs keepsV = true
  simp only [Cfg.digG, e₁, e₂]
  rcases shape P with ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ <;>
    rw [hW, hq] <;> rcases hv with h | h | h | h | h <;> rw [h] <;> decide +kernel

theorem conv_keepsV (hW : P.R.wide = true) {o s : Nat} (ho : o = fG ∧ s = 1 ∨ o = fT ∧ s = 7) :
    ((cfgOf P).conv o s).allInstrs keepsV = true := by
  obtain ⟨hw9, hQ66⟩ := P.sizesW hW
  have e₁ : (cfgOf P).len = 66 := hQ66
  have e₂ : (cfgOf P).w = 9 := hw9
  rw [conv_eq]
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [convBody, e₁, e₂, fG, fT] <;> decide +kernel

theorem start_keepsV : (cfgOf P).start.allInstrs keepsV = true := by
  have hd := digG_keepsV P
  cases hW : P.R.wide
  · have e : (cfgOf P).wide = false := hW
    simp only [Cfg.start, e, Bool.false_eq_true, ite_false, Code.allInstrs.eq_2, Bool.and_eq_true]
    exact ⟨rfl, hd, P.R.reduceKeepsV hW⟩
  · have e : (cfgOf P).wide = true := hW
    have h81 : 8 - (cfgOf P).sh = 1 := by show 8 - P.R.sh = 1; rw [sh7 hW]
    simp only [Cfg.start, e, ite_true, h81, Code.allInstrs.eq_2, Bool.and_eq_true]
    exact ⟨rfl, hd, conv_keepsV P hW (.inl ⟨rfl, rfl⟩), rfl⟩

theorem cand_keepsV : (cfgOf P).cand.allInstrs keepsV = true := by
  have hs : (cfgOf P).candStep.allInstrs keepsV = true := by
    simp only [Cfg.candStep, Code.allInstrs.eq_2, Bool.and_eq_true]
    exact ⟨hmacV_keepsV P, rfl, rfl⟩
  cases hW : P.R.wide
  · have e : (cfgOf P).wide = false := hW
    simp only [Cfg.cand, e, Bool.false_eq_true, ite_false, Code.allInstrs.eq_2, Code.allInstrs.eq_4,
      Bool.and_eq_true]
    exact ⟨rfl, hs⟩
  · have e : (cfgOf P).wide = true := hW
    have hsh : (cfgOf P).sh = 7 := sh7 hW
    simp only [Cfg.cand, e, ite_true, hsh, Code.allInstrs.eq_2, Code.allInstrs.eq_4, Bool.and_eq_true]
    exact ⟨rfl, hs, conv_keepsV P hW (.inr ⟨rfl, rfl⟩)⟩

theorem tryOne_keepsV : (cfgOf P).tryOne.allInstrs keepsV = true := by
  simp only [Cfg.tryOne, Code.allInstrs.eq_2, Code.allInstrs.eq_3, Code.allInstrs.eq_5, Bool.and_eq_true]
  exact ⟨cand_keepsV P, rfl, P.R.coreKeepsV, rfl, ⟨rekey_keepsV P, rfl⟩, rfl⟩

/-- No instruction writes a callee-saved SIMD register: not those of the
functions it calls, by what the tier and the curve know of them, nor its
own, which the kernel evaluates for each size of hash function and of
scalars. -/
theorem sign_keepsV : (cfgOf P).sign.allInstrs keepsV = true := by
  simp only [Cfg.sign, Cfg.body, Code.allInstrs.eq_2, Code.allInstrs.eq_4, Code.allInstrs.eq_6, Bool.and_eq_true]
  exact ⟨⟨rfl, ⟨rfl, rfl, start_keepsV P, rekeyFull_keepsV P 0, rekeyFull_keepsV P 1, rfl, tryOne_keepsV P, rfl⟩,
    rfl⟩, rfl⟩

/-! ## Any hash function of the tier -/

/-- The `RfcHash` of the hash function a call names. -/
def ofCall (R : RfcCurve) (J : Spec.Ecdsa.Rfc6979.Instance) (t : Tier) (hE : J.ecdsa = R.inst)
    (hpos : 0 < J.tries) (hlt : J.tries < 2 ^ 16) (s : State) (hk : selOf s ∈ Spec.Ecdsa.Rfc6979.hashIds) :
    RfcHash :=
  ⟨R, J, t, selOf s, hk, hE, hpos, hlt⟩

variable {R : RfcCurve} {J : Spec.Ecdsa.Rfc6979.Instance} {t : Tier} (hE : J.ecdsa = R.inst)
  (hpos : 0 < J.tries) (hlt : J.tries < 2 ^ 16)

include hE hpos hlt in
theorem sign_a64 (s : State) (h : (rfcAArch64 R.E J 512).pre s) :
    ∃ tr s', Exec isa (cfgT R t J.tries).sign s tr s' ∧ abiPreserved s s' ∧ (rfcAArch64 R.E J 512).post s s' := by
  let P := ofCall R J t hE hpos hlt s h.1
  obtain ⟨tr, s', he, ⟨hg, hsp⟩, hp⟩ := sign_ok (P := P) h rfl
  refine ⟨tr, s', he, ⟨hg, hsp, Exec.preservedV he (sign_keepsV P)⟩, ?_⟩
  have e : anyResult J s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3).toNat (selOf s) =
      some (result P.I s.mem (s.gpr .x1) (s.gpr .x2)) := by
    rw [dlen_of P h rfl]; exact anyResult_eq (P := P) _ _ _
  have hq : J.ecdsa.curve.len = P.Q := P.curveLen
  show match anyResult J s.mem (s.gpr .x1) (s.gpr .x2) (s.gpr .x3).toNat (selOf s) with
    | some (some rs, _) => _ | _ => _
  rw [e, hq]
  unfold postK at hp
  revert hp
  rcases (result P.I s.mem (s.gpr .x1) (s.gpr .x2)) with ⟨_ | rs, _⟩
  · exact id
  · intro h; rw [hE, R.curve]; exact h

include hE hpos hlt in
theorem sign_ct : ConstantTime isa (rfcAArch64 R.E J 512).pre (rfcAArch64 R.E J 512).pub
    (cfgT R t J.tries).sign := fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
  signK_ct (P := ofCall R J t hE hpos hlt s₁ h₁.1) s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, rfl⟩ ⟨h₂, hp.2.2.2.2.2.2.1.symm⟩
    hp e₁ e₂

/-- The notes on the implementation, for the documentation of the function
whose candidates `core` tries, in a stack frame of `frame` bytes. -/
def signNotes (core : String) (frame : Nat := Impl.Ecdsa.Rfc6979.AArch64.frameBytes) : String :=
  "Each HMAC calls the tier's `init`, the streaming `update` and `finalize` of the hash function `hash` \
  names, by a branch on `hash` (public), using the start of `scratch` for HMAC's states and working space \
  and the message; the digest is copied into the frame by a branch on it too, and `hlen`, the block size \
  and the selector are kept in the frame. `h = bits2octets(digest)` is the digest's leftmost bytes, or \
  the digest after zero bytes, less `n` by a conditional subtraction (P-521: shifted, whose integer is \
  below `n`). Each candidate is `V`s until it has the scalars' bytes (shifted on P-521), tried with `" ++
  core ++ "`, which uses all of `scratch`; whether to try another is computed without branches from its \
  result and the count of candidates left, so the code branches only on that and on `hash`. `K`, `V`, `h`, \
  the candidate, the count and the pointers are kept in a " ++ toString frame ++ "-byte stack frame, below \
  the 16 bytes saving `x30`, and the secrets are cleared before it is freed; the calls use the 16 bytes \
  below it."

include hE hpos hlt in
/-- Verified against any contract that implies the proof's (`himp`, for each curve). -/
theorem sign_verified {k : Contract isa} (himp : (rfcAArch64 R.E J 512).Implies k) :
    Verified AArch64.target (cfgT R t J.tries).sign k :=
  Verified.of_correct (sign_a64 hE hpos hlt) (sign_ct hE hpos hlt) himp

end VG.Proof.Ecdsa.Rfc6979.AArch64
