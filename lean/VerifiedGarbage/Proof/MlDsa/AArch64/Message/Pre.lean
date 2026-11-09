module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Message
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Layout
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Sha3.AArch64.Permute

/-!
# ML-DSA on AArch64, `sign_message`: the precondition and the layout

Untrusted: everything here is checked by Lean. The layout of runs of
`sign_message` (`slay`), with what the message wrappers share (`params`, `mScrLen`, `rKey`, `rMsg`, `rCtx`, `rStk`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

theorem mScr_eq (p : Params) : mScrLen p = oE p + 1024 := by
  simp only [mScrLen, messageScratchWords, oE]; omega_arith

theorem oE_lt {p : Params} (hp : p ∈ params) : oE p + 1024 < 2 ^ 31 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

section
variable (p : Params) (s : State)

abbrev rKey (n : Nat) : Region := ⟨s.gpr .x0, n⟩
abbrev rMsg : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
abbrev rCtx : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
abbrev rStk : Region := ⟨s.sp - 16#64, 16⟩

end

/-! ## Signing -/

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (s : State) : Lay where
  SP := s.sp
  key := s.gpr .x0
  keyLen := p.skLen
  msg := s.gpr .x1
  len := s.gpr .x2
  ctx := s.gpr .x3
  ctxLen := s.gpr .x4
  rnd := s.gpr .x5
  sig := s.gpr .x6
  scr := s.gpr .x7
  E := oE p
  rd := s.rd
  wr := s.wr

theorem slay_X (p : Params) (s : State) : Within (slay p s).XS ⟨s.gpr .x7, mScrLen p⟩ :=
  ⟨oE p, rfl, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq]⟩

theorem toNat_X {scr : Addr} {e n : Nat} (h : scr.toNat + n ≤ 2 ^ 64) (he : e + 1024 ≤ n) :
    (scr + BitVec.ofNat 64 e).toNat + 1024 ≤ 2 ^ 64 := by
  rw [toNat_add_ofNat (by omega_arith)]; omega_arith

end VG.Proof.MlDsa.AArch64.Message
