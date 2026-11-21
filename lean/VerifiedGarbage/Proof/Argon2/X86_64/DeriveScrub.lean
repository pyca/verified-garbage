module

public import VerifiedGarbage.Proof.Argon2.X86_64.DeriveVerified
public import VerifiedGarbage.Proof.Argon2.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Impl.Argon2.X86_64.Fn
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveLit
import VerifiedGarbage.Proof.Blake2.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_argon2_derive` without secret residue (x86-64)

`vg_argon2_derive` over any implementation of G (`CompressImpl`) and BLAKE2b
backend (`Blake2.X86_64.Backend`), followed by its cleanup, which wipes its
whole frame (`Impl.Argon2.X86_64.Fn.derive`). Its code is its code over a
stub (`stubCode`), with the implementations' code where it calls them
(`derive_fill`): the kernel evaluates what the cleanup needs of the stub
once (`stub_side`), and each implementation proves what it needs of its own
code where it is defined (`CompressImpl.side`, `Backend.side`).
-/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.Derive

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-- A stub of G. -/
@[instance_reducible] def stubG : Impl.Argon2.X86_64.Compressor := ⟨"", .block []⟩

/-- BLAKE2b's streaming functions over a stub of its compression function. -/
def stubHash : Impl.Argon2.X86_64.HPrime.Hash where
  initName := "vg_blake2b_init_core"
  init := Impl.Blake2.X86_64.Stream.init Spec.Blake2.b
  updateName := ""
  update := Impl.Blake2.X86_64.Stream.update Spec.Blake2.b ⟨"", .block []⟩
  finalizeName := ""
  finalize := Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b ⟨"", .block []⟩

/-- `vg_argon2_derive`'s code over the stubs. -/
def stubCode : Prog isa := @Impl.Argon2.X86_64.Derive.code stubG "" stubHash

theorem stub_side : stubSide stubCode VecLevel.sse.level (fun _ => 0) 344 [] = true := by lit_decide

/-- `vg_argon2_derive`'s code over `c` and `v` is its code over the stubs,
with theirs where it calls them. -/
theorem derive_fill [c : CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) {k : Nat}
    (hc : calleeSide c.code k 0 = true) (hv : calleeSide v.code k 0 = true) :
    Fill k (fun _ => 0) stubCode (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) := by
  unfold stubCode HPrime.hash stubHash Proof.Blake2.X86_64.Backend.update
    Proof.Blake2.X86_64.Backend.finalize Proof.Blake2.X86_64.Backend.init
    Proof.Blake2.X86_64.Backend.hashCallee
  fill_calls

/-- `vg_argon2_derive` over `c` and `v`, before its cleanup. -/
def plain [c : CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) :
    Unscrubbed Spec.Argon2.deriveApi target where
  code := Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)
  stack := 344
  verified := verified v name
  spSafe := code_spSafe v name

/-- `Spec.Argon2.deriveApi`'s function as emitted over `c` and `v`
(`Impl.Argon2.X86_64.Fn.derive`), its cleanup at the higher of their levels,
meets its contract in constant time and returns without secret residue. -/
theorem derive_scrubbed [c : CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) :
    VerifiedScrubbed target (Impl.Argon2.X86_64.Fn.derive (v.level.join c.level) name (HPrime.hash v))
      (Spec.Argon2.deriveApi.contract X86_64.abi 344) 0 :=
  verifiedScrubbedAllFill (plain v name) _ (Scrub.deriveOut 344)
    (derive_fill v name (calleeSide_mono (level_join_right v.level c.level) (Nat.le_refl _) c.side)
      (calleeSide_mono (level_join_left v.level c.level) (Nat.le_refl _) v.side))
    (Nat.zero_le _) (Nat.le_refl _) (ha := stub_side)

theorem derive_spSafe [CompressImpl] (v : Proof.Blake2.X86_64.Backend) (name : String) (lv : VecLevel) :
    (Impl.Argon2.X86_64.Fn.derive lv name (HPrime.hash v)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (code_spSafe v name)

end VG.Proof.Argon2.X86_64.Derive
