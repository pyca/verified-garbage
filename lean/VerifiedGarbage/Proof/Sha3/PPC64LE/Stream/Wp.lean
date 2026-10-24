module

import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Proof.MdStream.Spec

/-!
# The SHA-3 sponge on PPC64LE: the logical instructions

Weakest-precondition rules for `xor` and `or` of registers, beside those of
`Proof/MdStream/PPC64LE/Common.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE VG.Proof.MdStream.PPC64LE

variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

end VG.Proof.Sha3.PPC64LE.Stream
