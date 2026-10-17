module

public import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
public import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
meta import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Verified
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Verified
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
public import VerifiedGarbage.Impl.Sha512.X86_64.Stream
meta import VerifiedGarbage.Impl.Sha512.X86_64.Stream
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Verified
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Verified
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit

/-!
# Streaming SHA-512 on x86-64: `update` and `finalize`

`update` and `finalize` are the generic streaming code
(`Impl/MdStream/X86_64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/X86_64/`) for the SHA-512 family's instance
(`Proof/Sha512/Md.lean`), for any implementation `f` of the compression function
(`CalleeOk`: `scalar_ok`, `avx2_ok`, `shani_ok`), given what the family's own
pieces do: its length field and digest (`shape`) and that the taint analysis
accepts its code between the calls (`taints`).
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (len64 out64)
open VG.Impl.Sha512.X86_64 (at_)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append)
open VG.Impl.Sha512.X86_64.Stream (Callee update finalize)

abbrev params := Impl.Sha512.X86_64.Stream.params

theorem dims : Dims params := ⟨.inr rfl, by decide, by decide, by decide⟩

theorem wp_shri {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {n : Nat}
    (hn : 1 ≤ n ∧ n ≤ 63) (k : ∀ s', Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

theorem lenOf_split (x : BitVec 64) :
    md.lenOf x = bytes64 true (x >>> 61) ++ bytes64 true (BitVec.ofNat 64 (8 * x.toNat)) :=
  Proof.Sha512.lenOf_split x

/-- The length field: `count >> 61`, then `8 count`, big-endian, built in
`xmm7` and stored with one 16-byte store. -/
theorem len_ok (s : State) (hout : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 176) 16) :
    WP isa (.block params.len) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 176) (md.lenOf (s.gpr .r12)) := by
  show WP isa (.block (Impl.MdStream.X86_64.lenV128 ++ ([.movdquStore (at_ .rbx 176) .xmm7] : List Instr))) s _
  rw [WP.block_append_iff]
  refine (lenV128_ok s).mono fun s₁ ⟨g₁, rd₁, wr₁, m₁, _, x₁⟩ => ?_
  refine wp_movdquStore (a := s.gpr .rbx + BitVec.ofNat 64 176)
    (by rw [ea_at, g₁ _ (by decide), ofInt_natCast]) (by rw [wr₁]; exact hout)
    fun s₂ g₂ m₂ rd₂ wr₂ => WP.block_nil ⟨fun r h => by rw [g₂, g₁ r h], by rw [rd₂, rd₁], by rw [wr₂, wr₁], ?_⟩
  rw [m₂, m₁, Mem.writeW, Proof.Sha256.Stream.write_eq_writeBytes, lenOf_split, ← x₁]
  rfl

theorem digest_eq (mem : Mem) (p : Addr) :
    md.digest (md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
  simp [md, Spec.Sha512.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, bytes64,
    Spec.Sha512.wordBytes]

theorem shape : Shape (P := params) md where
  lenV s := (lenV128_ok s).mono fun _ ⟨g, rd, wr, m, x0, x7⟩ => ⟨g, rd, wr, m, x0, by
    rw [x7, lenOf_split]; rfl⟩
  len s hout := len_ok s hout
  out s hin hout hd := by
    refine (out64_ok (n := 8) (by decide) hin hout hd).mono fun s' ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, ?_⟩
    rw [m, digest_eq]

theorem taints : Taints params :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, by decide, by decide⟩

theorem scalar_ok : CalleeOk (P := params) md Callee.scalar.code :=
  .of_verified Rolled.compress_verified.1 Rolled.compress_verified.2.1
    (by change (instrs Impl.Sha512.X86_64.Rolled.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha512.X86_64.Rolled.compress.depth = 0; lit_decide)

theorem avx2_ok : CalleeOk (P := params) md Callee.avx2.code :=
  .of_verified Avx2.Rolled.compress_verified.1 Avx2.Rolled.compress_verified.2.1
    (by change (instrs Impl.Sha512.X86_64.Avx2Rolled.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha512.X86_64.Avx2Rolled.compress.depth = 0; lit_decide)

theorem shani_ok : CalleeOk (P := params) md Callee.shani.code :=
  .of_verified ShaNi.compressWide_verified.1 ShaNi.compressWide_verified.2.1
    (by change (instrs Impl.Sha512.X86_64.ShaNi.compress).all _ = true; rw [← Code.allInstrs_eq]; lit_decide)
    (by change Impl.Sha512.X86_64.ShaNi.compress.depth = 0; lit_decide)

namespace Update

/-- `update` is verified if it never loads MXCSR. -/
theorem verified_of {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (update f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (update f) Proof.Sha512.updateX86_64 :=
  MdStream.X86_64.Update.verified dims taints hf hm

/-- A state satisfying `update`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Update.sat params

end Update

namespace Finalize

/-- `finalize` is verified if it never loads MXCSR. -/
theorem verified_of {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (finalize f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize f) Proof.Sha512.finalizeX86_64 :=
  MdStream.X86_64.Finalize.verified dims shape taints hf hm

/-- A state satisfying `finalize`'s precondition. -/
abbrev sat : State := MdStream.X86_64.Finalize.sat params

end Finalize

end VG.Proof.Sha512.X86_64.Stream
