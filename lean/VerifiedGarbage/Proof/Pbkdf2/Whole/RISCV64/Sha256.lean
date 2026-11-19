module

import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Impl.Sha256.RISCV64
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
meta import VerifiedGarbage.Impl.Sha256.RISCV64
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Proof.Sha256.Md
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
meta import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `Pbkdf2.RISCV64.Sha256Out`, which this module and modules that import it used -/

section

/-!
# PBKDF2-HMAC's iteration on RISC-V: SHA-256's digest

The code writing the first `n` words of SHA-256's digest, big-endian, from
the hash value at `s1` to `s3` (as SHA-256's streaming `finalize` does,
`Impl/Sha256/RISCV64/Stream.lean`): what the iteration needs of it
(`OutOk`, `out_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha256Out

open VG.RISCV64 VG.RISCV64.ByteLoad
open VG.Impl.Sha256.RISCV64.Stream (outW)
open VG.WriteBytes (writeBytes writeBytes_frame writeBytes_append writeBytes_nil)
open VG.Spec.Sha256 (stateAt wordBytes)
open VG.Proof.Sha256.RISCV64.Stream.Finalize (flat_length take_flatMap_wordBytes beBytes_word)

/-- `k` words of the digest are written. -/
structure OutI (s : State) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  keep : ∀ r, r ≠ .t1 → r ≠ .t2 → t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem (s.gpr .s3) (((stateAt s.mem (s.gpr .s1)).toList.take k).flatMap wordBytes)

theorem contains_pre (p : Addr) {n len : Nat} (h : n ≤ len) : (⟨p, len⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [h]

section
variable {s : State} {D : Nat} (hD : D ≤ 32) (hin : InRegions (s.rd ++ s.wr) (s.gpr .s1) 32)
  (hout : InRegions s.wr (s.gpr .s3) D) (hd : Region.Disjoint ⟨s.gpr .s1, 32⟩ ⟨s.gpr .s3, D⟩)
include hD hin hout hd

theorem step {k : Nat} (hk : 4 * k + 4 ≤ D) {t : State} (h : OutI s k t) {rest : List Instr}
    {Q : State → Prop} (hnext : ∀ t', OutI s (k + 1) t' → WP isa (.block rest) t' Q) :
    WP isa (.block (outW k ++ rest)) t Q := by
  have hx1 : t.gpr .s1 = s.gpr .s1 := h.keep _ (by decide) (by decide)
  have hx3 : t.gpr .s3 = s.gpr .s3 := h.keep _ (by decide) (by decide)
  have hP := flat_length (stateAt s.mem (s.gpr .s1)) k (by omega_using [hD, hk])
  simp only [outW, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega_using [hD, hk])
    (by rw [hx1, h.rd, h.wr]; exact VG.CallLay.inRegions_sub hin (by omega_using [hD, hk]) (by omega_using []))) fun t₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega_using [hD, hk])
    fun j hj => ?_) fun t₃ e₃ => hnext t₃ ?_
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.wr_write,
      RegUpd.wr_write, hx3, h.wr]
    exact VG.CallLay.inRegions_sub hout (by omega_using [hk, hj]) (by omega_using [hD])
  subst e₃
  refine ⟨h.rd, h.wr, h.sp, fun r a b => ?_, ?_⟩
  · simp only [RegUpd.gpr_write, a, b, ite_false]
    exact h.keep r a b
  · have hread : t.mem.readW (s.gpr .s1 + BitVec.ofNat 64 (4 * k)) 32 =
        (stateAt s.mem (s.gpr .s1))[k]'(by omega_using [hD, hk]) := by
      rw [h.mem, (writeBytes_frame (R := ⟨s.gpr .s3, D⟩) s.mem (s.gpr .s3) _ (contains_pre _ (by omega_using [hk, hP]))).readW
        (r := ⟨s.gpr .s1 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (Offset.sub_base _ (by omega_using [hD, hk]))
    simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, hx1, hx3, hread, beBytes_word]
    rw [h.mem, ← hP, writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega_using [hD, hk]), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega_using [hD, hk]), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem all {n : Nat} (hn : 4 * n ≤ D) {rest : List Instr} {Q : State → Prop}
    (hrest : ∀ t, OutI s n t → WP isa (.block rest) t Q) :
    ∀ j ≤ n, ∀ t, OutI s (n - j) t →
      WP isa (.block (((List.range n).drop (n - j)).flatMap outW ++ rest)) t Q := by
  intro j
  induction j with
  | zero =>
    intro _ t h
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by simp), List.flatMap_nil, List.nil_append]
    exact hrest t (by rwa [Nat.sub_zero] at h)
  | succ j ih =>
    intro hj t h
    rw [List.drop_eq_getElem_cons (by simp; omega_using [hj]), List.flatMap_cons, List.append_assoc,
      List.getElem_range]
    refine step hD hin hout hd (by omega_using [hn, hj]) h fun t' h' => ?_
    rw [show n - (j + 1) + 1 = n - j by omega_using [hj]]
    exact ih (by omega_using [hj]) t' (by rwa [show n - (j + 1) + 1 = n - j by omega_using [hj]] at h')

end

/-- The first `n` words of the digest. -/
theorem out_ok (n : Nat) (hn : n ≤ 8) : OutOk Proof.Sha256.md (4 * n) ((List.range n).flatMap outW) := by
  intro s hin hout hd
  have := all (s := s) (D := 4 * n) (by omega_using [hn]) hin hout hd (n := n) (Nat.le_refl _) (rest := [])
    (Q := fun s' => (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s3) ((Proof.Sha256.md.digest (Proof.Sha256.md.stateAt s.mem (s.gpr .s1))).take (4 * n)))
    (fun t h => WP.block_nil ⟨fun r a b _ => h.keep r a b, h.rd, h.wr, h.sp, by
      rw [h.mem]; congr 1
      show _ = ((stateAt s.mem (s.gpr .s1)).toList.flatMap wordBytes).take (4 * n)
      rw [take_flatMap_wordBytes]⟩) n (Nat.le_refl _) s
    ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by simp [writeBytes_nil]⟩
  rwa [Nat.sub_self, List.drop_zero, List.append_nil] at this

end VG.Proof.Pbkdf2.RISCV64.Sha256Out

end

end

/-! ### `Pbkdf2.RISCV64.Sha256`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-256 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-256's sizes, compression function and digest code (`it`): what its
proof needs of SHA-256 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha256

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-256's parameters of the iteration. -/
def it : It where
  N := 32
  B := 64
  D := 32
  CW := 80
  cmpN := "vg_sha256_compress"
  cmpC := Impl.Sha256.RISCV64.compress
  out := (List.range 8).flatMap Impl.Sha256.RISCV64.Stream.outW
  pad := padBE 64 32 8

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha256.md 80 Impl.Sha256.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha256.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha256.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-256, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 239 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha256S Proof.Sha256.md Spec.Sha256.H0 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  out := Sha256Out.out_ok 8 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha256.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha256S Wi).pre (iterK Spec.Hmac.sha256S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha256

end

end

/-!
# PBKDF2-HMAC-SHA-256 on RISC-V: the whole derivation

`pbkdf2` over SHA-256's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 240 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha256I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha256

open VG.RISCV64
open VG.Proof.Hmac.Stream.RISCV64.Sha256Family (hash256 ok256)

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := hash256
  hiN := Spec.Hmac.sha256I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha256I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha256_iterate"
  itC := Pbkdf2.RISCV64.Sha256.code
  itW := 240

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := ok256
  hiCt := Proof.Hmac.Stream.RISCV64.Sha256.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha256.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha256.hashOkW 240 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha256.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha256.ctW 240
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha256.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha256.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha256I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, hash256, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha256
