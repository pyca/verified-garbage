module

public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.Pbkdf2.Whole.RISCV64.Fn
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Compress
public import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
public import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Shared
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512_256
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Impl.Sha512.RISCV64
public import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
import VerifiedGarbage.Proof.Hmac.Generic.Common
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Correct
meta import VerifiedGarbage.Impl.Sha512.RISCV64
meta import VerifiedGarbage.Impl.Sha512.RISCV64.Stream
meta import VerifiedGarbage.Spec.Pbkdf2.Generic
meta import VerifiedGarbage.Proof.Pbkdf2.Contract
meta import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Hmac.Generic.Common
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Md5.RISCV64.Compress
meta import VerifiedGarbage.Proof.Md5.RISCV64.Compress
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
import VerifiedGarbage.Proof.Md5.RISCV64.Stream
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Md5
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Impl.Md5.RISCV64
public import VerifiedGarbage.Impl.Md5.RISCV64.Stream
meta import VerifiedGarbage.Impl.Md5.RISCV64
meta import VerifiedGarbage.Impl.Md5.RISCV64.Stream
meta import VerifiedGarbage.Proof.Md5.Md
meta import VerifiedGarbage.Proof.Md5.RISCV64.Stream
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha512
import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Compress
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha224
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Impl.Sha256.RISCV64
public import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
import VerifiedGarbage.Proof.Sha256.Digest
meta import VerifiedGarbage.Impl.Sha256.RISCV64
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.RISCV64.Sha256
meta import VerifiedGarbage.Impl.Sha256.RISCV64.Stream
meta import VerifiedGarbage.Proof.Sha256.Md
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Common
meta import VerifiedGarbage.Proof.Sha256.Digest
public import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Pbkdf2.RISCV64.Calls
meta import VerifiedGarbage.Proof.Sha512.RISCV64.Stream.Finalize
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.WriteBytes

/-! ### `Pbkdf2.RISCV64.Sha512Out`, which only this module used -/

section

/-!
# PBKDF2-HMAC's iteration on RISC-V: the SHA-512 family's digest

The code writing the first `n` doublewords of SHA-512's digest, big-endian,
from the hash value at `s1` to `s3`, and for SHA-512/224 the high half of
the fourth after three (as the streaming `finalize`s do,
`Impl/Sha512/RISCV64/Stream.lean`): what the iteration needs of it
(`OutOk`, `out_ok`, `out224_ok`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512Out

open VG.RISCV64 VG.RISCV64.ByteLoad
open VG.Impl.Sha512.RISCV64.Stream (outW outHi)
open VG.WriteBytes (writeBytes writeBytes_frame writeBytes_append writeBytes_nil)
open VG.Spec.Sha512 (stateAt wordBytes)
open VG.Proof.Sha512.RISCV64.Stream.Finalize (flat_length take_flatMap_wordBytes beBytes_wordBytes beBytes_word
  take28)

/-- `k` doublewords of the digest are written. -/
structure OutI (s : State) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  keep : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → t.gpr r = s.gpr r
  mem : t.mem = writeBytes s.mem (s.gpr .s3) (((stateAt s.mem (s.gpr .s1)).toList.take k).flatMap wordBytes)

theorem contains_pre (p : Addr) {n len : Nat} (h : n ≤ len) : (⟨p, len⟩ : Region).Contains p n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [h]

section
variable {s : State} {D : Nat} (hD : D ≤ 64) (hin : InRegions (s.rd ++ s.wr) (s.gpr .s1) 64)
  (hout : InRegions s.wr (s.gpr .s3) D) (hd : Region.Disjoint ⟨s.gpr .s1, 64⟩ ⟨s.gpr .s3, D⟩)
include hD hin hout hd

theorem step {k : Nat} (hk : 8 * k + 8 ≤ D) {t : State} (h : OutI s k t) {rest : List Instr}
    {Q : State → Prop} (hnext : ∀ t', OutI s (k + 1) t' → WP isa (.block rest) t' Q) :
    WP isa (.block (outW k ++ rest)) t Q := by
  have hx1 : t.gpr .s1 = s.gpr .s1 := h.keep _ (by decide) (by decide) (by decide)
  have hx3 : t.gpr .s3 = s.gpr .s3 := h.keep _ (by decide) (by decide) (by decide)
  have hP := flat_length (stateAt s.mem (s.gpr .s1)) k (by omega_using [hD, hk])
  simp only [outW, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Words64.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega_using [hD, hk])
    (by rw [hx1, h.rd, h.wr]; exact VG.CallLay.inRegions_sub hin (by omega_using [hD, hk]) (by omega_using []))) fun t₁ u₁ => ?_
  have k3 : t₁.gpr .s3 = s.gpr .s3 := by rw [u₁.other _ (by decide) (by decide) (by decide), hx3]
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega_using [hD, hk])
    fun j hj => ?_) fun t₃ e₃ => hnext t₃ ?_
  · rw [k3, u₁.wr, h.wr]
    exact VG.CallLay.inRegions_sub hout (by omega_using [hk, hj]) (by omega_using [hD])
  subst e₃
  refine ⟨u₁.rd.trans h.rd, u₁.wr.trans h.wr, u₁.sp.trans h.sp, fun r a b c => ?_, ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ b]
    show t₁.gpr r = _
    rw [u₁.other _ a b c]
    exact h.keep r a b c
  · have hread : t.mem.readW (s.gpr .s1 + BitVec.ofNat 64 (8 * k)) 64 =
        (stateAt s.mem (s.gpr .s1))[k]'(by omega_using [hD, hk]) := by
      rw [h.mem, (writeBytes_frame (R := ⟨s.gpr .s3, D⟩) s.mem (s.gpr .s3) _ (contains_pre _ (by omega_using [hk, hP]))).readW
        (r := ⟨s.gpr .s1 + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _) ?_ (by decide)]
      · simp [stateAt]
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (Offset.sub_base _ (by omega_using [hD, hk]))
    rw [RegUpd.mem_write]
    show writeBytes t₁.mem (t₁.gpr .s3 + _) (beBytes 8 (t₁.gpr .t1)) = _
    rw [k3, u₁.gpr, u₁.mem, hx1, hread, beBytes_wordBytes]
    rw [h.mem, ← hP, writeBytes_append _ _ _ _ (by rw [hP]; simp [wordBytes]; omega_using [hD, hk]), List.take_add_one,
      List.getElem?_eq_getElem (by simp; omega_using [hD, hk]), Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, Vector.getElem_toList]

theorem all {n : Nat} (hn : 8 * n ≤ D) {rest : List Instr} {Q : State → Prop}
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

/-- What `OutOk` asks of the code, from `s`, for `D` bytes. -/
abbrev Post (D : Nat) (s s' : State) : Prop :=
  (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
    s'.mem = writeBytes s.mem (s.gpr .s3) ((Proof.Sha512.md.digest (Proof.Sha512.md.stateAt s.mem (s.gpr .s1))).take D)

/-- The first `n` doublewords of the digest. -/
theorem out_ok (n : Nat) (hn : n ≤ 8) : OutOk Proof.Sha512.md (8 * n) ((List.range n).flatMap outW) := by
  intro s hin hout hd
  have := all (s := s) (D := 8 * n) (by omega_using [hn]) hin hout hd (n := n) (Nat.le_refl _) (rest := [])
    (Q := Post (8 * n) s)
    (fun t h => WP.block_nil ⟨h.keep, h.rd, h.wr, h.sp, by
      rw [h.mem]; congr 1
      show _ = ((stateAt s.mem (s.gpr .s1)).toList.flatMap wordBytes).take (8 * n)
      rw [take_flatMap_wordBytes]⟩) n (Nat.le_refl _) s
    ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, by simp [writeBytes_nil]⟩
  rwa [Nat.sub_self, List.drop_zero, List.append_nil] at this

/-- The first three doublewords and the high half of the fourth, 28 bytes. -/
theorem out224_ok : OutOk Proof.Sha512.md 28 ((List.range 3).flatMap outW ++ outHi 3) := by
  intro s hin hout hd
  have := all (s := s) (D := 28) (by omega_using []) hin hout hd (n := 3) (by decide) (rest := outHi 3)
    (Q := Post 28 s) (fun t h => ?_) 3 (Nat.le_refl _) s
    ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, by simp [writeBytes_nil]⟩
  · rwa [Nat.sub_self, List.drop_zero] at this
  have hx1 : t.gpr .s1 = s.gpr .s1 := h.keep _ (by decide) (by decide) (by decide)
  have hx3 : t.gpr .s3 = s.gpr .s3 := h.keep _ (by decide) (by decide) (by decide)
  have hP : (((stateAt s.mem (s.gpr .s1)).toList.take 3).flatMap wordBytes).length = 24 :=
    flat_length (stateAt s.mem (s.gpr .s1)) 3 (by decide)
  rw [← List.append_nil (outHi 3)]
  simp only [outHi, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega_using [])
    (by rw [hx1, h.rd, h.wr]; exact VG.CallLay.inRegions_sub hin (by omega_using []) (by omega_using []))) fun t₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega_using [])
    fun j hj => ?_) fun t₃ e₃ => WP.block_nil ?_
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.wr_write,
      RegUpd.wr_write, hx3, h.wr]
    exact VG.CallLay.inRegions_sub hout (by omega_using [hj]) (by omega_using [])
  subst e₃
  refine ⟨fun r a b c => ?_, h.rd, h.wr, h.sp, ?_⟩
  · simp only [RegUpd.gpr_write, a, b, ite_false]
    exact h.keep r a b c
  · have hread : t.mem.readW (s.gpr .s1 + BitVec.ofNat 64 (8 * 3 + 4)) 32 =
        s.mem.readW (s.gpr .s1 + BitVec.ofNat 64 28) 32 := by
      rw [h.mem, (writeBytes_frame (R := ⟨s.gpr .s3, 28⟩) s.mem (s.gpr .s3) _ (contains_pre _ (by omega_using [hP]))).readW
        (r := ⟨s.gpr .s1 + BitVec.ofNat 64 (8 * 3 + 4), 4⟩) (Region.contains_self _ _) ?_ (by decide)]
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (Offset.sub_base _ (by omega_using []))
    simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, hx1, hx3, hread, beBytes_word]
    rw [h.mem, show (8 * 3 : Nat) = (((stateAt s.mem (s.gpr .s1)).toList.take 3).flatMap wordBytes).length
        from hP.symm,
      writeBytes_append _ _ _ _ (by rw [hP]; simp [Spec.Sha256.wordBytes]), ← take28]
    rfl

end VG.Proof.Pbkdf2.RISCV64.Sha512Out

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha512_224`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha512_224`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-512/224 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-512/224's sizes, compression function and digest code (`it`): what its
proof needs of SHA-512/224 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512_224

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-512/224's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 28
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 3).flatMap Impl.Sha512.RISCV64.Stream.outW ++ Impl.Sha512.RISCV64.Stream.outHi 3
  pad := padBE 128 28 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha512.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-512/224, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha512_224S Proof.Sha512.md Spec.Sha512.H0_512_224 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  out := Sha512Out.out224_ok
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha512_224S Wi).pre (iterK Spec.Hmac.sha512_224S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha512_224

end

end

/-!
# PBKDF2-HMAC-SHA-512/224 on RISC-V: the whole derivation

`pbkdf2` over SHA-512/224's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 400 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha512_224I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha512_224

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha512_224.hash
  hiN := Spec.Hmac.sha512_224I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha512_224I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha512_224_iterate"
  itC := Pbkdf2.RISCV64.Sha512_224.code
  itW := 400

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha512_224.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha512_224.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha512_224.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha512_224.hashOkW 400 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha512_224.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha512_224.ctW 400
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha512.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha512_224I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha512_224.hash, Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha512_224

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha384`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha384`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-384 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-384's sizes, compression function and digest code (`it`): what its
proof needs of SHA-384 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha384

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-384's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 48
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 6).flatMap Impl.Sha512.RISCV64.Stream.outW
  pad := padBE 128 48 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha512.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-384, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha384S Proof.Sha512.md Spec.Sha512.H0_384 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  out := Sha512Out.out_ok 6 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha384S Wi).pre (iterK Spec.Hmac.sha384S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha384

end

end

/-!
# PBKDF2-HMAC-SHA-384 on RISC-V: the whole derivation

`pbkdf2` over SHA-384's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 400 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha384I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha384

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha384.hash
  hiN := Spec.Hmac.sha384I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha384I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha384_iterate"
  itC := Pbkdf2.RISCV64.Sha384.code
  itW := 400

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha384.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha384.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha384.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha384.hashOkW 400 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha384.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha384.ctW 400
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha512.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha384I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha384.hash, Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha384

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha224`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha224`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-224 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-224's sizes, compression function and digest code (`it`): what its
proof needs of SHA-224 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha224

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-224's parameters of the iteration. -/
def it : It where
  N := 32
  B := 64
  D := 28
  CW := 80
  cmpN := "vg_sha256_compress"
  cmpC := Impl.Sha256.RISCV64.compress
  out := (List.range 7).flatMap Impl.Sha256.RISCV64.Stream.outW
  pad := padBE 64 28 8

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha256.md 80 Impl.Sha256.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha256.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha256.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-224, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 239 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha224S Proof.Sha256.md Spec.Sha256.H0_224 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  out := Sha256Out.out_ok 7 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => (Proof.Sha256.sha224_eq m).symm,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha256.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha224S Wi).pre (iterK Spec.Hmac.sha224S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha224

end

end

/-!
# PBKDF2-HMAC-SHA-224 on RISC-V: the whole derivation

`pbkdf2` over SHA-224's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 240 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha224I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha224

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha256Family.hash224
  hiN := Spec.Hmac.sha224I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha224I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha224_iterate"
  itC := Pbkdf2.RISCV64.Sha224.code
  itW := 240

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha256Family.ok224
  hiCt := Proof.Hmac.Stream.RISCV64.Sha224.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha224.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha224.hashOkW 240 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha224.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha224.ctW 240
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha256.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha256.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha224I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha224I, Spec.Hmac.sha224S, Spec.Hmac.sha224, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha256Family.hash224, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha224

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha512`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha512`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-512 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-512's sizes, compression function and digest code (`it`): what its
proof needs of SHA-512 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-512's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 64
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 8).flatMap Impl.Sha512.RISCV64.Stream.outW
  pad := padBE 128 64 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha512.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-512, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha512S Proof.Sha512.md Spec.Sha512.H0_512 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  out := Sha512Out.out_ok 8 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m =>
    (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha512S Wi).pre (iterK Spec.Hmac.sha512S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha512

end

end

/-!
# PBKDF2-HMAC-SHA-512 on RISC-V: the whole derivation

`pbkdf2` over SHA-512's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 400 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha512I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha512

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha512.hash
  hiN := Spec.Hmac.sha512I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha512I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha512_iterate"
  itC := Pbkdf2.RISCV64.Sha512.code
  itW := 400

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha512.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha512.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha512.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha512.hashOkW 400 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha512.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha512.ctW 400
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha512.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha512I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha512.hash, Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha512

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Md5`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Md5`, which only this module used -/

section

/-!
# PBKDF2-HMAC-MD5 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for MD5's sizes, compression function and digest code (`it`): what its
proof needs of MD5 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Md5

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padLE)

/-- MD5's parameters of the iteration. -/
def it : It where
  N := 16
  B := 64
  D := 16
  CW := 80
  cmpN := "vg_md5_compress"
  cmpC := Impl.Md5.RISCV64.compress
  out := Impl.Md5.RISCV64.Stream.params.out
  pad := padLE 64 16 8

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Md5.md 80 Impl.Md5.RISCV64.compress :=
  ⟨Proof.Md5.RISCV64.Stream.callee.verified, Proof.Md5.RISCV64.Stream.callee.noFrames⟩

/-- What the proof needs of MD5, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 223 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.md5S Proof.Md5.md Spec.Md5.H0 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega_using [hj])
  out := fun s h₁ h₂ h₃ => (Proof.Md5.RISCV64.Stream.shape.out s h₁ h₂ h₃).mono fun _ ⟨g, a, b, c, d⟩ =>
    ⟨fun r x y _ => g r x y, a, b, c, d⟩
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Md5.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.md5S Wi).pre (iterK Spec.Hmac.md5S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Md5

end

end

/-!
# PBKDF2-HMAC-MD5 on RISC-V: the whole derivation

`pbkdf2` over MD5's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 224 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.md5I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Md5

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Md5.hash
  hiN := Spec.Hmac.md5I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.md5I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_md5_iterate"
  itC := Pbkdf2.RISCV64.Md5.code
  itW := 224

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Md5.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Md5.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Md5.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Md5.hashOkW 224 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Md5.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Md5.ctW 224
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Md5.RISCV64.Stream.callee.noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Md5.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.md5I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Md5.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Md5

end

end

/-! ### `Pbkdf2.Whole.RISCV64.Sha512_256`, which only this module used -/

section

/-! ### `Pbkdf2.RISCV64.Sha512_256`, which only this module used -/

section

/-!
# PBKDF2-HMAC-SHA-512/256 on RISC-V: `iterate`

The iteration over a Merkle–Damgård hash function (`Impl/Pbkdf2/RISCV64.lean`)
for SHA-512/256's sizes, compression function and digest code (`it`): what its
proof needs of SHA-512/256 (`hashOk`), its constant time, which the kernel
checks.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.RISCV64.Sha512_256

open VG.RISCV64
open VG.Impl.Pbkdf2.RISCV64 (It padBE)

/-- SHA-512/256's parameters of the iteration. -/
def it : It where
  N := 64
  B := 128
  D := 32
  CW := 144
  cmpN := "vg_sha512_compress"
  cmpC := Impl.Sha512.RISCV64.compress
  out := (List.range 4).flatMap Impl.Sha512.RISCV64.Stream.outW
  pad := padBE 128 32 16

/-- `iterate`'s code. -/
abbrev code : Prog isa := it.iterate

theorem callee : CalleeOk Proof.Sha512.md 144 Impl.Sha512.RISCV64.compress :=
  ⟨fun s ⟨h₁, h₂, h₃, h₄, h₅, _⟩ => Proof.Sha512.RISCV64.compress_verified.1 s ⟨h₁, h₂, h₃, h₄, h₅⟩,
    Proof.Sha512.RISCV64.Stream.compress_noFrames⟩

/-- What the proof needs of SHA-512/256, with `Wi` bytes of working space. -/
theorem hashOkW (Wi : Nat) (h₁ : 399 ≤ Wi) (h₂ : Wi ≤ 8192) :
    HashOk it Wi Spec.Hmac.sha512_256S Proof.Sha512.md Spec.Sha512.H0_512_256 where
  sizes := ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by simp only [it]; omega_using [h₁], h₂⟩
  pad := by decide
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega_using [hj])
  out := Sha512Out.out_ok 4 (by decide)
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun _ => rfl,
    by decide, by decide⟩

/-- The taint analysis of `main`, which the kernel checks. -/
theorem main_ck : ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) it.main hc).isSome = true := by
  taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]

/-- `iterate`'s constant time, with any working space. -/
theorem ctW (Wi : Nat) : ConstantTime isa (iterK Spec.Hmac.sha512_256S Wi).pre (iterK Spec.Hmac.sha512_256S Wi).pub code :=
  main_ck.elim fun _ h => ct _ _ _ h

end VG.Proof.Pbkdf2.RISCV64.Sha512_256

end

end

/-!
# PBKDF2-HMAC-SHA-512/256 on RISC-V: the whole derivation

`pbkdf2` over SHA-512/256's streaming functions, HMAC's `init` and `finalize` and
PBKDF2's `iterate` (`F`, with 400 bytes of working space for `iterate`);
the taint checks of its pieces, which the kernel evaluates; and `pbkdf2`
against the shared contract of `Spec.Hmac.sha512_256I`.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Sha512_256

open VG.RISCV64

/-- The functions `pbkdf2` calls. -/
def F : Impl.Pbkdf2.Whole.RISCV64.Fns where
  H := Proof.Hmac.Stream.RISCV64.Sha512_256.hash
  hiN := Spec.Hmac.sha512_256I.initAnyKeyApi.name ++ "_core"
  hfN := Spec.Hmac.sha512_256I.finalizeApi.name ++ "_core"
  itN := "vg_pbkdf2_hmac_sha512_256_iterate"
  itC := Pbkdf2.RISCV64.Sha512_256.code
  itW := 400

/-- What the proofs need of them. -/
def okF : FnsOK F where
  hH := Proof.Hmac.Stream.RISCV64.Sha512_256.ok
  hiCt := Proof.Hmac.Stream.RISCV64.Sha512_256.init_ct
  hfCt := Proof.Hmac.Stream.RISCV64.Sha512_256.fin_ct
  itOk s hs := by
    have ho := Pbkdf2.RISCV64.Sha512_256.hashOkW 400 (by decide) (by decide)
    obtain ⟨t, s', he, h₁, h₂⟩ := Pbkdf2.RISCV64.correct ho Pbkdf2.RISCV64.Sha512_256.callee
      (Pbkdf2.RISCV64.pre_of ho.link.hS ho.link.hD hs)
    exact ⟨t, s', he, h₁, h₂⟩
  itCt := Pbkdf2.RISCV64.Sha512_256.ctW 400
  itNf := Pbkdf2.RISCV64.iterate_noFrames _ Proof.Sha512.RISCV64.Stream.compress_noFrames
  itW0 := by decide
  itB := by decide
  frB := by decide

theorem checks : Checks F := by
  constructor
  case upd => unfold Ck; taint_decide_sum [VG.Proof.Sha512.RISCV64.compressSum]
  all_goals refine ⟨?_, ?_⟩
  taint_decide_all

theorem pbkdf2 : Verified RISCV64.target F.pbkdf2 (Spec.Hmac.sha512_256I.pbkdf2Contract RISCV64.abi (F.itB + F.frB + F.X)) :=
  shared okF checks rfl (by
    inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
      Spec.Pbkdf2.pbkdf2Pre, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, Impl.Pbkdf2.Whole.RISCV64.Fns.itB,
      Impl.Pbkdf2.Whole.RISCV64.Fns.frB, Impl.Pbkdf2.Whole.RISCV64.Fns.X, Impl.Pbkdf2.Whole.RISCV64.Fns.bytes,
      Impl.Pbkdf2.Whole.RISCV64.Fns.intO, Impl.Pbkdf2.Whole.RISCV64.Fns.tO, Impl.Pbkdf2.Whole.RISCV64.Fns.uO,
      Impl.Pbkdf2.Whole.RISCV64.Fns.stWO, Impl.Pbkdf2.Whole.RISCV64.Fns.st1O, Impl.Pbkdf2.Whole.RISCV64.Fns.st0O,
      F, Proof.Hmac.Stream.RISCV64.Sha512_256.hash, Proof.Hmac.Stream.RISCV64.Sha512Family.hash, Impl.Hmac.Stream.RISCV64.Hash.ibytes, Impl.Hmac.Stream.RISCV64.Hash.fbytes,
      Impl.Hmac.Stream.RISCV64.Hash.iso, Impl.Hmac.Stream.RISCV64.Hash.fso, RISCV64.abi, RISCV64.argRegs]
      using pbkSat)

end VG.Proof.Pbkdf2.Whole.RISCV64.Sha512_256

end

end

/-!
# PBKDF2 on RISC-V, without secret residue

Each hash's PBKDF2 as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`),
followed by `Impl.Scrub.RISCV64.scrubTail`, which clears the caller-saved
registers and the stack its frames used. Each theorem below states that one
meets its contract in constant time and returns without secret residue
(`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbedAll`), which is what its
registration binds. Its postcondition reads the memory on return only within
`out`, as on x86-64 (`Proof/Pbkdf2/Md/X86_64/ScrubAll.lean`).
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Whole.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub

/-- PBKDF2's postcondition reads the memory on return only within `out`, the
derived key's bytes. -/
theorem pbkdf2Out (I : Spec.Hmac.Instance) (stack : Nat) :
    PostOut (I.pbkdf2Contract abi stack) (Spec.Pbkdf2.pbkdf2Sig.retBits 64) := by
  unfold Spec.Hmac.Instance.pbkdf2Contract Spec.Pbkdf2.pbkdf2Contract
  exact postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    obtain ⟨pw, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 6) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pwLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨salt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨saltLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨c, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨outLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
    simp only [Spec.Pbkdf2.pbkdf2Sig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    have ho : ∀ i < outLen.toNat, m₂ (out + BitVec.ofNat 64 i) = m₁ (out + BitVec.ofNat 64 i) :=
      fun i hi => (hb.2.2 _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))).symm
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.int 32,
      ArgWord.addr, ArgWord.int 64] (Spec.Pbkdf2.pbkdf2Post I.S 64) _ m m₂ r
    dsimp only [Curry.apply, Spec.Pbkdf2.pbkdf2Post, ArgWord.ofRaw] at h ⊢
    rw [Sha256.Stream.bytesAt_congr fun i hi => ho i (by
      rw [BitVec.toNat_setWidth] at hi; have := Nat.mod_le outLen.toNat (2 ^ 64); omega_using [hi])]
    exact h

/-- `vg_pbkdf2_hmac_md5` as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`) meets its
contract in constant time and returns without secret residue. -/
theorem md5_scrubbed :
    VerifiedScrubbed target (Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Md5.F)
      (Spec.Hmac.md5I.pbkdf2Contract RISCV64.abi (Md5.F.itB + Md5.F.frB + Md5.F.X)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.md5I.pbkdf2Api)
    (W := Md5.F.itB + Md5.F.frB + Md5.F.X)
    { code := Md5.F.pbkdf2, verified := Md5.pbkdf2 } (pbkdf2Out Spec.Hmac.md5I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha1` as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`) meets its
contract in constant time and returns without secret residue. -/
theorem sha1_scrubbed :
    VerifiedScrubbed target (Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Sha1.F)
      (Spec.Hmac.sha1I.pbkdf2Contract RISCV64.abi (Sha1.F.itB + Sha1.F.frB + Sha1.F.X)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha1I.pbkdf2Api)
    (W := Sha1.F.itB + Sha1.F.frB + Sha1.F.X)
    { code := Sha1.F.pbkdf2, verified := Sha1.pbkdf2 } (pbkdf2Out Spec.Hmac.sha1I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha224` as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`) meets its
contract in constant time and returns without secret residue. -/
theorem sha224_scrubbed :
    VerifiedScrubbed target (Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Sha224.F)
      (Spec.Hmac.sha224I.pbkdf2Contract RISCV64.abi (Sha224.F.itB + Sha224.F.frB + Sha224.F.X)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha224I.pbkdf2Api)
    (W := Sha224.F.itB + Sha224.F.frB + Sha224.F.X)
    { code := Sha224.F.pbkdf2, verified := Sha224.pbkdf2 } (pbkdf2Out Spec.Hmac.sha224I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha256` as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`) meets its
contract in constant time and returns without secret residue. -/
theorem sha256_scrubbed :
    VerifiedScrubbed target (Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Sha256.F)
      (Spec.Hmac.sha256I.pbkdf2Contract RISCV64.abi (Sha256.F.itB + Sha256.F.frB + Sha256.F.X)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha256I.pbkdf2Api)
    (W := Sha256.F.itB + Sha256.F.frB + Sha256.F.X)
    { code := Sha256.F.pbkdf2, verified := Sha256.pbkdf2 } (pbkdf2Out Spec.Hmac.sha256I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha384` as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`) meets its
contract in constant time and returns without secret residue. -/
theorem sha384_scrubbed :
    VerifiedScrubbed target (Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Sha384.F)
      (Spec.Hmac.sha384I.pbkdf2Contract RISCV64.abi (Sha384.F.itB + Sha384.F.frB + Sha384.F.X)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha384I.pbkdf2Api)
    (W := Sha384.F.itB + Sha384.F.frB + Sha384.F.X)
    { code := Sha384.F.pbkdf2, verified := Sha384.pbkdf2 } (pbkdf2Out Spec.Hmac.sha384I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha512` as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_scrubbed :
    VerifiedScrubbed target (Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Sha512.F)
      (Spec.Hmac.sha512I.pbkdf2Contract RISCV64.abi (Sha512.F.itB + Sha512.F.frB + Sha512.F.X)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512I.pbkdf2Api)
    (W := Sha512.F.itB + Sha512.F.frB + Sha512.F.X)
    { code := Sha512.F.pbkdf2, verified := Sha512.pbkdf2 } (pbkdf2Out Spec.Hmac.sha512I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha512_224` as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_224_scrubbed :
    VerifiedScrubbed target (Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Sha512_224.F)
      (Spec.Hmac.sha512_224I.pbkdf2Contract RISCV64.abi (Sha512_224.F.itB + Sha512_224.F.frB + Sha512_224.F.X)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_224I.pbkdf2Api)
    (W := Sha512_224.F.itB + Sha512_224.F.frB + Sha512_224.F.X)
    { code := Sha512_224.F.pbkdf2, verified := Sha512_224.pbkdf2 } (pbkdf2Out Spec.Hmac.sha512_224I _)
    (by dsimp only; lit_decide)

/-- `vg_pbkdf2_hmac_sha512_256` as emitted (`Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2`) meets its
contract in constant time and returns without secret residue. -/
theorem sha512_256_scrubbed :
    VerifiedScrubbed target (Impl.Pbkdf2.Whole.RISCV64.Fn.pbkdf2 Sha512_256.F)
      (Spec.Hmac.sha512_256I.pbkdf2Contract RISCV64.abi (Sha512_256.F.itB + Sha512_256.F.frB + Sha512_256.F.X)) 0 :=
  verifiedScrubbedAll (api := Spec.Hmac.sha512_256I.pbkdf2Api)
    (W := Sha512_256.F.itB + Sha512_256.F.frB + Sha512_256.F.X)
    { code := Sha512_256.F.pbkdf2, verified := Sha512_256.pbkdf2 } (pbkdf2Out Spec.Hmac.sha512_256I _)
    (by dsimp only; lit_decide)

end VG.Proof.Pbkdf2.Whole.RISCV64.Scrub
