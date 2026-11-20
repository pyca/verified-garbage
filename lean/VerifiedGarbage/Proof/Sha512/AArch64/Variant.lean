module

public import VerifiedGarbage.Proof.Framework.AArch64.ScrubSide
public import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Md
public import VerifiedGarbage.Proof.Sha512.AArch64.Compress
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Proof.Framework.AArch64.Syms
public import VerifiedGarbage.Impl.Sha512.AArch64.Stream
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Sha512.AArch64.Stream.InitPairs`, which only this module used -/

section

/-!
# Streaming SHA-512 on AArch64: `initPairs`

The initial hash value stored by pairs of doublewords, for the one-shot
digests: the same postcondition as `init`'s.
-/

@[expose] public section

namespace VG.Proof.Sha512.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha512.AArch64.Stream
open VG.Impl.Sha512.AArch64 (movImm64)
open VG.Proof.Sha512.AArch64 (writeState stateAt_writeState contains_offset)
open VG.Spec.Sha512 (HashValue stateAt)

/-- The nine instructions storing the 64-bit words `x` and `y` at `[x0 + off]`. -/
def pair (x y : BitVec 64) (off : Nat) : List Instr :=
  movImm64 .x9 x ++ movImm64 .x10 y ++ ([.stp .x9 .x10 .x0 off] : List Instr)

theorem initPairs_eq (iv : HashValue) : initPairs iv = .block (pair iv[0] iv[1] 0 ++ pair iv[2] iv[3] 16 ++
    pair iv[4] iv[5] 32 ++ pair iv[6] iv[7] 48) := rfl

theorem pair_ok {x y : BitVec 64} {off : Nat} (ho : off % 8 = 0 ∧ off ≤ 504) {rest : List Instr}
    {s : State} {Q : State → Prop} (hout : ∀ j ≤ 8, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (off + j)) 8)
    (k : ∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = (s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 off) x).writeW
        (s.gpr .x0 + BitVec.ofNat 64 (off + 8)) y → WP isa (.block rest) s' Q) :
    WP isa (.block (pair x y off ++ rest)) s Q := by
  simp only [pair, movImm64, List.cons_append, List.nil_append]
  refine MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl
    (MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl
    (MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl ?_)))))))
  refine MdStream.AArch64.OneShot.wp_stpB ho (b := s.gpr .x0) (by simp [State.write])
    (by simpa [State.write] using hout 0 (by omega_using [])) (by simpa [State.write] using hout 8 (by omega_using []))
    fun s' m => k s' (fun r h9 h10 => by rw [m.gpr]; simp [State.write, h9, h10]) (by rw [m.rd]; rfl)
      (by rw [m.wr]; rfl) (by rw [m.sp]; rfl) ?_
  rw [m.mem]
  simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
  simp only [show Reg.x9 ≠ Reg.x10 by decide, ite_false]
  rw [movz_movk64' x, movz_movk64' y]

theorem initPairs_correct {s₀ : State} (iv : HashValue) (hp : (Proof.Sha512.initAArch64 iv).pre s₀) :
    WP isa (initPairs iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha512.initAArch64 iv).post s₀ s' := by
  apply WP.withPreservedV (hc := by rfl)
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ j, j + 8 ≤ 64 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 j) 8 :=
    fun j hj => ⟨⟨s₀.gpr .x0, 192⟩, by simp [hwr], contains_offset (by omega_using [hj]) (by omega_using [hj])⟩
  rw [initPairs_eq, ← List.append_nil (_ ++ pair iv[6] iv[7] 48)]
  simp only [List.append_assoc]
  refine pair_ok (by decide) (fun j hj => o _ (by omega_using [hj])) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr .x0 = s₀.gpr .x0 := g1 _ (by decide) (by decide)
  refine pair_ok (by decide) (fun j hj => by rw [wr1, k1]; exact o _ (by omega_using [hj])) fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr .x0 = s₀.gpr .x0 := by rw [g2 _ (by decide) (by decide), k1]
  refine pair_ok (by decide) (fun j hj => by rw [wr2, wr1, k2]; exact o _ (by omega_using [hj]))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr .x0 = s₀.gpr .x0 := by rw [g3 _ (by decide) (by decide), k2]
  refine pair_ok (by decide) (fun j hj => by rw [wr3, wr2, wr1, k3]; exact o _ (by omega_using [hj]))
    fun s4 g4 _ _ sp4 m4 => WP.block_nil ?_
  have k4 : ∀ r, r ≠ .x9 → r ≠ .x10 → s4.gpr r = s₀.gpr r := fun r h9 h10 => by
    rw [g4 r h9 h10, g3 r h9 h10, g2 r h9 h10, g1 r h9 h10]
  have hm : s4.mem = writeState s₀.mem (s₀.gpr .x0) iv := by
    rw [m4, m3, m2, m1, k3, k2, k1]
    rfl
  refine ⟨⟨fun r hr => k4 r ?_ ?_, by rw [sp4, sp3, sp2, sp1]⟩, ?_⟩
  · rintro rfl; simp [preserved] at hr
  · rintro rfl; simp [preserved] at hr
  · show Spec.Sha512.Repr iv s4.mem (s₀.gpr .x0) []
    rw [hm]
    exact Proof.Sha512.Stream.repr_nil (stateAt_writeState _ _ _)

theorem initPairs_ok (iv : HashValue) :
    ∀ s, (Proof.Sha512.initAArch64 iv).pre s → ∃ t s', Exec isa (initPairs iv) s t s' ∧
      abiPreserved s s' ∧ (Proof.Sha512.initAArch64 iv).post s s' := fun s h => by
  obtain ⟨t, s', he, h⟩ := initPairs_correct iv h
  exact ⟨t, s', he, h⟩

theorem initPairs_writes (iv : HashValue) :
    ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs (initPairs iv), clobbers i r = false := by
  intro r h9 h10 i hi
  simp only [initPairs, instrs, List.mem_flatMap, List.mem_range, movImm64, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨k, -, hi⟩ := hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [clobbers, dstOf, Ne.symm h9, Ne.symm h10]

theorem initPairs_keepsV (iv : HashValue) :
    (initPairs iv).allInstrs VG.AArch64.keepsV = true := by
  rw [Code.allInstrs_eq]
  simp [initPairs, instrs, movImm64, VG.AArch64.keepsV, vdstOf]

end VG.Proof.Sha512.AArch64.Stream

end

end


/-!
# SHA-512 compression backends on AArch64

Each backend supplies its verified compression code and the mechanically
checked constant-time, register and frame facts for the generic streaming
wrappers. The functional streaming proofs are shared by every backend.
HMAC, PBKDF2 and Ed25519 consume the resulting streaming functions.
-/

@[expose] public section

namespace VG.Proof.Sha512.AArch64

open VG.AArch64 VG.Proof.MdStream.AArch64
open VG.Impl.MdStream.AArch64
open VG.Impl.Sha512.AArch64.Stream (compressName updateWith finalizeWith finalizeDigestWith params384 params512_256
  params512_224)

/-- What a backend's `finalizeDigestWith` with the digest code `o` (SHA-384's,
SHA-512/256's or SHA-512/224's `finalize`, writing a `D`-byte digest) needs
checked for its code, as `finalizeCT` and `finalizeDepth` for `finalize`. -/
structure DigestOk (o : List Instr) (D : Nat) (suffix : String) (code : Prog isa) : Prop where
  ct : ConstantTime isa (finKD (P := { Stream.params with out := o }) md D).pre
    (finKD (P := { Stream.params with out := o }) md D).pub
    (finalizeDigestWith { Stream.params with out := o } suffix code)
  depth : (finalizeMain { Stream.params with out := o } (compressName suffix) code).aarch64Depth = 0

/-- The one-shot digest with the digest code `o`, from the initial hash value
`iv`, calling the compression function `code` with the suffix `suffix`. -/
def oneShotWith (o : List Instr) (iv : Spec.Sha512.HashValue) (suffix : String) (code : Prog isa) :
    Prog isa :=
  Impl.MdStream.AArch64.OneShot.digest { Stream.params with out := o }
    (Impl.Sha512.AArch64.Stream.initPairs iv) (compressName suffix) code

/-- The one-shot digest is constant time. -/
abbrev OneShotCT (o : List Instr) (D : Nat) (iv : Spec.Sha512.HashValue) (suffix : String)
    (code : Prog isa) : Prop :=
  ConstantTime isa (MdStream.AArch64.OneShot.oneK (P := { Stream.params with out := o }) md iv D).pre
    (MdStream.AArch64.OneShot.oneK (P := { Stream.params with out := o }) md iv D).pub
    (oneShotWith o iv suffix code)

structure Compress where
  code : Prog isa
  verified : Verified AArch64.target code Proof.Sha512.compressAArch64
  noFrames : code.noFrames = true
  /-- Current streaming wrappers require untouched callee-saved SIMD registers. -/
  keepsV : code.allInstrs keepsV = true
  /-- It never writes PSTATE.DIT, so its callers' runs keep it (`DitDet.of_noWrite`). -/
  noDit : code.all (fun i => !i.writesDit) = true
  /-- No instruction of it writes PSTATE.DIT, and it calls nothing indirectly:
  what the cleanup of the functions that call it needs of its code
  (`ScrubAll.verifiedScrubbedOf`). -/
  side : ScrubAll.sideAll (fun i => !i.writesDit) code = true
  suffix : String
  features : List String
  updateCT : ConstantTime isa (updK (P := Stream.params) md).pre
    (updK (P := Stream.params) md).pub (updateWith suffix code)
  finalizeCT : ConstantTime isa (finK (P := Stream.params) md).pre
    (finK (P := Stream.params) md).pub (finalizeWith suffix code)
  updateDepth : (updateMain Stream.params (compressName suffix) code).aarch64Depth = 0
  finalizeDepth : (finalizeMain Stream.params (compressName suffix) code).aarch64Depth = 0
  /-- SHA-384's, SHA-512/256's and SHA-512/224's `finalize`. -/
  digest384 : DigestOk (out64 6) 48 suffix code
  digest512_256 : DigestOk (out64 4) 32 suffix code
  digest512_224 : DigestOk (out64 3 ++ Impl.Sha512.AArch64.Stream.outHi 3) 28 suffix code
  /-- The one-shot digests of SHA-512, SHA-384, SHA-512/256 and SHA-512/224. -/
  oneShot512 : OneShotCT (out64 8) 64 Spec.Sha512.H0_512 suffix code
  oneShot384 : OneShotCT (out64 6) 48 Spec.Sha512.H0_384 suffix code
  oneShot512_256 : OneShotCT (out64 4) 32 Spec.Sha512.H0_512_256 suffix code
  oneShot512_224 : OneShotCT (out64 3 ++ Impl.Sha512.AArch64.Stream.outHi 3) 28 Spec.Sha512.H0_512_224
    suffix code
  /-- The registers `code` writes, of those the calling convention does not
  preserve: what the cleanup of a function that calls it clears for it
  (`ScrubAll.scrubSide_union`). -/
  clear : Impl.Residue.AArch64.Clear
  scrub : AArch64.ScrubAll.calleeSide code clear = true

/-- The implementation, as the code of a function that hashes takes it. -/
def Compress.impl (v : Compress) : Impl.Sha512.AArch64.Stream.Compress := ⟨v.code, v.suffix, v.clear⟩

/-! ## The one-shot digests' common facts -/

namespace OneShot

open MdStream.AArch64.OneShot (oneK initK Fits)

theorem frameBytes_out (o : List Instr) :
    Impl.MdStream.AArch64.OneShot.frameBytes { Stream.params with out := o } =
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params := rfl

theorem fits (o : List Instr) : Fits { Stream.params with out := o } := ⟨by rw [frameBytes_out]; decide⟩

theorem init_ok (iv : Spec.Sha512.HashValue) :
    ∀ s, (initK (P := Stream.params) md iv).pre s → ∃ t s',
      Exec isa (Impl.Sha512.AArch64.Stream.initPairs iv) s t s' ∧
      abiPreserved s s' ∧ (initK (P := Stream.params) md iv).post s s' :=
  VG.Proof.Sha512.AArch64.Stream.initPairs_ok iv

theorem init_writes (iv : Spec.Sha512.HashValue) :
    ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs (Impl.Sha512.AArch64.Stream.initPairs iv), clobbers i r = false :=
  VG.Proof.Sha512.AArch64.Stream.initPairs_writes iv

theorem init_keepsV (iv : Spec.Sha512.HashValue) :
    (Impl.Sha512.AArch64.Stream.initPairs iv).allInstrs VG.AArch64.keepsV = true :=
  VG.Proof.Sha512.AArch64.Stream.initPairs_keepsV iv

/-- A state satisfying the precondition: an empty message at `0x1000`, the
digest at `0x2000` and the stack pointer at `0x10000`. -/
def sat (D : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, D⟩]

theorem sat_pre₀ {D : Nat} (hD : D ≤ 64) : MdStream.AArch64.OneShot.Pre Stream.params D (sat D) where
  rd := rfl
  wr := rfl
  d_o := show Region.Disjoint ⟨0x1000, 0⟩ ⟨0x2000, D⟩ from
    Offset.disjoint_of_le (show 4096 + 0 ≤ 8192 by decide) (show 8192 + D ≤ 2 ^ 64 by omega_using [hD])
  sp := show Impl.MdStream.AArch64.OneShot.frameBytes Stream.params ≤ (0x10000 : BitVec 64).toNat by decide
  f_d := show Region.Disjoint ⟨0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params),
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params⟩ ⟨0x1000, 0⟩ from
    (Offset.disjoint_of_le (by decide) (by decide)).symm
  f_o := show Region.Disjoint ⟨0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params),
      Impl.MdStream.AArch64.OneShot.frameBytes Stream.params⟩ ⟨0x2000, D⟩ from
    (Offset.disjoint_of_le (show 8192 + D ≤ _ by
      have : 8256 ≤ (0x10000 - BitVec.ofNat 64 (Impl.MdStream.AArch64.OneShot.frameBytes Stream.params) :
        BitVec 64).toNat := by decide
      dsimp only; omega_using [hD, this]) (by decide)).symm

/-- The precondition does not depend on the digest code. -/
theorem pre_out {o : List Instr} {D : Nat} {s : State} (h : MdStream.AArch64.OneShot.Pre Stream.params D s) :
    MdStream.AArch64.OneShot.Pre { Stream.params with out := o } D s := by
  have e := frameBytes_out o
  exact ⟨h.rd, h.wr, h.d_o, by rw [e]; exact h.sp,
    by simpa only [MdStream.AArch64.OneShot.fR, MdStream.AArch64.OneShot.fb, e] using h.f_d,
    by simpa only [MdStream.AArch64.OneShot.fR, MdStream.AArch64.OneShot.fb, e] using h.f_o⟩

theorem sat_pre {o : List Instr} {D : Nat} (hD : D ≤ 64) :
    MdStream.AArch64.OneShot.Pre { Stream.params with out := o } D (sat D) := pre_out (sat_pre₀ hD)

end OneShot

namespace Compress

variable (v : Compress)

/-- The symbol of the compression function. -/
def name : String := compressName v.suffix

def update : Prog isa := updateWith v.suffix v.code
def finalize : Prog isa := finalizeWith v.suffix v.code

theorem callee : CalleeOk (P := Stream.params) md v.code := ⟨v.verified.1, v.noFrames, v.keepsV⟩

theorem update_verified : Verified AArch64.target v.update Proof.Sha512.updateAArch64 := by
  have h := MdStream.AArch64.Update.verified Stream.dims v.callee v.updateCT
    (by rw [v.updateDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr hc,
    fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified : Verified AArch64.target v.finalize Proof.Sha512.finalizeAArch64 := by
  have h := MdStream.AArch64.Finalize.verified Stream.dims Stream.shape v.callee v.finalizeCT
    (by rw [v.finalizeDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h iv m hr hl hc => h iv m hr hl hc,
    fun _ _ _ _ h => h, h.2.2⟩

/-- `finalizeDigestWith` writing a `D`-byte digest, with the digest code `o`. -/
theorem finalizeDigest_verified {o : List Instr} {D : Nat}
    (hs : ShapeD (P := { Stream.params with out := o }) md D)
    (dk : DigestOk o D v.suffix v.code) :
    Verified AArch64.target (finalizeDigestWith { Stream.params with out := o } v.suffix v.code)
      (finKD (P := { Stream.params with out := o }) md D) :=
  MdStream.AArch64.Finalize.verifiedD (P := { Stream.params with out := o })
    ⟨Stream.dims.1, Stream.dims.2, Stream.dims.3, Stream.dims.4⟩ hs
    (v.callee.withOut o) dk.ct (by rw [dk.depth]; decide)

theorem update_keepsV : v.update.allInstrs VG.AArch64.keepsV = true := MdStream.AArch64.update_keepsV v.keepsV

theorem finalize_keepsV : v.finalize.allInstrs VG.AArch64.keepsV = true :=
  MdStream.AArch64.finalize_keepsV Stream.shape v.keepsV

theorem update_depth : v.update.aarch64Depth = 1 := by
  simp only [update, updateWith, Impl.MdStream.AArch64.update, Code.aarch64Depth, v.updateDepth]
  rfl

theorem finalize_depth : v.finalize.aarch64Depth = 1 := by
  simp only [finalize, finalizeWith, Impl.MdStream.AArch64.finalize, Code.aarch64Depth, v.finalizeDepth]
  rfl

/-- The one-shot digest with the digest code `o` (writing `D` bytes), from `iv`. -/
theorem oneShot_verified {o : List Instr} {D : Nat} {iv : Spec.Sha512.HashValue} (hD : D ≤ 64)
    (hs : ShapeD (P := { Stream.params with out := o }) md D)
    (hct : OneShotCT o D iv v.suffix v.code) :
    Verified AArch64.target (oneShotWith o iv v.suffix v.code)
      (MdStream.AArch64.OneShot.oneK (P := { Stream.params with out := o }) md iv D) :=
  MdStream.AArch64.OneShot.verified (P := { Stream.params with out := o }) (OneShot.fits o)
    ⟨Stream.dims.1, Stream.dims.2, Stream.dims.3, Stream.dims.4⟩ hs
    (v.callee.withOut o) (OneShot.init_ok iv) (OneShot.init_writes iv) rfl (OneShot.init_keepsV iv) hct
    ⟨_, OneShot.sat_pre hD⟩

end Compress
end VG.Proof.Sha512.AArch64
