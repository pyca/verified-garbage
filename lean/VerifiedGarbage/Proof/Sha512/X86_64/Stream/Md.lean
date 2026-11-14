module

public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
public import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Verified
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
public import VerifiedGarbage.Impl.Sha512.X86_64.Stream
public import VerifiedGarbage.Proof.Sha512.X86_64.Compress
public import VerifiedGarbage.Proof.Sha512.X86_64.Wide
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Verified
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Verified
meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
meta import VerifiedGarbage.Impl.Sha512.X86_64.Stream
meta import VerifiedGarbage.Proof.Sha512.X86_64.Compress
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Verified
meta import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
meta import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Sha256.Stream

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

/-- The length field: `count >> 61`, then `8 count`, big-endian. -/
theorem len_ok (s : State) (hout : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 176) 16) :
    WP isa (.block params.len) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 176) (md.lenOf (s.gpr .r12)) := by
  have h176 : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 176) 8 := by
    obtain ⟨R, hR, hc⟩ := hout
    exact ⟨R, hR, by unfold Region.Contains at *; omega_using [hc]⟩
  have e184 : s.gpr .rbx + BitVec.ofNat 64 176 + BitVec.ofNat 64 8 = s.gpr .rbx + BitVec.ofNat 64 184 := by
    rw [BitVec.add_assoc]; rfl
  have h184 : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 184) 8 := by
    rw [← e184]; exact InRegions.offset hout (by omega_using []) (by omega_using [])
  show WP isa (.block (.mov .rax (.reg .r12) :: .shift .shr .rax 61 :: .bswap .rax ::
    .store (at_ .rbx 176) .rax :: (len64 184 true ++ []))) s _
  refine wp_mov fun s₁ u₁ _ _ => wp_shri (by decide) fun s₂ u₂ => wp_bswap fun s₃ u₃ =>
    wp_store (a := s.gpr .rbx + BitVec.ofNat 64 176)
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ofInt_natCast])
      (by rw [u₃.wr, u₂.wr, u₁.wr]; exact h176) fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  have k₄ : ∀ r, r ≠ .rax → s₄.gpr r = s.gpr r := fun r h => by
    rw [g₄, u₃.other r h, u₂.other r h, u₁.other r h]
  have e₄ : s₄.mem = writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 176) (bytes64 true (s.gpr .r12 >>> 61)) := by
    rw [m₄, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, ← writeW64 _ _ true]; rfl
  refine len64_ok (by rw [wr₄, u₃.wr, u₂.wr, u₁.wr, k₄ _ (by decide)]; exact h184)
    fun s' g rd wr m => WP.block_nil ⟨fun r h => by rw [g r h, k₄ r h], by rw [rd, rd₄, u₃.rd, u₂.rd, u₁.rd],
      by rw [wr, wr₄, u₃.wr, u₂.wr, u₁.wr], ?_⟩
  have e' : s.gpr .rbx + BitVec.ofNat 64 176 + BitVec.ofNat 64 (bytes64 true (s.gpr .r12 >>> 61)).length =
      s.gpr .rbx + BitVec.ofNat 64 184 := by rw [bytes64_length]; exact e184
  rw [m, e₄, k₄ _ (by decide), k₄ _ (by decide), ← e',
    writeBytes_append _ _ _ _ (by rw [bytes64_length, bytes64_length]; decide), lenOf_split]

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

/-- `params` with `so` bytes of working space for the compression function
(`Impl.Pbkdf2.Md.X86_64.Hash.withWs`), for the implementations that use
less than AVX2's: the functions made with it give the compression function
only that much. -/
abbrev paramsS (so : Nat) : Impl.MdStream.X86_64.Params := { params with so := so }

theorem taintsS (so : Nat) (h : so = 0 ∨ so = 192) : Taints (paramsS so) := by
  rcases h with rfl | rfl <;>
  exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, by decide, by decide⟩

/-- `taintsS`, for each implementation's scratch space, AVX2's too. -/
theorem taintsS3 (so : Nat) (h : so = 0 ∨ so = 192 ∨ so = 1328) : Taints (paramsS so) := by
  rcases h with h | h | rfl
  · exact taintsS so (.inl h)
  · exact taintsS so (.inr h)
  · exact taints

/-- An implementation verified with `so` bytes of scratch space, as the code
made with `paramsS so` calls it. -/
theorem calleeS {code : Prog isa} (hf : CalleeOk (P := params) md code) {so : Nat}
    (hv : Verified X86_64.target code (Proof.Sha512.compressWideX86_64S so)) :
    CalleeOk (P := paramsS so) md code :=
  ⟨hv.1, hv.2.1, hf.nosp, hf.depth, hf.keeps_rdi, hf.keeps_rcx⟩

/-- The scalar compression function, verified with the scratch space it uses. -/
theorem scalar_verified192 :
    Verified X86_64.target Callee.scalar.code (Proof.Sha512.compressWideX86_64S 192) :=
  Rolled.compress_verified192

/-- The compression function with the SHA512 extension, verified with no
scratch space, which it does not use. -/
theorem shani_verified0 : Verified X86_64.target Callee.shani.code (Proof.Sha512.compressWideX86_64S 0) :=
  ShaNi.compress_verified0

theorem dimsS (so : Nat) (h : so ≤ 2048) : Dims (paramsS so) := ⟨dims.B, dims.N, dims.L, h⟩

theorem shapeS (so : Nat) : Shape (P := paramsS so) md := ⟨shape.len, shape.lenV, shape.out⟩

/-- `update` made with `so` bytes of working space for the compression
function, for an implementation verified with that much (`hv`). -/
theorem Update.verifiedS {so : Nat} (h : so = 0 ∨ so = 192) {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hv : Verified X86_64.target f.code (Proof.Sha512.compressWideX86_64S so))
    (hm : (Impl.MdStream.X86_64.update (paramsS so) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.MdStream.X86_64.update (paramsS so) f.name f.code)
      (Proof.Sha512.updateX86_64S (so + 48)) :=
  MdStream.X86_64.Update.verified (dimsS so (by omega_using [h])) (taintsS so h) (calleeS hf hv) hm

/-- `finalize` made with `so` bytes of working space for the compression
function, for an implementation verified with that much (`hv`). -/
theorem Finalize.verifiedS {so : Nat} (h : so = 0 ∨ so = 192) {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hv : Verified X86_64.target f.code (Proof.Sha512.compressWideX86_64S so))
    (hm : (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code)
      (Proof.Sha512.finalizeX86_64S (so + 48)) :=
  MdStream.X86_64.Finalize.verified (dimsS so (by omega_using [h])) (shapeS so) (taintsS so h) (calleeS hf hv) hm

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

/-! ### With the scratch space the compression function uses

`updateOwn` and `finalizeOwn` give the compression function only the
scratch space it uses (`Callee.so`), and are verified against the contracts
with the scratch space of the slowest implementation, which their callers
by name give them (`updateS_widen`: they run as they do with less). -/

/-- `update` verified with `a` bytes of scratch space is with any `b ≥ a`. -/
theorem updateS_widen {c : Prog isa} {a b : Nat} (h : Verified X86_64.target c (Proof.Sha512.updateX86_64S a))
    (hab : a ≤ b) (hsat : ∃ s, (Proof.Sha512.updateX86_64S b).pre s) :
    Verified X86_64.target c (Proof.Sha512.updateX86_64S b) :=
  Verified.widen h (fun s => [⟨s.gpr .rdi, 192⟩, ⟨s.gpr .r8, a⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ => ⟨h₁, rfl, h₃.sub_right (Region.sub_prefix hab), h₄, h₅.sub_right (Region.sub_prefix hab), h₆,
      h₇.sub_right (Region.sub_prefix hab), h₈, h₉, h₁₀.sub_right (Region.sub_prefix hab)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hab⟩ .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- `finalize` verified with `a` bytes of scratch space is with any `b ≥ a`. -/
theorem finalizeS_widen {c : Prog isa} {a b : Nat} (h : Verified X86_64.target c (Proof.Sha512.finalizeX86_64S a))
    (hab : a ≤ b) (hsat : ∃ s, (Proof.Sha512.finalizeX86_64S b).pre s) :
    Verified X86_64.target c (Proof.Sha512.finalizeX86_64S b) :=
  Verified.widen h (fun s => [⟨s.gpr .rdi, 192⟩, ⟨s.gpr .rdx, 64⟩, ⟨s.gpr .rcx, a⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ => ⟨h₁, rfl, h₃, h₄.sub_right (Region.sub_prefix hab), h₅.sub_right (Region.sub_prefix hab),
      h₆, h₇, h₈.sub_right (Region.sub_prefix hab), h₉, h₁₀, h₁₁.sub_right (Region.sub_prefix hab)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, Nat.le_refl _⟩ (.cons ⟨rfl, hab⟩ .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- `Impl.Sha512.X86_64.Stream.updateOwn`, for an implementation of the
compression function correct with the scratch space it uses (`hf`), if it
never loads MXCSR. -/
theorem updateOwn_verified {f : Callee} (h : f.so = 0 ∨ f.so = 192 ∨ f.so = 1328)
    (hf : CalleeOk (P := paramsS f.so) md f.code)
    (hm : (Impl.Sha512.X86_64.Stream.updateOwn f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, Proof.Sha512.updateX86_64.pre s) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.updateOwn f) Proof.Sha512.updateX86_64 :=
  updateS_widen (a := f.so + 48)
    (MdStream.X86_64.Update.verified (dimsS f.so (by omega_using [h])) (taintsS3 f.so h) hf hm)
    (by omega_using [h]) hsat

/-- `Impl.Sha512.X86_64.Stream.finalizeOwn`, likewise. -/
theorem finalizeOwn_verified {f : Callee} (h : f.so = 0 ∨ f.so = 192 ∨ f.so = 1328)
    (hf : CalleeOk (P := paramsS f.so) md f.code)
    (hm : (Impl.Sha512.X86_64.Stream.finalizeOwn f).allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, Proof.Sha512.finalizeX86_64.pre s) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.finalizeOwn f) Proof.Sha512.finalizeX86_64 :=
  finalizeS_widen (a := f.so + 48)
    (MdStream.X86_64.Finalize.verified (dimsS f.so (by omega_using [h])) (shapeS f.so) (taintsS3 f.so h) hf hm)
    (by omega_using [h]) hsat

end VG.Proof.Sha512.X86_64.Stream
