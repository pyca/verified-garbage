import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Md
import VerifiedGarbage.Proof.Sha512.Digest

/-!
# Streaming SHA-384, SHA-512/256 and SHA-512/224 on x86-64: `finalize`

`finalizeDigest` is the generic `finalize` (`Impl/MdStream/X86_64.lean`) with
a digest of the first 48, 32 or 28 bytes of the final hash value
(`params384`, `params512_256`, `params512_224`), so it is verified by the
generic proof of a `finalize` writing a prefix of the final hash value
(`Finalize.verifiedD`), for any implementation of the compression function,
given what writing that prefix does (`ShapeD`).
-/

namespace VG.Proof.Sha512.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (out64)
open VG.Impl.Sha512.X86_64 (at_)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_frame)
open VG.Impl.Sha512.X86_64.Stream (Callee outHi params384 params512_256 params512_224 finalizeDigest)

/-- `out64 n` writes the first `8 n` bytes of the digest. -/
theorem out64_take {n : Nat} (hn : n ≤ 8) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rbx) 64)
    (hout : InRegions s.wr (s.gpr .rbp) (8 * n)) (hd : Region.Disjoint ⟨s.gpr .rbx, 64⟩ ⟨s.gpr .rbp, 8 * n⟩) :
    WP isa (.block (out64 n)) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem (s.gpr .rbp) ((md.digest (md.stateAt s.mem (s.gpr .rbx))).take (8 * n)) :=
  (out64_ok (n := n) (by omega) (inRegions_prefix hin (by omega)) hout (hd.sub_left (Region.sub_prefix (by omega)))).mono
    fun _ ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, by rw [m, digest_take _ _ hn]⟩

/-- `out64 3 ++ outHi 3` writes the first 28 bytes of the digest. -/
theorem out224_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rbx) 64)
    (hout : InRegions s.wr (s.gpr .rbp) 28) (hd : Region.Disjoint ⟨s.gpr .rbx, 64⟩ ⟨s.gpr .rbp, 28⟩) :
    WP isa (.block (out64 3 ++ outHi 3)) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = writeBytes s.mem (s.gpr .rbp) ((md.digest (md.stateAt s.mem (s.gpr .rbx))).take 28) := by
  rw [WP.block_append_iff]
  refine (out64_ok (n := 3) (by decide) (inRegions_prefix hin (by decide)) (inRegions_prefix hout (by decide))
    ((hd.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)))).mono
    fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_
  have hl : ((List.range 3).flatMap fun k =>
      bytes64 true (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64)).length = 24 :=
    length_flatMap_range _ (w := 8) (fun _ => by simp [bytes64]) 3
  -- The high half of word 3 is not yet overwritten.
  have hread : s₁.mem.readW (s.gpr .rbx + BitVec.ofNat 64 28) 32 = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 28) 32 := by
    rw [m₁]
    refine (writeBytes_frame _ _ _ (R := ⟨s.gpr .rbp, 28⟩) ?_).readW
      (r := ⟨s.gpr .rbx + BitVec.ofNat 64 28, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    · rw [hl]
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
      decide
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (sub_offset (by decide) (by decide))
  refine wp_mov32m (a := s.gpr .rbx + BitVec.ofNat 64 28)
    (by rw [ea_at, g₁ _ (by decide), ofInt_natCast]) (by rw [rd₁, wr₁]; exact InRegions.offset hin (by decide) (by decide))
    fun s₂ u₂ => wp_bswap32 fun s₃ u₃ => wp_store32 (a := s.gpr .rbp + BitVec.ofNat 64 24)
      (by rw [ea_at, u₃.other _ (by decide), u₂.other _ (by decide), g₁ _ (by decide), ofInt_natCast])
      (by rw [u₃.wr, u₂.wr, wr₁]; exact InRegions.offset hout (by decide) (by decide)) fun s₄ g₄ m₄ rd₄ wr₄ =>
        WP.block_nil ⟨fun r h => by rw [g₄, u₃.other r h, u₂.other r h, g₁ r h], by rw [rd₄, u₃.rd, u₂.rd, rd₁],
          by rw [wr₄, u₃.wr, u₂.wr, wr₁], ?_⟩
  rw [m₄, u₃.mem, u₂.mem, u₃.gpr, u₂.gpr, setWidth32, setWidth32, hread, m₁, digest_take28,
    ← writeBytes_append _ _ _ _ (by rw [hl]; simp [bytes32]), hl, ← writeW32 _ _ true]
  rfl

theorem shape384 : ShapeD (P := params384) md 48 where
  le := by decide
  len := shape.len
  out s hin hout hd := out64_take (n := 6) (by decide) s hin hout hd

theorem shape512_256 : ShapeD (P := params512_256) md 32 where
  le := by decide
  len := shape.len
  out s hin hout hd := out64_take (n := 4) (by decide) s hin hout hd

theorem shape512_224 : ShapeD (P := params512_224) md 28 where
  le := by decide
  len := shape.len
  out s hin hout hd := out224_ok s hin hout hd

theorem taints384 : Taints params384 :=
  ⟨taints.updStart, taints.updHead, taints.updEnd, taints.finStart, taints.finPad, ⟨_, by taint_decide⟩,
    taints.lenSec, ⟨_, by taint_decide⟩, taints.lenSafe, by decide⟩

theorem taints512_256 : Taints params512_256 :=
  ⟨taints.updStart, taints.updHead, taints.updEnd, taints.finStart, taints.finPad, ⟨_, by taint_decide⟩,
    taints.lenSec, ⟨_, by taint_decide⟩, taints.lenSafe, by decide⟩

theorem taints512_224 : Taints params512_224 :=
  ⟨taints.updStart, taints.updHead, taints.updEnd, taints.finStart, taints.finPad, ⟨_, by taint_decide⟩,
    taints.lenSec, ⟨_, by taint_decide⟩, taints.lenSafe, by decide⟩

/-- `finalizeDigest`'s contract: `finalizeX86_64`, for a state hashed from
`iv` and a `D`-byte `digest`. -/
def finalizeDigestX86_64 (iv : Spec.Sha512.HashValue) (D : Nat) (digest : List Byte → List Byte) :
    Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 192⟩
    let out : Region := ⟨s.gpr .rdx, D⟩
    let scratch : Region := ⟨s.gpr .rcx, 1376⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Spec.Sha512.Repr iv s.mem (s.gpr .rdi) m → m.length < 2 ^ 64 →
    s.gpr .rsi = BitVec.ofNat 64 m.length → Spec.Sha512.bytesAt s'.mem (s.gpr .rdx) D = digest m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace Finalize

/-- `finalizeDigest P` writing a `D`-byte `digest` of the messages hashed
from `iv` is verified if it never loads MXCSR. -/
theorem verifiedDigest {o : List Instr} {D : Nat} (hs : ShapeD (P := { params with out := o }) md D)
    (ht : Taints { params with out := o }) {iv : Spec.Sha512.HashValue} {digest : List Byte → List Byte}
    (hdg : ∀ m, (md.hash iv m).take D = digest m) {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : (finalizeDigest { params with out := o } f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalizeDigest { params with out := o } f) (finalizeDigestX86_64 iv D digest) :=
  have h := MdStream.X86_64.Finalize.verifiedD (P := { params with out := o }) ⟨dims.B, dims.N, dims.L, dims.so⟩ hs ht (hf.withOut o) hm
  h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hl hc => (h iv m hr hl hc).trans (hdg m),
    fun _ _ _ _ h => h, h.2.2⟩

/-- A state satisfying `finalizeDigestX86_64`'s precondition. -/
abbrev satD (D : Nat) : State := MdStream.X86_64.Finalize.satD params D

end Finalize

end VG.Proof.Sha512.X86_64.Stream
