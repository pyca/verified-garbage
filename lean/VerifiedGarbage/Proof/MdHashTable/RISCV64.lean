module

public import VerifiedGarbage.Impl.MdHashTable.RISCV64
public import VerifiedGarbage.Proof.MdStream.Spec
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Artifact
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Impl.MdHashTable.RISCV64
import VerifiedGarbage.Proof.Md5.RISCV64.Stream
import VerifiedGarbage.Proof.Sha1.RISCV64.Stream
import VerifiedGarbage.Proof.MdStream.RISCV64.Words
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic

/-!
# The digest of a hash value on RISC-V

`digestK H`: the contract of `digest out` (`Impl/MdHashTable/RISCV64.lean`)
for a Merkle–Damgård hash function `H` whose digest `out` writes
(`OutOK`): it writes `H.digest` of the hash value at `a0` to `a1`
(`digest_ok`), and is constant time for the pointers (`digest_ct`). What
each family's `out` writes: MD5's and SHA-1's from their streaming proofs'
shapes, SHA-256's eight and the SHA-512 family's eight words big-endian
(`out_md5`, `out_sha1`, `out_sha256`, `out_sha512`).
-/

@[expose] public section

namespace VG.Proof.MdHashTable.RISCV64

open VG VG.RISCV64 VG.Proof.MdStream VG.RISCV64.ByteLoad
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)
open VG.Impl.MdHashTable.RISCV64 (digest outMd5 outSha1 outSha256 outSha512)

section
variable {B N L : Nat} (H : Md B N L)

/-- What `out` does: from the hash value at `s1`, writes its digest to `s3`,
and writes only `t1`, `t2` and `t4`. -/
def OutOK (out : List Instr) : Prop :=
  ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .s1) N → InRegions s.wr (s.gpr .s3) N →
    Region.Disjoint ⟨s.gpr .s1, N⟩ ⟨s.gpr .s3, N⟩ →
    WP isa (.block out) s fun s' => (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s3) (H.digest (H.stateAt s.mem (s.gpr .s1)))

/-- The contract of `digest(value = a0, out = a1)`: the `N` bytes of the
hash value readable, the `N` bytes of `out` writable, apart; `out` then holds
the digest of the hash value. -/
def digestK : Contract isa where
  pre s :=
    let value : Region := ⟨s.gpr .a0, N⟩
    let out : Region := ⟨s.gpr .a1, N⟩
    s.rd = [value] ∧ s.wr = [out] ∧ value.Disjoint out
  post s s' := s'.mem = writeBytes s.mem (s.gpr .a1) (H.digest (H.stateAt s.mem (s.gpr .a0)))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

variable {H}

/-- `digest out` meets `digestK H`, keeping every register but `a2`, `a3`,
`t1`, `t2` and `t4`, and the regions. -/
theorem digest_wp {out : List Instr} (ho : OutOK H out) {s : State} (hpre : (digestK H).pre s) :
    WP isa (digest out) s fun s' => (∀ r, r ≠ .a2 → r ≠ .a3 → r ≠ .t1 → r ≠ .t2 → r ≠ .t4 →
      s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (digestK H).post s s' := by
  obtain ⟨hrd, hwr, hvo⟩ := hpre
  unfold digest
  refine Steps.wp_mv fun s₁ u₁ => Steps.wp_mv fun s₂ u₂ => Steps.wp_mv fun s₃ u₃ => Steps.wp_mv fun s₄ u₄ => ?_
  have e1 : s₄.gpr .s1 = s.gpr .a0 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  have e3 : s₄.gpr .s3 = s.gpr .a1 := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  simp only [List.append_eq, List.nil_append]
  rw [WP.block_append_iff]
  refine WP.mono (ho s₄ (by rw [e1, rd₄, wr₄, hrd]; exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _),
      Region.contains_self _ _⟩) (by rw [e3, wr₄, hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
      (by rw [e1, e3]; exact hvo)) fun s₅ ⟨g₅, rd₅, wr₅, sp₅, mem₅⟩ => ?_
  refine Steps.wp_mv fun s₆ u₆ => Steps.wp_mv fun s₇ u₇ => WP.block_nil ?_
  have k₄ : ∀ r, r ≠ .a2 → r ≠ .a3 → r ≠ .s1 → r ≠ .s3 → s₄.gpr r = s.gpr r := fun r h2 h3 h1 h3' => by
    rw [u₄.other _ h3', u₃.other _ h1, u₂.other _ h3, u₁.other _ h2]
  refine ⟨fun r h2 h3 h1 ht2 h4 => ?_, by rw [u₇.rd, u₆.rd, rd₅, rd₄], by rw [u₇.wr, u₆.wr, wr₅, wr₄],
    by rw [u₇.sp, u₆.sp, sp₅, u₄.sp, u₃.sp, u₂.sp, u₁.sp], ?_⟩
  · by_cases hs1 : r = .s1
    · subst hs1
      rw [u₇.other _ (by decide), u₆.gpr, g₅ .a2 (by decide) (by decide) (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
    by_cases hs3 : r = .s3
    · subst hs3
      rw [u₇.gpr, u₆.other _ (by decide), g₅ .a3 (by decide) (by decide) (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
    rw [u₇.other _ hs3, u₆.other _ hs1, g₅ r h1 ht2 h4, k₄ r h2 h3 hs1 hs3]
  · show s₇.mem = _
    rw [u₇.mem, u₆.mem, mem₅, m₄, e1, e3]

/-- `digest out` meets `digestK H`. -/
theorem digest_ok {out : List Instr} (ho : OutOK H out) :
    ∀ s, (digestK H).pre s → ∃ t s', Exec isa (digest out) s t s' ∧ abiPreserved s s' ∧ (digestK H).post s s' :=
  fun _ hpre => let ⟨t, s', he, hg, _, _, hsp, hm⟩ := digest_wp ho hpre
    ⟨t, s', he, ⟨fun r hr => hg r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide) (by revert r; decide), hsp, hg _ (by decide) (by decide) (by decide) (by decide)
      (by decide)⟩, hm⟩

end

/-! ## Constant time -/

theorem digest_ct_of {B N L : Nat} {H : Md B N L} {out : List Instr}
    (h : ∃ hc, (taint.check (Taint.ofRegs [.a0, .a1]) (digest out) hc).isSome = true) :
    ConstantTime isa (digestK H).pre (digestK H).pub (digest out) :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h0, h1]⟩) h

theorem ct_md5 : ∃ hc, (taint.check (Taint.ofRegs [.a0, .a1]) (digest outMd5) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem ct_sha1 : ∃ hc, (taint.check (Taint.ofRegs [.a0, .a1]) (digest outSha1) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem ct_sha256 : ∃ hc, (taint.check (Taint.ofRegs [.a0, .a1]) (digest outSha256) hc).isSome = true :=
  ⟨_, by taint_decide⟩
theorem ct_sha512 : ∃ hc, (taint.check (Taint.ofRegs [.a0, .a1]) (digest outSha512) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## What each family's `out` writes -/

theorem out_md5 : OutOK Proof.Md5.md outMd5 := fun s hin hout hd =>
  (Proof.Md5.RISCV64.Stream.shape.out s hin hout hd).mono fun _ ⟨g, rd, wr, sp, m⟩ =>
    ⟨fun r h1 h2 _ => g r h1 h2, rd, wr, sp, by
      rw [m, List.take_of_length_le (by rw [Proof.Md5.md.digest_length])]⟩

theorem out_sha1 : OutOK Proof.Sha1.md outSha1 := fun s hin hout hd =>
  (Proof.Sha1.RISCV64.Stream.shape.out s hin hout hd).mono fun _ ⟨g, rd, wr, sp, m⟩ =>
    ⟨fun r h1 h2 _ => g r h1 h2, rd, wr, sp, by
      rw [m, List.take_of_length_le (by rw [Proof.Sha1.md.digest_length])]⟩

theorem out_sha256 : OutOK Proof.Sha256.md outSha256 := fun s hin hout hd =>
  (MdStream.RISCV64.outBE_ok (n := 8) (by decide) s hin hout hd).mono fun _ ⟨g, rd, wr, sp, m⟩ =>
    ⟨fun r h1 h2 _ => g r h1 h2, rd, wr, sp, by rw [m, Proof.Sha256.digest_eq]⟩

/-! ### The SHA-512 family's: eight 64-bit words, big-endian -/

/-- A doubleword of the digest, as `storeBE 8` stores it. -/
theorem beBytes_dword (x : BitVec 64) : ByteLoad.beBytes 8 x = bytes64 true x := by
  simp only [ByteLoad.beBytes, MdStream.RISCV64.shr_byte, bytes64, ite_true]
  rfl

theorem flat64_length (f : Nat → BitVec 64) (k : Nat) :
    ((List.range k).flatMap fun j => bytes64 true (f j)).length = 8 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih, List.flatMap_singleton,
      bytes64_length]
    omega

theorem digest512_eq (mem : Mem) (p : Addr) :
    Proof.Sha512.md.digest (Proof.Sha512.md.stateAt mem p) = (List.range 8).flatMap fun k =>
      bytes64 true (mem.readW (p + BitVec.ofNat 64 (8 * k)) 64) := by
  simp [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.toList_ofFn, List.range_succ, List.ofFn_succ, bytes64,
    Spec.Sha512.wordBytes]

/-- Bytes written right after `xs`, at `8 k`. -/
theorem writeBytes_after8 (m : Mem) (q : Addr) (xs ys : List Byte) {k : Nat} (hx : xs.length = 8 * k)
    (h : xs.length + ys.length < 2 ^ 64) :
    writeBytes (writeBytes m q xs) (q + BitVec.ofNat 64 (8 * k)) ys = writeBytes m q (xs ++ ys) := by
  rw [← hx, writeBytes_append _ _ _ _ h]

/-- The first `k` doublewords of the digest are written. -/
structure Out64 (s₀ : State) (k : Nat) (s : State) : Prop where
  keep : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t4 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem (s₀.gpr .s3) ((List.range k).flatMap fun j =>
    bytes64 true (s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (8 * j)) 64))

theorem out64_step {s₀ : State} (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .s1) 64)
    (hout : InRegions s₀.wr (s₀.gpr .s3) 64) (hd : Region.Disjoint ⟨s₀.gpr .s1, 64⟩ ⟨s₀.gpr .s3, 64⟩)
    {k : Nat} (hk : k < 8) {s : State} (h : Out64 s₀ k s) :
    WP isa (.block (Impl.Sha512.RISCV64.Stream.outW k)) s (Out64 s₀ (k + 1)) := by
  obtain ⟨Rin, hRin, cin⟩ := hin
  obtain ⟨Rout, hRout, cout⟩ := hout
  have h1 : s.gpr .s1 = s₀.gpr .s1 := h.keep _ (by decide) (by decide) (by decide)
  have h3 : s.gpr .s3 = s₀.gpr .s3 := h.keep _ (by decide) (by decide) (by decide)
  have hP := flat64_length (fun j => s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (8 * j)) 64) k
  simp only [Impl.Sha512.RISCV64.Stream.outW]
  rw [WP.block_append_iff]
  refine WP.mono (Words64.loadLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by omega)
    ⟨Rin, by rw [h.rd, h.wr]; exact hRin, by rw [h1]; exact MdStream.RISCV64.contains_add cin (by omega)⟩)
    fun s₁ u₁ => ?_
  have k3 : s₁.gpr .s3 = s₀.gpr .s3 := by rw [u₁.other _ (by decide) (by decide) (by decide), h3]
  refine WP.mono (storeBE_ok (by decide) (by decide) (by decide) (by decide) (by omega)
    fun j hj => ⟨Rout, by rw [u₁.wr, h.wr]; exact hRout, by
      rw [k3]; exact MdStream.RISCV64.contains_add cout (by omega)⟩) fun s₂ e₂ => ?_
  subst e₂
  have hread : s.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (8 * k)) 64 =
      s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (8 * k)) 64 := by
    rw [h.mem]
    refine (writeBytes_frame (R := ⟨s₀.gpr .s3, 64⟩) _ _ _ ?_).readW
      (r := ⟨s₀.gpr .s1 + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _) ?_ (by decide)
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hP]; omega
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (Offset.sub_base _ (by omega))
  refine ⟨fun r h1' h2' h4' => ?_, u₁.rd.trans h.rd, u₁.wr.trans h.wr, u₁.sp.trans h.sp, ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ h2']
    show s₁.gpr r = _
    rw [u₁.other _ h1' h2' h4']
    exact h.keep r h1' h2' h4'
  · rw [RegUpd.mem_write]
    show writeBytes s₁.mem (s₁.gpr .s3 + _) (ByteLoad.beBytes 8 (s₁.gpr .t1)) = _
    rw [k3, u₁.gpr, u₁.mem, h1, hread, beBytes_dword, h.mem,
      writeBytes_after8 _ _ _ _ hP (by rw [hP, bytes64_length]; omega), List.range_succ,
      List.flatMap_append, List.flatMap_singleton]

theorem out_sha512 : OutOK Proof.Sha512.md outSha512 := fun s hin hout hd =>
  (wp_range_flatMap (M := isa) (Out64 s) (fun k s' hk h => out64_step hin hout hd hk h) 8
    (Nat.le_refl _) s ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, by simp [writeBytes_nil]⟩).mono
    fun s' h => ⟨h.keep, h.rd, h.wr, h.sp, by rw [h.mem, digest512_eq]⟩

end VG.Proof.MdHashTable.RISCV64
