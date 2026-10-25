module

public import VerifiedGarbage.Proof.MdStream.RISCV64.Update
public meta import VerifiedGarbage.Proof.MdStream.RISCV64.Update
public import VerifiedGarbage.Proof.MdStream.RISCV64.Finalize
public meta import VerifiedGarbage.Proof.MdStream.RISCV64.Finalize
public import VerifiedGarbage.Proof.MdStream.RISCV64.Init
public meta import VerifiedGarbage.Proof.MdStream.RISCV64.Init
public import VerifiedGarbage.Proof.Md5.Md
public meta import VerifiedGarbage.Proof.Md5.Md
public import VerifiedGarbage.Proof.Md5.RISCV64.Compress
public meta import VerifiedGarbage.Proof.Md5.RISCV64.Compress
public import VerifiedGarbage.Impl.Md5.RISCV64.Stream
public meta import VerifiedGarbage.Impl.Md5.RISCV64.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
meta import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
meta import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Md5.Stream
meta import VerifiedGarbage.Proof.Md5.Stream
import all Init.Data.Nat.Bitwise.Basic

/-!
# Streaming MD5 on RISC-V

`init` stores the initial MD buffer (`Proof/MdStream/RISCV64/Init.lean`), and
`update` and `finalize` are the generic streaming code
(`Impl/MdStream/RISCV64.lean`), so they are verified by the generic proofs
(`Proof/MdStream/RISCV64/`) for MD5's instance (`Proof/Md5/Md.lean`), given
what MD5's own pieces do: its length field and digest (`shape`), that its
compression function is verified with the streaming code's 80 bytes of
scratch space (`callee`), and that the taint analysis accepts its code.
-/

@[expose] public section

namespace VG.Proof.Md5.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.ByteLoad VG.RISCV64.Bytes VG.Proof.MdStream
open VG.Proof.MdStream.RISCV64
open VG.Impl.Md5.RISCV64.Stream (params lenStore outW)
open VG.Impl.Words.RISCV64 (loadLE32 storeLE32 storeLE64)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_append writeBytes_frame write_eq_writeBytes)
open VG.Spec.Sha256 (bytesAt)

/-! ## The compression function, with 80 bytes of scratch space -/

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub64 (a : Addr) : Region.Sub ⟨a, 64⟩ ⟨a, 80⟩ := Region.sub_prefix (by decide)

/-- A state satisfying `compressK md`'s precondition. -/
def compressSat : State := { satState with wr := [⟨0x1000, 16⟩, ⟨0x3000, 80⟩] }

theorem compress80 : Verified RISCV64.target Impl.Md5.RISCV64.compress (compressK md) :=
  Verified.widen compress_verified (fun s => [⟨s.gpr .a0, 16⟩, ⟨s.gpr .a3, 64⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub64 _), h₄, h₅.sub_right (sub64 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    ⟨compressSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide)⟩

theorem callee : CalleeOk md Impl.Md5.RISCV64.compress := ⟨compress80.1, by decide +kernel⟩

/-! ## The length field and the digest -/

/-- A little-endian word written is its bytes. -/
theorem writeW32_eq (m : Mem) (a : Addr) (w : BitVec 32) :
    m.writeW a w = writeBytes m a (MdStream.bytes32 false w) := by
  rw [Mem.writeW, write_eq_writeBytes]
  simp [MdStream.bytes32, List.range_succ]

/-- A little-endian doubleword written as two words is its bytes. -/
theorem writeLE64 (m : Mem) (a : Addr) (x : BitVec 64) :
    (m.writeW a (x.setWidth 32)).writeW (a + BitVec.ofNat 64 4) ((x >>> 32).setWidth 32) =
      writeBytes m a ((List.range 8).map fun i => x.extractLsb' (8 * i) 8) := by
  rw [writeW32_eq, writeW32_eq, show (4 : Nat) = (MdStream.bytes32 false (x.setWidth 32)).length from rfl,
    writeBytes_append _ _ _ _ (by simp [MdStream.bytes32])]
  congr 1
  simp only [MdStream.bytes32, List.range_succ, List.range_zero, List.map, Bool.false_eq_true, ite_false,
    List.cons_append, List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i hi <;> simp <;>
    first | (intro; omega) | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

/-- An access at an offset within an access. -/
theorem contains_add {r : Region} {a : Addr} {n d m : Nat} (h : r.Contains a n) (hd : d + m ≤ n) :
    r.Contains (a + BitVec.ofNat 64 d) m := by
  simp only [Region.Contains] at h ⊢
  rw [show a + BitVec.ofNat 64 d - r.base = (a - r.base) + BitVec.ofNat 64 d by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]; ac_rfl, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem in_split {rs : List Region} {a : Addr} (h : InRegions rs a 8) :
    InRegions rs a 4 ∧ InRegions rs (a + BitVec.ofNat 64 4) 4 := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega⟩, ⟨r, hr, ?_⟩⟩
  simp only [Region.Contains] at hc ⊢
  rw [show a + BitVec.ofNat 64 4 - r.base = (a - r.base) + BitVec.ofNat 64 4 by
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]; ac_rfl, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem len_ok (s : State) (hout : InRegions s.wr (s.gpr .s1 + BitVec.ofNat 64 (params.N + 56)) 8) :
    WP isa (.block params.len) s fun s' => (∀ r, r ≠ .t1 → r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s1 + BitVec.ofNat 64 (params.N + 56)) (md.lenOf (s.gpr .s4)) := by
  obtain ⟨h0, h4⟩ := in_split hout
  show WP isa (.block (.shift .sll .d .t1 .s4 3 :: storeLE64 .t1 .t3 .t1 .s1 72)) s _
  refine wp_sll (by decide) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .s1 = s.gpr .s1 := u₁.other _ (by decide)
  refine WP.mono (storeLE64_ok (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [u₁.wr, e1]; exact h0)
    (by rw [u₁.wr, e1, show (72 + 4 : Nat) = 72 + 4 from rfl, BitVec.ofNat_add, ← BitVec.add_assoc]
        exact h4)) fun s' ⟨hm, hg, hrd, hwr, hsp⟩ =>
    ⟨fun r h1 h3 => by rw [hg r h3 h1, u₁.other r h1], by rw [hrd, u₁.rd], by rw [hwr, u₁.wr],
      by rw [hsp, u₁.sp], ?_⟩
  show _ = writeBytes s.mem (s.gpr .s1 + BitVec.ofNat 64 72) _
  rw [hm, e1, u₁.gpr, u₁.mem, show s.gpr .s1 + BitVec.ofNat 64 (72 + 4) =
    s.gpr .s1 + BitVec.ofNat 64 72 + BitVec.ofNat 64 4 by rw [BitVec.ofNat_add, BitVec.add_assoc], writeLE64]
  simp only [md, lenField, Proof.Sha256.Stream.bits8]

/-- The first `k` words of the digest are written. -/
structure OutI (s₀ : State) (k : Nat) (s : State) : Prop where
  keep : ∀ r, r ≠ .t1 → r ≠ .t2 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem (s₀.gpr .s3) ((List.range k).flatMap fun j =>
    MdStream.bytes32 false (s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (4 * j)) 32))

theorem flat_length (f : Nat → BitVec 32) (k : Nat) :
    ((List.range k).flatMap fun j => MdStream.bytes32 false (f j)).length = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp [MdStream.bytes32]; omega

/-- A word written after `4 k` bytes. -/
theorem writeBytes_word (m : Mem) (q : Addr) (xs : List Byte) (w : BitVec 32) {k : Nat} (hk : k < 4)
    (hx : xs.length = 4 * k) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 (4 * k)) w = writeBytes m q (xs ++ MdStream.bytes32 false w) := by
  rw [writeW32_eq, ← hx, writeBytes_append _ _ _ _ (by simp [MdStream.bytes32]; omega)]

theorem out_step {s₀ : State} (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .s1) 16)
    (hout : InRegions s₀.wr (s₀.gpr .s3) 16) (hd : Region.Disjoint ⟨s₀.gpr .s1, 16⟩ ⟨s₀.gpr .s3, 16⟩)
    {k : Nat} (hk : k < 4) {s : State} (h : OutI s₀ k s) :
    WP isa (.block (outW k)) s (OutI s₀ (k + 1)) := by
  obtain ⟨Rin, hRin, cin⟩ := hin
  obtain ⟨Rout, hRout, cout⟩ := hout
  have h1 : s.gpr .s1 = s₀.gpr .s1 := h.keep _ (by decide) (by decide)
  have h3 : s.gpr .s3 = s₀.gpr .s3 := h.keep _ (by decide) (by decide)
  have hP := flat_length (fun j => s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (4 * j)) 32) k
  unfold outW
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (by decide) (by decide) (by decide) (by omega)
    ⟨Rin, by rw [h.rd, h.wr]; exact hRin, by rw [h1]; exact contains_add cin (by omega)⟩) fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (storeLE32_ok (by decide) (by decide) (by omega)
    ⟨Rout, by rw [RegUpd.wr_write, RegUpd.wr_write, h.wr]; exact hRout, by
      rw [RegUpd.gpr_write_of_ne _ _ (by decide), RegUpd.gpr_write_of_ne _ _ (by decide), h3]
      exact contains_add cout (by omega)⟩) fun s₂ e₂ => ?_
  subst e₂
  -- The word read is the one of the initial memory: the output is elsewhere.
  have hread : s.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (4 * k)) 32 =
      s₀.mem.readW (s₀.gpr .s1 + BitVec.ofNat 64 (4 * k)) 32 := by
    rw [h.mem]
    refine (writeBytes_frame (R := ⟨s₀.gpr .s3, 16⟩) _ _ _ ?_).readW
      (r := ⟨s₀.gpr .s1 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _) ?_ (by decide)
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hP]; omega
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact hd.sub_left (Offset.sub_base _ (by omega))
  refine ⟨fun r h1' h2' => ?_, h.rd, h.wr, h.sp, ?_⟩
  · simp only [RegUpd.gpr_write, h1', h2', ite_false]
    exact h.keep r h1' h2'
  · simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ↓reduceIte, h1, h3, lo32_ext, hread]
    rw [h.mem, writeBytes_word _ _ _ _ hk hP, List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem out_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .s1) params.N)
    (hout : InRegions s.wr (s.gpr .s3) 16) (hd : Region.Disjoint ⟨s.gpr .s1, params.N⟩ ⟨s.gpr .s3, 16⟩) :
    WP isa (.block params.out) s fun s' => (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      s'.mem = writeBytes s.mem (s.gpr .s3) ((md.digest (md.stateAt s.mem (s.gpr .s1))).take 16) := by
  refine WP.mono (wp_range_flatMap (M := isa) (OutI s) (fun k s' hk h => out_step hin hout hd hk h) 4
    (Nat.le_refl _) s ⟨fun _ _ _ => rfl, rfl, rfl, rfl, by simp [writeBytes_nil]⟩)
    fun s' h => ⟨h.keep, h.rd, h.wr, h.sp, ?_⟩
  rw [h.mem, digest_eq, List.take_of_length_le (by rw [flat_length])]

theorem shape : ShapeD (P := params) md 16 where
  le := by decide
  len := len_ok
  out := out_ok

/-! ## The functions -/

theorem init_verified : Verified RISCV64.target Impl.Md5.RISCV64.Stream.init Proof.Md5.initRISCV64 :=
  have h := MdStream.RISCV64.init_verified (n := 80) Spec.Md5.H0.toList (by decide) (by decide)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0]) (fun _ _ _ _ h => initAgree h)
      (by taint_decide))
  Verified.of_implies h ⟨fun _ h => h, fun s _ _ h => by
      refine (repr_iff (m := [])).mpr (md.repr_nil (StateMem.stateAt_eq fun k hk => ?_))
      rw [h k (by simpa using hk), getElem!_pos _ k (by simpa using hk), Vector.getElem_toList],
    fun _ _ _ _ h => h, h.2.2⟩

theorem update_verified : Verified RISCV64.target Impl.Md5.RISCV64.Stream.update Proof.Md5.updateRISCV64 :=
  have h := MdStream.RISCV64.Update.verified (P := params) (name := "vg_md5_compress") (by decide) callee
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
      (fun _ _ _ _ hp => MdStream.RISCV64.Update.agree₀ hp) (by taint_decide))
    ⟨MdStream.RISCV64.Update.sat 16, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩
  Verified.of_implies h ⟨fun _ h => h, fun _ _ _ h m hr hc => h Spec.Md5.H0 m hr hc, fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified :
    Verified RISCV64.target Impl.Md5.RISCV64.Stream.finalize Proof.Md5.finalizeRISCV64 :=
  have h := MdStream.RISCV64.Finalize.verifiedD (P := params) (name := "vg_md5_compress") (by decide) shape callee
    (keepsN_all _ (by decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
      (fun _ _ _ _ hp => MdStream.RISCV64.Finalize.agree₀ hp) (by taint_decide))
    ⟨MdStream.RISCV64.Finalize.sat 16 16, rfl, rfl, Region.disjoint_of_sep (by decide), by decide, by decide,
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩
  Verified.of_implies h
    ⟨fun _ h => h, fun _ _ _ h m hr hc => by
      have := h Spec.Md5.H0 m hr trivial hc
      exact this.trans (List.take_of_length_le (Nat.le_of_eq (md.digest_length _))),
      fun _ _ _ _ h => h, h.2.2⟩

end VG.Proof.Md5.RISCV64.Stream
