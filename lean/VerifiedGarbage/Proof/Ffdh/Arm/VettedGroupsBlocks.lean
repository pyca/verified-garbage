module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.CompareBuffer
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay

/-! The vetted-group scanner reuses the RSA byte-comparison proof. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Arm.RegUpd
open VG.Impl.Ffdh.Arm.VettedGroups
open VG.Proof.X25519.Arm (Rest)

 theorem triple (n : Nat) : (BitVec.ofNat 32 n + (BitVec.ofNat 32 n <<< 1)) = BitVec.ofNat 32 (3 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  omega

 theorem header_ok (s : State) {p : BitVec 32} {g : Group} {k : Nat}
    (h : RecordAt p g s) (ptr : s.gpr .r4 = p) (width : s.gpr .r6 = BitVec.ofNat 32 k)
    (kfit : k < 2 ^ 32) :
    WP isa (.block header) s fun t =>
      (t.gpr .r4 = p + 8 ∧ t.gpr .r5 = BitVec.ofNat 32 (3 * g.len) ∧
       t.gpr .r11 = BitVec.ofNat 32 g.bits ∧ t.gpr .r2 = 1 ∧
       t.z = decide (g.len = k) ∧ t.mem = s.mem) ∧ Rest [.r2, .r4, .r5, .r11] s t := by
  refine withRest_all [.r2, .r4, .r5, .r11] ?_ (by rfl) (by rfl)
  have eq : (BitVec.ofNat 32 g.len - BitVec.ofNat 32 k == 0) = decide (g.len = k) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro equal
      have number := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.lenFit,
        Nat.mod_eq_of_lt kfit] at number
      change (2 ^ 32 - k + g.len) % 2 ^ 32 = 0 at number
      have := h.lenFit
      omega
    · intro equal
      subst k
      simp
  have rb : InRegions (s.rd ++ s.wr) (State.addr (p + 4#32)) 4 := h.readBits
  have vb : s.mem.readW (State.addr (p + 4#32)) 32 = BitVec.ofNat 32 g.bits := h.bits
  unfold header
  ffrun [ptr, width, h.readLen, rb, h.len, vb, BitVec.add_zero, BitVec.ofNat_eq_ofNat, triple, eq]
  exact eq

 theorem compareArgs_ok (s : State) :
    WP isa (.block compareArgs) s fun t =>
      (t.gpr .r0 = s.gpr .r9 ∧ t.gpr .r1 = s.gpr .r4 ∧ t.gpr .lr = s.gpr .r10 ∧
        t.gpr .r2 = 0 ∧ t.mem = s.mem) ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  refine withRest_all [.r0, .r1, .r2, .lr] ?_ (by rfl) (by rfl)
  unfold compareArgs
  ffrun []

 theorem compare_ok (s : State) {src p : BitVec 32} {k : Nat} {dom : List Byte} {g : Group}
    (source : Source src k dom s) (record : RecordAt p g s) (same : g.len = k)
    (first : s.gpr .r9 = src) (second : s.gpr .r4 = p + 8)
    (count : s.gpr .r10 = BitVec.ofNat 32 dom.length) :
    WP isa VG.Impl.Ffdh.Arm.VettedGroups.compare s fun t =>
      (t.gpr .r2 = 0 ↔ dom = g.domain.take dom.length) ∧ t.mem = s.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  have nfit : dom.length < 2 ^ 32 := by rw [← same] at source; have := record.fit; rcases source.length with h | h <;> omega
  have limit : dom.length ≤ 3 * g.len := by rcases source.length with h | h <;> omega
  have pfit : (p + 8).toNat + dom.length ≤ 2 ^ 32 := by
    change (p.toNat + 8) % 2 ^ 32 + dom.length ≤ 2 ^ 32
    have := record.fit
    omega
  have read : InRegions (s.rd ++ s.wr) (State.addr (p + 8)) dom.length := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CallLay.inRegions_sub record.read (off := 0) (by omega : 0 + dom.length ≤ 3 * g.len) (by have := record.fit; omega)
  rw [VG.Impl.Ffdh.Arm.VettedGroups.compare, WP.seq_iff]
  refine WP.mono (compareArgs_ok s) ?_
  rintro u ⟨⟨r0, r1, lr, zero, memU⟩, restU⟩
  refine WP.mono (VG.Proof.Bignum.Arm.compareBuffer_ok u source.positive nfit source.fit pfit
    (by rw [restU.rd, restU.wr]; exact source.read)
    (by rw [restU.rd, restU.wr]; exact read)
    (r0.trans first) (r1.trans second) (lr.trans count) zero) ?_
  rintro t ⟨equal, memT, restT⟩
  have front : Spec.Rsa.bytesAt s.mem (State.addr (p + 8)) dom.length = g.domain.take dom.length := by
    rw [← record.bytes]
    simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_eq_left limit]
  rw [memU, source.bytes, front] at equal
  exact ⟨equal, memT.trans memU, (restU.mono (by simp)).trans restT⟩

end VG.Proof.Ffdh.Arm.VettedGroups
