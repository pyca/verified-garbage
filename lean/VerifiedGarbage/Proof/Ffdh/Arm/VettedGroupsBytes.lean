module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsEnvironment
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsConsts
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Decode the serialized read-only vetted-domain table into its execution invariant. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Impl.Ffdh.Arm.VettedGroups

private theorem decode_wordBytes (x : Nat) (fit : x < 2 ^ 32) :
    VG.Proof.X25519.leNum (wordBytes x) = x := by
  simp only [wordBytes, List.range_succ, List.range_zero, List.map_append,
    List.map_cons, List.map_nil, List.nil_append, Nat.reduceMul, Nat.reducePow, Nat.div_one]
  simp only [List.cons_append, List.nil_append, VG.Proof.X25519.leNum,
    BitVec.toNat_ofNat, Nat.mul_zero, Nat.add_zero]
  omega

private theorem read_wordBytes {m : Mem} {p : Addr} {x : Nat}
    (fit : x < 2 ^ 32) (bytes : Spec.Rsa.bytesAt m p 4 = wordBytes x) :
    m.readW p 32 = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have number := congrArg VG.Proof.X25519.leNum bytes
  change VG.Proof.X25519.leNum (Spec.X25519.bytesAt m p 4) = _ at number
  rw [VG.Proof.X25519.leNum_bytesAt_32bit, decode_wordBytes x fit] at number
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit] using number

private theorem slice_bytes {s : State} {p : BitVec 32} {blob : List Byte} {d n : Nat}
    (fit : p.toNat + blob.length ≤ 2 ^ 32) (part : d + n ≤ blob.length) (positive : 0 < n)
    (bytes : Spec.Rsa.bytesAt s.mem (State.addr p) blob.length = blob) :
    Spec.Rsa.bytesAt s.mem (State.addr (p + BitVec.ofNat 32 d)) n = (blob.drop d).take n := by
  rw [VG.Arm.addr_add (by omega)]
  rw [← VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p) part, bytes]

 theorem recordOfBytes (s : State) (p : BitVec 32) (g : Group)
    (positive : 0 < g.len) (lenFit : g.len < 2 ^ 32) (bitsFit : g.bits < 2 ^ 32)
    (fit : p.toNat + g.bytes.length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr p) g.bytes.length)
    (bytes : Spec.Rsa.bytesAt s.mem (State.addr p) g.bytes.length = g.bytes) : RecordAt p g s := by
  have length := groupBytes_length g
  have wordLength (x : Nat) : (wordBytes x).length = 4 := by simp only [wordBytes, List.length_map, List.length_range]
  have domainLength : g.domain.length = 3 * g.len := by
    have h := groupBytes_length g
    simp only [Group.bytes, List.length_append, wordLength] at h
    omega
  have headLen : (g.bytes.drop 0).take 4 = wordBytes g.len := by
    simp only [Group.bytes, List.drop_zero, List.append_assoc, List.take_left', wordLength]
  have headBits : (g.bytes.drop 4).take 4 = wordBytes g.bits := by
    rw [Group.bytes, List.append_assoc, ← wordLength g.len, List.drop_left]
    simp only [List.take_left', wordLength]
  have domain : (g.bytes.drop 8).take (3 * g.len) = g.domain := by
    rw [Group.bytes, show 8 = (wordBytes g.len ++ wordBytes g.bits).length by simp only [List.length_append, wordLength], List.drop_left]
    rw [← domainLength, List.take_length]
  have reads (d n : Nat) (part : d + n ≤ g.bytes.length) (pos : 0 < n) :
      InRegions (s.rd ++ s.wr) (State.addr (p + BitVec.ofNat 32 d)) n := by
    rw [VG.Arm.addr_add (by omega)]
    exact VG.CallLay.inRegions_sub read part (by omega)
  refine ⟨positive, lenFit, bitsFit, by omega, ?_, reads 4 4 (by omega) (by decide), ?_, ?_,
    reads 8 (3 * g.len) (by omega) (by omega), ?_⟩
  · simpa only [BitVec.add_zero] using reads 0 4 (by omega) (by decide)
  · apply read_wordBytes lenFit
    have h := slice_bytes fit (d := 0) (n := 4) (by omega) (by decide) bytes
    simpa only [BitVec.add_zero, headLen] using h
  · exact read_wordBytes bitsFit ((slice_bytes fit (d := 4) (n := 4) (by omega) (by decide) bytes).trans headBits)
  · exact (slice_bytes fit (d := 8) (n := 3 * g.len) (by omega) (by omega) bytes).trans domain


theorem tableOfBytes (s : State) (p : BitVec 32) (gs : List Group) {regions : List Region}
    (fit : p.toNat + (gs.flatMap Group.bytes).length ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (State.addr p) (gs.flatMap Group.bytes).length)
    (bytes : Spec.Rsa.bytesAt s.mem (State.addr p) (gs.flatMap Group.bytes).length = gs.flatMap Group.bytes)
    (valid : ∀ g ∈ gs, 0 < g.len ∧ g.len < 2 ^ 32 ∧ g.bits < 2 ^ 32)
    (safe : ∀ r ∈ regions, (⟨State.addr p, (gs.flatMap Group.bytes).length⟩ : Region).Disjoint r) :
    TableAt p gs s ∧ TableSafe p gs regions := by
  induction gs generalizing p with
  | nil => exact ⟨trivial, trivial⟩
  | cons g gs ih =>
    have vg := valid g (by simp)
    have length := groupBytes_length g
    have blob : ((g :: gs).flatMap Group.bytes) = g.bytes ++ gs.flatMap Group.bytes := rfl
    have total : ((g :: gs).flatMap Group.bytes).length = g.bytes.length + (gs.flatMap Group.bytes).length := by
      rw [blob, List.length_append]
    have nowrap : (State.addr p).toNat + ((g :: gs).flatMap Group.bytes).length ≤ 2 ^ 32 := by
      simpa only [State.addr, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans p.isLt (by decide : 2 ^ 32 < 2 ^ 64))] using fit
    have hread := VG.CallLay.inRegions_sub read (off := 0) (l := g.bytes.length)
      (by rw [total]; omega) (by omega)
    have hbytes := slice_bytes fit (d := 0) (n := g.bytes.length) (by rw [total]; omega) (by omega) bytes
    simp only [BitVec.add_zero, List.drop_zero, blob, List.take_left] at hread hbytes
    have head := recordOfBytes s p g vg.1 vg.2.1 vg.2.2 (by rw [total] at fit; omega) hread hbytes
    have sub (d n : Nat) (part : d + n ≤ ((g :: gs).flatMap Group.bytes).length) (pos : 0 < n) :
        (⟨State.addr (p + BitVec.ofNat 32 d), n⟩ : Region).Sub
          ⟨State.addr p, ((g :: gs).flatMap Group.bytes).length⟩ := by
      rw [VG.Arm.addr_add (by omega)]
      exact Offset.sub_base _ part
    have hs : RecordSafe p g regions := by
      intro r hr
      have h0 := (safe r hr).sub_left (sub 0 4 (by rw [total]; omega) (by decide))
      simp only [BitVec.add_zero] at h0
      exact ⟨h0, (safe r hr).sub_left (sub 4 4 (by rw [total]; omega) (by decide)),
        (safe r hr).sub_left (sub 8 (3 * g.len) (by rw [total]; omega) (by omega))⟩
    by_cases empty : gs = []
    · subst gs
      exact ⟨⟨head, trivial⟩, ⟨hs, trivial⟩⟩
    have tailPositive : 0 < (gs.flatMap Group.bytes).length := by
      cases gs with
      | nil => exact False.elim (empty rfl)
      | cons first rest =>
        have vf := valid first (by simp)
        simp only [List.flatMap_cons, List.length_append, groupBytes_length]
        omega
    have stepFit : p.toNat + (8 + 3 * g.len) < 2 ^ 32 := by rw [total] at fit; omega
    have stepNat : (p + BitVec.ofNat 32 (8 + 3 * g.len)).toNat = p.toNat + (8 + 3 * g.len) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := 8 + 3 * g.len) (by omega), Nat.mod_eq_of_lt stepFit]
    have tfit : (p + BitVec.ofNat 32 (8 + 3 * g.len)).toNat + (gs.flatMap Group.bytes).length ≤ 2 ^ 32 := by
      rw [stepNat]; rw [total] at fit; omega
    have tread := VG.CallLay.inRegions_sub read (off := 8 + 3 * g.len)
      (l := (gs.flatMap Group.bytes).length) (by rw [total]; omega) (by omega)
    rw [← VG.Arm.addr_add stepFit] at tread
    have tbytes := slice_bytes fit (d := 8 + 3 * g.len) (n := (gs.flatMap Group.bytes).length)
      (by rw [total]; omega) tailPositive bytes
    rw [blob, ← length, List.drop_left, List.take_length] at tbytes
    rw [length] at tbytes
    have tsafe : ∀ r ∈ regions, (⟨State.addr (p + BitVec.ofNat 32 (8 + 3 * g.len)),
        (gs.flatMap Group.bytes).length⟩ : Region).Disjoint r := by
      intro r hr
      exact (safe r hr).sub_left (sub _ _ (by rw [total]; omega) tailPositive)
    obtain ⟨tail, safeTail⟩ := ih _ tfit tread tbytes (fun h hh => valid h (by simp [hh])) tsafe
    exact ⟨⟨head, tail⟩, ⟨hs, safeTail⟩⟩

end VG.Proof.Ffdh.Arm.VettedGroups
