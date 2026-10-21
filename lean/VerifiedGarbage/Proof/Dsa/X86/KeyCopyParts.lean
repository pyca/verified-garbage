module

import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyFrame
import VerifiedGarbage.Proof.Dsa.X86.KeyCopyPart
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame

/-! # Consecutive masked copies form the packed private key -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def keyPartsSize (parts : List (Pointer × Nat)) : Nat := (parts.map Prod.snd).sum

def keyPartsBytes (s : State) (base : Addr) (parts : List (Pointer × Nat)) : List Byte :=
  parts.flatMap fun part => Spec.Rsa.bytesAt s.mem ((pointerValue base s part.1).setWidth 64) part.2

theorem keyPartsBytes_keep {s t : State} {base out : Addr} {size total : Nat}
    {parts : List (Pointer × Nat)}
    (R : ∀ part ∈ parts, KeyPartReady s base out total part)
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (O : Outside out 0 total s.mem t.mem) (A : Region.Disjoint ⟨base, size⟩ ⟨out, total⟩)
    (K : Keeps [.eax, .ecx, .edx, .esi] s t) :
    keyPartsBytes t base parts = keyPartsBytes s base parts := by
  induction parts with
  | nil => rfl
  | cons part rest ih =>
    simp only [keyPartsBytes, List.flatMap_cons]
    rw [(R part List.mem_cons_self).bytes hs hz O A K]
    exact congrArg _ (ih (fun p hp => R p (List.mem_cons_of_mem _ hp)))

theorem keyCopyParts_ok (parts : List (Pointer × Nat)) {s : State} {base : Addr}
    {size : Nat} {out : BitVec 32} {mask : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (R : ∀ part ∈ parts, KeyPartReady s base (out.setWidth 64) (keyPartsSize parts) part)
    (ho : out.toNat + keyPartsSize parts ≤ 2 ^ 32) (small : keyPartsSize parts < 2 ^ 32)
    (A : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, keyPartsSize parts⟩)
    (hd : s.gpr .edx = out) (hm : s.gpr .ebx = mask)
    (write : ∀ i < keyPartsSize parts, InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa (Generate.copyParts parts) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) (keyPartsSize parts) =
        (keyPartsBytes s base parts).map (fun b => (b.setWidth 32 &&& mask).setWidth 8) ∧
      t.gpr .edx = out + BitVec.ofNat 32 (keyPartsSize parts) ∧ t.gpr .ebx = mask ∧
      Outside (out.setWidth 64) 0 (keyPartsSize parts) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .esi] s t := by
  induction parts generalizing s out with
  | nil =>
    exact WP.block_nil ⟨rfl, by simpa [keyPartsSize] using hd, hm,
      Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | cons part rest ih =>
    obtain ⟨input, len⟩ := part
    have total : keyPartsSize ((input, len) :: rest) = len + keyPartsSize rest := rfl
    have H := R (input, len) List.mem_cons_self
    have lenBound : len ≤ keyPartsSize ((input, len) :: rest) := by rw [total]; omega
    have firstSub : Region.Sub ⟨out.setWidth 64, len⟩
        ⟨out.setWidth 64, keyPartsSize ((input, len) :: rest)⟩ := by
      simpa only [BitVec.add_zero] using Offset.sub_base (out.setWidth 64) (d := 0) (by omega : 0 + len ≤ _)
    have H1 : KeyPartReady s base (out.setWidth 64) len (input, len) :=
      ⟨H.positive, H.fits, H.read, H.apart.sub_right firstSub⟩
    unfold Generate.copyParts
    refine WP.seq (WP.mono (keyCopyPart_ok hs hz H1
      (by omega)
      (by omega) hd hm (fun i hi => write i (by omega))) fun u ⟨V1, D1, M1, O1, K1⟩ => ?_)
    have O1' : Outside (out.setWidth 64) 0 (keyPartsSize ((input, len) :: rest)) s.mem u.mem :=
      O1.mono (Nat.le_refl _) (by omega)
    have Rrest (part : Pointer × Nat) (member : part ∈ rest) :=
      R part (List.mem_cons_of_mem _ member)
    cases rest with
    | nil =>
      refine WP.block_nil ⟨?_, ?_, M1, O1', K1⟩
      · simpa only [keyPartsSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          Nat.add_zero, keyPartsBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil] using V1
      · simpa only [keyPartsSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] using D1
    | cons next remaining =>
      let rest := next :: remaining
      have restEq : keyPartsSize rest = keyPartsSize (next :: remaining) := rfl
      have positive : 0 < keyPartsSize rest := by
        have H := (Rrest next List.mem_cons_self).positive
        change 0 < next.2 + keyPartsSize remaining
        omega
      let nextOut := out + BitVec.ofNat 32 len
      have nextAddr : nextOut.setWidth 64 = off (out.setWidth 64) len :=
        addr_eq (by rw [total] at ho; change out.toNat + (len + keyPartsSize rest) ≤ _ at ho; omega)
      have nextNat : nextOut.toNat = out.toNat + len := by
        have B : out.toNat + len < 2 ^ 32 := by
          rw [total] at ho
          change out.toNat + (len + keyPartsSize rest) ≤ _ at ho
          omega
        simp only [nextOut, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : len < 2 ^ 32), Nat.mod_eq_of_lt B]
      have tailSub : Region.Sub ⟨nextOut.setWidth 64, keyPartsSize rest⟩
          ⟨out.setWidth 64, keyPartsSize ((input, len) :: rest)⟩ := by
        rw [nextAddr]
        exact Offset.sub_base _ (by rw [total])
      have Rt : ∀ part ∈ rest, KeyPartReady u base (nextOut.setWidth 64) (keyPartsSize rest) part := by
        intro part member
        have B := (Rrest part member).keep hs hz O1' A K1
        exact ⟨B.positive, B.fits, B.read, B.apart.sub_right tailSub⟩
      refine WP.mono (ih (hs.of_keeps K1 (by decide)) Rt
        (by rw [nextNat]; rw [total] at ho; omega) (by rw [total] at small; omega) (A.sub_right tailSub) D1 M1
        (by
          intro i hi
          rw [K1.2.2, nextAddr, off, off, Offset.add_add]
          exact write (len + i) (by rw [total]; omega))) fun t ⟨V2, D2, M2, O2, K2⟩ => ?_
      have B : keyPartsBytes u base rest = keyPartsBytes s base rest :=
        keyPartsBytes_keep Rrest hs hz O1' A K1
      have O2a : Outside (off (out.setWidth 64) len) 0 (keyPartsSize rest) u.mem t.mem := by
        simpa only [nextAddr] using O2
      have first : Spec.Rsa.bytesAt t.mem (out.setWidth 64) len =
          Spec.Rsa.bytesAt u.mem (out.setWidth 64) len :=
        external_bytes O2a (Offset.base_disjoint _ (by omega) (by omega)) (by omega)
      refine ⟨?_, ?_, M2, ?_, K1.trans K2⟩
      · rw [total, bytesAt_split, first, V1]
        change _ ++ Spec.Rsa.bytesAt t.mem (off (out.setWidth 64) len) (keyPartsSize rest) = _
        rw [← nextAddr, V2, B]
        simp only [rest, keyPartsBytes, List.flatMap_cons, List.map_append]
      · rw [D2]
        simp only [nextOut, total, BitVec.ofNat_add, BitVec.add_assoc]
      · have F1 : OutputFrame base (out.setWidth 64) 0 len s.mem u.mem :=
          fun a _ h => O1 a (.inr (by simpa using h))
        have F2 : OutputFrame base (off (out.setWidth 64) len) 0 (keyPartsSize rest) u.mem t.mem :=
          fun a _ h => O2a a (.inr (by simpa using h))
        have F := F1.join F2 (by rw [total] at ho; omega)
        intro a ha
        rcases ha with ha | ha
        · omega
        · exact F a (Nat.zero_le _) (by rw [total] at ha; simpa only [Nat.zero_add, restEq] using ha)

end VG.Proof.Dsa.X86
