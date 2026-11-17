module

import VerifiedGarbage.Proof.Dsa.OutputBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.KeyCopyFrame
import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Dsa.X86.RandomScan
import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Spec.Rsa.Contract

/-! ### `Dsa.X86.KeyCopyPart`, which this module and modules that import it used -/

section

/-! # Copy one component from its saved pointer -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/KeyCopyStep.lean`, which only this module imported.
section

/-! # A masked byte-copy step for the packed private key -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86

structure KeyCopyInv (src out : BitVec 32) (len i : Nat) (mask : BitVec 32)
    (s t : State) : Prop where
  source : t.gpr .esi = src + BitVec.ofNat 32 i
  dest : t.gpr .edx = out + BitVec.ofNat 32 i
  counter : t.gpr .ecx = BitVec.ofNat 32 (len - i)
  maskReg : t.gpr .ebx = mask
  bytes : ∀ j < i, t.mem (off (out.setWidth 64) j) =
    (((s.mem (off (src.setWidth 64) j)).setWidth 32) &&& mask).setWidth 8
  mem : Outside (out.setWidth 64) 0 len s.mem t.mem
  keeps : Keeps [.eax, .ecx, .edx, .esi] s t

theorem keyCopyStep_ok {s t : State} {src out : BitVec 32} {len i : Nat} {mask : BitVec 32}
    (hi : i < len) (hl : len < 2 ^ 32)
    (hs : src.toNat + len ≤ 2 ^ 32) (ho : out.toNat + len ≤ 2 ^ 32)
    (apart : Region.Disjoint ⟨src.setWidth 64, len⟩ ⟨out.setWidth 64, len⟩)
    (read : InRegions (t.rd ++ t.wr) (off (src.setWidth 64) i) 1)
    (write : InRegions t.wr (off (out.setWidth 64) i) 1)
    (I : KeyCopyInv src out len i mask s t) :
    WP isa (.block Generate.copyMaskedStep) t fun u =>
      KeyCopyInv src out len (i + 1) mask s u ∧ u.zf = some (decide (i + 1 = len)) := by
  have input : t.mem (off (src.setWidth 64) i) = s.mem (off (src.setWidth 64) i) := by
    apply I.mem
    have H := apart _ (Offset.contains_base _ (by omega) (by omega : i < 2 ^ 64))
    change ¬ (ofs (out.setWidth 64) (off (src.setWidth 64) i) + 1 ≤ len) at H
    omega
  have source : t.ea (at_ .esi 0) = off (src.setWidth 64) i := by
    change (t.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, I.source]
    exact addr_eq (by omega)
  unfold Generate.copyMaskedStep
  refine wp_load8 source read fun a ta _ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun b ab => ?_
  have dest : b.ea (at_ .edx 0) = off (out.setWidth 64) i := by
    change (b.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
    rw [BitVec.add_zero, ab.other _ (by decide), ta.other _ (by decide), I.dest]
    exact addr_eq (by omega)
  refine VG.Proof.Weierstrass.X86.wp_store8' dest
    (by rw [ab.wr, ta.wr]; exact write) fun c bc => ?_
  refine wp_addi fun d cd => wp_addi fun e de => wp_subi fun u eu _ Zu => WP.block_nil ?_
  have byte : (b.gpr .eax).setWidth 8 =
      ((s.mem (off (src.setWidth 64) i)).setWidth 32 &&& mask).setWidth 8 := by
    rw [ab.gpr, ta.gpr, ta.other _ (by decide), I.maskReg, input]
    rfl
  have mem : u.mem = t.mem.writeW (off (out.setWidth 64) i)
      (((s.mem (off (src.setWidth 64) i)).setWidth 32 &&& mask).setWidth 8) := by
    rw [eu.mem, de.mem, cd.mem, bc.mem, show Reg8.al.reg = Reg.eax from rfl, byte, ab.mem, ta.mem]
  have K : Keeps [.eax, .ecx, .edx, .esi] t u :=
    (((((ta.keeps.mono (by decide)).trans (ab.keeps.mono (by decide))).trans (bc.keeps _)).trans
      (cd.keeps.mono (by decide))).trans (de.keeps.mono (by decide))).trans (eu.keeps.mono (by decide))
  refine ⟨⟨?_, ?_, ?_, (K.1 _ (by decide)).trans I.maskReg, ?_, ?_, I.keeps.trans K⟩, ?_⟩
  · rw [eu.other _ (by decide), de.other _ (by decide), cd.gpr, bc.gpr,
      ab.other _ (by decide), ta.other _ (by decide), I.source, Offset.add_ofNat_add_one]
  · rw [eu.other _ (by decide), de.gpr, cd.other _ (by decide), bc.gpr,
      ab.other _ (by decide), ta.other _ (by decide), I.dest, Offset.add_ofNat_add_one]
  · rw [eu.gpr, de.other _ (by decide), cd.other _ (by decide), bc.gpr,
      ab.other _ (by decide), ta.other _ (by decide), I.counter,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]
    rfl
  · intro j hj
    rw [mem]
    by_cases eq : j = i
    · subst j
      exact writeW8_self _ _ _
    · rw [writeW8_outside _ _ _ (by omega) _ (by rw [ofs_off0 _ (by omega)]; omega)]
      exact I.bytes j (by omega)
  · rw [mem]
    exact I.mem.trans ((writeW8_outside _ _ _ (by omega)).mono (Nat.zero_le _) (by omega))
  · rw [Zu, de.other _ (by decide), cd.other _ (by decide), bc.gpr,
      ab.other _ (by decide), ta.other _ (by decide), I.counter,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_beq (by omega) (by decide)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/KeyCopy.lean`, which only this module imported.
section

/-! # A bounded masked copy of disjoint buffers -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem keyCopy_ok {s : State} {src out : BitVec 32} {len : Nat} {mask : BitVec 32}
    (hl : 0 < len) (h32 : len < 2 ^ 32)
    (hs : src.toNat + len ≤ 2 ^ 32) (ho : out.toNat + len ≤ 2 ^ 32)
    (apart : Region.Disjoint ⟨src.setWidth 64, len⟩ ⟨out.setWidth 64, len⟩)
    (hp : s.gpr .esi = src) (hd : s.gpr .edx = out)
    (hc : s.gpr .ecx = BitVec.ofNat 32 len) (hm : s.gpr .ebx = mask)
    (read : ∀ i, i < len → InRegions (s.rd ++ s.wr) (off (src.setWidth 64) i) 1)
    (write : ∀ i, i < len → InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa Generate.copyMasked s fun t =>
      KeyCopyInv src out len len mask s t := by
  have I0 : KeyCopyInv src out len 0 mask s s :=
    ⟨by simpa using hp, by simpa using hd, by simpa using hc, hm,
      by intro j hj; omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.loop (M := isa) (fun k t => ∃ i, k = len - i ∧ i < len ∧ KeyCopyInv src out len i mask s t)
    ?_ len s ⟨0, rfl, hl, I0⟩
  rintro k t ⟨i, rfl, hi, I⟩
  refine WP.mono (keyCopyStep_ok hi h32 hs ho apart
    (by rw [I.keeps.2.1, I.keeps.2.2]; exact read i hi)
    (by rw [I.keeps.2.2]; exact write i hi) I) fun u ⟨next, Z⟩ => ?_
  by_cases done : i + 1 = len
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, Z, done, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, len - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    simp only [eval, Z, decide_eq_false done, Option.map_some, Bool.not_false]

theorem KeyCopyInv.result {s t : State} {src out : BitVec 32} {len : Nat} {mask : BitVec 32}
    (I : KeyCopyInv src out len len mask s t) :
    Spec.Rsa.bytesAt t.mem (out.setWidth 64) len =
      (Spec.Rsa.bytesAt s.mem (src.setWidth 64) len).map
        (fun b => (b.setWidth 32 &&& mask).setWidth 8) := by
  simp only [Spec.Rsa.bytesAt, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact I.bytes i (List.mem_range.mp hi)

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.X86

theorem keyCopyPart_ok {s : State} {base : Addr} {size len : Nat} {out : BitVec 32}
    {input : VG.Impl.Dsa.Layout.Pointer} {mask : BitVec 32}
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (R : KeyPartReady s base (out.setWidth 64) len (input, len))
    (hl : len < 2 ^ 32) (ho : out.toNat + len ≤ 2 ^ 32)
    (hd : s.gpr .edx = out) (hm : s.gpr .ebx = mask)
    (write : ∀ i < len, InRegions s.wr (off (out.setWidth 64) i) 1) :
    WP isa (Generate.copyPart input len) s fun t =>
      Spec.Rsa.bytesAt t.mem (out.setWidth 64) len =
        (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) len).map
          (fun b => (b.setWidth 32 &&& mask).setWidth 8) ∧
      t.gpr .edx = out + BitVec.ofNat 32 len ∧
      t.gpr .ebx = mask ∧ Outside (out.setWidth 64) 0 len s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx, .esi] s t := by
  unfold Generate.copyPart
  refine WP.seq (WP.block_append (WP.mono (pointer_ok hs hz input) fun u ⟨P, K, O⟩ => ?_))
  refine wp_movS rfl fun v uv _ => WP.block_nil ?_
  have Ksv : Keeps [.eax, .ecx, .edx, .esi] s v :=
    (K.mono (by decide)).trans (uv.keeps.mono (by decide))
  have mem : v.mem = s.mem := uv.mem.trans O
  refine WP.mono (keyCopy_ok (mask := mask) R.positive hl R.fits ho R.apart
    (by rw [uv.other _ (by decide), P]) (by rw [uv.other _ (by decide), K.1 _ (by decide)]; exact hd)
    uv.gpr (by rw [Ksv.1 _ (by decide)]; exact hm)
    (by rw [Ksv.2.1, Ksv.2.2]; exact R.read)
    (by rw [Ksv.2.2]; exact write)) fun t I => ?_
  refine ⟨?_, I.dest, I.maskReg, ?_, Ksv.trans I.keeps⟩
  · rw [I.result, mem]
  · rw [← mem]; exact I.mem

end VG.Proof.Dsa.X86

end

end

/-! # Consecutive masked copies form the packed private key -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def keyPartsSize (parts : List (Pointer × Nat)) : Nat := (parts.map Prod.snd).sum

def keyPartsBytes (s : State) (base : Addr) (parts : List (Pointer × Nat)) : List Byte :=
  parts.flatMap fun part => Spec.Rsa.bytesAt s.mem ((pointerValue base s part.1).setWidth 64) part.2

theorem keyPartsBytes_nil (s : State) (base : Addr) : keyPartsBytes s base [] = [] := rfl

theorem keyPartsBytes_cons (s : State) (base : Addr) (part : Pointer × Nat) (rest : List (Pointer × Nat)) :
    keyPartsBytes s base (part :: rest) =
      Spec.Rsa.bytesAt s.mem ((pointerValue base s part.1).setWidth 64) part.2 ++ keyPartsBytes s base rest :=
  List.flatMap_cons

theorem keyPartsBytes_keep {s t : State} {base out : Addr} {size total : Nat}
    {parts : List (Pointer × Nat)}
    (R : ∀ part ∈ parts, KeyPartReady s base out total part)
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (O : Outside out 0 total s.mem t.mem) (A : Region.Disjoint ⟨base, size⟩ ⟨out, total⟩)
    (K : Keeps [.eax, .ecx, .edx, .esi] s t) :
    keyPartsBytes t base parts = keyPartsBytes s base parts := by
  induction parts with
  | nil => rw [keyPartsBytes_nil, keyPartsBytes_nil]
  | cons part rest ih =>
    rw [keyPartsBytes_cons, keyPartsBytes_cons, (R part List.mem_cons_self).bytes hs hz O A K,
      ih (fun p hp => R p (List.mem_cons_of_mem _ hp))]

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
    have lenBound : len ≤ keyPartsSize ((input, len) :: rest) := by rw [total]; omega_arith
    have firstSub : Region.Sub ⟨out.setWidth 64, len⟩
        ⟨out.setWidth 64, keyPartsSize ((input, len) :: rest)⟩ := by
      simpa only [BitVec.add_zero] using Offset.sub_base (out.setWidth 64) (d := 0) (by omega_arith : 0 + len ≤ _)
    have H1 : KeyPartReady s base (out.setWidth 64) len (input, len) :=
      ⟨H.positive, H.fits, H.read, H.apart.sub_right firstSub⟩
    unfold Generate.copyParts
    refine WP.seq (WP.mono (keyCopyPart_ok hs hz H1
      (by omega_arith)
      (by omega_arith) hd hm (fun i hi => write i (by omega_arith))) fun u ⟨V1, D1, M1, O1, K1⟩ => ?_)
    have O1' : Outside (out.setWidth 64) 0 (keyPartsSize ((input, len) :: rest)) s.mem u.mem :=
      O1.mono (Nat.le_refl _) (by omega_arith)
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
        omega_arith
      let nextOut := out + BitVec.ofNat 32 len
      have nextAddr : nextOut.setWidth 64 = off (out.setWidth 64) len :=
        addr_eq (by rw [total] at ho; change out.toNat + (len + keyPartsSize rest) ≤ _ at ho; omega_arith)
      have nextNat : nextOut.toNat = out.toNat + len := by
        have B : out.toNat + len < 2 ^ 32 := by
          rw [total] at ho
          change out.toNat + (len + keyPartsSize rest) ≤ _ at ho
          omega_arith
        simp only [nextOut, BitVec.toNat_add, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega_arith : len < 2 ^ 32), Nat.mod_eq_of_lt B]
      have tailSub : Region.Sub ⟨nextOut.setWidth 64, keyPartsSize rest⟩
          ⟨out.setWidth 64, keyPartsSize ((input, len) :: rest)⟩ := by
        rw [nextAddr]
        exact Offset.sub_base _ (by rw [total])
      have Rt : ∀ part ∈ rest, KeyPartReady u base (nextOut.setWidth 64) (keyPartsSize rest) part := by
        intro part member
        have B := (Rrest part member).keep hs hz O1' A K1
        exact ⟨B.positive, B.fits, B.read, B.apart.sub_right tailSub⟩
      refine WP.mono (ih (hs.of_keeps K1 (by decide)) Rt
        (by rw [nextNat]; rw [total] at ho; omega_arith) (by rw [total] at small; omega_arith) (A.sub_right tailSub) D1 M1
        (by
          intro i hi
          rw [K1.2.2, nextAddr, off, off, Offset.add_add]
          exact write (len + i) (by rw [total]; omega_arith))) fun t ⟨V2, D2, M2, O2, K2⟩ => ?_
      have B : keyPartsBytes u base rest = keyPartsBytes s base rest :=
        keyPartsBytes_keep Rrest hs hz O1' A K1
      have O2a : Outside (off (out.setWidth 64) len) 0 (keyPartsSize rest) u.mem t.mem := by
        simpa only [nextAddr] using O2
      have first : Spec.Rsa.bytesAt t.mem (out.setWidth 64) len =
          Spec.Rsa.bytesAt u.mem (out.setWidth 64) len :=
        external_bytes O2a (Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (by omega_arith)
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
        have F := F1.join F2 (by rw [total] at ho; omega_arith)
        intro a ha
        rcases ha with ha | ha
        · omega_arith
        · exact F a (Nat.zero_le _) (by rw [total] at ha; simpa only [Nat.zero_add, restEq] using ha)

end VG.Proof.Dsa.X86
