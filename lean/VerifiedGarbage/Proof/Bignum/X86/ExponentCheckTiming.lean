module

import VerifiedGarbage.Proof.Bignum.X86.ExponentScan
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Impl.Bignum.X86.ExponentCheck
public import VerifiedGarbage.Proof.Bignum.ExponentCheckMath
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
import VerifiedGarbage.Proof.Bignum.X86.ExponentByte
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State
import VerifiedGarbage.Proof.Bignum.X86.ExponentAccumulate
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Bignum.X86.ExponentLoopTiming`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.ExponentScanState`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.ExponentConsumeTiming`, which this module and modules that import it used -/

section

/-! # Public exponent bytes determine the scanner's saturation branches -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86

theorem exponentAccumulate_trace :
    RelCT isa (VG.X86.Taint.Agree (τr [.esi])) (.block exponentAccumulate) (fun _ _ => True) := by
  apply RelCT.taint (A := taint) (τr [.esi]) (fun _ _ h => h) (hc := .block [])
  rfl

theorem exponentSaturate_trace :
    RelCT isa (fun s t => s.zf = t.zf)
      (.ite .e (.block []) (.block [.mov .edx (.imm 2)])) (fun _ _ => True) := by
  apply VG.RelCT.ite (M := isa) (c := .e) (P := fun s t => s.zf = t.zf) (fun _ _ h => h)
  · exact VG.RelCT.block_nil (fun _ _ _ => trivial)
  · apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl

theorem exponentConsume_trace {s t : State}
    (ptr : s.gpr .esi = t.gpr .esi) (low : s.gpr .ebx = t.gpr .ebx)
    (high : s.gpr .edx = t.gpr .edx)
    (readS : InRegions (s.rd ++ s.wr) (s.ea ⟨.esi, 0⟩) 1)
    (readT : InRegions (t.rd ++ t.wr) (t.ea ⟨.esi, 0⟩) 1)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa exponentConsume s tr sf) (F : Exec isa exponentConsume t ur tf) : tr = ur := by
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      obtain ⟨_, _, Zs, _, _⟩ := wp_result (exponentAccumulate_ok s rfl readS) E1
      obtain ⟨_, _, Zt, _, _⟩ := wp_result (exponentAccumulate_ok t rfl readT) F1
      have T1 := (exponentAccumulate_trace _ _ _ _ _ _
        (agree_regs (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact ptr)) E1 F1).1
      have T2 := (exponentSaturate_trace _ _ _ _ _ _
        (by dsimp only; rw [Zs, Zt, low, high]) E2 F2).1
      rw [T1, T2]

end VG.Proof.Bignum.X86

end

end

/-! # A common public prefix determines each exponent-scanner iteration -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure ExponentState (ep : BitVec 32) (eb : List Byte) (j k : Nat) (s : State) : Prop where
  ptr : s.gpr .esi = ep + BitVec.ofNat 32 j
  count : s.gpr .ecx = BitVec.ofNat 32 k
  low : s.gpr .ebx = BitVec.ofNat 32 (pre eb j % 2 ^ 32)
  high : s.gpr .edx = BitVec.ofNat 32 (exponentHigh (pre eb j))
  read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length
  bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i]

theorem ExponentState.current {ep : BitVec 32} {eb : List Byte} {j k : Nat} {s : State}
    (H : ExponentState ep eb j k s) (fit : ep.toNat + eb.length ≤ 2 ^ 32) (hj : j < eb.length) :
    InRegions (s.rd ++ s.wr) (s.ea ⟨.esi, 0⟩) 1 ∧
      s.mem (byteAddr (ep + BitVec.ofNat 32 j)) = eb[j] := by
  have address : byteAddr (ep + BitVec.ofNat 32 j) = byteAddr ep + BitVec.ofNat 64 j :=
    byteAddr_add (by omega_using [fit, hj])
  have ea : s.ea ⟨.esi, 0⟩ = byteAddr (ep + BitVec.ofNat 32 j) := by
    simp only [State.ea, H.ptr, BitVec.add_zero]; rfl
  refine ⟨?_, ?_⟩
  · rw [ea, address]
    exact CallLay.inRegions_sub H.read (by omega_using [hj]) (by omega_using [fit])
  · rw [address]; exact H.bytes j hj

theorem ExponentState.step {ep : BitVec 32} {eb : List Byte} {j k : Nat} {s : State}
    (H : ExponentState ep eb j k s) (fit : ep.toNat + eb.length ≤ 2 ^ 32)
    (hj : j < eb.length) (hk : 0 < k) (hk' : k < 2 ^ 32) :
    WP isa exponentByte s fun t => ExponentState ep eb (j + 1) (k - 1) t ∧
      t.zf = some (decide (k = 1)) := by
  obtain ⟨Read, Byte⟩ := H.current fit hj
  have ea : s.ea ⟨.esi, 0⟩ = byteAddr (ep + BitVec.ofNat 32 j) := by
    simp only [State.ea, H.ptr, BitVec.add_zero]; rfl
  rw [ea] at Read
  refine WP.mono (exponentByte_ok s hk hk' H.ptr H.count Read Byte H.low H.high) ?_
  intro t ⟨Lo, Hi, P, C, Z, M, K⟩
  have next : 256 * pre eb j + (eb[j]).toNat = pre eb (j + 1) := by
    rw [pre_succ eb hj, Nat.mul_comm]
  rw [next] at Lo Hi
  refine ⟨⟨?_, C, Lo, Hi, ?_, ?_⟩, Z⟩
  · rw [P]
    change ep + BitVec.ofNat 32 j + BitVec.ofNat 32 1 = _
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [K.2.1, K.2.2]; exact H.read
  · rw [M]; exact H.bytes

theorem exponentByte_trace {s t : State} {ep : BitVec 32} {eb : List Byte} {j k : Nat}
    (S : ExponentState ep eb j k s) (T : ExponentState ep eb j k t)
    (fit : ep.toNat + eb.length ≤ 2 ^ 32) (hj : j < eb.length)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa exponentByte s tr sf) (F : Exec isa exponentByte t ur tf) : tr = ur := by
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := exponentConsume_trace (S.ptr.trans T.ptr.symm) (S.low.trans T.low.symm)
        (S.high.trans T.high.symm) (S.current fit hj).1 (T.current fit hj).1 E1 F1
      have Advance : RelCT isa (fun _ _ => True) (.block exponentAdvance) (fun _ _ => True) := by
        apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
        rfl
      have T2 := (Advance _ _ _ _ _ _ trivial E2 F2).1
      rw [T1, T2]

end VG.Proof.Bignum.X86

end

end

/-! # A public byte sequence fixes the complete exponent-scan trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86

theorem exponentLoop_relCT (ep : BitVec 32) (eb : List Byte)
    (fit : ep.toNat + eb.length ≤ 2 ^ 32) (countFit : eb.length < 2 ^ 32)
    (k : Nat) :
    RelCT isa (fun s t => ∃ j, j + k = eb.length ∧ 0 < k ∧
      ExponentState ep eb j k s ∧ ExponentState ep eb j k t)
      (.loop exponentByte .ne) (fun _ _ => True) := by
  apply VG.RelCT.loop (M := isa)
    (fun k s t => ∃ j, j + k = eb.length ∧ 0 < k ∧
      ExponentState ep eb j k s ∧ ExponentState ep eb j k t) ?_ k
  intro n s t tr ur sf tf ⟨j, Eq, Pos, S, T⟩ E F
  have hj : j < eb.length := by omega_using [Eq, Pos]
  have hn : n < 2 ^ 32 := by omega_using [countFit, Eq]
  obtain ⟨S', Zs⟩ := wp_result (S.step fit hj Pos hn) E
  obtain ⟨T', Zt⟩ := wp_result (T.step fit hj Pos hn) F
  refine ⟨exponentByte_trace S T fit hj E F, ?_, fun _ => trivial, ?_⟩
  · change sf.zf.map not = tf.zf.map not
    rw [Zs, Zt]
  · intro Continue
    have ne : n ≠ 1 := by
      intro h
      change sf.zf.map not = some true at Continue
      simp only [Zs, h, decide_true, Option.map_some, Bool.not_true] at Continue
      cases Continue
    exact ⟨n - 1, by omega_using [Pos], j + 1, by omega_using [Eq, Pos], by omega_using [Pos, ne], S', T'⟩

end VG.Proof.Bignum.X86

end

end

/-! # Exponent-validation timing depends only on the public exponent bytes -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem exponentInit_ok {s : State} {ep : BitVec 32} {eb : List Byte}
    (ptr : s.gpr .esi = ep) (count : s.gpr .ecx = BitVec.ofNat 32 eb.length)
    (read : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (bytes : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i]) :
    WP isa (.block [.mov .ebx (.imm 0), .mov .edx (.imm 0)]) s
      (ExponentState ep eb 0 eb.length) := by
  refine wp_movS rfl fun u A _ => ?_
  refine wp_movS rfl fun t B _ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [BitVec.add_zero] using (B.other .esi (by decide)).trans ((A.other .esi (by decide)).trans ptr)
  · rw [B.other .ecx (by decide), A.other .ecx (by decide)]; exact count
  · rw [B.other .ebx (by decide), A.gpr, pre_zero]; rfl
  · rw [B.gpr, pre_zero]; rfl
  · rw [B.rd, B.wr, A.rd, A.wr]; exact read
  · rw [B.mem, A.mem]; exact bytes

theorem exponentCheck_trace {s t : State} {ep : BitVec 32} {eb : List Byte}
    (positive : 0 < eb.length) (countFit : eb.length < 2 ^ 32)
    (fit : ep.toNat + eb.length ≤ 2 ^ 32)
    (readS : InRegions (s.rd ++ s.wr) (byteAddr ep) eb.length)
    (readT : InRegions (t.rd ++ t.wr) (byteAddr ep) eb.length)
    (bytesS : ∀ i (hi : i < eb.length), s.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (bytesT : ∀ i (hi : i < eb.length), t.mem (byteAddr ep + BitVec.ofNat 64 i) = eb[i])
    (ptrS : s.gpr .esi = ep) (ptrT : t.gpr .esi = ep)
    (countS : s.gpr .ecx = BitVec.ofNat 32 eb.length)
    (countT : t.gpr .ecx = BitVec.ofNat 32 eb.length)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa exponentCheck s tr sf) (F : Exec isa exponentCheck t ur tf) : tr = ur := by
  have Init : RelCT isa (fun _ _ => True) (.block [.mov .ebx (.imm 0), .mov .edx (.imm 0)])
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs (by simp)) (hc := .block [])
    rfl
  have Scan : ∀ {tr ur : List Leak} {sf tf : State},
      Exec isa exponentScan s tr sf → Exec isa exponentScan t ur tf → tr = ur := by
    intro tr ur sf tf Es Et
    cases Es with
    | seq Ei El =>
      cases Et with
      | seq Fi Fl =>
        have Si := wp_result (exponentInit_ok ptrS countS readS bytesS) Ei
        have Ti := wp_result (exponentInit_ok ptrT countT readT bytesT) Fi
        have L := (exponentLoop_relCT ep eb fit countFit eb.length _ _ _ _ _ _
          ⟨0, by omega_using [], positive, Si, Ti⟩ El Fl).1
        rw [(Init _ _ _ _ _ _ trivial Ei Fi).1, L]
  have Test : RelCT isa (VG.X86.Taint.Agree (τr [.ebx, .edx])) exponentTest (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.ebx, .edx]) (fun _ _ h => h)
      (hc := VG.Taint.hintOf taint (τr [.ebx, .edx]) exponentTest)
    kernel_rfl
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      obtain ⟨LoS, HiS, _, _⟩ := wp_result (exponentScan_ok s positive countFit fit readS bytesS ptrS countS) E1
      obtain ⟨LoT, HiT, _, _⟩ := wp_result (exponentScan_ok t positive countFit fit readT bytesT ptrT countT) F1
      have T2 := (Test _ _ _ _ _ _ (agree_regs (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact LoS.trans LoT.symm
        · exact HiS.trans HiT.symm)) E2 F2).1
      have T1 := Scan E1 F1
      rw [T1, T2]

end VG.Proof.Bignum.X86
