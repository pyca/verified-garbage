module
public import VerifiedGarbage.Proof.Bignum.X86.ExponentScanState

import VerifiedGarbage.Proof.Bignum.X86.ExponentLoopTiming
import VerifiedGarbage.Proof.Bignum.X86.ExponentScan
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

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
          ⟨0, by omega, positive, Si, Ti⟩ El Fl).1
        rw [(Init _ _ _ _ _ _ trivial Ei Fi).1, L]
  have Test : RelCT isa (VG.X86.Taint.Agree (τr [.ebx, .edx])) exponentTest (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (τr [.ebx, .edx]) (fun _ _ h => h)
      (hc := VG.Taint.hintOf taint (τr [.ebx, .edx]) exponentTest)
    rfl
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
