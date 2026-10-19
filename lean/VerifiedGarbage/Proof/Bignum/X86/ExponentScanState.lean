module

public import VerifiedGarbage.Proof.Bignum.X86.ExponentScan
public import VerifiedGarbage.Proof.Bignum.X86.ExponentConsumeTiming

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
    byteAddr_add (by omega)
  have ea : s.ea ⟨.esi, 0⟩ = byteAddr (ep + BitVec.ofNat 32 j) := by
    simp only [State.ea, H.ptr, BitVec.add_zero]; rfl
  refine ⟨?_, ?_⟩
  · rw [ea, address]
    exact CallLay.inRegions_sub H.read (by omega) (by omega)
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
