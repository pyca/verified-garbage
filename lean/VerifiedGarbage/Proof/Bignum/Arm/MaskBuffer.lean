module

public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! # Branchless masking of an ordinary RSA output buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

theorem maskCtx_of_region (s : State) {dst : BitVec 32} {n : Nat}
    (hn : n < 2 ^ 32) (fit : dst.toNat + n ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr dst) n) : MaskCtx s dst n := by
  have writable (i : Nat) (hi : i < n) :
      InRegions s.wr (State.addr (dst + BitVec.ofNat 32 i)) 1 := by
    rw [addr_add (by omega)]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)⟩
  refine ⟨hn, ?_, writable, ?_⟩
  · intro i hi
    obtain ⟨r, hr, hc⟩ := writable i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro i hi j hj he
    rw [addr_add (by omega), addr_add (by omega)] at he
    have eq := congrArg (fun a => (a - State.addr dst).toNat) he
    simpa only [Mem.sub_ofNat_toNat _ (by omega : i < 2 ^ 64),
      Mem.sub_ofNat_toNat _ (by omega : j < 2 ^ 64)] using eq

theorem maskBuffer_ok (s : State) {dst : BitVec 32} {n : Nat}
    (hn : 0 < n) (hn' : n < 2 ^ 32) (fit : dst.toNat + n ≤ 2 ^ 32)
    (write : InRegions s.wr (State.addr dst) n)
    (ptr : s.gpr .r0 = dst) (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa maskBytes s fun t =>
      Spec.Rsa.bytesAt t.mem (State.addr dst) n =
        (Spec.Rsa.bytesAt s.mem (State.addr dst) n).map (· &&& (s.gpr .r2).setWidth 8) ∧
      Frame [⟨State.addr dst, n⟩] s.mem t.mem ∧ Rest [.r0, .r1, .lr] s t := by
  refine WP.mono (maskBytes_ok s (maskCtx_of_region s hn' fit write) hn ptr count) ?_
  intro t inv
  refine ⟨?_, ?_, inv.rest⟩
  · simp only [Spec.Rsa.bytesAt, List.map_map]
    apply List.map_congr_left
    intro j hj
    have hj' : j < n := List.mem_range.mp hj
    have value := inv.masked j hj'
    rw [addr_add (by omega)] at value
    exact value
  · intro a ha
    apply inv.outside a
    intro j hj he
    apply ha ⟨State.addr dst, n⟩ (by simp)
    rw [he, addr_add (by omega)]
    exact Offset.contains_base _ (by omega) (by omega)

end VG.Proof.Bignum.Arm
