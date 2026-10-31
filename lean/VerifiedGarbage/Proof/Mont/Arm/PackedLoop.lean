module

public import VerifiedGarbage.Proof.Mont.Arm.PackedRound
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Arm.MontMath

/-! Induction over packed Montgomery rounds. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)
open VG.Proof.Bignum.Arm (round_step)

structure LoopInv (s0 : State) (base : Addr) (acc a b n m i : Nat) (s : State) : Prop where
  index : i ≤ n
  ptr : s.gpr .r1 = s0.gpr .r12 + BitVec.ofNat 32 (a + 4 * i)
  count : s.gpr .r9 = BitVec.ofNat 32 (n - i)
  outside : Outside base acc (4 * (n + 2)) s0.mem s.mem
  bound : val32 s.mem base acc (n + 2) < 2 * m
  value : 2 ^ (32 * i) * val32 s.mem base acc (n + 2) % m =
    val32 s0.mem base a i * val32 s0.mem base b n % m
  rest : Rest roundClob s0 s

 theorem loop_ok (u : Bool) {s : State} {base : Addr} {size acc a b n m : Nat} {M : Mod}
    (hs : Scr s base size) (hMn : 2 * M.n = n) (hn : 0 < n) (hn32 : n < 2 ^ 32)
    (pa : s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 a)
    (pb : s.gpr .r4 = s.gpr .r12 + BitVec.ofNat 32 b)
    (pc : s.gpr .r9 = BitVec.ofNat 32 n)
    (fa : a + 4 * n ≤ size) (fb : b + 4 * n ≤ size)
    (fm : M.mo + 4 * n ≤ size) (ft : acc + 4 * (n + 2) ≤ size)
    (sa : acc + 4 * (n + 2) ≤ a ∨ a + 4 * n ≤ acc)
    (sb : acc + 4 * (n + 2) ≤ b ∨ b + 4 * n ≤ acc)
    (sm : acc + 4 * (n + 2) ≤ M.mo ∨ M.mo + 4 * n ≤ acc)
    (modulus : val32 s.mem base M.mo n = m)
    (inverse : (m * M.minv.toNat + 1) % 2 ^ 64 = 0)
    (operand : val32 s.mem base b n < m) (zero : val32 s.mem base acc (n + 2) = 0) :
    WP isa (.loop (.block (round M acc u)) .ne) s fun t =>
      val32 t.mem base acc (n + 2) < 2 * m ∧
      2 ^ (32 * n) * val32 t.mem base acc (n + 2) % m = val32 s.mem base a n * val32 s.mem base b n % m ∧
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClob s t := by
  have nowrap := hs.nowrap
  have mpos : 0 < m := by omega
  let I := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ LoopInv s base acc a b n m i t
  have step (k : Nat) (w : State) (h : I k w) :
      WP isa (.block (round M acc u)) w fun t =>
        (isa.eval .ne t = some false ∧ (val32 t.mem base acc (n + 2) < 2 * m ∧
          2 ^ (32 * n) * val32 t.mem base acc (n + 2) % m = val32 s.mem base a n * val32 s.mem base b n % m ∧
          Outside base acc (4 * (n + 2)) s.mem t.mem ∧ Rest roundClob s t)) ∨
        (isa.eval .ne t = some true ∧ ∃ j < k, I j t) := by
    obtain ⟨i, hik, hk, inv⟩ := h
    have hi : i < n := by omega
    have hu := hs.of_rest inv.rest (by decide)
    have pu : w.gpr .r1 = w.gpr .r12 + BitVec.ofNat 32 (a + 4 * i) := by
      rw [inv.ptr, inv.rest.gpr .r12 (by decide)]
    have bu : w.gpr .r4 = w.gpr .r12 + BitVec.ofNat 32 b := by
      rw [inv.rest.gpr .r4 (by decide), inv.rest.gpr .r12 (by decide)]; exact pb
    have oldM := inv.outside.val32 (d := M.mo) (k := n) (by omega) (by omega)
    have oldB := inv.outside.val32 (d := b) (k := n) (by omega) (by omega)
    have oldA := inv.outside.w32 (d := a + 4 * i) (by omega) (by omega)
    refine WP.mono (round_ok u hu hMn pu bu (by omega) fb fm ft sb sm
      (oldM.trans modulus) inverse (by rw [oldB]; exact operand) inv.bound) fun t post => ?_
    obtain ⟨⟨q, hq, value⟩, bound, out, rest, ptr, count, zeroFlag⟩ := post
    rw [oldA, oldB] at value
    have vnext : 2 ^ (32 * (i + 1)) * val32 t.mem base acc (n + 2) % m =
        val32 s.mem base a (i + 1) * val32 s.mem base b n % m := by
      rw [pow32_succ, Nat.mul_comm (2 ^ 32) (2 ^ (32 * i)), val32_succ s.mem base a i]
      exact round_step value inv.value
    have cnext : t.gpr .r9 = BitVec.ofNat 32 (n - (i + 1)) := by
      rw [count, inv.count]
      change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
      congr 1
    have znext : t.z = decide (i + 1 = n) := by
      rw [zeroFlag, inv.count]
      change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
      rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),
        ofNat_beq_zero (by omega)]
      simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]
    have pnext : t.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 (a + 4 * (i + 1)) := by
      rw [ptr, inv.ptr, BitVec.add_assoc, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, ← BitVec.ofNat_add]
      congr 1
    have next : LoopInv s base acc a b n m (i + 1) t :=
      ⟨by omega, pnext, cnext, inv.outside.trans out, bound, vnext, inv.rest.trans rest⟩
    by_cases last : i + 1 = n
    · left
      refine ⟨?_, bound, ?_, next.outside, next.rest⟩
      · change some (!t.z) = some false
        simp only [znext, last, decide_true, Bool.not_true]
      · simpa only [last] using vnext
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, next⟩
      change some (!t.z) = some true
      simp only [znext, last, decide_false, Bool.not_false]
  refine WP.loop (M := isa) I step n s ?_
  refine ⟨0, by omega, hn, ⟨by omega, ?_, ?_, Outside.refl _ _ _ _, ?_, ?_, Rest.refl _ _⟩⟩
  · simpa only [Nat.mul_zero, Nat.add_zero] using pa
  · simpa only [Nat.sub_zero] using pc
  · rw [zero]; omega
  · rw [zero]; simp only [Nat.mul_zero, Nat.zero_mod, val32, Nat.zero_mul]

end VG.Proof.Mont.Arm.Packed
