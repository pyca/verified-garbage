module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The checks of an RSA key on PPC64LE: the entry

`entry_ok`: `save`, the register arguments kept (`moves`, whatever they
establish, `M`), and `e`'s `Le` bytes at `Ep` (in `r5` and `r6`) read
saturated at `2^33` into `r24` and checked into `r26`; `r24` then holds the
saturated `e` times `2^31`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.KeyCheck (entry save)
open VG.Proof.Bignum.PPC64LE.Pub (sat)

/-- The registers `save` and the reading of `e` change. -/
abbrev entryRegs (mv : List Reg) : List Reg := [.r11, .r31] ++ (mv ++ [.r0, .r3, .r4, .r7, .r8, .r24, .r26])

theorem entry_ok {s0 : State} {B : Addr} {Z K oS na : Nat} (hp : KPre s0 B Z K oS na)
    (hoS : 96 + 8 * oS < 2 ^ 15) {moves : List Instr} {mv : List Reg} {M : State → State → Prop}
    (hm : ∀ u : State, WP isa (.block (moves ++ ([.addi .r7 .r5 0, .addi .r8 .r6 0] : List Instr))) u fun v =>
      (M u v ∧ v.mem = u.mem ∧ v.gpr .r7 = u.gpr .r5 ∧ v.gpr .r8 = u.gpr .r6) ∧ Keep mv u v)
    (hmv : .r31 ∉ mv) {Ep : Addr} {Le : Nat} (h5 : s0.gpr .r5 = Ep) (h6 : s0.gpr .r6 = BitVec.ofNat 64 Le)
    (hL : 1 ≤ Le) (hL' : Le ≤ 1024) (hrd : (⟨Ep, Le⟩ : Region) ∈ s0.rd)
    (hd : (⟨Ep, Le⟩ : Region).Disjoint ⟨B, Z⟩) :
    WP isa (entry oS moves) s0 fun t => ∃ u v, Keep [.r11, .r31] s0 u ∧ M u v ∧
      Keep [.r0, .r3, .r4, .r7, .r8, .r24, .r0, .r3, .r4, .r24, .r26] v t ∧ KBase B Z s0 t ∧
      t.gpr .r24 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem Ep Le))) <<< 31 ∧
      t.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64
        (if Spec.Rsa.exponentValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem Ep Le)) then 1 else 0) ∧
      Keep (entryRegs mv) s0 t := by
  unfold entry
  rw [WP.seq_iff, List.append_assoc]
  refine save_ok hp hoS fun u bu ku => ?_
  refine WP.mono (hm u) fun v ⟨⟨mv', vm, v7, v8⟩, kv⟩ => ?_
  have bv := bu.of_regs kv vm hmv
  have hc : ∀ i < Le, (⟨Ep, Le⟩ : Region).Contains (off Ep i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  have e7 : v.gpr .r7 = off Ep 0 := by
    rw [v7, ku.gpr _ (by decide), h5]; simp [off]
  have e8 : v.gpr .r8 = BitVec.ofNat 64 Le := by rw [v8, ku.gpr _ (by decide), h6]
  refine WP.seq (WP.mono (Pub.readE_ok e7 e8 hL (by omega)
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [bv.rd]; exact hrd), hc i hi⟩)) fun w ⟨⟨w24, wm⟩, kw⟩ => ?_)
  have hb : Spec.Rsa.bytesAt v.mem Ep Le = Spec.Rsa.bytesAt s0.mem Ep Le := by
    simp only [Spec.Rsa.bytesAt]
    exact List.map_congr_left fun i hi =>
      bv.frame _ (CrtValues.past_of_disjoint hd (hc i (List.mem_range.mp hi)))
  rw [hb] at w24
  have hsat : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem Ep Le)) ≤ 2 ^ 33 := by
    unfold sat; omega
  refine WP.mono (Pub.checkE_ok w24 hsat) fun t ⟨⟨t26, t24, tm⟩, kt⟩ => ?_
  refine ⟨u, v, ku, mv', kw.trans kt, (bv.of_regs kw wm).of_regs kt tm, t24, ?_, ?_⟩
  · rw [t26, Pub.exponentValid_sat]
  · have tail : ∀ r ∈ ([.r0, .r3, .r4, .r7, .r8, .r24] ++ [.r0, .r3, .r4, .r24, .r26] : List Reg),
        r ∈ ([.r0, .r3, .r4, .r7, .r8, .r24, .r26] : List Reg) := by decide
    refine (((ku.trans kv).trans kw).trans kt).mono fun r h => ?_
    rw [List.append_assoc] at h
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
    · exact List.mem_append_right _ (List.mem_append_right _ (tail r h))

end VG.Proof.Rsa.PPC64LE.KeyCheck
