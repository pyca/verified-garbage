module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Body
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.ByteOps
import VerifiedGarbage.Proof.Bignum.ExportEncoding
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # `vg_rsa_private_precompute` on x86: `pre` under the mask

`maskLoop`: each of `pre`'s `8 pre_len` bytes and-ed with the mask's low
byte (`maskLoop_ok`): all ones keeps `pre`'s words (`wordsAt_keep`), zero
clears them (`wordsAt_zeros`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (maskStep maskLoop stackAt statusOffset)

theorem wordsAt_keep {m m' : Mem} {P : Addr} {n : Nat}
    (h : ∀ i < 8 * n, m' (P + BitVec.ofNat 64 i) = m (P + BitVec.ofNat 64 i)) :
    Spec.Rsa.wordsAt m' P n = Spec.Rsa.wordsAt m P n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine Mem.readW_congr fun k hk => ?_
  rw [Offset.add_add]
  exact h _ (by omega)

theorem wordsAt_zeros {m : Mem} {P : Addr} {n : Nat}
    (h : ∀ i < 8 * n, m (P + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.wordsAt m P n = List.replicate n 0 := by
  refine VG.Proof.Bignum.wordsAt_zero_read ?_
  rw [Mem.read_eq_of_bytes (v := 0) fun i hi => by rw [h i hi]; simp]
  rfl

section
variable {s t : State}

theorem maskStep_ok (A : PPABI s) (B : Body s t) {a : Addr} (ha : t.ea ⟨.edx, 0⟩ = a)
    (hw : InRegions t.wr a 1) :
    WP isa (.block maskStep) t fun u =>
      u.mem = t.mem.writeW a (t.mem a &&& (t.mem.readW (slot s (statusOffset + 4)) 32).setWidth 8) ∧
      u.gpr .edx = t.gpr .edx + 1 ∧ u.gpr .ecx = t.gpr .ecx - 1 ∧ u.zf = some (t.gpr .ecx - 1 == 0) ∧
      Keeps [.eax, .edx, .ecx] t u := by
  unfold maskStep
  refine wp_loadByte ha ⟨_, List.mem_append_right _ hw.choose_spec.1, hw.choose_spec.2⟩ fun a₁ A₁ => ?_
  have B₁ : Body s a₁ := B.next (A₁.other _ (by decide)) A₁.rd A₁.wr (by rw [A₁.mem]; exact Frame.refl _ _)
  refine wp_logicS (.inl rfl) (B₁.readSlot A (d := statusOffset + 4) (by decide)) fun b₁ Bq => ?_
  refine wp_storeByte (a := a)
    (by change (b₁.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = a
        rw [Bq.other .edx (by decide), A₁.other .edx (by decide)]; exact ha)
    (by rw [Bq.wr, A₁.wr]; exact hw) fun c C => ?_
  refine wp_addS rfl fun f F _ => ?_
  refine wp_subS rfl fun h H _ => ?_
  refine wp_cmpS rfl fun u U Z => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [U.mem, H.mem, F.mem, C.mem, Bq.mem, A₁.mem]
    change t.mem.writeW a ((b₁.gpr .eax).setWidth 8) = _
    rw [Bq.gpr, A₁.gpr, ite_eq_left rfl, BitVec.setWidth_and,
      BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), BitVec.setWidth_eq, A₁.mem]
  · rw [U.gpr, H.other .edx (by decide), F.gpr, C.gpr, Bq.other .edx (by decide), A₁.other .edx (by decide)]
  · rw [U.gpr, H.gpr, F.other .ecx (by decide), C.gpr, Bq.other .ecx (by decide), A₁.other .ecx (by decide)]
  · rw [Z, H.gpr, F.other .ecx (by decide), C.gpr, Bq.other .ecx (by decide), A₁.other .ecx (by decide)]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
  · exact (A₁.keeps.mono (rs' := [.eax, .edx, .ecx]) (by decide)).trans
      ((Bq.keeps.mono (rs' := [.eax, .edx, .ecx]) (by decide)).trans ((C.keeps _).trans
      ((F.keeps.mono (rs' := [.eax, .edx, .ecx]) (by decide)).trans
      ((H.keeps.mono (rs' := [.eax, .edx, .ecx]) (by decide)).trans (U.keeps _)))))

/-- The mask's low byte, from the frame. -/
abbrev mask8 (s : State) (m : Mem) : BitVec 8 := (m.readW (slot s (statusOffset + 4)) 32).setWidth 8

theorem maskLoop_ok (A : PPABI s) (B : Body s t) (hedx : t.gpr .edx = arg s 0)
    (hecx : (t.gpr .ecx).toNat = (arg s 1).toNat * 8) :
    WP isa maskLoop t fun u => Body s u ∧ Keeps [.eax, .edx, .ecx] t u ∧ Frame [preR s] t.mem u.mem ∧
      ∀ i < (arg s 1).toNat * 8, u.mem (argumentPointer s 0 + BitVec.ofNat 64 i) =
        t.mem (argumentPointer s 0 + BitVec.ofNat 64 i) &&& mask8 s t.mem := by
  have pb := A.preBound
  have hl := A.preLength
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords] at hl
  have p0 : (argumentPointer s 0).toNat = (arg s 0).toNat := by
    simp only [argumentPointer, BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (arg s 0).isLt; omega)
  let N := (arg s 1).toNat * 8
  have hN : 0 < N := by simp only [N]; omega
  let I : Nat → State → Prop := fun j u =>
    Body s u ∧ Keeps [.eax, .edx, .ecx] t u ∧ u.gpr .edx = arg s 0 + BitVec.ofNat 32 j ∧
      (u.gpr .ecx).toNat = N - j ∧ Frame [⟨argumentPointer s 0, j⟩] t.mem u.mem ∧
      ∀ i < j, u.mem (argumentPointer s 0 + BitVec.ofNat 64 i) =
        t.mem (argumentPointer s 0 + BitVec.ofNat 64 i) &&& mask8 s t.mem
  refine WP.mono (PublicRt.countLoop hN I ?_ ⟨B, Keeps.refl _ _, by rw [hedx]; simp, by rw [hecx]; simp only [N, Nat.sub_zero], Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun u ⟨Bu, Ku, _, _, Fu, Vu⟩ =>
      ⟨Bu, Ku, Fu.sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact ⟨preR s, List.mem_singleton_self _, fun _ h => h⟩, Vu⟩
  rintro j v hj ⟨Bv, Kv, Ev, Cv, Fv, Vv⟩
  have one : (1 : BitVec 32).toNat = 1 := rfl
  have zero : (0 : BitVec 32).toNat = 0 := rfl
  have hjN : j < (arg s 1).toNat * 8 := hj
  have ha : v.ea ⟨.edx, 0⟩ = argumentPointer s 0 + BitVec.ofNat 64 j := by
    simp only [State.ea, Ev]
    apply BitVec.eq_of_toNat_eq
    have := (arg s 0).isLt
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, argumentPointer]
    rw [Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (a := (arg s 0).toNat) (by omega)]
    omega
  have hw : InRegions v.wr (argumentPointer s 0 + BitVec.ofNat 64 j) 1 :=
    ⟨preR s, by rw [Bv.wr, A.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have keepM : v.mem.readW (slot s (statusOffset + 4)) 32 = t.mem.readW (slot s (statusOffset + 4)) 32 :=
    slot_keep A (Fv.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨preR s, by simp, Region.sub_prefix (by omega)⟩) (by decide)
  refine WP.mono (maskStep_ok A Bv ha hw) fun u ⟨Mu, Eu, Cu, Zu, Ku⟩ => ⟨⟨?_, Kv.trans Ku, ?_, ?_, ?_, ?_⟩, ?_⟩
  · refine Bv.next (Ku.1 _ (by decide)) Ku.2.1 Ku.2.2 ?_
    rw [Mu]
    exact (Frame.refl _ _).writeW (r := preR s) (by simp) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [Eu, Ev, BitVec.add_assoc, BitVec.ofNat_add]; rfl
  · rw [Cu, BitVec.toNat_sub, Cv, one]
    simp only [N]
    omega
  · rw [Mu]
    refine (Fv.sub fun r hr => ?_).trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega)))
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩
  · intro i hi
    rw [Mu]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hij
    · rw [Frame.bytes (rs := [⟨argumentPointer s 0 + BitVec.ofNat 64 j, 1⟩])
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (R := ⟨argumentPointer s 0, j⟩) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)) (by simp; omega) hi]
      exact Vv i hi
    · rw [hij]
      have e0 := Fv.bytes (R := ⟨argumentPointer s 0 + BitVec.ofNat 64 j, 1⟩) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)) (by simp) (i := 0) Nat.zero_lt_one
      simp only [BitVec.add_zero] at e0
      simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
      rw [e0, keepM]
      simp
  · rw [Zu]
    congr 1
    have c1 : 1 ≤ (v.gpr .ecx).toNat := by rw [Cv]; simp only [N]; omega
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_sub, Cv, one, zero] at this
      simp only [N] at this ⊢
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, Cv, one, zero]
      simp only [N] at h ⊢
      omega

end
end VG.Proof.Bignum.X86.PrivPre
