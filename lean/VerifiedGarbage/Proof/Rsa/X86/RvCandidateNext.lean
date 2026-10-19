module

public import VerifiedGarbage.Proof.Rsa.RecoverExp
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Advancing the candidate number and testing the search bound -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

theorem candNext_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat} {ok : Bool}
    (h : KS g s0 A live AW liveW V ls s) (lc : sCand ∈ ls) (lo : sOk ∈ ls)
    (hc : V sCand < 100) (vo : V sOk = b2n ok) :
    WP isa (.block candNext) s fun t =>
      KS g s0 A live AW liveW (upd V sCand (V sCand + 1)) (sCand :: ls) t ∧
      t.zf = some (!(decide (V sCand + 1 < 100) && !ok)) := by
  unfold candNext
  refine wp_movS (h.readSlot lc) fun s1 U1 _ => ?_
  have h1 := h.of_rest U1.keeps (by decide) U1.mem
  refine wp_addS rfl fun s2 U2 _ => ?_
  have h2 := h1.of_rest U2.keeps (by decide) U2.mem
  have number : s2.gpr .eax = BitVec.ofNat 32 (V sCand + 1) := by
    rw [U2.gpr, U1.gpr]
    exact (BitVec.ofNat_add _ _).symm
  have natNumber : (s2.gpr .eax).toNat = V sCand + 1 := by
    rw [number, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.block_append (WP.mono (h2.storeSlot (d := sCand) (by decide) .eax)
    fun s3 ⟨h3, _, R3⟩ => ?_)
  rw [natNumber] at h3
  refine wp_subS rfl fun s4 U4 _ => ?_
  have h4 := h3.of_rest U4.keeps (by decide) U4.mem
  refine wp_shr (by decide) fun s5 U5 _ => ?_
  have h5 := h4.of_rest U5.keeps (by decide) U5.mem
  have ltWord : s5.gpr .eax = BitVec.ofNat 32 (b2n (decide (V sCand + 1 < 100))) := by
    rw [U5.gpr, U4.gpr, R3.1 .eax (by decide), number]
    exact VG.Proof.Rsa.lt_bv (by omega) (by decide)
  refine wp_movS (h5.readSlot (by simp [lo] : sOk ∈ sCand :: ls)) fun s6 U6 _ => ?_
  have h6 := h5.of_rest U6.keeps (by decide) U6.mem
  refine wp_logicS (.inr rfl) rfl fun s7 U7 => ?_
  have h7 := h6.of_rest U7.keeps (by decide) U7.mem
  refine wp_logicS (.inl rfl) rfl fun s8 U8 => ?_
  have h8 := h7.of_rest U8.keeps (by decide) U8.mem
  have mask : s8.gpr .eax = BitVec.ofNat 32 (b2n (decide (V sCand + 1 < 100) && !ok)) := by
    rw [U8.gpr, ite_eq_left rfl, U7.other .eax (by decide), U6.other .eax (by decide),
      ltWord, U7.gpr, ite_eq_right (by decide), U6.gpr, upd_ne _ _ (by decide : sOk ≠ sCand), vo]
    cases decide (V sCand + 1 < 100) <;> cases ok <;> rfl
  refine wp_cmpS rfl fun t T Z => WP.block_nil ⟨h8.of_rest (T.keeps []) (by simp) T.mem, ?_⟩
  rw [Z, mask]
  cases decide (V sCand + 1 < 100) <;> cases ok <;> rfl

end VG.Proof.Rsa.X86.Recover
