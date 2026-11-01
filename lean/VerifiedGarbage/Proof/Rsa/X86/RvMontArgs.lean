module

public import VerifiedGarbage.Proof.Bignum.X86.RtCall
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Bignum.X86.PublicRt
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! # The arguments of recovery's calls of `vg_rsa_mont_mul_at`

`mulArgs o a b` stores into the call's frame the working space, its length,
the width `n` and the offsets of the narrow arrays `mBase`, `mAcc`, `o`, `a`
and `b` and of the inverse's header word (`mulArgs_ok`), as `RtCall.call_ok`
takes them.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (adds_ok frame_store frame_other)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Impl.Rsa.X86.RecoverRt (offIn mulArgs narF)
open VG.Impl.Rsa.X86.Recover (mBase mAcc sInv nArr width)
open VG.Impl.Rsa.X86.Keys (hdr)
open VG.Proof.Rsa.X86.Keys (arr S)
open VG.Proof.Rsa.X86.KeyRt (kw LenSrc bytesB_ok)

/-- `offIn j`: `eax = hdr + j t` from `edx = t`. -/
theorem offIn_ok {s : State} {is : List Instr} {Q : State → Prop} {j t : Nat}
    (hedx : s.gpr .edx = BitVec.ofNat 32 t) (ht : t ≤ 2080) (hj : j < nArr)
    (kk : ∀ u, Keeps [.eax] s u → u.mem = s.mem → u.gpr .eax = BitVec.ofNat 32 (hdr + j * t) →
      WP isa (.block is) u Q) :
    WP isa (.block (offIn j ++ is)) s Q := by
  simp only [offIn, List.cons_append]
  refine wp_movS rfl fun s₁ u₁ _ => adds_ok (r := .eax) (t := .edx) (by decide) j fun u K m e => ?_
  refine kk u (u₁.keeps.trans K) (by rw [m, u₁.mem]) ?_
  rw [e, u₁.gpr, u₁.other _ (by decide), hedx]
  apply BitVec.eq_of_toNat_eq
  have : j * t ≤ 44 * 2080 := Nat.mul_le_mul (by unfold nArr at hj; omega_arith) ht
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hdr]
  rw [Nat.mod_eq_of_lt (a := t) (by omega_arith), Nat.mod_eq_of_lt (a := j * t) (by omega_arith)]

theorem arr_width (n j : Nat) : arr (width n) j = hdr + j * (8 * n + 16) := by
  simp only [arr, S, width]; congr 2; omega_arith

theorem mulArgs_ok {f : State} {n : Nat} {o a b : Nat} {wsLen : BitVec 32}
    (hl : LenSrc narF f (8 * n + 8)) (hn : n ≤ 128)
    (hr11 : readSrc f (.mem (argAt 9 11)) = some wsLen)
    (ho : o < nArr) (ha : a < nArr) (hb : b < nArr)
    (hesp : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32) (hfr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (mulArgs o a b)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        callArg (f.gpr .edi) wsLen n (arr (width n) mBase) sInv (arr (width n) mAcc) (arr (width n) o)
          (arr (width n) a) (arr (width n) b) i := by
  have kn : kw (8 * n + 8) = 2 * n + 2 := by simp only [kw, Spec.Rsa.modulusWords]; omega_arith
  generalize hP : (f.gpr .esp).setWidth 64 = P at hfr ⊢
  simp only [mulArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine bytesB_ok hl (by omega_arith) fun s₁ K₁ m₁ e₁ => ?_
  rw [kn] at e₁
  have fr : ∀ t : State, t.gpr .esp = f.gpr .esp → t.wr = f.wr → ∀ k, k + 4 ≤ 36 →
      t.ea (at_ .esp k) = P + BitVec.ofNat 64 k ∧ InRegions t.wr (P + BitVec.ofNat 64 k) 4 :=
    fun t he hw' k hk => frame_store (by rw [he, hP]) (by rw [he]; exact hesp) (by rw [hw']; exact hfr) hk
  have sp₁ : s₁.gpr .esp = f.gpr .esp := K₁.1 _ (by decide)
  have edi₁ : s₁.gpr .edi = f.gpr .edi := K₁.1 _ (by decide)
  have hr11₁ : readSrc s₁ (.mem (argAt 9 11)) = some wsLen := by
    rw [← hr11]; simp only [readSrc, State.load32, State.ea, argAt, at_, sp₁, m₁, K₁.2.1, K₁.2.2]; rfl
  refine wp_movS hr11₁ fun s₂ u₂ _ => ?_
  have K₂ : Keeps [.eax, .edx] f s₂ := (K₁.mono (by decide)).trans (u₂.keeps.mono (by decide))
  obtain ⟨a₄, w₄⟩ := fr s₂ (K₂.1 _ (by decide)) K₂.2.2 4 (by decide)
  refine wp_storeS a₄ w₄ fun s₃ m₃ => ?_
  obtain ⟨a₀, w₀⟩ := fr s₃ (by rw [m₃.gpr]; exact K₂.1 _ (by decide)) (by rw [m₃.wr]; exact K₂.2.2) 0 (by decide)
  refine wp_storeS a₀ w₀ fun s₄ m₄ => ?_
  have K₄ : Keeps [.eax, .edx] f s₄ := (K₂.trans (m₃.keeps _)).trans (m₄.keeps _)
  refine wp_movS rfl fun s₅ u₅ _ => wp_subS rfl fun s₅' u₅' _ =>
    VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₆ u₆ => ?_
  have K₆ : Keeps [.eax, .edx] f s₆ :=
    ((K₄.trans (u₅.keeps.mono (by decide))).trans (u₅'.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))
  obtain ⟨a₈, w₈⟩ := fr s₆ (K₆.1 _ (by decide)) K₆.2.2 8 (by decide)
  refine wp_storeS a₈ w₈ fun s₇ m₇ => wp_addS rfl fun s₇' u₇' _ => ?_
  have edxS : s₇'.gpr .edx = BitVec.ofNat 32 (8 * n + 16) := by
    rw [u₇'.gpr, m₇.gpr, u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide), m₄.gpr, m₃.gpr,
      u₂.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, e₁, show (8 : BitVec 32).toNat = 8 from rfl, BitVec.toNat_ofNat]
    omega_arith
  have hst : 8 * n + 16 ≤ 2080 := by omega_arith
  refine offIn_ok (j := mBase) edxS hst (by decide) fun s₈ K₈ m₈ e₈ => ?_
  have K₈' : Keeps [.eax, .edx] f s₈ :=
    ((K₆.trans (m₇.keeps _)).trans (u₇'.keeps.mono (by decide))).trans (K₈.mono (by decide))
  obtain ⟨a₁₂, w₁₂⟩ := fr s₈ (K₈'.1 _ (by decide)) K₈'.2.2 12 (by decide)
  refine wp_storeS a₁₂ w₁₂ fun s₉ m₉ => wp_movS rfl fun s₁₀ u₁₀ _ => ?_
  have K₁₀ : Keeps [.eax, .edx] f s₁₀ := (K₈'.trans (m₉.keeps _)).trans (u₁₀.keeps.mono (by decide))
  obtain ⟨a₁₆, w₁₆⟩ := fr s₁₀ (K₁₀.1 _ (by decide)) K₁₀.2.2 16 (by decide)
  refine wp_storeS a₁₆ w₁₆ fun s₁₁ m₁₁ => ?_
  have K₁₁ : Keeps [.eax, .edx] f s₁₁ := K₁₀.trans (m₁₁.keeps _)
  have edx₁₁ : s₁₁.gpr .edx = BitVec.ofNat 32 (8 * n + 16) := by
    rw [m₁₁.gpr, u₁₀.other _ (by decide), m₉.gpr, K₈.1 _ (by decide), edxS]
  refine offIn_ok (j := mAcc) edx₁₁ hst (by decide) fun s₁₂ K₁₂ m₁₂ e₁₂ => ?_
  have K₁₂' : Keeps [.eax, .edx] f s₁₂ := K₁₁.trans (K₁₂.mono (by decide))
  obtain ⟨a₂₀, w₂₀⟩ := fr s₁₂ (K₁₂'.1 _ (by decide)) K₁₂'.2.2 20 (by decide)
  refine wp_storeS a₂₀ w₂₀ fun s₁₃ m₁₃ => ?_
  have edx₁₃ : s₁₃.gpr .edx = BitVec.ofNat 32 (8 * n + 16) := by rw [m₁₃.gpr, K₁₂.1 _ (by decide), edx₁₁]
  refine offIn_ok (j := o) edx₁₃ hst ho fun s₁₄ K₁₄ m₁₄ e₁₄ => ?_
  have K₁₄' : Keeps [.eax, .edx] f s₁₄ := (K₁₂'.trans (m₁₃.keeps _)).trans (K₁₄.mono (by decide))
  obtain ⟨a₂₄, w₂₄⟩ := fr s₁₄ (K₁₄'.1 _ (by decide)) K₁₄'.2.2 24 (by decide)
  refine wp_storeS a₂₄ w₂₄ fun s₁₅ m₁₅ => ?_
  have edx₁₅ : s₁₅.gpr .edx = BitVec.ofNat 32 (8 * n + 16) := by rw [m₁₅.gpr, K₁₄.1 _ (by decide), edx₁₃]
  refine offIn_ok (j := a) edx₁₅ hst ha fun s₁₆ K₁₆ m₁₆ e₁₆ => ?_
  have K₁₆' : Keeps [.eax, .edx] f s₁₆ := (K₁₄'.trans (m₁₅.keeps _)).trans (K₁₆.mono (by decide))
  obtain ⟨a₂₈, w₂₈⟩ := fr s₁₆ (K₁₆'.1 _ (by decide)) K₁₆'.2.2 28 (by decide)
  refine wp_storeS a₂₈ w₂₈ fun s₁₇ m₁₇ => ?_
  have edx₁₇ : s₁₇.gpr .edx = BitVec.ofNat 32 (8 * n + 16) := by rw [m₁₇.gpr, K₁₆.1 _ (by decide), edx₁₅]
  refine offIn_ok (j := b) edx₁₇ hst hb fun s₁₈ K₁₈ m₁₈ e₁₈ => ?_
  have K₁₈' : Keeps [.eax, .edx] f s₁₈ := (K₁₆'.trans (m₁₇.keeps _)).trans (K₁₈.mono (by decide))
  obtain ⟨a₃₂, w₃₂⟩ := fr s₁₈ (K₁₈'.1 _ (by decide)) K₁₈'.2.2 32 (by decide)
  refine wp_storeS a₃₂ w₃₂ fun g mg => WP.block_nil ?_
  have edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (8 * n + 8) := by
    rw [m₄.gpr, m₃.gpr, u₂.other _ (by decide)]
    apply BitVec.eq_of_toNat_eq; rw [e₁, BitVec.toNat_ofNat]; omega_arith
  have eW : s₆.gpr .eax = BitVec.ofNat 32 n := by
    rw [u₆.gpr, u₅'.gpr, u₅.gpr, edx₄]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (8 : BitVec 32).toNat = 8 from rfl]
    omega_arith
  have offs : ∀ j, hdr + j * (8 * n + 16) = arr (width n) j := fun j => (arr_width n j).symm
  have mem : g.mem = ((((((((f.mem.writeW (P + BitVec.ofNat 64 4) wsLen).writeW (P + BitVec.ofNat 64 0)
      (f.gpr .edi)).writeW (P + BitVec.ofNat 64 8) (BitVec.ofNat 32 n)).writeW
      (P + BitVec.ofNat 64 12) (BitVec.ofNat 32 (arr (width n) mBase))).writeW (P + BitVec.ofNat 64 16)
      (BitVec.ofNat 32 sInv)).writeW (P + BitVec.ofNat 64 20) (BitVec.ofNat 32 (arr (width n) mAcc))).writeW
      (P + BitVec.ofNat 64 24) (BitVec.ofNat 32 (arr (width n) o))).writeW (P + BitVec.ofNat 64 28)
      (BitVec.ofNat 32 (arr (width n) a))).writeW (P + BitVec.ofNat 64 32)
        (BitVec.ofNat 32 (arr (width n) b)) := by
    rw [mg.mem, m₁₈, m₁₇.mem, m₁₆, m₁₅.mem, m₁₄, m₁₃.mem, m₁₂, m₁₁.mem, u₁₀.mem, m₉.mem, m₈,
      u₇'.mem, m₇.mem, u₆.mem, u₅'.mem, u₅.mem, m₄.mem, m₃.mem, u₂.mem, m₁, e₁₈, e₁₆, e₁₄, e₁₂, e₈, u₁₀.gpr,
      eW, m₃.gpr, u₂.gpr, u₂.other .edi (by decide), edi₁, offs, offs, offs, offs, offs]
  refine ⟨K₁₈'.trans (mg.keeps _), ?_, ?_⟩
  · have fw : ∀ {m : Mem} (k : Nat) (v : BitVec 32), k + 4 ≤ 36 → Frame [⟨P, 36⟩] f.mem m →
        Frame [⟨P, 36⟩] f.mem (m.writeW (P + BitVec.ofNat 64 k) v) := fun k v hk F =>
      F.writeW (List.mem_singleton_self _) v (Offset.contains_base _ hk (by omega_arith))
    rw [mem]
    exact fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) (Frame.refl _ _)
  · intro i hi
    rw [mem]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first
      | omega_arith
      | simp (disch := decide) only [frame_other, Mem.readW_writeW_self32, callArg, Nat.mul_zero, Nat.reduceMul,
          Nat.reduceAdd, Nat.zero_add]

end VG.Proof.Rsa.X86.Recover
