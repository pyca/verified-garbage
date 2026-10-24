module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Cut
public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega

/-! A fixed-length scalar mask preserves success bytes and zeroes failure bytes. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.WriteBytes (writeW8_apply)

structure MaskOutputInv (s₀ : State) (op : Addr) (c : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.x1, .x2, .x3] s₀ t
  x1 : t.gpr .x1 = op + BitVec.ofNat 64 j
  bytes : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if c then s₀.mem (op + BitVec.ofNat 64 i) else 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s₀.mem x

theorem maskOutputByte_ok {t : State} {op : Addr} {j : Nat} {c : Bool} (h1 : t.gpr .x1 = op + BitVec.ofNat 64 j)
    (h15 : t.gpr .x15 = mask c) (hwr : InRegions t.wr (op + BitVec.ofNat 64 j) 1) :
    WP isa (.block [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x15, .strb .x3 .x1 0, .addImm .x .x1 .x1 1,
      .subImm .x .x2 .x2 1]) t fun u =>
      (u.mem = t.mem.write (op + BitVec.ofNat 64 j) 1 (if c then t.mem (op + BitVec.ofNat 64 j) else 0) ∧
        u.gpr .x1 = op + BitVec.ofNat 64 (j + 1) ∧ u.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1) ∧
      Keep [.x1, .x2, .x3] t u := by
  have hrd : InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 j) 1 :=
    let ⟨r, hr, hc⟩ := hwr; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [h1, h15, hrd, hwr, VG.Proof.MlKem.AArch64.read_one]
  congr 1
  cases c
  · simp [mask]
  · rw [show mask true = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    have := (t.mem (op + BitVec.ofNat 64 j)).isLt
    simp

theorem maskOutputStep_ok {s₀ t : State} {op : Addr} {len j : Nat} {c : Bool} (hl : len < 2 ^ 31) (hj : j < len)
    (h15 : s₀.gpr .x15 = mask c) (hwr : ∀ i < len, InRegions s₀.wr (op + BitVec.ofNat 64 i) 1)
    (hI : MaskOutputInv s₀ op c j t) :
    WP isa (.block [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x15, .strb .x3 .x1 0, .addImm .x .x1 .x1 1,
      .subImm .x .x2 .x2 1]) t fun u => MaskOutputInv s₀ op c (j + 1) u ∧ u.gpr .x2 = t.gpr .x2 - BitVec.ofNat 64 1 := by
  have k₀ := hI.keep
  refine WP.mono (maskOutputByte_ok hI.x1 ((k₀.gpr .x15 (by decide)).trans h15) (by rw [k₀.wr]; exact hwr j hj))
    fun u ⟨⟨hm, h1, h2⟩, k⟩ => ⟨⟨(k₀.trans k).mono (by decide), h1, ?_, ?_⟩, h2⟩
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro i hi
    rw [hm, hw8, writeW8_apply]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, hI.frame _ fun i' hi' => out_ne (by omega) (by omega) (by omega)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega) (by omega) (by omega)))]
      exact hI.bytes i (by omega)
  · have hw8 : ∀ (m : Mem) (a : Addr) (v : BitVec 8), m.write a 1 v = m.writeW a v := fun _ _ _ => rfl
    intro x hx
    rw [hm, hw8, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega)))]
    exact hI.frame x fun i hi => hx i (by omega)

theorem maskOutputLoop_ok {s : State} {out : Addr} {k : Nat} {c : Bool}
 (positive : 0<k) (size : k<2^31) (pointer : s.gpr .x1=out) (count : s.gpr .x2=BitVec.ofNat 64 k)
 (maskValue : s.gpr .x15=mask c) (writable : ∀ i<k,InRegions s.wr (out+BitVec.ofNat 64 i) 1) :
 WP isa (countLoop .x2 [.ldrb .x3 .x1 0,.logic .and .x .x3 .x3 .x15,.strb .x3 .x1 0,.addImm .x .x1 .x1 1]) s fun t =>
 Spec.Rsa.bytesAt t.mem out k=(if c then Spec.Rsa.bytesAt s.mem out k else List.replicate k 0) ∧
 Outside out 0 k s.mem t.mem ∧ Keep [.x1,.x2,.x3] s t := by
 refine WP.mono (wp_countdown (N:=k) (by omega) (by omega) (MaskOutputInv s out c)
  (fun j hj t inv _ =>maskOutputStep_ok size hj maskValue writable inv)
  ⟨Keep.refl _ _,by simpa only [show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using pointer,
   fun _ h =>by omega,fun _ _ =>rfl⟩ count) ?_
 intro t inv
 refine ⟨?_,?_,inv.keep⟩
 · cases c
   · change Spec.Rsa.bytesAt t.mem out k=List.replicate k 0
     apply List.ext_getElem
     · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range,List.length_replicate]
     · intro i hi _
       have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
       simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range,List.getElem_replicate]
       simpa using inv.bytes i bound
   · change Spec.Rsa.bytesAt t.mem out k=Spec.Rsa.bytesAt s.mem out k
     apply List.ext_getElem
     · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
     · intro i hi _
       have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
       simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
       simpa using inv.bytes i bound
 · intro x hx
   apply inv.frame x
   intro i hi eq
   subst x
   rw [show ofs out (out+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega)] at hx
   omega

end VG.Proof.Ffdh.AArch64.Cached
