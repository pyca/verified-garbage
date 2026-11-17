module

public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Weierstrass.Arm.TCombMask`, which this module and modules that import it used -/

section

/-! The constant-time comb scan compares its public index with the secret magnitude. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.X25519.Arm

theorem eqMask_ok {s : State} {index : Op2} {v : BitVec 32}
    (hi : index.eval s = some v) :
    WP isa (.block (TCombCfg.eqMask index)) s fun t =>
      t.gpr .r10 = 0#32 - (((s.gpr .r9 ^^^ v) - 1) >>> 31) ∧
      Rest [.r5,.r10] s t ∧ t.mem = s.mem := by
  unfold TCombCfg.eqMask
  refine wp_dp hi fun s₁ u₁ => wp_dp (op2_imm (by decide)) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp))))), ?_⟩
  · rw [u₅.gpr,dpVal,u₄.gpr,u₄.other .r10 (by decide),u₃.gpr,u₂.gpr,dpVal,u₁.gpr,dpVal]
    rfl
  · rw [u₅.mem,u₄.mem,u₃.mem,u₂.mem,u₁.mem]

theorem zero_test_bit (x : BitVec 32) (hx : x.toNat < 2^31) :
    (x-1) >>> 31 = if x=0#32 then 1 else 0 := by
  by_cases h : x = 0#32
  · subst h; decide
  · have h0 : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp only [h, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (1 : BitVec 32).toNat = 1 from rfl]
    show _ = 0
    omega_using [hx, h0]

theorem equality_mask {a b : BitVec 32} (ha : a.toNat < 2^31) (hb : b.toNat < 2^31) :
    0#32 - (((a ^^^ b)-1) >>> 31) = if a=b then BitVec.allOnes 32 else 0 := by
  have hx : (a ^^^ b).toNat < 2^31 := by
    rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow ha hb
  rw [zero_test_bit _ hx]
  by_cases h : a=b
  · subst h; simp only [BitVec.xor_self, ↓reduceIte]; decide
  · have hn : a ^^^ b ≠ 0#32 := fun e => h (BitVec.xor_eq_zero_iff.mp e)
    simp only [hn,h,↓reduceIte]; decide

end VG.Proof.Weierstrass.Arm.TComb

end

end

/-! ### `Weierstrass.Arm.TCombWord`, which only this module used -/

section

/-! One word of the fixed-base comb's constant-time table scan. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm VG.Impl.Mont.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selectWord_ok (K : TCombCfg) {s : State} {base X : Addr} {size i : Nat}
    (hs : Scr s base size) (hX : State.addr (s.gpr .r8) = X)
    (ho : K.Q.x+4*i+4 ≤ size) (hi : 4*i+4 ≤ 4096)
    (fit : X.toNat+4*i+4 ≤ 2^32)
    (hr : InRegions (s.rd ++ s.wr) (off X (4*i)) 4)
    (b : Bool) (hc : s.gpr .r10 = if b then BitVec.allOnes 32 else 0) :
    WP isa (.block (K.selectWord i)) s fun t =>
      t.mem.readW (off base (K.Q.x+4*i)) 32 =
        (if b then s.mem.readW (off X (4*i)) 32 else s.mem.readW (off base (K.Q.x+4*i)) 32) ∧
      Rest [.r4,.r5] s t ∧ Outside base (K.Q.x+4*i) 4 s.mem t.mem := by
  have hn := hs.nowrap
  have hxnat : (s.gpr .r8).toNat = X.toNat := by
    rw [← hX,addr_toNat]
  have hea : State.addr (s.gpr .r8+BitVec.ofNat 32 (4*i)) = off X (4*i) := by
    rw [VG.Arm.addr_add (by omega_using [fit,hxnat]),hX]
  unfold TCombCfg.selectWord
  refine wp_ldr (hs.off_lt (by omega_using [ho])) (hs.ea (by omega_using [ho])) (hs.read ho)
    fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  have ea₁ : State.addr (s₁.gpr .r8+BitVec.ofNat 32 (4*i)) = off X (4*i) := by
    rw [u₁.other .r8 (by decide),hea]
  have hr₁ : InRegions (s₁.rd ++ s₁.wr) (off X (4*i)) 4 := by rw [u₁.rd,u₁.wr]; exact hr
  refine wp_ldr (by omega_using [hi]) ea₁ hr₁ fun s₂ u₂ =>
    wp_dp (op2_reg _ _) fun s₃ u₃ => wp_dp (op2_reg _ _) fun s₄ u₄ =>
    wp_dp (op2_reg _ _) fun s₅ u₅ => ?_
  have k₅ : Rest [.r4,.r5] s s₅ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans ((u₄.rest (by simp)).trans (u₅.rest (by simp)))))
  have hs₅ := hs.of_rest k₅ (by decide)
  refine wp_str (hs.off_lt (by omega_using [ho])) (hs₅.ea (by omega_using [ho])) (hs₅.write ho)
    fun s₆ m₆ => WP.block_nil ?_
  have a₂ : s₂.gpr .r4 = s.mem.readW (off base (K.Q.x+4*i)) 32 := by
    rw [u₂.other .r4 (by decide),u₁.gpr]
  have d₂ : s₂.gpr .r5 = s.mem.readW (off X (4*i)) 32 := by rw [u₂.gpr,u₁.mem]
  have c₂ : s₂.gpr .r10 = s.gpr .r10 := by
    rw [u₂.other .r10 (by decide),u₁.other .r10 (by decide)]
  have d₃ : s₃.gpr .r5 = s.mem.readW (off X (4*i)) 32 ^^^ s.mem.readW (off base (K.Q.x+4*i)) 32 := by
    rw [u₃.gpr,dpVal,d₂,a₂]
  have d₄ : s₄.gpr .r5 = (s.mem.readW (off X (4*i)) 32 ^^^ s.mem.readW (off base (K.Q.x+4*i)) 32) &&&
      (if b then BitVec.allOnes 32 else 0) := by
    rw [u₄.gpr,dpVal,d₃,u₃.other .r10 (by decide),c₂,hc]
  have v₅ : s₅.gpr .r4 = if b then s.mem.readW (off X (4*i)) 32 else s.mem.readW (off base (K.Q.x+4*i)) 32 := by
    rw [u₅.gpr,dpVal,d₄,u₄.other .r4 (by decide),u₃.other .r4 (by decide),a₂]
    exact select_val _ _ b
  have mem₅ : s₅.mem=s.mem := by rw [u₅.mem,u₄.mem,u₃.mem,u₂.mem,u₁.mem]
  refine ⟨?_,k₅.trans (m₆.rest _),?_⟩
  · rw [m₆.mem,Mem.readW_writeW_self32,v₅]
  · rw [m₆.mem,mem₅]; exact writeW32_outside _ _ _ (by omega_using [ho,hn])

end VG.Proof.Weierstrass.Arm.TComb

end

end


/-! A row entry is selected one packed word at a time. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

/-- Changes confined to a subrange are a frame within the containing workspace. -/
theorem outside_frame {base : Addr} {o n size : Nat} {m m' : Mem}
    (h : Outside base o n m m') (hle : o+n ≤ size) : Frame [⟨base,size⟩] m m' := by
  intro x hx
  have hn := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at hn
  apply h
  right
  change o+n ≤ (x-base).toNat
  omega_arith

theorem selectWords_ok (K : TCombCfg) {s : State} {base X : Addr} {size : Nat}
    (hs : Scr s base size) (hX : State.addr (s.gpr .r8)=X)
    (ho : K.Q.x+16*K.L.M.n ≤ size) (hi : 16*K.L.M.n ≤ 4096)
    (fit : X.toNat+16*K.L.M.n ≤ 2^32)
    (hr : InRegions (s.rd ++ s.wr) X (16*K.L.M.n))
    (hd : Region.Disjoint ⟨X,16*K.L.M.n⟩ ⟨base,size⟩)
    (b : Bool) (hc : s.gpr .r10=if b then BitVec.allOnes 32 else 0) :
    ∀ k, k ≤ 4*K.L.M.n →
    WP isa (.block ((List.range k).flatMap K.selectWord)) s fun t =>
      (∀ i<k, w32 t.mem base (K.Q.x+4*i) =
        if b then w32 s.mem X (4*i) else w32 s.mem base (K.Q.x+4*i)) ∧
      Rest [.r4,.r5] s t ∧ Outside base K.Q.x (4*k) s.mem t.mem
  | 0, _ => WP.block_nil ⟨fun _ h => by omega_arith,Rest.refl _ _,Outside.refl _ _ _ _⟩
  | k+1, hk => by
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (selectWords_ok K hs hX ho hi fit hr hd b hc k (by omega_arith))
      fun s₁ ⟨e₁,k₁,O₁⟩ => ?_
    have hs₁ := hs.of_rest k₁ (by decide)
    have hx₁ : State.addr (s₁.gpr .r8)=X := by rw [k₁.gpr .r8 (by decide),hX]
    have hc₁ : s₁.gpr .r10=if b then BitVec.allOnes 32 else 0 := by rw [k₁.gpr .r10 (by decide),hc]
    have hr₁ : InRegions (s₁.rd ++ s₁.wr) (off X (4*k)) 4 := by
      rw [k₁.rd,k₁.wr]
      exact CallLay.inRegions_sub (off := 4*k) (l := 4) hr (by omega_arith) (by omega_arith)
    refine WP.mono (selectWord_ok K (i := k) hs₁ hx₁ (by omega_arith) (by omega_arith) (by omega_arith) hr₁ b hc₁)
      fun s₂ ⟨v₂,k₂,O₂⟩ => ?_
    refine ⟨fun i hii => ?_,k₁.trans k₂,
      (O₁.mono (Nat.le_refl _) (by omega_arith)).trans (O₂.mono (by omega_arith) (by omega_arith))⟩
    by_cases hik : i<k
    · rw [O₂.w32 (by omega_arith) (by have := hs.nowrap; omega_arith),e₁ i hik]
    · have ei : i=k := by omega_arith
      subst i
      have vnat := congrArg BitVec.toNat v₂
      change w32 s₂.mem base (K.Q.x+4*k) = _ at vnat
      have xeq : w32 s₁.mem X (4*k) = w32 s.mem X (4*k) := by
        apply congrArg BitVec.toNat
        exact (outside_frame (size := size) O₁ (by omega_arith)).readW (r := ⟨X,16*K.L.M.n⟩)
          (Offset.contains_base (d := 4*k) (n := 4) (k := 16*K.L.M.n) X (by omega_arith) (by omega_arith))
          (fun r hr' => by rcases List.mem_singleton.mp hr' with rfl; exact hd) (by decide)
      have oeq : w32 s₁.mem base (K.Q.x+4*k) = w32 s.mem base (K.Q.x+4*k) :=
        O₁.w32 (by omega_arith) (by have := hs.nowrap; omega_arith)
      cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] at vnat ⊢ <;>
        rw [vnat] <;> first | exact oeq | exact xeq

end VG.Proof.Weierstrass.Arm.TComb
