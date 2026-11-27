module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Pre
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
meta import VerifiedGarbage.Impl.RsaPss.PPC64LE
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Hash
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.View
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Mid
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Calls

/-! ### `RsaPss.PPC64LE.ByIdx`, which the modules that import this one used -/

section

/-! ### `RsaPss.PPC64LE.Fixed`, which the modules that import this one used -/

section

/-!
# RSASSA-PSS verification on PPC64LE: `H'` for a given salt length

Untrusted: everything here is checked by Lean. `hashFixedG_ok`: `hashFixed`
writes what `finalize` writes for the `8 + hLen + salt_len` bytes of `M'` at
`oY` to `oDig`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (oEm oSt oDig oW oRsa)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off off_off view fx hiRegs Same hfits offs)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_li wp_addi wp_nil)

/-- Bytes of our part of the working space outside the ranges a `Same` covers. -/
theorem bytes_same {S : Addr} {t t' : State} {rgs : List (Nat × Nat)} (h : Same S t t' rgs) {d n : Nat}
    (hd : d + n ≤ oRsa) (hr : ∀ p ∈ rgs, d + n ≤ p.1 ∨ p.1 + p.2 ≤ d) :
    Spec.Sha256.bytesAt t'.mem (off S d) n = Spec.Sha256.bytesAt t.mem (off S d) n := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  have := h (d + i) (by omega_arith) fun p hp => by have := hr p hp; omega_arith
  simp only [view] at this
  rw [← off_off] at this
  exact this

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {D : Nat} {s : State} (F : Fits S s) {H : Hash}
  (hH : HashOK H) {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat} {p : Addr}
  (T : MdTabS H cn cc dn dc f j S s p)
include F hH T

/-- `hashFixed`, for any `Base` whose `r19` is the salt's length `sl`. -/
theorem hashFixedG_ok (hD : H.D = D) {sl : Nat} (h19 : vf s .r19 = BitVec.ofNat 64 sl) {t : State}
    (h : Base S vf s t) (sy : t.syms = s.syms) (hsl : sl + 8 + D ≤ 2048) :
    WP isa (hashFixed H f j) t fun t' => (Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.FD =
        hH.fh (Spec.Sha256.bytesAt t.mem (off (S s) oY) (8 + D + sl))) ∧ t'.syms = s.syms := by
  have Fh := hfits hH
  have hY : oY = 2560 := rfl
  have hR : oRsa = 8192 := rfl
  have hD64 := hH.hD64
  have g19 : ∀ {u : State}, Base S vf s u → u.gpr .r19 + BitVec.ofNat 64 (8 + H.D) =
      BitVec.ofNat 64 (8 + D + sl) := fun b => by
    rw [b.vs .r19 (by decide), h19, hD, BitVec.ofNat_add_ofNat]; congr 1; omega_using []
  refine WP.seq (WP.mono (hInit_ok F hH T h sy) fun t₁ ⟨⟨b₁, g₁, s₁, r₁⟩, y₁⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_li (by decide) fun t₂ o₂ e₂ => wp_addi (h := by decide) fun t₃ o₃ e₃ =>
    wp_addi (h := by omega_arith) fun t₄ o₄ e₄ => wp_nil fun y₄ => ?_))
  have k₄ : Only [.r4, .r5, .r6] t₁ t₄ := (o₂.trans (o₃.trans o₄)).mono
  have b₄ := b₁.only F k₄
  refine WP.seq (WP.mono (hUpd_ok F hH T b₄ (y₄.trans y₁) (m := []) (by rw [k₄.mem]; exact r₁) (by rw [o₄.get .r4, o₃.get .r4, e₂]; rfl)
    (d := oY) (len := 8 + D + sl) (by rw [o₄.get .r5, e₃, o₂.get .r14, b₁.r14])
    (by rw [e₄, o₃.get .r19, o₂.get .r19, g19 b₁]) (Nat.le_refl _) (by omega_arith)) fun t₅ ⟨⟨b₅, g₅, s₅, r₅⟩, y₅⟩ => ?_)
  refine WP.seq (WP.of_syms (wp_addi (h := by omega_arith) fun t₆ o₆ e₆ => wp_nil fun y₆ => ?_))
  have b₆ := b₅.only F o₆
  refine WP.mono (hFin_ok F hH T b₆ (y₆.trans y₅) (m := [] ++ Spec.Sha256.bytesAt t₄.mem (off (S s) oY) (8 + D + sl))
    (by rw [o₆.mem]; exact r₅) (by rw [e₆, g19 b₅, List.nil_append, Spec.Sha256.bytesAt]; simp)
    (by simp [Spec.Sha256.bytesAt]; omega_arith)) fun t' ⟨⟨b', g', s', r'⟩, y'⟩ => ⟨⟨b', fun r hr => ?_, ?_, ?_⟩, y'⟩
  · rw [g' r hr, pres_of o₆ (by decide) r hr, g₅ r hr, pres_of k₄ (by decide) r hr, g₁ r hr]
  · exact (((s₁.mono (by simp)).trans ((Same.of_mem k₄.mem _).trans (s₅.mono (by simp)))).trans
      (Same.of_mem o₆.mem _)).trans s'
  · obtain ⟨_, hSt, _, _, _, _⟩ := offs
    rw [r', List.nil_append, k₄.mem, bytes_same s₁ (by omega_arith) (by simp; omega_arith)]

end

section
variable {D : Nat} {s : State} (F : Fits Sp s) {H : Hash} (hH : HashOK H)
  {cn dn : String} {cc dc : Prog isa} {f : MdFns} {j : Nat} {p : Addr} (T : MdTabS H cn cc dn dc f j Sp s p)
include F hH T

theorem hashFixed_ok (hD : H.D = D) {t : State} (h : Base Sp (vP D) s t) (sy : t.syms = s.syms)
    (hsl : (stackArg s 0).toNat + 8 + D ≤ 2048) :
    WP isa (hashFixed H f j) t fun t' => (Base Sp (vP D) s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (Sp s) t t' [(oSt, H.S), (oDig, H.FD), (oW, H.W)] ∧
      Spec.Sha256.bytesAt t'.mem (off (Sp s) oDig) H.FD =
        hH.fh (Spec.Sha256.bytesAt t.mem (off (Sp s) oY) (8 + D + (stackArg s 0).toNat))) ∧ t'.syms = s.syms :=
  hashFixedG_ok F hH T hD (vf := vP D) (sl := (stackArg s 0).toNat) (by show stackArg s 0 = _; rw [ofNat_toNat]) h sy
    hsl

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-!
# RSASSA-PSS on PPC64LE: the code for a hash function's index

Untrusted: everything here is checked by Lean. The index of the hash
function's table (its word 5), loaded on entry, after the frame's push
(`twordA_ok`); `byIdx b is` with the index `i` in `r11`, one of `is`, runs
`b i` (`byIdx_ok`), and two runs with the same index leak alike
(`byIdx_ct`): each comparison is `r11 - i` into `r12`, by the taint analysis
with `r11` public (`idxs_certs`), and its branch on a public value; as
RSAES-OAEP's choice by the digest length (`Proof/RsaOaep/PPC64LE/ByLen.lean`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes arg tword)
open VG.Proof.RsaOaep.PPC64LE (kR fb ofNat_sub_beq64 allocated_rd allocated_mem allocated_gpr allocated_sp frame_contains
  stackArgAddr_fb)

/-- The table's word `k`, through our stack argument `j`, into `r11`, from
the state after the frame's push. -/
theorem twordA_ok {s : State} {j k : Nat} {p : Addr} (hj : arg j < 2 ^ 15 ∧ arg j % 4 = 0)
    (hk : 8 * k < 2 ^ 15 ∧ 8 * k % 4 = 0) (hA : InRegions s.rd (stackArgAddr s j) 8)
    (hAk : Region.Disjoint ⟨stackArgAddr s j, 8⟩ (kR s)) (harg : s.mem.readW (stackArgAddr s j) 64 = p)
    (hT : InRegions s.rd (p + BitVec.ofNat 64 (8 * k)) 8) (hTk : Region.Disjoint ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (kR s))
    {is : List Instr} {Q : State → Prop}
    (kk : ∀ u, Only [.r11] (allocated frameBytes s) u → u.gpr .r11 = s.mem.readW (p + BitVec.ofNat 64 (8 * k)) 64 →
      WP isa (.block is) u Q) :
    WP isa (.block (tword .r11 j k ++ is)) (allocated frameBytes s) Q := by
  have hm0 : Frame [kR s] s.mem (allocated frameBytes s).mem := by
    rw [allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  have rd : ∀ {a : Addr}, Region.Disjoint ⟨a, 8⟩ (kR s) →
      (allocated frameBytes s).mem.readW a 64 = s.mem.readW a 64 := fun hd =>
    hm0.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  simp only [tword, List.cons_append, List.nil_append]
  refine wp_addSp fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j) (by
      rw [e₁, allocated_sp, BitVec.add_zero, stackArgAddr_fb])
    (by rw [o₁.rd, allocated_rd]; exact let ⟨R, hR, hc⟩ := hA; ⟨R, List.mem_append_left _ hR, hc⟩)
    (fun u₂ o₂ e₂ => wp_ld (a := p + BitVec.ofNat 64 (8 * k)) (by rw [e₂, o₁.mem, rd hAk, harg])
      (by rw [o₂.rd, o₁.rd, allocated_rd]; exact let ⟨R, hR, hc⟩ := hT; ⟨R, List.mem_append_left _ hR, hc⟩)
      (fun u₃ o₃ e₃ => kk u₃ ((o₁.trans (o₂.trans o₃)).mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr)
        (by rw [e₃, o₂.mem, o₁.mem, rd hTk])) (by decide) hk) (by decide) hj

/-- Our stack argument `j` into `r11`, from the state after the frame's
push. -/
theorem argA_ok {s : State} {j : Nat} (hj : arg j < 2 ^ 15 ∧ arg j % 4 = 0)
    (hA : InRegions s.rd (stackArgAddr s j) 8) (hAk : Region.Disjoint ⟨stackArgAddr s j, 8⟩ (kR s)) :
    WP isa (.block [.addSp .r11 0, .load .d .r11 .r11 (arg j)]) (allocated frameBytes s) fun u =>
      Only [.r11] (allocated frameBytes s) u ∧ u.gpr .r11 = stackArg s j := by
  have hm0 : Frame [kR s] s.mem (allocated frameBytes s).mem := by
    rw [allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine wp_addSp fun u₁ o₁ e₁ => wp_ld (a := stackArgAddr s j) (by
      rw [e₁, allocated_sp, BitVec.add_zero, stackArgAddr_fb])
    (by rw [o₁.rd, allocated_rd]; exact let ⟨R, hR, hc⟩ := hA; ⟨R, List.mem_append_left _ hR, hc⟩)
    (fun u₂ o₂ e₂ => wp_nil ⟨(o₁.trans o₂).mono fun r hr => by
      simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, by
        rw [e₂, o₁.mem]
        exact hm0.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hAk)
          (by decide)⟩) (by decide) hj

/-- The word at `r11 + o` into `r11`, from a state after the frame's push
whose only change is `r11`. -/
theorem wordA_ok {s u : State} {o : Nat} {p : Addr} (hu : Only [.r11] (allocated frameBytes s) u)
    (h11 : u.gpr .r11 = p) (ho : o < 2 ^ 15 ∧ o % 4 = 0) (hT : InRegions s.rd (p + BitVec.ofNat 64 o) 8)
    (hTk : Region.Disjoint ⟨p + BitVec.ofNat 64 o, 8⟩ (kR s)) :
    WP isa (.block [.load .d .r11 .r11 o]) u fun u' =>
      Only [.r11] (allocated frameBytes s) u' ∧ u'.gpr .r11 = s.mem.readW (p + BitVec.ofNat 64 o) 64 := by
  have hm0 : Frame [kR s] s.mem (allocated frameBytes s).mem := by
    rw [allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine wp_ld (a := p + BitVec.ofNat 64 o) (by rw [h11])
    (by rw [hu.rd, allocated_rd]; exact let ⟨R, hR, hc⟩ := hT; ⟨R, List.mem_append_left _ hR, hc⟩)
    (fun u₂ o₂ e₂ => wp_nil ⟨(hu.trans o₂).mono fun r hr => by
      simp only [List.mem_append, List.mem_singleton, or_self] at hr ⊢; exact hr, by
        rw [e₂, hu.mem]
        exact hm0.readW (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hTk)
          (by decide)⟩) (by decide) ho

/-- The comparisons with each of `idxs`: an immediate `subi` takes, and the
taint check with `r11` public. -/
theorem idxs_certs : ∀ x ∈ idxs, x ≤ 2 ^ 15 ∧
    ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r11]) (.block [.subi .r12 .r11 x]) hc).isSome = true := by
  intro x hx
  simp only [idxs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, _, by taint_decide⟩

section
variable {b : Nat → Prog isa} {D : Nat} (hD : D < 2 ^ 64)
include hD

/-- `byIdx b ds`, with `D` in `r11`, runs `b D`. -/
theorem byIdx_ok {F : State → Prop} {Q : State → Prop} (h3 : ∀ t, F t → t.gpr .r11 = BitVec.ofNat 64 D)
    (hF : ∀ t t', F t → Only [.r12] t t' → t'.syms = t.syms → F t') (hb : ∀ t, F t → WP isa (b D) t Q) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x ≤ 2 ^ 15) → ∀ t, F t → WP isa (byIdx b ds) t Q
  | [], h, _, _, _ => absurd h List.not_mem_nil
  | [x], h, _, t, ht => by obtain rfl := List.mem_singleton.mp h; exact hb t ht
  | x :: y :: ds, h, hx, t, ht => by
    have hx0 := hx x (List.mem_cons_self ..)
    refine WP.seq (WP.of_syms (wp_subi (h := hx0) fun t' o e => wp_nil fun y => ?_))
    have ht' := hF t t' ht o y
    have e4 : (t'.gpr .r12 == 0) = decide (D = x) := by
      rw [e, h3 t ht, ofNat_sub_beq64 hD (by omega_using [hx0])]
    refine WP.ite _ (eval_zero _ _) (fun hc => ?_) (fun hc => ?_)
    · rw [e4] at hc
      obtain rfl := of_decide_eq_true hc
      exact hb t' ht'
    · rw [e4] at hc
      have hne : D ≠ x := of_decide_eq_false hc
      exact byIdx_ok h3 hF hb ((List.mem_cons.mp h).resolve_left hne)
        (fun z hz => hx z (List.mem_cons_of_mem _ hz)) t' ht'

/-- Two runs of `byIdx b ds`, with `D` in `r11`, are two runs of `b D`. -/
theorem byIdx_ct {α : Type} {Φ : α → State → Prop} {R : State → State → Prop}
    (h3 : ∀ a t, Φ a t → t.gpr .r11 = BitVec.ofNat 64 D) (hsp : ∀ a t₁ t₂, Φ a t₁ → Φ a t₂ → t₁.sp = t₂.sp)
    (hF : ∀ a t t', Φ a t → Only [.r12] t t' → t'.syms = t.syms → Φ a t') (hb : RelCT isa (Two Φ) (b D) R) :
    ∀ {ds : List Nat}, D ∈ ds → (∀ x ∈ ds, x ≤ 2 ^ 15 ∧
      ∃ hc, (VG.Taint.check taint (VG.PPC64LE.Taint.ofRegs [.r11]) (.block [.subi .r12 .r11 x]) hc).isSome = true) →
      RelCT isa (Two Φ) (byIdx b ds) R
  | [], h, _ => absurd h List.not_mem_nil
  | [x], h, _ => by obtain rfl := List.mem_singleton.mp h; exact hb
  | x :: y :: ds, h, hx => by
    obtain ⟨hx0, _, hcx⟩ := hx x (List.mem_cons_self ..)
    let Ψ : α → State → Prop := fun a t => Φ a t ∧ t.gpr .r12 = BitVec.ofNat 64 D - BitVec.ofNat 64 x
    refine RelCT.seq (two_post (Ψ := Ψ) (two_taint [.r11] (fun a t₁ t₂ h₁ h₂ => ⟨hsp a t₁ t₂ h₁ h₂, fun r hr => by
        rw [List.mem_singleton.mp hr, h3 a t₁ h₁, h3 a t₂ h₂]⟩) hcx)
      fun a t ht => WP.of_syms (wp_subi (h := hx0) fun t' o e => wp_nil fun y => ⟨hF a t t' ht o y,
        by rw [e, h3 a t ht]⟩)) ?_
    have e4 : ∀ a t, Ψ a t → isa.eval (.zero .d .r12) t = some (decide (D = x)) := fun a t ht => by
      rw [eval_zero, ht.2, ofNat_sub_beq64 hD (by omega_using [hx0])]
    refine two_ite (fun a t₁ t₂ h₁ h₂ => by rw [e4 a t₁ h₁, e4 a t₂ h₂]) ?_ ?_
    · by_cases hDx : D = x
      · subst hDx
        exact hb.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.1, h₂.1.1⟩) fun _ _ h => h
      · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by
          have := (e4 a _ h₁.1).symm.trans h₁.2
          simp [hDx] at this
    · by_cases hDx : D = x
      · exact RelCT.of_false fun _ _ ⟨a, h₁, _⟩ => by
          have := (e4 a _ h₁.1).symm.trans h₁.2
          simp [hDx] at this
      · exact (byIdx_ct h3 hsp hF hb ((List.mem_cons.mp h).resolve_left hDx)
          (fun z hz => hx z (List.mem_cons_of_mem _ hz))).mono
          (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1.1, h₂.1.1⟩) fun _ _ h => h

end

end VG.Proof.RsaPss.PPC64LE

end

end

/-!
# RSASSA-PSS verification on PPC64LE: the entry

Untrusted: everything here is checked by Lean. `entry_ok`: from the state
after the frame's push, the saves and the prologue leave `Base` with `e`,
`e_len`, the signature and `scratch_len` in `r24`–`r27` and `n₀` in `r9`
(`Entered`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE
open VG.Impl.RsaOaep.PPC64LE (frameBytes saved oLr arg oEm oSt oDig oW oRsa copyLoop zeroLoop mgfXor save restore)
open VG.Proof.RsaOaep.PPC64LE (Base Fits SC off fx kR fb fr frameR_eq save_ok Saves stackArgAddr_fb
  stackArgAddr_eq frame_contains allocated_sp allocated_rd allocated_wr allocated_gpr allocated_lr
  allocated_mem)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_ld wp_mov wp_nil wp_lsrw wp_lbz wp_lsr wp_or wp_subi wp_li
  wp_sub wp_and)

/-- The stack arguments are in `aR`. -/
theorem in_aR {s : State} {j : Nat} (hj : j < 8) : (aR s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem in_aR_sub {s : State} {j : Nat} (hj : j < 8) : Region.Sub ⟨stackArgAddr s j, 8⟩ (aR s) := by
  rw [stackArgAddr_eq s j]; exact Offset.sub_base _ (by omega_using [hj])

/-- A word of a table of `n` words is in its region. -/
theorem tab_sub {p : Addr} {n k : Nat} (hk : k < n) :
    Region.Sub ⟨p + BitVec.ofNat 64 (8 * k), 8⟩ (Sig.tableRegion 64 p n) :=
  Offset.sub_base p (by show 8 * k + 8 ≤ n * (64 / 8); omega_using [hk])

/-- After the saves and the prologue. -/
structure Entered (D : Nat) (s t : State) : Prop where
  base : Base Sp (vP D) s t
  r24 : t.gpr .r24 = s.gpr .r5
  r25 : t.gpr .r25 = s.gpr .r6
  r26 : t.gpr .r26 = s.gpr .r9
  r27 : t.gpr .r27 = stackArg s 3
  r9 : t.gpr .r9 = n0 s

section
variable {D : Nat} {s : State} (P : PreP D s)
include P

/-- A load of our stack argument `j` through `r12`, the frame's base. -/
theorem wp_arg {t : State} {r : Reg} {j : Nat} {is : List Instr} {Q : State → Prop} (hj : j < 8)
    (h12 : t.gpr .r12 = fb s) (hrd : t.rd = s.rd) (hm : Frame [kR s] s.mem t.mem)
    (k : ∀ t', Only [r] t t' → t'.gpr r = stackArg s j → WP isa (.block is) t' Q)
    (ho : arg j < 2 ^ 15 ∧ arg j % 4 = 0 := by decide) :
    WP isa (.block (.load .d r .r12 (arg j) :: is)) t Q := by
  refine wp_ld (a := stackArgAddr s j) (by rw [h12, stackArgAddr_fb]) ?_ (fun t' o e => k t' o ?_) (by decide) ho
  · rw [hrd, P.hrd]; exact ⟨aR s, by simp, in_aR hj⟩
  · rw [e, stackArg, hm.readW (in_aR hj) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact P.ka.symm) (by decide)]

/-- From the state after the frame's push and the choice of the code for
the hash function (which writes only `r11` and `r12`). -/
theorem entry_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD : H.D = D) (hD64 : D ≤ 64) {u : State}
    (hu : Only [.r11, .r12] (allocated frameBytes s) u) :
    WP isa (.block (save ++ prologue H)) u (Entered D s) := by
  have hm0 : Frame [kR s] s.mem u.mem := by
    rw [hu.mem, allocated_mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (by
      have := frame_contains s (d := 0) (n := 8) (by decide); rwa [BitVec.add_zero] at this)
  refine save_ok (by rw [hu.sp, allocated_sp]) (by rw [hu.wr, allocated_wr, frameR_eq]) hm0
    (fun r hr => by rw [hu.gpr r (by revert r hr; decide), allocated_gpr]) (by rw [hu.lr, allocated_lr])
    fun v kv h12 hm hsv hls => ?_
  have hrd : v.rd = s.rd := kv.rd.trans (hu.rd.trans (allocated_rd _ _))
  have gs : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r9], v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r (by revert r; decide), hu.gpr r (by revert r hr; decide), allocated_gpr]
  simp only [Impl.RsaPss.PPC64LE.prologue]
  -- The stack arguments.
  refine wp_arg P (j := 1) (by decide) h12 hrd hm fun v₁ o₁ e₁ => wp_lsrw fun v₂ o₂ e₂ => ?_
  have k₂ : Only [.r20] v v₂ := (o₁.trans o₂).mono
  refine wp_arg P (j := 2) (by decide) (by rw [k₂.get .r12]; exact h12) (k₂.rd.trans hrd) (by rw [k₂.mem]; exact hm)
    fun v₃ o₃ e₃ => ?_
  refine wp_arg P (j := 3) (by decide) (by rw [o₃.get .r12, k₂.get .r12]; exact h12) (o₃.rd.trans (k₂.rd.trans hrd))
    (by rw [o₃.mem, k₂.mem]; exact hm) fun v₄ o₄ e₄ => ?_
  have k₄ : Only [.r20, .r14, .r27] v v₄ := (k₂.trans (o₃.trans o₄)).mono
  refine wp_arg P (j := 4) (by decide) (by rw [k₄.get .r12]; exact h12) (k₄.rd.trans hrd) (by rw [k₄.mem]; exact hm)
    fun v₅ o₅ e₅ => ?_
  refine wp_arg P (j := 5) (by decide) (by rw [o₅.get .r12, k₄.get .r12]; exact h12) (o₅.rd.trans (k₄.rd.trans hrd))
    (by rw [o₅.mem, k₄.mem]; exact hm) fun v₆ o₆ e₆ => ?_
  have k₆ : Only [.r20, .r14, .r27, .r22, .r23] v v₆ := (k₄.trans (o₅.trans o₆)).mono
  -- The moves.
  refine wp_mov fun v₇ o₇ e₇ => wp_mov fun v₈ o₈ e₈ => ?_
  have k₈ : Only [.r15, .r16] v₆ v₈ := (o₇.trans o₈).mono
  refine wp_arg P (j := 0) (by decide) (by rw [k₈.get .r12, k₆.get .r12]; exact h12) (k₈.rd.trans (k₆.rd.trans hrd))
    (by rw [k₈.mem, k₆.mem]; exact hm) fun v₉ o₉ e₉ => ?_
  refine wp_mov fun v₁₀ o₁₀ e₁₀ => wp_mov fun v₁₁ o₁₁ e₁₁ => wp_mov fun v₁₂ o₁₂ e₁₂ => ?_
  have k₁₂ : Only [.r15, .r16, .r19, .r24, .r25, .r26] v₆ v₁₂ :=
    (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))))).mono
  have g12 : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r9], v₆.gpr r = s.gpr r := fun r hr => by
    rw [k₆.gpr r (by revert r; decide), gs r hr]
  -- `n₀`.
  have hn : (nR s).Contains (s.gpr .r3) 1 := by
    have := Offset.contains_base (s.gpr .r3) (d := 0) (n := 1) (k := (s.gpr .r4).toNat) (by have := P.k1; omega_using [this])
      (by decide)
    rwa [BitVec.add_zero] at this
  refine wp_lbz (a := s.gpr .r3) (by rw [k₁₂.get .r3, g12 .r3 (by decide), BitVec.add_zero])
    (by rw [k₁₂.rd, k₆.rd, hrd, P.hrd]; exact ⟨nR s, by simp, hn⟩) fun v₁₃ o₁₃ e₁₃ => ?_
  have hn0 : v₁₃.gpr .r9 = n0 s := by
    rw [e₁₃, k₁₂.mem, k₆.mem, hm _ fun r hr hc => P.kn _ (List.mem_singleton.mp hr ▸ hc) hn]; rfl
  refine wp_lsr fun v₁₄ o₁₄ e₁₄ => wp_lsr fun v₁₅ o₁₅ e₁₅ => wp_or fun v₁₆ o₁₆ e₁₆ => wp_lsr fun v₁₇ o₁₇ e₁₇ =>
    wp_or fun v₁₈ o₁₈ e₁₈ => wp_lsr fun v₁₉ o₁₉ e₁₉ => wp_or fun v₂₀ o₂₀ e₂₀ => wp_subi fun v₂₁ o₂₁ e₂₁ =>
    wp_lsr fun v₂₂ o₂₂ e₂₂ => wp_li (by decide) fun v₂₃ o₂₃ e₂₃ => wp_sub fun v₂₄ o₂₄ e₂₄ =>
    wp_li (by decide) fun v₂₅ o₂₅ e₂₅ => wp_and fun v₂₆ o₂₆ e₂₆ => wp_or fun v₂₇ o₂₇ e₂₇ =>
    wp_sub fun v₂₈ o₂₈ e₂₈ => wp_subi (h := by omega_using [hD, hD64]) fun w ow ew => wp_nil ?_
  have x16 : v₁₆.gpr .r10 = (n0 s >>> 1) ||| (n0 s >>> 1) >>> 1 := by
    rw [e₁₆, o₁₅.get .r10, e₁₅, e₁₄, hn0]
  have x18 : v₁₈.gpr .r10 = ((n0 s >>> 1) ||| (n0 s >>> 1) >>> 1) |||
      ((n0 s >>> 1) ||| (n0 s >>> 1) >>> 1) >>> 2 := by
    rw [e₁₈, o₁₇.get .r10, e₁₇, x16]
  have x20 : v₂₀.gpr .r10 = smear s := by
    rw [e₂₀, o₁₉.get .r10, e₁₉, x18]; rfl
  have x22 : v₂₂.gpr .r17 = lo s := by rw [e₂₂, e₂₁, x20]; rfl
  have x27 : v₂₇.gpr .r18 = cm s := by
    rw [e₂₇, o₂₆.get .r10, o₂₅.get .r10, o₂₄.get .r10, o₂₃.get .r10, o₂₂.get .r10, o₂₁.get .r10, x20, e₂₆,
      o₂₅.get .r11, e₂₄, e₂₃, e₂₅, o₂₃.get .r17, x22]; rfl
  have k₁₃ : Only [.r9] v₁₂ v₁₃ := o₁₃
  have kL : Only [.r10, .r11, .r17, .r8, .r18, .r21] v₁₃ w :=
    (o₁₄.trans (o₁₅.trans (o₁₆.trans (o₁₇.trans (o₁₈.trans (o₁₉.trans (o₂₀.trans (o₂₁.trans (o₂₂.trans
      (o₂₃.trans (o₂₄.trans (o₂₅.trans (o₂₆.trans (o₂₇.trans (o₂₈.trans ow))))))))))))))).mono
  have kA : Only [.r20, .r14, .r27, .r22, .r23, .r15, .r16, .r19, .r24, .r25, .r26, .r9, .r10, .r11, .r17, .r8, .r18,
      .r21] v w := (k₆.trans (k₁₂.trans (k₁₃.trans kL))).mono
  have sv : Saves s w := ⟨by rw [kA.sp, kv.sp, hu.sp, allocated_sp],
    by rw [kA.wr, kv.wr, hu.wr, allocated_wr, frameR_eq],
    fun r hr => by
      rw [kA.gpr r (by revert r; decide), kv.gpr r (by revert r; decide), hu.gpr r (by revert r; decide),
        allocated_gpr],
    by rw [kA.mem]; exact hsv,
    by rw [kA.mem]; exact hls⟩
  have lw : w.gpr .r17 = lo s := by
    rw [ow.get .r17, o₂₈.get .r17, o₂₇.get .r17, o₂₆.get .r17, o₂₅.get .r17, o₂₄.get .r17, o₂₃.get .r17, x22]
  have m15 : v₁₂.gpr .r15 = s.gpr .r4 := by
    rw [o₁₂.get .r15, o₁₁.get .r15, o₁₀.get .r15, o₉.get .r15, o₈.get .r15, e₇,
      g12 .r4 (by decide)]
  refine ⟨⟨sv, kA.rd.trans hrd, ?_, fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 2
  · rw [kA.mem]; exact hm.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp
  · rw [kL.get .r24, k₁₃.get .r24, o₁₂.get .r24, o₁₁.get .r24, e₁₀, o₉.get .r5, o₈.get .r5, o₇.get .r5, g12 .r5 (by decide)]
  · rw [kL.get .r25, k₁₃.get .r25, o₁₂.get .r25, e₁₁, o₁₀.get .r6, o₉.get .r6, o₈.get .r6, o₇.get .r6, g12 .r6 (by decide)]
  · rw [kL.get .r26, k₁₃.get .r26, e₁₂, o₁₁.get .r9, o₁₀.get .r9, o₉.get .r9, o₈.get .r9, o₇.get .r9, g12 .r9 (by decide)]
  · rw [kL.get .r27, k₁₃.get .r27, k₁₂.get .r27, o₆.get .r27, o₅.get .r27]; exact e₄
  · rw [kL.get .r9]; exact hn0
  · rw [kL.get .r14, k₁₃.get .r14, k₁₂.get .r14, o₆.get .r14, o₅.get .r14, o₄.get .r14]; exact e₃
  simp only [fx, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [vP]
  · rw [kL.get .r15, k₁₃.get .r15, m15]
  · rw [kL.get .r16, k₁₃.get .r16, o₁₂.get .r16, o₁₁.get .r16, o₁₀.get .r16, o₉.get .r16, e₈, o₇.get .r7,
      g12 .r7 (by decide)]
  · exact lw
  · rw [ow.get .r18, o₂₈.get .r18, x27]
  · rw [kL.get .r19, k₁₃.get .r19, o₁₂.get .r19, o₁₁.get .r19, o₁₀.get .r19, e₉]
  · rw [kL.get .r20, k₁₃.get .r20, k₁₂.get .r20, o₆.get .r20, o₅.get .r20, o₄.get .r20, o₃.get .r20, e₂, e₁]; rfl
  · rw [ew, e₂₈, o₂₇.get .r15, o₂₆.get .r15, o₂₅.get .r15, o₂₄.get .r15, o₂₃.get .r15, o₂₂.get .r15, o₂₁.get .r15,
      o₂₀.get .r15, o₁₉.get .r15, o₁₈.get .r15, o₁₇.get .r15, o₁₆.get .r15, o₁₅.get .r15, o₁₄.get .r15, k₁₃.get .r15,
      m15, o₂₇.get .r17, o₂₆.get .r17, o₂₅.get .r17, o₂₄.get .r17, o₂₃.get .r17, x22, hD]; rfl
  · rw [kL.get .r22, k₁₃.get .r22, k₁₂.get .r22, o₆.get .r22]; exact e₅
  · rw [kL.get .r23, k₁₃.get .r23, k₁₂.get .r23]; exact e₆

end

end VG.Proof.RsaPss.PPC64LE
