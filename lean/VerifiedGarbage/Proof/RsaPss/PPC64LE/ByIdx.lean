module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Impl.RsaPss.PPC64LE
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Two
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
meta import VerifiedGarbage.Impl.RsaPss.PPC64LE
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Base
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.ByLen
meta import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Entry
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.Offset

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
      rw [e, h3 t ht, ofNat_sub_beq64 hD (by omega)]
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
      rw [eval_zero, ht.2, ofNat_sub_beq64 hD (by omega)]
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
