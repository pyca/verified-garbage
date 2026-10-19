module

public import VerifiedGarbage.Impl.MlKem.AArch64.OptimizedUsing
public import VerifiedGarbage.Proof.MlKem.AArch64.KemOps
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call

/-! # PRF/CBD composition with a replaceable verified 33-byte SHAKE256 -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM VG.Proof.MlKem.AArch64
open VG.Spec.MlKem VG.Proof.MlKem
open VG.Spec.Sha3 (bytesAt absorb pad)
variable {P : KemLay} {L : Layout}

def PrfHashValid (hash : Prog isa) : Prop :=
 ∀{s : State}, HSetup .x28 ST WK 136 s→
 (∀p∈[Piece.mk .x28 RB 33],PieceOk .x28 ST WK s false p)→
 (∀p∈[Piece.mk .x28 PB 128],PieceOk .x28 ST WK s true p)→
 WP isa hash s fun t=>
  Kept (STr .x28 ST s :: WKr .x28 WK s :: below s.sp 16 :: [preg s ⟨.x28,PB,128⟩]) s t ∧
  Outs s t.mem 136 (absorb 136 (pad 136 (BitVec.ofNat 8 31) (bytesAt s.mem (s.gpr .x28+BitVec.ofNat 64 RB) 33))) 0 [⟨.x28,PB,128⟩]

theorem prfCbd_using_ok (hash : Prog isa) (valid : PrfHashValid hash) {s₀ : State} (hp : Pre P L s₀) {N off : Nat} (hN : N < 256) (ho : PO P off) {s : State}
    (hk : KB P L s₀ s) {rv : List Byte} (hr : bytesAt s.mem (sA L s₀ RB) 32 = rv) :
    WP isa (Impl.MlKem.AArch64.Optimized.prfCbdUsing hash N off) s fun s' => KB P L s₀ s' ∧
      Frame (pcW L s₀ off) s.mem s'.mem ∧ PolyIsW (cw true) s'.mem (sA L s₀ off) (cbd rv N) ∧
      s'.gpr .x24 = s.gpr .x24 := by
  have fo := ho.le
  have hsl : ∀ {o l : Nat}, o + l ≤ SV P + 48 → o + l ≤ L.len L.sc := hp.fs
  -- `N` after `r`
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_strb (a := sA L s₀ (RB + 32)) (by decide)
    (by rw [h₁.get .x28, e28 hk]) (by
      rw [h₁.wr]; exact in_R (cov_s hp hk (o := RB + 32) (l := 1) (by kom)) (k := 0) (by decide)
        (by decide)) fun s₂ h₂ => wp_nil ?_)
  have m₂ : s₂.mem = s.mem.writeW (sA L s₀ (RB + 32)) ((s₁.gpr .x9).setWidth 8) := by
    rw [h₂.mem, h₁.mem]
  have f₂ : Frame [R (kA s₀) L.sc (RB + 32) 1] s.mem s₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (R.contains (k := 0) (by decide)
      (by decide))
  have kb₂ : KB P L s₀ s₂ := hk.frame (h₁.keep.trans h₂.keep) f₂ (by decide) fun r hr => by
    rw [List.mem_singleton.mp hr]; exact safe_scr hp (by kom)
  have msg : bytesAt s₂.mem (sA L s₀ RB) 33 = rv ++ [BitVec.ofNat 8 N] := by
    rw [show 33 = 32 + 1 from rfl, bytesAt_add, bytesAt_frame (p := sA L s₀ RB) (len := 32)
      f₂ (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact sdisj hp (by kom) (by kom) (by decide)) (by decide), hr]
    refine congrArg (rv ++ ·) (bytesAt_eq rfl fun k hk' => ?_)
    have : k = 0 := by omega
    subst this
    rw [ptr_zero, ptr_add, m₂, writeW8_apply, ite_eq_left rfl, e₁]
    exact sfx8 hN
  -- `PRF₂(r, N)`
  refine WP.seq (WP.mono (valid (hsetup hp kb₂ (by decide : 136 ∈ Spec.Sha3.rates))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₂ (by decide) (hsl (by kom)) (.inr (by decide)) (by decide)
        (fun _ => hp.scw))
    (fun p hp' => by
      rw [List.mem_singleton.mp hp']
      exact pieceOk (k := 3) hp kb₂ (by decide) (hsl (by kom)) (.inr (by decide)) (by decide)
        (fun _ => hp.scw)) ) fun s₃ ⟨k₃, o₃⟩ => ?_)
  have kb₃ : KB P L s₀ s₃ := kb₂.hash (outs := [⟨.x28,PB,128⟩]) hp k₃ fun p hp' => by
    rw [List.mem_singleton.mp hp']
    exact ⟨3, PB, 128, rfl, by decide, hp.scw, hsl (by kom), .inr (.inr (by kom))⟩
  have prf₃ : bytesAt s₃.mem (sA L s₀ PB) 128 = prf 2 rv (BitVec.ofNat 8 N) := by
    obtain ⟨o, -⟩ := o₃
    simp only [e28 kb₂] at o
    rw [msg] at o
    rw [o, prf_eq]; rfl
  have k₃' := k₃
  simp only [VG.Proof.MlKem.AArch64.STr, VG.Proof.MlKem.AArch64.WKr, preg,
    kb₂.x28, kb₂.sp] at k₃'
  -- `SamplePolyCBD₂`
  refine WP.seq (wp_ptrTo (by decide) (by decide) fun s₄ h₄ e₄ => wp_ptrTo' (by decide)
    (by obtain ⟨-, h⟩ := ho; kom) fun s₅ h₅ e₅ => ?_)
  have kb₅ := kb₃.block (h₄.trans h₅).keep (by rw [h₅.mem, h₄.mem]) (by decide)
  refine cbdW_call (b := sA L s₀ PB) (f := sA L s₀ off)
    (by rw [h₅.get .x0, e₄, e28 kb₃]) (by rw [e₅, h₄.get .x28, e28 kb₃])
    (sdisj hp (by kom) fo (.inl (by obtain ⟨h, -⟩ := ho; kom)))
    (covers_cons (cov_sr hp kb₅ (o := PB) (l := 128) (by kom)) (cov_sr hp kb₅ fo))
    (cov_s hp kb₅ fo) fun s₆ k₆ p₆ => ?_
  have kb₆ := kb₅.call k₆ fun r hr => by rw [List.mem_singleton.mp hr]; exact ho.safe hp
  rw [show s₅.mem = s₃.mem by rw [h₅.mem, h₄.mem], prf₃] at p₆
  have m₅ : s₅.mem = s₃.mem := by rw [h₅.mem, h₄.mem]
  have F₁ : Frame (pcW L s₀ off) s.mem s₂.mem := f₂.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  have F₂ : Frame (pcW L s₀ off) s₂.mem s₃.mem := k₃'.frame.mono fun r hr => by
    rcases mem4 hr with rfl | rfl | rfl | rfl <;> simp
  have F₃ : Frame (pcW L s₀ off) s₅.mem s₆.mem := k₆.frame.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; simp
  rw [m₅] at F₃
  refine ⟨kb₆, F₁.trans (F₂.trans F₃), p₆, ?_⟩
  rw [k₆.cs _ (by decide) (by decide), h₅.get .x24, h₄.get .x24, k₃.cs _ (by decide) (by decide), h₂.gpr,
    h₁.get .x24]

/-- `PrfValid` with the polynomial stored with 16 bits. -/
def PrfValidW (P : KemLay) (L : Layout) (prf : Nat→Nat→Prog isa) : Prop :=
 ∀{s₀ : State}, Pre P L s₀→∀{N off : Nat}, N<256→PO P off→∀{s : State},
 KB P L s₀ s→∀{rv : List Byte},bytesAt s.mem (sA L s₀ RB) 32=rv→
 WP isa (prf N off) s fun t=>KB P L s₀ t ∧ Frame (pcW L s₀ off) s.mem t.mem ∧
   PolyIsW 16 t.mem (sA L s₀ off) (cbd rv N) ∧ t.gpr .x24=s.gpr .x24

theorem prf_using_validW {hash : Prog isa} (valid : PrfHashValid hash) :
    PrfValidW P L (fun N off => Impl.MlKem.AArch64.Optimized.prfCbdUsing hash N off) :=
  fun {_} hp {_ _} hn ho {_} hk {_} hr=>prfCbd_using_ok hash valid hp hn ho hk hr

end VG.Proof.MlKem.AArch64.Kem
