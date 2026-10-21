module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Front
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

/-! # The run-time width multiplication

`body_ok`: the number at `o` is `A B R⁻¹` modulo `M`, below `M`; only the
function's range and the result change; the callee-saved registers are as
they were.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

/-- The value selected into the result is `T mod M`. -/
theorem select_mod {Tl D top X M : Nat} {c : Bool} (hX : M < X) (hD : D < X) (hV : Tl + X * top < 2 * M)
    (he : D + M = Tl + X * c.toNat) :
    (if !(decide (top < c.toNat)) then D else Tl) = (Tl + X * top) % M := by
  rw [← csub_arith hX hD hV he]
  by_cases h : top < c.toNat <;> simp [h]

theorem scalarBody_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {N S mo inv o a b : Nat} (V : ArgVals A W N S mo inv o a b) (hL : Lay L N S mo inv a b)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32) (ho : o + 4 * N ≤ L) (hso : o + 4 * N ≤ S ∨ S + 12 * N + 56 ≤ o)
    (hinv : (val32 s.mem W mo N * w32 s.mem W inv + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < val32 s.mem W mo N) :
    WP isa Rt.scalarBody s fun t =>
      Outs W [(S, 12 * N + 56), (o, 4 * N)] s.mem t.mem ∧
      val32 t.mem W o N < val32 s.mem W mo N ∧
      val32 t.mem W o N * 2 ^ (32 * N) % val32 s.mem W mo N =
        val32 s.mem W a N * val32 s.mem W b N % val32 s.mem W mo N ∧
      t.gpr .ebx = s.gpr .ebx ∧ t.gpr .esi = s.gpr .esi ∧ t.gpr .ebp = s.gpr .ebp ∧
      t.gpr .edi = s.gpr .edi ∧ t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hn := hw.nowrap
  have hscr := hL.scr
  have hmo := hL.mo_le
  have hsmo := hL.smo
  have eacc := accOff_eq
  unfold Rt.scalarBody
  refine WP.assoc (WP.assoc (WP.seq (WP.mono (WP.assoc' (front_ok hw ha V hL hN hN32 hinv hB))
    fun u ⟨Fu, svu, ebpu, ltu, ⟨U, hU⟩, espu, rdu, wru⟩ => ?_)))
  have hwu : Ws u W L := hw.of_wr wru
  have toL : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Outs W rs m m' → (∀ r ∈ rs, r.1 + r.2 ≤ L) →
      Outs W [(0, L)] m m' := fun O hr =>
    Outs.widen O fun y hy r hr' => by
      have := hy _ (List.mem_singleton_self _)
      have := hr r hr'
      omega
  have hau : Args u W L A := ha.keep (toL Fu (by simp only [List.mem_singleton, forall_eq]; omega_using [hscr])) espu rdu wru
  -- The modulus, apart from the function's range.
  have mou : val32 u.mem W mo N = val32 s.mem W mo N :=
    Fu.val32 (by simp only [List.mem_singleton, forall_eq]; omega_using [hsmo]) (by omega_using [hmo, hn])
  have hM : val32 s.mem W mo N < 2 ^ (32 * N) := val32_lt _ _ _ _
  -- The subtraction.
  refine WP.seq (WP.mono (subAll_ok hwu hau V hL hN hN32 ebpu) fun v ⟨Ov, ⟨c, ecv, Vv⟩, ebpv, ediv, Kv⟩ => ?_)
  have hwv : Ws v W L := hwu.of_keeps Kv
  have hav : Args v W L A := hau.of_keeps Kv (by decide)
    (toL (Outs.of_outside Ov (List.mem_singleton_self _)) (by simp only [List.mem_singleton, forall_eq]; omega_using [hscr, eacc]))
  have srcv : val32 v.mem W (S + accOff + 4 * N) N = val32 u.mem W (S + accOff + 4 * N) N :=
    Ov.val32 (by omega_using []) (by omega_using [hscr, hn, eacc])
  have topv : w32 v.mem W (S + accOff + 8 * N) = w32 u.mem W (S + accOff + 8 * N) :=
    Ov.w32 (by omega_using []) (by omega_using [hscr, hn, eacc])
  -- The mask and the selection.
  refine WP.assoc (WP.seq (WP.mono (selAll_ok hwv hav V hL ho hso hN hN32 ebpv ecv)
    fun w ⟨Ow, Vw, Kw⟩ => ?_))
  have hww : Ws w W L := hwv.of_keeps Kw
  have haw : Args w W L A := hav.of_keeps Kw (by decide)
    (toL (Outs.of_outside Ow (List.mem_singleton_self _)) (by simp only [List.mem_singleton, forall_eq]; omega_using [ho]))
  have svw : SavedAt w.mem W S s.gpr :=
    (svu.of_outs (Outs.of_outside Ov (List.mem_singleton_self _)) (by simp only [List.mem_singleton, forall_eq]; omega_using [eacc])
      (by omega_using [hscr, hn])).of_outs (Outs.of_outside Ow (List.mem_singleton_self _))
      (by simp only [List.mem_singleton, forall_eq]; omega_using [hso]) (by omega_using [hscr, hn])
  refine WP.mono (restore_ok hww haw V.ws V.s (by omega_using [hscr]) svw)
    fun t ⟨ebx, esi, ebp, edi, mt, Kt⟩ => ?_
  have Kvw := Kv.trans (Kw.mono (by decide))
  refine ⟨?_, ?_, ?_, ebx, esi, ebp, edi, ?_, ?_, ?_⟩
  · rw [mt]
    have e₁ : Outs W [(S, 12 * N + 56), (o, 4 * N)] s.mem u.mem := Fu.mono (by simp)
    have e₂ : Outs W [(S, 12 * N + 56), (o, 4 * N)] u.mem v.mem :=
      Outs.widen (Outs.of_outside Ov (List.mem_singleton_self _)) fun y hy r hr => by
        have := hy _ (List.mem_cons_self ..)
        simp only [List.mem_singleton] at hr; subst hr; simp only at this ⊢; omega
    have e₃ : Outs W [(S, 12 * N + 56), (o, 4 * N)] v.mem w.mem :=
      Outs.of_outside Ow (by simp)
    exact (e₁.trans e₂).trans e₃
  · -- The result: `T mod M`, for the high half and top word `T`.
    rw [mt]
    have hT : val32 u.mem W (S + accOff + 4 * N) (N + 1) =
        val32 v.mem W (S + accOff + 4 * N) N + 2 ^ (32 * N) * w32 v.mem W (S + accOff + 8 * N) := by
      rw [val32_succ, srcv, topv, show S + accOff + 4 * N + 4 * N = S + accOff + 8 * N by omega_using []]
    have he : val32 v.mem W (S + accOff + 8 * N + 4) N + val32 s.mem W mo N =
        val32 v.mem W (S + accOff + 4 * N) N + 2 ^ (32 * N) * c.toNat := by rw [srcv, ← mou]; exact Vv
    have hsel := select_mod hM (val32_lt _ _ _ _) (by rw [← hT]; exact ltu) he
    rw [Vw]
    have : val32 v.mem W (if !(decide (w32 v.mem W (S + accOff + 8 * N) < c.toNat)) then
        S + accOff + 8 * N + 4 else S + accOff + 4 * N) N = (if !(decide (w32 v.mem W (S + accOff + 8 * N) <
        c.toNat)) then val32 v.mem W (S + accOff + 8 * N + 4) N else val32 v.mem W (S + accOff + 4 * N) N) := by
      split <;> rfl
    rw [this, hsel, ← hT]
    exact Nat.mod_lt _ (by omega_using [hB])
  · rw [mt]
    have hT : val32 u.mem W (S + accOff + 4 * N) (N + 1) =
        val32 v.mem W (S + accOff + 4 * N) N + 2 ^ (32 * N) * w32 v.mem W (S + accOff + 8 * N) := by
      rw [val32_succ, srcv, topv, show S + accOff + 4 * N + 4 * N = S + accOff + 8 * N by omega_using []]
    have he : val32 v.mem W (S + accOff + 8 * N + 4) N + val32 s.mem W mo N =
        val32 v.mem W (S + accOff + 4 * N) N + 2 ^ (32 * N) * c.toNat := by rw [srcv, ← mou]; exact Vv
    have hsel := select_mod hM (val32_lt _ _ _ _) (by rw [← hT]; exact ltu) he
    rw [Vw]
    have : val32 v.mem W (if !(decide (w32 v.mem W (S + accOff + 8 * N) < c.toNat)) then
        S + accOff + 8 * N + 4 else S + accOff + 4 * N) N = (if !(decide (w32 v.mem W (S + accOff + 8 * N) <
        c.toNat)) then val32 v.mem W (S + accOff + 8 * N + 4) N else val32 v.mem W (S + accOff + 4 * N) N) := by
      split <;> rfl
    rw [this, hsel, ← hT, Nat.mod_mul_mod, Nat.mul_comm, hU, Nat.add_mul_mod_self_right]
  · rw [Kt.1 _ (by decide), Kvw.1 _ (by decide), espu]
  · rw [Kt.2.1, Kvw.2.1, rdu]
  · rw [Kt.2.2, Kvw.2.2, wru]

end VG.Proof.Mont.X86.Rt
