module

import VerifiedGarbage.Proof.Mont.X86.Compact.Front
import VerifiedGarbage.Proof.Mont.X86.Compact.SubAll
import VerifiedGarbage.Proof.Mont.X86.Compact.SelectAll
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Mont.X86.Compact.Bounds
public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub

/-! # Compact prepared multiplication computes the reduced Montgomery product -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- The value selected into the result is `T mod M`. -/
theorem select_mod {Tl D top X M : Nat} {c : Bool} (hX : M < X) (hD : D < X) (hV : Tl + X * top < 2 * M)
    (he : D + M = Tl + X * c.toNat) :
    (if !(decide (top < c.toNat)) then D else Tl) = (Tl + X * top) % M := by
  rw [← csub_arith hX hD hV he]
  by_cases h : top < c.toNat <;> simp [h]

theorem core_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Args s W L A)
    {N S mo o a b : Nat} (base : (A 0).toNat = W.toNat)
    (V : Metadata s.mem W A N S mo a b) (hL : Lay L N S mo a b)
    (outIndex : (A 2).toNat < 8)
    (outPtr : w32 s.mem W (64 + 8 * (A 2).toNat) = (W.toNat + o) % 2 ^ 32)
    (outHeader : 128 ≤ o) (outMod : o = mo ∨ o + 4 * N ≤ mo ∨ mo + 4 * N ≤ o)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32) (ho : o + 4 * N ≤ L) (hso : o + 4 * N ≤ S ∨ S + 8 * N + 28 ≤ o)
    (hinv : (val32 s.mem W mo N * w32 s.mem W 56 + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W b N < val32 s.mem W mo N) :
    WP isa Compact.core s fun t =>
      Outs W [(S, 8 * N + 28), (o, 4 * N)] s.mem t.mem ∧
      val32 t.mem W o N < val32 s.mem W mo N ∧
      val32 t.mem W o N * 2 ^ (32 * N) % val32 s.mem W mo N =
        val32 s.mem W a N * val32 s.mem W b N % val32 s.mem W mo N ∧
      Keeps clob7 s t := by
  have hn := hw.nowrap
  have hscr := hL.scr
  have hmo := hL.mo_le
  have hsmo := hL.smo
  have eacc : Compact.accOff = 24 := rfl
  unfold Compact.core
  refine WP.assoc (WP.assoc (WP.seq (WP.mono (WP.assoc' (front_ok hw ha base V hL hN hN32 hinv hB))
    fun u ⟨Fu, ebpu, ltu, ⟨U, hU⟩, Kfu⟩ => ?_)))
  have hwu : Ws u W L := hw.of_keeps Kfu
  have Fout := Outs.of_outside Fu (List.mem_singleton_self _)
  have toL : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Outs W rs m m' → (∀ r ∈ rs, r.1 + r.2 ≤ L) →
      Outs W [(0, L)] m m' := fun O hr =>
    Outs.widen O fun y hy r hr' => by
      have := hy _ (List.mem_singleton_self _)
      have := hr r hr'
      omega_arith
  have hau : Args u W L A := ha.of_keeps Kfu (by decide) (toL Fout (by simp only [List.mem_singleton, forall_eq]; omega_using [hscr]))
  -- The modulus, apart from the function's range.
  have mou : val32 u.mem W mo N = val32 s.mem W mo N :=
    Fu.val32 hsmo (by omega_using [hmo, hn])
  have hM : val32 s.mem W mo N < 2 ^ (32 * N) := val32_lt _ _ _ _
  -- The subtraction.
  have vu := V.keep Fu (by have := hL.header; omega_arith)
  have outPu : w32 u.mem W (64 + 8 * (A 2).toNat) = (W.toNat + o) % 2 ^ 32 := by
    rw [Fu.w32 (by have := hL.header; omega_arith) (by omega_arith), outPtr]
  refine WP.seq (WP.mono (subAll_ok hwu hau base vu (by have := hL.header; omega_arith)
    outIndex outPu hN hN32 (by omega_arith) hL.mo_le ho outHeader (by omega_arith) outMod ebpu) fun v ⟨Ov, ⟨c, ecv, Vv⟩, ebpv, ediv, Kv⟩ => ?_)
  have hwv : Ws v W L := hwu.of_keeps Kv
  have hav : Args v W L A := hau.of_keeps Kv (by decide)
    (toL (Outs.of_outside Ov (List.mem_singleton_self _)) (by simp only [List.mem_singleton, forall_eq]; omega_using [ho]))
  have srcv : val32 v.mem W (S + Compact.accOff + 4 * N) N = val32 u.mem W (S + Compact.accOff + 4 * N) N :=
    Ov.val32 (by omega_using [hso, eacc]) (by omega_using [hscr, hn, eacc])
  have topv : w32 v.mem W (S + Compact.accOff + 8 * N) = w32 u.mem W (S + Compact.accOff + 8 * N) :=
    Ov.w32 (by omega_using [hso, eacc]) (by omega_using [hscr, hn, eacc])
  -- The mask and the selection.
  have outPv : w32 v.mem W (64 + 8 * (A 2).toNat) = (W.toNat + o) % 2 ^ 32 := by
    rw [Ov.w32 (by omega_arith) (by omega_arith), outPu]
  refine WP.mono (selectAll_ok hwv hav base (vu.keep Ov outHeader).width
    (by have := hL.header; omega_arith) outIndex outPv hN hN32 (by omega_arith) ho (by omega_arith) ebpv ecv)
    fun w ⟨Ow, Vw, Kw⟩ => ?_
  refine ⟨?_, ?_, ?_, Kfu.trans (Kv.trans Kw)⟩
  · have e₁ : Outs W [(S, 8 * N + 28), (o, 4 * N)] s.mem u.mem := Fout.mono (by simp)
    have e₂ : Outs W [(S, 8 * N + 28), (o, 4 * N)] u.mem v.mem := Outs.of_outside Ov (by simp)
    have e₃ : Outs W [(S, 8 * N + 28), (o, 4 * N)] v.mem w.mem := Outs.of_outside Ow (by simp)
    exact (e₁.trans e₂).trans e₃
  · -- The result: `T mod M`, for the high half and top word `T`.
    have hT : val32 u.mem W (S + Compact.accOff + 4 * N) (N + 1) =
        val32 v.mem W (S + Compact.accOff + 4 * N) N + 2 ^ (32 * N) * w32 v.mem W (S + Compact.accOff + 8 * N) := by
      rw [val32_succ, srcv, topv, show S + Compact.accOff + 4 * N + 4 * N = S + Compact.accOff + 8 * N by omega_using []]
    have he : val32 v.mem W o N + val32 s.mem W mo N =
        val32 v.mem W (S + Compact.accOff + 4 * N) N + 2 ^ (32 * N) * c.toNat := by rw [srcv, ← mou]; exact Vv
    have hsel := select_mod hM (val32_lt _ _ _ _) (by rw [← hT]; exact ltu) he
    rw [Vw]
    have : val32 v.mem W (if !(decide (w32 v.mem W (S + Compact.accOff + 8 * N) < c.toNat)) then
        o else S + Compact.accOff + 4 * N) N = (if !(decide (w32 v.mem W (S + Compact.accOff + 8 * N) <
        c.toNat)) then val32 v.mem W o N else val32 v.mem W (S + Compact.accOff + 4 * N) N) := by
      split <;> rfl
    rw [this, hsel, ← hT]
    exact Nat.mod_lt _ (by omega_using [hB])
  · have hT : val32 u.mem W (S + Compact.accOff + 4 * N) (N + 1) =
        val32 v.mem W (S + Compact.accOff + 4 * N) N + 2 ^ (32 * N) * w32 v.mem W (S + Compact.accOff + 8 * N) := by
      rw [val32_succ, srcv, topv, show S + Compact.accOff + 4 * N + 4 * N = S + Compact.accOff + 8 * N by omega_using []]
    have he : val32 v.mem W o N + val32 s.mem W mo N =
        val32 v.mem W (S + Compact.accOff + 4 * N) N + 2 ^ (32 * N) * c.toNat := by rw [srcv, ← mou]; exact Vv
    have hsel := select_mod hM (val32_lt _ _ _ _) (by rw [← hT]; exact ltu) he
    rw [Vw]
    have : val32 v.mem W (if !(decide (w32 v.mem W (S + Compact.accOff + 8 * N) < c.toNat)) then
        o else S + Compact.accOff + 4 * N) N = (if !(decide (w32 v.mem W (S + Compact.accOff + 8 * N) <
        c.toNat)) then val32 v.mem W o N else val32 v.mem W (S + Compact.accOff + 4 * N) N) := by
      split <;> rfl
    rw [this, hsel, ← hT, Nat.mod_mul_mod, Nat.mul_comm, hU, Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86.Compact
