module

public import VerifiedGarbage.Proof.Mont.X86.Rt.RowFull

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.X86.Rt.Sub

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
public import VerifiedGarbage.Impl.Mont.X86.PreparedSquare
public import VerifiedGarbage.Proof.Mont.X86.Compact.Metadata
import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Columns
import VerifiedGarbage.Proof.Mont.X86.Compact.Core
import VerifiedGarbage.Proof.Mont.X86.Compact.SubAll
import VerifiedGarbage.Proof.Mont.X86.Compact.SelectAll
import VerifiedGarbage.Proof.Mont.X86.Square.FinalMath

/-! # The symmetric square and the prepared result selection -/

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Compact

theorem core_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} (hw : Ws s W L) (ha : Compact.Args s W L A)
    {N S mo o a : Nat} (base : (A 0).toNat = W.toNat)
    (V : Compact.Metadata s.mem W A N S mo a a) (hL : Lay L N S mo 56 a a)
    (header : 128 ≤ S) {C : Nat → BitVec 32} (cached : Args s W L C)
    (values : ArgVals C W N S mo 56 o a a) (edi : PtrAt s W .edi S)
    (outIndex : (A 2).toNat < 8)
    (outPtr : w32 s.mem W (64 + 8 * (A 2).toNat) = (W.toNat + o) % 2 ^ 32)
    (outHeader : 128 ≤ o) (outMod : o = mo ∨ o + 4 * N ≤ mo ∨ mo + 4 * N ≤ o)
    (hN : 0 < N) (hN32 : 4 * N < 2 ^ 32) (ho : o + 4 * N ≤ L) (hso : o + 4 * N ≤ S ∨ S + 8 * N + 32 ≤ o)
    (hinv : (val32 s.mem W mo N * w32 s.mem W 56 + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem W a N < val32 s.mem W mo N) :
    WP isa VG.Impl.Mont.X86.PreparedSquare.core s fun t =>
      Outs W [(S + 16, 8 * N + 16), (o, 4 * N)] s.mem t.mem ∧
      val32 t.mem W o N < val32 s.mem W mo N ∧
      val32 t.mem W o N * 2 ^ (32 * N) % val32 s.mem W mo N =
        val32 s.mem W a N * val32 s.mem W a N % val32 s.mem W mo N ∧
      Keeps clob7 s t := by
  have hn := hw.nowrap
  have hscr := hL.scr
  have hmo := hL.mo_le
  have hsmo := hL.smo
  have eacc : Compact.accOff = 24 := rfl
  simp only [VG.Impl.Mont.X86.PreparedSquare.core, VG.Impl.Mont.X86.PreparedSquare.seqs]
  refine WP.seq (WP.mono (columns_ok cached hw values hL hN edi
    (VG.Proof.Mont.X86.Square.low_inverse s.mem W mo 56 hN hinv) hB)
    fun u ⟨Fu, Fdetail, ebpu, ltu, ⟨U, hU⟩, Kfu0⟩ => ?_)
  rw [VG.Proof.Mont.X86.Square.pow32] at hU
  change 2 ^ (32 * N) * val32 u.mem W (S + Compact.accOff + 4 * N) (N + 1) =
    val32 s.mem W a N * val32 s.mem W a N + U * val32 s.mem W mo N at hU
  have Kfu : Keeps clob7 s u := Kfu0.mono (by decide)
  have hwu : Ws u W L := hw.of_keeps Kfu
  have Fout : Outs W [(S + 16, 8 * N + 16)] s.mem u.mem :=
    Outs.widen Fdetail fun x hx r hr => by
      have outside := hx _ (List.mem_singleton_self _)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only at * <;> omega
  have toL : ∀ {m m' : Mem} {rs : List (Nat × Nat)}, Outs W rs m m' → (∀ r ∈ rs, r.1 + r.2 ≤ L) →
      Outs W [(0, L)] m m' := fun O hr =>
    Outs.widen O fun y hy r hr' => by
      have := hy _ (List.mem_singleton_self _)
      have := hr r hr'
      omega
  have hau : Compact.Args u W L A := ha.of_keeps Kfu (by decide) (toL Fout (by simp only [List.mem_singleton, forall_eq]; omega_using [hscr]))
  -- The modulus, apart from the function's range.
  have mou : val32 u.mem W mo N = val32 s.mem W mo N :=
    Fu.val32 hsmo (by omega_using [hmo, hn])
  have hM : val32 s.mem W mo N < 2 ^ (32 * N) := val32_lt _ _ _ _
  -- The subtraction.
  have vu := V.keep Fu (by omega)
  have outPu : w32 u.mem W (64 + 8 * (A 2).toNat) = (W.toNat + o) % 2 ^ 32 := by
    rw [Fu.w32 (by omega) (by omega), outPtr]
  refine WP.seq (WP.mono (subAll_ok hwu hau base vu (by omega)
    outIndex outPu hN hN32 (by omega) hL.mo_le ho outHeader (by omega) outMod ebpu) fun v ⟨Ov, ⟨c, ecv, Vv⟩, ebpv, ediv, Kv⟩ => ?_)
  have hwv : Ws v W L := hwu.of_keeps Kv
  have hav : Compact.Args v W L A := hau.of_keeps Kv (by decide)
    (toL (Outs.of_outside Ov (List.mem_singleton_self _)) (by simp only [List.mem_singleton, forall_eq]; omega_using [ho]))
  have srcv : val32 v.mem W (S + Compact.accOff + 4 * N) N = val32 u.mem W (S + Compact.accOff + 4 * N) N :=
    Ov.val32 (by omega_using [hso, eacc]) (by omega_using [hscr, hn, eacc])
  have topv : w32 v.mem W (S + Compact.accOff + 8 * N) = w32 u.mem W (S + Compact.accOff + 8 * N) :=
    Ov.w32 (by omega_using [hso, eacc]) (by omega_using [hscr, hn, eacc])
  -- The mask and the selection.
  have outPv : w32 v.mem W (64 + 8 * (A 2).toNat) = (W.toNat + o) % 2 ^ 32 := by
    rw [Ov.w32 (by omega) (by omega), outPu]
  refine WP.mono (selectAll_ok hwv hav base (vu.keep Ov outHeader).width
    (by omega) outIndex outPv hN hN32 (by omega) ho (by omega) ebpv ecv)
    fun w ⟨Ow, Vw, Kw⟩ => ?_
  refine ⟨?_, ?_, ?_, Kfu.trans (Kv.trans Kw)⟩
  · have e₁ : Outs W [(S + 16, 8 * N + 16), (o, 4 * N)] s.mem u.mem := Fout.mono (by simp)
    have e₂ : Outs W [(S + 16, 8 * N + 16), (o, 4 * N)] u.mem v.mem := Outs.of_outside Ov (by simp)
    have e₃ : Outs W [(S + 16, 8 * N + 16), (o, 4 * N)] v.mem w.mem := Outs.of_outside Ow (by simp)
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


end VG.Proof.Mont.X86.PreparedSquare
