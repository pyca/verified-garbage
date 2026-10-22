module

public import VerifiedGarbage.Proof.Rsa.Arm.RvSt
public import VerifiedGarbage.Proof.Rsa.Arm.RecoverScalar
import VerifiedGarbage.Proof.Rsa.Arm.RvStage
import VerifiedGarbage.Proof.Rsa.Arm.RvOps2
import VerifiedGarbage.Proof.Rsa.Arm.RvProd

/-! Lift the existing scalar arithmetic proofs to the recovery invariant. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover
open VG.Proof.Rsa.Arm.Keys VG.Proof.X25519.Arm

theorem scalar_headroom {P : RP} {σ : State} (pre : In P σ) :
    2 * P.n ≤ 2 ^ (32 * P.w) := by
  have upper := bytes_lt σ.mem (State.addr P.nP) P.K
  rw [pre.nB] at upper
  change P.n < 2 ^ (8 * P.K) at upper
  have kw := pre.sizes.kw
  have wpos : 2 ≤ P.w := by simp only [RP.w]; omega
  have exp : 8 * P.K + 1 ≤ 32 * P.w := by omega
  have powers : 2 * 2 ^ (8 * P.K) ≤ (2 : Nat) ^ (32 * P.w) := by
    calc 2 * 2 ^ (8 * P.K) = 2 ^ (8 * P.K + 1) := Nat.pow_succ'.symm
         _ ≤ 2 ^ (32 * P.w) := Nat.pow_le_pow_right (by decide) exp
  omega

section
variable {P : RP} {E : State → Prop} {A AW V : State → Nat → Nat} {L LW LS : List Nat}

abbrev scalarLive (L : List Nat) : List Nat := L.filter (fun j => j ∉ RecoverScalar.writes)

/-- Either scalar helper preserves every array outside its documented scratch. -/
theorem St.pscalar (code : Prog isa) (factor : Nat) (cert : Cert code)
    (correct : ∀ {s : State} {B : BitVec 32} {Z w : Nat}, Ws s B Z w nArr →
      WP isa code s fun t => Ws t B Z w nArr ∧
        Keep B w RecoverScalar.writes [sC] s.mem t.mem ∧ Rest opRegs s t ∧
        (num s.mem B w aZ = 0 → num s.mem B w mX < num s.mem B w aN →
          2 * num s.mem B w aN ≤ 2 ^ (32 * w) →
          num t.mem B w mXm = (factor * num s.mem B w mX) % num s.mem B w aN))
    (hz : aZ ∈ L) (hn : aN ∈ L) (hx : mX ∈ L)
    (values : ∀ σ, E σ → A σ aZ = 0 ∧ A σ aN = P.n ∧ A σ mX < P.n)
    (wide : ∀ j ∈ LW, ∀ i ∈ RecoverScalar.writes, i / 2 ≠ j)
    (slots : ∀ d ∈ LS, d + 4 ≤ sC ∨ sC + 4 ≤ d) :
    VP (St P E A L AW LW V LS P.w nArr) code
      (St P E (fun σ => upd (A σ) mXm ((factor * A σ mX) % P.n))
        (mXm :: scalarLive L) AW LW V LS P.w nArr) := by
  refine VP.ctx cert (fun _ _ h => h.2.2.2) fun σ s ⟨e, h, hm, hw⟩ => ?_
  refine WP.mono (correct hw) fun t ⟨ht, keep, rest, value⟩ => ?_
  obtain ⟨zero, modulus, bound⟩ := values σ e
  have z := (h.arrs aZ hz).trans zero
  have n := (h.arrs aN hn).trans modulus
  have x := h.arrs mX hx
  have result := value z (by rw [x, n]; exact bound) (by rw [n]; exact scalar_headroom h.bs.pre)
  rw [x, n] at result
  have fit : ∀ j ∈ RecoverScalar.writes, arr P.w j + S P.w ≤ P.Z := fun j hj =>
    fitZ_w h.sizes (by
      simp only [RecoverScalar.writes, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> decide)
  have slotOk : ∀ d ∈ [sC], SlotOk d := by decide
  refine ⟨e, h.core keep fit slotOk (h.r8_of rest) rest.sp rest.rd rest.wr ?_ ?_
    (h.arrsW_w keep wide slotOk) h.liveW_lt (h.sl_keep keep ?_) h.ls_ok,
    hm.of_keep h.bs keep (by decide) (by decide) rest.sp rest.rd rest.wr, ht⟩
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · simpa only [upd_self] using result
    · obtain ⟨live, outside⟩ := List.mem_filter.mp hj
      have outside' : j ∉ RecoverScalar.writes := by simpa using outside
      have different : j ≠ mXm := fun eq => outside' (eq ▸ (by decide))
      change num t.mem P.B P.w j = upd (A σ) mXm ((factor * A σ mX) % P.n) j
      rw [upd_ne _ _ different, keep.num (j := j) (fun i hi eq => outside' (eq ▸ hi))
        (by decide) (fit_w h.sizes (h.live_lt j live)), h.arrs j live]
  · intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · decide
    · exact h.live_lt j (List.mem_filter.mp hj).1
  · intro d hd a ha
    simp only [List.mem_singleton] at ha
    subst ha
    exact slots d hd

end
end VG.Proof.Rsa.Arm.Recover
