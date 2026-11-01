module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.IbOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbInit
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbMain
import VerifiedGarbage.Proof.Rsa.PPC64LE.IbEnd
import VerifiedGarbage.Proof.Rsa.Divstep.InvResult
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The batched inverse on PPC64LE

`inverse_ok`: from `x` in array 0 and an odd `m` in array 8, both below
`2^(32 n)` for `n` in `r11` (`1 ≤ n ≤ w`), `inverse` leaves `gcd(x, m)` in
array 1 and, for `m > 1`, `y < m` with `y x ≡ gcd(x, m) (mod m)` in array 3,
`w` digits each; it writes only arrays 1–7 and 11–14 and the registers
`r0`, `r3`–`r12`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.InvBatch

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Impl.Rsa.PPC64LE.InvBatch
open VG.Proof.Rsa.KeyWorkspace (arr S num)
open VG.Proof.Rsa.Divstep (oddInput)

/-- The arrays `inverse` writes. -/
abbrev invArrs : List Nat := [1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14]

/-- The registers `inverse` changes. -/
abbrev invRegs : List Reg := .r10 :: kRegs

theorem inverse_ok {s : State} {B : Addr} {Z w N n : Nat} (h : Ws s B Z w N) (hN15 : 15 ≤ N) (hN : N ≤ 256)
    (hw : 10 ≤ w) (h11 : s.gpr .r11 = BitVec.ofNat 64 n) (hn1 : 1 ≤ n) (hnw : n ≤ w) {x m : Nat}
    (hx : num s.mem B w aX = x) (hxn : x < 2 ^ (32 * n)) (hm : num s.mem B w aMin = m) (hmn : m < 2 ^ (32 * n))
    (hodd : m % 2 = 1) :
    WP isa inverse s fun t => Ws t B Z w N ∧ KeyWorkspace.Keep B w invArrs [] s.mem t.mem ∧ Keep invRegs s t ∧
      (1 < m → num t.mem B w 1 = Nat.gcd x m ∧
        (m : Int) ∣ (num t.mem B w 3 : Int) * x - num t.mem B w 1 ∧ num t.mem B w 3 < m) := by
  have := h.wle
  have fit : ∀ j < N, arr w j + S w ≤ 2 ^ 64 := fun j hj => h.fit64 hj
  have hx' : val32 s.mem B (arr w aX) n = x := val_low hnw hx hxn
  have hm' : val32 s.mem B (arr w aMin) n = m := val_low hnw hm hmn
  have p1 : 1 < vmod m := by unfold vmod; split <;> omega
  have po : vmod m % 2 = 1 := by unfold vmod; split <;> omega
  have pA : vmod m < 2 ^ (32 * n) := by
    unfold vmod; split
    · have : 2 ^ 32 ≤ 2 ^ (32 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · exact hmn
  have hk1 : n + 1 ≤ w + 2 := by omega
  have nF : aF < N := by unfold aF; omega
  have nA : aA < N := by unfold aA; omega
  have nM : aMz < N := by unfold aMz; omega
  simp only [inverse, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN15 hN hw h11 hn1 hnw hx' hxn hm' hmn hodd) fun t0 ⟨h0, ⟨iv, hiv, st0⟩, K0, k0⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (loop_ok hN h0 st0 po p1 hiv pA hxn) fun t1 ⟨h1, st1, K1, k1⟩ => ?_
  rw [Nat.sub_self] at h1
  generalize hst : Divstep.W32.invRun 30 (vmod m) iv (oddInput (vmod m) x) (3 * (n + 1)) = st at st1
  have ox : oddInput (vmod m) x ≤ vmod m + x := by
    unfold oddInput; generalize vmod m = P; split <;> omega
  obtain ⟨-, -, -, -, a0, a1, -, -⟩ := VG.Proof.Rsa.Divstep.invRun_bounds (cap := vmod m + x) po p1 hiv
    (by omega) ox (3 * (n + 1))
  rw [hst] at a0 a1
  have ea : val32 t1.mem B (arr w aA) (n + 1) = st.a.toNat := by have := st1.a; omega
  rw [WP.seq_iff]
  refine WP.mono (normalize_ok h1 hN st1.p ea (by omega)) fun t2 ⟨h2, K2, v2, k2⟩ => ?_
  rw [st1.f] at v2
  rw [WP.seq_iff]
  refine WP.mono (doublings_ok h2 hN (by rw [keep_val K2 hk1 (by decide) (by simp) (fit _ nM)]; exact st1.p) v2
    (Divstep.normal_range _ (by omega) (by omega)) pA) fun t3 ⟨h3, v3, K3, k3⟩ => ?_
  rw [Nat.sub_self] at h3
  have res := VG.Proof.Rsa.Divstep.invRun_result' (iv := iv) po p1 hiv pA hxn
  simp only at res
  rw [hst] at res
  obtain ⟨gf, gd, gl⟩ := res
  have hf3 : sv t3.mem B (arr w aF) n = st.f := by
    rw [keep_sv K3 hk1 (by decide) (by simp) (fit _ nF), keep_sv K2 hk1 (by decide) (by simp) (fit _ nF), st1.f]
  have gle : Nat.gcd (vmod m) x ≤ vmod m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have ce := VG.Proof.Rsa.Divstep.correction_eq' (p := vmod m) (st := st) (n := n) (a := st.a.toNat) (by omega) (by omega)
  have hfr : st.f.natAbs < 2 ^ (32 * n) := by rw [gf]; omega
  have hyr : Divstep.doubled (vmod m) (Divstep.normal (vmod m) st.a.toNat st.f) (6 * (n + 1)) < 2 ^ (32 * n) := by
    have := Divstep.doubled_lt (p := vmod m) (a := Divstep.normal (vmod m) st.a.toNat st.f) (k := 6 * (n + 1))
      (by omega)
    omega
  refine WP.mono (finish_ok h3 hN hf3 hfr v3 hyr) fun t4 ⟨h4, K4, g4, y4, k4⟩ => ?_
  refine ⟨h4.ws, ((K0.mono (by decide)).trans ((K1.mono (by decide)).trans ((K2.mono (by decide)).trans
    ((K3.mono (by decide)).trans (K4.mono (by decide)))))), ((k0.trans' k1).trans' (k2.mono (by decide))).trans'
    (k3.trans' (k4.mono (by decide))), fun hm1 => ?_⟩
  have pm : vmod m = m := by unfold vmod; split <;> omega
  rw [pm] at gf gd gl ce
  rw [show aGcd = 1 from rfl] at g4
  rw [show aY = 3 from rfl] at y4
  rw [g4, y4, pm, ce, gf]
  exact ⟨Nat.gcd_comm _ _, gd, gl⟩

end VG.Proof.Rsa.PPC64LE.InvBatch
