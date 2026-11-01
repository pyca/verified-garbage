module

public import VerifiedGarbage.Proof.Rsa.Arm.Inv.Update
public import VerifiedGarbage.Proof.Rsa.Arm.InvLaw
public import VerifiedGarbage.Proof.Rsa.Divstep.OddInputDef
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Proof.Divstep.Red30
public import VerifiedGarbage.Proof.Rsa.Arm.Inv.Geo
import VerifiedGarbage.Proof.Rsa.Divstep.InvBounds
import VerifiedGarbage.Proof.Divstep.Word32
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.Arm.InvParts
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith.Frontend
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.Arm.Inv.Ops
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Proof.Rsa.Divstep.Inv30
import Mathlib.Algebra.Order.Ring.Int

/-! # `inverse` on ARMv7: batched divsteps at run-time width

`inverseK_ok`: what `InvLaw` states of `inverse`, and the instance the
registrations import; nothing else imports this module.
-/

@[expose] public section

/-! ## The batches of `inverse` on ARMv7

`BI σ s … i`: after `i` batches from `σ`, `δ`, `f` and `g` are those of `invRun` (`f`, `g` modulo
`2^(32 (k + 1))`), and `d, e < m` with `f ≡ a' d` and `g ≡ a' e` modulo `m`, `a' = oddInput m a`.
-/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys VG.Proof.Divstep VG.Proof.Divstep.W32
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Divstep (oddInput)


/-- The state of the algorithm after `i` batches. -/
abbrev st (p iv x i : Nat) : IState := invRun 30 p iv (oddInput p x) i

/-- The number of batches. -/
abbrev nB (k : Nat) : Nat := 3 * (k + 1)

abbrev M (k : Nat) : Int := ((2 ^ (32 * (k + 1)) : Nat) : Int)

/-- What the values need: an odd `p > 1` and `iv = -p⁻¹ mod 2^32`. The frame
facts hold without it. -/
def Good (p iv : Nat) : Prop := p % 2 = 1 ∧ 1 < p ∧ (p * iv + 1) % 2 ^ 32 = 0

structure BI (σ s : State) (B : BitVec 32) (Z W k N p iv x i : Nat) : Prop where
  geo : Gk s B Z W k N
  keep : Keep B W invArrs invSlots σ.mem s.mem
  rest : Rest (.r6 :: opRegs) σ s
  count : s.gpr .r6 = BitVec.ofNat 32 (32 * (nB k - i))
  hP : nk s.mem B W bP (k + 1) = p
  hZ : nk s.mem B W bZ (k + 1) = 0
  hiv : slot s.mem B sB = iv
  hd : Good p iv → bw s.mem B sOdd = BitVec.ofInt 32 (st p iv x i).d
  hf : Good p iv → (nk s.mem B W bF (k + 1) : Int) % M k = (st p iv x i).f % M k
  hg : Good p iv → (nk s.mem B W bG (k + 1) : Int) % M k = (st p iv x i).g % M k
  dv : Good p iv → nk s.mem B W bD (k + 1) < p
  ev : Good p iv → nk s.mem B W bE (k + 1) < p
  cf : Good p iv → (st p iv x i).f ≡ (oddInput p x : Int) * nk s.mem B W bD (k + 1) [ZMOD p]
  cg : Good p iv → (st p iv x i).g ≡ (oddInput p x : Int) * nk s.mem B W bE (k + 1) [ZMOD p]
  de : Good p iv → nk s.mem B W bD (k + 1) = (deRun p (oddInput p x) i).1 ∧
    nk s.mem B W bE (k + 1) = (deRun p (oddInput p x) i).2

/-- The low word of `f` (or `g`) from its words modulo `2^(32 (k + 1))`. -/
theorem low_word {m : Mem} {B : BitVec 32} {W k j : Nat} {f : Int}
    (h : (nk m B W j (k + 1) : Int) % M k = f % M k) :
    ((bw m B (arr W j)).toNat : Int) % 2 ^ 32 = f % 2 ^ 32 := by
  have e : (bw m B (arr W j)).toNat = nk m B W j (k + 1) % 2 ^ 32 := by
    have := word0 m B W j k; simp only [aw, w32, Nat.add_zero] at this; exact this
  have dvd : (2 ^ 32 : Int) ∣ M k := by
    simp only [M]; rw [pow32_succ]; push_cast; exact Dvd.intro _ rfl
  rw [e]
  have : (((nk m B W j (k + 1) % 2 ^ 32 : Nat)) : Int) = (nk m B W j (k + 1) : Int) % 2 ^ 32 := by
    push_cast; rfl
  rw [this, ← Int.emod_emod_of_dvd (nk m B W j (k + 1) : Int) dvd, h, Int.emod_emod_of_dvd _ dvd, Int.emod_emod]

theorem update_eq : update = seqs (fgList ++ (deList ++ ([.block [.subs .r6 .r6 (.imm 32)]] : List (Prog isa)))) := rfl

theorem nB_le {k : Nat} (hk : k ≤ 1024) : 32 * nB k + 30 < 2 ^ 32 := by simp only [nB]; omega

/-- A batch takes the state after `i` batches to the state after `i + 1`. -/
theorem batch_ok {σ s : State} {B : BitVec 32} {Z W k N p iv x i : Nat} (hN : 15 ≤ N) (hN' : N ≤ 256)
    (I : BI σ s B Z W k N p iv x i) (hi : i < nB k)
    (hpk : p < 2 ^ (32 * k)) (hx : x < 2 ^ (32 * k)) :
    WP isa batch s fun t => BI σ t B Z W k N p iv x (i + 1) ∧ t.z = decide (i + 1 = nB k) := by
  have g := I.geo
  have hW : 1 ≤ W := Nat.le_trans g.kpos g.kle
  have hL : k + 1 ≤ W + 2 := by have := g.kle; omega
  have fit := fun j (hj : j < N) => g.fit64 hj
  have hk : k ≤ 1024 := Nat.le_trans g.kle g.wle
  let S := st p iv x i
  have bounds := fun (G : Good p iv) => VG.Proof.Rsa.Divstep.invRun_bounds (p := p) (x := x) (inv := iv)
    (cap := p + x) G.1 G.2.1 G.2.2 (by omega) (by unfold oddInput; split <;> omega) i
  have bd : Good p iv → |S.d| ≤ _ := fun G => (bounds G).1
  have bodd := fun G => (bounds G).2.1
  have bf := fun G => (bounds G).2.2.1
  have bg := fun G => (bounds G).2.2.2.1
  rw [VG.Impl.Rsa.Arm.Keys.Inv.batch, WP.seq_iff]
  refine WP.mono (divsteps_ok g (by omega) (b := nB k - i) I.count (by have := nB_le hk; omega))
    fun t1 ⟨g1, k1, c1, wd, wu, wv, wq, wr, r1⟩ => ?_
  -- The words of the batch's matrix.
  let T := msteps 30 (MSt.init S.d S.f S.g)
  have w30 := fun (G : Good p iv) => by
    have hrel : (win0 s.mem B W).rel (MSt.init S.d S.f S.g) 32 :=
      ⟨I.hd G, rfl, rfl, rfl, rfl, low_word (I.hf G), low_word (I.hg G)⟩
    have hd30 : |(MSt.init S.d S.f S.g).d| + 2 * 32 < 2 ^ 30 := by
      change |S.d| + 2 * 32 < 2 ^ 30
      have : (1 + 2 * (30 * i : Nat) : Int) ≤ 1 + 2 * (30 * 3075) := by push_cast; simp only [nB] at hi; omega
      have := bd G
      linarith
    exact wsteps_rel (le_refl 32) hrel hd30 (bodd G) 30 (by decide)
  have hm : Good p iv → Mat t1.mem B W T.u T.v T.q T.r := fun G => by
    obtain ⟨eD, eU, eV, eQ, eR, -, -⟩ := w30 G
    exact ⟨by simp only [cU, Nat.add_zero]; rw [wu, eU], by simp only [cV]; rw [wv, eV],
     by simp only [cQ]; rw [wq, eQ], by simp only [cR, Nat.add_zero]; rw [wr, eR]⟩
  obtain ⟨huv, hqr⟩ := msteps_bnd S.d S.f S.g 30
  -- The arrays the divsteps leave.
  have n1 : ∀ j, j ∈ [bF, bG, bP, bZ, bD, bE] → nk t1.mem B W j (k + 1) = nk s.mem B W j (k + 1) := by
    intro j hj
    have hj' : j ≠ 1 ∧ j ≠ 3 ∧ j < 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have a1 : ∀ x ∈ [1, 3], x ≠ j := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hj'.1.symm, hj'.2.1.symm⟩
    have a2 : ∀ d ∈ [sOdd], d + 4 ≤ hdr := by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; decide
    exact Keep.nk k1 hL a1 a2 (fit _ (by omega))
  have f1 := n1 bF (by simp)
  have g1' := n1 bG (by simp)
  have p1 := n1 bP (by simp)
  have z1 := n1 bZ (by simp)
  have d1 := n1 bD (by simp)
  have e1 := n1 bE (by simp)
  have iv1 : slot t1.mem B sB = iv := by
    rw [Keep.slot k1 (by decide) (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, sOdd, sB]; omega),
      I.hiv]
  -- The next state.
  have hS1 : st p iv x (i + 1) = batch 30 p iv S := rfl
  have zf : Good p iv → T.u * S.f + T.v * S.g = 2 ^ 30 * (st p iv x (i + 1)).f := fun G => by
    obtain ⟨m1, m2⟩ := msteps_mat (d := S.d) (g := S.g) (bodd G) 30
    rw [hS1, ← m1]; show 2 ^ 30 * T.f = 2 ^ 30 * ((T.u * S.f + T.v * S.g) / 2 ^ 30)
    rw [← m1, Int.mul_ediv_cancel_left _ (by norm_num)]
  have zg : Good p iv → T.q * S.f + T.r * S.g = 2 ^ 30 * (st p iv x (i + 1)).g := fun G => by
    obtain ⟨m1, m2⟩ := msteps_mat (d := S.d) (g := S.g) (bodd G) 30
    rw [hS1, ← m2]; show 2 ^ 30 * T.g = 2 ^ 30 * ((T.q * S.f + T.r * S.g) / 2 ^ 30)
    rw [← m2, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hcap : 2 ^ 30 * (p + x) < 2 ^ 31 * 2 ^ (32 * k) := by omega
  rw [update_eq, wp_seqs_append (by simp [fgList]) (by simp)]
  refine WP.mono (fg_ok (cap := p + x) g1 hN hN' hm (fun _ => huv) (fun _ => hqr)
    (fun G => by rw [f1]; exact I.hf G) (fun G => by rw [g1']; exact I.hg G)
    (fun G => by exact_mod_cast bf G) (fun G => by exact_mod_cast bg G) (fun _ => hcap) zf zg
    (by rw [z1]; exact I.hZ))
    fun t2 ⟨g2, k2, F2, G2, r2⟩ => ?_
  have n2 : ∀ j, j ∈ [bP, bZ, bD, bE] → nk t2.mem B W j (k + 1) = nk t1.mem B W j (k + 1) := by
    intro j hj
    have hj' : j < 8 ∧ ∀ y ∈ fgArrs, y ≠ j := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> decide
    exact Keep.nk k2 hL hj'.2 (by simp) (fit _ (by omega))
  have hm2 := fun G => (hm G).keep k2 (by decide) hW (fit 1 (by omega)) (fit 3 (by omega))
  have iv2 : slot t2.mem B sB = iv := by rw [Keep.slot k2 (by decide) (by simp), iv1]
  rw [wp_seqs_append (by simp [deList]) (by simp)]
  have hpk' : p ≤ 2 ^ (32 * k) := hpk.le
  refine WP.mono (de_ok g2 hN hN' hm2 (fun _ => huv) (fun _ => hqr) (by rw [n2 bP (by simp), p1]; exact I.hP)
    (fun G => G.1) hpk' (fun G => G.2.2) iv2
    (fun G => by rw [n2 bD (by simp), d1]; exact I.dv G) (fun G => by rw [n2 bE (by simp), e1]; exact I.ev G))
    fun t3 ⟨g3, k3, dD, dE, r3⟩ => ?_
  rw [n2 bD (by simp), d1, n2 bE (by simp), e1] at dD dE
  simp only [seqs]
  refine wp_subs (op2_imm (by decide)) fun t u4 hz => WP.block_nil ?_
  have k4 : t.mem = t3.mem := u4.mem
  have n3 : ∀ j, j ∈ [bF, bG, bP, bZ] → nk t.mem B W j (k + 1) = nk t2.mem B W j (k + 1) := by
    intro j hj
    have hj' : j < 8 ∧ ∀ y ∈ deArrs, y ≠ j := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> decide
    rw [k4]; exact Keep.nk k3 hL hj'.2 (by simp) (fit _ (by omega))
  have cong := fun (G : Good p iv) => batch_cong30 (m := iv) (x := (oddInput p x : Int)) (a := nk s.mem B W bD (k + 1))
    (b := nk s.mem B W bE (k + 1)) (a' := nk t3.mem B W bD (k + 1)) (b' := nk t3.mem B W bE (k + 1))
    (s := S) (by exact_mod_cast G.1) (by exact_mod_cast (by have := G.2.1; omega : 0 < p)) (bodd G) (I.cf G) (I.cg G)
    (dD G).2 (dE G).2
  have r6t : t3.gpr .r6 = BitVec.ofNat 32 (32 * (nB k - i)) := by
    rw [r3.gpr _ (by decide), r2.gpr _ (by decide), c1]
  have hb := nB_le hk
  refine ⟨⟨g3.rest (u4.rest (ws := [.r6]) (by simp)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [k4]
    exact I.keep.trans (((k1.mono (by decide) (by decide)).trans (k2.mono (by decide) (by simp))).trans
      (k3.mono (by decide) (by simp)))
  · exact I.rest.trans ((r1.mono (by decide)).trans ((r2.mono (by simp)).trans ((r3.mono (by simp)).trans
      (u4.rest (by simp)))))
  · rw [u4.gpr, r6t]
    change BitVec.ofNat 32 (32 * (nB k - i)) - BitVec.ofNat 32 32 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega),
      show 32 * (nB k - i) - 32 = 32 * (nB k - (i + 1)) by omega]
  · rw [n3 bP (by simp), n2 bP (by simp), p1]; exact I.hP
  · rw [n3 bZ (by simp), n2 bZ (by simp), z1]; exact I.hZ
  · rw [k4, Keep.slot k3 (by decide) (by simp), iv2]
  · intro G
    obtain ⟨eD, -⟩ := w30 G
    have e : bw t.mem B sOdd = bw t1.mem B sOdd := by
      apply BitVec.eq_of_toNat_eq
      have h3 := Keep.slot k3 (e := sOdd) (by decide) (by simp)
      have h2 := Keep.slot k2 (e := sOdd) (by decide) (by simp)
      rw [k4]; exact h3.trans h2
    rw [e, wd, eD, hS1, batch_d]
  · intro G; rw [n3 bF (by simp)]; exact F2 G
  · intro G; rw [n3 bG (by simp)]; exact G2 G
  · intro G; rw [k4]; exact (dD G).1
  · intro G; rw [k4]; exact (dE G).1
  · intro G; rw [k4]; exact (cong G).1
  · intro G; rw [k4]; exact (cong G).2
  · intro G
    obtain ⟨hD, hE⟩ := I.de G
    have e : deRun p (oddInput p x) (i + 1) = deStep p S (deRun p (oddInput p x) i) := by
      show deStep p (invRun 30 p 0 (oddInput p x) i) _ = _
      rw [← deStep_m (m := (iv : Int)) G.1]
    rw [e, k4]
    simp only [deStep]
    rw [← hD, ← hE]
    exact ⟨red30_unique G.1 (dD G).1 (dD G).2, red30_unique G.1 (dE G).1 (dE G).2⟩
  · rw [hz, r6t]
    change (BitVec.ofNat 32 (32 * (nB k - i)) - BitVec.ofNat 32 32 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]; omega

/-- The `3 (k + 1)` batches. -/
theorem batches_ok {σ s : State} {B : BitVec 32} {Z W k N p iv x : Nat} (hN : 15 ≤ N) (hN' : N ≤ 256)
    (I : BI σ s B Z W k N p iv x 0) (hpk : p < 2 ^ (32 * k)) (hx : x < 2 ^ (32 * k)) :
    WP isa (.loop batch .ne) s fun t => BI σ t B Z W k N p iv x (nB k) := by
  refine WP.loop (M := isa) (fun n t => ∃ i, i + n = nB k ∧ 0 < n ∧ BI σ t B Z W k N p iv x i) ?_ (nB k) s
    ⟨0, by omega, by simp only [nB]; omega, I⟩
  rintro n t ⟨i, hin, hn, hi⟩
  refine WP.mono (batch_ok hN hN' hi (by omega) hpk hx) fun u ⟨hu, hz⟩ => ?_
  by_cases he : i + 1 = nB k
  · exact Or.inl ⟨by change some (!u.z) = some false; simp only [hz, he, decide_true, Bool.not_true], he ▸ hu⟩
  · exact Or.inr ⟨by change some (!u.z) = some true; simp only [hz, he, decide_false, Bool.not_false],
      n - 1, by omega, i + 1, by omega, by omega, hu⟩

end VG.Proof.Rsa.Arm.Inv

/-! ## The end of `inverse` on ARMv7: `|f|` to array 1 and `±d mod m` to array 3 -/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm

/-- `fSign`: `r11` := the sign bit of word `k` of `f`. -/
theorem fSign_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (hN : 8 ≤ N)
    {rest : List Instr} {Q : State → Prop}
    (kk : ∀ t, (t.gpr .r11).toNat = (if 2 ^ 31 ≤ aw s.mem B W bF (4 * k) then 1 else 0) →
      t.mem = s.mem → Rest [.r1, .r11, .r12] s t → Gk t B Z W k N → WP isa (.block rest) t Q) :
    WP isa (.block (fSign ++ rest)) s Q := by
  have fit := h.arr_fit (j := bF) (by simp only [bF]; omega)
  have hS : S W = 4 * (W + 2) := rfl
  have hk := h.kle
  rw [fSign, List.append_assoc]
  refine h.ptr_ok (r := .r12) (j := bF) (by decide) (by decide) fun s1 p1 r1 m1 h1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  have p2 : s2.gpr .r12 = B + BitVec.ofNat 32 (arr W bF + 4 * k) := by
    rw [u2.gpr, dpVal, p1, h1.r9, BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    have := h.wle
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have h2 : Gk s2 B Z W k N := h1.rest (u2.rest (ws := [.r12]) (by simp))
  refine wp_ldr (by decide) (h2.arrAddr (j := bF) (by simp only [bF]; omega) (d := 4 * k) p2 (by omega))
    (h2.read (by omega)) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun t u4 => kk t ?_ (by rw [u4.mem, u3.mem, u2.mem, m1])
    ((r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp)))))
    ((h2.rest (u3.rest (ws := [.r1]) (by simp))).rest (u4.rest (ws := [.r11]) (by simp)))
  rw [u4.gpr, u3.gpr, sign_bit, u2.mem, m1]; simp

theorem low_extend {m0 m : Mem} {base : Addr} {d k W : Nat} (hk : k ≤ W) (h0 : val32 m0 base d W = 0)
    (hup : val32 m base (d + 4 * k) (W - k) = val32 m0 base (d + 4 * k) (W - k)) :
    val32 m base d W = val32 m base d k := by
  have e := val32_append m base d k (W - k)
  rw [show k + (W - k) = W by omega, hup, VG.Proof.Rsa.KeyWorkspace.val32_zero_part h0 (by omega)] at e
  omega

theorem Keep.sub {B : BitVec 32} {W : Nat} {js : List Nat} {m m' : Mem} (h : Keep B W js [] m m') {j d c : Nat}
    (hd : d + 4 * c ≤ S W) (hj : ∀ y ∈ js, y ≠ j) (fit : arr W j + S W ≤ 2 ^ 64) :
    val32 m' (State.addr B) (arr W j + d) c = val32 m (State.addr B) (arr W j + d) c := by
  refine Outs.val32 h (fun r hr => ?_) (by omega)
  simp only [ranges, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨y, hy, rfl⟩ | ⟨e, he, rfl⟩
  · have := arr_disj (w := W) (hj y hy); dsimp only; omega
  · simp at he

/-- The end: `|f|` and `±d mod m`, each `k` words of zeros to the width `W`. -/
theorem finish_ok {σ s : State} {B : BitVec 32} {Z W k N p iv x : Nat} (hN : 15 ≤ N) (hN' : N ≤ 256)
    (I : BI σ s B Z W k N p iv x (nB k)) (hpk : p < 2 ^ (32 * k))
    (hf : Good p iv → (st p iv x (nB k)).f.natAbs < 2 ^ (32 * k)) :
    WP isa finish s fun t => Gk t B Z W k N ∧ Keep B W invArrs invSlots σ.mem t.mem ∧
      Rest (.r6 :: opRegs) σ t ∧ (Good p iv → nk t.mem B W 1 W = (st p iv x (nB k)).f.natAbs ∧
      nk t.mem B W 3 W < p ∧
      (nk t.mem B W 3 W : Int) ≡ (if (st p iv x (nB k)).f < 0 then -(nk s.mem B W bD (k + 1) : Int)
        else nk s.mem B W bD (k + 1)) [ZMOD p]) := by
  have g := I.geo
  have hW : 1 ≤ W := Nat.le_trans g.kpos g.kle
  have hkW := g.kle
  have hL : k + 1 ≤ W + 2 := by omega
  have fit := fun j (hj : j < N) => g.fit64 hj
  have hS : S W = 4 * (W + 2) := rfl
  set f := (st p iv x (nB k)).f
  have AW := fun (G : Good p iv) T => VG.Proof.Divstep.W32.abs_words (P := 2 ^ (32 * k)) (F := nk s.mem B W bF (k + 1)) (T := T)
    (Nat.two_pow_pos _) (by rw [← pow32_succ]; exact val32_lt _ _ _ _) (by rw [← pow32_succ]; exact I.hf G) (hf G)
  have sgn : Good p iv → ((2 ^ 31 ≤ aw s.mem B W bF (4 * k)) ↔ f < 0) := fun G => by
    rw [← top_bit]; exact (AW G 0).1
  simp only [finish, seqs]
  rw [WP.seq_iff]
  refine WP.mono (zeroW_ok g (o := 1) (by omega) hN') fun t1 ⟨g1, k1, z1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (zeroW_ok g1 (o := 3) (by omega) hN') fun t2 ⟨g2, k2, z2, r2⟩ => ?_
  have kF : ∀ {m m' : Mem} {js : List Nat}, Keep B W js [] m m' → bF ∉ js →
      nk m' B W bF (k + 1) = nk m B W bF (k + 1) ∧ aw m' B W bF (4 * k) = aw m B W bF (4 * k) :=
    fun kk hj => ⟨Keep.nk kk hL (fun y hy e => hj (e ▸ hy)) (by simp) (fit _ (by simp only [bF]; omega)),
      Keep.aw kk (by omega) (fun y hy e => hj (e ▸ hy)) (fit _ (by simp only [bF]; omega))⟩
  have kn : ∀ {m m' : Mem} {js : List Nat} (j : Nat), Keep B W js [] m m' → j ∉ js → j < N →
      nk m' B W j (k + 1) = nk m B W j (k + 1) :=
    fun j kk hj hjN => Keep.nk kk hL (fun y hy e => hj (e ▸ hy)) (by simp) (fit _ hjN)
  obtain ⟨F2, A2⟩ : nk t2.mem B W bF (k + 1) = nk s.mem B W bF (k + 1) ∧
      aw t2.mem B W bF (4 * k) = aw s.mem B W bF (4 * k) := by
    obtain ⟨a, b⟩ := kF k2 (by decide); obtain ⟨c, d⟩ := kF k1 (by decide)
    exact ⟨a.trans c, b.trans d⟩
  have Z2 : nk t2.mem B W bZ (k + 1) = 0 := by
    rw [kn bZ k2 (by decide) (by simp only [bZ]; omega), kn bZ k1 (by decide) (by simp only [bZ]; omega), I.hZ]
  rw [WP.seq_iff]
  refine WP.mono (sub1_ok g2 (o := bT1) (a := bZ) (b := bF) (by ix) (by ix) (by ix) hN' (by decide) (by decide))
    fun t3 ⟨g3, k3, v3, b3, r3⟩ => ?_
  rw [Z2, F2] at v3
  obtain ⟨F3, A3⟩ := kF k3 (by decide)
  rw [WP.seq_iff, ← List.append_nil fSign]
  refine fSign_ok g3 (by omega) fun t4 b4 m4 r4 g4 => WP.block_nil ?_
  rw [A3, A2] at b4
  rw [WP.seq_iff]
  refine WP.mono (sel1_ok true g4 (o := 1) (a := bF) (b := bT1) (by omega) (by ix) (by ix) hN'
    (by rw [b4]; split <;> decide)) fun t5 ⟨g5, k5, v5, r5, o5⟩ => ?_
  rw [b4, m4] at v5
  simp only [len1, ↓reduceIte] at v5 o5
  -- `|f|` in array 1.
  have one : Good p iv → nk t5.mem B W 1 k = f.natAbs := fun G => by
    rw [v5]
    by_cases hneg : f < 0
    · have : 2 ^ 31 ≤ aw s.mem B W bF (4 * k) := (sgn G).mpr hneg
      simp only [this, ↓reduceIte, Nat.one_ne_zero]
      simp only [nk]; rw [val32_low]
      exact (AW G _).2.2 hneg _ (by rw [← pow32_succ]; simpa using v3) (by rw [← pow32_succ]; exact val32_lt _ _ _ _)
    · have : ¬ 2 ^ 31 ≤ aw s.mem B W bF (4 * k) := fun h => hneg ((sgn G).mp h)
      simp only [this, ↓reduceIte]
      simp only [nk]; rw [val32_low]
      have e : nk t3.mem B W bF (k + 1) % 2 ^ (32 * k) = f.natAbs := by rw [F3, F2]; exact (AW G 0).2.1 hneg
      exact e
  have Z5 : nk t5.mem B W bZ (k + 1) = 0 := by
    rw [kn bZ k5 (by decide) (by ix), m4, kn bZ k3 (by decide) (by ix), Z2]
  have P5 : nk t5.mem B W bP (k + 1) = p := by
    rw [kn bP k5 (by decide) (by ix), m4, kn bP k3 (by decide) (by ix), kn bP k2 (by decide) (by ix),
      kn bP k1 (by decide) (by ix), I.hP]
  have D5 : nk t5.mem B W bD (k + 1) = nk s.mem B W bD (k + 1) := by
    rw [kn bD k5 (by decide) (by ix), m4, kn bD k3 (by decide) (by ix), kn bD k2 (by decide) (by ix),
      kn bD k1 (by decide) (by ix)]
  rw [WP.seq_iff]
  refine WP.mono (sub1_ok g5 (o := bT2) (a := bP) (b := bD) (by ix) (by ix) (by ix) hN' (by decide) (by decide))
    fun t6 ⟨g6, k6, v6, b6, r6⟩ => ?_
  rw [P5, D5] at v6
  obtain ⟨F6, A6⟩ := kF k6 (by decide)
  obtain ⟨F5, A5⟩ := kF k5 (by decide)
  rw [WP.seq_iff, ← List.append_nil fSign]
  refine fSign_ok g6 (by omega) fun t7 b7 m7 r7 g7 => WP.block_nil ?_
  rw [A6, A5, m4, A3, A2] at b7
  rw [WP.seq_iff]
  refine WP.mono (sel1_ok false g7 (o := bT2) (a := bD) (b := bT2) (by ix) (by ix) (by ix) hN'
    (by rw [b7]; split <;> decide)) fun t8 ⟨g8, k8, v8, r8, _⟩ => ?_
  rw [b7, m7] at v8
  simp only [len1, Bool.false_eq_true, ↓reduceIte] at v8
  rw [kn bD k6 (by decide) (by ix), D5] at v8
  have P8 : nk t8.mem B W bP (k + 1) = p := by
    rw [kn bP k8 (by decide) (by ix), m7, kn bP k6 (by decide) (by ix), P5]
  refine WP.mono (csub1_ok true g8 (o := 3) (a := bT2) hN hN' (by omega) (by ix) (by decide))
    fun t ⟨gt, kt, vt, rt, ot⟩ => ?_
  rw [v8, P8] at vt
  simp only [len1, ↓reduceIte] at vt ot
  have hk4 : 4 * k + 4 * (W - k) ≤ S W := by omega
  have f1 := fit 1 (by omega)
  have f3 := fit 3 (by omega)
  have kup : ∀ {m m' : Mem} {js : List Nat} (j : Nat), Keep B W js [] m m' → (∀ y ∈ js, y ≠ j) → j < N →
      val32 m' (State.addr B) (arr W j + 4 * k) (W - k) = val32 m (State.addr B) (arr W j + 4 * k) (W - k) :=
    fun j kk hj hjN => Keep.sub kk hk4 hj (fit _ hjN)
  -- Array 1.
  have up1 : val32 t.mem (State.addr B) (arr W 1 + 4 * k) (W - k) =
      val32 t1.mem (State.addr B) (arr W 1 + 4 * k) (W - k) := by
    rw [kup 1 kt (by decide) (by omega), kup 1 k8 (by decide) (by omega), m7, kup 1 k6 (by decide) (by omega),
      o5.val32 (by omega) (by omega), m4, kup 1 k3 (by decide) (by omega), kup 1 k2 (by decide) (by omega)]
  have lo1 : nk t.mem B W 1 k = nk t5.mem B W 1 k := by
    have h1 : ∀ {m m' : Mem} {js : List Nat}, Keep B W js [] m m' → (∀ y ∈ js, y ≠ 1) →
        nk m' B W 1 k = nk m B W 1 k := fun kk hj => by
      have := Keep.sub kk (d := 0) (c := k) (by omega) hj f1; simpa using this
    rw [h1 kt (by decide), h1 k8 (by decide), m7, h1 k6 (by decide)]
  -- Array 3.
  have up3 : val32 t.mem (State.addr B) (arr W 3 + 4 * k) (W - k) =
      val32 t2.mem (State.addr B) (arr W 3 + 4 * k) (W - k) := by
    rw [Outs.val32 ot (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · dsimp only; omega
        · have := arr_disj (w := W) (show 3 ≠ bT1 by decide); dsimp only; omega) (by omega),
      kup 3 k8 (by decide) (by omega), m7, kup 3 k6 (by decide) (by omega), kup 3 k5 (by decide) (by omega), m4,
      kup 3 k3 (by decide) (by omega)]
  have Tb : Good p iv → ∀ b, nk t6.mem B W bT2 (k + 1) + nk s.mem B W bD (k + 1) = p + 2 ^ (32 * (k + 1)) * b →
      nk t6.mem B W bT2 (k + 1) = p - nk s.mem B W bD (k + 1) := by
    intro G b hb
    have hT := val32_lt t6.mem (State.addr B) (arr W bT2) (k + 1)
    have hD := I.dv G
    change nk t6.mem B W bT2 (k + 1) < _ at hT
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · omega
    · have : 2 ^ (32 * (k + 1)) ≤ 2 ^ (32 * (k + 1)) * b := Nat.le_mul_of_pos_right _ hb0
      omega
  have sel : Good p iv → (if (if 2 ^ 31 ≤ aw s.mem B W bF (4 * k) then 1 else 0) = 0 then nk s.mem B W bD (k + 1)
      else nk t6.mem B W bT2 (k + 1)) = if f < 0 then nk t6.mem B W bT2 (k + 1) else nk s.mem B W bD (k + 1) := fun G => by
    by_cases h : f < 0
    · simp only [(sgn G).mpr h, ↓reduceIte, Nat.one_ne_zero, h]
    · have : ¬ 2 ^ 31 ≤ aw s.mem B W bF (4 * k) := fun h' => h ((sgn G).mp h')
      simp only [this, ↓reduceIte, h]
  refine ⟨gt, ?_, ?_, fun G => ?_⟩
  · rw [m4] at k5
    rw [m7] at k8
    exact I.keep.trans ((((k1.mono (by decide) (by simp)).trans (k2.mono (by decide) (by simp))).trans
      (k3.mono (by decide) (by simp))).trans ((k5.mono (by decide) (by simp)).trans ((k6.mono (by decide) (by simp)).trans
      ((k8.mono (by decide) (by simp)).trans (kt.mono (by decide) (by simp))))))
  · exact I.rest.trans (((r1.mono (by simp)).trans ((r2.mono (by simp)).trans ((r3.mono (by simp)).trans
      ((r4.mono (by simp)).trans ((r5.mono (by simp)).trans ((r6.mono (by simp)).trans ((r7.mono (by simp)).trans
        ((r8.mono (by simp)).trans (rt.mono (by simp)))))))))))
  · rw [sel G] at vt
    obtain ⟨Xp, Xc⟩ := VG.Proof.Divstep.W32.sel_mod (I.dv G) hpk.le (Tb G) ⟨_, v6⟩ vt
    refine ⟨?_, ?_, ?_⟩
    · rw [nk, low_extend hkW z1 up1]; change nk t.mem B W 1 k = _; rw [lo1, one G]
    · rw [nk, low_extend hkW z2 up3]; change nk t.mem B W 3 k < _; exact Xp
    · rw [nk, low_extend hkW z2 up3]; change (nk t.mem B W 3 k : Int) ≡ _ [ZMOD p]; exact Xc

end VG.Proof.Rsa.Arm.Inv

/-! ## `-m⁻¹ mod 2^32` for `inverse` on ARMv7: four Newton steps from `m` -/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm
open VG.Proof.Mont.Arm.Dyn (newton_step newton_val)
open VG.Proof.Bignum (odd_sq emod_pow_weaken)

/-- `r2 := r2 (2 - r5 r2)`. -/
theorem newtonStep_ok (s : State) {j : Nat} {P : Prop} (hj : 2 * j ≤ 32)
    (h : P → (((s.gpr .r5).toNat : Int) * (s.gpr .r2).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newtonStep) s fun t =>
      (P → (((t.gpr .r5).toNat : Int) * (t.gpr .r2).toNat - 1) % (2 ^ (2 * j) : Int) = 0) ∧
      Rest [.r2, .r3, .r4] s t ∧ t.mem = s.mem := by
  unfold newtonStep
  refine wp_mul fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_dp (op2_reg _ _) fun s₃ u₃ => wp_mul fun t u₄ =>
    WP.block_nil ⟨?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · intro hP
    have e5 : t.gpr .r5 = s.gpr .r5 := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    have e2 : t.gpr .r2 = s.gpr .r2 * ((0x2 : BitVec 16).setWidth 32 - s.gpr .r5 * s.gpr .r2) := by
      rw [u₄.gpr, u₃.other .r2 (by decide), u₂.other .r2 (by decide), u₁.other .r2 (by decide), u₃.gpr, dpVal,
        u₂.gpr, u₂.other .r4 (by decide), u₁.gpr]
    rw [e5]
    exact newton_step hj (h hP) (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp (by rw [e2]; exact newton_val _ _))
  · exact ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans ((u₃.rest (by decide)).trans (u₄.rest (by decide)))

/-- `negInv`: the header word `sB` := `-m⁻¹ mod 2^32` for the odd low word of `[bP]`. -/
theorem negInv_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (hN : 3 ≤ N)
    {P : Prop} (hodd : P → (s.mem.readW (off (State.addr B) (arr W bP + 0)) 32).toNat % 2 = 1) {rest : List Instr}
    {Q : State → Prop}
    (kk : ∀ t, (P → ((s.mem.readW (off (State.addr B) (arr W bP + 0)) 32).toNat * slot t.mem B sB + 1) % 2 ^ 32 = 0) →
      Keep B W [] [sB] s.mem t.mem → Rest [.r0, .r2, .r3, .r4, .r5] s t → Gk t B Z W k N →
      WP isa (.block rest) t Q) :
    WP isa (.block (negInv ++ rest)) s Q := by
  have fit := h.arr_fit (j := bP) (by simp only [bP]; omega)
  have hS : S W = 4 * (W + 2) := rfl
  have hz : hdr ≤ Z := Nat.le_trans (Nat.le_add_right _ _) h.fits
  simp only [negInv, List.append_assoc, List.cons_append, List.nil_append]
  refine h.ptr_ok (r := .r0) (j := bP) (by decide) (by decide) fun s1 p1 r1 m1 h1 => ?_
  refine wp_ldr (by decide) (VG.Proof.Rsa.Arm.Inv.Gk.arrAddr h1 (j := bP) (by simp only [bP]; omega) (d := 0)
    (by simpa using p1) (by omega)) (h1.read (by omega)) fun s2 u2 => ?_
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  generalize hA : s.mem.readW (off (State.addr B) (arr W bP + 0)) 32 = a at hodd kk
  have a3 : s3.gpr .r5 = a := by rw [u3.other _ (by decide), u2.gpr, m1, Nat.add_zero, ← hA, Nat.add_zero]
  have x3 : s3.gpr .r2 = a := by rw [u3.gpr, u2.gpr, m1, Nat.add_zero, ← hA, Nat.add_zero]
  have j3 : P → (((s3.gpr .r5).toNat : Int) * (s3.gpr .r2).toNat - 1) % (2 ^ 3 : Int) = 0 := fun hP => by
    rw [a3, x3]
    have := odd_sq a.toNat (hodd hP)
    omega
  apply WP.block_append_iff.mpr
  refine WP.mono (newtonStep_ok s3 (by decide) j3) fun s4 ⟨j4, r4, m4⟩ => ?_
  apply WP.block_append_iff.mpr
  refine WP.mono (newtonStep_ok s4 (by decide) j4) fun s5 ⟨j5, r5, m5⟩ => ?_
  apply WP.block_append_iff.mpr
  refine WP.mono (newtonStep_ok s5 (by decide) j5) fun s6 ⟨j6, r6, m6⟩ => ?_
  apply WP.block_append_iff.mpr
  refine WP.mono (newtonStep_ok s6 (j := 16) (by decide) (fun hP => emod_pow_weaken (by decide) (j6 hP))) fun s7 ⟨j7, r7, m7⟩ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s8 u8 => ?_
  have h8 : Gk s8 B Z W k N := ((((((h1.rest (u2.rest (ws := [.r5]) (by simp))).rest (u3.rest (ws := [.r2]) (by simp))).rest
    r4).rest r5).rest r6).rest r7).rest (u8.rest (ws := [.r2]) (by simp))
  have hsl : sB + 4 ≤ hdr := by decide
  refine wp_str (by decide) (by rw [h8.r8]; exact h8.addr (by omega)) (h8.write (by omega)) fun t u9 => ?_
  apply kk t
  · intro hP
    replace j7 := j7 hP
    have e5 : s7.gpr .r5 = a := by
      rw [r7.gpr _ (by decide), r6.gpr _ (by decide), r5.gpr _ (by decide), r4.gpr _ (by decide), a3]
    rw [u9.mem, slot_write_self, u8.gpr, dpVal, VG.Proof.Rsa.Arm.Inv.sub_shl1, BitVec.toNat_sub]
    rw [e5] at j7
    generalize s7.gpr .r2 = y at *
    have hy := y.isLt
    have ha := a.isLt
    rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero]
    obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero j7
    rcases Nat.eq_zero_or_pos y.toNat with h0 | h0
    · rw [h0] at hc; omega
    · rw [show (2 ^ 32 - y.toNat + 0) % 2 ^ 32 = 2 ^ 32 - y.toNat by omega]
      apply Nat.mod_eq_zero_of_dvd
      have hd : ((2 ^ 32 : Nat) : Int) ∣ ((a.toNat * (2 ^ 32 - y.toNat) + 1 : Nat) : Int) := by
        refine ⟨(a.toNat : Int) - c, ?_⟩
        have e : ((2 ^ 32 - y.toNat : Nat) : Int) = 2 ^ 32 - y.toNat := by omega
        rw [Nat.cast_add, Nat.cast_mul, e]
        push_cast
        have : (2 : Int) ^ (2 * 16) = 2 ^ 32 := by norm_num
        rw [this] at hc
        linear_combination -hc
      exact Int.natCast_dvd_natCast.mp hd
  · rw [u9.mem, u8.mem, m7, m6, m5, m4, u3.mem, u2.mem, m1]
    exact keep_write _ _ (by simp) (by simp only [sB, hdr] at *; omega)
  · exact (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans ((r4.mono (by simp)).trans
      ((r5.mono (by simp)).trans ((r6.mono (by simp)).trans ((r7.mono (by simp)).trans ((u8.rest (by simp)).trans
        (u9.rest _))))))))
  · exact h8.rest (u9.rest [])

end VG.Proof.Rsa.Arm.Inv

/-! ## The start of `inverse` on ARMv7: `m`, `f = m`, `g = oddInput m a`, `d = 0`, `e = 1` -/

namespace VG.Proof.Rsa.Arm.Inv
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Proof.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm
open VG.Proof.Rsa.Divstep (oddInput)

/-- A word stored at byte `d` of array `j`: the rest of the array is kept. -/
theorem storeAt_ok {s : State} {B : BitVec 32} {Z W k N j d : Nat} (h : Gk s B Z W k N) (hj : j < N)
    (hd : d + 4 ≤ S W) (hd' : d < 4096) {t r : Reg} (p0 : s.gpr r = B + BitVec.ofNat 32 (arr W j))
    {rest : List Instr} {Q : State → Prop}
    (kk : ∀ u, u.mem = s.mem.writeW (off (State.addr B) (arr W j + d)) (s.gpr t) → Rest [] s u →
      Gk u B Z W k N → WP isa (.block rest) u Q) :
    WP isa (.block (.str t r d :: rest)) s Q := by
  have fit := h.arr_fit hj
  refine wp_str hd' (h.arrAddr (j := j) hj (d := 0) (by simpa using p0) (by omega)) (h.write (by omega))
    fun u mu => ?_
  exact kk u (by rw [mu.mem]; simp) (mu.rest []) (h.rest (mu.rest []))

theorem keep_word {B : BitVec 32} {W j d : Nat} {js : List Nat} (m : Mem) (v : BitVec 32) (hj : j ∈ js)
    (hd : d + 4 ≤ S W) (fit : arr W j + d + 4 ≤ 2 ^ 64) :
    Keep B W js [] m (m.writeW (off (State.addr B) (arr W j + d)) v) :=
  Keep.of_arr (writeW32_outside m _ v fit) hd hj

/-- Word `k` of `[o]` := 0. -/
theorem topZero_ok {s : State} {B : BitVec 32} {Z W k N o : Nat} (h : Gk s B Z W k N) (ho : o < N) (hN : N ≤ 256)
    {rest : List Instr} {Q : State → Prop}
    (kk : ∀ u, Keep B W [o] [] s.mem u.mem → nk u.mem B W o (k + 1) = nk s.mem B W o k →
      Rest [.r0, .r1] s u → Gk u B Z W k N → WP isa (.block rest) u Q) :
    WP isa (.block (topZero o ++ rest)) s Q := by
  have fit := h.arr_fit ho
  have hS : S W = 4 * (W + 2) := rfl
  have hk := h.kle
  have hW := h.wle
  have hnw := h.nowrap
  rw [topZero, List.append_assoc]
  refine h.ptr_ok (r := .r0) (j := o) (by decide) (by omega) fun s1 p1 r1 m1 h1 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s2 u2 => ?_
  have p2 : s2.gpr .r0 = B + BitVec.ofNat 32 (arr W o + 4 * k) := by
    rw [u2.gpr, dpVal, p1, h1.r9, BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    omega
  have h2 : Gk s2 B Z W k N := h1.rest (u2.rest (ws := [.r0]) (by simp))
  refine wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  have h3 : Gk s3 B Z W k N := h2.rest (u3.rest (ws := [.r1]) (by simp))
  refine wp_str (by decide) (h3.arrAddr (j := o) ho (d := 4 * k) (by rw [u3.other _ (by decide)]; exact p2)
    (by omega)) (h3.write (by omega)) fun u mu => kk u ?_ ?_ ?_ (h3.rest (mu.rest []))
  · rw [mu.mem, u3.mem, u2.mem, m1]
    exact keep_word _ _ (by simp) (by omega) (by omega)
  · rw [mu.mem, u3.mem, u2.mem, m1, Nat.add_zero, u3.gpr]
    change val32 _ _ _ (k + 1) = _
    rw [val32_succ]
    rw [show w32 (s.mem.writeW (off (State.addr B) (arr W o + 4 * k)) (0 : BitVec 32)) (State.addr B) (arr W o + 4 * k) = 0
      from by rw [w32_write_self]; rfl]
    rw [Nat.mul_zero, Nat.add_zero]
    exact (writeW32_outside s.mem (State.addr B) (d := arr W o + 4 * k) 0 (by omega)).val32 (by omega) (by omega)
  · exact (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (mu.rest _)))

/-- `r11` := 1 if `[0]` is even, else 0. -/
theorem evenBit_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (hN : 1 ≤ N)
    {Q : State → Prop}
    (kk : ∀ u, (u.gpr .r11).toNat = 1 - aw s.mem B W 0 0 % 2 → u.mem = s.mem → Rest [.r0, .r1, .r11] s u →
      Gk u B Z W k N → Q u) :
    WP isa (.block (ptr .r0 0 ++ ([.ldr .r1 .r0 0, .mvn .r1 (.reg .r1), .dp .and .r11 .r1 (.imm 1)] : List Instr))) s Q := by
  have fit := h.arr_fit (j := 0) (by omega)
  have hS : S W = 4 * (W + 2) := rfl
  refine h.ptr_ok (r := .r0) (j := 0) (by decide) (by decide) fun s1 p1 r1 m1 h1 => ?_
  refine wp_ldr (by decide) (h1.arrAddr (j := 0) (by omega) (d := 0) (by simpa using p1) (by omega))
    (h1.read (by omega)) fun s2 u2 => ?_
  refine VG.Proof.X25519.Arm.WP.cons (s' := s2.setReg .r1 (~~~(s2.gpr .r1))) (by simp only [exec, Op2.eval,
    Option.map_some]) ?_
  have u3 := Upd.setReg s2 .r1 (~~~(s2.gpr .r1))
  refine wp_dp (op2_imm (by decide)) fun u u4 => WP.block_nil (kk u ?_ ?_ ?_ ?_)
  · rw [u4.gpr, dpVal, u3.gpr, u2.gpr, m1]
    simp only [Nat.add_zero, aw, w32]
    generalize s.mem.readW (off (State.addr B) (arr W 0)) 32 = y
    rw [BitVec.toNat_and, BitVec.toNat_not, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]
    have := y.isLt
    omega
  · rw [u4.mem, u3.mem, u2.mem, m1]
  · exact (r1.mono (by simp)).trans ((u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp))))
  · exact ((h1.rest (u2.rest (ws := [.r1]) (by simp))).rest (u3.rest (ws := [.r1]) (by simp))).rest
      (u4.rest (ws := [.r11]) (by simp))

/-- `setOne bE` on `[bE] = 0`: `[bE] = 1`. -/
theorem setOneE_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) (hN : 8 ≤ N)
    (hz : nk s.mem B W bE (k + 1) = 0) {rest : List Instr} {Q : State → Prop}
    (kk : ∀ u, Keep B W [bE] [] s.mem u.mem → nk u.mem B W bE (k + 1) = 1 → Rest [.r0, .r1] s u →
      Gk u B Z W k N → WP isa (.block rest) u Q) :
    WP isa (.block (setOne bE ++ rest)) s Q := by
  have fit := h.arr_fit (j := bE) (by simp only [bE]; omega)
  have hS : S W = 4 * (W + 2) := rfl
  have hnw := h.nowrap
  have hkW := h.kle
  rw [setOne, List.append_assoc]
  refine h.ptr_ok (r := .r0) (j := bE) (by decide) (by decide) fun s1 p1 r1 m1 h1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  have h2 : Gk s2 B Z W k N := h1.rest (u2.rest (ws := [.r1]) (by simp))
  refine storeAt_ok h2 (j := bE) (by simp only [bE]; omega) (d := 0) (by omega) (by decide)
    (by rw [u2.other _ (by decide)]; exact p1) fun u mu gu hu => kk u ?_ ?_ ?_ hu
  · rw [mu, u2.mem, m1]; exact keep_word _ _ (by simp) (by omega) (by omega)
  · rw [mu, u2.mem, m1, u2.gpr]
    change val32 _ _ _ (k + 1) = 1
    rw [val32, Nat.add_zero, w32_write_self]
    rw [(writeW32_outside s.mem (State.addr B) (d := arr W bE) _ (by omega)).val32 (d := arr W bE + 4) (k := k)
      (by omega) (by omega)]
    have := VG.Proof.Rsa.KeyWorkspace.val32_zero_part (a := 1) (c := k) hz (by omega)
    rw [Nat.mul_one] at this
    rw [this]; rfl
  · exact (r1.mono (by simp)).trans ((u2.rest (by simp)).trans (gu.mono (by simp)))

/-- `start`: `δ = 1` and `32 · 3 (k + 1)` in `r6`. -/
theorem start_ok {s : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk s B Z W k N) {Q : State → Prop}
    (kk : ∀ u, Keep B W [] [sOdd] s.mem u.mem → bw u.mem B sOdd = 1 → u.gpr .r6 = BitVec.ofNat 32 (32 * nB k) →
      Rest [.r1, .r6] s u → Gk u B Z W k N → Q u) :
    WP isa (.block start) s Q := by
  have hz : hdr ≤ Z := Nat.le_trans (Nat.le_add_right _ _) h.fits
  have hk := Nat.le_trans h.kle h.wle
  unfold start
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have h1 : Gk s1 B Z W k N := h.rest (u1.rest (ws := [.r1]) (by simp))
  have hsl : sOdd + 4 ≤ hdr := by decide
  refine wp_str (by decide) (by rw [h1.r8]; exact h1.addr (by simp only [sOdd, hdr] at *; omega))
    (h1.write (by simp only [sOdd, hdr] at *; omega)) fun s2 u2 => ?_
  have h2 : Gk s2 B Z W k N := h1.rest (u2.rest [])
  refine wp_dp (op2_imm (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_lsl (by decide)) fun s4 u4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun u u5 => WP.block_nil (kk u ?_ ?_ ?_ ?_ ?_)
  · rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; exact keep_write _ _ (by simp) (by simp only [sOdd]; omega)
  · rw [u5.mem, u4.mem, u3.mem, u2.mem]; exact bw_write_self _ _ _ _ |>.trans u1.gpr
  · rw [u5.gpr, dpVal, u4.gpr, u3.gpr, dpVal, u2.gpr, h1.r9]
    have e1 : (BitVec.ofNat 32 k + 1).toNat = k + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]; omega
    have e2 : ((BitVec.ofNat 32 k + 1) <<< 5).toNat = 32 * (k + 1) := by rw [toNat_shl, e1]; omega
    have e3 : ((BitVec.ofNat 32 k + 1) <<< 5 <<< 1).toNat = 64 * (k + 1) := by rw [toNat_shl, e2]; omega
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, e2, e3, BitVec.toNat_ofNat]
    simp only [nB]; omega
  · exact (u1.rest (by simp)).trans ((u2.rest _).trans ((u3.rest (by simp)).trans ((u4.rest (by simp)).trans
      (u5.rest (by simp)))))
  · exact ((h2.rest (u3.rest (ws := [.r6]) (by simp))).rest (u4.rest (ws := [.r6]) (by simp))).rest
      (u5.rest (ws := [.r6]) (by simp))

/-- `init`: the state before the batches. -/
theorem init_ok {σ : State} {B : BitVec 32} {Z W k N m a : Nat} (h : Gk σ B Z W k N) (hN : 15 ≤ N) (hN' : N ≤ 256)
    (hm : nk σ.mem B W aM k = m) (ha : nk σ.mem B W 0 k = a)
    (hmk : m < 2 ^ (32 * k)) (hak : a < 2 ^ (32 * k)) :
    WP isa init σ fun s => ∃ iv, (m % 2 = 1 → (m * iv + 1) % 2 ^ 32 = 0) ∧ BI σ s B Z W k N m iv a 0 := by
  have hL : k + 1 ≤ W + 2 := by have := h.kle; omega
  have fit := fun j (hj : j < N) => h.fit64 hj
  have hS : S W = 4 * (W + 2) := rfl
  have kn : ∀ {m m' : Mem} {js : List Nat} (j : Nat), Keep B W js [] m m' → (∀ y ∈ js, y ≠ j) → j < N →
      nk m' B W j (k + 1) = nk m B W j (k + 1) :=
    fun j kk hj hjN => Keep.nk kk hL hj (by simp) (fit _ hjN)
  have hM : 2 ^ (32 * k) < 2 ^ (32 * (k + 1)) := Nat.pow_lt_pow_right (by decide) (by omega)
  simp only [init, seqs]
  rw [WP.seq_iff]
  refine WP.mono (copy1_ok true h (o := bP) (a := aM) (by ix) (by simp only [aM]; omega) hN' (by decide))
    fun s1 ⟨g1, k1, v1, r1, _⟩ => ?_
  simp only [len1, ↓reduceIte] at v1
  rw [WP.seq_iff, ← List.append_nil (topZero bP)]
  refine topZero_ok g1 (o := bP) (by ix) hN' fun s2 k2 v2 r2 g2 => WP.block_nil ?_
  rw [v1, hm] at v2
  rw [WP.seq_iff, ← List.append_nil (topZero 0)]
  refine topZero_ok g2 (o := 0) (by omega) hN' fun s3 k3 v3 r3 g3 => WP.block_nil ?_
  have a3 : nk s3.mem B W 0 (k + 1) = a := by
    rw [v3]
    have := Keep.sub k2 (j := 0) (d := 0) (c := k) (by omega) (by decide) (fit 0 (by omega))
    have := Keep.sub k1 (j := 0) (d := 0) (c := k) (by omega) (by decide) (fit 0 (by omega))
    simp only [Nat.add_zero] at *
    change val32 _ _ _ _ = _
    rw [‹val32 s2.mem _ _ k = _›, ‹val32 s1.mem _ _ k = _›]; exact ha
  have p3 : nk s3.mem B W bP (k + 1) = m := by rw [kn bP k3 (by decide) (by ix), v2]
  rw [WP.seq_iff]
  refine WP.mono (zero1_ok g3 (o := bT1) (by ix) hN') fun s4 ⟨g4, k4, z4, r4⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (sub1_ok g4 (o := bA1) (a := bT1) (b := bP) (by ix) (by ix) (by ix) hN' (by decide) (by decide))
    fun s5 ⟨g5, k5, v5, b5, r5⟩ => ?_
  rw [z4, kn bP k4 (by decide) (by ix), p3] at v5
  rw [WP.seq_iff]
  refine evenBit_ok g5 (by omega) fun s6 b6 m6 r6 g6 => ?_
  have w0 : aw s5.mem B W 0 0 = a % 2 ^ 32 := by
    rw [word0 _ _ _ _ k, kn 0 k5 (by decide) (by omega), kn 0 k4 (by decide) (by omega), a3]
  rw [w0] at b6
  rw [WP.seq_iff]
  refine WP.mono (sel1_ok false g6 (o := bT2) (a := bT1) (b := bA1) (by ix) (by ix) (by ix) hN' (by omega))
    fun s7 ⟨g7, k7, v7, r7, _⟩ => ?_
  simp only [len1, Bool.false_eq_true, ↓reduceIte] at v7
  rw [b6, m6, kn bT1 k5 (by decide) (by ix), z4] at v7
  rw [WP.seq_iff]
  refine WP.mono (sub1_ok g7 (o := bG) (a := 0) (b := bT2) (by ix) (by omega) (by ix) hN' (by decide) (by decide))
    fun s8 ⟨g8, k8, v8, b8, r8⟩ => ?_
  rw [v7, kn 0 k7 (by decide) (by omega), m6, kn 0 k5 (by decide) (by omega), kn 0 k4 (by decide) (by omega), a3] at v8
  rw [WP.seq_iff]
  refine WP.mono (copy1_ok false g8 (o := bF) (a := bP) (by ix) (by ix) hN' (by decide)) fun s9 ⟨g9, k9, v9, r9, _⟩ => ?_
  simp only [len1, Bool.false_eq_true, ↓reduceIte] at v9
  have p8 : nk s8.mem B W bP (k + 1) = m := by
    rw [kn bP k8 (by decide) (by ix), kn bP k7 (by decide) (by ix), m6, kn bP k5 (by decide) (by ix),
      kn bP k4 (by decide) (by ix), p3]
  rw [p8] at v9
  rw [WP.seq_iff]
  refine WP.mono (zero1_ok g9 (o := bZ) (by ix) hN') fun s10 ⟨g10, k10, z10, r10⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (zero1_ok g10 (o := bD) (by ix) hN') fun s11 ⟨g11, k11, z11, r11⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (zero1_ok g11 (o := bE) (by ix) hN') fun s12 ⟨g12, k12, z12, r12⟩ => ?_
  rw [List.append_assoc]
  refine setOneE_ok g12 (by omega) z12 fun s13 k13 e13 r13 g13 => ?_
  have hP13 : nk s13.mem B W bP (k + 1) = m := by
    rw [kn bP k13 (by decide) (by ix), kn bP k12 (by decide) (by ix), kn bP k11 (by decide) (by ix),
      kn bP k10 (by decide) (by ix), kn bP k9 (by decide) (by ix), p8]
  have odd13 : m % 2 = 1 → (s13.mem.readW (off (State.addr B) (arr W bP + 0)) 32).toNat % 2 = 1 := fun hmo => by
    have := word0 s13.mem B W bP k
    simp only [aw, w32] at this
    rw [this, hP13]; omega
  refine negInv_ok g13 (by omega) odd13 fun s14 i14 k14 r14 g14 => ?_
  refine start_ok g14 fun t k15 d15 c15 r15 g15 => ⟨slot s14.mem B sB, ?_, ?_⟩
  · intro hmo
    have : (s13.mem.readW (off (State.addr B) (arr W bP + 0)) 32).toNat % 2 ^ 32 = m % 2 ^ 32 := by
      have := word0 s13.mem B W bP k
      simp only [aw, w32] at this
      rw [this, hP13]; omega
    rw [Nat.add_mod, Nat.mul_mod, ← this, ← Nat.mul_mod, ← Nat.add_mod]; exact i14 hmo
  have ks : ∀ {m m' : Mem} {ds : List Nat}, Keep B W [] ds m m' → (∀ d ∈ ds, d + 4 ≤ hdr) →
      ∀ j, j < N → nk m' B W j (k + 1) = nk m B W j (k + 1) := fun kk hd j hj =>
    Keep.nk kk hL (by simp) hd (fit _ hj)
  have kt : ∀ j, j < N → nk t.mem B W j (k + 1) = nk s13.mem B W j (k + 1) := fun j hj => by
    rw [ks k15 (by decide) j hj, ks k14 (by decide) j hj]
  refine ⟨g15, ?_, ?_, by rw [c15, Nat.sub_zero], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m6] at k7
    exact (((((((k1.mono (by decide) (by simp)).trans (k2.mono (by decide) (by simp))).trans
      (k3.mono (by decide) (by simp))).trans (k4.mono (by decide) (by simp))).trans ((k5.mono (by decide) (by simp)).trans
      (k7.mono (by decide) (by simp)))).trans ((k8.mono (by decide) (by simp)).trans (k9.mono (by decide) (by simp)))).trans
      ((k10.mono (by decide) (by simp)).trans (k11.mono (by decide) (by simp)))).trans ((k12.mono (by decide) (by simp)).trans
      ((k13.mono (by decide) (by simp)).trans ((k14.mono (by decide) (by simp)).trans (k15.mono (by decide) (by simp)))))
  · have R : ∀ {ws : List Reg} {a b : State}, Rest ws a b → (∀ r ∈ ws, r ∈ Reg.r6 :: opRegs) →
        Rest (.r6 :: opRegs) a b := fun h hs => h.mono hs
    refine (R r1 (by simp)).trans ?_
    refine (R r2 (by simp)).trans ?_
    refine (R r3 (by simp)).trans ?_
    refine (R r4 (by simp)).trans ?_
    refine (R r5 (by simp)).trans ?_
    refine (R r6 (by simp)).trans ?_
    refine (R r7 (by simp)).trans ?_
    refine (R r8 (by simp)).trans ?_
    refine (R r9 (by simp)).trans ?_
    refine (R r10 (by simp)).trans ?_
    refine (R r11 (by simp)).trans ?_
    refine (R r12 (by simp)).trans ?_
    refine (R r13 (by simp)).trans ?_
    refine (R r14 (by simp)).trans ?_
    exact R r15 (by simp)
  · rw [kt bP (by ix), hP13]
  · rw [kt bZ (by ix), kn bZ k13 (by decide) (by ix), kn bZ k12 (by decide) (by ix), kn bZ k11 (by decide) (by ix), z10]
  · have hd : ∀ d ∈ [sOdd], sB + 4 ≤ d ∨ d + 4 ≤ sB := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, sOdd, sB]; omega
    rw [Keep.slot k15 (by decide) hd]
  · intro _; rw [d15]; rfl
  · intro _; rw [kt bF (by ix), kn bF k13 (by decide) (by ix), kn bF k12 (by decide) (by ix), kn bF k11 (by decide) (by ix),
      kn bF k10 (by decide) (by ix), v9]; rfl
  · intro G; have hm1 := G.2.1; rw [kt bG (by ix), kn bG k13 (by decide) (by ix), kn bG k12 (by decide) (by ix), kn bG k11 (by decide) (by ix),
      kn bG k10 (by decide) (by ix), kn bG k9 (by decide) (by ix)]
    show _ = (oddInput m a : Int) % _
    congr 1
    have hG := val32_lt s8.mem (State.addr B) (arr W bG) (k + 1)
    have hA := val32_lt s5.mem (State.addr B) (arr W bA1) (k + 1)
    change nk s8.mem B W bG (k + 1) < _ at hG
    change nk s5.mem B W bA1 (k + 1) < _ at hA
    have e : nk s8.mem B W bG (k + 1) = oddInput m a := by
      have hM' : a + m < 2 ^ (32 * (k + 1)) := by
        rw [show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add]; omega
      generalize 2 ^ (32 * (k + 1)) = M at *
      generalize nk s8.mem B W bG (k + 1) = G at *
      generalize nk s5.mem B W bA1 (k + 1) = A at *
      generalize (s5.gpr .r11).toNat = c5 at *
      generalize (s8.gpr .r11).toNat = c8 at *
      unfold oddInput
      have hp : a % 2 ^ 32 % 2 = a % 2 := Nat.mod_mod_of_dvd _ (by decide)
      rw [hp] at v8
      rcases Nat.mod_two_eq_zero_or_one a with he | ho
      · rw [he] at v8
        simp only [Nat.sub_zero, Nat.one_ne_zero, ↓reduceIte, he] at v8 ⊢
        have c51 : c5 = 1 := by
          rcases (by omega : c5 = 0 ∨ c5 = 1) with h0 | h1
          · subst h0; omega
          · exact h1
        subst c51
        have c81 : c8 = 1 := by
          rcases (by omega : c8 = 0 ∨ c8 = 1) with h0 | h1
          · subst h0; omega
          · exact h1
        subst c81
        omega
      · rw [ho] at v8
        simp only [Nat.sub_self, ↓reduceIte, ho] at v8 ⊢
        have c80 : c8 = 0 := by
          rcases (by omega : c8 = 0 ∨ c8 = 1) with h0 | h1
          · exact h0
          · subst h1; omega
        subst c80
        simp only [Nat.one_ne_zero, ↓reduceIte]; omega
    rw [e]
  · intro G; have := G.2.1; rw [kt bD (by ix), kn bD k13 (by decide) (by ix), kn bD k12 (by decide) (by ix), z11]; omega
  · intro G; rw [kt bE (by ix), e13]; exact G.2.1
  · intro _; rw [kt bD (by ix), kn bD k13 (by decide) (by ix), kn bD k12 (by decide) (by ix), z11]
    show (m : Int) ≡ _ [ZMOD m]
    simp [Int.ModEq]
  · intro _; rw [kt bE (by ix), e13]
    show ((oddInput m a : Nat) : Int) ≡ _ [ZMOD m]
    simp
  · intro _
    rw [kt bD (by ix), kn bD k13 (by decide) (by ix), kn bD k12 (by decide) (by ix), z11, kt bE (by ix), e13]
    exact ⟨rfl, rfl⟩

end VG.Proof.Rsa.Arm.Inv

namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Impl.Rsa.Arm.Keys.Inv
open VG.Proof.X25519.Arm VG.Proof.Rsa.Arm.Inv
open VG.Proof.Rsa.Divstep (oddInput)

theorem inverseK_ok {σ : State} {B : BitVec 32} {Z W k N : Nat} (h : Gk σ B Z W k N) (hN15 : 15 ≤ N)
    (hN : N ≤ 256) :
    WP isa VG.Impl.Rsa.Arm.Keys.inverse σ fun t => Gk t B Z W k N ∧ Keep B W invArrs invSlots σ.mem t.mem ∧
      Rest (.r6 :: opRegs) σ t ∧
      (nk σ.mem B W aM k % 2 = 1 → 1 < nk σ.mem B W aM k →
        nk t.mem B W 1 W = Nat.gcd (nk σ.mem B W 0 k) (nk σ.mem B W aM k) ∧
        nk t.mem B W 3 W = VG.Proof.Rsa.Divstep.inv30 k (nk σ.mem B W 0 k) (nk σ.mem B W aM k)) := by
  generalize hm : nk σ.mem B W aM k = m
  generalize ha : nk σ.mem B W 0 k = a
  have hmk : m < 2 ^ (32 * k) := hm ▸ val32_lt _ _ _ _
  have hak : a < 2 ^ (32 * k) := ha ▸ val32_lt _ _ _ _
  simp only [VG.Impl.Rsa.Arm.Keys.inverse, seqs]
  rw [WP.seq_iff]
  refine WP.mono (init_ok h hN15 hN hm ha hmk hak) fun s ⟨iv, hiv, I⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (batches_ok hN15 hN I hmk hak) fun s2 I2 => ?_
  have done := fun (G : Good m iv) => VG.Proof.Rsa.Divstep.invRun_done (inv := iv) G.1 hmk hak
  have hf : Good m iv → (st m iv a (nB k)).f.natAbs < 2 ^ (32 * k) := fun G => by
    rw [(done G).2]; exact lt_of_le_of_lt (Nat.gcd_le_left _ (by have := G.2.1; omega)) hmk
  refine WP.mono (finish_ok hN15 hN I2 hmk hf) fun t ⟨gt, kt, rt, v⟩ => ⟨gt, kt, rt, fun hmo hm1 => ?_⟩
  have G : Good m iv := ⟨hmo, hm1, hiv hmo⟩
  obtain ⟨v1, v3, vc⟩ := v G
  refine ⟨by rw [v1, (done G).2, Nat.gcd_comm], ?_⟩
  have hD := (I2.de G).1
  have hF := (VG.Proof.Divstep.W32.invRun_dfg_m (p := (m : Int)) (m := (iv : Int)) (m' := 0) (x := (oddInput m a : Int))
    (by exact_mod_cast G.1) (nB k)).2.1
  change (st m iv a (nB k)).f = _ at hF
  rw [hF, hD] at vc
  have hm0 : (0 : Int) < m := Int.natCast_pos.mpr (by omega)
  unfold VG.Proof.Rsa.Divstep.inv30
  have e : (nk t.mem B W 3 W : Int) = (nk t.mem B W 3 W : Int) % m :=
    (Int.emod_eq_of_lt (by omega) (by exact_mod_cast v3)).symm
  rw [Int.ModEq] at vc
  rw [← vc, ← e]
  rfl

/-- What `InvLaw` states, which callers take as an instance: the registrations
import this module for it. -/
instance invLaw : InvLaw where
  inverseK_ok := inverseK_ok
  inv30_spec := VG.Proof.Rsa.Divstep.inv30_spec

end VG.Proof.Rsa.Arm.Keys
