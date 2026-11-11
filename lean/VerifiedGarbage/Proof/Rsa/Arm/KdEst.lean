module

public import VerifiedGarbage.Proof.Rsa.Arm.KdRefine
import VerifiedGarbage.Proof.Bignum.WordTop32
import VerifiedGarbage.Proof.Bignum.WordStepNorm32
import VerifiedGarbage.Proof.Bignum.WordStep32
import VerifiedGarbage.Proof.Rsa.Arm.KdTop

/-! # A step's estimate of the key checks' division on ARMv7 (`KeyDiv.estimate`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.KeyDiv

open VG VG.Arm VG.Impl.Rsa.Arm.KeyDiv VG.Proof.Rsa.Arm.Keys VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_reg)

open VG.Proof.Bignum.WordStep32 VG.Proof.Bignum.WordTop32 in
/-- The estimate's arithmetic: for a window `Y < 2^32 M` whose top four words
are `a₁ a₂ a₃ a` (`k` words `L` below), `u₂ u₁ u₀` the top three words of
`Y 2^z` and `D = Dh 2^32 + Dl` the top two of `M 2^z`, `M 2^z < 2^(32 (k + 3))`
normalized: `u₂ ≤ Dh`, `U < (2^32 + 1) D`, the 2-by-1 estimate within 2 above
`Q = min(⌊U / D⌋, 2^32 - 1)`, and `⌊Y / M⌋ ≤ Q ≤ ⌊Y / M⌋ + 1`. -/
theorem est_math {Y M z k L a a1 a2 a3 Dh Dl u2 u1 u0 : Nat} (hz : z ≤ 31)
    (hY' : Y = (L + 2 ^ (32 * k) * a) + 2 ^ (32 * (k + 1)) * a3 +
      2 ^ (32 * (k + 1)) * 2 ^ 32 * (a2 + 2 ^ 32 * a1))
    (hL : L < 2 ^ (32 * k)) (ha : a < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32)
    (hYM : Y < M * 2 ^ 32) (hMP : M * 2 ^ z < 2 ^ (32 * (k + 3)))
    (hD : Dh * 2 ^ 32 + Dl = M * 2 ^ z / 2 ^ (32 * (k + 1))) (hDn : 2 ^ 31 ≤ Dh) (hDl : Dl < 2 ^ 32)
    (hu2 : u2 = wordP a1 a2 (2 ^ z)) (hu1 : u1 = wordP a2 a3 (2 ^ z)) (hu0 : u0 = wordP a3 a (2 ^ z)) :
    u2 ≤ Dh ∧ u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 < (2 ^ 32 + 1) * (Dh * 2 ^ 32 + Dl) ∧
    min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ≤
      min ((u2 * 2 ^ 32 + u1) / Dh) (2 ^ 32 - 1) ∧
    min ((u2 * 2 ^ 32 + u1) / Dh) (2 ^ 32 - 1) ≤
      min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) + 2 ∧
    Y / M ≤ min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ∧
    min ((u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / (Dh * 2 ^ 32 + Dl)) (2 ^ 32 - 1) ≤ Y / M + 1 := by
  have hP := Nat.two_pow_pos z
  have eK : (2 : Nat) ^ (32 * (k + 1)) = 2 ^ (32 * k) * 2 ^ 32 := by
    rw [show 32 * (k + 1) = 32 * k + 32 by omega, Nat.pow_add]
  have hL' : L + 2 ^ (32 * k) * a < 2 ^ (32 * (k + 1)) := by
    rw [eK]
    have := Nat.mul_le_mul_left (2 ^ (32 * k)) (show a + 1 ≤ 2 ^ 32 by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  -- `Y 2^z < 2^32 M 2^z < 2^(32 (k + 4))`.
  have hYP : Y * 2 ^ z < M * 2 ^ z * 2 ^ 32 := by
    rw [Nat.mul_right_comm]; exact Nat.mul_lt_mul_of_pos_right hYM hP
  have hY : Y = L + 2 ^ (32 * k) * a + 2 ^ (32 * k) * 2 ^ 32 * (a3 + 2 ^ 32 * a2 + 2 ^ 64 * a1) := by
    rw [hY', eK]; grind
  have hsm : a1 * 2 ^ z < 2 ^ 32 := by
    refine top_small (L := L + 2 ^ (32 * k) * a) (k := k + 1) (a2 := a2) (a3 := a3) ?_
    rw [← hY', show 32 * (k + 1 + 3) = 32 * (k + 3) + 32 by omega, Nat.pow_add]
    exact Nat.lt_of_lt_of_le hYP (Nat.mul_le_mul_right _ (Nat.le_of_lt hMP))
  have e2 : u2 = a1 * 2 ^ z % 2 ^ 32 + a2 * 2 ^ z / 2 ^ 32 := by
    rw [hu2]; exact Nat.mod_eq_of_lt (lohi_lt (by omega) ha2)
  have e1 : u1 = a2 * 2 ^ z % 2 ^ 32 + a3 * 2 ^ z / 2 ^ 32 := by
    rw [hu1]; exact Nat.mod_eq_of_lt (lohi_lt (by omega) ha3)
  have e0 : u0 = a3 * 2 ^ z % 2 ^ 32 + a * 2 ^ z / 2 ^ 32 := by
    rw [hu0]; exact Nat.mod_eq_of_lt (lohi_lt (by omega) ha)
  have hU : u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0 = Y * 2 ^ z / 2 ^ (32 * k + 32) := by
    rw [e2, e1, e0, top3_math hz hL hsm, ← hY]
    exact congrArg (Y * 2 ^ z / ·) (Nat.pow_add 2 (32 * k) 32).symm
  have hu0' : u0 < 2 ^ 32 := hu0 ▸ Nat.mod_lt _ (by decide)
  have hu1' : u1 < 2 ^ 32 := hu1 ▸ Nat.mod_lt _ (by decide)
  have hDD : M * 2 ^ z / 2 ^ (32 * k + 32) = Dh * 2 ^ 32 + Dl := by
    rw [hD, show 32 * (k + 1) = 32 * k + 32 by omega]
  have hDh : (Dh * 2 ^ 32 + Dl) / 2 ^ 32 = Dh := by omega_using [hDl]
  have hUh : (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / 2 ^ 32 = u2 * 2 ^ 32 + u1 := by omega_using [hu0']
  have q := qhat3_div (Y := Y) (M := M) (P := 2 ^ z) (K := 32 * k) hP hYM (by rw [hDD, hDh]; exact hDn)
  rw [hDD, ← hU, hDh, hUh] at q
  refine ⟨?_, q⟩
  -- `u₂ = ⌊Y 2^z / 2^(32 (k + 3))⌋ ≤ ⌊2^32 M 2^z / 2^(32 (k + 3))⌋ = Dh`.
  have h2 : u2 = (u2 * 2 ^ 64 + u1 * 2 ^ 32 + u0) / 2 ^ 64 := by omega_using [hu0', hu1']
  have hd2 : Dh = M * 2 ^ z * 2 ^ 32 / 2 ^ (32 * k + 32) / 2 ^ 64 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, show 32 * k + 32 + 64 = (32 * k + 64) + 32 by omega,
      Nat.pow_add 2 (32 * k + 64) 32, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos 32),
      show 32 * k + 64 = (32 * k + 32) + 32 by omega, Nat.pow_add 2 (32 * k + 32) 32, ← Nat.div_div_eq_div_mul,
      hDD, hDh]
  rw [h2, hU, hd2]
  exact Nat.div_le_div_right (Nat.div_le_div_right (Nat.le_of_lt hYP))

/-- `ctx`: `w` (16) into `r9` and its stride into `r7`, with `r8 = B`. -/
theorem kctx_ok {s : State} {B : BitVec 32} {Z w N : Nat} (h : WsM s B Z w N) (h8 : s.gpr .r8 = B)
    (h16 : slot s.mem B 16 = w) (hw0 : 0 < w) (hw : w ≤ 1024) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N → Rest [.r9, .r7] s t → t.mem = s.mem → WP isa (.block rest) t Q) :
    WP isa (.block (ctx ++ rest)) s Q := by
  have hz := h.hdr_le
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r9, .r7] (Q := fun v =>
      v.gpr .r9 = BitVec.ofNat 32 w ∧ v.gpr .r7 = (BitVec.ofNat 32 w + 2) <<< 2 ∧ v.mem = s.mem) (by
    krun [ctx, VG.Impl.Rsa.Arm.Keys.stride, h8, h.addr (d := 16) (by omega), h.read (d := 16) (by omega),
      show s.mem.readW (off (State.addr B) 16) 32 = BitVec.ofNat 32 w by rw [← h16]; exact (ofNat_toNat32 _).symm])
    (by decide)) fun t ⟨⟨n9, n7, mt⟩, kt⟩ => ?_)
  refine k t ⟨h.nowrap, by rw [kt.wr]; exact h.writable, h.fits, hw0, hw, ?_, by rw [kt.gpr _ (by decide)]; exact h8,
    n9⟩ kt mt
  rw [n7, stride_val hw]

/-- The registers `estimate` changes. -/
abbrev estRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr]

open VG.Proof.Bignum.WordTop32 in
/-- `estimate r`: `q̂` (156) with `⌊Y / M⌋ ≤ q̂ ≤ ⌊Y / M⌋ + 1`, for the window `Y < 2^32 M`
of `w / 2 + 1` words at word `j` (72, `4 j`) of `[r]`, `P = 2^z` (136), the top two words
`(d, d₁)` (140, 148) of `M 2^z`, normalized, and `v` (144) `d`'s reciprocal. -/
theorem estimate_ok {s : State} {B : BitVec 32} {Z w N r j z : Nat} (h : Ws s B Z w N) (hr : r < N)
    (hN : N ≤ 256) (h16 : slot s.mem B 16 = w) (hdw : 3 ≤ w / 2) (hJ : slot s.mem B sJ = 4 * j)
    (hj : j + w / 2 ≤ w) {Y M : Nat} (hY : val32 s.mem (State.addr B) (arr w r + 4 * j) (w / 2 + 1) = Y)
    (hYM : Y < M * 2 ^ 32) (hz : z ≤ 31) (hP : slot s.mem B sP = 2 ^ z) (hMP : M * 2 ^ z < 2 ^ (32 * (w / 2)))
    (hD : slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1 = M * 2 ^ z / 2 ^ (32 * (w / 2 - 2)))
    (hDn : 2 ^ 31 ≤ slot s.mem B sD) (hV : slot s.mem B sV = (2 ^ 64 - 1) / slot s.mem B sD - 2 ^ 32)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t q, slot t.mem B sQ = q → Y / M ≤ q → q ≤ Y / M + 1 → q < 2 ^ 32 →
      Keep B w [] [sMk, sQ, sU0, sU2] s.mem t.mem → Ws t B Z w N → Rest estRegs s t →
      WP isa (.block rest) t Q) :
    WP isa (.block (estimate r ++ rest)) s Q := by
  have := h.wle
  have nw := h.nowrap
  have fr := h.arr_fit hr
  have hz' := h.hdr_le
  simp only [S] at fr
  simp only [VG.Impl.Rsa.Arm.Keys.hdr] at hz'
  obtain ⟨kk, hk⟩ : ∃ kk, w / 2 = kk + 3 := ⟨w / 2 - 3, by omega⟩
  simp only [estimate, List.append_assoc]
  refine topPtr_ok h (r := .r10) (t := .r0) (by decide) (by decide) (by decide) (j := r) (i := 3) (by omega)
    (by omega) (by decide) (by omega) fun u1 p1 r1 m1 h1 => ?_
  have aJ := h.addr (d := sJ) (by simp only [sJ]; omega)
  have rJ : InRegions (u1.rd ++ u1.wr) (off (State.addr B) sJ) 4 := h1.read (by simp only [sJ]; omega)
  have vJ : u1.mem.readW (off (State.addr B) sJ) 32 = BitVec.ofNat 32 (4 * j) := by
    rw [m1, ← hJ]; exact (ofNat_toNat32 _).symm
  generalize eX : arr w r + 4 * j + 4 * kk = X
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.r0, .r10] (Q := fun v =>
      v.gpr .r10 = B + BitVec.ofNat 32 X ∧ v.mem = u1.mem) (by
    krun [h1.r8, aJ, rJ, vJ, p1]
    rw [add_ofNat_assoc, ← eX]; congr 2; omega) (by decide)) fun u2 ⟨⟨p2, m2⟩, k2⟩ => ?_)
  have h2 : Ws u2 B Z w N := h1.rest k2
  have mu2 : u2.mem = s.mem := m2.trans m1
  have wr2 : u2.wr = s.wr := k2.wr.trans r1.wr
  have hXZ : X + 16 ≤ Z := by omega
  refine topWords_ok h2 hXZ p2 fun t3 m3 q11 q12 R3 => ?_
  rw [mu2] at m3 q11
  simp only [hP] at m3 q11
  generalize ea : w32 s.mem (State.addr B) X = a at m3 q11
  generalize ea3 : w32 s.mem (State.addr B) (X + 4) = a3 at m3 q11
  generalize ea2 : w32 s.mem (State.addr B) (X + 8) = a2 at m3 q11
  generalize ea1 : w32 s.mem (State.addr B) (X + 12) = a1 at m3
  have ha : a < 2 ^ 32 := ea ▸ BitVec.isLt _
  have ha3 : a3 < 2 ^ 32 := ea3 ▸ BitVec.isLt _
  have ha2 : a2 < 2 ^ 32 := ea2 ▸ BitVec.isLt _
  have hYe : Y = (val32 s.mem (State.addr B) (arr w r + 4 * j) kk + 2 ^ (32 * kk) * a) +
      2 ^ (32 * (kk + 1)) * a3 + 2 ^ (32 * (kk + 1)) * 2 ^ 32 * (a2 + 2 ^ 32 * a1) := by
    rw [← hY, hk, show kk + 3 + 1 = (kk + 1) + 3 from rfl, val32_top3, val32_succ, ← ea, ← ea3, ← ea2, ← ea1,
      show arr w r + 4 * j + 4 * kk = X from eX, show arr w r + 4 * j + 4 * (kk + 1) = X + 4 by omega,
      show arr w r + 4 * j + 4 * (kk + 1 + 1) = X + 8 by omega,
      show arr w r + 4 * j + 4 * (kk + 1 + 2) = X + 12 by omega]
  have E := est_math (u2 := wordP a1 a2 (2 ^ z)) (u1 := wordP a2 a3 (2 ^ z)) (u0 := wordP a3 a (2 ^ z)) hz hYe
    (val32_lt _ _ _ _) ha ha2 ha3 hYM (hk ▸ hMP) (by rw [hD, hk, show kk + 3 - 2 = kk + 1 by omega]) hDn (BitVec.isLt _) rfl rfl rfl
  obtain ⟨Eu, EUD, Ege, Ele, Elo, Ehi⟩ := E
  have hA : (State.addr B).toNat + Z ≤ 2 ^ 32 := by simp only [State.addr, BitVec.toNat_setWidth]; omega
  -- Header words other than `u₀` and `u₂` after `topWords`.
  have s3 : ∀ {o : Nat}, o + 4 ≤ 160 → (o + 4 ≤ sU0 ∨ sU0 + 4 ≤ o) → (o + 4 ≤ sU2 ∨ sU2 + 4 ≤ o) →
      slot t3.mem B o = slot s.mem B o := fun ho h0 h2 => by
    simp only [slot]
    rw [m3, w32_write_ne hA (by simp only [sU2]; omega) (by omega) h2,
      w32_write_ne hA (by simp only [sU0]; omega) (by omega) h0]
  have tw : ∀ {x : Nat}, (BitVec.ofNat 32 (x % 2 ^ 32)).toNat = x % 2 ^ 32 := fun {x} => by
    rw [BitVec.toNat_ofNat, Nat.mod_mod]
  have sU2v : slot t3.mem B sU2 = wordP a1 a2 (2 ^ z) := by simp only [slot]; rw [m3, w32_write_self, tw]
  have sU0v : slot t3.mem B sU0 = wordP a3 a (2 ^ z) := by
    simp only [slot]; rw [m3, w32_write_ne hA (by simp only [sU2]; omega) (by simp only [sU0]; omega) (by decide),
      w32_write_self, tw]
  have wr3 : t3.wr = s.wr := R3.wr.trans wr2
  have hDl : slot s.mem B sD < 2 ^ 32 := BitVec.isLt _
  refine quot_ok (h.m.of wr3) q12 q11 (s3 (by decide) (by decide) (by decide)) sU2v
    (by rw [s3 (by decide) (by decide) (by decide)]; exact hV) hDn hDl Eu (Nat.mod_lt _ (by decide))
    fun t4 hq4 K4 q11' q12' R4 => ?_
  rw [qhat_min Eu (Nat.mod_lt _ (by decide)) (by omega)] at hq4
  have s4 : ∀ {o : Nat}, o + 4 ≤ VG.Impl.Rsa.Arm.Keys.hdr → (∀ d ∈ [sMk, sQ], o + 4 ≤ d ∨ d + 4 ≤ o) →
      slot t4.mem B o = slot t3.mem B o := fun ho hd => K4.slot ho hd
  have wr4 : t4.wr = s.wr := R4.wr.trans wr3
  refine refine3_ok (h.m.of wr4) q12' (u1 := wordP a2 a3 (2 ^ z)) (q11'.trans q11) (Nat.mod_lt _ (by decide)) hq4
    (U := wordP a1 a2 (2 ^ z) * 2 ^ 64 + wordP a2 a3 (2 ^ z) * 2 ^ 32 + wordP a3 a (2 ^ z))
    (D := slot s.mem B sD * 2 ^ 32 + slot s.mem B sD1)
    (by rw [s4 (by decide) (by decide), s4 (by decide) (by decide), sU2v, sU0v])
    (by rw [s4 (by decide) (by decide), s4 (by decide) (by decide), s3 (by decide) (by decide) (by decide),
      s3 (by decide) (by decide) (by decide)])
    (by omega) EUD Ege Ele fun t5 hq5 K5 q12'' R5 => ?_
  have K45 : Keep B w [] [sMk, sQ, sU0, sU2] s.mem t5.mem := by
    have K3 : Keep B w [] [sMk, sQ, sU0, sU2] s.mem t3.mem := by
      rw [m3]
      exact (keep_write _ _ (by simp) (by simp only [sU0]; omega)).trans
        (keep_write _ _ (by simp) (by simp only [sU2]; omega))
    exact (K3.trans K4.mono).trans K5.mono
  rw [List.singleton_append]
  refine wp_mov (op2_reg _ _) fun t6 u6 => ?_
  have h86 : t6.gpr .r8 = B := by rw [u6.gpr, q12'']
  have wr6 : t6.wr = s.wr := u6.wr.trans (R5.wr.trans wr4)
  have h166 : slot t6.mem B 16 = w := by
    rw [u6.mem, K45.slot (by decide) (by decide), h16]
  refine kctx_ok (h.m.of wr6) h86 h166 h.wpos this fun t7 h7 R7 m7 => ?_
  refine k t7 _ (by rw [m7, u6.mem, hq5]) Elo Ehi (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide))
    (by rw [m7, u6.mem]; exact K45) h7 ?_
  have K : Rest (estRegs ++ [.r7, .r8, .r9]) s t7 :=
    ((((r1.mono (by decide)).trans (k2.mono (by decide))).trans ((R3.mono (by decide)).trans (R4.mono (by decide)))).trans
      (((R5.mono (by decide)).trans (u6.rest (by decide))).trans (R7.mono (by decide))))
  refine ⟨fun r hr => ?_, K.rd, K.wr, K.sp⟩
  by_cases e : r ∈ [Reg.r7, .r8, .r9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at e
    rcases e with rfl | rfl | rfl
    · rw [h7.r7, h.r7]
    · rw [h7.r8, h.r8]
    · rw [h7.r9, h.r9]
  · exact K.gpr r fun hm => (List.mem_append.mp hm).elim hr e

end VG.Proof.Rsa.Arm.KeyDiv
