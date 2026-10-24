module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSSetup
public import VerifiedGarbage.Proof.Rsa.PPC64LE.DivLoop
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: the division in the key working space

`div_vp`: `[q] := [q] / [d]` and `[r] := [q] mod [d]` (`div_ok`), for a
divisor whose top word is zero (`TopAll`), the temporary `t` lost.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws stepRegs div_ok)
open VG.Impl.Dsa.PPC64LE.Generation

/-- `w + 1` digits below `2^(32 w)` are `w` digits. -/
theorem num_of_num1 {m : Mem} {B : Addr} {w j : Nat} (h : val32 m B (arr w j) (w + 1) < 2 ^ (32 * w)) :
    num m B w j = val32 m B (arr w j) (w + 1) := by
  have e := val32_append m B (arr w j) w 1
  rw [e] at h ⊢
  have : val32 m B (arr w j + 4 * w) 1 = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m B (arr w j + 4 * w) 1) with z | z
    · exact z
    · have := Nat.mul_le_mul_left (2 ^ (32 * w)) z; omega
  rw [this, Nat.mul_zero, Nat.add_zero]

/-- The stage after the division. -/
abbrev divCfg (c : Cfg) (q r d : Nat) : Cfg :=
  { c with A := KU (KU c.A q (c.A q / c.A d)) r (c.A q % c.A d), live := q :: r :: c.live }

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The division: `[q] := [q] / [d]`, `[r] := [q] mod [d]`, the temporary `t` lost. -/
theorem div_vp {q r d t : Nat} (cert : CertK (VG.Impl.Rsa.PPC64LE.Div.div q r d t))
    (hq : q < nArrs) (hr : r < nArrs) (hd : d < nArrs) (ht : t < nArrs)
    (hqr : q ≠ r) (hqd : q ≠ d) (hqt : q ≠ t) (hrd : r ≠ d) (hrt : r ≠ t) (hdt : d ≠ t) (hd1 : d ≠ aOne)
    (hqL : q ∈ c.live) (hdL : d ∈ c.live) (htL : t ∉ c.live) (hpos : 0 < c.A d) :
    VP (fun σ s => KSt G c X σ s ∧ TopAll G s.mem) (VG.Impl.Rsa.PPC64LE.Div.div q r d t)
      (KSt G (divCfg c q r d) X) := by
  refine ks_vp cert (fun σ s h => ⟨h.1.1.1, h.1.2⟩) fun σ s ⟨⟨⟨h, x⟩, kr⟩, top⟩ => ?_
  have hw := h.ws kr
  have va := h.arrs.get hqL
  have vd := h.arrs.get hdL
  refine h.ksWP rfl (div_ok hw hq hr hd ht (by decide) hqr hqd hqt hrd hrt hdt (top d hd hd1))
    fun u ⟨_, k, R, v⟩ hr' hw' f => ?_
  have R' : Keep stepRegs s u := ⟨R.gpr, hr', hw'⟩
  simp only [GP.ksState, State.withRegions_mem] at v k
  rw [vd] at v
  obtain ⟨vq, vr⟩ := v hpos
  rw [va] at vq vr
  have dl : c.A d < 2 ^ (32 * G.w) := vd ▸ val32_lt _ _ _ _
  have vr1 : val32 u.mem G.KB (arr G.w r) (G.w + 1) = c.A q % c.A d := vr
  have vr' : num u.mem G.KB G.w r = c.A q % c.A d := by
    have := Nat.mod_lt (c.A q) hpos
    rw [num_of_num1 (by rw [vr1]; omega)]
    exact vr1
  refine ⟨⟨h.of_ks R' R.sp f (fun j hj => ?_) (fun j hj => ?_) (fun e he => ?_) h.kslOk, x⟩, kr.of_keep R'⟩
  · show num u.mem G.KB G.w j = VG.Proof.Rsa.KeyWorkspace.upd (VG.Proof.Rsa.KeyWorkspace.upd c.A q
      (c.A q / c.A d)) r (c.A q % c.A d) j
    by_cases ejr : j = r
    · subst ejr; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact vr'
    rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ ejr]
    by_cases ejq : j = q
    · subst ejq; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact vq
    rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ ejq]
    have jl : j ∈ c.live := by
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejq
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd rfl ejr
      · exact hj
    have ejt : j ≠ t := fun e => htL (e ▸ jl)
    rw [k.num (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro k' (rfl | rfl | rfl) <;> omega)
      (by simp) (hw.fit64 (h.liveOk j jl))]
    exact h.arrs.get jl
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact hq
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hr
    · exact h.liveOk j hj
  · rw [k.slot (h.kslOk e he).1 (by simp)]; exact h.ksl e he

end

end VG.Proof.Dsa.PPC64LE.Gen
