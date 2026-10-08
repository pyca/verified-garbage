import VerifiedGarbage.Proof.Cast5.AArch64.KeyGroup

/-!
# CAST5 key expansion on AArch64: a half

`half` runs the eight groups of lines of §2.4 (`halfImpl`), writing sixteen
subkeys from `x2`, then moves `x2` on and counts the half (`half_ok`).
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem gA : GroupOk none aLines := by unfold GroupOk; decide
theorem gB : GroupOk none bLines := by unfold GroupOk; decide
theorem gC : GroupOk none cLines := by unfold GroupOk; decide
theorem gD : GroupOk none dLines := by unfold GroupOk; decide

theorem storeKey_zero : (fun k => storeKey (0 + k)) = storeKey := funext fun k => by rw [Nat.zero_add]

/-- The registers key expansion's halves write. -/
def keyRegs : List Reg := [.x0, .x9, .x10, .x11, .x2, .x1]

theorem keep_widen {s u : State} (h : Keep [.x0, .x9, .x10, .x11] s u) : Keep keyRegs s u :=
  Keep.mono h

theorem half_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {hh : Nat} (hdx : s.gpr .x2 = K + BitVec.ofNat 64 (64 * hh))
    (hlen : ws.length = 16 * hh) (hle : hh < 2) :
    WP isa half s fun u =>
      KS m0 c K u (halfImpl st).2 (ws ++ (halfImpl st).1) ∧
      u.gpr .x2 = K + BitVec.ofNat 64 (64 * (hh + 1)) ∧ u.gpr .x1 = s.gpr .x1 - BitVec.ofNat 64 1 ∧
      u.syms = s.syms ∧ Keep keyRegs s u := by
  have kd {u v : State} (k : Keep [.x0, .x9, .x10, .x11] u v) : v.gpr .x2 = u.gpr .x2 := k.gpr _ (by decide)
  have l4 (ls : List Impl.Cast5.Line) (t : XZ) : (keys4 ls t).length = 4 := rfl
  unfold half
  refine WP.seq (WP.mono (groupQ_ok h .z gZ) fun u1 ⟨h1, s1, k1⟩ => ?_)
  rw [runQ_z] at h1
  have g2 := groupK_ok h1 gA (b := 0) (hh := hh) (by decide) (by rw [kd k1, hdx]) (by rw [hlen]; rfl)
    (by omega)
  rw [storeKey_zero] at g2
  refine WP.seq (WP.mono g2 fun u2 ⟨h2, s2, k2⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h2 .x gX) fun u3 ⟨h3, s3, k3⟩ => ?_)
  rw [runQ_x] at h3
  have g4 := groupK_ok h3 gB (b := 4) (hh := hh) (by decide) (by rw [kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, hlen, l4]) (by rw [List.length_append, hlen, l4]; omega)
  refine WP.seq (WP.mono g4 fun u4 ⟨h4, s4, k4⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h4 .z gZ) fun u5 ⟨h5, s5, k5⟩ => ?_)
  rw [runQ_z] at h5
  have g6 := groupK_ok h5 gC (b := 8) (hh := hh) (by decide) (by rw [kd k5, kd k4, kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, List.length_append, hlen, l4, l4])
    (by rw [List.length_append, List.length_append, hlen, l4, l4]; omega)
  refine WP.seq (WP.mono g6 fun u6 ⟨h6, s6, k6⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h6 .x gX) fun u7 ⟨h7, s7, k7⟩ => ?_)
  rw [runQ_x] at h7
  have g8 := groupK_ok h7 gD (b := 12) (hh := hh) (by decide)
    (by rw [kd k7, kd k6, kd k5, kd k4, kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4]; omega)
  refine WP.seq (WP.mono g8 fun u8 ⟨h8, s8, k8⟩ => ?_)
  have k18 := keep_same (keep_same (keep_same (keep_same (keep_same (keep_same (keep_same k1 k2) k3) k4) k5)
    k6) k7) k8
  have hdx8 : u8.gpr .x2 = K + BitVec.ofNat 64 (64 * hh) := by rw [k18.gpr _ (by decide), hdx]
  have hsi8 : u8.gpr .x1 = s.gpr .x1 := k18.gpr _ (by decide)
  refine WP.mono_syms (WP.keep [.x1, .x2] (show WP isa (.block [.addImm .x .x2 .x2 64, .subImm .x .x1 .x1 1]) u8
      fun w => w.gpr .x2 = u8.gpr .x2 + BitVec.ofNat 64 64 ∧ w.gpr .x1 = u8.gpr .x1 - BitVec.ofNat 64 1 ∧
        w.mem = u8.mem ∧ w.rd = u8.rd ∧ w.wr = u8.wr by crun) rfl rfl (by decide))
    fun w ⟨⟨w2, w1, wm, wrd, wwr⟩, wk⟩ wsy => ?_
  have hst : (halfImpl st).2 = runX xLines (runZ zLines (runX xLines (runZ zLines st))) := rfl
  have hks : ws ++ (halfImpl st).1 = ws ++ keys4 aLines (runZ zLines st) ++
      keys4 bLines (runX xLines (runZ zLines st)) ++ keys4 cLines (runZ zLines (runX xLines (runZ zLines st))) ++
      keys4 dLines (runX xLines (runZ zLines (runX xLines (runZ zLines st)))) := by
    simp only [halfImpl, List.append_assoc]
  rw [hst, hks]
  refine ⟨h8.update (wk.gpr _ (by decide)) (by rw [wm]; exact h8.mem) h8.len wrd wwr wsy, ?_,
    by rw [w1, hsi8], by rw [wsy, s8, s7, s6, s5, s4, s3, s2, s1], keep_same (keep_widen k18) (wk.mono)⟩
  rw [w2, hdx8, Proof.Cast5.add_ofNat_add, Nat.mul_succ]

end VG.Proof.Cast5.AArch64
