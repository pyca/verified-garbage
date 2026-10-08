import VerifiedGarbage.Proof.Cast5.X86_64.KeyGroup

/-!
# CAST5 key expansion on x86-64: a half

`half` runs the eight groups of lines of §2.4 (`halfImpl`), writing sixteen
subkeys from `rdx`, then moves `rdx` on and counts the half (`half_ok`).
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly sx_ofNat)

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem gA : GroupOk none aLines := by unfold GroupOk; decide
theorem gB : GroupOk none bLines := by unfold GroupOk; decide
theorem gC : GroupOk none cLines := by unfold GroupOk; decide
theorem gD : GroupOk none dLines := by unfold GroupOk; decide

theorem storeKey_zero : (fun k => storeKey (0 + k)) = storeKey := funext fun k => by rw [Nat.zero_add]

/-- The registers key expansion writes. -/
def keyRegs : List Reg := [.rax, .r9, .r10, .r11, .rdx, .rsi]

theorem keep_widen {s u : State} (h : Keep [.rax, .r9, .r10, .r11] s u) : Keep keyRegs s u :=
  Keep.mono h fun r hr => by
    simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem half_ok {m0 : Mem} {c K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 c K s st ws) {hh : Nat} (hdx : s.gpr .rdx = K + BitVec.ofNat 64 (64 * hh))
    (hlen : ws.length = 16 * hh) (hle : hh < 2) :
    WP isa half s fun u =>
      KS m0 c K u (halfImpl st).2 (ws ++ (halfImpl st).1) ∧
      u.gpr .rdx = K + BitVec.ofNat 64 (64 * (hh + 1)) ∧ u.gpr .rsi = s.gpr .rsi - 1 ∧
      u.zf = some (s.gpr .rsi - 1 == 0) ∧ u.syms = s.syms ∧ Keep keyRegs s u := by
  have kd {u v : State} (k : Keep [.rax, .r9, .r10, .r11] u v) : v.gpr .rdx = u.gpr .rdx := k.1 _ (by decide)
  have l4 (ls : List Impl.Cast5.Line) (t : XZ) : (keys4 ls t).length = 4 := rfl
  unfold half
  refine WP.seq (WP.mono (groupQ_ok h .z gZ) fun u1 ⟨h1, s1, k1⟩ => ?_)
  rw [runQ_z] at h1
  have g2 := groupK_ok h1 gA (b := 0) (hh := hh) (by rw [kd k1, hdx]) (by rw [hlen]; rfl) (by omega)
  rw [storeKey_zero] at g2
  refine WP.seq (WP.mono g2 fun u2 ⟨h2, s2, k2⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h2 .x gX) fun u3 ⟨h3, s3, k3⟩ => ?_)
  rw [runQ_x] at h3
  have g4 := groupK_ok h3 gB (b := 4) (hh := hh) (by rw [kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, hlen, l4]) (by rw [List.length_append, hlen, l4]; omega)
  refine WP.seq (WP.mono g4 fun u4 ⟨h4, s4, k4⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h4 .z gZ) fun u5 ⟨h5, s5, k5⟩ => ?_)
  rw [runQ_z] at h5
  have g6 := groupK_ok h5 gC (b := 8) (hh := hh) (by rw [kd k5, kd k4, kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, List.length_append, hlen, l4, l4])
    (by rw [List.length_append, List.length_append, hlen, l4, l4]; omega)
  refine WP.seq (WP.mono g6 fun u6 ⟨h6, s6, k6⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h6 .x gX) fun u7 ⟨h7, s7, k7⟩ => ?_)
  rw [runQ_x] at h7
  have g8 := groupK_ok h7 gD (b := 12) (hh := hh)
    (by rw [kd k7, kd k6, kd k5, kd k4, kd k3, kd k2, kd k1, hdx])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4]; omega)
  refine WP.seq (WP.mono g8 fun u8 ⟨h8, s8, k8⟩ => ?_)
  have k18 := keep_same (keep_same (keep_same (keep_same (keep_same (keep_same (keep_same k1 k2) k3) k4) k5)
    k6) k7) k8
  have hdx8 : u8.gpr .rdx = K + BitVec.ofNat 64 (64 * hh) := by rw [k18.1 _ (by decide), hdx]
  have hsi8 : u8.gpr .rsi = s.gpr .rsi := k18.1 _ (by decide)
  xrun [imm, sx_ofNat (show 64 < 2 ^ 31 by decide), sx_ofNat (show 1 < 2 ^ 31 by decide), hdx8, hsi8]
  have e64 : K + BitVec.ofNat 64 (64 * hh) + 64#64 = K + BitVec.ofNat 64 (64 * (hh + 1)) := by
    rw [show (64#64 : BitVec 64) = BitVec.ofNat 64 64 from rfl, Proof.Cast5.add_ofNat_add, Nat.mul_succ]
  have hst : (halfImpl st).2 = runX xLines (runZ zLines (runX xLines (runZ zLines st))) := rfl
  have hks : ws ++ (halfImpl st).1 = ws ++ keys4 aLines (runZ zLines st) ++
      keys4 bLines (runX xLines (runZ zLines st)) ++ keys4 cLines (runZ zLines (runX xLines (runZ zLines st))) ++
      keys4 dLines (runX xLines (runZ zLines (runX xLines (runZ zLines st)))) := by
    simp only [halfImpl, List.append_assoc]
  rw [hst, hks]
  refine ⟨h8.update (by simp only [gpr_setReg_of_ne _ _ (show Reg.rcx ≠ .rsi by decide), gpr_setFlags,
      gpr_setReg_of_ne _ _ (show Reg.rcx ≠ .rdx by decide)]) h8.mem h8.len rfl rfl rfl, e64,
    rfl, rfl, by
      show u8.syms = s.syms
      rw [s8, s7, s6, s5, s4, s3, s2, s1], fun r hr => ?_, k18.2.1, k18.2.2⟩
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [gpr_setReg_of_ne _ _ hr.2.2.2.2.2, gpr_setFlags, gpr_setReg_of_ne _ _ hr.2.2.2.2.1]
  exact k18.1 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1⟩)

end VG.Proof.Cast5.X86_64
