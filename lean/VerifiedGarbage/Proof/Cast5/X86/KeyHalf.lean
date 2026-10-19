module

public import VerifiedGarbage.Proof.Cast5.X86.KeyGroup
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Cast5.X86.Round
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# CAST5 key expansion on 32-bit x86: a half

`half` runs the eight groups of lines of §2.4 (`halfImpl`), writing sixteen
subkeys from `edi`, then moves `edi` on and counts the half (`half_ok`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5 VG.Impl.Cast5.X86
open VG.Proof.Cast5 (XZ GroupOk keys4 runQ_z runQ_x halfImpl runZ runX)

theorem gZ : GroupOk (some .z) zLines := by unfold GroupOk; decide
theorem gX : GroupOk (some .x) xLines := by unfold GroupOk; decide
theorem gA : GroupOk none aLines := by unfold GroupOk; decide
theorem gB : GroupOk none bLines := by unfold GroupOk; decide
theorem gC : GroupOk none cLines := by unfold GroupOk; decide
theorem gD : GroupOk none dLines := by unfold GroupOk; decide

theorem storeKey_zero : (fun k => storeKey (0 + k)) = storeKey := funext fun k => by rw [Nat.zero_add]

/-- The registers key expansion's halves write. -/
def keyRegs : List Reg := [.eax, .ecx, .edx, .ebp, .edi, .ebx]

theorem keep_widen {s u : State} (h : Keep lineRegs s u) : Keep keyRegs s u :=
  Keep.mono h fun r hr => by
    simp only [lineRegs, keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp

theorem half_ok {m0 : Mem} {S : BitVec 32} {K : Addr} {s : State} {st : XZ} {ws : List Spec.Cast5.Word}
    (h : KS m0 S K s st ws) {hh : Nat} {K32 : BitVec 32} (hK : K = K32.setWidth 64)
    (hfitK : K32.toNat + 128 ≤ 2 ^ 32) (hdi : s.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh))
    (hlen : ws.length = 16 * hh) (hle : hh < 2) :
    WP isa half s fun u =>
      KS m0 S K u (halfImpl st).2 (ws ++ (halfImpl st).1) ∧
      u.gpr .edi = K32 + BitVec.ofNat 32 (64 * (hh + 1)) ∧ u.gpr .ebx = s.gpr .ebx - 1 ∧
      u.zf = some (s.gpr .ebx - 1 == 0) ∧ u.syms = s.syms ∧ Keep keyRegs s u := by
  have kd {u v : State} (k : Keep lineRegs u v) : v.gpr .edi = u.gpr .edi := k.gpr _ (by decide)
  have l4 (ls : List Impl.Cast5.Line) (t : XZ) : (keys4 ls t).length = 4 := rfl
  have hE : ∀ k < 16, addr (K32 + BitVec.ofNat 32 (64 * hh)) (4 * k) = K + BitVec.ofNat 64 (64 * hh + 4 * k) := by
    intro k hk
    rw [hK, show addr (K32 + BitVec.ofNat 32 (64 * hh)) (4 * k) = addr K32 (64 * hh + 4 * k) by
      simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]]
    exact addr_eq (by omega)
  unfold half
  refine WP.seq (WP.mono (groupQ_ok h .z gZ) fun u1 ⟨h1, s1, k1⟩ => ?_)
  rw [runQ_z] at h1
  have g2 := groupK_ok h1 gA (b := 0) (hh := hh) (by rw [kd k1, hdi]) hE (by rw [hlen]; rfl) (by omega) (by omega)
  rw [storeKey_zero] at g2
  refine WP.seq (WP.mono g2 fun u2 ⟨h2, s2, k2⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h2 .x gX) fun u3 ⟨h3, s3, k3⟩ => ?_)
  rw [runQ_x] at h3
  have g4 := groupK_ok h3 gB (b := 4) (hh := hh) (by rw [kd k3, kd k2, kd k1, hdi]) hE
    (by rw [List.length_append, hlen, l4]) (by rw [List.length_append, hlen, l4]; omega) (by omega)
  refine WP.seq (WP.mono g4 fun u4 ⟨h4, s4, k4⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h4 .z gZ) fun u5 ⟨h5, s5, k5⟩ => ?_)
  rw [runQ_z] at h5
  have g6 := groupK_ok h5 gC (b := 8) (hh := hh) (by rw [kd k5, kd k4, kd k3, kd k2, kd k1, hdi]) hE
    (by rw [List.length_append, List.length_append, hlen, l4, l4])
    (by rw [List.length_append, List.length_append, hlen, l4, l4]; omega) (by omega)
  refine WP.seq (WP.mono g6 fun u6 ⟨h6, s6, k6⟩ => ?_)
  refine WP.seq (WP.mono (groupQ_ok h6 .x gX) fun u7 ⟨h7, s7, k7⟩ => ?_)
  rw [runQ_x] at h7
  have g8 := groupK_ok h7 gD (b := 12) (hh := hh)
    (by rw [kd k7, kd k6, kd k5, kd k4, kd k3, kd k2, kd k1, hdi]) hE
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4])
    (by rw [List.length_append, List.length_append, List.length_append, hlen, l4, l4, l4]; omega) (by omega)
  refine WP.seq (WP.mono g8 fun u8 ⟨h8, s8, k8⟩ => ?_)
  have k18 := (((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans k8)
  have hdi8 : u8.gpr .edi = K32 + BitVec.ofNat 32 (64 * hh) := by rw [k18.gpr _ (by decide), hdi]
  have hbx8 : u8.gpr .ebx = s.gpr .ebx := k18.gpr _ (by decide)
  crun [hdi8, hbx8]
  have hst : (halfImpl st).2 = runX xLines (runZ zLines (runX xLines (runZ zLines st))) := rfl
  have hks : ws ++ (halfImpl st).1 = ws ++ keys4 aLines (runZ zLines st) ++
      keys4 bLines (runX xLines (runZ zLines st)) ++ keys4 cLines (runZ zLines (runX xLines (runZ zLines st))) ++
      keys4 dLines (runX xLines (runZ zLines (runX xLines (runZ zLines st)))) := by
    simp only [halfImpl, List.append_assoc]
  rw [hst, hks]
  refine ⟨h8.update rfl rfl h8.mem h8.len rfl rfl rfl, ?_, ?_, rfl, by rw [s8, s7, s6, s5, s4, s3, s2, s1],
    fun r hr => ?_, k18.rd, k18.wr⟩
  · rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]
  · rfl
  · have hr' := hr
    simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    have hl : r ∉ lineRegs := by
      simp only [lineRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hr'.1, hr'.2.1, hr'.2.2.1, hr'.2.2.2.1⟩
    simp only [gpr_setReg, gpr_arithFlags, hr'.2.2.2.2.1, hr'.2.2.2.2.2, ite_false]
    exact k18.gpr r hl

end VG.Proof.Cast5.X86
