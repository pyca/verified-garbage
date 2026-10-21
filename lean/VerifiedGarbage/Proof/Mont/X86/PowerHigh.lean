module

public import VerifiedGarbage.Impl.Mont.X86.PowerHigh
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.PowerStep

/-! Initializing the high-bit seed, with the same frame guarantee as ordinary one. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem highOne_ok {s : State} {base : Addr} {size n out : Nat} (hs : Scr s base size)
    (hn : 0 < n) (ho : out + 8*n ≤ size) :
    WP isa (VG.Impl.Mont.X86.Dynamic.highOne n out) s fun t =>
      Outside base out (8*n) s.mem t.mem ∧
      wordsVal t.mem base out n = 2^(64*n-1) ∧ Keeps [.eax, .ebp, .edx] s t := by
  unfold VG.Impl.Mont.X86.Dynamic.highOne
  refine WP.seq (WP.mono (zerosW_ok hs (by omega) (by omega)) fun s₁ ⟨O, V, K⟩ => ?_)
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  have ks : Keeps [.eax, .ebp, .edx] s s₂ := K.widen u₂.keeps
  have hs₂ := hs.of_keeps ks (by decide)
  refine wp_storeS (hs₂.ea (d := out+4*(2*n-1)) (by omega))
    (hs₂.write (d := out+4*(2*n-1)) (n := 4) (by omega))
    fun t mt => WP.block_nil ⟨?_, ?_, ks.trans (mt.keeps _)⟩
  · rw [mt.mem, u₂.mem]
    exact (O.mono (Nat.le_refl _) (by omega)).trans
      ((writeW32_outside s₁.mem base (d := out+4*(2*n-1)) (s₂.gpr .eax)
        (by have := hs.nowrap; omega)).mono (by omega) (by omega))
  · have width : 2*n = (2*n-1)+1 := by omega
    rw [width, val32_succ] at V
    have low : val32 s₁.mem base out (2*n-1) = 0 := by omega
    rw [wordsVal_eq_val32, width, mt.mem, val32_store hs.nowrap (by omega),
      u₂.mem, low, u₂.gpr, Nat.zero_add]
    change 2^(32*(2*n-1)) * 2^31 = 2^(64*n-1)
    rw [← Nat.pow_add]
    congr 1
    omega

theorem highPower_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    {M : VG.Impl.Mont.Mod} {m acc out bits : Nat} (hm : Modulus M size m s.mem base)
    (hl : OpLay M size acc out out out)
    (ho : out + 8*M.n ≤ M.mo ∨ M.mo + 8*M.n ≤ out)
    (full : 2^(64*M.n-1) < m) (hb : 0 < bits) (hb32 : bits < 2^32) :
    WP isa (VG.Impl.Mont.X86.Dynamic.highPower M acc out bits) s fun t =>
      wordsVal t.mem base out M.n = 2^(bits + (64*M.n-1)) % m ∧
      wordsVal t.mem base out M.n < m ∧ Modulus M size m t.mem base ∧
      Outs base [(out, 8*M.n), (M.tmp, 8*M.n), (acc, accLen M)] s.mem t.mem ∧
      Keeps powerClob s t := by
  unfold VG.Impl.Mont.X86.Dynamic.highPower
  refine WP.seq (WP.mono (highOne_ok hs hm.n0 hl.o_le) fun u ⟨O, V, K⟩ => ?_)
  refine WP.seq (wp_movS rfl fun v uv _ => WP.block_nil ?_)
  have kv : Keeps powerClob s v := (K.mono (by decide)).widen uv.keeps
  have hv := hs.of_keeps kv (by decide)
  have vv : wordsVal v.mem base out M.n = 2^(64*M.n-1) := by rw [uv.mem, V]
  have mv : Modulus M size m v.mem base := by
    refine ⟨hm.n0, hm.mo, hm.tmp, hm.sep, ?_⟩
    rw [uv.mem, wordsVal_eq_val32, O.val32 (by omega) (by have := hs.nowrap; have := hm.mo; omega),
      ← wordsVal_eq_val32, hm.val]
  refine WP.mono (doubleLoop_ok hv mv hl ho (by rw [vv]; exact full) hb hb32 uv.gpr) fun t I => ?_
  refine ⟨?_, I.lt, I.modulus, ?_, kv.trans I.keeps⟩
  · rw [I.value, vv, ← Nat.pow_add]
  · have ov : Outside base out (8*M.n) s.mem v.mem := uv.mem ▸ O
    exact (Outs.of_outside ov (by simp)).trans I.mem

end VG.Proof.Mont.X86.Dynamic
