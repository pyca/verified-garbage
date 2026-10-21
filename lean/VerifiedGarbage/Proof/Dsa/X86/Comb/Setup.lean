module

public import VerifiedGarbage.Impl.Dsa.X86.CombSetup
import VerifiedGarbage.Proof.Mont.X86.ContextSquares
import VerifiedGarbage.Proof.Mont.X86.PowerHigh
import VerifiedGarbage.Proof.Mont.X86.PowerHighBounds
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.X86.ContextInit

/-! Public full-width and padded setup paths establish the same Montgomery seed. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Comb

theorem seed_ok {n size m : Nat} {base : Addr} {s : State}
    (hs : Scr s base size) (hn : 0 < n) (hn32 : 128*n < 2^32)
    (hz : contextBytes n ≤ size) (hv : wordsVal s.mem base (slot n 0) n = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (seed n) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2^(65*n) % m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold seed
  refine WP.seq (WP.mono (contextStart_ok hs hn hz hv hm1 hodd) fun v ⟨Cv, Vv, Ov, Kv⟩ => ?_)
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have s04 := slot_le (n := n) (i := 0) (j := 4) (by decide)
  refine WP.seq (wp_movS (readSrc_sc Cv.scr (d := slot n 0 + 4*(2*n-1))
    (by unfold stride at b0; omega)) fun u₁ U₁ _ => ?_)
  refine wp_shr (by decide) fun u₂ U₂ _ => ?_
  refine wp_cmpS rfl fun w U₃ Z => WP.block_nil ?_
  have mem : w.mem = v.mem := U₃.mem.trans (U₂.mem.trans U₁.mem)
  have K : Keeps powerClob v w :=
    ((U₁.keeps.mono (by decide)).widen U₂.keeps).trans (U₃.keeps powerClob)
  have Cw : Context n m base size w :=
    ⟨Cv.scr.of_keeps K (by decide), hz, mem ▸ Cv.modulus, hm1, mem ▸ Cv.inverse⟩
  have Ostart : Outs base (setupRanges n) s.mem w.mem := mem ▸ Ov
  have Kstart := Kv.trans K
  have finish : ∀ t, Context n m base size t →
      wordsVal t.mem base (slot n 3) n = wordsVal w.mem base (slot n 3) n →
      wordsVal t.mem base (slot n 4) n = 2^(65*n) % m →
      Outs base (setupRanges n) w.mem t.mem → Keeps powerClob w t →
      Context n m base size t ∧ wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2^(65*n) % m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
    intro t Ct one value frame keep
    exact ⟨Ct, by rw [one, mem, Vv], value, Ostart.trans frame, Kstart.trans keep⟩
  refine WP.ite (u₂.gpr .eax - 1 == 0) (by simpa only [isa, eval] using Z) ?_ ?_
  · intro high
    have shifted : (v.mem.readW (off base (slot n 0+4*(2*n-1))) 32) >>> 31 = 1 := by
      have eq : (v.mem.readW (off base (slot n 0+4*(2*n-1))) 32) >>> 31 - 1 = 0 := by
        simpa only [beq_iff_eq, U₂.gpr, U₁.gpr] using high
      have add := congrArg (fun x : BitVec 32 => x + 1) eq
      simpa only [BitVec.sub_add_cancel, show (0 : BitVec 32)+1 = 1 from rfl] using add
    have top : 2^31 ≤ w32 v.mem base (slot n 0+4*(2*n-1)) := by
      have h := congrArg BitVec.toNat shifted
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h
      change _ / 2^31 = 1 at h
      change 2^31 ≤ (v.mem.readW (off base (slot n 0+4*(2*n-1))) 32).toNat
      omega
    have full : 2^(64*n-1) < m :=
      high_seed_reduced hn (Cv.modulus.val ▸ high_word_bound hn top) hodd
    refine WP.mono (highPower_ok Cw.scr Cw.modulus
      (context_opLay hz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by change slot n 4 + 8*n ≤ slot n 0 ∨ slot n 0 + 8*n ≤ slot n 4; unfold stride at s04; omega)
      full (by omega) (by omega)) fun t ⟨Vt, _, Mt, Ot, Kt⟩ => ?_
    obtain ⟨Ct, one, frame⟩ := Cw.power_frame Mt Ot Kt
    apply finish t Ct one ?_ frame Kt
    simpa only [contextMod, high_seed_doubled hn] using Vt
  · intro _
    refine WP.mono (powerTwo_ok Cw.scr Cw.modulus
      (context_opLay hz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by change slot n 4 + 8*n ≤ slot n 0 ∨ slot n 0 + 8*n ≤ slot n 4; unfold stride at s04; omega)
      hm1 (by omega) (by omega)) fun t ⟨Vt, _, Mt, Ot, Kt⟩ => ?_
    obtain ⟨Ct, one, frame⟩ := Cw.power_frame Mt Ot Kt
    exact finish t Ct one Vt frame Kt

theorem setup_ok {n size m : Nat} {base : Addr} {s : State}
    (hs : Scr s base size) (hn : 0 < n) (hn32 : 128*n < 2^32)
    (hz : contextBytes n ≤ size) (hv : wordsVal s.mem base (slot n 0) n = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (setup n) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2^(128*n) % m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold setup
  refine WP.seq (WP.mono (seed_ok hs hn hn32 hz hv hm1 hodd) fun u ⟨Cu, Ou, Vu, Fu, Ku⟩ => ?_)
  have value : wordsVal u.mem base (slot n 4) n = 2^(64*n+n) % m := by
    simpa only [show 64*n+n = 65*n by omega] using Vu
  refine WP.mono (setupSquares_ok Cu value) fun t ⟨Ct, Ot, Vt, Ft, Kt⟩ => ?_
  exact ⟨Ct, Ot.trans Ou, by simpa only [show 64*n+64*n = 128*n by omega] using Vt,
    Fu.trans Ft, Ku.trans Kt⟩

end VG.Proof.Dsa.X86.Comb
