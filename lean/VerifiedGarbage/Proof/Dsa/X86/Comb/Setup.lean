module

public import VerifiedGarbage.Impl.Dsa.X86.CombSetup
import VerifiedGarbage.Proof.Mont.X86.ContextSquares
import VerifiedGarbage.Proof.Mont.X86.PublicPower
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
  have s04 := slot_le (n := n) (i := 0) (j := 4) (by decide)
  refine WP.mono (publicPower_ok Cv.scr Cv.modulus
    (context_opLay hz (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (by change slot n 4+8*n≤slot n 0 ∨ slot n 0+8*n≤slot n 4;unfold stride at s04;omega)
    hn32 hm1 hodd) fun t ⟨Vt,Mt,Ot,Kt⟩ => ?_
  obtain ⟨Ct,one,frame⟩ := Cv.power_frame Mt Ot Kt
  exact ⟨Ct,one.trans Vv,Vt,Ov.trans frame,Kv.trans Kt⟩

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
