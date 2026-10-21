module

public import VerifiedGarbage.Impl.Mont.X86.CombTable

public import VerifiedGarbage.Proof.Mont.X86.CombFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! Initialize the retained modulus, R-squared, and the first two comb entries. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def startRanges (n context : Nat) : List (Nat × Nat) := encodeRanges n ++ [(context, 272*n)]

theorem start_table_frame {n context d len : Nat} {base : Addr} {s t : Mem}
    (O : Outside base d len s t) (lo : context ≤ d) (hi : d+len ≤ context+272*n) :
    Outs base (startRanges n context) s t :=
  widen (Outs.of_outside O (rs := [(d,len)]) (by simp)) (by
    intro r hr; simp only [List.mem_singleton] at hr; subst r
    exact ⟨(context,272*n), by simp [startRanges], lo, hi⟩)

theorem buildStart_ok {n context size m : Nat} {base : Addr} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2^(128*n) % m) :
    WP isa (VG.Impl.Mont.X86.Comb.buildStart n context) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base context n = m ∧
      wordsVal t.mem base (context+8*n) n = 2^(128*n) % m ∧
      wordsVal t.mem base (context+16*n) n = 2^(64*n) % m ∧
      wordsVal t.mem base (context+24*n) n = wordsVal s.mem base (slot n 5) n * 2^(64*n) % m ∧
      wordsVal t.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n * 2^(64*n) % m ∧
      Outs base (startRanges n context) s.mem t.mem ∧ Keeps powerClob s t := by
  have bound := L.bound
  have b0 := L.slot (i := 0) (by decide)
  have b3 := L.slot (i := 3) (by decide)
  have b4 := L.slot (i := 4) (by decide)
  have b5 := L.slot (i := 5) (by decide)
  have b6 := L.slot (i := 6) (by decide)
  have nw := C.scr.nowrap
  unfold VG.Impl.Mont.X86.Comb.buildStart VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono (high_copy_ok L C (by omega) (Nat.le_refl _) (by omega) (.inr (.inr b0)))
    fun a ⟨Ca, Pa, Oa, Ka⟩ => ?_)
  have Ra : wordsVal a.mem base (slot n 4) n = 2^(128*n) % m :=
    (high_write_low L C.scr (by decide) Oa (Nat.le_refl _)).trans r2
  have Ga := high_write_low L C.scr (i := 5) (by decide) Oa (Nat.le_refl _)
  have Onea := (high_write_low L C.scr (i := 3) (by decide) Oa (Nat.le_refl _)).trans one
  have Pa' : wordsVal a.mem base context n = m := Pa.trans C.modulus.val
  refine WP.seq (WP.mono (high_copy_ok L Ca (by omega) (by omega) (by omega) (.inr (.inr (by omega))))
    fun b ⟨Cb, Rb, Ob, Kb⟩ => ?_)
  have Rb' : wordsVal b.mem base (context+8*n) n = 2^(128*n) % m := Rb.trans Ra
  have Pb : wordsVal b.mem base context n = m := (Ob.wordsVal (.inl (by omega)) (by omega)).trans Pa'
  have Rlow : wordsVal b.mem base (slot n 4) n = 2^(128*n) % m :=
    (high_write_low L Ca.scr (by decide) Ob (by omega)).trans Ra
  have Glow := (high_write_low L Ca.scr (i := 5) (by decide) Ob (by omega)).trans Ga
  have Onelow := (high_write_low L Ca.scr (i := 3) (by decide) Ob (by omega)).trans Onea
  refine WP.seq (WP.mono (encodeBase_ok Cb Onelow Rlow) fun c ⟨Cc, Yc, Gc, Oc, Kc⟩ => ?_)
  have Pc : wordsVal c.mem base context n = m := (encode_high L Cb.scr Oc (Nat.le_refl _) (by omega)).trans Pb
  have Rc : wordsVal c.mem base (context+8*n) n = 2^(128*n) % m :=
    (encode_high L Cb.scr Oc (by omega) (by omega)).trans Rb'
  have Gc' : wordsVal c.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n * 2^(64*n) % m := by
    rw [Gc, Glow]
  refine WP.seq (WP.mono (high_copy_ok L Cc (by omega) (by omega) (by omega) (.inr (.inr (by omega))))
    fun d ⟨Cd, Yd, Od, Kd⟩ => ?_)
  have Pd := (Od.wordsVal (d := context) (k := n) (.inl (by omega)) (by omega)).trans Pc
  have Rd := (Od.wordsVal (d := context+8*n) (k := n) (.inl (by omega)) (by omega)).trans Rc
  have Yd' := Yd.trans Yc
  have Gd := (high_write_low L Cc.scr (i := 5) (by decide) Od (by omega)).trans Gc'
  have entry1 : entry n (context+16*n) 1 = context+24*n := by unfold entry; omega
  rw [entry1]
  refine WP.seq (WP.mono (high_copy_ok L Cd (by omega) (by omega) (by omega) (.inr (.inr (by omega))))
    fun t ⟨Ct, Gt, Ot, Kt⟩ => WP.block_nil ?_)
  refine ⟨Ct, (Ot.wordsVal (.inl (by omega)) (by omega)).trans Pd,
    (Ot.wordsVal (.inl (by omega)) (by omega)).trans Rd,
    (Ot.wordsVal (.inl (by omega)) (by omega)).trans Yd', Gt.trans Gd,
    (high_write_low L Cd.scr (by decide) Ot (by omega)).trans Gd, ?_, ?_⟩
  · exact ((((start_table_frame Oa (by omega) (by omega)).trans
      (start_table_frame Ob (by omega) (by omega))).trans
      (Oc.mono (fun _ h => List.mem_append_left _ h))).trans
      (start_table_frame Od (by omega) (by omega))).trans (start_table_frame Ot (by omega) (by omega))
  · have kab : Keeps powerClob s b := (Ka.mono (by decide)).trans (Kb.mono (by decide))
    have kac : Keeps powerClob s c := kab.trans (Kc.mono (by decide))
    have kad : Keeps powerClob s d := kac.trans (Kd.mono (by decide))
    exact kad.trans (Kt.mono (by decide))

end VG.Proof.Mont.X86.Comb
