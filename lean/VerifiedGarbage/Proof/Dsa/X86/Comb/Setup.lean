module

public import VerifiedGarbage.Impl.Dsa.X86.CombSetup
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Impl.Mont.X86.PublicPower
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Impl.Mont.X86.PowerHigh
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.PowerLoop
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.PowerTwo
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Impl.Mont.X86.ContextSquares
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.RepeatSquares

/-! ### `Mont.X86.PublicPower`, which only this module used -/

section

/-! ### `Mont.X86.PowerHigh`, which only this module used -/

section

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
  refine WP.seq (WP.mono (zerosW_ok hs (by omega_using [hn]) (by omega_using [ho])) fun s₁ ⟨O, V, K⟩ => ?_)
  refine wp_movS rfl fun s₂ u₂ _ => ?_
  have ks : Keeps [.eax, .ebp, .edx] s s₂ := K.widen u₂.keeps
  have hs₂ := hs.of_keeps ks (by decide)
  refine wp_storeS (hs₂.ea (d := out+4*(2*n-1)) (by omega_using [hn, ho]))
    (hs₂.write (d := out+4*(2*n-1)) (n := 4) (by omega_using [hn, ho]))
    fun t mt => WP.block_nil ⟨?_, ?_, ks.trans (mt.keeps _)⟩
  · rw [mt.mem, u₂.mem]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside s₁.mem base (d := out+4*(2*n-1)) (s₂.gpr .eax)
        (by have := hs.nowrap; omega_using [ho, this])).mono (by omega_using []) (by omega_using [hn]))
  · have width : 2*n = (2*n-1)+1 := by omega_using [hn]
    rw [width, val32_succ] at V
    have low : val32 s₁.mem base out (2*n-1) = 0 := by omega_using [V]
    rw [wordsVal_eq_val32, width, mt.mem, val32_store hs.nowrap (by omega_using [hn, ho]),
      u₂.mem, low, u₂.gpr, Nat.zero_add]
    change 2^(32*(2*n-1)) * 2^31 = 2^(64*n-1)
    rw [← Nat.pow_add]
    congr 1
    omega_using [hn]

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
    rw [uv.mem, wordsVal_eq_val32, O.val32 (by omega_using [ho]) (by have := hs.nowrap; have := hm.mo; omega_arith),
      ← wordsVal_eq_val32, hm.val]
  refine WP.mono (doubleLoop_ok hv mv hl ho (by rw [vv]; exact full) hb hb32 uv.gpr) fun t I => ?_
  refine ⟨?_, I.lt, I.modulus, ?_, kv.trans I.keeps⟩
  · rw [I.value, vv, ← Nat.pow_add]
  · have ov : Outside base out (8*M.n) s.mem v.mem := uv.mem ▸ O
    exact (Outs.of_outside ov (by simp)).trans I.mem

end VG.Proof.Mont.X86.Dynamic

end

end

/-! The high-bit branch and padded fallback establish the same seed. -/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/PowerHighBounds.lean`, which only this module imported.
section

/-! A public high-bit test certifies that the setup seed is reduced. -/

section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.Proof.Mont

theorem high_word_bound {mem : Mem} {base : Addr} {out n : Nat}
    (hn : 0 < n) (high : 2^31 ≤ w32 mem base (out+4*(2*n-1))) :
    2^(64*n-1) ≤ wordsVal mem base out n := by
  have width : 2*n = (2*n-1)+1 := by omega
  have exponent : 2^(64*n-1) = 2^(32*(2*n-1)) * 2^31 := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [wordsVal_eq_val32, width, val32_succ, exponent]
  have := Nat.mul_le_mul_left (2^(32*(2*n-1))) high
  omega

theorem high_seed_reduced {n m : Nat} (hn : 0 < n)
    (lower : 2^(64*n-1) ≤ m) (odd : m % 2 = 1) : 2^(64*n-1) < m := by
  have power : 64*n-1 = (64*n-2)+1 := by omega
  have even : 2^(64*n-1) % 2 = 0 := by
    rw [power, Nat.pow_succ, Nat.mul_mod]
    simp
  omega

theorem high_seed_doubled {n : Nat} (hn : 0 < n) :
    2^((n+1)+(64*n-1)) = 2^(65*n) := by
  congr 1
  omega

end VG.Proof.Mont.X86.Dynamic
end

end

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86

theorem publicPower_ok {s : State} {base : Addr} {size m acc out : Nat} {M : Mod}
    (hs : Scr s base size) (hm : Modulus M size m s.mem base)
    (hl : OpLay M size acc out out out)
    (apart : out+8*M.n≤M.mo ∨ M.mo+8*M.n≤out)
    (small : 128*M.n<2^32) (positive : 1<m) (odd : m%2=1) :
    WP isa (publicPower M acc out) s fun t =>
      wordsVal t.mem base out M.n=2^(65*M.n)%m ∧ Modulus M size m t.mem base ∧
      Outs base [(out,8*M.n),(M.tmp,8*M.n),(acc,accLen M)] s.mem t.mem ∧ Keeps powerClob s t := by
  unfold publicPower
  refine WP.seq (wp_movS (readSrc_sc hs (d := M.mo+4*(2*M.n-1))
    (by have := hm.mo;have := hm.n0;omega_arith)) fun u₁ U₁ _ => ?_)
  refine wp_shr (by decide) fun u₂ U₂ _ => ?_
  refine wp_cmpS rfl fun w U₃ Z => WP.block_nil ?_
  have mem : w.mem=s.mem := U₃.mem.trans (U₂.mem.trans U₁.mem)
  have K : Keeps powerClob s w :=
    ((U₁.keeps.mono (by decide)).widen U₂.keeps).trans (U₃.keeps powerClob)
  have Mw : Modulus M size m w.mem base := mem ▸ hm
  have finish : ∀ t, wordsVal t.mem base out M.n=2^(65*M.n)%m →
      Modulus M size m t.mem base →
      Outs base [(out,8*M.n),(M.tmp,8*M.n),(acc,accLen M)] w.mem t.mem → Keeps powerClob w t →
      wordsVal t.mem base out M.n=2^(65*M.n)%m ∧ Modulus M size m t.mem base ∧
      Outs base [(out,8*M.n),(M.tmp,8*M.n),(acc,accLen M)] s.mem t.mem ∧ Keeps powerClob s t := by
    intro t V T O L
    exact ⟨V,T,mem ▸ O,K.trans L⟩
  refine WP.ite (u₂.gpr .eax-1==0) (by simpa only [isa,eval] using Z) ?_ ?_
  · intro high
    have shifted : (s.mem.readW (off base (M.mo+4*(2*M.n-1))) 32) >>> 31=1 := by
      have eq : (s.mem.readW (off base (M.mo+4*(2*M.n-1))) 32) >>> 31-1=0 := by
        simpa only [beq_iff_eq,U₂.gpr,U₁.gpr] using high
      have add := congrArg (fun x : BitVec 32 => x+1) eq
      simpa only [BitVec.sub_add_cancel,show (0 : BitVec 32)+1=1 from rfl] using add
    have top : 2^31≤w32 s.mem base (M.mo+4*(2*M.n-1)) := by
      have h := congrArg BitVec.toNat shifted
      rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow] at h
      change _/2^31=1 at h
      change 2^31≤(s.mem.readW (off base (M.mo+4*(2*M.n-1))) 32).toNat
      omega_using [h]
    have full : 2^(64*M.n-1)<m :=
      high_seed_reduced hm.n0 (hm.val ▸ high_word_bound hm.n0 top) odd
    refine WP.mono (highPower_ok (hs.of_keeps K (by decide)) Mw hl apart full
      (by omega_using []) (by omega_using [small])) fun t ⟨V,_,T,O,L⟩ => ?_
    apply finish t ?_ T O L
    simpa only [high_seed_doubled hm.n0] using V
  · intro _
    exact WP.mono (powerTwo_ok (hs.of_keeps K (by decide)) Mw hl apart positive
      (by have := hm.n0;omega_using [this]) (by omega_using [small])) fun t ⟨V,_,T,O,L⟩ => finish t V T O L

end VG.Proof.Mont.X86.Dynamic

end

end

/-! Public full-width and padded setup paths establish the same Montgomery seed. -/

-- Formerly `VerifiedGarbage/Proof/Mont/X86/ContextSquares.lean`, which only this module imported.
section

/-! The common squaring-loop proof instantiated for the DSA Montgomery workspace. -/

section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86

structure SetupState (n m size : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  one : wordsVal t.mem base (slot n 3) n=wordsVal s.mem base (slot n 3) n
  mem : Outs base (setupRanges n) s.mem t.mem
  keeps : Keeps powerClob s t

theorem setupSquares_ok {n size m a : Nat} {base : Addr} {s : State}
    (C : Context n m base size s)
    (V : wordsVal s.mem base (slot n 4) n=2^(64*n+a)%m) :
    WP isa (setupSquares n) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 3) n=wordsVal s.mem base (slot n 3) n ∧
      wordsVal t.mem base (slot n 4) n=2^(64*n+64*a)%m ∧
      Outs base (setupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  let square := mul (contextMod n) 0 (slot n 2) (slot n 4) (slot n 4) (slot n 4)
  let P := SetupState n m size base s
  let num := fun t : State => wordsVal t.mem base (slot n 4) n
  have stable (u v : State) (U : P u) (mem : v.mem=u.mem) (keep : Keeps [.esi] u v) : P v :=
    ⟨⟨U.context.scr.of_keeps keep (by decide),U.context.size_le,mem ▸ U.context.modulus,
      U.context.gt_one,mem ▸ U.context.inverse⟩,mem ▸ U.one,mem ▸ U.mem,
      U.keeps.trans (keep.mono (by decide))⟩
  have step (u : State) (U : P u) (lt : num u<m) :
      WP isa square u fun v =>
        P v ∧ Keeps clob u v ∧ num v<m ∧ num v*2^(64*n)%m=num u*num u%m := by
    refine WP.mono (context_mul_ok U.context (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) lt) fun v ⟨Cv,K,lv,Mv⟩ => ?_
    refine ⟨⟨Cv,?_,U.mem.trans (K.mem.mono ?_),
      U.keeps.trans ((OpKeep.keeps K).mono (by decide))⟩,OpKeep.keeps K,lv,Mv⟩
    · exact (context_slot_val U.context (i := 3) (by decide) (by decide) (by decide) (by decide) K).trans U.one
    · intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [setupRanges,contextMod,accLen,words] <;> omega
  have initial : P s := ⟨C,rfl,Outs.refl _ _ _,Keeps.refl _ _⟩
  change WP isa (repeatSquaresWith square 6) s _
  refine WP.mono (repeatSquaresWith_ok square P num (E := a) C.coprime stable
    (fun u v h => by dsimp only [num];rw [h]) step (by decide) (by decide) initial
    (by dsimp only [num];rw [V];exact Nat.mod_lt _ (by have := C.gt_one;omega))
    (by dsimp only [num];rw [V,Nat.mod_mod,←Nat.pow_add];congr 2;omega))
    fun t ⟨T,lt,value⟩ => ?_
  refine ⟨T.context,T.one,?_,T.mem,T.keeps⟩
  rw [Nat.mod_eq_of_lt lt,show 2^(6 : Nat)*a=64*a from rfl,←Nat.pow_add] at value
  simpa only [Nat.add_comm] using value

end VG.Proof.Mont.X86.Dynamic
end

end

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
    (by change slot n 4+8*n≤slot n 0 ∨ slot n 0+8*n≤slot n 4;unfold stride at s04;omega_using [s04])
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
    simpa only [show 64*n+n = 65*n by omega_using []] using Vu
  refine WP.mono (setupSquares_ok Cu value) fun t ⟨Ct, Ot, Vt, Ft, Kt⟩ => ?_
  exact ⟨Ct, Ot.trans Ou, by simpa only [show 64*n+64*n = 128*n by omega_using []] using Vt,
    Fu.trans Ft, Ku.trans Kt⟩

end VG.Proof.Dsa.X86.Comb
