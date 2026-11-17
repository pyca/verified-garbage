module

public import VerifiedGarbage.Proof.Dsa.X86.Moduli
public import VerifiedGarbage.Proof.Dsa.X86.StageFrame
public import VerifiedGarbage.Proof.Dsa.X86.CoreFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
import VerifiedGarbage.Proof.Dsa.X86.CoreStore
import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Dsa.X86.CoreInputs
import VerifiedGarbage.Proof.Dsa.X86.CoreSetup
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
public import VerifiedGarbage.Proof.Dsa.X86.StreamFrame
import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Dsa.X86.PowCallFrame
public import VerifiedGarbage.Impl.Dsa.X86.Arith
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
public import VerifiedGarbage.Proof.Dsa.ModPowContract
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Dsa.X86.StreamStep
import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Dsa.StreamBytes
public import VerifiedGarbage.Proof.Dsa.X86.PowABI
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.StreamTiming
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Dsa.X86.WorkspaceCall
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Arithmetic

/-! ### `Dsa.X86.MulCall`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.MulBody`, which this module and modules that import it used -/

section

/-! # IA-32 DSA products with their callee-saved registers restored -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Mul
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86.Pow (Entry save_ok restore_ok)

/-- A word outside every range that changed keeps its value. -/
theorem Outs.readW32 {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d : Nat} (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hn : base.toNat + d + 4 ≤ 2 ^ 32) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun i hi => h _ fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega_using [hn, hi])]; omega_using [hi, this]

theorem body_ok {s : State} {base : Addr} {size n m : Nat}
    (E : Entry s base size) (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (mulBody n) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n * wordsVal s.mem base (slot n 8) n % m ∧
      Outs base (scratch n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have nw := E.nowrap
  have hz' := hz
  simp only [contextBytes, slot, stride] at hz'
  have hz24 : 24 ≤ size := by omega_using [hz']
  unfold mulBody
  refine WP.seq (WP.mono (save_ok E hz24) fun u ⟨Su, Sv, Ou, Ku⟩ => ?_)
  have kept (i : Nat) (hi : i < 9) : wordsVal u.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
    have := slot_bound (n := n) hi
    simp only [stride] at this
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact Ou.val32 (by simp only [slot]; omega_using []) (by omega_using [hz, nw, this])
  refine WP.seq (WP.mono (contextSetup_ok Su hn (by omega_using [hn48]) hz ((kept 0 (by decide)).trans hv) hm1 hodd)
    fun v ⟨Cv, _, R2, Ov, Kv⟩ => ?_)
  have setupVal (i : Nat) (hi : i = 5 ∨ i = 8) :
      wordsVal v.mem base (slot n i) n = wordsVal u.mem base (slot n i) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    rcases hi with rfl | rfl <;>
    · refine Ov.val32 (fun r hr => ?_) (by simp only [slot, stride]; omega_using [hn48])
      simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using []
  refine WP.seq (WP.mono (ordinaryMul_ok Cv R2) fun w ⟨Cw, Vw, Ow, Kw⟩ => ?_)
  have savedW : Saved w.mem (off base) s.gpr slots := by
    intro p hp
    have hp' : 8 ≤ p.2 ∧ p.2 + 4 ≤ 24 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    rw [Outs.readW32 Ow (fun r hr => by
        simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using [hp']) (by omega_using [nw, hz', hp']),
      Outs.readW32 Ov (fun r hr => by
        simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using [hp']) (by omega_using [nw, hz', hp'])]
    exact Sv p hp
  have Kuw : Keeps powerClob u w := Kv.trans (Kw.mono (by decide))
  refine WP.mono (restore_ok (Su.of_keeps Kuw (by decide)) hz24 savedW)
    fun t R' => ⟨?_, ?_, R'.abi (by decide) (by decide) ?_, ?_, ?_⟩
  · rw [R'.mem, Vw, setupVal 5 (.inl rfl), setupVal 8 (.inr rfl),
      kept 5 (by decide), kept 8 (by decide)]
  · rw [R'.mem]
    have cover : ∀ y : Nat, (∀ r ∈ scratch n, y < r.1 ∨ r.1 + r.2 ≤ y) →
        y < 8 ∨ 24 ≤ y ∧ ∀ r ∈ setupRanges n ++ productRanges n, y < r.1 ∨ r.1 + r.2 ≤ y := by
      intro y hy
      have h0 := hy (0, 64) (List.mem_cons_self ..)
      have h1 := hy _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      dsimp only at h0 h1
      simp only [contextBytes, slot, stride] at h1
      by_cases y8 : y < 8
      · exact .inl y8
      refine .inr ⟨by omega_using [h0], fun r hr => ?_⟩
      simp only [setupRanges, productRanges, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [slot, stride] <;> omega_arith
    intro x hx
    rcases cover _ hx with lo | ⟨hi, rest⟩
    · rw [Ow x (fun r hr => by
          simp only [productRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using [lo]),
        Ov x (fun r hr => by
          simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
          have h0 := hx (0, 64) (List.mem_cons_self ..)
          dsimp only at h0
          rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_arith)]
      exact Ou x (.inl lo)
    · rw [Ow x (fun r hr => rest r (List.mem_append_right _ hr)),
        Ov x (fun r hr => rest r (List.mem_append_left _ hr))]
      exact Ou x (.inr (by omega_using [hi]))
  · exact (Kuw.1 _ (by decide)).trans (Ku.1 _ (by decide))
  · rw [R'.rd, Kuw.2.1, Ku.2.1]
  · rw [R'.wr, Kuw.2.2, Ku.2.2]

end VG.Proof.Dsa.X86.Mul

end

end

/-! The ordinary product helper uses the shared workspace-call boundary. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Mul
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Arith

theorem body_noSp (n : Nat) : NoSp (mulBody n) := NoSp.of_all rfl

theorem body_stackUse (n : Nat) : stackUse (mulBody n) = 0 := rfl

theorem call_ok {s : State} {base : Addr} {size n m : Nat}
    (hs : Scr s base size) (room : Pow.Room (s.gpr .esp) base size)
    (hz : contextBytes n ≤ size) (hused : VG.Impl.Dsa.Layout.usedBytes ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (mulCall n) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n * wordsVal s.mem base (slot n 8) n % m ∧
      StackOuts base (s.gpr .esp) (VG.Impl.Dsa.X86.Pow.scratch n) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t := by
  unfold mulCall
  let P := fun mem => wordsVal mem base (slot n 0) n = m ∧
    wordsVal mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n ∧
    wordsVal mem base (slot n 8) n = wordsVal s.mem base (slot n 8) n
  refine workspaceCall_ok (P := P) (Q := fun mem => wordsVal mem base (slot n 6) n =
      wordsVal s.mem base (slot n 5) n * wordsVal s.mem base (slot n 8) n % m)
    (bytes := contextBytes n) (name := mulName n) hs room hused (body_noSp n)
    (by rw [body_stackUse]; decide) (Pow.scratch_fits hz) ?_ ?_
  · intro mem F
    have vals : ∀ d k, d + 4 * k ≤ size → val32 mem base d k = val32 s.mem base d k :=
      fun _ _ hd => Pow.frame_val32 room hs.nowrap F hd
    refine ⟨?_, ?_, ?_⟩
    · rw [wordsVal_eq_val32, vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega_using [hz]),
        ← wordsVal_eq_val32, hv]
    · rw [wordsVal_eq_val32, wordsVal_eq_val32]
      exact vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega_using [hz])
    · rw [wordsVal_eq_val32, wordsVal_eq_val32]
      exact vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega_using [hz])
  · intro v E _ ⟨M, A, B⟩
    exact WP.mono (body_ok E hz hn hn48 M hm1 hodd) fun w ⟨V, O, R, Rd, Wr⟩ =>
      ⟨by rw [V, A, B], Pow.OutsS.of_outs O, R, Rd, Wr⟩

end VG.Proof.Dsa.X86.Mul

end

end

/-! ### `Dsa.X86.CoreReduce`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.RedCall`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86.RedTiming`, which only this module used -/

section

/-! ### `Dsa.X86.RedBody`, which only this module used -/

section

/-! # IA-32 DSA reductions with their callee-saved registers restored -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/StreamInit.lean`, which only this module imported.
section

/-! # Initializing the streaming accumulator and byte padding -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem zeroSlot_ok {n size m j : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hj : 0 < j) (hj9 : j < 9) :
    WP isa (zerosW (slot n j) (2 * n)) s fun t =>
      Context n m base size t ∧ wordsVal t.mem base (slot n j) n = 0 ∧
      Outside base (slot n j) (8 * n) s.mem t.mem ∧ Keeps [.eax, .ebp, .edx] s t := by
  obtain b := slot_bound (n := n) hj9
  obtain sep := slot_le (n := n) (i := 0) (j := j) hj
  obtain hd := slot_header n j
  have sz := h.size_le
  have n0 : 0 < n := h.modulus.n0
  refine WP.mono (zerosW_ok h.scr (by omega) (by unfold stride at b; omega)) fun t ⟨O, V, K⟩ => ?_
  obtain len : 4 * (2 * n) = 8 * n := by omega
  rw [len] at O
  exact ⟨h.outside_keep K (by decide) (by decide) O (.inl (by unfold stride at sep; omega)) (by omega),
    by rw [wordsVal_eq_val32, V], O, K⟩

/-- Clearing slots six and seven before `rest`. -/
theorem streamInit_ok {n size m : Nat} {base : Addr} {s : State} {rest : Prog isa} {Q : State → Prop}
    (h : Context n m base size s)
    (k : ∀ t, Context n m base size t → wordsVal t.mem base (slot n 6) n = 0 →
      wordsVal t.mem base (slot n 7) n = 0 → Outs base (streamRanges n) s.mem t.mem →
      Keeps [.eax, .ebp, .edx] s t → WP isa rest t Q) :
    WP isa (.seq (zerosW (slot n 6) (2 * n)) (.seq (zerosW (slot n 7) (2 * n)) rest)) s Q := by
  refine WP.seq (WP.mono (zeroSlot_ok h (j := 6) (by decide) (by decide)) fun u ⟨cu, Yu, Ou, Ku⟩ => ?_)
  refine WP.seq (WP.mono (zeroSlot_ok cu (j := 7) (by decide) (by decide)) fun v ⟨cv, Bv, Ov, Kv⟩ => ?_)
  obtain sep := slot_le (n := n) (i := 6) (j := 7) (by decide)
  obtain bd := slot_bound (n := n) (i := 6) (by decide)
  have sz := h.size_le
  have nw := h.scr.nowrap
  obtain Yv : wordsVal v.mem base (slot n 6) n = 0 := by
    rw [wordsVal_eq_val32, Ov.val32 (by unfold stride at sep; omega)
      (by unfold stride at bd; omega), ← wordsVal_eq_val32, Yu]
  exact k v cv Yv Bv ((Outs.of_outside Ou (by simp [streamRanges])).trans (Outs.of_outside Ov (by simp [streamRanges])))
    (Ku.trans Kv)

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/StreamLoop.lean`, which only this module imported.
section

/-! # Functional correctness and termination of streaming reduction -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86

structure StreamInv (n size m len i : Nat) (base : Addr) (p : BitVec 32) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .esi = p + BitVec.ofNat 32 i
  stop : t.gpr .ebx = p + BitVec.ofNat 32 len
  value : wordsVal t.mem base (slot n 6) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) i) % m
  lt : wordsVal t.mem base (slot n 6) n < m
  pad : wordsVal t.mem base (slot n 7) n < 2 ^ 32
  mem : Outs base (streamRanges n) s.mem t.mem
  keeps : Keeps powerClob s t

theorem streamLoop_ok {n size m len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hlen : 0 < len) (hlen32 : len < 2 ^ 32)
    (inp : StreamInput s base (contextBytes n) p len)
    (hc : s.gpr .esi = p) (he : s.gpr .ebx = p + BitVec.ofNat 32 len) (hv : wordsVal s.mem base (slot n 6) n = 0)
    (hpad : wordsVal s.mem base (slot n 7) n < 2 ^ 32) :
    WP isa (.loop (streamStep n) .ne) s (StreamInv n size m len len base p s) := by
  obtain init : StreamInv n size m len 0 base p s s := by
    refine ⟨h, by rw [hc]; exact (BitVec.add_zero _).symm, he, ?_, by rw [hv]; omega, hpad, Outs.refl _ _ _,
      Keeps.refl _ _⟩
    rw [hv]
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, Spec.Dsa.decodeBE, List.foldl_nil, Nat.zero_mod]
  refine WP.loop (M := isa)
    (fun k t => ∃ i, k = len - i ∧ i < len ∧ StreamInv n size m len i base p s t)
    ?_ len s ⟨0, rfl, hlen, init⟩
  rintro k t ⟨i, rfl, hi, I⟩
  obtain inpt := inp.keep I.keeps
  refine WP.mono (streamStep_ok I.context hm hi hlen32 I.counter I.stop inpt.fit (inpt.read i hi) I.lt I.pad)
    fun u ⟨cu, count, stop, zf, val, pad, O, K⟩ => ?_
  obtain next : StreamInv n size m len (i + 1) base p s u := by
    refine ⟨cu, count, stop.trans I.stop, ?_, ?_, pad, I.mem.trans O, I.keeps.trans K⟩
    · rw [val, I.value, inp.byte hi (streamRanges_whole (Nat.le_refl _) I.mem), VG.Proof.Dsa.reduce_prefix_succ]
    · rw [val]; exact Nat.mod_lt _ (by omega)
  by_cases done : i + 1 = len
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, zf, done, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, len - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    simp only [eval, zf, decide_eq_false done, Option.map_some, Bool.not_false]

end VG.Proof.Dsa.X86
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/Stream.lean`, which only this module imported.
section

/-! # Complete streaming reduction, including the empty input -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.X86

theorem reduceStream_ok {n size m len : Nat} {base : Addr} {s : State} {p : BitVec 32} {src : Src}
    (h : Context n m base size s) (hm : 255 < m) (hlen : len < 2 ^ 32)
    (hsrc : LenSrc base size n s src len)
    (inp : StreamInput s base (contextBytes n) p len) (hp : s.gpr .esi = p) :
    WP isa (reduceStream n src) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold reduceStream
  refine streamInit_ok h fun u cu Y B O K' => ?_
  obtain K : Keeps powerClob s u := K'.mono (by decide)
  obtain esi : u.gpr .esi = p := by rw [K'.1 _ (by decide)]; exact hp
  refine WP.seq (wp_movS (hsrc u cu.scr K.2.1 K.2.2 O) fun u₁ v₁ _ => WP.block_nil ?_)
  refine WP.seq (wp_addS rfl fun u₂ v₂ _ => wp_cmpS rfl fun u₃ f₃ z₃ => WP.block_nil ?_)
  obtain K₃ : Keeps powerClob u u₃ := ((v₁.keeps.mono (by decide)).widen v₂.keeps).trans (f₃.keeps _)
  obtain m₃ : u₃.mem = u.mem := by rw [f₃.mem, v₂.mem, v₁.mem]
  obtain c₃ : Context n m base size u₃ := ⟨cu.scr.of_keeps K₃ (by decide), cu.size_le,
    m₃ ▸ cu.modulus, cu.gt_one, m₃ ▸ cu.inverse⟩
  obtain esi₂ : u₂.gpr .esi = p := by rw [v₂.other _ (by decide), v₁.other _ (by decide), esi]
  obtain ebx₂ : u₂.gpr .ebx = p + BitVec.ofNat 32 len := by
    rw [v₂.gpr, v₁.gpr, v₁.other _ (by decide), esi, BitVec.add_comm]
  obtain z : (p - (p + BitVec.ofNat 32 len) == 0) = decide (len = 0) := by
    rw [show p - (p + BitVec.ofNat 32 len) = BitVec.ofNat 32 0 - BitVec.ofNat 32 len by bv_omega,
      counter_equal (by decide) hlen]
    exact decide_eq_decide.mpr eq_comm
  rw [esi₂, ebx₂, z] at z₃
  by_cases hz : len = 0
  · refine WP.ite true (by simp only [eval, z₃, hz, decide_true]) (fun _ => WP.block_nil ⟨c₃, ?_, by rw [m₃]; exact O,
      K.trans K₃⟩) (fun h => Bool.noConfusion h)
    rw [m₃, Y, hz]
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, Spec.Dsa.decodeBE, List.foldl_nil, Nat.zero_mod]
  · refine WP.ite false (by simp only [eval, z₃, hz, decide_false]) (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain Os : Outs base (streamRanges n) s.mem u₃.mem := by rw [m₃]; exact O
    obtain Ks : Keeps powerClob s u₃ := K.trans K₃
    obtain count : u₃.gpr .esi = p := by rw [f₃.gpr, esi₂]
    obtain stop : u₃.gpr .ebx = p + BitVec.ofNat 32 len := by rw [f₃.gpr, ebx₂]
    refine WP.mono (streamLoop_ok c₃ hm (by omega) hlen (inp.keep Ks) count stop
      (by rw [m₃]; exact Y) (by rw [m₃, B]; decide)) fun t I => ⟨I.context, ?_, Os.trans I.mem, Ks.trans I.keeps⟩
    rw [I.value, inp.bytes (streamRanges_whole (Nat.le_refl _) Os)]

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86.Pow (Entry save_ok restore_ok)
open VG.Proof.Dsa.X86 (StreamInput LenSrc streamRanges setupRanges_whole streamRanges_whole reduceStream_ok)

/-- A word apart from the working space keeps its value across changes within it. -/
theorem readW_apart {base : Addr} {o n size : Nat} {m m' : Mem} {a : Addr} (h : Outside base o n m m')
    (ho : o + n ≤ size) (hd : Region.Disjoint ⟨a, 4⟩ ⟨base, size⟩) : m'.readW a 32 = m.readW a 32 :=
  (Mem.readW_congr fun i hi => (h _ (.inr (by
    have := hd _ (Offset.contains_base a (d := i) (n := 1) (k := 4) (by omega_using [hi]) (by omega_using [hi]))
    simp only [Region.Contains] at this
    simp only [ofs]
    omega_using [ho, this]))).symm).symm

/-- What a reduction needs of the state it starts in, besides the modulus:
its stack arguments readable and apart from the working space, the bytes'
address `p` and length `len`, and the bytes readable and apart from the
context. -/
structure In (n : Nat) (s : State) (base : Addr) (size : Nat) (p : BitVec 32) (len : Nat) : Prop where
  entry : Entry s base size
  arg2 : InRegions (s.rd ++ s.wr) (argAddr s 2) 4
  arg3 : InRegions (s.rd ++ s.wr) (argAddr s 3) 4
  apart2 : Region.Disjoint ⟨argAddr s 2, 4⟩ ⟨base, size⟩
  apart3 : Region.Disjoint ⟨argAddr s 3, 4⟩ ⟨base, size⟩
  data : arg s 2 = p
  length : arg s 3 = BitVec.ofNat 32 len
  lenFit : len < 2 ^ 32
  input : StreamInput s base (contextBytes n) p len

/-- What the prefix leaves for the stream: the context, the bytes' address in
`esi` and their length in the header, the saved registers, and changes only
within the header and the context. -/
structure Ready (n m : Nat) (s x : State) (base : Addr) (size : Nat) (p : BitVec 32) (len : Nat) : Prop where
  ctx : Context n m base size x
  esi : x.gpr .esi = p
  lenSrc : LenSrc base size n x (.mem (sc lenAt)) len
  input : StreamInput x base (contextBytes n) p len
  outs : Outs base (scratch n) s.mem x.mem
  outside : Outside base 0 (contextBytes n) s.mem x.mem
  saved : Saved x.mem (off base) s.gpr slots
  esp : x.gpr .esp = s.gpr .esp
  rd : x.rd = s.rd
  wr : x.wr = s.wr

theorem prefix_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32}
    (I : In n s base size p len) (hz : contextBytes n ≤ size) (hn : 0 < n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm : 255 < m) (hodd : m % 2 = 1) :
    WP isa (reducePrefix n) s fun x => Ready n m s x base size p len := by
  have E := I.entry
  have nw := E.nowrap
  have hz' := hz
  simp only [contextBytes, slot, stride] at hz'
  obtain hz24 : 24 ≤ size := by omega_using [hz']
  unfold reducePrefix
  refine WP.seq (WP.mono (save_ok E hz24) fun u ⟨Su, Sv, Ou, Ku⟩ => ?_)
  obtain usp : u.gpr .esp = s.gpr .esp := Ku.1 _ (by decide)
  -- the arguments, as the saves left them
  obtain a3 : u.mem.readW (addr (u.gpr .esp) 16) 32 = BitVec.ofNat 32 len := by
    rw [usp]
    exact (readW_apart Ou (by omega_using [hz']) I.apart3).trans I.length
  obtain a2 : u.mem.readW (addr (u.gpr .esp) 12) 32 = p := by
    rw [usp]
    exact (readW_apart Ou (by omega_using [hz']) I.apart2).trans I.data
  obtain r3 : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 16) 4 := by
    rw [usp, Ku.2.1, Ku.2.2]; exact I.arg3
  obtain r2 : InRegions (u.rd ++ u.wr) (addr (u.gpr .esp) 12) 4 := by
    rw [usp, Ku.2.1, Ku.2.2]; exact I.arg2
  unfold stash
  refine WP.seq (wp_ldm rfl r3 fun u₁ U₁ => ?_)
  refine wp_ldm (by rw [U₁.other _ (by decide)]) (by rw [U₁.rd, U₁.wr]; exact r2) fun u₂ U₂ => ?_
  obtain K₂ : Keeps [.eax, .ecx] u u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  obtain S₂ : Scr u₂ base size := Su.of_keeps K₂ (by decide)
  refine wp_storeS (S₂.ea (show 24 < size by omega_using [hz'])) (S₂.write (show 24 + 4 ≤ size by omega_using [hz'])) fun u₃ M₃ => ?_
  obtain S₃ : Scr u₃ base size := S₂.of_keeps (M₃.keeps [.eax]) (by decide)
  refine wp_storeS (S₃.ea (show 28 < size by omega_using [hz'])) (S₃.write (show 28 + 4 ≤ size by omega_using [hz'])) fun w M₄ =>
    WP.block_nil ?_
  obtain Sw : Scr w base size := S₃.of_keeps (M₄.keeps [.eax]) (by decide)
  obtain Mw : w.mem = ((u.mem.writeW (off base 24) (BitVec.ofNat 32 len)).writeW (off base 28) p) := by
    obtain e1 : u₂.gpr .eax = BitVec.ofNat 32 len := by rw [U₂.other _ (by decide), U₁.gpr]; exact a3
    obtain e2 : u₂.gpr .ecx = p := by rw [U₂.gpr, U₁.mem]; exact a2
    rw [M₄.mem, M₃.gpr, e2, M₃.mem, e1, U₂.mem, U₁.mem]
    rfl
  obtain OW : Outs base [(24, 4), (28, 4)] u.mem w.mem := by
    rw [Mw]
    exact (Outs.of_outside (writeW32_outside _ base _ (by decide)) (by simp)).trans
      (Outs.of_outside (writeW32_outside _ base _ (by decide)) (by simp))
  obtain W24 : w.mem.readW (off base 24) 32 = BitVec.ofNat 32 len := by
    rw [Mw, Mul.Outs.readW32 (Outs.of_outside (rs := [(28, 4)]) (writeW32_outside _ base _ (by decide)) (by simp))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; omega_using []) (by omega_using [nw, hz'])]
    exact Mem.readW_writeW_self32 _ _ _
  obtain W28 : w.mem.readW (off base 28) 32 = p := by
    rw [Mw]; exact Mem.readW_writeW_self32 _ _ _
  obtain Kuw : Keeps [.eax, .ecx] u w := K₂.trans ((M₃.keeps _).trans (M₄.keeps _))
  -- the modulus is where the caller left it
  obtain Osw : Outs base [(8, 16), (24, 4), (28, 4)] s.mem w.mem :=
    (Outs.of_outside Ou (by simp)).trans (OW.mono (by simp))
  obtain hvw : wordsVal w.mem base (slot n 0) n = m := by
    rw [wordsVal_eq_val32, Osw.val32 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [slot] <;> omega_using []) (by simp only [slot]; omega_using [nw, hz']),
      ← wordsVal_eq_val32, hv]
  refine WP.seq (WP.mono (contextStart_ok Sw hn hz hvw (by omega_using [hm]) hodd) fun v ⟨Cv, _, Ov, Kv⟩ => ?_)
  have avoid (d : Nat) (hd : 24 ≤ d ∧ d + 4 ≤ 64) : ∀ r ∈ setupRanges n, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro r hr
    simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using [hd]
  obtain V28 : v.mem.readW (off base 28) 32 = p := by
    rw [Mul.Outs.readW32 Ov (avoid 28 (by omega_using [])) (by omega_using [nw, hz']), W28]
  have Sv' : Scr v base size := Cv.scr
  refine wp_movS (readSrc_sc Sv' (show 28 + 4 ≤ size by omega_using [hz'])) fun x X _ => WP.block_nil ?_
  obtain Cx : Context n m base size x :=
    Cv.outs_keep (ranges := []) X.keeps (by decide) (by decide) (fun _ _ => by rw [X.mem])
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
  obtain xrd : x.rd = s.rd := by rw [X.rd, Kv.2.1, Kuw.2.1, Ku.2.1]
  obtain xwr : x.wr = s.wr := by rw [X.wr, Kv.2.2, Kuw.2.2, Ku.2.2]
  obtain hsrc : LenSrc base size n x (.mem (sc lenAt)) len := by
    intro y hy _ _ O
    change readSrc y (.mem (sc 24)) = _
    rw [readSrc_sc hy (show 24 + 4 ≤ size by omega_using [hz'])]
    refine congrArg _ ?_
    rw [Mul.Outs.readW32 O (fun r hr => by
        simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using []) (by omega_using [nw, hz']),
      X.mem, Mul.Outs.readW32 Ov (avoid 24 (by omega_using [])) (by omega_using [nw, hz']), W24]
  obtain inp : StreamInput x base (contextBytes n) p len :=
    ⟨I.input.fit, by rw [xrd, xwr]; exact I.input.read, I.input.far, by rw [xrd, xwr]; exact I.input.whole⟩
  -- every change so far is in the header and the context's slots
  obtain Osx : Outs base (scratch n) s.mem x.mem := by
    intro z hz
    obtain h0 := hz (0, 64) (List.mem_cons_self ..)
    obtain h1 := hz _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    dsimp only at h0 h1
    simp only [contextBytes, slot, stride] at h1
    rw [X.mem, Ov z (fun r hr => by
        simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_arith),
      Osw z (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> omega_using [h0])]
  obtain Ox : Outside base 0 (contextBytes n) s.mem x.mem := fun z hz => Osx z fun r hr => by
    simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> simp only [contextBytes, slot, stride] at hz ⊢ <;> omega_using [hz]
  obtain savedX : Saved x.mem (off base) s.gpr slots := by
    intro q hq
    obtain hq' : 8 ≤ q.2 ∧ q.2 + 4 ≤ 24 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> decide
    rw [X.mem, Mul.Outs.readW32 Ov (fun r hr => by
        simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using [hq']) (by omega_using [nw, hz', hq']),
      Mul.Outs.readW32 OW (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> omega_using [hq']) (by omega_using [nw, hz', hq'])]
    exact Sv q hq
  obtain Kwx : Keeps powerClob w x := Kv.trans (X.keeps.mono (by decide))
  exact ⟨Cx, by rw [X.gpr]; exact V28, hsrc, inp, Osx, Ox, savedX,
    by rw [Kwx.1 _ (by decide), Kuw.1 _ (by decide)]; exact usp, xrd, xwr⟩

theorem body_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32}
    (I : In n s base size p len) (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm : 255 < m) (hodd : m % 2 = 1) :
    WP isa (reduceBody n) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len) % m ∧
      Outs base (scratch n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hz' := hz
  simp only [contextBytes, slot, stride] at hz'
  unfold reduceBody
  refine WP.seq (WP.mono (prefix_ok I hz hn hv hm hodd) fun x R => ?_)
  refine WP.seq (WP.mono (reduceStream_ok R.ctx hm I.lenFit R.lenSrc R.input R.esi)
    fun y ⟨Cy, Vy, Oy, Ky⟩ => ?_)
  obtain Oxy : Outs base (scratch n) x.mem y.mem := VG.Proof.Mont.X86.Outs.widen Oy fun z hz r hr => by
    obtain h1 := hz _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    dsimp only at h1
    simp only [contextBytes, slot, stride] at h1
    simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega
  obtain savedY : Saved y.mem (off base) s.gpr slots := by
    intro q hq
    obtain hq' : 8 ≤ q.2 ∧ q.2 + 4 ≤ 24 := by
      simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> decide
    rw [Mul.Outs.readW32 Oy (fun r hr => by
        simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using [hq'])
        (by have := I.entry.nowrap; omega_using [hz', hq', this])]
    exact R.saved q hq
  refine WP.mono (restore_ok Cy.scr (by omega_using [hz']) savedY)
    fun t R' => ⟨?_, ?_, R'.abi (by decide) (by decide) ?_, ?_, ?_⟩
  · rw [R'.mem, Vy, I.input.bytes R.outside]
  · rw [R'.mem]; exact R.outs.trans Oxy
  · rw [Ky.1 _ (by decide)]; exact R.esp
  · rw [R'.rd, Ky.2.1, R.rd]
  · rw [R'.wr, Ky.2.2, R.wr]

end VG.Proof.Dsa.X86.Red

end

end


/-! # Traces of the IA-32 DSA reduction

Two runs with the same stack pointer and arguments leak the same trace: the
saves and the loads of the arguments are at public addresses, the context's
setup is checked by taint, and the stream runs from the same public address
and length (`reduceStream_relCT`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith VG.Proof.Mont.X86.Dynamic
open VG.Proof.Dsa.X86.Pow (ws bytes)

/-- What the body needs of a run on entry, at the places its arguments give,
with a working space of `size` bytes. -/
structure BodyIn (n size : Nat) (s : State) : Prop where
  input : In n s (ws s) size (arg s 2) (arg s 3).toNat
  size : contextBytes n ≤ size
  large : 255 < wordsVal s.mem (ws s) (slot n 0) n
  odd : wordsVal s.mem (ws s) (slot n 0) n % 2 = 1

/-- Two runs of the body: the same stack pointer and arguments. -/
def Pair (n size : Nat) (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ i < 4, arg s i = arg t i) ∧
    readSrc s (.mem (at_ .esp 4)) = some (arg s 0) ∧ readSrc t (.mem (at_ .esp 4)) = some (arg t 0) ∧
    BodyIn n size s ∧ BodyIn n size t

theorem contextStart_check (n : Nat) :
    VG.Taint.check taint (workspaceTaint false) (contextStart n) (.seq (workspaceTaint false) (.block []) (oneHint false)) =
      some (zerosTaint false) :=
  exponent_check_seq taint (a := .block (setupInverse (slot n 0) 0)) (ha := .block [])
    (setupInverse_taint false (slot n 0) 0) (by rfl) (one_check false n (slot n 3))

theorem edi_eq {s t : State} {base : Addr} {size size' : Nat} (S : Scr s base size) (T : Scr t base size') :
    s.gpr .edi = t.gpr .edi :=
  BitVec.eq_of_toNat_eq (S.edi_toNat.trans T.edi_toNat.symm)

theorem prefix_relCT (n size : Nat) : RelCT isa (Pair n size) (reducePrefix n) (fun _ _ => True) := by
  unfold reducePrefix
  obtain saveCT : RelCT isa (Pair n size) (.block VG.Impl.Dsa.X86.Pow.save) (VG.X86.Taint.Agree (workspaceTaint false)) := by
    unfold VG.Impl.Dsa.X86.Pow.save
    rw [List.append_assoc]
    exact (RelCT.block_append (RelCT.seq (scratchArgument_relCT 0)
      (checkedProgramChange (σ := workspaceTaint false) (hint := .block []) rfl rfl))).mono
      (fun _ _ ⟨SP, A, R₁, R₂, _⟩ => ⟨SP, A 0 (by decide), R₁, R₂⟩) (fun _ _ h => h)
  obtain saved := saveCT.wpDep (F := fun (σ u : State) => Scr u (ws σ) size ∧ u.gpr .esp = σ.gpr .esp)
    fun s t ⟨_, _, _, _, B₁, B₂⟩ => by
      obtain go : ∀ σ, BodyIn n size σ → WP isa (.block VG.Impl.Dsa.X86.Pow.save) σ fun u =>
          Scr u (ws σ) size ∧ u.gpr .esp = σ.gpr .esp := by
        intro σ B
        obtain hz24 : 24 ≤ size := by have := B.size; simp only [contextBytes, slot, stride] at this; omega_using [this]
        exact WP.mono (Pow.save_ok B.input.entry hz24) fun u ⟨Su, _, _, Ku⟩ => ⟨Su, Ku.1 _ (by decide)⟩
      exact ⟨go s B₁, go t B₂⟩
  obtain toAgree : ∀ u₁ u₂ : State, (VG.X86.Taint.Agree (workspaceTaint false) u₁ u₂ ∧ ∃ σ₁ σ₂, Pair n size σ₁ σ₂ ∧
      (Scr u₁ (ws σ₁) size ∧ u₁.gpr .esp = σ₁.gpr .esp) ∧
      (Scr u₂ (ws σ₂) size ∧ u₂.gpr .esp = σ₂.gpr .esp)) →
      VG.X86.Taint.Agree (τr [.edi, .esp]) u₁ u₂ := by
    rintro u₁ u₂ ⟨_, σ₁, σ₂, ⟨SP, A, _⟩, ⟨S₁, E₁⟩, ⟨S₂, E₂⟩⟩
    apply agree_regs
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [show ws σ₂ = ws σ₁ by simp only [ws, A 0 (by decide)]] at S₂
      exact edi_eq S₁ S₂
    · rw [E₁, E₂, SP]
  refine RelCT.seq (saved.mono (fun _ _ h => h) toAgree) ?_
  refine RelCT.seq (checkedProgramChange (τ := τr [.edi, .esp]) (σ := workspaceTaint false) (hint := .block []) rfl rfl) ?_
  refine RelCT.seq (checkedProgramChange (σ := workspaceTaint false) (contextStart_check n) (by rfl)) ?_
  exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
    (fun _ _ h => h) (fun _ _ _ => trivial)

theorem body_relCT (n size : Nat) (hn : 0 < n) : RelCT isa (Pair n size) (reduceBody n) (fun _ _ => True) := by
  unfold reduceBody
  obtain P := (prefix_relCT n size).wpDep (F := fun (σ x : State) => Ready n (wordsVal σ.mem (ws σ) (slot n 0) n) σ x
      (ws σ) size (arg σ 2) (arg σ 3).toNat) fun s t ⟨_, _, _, _, B₁, B₂⟩ =>
    ⟨prefix_ok B₁.input B₁.size hn rfl B₁.large B₁.odd, prefix_ok B₂.input B₂.size hn rfl B₂.large B₂.odd⟩
  refine RelCT.seq (R := fun x₁ x₂ => ∃ q : Addr × Nat × Nat, contextBytes n ≤ q.2.1 ∧
      VG.Proof.Dsa.X86.StreamPair n q.2.1 q.2.2 q.1 (.mem (sc lenAt)) x₁ x₂)
    (P.mono (fun _ _ h => h) ?_) ?_
  · rintro x₁ x₂ ⟨_, σ₁, σ₂, ⟨_, A, _, _, B₁, _⟩, R₁, R₂⟩
    obtain e0 : ws σ₂ = ws σ₁ := by simp only [ws, A 0 (by decide)]
    obtain e2 : arg σ₂ 2 = arg σ₁ 2 := (A 2 (by decide)).symm
    obtain e3 : (arg σ₂ 3).toNat = (arg σ₁ 3).toNat := by rw [A 3 (by decide)]
    rw [e0, e2, e3] at R₂
    refine ⟨(ws σ₁, size, (arg σ₁ 3).toNat), B₁.size, ?_, R₁.ctx.scr, R₂.ctx.scr, R₁.lenSrc, R₂.lenSrc⟩
    apply agree_regs (rs := [.edi, .esi])
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact edi_eq R₁.ctx.scr R₂.ctx.scr
    · rw [R₁.esi, R₂.esi]
  refine RelCT.exists_ fun q => ?_
  refine RelCT.seq (R := VG.X86.Taint.Agree (workspaceTaint true)) ?_ ?_
  · intro s t tr ur sf tf ⟨hz, H⟩ E F
    exact VG.Proof.Dsa.X86.reduceStream_relCT (by exact .inr ⟨_, rfl⟩) hn hz s t tr ur sf tf H E F
  · exact (checkedProgramChange (σ := { regs := .ofList [], flags := false }) (hint := .block []) (by rfl) rfl).mono
      (fun _ _ h => taint.le_sound (show taint.le (workspaceTaint false) (workspaceTaint true) = true from rfl) h)
      (fun _ _ _ => trivial)

end VG.Proof.Dsa.X86.Red

end

end

/-! ### `Dsa.X86.RedVerified`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86.Pow (ws bytes numAt_eq8 scratch_fits)

/-- A run of the body from a state ready for it, its return address apart
from the working space. -/
theorem run {n size : Nat} (hn : 0 < n) (hn48 : n ≤ 48) {s : State} (B : BodyIn n size s)
    (ret : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨ws s, size⟩) :
    ∃ tr t, Exec isa (reduceBody n) s tr t ∧ abiPreserved s t ∧
      wordsVal t.mem (ws s) (slot n 6) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) %
          wordsVal s.mem (ws s) (slot n 0) n ∧
      Outs (ws s) (VG.Impl.Dsa.X86.Pow.scratch n) s.mem t.mem := by
  obtain ⟨tr, t, E, V, O, R, _, _⟩ := body_ok B.input B.size hn hn48 rfl B.large B.odd
  have F : Frame [⟨ws s, size⟩] s.mem t.mem := by
    intro x hx
    have H := hx _ (List.mem_cons_self ..)
    refine O x (fun r hr => ?_)
    have Bd := scratch_fits B.size r hr
    simp only [Region.Contains, ofs] at H ⊢
    omega_using [H, Bd]
  refine ⟨tr, t, E, ⟨R, ?_⟩, V, O⟩
  exact F.readW (by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((s.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      exact ret) (by decide)

end VG.Proof.Dsa.X86.Red

end

end


/-! # Calls of the IA-32 DSA reduction

The caller passes the working space, its length, and the bytes' address and
length (`esi`, `ebx`) as cdecl's four stack arguments (`reduceCall`). -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Red
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Impl.Dsa.X86.Arith
open VG.Proof.Dsa.X86 (StreamInput callStack)
open VG.Proof.Dsa.X86.Pow (ws bytes)

abbrev pushes : List Reg := [.ebx, .esi, .eax, .edi]

/-- The callee's argument `i`, `16 - 4 i` bytes below the caller's `esp`. -/
theorem argAddr_entry (s : State) (i : Nat) (hi : i < 4) :
    argAddr (pushed pushes s).callEntry i = (s.gpr .esp - BitVec.ofNat 32 (16 - 4 * i)).setWidth 64 := by
  unfold argAddr
  rw [callEntry_esp']
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, List.length_cons, List.length_nil]
  have := (s.gpr .esp).isLt
  omega_using [hi]

/-- What the caller provides for a reduction of the `len` bytes at `p`, with
the modulus `m` in slot 0. -/
structure CallIn (n m : Nat) (s : State) (base : Addr) (size : Nat) (p : BitVec 32) (len : Nat) : Prop where
  scr : Scr s base size
  room : Pow.Room (s.gpr .esp) base size
  context : contextBytes n ≤ size
  modulus : wordsVal s.mem base (slot n 0) n = m
  large : 255 < m
  odd : m % 2 = 1
  esi : s.gpr .esi = p
  ebx : s.gpr .ebx = BitVec.ofNat 32 len
  lenFit : len < 2 ^ 32
  input : StreamInput s base (contextBytes n) p len
  stack : Region.Disjoint ⟨p.setWidth 64, len⟩ (callStack (s.gpr .esp))

theorem CallIn.sp {n m : Nat} {s : State} {base : Addr} {size : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) : 108 ≤ (s.gpr .esp).toNat := C.room.1

/-- The memory of the callee's entry is the caller's but for the 20 bytes
below `esp`. -/
theorem entry_frame (s : State) (h : 20 ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) 20] s.mem (pushed pushes s).callEntry.mem :=
  callEntry_frame (rs := pushes) (by simp; omega_using [h]) (by decide)

/-- Below `esp` within the call's stack, apart from the working space. -/
theorem below_apart {sp : BitVec 32} {base : Addr} {size k : Nat} (room : Pow.Room sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) (hk : k ≤ 108) {sz : Nat} (hsz : sz ≤ size) {x : Addr}
    (hx : (below sp k).Contains x 1) : ¬ (⟨base, sz⟩ : Region).Contains x 1 := by
  have := Pow.zone_ofs' room hn hk hx
  simp only [Region.Contains, ofs] at this ⊢
  omega_using [hsz, this]

theorem frame_val32 {sp : BitVec 32} {base : Addr} {size : Nat}
    (H : Pow.Room sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {m m' : Mem} (F : Frame [below sp 20] m m') {d k : Nat} (hd : d + 4 * k ≤ size) :
    val32 m' base d k = val32 m base d k := by
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => F _ fun r hr hc => ?_)
  rw [List.mem_singleton.mp hr] at hc
  have := Pow.zone_ofs' H hn (by decide) hc
  rw [ofs_off base (by omega_using [hn, hd, hj, hi])] at this
  omega_using [hd, hj, hi, this]

theorem entry_bodyIn {n m : Nat} {s : State} {base : Addr} {size sz : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) (hsz : contextBytes n ≤ sz) (hsz' : sz ≤ size)
    {rd wr : List Region} (hargs : below (s.gpr .esp) 16 ∈ rd ++ wr)
    (hdata : InRegions (rd ++ wr) (p.setWidth 64) len) (hws : (⟨base, sz⟩ : Region) ∈ wr) :
    BodyIn n sz ((pushed pushes s).callEntry.withRegions rd wr) := by
  have hsp := C.sp
  have nw := C.scr.nowrap
  have lf := C.lenFit
  have fit : 4 * pushes.length + 4 ≤ (s.gpr .esp).toNat := by simp; omega_using [hsp]
  have a0 : arg ((pushed pushes s).callEntry.withRegions rd wr) 0 = s.gpr .edi :=
    callEntry_arg fit (by decide) (by decide)
  have a2 : arg ((pushed pushes s).callEntry.withRegions rd wr) 2 = p :=
    (callEntry_arg fit (by decide) (by decide)).trans C.esi
  have a3 : arg ((pushed pushes s).callEntry.withRegions rd wr) 3 = BitVec.ofNat 32 len :=
    (callEntry_arg fit (by decide) (by decide)).trans C.ebx
  have hws' : ws ((pushed pushes s).callEntry.withRegions rd wr) = base := by
    simp only [ws, a0]; exact C.scr.edi
  have argIn (i : Nat) (hi : i < 4) :
      InRegions (((pushed pushes s).callEntry.withRegions rd wr).rd ++
        ((pushed pushes s).callEntry.withRegions rd wr).wr)
        (argAddr ((pushed pushes s).callEntry.withRegions rd wr) i) 4 := by
    refine ⟨_, hargs, ?_⟩
    rw [argAddr_withRegions, argAddr_entry s i hi]
    exact below_top (by omega_using []) (by omega_using [hsp]) (by omega_using [hi])
  have argApart (i : Nat) (hi : i < 4) :
      Region.Disjoint ⟨argAddr ((pushed pushes s).callEntry.withRegions rd wr) i, 4⟩ ⟨base, sz⟩ := by
    rw [argAddr_withRegions, argAddr_entry s i hi]
    intro x h₁ h₂
    have top : (below (s.gpr .esp) 16).Contains ((s.gpr .esp - BitVec.ofNat 32 (16 - 4 * i)).setWidth 64) 4 :=
      below_top (by omega_using []) (by omega_using [hsp]) (by omega_using [hi])
    have inner := Region.Contains.byte top (by simp only [Region.Contains] at h₁; exact Nat.lt_of_succ_le h₁)
    exact below_apart C.room nw (by decide : 16 ≤ 108) hsz' inner h₂
  have M : wordsVal ((pushed pushes s).callEntry.withRegions rd wr).mem base (slot n 0) n =
      wordsVal s.mem base (slot n 0) n := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    exact frame_val32 C.room nw (entry_frame s (by omega_using [hsp]))
      (by have := C.context; simp only [contextBytes, slot, stride] at this ⊢; omega_using [this])
  refine ⟨?_, hsz, ?_, ?_⟩
  · rw [hws', a2, a3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt C.lenFit]
    refine ⟨⟨argIn 0 (by decide), by rw [a0]; exact C.scr.edi, hws, by omega_using [hsz', nw], ?_⟩, argIn 2 (by decide),
      argIn 3 (by decide), argApart 2 (by decide), argApart 3 (by decide), a2, a3, C.lenFit,
      ⟨C.input.fit, fun i hi => by
        obtain ⟨r, hr, hc⟩ := hdata
        exact ⟨r, hr, Region.Contains.byte hc (by rw [Mem.sub_ofNat_toNat _ (by omega_using [lf, hi])]; exact hi)⟩,
        C.input.far, hdata⟩⟩
    show StkOk ((pushed pushes s).callEntry.gpr .esp) base sz
    have R := C.room
    unfold StkOk Pow.Room at *
    rw [callEntry_espNat fit]
    simp only [List.length_cons, List.length_nil]
    omega_using [hsz', R]
  · rw [hws', M, C.modulus]; exact C.large
  · rw [hws', M, C.modulus]; exact C.odd

theorem body_noSp (n : Nat) : NoSp (reduceBody n) := NoSp.of_all rfl

theorem body_stackUse (n : Nat) : stackUse (reduceBody n) = 0 := rfl

theorem CallIn.eax {n m : Nat} {s t : State} {base : Addr} {size : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) (K : Keeps [.eax] s t) (M : t.mem = s.mem) :
    CallIn n m t base size p len := by
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  refine ⟨C.scr.of_keeps K (by decide), by rw [esp]; exact C.room, C.context, by rw [M]; exact C.modulus,
    C.large, C.odd, by rw [K.1 _ (by decide)]; exact C.esi, by rw [K.1 _ (by decide)]; exact C.ebx, C.lenFit,
    ⟨C.input.fit, by rw [K.2.1, K.2.2]; exact C.input.read, C.input.far, by rw [K.2.1, K.2.2]; exact C.input.whole⟩,
    by rw [esp]; exact C.stack⟩

theorem call_ok {n m : Nat} {s : State} {base : Addr} {size : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) (hused : VG.Impl.Dsa.Layout.usedBytes ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) :
    WP isa (reduceCall n) s fun t =>
      wordsVal t.mem base (slot n 6) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len) % m ∧
      StackOuts base (s.gpr .esp) (VG.Impl.Dsa.X86.Pow.scratch n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have hsp := C.sp
  have nw := C.scr.nowrap
  have cb := C.context
  have cb8 : contextBytes n / 8 * 8 = contextBytes n := by simp only [contextBytes, slot, stride]; omega_using []
  unfold reduceCall
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have Cu := C.eax U.keeps U.mem
  have usp : u.gpr .esp = s.gpr .esp := U.other _ (by decide)
  have hu : 108 ≤ (u.gpr .esp).toNat := by rw [usp]; exact hsp
  have fit : 4 * pushes.length + 4 ≤ (u.gpr .esp).toNat := by rw [usp]; simp; omega_using [hsp]
  let rd : List Region := [⟨p.setWidth 64, len⟩, below (u.gpr .esp) 16]
  let wr : List Region := [⟨base, contextBytes n⟩]
  let v := (pushed pushes u).callEntry.withRegions rd wr
  have Bv : BodyIn n (contextBytes n) v :=
    entry_bodyIn Cu (Nat.le_refl _) cb (by simp [rd]) ⟨⟨p.setWidth 64, len⟩, by simp [rd], by simp [Region.Contains]⟩ (by simp [wr])
  have a0 : ws v = base := by
    simp only [ws]
    rw [show arg v 0 = u.gpr .edi from callEntry_arg fit (by decide) (by decide)]
    exact Cu.scr.edi
  have vsp : (v.gpr .esp).toNat = (u.gpr .esp).toNat - 20 := callEntry_espNat fit
  let K : Contract isa :=
    { pre := fun w => BodyIn n (contextBytes n) w ∧ ws w = base ∧
        Region.Disjoint ⟨(w.gpr .esp).setWidth 64, 4⟩ ⟨base, contextBytes n⟩
      post := fun w w' => wordsVal w'.mem base (slot n 6) n =
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt w.mem ((arg w 2).setWidth 64) (arg w 3).toNat) %
            wordsVal w.mem base (slot n 0) n ∧
        Outs base (VG.Impl.Dsa.X86.Pow.scratch n) w.mem w'.mem
      pub := fun _ _ => True }
  have ret : Region.Disjoint ⟨(v.gpr .esp).setWidth 64, 4⟩ ⟨base, contextBytes n⟩ := by
    intro x h₁ h₂
    have e : (v.gpr .esp) = u.gpr .esp - BitVec.ofNat 32 20 := by
      apply BitVec.eq_of_toNat_eq; rw [vsp, BitVec.toNat_sub, BitVec.toNat_ofNat]; have := (u.gpr .esp).isLt; omega_using [hu]
    rw [e] at h₁
    have top : (below (u.gpr .esp) 20).Contains ((u.gpr .esp - BitVec.ofNat 32 20).setWidth 64) 4 :=
      below_top (by omega_using []) (by omega_using [hu]) (by omega_using [])
    exact below_apart Cu.room nw (by decide : 20 ≤ 108) cb
      (Region.Contains.byte top (by simp only [Region.Contains] at h₁; exact Nat.lt_of_succ_le h₁)) h₂
  refine WP.callWith (k := K) (fun w ⟨B, W, R⟩ => ?_) (body_noSp n) (by decide) (by decide)
    (by rw [body_stackUse]; simp; omega_using [hu]) (rd := rd) (wr := wr) ⟨⟨Bv, a0, ret⟩, ?_, ?_⟩ ?_
  · rw [← W] at R
    obtain ⟨tr, t, E, A, V, O⟩ := run hn hn48 B R
    rw [W] at V O
    exact ⟨tr, t, E, A, V, O⟩
  · refine Covers.append_left (Covers.cons ?_ (Covers.cons ?_ Covers.nil)) (Covers.cons ?_ Covers.nil)
    · exact (Covers.one Cu.input.whole).trans (Covers.append (Covers.refl _)
        (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr))
    · exact Covers.of_mem fun r hr => by
        rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact (Covers.one (rs := u.wr) ⟨⟨base, size⟩, Cu.scr.wr, by simp [Region.Contains]; omega_using [cb]⟩).trans
        (Covers.of_mem fun r hr => List.mem_append_right _ (List.mem_cons_of_mem _ hr))
  · refine (Covers.one (rs := u.wr) ⟨⟨base, size⟩, Cu.scr.wr, by simp [Region.Contains]; omega_using [cb]⟩).trans
      (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
  · intro w rdw wrw cs F ⟨w₂, mem, V, O⟩
    rw [body_stackUse] at F
    have Fe : Frame [below (u.gpr .esp) 20] u.mem v.mem := entry_frame u (by omega_using [hu])
    have a2 : arg v 2 = p := (callEntry_arg fit (by decide) (by decide)).trans Cu.esi
    have a3 : (arg v 3).toNat = len := by
      rw [show arg v 3 = u.gpr .ebx from callEntry_arg fit (by decide) (by decide), Cu.ebx, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt Cu.lenFit]
    have Mv : wordsVal v.mem base (slot n 0) n = m := by
      rw [wordsVal_eq_val32, frame_val32 Cu.room nw Fe
        (by simp only [contextBytes, slot, stride] at cb ⊢; omega_using [cb]), ← wordsVal_eq_val32, Cu.modulus]
    have inStack {x : Addr} (hx : (below (u.gpr .esp) 20).Contains x 1) : (callStack (s.gpr .esp)).Contains x 1 := by
      rw [← usp]; exact below_sub (by decide) hu _ hx
    have Bv : Spec.Rsa.bytesAt v.mem (p.setWidth 64) len = Spec.Rsa.bytesAt s.mem (p.setWidth 64) len := by
      unfold Spec.Rsa.bytesAt
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      rw [← U.mem]
      refine Fe _ fun r hr hc => ?_
      rw [List.mem_singleton.mp hr] at hc
      exact C.stack _ (Offset.contains_base _ (by omega_using [hi']) (by have := C.lenFit; omega_using [a3, hi'])) (inStack hc)
    refine ⟨?_, ?_, ?_⟩
    · rw [← mem, V, a2, a3, Bv, Mv]
    · intro x hx hs
      rw [← U.mem]
      by_cases hin : (⟨base, contextBytes n⟩ : Region).Contains x 1
      · rw [← mem, O x hx]
        refine Fe x fun r hr hc => ?_
        rw [List.mem_singleton.mp hr] at hc
        exact below_apart Cu.room nw (by decide : 20 ≤ 108) cb hc hin
      · by_cases hb : (below (u.gpr .esp) 20).Contains x 1
        · exfalso
          have hz := Pow.zone_ofs' Cu.room nw (by decide : 20 ≤ 108) hb
          rcases hs with lo | hs
          · omega_using [hused, hn, hn48, hsp, nw, cb, cb8, usp, hu, fit, vsp, V, a2, a3, Mv, hz, lo]
          · exact hs (inStack hb)
        · refine F x fun r hr => ?_
          simp only [wr, List.mem_append, List.mem_singleton, List.length_cons, List.length_nil] at hr
          rcases hr with rfl | rfl
          · exact hin
          · exact hb
    · refine ⟨fun r hr => ?_, rdw.trans U.rd, wrw.trans U.wr⟩
      have cr : r ∈ calleeSaved := by revert hr; cases r <;> decide
      rw [cs r cr, U.other r (by revert hr; cases r <;> decide)]

theorem body_readArg {n : Nat} {s t : State} {tr : List Leak}
    (E : Exec isa (reduceBody n) s tr t) :
    readSrc s (.mem (at_ .esp 4)) = some (arg s 0) := by
  change s.load32 (argAddr s 0) = some (arg s 0)
  unfold State.load32
  split
  · rfl
  · rename_i h
    cases E with
    | seq E _ =>
      cases E with
      | seq E _ =>
        cases E with
        | block H =>
          simp only [VG.Impl.Dsa.X86.Pow.save, VG.Impl.Dsa.X86.Pow.slots, List.map_cons, List.map_nil,
            List.cons_append, List.nil_append, execBlock, isa, exec, readSrc, State.load32] at H
          simp only [show s.ea (at_ .esp 4) = argAddr s 0 from rfl, h, ↓reduceIte, Option.map_none] at H
          cases H

/-- Two runs about to call the reduction with the same public arguments. -/
def CallPair (n : Nat) (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ r ∈ pushes, s.gpr r = t.gpr r) ∧
    ∃ base size m₁ m₂ p len, CallIn n m₁ s base size p len ∧ CallIn n m₂ t base size p len

theorem entry_self {n m : Nat} {s : State} {base : Addr} {size : Nat} {p : BitVec 32} {len : Nat}
    (C : CallIn n m s base size p len) : BodyIn n size (pushed pushes s).callEntry := by
  have B := entry_bodyIn C C.context (Nat.le_refl _) (rd := (pushed pushes s).callEntry.rd)
    (wr := (pushed pushes s).callEntry.wr)
    (by simp only [State.callEntry_rd, State.callEntry_wr, pushed_rd, pushed_wr]; simp)
    (by
      obtain ⟨r, hr, hc⟩ := C.input.whole
      refine ⟨r, ?_, hc⟩
      simp only [State.callEntry_rd, State.callEntry_wr, pushed_rd, pushed_wr, List.mem_append,
        List.mem_cons] at hr ⊢
      rcases hr with h | h
      · exact .inl h
      · exact .inr (.inr h))
    (by simp only [State.callEntry_wr, pushed_wr]; exact List.mem_cons_of_mem _ C.scr.wr)
  exact B

theorem framed_relCT (n : Nat) (hn : 0 < n) :
    RelCT isa (CallPair n) (.frame (.push pushes) (.call (reduceName n) (reduceBody n)) (.pop .eax 4))
      (fun _ _ => True) := by
  refine RelCT.frame (R := fun _ _ => True) (fun _ _ H => H.1) ?_
  rintro _ _ tr ur sf tf ⟨s, t, ⟨SP, RG, base, size, m₁, m₂, p, len, C₁, C₂⟩, rfl, rfl⟩ E F
  have fit : 4 * pushes.length + 4 ≤ (s.gpr .esp).toNat := by have := C₁.sp; simp; omega_using [this]
  cases E with
  | call C E R =>
    cases F with
    | call D F S =>
      rw [call_callEntry, Option.some.injEq] at C D
      subst C D
      have sp : (pushed pushes s).callEntry.gpr .esp = (pushed pushes t).callEntry.gpr .esp := by
        rw [callEntry_esp', callEntry_esp', SP]
      have args : ∀ i < 4, arg (pushed pushes s).callEntry i = arg (pushed pushes t).callEntry i :=
        fun i hi => callEntry_arg_eq (by decide) fit SP RG hi
      have traces := (body_relCT n size hn) _ _ _ _ _ _
        ⟨sp, args, body_readArg E, body_readArg F, entry_self C₁, entry_self C₂⟩ E F
      have r := (ret_gpr R .esp).1
      have q := (ret_gpr S .esp).1
      refine ⟨?_, trivial⟩
      simp only [r, q, State.callEntry_esp, pushed_esp, SP, traces.1]

/-- Two runs about to reduce: the same public stack pointer, working space and
bytes. -/
def CallReady (n : Nat) (s t : State) : Prop :=
  s.gpr .esp = t.gpr .esp ∧ (∀ r ∈ [Reg.ebx, .esi, .edi], s.gpr r = t.gpr r) ∧
    ∃ base size m₁ m₂ p len, VG.Impl.Dsa.Layout.usedBytes ≤ size ∧
      CallIn n m₁ s base size p len ∧ CallIn n m₂ t base size p len

theorem call_relCT (n : Nat) (hn : 0 < n) :
    RelCT isa (CallReady n) (reduceCall n) (fun _ _ => True) := by
  unfold reduceCall
  refine RelCT.seq ?_ (framed_relCT n hn)
  intro s t tr ur sf tf ⟨SP, RG, base, size, m₁, m₂, p, len, _, C₁, C₂⟩ E F
  have W (s : State) : WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (contextBytes n / 8)))]) s
      (fun t => Keeps [.eax] s t ∧ t.mem = s.mem ∧ t.gpr .eax = BitVec.ofNat 32 (contextBytes n / 8)) :=
    wp_movS rfl fun _ U _ => WP.block_nil ⟨U.keeps, U.mem, U.gpr⟩
  have K := VG.Proof.Dsa.X86.wp_result (W s) E
  have L := VG.Proof.Dsa.X86.wp_result (W t) F
  refine ⟨?_, ?_⟩
  · cases E with
    | block E => cases F with
      | block F =>
        simp only [execBlock, isa, exec, readSrc, Option.map_some, addrs, srcAddrs, List.map_nil,
          List.nil_append, Option.some.injEq, Prod.mk.injEq] at E F
        exact E.2.symm.trans F.2
  · refine ⟨by rw [K.1.1 .esp (by decide), L.1.1 .esp (by decide)]; exact SP, fun r hr => ?_,
      base, size, m₁, m₂, p, len, C₁.eax K.1 K.2.1, C₂.eax L.1 L.2.1⟩
    simp only [pushes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [K.1.1 _ (by decide), L.1.1 _ (by decide)]; exact RG _ (by simp)
    · rw [K.1.1 _ (by decide), L.1.1 _ (by decide)]; exact RG _ (by simp)
    · rw [K.2.2, L.2.2]
    · rw [K.1.1 _ (by decide), L.1.1 _ (by decide)]; exact RG _ (by simp)

end VG.Proof.Dsa.X86.Red

end

end

/-! # Complete big-endian reduction call -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- `src` reads the public length `len` in every state that differs from
`s` only in the arithmetic context. -/
def LenOperand (base : Addr) (size n : Nat) (s : State) (src : Src) (len : Nat) : Prop :=
  ∀ t : State, Scr t base size → t.rd = s.rd → t.wr = s.wr → Outside base 0 (contextBytes n) s.mem t.mem →
    readSrc t src = some (BitVec.ofNat 32 len)

theorem LenOperand.imm (base : Addr) (size n : Nat) (s : State) (len : Nat) :
    LenOperand base size n s (.imm (BitVec.ofNat 32 len)) len := fun _ _ _ _ _ => rfl

/-- The saved digest-prefix length, as `Core.digestPrefix` reads it. -/
theorem LenOperand.prefix {base : Addr} {size n len : Nat} {s : State}
    (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (hn : n ≤ 48)
    (h : pointerValue base s (.input .digestPrefixLen) = BitVec.ofNat 32 len) :
    LenOperand base size n s Core.digestPrefix len := by
  intro t ht _ _ O
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn
  have hs : 8256 ≤ size := hz
  show readSrc t (.mem (VG.Impl.Mont.X86.sc (VG.Impl.Dsa.X86.Layout.field .digestPrefixLen))) = _
  rw [readSrc_sc ht (by change 8244 ≤ size; omega_using [hs])]
  congr 1
  rw [← h]
  apply BitVec.eq_of_toNat_eq
  have f : VG.Impl.Dsa.X86.Layout.field .digestPrefixLen = 8240 := rfl
  rw [f] at *
  exact O.w32 (.inr (by omega_using [cb])) (by omega_using [])

/-- The modulus into slot 0, and the bytes' address and length into `esi` and
`ebx`: the state `Red.call_ok` reduces from. -/
theorem reduceHead_ok {s : State} {base : Addr} {size len inputLen n m : Nat} {input : Pointer}
    {src : Src} (hsrc : LenOperand base size n s src inputLen)
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ri : StreamInput s base (contextBytes n) (pointerValue base s input) inputLen)
    (Rs : Region.Disjoint ⟨(pointerValue base s input).setWidth 64, inputLen⟩ (callStack (s.gpr .esp)))
    (hi : inputLen < 2 ^ 32)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm255 : 255 < m) (hodd : m % 2 = 1) :
    WP isa (.seq (Core.load n len (slot n 0) (.input .q))
      (.block (Core.pointer input ++ ([.mov .ebx src] : List Instr)))) s
      fun w => Red.CallIn n m w base size (pointerValue base s input) inputLen ∧
        Outside base 0 (contextBytes n) s.mem w.mem ∧ Keeps powerClob s w := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have hl : len ≤ 8 * n := by omega_using [hn]
  have hz' : 8256 ≤ size := hz
  have cb : contextBytes n ≤ 8192 := Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [H]
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega_using [hz', cb, this]
  refine WP.seq (WP.mono (coreLoad_ok hs hz (bounds 0 (by decide)) h4 hl hw4 Rq.toReadableComponent
    (Rq.slot (by decide))) fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have Ou' : Outside base 0 (contextBytes n) s.mem u.mem :=
    Ou.mono (by omega_using []) (by have := bound 0 (by decide); omega_using [this])
  have Su : Scr u base size := hs.of_keeps Ku (by decide)
  have Pu := pointerValue_keep Ku (by decide) Ou' cb input
  refine WP.block_append (WP.mono (pointer_ok Su hz input) fun v ⟨Pv, Kv, Mv⟩ => ?_)
  have Sv : Scr v base size := Su.of_keeps Kv (by decide)
  have Ov : Outside base 0 (contextBytes n) s.mem v.mem := by rw [Mv]; exact Ou'
  refine wp_movS (hsrc v Sv (by rw [Kv.2.1, Ku.2.1]) (by rw [Kv.2.2, Ku.2.2]) Ov) fun w W _ => WP.block_nil ?_
  have Kuw : Keeps [.esi, .ebx] u w := (Kv.mono (by decide)).trans (W.keeps.mono (by decide))
  have Ksw : Keeps powerClob s w := (Ku.mono (by decide)).trans (Kuw.mono (by decide))
  have Mw : w.mem = u.mem := W.mem.trans Mv
  refine ⟨{ scr := Su.of_keeps Kuw (by decide)
            room := by rw [Ksw.1 _ (by decide)]; exact room
            context := by omega_using [hz', cb]
            modulus := by rw [Mw, Vu, hm]
            large := hm255
            odd := hodd
            esi := by rw [W.other _ (by decide), Pv, Pu]
            ebx := W.gpr
            lenFit := hi
            input := Ri.keep Ksw
            stack := by rw [Ksw.1 _ (by decide)]; exact Rs }, by rw [Mw]; exact Ou', Ksw⟩

theorem coreReduce_ok {s : State} {base : Addr} {size len inputLen n m output : Nat} {input : Pointer}
    {src : Src} (hsrc : LenOperand base size n s src inputLen)
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ri : StreamInput s base (contextBytes n) (pointerValue base s input) inputLen)
    (Rs : Region.Disjoint ⟨(pointerValue base s input).setWidth 64, inputLen⟩ (callStack (s.gpr .esp)))
    (hi : inputLen < 2 ^ 32)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm255 : 255 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.reduce len src input output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s input).setWidth 64) inputLen) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have hl : len ≤ 8 * n := by omega_using [hn]
  have hz' : 8256 ≤ size := hz
  have cb : contextBytes n ≤ 8192 := Nat.le_trans (VG.Proof.Dsa.X86.Layout.context_bound hn48) (by decide)
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [H]
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega_using [hz, hused, hn, h4, hmax, hw4, ho, hfar, hn48, hl, hz', cb, this]
  unfold Core.reduce
  dsimp only
  rw [← hn]
  apply WP.assoc
  refine WP.seq (WP.mono (reduceHead_ok hsrc hs hz room hn h4 hmax hw4 Rq Ri Rs hi hm hm255 hodd)
    fun w ⟨C, Ow, Ksw⟩ => ?_)
  refine WP.seq (WP.mono (Red.call_ok C hused (by omega_using [hn, h4]) hn48) fun x ⟨Vx, Ox, Kx⟩ => ?_)
  refine WP.mono (coreStore_ok (C.scr.of_keeps Kx (by decide)) hz hn.symm (bounds 6 (by decide)) h4 hl hw4 ho
    (by have := bound 6 (by decide); omega_using [hfar, this])) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vx, Ri.bytes Ow], ?_, ?_⟩
  · rw [Ksw.1 _ (by decide)] at Ox
    have Of : StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] w.mem x.mem :=
      Ox.mono fun r hr => ⟨(0, contextBytes n), by simp, by omega_using [],
        by simpa only [Nat.zero_add] using Pow.scratch_fits (Nat.le_refl _) r hr⟩
    exact ((StackOuts.of_outs (Outs.of_outside Ow (by simp))).trans Of).trans
      (StackOuts.of_outs (Outs.of_outside Ot (by simp)))
  · exact (Ksw.trans (Kx.mono (by decide))).trans (Kt.mono (by decide))

end VG.Proof.Dsa.X86

end

end

/-! ### `Dsa.X86.CoreProduct`, which only this module used -/

section

/-! # Complete ordinary modular product call, including byte I/O

The modulus and both operands are loaded into the context's slots 0, 5 and
8, the width's shared product (`vg_dsa_mulmod_{n}`, `Mul.call_ok`) leaves
their product in slot 6, and it is stored as bytes. -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- The modulus and both operands, at full width, into slots 0, 5 and 8. -/
theorem coreLoadProduct_ok {s : State} {base : Addr} {size len n m : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (contextRoom : contextBytes n ≤ size) :
    WP isa (Core.loadPower n len len modulus a b) s fun t =>
      wordsVal t.mem base (slot n 0) n = m ∧
      wordsVal t.mem base (slot n 5) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) ∧
      wordsVal t.mem base (slot n 8) n =
        Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) ∧
      Outside base 0 (contextBytes n) s.mem t.mem ∧ Keeps loadClob s t := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hl : len ≤ 8 * n := by omega_using [hn]
  have nw := hs.nowrap
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [H]
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega_using [contextRoom, this]
  unfold Core.loadPower
  refine WP.seq (WP.mono (coreLoad_ok hs hz (bounds 0 (by decide)) h4 hl hw4
    Rq.toReadableComponent (Rq.slot (by decide))) fun u ⟨Mu, Ku, Ou⟩ => ?_)
  have Ou' := slotOutside_whole Ou (by decide)
  have Rau := Ra.keep Ku (by decide) Ou' hn48
  have Rbu := Rb.keep Ku (by decide) Ou' hn48
  refine WP.seq (WP.mono (coreLoad_ok (hs.of_keeps Ku (by decide)) hz
    (bounds 5 (by decide)) h4 hl hw4 Rau.toReadableComponent (Rau.slot (by decide)))
    fun v ⟨Av, Kv, Ov⟩ => ?_)
  have Ov' := slotOutside_whole Ov (by decide)
  have Rbv := Rbu.keep Kv (by decide) Ov' hn48
  have Ksv := Ku.trans Kv
  have Osv := Ou'.trans Ov'
  refine WP.mono (coreLoad_ok (hs.of_keeps Ksv (by decide)) hz (bounds 8 (by decide))
    h4 hl hw4 Rbv.toReadableComponent (Rbv.slot (by decide))) fun w ⟨Bw, Kw, Ow⟩ => ?_
  refine ⟨?_, ?_, ?_, Osv.trans (slotOutside_whole Ow (by decide)), Ksv.trans Kw⟩
  · rw [slotOutside_val Ow (by decide) (by have := bounds 0 (by decide); omega_using [nw, this]),
      slotOutside_val Ov (by decide) (by have := bounds 0 (by decide); omega_using [nw, this]), Mu, hm]
  · rw [slotOutside_val Ow (by decide) (by have := bounds 5 (by decide); omega_using [nw, this]), Av,
      Ra.bytes Ku (by decide) Ou' hn48]
  · rw [Bw, Rb.bytes Ksv (by decide) Osv hn48]

theorem coreProductMod_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer} {modulus : Field}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input modulus) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input modulus)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.productMod len modulus a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) *
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega_using [hn, hmax]
  have cb := VG.Proof.Dsa.X86.Layout.context_bound hn48
  have hl : len ≤ 8 * n := by omega_using [hn]
  have bound (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ contextBytes n := by
    have H := slot_bound (n := n) hj
    simp only [stride] at H
    omega_using [H]
  have bounds (j : Nat) (hj : j < 9) : slot n j + 8 * n ≤ size := by have := bound j hj; omega_using [ho, hfar, this]
  unfold Core.productMod
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreLoadProduct_ok hs hz hn h4 hmax hw4 Rq Ra Rb hm (by omega_using [ho, hfar]))
    fun w ⟨Mw, Aw, Bw, Opre, Ksw⟩ => ?_)
  have Wscr := hs.of_keeps Ksw (by decide)
  refine WP.seq (WP.mono (Mul.call_ok Wscr (by rw [Ksw.1 _ (by decide)]; exact room)
    (by omega_using [ho, hfar]) hused (by omega_using [hn, h4]) hn48 Mw hm1 hodd) fun v ⟨Vv, Ov, Kv⟩ => ?_)
  refine WP.mono (coreStore_ok (Wscr.of_keeps Kv (by decide)) hz hn.symm
    (bounds 6 (by decide)) h4 hl hw4 ho (by have := bound 6 (by decide); omega_using [hfar, this])) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vv, Aw, Bw], ?_, ?_⟩
  · rw [Ksw.1 _ (by decide)] at Ov
    have Of : StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] w.mem v.mem :=
      Ov.mono fun r hr => ⟨(0, contextBytes n), by simp, by omega_using [],
        by simpa only [Nat.zero_add] using Pow.scratch_fits (Nat.le_refl _) r hr⟩
    exact ((StackOuts.of_outs (Outs.of_outside Opre (by simp))).trans Of).trans
      (StackOuts.of_outs (Outs.of_outside Ot (by simp)))
  · exact ((Ksw.mono (by decide)).trans (Kv.mono (by decide))).trans (Kt.mono (by decide))

theorem coreProduct_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (room : Pow.Room (s.gpr .esp) base size) (hused : usedBytes ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.product len a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) *
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) % m) ∧
      StackOuts base (s.gpr .esp) [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t :=
  coreProductMod_ok hs hz room hused hn h4 hmax hw4 Rq Ra Rb hm hm1 hodd ho hfar

end VG.Proof.Dsa.X86

end

end

/-! # Scalar arithmetic stages preserve validated caller parameters -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86/CoreSum.lean`, which only this module imported.
section

/-! # Complete reduced modular addition call, including byte I/O -/

section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem coreSum_ok {s : State} {base : Addr} {size len n m output : Nat} {a b : Pointer}
    (hs : Scr s base size) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size)
    (hn : n = (len + 7) / 8) (h4 : 4 ≤ len) (hmax : len ≤ 384) (hw4 : len % 4 = 0)
    (Rq : OperandReady s base n (.input .q) len)
    (Ra : OperandReady s base n a len) (Rb : OperandReady s base n b len)
    (hm : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s (.input .q)).setWidth 64) len) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1)
    (ha : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) < m)
    (hb : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len) < m)
    (ho : output + len ≤ size) (hfar : contextBytes n ≤ output) :
    WP isa (Core.sum len a b output) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base output) len = Spec.Dsa.encodeBE len
        ((Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s a).setWidth 64) len) +
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem ((pointerValue base s b).setWidth 64) len)) % m) ∧
      Outs base [(0, contextBytes n), (output, len)] s.mem t.mem ∧ Keeps powerClob s t := by
  have hn48 : n ≤ 48 := by omega
  have hl : len ≤ 8 * n := by omega
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  simp only [stride] at b6
  unfold Core.sum
  dsimp only
  rw [← hn]
  refine WP.seq (WP.mono (coreSetup_ok hs hz hn h4 hmax hw4 Rq.toReadableComponent (Rq.slot (by decide)) hm hm1 hodd)
    fun u ⟨Cu, _, _, Ou, Ku⟩ => ?_)
  have Rau := Ra.keep Ku (by decide) Ou hn48
  have Rbu := Rb.keep Ku (by decide) Ou hn48
  refine WP.seq (WP.mono (coreInputs_ok Cu hz hn48 h4 hl h4 hl hw4 hw4 Rau Rbu)
    fun v ⟨Cv, Av, Bv, _, Ov, Kv⟩ => ?_)
  rw [Ra.bytes Ku (by decide) Ou hn48] at Av
  rw [Rb.bytes Ku (by decide) Ou hn48] at Bv
  refine WP.seq (WP.mono (ordinaryAdd_ok Cv (by rw [Av]; exact ha) (by rw [Bv]; exact hb)) fun w ⟨Cw, Kw, Vw⟩ => ?_)
  have bw : slot n 6 + 8 * n ≤ size := Nat.le_trans (by omega) Cw.size_le
  refine WP.mono (coreStore_ok Cw.scr hz hn.symm bw h4 hl hw4 ho (by omega)) fun t ⟨Vt, Kt, Ot⟩ => ?_
  refine ⟨by rw [Vt, Vw, Av, Bv], ?_, ?_⟩
  · have Opre := (Ou.trans Ov).trans (resultKeep_whole Kw)
    exact (Outs.of_outside Opre (by simp)).trans (Outs.of_outside Ot (by simp))
  · exact (((Ku.trans (Kv.mono (by decide))).trans ((OpKeep.keeps Kw).mono (by decide))).trans (Kt.mono (by decide)))

end VG.Proof.Dsa.X86
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem stageProduct_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((qLen + 7) / 8) a qLen) (Rb : OperandReady s base ((qLen + 7) / 8) b qLen)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.product qLen a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output qLen (operandValue s base a qLen * operandValue s base b qLen % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreProduct_ok M.scr M.saved M.room M.extent rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.qReady Ra Rb M.qValue
    (by have := M.qLarge; omega_using [this]) M.qOdd (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (operandValue s base a qLen * operandValue s base b qLen % q) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageProductP_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((pLen + 7) / 8) a pLen) (Rb : OperandReady s base ((pLen + 7) / 8) b pLen)
    (ho : r ≤ output) (hb : output + pLen ≤ usedBytes) :
    WP isa (Core.productMod pLen .p a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output pLen (operandValue s base a pLen * operandValue s base b pLen % p) := by
  have L := M.lengths
  have A := M.aligned
  have N : (pLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreProductMod_ok M.scr M.saved M.room M.extent rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.pReady Ra Rb M.pValue
    M.pLarge M.pOdd (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output pLen (operandValue s base a pLen * operandValue s base b pLen % p) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageSum_ok {base : Addr} {size pLen qLen p q output : Nat} {s : State} {a b : Pointer}
    (M : Moduli base size pLen qLen p q s)
    (Ra : OperandReady s base ((qLen + 7) / 8) a qLen) (Rb : OperandReady s base ((qLen + 7) / 8) b qLen)
    (ha : operandValue s base a qLen < q) (hbb : operandValue s base b qLen < q)
    (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.sum qLen a b output) s fun t =>
      Moduli base size pLen qLen p q t ∧
      StageResult base s t output qLen ((operandValue s base a qLen + operandValue s base b qLen) % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreSum_ok M.scr M.saved rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.qReady Ra Rb M.qValue
    (by have := M.qLarge; omega_using [this]) M.qOdd ha hbb (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen ((operandValue s base a qLen + operandValue s base b qLen) % q) :=
    ⟨StageFrame.of_frame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

theorem stageReduce_ok {base : Addr} {size pLen qLen p q output len : Nat} {s : State} {input : Pointer}
    {src : Src} (hsrc : LenOperand base size ((qLen + 7) / 8) s src len)
    (M : Moduli base size pLen qLen p q s)
    (Ri : StreamInput s base (contextBytes ((qLen + 7) / 8)) (pointerValue base s input) len)
    (Rs : Region.Disjoint ⟨(pointerValue base s input).setWidth 64, len⟩ (callStack (s.gpr .esp)))
    (hi : len < 2 ^ 32) (ho : r ≤ output) (hb : output + qLen ≤ usedBytes) :
    WP isa (Core.reduce qLen src input output) s fun t =>
      Moduli base size pLen qLen p q t ∧ StageResult base s t output qLen (operandValue s base input len % q) := by
  have L := M.lengths
  have A := M.aligned
  have N : (qLen + 7) / 8 ≤ 48 := by omega_using [L]
  have C := VG.Proof.Dsa.X86.Layout.context_bound N
  have low : 14720 ≤ output := ho
  refine WP.mono (coreReduce_ok hsrc M.scr M.saved M.room M.extent rfl (by omega_using [L]) (by omega_using [L]) (by omega_using [A]) M.qReady
    Ri Rs hi M.qValue M.qLarge M.qOdd (Nat.le_trans hb M.extent) (by omega_using [C, low])) fun t ⟨V, O, K⟩ => ?_
  have F : StageResult base s t output qLen (operandValue s base input len % q) :=
    ⟨StageFrame.of_stackFrame K (by intro reg hr; exact hr) O N, V⟩
  exact ⟨M.keep (F.toStageFrame.run (.inl ⟨ho, hb⟩)) F.keeps (by decide) (by decide), F⟩

end VG.Proof.Dsa.X86
