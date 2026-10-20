module

import VerifiedGarbage.Proof.Dsa.X86.PowCorrect
public import VerifiedGarbage.Proof.Dsa.X86.StackFrame
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Pow
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.PowBody
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! # Calling shared DSA exponentiation with an explicit stack frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

theorem shift_noSp (e d : Nat) :
    (shiftExponent e d).all (fun i => !Taint.clobbers i .esp) = true := by
  induction e generalizing d with
  | zero => rfl
  | succ e ih => simp only [shiftExponent, List.all_append, ih, Bool.and_true]; rfl

theorem body_noSp (n e : Nat) : NoSp (body n e) := NoSp.of_all (by
  rw [Code.allInstrs_eq]
  simp only [body, core, contextSetup, exponentiate, exponentStep, exponentBody,
    exponentProduct, instrs, List.all_append, shift_noSp, Bool.and_true]
  rfl)

theorem shift_spSafe (e d : Nat) :
    (shiftExponent e d).all (fun i => !isa.writesSp i) = true := by
  induction e generalizing d with
  | zero => rfl
  | succ e ih => simp only [shiftExponent, List.all_append, ih, Bool.and_true]; rfl

theorem body_spSafe (n e : Nat) : (body n e).allInstrs (fun i => !isa.writesSp i) = true := by
  rw [Code.allInstrs_eq]
  simp only [body, core, contextSetup, exponentiate, exponentStep, exponentBody,
    exponentProduct, instrs, List.all_append, shift_spSafe, Bool.and_true]
  rfl

theorem body_stackUse (n e : Nat) : stackUse (body n e) = 0 := by rfl

theorem zone_ofs {sp : BitVec 32} {base : Addr} {size : Nat}
    (H : Room sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {x : Addr} (hx : (below sp 12).Contains x 1) : size ≤ ofs base x := by
  obtain ⟨h32, hz⟩ := H
  have hsp := sp.isLt
  simp only [Region.Contains] at hx
  simp only [ofs]
  have e : ((sp - BitVec.ofNat 32 12).setWidth 64).toNat = sp.toNat - 12 := by
    rw [BitVec.toNat_setWidth, VG.X86.sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  generalize ((sp - BitVec.ofNat 32 12).setWidth 64) = z at hx e
  bv_omega

theorem frame_val32 {sp : BitVec 32} {base : Addr} {size : Nat}
    (H : Room sp base size) (hn : base.toNat + size ≤ 2 ^ 32)
    {m m' : Mem} (F : Frame [below sp 12] m m') {d k : Nat} (hd : d + 4 * k ≤ size) :
    val32 m' base d k = val32 m base d k := by
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => F _ fun r hr hc => ?_)
  rw [List.mem_singleton.mp hr] at hc
  have := zone_ofs H hn hc
  rw [ofs_off base (by omega)] at this
  omega

theorem call_ok {s : State} {base : Addr} {size n e m : Nat}
    (hs : Scr s base size) (room : Room (s.gpr .esp) base size)
    (hz : contextBytes n ≤ size) (hused : VG.Impl.Dsa.Layout.usedBytes ≤ size)
    (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Impl.Dsa.X86.Pow.call n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      StackOuts base (s.gpr .esp) (scratch n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  have nw := hs.nowrap
  obtain ⟨h32, sep⟩ := room
  have spBound := (s.gpr .esp).isLt
  unfold Impl.Dsa.X86.Pow.call
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have usp : u.gpr .esp = s.gpr .esp := U.other _ (by decide)
  have udi : u.gpr .edi = s.gpr .edi := U.other _ (by decide)
  have fit : 4 * [Reg.eax, .edi].length + 4 ≤ (u.gpr .esp).toNat := by rw [usp]; simp; omega
  let t := ((pushed [Reg.eax, .edi] u).callEntry).withRegions [below (u.gpr .esp) 8] [⟨base, size⟩]
  have a0 : (arg t 0).setWidth 64 = base := by
    rw [show arg t 0 = u.gpr .edi from callEntry_arg fit (by decide) (by decide), udi, hs.edi]
  have tsp : (t.gpr .esp).toNat = (s.gpr .esp).toNat - 12 := by
    show ((pushed _ u).callEntry.gpr .esp).toNat = _
    rw [callEntry_espNat fit, usp]; rfl
  have argA : argAddr t 0 = (u.gpr .esp - BitVec.ofNat 32 8).setWidth 64 := callEntry_argAddr0 _ _
  have argN : (argAddr t 0).toNat = (s.gpr .esp).toNat - 8 := by
    rw [argA, usp, BitVec.toNat_setWidth, VG.X86.sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have retN : ((t.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat - 12 := by
    rw [BitVec.toNat_setWidth, tsp]; exact Nat.mod_eq_of_lt (by omega)
  have fr : Frame [below (s.gpr .esp) 12] s.mem t.mem := by
    have H := callEntry_frame fit (rs := [Reg.eax, .edi]) (by decide)
    rw [U.mem, usp] at H
    exact H
  have E : Entry t base size := by
    refine ⟨?_, a0, List.mem_singleton_self _, nw, ?_⟩
    · refine ⟨⟨argAddr t 0, 8⟩, ?_, ?_⟩
      · change _ ∈ [below (u.gpr .esp) 8] ++ [⟨base, size⟩]
        rw [argA]; exact List.mem_cons_self ..
      · simpa only [BitVec.add_zero] using Offset.contains_base (argAddr t 0)
          (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    · unfold StkOk; rw [tsp]; constructor <;> omega
  have ret : Region.Disjoint ⟨(t.gpr .esp).setWidth 64, 4⟩ ⟨base, size⟩ :=
    Region.disjoint_of_le (by simp only; rw [retN]; omega)
      (by simp only; rw [retN]; omega) (by simp only; omega)
  let K : Contract isa :=
    { pre := fun v => Entry v base size ∧
        Region.Disjoint ⟨(v.gpr .esp).setWidth 64, 4⟩ ⟨base, size⟩ ∧
        wordsVal v.mem base (slot n 0) n = m
      post := fun v w => wordsVal w.mem base (slot n 6) n =
        wordsVal v.mem base (slot n 5) n ^ val32 v.mem base (slot n 8) e % m ∧
        Outs base (scratch n) v.mem w.mem
      pub := fun _ _ => True }
  have vals : ∀ d k, d + 4 * k ≤ size → val32 t.mem base d k = val32 s.mem base d k :=
    fun _ _ hd => frame_val32 ⟨h32, sep⟩ nw fr hd
  have V : wordsVal t.mem base (slot n 0) n = m := by
    rw [wordsVal_eq_val32, vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega),
      ← wordsVal_eq_val32, hv]
  refine WP.callWith (k := K) (fun v ⟨Ev, Rv, Mv⟩ => ?_) (body_noSp n e) (by decide) (by decide)
    (by rw [body_stackUse]; exact fit) (rd := [below (u.gpr .esp) 8]) (wr := [⟨base, size⟩])
    ⟨⟨E, ret, V⟩, ?_, ?_⟩ ?_
  · obtain ⟨tr, w, ex, W, O, R, _, _⟩ := body_ok Ev hz hn hn48 he hen Mv hm1 hodd
    have F : Frame [⟨base, size⟩] v.mem w.mem := by
      intro x hx
      apply O x
      intro r hr
      have H := hx _ (List.mem_singleton_self _)
      have B := scratch_fits hz r hr
      simp only [Region.Contains, ofs] at H ⊢
      omega
    refine ⟨tr, w, ex, ⟨R, ?_⟩, W, O⟩
    exact F.readW (by simpa only [BitVec.add_zero] using
      Offset.contains_base ((v.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact Rv) (by decide)
  · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; simp
    · rw [List.mem_singleton.mp hr, U.wr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, U.wr]; exact List.mem_cons_of_mem _ hs.wr
  · intro w rd wr cs _ post
    obtain ⟨v, mem, W, O⟩ := post
    refine ⟨?_, ?_, ?_⟩
    · rw [← mem, W, wordsVal_eq_val32, vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega),
        vals _ _ (by simp only [contextBytes, slot, stride] at hz ⊢; omega), ← wordsVal_eq_val32]
    · intro x hx hxstack
      have outside : ¬ (below (s.gpr .esp) 12).Contains x 1 := by
        intro hin
        rcases hxstack with hlocal | hstack
        · have := zone_ofs ⟨h32, sep⟩ nw hin; omega
        · apply hstack
          have sub := below_sub (sp := s.gpr .esp) (a := 12) (b := 32) (by decide) h32
          exact sub _ hin
      rw [← mem, O x hx]
      exact fr x fun r hr => by rw [List.mem_singleton.mp hr]; exact outside
    · refine ⟨fun r hr => ?_, rd.trans U.rd, wr.trans U.wr⟩
      have cr : r ∈ calleeSaved := by revert hr; cases r <;> decide
      rw [cs r cr, U.other r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.1)]

end VG.Proof.Dsa.X86.Pow
