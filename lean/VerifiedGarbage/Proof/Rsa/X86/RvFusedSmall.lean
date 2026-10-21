module

public import VerifiedGarbage.Proof.Rsa.X86.RvMont
public import VerifiedGarbage.Proof.Rsa.X86.RvMontPower
public import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
public import VerifiedGarbage.Proof.Rsa.X86.RvFusedFlags
import VerifiedGarbage.Proof.Rsa.X86.RvOps
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Multiplication by the public recovery candidate, using modular additions. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev fusedLive : List Nat := [0, mY, mX, mXm] ++ liveM
abbrev fusedSlots : List Nat := [sInv,sCnt,sTc,sCand,sWin,sBit,sDone,sOk]

def SmallI (g : Geo) (s0 : State) (A AW V : Nat → Nat) (m x b j : Nat) (s : State) : Prop :=
  KS g s0 (upd A mXm (j * x % m)) fusedLive AW [wRc,wR] V fusedSlots s ∧
    s.gpr .esi = BitVec.ofNat 32 (b - j)

theorem fusedSmallStep_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m x b j : Nat}
    (h : SmallI g s0 A AW V m x b j s)
    (value : A mBase = m) (modulus : A aN = m) (zero : A aZ = 0)
    (bound : m < 2 ^ (64 * g.n)) (inverse : (m * V sInv + 1) % 2 ^ 32 = 0)
    (positive : 0 < m) (vx : A mX = x) (xl : x < m) (hj : j < b) (bb : b ≤ 101) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedSmallStep s fun t =>
      SmallI g s0 A AW V m x b (j+1) t ∧ t.zf = some (decide (b - (j+1) = 0)) := by
  obtain ⟨h, counter⟩ := h
  have mr := h.montReady (by decide) (by decide)
    (by exact value) bound inverse
  have big : 2 * m ≤ 2 ^ (32 * g.w) := by
    have pw := Nat.pow_le_pow_right (n := 2) (by decide) (show 64*g.n+1 ≤ 32*g.w by
      simp only [Geo.w, width]; omega)
    rw [Nat.pow_succ] at pw
    omega
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedSmallStep
  refine WP.seq (WP.mono (h.addMod mr (o := mXm) (a := mXm) (b := mX) (n := aN) (z := aZ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    (by exact zero)
    (by change j*x % m < A aN; rw [modulus]; exact Nat.mod_lt _ positive)
    (by change A mX < A aN; rw [vx,modulus]; exact xl)
    (by change 2*A aN ≤ _; rw [modulus]; exact big)) fun u ⟨hu, _, _, esi⟩ => ?_)
  have sum : (j*x % m + x) % m = (j+1)*x % m := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mod_add_mod]
  have v : (upd A mXm (j*x % m) mXm + upd A mXm (j*x % m) mX) %
      upd A mXm (j*x % m) aN = (j+1)*x % m := by
    change (j*x % m + A mX) % A aN = _
    rw [vx,modulus]
    exact sum
  rw [v] at hu
  have hu' : KS g s0 (upd A mXm ((j+1)*x % m)) fusedLive AW [wRc,wR] V fusedSlots u :=
    hu.mono (fun i hi => ⟨List.mem_cons_of_mem _ hi, by rw [upd_twice]⟩) (fun i hi => ⟨hi,rfl⟩) (fun d hd => ⟨hd,rfl⟩)
  refine wp_subS rfl fun v D _ => ?_
  have hv := hu'.of_rest D.keeps (by decide) D.mem
  have count : v.gpr .esi = BitVec.ofNat 32 (b-(j+1)) := by
    rw [D.gpr, esi, counter]
    change BitVec.ofNat 32 (b-j) - 1 = BitVec.ofNat 32 (b-(j+1))
    calc
      _ = BitVec.ofNat 32 ((b-j)-1) := BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
      _ = _ := congrArg (BitVec.ofNat 32) (by omega)
  refine wp_cmpS (v := (0 : BitVec 32)) rfl fun t T zt => WP.block_nil ?_
  refine ⟨⟨hv.of_rest (T.keeps []) (by decide) T.mem, ?_⟩, ?_⟩
  · rw [T.gpr, count]
  · rw [zt, count]
    rw [show BitVec.ofNat 32 (b-(j+1)) - (0 : BitVec 32) = BitVec.ofNat 32 (b-(j+1))
      from BitVec.sub_zero _]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl

theorem fusedSmallLoop_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m x b : Nat}
    (h : SmallI g s0 A AW V m x b 1 s)
    (value : A mBase = m) (modulus : A aN = m) (zero : A aZ = 0)
    (bound : m < 2 ^ (64 * g.n)) (inverse : (m * V sInv + 1) % 2 ^ 32 = 0)
    (positive : 0 < m) (vx : A mX = x) (xl : x < m) (lo : 2 ≤ b) (hi : b ≤ 101) :
    WP isa (.loop VG.Impl.Rsa.X86.RecoverRt.fusedSmallStep .ne) s
      (SmallI g s0 A AW V m x b b) := by
  refine WP.loop (M := isa)
    (fun left u => ∃ j, j + left = b ∧ 0 < left ∧ SmallI g s0 A AW V m x b j u)
    ?_ (b-1) s ⟨1, by omega, by omega, h⟩
  intro left u ⟨j, total, positiveLeft, hu⟩
  refine WP.mono (fusedSmallStep_ok hu value modulus zero bound inverse positive vx xl
    (by omega) hi) fun t ⟨ht, zt⟩ => ?_
  by_cases last : j+1 = b
  · left
    refine ⟨?_, ?_⟩
    · change t.zf.map (!·) = some false
      simp [zt,last]
    · simpa only [last] using ht
  · right
    refine ⟨?_,left-1,by omega,j+1,by omega,by omega,ht⟩
    change t.zf.map (!·) = some true
    simp [zt, show b-(j+1) ≠ 0 by omega]

def fusedSmallStart : Prog isa := .seq
  (VG.Impl.Rsa.X86.KeyRt.copy VG.Impl.Rsa.X86.RecoverRt.nar mXm mX)
  (.block [.mov .esi (.mem (VG.Impl.Mont.X86.sc sCand)), .alu .add .esi (.imm 1)])

theorem fusedSmallStart_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m x : Nat}
    (h : KS g s0 A fusedLive AW [wRc,wR] V fusedSlots s)
    (vx : A mX = x) (xl : x < m) :
    WP isa fusedSmallStart s (SmallI g s0 A AW V m x (V sCand+2) 1) := by
  unfold fusedSmallStart
  refine WP.seq (WP.mono (h.copy_w (o := mXm) (a := mX) (by decide) (by decide)
    (by decide) (by decide)) fun u ⟨hu,_,_⟩ => ?_)
  refine wp_movS (hu.readSlot (by decide)) fun v U _ => ?_
  have hv := hu.of_rest U.keeps (by decide) U.mem
  refine wp_addS rfl fun w D _ => WP.block_nil ?_
  have hw := hv.of_rest D.keeps (by decide) D.mem
  show SmallI g s0 A AW V m x (V sCand+2) 1 w

  refine ⟨hw.mono (fun i hi => ⟨List.mem_cons_of_mem _ hi, ?_⟩)
    (fun i hi => ⟨hi,rfl⟩) (fun d hd => ⟨hd,rfl⟩), ?_⟩
  · rw [vx, Nat.one_mul, Nat.mod_eq_of_lt xl]
  · rw [D.gpr, U.gpr]
    change BitVec.ofNat 32 (V sCand) + BitVec.ofNat 32 1 = BitVec.ofNat 32 (V sCand+2-1)
    rw [← BitVec.ofNat_add]
    congr 1

theorem fusedSmall_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m x : Nat}
    (h : KS g s0 A fusedLive AW [wRc,wR] V fusedSlots s)
    (value : A mBase = m) (modulus : A aN = m) (zero : A aZ = 0)
    (bound : m < 2 ^ (64 * g.n)) (inverse : (m * V sInv + 1) % 2 ^ 32 = 0)
    (positive : 0 < m) (vx : A mX = x) (xl : x < m) (candidate : V sCand < 100) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.fusedSmall s fun t =>
      KS g s0 (upd A mXm ((V sCand+2)*x % m)) fusedLive AW [wRc,wR] V fusedSlots t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.fusedSmall
  simp only [seqs]
  refine WP.seq (WP.mono (h.copy_w (o := mXm) (a := mX) (by decide) (by decide)
    (by decide) (by decide)) fun u ⟨hu,_,_⟩ => ?_)
  refine WP.seq (wp_movS (hu.readSlot (by decide)) fun v U _ => ?_)
  have hv := hu.of_rest U.keeps (by decide) U.mem
  refine wp_addS rfl fun w D _ => WP.block_nil ?_
  have hw := hv.of_rest D.keeps (by decide) D.mem
  have init : SmallI g s0 A AW V m x (V sCand+2) 1 w := by
    refine ⟨hw.mono (fun i hi => ⟨List.mem_cons_of_mem _ hi, ?_⟩)
      (fun i hi => ⟨hi,rfl⟩) (fun d hd => ⟨hd,rfl⟩), ?_⟩
    · rw [vx, Nat.one_mul, Nat.mod_eq_of_lt xl]
    · rw [D.gpr, U.gpr]
      change BitVec.ofNat 32 (V sCand) + BitVec.ofNat 32 1 = BitVec.ofNat 32 (V sCand+2-1)
      rw [← BitVec.ofNat_add]
      congr 1
  refine WP.mono (fusedSmallLoop_ok init value modulus zero bound inverse positive vx xl
    (by omega) (by omega)) fun t ht => ht.1

end VG.Proof.Rsa.X86.Recover
