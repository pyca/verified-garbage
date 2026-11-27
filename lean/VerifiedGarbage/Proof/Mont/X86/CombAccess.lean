module

public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.X86.WordOps
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath
import VerifiedGarbage.Proof.Mont.X86.WindowSelect
public import VerifiedGarbage.Impl.Mont.X86.Window

/-! ### `Mont.X86.CombFrame`, which the modules that import this one used -/

section

/-! ### `Mont.X86.EncodeBase`, which only this module used -/

section

/-! Shared Montgomery initialization for ordinary powers and fixed-base combs. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86

def encodeRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 5, 8*n), (slot n 6, 8*n), (slot n 1, 8*n), (slot n 2, 16*n+4)]

theorem encodeBase_ok {n size m : Nat} {base : Addr} {s : State}
    (C : Context n m base size s)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2^(128*n) % m) :
    WP isa (encodeBase n) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n 6) n = 2^(64*n) % m ∧
      wordsVal t.mem base (slot n 5) n = wordsVal s.mem base (slot n 5) n * 2^(64*n) % m ∧
      Outs base (encodeRanges n) s.mem t.mem ∧ Keeps clob s t := by
  unfold encodeBase
  refine WP.seq (WP.mono (context_mul_ok C (o := 6) (a := 4) (b := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [one]; exact C.gt_one)) fun u ⟨Cu, Ku, ltu, Vu⟩ => ?_)
  have Yu : wordsVal u.mem base (slot n 6) n = 2^(64*n) % m :=
    mont_one C.coprime ltu (by rw [Vu, one, r2, Nat.mul_one, Nat.mod_mod])
  have Ru : wordsVal u.mem base (slot n 4) n = 2^(128*n) % m := by
    rw [context_slot_val C (by decide) (by decide) (by decide) (by decide) Ku, r2]
  have Bu := context_slot_val C (i := 5) (by decide) (by decide) (by decide) (by decide) Ku
  refine WP.mono (context_mul_ok Cu (o := 5) (a := 5) (b := 4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Ru]; exact Nat.mod_lt _ (by have := C.gt_one; omega_using [ltu]))) fun t ⟨Ct, Kt, ltt, Vt⟩ => ?_
  refine ⟨Ct, ?_, mont_encode C.coprime ltt (by rw [Vt, Ru, Bu]), ?_, (OpKeep.keeps Ku).trans (OpKeep.keeps Kt)⟩
  · rw [context_slot_val Cu (by decide) (by decide) (by decide) (by decide) Kt, Yu]
  · have frame {a b : State} {o : Nat} (ho : o = 5 ∨ o = 6)
        (K : OpKeep (contextMod n) base (slot n 2) (slot n o) a b) :
        Outs base (encodeRanges n) a.mem b.mem := K.mem.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rcases ho with rfl | rfl <;>
        simp [encodeRanges, contextMod, accLen, words] <;> omega_using [])
    exact (frame (.inr rfl) Ku).trans (frame (.inl rfl) Kt)

end VG.Proof.Mont.X86.Dynamic

end

end


/-! Shared memory geometry for the retained comb and arithmetic scratch. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

structure Layout (n context size : Nat) : Prop where
  positive : 0 < n
  apart : contextBytes n ≤ context
  bound : context+272*n ≤ size

theorem Layout.slot {n context size : Nat} (L : Layout n context size) {i : Nat} (hi : i < 9) :
    slot n i+8*n ≤ context := by
  have := slot_bound (n := n) hi
  have := L.apart
  unfold stride at *
  omega_arith

theorem entry_apart (n tab : Nat) {j k : Nat} (h : j ≠ k) :
    entry n tab j+8*n ≤ entry n tab k ∨ entry n tab k+8*n ≤ entry n tab j := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · left
    have := Nat.mul_le_mul_left (8*n) (show j+1 ≤ k by omega_using [h])
    simp only [Nat.mul_add, Nat.mul_one] at this
    unfold entry; omega_using [this]
  · right
    have := Nat.mul_le_mul_left (8*n) (show k+1 ≤ j by omega_using [h])
    simp only [Nat.mul_add, Nat.mul_one] at this
    unfold entry; omega_using [this]

theorem Layout.entry {n context size : Nat} (_L : Layout n context size) {j : Nat} (hj : j < 32) :
    context+16*n ≤ entry n (context+16*n) j ∧
    entry n (context+16*n) j+8*n ≤ context+272*n := by
  have := Nat.mul_le_mul_left (8*n) (show j+1 ≤ 32 by omega_using [hj])
  simp only [Nat.mul_add, Nat.mul_one] at this
  unfold VG.Impl.Mont.X86.Dynamic.entry
  omega_using [this]

theorem op_high {n size m o d : Nat} {base : Addr} {s t : State}
    (C : Context n m base size s) (ho : o < 9)
    (K : OpKeep (contextMod n) base (slot n 2) (slot n o) s t)
    (hd : contextBytes n ≤ d) (hz : d+8*n ≤ size) :
    wordsVal t.mem base d n = wordsVal s.mem base d n := by
  have bo := slot_bound (n := n) ho
  have b1 := slot_bound (n := n) (i := 1) (by decide)
  have b2 := slot_bound (n := n) (i := 2) (by decide)
  have nw := C.scr.nowrap
  unfold stride at bo b1 b2
  apply OpKeep.val K
  · right; change slot n o+8*n ≤ d; omega_using [hd, bo]
  · right; change slot n 1+8*n ≤ d; omega_using [hd, b1]
  · right; rw [context_accLen]; omega_using [hd, b2]
  · omega_using [hz, nw]

theorem outside_high_context {n context size m d len : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (C : Context n m base size s) {rs : List Reg}
    (K : Keeps rs s t) (hdi : .edi ∉ rs) (hsp : .esp ∉ rs)
    (O : Outside base d len s.mem t.mem) (hd : context ≤ d) : Context n m base size t := by
  apply C.outside_keep K hdi hsp O
  · left; have := L.slot (i := 0) (by decide); omega_using [hd, this]
  · have := slot_header n 9; have := L.apart; change slot n 9 ≤ context at this; omega_arith

/-- A retained-context write preserves every arithmetic slot. -/
theorem high_write_low {n context size i d len : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (hs : Scr s base size) (hi : i < 9)
    (O : Outside base d len s.mem t.mem) (hd : context ≤ d) :
    wordsVal t.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
  have bound := L.slot hi
  have size := L.bound
  have nw := hs.nowrap
  exact O.wordsVal (.inl (by omega_using [hd, bound])) (by omega_using [bound, size, nw])

theorem encode_high {n context size d : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (hs : Scr s base size)
    (O : Outs base (encodeRanges n) s.mem t.mem) (hd : context ≤ d) (hz : d+8*n ≤ size) :
    wordsVal t.mem base d n = wordsVal s.mem base d n := by
  have a := L.slot (i := 5) (by decide)
  have b := L.slot (i := 6) (by decide)
  have c := L.slot (i := 1) (by decide)
  have d' := slot_bound (n := n) (i := 2) (by decide)
  have apart := L.apart
  unfold stride at d'
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  apply O.val32
  · intro r hr
    simp only [encodeRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> right <;> omega_arith
  · have := hs.nowrap; omega_using [hz, this]

theorem high_copy_ok {n context size m src dst : Nat} {base : Addr} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (hb : src+8*n ≤ size) (hd : context ≤ dst) (hz : dst+8*n ≤ size)
    (sep : dst=src ∨ dst+8*n ≤ src ∨ src+8*n ≤ dst) :
    WP isa (copyWords n src dst) s fun t => Context n m base size t ∧
      wordsVal t.mem base dst n = wordsVal s.mem base src n ∧
      Outside base dst (8*n) s.mem t.mem ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  refine WP.mono (copyWords_ok C.scr L.positive hb hz sep) fun t ⟨V, O, K⟩ =>
    ⟨outside_high_context L C K (by decide) (by decide) O hd, V, O, K⟩

/-- Enlarge disjoint write ranges without changing their meaning. -/
theorem widen {base : Addr} {rs qs : List (Nat × Nat)} {s t : Mem}
    (O : Outs base rs s t)
    (h : ∀ r ∈ rs, ∃ q ∈ qs, q.1 ≤ r.1 ∧ r.1+r.2 ≤ q.1+q.2) : Outs base qs s t := by
  intro x hx
  apply O x
  intro r hr
  obtain ⟨q, hq, lo, hi⟩ := h r hr
  have := hx q hq
  omega_using [lo, hi, this]

end VG.Proof.Mont.X86.Comb

end

end

/-! ### `Mont.X86.CombCopy`, which only this module used -/

section

/-! A shared public-pointer copy loop for comb construction and selection. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

private theorem count_one {x : BitVec 32} {N i : Nat} (h : x.toNat = N-i) (hi : i < N) :
    (x-1#32).toNat = N-(i+1) ∧ (x-1#32 == 0) = decide (i+1 = N) := by
  have value : (x-1#32).toNat = N-(i+1) := by
    rw [BitVec.toNat_sub, h]
    change (2^32 - 1 + (N-i)) % 2^32 = _
    have := x.isLt
    omega_using [h, hi]
  refine ⟨value, ?_⟩
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro hz; have := congrArg BitVec.toNat hz; rw [value] at this; change N-(i+1) = 0 at this; omega_using [hi, this]
  · intro hiN; apply BitVec.eq_of_toNat_eq; rw [value]; change N-(i+1) = 0; omega_using [hiN]

/-- Both copy directions use the same proof. Only public pointers advance;
source and destination must be separate. -/
theorem copyLoop_ok {s : State} {W : Addr} {size x y sd dd N : Nat} {src dst : Reg}
    (hw : Ws s W size) (hN : 0 < N)
    (hs : src ∈ [.ecx, .ebp]) (hd : dst ∈ [.ecx, .ebp])
    (hx : x+sd+4*N ≤ size) (hy : y+dd+4*N ≤ size)
    (sep : x+sd+4*N ≤ y+dd ∨ y+dd+4*N ≤ x+sd)
    (ps : PtrAt s W src x) (pd : PtrAt s W dst y)
    (count : (s.gpr .ebx).toNat = N) :
    WP isa (VG.Impl.Mont.X86.Comb.copyLoop (at_ src sd) (at_ dst dd)) s fun t =>
      Outside W (y+dd) (4*N) s.mem t.mem ∧
      val32 t.mem W (y+dd) N = val32 s.mem W (x+sd) N ∧
      Keeps [.eax, .ebx, .ecx, .ebp] s t := by
  have nw := hw.nowrap
  unfold VG.Impl.Mont.X86.Comb.copyLoop
  refine WP.mono (countLoop hN (fun i t =>
      Keeps [.eax, .ebx, .ecx, .ebp] s t ∧ PtrAt t W src (x+4*i) ∧ PtrAt t W dst (y+4*i) ∧
      (t.gpr .ebx).toNat = N-i ∧ Outside W (y+dd) (4*i) s.mem t.mem ∧
      val32 t.mem W (y+dd) i = val32 s.mem W (x+sd) i) ?_
    ⟨Keeps.refl _ _, by simpa using ps, by simpa using pd, by simpa using count,
      Outside.refl _ _ _ _, rfl⟩) fun t ⟨K, _, _, _, O, V⟩ => ⟨O, V, K⟩
  rintro i t hi ⟨K, PS, PD, C, O, V⟩
  have ht := hw.of_keeps K
  have dst_eax : dst ≠ .eax := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> decide
  refine wp_movS (readSrc_ptr ht PS (d := sd) (by omega_arith)) fun u U _ => ?_
  have hu := ht.of_keeps U.keeps
  have PD' : PtrAt u W dst (y+4*i) := by rw [PtrAt, U.other dst dst_eax]; exact PD
  refine wp_storeS (ea_ptr hu PD' (d := dd) (by omega_arith))
    (ws_write hu (y := y+4*i+dd) (n := 4) (by omega_arith)) fun v M => ?_
  refine wp_addS rfl fun v₁ A _ => wp_addS rfl fun v₂ B _ => wp_subZ rfl fun v₃ D Z => WP.block_nil ?_
  have C' : v₂.gpr .ebx = t.gpr .ebx := by
    rw [B.other _ (by decide), A.other _ (by decide), M.gpr, U.other _ (by decide)]
  obtain ⟨newCount, zero⟩ := count_one C hi
  have pointers : ∀ r ∈ [.ecx, .ebp], v₃.gpr r = t.gpr r + 4 := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [D.other _ (by decide), B.other _ (by decide), A.gpr, M.gpr, U.other _ (by decide)]; rfl
    · rw [D.other _ (by decide), B.gpr, A.other _ (by decide), M.gpr, U.other _ (by decide)]; rfl
  have mem : v₃.mem = u.mem.writeW (off W (y+4*i+dd)) (u.gpr .eax) := by
    rw [D.mem, B.mem, A.mem, M.mem]
  refine ⟨⟨((((K.widen U.keeps).trans (M.keeps _)).widen A.keeps).widen B.keeps).widen D.keeps,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [PtrAt, pointers src hs]; exact ptr4 PS
  · rw [PtrAt, pointers dst hd]; exact ptr4 PD
  · rw [D.gpr, C']; exact newCount
  · rw [mem, U.mem]
    exact (O.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · rw [mem, show y+4*i+dd = y+dd+4*i by omega_arith, val32_store nw (by omega_arith), U.mem, V, U.gpr]
    rw [val32_succ]
    congr 1
    congr 1
    change w32 t.mem W (x+4*i+sd) = w32 s.mem W (x+sd+4*i)
    rw [show x+4*i+sd = x+sd+4*i by omega_arith]
    exact O.w32 (by omega_arith) (by omega_arith)
  · rw [Z, C', zero]

/-- The same public pointer setup serves both table reads and table writes. -/
theorem copySetup_ok {s : State} {W : Addr} {size n tab : Nat} {index : Src} {v : BitVec 32}
    (hs : Scr s W size) (hn : 8*n < 2^32) (hv : readSrc s index = some v) :
    WP isa (VG.Impl.Mont.X86.Comb.copySetup n tab index) s fun t =>
      t.mem = s.mem ∧ PtrAt t W .ecx (tab+8*n*v.toNat) ∧ PtrAt t W .ebp 0 ∧
      (t.gpr .ebx).toNat = 2*n ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Comb.copySetup
  refine wp_movS hv fun s₁ U₁ _ => wp_movS rfl fun s₂ U₂ _ => wp_mul fun s₃ U₃ => ?_
  refine wp_addS rfl fun s₄ U₄ _ => wp_addS rfl fun s₅ U₅ _ => wp_movS rfl fun s₆ U₆ _ => ?_
  refine wp_movS rfl fun s₇ U₇ _ => wp_movS rfl fun t U₈ _ => WP.block_nil ?_
  have E : s₂.gpr .eax = v := by rw [U₂.other _ (by decide), U₁.gpr]
  have D : s₂.gpr .edx = BitVec.ofNat 32 (8*n) := U₂.gpr
  have base : s₃.gpr .edi = s.gpr .edi := by
    rw [U₃.other _ (by decide) (by decide), U₂.other _ (by decide), U₁.other _ (by decide)]
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t :=
    (((((((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps).widen U₄.keeps).widen
      U₅.keeps).widen U₆.keeps).widen U₇.keeps).widen U₈.keeps
  refine ⟨?_, ?_, ?_, ?_, K⟩
  · rw [U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  · unfold PtrAt
    rw [U₈.other _ (by decide), U₇.other _ (by decide), U₆.gpr, U₅.gpr, U₄.gpr, U₃.eax, E, D, base]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hn, hs.edi_toNat]
    rw [Nat.mul_comm v.toNat]
    omega_using []
  · unfold PtrAt
    rw [U₈.other _ (by decide), U₇.gpr, U₆.other _ (by decide), U₅.other _ (by decide),
      U₄.other _ (by decide), base, hs.edi_toNat, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (by rw [← hs.edi_toNat]; exact (s.gpr .edi).isLt)).symm
  · rw [U₈.gpr]
    change (2*n) % 2^32 = 2*n
    exact Nat.mod_eq_of_lt (by omega_using [hn])

end VG.Proof.Mont.X86.Comb

end

end


/-! Public comb table access shares its pointer setup and copying proof. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem publicSelect_ok {s : State} {base : Addr} {size n tab dst : Nat}
    (hs : Scr s base size) (hn : 0 < n) (header : 8 ≤ size)
    (src : entry n tab (w32 s.mem base 4)+8*n ≤ size) (out : dst+8*n ≤ size)
    (sep : dst+8*n ≤ entry n tab (w32 s.mem base 4) ∨
      entry n tab (w32 s.mem base 4)+8*n ≤ dst) :
    WP isa (VG.Impl.Mont.X86.Comb.publicSelect n tab dst) s fun t =>
      Outside base dst (8*n) s.mem t.mem ∧
      wordsVal t.mem base dst n = wordsVal s.mem base (entry n tab (w32 s.mem base 4)) n ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Comb.publicSelect
  refine WP.seq (WP.mono (copySetup_ok hs (by have := hs.size_lt; omega_using [src, this])
    (readSrc_sc hs (d := 4) header)) fun u ⟨M, P, Q, C, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  refine WP.mono (copyLoop_ok (x := entry n tab (w32 s.mem base 4)) (y := 0) (sd := 0) (dd := dst)
    (N := 2*n) ⟨hu.wr, hu.nowrap⟩ (by omega_using [hn]) (by simp) (by simp)
    (by omega_using [src]) (by omega_using [out]) (by omega_using [sep]) P Q C) fun t ⟨O, V, K'⟩ => ?_
  refine ⟨?_, ?_, K.trans (K'.mono (by decide))⟩
  · simpa only [Nat.zero_add, show 4*(2*n) = 8*n by omega_using [], M] using O
  · simpa only [wordsVal_eq_val32, Nat.zero_add, Nat.add_zero, M] using V

theorem copyToComb_ok {s : State} {base : Addr} {size n tab src : Nat}
    (hs : Scr s base size) (hn : 0 < n)
    (input : src+8*n ≤ size) (out : entry n tab (s.gpr .esi).toNat+8*n ≤ size)
    (sep : src+8*n ≤ entry n tab (s.gpr .esi).toNat ∨
      entry n tab (s.gpr .esi).toNat+8*n ≤ src) :
    WP isa (VG.Impl.Mont.X86.Comb.copyToComb n tab src) s fun t =>
      Outside base (entry n tab (s.gpr .esi).toNat) (8*n) s.mem t.mem ∧
      wordsVal t.mem base (entry n tab (s.gpr .esi).toNat) n = wordsVal s.mem base src n ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold VG.Impl.Mont.X86.Comb.copyToComb
  refine WP.seq (WP.mono (copySetup_ok hs (by have := hs.size_lt; omega_using [input, this]) rfl)
    fun u ⟨M, P, Q, C, K⟩ => ?_)
  have hu := hs.of_keeps K (by decide)
  refine WP.mono (copyLoop_ok (x := 0) (y := entry n tab (s.gpr .esi).toNat) (sd := src) (dd := 0)
    (N := 2*n) ⟨hu.wr, hu.nowrap⟩ (by omega_using [hn]) (by simp) (by simp)
    (by omega_using [input]) (by omega_using [out]) (by omega_using [sep]) Q P C) fun t ⟨O, V, K'⟩ => ?_
  refine ⟨?_, ?_, K.trans (K'.mono (by decide))⟩
  · simpa only [Nat.add_zero, show 4*(2*n) = 8*n by omega_using [], M] using O
  · simpa only [wordsVal_eq_val32, Nat.zero_add, Nat.add_zero, M] using V

end VG.Proof.Mont.X86.Comb
