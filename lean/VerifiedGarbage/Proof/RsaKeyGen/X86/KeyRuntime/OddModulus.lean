module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Ops
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Scalar
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyDivision
public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.WordBounds32
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Zero

/-! ### `RsaKeyGen.X86.KeyRuntime.Constant`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.KeyRuntime.Small`, which this module and modules that import it used -/

section

/-! # Small constants need one store after a shared runtime zero loop -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.Mont.X86.Rt (PtrAt)

theorem write_zero {m : Mem} {B : Addr} {Z o k : Nat} (nw : B.toNat + Z ≤ 2 ^ 32)
    (fit : o + 4 * (k + 1) ≤ Z) (zero : val32 m B o (k + 1) = 0) (x : BitVec 32) :
    val32 (m.writeW (off B o) x) B o (k + 1) = x.toNat := by
  rw [val32] at zero ⊢
  have above : val32 m B (o + 4) k = 0 := by omega_using [zero]
  rw [w32_write_self]
  have O := writeW32_outside m B (d := o) x (by omega_using [nw, fit])
  rw [O.val32 (by omega_using []) (by omega_using [nw, fit]), above, Nat.mul_zero, Nat.add_zero]

theorem small_ok {s : State} {B : Addr} {Z n N j : Nat} (h : Ws s B Z n N)
    (w : Width) (x : BitVec 32)
    (fit : (Loc.array w j).offset n + 4 * (w.words n + 2) ≤ Z) :
    WP isa (small w j x) s fun t => Ws t B Z n N ∧
      Outside B (Loc.offset n (.array w j)) (4 * (w.words n + 2)) s.mem t.mem ∧
      val32 t.mem B (Loc.offset n (.array w j)) (w.words n + 2) = x.toNat ∧
      Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have nowrap := h.old.workspace.nowrap
  unfold small
  refine WP.seq (WP.mono (zero_ok h w (.array w j) fit) fun a ⟨ha, Oa, V, Ka⟩ => ?_)
  refine ha.ptr_ok (.array w j) (by decide) (by decide) (by omega_using [fit, nowrap]) fun b Kb mb P => ?_
  refine wp_movS rfl fun c C _ => ?_
  have Kac : Keeps [.eax, .ecx, .edx, .ebp] a c := (Kb.mono (by decide)).trans
    (C.keeps.mono (by decide))
  have hw := ha.full.rt.of_keeps Kac
  have pc : PtrAt c B .ebp (Loc.offset n (.array w j)) := by
    rw [PtrAt, C.other _ (by decide)]; exact P
  refine wp_storeS (VG.Proof.Mont.X86.Rt.ea_ptr hw pc (d := 0) (by omega_using [fit]))
    (VG.Proof.Mont.X86.Rt.ws_write hw (y := Loc.offset n (.array w j) + 0) (n := 4)
      (by omega_using [fit])) fun t T => WP.block_nil ?_
  have memory : t.mem = a.mem.writeW (off B (Loc.offset n (.array w j))) x := by
    rw [T.mem, C.mem, mb, C.gpr, Nat.add_zero]
  have Ot : Outside B (Loc.offset n (.array w j)) 4 a.mem t.mem := by
    rw [memory]; exact writeW32_outside _ _ _ (by omega_using [fit, nowrap])
  have Kall : Keeps [.eax, .ecx, .edx, .ebp] s t := Ka.trans
    (Kac.trans (T.keeps _))
  have Oall := Oa.trans (Ot.mono (Nat.le_refl _) (by omega_using []))
  refine ⟨h.keep Kall (Oall.mono (Nat.zero_le _) (by omega_using [fit])), Oall, ?_, Kall⟩
  rw [memory]
  exact write_zero nowrap fit V x

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! # Small constants in the persistent runtime-width bank -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep arr S)
open VG.Impl.RsaKeyGen.X86.KeyRuntime hiding arr

theorem constant_ok {s : State} {B : Addr} {Z n N j : Nat}
    (h : Ws s B Z n N) (hj : j < N) (x : BitVec 32) :
    WP isa (cn j x) s fun t => Ws t B Z n N ∧ Keep B n [j] [] s.mem t.mem ∧
      num t.mem B n j = x.toNat ∧ Keeps [.eax, .ecx, .edx, .ebp] s t := by
  have fit := h.arr_fit hj
  refine WP.mono (small_ok h .modulus x (by
    simpa only [offset_array, Width.words, S] using fit)) fun t ⟨ht, O, V, K⟩ => ?_
  simp only [offset_array, Width.words] at O V
  have bound : val32 t.mem B (arr n j) (n + 2) < 2 ^ (32 * n) := by
    rw [V]
    exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by have := h.wpos; omega_using [this]))
  exact ⟨ht, Keep.of_arr (d := 0) (by simpa only [Nat.add_zero] using O)
      (by simp only [S]; omega_using []) (by simp),
    (VG.Proof.RsaKeyGen.WordBounds32.low_eq (by omega_using [] : n ≤ n + 2) bound).trans V, K⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime

end

end

/-! ### `RsaKeyGen.X86.KeyOddFlag`, which only this module used -/

section

/-! # Form a secret modulus-validity bit from a borrow and parity -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem odd_mask (b x : BitVec 32) (bit : b.toNat ≤ 1) :
    (((1 : BitVec 32) - b) &&& x &&& (1 : BitVec 32)).toNat =
      if b.toNat = 0 then x.toNat % 2 else 0 := by
  rcases VG.Proof.Rsa.KeyBits32.bit_cases bit with hb | hb
  · rw [hb]
    change (((1 : BitVec 32) &&& x) &&& (1 : BitVec 32)).toNat = x.toNat % 2
    rw [BitVec.and_comm (1 : BitVec 32) x, BitVec.and_assoc, BitVec.and_self]
    exact VG.Proof.Rsa.KeyBits32.bv_and_one x
  · rw [hb]
    change ((0#32 &&& x) &&& (1 : BitVec 32)).toNat = 0
    simp only [BitVec.zero_and, BitVec.toNat_zero]

end VG.Proof.RsaKeyGen.X86.Key

end

end

/-! # Safe inverse moduli at the shared runtime width -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRuntime/OddFlag.lean`, which only this module imported.
section

/-! # Form the inverse-modulus validity bit through a public runtime pointer -/

section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (num Keep slot)
open VG.Impl.RsaKeyGen.X86.Key (kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem oddFlag_ok {s : State} {B : Addr} {Z n N input : Nat}
    (h : Ws s B Z n N) (hi : input < N) (bit : (s.gpr .ebx).toNat ≤ 1) :
    WP isa (.block (oddFlag input)) s fun t => Ws t B Z n N ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if (s.gpr .ebx).toNat = 0 then num s.mem B n input % 2 else 0) ∧
      Keeps [.eax, .edx, .ebp] s t := by
  have fit := h.arr_fit hi
  have nowrap := h.old.workspace.nowrap
  unfold oddFlag
  simp only [List.cons_append, List.nil_append]
  refine wp_movS rfl fun u U _ => wp_subS rfl fun v V _ => ?_
  have Kv : Keeps [.eax] s v := U.keeps.trans V.keeps
  have mv : v.mem = s.mem := V.mem.trans U.mem
  have hv := h.keep Kv (by rw [mv]; exact Outside.refl _ _ _ _)
  refine hv.ptr_ok (arr input) (by decide) (by decide)
    (by simp only [arr, offset_array, Width.words]; unfold VG.Proof.Rsa.X86.Keys.S at fit; omega)
    fun w Kw mw P => ?_
  have hw := hv.keep Kw (by rw [mw]; exact Outside.refl _ _ _ _)
  refine wp_logicS (.inl rfl) (VG.Proof.Mont.X86.Rt.readSrc_ptr hw.full.rt P
    (d := 0) (by simp only [arr, offset_array, Width.words]
                 unfold VG.Proof.Rsa.X86.Keys.S at fit; omega)) fun x X => ?_
  refine wp_logicS (.inl rfl) rfl fun y Y => ?_
  have K : Keeps [.eax, .edx, .ebp] s y :=
    ((Kv.mono (by decide)).trans (Kw.mono (by decide))).trans
      ((X.keeps.mono (by decide)).trans (Y.keeps.mono (by decide)))
  have memory : y.mem = s.mem := Y.mem.trans (X.mem.trans (mw.trans mv))
  have hy := h.keep K (by rw [memory]; exact Outside.refl _ _ _ _)
  have value : y.gpr .eax = ((1 : BitVec 32) - s.gpr .ebx) &&&
      s.mem.readW (off B (VG.Proof.Rsa.X86.Keys.arr n input)) 32 &&& (1 : BitVec 32) := by
    rw [Y.gpr, X.gpr, Kw.1 _ (by decide), V.gpr, U.gpr, U.other _ (by decide),
      mw, V.mem, U.mem, Nat.add_zero, arr, offset_array, Width.words]
    rfl
  refine WP.mono (store_slot hy (d := kFlag) (by decide) .eax) fun t ⟨ht, O, flag, Kt⟩ => ?_
  rw [memory] at O
  refine ⟨ht, O, ?_, K.trans (Kt.mono (by decide))⟩
  rw [flag, value, VG.Proof.RsaKeyGen.X86.Key.odd_mask _ _ bit,
    ← VG.Proof.RsaKeyGen.X86.Key.num_parity s.mem B h.wpos input]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (kFlag)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

theorem oddModulus_ok {s : State} {B : Addr} {Z n input out : Nat}
    (h : Ws s B Z n 32) (hi : input < 32) (ho : out < 32)
    (ip : 16 ≤ input) :
    WP isa (oddModulus input out) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2, out] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if num s.mem B n input % 2 = 1 ∧ 3 ≤ num s.mem B n input then 1 else 0) ∧
      num t.mem B n out = (if num s.mem B n input % 2 = 1 ∧ 3 ≤ num s.mem B n input then num s.mem B n input else 3) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have fi := h.fit64 hi
  have fc := h.fit64 (j := aT1) (by decide)
  have hf : kFlag + 4 ≤ hdr := by decide
  unfold oddModulus seqs
  refine WP.seq (WP.mono (constant_ok h (by decide) (3 : BitVec 32)) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  change num u.mem B n aT1 = 3 at constant
  have Iu : num u.mem B n input = num s.mem B n input :=
    Ou.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aT1; omega_using [ip]) (by simp) fi
  refine WP.seq (WP.mono (sub_ok hu (by decide) hi (by decide)) fun v ⟨hv, Ov, subtract, bit, Kv⟩ => ?_)
  rw [Iu, constant] at subtract
  have borrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) bit
  have Iv : num v.mem B n input = num s.mem B n input := by
    rw [Ov.num (by simp only [List.mem_singleton]; intro k e; subst k; unfold aT2; omega_using [ip]) (by simp) fi, Iu]
  have Cv : num v.mem B n aT1 = 3 := by rw [Ov.num (by decide) (by simp) fc, constant]
  refine WP.seq (WP.mono (oddFlag_ok hv hi bit) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  rw [Iv] at flag
  have valid : slot w.mem B kFlag =
      if num s.mem B n input % 2 = 1 ∧ 3 ≤ num s.mem B n input then 1 else 0 := by
    by_cases b : (v.gpr .ebx).toNat = 0
    · have ge := borrow.mp b
      by_cases p : num s.mem B n input % 2 = 1
      · simp only [b, ite_true, p] at flag
        simpa [p, ge] using flag
      · have parity : num s.mem B n input % 2 = 0 := by omega_using [p]
        simp only [b, ite_true, parity] at flag
        simpa [p] using flag
    · have ng : ¬3 ≤ num s.mem B n input := fun ge => b (borrow.mpr ge)
      simp only [b, ite_false] at flag
      simpa [ng] using flag
  have bitW : slot w.mem B kFlag ≤ 1 := by rw [valid]; split <;> omega_using []
  have Iw : num w.mem B n input = num s.mem B n input := by
    rw [Ow.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fi, Iv]
  have Cw : num w.mem B n aT1 = 3 := by
    rw [Ow.num (by simp) (by simp only [List.mem_singleton]; intro d e; subst d; exact hf) fc, Cv]
  refine WP.mono (sel_ok hw ho (by decide) hi hf bitW (by
    by_cases e : out = aT1
    · right; rw [e]; unfold aT1; omega_using [ip]
    · exact Or.inl e)) fun t ⟨ht, Ot, selected, Kt⟩ => ?_
  refine ⟨ht, (((Ou.join Ov (js := [aT1, aT2, out]) (ds := [])).join Ow
    (js := [aT1, aT2, out]) (ds := [kFlag])).join Ot
    (js := [aT1, aT2, out]) (ds := [kFlag])), ?_, ?_,
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  · rw [Ot.slot hf (by simp), valid]
  · rw [selected, valid, Iw, Cw]
    by_cases p : num s.mem B n input % 2 = 1 ∧ 3 ≤ num s.mem B n input <;> simp [p]

end VG.Proof.RsaKeyGen.X86.KeyRuntime
