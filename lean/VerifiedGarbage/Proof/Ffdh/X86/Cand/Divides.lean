module

import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialDivisor
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Power
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Spec.Dsa

/-!
# The FFDH candidate on i686: divisibility by a small prime

`divides x prime inv` runs RSA's whole-word Montgomery trial division
(`Trial.divisor`) on a wide slot, in a frame of 20 bytes that holds the
slot's end: `eax` is one exactly when the prime divides the number
(`divides_ok`). The frame lies below `esp`, apart from the working space.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The words of a number read from its own address. -/
theorem val32_rebase (m : Mem) (base : Addr) (o : Nat) : ∀ n d,
    val32 m (off base o) d n = val32 m base (o + d) n
  | 0, _ => rfl
  | n + 1, d => by
    rw [val32, val32, val32_rebase m base o n (d + 4), Nat.add_assoc]
    have e : w32 m (off base o) d = w32 m base (o + d) := by
      show (m.readW (off (off base o) d) 32).toNat = (m.readW (off base (o + d)) 32).toNat
      rw [off, off, off, VG.Offset.add_add]
    rw [e]

theorem cwc_two (len : Nat) : cwc len .wide = 2 * mw len := by
  simp only [cwc, bc]; omega_arith

/-- `eax` the address of wide slot `j`, and `ecx` its end. -/
theorem bounds_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27)
    (k : ∀ t, t.mem = s.mem → Keeps [.eax, .ecx, .edx] s t →
      (t.gpr .eax).toNat = base.toNat + lo len (.slot .wide j) →
      t.gpr .ecx = t.gpr .eax + BitVec.ofNat 32 (bc len .wide) → WP isa (.block is) t Q) :
    WP isa (.block (bounds (.slot .wide j) ++ is)) s Q := by
  have bl := h.bytes_lt
  have f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  unfold bounds
  simp only [List.append_assoc]
  refine ptrTo_ok (r := .eax) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_arith)
    fun u Ku mu pu => ?_
  have hu : In Ex base bytes len args u := h.regs (Ku.mono (by decide) : Keeps [.eax, .edx] s u) mu
  refine cntTo_ok (n := one .wide) hu.width h.upper' (by decide) fun u₁ K₁ m₁ c₁ => ?_
  refine wp_addS rfl fun t U _ => k t (by rw [U.mem, m₁, mu]) ((Ku.mono (by decide)).trans ((K₁.mono (by decide)).trans
    (U.keeps.mono (by decide)))) ?_ ?_
  · have := bc_ge h.lower' .wide
    have : base.toNat + lo len (.slot .wide j) < 2 ^ 32 := by omega_arith
    rw [U.other _ (by decide), K₁.1 _ (by decide), pu, Nat.mod_eq_of_lt this]
  · rw [U.gpr, U.other _ (by decide), c₁, cb1, BitVec.add_comm]

/-- A stack argument read after a write below `esp`. -/
theorem arg_after (h : In Ex base bytes len args s) {t : State} {i : Nat} (hi : i < 18)
    (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (F : Frame (frameR base (s.gpr .esp) []) s.mem t.mem) :
    readSrc t (.mem (VG.Impl.Bignum.X86.PublicRt.argAt 0 i)) = some (args i) := by
  have R := h.arg hi
  have top := h.top
  have hE := (s.gpr .esp).isLt
  have low := h.room.low
  have ea : t.ea (VG.Impl.Bignum.X86.PublicRt.argAt 0 i) = s.ea (VG.Impl.Bignum.X86.PublicRt.argAt 0 i) := by
    simp only [State.ea, VG.Impl.Bignum.X86.PublicRt.argAt, at_, sp]
  have eaS : s.ea (VG.Impl.Bignum.X86.PublicRt.argAt 0 i) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
    simp only [VG.Impl.Bignum.X86.PublicRt.argAt, at_]
    rw [ea_mk, addr_eq (by omega_arith)]
    simp only [Nat.mul_zero, Nat.add_zero]
  change t.load32 (t.ea _) = _
  change s.load32 (s.ea _) = _ at R
  rw [ea]
  simp only [State.load32, rd, wr] at R ⊢
  split at R
  · rename_i hin
    simp only [hin, ↓reduceIte]
    rw [F.readW (r := ⟨s.ea (VG.Impl.Bignum.X86.PublicRt.argAt 0 i), 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [frameR, List.map_nil, List.mem_singleton] at hr
      subst hr
      rw [eaS]
      simp only [below]
      rw [VG.X86.Taint.sub_setWidth (by omega_arith)]
      exact Offset.disjoint_below _ (by omega_arith)) (by decide)]
    exact R
  · cases R

/-- `eax` one if `prime` divides wide slot `j`, else zero, for `inv = −prime⁻¹ mod 2³²`. -/
theorem divides_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {prime inv : Nat}
    (p3 : 3 ≤ prime) (p65 : prime ≤ 65537) (podd : prime % 2 = 1) (pinv : (prime * inv + 1) % 2 ^ 32 = 0)
    (invl : inv < 2 ^ 32) :
    WP isa (divides (.slot .wide j) prime inv) s fun t => In Ex base bytes len args t ∧
      Frame (frameR base (s.gpr .esp) []) s.mem t.mem ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (sv s.mem base len .wide j % prime = 0)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have bl := h.bytes_lt
  have f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have low := h.room.low
  have top := h.top
  have bw := bc_eq_cwc len .wide
  have c2 := cwc_two len
  have hE := (s.gpr .esp).isLt
  have pl : prime < 2 ^ 32 := by omega_arith
  have lw := h.lower'
  have mwp : 8 ≤ mw len := by simp only [mw, Spec.Rsa.modulusWords]; omega_arith
  unfold divides
  rw [show bounds (.slot .wide j) = bounds (.slot .wide j) ++ [] from (List.append_nil _).symm]
  refine WP.seq (bounds_ok (is := []) h hj fun u mu Ku au cu => WP.block_nil ?_)
  have spu : u.gpr .esp = s.gpr .esp := Ku.1 _ (by decide)
  -- The frame's word holding the end, and the number's address.
  obtain ⟨A, hA⟩ : ∃ A : Addr, A = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : BitVec 32, u.gpr .eax = P := ⟨_, rfl⟩
  rw [hP] at au cu
  have s20 : (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20 :=
    VG.X86.Taint.sub_setWidth (by omega_arith)
  have s40 : (s.gpr .esp - BitVec.ofNat 32 96).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 96 :=
    VG.X86.Taint.sub_setWidth (by omega_arith)
  have addrA : addr (s.gpr .esp - BitVec.ofNat 32 20) 4 = A := by
    rw [addr_eq (by rw [VG.X86.sub_toNat (by omega_arith)]; omega_arith), s20, hA]
    rw [show (4 : Nat) = 20 - 16 from rfl, ← VG.Offset.sub_ofNat_eq _ (by decide : 16 ≤ 20)]
  have inFrame : (⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ : Region).Contains A 4 := by
    rw [s20, hA]; exact Offset.contains_below _ (by decide) (by decide) (by decide)
  have inBelow : (below (s.gpr .esp) 96).Contains A (32 / 8) := by
    simp only [below]; rw [s40, hA]; exact Offset.contains_below _ (by decide) (by decide) (by decide)
  have PA : byteAddr P = off base (lo len (.slot .wide j)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, au]
    have := base.isLt
    omega_arith
  have Fw : ∀ v : BitVec 32, Frame (frameR base (s.gpr .esp) []) s.mem (s.mem.writeW A v) := fun v =>
    (Frame.refl _ _).writeW (List.mem_singleton_self _) v inBelow
  refine WP.seq (WP.mono (WP.frameAlloc (bytes := 20) (Q := fun t => t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.mem = s.mem.writeW A (P + BitVec.ofNat 32 (bc len .wide)) ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (sv s.mem base len .wide j % prime = 0)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t) (by decide) (by decide)
    (by decide) (by rw [spu]; omega_arith) (NoSp.of_all (by rfl)) ?_) fun t ht => ?_)
  · -- The body, from the frame's allocation.
    have a0 : (allocFrame 20 u).gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by rw [allocFrame_esp, spu]
    refine WP.seq (wp_mov fun a₁ U₁ => ?_)
    have eaA : a₁.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) = A := by
      rw [show a₁.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) = addr (a₁.gpr .esp) 4 from rfl, U₁.other _ (by decide), a0,
        addrA]
    refine wp_storeS eaA ⟨_, by rw [U₁.wr, allocFrame_wr]; exact List.mem_cons_self .., by
      rw [spu]; exact inFrame⟩ fun a₂ M₂ => ?_
    refine wp_movi fun a₃ U₃ => wp_movi fun a₄ U₄ => wp_movi fun a₅ U₅ => WP.block_nil ?_
    have K₅ : Keeps [.ebx, .esi, .ebp, .edi] (allocFrame 20 u) a₅ :=
      (U₁.keeps.mono (by decide)).trans ((M₂.keeps _).trans ((U₃.keeps.mono (by decide)).trans
        ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide)))))
    have m₅ : a₅.mem = s.mem.writeW A (P + BitVec.ofNat 32 (bc len .wide)) := by
      rw [U₅.mem, U₄.mem, U₃.mem, M₂.mem, U₁.other _ (by decide), allocFrame_gpr _ _ (by decide), cu, U₁.mem,
        allocFrame_mem, mu]
    have sp₅ : a₅.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by rw [K₅.1 _ (by decide), a0]
    have wsIn : (⟨base, bytes⟩ : Region) ∈ a₅.wr := by
      rw [K₅.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ (Ku.2.2 ▸ h.ws.wr)
    have hw₅ : Ws a₅ base bytes := ⟨wsIn, nw⟩
    refine WP.mono (VG.Proof.RsaKeyGen.X86.Trial.divisor_ok a₅ P (mw len) 4 (by simp only [mw, Spec.Rsa.modulusWords]; omega_arith)
      (by omega_arith) (by rw [au]; omega_arith) (fun i hi => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
      fun t ⟨E, Mt, Kt⟩ => ?_
    · rw [PA, off, Offset.add_add, ← off]
      exact ws_read hw₅ (by omega_arith)
    · rw [sp₅, addrA]
      exact ⟨_, List.mem_append_right _ (by rw [K₅.2.2, allocFrame_wr]; exact List.mem_cons_self ..),
        by rw [spu]; exact inFrame⟩
    · rw [sp₅, addrA, m₅, Mem.readW_writeW_self32, show bc len .wide = 4 * (2 * mw len) by simp only [bc]; omega_arith]
    · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.other _ (by decide), M₂.keeps [] |>.1 _ (by simp), U₁.gpr,
        allocFrame_gpr _ _ (by decide), hP]
    · exact U₅.gpr
    · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pl]; exact p3
    · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pl]; exact p65
    · rw [U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt pl]; exact podd
    · rw [U₅.other _ (by decide), U₅.other _ (by decide), U₄.gpr, U₄.other _ (by decide), U₃.gpr, BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt pl, Nat.mod_eq_of_lt invl]
      exact pinv
    · -- After the division.
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [freed_esp, Kt.1 _ (by decide), sp₅, BitVec.sub_add_cancel]
      · rw [freed_rd, Kt.2.1, K₅.2.1, allocFrame_rd, Ku.2.1]
      · rw [freed_wr, Kt.2.2, K₅.2.2, allocFrame_wr, List.tail_cons, Ku.2.2]
      · rw [freed_mem, Mt, m₅]
      · rw [freed_gpr _ _ (by decide), E, U₅.other _ (by decide), U₄.other _ (by decide), U₃.gpr,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt pl, m₅, PA, val32_rebase, Nat.add_zero, ← c2]
        rw [frameR_val32 (d := lo len (.slot .wide j)) (k := cwc len .wide) (Fw _) (h.room) nw (by omega_arith)
          (fun _ h => nomatch h) (fun _ h => nomatch h)]
      · refine ⟨fun r hr => ?_, ?_, ?_⟩
        · have e : r = .esp := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
            cases r <;> simp_all
          subst e
          rw [freed_esp, Kt.1 _ (by decide), sp₅, BitVec.sub_add_cancel]
        · rw [freed_rd, Kt.2.1, K₅.2.1, allocFrame_rd, Ku.2.1]
        · rw [freed_wr, Kt.2.2, K₅.2.2, allocFrame_wr, List.tail_cons, Ku.2.2]
  · obtain ⟨spt, rdt, wrt, mt, et, Kt⟩ := ht
    have Ft : Frame (frameR base (s.gpr .esp) []) s.mem t.mem := by rw [mt]; exact Fw _
    refine wp_movS (arg_after h (by decide) spt rdt wrt Ft) fun t' U _ => WP.block_nil ?_
    have K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t' := by
      refine ⟨fun r hr => ?_, U.rd.trans Kt.2.1, U.wr.trans Kt.2.2⟩
      by_cases e : r = .edi
      · subst e; rw [U.gpr]; exact h.edi_eq
      · rw [U.other _ e]
        by_cases e' : r = .esp
        · subst e'; exact spt
        · exact absurd (by cases r <;> simp_all) hr
    have F' : Frame (frameR base (s.gpr .esp) []) s.mem t'.mem := by rw [U.mem]; exact Ft
    refine ⟨h.keepF K' (by decide) (by decide) F' (fun _ h => nomatch h), F', ?_, K'⟩
    rw [U.other _ (by decide), et]

end VG.Proof.Ffdh.X86.Cand
