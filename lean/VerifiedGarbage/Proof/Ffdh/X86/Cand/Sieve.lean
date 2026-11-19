module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStep
import VerifiedGarbage.Proof.Framework.X86.SymFrame
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Ffdh.X86.Cand.Base
import VerifiedGarbage.Proof.Ffdh.X86.Stages
public import VerifiedGarbage.Impl.Ffdh.X86.Candidate
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialDivisor

/-! ### `Ffdh.X86.Cand.Divides`, which this module and modules that import it used -/

section

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
    obtain e : w32 m (off base o) d = w32 m base (o + d) := by
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
  obtain f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  unfold bounds
  simp only [List.append_assoc]
  refine ptrTo_ok (r := .eax) (t := .edx) (by decide) (by decide) h.edi h.width h.upper' (by omega_arith)
    fun u Ku mu pu => ?_
  obtain hu : In Ex base bytes len args u := h.regs (Ku.mono (by decide) : Keeps [.eax, .edx] s u) mu
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
  obtain R := h.arg hi
  have top := h.top
  obtain hE := (s.gpr .esp).isLt
  have low := h.room.low
  obtain ea : t.ea (VG.Impl.Bignum.X86.PublicRt.argAt 0 i) = s.ea (VG.Impl.Bignum.X86.PublicRt.argAt 0 i) := by
    simp only [State.ea, VG.Impl.Bignum.X86.PublicRt.argAt, at_, sp]
  obtain eaS : s.ea (VG.Impl.Bignum.X86.PublicRt.argAt 0 i) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
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
  obtain f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have low := h.room.low
  have top := h.top
  obtain bw := bc_eq_cwc len .wide
  obtain c2 := cwc_two len
  obtain hE := (s.gpr .esp).isLt
  obtain pl : prime < 2 ^ 32 := by omega_arith
  have lw := h.lower'
  obtain mwp : 8 ≤ mw len := by simp only [mw, Spec.Rsa.modulusWords]; omega_arith
  unfold divides
  rw [show bounds (.slot .wide j) = bounds (.slot .wide j) ++ [] from (List.append_nil _).symm]
  refine WP.seq (bounds_ok (is := []) h hj fun u mu Ku au cu => WP.block_nil ?_)
  obtain spu : u.gpr .esp = s.gpr .esp := Ku.1 _ (by decide)
  -- The frame's word holding the end, and the number's address.
  obtain ⟨A, hA⟩ : ∃ A : Addr, A = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 16 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : BitVec 32, u.gpr .eax = P := ⟨_, rfl⟩
  rw [hP] at au cu
  obtain s20 : (s.gpr .esp - BitVec.ofNat 32 20).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 20 :=
    VG.X86.Taint.sub_setWidth (by omega_arith)
  obtain s40 : (s.gpr .esp - BitVec.ofNat 32 96).setWidth 64 = (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 96 :=
    VG.X86.Taint.sub_setWidth (by omega_arith)
  obtain addrA : addr (s.gpr .esp - BitVec.ofNat 32 20) 4 = A := by
    rw [addr_eq (by rw [VG.X86.sub_toNat (by omega_arith)]; omega_arith), s20, hA]
    rw [show (4 : Nat) = 20 - 16 from rfl, ← VG.Offset.sub_ofNat_eq _ (by decide : 16 ≤ 20)]
  obtain inFrame : (⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ : Region).Contains A 4 := by
    rw [s20, hA]; exact Offset.contains_below _ (by decide) (by decide) (by decide)
  obtain inBelow : (below (s.gpr .esp) 96).Contains A (32 / 8) := by
    simp only [below]; rw [s40, hA]; exact Offset.contains_below _ (by decide) (by decide) (by decide)
  obtain PA : byteAddr P = off base (lo len (.slot .wide j)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, au]
    have := base.isLt
    omega_arith
  obtain Fw : ∀ v : BitVec 32, Frame (frameR base (s.gpr .esp) []) s.mem (s.mem.writeW A v) := fun v =>
    (Frame.refl _ _).writeW (List.mem_singleton_self _) v inBelow
  refine WP.seq (WP.mono (WP.frameAllocLocal (bytes := 20) (Q := fun t => t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ Frame (frameR base (s.gpr .esp) []) s.mem t.mem ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (sv s.mem base len .wide j % prime = 0)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t) (by decide) (by decide)
    (by decide) (by rw [spu]; omega_arith) (NoSp.of_all (by rfl))
    (fun _ _ _ ⟨a, b, c, F, e, K⟩ fl => ⟨a, b, c, F.trans (fl.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self .., by rw [spu]; exact below_sub (by decide) (by omega_arith)⟩), e, K⟩) ?_) fun t ht => ?_)
  · -- The body, from the frame's allocation.
    obtain a0 : (allocFrame 20 u).gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by rw [allocFrame_esp, spu]
    refine WP.seq (wp_mov fun a₁ U₁ => ?_)
    obtain eaA : a₁.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) = A := by
      rw [show a₁.ea (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) = addr (a₁.gpr .esp) 4 from rfl, U₁.other _ (by decide), a0,
        addrA]
    refine wp_storeS eaA ⟨_, by rw [U₁.wr, allocFrame_wr]; exact List.mem_cons_self .., by
      rw [spu]; exact inFrame⟩ fun a₂ M₂ => ?_
    refine wp_movi fun a₃ U₃ => wp_movi fun a₄ U₄ => wp_movi fun a₅ U₅ => WP.block_nil ?_
    obtain K₅ : Keeps [.ebx, .esi, .ebp, .edi] (allocFrame 20 u) a₅ :=
      (U₁.keeps.mono (by decide)).trans ((M₂.keeps _).trans ((U₃.keeps.mono (by decide)).trans
        ((U₄.keeps.mono (by decide)).trans (U₅.keeps.mono (by decide)))))
    obtain m₅ : a₅.mem = s.mem.writeW A (P + BitVec.ofNat 32 (bc len .wide)) := by
      rw [U₅.mem, U₄.mem, U₃.mem, M₂.mem, U₁.other _ (by decide), allocFrame_gpr _ _ (by decide), cu, U₁.mem,
        allocFrame_mem, mu]
    obtain sp₅ : a₅.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by rw [K₅.1 _ (by decide), a0]
    obtain wsIn : (⟨base, bytes⟩ : Region) ∈ a₅.wr := by
      rw [K₅.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ (Ku.2.2 ▸ h.ws.wr)
    obtain hw₅ : Ws a₅ base bytes := ⟨wsIn, nw⟩
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
      · rw [freed_mem, Mt, m₅]; exact Fw _
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
  · obtain ⟨spt, rdt, wrt, Ft, et, Kt⟩ := ht
    refine wp_movS (arg_after h (by decide) spt rdt wrt Ft) fun t' U _ => WP.block_nil ?_
    obtain K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t' := by
      refine ⟨fun r hr => ?_, U.rd.trans Kt.2.1, U.wr.trans Kt.2.2⟩
      by_cases e : r = .edi
      · subst e; rw [U.gpr]; exact h.edi_eq
      · rw [U.other _ e]
        by_cases e' : r = .esp
        · subst e'; exact spt
        · exact absurd (by cases r <;> simp_all) hr
    obtain F' : Frame (frameR base (s.gpr .esp) []) s.mem t'.mem := by rw [U.mem]; exact Ft
    refine ⟨h.keepF K' (by decide) (by decide) F' (fun _ h => nomatch h), F', ?_, K'⟩
    rw [U.other _ (by decide), et]

end VG.Proof.Ffdh.X86.Cand

end

end

/-!
# The FFDH candidate on i686: RSA's small-prime sieve

`sieve x` runs RSA's sieve loop (`Sieve.loop`) over a wide slot, in a frame
of its five words: the slot's address and end, the table's cursor, the
count of primes (512 up to 1024 bits, 1024 above) and the hit. `eax` is
`trialPrefix` of the number for that count (`sieve_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86.Cand

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Ffdh.X86
open VG.Impl.Ffdh.X86.Candidate
open VG.Proof.RsaKeyGen.X86.Sieve (Geometry StackContext Context StateAt)

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The count of primes the sieve tries for `bits` bits. -/
def sieveCount (bits : Nat) : Nat := if bits ≤ 1024 then 512 else 1024

/-- RSA's table of primes and their inverses, at `T`. -/
structure Table (T : BitVec 32) (sp : BitVec 32) (s : State) : Prop where
  sym : s.syms VG.Impl.RsaKeyGen.TrialTable32.symbol = T
  read : ∀ i < 1024, ∀ d ∈ [0, 4], InRegions (s.rd ++ s.wr) (addr (T + BitVec.ofNat 32 (8 * i)) d) 4
  words : ∀ i < 1024, s.mem.readW (T.setWidth 64 + BitVec.ofNat 64 (8 * i)) 64 =
    BitVec.ofNat 64 (VG.Impl.RsaKeyGen.TrialTable32.entry i)
  fit : T.toNat + 8192 ≤ 2 ^ 32
  far : Region.Disjoint ⟨T.setWidth 64, 8192⟩ (below sp 96)

/-- The count computed from `bits` in `edx`. -/
theorem countBlock_ok {is : List Instr} {Q : State → Prop} (h : In Ex base bytes len args s) {bits : Nat}
    (hb : w32 s.mem base bitsOff = bits)
    (k : ∀ t, t.mem = s.mem → Keeps [.edx] s t → t.gpr .edx = BitVec.ofNat 32 (sieveCount bits) →
      WP isa (.block is) t Q) :
    WP isa (.block (([.mov .edx (.mem (sc bitsOff)), .alu .cmp .edx (.imm 1025), .alu .sbb .edx (.reg .edx),
      .alu .and .edx (.imm 0xFFFFFE00), .alu .add .edx (.imm 1024)] : List Instr) ++ is)) s Q := by
  obtain bl : bits < 2 ^ 32 := by rw [← hb]; exact (s.mem.readW _ 32).isLt
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (hdr_read h (d := bitsOff) ⟨.inl ⟨by decide, by decide⟩, by decide⟩) fun u₁ U₁ _ => ?_
  refine wp_cmpi fun u₂ F₂ c₂ _ => wp_sbb_self c₂ fun u₃ U₃ => ?_
  refine wp_andi fun u₄ U₄ => wp_addi fun u₅ U₅ => k u₅ ?_ ?_ ?_
  · rw [U₅.mem, U₄.mem, U₃.mem, F₂.mem, U₁.mem]
  · exact (U₁.keeps.trans (F₂.keeps _)).trans ((U₃.keeps.trans U₄.keeps).trans U₅.keeps)
  · have e1 : (u₁.gpr .edx).toNat = bits := by
      rw [U₁.gpr, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bl]
    rw [U₅.gpr, U₄.gpr, U₃.gpr, e1, show (1025 : BitVec 32).toNat = 1025 from rfl]
    unfold sieveCount
    by_cases small : bits ≤ 1024
    · rw [ite_eq_left_iff.mpr (fun h => absurd small h), show decide (bits < 1025) = true from decide_eq_true (by omega_arith)]
      decide
    · rw [ite_eq_right_iff.mpr (fun h => absurd h small), show decide (bits < 1025) = false from decide_eq_false (by omega_arith)]
      decide

theorem trialPrefix_sieveCount {c bits : Nat} (hc : 8161 < c) :
    VG.Proof.RsaKeyGen.trialPrefix c (sieveCount bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
  obtain oc : ∀ b b', Spec.RsaKeyGen.trialPrimes b = Spec.RsaKeyGen.trialPrimes b' →
      Spec.RsaKeyGen.obviouslyComposite b c = Spec.RsaKeyGen.obviouslyComposite b' c := by
    intro b b' e; unfold Spec.RsaKeyGen.obviouslyComposite; rw [e]
  by_cases small : bits ≤ 1024
  · have := VG.Proof.RsaKeyGen.trialPrefix_spec (w := 16) hc
    simp only [show (16 : Nat) ≤ 16 from Nat.le_refl _, ↓reduceIte] at this
    simp only [sieveCount, small, ↓reduceIte, this]
    exact oc _ _ (by simp only [Spec.RsaKeyGen.trialPrimes]; split <;> split <;> omega_arith)
  · have := VG.Proof.RsaKeyGen.trialPrefix_spec (w := 17) hc
    simp only [show ¬ (17 : Nat) ≤ 16 by decide, ↓reduceIte] at this
    simp only [sieveCount, small, ↓reduceIte, this]
    exact oc _ _ (by simp only [Spec.RsaKeyGen.trialPrimes]; split <;> split <;> omega_arith)

/-- The stack below `sp − 20`, for four bytes, within the 96 below `sp`. -/
theorem below_frames {sp : BitVec 32} (low : 96 ≤ sp.toNat) :
    Region.Sub (below (sp - BitVec.ofNat 32 20) 4) (below sp 96) ∧
      Region.Sub ⟨(sp - BitVec.ofNat 32 20).setWidth 64, 20⟩ (below sp 96) := by
  obtain e24 : (sp - BitVec.ofNat 32 20 - BitVec.ofNat 32 4).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 24 := by
    rw [BitVec.sub_sub, show BitVec.ofNat 32 20 + BitVec.ofNat 32 4 = BitVec.ofNat 32 24 from rfl]
    exact VG.X86.Taint.sub_setWidth (by omega_arith)
  obtain e20 : (sp - BitVec.ofNat 32 20).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 20 :=
    VG.X86.Taint.sub_setWidth (by omega_arith)
  obtain e40 : (sp - BitVec.ofNat 32 96).setWidth 64 = sp.setWidth 64 - BitVec.ofNat 64 96 :=
    VG.X86.Taint.sub_setWidth (by omega_arith)
  simp only [below]
  rw [e24, e20, e40]
  exact ⟨Offset.sub_below _ (by decide) (by decide), Offset.sub_below _ (by decide) (by decide)⟩

/-- The sieve's geometry for the number at `P` below `sp`, RSA's table at `T`, for `bits` bits. -/
abbrev sieveGeo (sp P T : BitVec 32) (len bits : Nat) : Geometry := ⟨sp - BitVec.ofNat 32 20, P, T, mw len, sieveCount bits⟩

theorem sieveGeo_valid (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {T P : BitVec 32}
    (TT : Table T (s.gpr .esp) s) (au : P.toNat = base.toNat + lo len (.slot .wide j)) (bits : Nat) :
    (sieveGeo (s.gpr .esp) P T len bits).Valid ∧
      (sieveGeo (s.gpr .esp) P T len bits).candidateRegion.Disjoint (below (s.gpr .esp) 96) := by
  have bl := h.bytes_lt
  obtain f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have low := h.room.low
  have lw := h.lower'
  have up := h.upper'
  obtain mwu : mw len ≤ 128 := by simp only [mw, Spec.Rsa.modulusWords]; omega_arith
  obtain mwp : 8 ≤ mw len := by simp only [mw, Spec.Rsa.modulusWords]; omega_arith
  have bc8 : bc len .wide = 8 * mw len := rfl
  obtain frames := below_frames low
  obtain PA : byteAddr P = off base (lo len (.slot .wide j)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, au]
    have := base.isLt
    omega_arith
  obtain wsFar : Region.Disjoint (sieveGeo (s.gpr .esp) P T len bits).candidateRegion (below (s.gpr .esp) 96) := by
    obtain sub : Region.Sub (sieveGeo (s.gpr .esp) P T len bits).candidateRegion ⟨base, bytes⟩ := by
      show Region.Sub ⟨P.setWidth 64, 8 * mw len⟩ _
      rw [show P.setWidth 64 = byteAddr P from rfl, PA]
      exact Offset.sub_base _ (by omega_arith)
    exact (h.room.apart.symm.sub_left sub)
  refine ⟨⟨by show 0 < mw len; omega_arith, mwu, ?_, ?_, ?_, TT.fit, ?_, ?_⟩, wsFar⟩
  · show 0 < sieveCount bits; unfold sieveCount; split <;> decide
  · show sieveCount bits ≤ 1024; unfold sieveCount; split <;> decide
  · show P.toNat + 8 * mw len ≤ 2 ^ 32; omega_arith
  · exact wsFar.sub_right frames.2
  · exact TT.far.sub_right frames.2

/-- The sieve's frame set up, from the number's address and end and the count in `eax`, `ecx` and
`edx`: the state RSA's sieve loop starts from. -/
theorem sieveSetup_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {T : BitVec 32}
    (TT : Table T (s.gpr .esp) s) {bits : Nat} {u' : State} {P : BitVec 32}
    (au : P.toNat = base.toNat + lo len (.slot .wide j)) (eaU : u'.gpr .eax = P)
    (ecU : u'.gpr .ecx = P + BitVec.ofNat 32 (bc len .wide)) (du' : u'.gpr .edx = BitVec.ofNat 32 (sieveCount bits))
    (Ku' : Keeps [.eax, .ecx, .edx] s u') (mU : u'.mem = s.mem) (Su : u'.syms = s.syms) :
    WP isa sieveSetup (allocFrame 20 u') fun c₂ =>
      StateAt (sieveGeo (s.gpr .esp) P T len bits) (sv s.mem base len .wide j) 0 (sieveCount bits) c₂ ∧
      c₂.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 ∧ c₂.rd = s.rd ∧
      c₂.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ :: s.wr ∧
      Frame [below (s.gpr .esp) 96] s.mem c₂.mem := by
  have bl := h.bytes_lt
  obtain f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have low := h.room.low
  obtain bw := bc_eq_cwc len .wide
  obtain c2 := cwc_two len
  obtain hE := (s.gpr .esp).isLt
  have lw := h.lower'
  have up := h.upper'
  have bc8 : bc len .wide = 8 * mw len := rfl
  obtain frames := below_frames low
  obtain spU : u'.gpr .esp = s.gpr .esp := Ku'.1 _ (by decide)
  have rdU : u'.rd = s.rd := Ku'.2.1
  have wrU : u'.wr = s.wr := Ku'.2.2
  obtain PA : byteAddr P = off base (lo len (.slot .wide j)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [byteAddr, off, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, au]
    have := base.isLt
    omega_arith
  let g : Geometry := sieveGeo (s.gpr .esp) P T len bits
  have gw : g.w = mw len := rfl
  obtain ⟨v, wsFar⟩ := sieveGeo_valid h hj TT au bits
  obtain candidateFar : g.candidateRegion.Disjoint (below g.sp 4) := wsFar.sub_right frames.1
  obtain tableFar : g.tableRegion.Disjoint (below g.sp 4) := TT.far.sub_right frames.1
  obtain gsp : g.sp.toNat = (s.gpr .esp).toNat - 20 := VG.X86.sub_toNat (by omega_arith)
  obtain sa : (allocFrame 20 u').gpr .esp = g.sp := by rw [allocFrame_esp, spU]
  obtain SC : StackContext g.sp (allocFrame 20 u') := by
    refine ⟨⟨?_, ?_⟩, sa⟩
    · rw [allocFrame_wr, spU]; exact List.mem_cons_self ..
    · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := g.sp.isLt; omega_arith)]; omega_arith
  obtain wsA : Ws (allocFrame 20 u') base bytes :=
    ⟨by rw [allocFrame_wr, wrU]; exact List.mem_cons_of_mem _ h.ws.wr, nw⟩
  have PS : P.setWidth 64 = off base (lo len (.slot .wide j)) := PA
  obtain C₀ : Context g (sv s.mem base len .wide j) (allocFrame 20 u') := by
    refine ⟨SC, fun i hi => ?_, fun i hi d hd => ?_, fun i hi => ?_, ?_⟩
    · show InRegions _ (off (P.setWidth 64) (4 * i)) 4
      rw [PS, off, VG.Offset.add_add, ← off]
      exact ws_read wsA (by omega_arith)
    · rw [allocFrame_rd, allocFrame_wr, rdU, wrU]
      obtain ⟨r, hr, hc⟩ := TT.read i hi d hd
      refine ⟨r, ?_, hc⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact List.mem_append_left _ hr
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
    · rw [allocFrame_mem, mU]; exact TT.words i hi
    · show val32 _ (P.setWidth 64) 0 (2 * mw len) = _
      rw [allocFrame_mem, mU, PS, val32_rebase, Nat.add_zero, ← c2]
  obtain ea₀ : (allocFrame 20 u').gpr .eax = P := by rw [allocFrame_gpr _ _ (by decide), eaU]
  obtain ec₀ : (allocFrame 20 u').gpr .ecx = g.ending := by
    rw [allocFrame_gpr _ _ (by decide), ecU, bc8]; rfl
  obtain ed₀ : (allocFrame 20 u').gpr .edx = BitVec.ofNat 32 g.limit := by
    rw [allocFrame_gpr _ _ (by decide), du']
  obtain gsp4 : 4 ≤ g.sp.toNat := by omega_arith
  -- The three stores of the geometry.
  obtain stores : WP isa (.block [.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 0) .eax,
      .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .ecx, .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 12) .edx])
      (allocFrame 20 u') fun b => Context g (sv s.mem base len .wide j) b ∧
        b.mem.readW (off (g.sp.setWidth 64) 0) 32 = P ∧ b.mem.readW (off (g.sp.setWidth 64) 4) 32 = g.ending ∧
        b.mem.readW (off (g.sp.setWidth 64) 12) 32 = BitVec.ofNat 32 g.limit ∧
        Outside (g.sp.setWidth 64) 0 20 (allocFrame 20 u').mem b.mem ∧ Keeps [] (allocFrame 20 u') b := by
    change WP isa (.block ([.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 0) .eax] ++
      ([.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 4) .ecx] ++ [.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 12) .edx]))) _ _
    refine WP.block_append (WP.mono (SC.store 0 (by decide) .eax) fun b₁ ⟨M₁, O₁, K₁, S₁⟩ => ?_)
    refine WP.block_append (WP.mono (S₁.store 4 (by decide) .ecx) fun b₂ ⟨M₂, O₂, K₂, S₂⟩ => ?_)
    refine WP.mono (S₂.store 12 (by decide) .edx) fun b₃ ⟨M₃, O₃, K₃, S₃⟩ => ?_
    obtain K : Keeps [] (allocFrame 20 u') b₃ := (K₁.trans K₂).trans K₃
    obtain O : Outside (g.sp.setWidth 64) 0 20 (allocFrame 20 u').mem b₃.mem :=
      ((O₁.mono (by decide) (by decide)).trans (O₂.mono (by decide) (by decide))).trans
        (O₃.mono (by decide) (by decide))
    obtain e1 : b₁.gpr .ecx = g.ending := by rw [K₁.1 _ (by simp), ec₀]
    obtain e2 : b₂.gpr .edx = BitVec.ofNat 32 g.limit := by rw [K₂.1 _ (by simp), K₁.1 _ (by simp), ed₀]
    obtain mem : b₃.mem = (((allocFrame 20 u').mem.writeW (off (g.sp.setWidth 64) 0) P).writeW
        (off (g.sp.setWidth 64) 4) g.ending).writeW (off (g.sp.setWidth 64) 12) (BitVec.ofNat 32 g.limit) := by
      rw [M₃, M₂, M₁, ea₀, e1, e2]
    refine ⟨C₀.keep v K (by decide) (VG.Proof.RsaKeyGen.X86.Sieve.outsideStack_frame O), ?_, ?_, ?_, O, K⟩
    · rw [mem, VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide),
        VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · rw [mem, VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]
    · rw [mem, Mem.readW_writeW_self32]
  refine WP.seq (VG.X86.WP.mono_syms stores fun b ⟨Cb, b0, b4, b12, Ob, Kb⟩ Sb => ?_)
  refine WP.seq (WP.mono (symFrame_ok VG.Impl.RsaKeyGen.TrialTable32.symbol b (by rw [Cb.stack.sp]; exact gsp4))
    fun b' R => ?_)
  obtain Cb' := Cb.keepSymbol v R candidateFar tableFar
  obtain b0' := (VG.Proof.RsaKeyGen.X86.Sieve.symbol_stack_word Cb R gsp4 (d := 0) (by decide)).trans b0
  obtain b4' := (VG.Proof.RsaKeyGen.X86.Sieve.symbol_stack_word Cb R gsp4 (d := 4) (by decide)).trans b4
  obtain b12' := (VG.Proof.RsaKeyGen.X86.Sieve.symbol_stack_word Cb R gsp4 (d := 12) (by decide)).trans b12
  obtain eaT : b'.gpr .eax = g.table := by
    rw [R.addr, Sb, show (allocFrame 20 u').syms = u'.syms from rfl, Su]; exact TT.sym
  change WP isa (.block ([.store (VG.Impl.RsaKeyGen.X86.Sieve.slot 8) .eax] ++
    [.mov .eax (.imm 0), .store (VG.Impl.RsaKeyGen.X86.Sieve.slot 16) .eax])) b' _
  refine WP.block_append (WP.mono (Cb'.stack.store 8 (by decide) .eax) fun c₁ ⟨M₁, O₁, K₁, S₁⟩ =>
    WP.mono (S₁.literal 16 (by decide) 0#32) fun c₂ ⟨M₂, O₂, K₂, S₂⟩ => ?_)
  obtain Kc : Keeps [.eax] b' c₂ := (K₁.mono (by decide)).trans K₂
  obtain Oc : Outside (g.sp.setWidth 64) 0 20 b'.mem c₂.mem :=
    (O₁.mono (by decide) (by decide)).trans (O₂.mono (by decide) (by decide))
  obtain memc : c₂.mem = (b'.mem.writeW (off (g.sp.setWidth 64) 8) g.table).writeW (off (g.sp.setWidth 64) 16) 0#32 := by
    rw [M₂, M₁, eaT]
  obtain H : StateAt g (sv s.mem base len .wide j) 0 g.limit c₂ := by
    refine ⟨Cb'.keep v Kc (by decide) (VG.Proof.RsaKeyGen.X86.Sieve.outsideStack_frame Oc), ?_, ?_, ?_, ?_⟩
    · rw [memc, VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide),
        VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide)]
      exact b0'
    · rw [memc, VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide),
        VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide)]
      exact b4'
    · rw [memc, VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32]
      unfold Geometry.cursor
      rw [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
    · rw [memc, VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide),
        VG.Proof.RsaKeyGen.X86.Sieve.stack_write_ne (by decide) (by decide) (by decide)]
      exact b12'
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · rw [Kc.1 _ (by decide), R.gpr _ (by decide), Kb.1 _ (by decide), sa]
  · rw [Kc.2.1, R.rd, Kb.2.1, allocFrame_rd, rdU]
  · rw [Kc.2.2, R.wr, Kb.2.2, allocFrame_wr, spU, wrU]
  · have toBelow : ∀ {m m' : Mem}, Frame [g.stackRegion] m m' → Frame [below (s.gpr .esp) 96] m m' :=
      fun F => F.sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_singleton_self _, frames.2⟩
    obtain F₁ : Frame [below (s.gpr .esp) 96] s.mem b.mem := by
      have := toBelow (VG.Proof.RsaKeyGen.X86.Sieve.outsideStack_frame Ob)
      rw [allocFrame_mem, mU] at this; exact this
    obtain F₂ : Frame [below (s.gpr .esp) 96] b.mem b'.mem := by
      have := R.frame
      rw [Cb.stack.sp] at this
      exact this.sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_singleton_self _, frames.1⟩
    exact (F₁.trans F₂).trans (toBelow (VG.Proof.RsaKeyGen.X86.Sieve.outsideStack_frame Oc))

/-- The register outside the seven is `esp`. -/
private theorem esp_of_not_mem (r : Reg) :
    r ∉ [Reg.eax, Reg.ebx, Reg.ecx, Reg.edx, Reg.ebp, Reg.esi, Reg.edi] → r = .esp := by
  cases r <;> decide

/-- A register that is neither `edi` nor `esp` is one of the six. -/
private theorem mem_of_ne_edi_esp (r : Reg) :
    ¬r = .edi → ¬r = .esp → r ∈ [Reg.eax, Reg.ebx, Reg.ecx, Reg.edx, Reg.ebp, Reg.esi] := by
  cases r <;> decide

/-- `eax` RSA's sieve of wide slot `j` for `bits` (in the header) bits: one if a prime of the table's
first `sieveCount bits` divides it. -/
theorem sieve_ok (h : In Ex base bytes len args s) {j : Nat} (hj : j ≤ 27) {T : BitVec 32}
    (TT : Table T (s.gpr .esp) s) {bits : Nat} (hb : w32 s.mem base bitsOff = bits) :
    WP isa (sieve (.slot .wide j)) s fun t => In Ex base bytes len args t ∧
      Frame (frameR base (s.gpr .esp) []) s.mem t.mem ∧
      t.gpr .eax = BitVec.ofNat 32
        (VG.Proof.RsaKeyGen.trialPrefix (sv s.mem base len .wide j) (sieveCount bits)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have bl := h.bytes_lt
  obtain f := slot_fit1 h hj
  rw [cb1] at f
  have nw := h.scratch.nowrap
  have low := h.room.low
  have top := h.top
  obtain bw := bc_eq_cwc len .wide
  obtain c2 := cwc_two len
  obtain hE := (s.gpr .esp).isLt
  have lw := h.lower'
  have up := h.upper'
  obtain mwp : 8 ≤ mw len := by simp only [mw, Spec.Rsa.modulusWords]; omega_arith
  obtain mwu : mw len ≤ 128 := by simp only [mw, Spec.Rsa.modulusWords]; omega_arith
  have bc8 : bc len .wide = 8 * mw len := rfl
  obtain frames := below_frames low
  unfold sieve
  rw [show bounds (.slot .wide j) ++ [.mov .edx (.mem (sc bitsOff)), .alu .cmp .edx (.imm 1025),
      .alu .sbb .edx (.reg .edx), .alu .and .edx (.imm 0xFFFFFE00), .alu .add .edx (.imm 1024)] =
    bounds (.slot .wide j) ++ ([.mov .edx (.mem (sc bitsOff)), .alu .cmp .edx (.imm 1025),
      .alu .sbb .edx (.reg .edx), .alu .and .edx (.imm 0xFFFFFE00), .alu .add .edx (.imm 1024)] ++ []) by simp]
  obtain pre : WP isa (.block (bounds (.slot .wide j) ++ ([.mov .edx (.mem (sc bitsOff)), .alu .cmp .edx (.imm 1025),
      .alu .sbb .edx (.reg .edx), .alu .and .edx (.imm 0xFFFFFE00), .alu .add .edx (.imm 1024)] ++ []))) s
      fun u' => ∃ P : BitVec 32, P.toNat = base.toNat + lo len (.slot .wide j) ∧ u'.gpr .eax = P ∧
        u'.gpr .ecx = P + BitVec.ofNat 32 (bc len .wide) ∧ u'.gpr .edx = BitVec.ofNat 32 (sieveCount bits) ∧
        Keeps [.eax, .ecx, .edx] s u' ∧ u'.mem = s.mem :=
    bounds_ok h hj fun u mu Ku au cu =>
      countBlock_ok (bits := bits) (h.regs Ku mu) (by rw [mu]; exact hb) fun u' mu' Ku' du' => WP.block_nil
        ⟨u.gpr .eax, au, Ku'.1 _ (by decide), by rw [Ku'.1 _ (by decide), cu], du', Ku.trans (Ku'.mono (by decide)),
          by rw [mu', mu]⟩
  refine WP.seq (VG.X86.WP.mono_syms pre fun u' ⟨P, au, eaU, ecU, du', Ku', mU⟩ Su => ?_)
  obtain spU : u'.gpr .esp = s.gpr .esp := Ku'.1 _ (by decide)
  refine WP.seq (WP.mono (WP.frameAllocLocal (bytes := 20) (Q := fun t => t.gpr .esp = s.gpr .esp ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ Frame [below (s.gpr .esp) 96] s.mem t.mem ∧
      t.gpr .eax = BitVec.ofNat 32
        (VG.Proof.RsaKeyGen.trialPrefix (sv s.mem base len .wide j) (sieveCount bits)).toNat ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t) (by decide) (by decide)
    (by decide) (by rw [spU]; omega_arith) (NoSp.of_all (by rfl))
    (fun _ _ _ ⟨a, b, c, F, e, K⟩ fl => ⟨a, b, c, F.trans (fl.sub fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, by rw [spU]; exact below_sub (by decide) (by omega_arith)⟩), e, K⟩) ?_) fun t ht => ?_)
  · -- The frame's body.
    obtain ⟨v, -⟩ := sieveGeo_valid h hj TT au bits
    refine WP.seq (WP.mono (sieveSetup_ok h hj TT au eaU ecU du' Ku' mU Su) fun c₂ ⟨H, spc, rdc, wrc, Fc⟩ => ?_)
    refine WP.mono (VG.Proof.RsaKeyGen.X86.Sieve.loop_full_ok v H) fun t ⟨E, Ot, Kt, _⟩ => ?_
    obtain spT : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 20 := by rw [Kt.1 _ (by decide), spc]
    obtain rdT : t.rd = s.rd := by rw [Kt.2.1, rdc]
    obtain wrT : t.wr = ⟨(s.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩ :: s.wr := by rw [Kt.2.2, wrc]
    obtain Fall : Frame [below (s.gpr .esp) 96] s.mem t.mem := by
      refine Fc.trans ((VG.Proof.RsaKeyGen.X86.Sieve.outsideStack_frame Ot).sub fun r hr => ?_)
      obtain rfl := List.mem_singleton.mp hr; exact ⟨_, List.mem_singleton_self _, (below_frames low).2⟩
    refine ⟨?_, ?_, ?_, Fall, ?_, ?_⟩
    · rw [freed_esp, spT]; exact BitVec.sub_add_cancel _ _
    · rw [freed_rd, rdT]
    · rw [freed_wr, wrT, List.tail_cons]
    · rw [freed_gpr _ _ (by decide), E]
    · refine ⟨fun r hr => ?_, by rw [freed_rd, rdT], by rw [freed_wr, wrT, List.tail_cons]⟩
      obtain e : r = .esp := esp_of_not_mem r hr
      subst e
      rw [freed_esp, spT]; exact BitVec.sub_add_cancel _ _
  · obtain ⟨spt, rdt, wrt, Ft, et, Kt⟩ := ht
    refine wp_movS (arg_after h (by decide) spt rdt wrt Ft) fun t' U _ => WP.block_nil ?_
    obtain K' : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t' := by
      refine ⟨fun r hr => ?_, U.rd.trans Kt.2.1, U.wr.trans Kt.2.2⟩
      by_cases e : r = .edi
      · subst e; rw [U.gpr]; exact h.edi_eq
      · rw [U.other _ e]
        by_cases e' : r = .esp
        · subst e'; exact spt
        · exact absurd (mem_of_ne_edi_esp r e e') hr
    obtain F' : Frame (frameR base (s.gpr .esp) []) s.mem t'.mem := by rw [U.mem]; exact Ft
    refine ⟨h.keepF K' (by decide) (by decide) F' (fun _ h => nomatch h), F', ?_, K'⟩
    rw [U.other _ (by decide), et]

end VG.Proof.Ffdh.X86.Cand
