module

import VerifiedGarbage.Proof.Mont.X86.Sse2.Shape
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.In
public import VerifiedGarbage.Proof.Bignum.X86.RtCall
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.MulArgs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Mont.X86.MulRt

/-! ### `Bignum.X86.CrtRt.Mul`, which only this module used -/

section

/-! # A multiplication by a call, in private CRT at a run-time width

`mulArgs c o a b` stores the arguments of `vg_rsa_mont_mul_at` for the slots
`o`, `a` and `b` of the context `c` (`mulArgs_ok`); `mul c o a b` writes the
Montgomery product of slots `a` and `b` into slot `o`, changing only it,
the callee's range (from slot 1) and the 40 bytes below `esp` (`mul_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (adds_ok frame_store frame_other argAt_alloc)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Proof.Rsa.MontMul (scratchBytes)

/-- `offIn (.slot c j)`: `eax = numBase + j t` from `edx = t`. -/
theorem offIn_ok {s : State} {is : List Instr} {Q : State → Prop} {c : Ctx} {j t : Nat}
    (hedx : s.gpr .edx = BitVec.ofNat 32 t) (ht : t ≤ 2080) (hj : j ≤ 28)
    (kk : ∀ u, Keeps [.eax] s u → u.mem = s.mem → u.gpr .eax = BitVec.ofNat 32 (numBase + j * t) →
      WP isa (.block is) u Q) :
    WP isa (.block (offIn (.slot c j) ++ is)) s Q := by
  simp only [offIn, List.cons_append]
  refine wp_movS rfl fun s₁ u₁ _ => adds_ok (r := .eax) (t := .edx) (by decide) j fun u K m e => ?_
  refine kk u (u₁.keeps.trans K) (by rw [m, u₁.mem]) ?_
  rw [e, u₁.gpr, u₁.other _ (by decide), hedx]
  apply BitVec.eq_of_toNat_eq
  have : j * t ≤ 28 * 2080 := Nat.mul_le_mul hj ht
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, numBase]
  rw [Nat.mod_eq_of_lt (a := t) (by omega_using [ht]), Nat.mod_eq_of_lt (a := j * t) (by omega_using [this])]

theorem mulArgs_ok {f : State} {len : Nat} {c : Ctx} {o a b : Nat} {wsLen : BitVec 32}
    (hr1 : readSrc f (.mem (argAt 9 1)) = some (BitVec.ofNat 32 len))
    (hr17 : readSrc f (.mem (argAt 9 wsLenArg)) = some wsLen)
    (hl : len ≤ 1024) (ho : o ≤ 28) (ha : a ≤ 28) (hb : b ≤ 28)
    (hesp : (f.gpr .esp).toNat + 36 ≤ 2 ^ 32) (hfr : (⟨(f.gpr .esp).setWidth 64, 36⟩ : Region) ∈ f.wr) :
    WP isa (.block (mulArgs c o a b)) f fun g =>
      Keeps [.eax, .edx] f g ∧ Frame [⟨(f.gpr .esp).setWidth 64, 36⟩] f.mem g.mem ∧
      ∀ i < 9, g.mem.readW ((f.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
        callArg (f.gpr .edi) wsLen (bc len c / 8) numBase invOff (lo len (.slot c 1)) (lo len (.slot c o))
          (lo len (.slot c a)) (lo len (.slot c b)) i := by
  have hw := bc_le hl c
  have h8 := bc_dvd len c
  generalize hP : (f.gpr .esp).setWidth 64 = P at hfr ⊢
  simp only [mulArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine widthC_ok hr1 hl fun s₁ K₁ m₁ e₁ => ?_
  have fr : ∀ t : State, t.gpr .esp = f.gpr .esp → t.wr = f.wr → ∀ k, k + 4 ≤ 36 →
      t.ea (at_ .esp k) = P + BitVec.ofNat 64 k ∧ InRegions t.wr (P + BitVec.ofNat 64 k) 4 :=
    fun t he hw' k hk => frame_store (by rw [he, hP]) (by rw [he]; exact hesp) (by rw [hw']; exact hfr) hk
  have sp₁ : s₁.gpr .esp = f.gpr .esp := K₁.1 _ (by decide)
  have edi₁ : s₁.gpr .edi = f.gpr .edi := K₁.1 _ (by decide)
  have hr17₁ : readSrc s₁ (.mem (argAt 9 wsLenArg)) = some wsLen := by
    rw [← hr17]; simp only [readSrc, State.load32, State.ea, argAt, at_, sp₁, m₁, K₁.2.1, K₁.2.2]; rfl
  refine wp_movS hr17₁ fun s₂ u₂ _ => ?_
  have K₂ : Keeps [.eax, .edx] f s₂ := (K₁.mono (by decide)).trans (u₂.keeps.mono (by decide))
  obtain ⟨a₄, w₄⟩ := fr s₂ (K₂.1 _ (by decide)) K₂.2.2 4 (by decide)
  refine wp_storeS a₄ w₄ fun s₃ m₃ => ?_
  obtain ⟨a₀, w₀⟩ := fr s₃ (by rw [m₃.gpr]; exact K₂.1 _ (by decide)) (by rw [m₃.wr]; exact K₂.2.2) 0 (by decide)
  refine wp_storeS a₀ w₀ fun s₄ m₄ => ?_
  have K₄ : Keeps [.eax, .edx] f s₄ := (K₂.trans (m₃.keeps _)).trans (m₄.keeps _)
  refine wp_movS rfl fun s₅ u₅ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₆ u₆ => ?_
  have K₆ : Keeps [.eax, .edx] f s₆ := (K₄.trans (u₅.keeps.mono (by decide))).trans (u₆.keeps.mono (by decide))
  obtain ⟨a₈, w₈⟩ := fr s₆ (K₆.1 _ (by decide)) K₆.2.2 8 (by decide)
  refine wp_storeS a₈ w₈ fun s₇ m₇ => wp_addS rfl fun s₇' u₇' _ => wp_addS rfl fun s₇'' u₇'' _ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => ?_
  have K₈ : Keeps [.eax, .edx] f s₈ :=
    (((K₆.trans (m₇.keeps _)).trans (u₇'.keeps.mono (by decide))).trans (u₇''.keeps.mono (by decide))).trans
      (u₈.keeps.mono (by decide))
  obtain ⟨a₁₂, w₁₂⟩ := fr s₈ (K₈.1 _ (by decide)) K₈.2.2 12 (by decide)
  refine wp_storeS a₁₂ w₁₂ fun s₉ m₉ => wp_movS rfl fun s₁₀ u₁₀ _ => ?_
  have K₁₀ : Keeps [.eax, .edx] f s₁₀ := (K₈.trans (m₉.keeps _)).trans (u₁₀.keeps.mono (by decide))
  obtain ⟨a₁₆, w₁₆⟩ := fr s₁₀ (K₁₀.1 _ (by decide)) K₁₀.2.2 16 (by decide)
  refine wp_storeS a₁₆ w₁₆ fun s₁₁ m₁₁ => ?_
  have K₁₁ : Keeps [.eax, .edx] f s₁₁ := K₁₀.trans (m₁₁.keeps _)
  -- `edx` holds the stride from the two additions on.
  have edxS : s₇''.gpr .edx = BitVec.ofNat 32 (st len c) := by
    rw [u₇''.gpr, u₇'.gpr, m₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), m₄.gpr, m₃.gpr,
      u₂.other _ (by decide), e₁]
    apply BitVec.eq_of_toNat_eq
    have e32 : (32 : BitVec 32).toNat = 32 := rfl
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, e32, st]
    rw [Nat.mod_eq_of_lt (a := bc len c) (by omega_using [hw])]
    omega_using []
  have edx₁₁ : s₁₁.gpr .edx = BitVec.ofNat 32 (st len c) := by
    rw [m₁₁.gpr, u₁₀.other _ (by decide), m₉.gpr, u₈.other _ (by decide), edxS]
  have hst : st len c ≤ 2080 := by simp only [st]; omega_using [hw]
  refine offIn_ok (c := c) (j := 1) edx₁₁ hst (by decide) fun s₁₂ K₁₂ m₁₂ e₁₂ => ?_
  have K₁₂' : Keeps [.eax, .edx] f s₁₂ := K₁₁.trans (K₁₂.mono (by decide))
  obtain ⟨a₂₀, w₂₀⟩ := fr s₁₂ (K₁₂'.1 _ (by decide)) K₁₂'.2.2 20 (by decide)
  refine wp_storeS a₂₀ w₂₀ fun s₁₃ m₁₃ => ?_
  have edx₁₃ : s₁₃.gpr .edx = BitVec.ofNat 32 (st len c) := by rw [m₁₃.gpr, K₁₂.1 _ (by decide), edx₁₁]
  refine offIn_ok (c := c) (j := o) edx₁₃ hst ho fun s₁₄ K₁₄ m₁₄ e₁₄ => ?_
  have K₁₄' : Keeps [.eax, .edx] f s₁₄ := (K₁₂'.trans (m₁₃.keeps _)).trans (K₁₄.mono (by decide))
  obtain ⟨a₂₄, w₂₄⟩ := fr s₁₄ (K₁₄'.1 _ (by decide)) K₁₄'.2.2 24 (by decide)
  refine wp_storeS a₂₄ w₂₄ fun s₁₅ m₁₅ => ?_
  have edx₁₅ : s₁₅.gpr .edx = BitVec.ofNat 32 (st len c) := by rw [m₁₅.gpr, K₁₄.1 _ (by decide), edx₁₃]
  refine offIn_ok (c := c) (j := a) edx₁₅ hst ha fun s₁₆ K₁₆ m₁₆ e₁₆ => ?_
  have K₁₆' : Keeps [.eax, .edx] f s₁₆ := (K₁₄'.trans (m₁₅.keeps _)).trans (K₁₆.mono (by decide))
  obtain ⟨a₂₈, w₂₈⟩ := fr s₁₆ (K₁₆'.1 _ (by decide)) K₁₆'.2.2 28 (by decide)
  refine wp_storeS a₂₈ w₂₈ fun s₁₇ m₁₇ => ?_
  have edx₁₇ : s₁₇.gpr .edx = BitVec.ofNat 32 (st len c) := by rw [m₁₇.gpr, K₁₆.1 _ (by decide), edx₁₅]
  refine offIn_ok (c := c) (j := b) edx₁₇ hst hb fun s₁₈ K₁₈ m₁₈ e₁₈ => ?_
  have K₁₈' : Keeps [.eax, .edx] f s₁₈ := (K₁₆'.trans (m₁₇.keeps _)).trans (K₁₈.mono (by decide))
  obtain ⟨a₃₂, w₃₂⟩ := fr s₁₈ (K₁₈'.1 _ (by decide)) K₁₈'.2.2 32 (by decide)
  refine wp_storeS a₃₂ w₃₂ fun g mg => WP.block_nil ?_
  have edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (bc len c) := by rw [m₄.gpr, m₃.gpr, u₂.other _ (by decide), e₁]
  have eW : s₆.gpr .eax = BitVec.ofNat 32 (bc len c / 8) := by
    rw [u₆.gpr, u₅.gpr, edx₄]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (a := bc len c) (by omega_using [hw]), Nat.mod_eq_of_lt (by omega_using [hw])]
  have mem : g.mem = ((((((((f.mem.writeW (P + BitVec.ofNat 64 4) wsLen).writeW (P + BitVec.ofNat 64 0)
      (f.gpr .edi)).writeW (P + BitVec.ofNat 64 8) (BitVec.ofNat 32 (bc len c / 8))).writeW
      (P + BitVec.ofNat 64 12) (BitVec.ofNat 32 numBase)).writeW (P + BitVec.ofNat 64 16)
      (BitVec.ofNat 32 invOff)).writeW (P + BitVec.ofNat 64 20) (BitVec.ofNat 32 (lo len (.slot c 1)))).writeW
      (P + BitVec.ofNat 64 24) (BitVec.ofNat 32 (lo len (.slot c o)))).writeW (P + BitVec.ofNat 64 28)
      (BitVec.ofNat 32 (lo len (.slot c a)))).writeW (P + BitVec.ofNat 64 32)
        (BitVec.ofNat 32 (lo len (.slot c b))) := by
    rw [mg.mem, m₁₈, m₁₇.mem, m₁₆, m₁₅.mem, m₁₄, m₁₃.mem, m₁₂, m₁₁.mem, u₁₀.mem, m₉.mem, u₈.mem,
      u₇''.mem, u₇'.mem, m₇.mem, u₆.mem, u₅.mem, m₄.mem, m₃.mem, u₂.mem, m₁, e₁₈, e₁₆, e₁₄, e₁₂, u₁₀.gpr, u₈.gpr,
      eW, m₃.gpr, u₂.gpr, u₂.other .edi (by decide), edi₁]
    rfl
  refine ⟨K₁₈'.trans (mg.keeps _), ?_, ?_⟩
  · have fw : ∀ {m : Mem} (k : Nat) (v : BitVec 32), k + 4 ≤ 36 → Frame [⟨P, 36⟩] f.mem m →
        Frame [⟨P, 36⟩] f.mem (m.writeW (P + BitVec.ofNat 64 k) v) := fun k v hk F =>
      F.writeW (List.mem_singleton_self _) v (Offset.contains_base _ hk (by omega_using [hk]))
    rw [mem]
    exact fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <| fw _ _ (by decide) <|
      fw _ _ (by decide) (Frame.refl _ _)
  · intro i hi
    rw [mem]
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i
    all_goals first
      | omega
      | simp (disch := decide) only [frame_other, Mem.readW_writeW_self32, callArg, Nat.mul_zero, Nat.reduceMul,
          Nat.reduceAdd, Nat.zero_add]

end VG.Proof.Bignum.X86.CrtRt

end

end


/-! # The Montgomery product of two slots of a context, by a call -/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (argAt_alloc)
open VG.Impl.Bignum.X86.PublicRt (argAt)
open VG.Proof.Rsa.MontMul (scratchBytes)

/-- The words of a number of the context. -/
abbrev cwc (len : Nat) (c : Ctx) : Nat := bc len c / 4

theorem cwc_eq (len : Nat) (c : Ctx) : 2 * (bc len c / 8) = cwc len c := by
  have := bc_dvd len c; simp only [cwc]; omega_using [this]

theorem bc_eq_cwc (len : Nat) (c : Ctx) : bc len c = 4 * cwc len c := by
  have := bc_dvd len c; simp only [cwc]; omega_using [this]

theorem mulBody_noSp (c : Ctx) (o a b : Nat) :
    NoSp (.seq (.block (mulArgs c o a b)) (.call "vg_rsa_mont_mul_at" Sse2.atBody) : Prog isa) := by
  apply NoSp.of_all
  have e : (!Taint.clobbers (Instr.alu AluOp.add Reg.eax (Src.reg Reg.edx)) Reg.esp) = true := rfl
  rw [Code.allInstrs_eq]
  cases c <;>
  simp only [instrs, mulArgs, widthC, VG.Impl.Bignum.X86.PublicRt.widthB, offIn, List.all_append, List.all_cons,
    List.all_nil, List.all_replicate, e, ite_self] <;>
  rw [← Code.allInstrs_eq] <;>
  rw [show Sse2.atBody.allInstrs (fun i => !Taint.clobbers i .esp)=true from VG.Proof.Mont.X86.Sse2.atBody_allNoSp] <;> rfl

/-- The callee's offsets for slots `o`, `a` and `b` (3 to 8) of a context. -/
theorem In.offs {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args s) (c : Ctx) {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8)
    (hb3 : 3 ≤ b) (hb : b ≤ 8) :
    Offs bytes (bc len c / 8) numBase invOff (lo len (.slot c 1)) (lo len (.slot c o)) (lo len (.slot c a))
      (lo len (.slot c b)) := by
  have f8 := h.slot_fit c (j := 8) (by decide)
  have g := bc_ge h.lower' c
  have e8 := bc_dvd len c
  have mo : ∀ j, 3 ≤ j → j ≤ 8 → numBase + 3 * st len c ≤ lo len (.slot c j) ∧
      lo len (.slot c j) + st len c ≤ lo len (.slot c 8) + st len c := fun j h3 h8 => by
    have := Nat.mul_le_mul_right (st len c) h3
    have := Nat.mul_le_mul_right (st len c) h8
    simp only [lo]; omega_arith
  obtain ⟨o1, o2⟩ := mo o ho3 ho
  obtain ⟨a1, a2⟩ := mo a ha3 ha
  obtain ⟨b1, b2⟩ := mo b hb3 hb
  have hb8 : 8 * (bc len c / 8) = bc len c := by omega_using [e8]
  have est : st len c = 2 * bc len c + 32 := rfl
  have nb : numBase = 3336 := rfl
  simp only [lo] at f8 o1 o2 a1 a2 b1 b2
  refine ⟨by omega_using [g], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [lo, scratchBytes, VG.Proof.Rsa.MontMul.Apart, invOff, hb8] <;> omega_arith

theorem mul_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (h : In Ex base bytes len args s) (c : Ctx) {o a b : Nat} (ho3 : 3 ≤ o) (ho : o ≤ 8) (ha3 : 3 ≤ a) (ha : a ≤ 8)
    (hb3 : 3 ≤ b) (hb : b ≤ 8)
    (hinv : (val32 s.mem base numBase (cwc len c) * w32 s.mem base invOff + 1) % 2 ^ 32 = 0)
    (hB : val32 s.mem base (lo len (.slot c b)) (cwc len c) < val32 s.mem base numBase (cwc len c)) :
    WP isa (mul c o a b) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨off base (lo len (.slot c o)), bc len c⟩, ⟨off base (lo len (.slot c 1)), 3 * bc len c + 56⟩,
        below (s.gpr .esp) 96] s.mem t.mem ∧
      val32 t.mem base (lo len (.slot c o)) (cwc len c) < val32 s.mem base numBase (cwc len c) ∧
      val32 t.mem base (lo len (.slot c o)) (cwc len c) * 2 ^ (8 * bc len c) % val32 s.mem base numBase (cwc len c) =
        val32 s.mem base (lo len (.slot c a)) (cwc len c) * val32 s.mem base (lo len (.slot c b)) (cwc len c) %
          val32 s.mem base numBase (cwc len c) := by
  have low := h.room.low
  have top := h.top
  have e8 := bc_dvd len c
  have hb8 : 8 * (bc len c / 8) = bc len c := by omega_using [e8]
  have sb : scratchBytes (bc len c / 8) = 3 * bc len c + 56 := by simp only [scratchBytes]; omega_using [e8]
  have p64 : 64 * (bc len c / 8) = 8 * bc len c := by omega_using [e8]
  have fEsp : (allocFrame 36 s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := allocFrame_esp _ _
  have fEspN : ((allocFrame 36 s).gpr .esp).toNat = (s.gpr .esp).toNat - 36 := by
    rw [fEsp, VG.X86.sub_toNat (by omega_using [low])]
  have C := call_ok (is := mulArgs c o a b) h.scratch h.hbytes h.room (h.offs c ho3 ho ha3 ha hb3 hb)
    (by rw [cwc_eq]; exact hinv) (by rw [cwc_eq]; exact hB) (mulBody_noSp c o a b)
    (by
      have := mulArgs_ok (f := allocFrame 36 s) (len := len) (c := c) (o := o) (a := a) (b := b)
        (argAt_alloc h.width) (argAt_alloc (h.arg (i := wsLenArg) (by decide))) h.upper' (by omega_using [ho]) (by omega_using [ha])
        (by omega_using [hb]) (by omega_using [fEspN]) (by rw [allocFrame_wr, fEsp]; exact List.mem_cons_self ..)
      rwa [show (allocFrame 36 s).gpr .edi = s.gpr .edi from allocFrame_gpr _ _ (by decide)] at this)
  refine WP.mono C fun t ⟨cs, rd, wr, F, L, V⟩ => ⟨cs, rd, wr, ?_, ?_, ?_⟩
  · rw [hb8, sb] at F; exact F
  · rw [cwc_eq] at L; exact L
  · rw [cwc_eq, p64] at V; exact V

end VG.Proof.Bignum.X86.CrtRt
