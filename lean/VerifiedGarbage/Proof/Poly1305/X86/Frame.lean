module

public import VerifiedGarbage.Proof.Poly1305.X86.Finalize
public import VerifiedGarbage.Impl.StackScratch.X86
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.StackScratch
import VerifiedGarbage.Proof.Poly1305.X86.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Poly1305.Scratch
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Poly1305.X86.Sse2
import VerifiedGarbage.Proof.Framework.X86.Rel2
meta import VerifiedGarbage.Proof.Framework.X86.Rel2
meta import VerifiedGarbage.Proof.Poly1305.X86.Finalize
meta import VerifiedGarbage.Proof.Poly1305.Scratch
meta import VerifiedGarbage.Proof.Poly1305.X86.Lit
meta import VerifiedGarbage.Proof.Poly1305.Stream
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `Poly1305.X86.Update`, which only this module used -/

section

/-!
# Poly1305 on x86 (32-bit): `update`
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev dp : BitVec 32 := arg s₀ 3
abbrev dl : Nat := (arg s₀ 4).toNat
abbrev dR : Region := ⟨(dp s₀).setWidth 64, dl s₀⟩
abbrev scR : Region := ⟨(arg s₀ 5).setWidth 64, 128⟩
/-- The first `c` bytes of data. -/
abbrev Dt (c : Nat) : List Byte := bytesAt s₀.mem ((dp s₀).setWidth 64) c
end

theorem dl_lt (s₀ : State) : dl s₀ < 2 ^ 32 := (arg s₀ 4).isLt

structure UPre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, ⟨argAddr s₀ 0, 24⟩]
  wr : s₀.wr = [sR (stp s₀), scR s₀]
  st_d : (sR (stp s₀)).Disjoint (dR s₀)
  st_sc : (sR (stp s₀)).Disjoint (scR s₀)
  d_sc : (dR s₀).Disjoint (scR s₀)
  arg_st : Region.Disjoint ⟨argAddr s₀ 0, 24⟩ (sR (stp s₀))
  arg_sc : Region.Disjoint ⟨argAddr s₀ 0, 24⟩ (scR s₀)
  ret_st : (retR s₀).Disjoint (sR (stp s₀))
  ret_sc : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (sR (stp s₀))
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_sc : (stkR s₀).Disjoint (scR s₀)
  st_fit : (stp s₀).toNat + 128 ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + dl s₀ ≤ 2 ^ 32
  sc_fit : (arg s₀ 5).toNat + 128 ≤ 2 ^ 32
  sp_stk : 524 ≤ (s₀.gpr .esp).toNat
  sp_fit : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32

theorem UPre.of (s₀ : State) (h : Proof.Poly1305.updateX86.pre s₀) : UPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

namespace UPre
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨⟨argAddr s₀ 0, 24⟩, by rw [hp.rd]; simp, arg_contains (n := 24) (by have := hp.sp_fit; omega_using [this])
    (by omega_using [hi])⟩

/-- An argument, in memory the code has written only in the state. -/
theorem arg_same {m : Mem} (hf : Frame [sR (stp s₀)] s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (arg_contains (n := 24) (by have := hp.sp_fit; omega_using [this]) (by omega_using [hi])) (by simpa using hp.arg_st)
    (by decide)

theorem st_in : sR (stp s₀) ∈ s₀.wr := by rw [hp.wr]; exact List.mem_cons_self

/-- Byte `c + i` of the data. -/
theorem data_addr {c i : Nat} (h : c + i < dl s₀) :
    addr (dp s₀ + BitVec.ofNat 32 c) i = (dp s₀).setWidth 64 + BitVec.ofNat 64 (c + i) := by
  have := hp.d_fit
  rw [show addr (dp s₀ + BitVec.ofNat 32 c) i = addr (dp s₀) (c + i) by
    simp only [addr]; rw [BitVec.add_assoc, ← BitVec.ofNat_add], addr_eq (by omega_using [h, this])]

theorem dR_contains {i n : Nat} (h : i + n ≤ dl s₀) :
    (dR s₀).Contains ((dp s₀).setWidth 64 + BitVec.ofNat 64 i) n := by
  have := hp.d_fit
  exact Offset.contains_base _ h (by omega_using [h, this])

/-- The data, as a source of bytes to copy. -/
theorem srcOk {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hf : Frame [sR (stp s₀)] s₀.mem s.mem)
    {c n : Nat} (h : c + n ≤ dl s₀) (hn : 0 < n) :
    SrcOk s (stp s₀) s₀.mem (dp s₀ + BitVec.ofNat 32 c) n := by
  have := hp.d_fit
  refine ⟨?_, fun i hi => ⟨?_, fun hb => ?_, ?_⟩⟩
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega_using [h, hn, this]), Nat.mod_eq_of_lt (by omega_using [h, hn, this])]
    omega_using [h, this]
  · rw [hrd, hwr, hp.rd, hp.data_addr (by omega_using [h, hi])]
    exact ⟨dR s₀, by simp, hp.dR_contains (by omega_using [h, hi])⟩
  · rw [hp.data_addr (by omega_using [h, hi])] at hb
    exact hp.st_d _ (bfR_sub hp.st_fit _ hb) (hp.dR_contains (by omega_using [h, hi]))
  · rw [hp.data_addr (by omega_using [h, hi])]
    exact hf _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact fun hc => hp.st_d _ hc (hp.dR_contains (by omega_using [h, hi]))

/-- The bytes at `dp + c`, as the data's. -/
theorem data_bytes {c n : Nat} (h : c + n ≤ dl s₀) :
    bytesAt s₀.mem ((dp s₀ + BitVec.ofNat 32 c).setWidth 64) n =
      bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · have := hp.d_fit
    rw [show (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = addr (dp s₀) c from rfl, addr_eq (by omega_using [h, hn, this])]

end UPre

theorem Dt_add (s₀ : State) (c n : Nat) :
    Dt s₀ (c + n) = Dt s₀ c ++ bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) n :=
  Poly1305.bytesAt_add _ _ _ _

/-! ## Invariants -/

/-- Before any data is consumed. -/
structure Pre1 (s₀ : State) (F : Nat → Nat) (s : State) : Prop extends UCommon s₀ F s where
  esi : s.gpr .esi = dp s₀
  buf : bytesAt s.mem (bq (stp s₀)) (kb s₀) = Bf s₀
  acc : Acc s₀ [] s.mem

/-- The buffer and the first `c` bytes of data are absorbed, a whole number
of blocks. -/
structure Cons (s₀ : State) (F : Nat → Nat) (c : Nat) (s : State) : Prop extends UCommon s₀ F s where
  c_le : c ≤ dl s₀
  whole : (kb s₀ + c) % 16 = 0
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c
  acc : Acc s₀ (Bf s₀ ++ Dt s₀ c) s.mem

/-- The buffer and the data are the whole blocks `X`, absorbed, followed by
`Y`, in the buffer. -/
structure Done (s₀ : State) (F : Nat → Nat) (s : State) : Prop extends UCommon s₀ F s where
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 (dl s₀)
  done : ∃ X Y : List Byte, Acc s₀ X s.mem ∧ X.length % 16 = 0 ∧ Y.length < 16 ∧
    Bf s₀ ++ Dt s₀ (dl s₀) = X ++ Y ∧ bytesAt s.mem (bq (stp s₀)) Y.length = Y

theorem Cons.regs {s₀ s s' : State} {F : Nat → Nat} {c : Nat} (h : Cons s₀ F c s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Cons s₀ F c s' :=
  { h.toUCommon.regs hedi hesp hm hrd hwr with
    c_le := h.c_le, whole := h.whole, esi := hesi.trans h.esi, acc := hm ▸ h.acc }

theorem Done.regs {s₀ s s' : State} {F : Nat → Nat} (h : Done s₀ F s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Done s₀ F s' :=
  { h.toUCommon.regs hedi hesp hm hrd hwr with
    esi := hesi.trans h.esi, done := hm ▸ h.done }

/-! ## Prologue -/

theorem uprologue_ok {s₀ : State} (hp : UPre s₀) :
    WP isa (.block (setup ++ ([.mov .esi (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 8)),
      .alu .and .edx (.imm 15), .alu .test .edx (.reg .edx)] : List Instr))) s₀ fun s => ∃ F, SetupF s₀ F ∧
        Pre1 s₀ F s ∧ s.gpr .edx = BitVec.ofNat 32 (kb s₀) ∧
        s.zf = some (BitVec.ofNat 32 (kb s₀) &&& BitVec.ofNat 32 (kb s₀) == 0) := by
  have hfit := hp.st_fit
  refine WP.block_append (WP.mono (setup_ok (arg0_eq s₀) (hp.argIn (i := 0) (by decide)) hfit hp.st_in)
    fun s₁ ⟨F, A₁, c₁, hF, sv, co⟩ => ?_)
  obtain esp₁ := A₁.gpr .esp (by decide)
  obtain hF' := SetupF.of hF sv co
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 3)) (by rw [ea_at, esp₁])
    (by rw [A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₂ u₂ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, u₂.other _ (by decide), esp₁])
    (by rw [u₂.rd, u₂.wr, A₁.rd, A₁.wr]; exact hp.argIn (by decide)) fun s₃ u₃ _ => ?_
  refine wp_andx (readSrc_imm _ _) fun s₄ u₄ => wp_test fun s₅ k₅ z₅ => WP.block_nil ?_
  obtain hm : s₅.mem = s₁.mem := by rw [k₅.2.1, u₄.mem, u₃.mem, u₂.mem]
  obtain hedx₄ : s₄.gpr .edx = BitVec.ofNat 32 (kb s₀) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, hp.arg_same A₁.frame (i := 1) (by decide), and15]
  obtain hedx : s₅.gpr .edx = BitVec.ofNat 32 (kb s₀) := by rw [k₅.1 _ (by simp), hedx₄]
  obtain hw : ∀ k < 32, words s₅.mem (stp s₀) k = F k := fun k hk => by rw [hm]; exact A₁.words k hk
  refine ⟨F, hF', ⟨⟨c₁.keep (by rw [k₅.1 _ (by simp), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide)]) (by rw [k₅.2.2.2, u₄.wr, u₃.wr, u₂.wr]), ?_, by rw [hm]; exact A₁.frame,
      by rw [k₅.2.2.1, u₄.rd, u₃.rd, u₂.rd, A₁.rd], by rw [k₅.2.2.2, u₄.wr, u₃.wr, u₂.wr, A₁.wr],
      fun k hk _ _ => hw k hk⟩, ?_, ?_, fun hA => ?_⟩, hedx, ?_⟩
  · rw [k₅.1 _ (by simp), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), esp₁]
  · rw [k₅.1 _ (by simp), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      hp.arg_same A₁.frame (i := 3) (by decide)]
  · refine bytes_words hfit (fun k h₁ h₂ => ?_) (Nat.le_of_lt (kb_lt s₀))
    rw [hw k (by omega_using [h₁, h₂]), hF'.low k (by omega_using [h₂]) (by omega_using [h₁, h₂])]
  · exact acc_entry hfit hF' (fun k hk => hw k (by omega_using [hk])) hA
  · rw [z₅, hedx₄]

/-! ## Filling the buffer -/

theorem Pre1.regs {s₀ s s' : State} {F : Nat → Nat} (h : Pre1 s₀ F s) (hedi : s'.gpr .edi = s.gpr .edi)
    (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi) (hm : s'.mem = s.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Pre1 s₀ F s' :=
  { h.toUCommon.regs hedi hesp hm hrd hwr with
    esi := hesi.trans h.esi, buf := hm ▸ h.buf, acc := hm ▸ h.acc }

theorem sub16_eq {k : Nat} (hk : k ≤ 16) : (16 : BitVec 32) - BitVec.ofNat 32 k = BitVec.ofNat 32 (16 - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [show (16 : BitVec 32).toNat = 16 from rfl]
  omega_using [hk]

theorem count_eq : count = .seq (.block [.mov .eax (.imm 16), .alu .sub .eax (.reg .edx),
    .mov .ecx (.mem (at_ .esp 20)), .alu .cmp .ecx (.reg .eax)])
    (.seq (.ite .b (.block [.mov .eax (.reg .ecx)]) (.block []))
      (.block [.alu .add .edx (.reg .edi), .alu .test .eax (.reg .eax)])) := rfl

/-- The number of bytes to copy, `n = min(16 - kb, dl)`, into `eax`, and the
address `state + kb` into `edx`. -/
theorem count_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State} (h : Pre1 s₀ F s)
    (hedx : s.gpr .edx = BitVec.ofNat 32 (kb s₀)) :
    WP isa count s fun s' => Pre1 s₀ F s' ∧ s'.gpr .edx = stp s₀ + BitVec.ofNat 32 (kb s₀) ∧
      s'.gpr .eax = BitVec.ofNat 32 (min (16 - kb s₀) (dl s₀)) ∧
      s'.zf = some (decide (min (16 - kb s₀) (dl s₀) = 0)) := by
  obtain hkl := kb_lt s₀
  obtain hdl : dl s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  rw [count_eq]
  refine WP.seq (wp_movi fun s₁ u₁ _ => wp_subx (readSrc_reg _ _) fun s₂ u₂ _ => ?_)
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 4))
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, h.rd, h.wr]; exact hp.argIn (by decide)) fun s₃ u₃ _ => ?_
  refine wp_cmpx (readSrc_reg _ _) fun s₄ k₄ _ cf₄ => WP.block_nil ?_
  obtain heax₂ : s₂.gpr .eax = BitVec.ofNat 32 (16 - kb s₀) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hedx, sub16_eq (by omega_using [hkl])]
  obtain hecx₃ : s₃.gpr .ecx = arg s₀ 4 := by
    rw [u₃.gpr, u₂.mem, u₁.mem]; exact hp.arg_same h.frame (by decide)
  have hP₄ : Pre1 s₀ F s₄ := h.regs
    (by rw [k₄.gpr', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [k₄.gpr', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [k₄.gpr', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [k₄.2.1, u₃.mem, u₂.mem, u₁.mem]) (by rw [k₄.2.2.1, u₃.rd, u₂.rd, u₁.rd])
    (by rw [k₄.2.2.2, u₃.wr, u₂.wr, u₁.wr])
  obtain hedx₄ : s₄.gpr .edx = BitVec.ofNat 32 (kb s₀) := by
    rw [k₄.gpr', u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hedx]
  obtain heax₄ : s₄.gpr .eax = BitVec.ofNat 32 (16 - kb s₀) := by rw [k₄.gpr', u₃.other _ (by decide), heax₂]
  obtain hecx₄ : s₄.gpr .ecx = arg s₀ 4 := by rw [k₄.gpr', hecx₃]
  -- `eax = n`.
  refine WP.seq (WP.mono (Q := fun s₅ : State => Pre1 s₀ F s₅ ∧ s₅.gpr .edx = BitVec.ofNat 32 (kb s₀) ∧
      s₅.gpr .eax = BitVec.ofNat 32 (min (16 - kb s₀) (dl s₀))) ?_ fun s₅ ⟨hP₅, hedx₅, heax₅⟩ => ?_)
  · refine WP.ite (decide (dl s₀ < 16 - kb s₀)) (by
      simp only [eval, cf₄, u₃.other .eax (by decide), heax₂, hecx₃, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 16 - kb s₀ < 2 ^ 32 by omega_using [hkl])]) (fun hb => ?_) (fun hb => ?_)
    · refine wp_mov fun s₅ u₅ _ => WP.block_nil ⟨hP₄.regs (u₅.other _ (by decide)) (u₅.other _ (by decide))
        (u₅.other _ (by decide)) u₅.mem u₅.rd u₅.wr, by rw [u₅.other _ (by decide), hedx₄], ?_⟩
      simp only [decide_eq_true_eq] at hb
      rw [u₅.gpr, hecx₄, Nat.min_eq_right (by omega_using [hb])]
      simp
    · refine WP.block_nil ⟨hP₄, hedx₄, ?_⟩
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
      rw [heax₄, Nat.min_eq_left hb]
  · refine wp_addx (readSrc_reg _ _) fun s₆ u₆ _ => wp_test fun s₇ k₇ z₇ => WP.block_nil ?_
    refine ⟨hP₅.regs (by rw [k₇.gpr', u₆.other _ (by decide)]) (by rw [k₇.gpr', u₆.other _ (by decide)])
      (by rw [k₇.gpr', u₆.other _ (by decide)]) (by rw [k₇.2.1, u₆.mem]) (by rw [k₇.2.2.1, u₆.rd])
      (by rw [k₇.2.2.2, u₆.wr]), ?_, ?_, ?_⟩
    · rw [k₇.gpr', u₆.gpr, hedx₅, hP₅.ctx.edi, BitVec.add_comm]
    · rw [k₇.gpr', u₆.other _ (by decide), heax₅]
    · rw [z₇, u₆.other _ (by decide), heax₅, BitVec.and_self, ofNat32_beq_zero (by omega_using [hdl])]

/-- After copying `n` bytes of data into the buffer. -/
structure Filled (s₀ : State) (F : Nat → Nat) (n : Nat) (s : State) : Prop extends UCommon s₀ F s where
  n_le : n ≤ dl s₀
  n_le' : kb s₀ + n ≤ 16
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 n
  buf : bytesAt s.mem (bq (stp s₀)) (kb s₀ + n) = Bf s₀ ++ Dt s₀ n
  acc : Acc s₀ [] s.mem

theorem UPre.srcOk0 {s₀ : State} (hp : UPre s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hf : Frame [sR (stp s₀)] s₀.mem s.mem) {n : Nat} (h : n ≤ dl s₀) (hn : 0 < n) :
    SrcOk s (stp s₀) s₀.mem (dp s₀) n := by
  have := hp.srcOk hrd hwr hf (c := 0) (n := n) (by omega_using [h]) hn
  simpa using this

theorem copyFill_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State} (h : Pre1 s₀ F s) {n : Nat}
    (hn : n ≤ dl s₀) (hn' : kb s₀ + n ≤ 16) (hedx : s.gpr .edx = stp s₀ + BitVec.ofNat 32 (kb s₀))
    (heax : s.gpr .eax = BitVec.ofNat 32 n) (hz : s.zf = some (decide (n = 0))) :
    WP isa (.ite .e (.block []) copyIn) s fun s' =>
      Filled s₀ F n s' ∧ s'.gpr .edx = stp s₀ + BitVec.ofNat 32 (kb s₀ + n) := by
  have hfit := hp.st_fit
  refine WP.ite (decide (n = 0)) (by simp [eval, hz]) (fun h0 => ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0
    subst h0
    exact WP.block_nil ⟨{ h.toUCommon with
      n_le := hn, n_le' := hn', esi := by rw [h.esi]; simp
      buf := by rw [Nat.add_zero, h.buf]; simp [Dt, bytesAt]
      acc := h.acc }, by rw [hedx, Nat.add_zero]⟩
  · simp only [decide_eq_false_iff_not] at h0
    refine WP.mono (copy_ok (m₀ := s₀.mem) hfit hn' (by omega_using [h0]) (by rw [h.wr]; exact hp.st_in)
      (hp.srcOk0 h.rd h.wr h.frame hn (by omega_using [h0])) h.esi hedx heax) fun s' hc => ?_
    obtain hf := hc.frame hn'
    obtain hU : UCommon s₀ F s' := h.toUCommon.buf (hc.keep _ (by decide) (by decide) (by decide) (by decide))
      (hc.keep _ (by decide) (by decide) (by decide) (by decide)) hf hc.rd hc.wr hfit
    exact ⟨{ hU with
      n_le := hn, n_le' := hn', esi := hc.esi
      buf := by rw [hc.buf hn', h.buf]
      acc := h.acc.words fun k hk => words_bf hfit hf (by omega_using [hk]) (by omega_using [hk]) }, hc.edx⟩

/-- Absorbing the full buffer. -/
theorem absorbBuf_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State} {n : Nat}
    (h : Filled s₀ F n s) (hfull : kb s₀ + n = 16) : WP isa (.block (absorbAt .edi 56 1)) s (Cons s₀ F n) := by
  have hfit := hp.st_fit
  have hc := h.ctx
  refine WP.mono (absorbAtFull_ok hc (bp := stp s₀ + BitVec.ofNat 32 56) (absorbBuf_okList 1)
    (fun h => absurd h (by decide)) (by decide) (fun k _ => by rw [hc.edi, buf_ea])
    (fun k hk => by rw [← buf_ea]; exact hc.inRW (by omega_using [hk]) (by decide))
    (fun k hk => .inr ⟨14 + k, by omega_arith, by omega_using [hk], by rw [← buf_ea]; congr 1; omega_using []⟩)
    (by decide) (C := A0 s₀ < P)
    (fun hA => ⟨hF.coefs.congr fun k h₁ h₂ => h.keep k (by omega_using [h₁, h₂]) (not_hS (.inl ⟨by omega_using [h₁, h₂], h₂⟩)) (.inr h₁),
      (h.acc hA).1⟩))
    fun s' ⟨S, ha⟩ => ?_
  refine ⟨⟨hc.keep (S.gpr _ (by decide)) S.wr, by rw [S.gpr _ (by decide)]; exact h.esp,
    h.frame.trans S.frame, by rw [S.rd]; exact h.rd, by rw [S.wr]; exact h.wr,
    fun k hk hS h' => (S.same k hk hS).trans (h.keep k hk hS h')⟩, h.n_le, by rw [hfull],
    by rw [S.gpr _ (by decide)]; exact h.esi, fun hA => ?_⟩
  obtain ⟨-, hv⟩ := h.acc hA
  obtain ⟨h4, hv'⟩ := ha hA
  refine ⟨h4, ?_⟩
  obtain hl : (Bf s₀ ++ Dt s₀ n).length = 16 := by
    simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; omega_using [hfull]
  obtain e : leNum (Bf s₀ ++ Dt s₀ n ++ [0x01]) = leNum (Bf s₀ ++ Dt s₀ n) + 2 ^ 128 * 1 := by
    rw [Poly1305.leNum_append, hl]; rfl
  rw [Poly1305.absorbAll_nil] at hv
  rw [hv', buf_value hfit, ← hfull, h.buf, show (1 : BitVec 32).toNat = 1 from rfl, mod_step hv,
    Poly1305.absorbAll_block (by omega_using [hl]) (by omega_using [hl]), e]

theorem Filled.regs {s₀ s s' : State} {F : Nat → Nat} {n : Nat} (h : Filled s₀ F n s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hesi : s'.gpr .esi = s.gpr .esi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Filled s₀ F n s' :=
  { h.toUCommon.regs hedi hesp hm hrd hwr with
    n_le := h.n_le, n_le' := h.n_le', esi := hesi.trans h.esi, buf := hm ▸ h.buf,
    acc := hm ▸ h.acc }

theorem sub_self_add (st : BitVec 32) (a : Nat) : st + BitVec.ofNat 32 a - st = BitVec.ofNat 32 a := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- `min(16 - kb, dl)` bytes into the buffer, which is absorbed if that fills it. -/
theorem fill_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State} (h : Pre1 s₀ F s)
    (hedx : s.gpr .edx = BitVec.ofNat 32 (kb s₀)) :
    WP isa fill s fun s' => (∃ c, Cons s₀ F c s') ∨ Done s₀ F s' := by
  obtain hkl := kb_lt s₀
  obtain hn : min (16 - kb s₀) (dl s₀) ≤ dl s₀ := Nat.min_le_right _ _
  obtain hn' : kb s₀ + min (16 - kb s₀) (dl s₀) ≤ 16 := by
    have := Nat.min_le_left (16 - kb s₀) (dl s₀); omega_using [hkl, this]
  refine WP.seq (WP.mono (count_ok hp h hedx) fun s₁ ⟨h₁, hedx₁, heax₁, hz₁⟩ => ?_)
  refine WP.seq (WP.mono (copyFill_ok hp h₁ hn hn' hedx₁ heax₁ hz₁) fun s₂ ⟨h₂, hedx₂⟩ => ?_)
  refine WP.seq (wp_subx (readSrc_reg _ _) fun s₃ u₃ _ => wp_cmpx (readSrc_imm _ _) fun s₄ k₄ z₄ _ =>
    WP.block_nil ?_)
  have h₄ : Filled s₀ F (min (16 - kb s₀) (dl s₀)) s₄ := h₂.regs
    (by rw [k₄.gpr', u₃.other _ (by decide)]) (by rw [k₄.gpr', u₃.other _ (by decide)])
    (by rw [k₄.gpr', u₃.other _ (by decide)]) (by rw [k₄.2.1, u₃.mem]) (by rw [k₄.2.2.1, u₃.rd])
    (by rw [k₄.2.2.2, u₃.wr])
  refine WP.ite (decide (kb s₀ + min (16 - kb s₀) (dl s₀) = 16))
    (by simp only [eval, z₄, u₃.gpr, hedx₂, h₂.ctx.edi, sub_self_add]; rw [eq16_beq hn'])
    (fun hfull => ?_) (fun hnf => ?_)
  · exact WP.mono (absorbBuf_ok hp hF h₄ (by simpa using hfull)) fun s' h' => .inl ⟨_, h'⟩
  · simp only [decide_eq_false_iff_not] at hnf
    obtain hnd : min (16 - kb s₀) (dl s₀) = dl s₀ := by omega_using [hkl, hn, hn', hnf]
    refine WP.block_nil (.inr { h₄.toUCommon with
      esi := by rw [h₄.esi, hnd]
      done := ⟨[], Bf s₀ ++ Dt s₀ (min (16 - kb s₀) (dl s₀)), h₄.acc, rfl, ?_, ?_, ?_⟩ })
    · simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; omega_using [hn', hnf]
    · rw [hnd, List.nil_append]
    · simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]
      exact h₄.buf

/-! ## Whole blocks of data -/

namespace UPre
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- Word `d` of the data from byte `c` on, within the data. -/
theorem blk_sub {c d : Nat} (h : c + d + 4 ≤ dl s₀) :
    Region.Sub (sub (dp s₀ + BitVec.ofNat 32 c) d 4) (dR s₀) := fun a ha =>
  (hp.dR_contains (i := c + d) (n := 4) (by omega_using [h])).byte (by
    rw [← hp.data_addr (by omega_using [h])]; simp only [Region.Contains] at ha; omega_using [ha])

theorem blkIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {c : Nat} (hc : c + 16 ≤ dl s₀)
    (hesi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c) : BlkIn s := fun d hd => by
  rw [hrd, hwr, hesi, hp.rd, hp.data_addr (by omega_using [hc, hd])]
  exact ⟨dR s₀, by simp, hp.dR_contains (by omega_using [hc, hd])⟩

theorem blk_disj {c : Nat} (hc : c + 16 ≤ dl s₀) {k : Nat} (hk : k < 4) :
    (sub (dp s₀ + BitVec.ofNat 32 c) (4 * k) 4).Disjoint (sR (stp s₀)) :=
  hp.st_d.symm.sub_left (hp.blk_sub (by omega_using [hc, hk]))

/-- The value of the block of data at byte `c`, with the `0x01` byte appended:
its four words and `2¹²⁸`. -/
theorem data_value {m : Mem} (hf : Frame [sR (stp s₀)] s₀.mem m) {c : Nat} (hc : c + 16 ≤ dl s₀) :
    blkv m (dp s₀ + BitVec.ofNat 32 c) 1 =
      leNum (bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) 16 ++ [0x01]) := by
  obtain hw : ∀ k < 4, wv m (dp s₀ + BitVec.ofNat 32 c) (4 * k) =
      w32 s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) k := fun k hk => by
    show (wd m _ (4 * k)).toNat = _
    rw [wd_frame hf (by simpa using hp.blk_disj hc hk)]
    simp only [wd, w32]
    rw [hp.data_addr (by omega_using [hc, hk]), add_ofNat_add]
  rw [Poly1305.leNum_append, Poly1305.length_bytesAt, leNum_bytesAt_16, ← hw 0 (by decide),
    ← hw 1 (by decide), ← hw 2 (by decide), ← hw 3 (by decide)]
  simp only [blkv, Spec.Poly1305.leNum]
  rfl

end UPre

theorem left_eq : left = [.mov .eax (.mem (at_ .esp 16)), .mov .ecx (.mem (at_ .esp 20)),
    .alu .add .eax (.reg .ecx), .alu .sub .eax (.reg .esi)] := rfl

theorem sub_left_eq {d : BitVec 32} {L c : Nat} (hL : L < 2 ^ 32) (hc : c ≤ L) :
    d + BitVec.ofNat 32 L - (d + BitVec.ofNat 32 c) = BitVec.ofNat 32 (L - c) := by
  apply BitVec.eq_of_toNat_eq
  have := d.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [hL, hc]

/-- The length of the data left, `dl - c`, into `eax`. -/
theorem left_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State} (hU : UCommon s₀ F s) {c : Nat}
    (hc : c ≤ dl s₀) (hesi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c) :
    WP isa (.block left) s fun s' => Keeps [.eax, .ecx] s s' ∧
      s'.gpr .eax = BitVec.ofNat 32 (dl s₀ - c) ∧ s'.zf = some (decide (dl s₀ - c = 0)) := by
  obtain hdl : dl s₀ < 2 ^ 32 := (arg s₀ 4).isLt
  rw [left_eq]
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 3)) (by rw [ea_at, hU.esp])
    (by rw [hU.rd, hU.wr]; exact hp.argIn (by decide)) fun s₁ u₁ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 4)) (by rw [ea_at, u₁.other _ (by decide), hU.esp])
    (by rw [u₁.rd, u₁.wr, hU.rd, hU.wr]; exact hp.argIn (by decide)) fun s₂ u₂ _ => ?_
  refine wp_addx (readSrc_reg _ _) fun s₃ u₃ _ => wp_subx (readSrc_reg _ _) fun s₄ u₄ z₄ => WP.block_nil ?_
  obtain heax₃ : s₃.gpr .eax = dp s₀ + BitVec.ofNat 32 (dl s₀) := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, hp.arg_same hU.frame (i := 3) (by decide),
      hp.arg_same hU.frame (i := 4) (by decide)]
    simp
  obtain hesi₃ : s₃.gpr .esi = dp s₀ + BitVec.ofNat 32 c := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesi]
  obtain heax₄ : s₄.gpr .eax = BitVec.ofNat 32 (dl s₀ - c) := by
    rw [u₄.gpr, heax₃, hesi₃, sub_left_eq hdl hc]
  refine ⟨⟨fun r hr => ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩, heax₄, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₄.other r hr.1, u₃.other r hr.1, u₂.other r hr.2, u₁.other r hr.1]
  · rw [z₄, ← u₄.gpr, heax₄, ofNat32_beq_zero (by omega_using [hc, hdl])]

theorem add_ofNat_inj {d : BitVec 32} {a b L : Nat} (ha : a ≤ L) (hb : b ≤ L) (hL : L < 2 ^ 32)
    (h : d + BitVec.ofNat 32 a = d + BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have := d.isLt
  omega_arith

theorem Pos.whole {s₀ s : State} {F : Nat → Nat} (h : (∃ c, Cons s₀ F c s) ∨ Done s₀ F s) :
    ∃ c, c ≤ dl s₀ ∧ s.gpr .esi = dp s₀ + BitVec.ofNat 32 c := by
  rcases h with ⟨c, hc⟩ | hd
  · exact ⟨c, hc.c_le, hc.esi⟩
  · exact ⟨dl s₀, (Nat.le_refl _), hd.esi⟩

/-- One whole block of data. -/
theorem whole_step {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {c : Nat} {s : State}
    (h : Cons s₀ F c s) (hc : 16 ≤ dl s₀ - c) :
    WP isa (.block (absorb 1 ++ ([.alu .add .esi (.imm 16)] : List Instr) ++ left ++ ([.alu .cmp .eax (.imm 16)] : List Instr))) s fun s' =>
      Cons s₀ F (c + 16) s' ∧ s'.cf = some (decide (dl s₀ - (c + 16) < 16)) := by
  have hfit := hp.st_fit
  rw [show absorb 1 ++ [.alu .add .esi (.imm 16)] ++ left ++ [.alu .cmp .eax (.imm 16)] =
    absorb 1 ++ (.alu .add .esi (.imm 16) :: (left ++ [.alu .cmp .eax (.imm 16)])) by simp]
  refine WP.block_append (WP.mono (absorbFull_ok h.ctx (hp.blkIn h.rd h.wr (by omega_using [hc]) h.esi)
    (fun k hk => by rw [h.esi]; exact hp.blk_disj (by omega_using [hc]) hk) 1 (by decide) (C := A0 s₀ < P)
    (fun hA => ⟨hF.coefs.congr fun k h₁ h₂ => h.keep k (by omega_using [h₁, h₂]) (not_hS (.inl ⟨by omega_using [h₁, h₂], h₂⟩)) (.inr h₁),
      (h.acc hA).1⟩)) fun s₁ ⟨S₁, h₁⟩ => ?_)
  refine wp_addx (readSrc_imm _ _) fun s₂ u₂ _ => ?_
  obtain hC₂ : Cons s₀ F (c + 16) s₂ := by
    refine ⟨⟨h.ctx.keep (by rw [u₂.other _ (by decide), S₁.gpr _ (by decide)]) (by rw [u₂.wr, S₁.wr]),
      by rw [u₂.other _ (by decide), S₁.gpr _ (by decide)]; exact h.esp,
      by rw [u₂.mem]; exact h.frame.trans S₁.frame, by rw [u₂.rd, S₁.rd]; exact h.rd,
      by rw [u₂.wr, S₁.wr]; exact h.wr,
      fun k hk hS h' => by rw [u₂.mem]; exact (S₁.same k hk hS).trans (h.keep k hk hS h')⟩,
      by omega_using [hc, h₁], by have := h.whole; omega_using [this], ?_, fun hA => ?_⟩
    · rw [u₂.gpr, S₁.gpr _ (by decide), h.esi, BitVec.add_assoc,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, ← BitVec.ofNat_add]
    · obtain ⟨h4, hv⟩ := h₁ hA
      obtain ⟨-, hv₀⟩ := h.acc hA
      refine ⟨by rw [u₂.mem]; exact h4, ?_⟩
      obtain h16 : (Bf s₀ ++ Dt s₀ c).length % 16 = 0 := by
        simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; exact h.whole
      obtain hb1 : 0 < (bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) 16).length := by
        rw [Poly1305.length_bytesAt]; omega_using []
      obtain hb2 : (bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) 16).length ≤ 16 := by
        rw [Poly1305.length_bytesAt]
      rw [u₂.mem, hv, h.esi, show (1 : BitVec 32).toNat = 1 from rfl, hp.data_value h.frame (by omega_using [hc, h₁, hA]),
        mod_step hv₀, Dt_add, ← List.append_assoc, Poly1305.absorbAll_append h16,
        Poly1305.absorbAll_block hb1 hb2]
  refine WP.block_append (WP.mono (left_ok hp hC₂.toUCommon hC₂.c_le hC₂.esi) fun s₃ ⟨k₃, heax₃, _⟩ => ?_)
  refine wp_cmpx (readSrc_imm _ _) fun s₄ k₄ _ cf₄ => WP.block_nil ⟨hC₂.regs
    (by rw [k₄.gpr', k₃.gpr']) (by rw [k₄.gpr', k₃.gpr']) (by rw [k₄.gpr', k₃.gpr'])
    (by rw [k₄.2.1, k₃.2.1]) (by rw [k₄.2.2.1, k₃.2.2.1]) (by rw [k₄.2.2.2, k₃.2.2.2]), ?_⟩
  rw [cf₄, heax₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := dl_lt s₀; omega_using [this])]
  rfl

/-- The loop over the whole blocks of data. -/
theorem whole_loop {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {c : Nat} {s : State}
    (h : Cons s₀ F c s) (hc : 16 ≤ dl s₀ - c) :
    WP isa (.loop (.block (absorb 1 ++ ([.alu .add .esi (.imm 16)] : List Instr) ++ left ++ ([.alu .cmp .eax (.imm 16)] : List Instr))) .ae) s
      fun s' => ∃ c', Cons s₀ F c' s' ∧ dl s₀ - c' < 16 := by
  refine WP.loop (M := isa) (fun k s => ∃ c, k = dl s₀ - c ∧ Cons s₀ F c s ∧ 16 ≤ dl s₀ - c) ?_ _ s
    ⟨c, rfl, h, hc⟩
  rintro k s ⟨c, rfl, h, hc⟩
  refine WP.mono (whole_step hp hF h hc) fun s' ⟨h', hcf⟩ => ?_
  by_cases hl : dl s₀ - (c + 16) < 16
  · exact .inl ⟨by simp [eval, hcf, hl], c + 16, h', hl⟩
  · exact .inr ⟨by simp [eval, hcf, hl], _, by omega_using [hl], c + 16, rfl, h', by omega_using [hl]⟩

/-- The whole blocks left, one at a time. -/
theorem whole16_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (h : (∃ c, Cons s₀ F c s) ∨ Done s₀ F s) :
    WP isa (.seq (.block (left ++ ([.alu .cmp .eax (.imm 16)] : List Instr)))
      (.ite .b (.block []) (.loop (.block (absorb 1 ++ ([.alu .add .esi (.imm 16)] : List Instr) ++ left ++
        ([.alu .cmp .eax (.imm 16)] : List Instr))) .ae))) s
      fun s' => (∃ c, Cons s₀ F c s' ∧ dl s₀ - c < 16) ∨ Done s₀ F s' := by
  obtain ⟨c, hcl, hesi⟩ := Pos.whole h
  obtain hU : UCommon s₀ F s := by rcases h with ⟨_, hc⟩ | hd; exacts [hc.toUCommon, hd.toUCommon]
  refine WP.seq (WP.mono (Q := fun s₂ : State => Keeps [.eax, .ecx] s s₂ ∧ s₂.cf = some (decide (dl s₀ - c < 16)))
    (WP.block_append (WP.mono (left_ok hp hU hcl hesi) fun s₁ ⟨k₁, heax₁, _⟩ =>
      wp_cmpx (readSrc_imm _ _) fun s₂ k₂ _ cf₂ => WP.block_nil ⟨(k₁.trans k₂).mono, ?_⟩))
    fun s₂ ⟨k₂, cf₂⟩ => ?_)
  · rw [cf₂, heax₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := dl_lt s₀; omega_using [hcl, this])]; rfl
  refine WP.ite (decide (dl s₀ - c < 16)) (by simp only [eval, cf₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ?_
    rcases h with ⟨c', hc⟩ | hd
    · have e : c' = c := by
        have := hc.esi; rw [hesi] at this
        exact (add_ofNat_inj hcl hc.c_le (dl_lt s₀) this).symm
      subst e
      exact .inl ⟨c', hc.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2, hb⟩
    · exact .inr (hd.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2)
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    rcases h with ⟨c', hc⟩ | hd
    · have e : c' = c := by
        have := hc.esi; rw [hesi] at this
        exact (add_ofNat_inj hcl hc.c_le (dl_lt s₀) this).symm
      subst e
      exact WP.mono (whole_loop hp hF (hc.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2) hb)
        fun s' h' => .inl h'
    · have := hd.esi; rw [hesi] at this
      have := add_ofNat_inj hcl (Nat.le_refl _) (dl_lt s₀) this
      omega_using [hb, this]

/-! ## The stack below `esp`

`pairs` leaves other bytes in the 524 bytes below `esp`. What follows it is
proved as from a state `t₀` that is `s₀` with those bytes (`Rebase`): the
precondition, the words `setup` left and the invariant hold of `t₀` as of
`s₀`, since nothing they say reads the stack. -/

namespace UPre
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem stk_eq : below (s₀.gpr .esp) 524 = stkR s₀ := by
  show (⟨(s₀.gpr .esp - BitVec.ofNat 32 524).setWidth 64, 524⟩ : Region) = _
  rw [VG.X86.Taint.sub_setWidth hp.sp_stk]

/-- The stack is apart from the arguments and the return address. -/
theorem stk_args : (stkR s₀).Disjoint ⟨argAddr s₀ 0, 24⟩ ∧ (stkR s₀).Disjoint (retR s₀) := by
  have hn := hp.sp_stk
  have hf := hp.sp_fit
  have hS : (s₀.gpr .esp - BitVec.ofNat 32 524).toNat + 552 ≤ 2 ^ 32 := by
    rw [sub_toNat hn]; omega_using [hn, hf]
  have e1 : stkR s₀ = ⟨addr (s₀.gpr .esp - BitVec.ofNat 32 524) 0, 524⟩ := by
    rw [Proof.Aes.X86.addr_zero, ← hp.stk_eq]
  have e2 : argAddr s₀ 0 = addr (s₀.gpr .esp - BitVec.ofNat 32 524) 528 := by
    have := Proof.Aes.X86.addr_add (s₀.gpr .esp - BitVec.ofNat 32 524) 524 4
    rw [BitVec.sub_add_cancel] at this
    exact this
  have e3 : (s₀.gpr .esp).setWidth 64 = addr (s₀.gpr .esp - BitVec.ofNat 32 524) 524 := by
    have := Proof.Aes.X86.addr_add (s₀.gpr .esp - BitVec.ofNat 32 524) 524 0
    rw [BitVec.sub_add_cancel, Proof.Aes.X86.addr_zero] at this
    exact this
  rw [e1, e2, show retR s₀ = ⟨(s₀.gpr .esp).setWidth 64, 4⟩ from rfl, e3]
  exact ⟨Proof.Aes.X86.part_disj hS (by decide) (by decide) (.inl (by decide)),
    Proof.Aes.X86.part_disj hS (by decide) (by decide) (.inl (by decide))⟩

end UPre

/-- The precondition holds of a state with the same `esp`, arguments and
regions. -/
theorem UPre.congr {s₀ t₀ : State} (hp : UPre s₀) (g : t₀.gpr .esp = s₀.gpr .esp) (hrd : t₀.rd = s₀.rd)
    (hwr : t₀.wr = s₀.wr) (ha : ∀ i < 6, arg t₀ i = arg s₀ i) : UPre t₀ := by
  have a0 := ha 0 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  have eD : dR t₀ = dR s₀ := by
    show (⟨(arg t₀ 3).setWidth 64, (arg t₀ 4).toNat⟩ : Region) = _; rw [a3, a4]
  have eS : sR (stp t₀) = sR (stp s₀) := by show sR (arg t₀ 0) = _; rw [a0]
  have eC : scR t₀ = scR s₀ := by show (⟨(arg t₀ 5).setWidth 64, 128⟩ : Region) = _; rw [a5]
  have eA : argAddr t₀ 0 = argAddr s₀ 0 := by
    show (t₀.gpr .esp + _).setWidth 64 = _; rw [g]; rfl
  have eR : retR t₀ = retR s₀ := by show (⟨(t₀.gpr .esp).setWidth 64, 4⟩ : Region) = _; rw [g]
  have eK : stkR t₀ = stkR s₀ := by
    show (⟨(t₀.gpr .esp).setWidth 64 - BitVec.ofNat 64 524, 524⟩ : Region) = _; rw [g]
  exact
    { rd := by rw [hrd, eD, eA]; exact hp.rd
      wr := by rw [hwr, eS, eC]; exact hp.wr
      st_d := by rw [eS, eD]; exact hp.st_d
      st_sc := by rw [eS, eC]; exact hp.st_sc
      d_sc := by rw [eD, eC]; exact hp.d_sc
      arg_st := by rw [eA, eS]; exact hp.arg_st
      arg_sc := by rw [eA, eC]; exact hp.arg_sc
      ret_st := by rw [eR, eS]; exact hp.ret_st
      ret_sc := by rw [eR, eC]; exact hp.ret_sc
      stk_st := by rw [eK, eS]; exact hp.stk_st
      stk_d := by rw [eK, eD]; exact hp.stk_d
      stk_sc := by rw [eK, eC]; exact hp.stk_sc
      st_fit := by show (arg t₀ 0).toNat + 128 ≤ _; rw [a0]; exact hp.st_fit
      d_fit := by show (arg t₀ 3).toNat + (arg t₀ 4).toNat ≤ _; rw [a3, a4]; exact hp.d_fit
      sc_fit := by rw [a5]; exact hp.sc_fit
      sp_stk := by rw [g]; exact hp.sp_stk
      sp_fit := by rw [g]; exact hp.sp_fit }

/-- A state in the middle of `update` satisfies the precondition, with the
arguments of the state on entry. -/
theorem UCommon.mid {s₀ s : State} {F : Nat → Nat} (hp : UPre s₀) (h : UCommon s₀ F s) :
    UPre s ∧ ∀ i < 6, arg s i = arg s₀ i := by
  have ha : ∀ i < 6, arg s i = arg s₀ i := fun i hi => by
    show s.mem.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = _
    rw [h.esp]; exact hp.arg_same h.frame hi
  exact ⟨hp.congr h.esp h.rd h.wr ha, ha⟩

/-- `t₀` is `s₀` with other bytes in the stack below `esp`. -/
structure Rebase (s₀ t₀ : State) : Prop where
  gpr : t₀.gpr = s₀.gpr
  rd : t₀.rd = s₀.rd
  wr : t₀.wr = s₀.wr
  frame : Frame [stkR s₀] s₀.mem t₀.mem

theorem Rebase.refl (s₀ : State) : Rebase s₀ s₀ := ⟨rfl, rfl, rfl, Frame.refl _ _⟩

namespace Rebase
variable {s₀ t₀ : State} (h : Rebase s₀ t₀) (hp : UPre s₀)
include h hp

theorem arg_eq {i : Nat} (hi : i < 6) : arg t₀ i = arg s₀ i := by
  show t₀.mem.readW (addr (t₀.gpr .esp) (4 + 4 * i)) 32 = s₀.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32
  rw [h.gpr]
  exact h.frame.readW (arg_contains (n := 24) (by have := hp.sp_fit; omega_using [this]) (by omega_using [hi]))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.stk_args.1.symm) (by decide)

theorem stp_eq : stp t₀ = stp s₀ := h.arg_eq hp (by decide)
theorem dp_eq : dp t₀ = dp s₀ := h.arg_eq hp (by decide)
theorem dl_eq : dl t₀ = dl s₀ := congrArg BitVec.toNat (h.arg_eq hp (i := 4) (by decide))
theorem kb_eq : kb t₀ = kb s₀ := congrArg (fun x : BitVec 32 => x.toNat % 16) (h.arg_eq hp (i := 1) (by decide))

/-- Bytes of the state. -/
theorem stBytes {d n : Nat} (hd : d + n ≤ 128) :
    bytesAt t₀.mem (addr (stp s₀) d) n = bytesAt s₀.mem (addr (stp s₀) d) n :=
  Sse2.bytesAt_frame h.frame (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.stk_st.symm.sub_left (Proof.Aes.X86.part_sub_reg hp.st_fit hd)) (by omega_using [hd])

/-- Bytes of the data. -/
theorem dBytes {n : Nat} (hn : n ≤ dl s₀) :
    bytesAt t₀.mem ((dp s₀).setWidth 64) n = bytesAt s₀.mem ((dp s₀).setWidth 64) n :=
  Sse2.bytesAt_frame h.frame (fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.stk_d.symm.sub_left (Region.sub_prefix hn)) (by have := dl_lt s₀; omega_using [hn, this])

theorem words_eq {k : Nat} (hk : k < 32) : words t₀.mem (stp s₀) k = words s₀.mem (stp s₀) k :=
  congrArg BitVec.toNat (wd_frame h.frame (x := stp s₀) (d := 4 * k) fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.stk_st.symm.sub_left (Proof.Aes.X86.part_sub_reg hp.st_fit (by omega_using [hk])))

theorem Dt_eq {c : Nat} (hc : c ≤ dl s₀) : Dt t₀ c = Dt s₀ c := by
  show bytesAt t₀.mem ((dp t₀).setWidth 64) c = _
  rw [h.dp_eq hp]; exact h.dBytes hp hc

theorem Bf_eq : Bf t₀ = Bf s₀ := by
  show bytesAt t₀.mem (addr (stp t₀) 56) (kb t₀) = _
  rw [h.stp_eq hp, h.kb_eq hp]
  exact h.stBytes hp (by have := kb_lt s₀; omega_using [this])

theorem A0_eq : A0 t₀ = A0 s₀ := by
  show leNum (bytesAt t₀.mem ((stp t₀).setWidth 64) 24) = _
  rw [h.stp_eq hp, ← Proof.Aes.X86.addr_zero, h.stBytes hp (by decide), Proof.Aes.X86.addr_zero]

theorem Rn_eq : Rn t₀ = Rn s₀ := by
  simp only [Rn, r0v, qv, h.stp_eq hp, h.words_eq hp (show 6 < 32 by decide),
    h.words_eq hp (show 6 + 1 < 32 by decide), h.words_eq hp (show 6 + 2 < 32 by decide),
    h.words_eq hp (show 6 + 3 < 32 by decide)]

theorem upre : UPre t₀ :=
  hp.congr (by rw [h.gpr]) h.rd h.wr fun _ hi => h.arg_eq hp hi

theorem setupF {F : Nat → Nat} (hF : SetupF s₀ F) : SetupF t₀ F := by
  refine ⟨fun k h₁ h₂ => ?_, ?_, ?_⟩
  · rw [h.stp_eq hp, h.words_eq hp (by omega_using [h₁])]; exact hF.low k h₁ h₂
  · have := hF.saved
    unfold SavedIn at this ⊢
    simp only [v, h.gpr]; exact this
  · have e := hF.coefs
    simp only [r0v, qv, h.stp_eq hp, h.words_eq hp (show 6 < 32 by decide),
      h.words_eq hp (show 6 + 1 < 32 by decide), h.words_eq hp (show 6 + 2 < 32 by decide),
      h.words_eq hp (show 6 + 3 < 32 by decide)] at e ⊢
    exact e

/-- The invariant of `t₀`, from what holds in terms of `s₀`. -/
theorem cons {F : Nat → Nat} {c : Nat} {s : State} (hctx : Ctx (stp s₀) s) (hesp : s.gpr .esp = s₀.gpr .esp)
    (hfr : Frame [sR (stp s₀)] t₀.mem s.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hkeep : ∀ k < 32, k ∉ hS → (k < 14 ∨ 18 ≤ k) → words s.mem (stp s₀) k = F k) (hcl : c ≤ dl s₀)
    (hwh : (kb s₀ + c) % 16 = 0) (hesi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c)
    (hacc : Acc s₀ (Bf s₀ ++ Dt s₀ c) s.mem) : Cons t₀ F c s :=
  { ctx := by rw [h.stp_eq hp]; exact hctx
    esp := by rw [h.gpr]; exact hesp
    frame := by rw [h.stp_eq hp]; exact hfr
    rd := by rw [h.rd]; exact hrd
    wr := by rw [h.wr]; exact hwr
    keep := by rw [h.stp_eq hp]; exact hkeep
    c_le := by rw [h.dl_eq hp]; exact hcl
    whole := by rw [h.kb_eq hp]; exact hwh
    esi := by rw [h.dp_eq hp]; exact hesi
    acc := by
      unfold Acc
      rw [h.A0_eq hp, h.Rn_eq hp, h.Bf_eq hp, h.Dt_eq hp hcl, h.stp_eq hp]
      exact hacc }

theorem abi {s' : State} (hab : abiPreserved t₀ s') : abiPreserved s₀ s' := by
  obtain ⟨h1, h2⟩ := hab
  refine ⟨fun r hr => by rw [← h.gpr]; exact h1 r hr, ?_⟩
  rw [h.gpr] at h2
  rw [h2]
  exact h.frame.readW (r := retR s₀) (Region.contains_self _ _)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.stk_args.2.symm) (by decide)

theorem post {s' : State} (hpost : Proof.Poly1305.updateX86.post t₀ s') :
    Proof.Poly1305.updateX86.post s₀ s' := by
  intro key msg hbuf hcnt
  have a0 := h.arg_eq hp (i := 0) (by decide)
  have a1 := h.arg_eq hp (i := 1) (by decide)
  have a2 := h.arg_eq hp (i := 2) (by decide)
  have a3 := h.arg_eq hp (i := 3) (by decide)
  have a4 := h.arg_eq hp (i := 4) (by decide)
  have hb : Buffered t₀.mem ((arg t₀ 0).setWidth 64) key msg := by
    rw [a0]
    exact Proof.Poly1305.buffered_congr (fun i hi => h.frame _ fun r hr hc => by
      rw [List.mem_singleton.mp hr] at hc
      exact hp.stk_st _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))) hbuf
  have hc : Proof.Poly1305.countX86 t₀ = BitVec.ofNat 64 msg.length := by
    have e : Proof.Poly1305.countX86 t₀ = Proof.Poly1305.countX86 s₀ := by
      simp only [Proof.Poly1305.countX86, a2, a1]
    exact e.trans hcnt
  have := hpost key msg hb hc
  rw [a0, a3, a4] at this
  rw [← h.dBytes hp (Nat.le_refl _)]
  exact this

end Rebase

theorem ofNat_shr5 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 5 = BitVec.ofNat 32 (n / 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega_using [hn])]

/-- The number of pairs into `ecx`: what `pairs` starts from. -/
private theorem pairsArg_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {c : Nat} {s : State}
    (h : Cons s₀ F c s) (hc : 256 ≤ dl s₀ - c) (heax : s.gpr .eax = BitVec.ofNat 32 (dl s₀ - c)) :
    WP isa (.block [.mov .ecx (.reg .eax), .shift .shr .ecx 5]) s fun s₂ =>
      Cons s₀ F c s₂ ∧ Sse2.PPre (stp s₀) (dp s₀ + BitVec.ofNat 32 c) ((dl s₀ - c) / 32) s₂ := by
  have hdl := dl_lt s₀
  have hdf := hp.d_fit
  have hcl := h.c_le
  obtain ⟨p, hpdef⟩ : ∃ p, p = (dl s₀ - c) / 32 := ⟨_, rfl⟩
  rw [← hpdef]
  have hp8 : 2 ≤ p := by omega_using [hpdef, hc]
  have hpl : c + 32 * p ≤ dl s₀ := by omega_using [hpdef, hc]
  refine wp_mov fun s₁ u₁ _ => wp_shr (by decide) fun s₂ u₂ => WP.block_nil ?_
  have hC₂ : Cons s₀ F c s₂ := h.regs (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr])
  have hdn : (dp s₀ + BitVec.ofNat 32 c).toNat = (dp s₀).toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega_using [hcl, hdl]),
      Nat.mod_eq_of_lt (by omega_using [hdf, hpl, hp8])]
  have hsub : Region.Sub (Proof.Aes.X86.reg32 (dp s₀ + BitVec.ofNat 32 c) (32 * p)) (dR s₀) :=
    Proof.Aes.X86.part_sub_reg (b := dp s₀) (a := c) hdf hpl
  exact ⟨hC₂,
    { ctx := hC₂.ctx, esi := hC₂.esi
      ecx := by rw [u₂.gpr, u₁.gpr, heax, ofNat_shr5 (by omega_using [hdl]), hpdef]
      two := hp8
      dfit := by rw [hdn]; omega_using [hdf, hpl]
      din := fun d hd => by
        rw [hC₂.rd, hC₂.wr, hp.rd, hp.data_addr (by omega_using [hd, hpl])]
        exact ⟨dR s₀, by simp, hp.dR_contains (by omega_using [hd, hpl])⟩
      sp := by rw [hC₂.esp]; exact hp.sp_stk
      ss := by rw [hC₂.esp, hp.stk_eq]; exact hp.stk_st
      sd := by rw [hC₂.esp, hp.stk_eq]; exact hp.stk_d.sub_right hsub
      ds := hp.st_d.sub_right hsub }⟩

/-- The pairs of blocks: the invariant then holds of a state `t₀` that is
`s₀` with the bytes `pairs` left in the stack. -/
private theorem pairsRun_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {c p : Nat} {s₂ : State}
    (hC₂ : Cons s₀ F c s₂) (hP : Sse2.PPre (stp s₀) (dp s₀ + BitVec.ofNat 32 c) p s₂) (hpl : c + 32 * p ≤ dl s₀) :
    WP isa pairs s₂ fun s' => ∃ t₀, Rebase s₀ t₀ ∧ Cons t₀ F (c + 32 * p) s' := by
  have hdl := dl_lt s₀
  have hsub : Region.Sub (Proof.Aes.X86.reg32 (dp s₀ + BitVec.ofNat 32 c) (32 * p)) (dR s₀) :=
    Proof.Aes.X86.part_sub_reg (b := dp s₀) (a := c) hp.d_fit hpl
  refine WP.mono (Sse2.pairs_ok hP.ctx hP.esi hP.ecx hP.two hP.dfit hP.din hP.sp hP.ss hP.sd hP.ds
    (C := A0 s₀ < P) (X := Poly1305.absorbAll (Rn s₀) (A0 s₀) (Bf s₀ ++ Dt s₀ c))
    (fun hA => ⟨hF.coefs.congr fun k h₁ h₂ => hC₂.keep k (by omega_using [h₁, h₂])
      (not_hS (.inl ⟨by omega_using [h₁, h₂], h₂⟩)) (.inr h₁), (hC₂.acc hA).1, (hC₂.acc hA).2⟩))
    fun s' ⟨g, esi, rd, wr, fr, same, hv⟩ => ?_
  rw [hC₂.esp, hp.stk_eq] at fr
  -- `s₀` with the stack's bytes of `s'`.
  obtain ⟨t₀, ht⟩ : ∃ t₀ : State, t₀ = { s₀ with
      mem := fun x => if (stkR s₀).Contains x 1 then s'.mem x else s₀.mem x } := ⟨_, rfl⟩
  have hR : Rebase s₀ t₀ := by
    subst ht
    exact ⟨rfl, rfl, rfl, fun x hx => ite_eq_right (hx _ (List.mem_singleton_self _))⟩
  have hfr : Frame [sR (stp s₀)] t₀.mem s'.mem := fun x hx => by
    subst ht
    show s'.mem x = if (stkR s₀).Contains x 1 then s'.mem x else s₀.mem x
    by_cases hx' : (stkR s₀).Contains x 1
    · rw [ite_eq_left hx']
    · rw [ite_eq_right hx', fr x (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hx _ (List.mem_singleton_self _)
        · exact hx'), hC₂.frame x hx]
  refine ⟨t₀, hR, hR.cons hp (hC₂.ctx.keep (g _ (by decide) (by decide)) wr)
    (by rw [g _ (by decide) (by decide)]; exact hC₂.esp) hfr (by rw [rd]; exact hC₂.rd) (by rw [wr]; exact hC₂.wr)
    (fun k hk hS' h' => (same k hk hS').trans (hC₂.keep k hk hS' h')) hpl
    (by have := hC₂.whole; omega_using [this])
    (by rw [esi, BitVec.add_assoc, ← BitVec.ofNat_add]) fun hA => ?_⟩
  obtain ⟨h4, hv'⟩ := hv hA
  refine ⟨h4, ?_⟩
  have h16 : (Bf s₀ ++ Dt s₀ c).length % 16 = 0 := by
    simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; exact hC₂.whole
  have eb : bytesAt s₂.mem ((dp s₀ + BitVec.ofNat 32 c).setWidth 64) (32 * p) =
      bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c) (32 * p) := by
    rw [Sse2.bytesAt_frame hC₂.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.st_d.sub_right hsub).symm) (by omega_using [hpl, hdl]),
      hp.data_bytes hpl]
  rw [hv', eb, Dt_add, ← List.append_assoc, Poly1305.absorbAll_append h16]

/-- The data left, compared with 16 blocks. -/
theorem leftCmp_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State}
    (h : (∃ c, Cons s₀ F c s) ∨ Done s₀ F s) :
    WP isa (.block (left ++ ([.alu .cmp .eax (.imm 256)] : List Instr))) s fun s₂ =>
      ∃ c, c ≤ dl s₀ ∧ s.gpr .esi = dp s₀ + BitVec.ofNat 32 c ∧ Keeps [.eax, .ecx] s s₂ ∧
        s₂.gpr .eax = BitVec.ofNat 32 (dl s₀ - c) ∧ s₂.cf = some (decide (dl s₀ - c < 256)) := by
  obtain ⟨c, hcl, hesi⟩ := Pos.whole h
  obtain hU : UCommon s₀ F s := by rcases h with ⟨_, hc⟩ | hd; exacts [hc.toUCommon, hd.toUCommon]
  refine WP.block_append (WP.mono (left_ok hp hU hcl hesi) fun s₁ ⟨k₁, heax₁, _⟩ =>
    wp_cmpx (readSrc_imm _ _) fun s₂ k₂ _ cf₂ => WP.block_nil
      ⟨c, hcl, hesi, (k₁.trans k₂).mono, by rw [k₂.gpr']; exact heax₁, ?_⟩)
  rw [cf₂, heax₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := dl_lt s₀; omega_using [hcl, this])]; rfl

/-- From 16 blocks on, the pairs of blocks. -/
theorem pairsPart_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s s₂ : State}
    (h : (∃ c, Cons s₀ F c s) ∨ Done s₀ F s) {c : Nat} (hcl : c ≤ dl s₀)
    (hesi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c) (k₂ : Keeps [.eax, .ecx] s s₂)
    (heax₂ : s₂.gpr .eax = BitVec.ofNat 32 (dl s₀ - c)) (cf₂ : s₂.cf = some (decide (dl s₀ - c < 256))) :
    WP isa (.ite .b (.block []) (.seq (.block [.mov .ecx (.reg .eax), .shift .shr .ecx 5]) pairs)) s₂ fun s₃ =>
      ∃ t₀, Rebase s₀ t₀ ∧ ((∃ c, Cons t₀ F c s₃) ∨ Done t₀ F s₃) := by
  refine WP.ite (decide (dl s₀ - c < 256)) (by simp only [eval, cf₂]) (fun hb => ?_) (fun hb => ?_)
  · refine WP.block_nil ⟨s₀, Rebase.refl s₀, ?_⟩
    rcases h with ⟨c', hc⟩ | hd
    · exact .inl ⟨c', hc.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2⟩
    · exact .inr (hd.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2)
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    rcases h with ⟨c', hc⟩ | hd
    · have e : c' = c := by
        have := hc.esi; rw [hesi] at this
        exact (add_ofNat_inj hcl hc.c_le (dl_lt s₀) this).symm
      subst e
      refine WP.seq (WP.mono (pairsArg_ok hp (hc.regs (k₂.gpr') (k₂.gpr') (k₂.gpr') k₂.2.1 k₂.2.2.1 k₂.2.2.2)
        hb heax₂) fun s₃ ⟨hC₃, hP₃⟩ => WP.mono (pairsRun_ok (p := (dl s₀ - c') / 32) hp hF hC₃ hP₃
          (by omega_using [hb]))
          fun s' ⟨t₀, hR, h'⟩ => ⟨t₀, hR, .inl ⟨_, h'⟩⟩)
    · have := hd.esi; rw [hesi] at this
      have := add_ofNat_inj hcl (Nat.le_refl _) (dl_lt s₀) this
      omega_using [hb, this]

/-- The whole blocks of the data. -/
theorem whole_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (h : (∃ c, Cons s₀ F c s) ∨ Done s₀ F s) :
    WP isa whole s fun s' => ∃ t₀, Rebase s₀ t₀ ∧
      ((∃ c, Cons t₀ F c s' ∧ dl t₀ - c < 16) ∨ Done t₀ F s') := by
  refine WP.seq (WP.mono (leftCmp_ok hp h) fun s₂ ⟨c, hcl, hesi, k₂, heax₂, cf₂⟩ => ?_)
  exact WP.seq (WP.mono (pairsPart_ok hp hF h hcl hesi k₂ heax₂ cf₂) fun s₃ ⟨t₀, hR, h₃⟩ =>
    WP.mono (whole16_ok (hR.upre hp) (hR.setupF hp hF) h₃) fun s₄ h₄ => ⟨t₀, hR, h₄⟩)

/-! ## The rest of the data -/

/-- All the data consumed, into whole blocks. -/
theorem Cons.done {s₀ s : State} {F : Nat → Nat} {c : Nat} (h : Cons s₀ F c s) (hc : c = dl s₀) :
    Done s₀ F s :=
  { h.toUCommon with
    esi := by rw [h.esi, hc]
    done := ⟨Bf s₀ ++ Dt s₀ c, [], h.acc,
      by simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; exact h.whole, by simp,
      by rw [hc, List.append_nil], rfl⟩ }

theorem rest_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} {s : State}
    (h : (∃ c, Cons s₀ F c s ∧ dl s₀ - c < 16) ∨ Done s₀ F s) :
    WP isa rest s (Done s₀ F) := by
  have hfit := hp.st_fit
  obtain ⟨c, hcl, hesi⟩ : ∃ c, c ≤ dl s₀ ∧ s.gpr .esi = dp s₀ + BitVec.ofNat 32 c := by
    rcases h with ⟨c, hc, _⟩ | hd
    · exact ⟨c, hc.c_le, hc.esi⟩
    · exact ⟨dl s₀, (Nat.le_refl _), hd.esi⟩
  obtain hU : UCommon s₀ F s := by rcases h with ⟨_, hc, _⟩ | hd; exacts [hc.toUCommon, hd.toUCommon]
  refine WP.seq (WP.mono (Q := fun s₂ : State => Keeps [.eax, .ecx] s s₂ ∧
      s₂.gpr .eax = BitVec.ofNat 32 (dl s₀ - c) ∧ s₂.zf = some (decide (dl s₀ - c = 0)))
    (WP.block_append (WP.mono (left_ok hp hU hcl hesi) fun s₁ ⟨k₁, heax₁, _⟩ =>
      wp_test fun s₂ k₂ z₂ => WP.block_nil ⟨(k₁.trans k₂).mono, by rw [k₂.gpr']; exact heax₁, ?_⟩))
    fun s₂ ⟨k₂, heax₂, z₂⟩ => ?_)
  · rw [z₂, heax₁, BitVec.and_self, ofNat32_beq_zero (by have := dl_lt s₀; omega_using [hcl, this])]
  refine WP.ite (decide (dl s₀ - c = 0)) (by simp only [eval, z₂]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ?_
    rcases h with ⟨c', hc, _⟩ | hd
    · have e : c' = c := add_ofNat_inj hc.c_le hcl (dl_lt s₀) (hc.esi.symm.trans hesi)
      subst e
      exact (hc.regs k₂.gpr' k₂.gpr' k₂.gpr' k₂.2.1 k₂.2.2.1 k₂.2.2.2).done (by have := hc.c_le; omega_using [hcl, hb])
    · exact hd.regs k₂.gpr' k₂.gpr' k₂.gpr' k₂.2.1 k₂.2.2.1 k₂.2.2.2
  · simp only [decide_eq_false_iff_not] at hb
    rcases h with ⟨c', hc, hlt⟩ | hd
    · have e : c' = c := add_ofNat_inj hc.c_le hcl (dl_lt s₀) (hc.esi.symm.trans hesi)
      subst e
      obtain hc₂ := hc.regs k₂.gpr' k₂.gpr' k₂.gpr' k₂.2.1 k₂.2.2.1 k₂.2.2.2
      refine WP.seq (wp_mov fun s₃ u₃ _ => WP.block_nil ?_)
      obtain hc₃ := hc₂.regs (u₃.other _ (by decide)) (u₃.other _ (by decide)) (u₃.other _ (by decide)) u₃.mem
        u₃.rd u₃.wr
      refine WP.mono (copy_ok (m₀ := s₀.mem) (j0 := 0) (n := dl s₀ - c') hfit (by omega_using [hlt]) (by omega_using [hlt, hb])
        (by rw [hc₃.wr]; exact hp.st_in)
        (hp.srcOk hc₃.rd hc₃.wr hc₃.frame (c := c') (n := dl s₀ - c') (by omega_using [hlt, hcl, hb]) (by omega_using [hlt, hb])) hc₃.esi
        (by rw [u₃.gpr, hc₂.ctx.edi]; simp) (by rw [u₃.other _ (by decide), heax₂])) fun s' hcp => ?_
      obtain hf := hcp.frame (by omega_using [hlt])
      obtain hU' : UCommon s₀ F s' := hc₃.toUCommon.buf (hcp.keep _ (by decide) (by decide) (by decide) (by decide))
        (hcp.keep _ (by decide) (by decide) (by decide) (by decide)) hf hcp.rd hcp.wr hfit
      obtain hY : (bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c') (dl s₀ - c')).length = dl s₀ - c' :=
        Poly1305.length_bytesAt _ _ _
      refine { hU' with
        esi := by rw [hcp.esi, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' hc.c_le]
        done := ⟨Bf s₀ ++ Dt s₀ c', bytesAt s₀.mem ((dp s₀).setWidth 64 + BitVec.ofNat 64 c') (dl s₀ - c'),
          hc₃.acc.words fun k hk => words_bf hfit hf (by omega_using [hk]) (by omega_using [hk]), ?_, by omega_using [hlt, hY], ?_, ?_⟩ }
      · simp only [List.length_append, Dt, Bf, Poly1305.length_bytesAt]; exact hc.whole
      · rw [List.append_assoc, ← Dt_add, Nat.add_sub_cancel' hc.c_le]
      · have hb' := hcp.buf (by omega_using [hlt, hY])
        rw [Nat.zero_add, hp.data_bytes (by omega_using [hlt, hcl, hb, hY])] at hb'
        rw [hY, hb']
        rfl
    · have := add_ofNat_inj (Nat.le_refl _) hcl (dl_lt s₀) (hd.esi.symm.trans hesi)
      omega_using [hb, this]

/-! ## Epilogue -/

theorem uepilogue_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s : State}
    (hd : Done s₀ F s) :
    WP isa (.block (reduce ++ restore)) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Poly1305.updateX86.post s₀ s' := by
  have hfit := hp.st_fit
  refine WP.mono (finish_ok hd.ctx) fun s₂ ⟨b₂, si₂, di₂, bp₂, sp₂, _, _, fr₂, z₂, hk₂, _, hr₂⟩ => ?_
  obtain hframe : Frame [sR (stp s₀)] s₀.mem s₂.mem := hd.frame.trans fr₂
  refine ⟨abi_of hF.saved ?_ ?_ ?_ ?_ (by rw [sp₂, hd.esp]) ?_, fun key msg hbuf hcnt => ?_⟩
  · rw [b₂, hd.keep 29 (by decide) (by decide) (by decide)]
  · rw [si₂, hd.keep 30 (by decide) (by decide) (by decide)]
  · rw [di₂, hd.keep 31 (by decide) (by decide) (by decide)]
  · rw [bp₂, hd.keep 5 (by decide) (by decide) (by decide)]
  · exact hframe.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · obtain ⟨W, rfl, hrep⟩ := buffered_split hfit hbuf (count_mod16 hcnt)
    obtain ⟨X, Y, hacc, hX, hY, hXY, hbufY⟩ := hd.done
    obtain hA := A0_lt hrep
    obtain ⟨hcl, hac⟩ := repr_acc hfit hrep
    obtain ⟨h4, hv⟩ := hacc hA
    rw [show W ++ Bf s₀ ++ bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat = W ++ X ++ Y by
      rw [List.append_assoc, show bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat = Dt s₀ (dl s₀)
        from rfl, hXY, List.append_assoc]]
    refine Buffered.of ⟨?_, ?_, ?_⟩ hY ?_
    · rw [List.length_append]; have := hrep.1; omega_using [hX, this]
    · rw [key_same hfit fun k h₁ h₂ => ?_]
      · exact hrep.2.1
      · rw [hk₂ k (by omega_using [h₁, h₂]) (not_hS (.inl ⟨by omega_using [h₁, h₂], by omega_using [h₁, h₂]⟩)) (by omega_using [h₁, h₂]),
          hd.keep k (by omega_using [h₁, h₂]) (not_hS (.inl ⟨by omega_using [h₁, h₂], by omega_using [h₁, h₂]⟩)) (by omega_using [h₁, h₂]), hF.low k (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂])]
    · rw [leNum_acc hfit (words_ok _ _), z₂, hcl, Poly1305.accumulate_append hrep.1, hac, hr₂ h4, hv,
        Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hA _)]
      simp
    · rw [← bq_eq hfit, bytes_words hfit (fun k h₁ h₂ => hk₂ k (by omega_using [h₁, h₂])
        (by simp only [hS, List.mem_cons, List.not_mem_nil, or_false]; omega_using [h₁, h₂]) (by omega_using [h₁, h₂])) (by omega_using [hY]), hbufY]

/-! ## The whole function -/

theorem update_eq : update = .seq (.block (setup ++ ([.mov .esi (.mem (at_ .esp 16)),
    .mov .edx (.mem (at_ .esp 8)), .alu .and .edx (.imm 15), .alu .test .edx (.reg .edx)] : List Instr)))
    (.seq (.ite .e (.block []) fill) (.seq whole (.seq rest (.block (reduce ++ restore))))) := rfl

/-- Nothing buffered: nothing of the data is consumed yet. -/
theorem Pre1.cons {s₀ s : State} {F : Nat → Nat} (h : Pre1 s₀ F s) (hk : kb s₀ = 0) : Cons s₀ F 0 s :=
  { h.toUCommon with
    c_le := Nat.zero_le _, whole := by rw [hk]
    esi := by rw [h.esi]; simp
    acc := by
      obtain e : Bf s₀ ++ Dt s₀ 0 = [] := by simp only [Bf, Dt, hk]; rfl
      rw [e]; exact h.acc }

/-- The buffered bytes, if any, with the first of the data. -/
theorem fillPart_ok {s₀ : State} (hp : UPre s₀) {F : Nat → Nat} (hF : SetupF s₀ F) {s₁ : State}
    (h₁ : Pre1 s₀ F s₁) (hedx : s₁.gpr .edx = BitVec.ofNat 32 (kb s₀))
    (hz : s₁.zf = some (BitVec.ofNat 32 (kb s₀) &&& BitVec.ofNat 32 (kb s₀) == 0)) :
    WP isa (.ite .e (.block []) fill) s₁ fun s => (∃ c, Cons s₀ F c s) ∨ Done s₀ F s := by
  refine WP.ite (BitVec.ofNat 32 (kb s₀) &&& BitVec.ofNat 32 (kb s₀) == 0) (by simp [eval, hz])
    (fun h => ?_) (fun _ => fill_ok hp hF h₁ hedx)
  rw [BitVec.and_self, ofNat32_beq_zero (by have := kb_lt s₀; omega_using [this])] at h
  simp only [decide_eq_true_eq] at h
  exact WP.block_nil (.inl ⟨0, h₁.cons h⟩)

theorem update_correct {s₀ : State} (hp : UPre s₀) :
    WP isa update s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.updateX86.post s₀ s' := by
  rw [update_eq]
  refine WP.seq (WP.mono (uprologue_ok hp) fun s₁ ⟨F, hF, h₁, hedx, hz⟩ => ?_)
  refine WP.seq (WP.mono (fillPart_ok hp hF h₁ hedx hz) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (whole_ok hp hF h₂) fun s₃ ⟨t₀, hR, h₃⟩ => ?_)
  have hp' := hR.upre hp
  exact WP.seq (WP.mono (rest_ok hp' h₃) fun s₄ h₄ =>
    WP.mono (uepilogue_ok hp' (hR.setupF hp hF) h₄) fun s₅ ⟨ha, hpo⟩ => ⟨hR.abi hp ha, hR.post hp hpo⟩)

/-! ## Constant time and satisfiability -/

/-- The taint with the stack arguments public, and the registers `rs`
besides `esp` (and the flags, if `fl`). The analysis starts from
`updateτ [] false`. -/
def updateτ (rs : List Reg) (fl : Bool) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: rs), flags := fl, argLen := 28 }

theorem update_wf {s : State} (hp : UPre s) (rs : List Reg) (fl : Bool) : VG.X86.Taint.Wf (updateτ rs fl) s := by
  have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨by simp only [updateτ]; omega_using [hs], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega_using [hs]) hp.ret_st hp.arg_st
  · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega_using [hs]) hp.ret_sc hp.arg_sc

/-- Two states that satisfy the precondition, with the same `esp`,
arguments and registers `rs`, agree on what `updateτ rs false` says is public. -/
theorem update_agree {s₁ s₂ : State} (hp₁ : UPre s₁) (hp₂ : UPre s₂) (hesp : s₁.gpr .esp = s₂.gpr .esp)
    (ha : ∀ i < 6, arg s₁ i = arg s₂ i) {rs : List Reg} (hr : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.X86.Taint.Agree (updateτ rs false) s₁ s₂ := by
  refine ⟨⟨fun r hr' => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, update_wf hp₁ rs false,
    update_wf hp₂ rs false, VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega_using [hi]))
      h4 hk⟩
  simp only [updateτ, RegSet.mem_ofList, List.mem_cons] at hr'
  rcases hr' with rfl | hr'
  · exact hesp
  · exact hr r hr'

/-- Two runs of `update` from states that satisfy the precondition, with
the same `esp` and arguments, leak the same. The taint analysis checks the
code before, between and after the pairs of blocks, from taints that it shows
the states to agree on (`rel_check`): `esp`, the pointers `esi` and `edi`,
and the stack arguments; the two runs of `pairs` are related by
`Sse2.pairs_rel`, from states the correctness proof describes, and the
states they end in satisfy the precondition again, with the same arguments
(`UCommon.mid`). -/
private theorem update_rel {a b : State} (ha : UPre a) (hb : UPre b) (hesp : a.gpr .esp = b.gpr .esp)
    (harg : ∀ i < 6, arg a i = arg b i) : RelCT isa (Eq2 a b) update (fun _ _ => True) := by
  have est : stp b = stp a := (harg 0 (by decide)).symm
  have edp : dp b = dp a := (harg 3 (by decide)).symm
  have edl : dl b = dl a := congrArg BitVec.toNat (harg 4 (by decide)).symm
  have tEnd : ∃ h, (VG.X86.taint.check (updateτ [.esi, .edi] false)
      (.seq rest (.block (reduce ++ restore))) h).isSome = true := ⟨_, by taint_decide⟩
  have t16 : ∃ h, (VG.X86.taint.check (updateτ [.esi, .edi] false)
      (.seq (.block (left ++ ([.alu .cmp .eax (.imm 16)] : List Instr)))
        (.ite .b (.block []) (.loop (.block (absorb 1 ++ ([.alu .add .esi (.imm 16)] : List Instr) ++ left ++
          ([.alu .cmp .eax (.imm 16)] : List Instr))) .ae))) h).map
      (VG.X86.taint.le (updateτ [.esi, .edi] false)) = some true := ⟨_, by taint_decide⟩
  rw [update_eq]
  refine rel_seqR (rel_check (updateτ [.esi, .edi, .edx] true)
      (update_agree ha hb hesp harg (rs := []) fun _ h => absurd h List.not_mem_nil) ⟨_, by taint_decide⟩)
    (uprologue_ok ha) (uprologue_ok hb) fun x₁ y₁ A₁ ⟨F₁, hF₁, p₁, dx₁, z₁⟩ ⟨F₂, hF₂, p₂, dx₂, z₂⟩ => ?_
  refine rel_seqR (rel_check (updateτ [.esi, .edi] false) A₁ ⟨_, by taint_decide⟩)
    (fillPart_ok ha hF₁ p₁ dx₁ z₁) (fillPart_ok hb hF₂ p₂ dx₂ z₂) fun x₂ y₂ A₂ g₁ g₂ => ?_
  refine rel_then (Q := fun _ _ => True) (R := VG.X86.Taint.Agree (updateτ [.esi, .edi] false)) ?_
    fun x₃ y₃ A₃ => rel_checkT A₃ tEnd
  -- `whole`.
  unfold whole
  refine rel_seqR (rel_check (updateτ [.esi, .edi, .eax] true) A₂ ⟨_, by taint_decide⟩)
    (leftCmp_ok ha g₁) (leftCmp_ok hb g₂)
    fun x y A ⟨c₁, hc₁, si₁, k₁, ax₁, cf₁⟩ ⟨c₂, hc₂, si₂, k₂, ax₂, cf₂⟩ => ?_
  have ec : c₂ = c₁ := by
    have e := A₂.reg (r := .esi) rfl
    rw [si₁, si₂, edp] at e
    exact (add_ofNat_inj hc₁ (edl ▸ hc₂) (dl_lt a) e).symm
  subst ec
  rw [edl] at cf₂ ax₂
  refine rel_then (R := VG.X86.Taint.Agree (updateτ [.esi, .edi] false)) ?_
    fun x₃ y₃ A₃ => rel_check (updateτ [.esi, .edi] false) A₃ t16
  -- The pairs, taken by both runs or by neither.
  refine rel_iteR (b := decide (dl a - c₂ < 256)) cf₁ cf₂ (fun _ => RelCT.nil fun u v huv => by
    obtain ⟨rfl, rfl⟩ := huv
    exact VG.X86.taint.le_sound (τ := updateτ [.esi, .edi] false) (by decide) A) fun hbq => ?_
  have hb256 : 256 ≤ dl a - c₂ := by simpa using hbq
  -- Both runs are in the middle of the data.
  have hcons : ∀ {s₀ s s' : State} {F : Nat → Nat}, (∃ c, Cons s₀ F c s) ∨ Done s₀ F s → c₂ ≤ dl s₀ →
      s.gpr .esi = dp s₀ + BitVec.ofNat 32 c₂ → 256 ≤ dl s₀ - c₂ → Keeps [.eax, .ecx] s s' → Cons s₀ F c₂ s' :=
    fun {s₀ s s' F} g hc hsi h256 k => by
      rcases g with ⟨c', hC⟩ | hd
      · have e : c' = c₂ := by
          have := hC.esi; rw [hsi] at this
          exact (add_ofNat_inj hc hC.c_le (dl_lt s₀) this).symm
        subst e
        exact hC.regs (k.gpr') (k.gpr') (k.gpr') k.2.1 k.2.2.1 k.2.2.2
      · have := hd.esi; rw [hsi] at this
        have := add_ofNat_inj hc (Nat.le_refl _) (dl_lt s₀) this
        omega_using [h256, this]
  have C₁ := hcons g₁ hc₁ si₁ hb256 k₁
  have C₂ := hcons g₂ hc₂ si₂ (by rw [edl]; exact hb256) k₂
  refine rel_seqR (rel_taint [] (fun _ h => absurd h List.not_mem_nil) ⟨_, by taint_decide⟩)
    (pairsArg_ok ha C₁ hb256 ax₁) (pairsArg_ok hb C₂ (by rw [edl]; exact hb256) (by rw [edl]; exact ax₂))
    fun x₄ y₄ _ ⟨D₁, P₁⟩ ⟨D₂, P₂⟩ => ?_
  rw [est, edp, edl] at P₂
  have hpl : c₂ + 32 * ((dl a - c₂) / 32) ≤ dl a := by omega_using [hb256]
  refine ((Sse2.pairs_rel P₁ P₂ (by rw [D₁.esp, D₂.esp]; exact hesp)).wp
    (F₁ := fun s' => ∃ t₀, Rebase a t₀ ∧ Cons t₀ F₁ (c₂ + 32 * ((dl a - c₂) / 32)) s')
    (F₂ := fun s' => ∃ t₀, Rebase b t₀ ∧ Cons t₀ F₂ (c₂ + 32 * ((dl a - c₂) / 32)) s')
    fun u v huv => by
      obtain ⟨rfl, rfl⟩ := huv
      exact ⟨pairsRun_ok ha hF₁ D₁ P₁ hpl, pairsRun_ok hb hF₂ D₂ (by rw [est, edp]; exact P₂) (by rw [edl]; exact hpl)⟩).mono
    (fun _ _ h => h) fun x' y' ⟨_, ⟨t₁, R₁, K₁⟩, ⟨t₂, R₂, K₂⟩⟩ => ?_
  -- The states after the pairs satisfy the precondition, with the same arguments.
  obtain ⟨hx', ax'⟩ := K₁.toUCommon.mid (R₁.upre ha)
  obtain ⟨hy', ay'⟩ := K₂.toUCommon.mid (R₂.upre hb)
  refine update_agree hx' hy' (by rw [K₁.esp, K₂.esp, R₁.gpr, R₂.gpr]; exact hesp)
    (fun i hi => by rw [ax' i hi, ay' i hi, R₁.arg_eq ha hi, R₂.arg_eq hb hi]; exact harg i hi) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [K₁.esi, K₂.esi, R₁.dp_eq ha, R₂.dp_eq hb, edp]
  · rw [K₁.ctx.edi, K₂.ctx.edi, R₁.stp_eq ha, R₂.stp_eq hb, est]

/-- Memory holding the arguments `0x1000, 0, 0, 0x2000, 0, 0x3000` at `0x4004`. -/
def updateSatMem : Mem := fun a =>
  bif Nat.beq a.toNat 0x4005 then 0x10 else bif Nat.beq a.toNat 0x4011 then 0x20 else bif Nat.beq a.toNat 0x4019 then 0x30 else 0

/-- A state satisfying the precondition (with no data). -/
def updateSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := updateSatMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 24⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 128⟩]

theorem update_ok (s : State) (hs : Proof.Poly1305.updateX86.pre s) :
    ∃ t s', Exec isa update s t s' ∧ abiPreserved s s' ∧ Proof.Poly1305.updateX86.post s s' :=
  update_correct (UPre.of s hs)

theorem update_ct : ConstantTime isa Proof.Poly1305.updateX86.pre Proof.Poly1305.updateX86.pub
    update :=
  ct_of fun _ _ h₁ h₂ hp => update_rel (UPre.of _ h₁) (UPre.of _ h₂) hp.1 hp.2

theorem update_verified :
    Verified X86.target Impl.Poly1305.X86.update (Proof.Poly1305.updateScratchContract X86.abi 524) :=
  Verified.of_correct update_ok update_ct (by
    obtain a0 : arg updateSat 0 = 0x1000 := by decide
    obtain a3 : arg updateSat 3 = 0x2000 := by decide
    obtain a4 : arg updateSat 4 = 0 := by decide
    obtain a5 : arg updateSat 5 = 0x3000 := by decide
    obtain e : argAddr updateSat 0 = 0x4004 := by decide
    have esp : updateSat.gpr .esp = 0x4000 := rfl
    sig_implies [Proof.Poly1305.updateScratchContract, Proof.Poly1305.updateScratchSig, Spec.Poly1305.updatePost, Proof.Poly1305.updateX86,
      Proof.Poly1305.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [a0, a3, a4, a5, e, esp] using Proof.Poly1305.X86.updateSat)

end VG.Proof.Poly1305.X86

end

end

/-!
# Streaming Poly1305 on x86, with its working space on the stack

`update` and `finalize` run their code, proved with the working space as an
argument, in a frame that allocates it and copies the arguments passed on
the stack (`Verified.stackScratch`): the return address, the copied
arguments (five slots for `update`, four for `finalize`) and the 128 bytes
of working space. The copies are read only where the postconditions read
the buffers (`Proof/Poly1305/Scratch.lean`).
-/

@[expose] public section

namespace VG.Proof.Poly1305.X86

open VG VG.X86

/-- A state satisfying `vg_poly1305_update`'s precondition, without the
working space. -/
def updateFrameSat : State :=
  { updateSat with rd := [⟨0x2000, 0⟩, ⟨0x4004, 20⟩], wr := [⟨0x1000, 128⟩] }

theorem updateFrameSat_pre : ∃ s, (Spec.Poly1305.updateContract X86.abi 680).pre s := by
  implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, Spec.Poly1305.updatePost,
    X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateFrameSat, updateSat, updateSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using updateFrameSat

theorem update_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 156 5 Impl.Poly1305.X86.update)
      (Spec.Poly1305.updateContract X86.abi 680) :=
  X86.Verified.stackScratch (sig := Spec.Poly1305.updateSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.updatePost X86.abi.ptrBits) (wa := false) (stack := 524)
    (bytes := 156) update_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (updatePost_local _)
    (fun vs m m₁ m₂ r hl _ hb => updatePostOut_local _ vs m m₁ m₂ r hl hb)
    updateFrameSat_pre

/-- A state satisfying `vg_poly1305_finalize`'s precondition, without the
working space. -/
def finalizeFrameSat : State :=
  { finalizeSat with rd := [⟨0x4004, 16⟩], wr := [⟨0x1000, 128⟩, ⟨0x2000, 16⟩] }

theorem finalizeFrameSat_pre : ∃ s, (Spec.Poly1305.finalizeContract X86.abi 152).pre s := by
  implies_sat [Spec.Poly1305.finalizeContract, Spec.Poly1305.finalizeSig,
    Spec.Poly1305.finalizePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finalizeFrameSat, finalizeSat, finalizeSatMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
    using finalizeFrameSat

theorem finalize_framed :
    Verified X86.target (Impl.StackScratch.X86.withStackScratch 152 4 Impl.Poly1305.X86.finalize)
      (Spec.Poly1305.finalizeContract X86.abi 152) :=
  X86.Verified.stackScratch (sig := Spec.Poly1305.finalizeSig) (nm := "scratch") (e := .u64)
    (n := 16) (post := Spec.Poly1305.finalizePost X86.abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 152) finalize_verified (by decide) (by lit_decide) (by lit_decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finalizePost_local _)
    (fun vs m m₁ m₂ r hl _ hb => finalizePostOut_local _ vs m m₁ m₂ r hl hb)
    finalizeFrameSat_pre

end VG.Proof.Poly1305.X86
