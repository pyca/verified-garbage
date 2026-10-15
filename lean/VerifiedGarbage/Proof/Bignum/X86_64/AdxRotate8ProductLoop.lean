module

public import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8ProductStep
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.XmmFrame
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! The product of a modulus block by the eight digits, as a loop indexed by
`rdi`, whose value waits in `xmm0`. -/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

theorem productStepX_ok {s : State} {B : Addr} {Z eU eO eN m j : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (hi : s.gpr .rdi = idx m)
    (hp : s.gpr .rbp = off B eN) (ho : s.gpr .rsi = off B eO)
    (huZ : eU + 8 * m + 8 * j + 8 ≤ Z) (hoZ : eO + 8 * m + 8 * j + 8 ≤ Z) (hnZ : eN + 64 ≤ Z) :
    WP isa (AdxRotate8.productStepX j) s fun t =>
      (word t.mem B (eO + 8 * m + 8 * j)).toNat + 2 ^ 64 * cols t =
        cols s + (word s.mem B (eU + 8 * m + 8 * j)).toNat * wv s.mem B eN 8 ∧
      Outside B (eO + 8 * m + 8 * j) 8 s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  have hsrc := readSrc_word hs (ea_atx hc hi (8 * j)) huZ
  unfold AdxRotate8.productStepX
  refine WP.seq (WP.mono (movMem_ok s (dst := .rdx) hsrc) fun a ⟨ha, _, _, ka⟩ => ?_)
  refine WP.seq (WP.mono (core_mem (hs.congr ka.2.2.2) ((ka.gpr (by decide)).trans hp) hnZ)
    fun b ⟨eb, _, _, kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.mono (storeMem_ok (hs.congr kab.2.2.2)
    (ea_atx ((kab.gpr (by decide)).trans ho) ((kab.gpr (by decide)).trans hi) (8 * j)) hoZ)
    fun t ⟨wt, ot, kt⟩ => ?_
  rw [ha, ka.2.1, cols_keep ka.keep (by decide)] at eb
  refine ⟨?_, ?_, (kab.keep.trans kt).mono (by decide)⟩
  · rw [wt, cols_keep kt (by simp)]; exact eb
  · rw [kab.2.1] at ot; exact ot

theorem productStepsX_ok {s : State} {B : Addr} {Z eU eO eN m n : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (hi : s.gpr .rdi = idx m)
    (hp : s.gpr .rbp = off B eN) (ho : s.gpr .rsi = off B eO)
    (huZ : eU + 8 * m + 8 * n ≤ Z) (hoZ : eO + 8 * m + 8 * n ≤ Z) (hnZ : eN + 64 ≤ Z)
    (hsepU : eU + 64 ≤ eO) (hsepN : eN + 64 ≤ eO) (hmn : m + n ≤ 8) :
    WP isa (AdxRotate8.productStepsX n) s fun t =>
      wv t.mem B (eO + 8 * m) n + 2 ^ (64 * n) * cols t =
        cols s + wv s.mem B (eU + 8 * m) n * wv s.mem B eN 8 ∧
      Outside B (eO + 8 * m) (8 * n) s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  induction n with
  | zero =>
    apply WP.block_nil
    exact ⟨by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add],
      Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    unfold AdxRotate8.productStepsX
    refine WP.seq (WP.mono (ih (by omega_arith) (by omega_arith) (by omega_arith)) fun a ⟨va, oa, ka⟩ => ?_)
    have sa := hs.congr ka.2.2
    have hna := sa.nowrap
    refine WP.mono (productStepX_ok sa ((ka.gpr (by decide)).trans hc) ((ka.gpr (by decide)).trans hi)
      ((ka.gpr (by decide)).trans hp) ((ka.gpr (by decide)).trans ho)
      (by omega_arith) (by omega_arith) hnZ) fun t ⟨vt, ot, kt⟩ => ?_
    have mn : wv a.mem B eN 8 = wv s.mem B eN 8 := oa.wv (by omega_arith) (by omega_arith)
    have mu : word a.mem B (eU + 8 * m + 8 * n) = word s.mem B (eU + 8 * m + 8 * n) :=
      oa.word (by omega_arith) (by omega_arith)
    have lo : wv t.mem B (eO + 8 * m) n = wv a.mem B (eO + 8 * m) n := ot.wv (by omega_arith) (by omega_arith)
    refine ⟨?_, (oa.mono (o' := eO + 8 * m) (n' := 8 * (n + 1)) (by omega_arith) (by omega_arith)).trans
      (ot.mono (o' := eO + 8 * m) (n' := 8 * (n + 1)) (by omega_arith) (by omega_arith)),
      (ka.trans kt).mono (by decide)⟩
    rw [mn, mu] at vt
    rw [wv, wv, lo, pow64_succ]
    grind

theorem not_mem_loop {r : Reg}
    (hr : r ∉ ([.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] : List Reg))
    (hd : r ≠ .rdi) :
    r ∉ ([.rdx, .rax, .rbx, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] : List Reg) ++ [.rdi] := by
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  grind

/-- The product loop's state after `j` iterations. -/
structure ProdInv (s₀ : State) (B : Addr) (Z eU eO eN : Nat) (j : Nat) (s : State) : Prop where
  scr : Scr s B Z
  rcx : s.gpr .rcx = off B eU
  rbp : s.gpr .rbp = off B eN
  rsi : s.gpr .rsi = off B eO
  rdi : s.gpr .rdi = idx (2 * j)
  xmm : (s.xmm .xmm0).extractLsb' 0 64 = s₀.gpr .rdi
  val : wv s.mem B eO (2 * j) + 2 ^ (64 * (2 * j)) * cols s =
    cols s₀ + wv s₀.mem B eU (2 * j) * wv s₀.mem B eN 8
  out : Outside B eO (8 * (2 * j)) s₀.mem s.mem
  keep : Keep [.rdx, .rax, .rbx, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s₀ s

theorem productLoop_ok {s : State} {B : Addr} {Z eU eO eN : Nat}
    (hs : Scr s B Z) (hc : s.gpr .rcx = off B eU) (hp : s.gpr .rbp = off B eN)
    (ho : s.gpr .rsi = off B eO) (hoZ : eO + 8 * 8 ≤ Z) (hnZ : eN + 64 ≤ Z)
    (hsepU : eU + 8 * 8 ≤ eO) (hsepN : eN + 64 ≤ eO) :
    WP isa AdxRotate8.productLoop s fun t =>
      wv t.mem B eO 8 + 2 ^ (64 * 8) * cols t =
        cols s + wv s.mem B eU 8 * wv s.mem B eN 8 ∧
      Outside B eO (8 * 8) s.mem t.mem ∧
      Keep [.rdx, .rax, .rbx, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.productLoop
  rw [show AdxRotate8.unroll = 2 from rfl]
  rw [show [Instr.xop (.movq .xmm0 .rdi), .mov .rdi (.imm (-64))] =
    [.xop (.movq .xmm0 .rdi)] ++ [.mov .rdi (.imm (-64))] from rfl]
  refine WP.seq (WP.block_append (WP.mono (WP.keep [] (Q := fun t =>
      (t.xmm .xmm0).extractLsb' 0 64 = s.gpr .rdi ∧ t.mem = s.mem) ?_ rfl) fun a ⟨⟨xa, ma⟩, ka⟩ => ?_))
  · xrun []
    simp only [XOp.exec, State.setXmm, ite_true, VG.X86_64.KeepReg.xmm_lo_append]
    exact ⟨trivial, trivial⟩
  refine WP.mono (VG.X86_64.KeepReg.WP.keepXmm (idxInit_ok a .rdi) (by decide) (by decide))
    fun a' ⟨⟨ia, ma', ka'⟩, xa'⟩ => ?_
  have kaa := ka.trans ka'
  have h0 : ProdInv s B Z eU eO eN 0 a' := ⟨hs.congr kaa.2.2, (kaa.gpr (by decide)).trans hc,
    (kaa.gpr (by decide)).trans hp, (kaa.gpr (by decide)).trans ho, by simpa only [Nat.mul_zero] using ia,
    by rw [xa']; exact xa,
    by simp only [Nat.mul_zero, wv, Nat.pow_zero, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add,
      cols_keep kaa (by decide)],
    by rw [ma', ma]; exact Outside.refl _ _ _ _, kaa.mono (by decide)⟩
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := 4) (by decide) (ProdInv s B Z eU eO eN) ?body
    (fun _ h => h) h0) fun b hb => ?_)
  case body =>
    intro j _ hj b hb
    have hna := hb.scr.nowrap
    refine WP.mono (VG.X86_64.KeepReg.WP.keepXmm (Q := fun t => t.zf = some (decide (j + 1 = 4)) ∧
        ((t.xmm .xmm0).extractLsb' 0 64 = s.gpr .rdi → ProdInv s B Z eU eO eN (j + 1) t)) ?_
        (by decide) (by decide))
      fun t ⟨⟨zt, ht⟩, xt⟩ => ⟨zt, ht (by rw [xt]; exact hb.xmm)⟩
    refine WP.seq (WP.mono (productStepsX_ok (n := 2) (m := 2 * j) hb.scr hb.rcx hb.rdi hb.rbp hb.rsi
      (by omega) (by omega) hnZ (by omega) hsepN (by omega)) fun c ⟨vc, oc, kc⟩ => ?_)
    refine WP.mono (idxAdd_ok (u := 2) ((kc.gpr (by decide)).trans hb.rdi) (by omega))
      fun t ⟨it, zt, mt, kt⟩ => ⟨by rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega)), fun hx => ?_⟩
    have kct := kc.trans kt
    refine ⟨hb.scr.congr kct.2.2, (kct.gpr (by decide)).trans hb.rcx, (kct.gpr (by decide)).trans hb.rbp,
      (kct.gpr (by decide)).trans hb.rsi, by rw [it]; congr 1, hx, ?_, ?_, (hb.keep.trans kct).mono (by decide)⟩
    · have vb := hb.val
      have wu : wv b.mem B (eU + 8 * (2 * j)) 2 = wv s.mem B (eU + 8 * (2 * j)) 2 :=
        hb.out.wv (by omega) (by omega)
      have wn : wv b.mem B eN 8 = wv s.mem B eN 8 := hb.out.wv (by omega) (by omega)
      rw [wu, wn] at vc
      rw [cols_keep kt (by decide), mt, show 2 * (j + 1) = 2 * j + 2 by omega, wv_add, wv_add (m := s.mem),
        show wv c.mem B eO (2 * j) = wv b.mem B eO (2 * j) from oc.wv (by omega) (by omega),
        show 64 * (2 * j + 2) = 64 * (2 * j) + 64 * 2 by omega, Nat.pow_add]
      grind
    · rw [mt]
      exact (hb.out.mono (o' := eO) (n' := 8 * (2 * (j + 1))) (by omega) (by omega)).trans
        (oc.mono (o' := eO) (n' := 8 * (2 * (j + 1))) (by omega) (by omega))
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = s.gpr .rdi ∧ t.mem = b.mem) ?_ rfl)
    fun t ⟨⟨ht, mt⟩, kt⟩ => ?_
  · xrun [hb.xmm]
  have v := hb.val
  rw [show 2 * 4 = 8 from rfl] at v
  refine ⟨by rw [cols_keep kt (by decide), mt]; exact v, by rw [mt]; exact hb.out, ?_⟩
  refine ⟨fun r hr => ?_, (hb.keep.trans kt).2⟩
  by_cases hd : r = .rdi
  · subst hd; exact ht
  · exact (hb.keep.trans kt).gpr (not_mem_loop hr hd)
end VG.Proof.Bignum.X86_64.AdxRotate8
