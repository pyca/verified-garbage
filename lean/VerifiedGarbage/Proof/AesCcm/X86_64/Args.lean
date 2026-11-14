module

public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Proof.AesCcm.X86_64.Env
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.AesCcm.X86_64.Run
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee

/-! ### `AesCcm.X86_64.Entry`, which only this module used -/

section

/-!
# AES-CCM on x86-64: the entry and the exit (`entry`, `restore`)

Untrusted: everything here is checked by Lean. `entry` reads the stack
arguments but `tag`, saves our caller's registers at `W + 112` and keeps the arguments
in `W` (`entry_ok`); `restore` reads the registers back (`restore_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)

/-- Our caller's registers, saved at `W + 112`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The save area and the slots, which `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 112, 128⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} {s : State} (P : Perm K W s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (hsp : s.gpr .rsp = SP) (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr))
    (hargsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    ∃ s₁, runBlock isa entry s = some s₁ ∧ Env K W SP s₁ ∧ Slots W R N A D nl al n tl s₁.mem ∧
      Saved s₁.mem W s.gpr ∧ Frame [entryR W] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₁₆ := in_off (d := 8) (n := 8) hargs (by decide) (by decide)
  have a₃₂ := in_off (d := 24) (n := 8) hargs (by decide) (by decide)
  have a₄₀ := in_off (d := 32) (n := 8) hargs (by decide) (by decide)
  rw [add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [add_ofNat_assoc] at a₁₆ a₃₂ a₄₀
  have w₁ := P.wW (show 112 + 8 ≤ 2560 by decide)
  have w₂ := P.wW (show 120 + 8 ≤ 2560 by decide)
  have w₃ := P.wW (show 128 + 8 ≤ 2560 by decide)
  have w₄ := P.wW (show 136 + 8 ≤ 2560 by decide)
  have w₅ := P.wW (show 144 + 8 ≤ 2560 by decide)
  have w₆ := P.wW (show 152 + 8 ≤ 2560 by decide)
  have w₇ := P.wW (show 160 + 8 ≤ 2560 by decide)
  have w₈ := P.wW (show 168 + 8 ≤ 2560 by decide)
  have w₉ := P.wW (show 176 + 8 ≤ 2560 by decide)
  have w₁₀ := P.wW (show 184 + 8 ≤ 2560 by decide)
  have w₁₁ := P.wW (show 192 + 8 ≤ 2560 by decide)
  have w₁₂ := P.wW (show 200 + 8 ≤ 2560 by decide)
  have w₁₃ := P.wW (show 208 + 8 ≤ 2560 by decide)
  have w₁₄ := P.wW (show 232 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h⟩ : ∃ s₁, runBlock isa
      ([.mov .rax (.mem (at_ .rsp 40)), .mov .r10 (.mem (at_ .rsp 8)), .mov .r11 (.mem (at_ .rsp 16))] ++ save .rax ++
        [.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
          .store (at_ .r15 nonceO) .rdx, .store (at_ .r15 nlenO) .rcx, .store (at_ .r15 aadO) .r8,
          .store (at_ .r15 alenO) .r9, .store (at_ .r15 dataO) .r10, .store (at_ .r15 lenO) .r11]) s = some s₁ ∧
      s₁.gpr .rsp = SP ∧ s₁.gpr .r15 = W ∧ s₁.gpr .r13 = K ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      Frame [entryR W] s.mem s₁.mem ∧ Saved s₁.mem W s.gpr ∧
      s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R ∧ s₁.mem.readW (W + BitVec.ofNat 64 160) 64 = N ∧
      s₁.mem.readW (W + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 nl ∧
      s₁.mem.readW (W + BitVec.ofNat 64 176) 64 = A ∧
      s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al ∧
      s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = D ∧
      s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by
    have cE : ∀ d, 112 ≤ d → d + 8 ≤ 240 → (entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains W h₁ (by omega_using [h₂]) (by decide)
    refine ⟨_, by crun [save, saved, List.map_cons, List.map_nil, hW, hsp, hD, hn, a₈, a₁₆, a₄₀, w₁, w₂, w₃, w₄,
      w₅, w₆, w₇, w₈, w₉, w₁₀, w₁₁, w₁₂, w₁₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hsp]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
    · rfl
    · rfl
    · simp only [mem_setReg]
      repeat (first | exact Frame.refl _ _ |
        refine Frame.writeW ?_ (List.mem_singleton_self _) _ (cE _ (by decide) (by decide)))
    · intro p hp
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64]
    all_goals simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
      ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9]
  obtain ⟨hsp₁, h15, h13, hrd₁, hwr₁, f₁, sv₁, s232, s160, s168, s176, s184, s192, s200⟩ := h
  have htl₁ : s₁.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl := by
    rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have e : SP + BitVec.ofNat 64 32 = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 24 := by rw [add_ofNat_assoc]
      rw [e]
      exact (hargsW.sub_left (Offset.sub_base _ (by decide))).sub_right (Lay.wSub (by decide))) (by decide), htl]
  have a₃₂' : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 32) 8 := by rw [hrd₁, hwr₁]; exact a₃₂
  have w₁₃' : InRegions s₁.wr (W + BitVec.ofNat 64 208) 8 := by rw [hwr₁]; exact w₁₃
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .rax (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rax] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 tl) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by crun [hsp₁, h15, htl₁, a₃₂', w₁₃'], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg]
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have k : ∀ {d}, (d + 8 ≤ 208 ∨ 216 ≤ d) → d + 8 ≤ 2 ^ 64 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ => by
    rw [hm₂, readW_writeW_off _ (by omega_using [h₁]) h₂ (by decide)]
  refine ⟨s₂, ?_, ⟨by rw [hg₂ _ (by decide), h13], by rw [hg₂ _ (by decide), h15], by rw [hg₂ _ (by decide), hsp₁],
    P.of_eq (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁])⟩,
    ⟨by rw [k (by omega_using []) (by decide), s232], by rw [k (by omega_using []) (by decide), s160],
      by rw [k (by omega_using []) (by decide), s168], by rw [k (by omega_using []) (by decide), s176],
      by rw [k (by omega_using []) (by decide), s184], by rw [k (by omega_using []) (by decide), s192],
      by rw [k (by omega_using []) (by decide), s200], by rw [hm₂, Mem.readW_writeW_self64]⟩,
    fun p hp => ?_, ?_, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [show entry = ([.mov .rax (.mem (at_ .rsp 40)), .mov .r10 (.mem (at_ .rsp 8)),
        .mov .r11 (.mem (at_ .rsp 16))] ++ save .rax ++
        [.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
          .store (at_ .r15 nonceO) .rdx, .store (at_ .r15 nlenO) .rcx, .store (at_ .r15 aadO) .r8,
          .store (at_ .r15 alenO) .r9, .store (at_ .r15 dataO) .r10, .store (at_ .r15 lenO) .r11]) ++
        [.mov .rax (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rax] by
      simp only [entry, List.append_assoc, List.cons_append, List.nil_append],
      runBlock_append, run₁, Option.bind_some, run₂]
  · have hp' := hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [← sv₁ p hp]
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k (by decide) (by decide)
  · rw [hm₂]
    exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains W (d := 208) (n := 8) (e := 112) (k := 128)
      (by decide) (by decide) (by decide))

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {g : Reg → BitVec 64} (hs : Saved s.mem W g) :
    ∃ s', runBlock isa restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 112 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 120 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 128 + 8 ≤ 2560 by decide)
  have r₄ := E.perm.wR (show 136 + 8 ≤ 2560 by decide)
  have r₅ := E.perm.wR (show 144 + 8 ≤ 2560 by decide)
  have r₆ := E.perm.wR (show 152 + 8 ≤ 2560 by decide)
  have v₁ := hs (.rbx, 112) (by decide)
  have v₂ := hs (.rbp, 120) (by decide)
  have v₃ := hs (.r12, 128) (by decide)
  have v₄ := hs (.r13, 136) (by decide)
  have v₅ := hs (.r14, 144) (by decide)
  have v₆ := hs (.r15, 152) (by decide)
  refine ⟨_, by crun [restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesCcm.X86_64

end

end


/-!
# AES-CCM on x86-64: the arguments

Untrusted: everything here is checked by Lean. The preconditions `sealPre`
and `openPre` give the facts the proofs use about the arguments (`Args`,
`TagBuf`, `args_of_seal`, `args_of_open`). Between `entry` and `restore`, the
pieces only write the parts of `W` below 112, from 216 to 232 and from 240
on, the stack below `SP` and the data (`mutR`), so they keep the slots, the
saved registers, the key schedule, the nonce, the associated data, the tag's
address on the stack (`argT_kept`) and the received tag (`tag_kept`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64
open VG.Impl.AesCcm.X86_64 (saved)
open VG.Spec.Aes (bytesAt)

/-- What `seal` and `open` are given: the key schedule at `K` for `R`
rounds, the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), a tag of `tl` bytes, the working space at
`W` and the stack pointer `SP`. -/
structure Args (s : State) (K W SP N A D : Addr) (R nl al n tl : Nat) : Prop where
  lay : Lay K W SP
  perm : Perm K W s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  nonce : Buf K W SP s N nl
  aad : Buf K W SP s A al
  data : Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩
  nd : (⟨N, nl⟩ : Region).Disjoint ⟨D, n⟩
  ad : (⟨A, al⟩ : Region).Disjoint ⟨D, n⟩
  h7 : 7 ≤ nl
  h13 : nl ≤ 13
  t4 : 4 ≤ tl
  t16 : tl ≤ 16
  te : tl % 2 = 0
  hn : n < 256 ^ (15 - nl)
  retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 2560⟩
  retD : (⟨SP, 8⟩ : Region).Disjoint ⟨D, n⟩
  args : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr)
  argsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩
  argsD : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩

/-- The tag, the `tl` bytes at `T`: apart from the data, `W` and the stack
below `SP`. -/
structure TagBuf (W SP D : Addr) (n : Nat) (T : Addr) (tl : Nat) : Prop where
  d : (⟨T, tl⟩ : Region).Disjoint ⟨D, n⟩
  w : (⟨T, tl⟩ : Region).Disjoint ⟨W, 2560⟩
  stk : (below SP 16).Disjoint ⟨T, tl⟩
  wrap : T.toNat + tl ≤ 2 ^ 64

/-- `Args` from the layout, with the buffers covered as each function's
permissions say. -/
theorem args_of_lay {s : State} (h : oneLay s)
    (hk : Covers [⟨s.gpr .rdi, 240⟩] (s.rd ++ s.wr)) (hN : Covers [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩] (s.rd ++ s.wr))
    (hA : Covers [⟨s.gpr .r8, (s.gpr .r9).toNat⟩] (s.rd ++ s.wr)) (ha : Covers [args s 5] (s.rd ++ s.wr))
    (hD : Covers [⟨arg s 0, (arg s 1).toNat⟩] s.wr) (hW : Covers [⟨arg s 4, 2560⟩] s.wr) :
    Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat ∧
      TagBuf (arg s 4) (s.gpr .rsp) (arg s 0) (arg s 1).toNat (arg s 2) (arg s 3).toNat := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, b20, b21, b22, b23,
    b24, b25, b26, _, hR, hv⟩ := h
  simp only [Spec.Ccm.valid, Spec.Ccm.tagLenOk, Spec.Ccm.nonceLenOk, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hv
  obtain ⟨⟨⟨⟨⟨ht4, ht16⟩, hte⟩, hn7, hn13⟩, hp⟩, -⟩ := hv
  rw [Nat.pow_mul] at hp
  exact ⟨{
    lay := ⟨b20, b25, d2, d14, d19, b26⟩
    perm := ⟨hk, hW⟩
    rounds := hR
    nonce := ⟨hN, BitVec.isLt _, b21, d4, d15⟩
    aad := ⟨hA, BitVec.isLt _, b22, d6, d16⟩
    data := ⟨covers_left hD, BitVec.isLt _, b23, d9, d17⟩
    dw := hD
    dk := d1
    nd := d3
    ad := d5
    h7 := hn7
    h13 := hn13
    t4 := ht4
    t16 := ht16
    te := hte
    hn := hp
    retW := d13
    retD := d12
    args := ha
    argsW := d11.symm
    argsD := d10.symm }, ⟨d7, d8, d18, b24⟩⟩

/-- `seal`'s arguments, and its tag, to write. -/
theorem args_of_seal {s : State} (h : sealPre s) :
    (Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat ∧
      TagBuf (arg s 4) (s.gpr .rsp) (arg s 0) (arg s 1).toNat (arg s 2) (arg s 3).toNat) ∧
      Covers [⟨arg s 2, (arg s 3).toNat⟩] s.wr ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨arg s 2, (arg s 3).toNat⟩ := by
  obtain ⟨hrd, hwr, hl, hrt⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      args s 5], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨arg s 0, (arg s 1).toNat⟩ : Region), ⟨arg s 2, (arg s 3).toNat⟩, ⟨arg s 4, 2560⟩],
      Covers [r] s.wr := fun r hr => covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mwr _ (by simp), hrt⟩

/-- `open`'s arguments, and its received tag, to read. -/
theorem args_of_open {s : State} (h : openPre s) :
    (Args s (s.gpr .rdi) (arg s 4) (s.gpr .rsp) (s.gpr .rdx) (s.gpr .r8) (arg s 0) (s.gpr .rsi).toNat
        (s.gpr .rcx).toNat (s.gpr .r9).toNat (arg s 1).toNat (arg s 3).toNat ∧
      TagBuf (arg s 4) (s.gpr .rsp) (arg s 0) (arg s 1).toNat (arg s 2) (arg s 3).toNat) ∧
      Covers [⟨arg s 2, (arg s 3).toNat⟩] (s.rd ++ s.wr) := by
  obtain ⟨hrd, hwr, hl⟩ := h
  have mrd : ∀ r ∈ [(⟨s.gpr .rdi, 240⟩ : Region), ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
      ⟨arg s 2, (arg s 3).toNat⟩, args s 5], Covers [r] (s.rd ++ s.wr) := fun r hr =>
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr))
  have mwr : ∀ r ∈ [(⟨arg s 0, (arg s 1).toNat⟩ : Region), ⟨arg s 4, 2560⟩], Covers [r] s.wr := fun r hr =>
    covers_of_mem (by rw [hwr]; exact hr)
  exact ⟨args_of_lay hl (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mrd _ (by simp)) (mwr _ (by simp))
    (mwr _ (by simp)), mrd _ (by simp)⟩

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

/-- What the pieces before the data is written may change. -/
abbrev wR (W SP : Addr) : List Region := [wA W, wK W, wC W, below SP 16]

theorem wR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ wR W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  refine ⟨r, ?_, fun _ h => h⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl <;> simp

section
variable {K W SP N A D : Addr} {R nl al n tl : Nat} {m m' : Mem}

theorem slots_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') (S : Slots W R N A D nl al n tl m) : Slots W R N A D nl al n tl m' := by
  have k : ∀ d, (112 ≤ d ∧ d + 8 ≤ 216 ∨ 232 ≤ d ∧ d + 8 ≤ 240) →
      m'.readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 := fun d hd =>
    hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD hd) (by decide)
  exact ⟨by rw [k 232 (by decide)]; exact S.rounds, by rw [k 160 (by decide)]; exact S.nonce,
    by rw [k 168 (by decide)]; exact S.nlen, by rw [k 176 (by decide)]; exact S.aad,
    by rw [k 184 (by decide)]; exact S.alen, by rw [k 192 (by decide)]; exact S.data,
    by rw [k 200 (by decide)]; exact S.len, by rw [k 208 (by decide)]; exact S.tl⟩

theorem saved_mut (L : Lay K W SP) (hD : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (mutR W SP D n) m m') {g : Reg → BitVec 64} (S : Saved m W g) : Saved m' W g := by
  intro p hp
  rw [← S p hp]
  have hd : 112 ≤ p.2 ∧ p.2 + 8 ≤ 216 := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact hf.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (w := 64) (Region.contains_self _ _) (kept_mut L hD (.inl hd))
    (by decide)

theorem ciph_mut (L : Lay K W SP) (hdk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hf : Frame (mutR W SP D n) m m') : Spec.Ccm.ctxCiph m' K R = Spec.Ccm.ctxCiph m K R :=
  ctxCiph_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.k_w.sub_right (Region.sub_prefix (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact L.stk_k.symm
    · exact hdk) (by rcases hR with h | h | h <;> subst h <;> decide)

theorem buf_mut {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len)
    (hPD : (⟨P, len⟩ : Region).Disjoint ⟨D, n⟩) (hf : Frame (mutR W SP D n) m m') :
    bytesAt m' P len = bytesAt m P len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
    · exact hPD) (by have := hP.lt; omega_using [this])

theorem buf_wR {s : State} {P : Addr} {len : Nat} (hP : Buf K W SP s P len) (hf : Frame (wR W SP) m m') :
    bytesAt m' P len = bytesAt m P len :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Region.sub_prefix (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega_using [this])

end

section
variable {K W SP D : Addr} {n : Nat}

/-- The tag's address, at `SP + 24`, is apart from what the entry and the
pieces write. -/
theorem argT_disj (hW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ entryR W :: mutR W SP D n, (⟨SP + BitVec.ofNat 64 24, 8⟩ : Region).Disjoint r := by
  have hs : Region.Sub ⟨SP + BitVec.ofNat 64 24, 8⟩ ⟨SP + BitVec.ofNat 64 8, 40⟩ := by
    rw [show SP + BitVec.ofNat 64 24 = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 16 by rw [add_ofNat_assoc]]
    exact Offset.sub_base _ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hW.sub_left hs).sub_right (Region.sub_prefix (by decide))
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact (hW.sub_left hs).sub_right (Lay.wSub (by decide))
  · exact Offset.disjoint_below SP (by decide)
  · exact hD.sub_left hs

/-- The tag's address, at `SP + 24`, through the entry and the pieces. -/
theorem argT_kept {m m' : Mem} (hf : Frame (entryR W :: mutR W SP D n) m m')
    (hW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨D, n⟩) :
    m'.readW (SP + BitVec.ofNat 64 24) 64 = m.readW (SP + BitVec.ofNat 64 24) 64 :=
  hf.readW (r := ⟨SP + BitVec.ofNat 64 24, 8⟩) (Region.contains_self _ _) (argT_disj hW hD) (by decide)

/-- The received tag, through the entry and the pieces. -/
theorem tag_kept {T : Addr} {tl : Nat} (hT : TagBuf W SP D n T tl) (ht : tl ≤ 16) {m m' : Mem}
    (hf : Frame (entryR W :: mutR W SP D n) m m') : bytesAt m' T tl = bytesAt m T tl :=
  bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Region.sub_prefix (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.w.sub_right (Lay.wSub (by decide))
    · exact hT.stk.symm
    · exact hT.d) (by omega_using [ht])

end

end VG.Proof.AesCcm.X86_64
