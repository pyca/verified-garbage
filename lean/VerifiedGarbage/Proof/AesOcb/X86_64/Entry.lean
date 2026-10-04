import VerifiedGarbage.Proof.AesOcb.X86_64.Callee

/-!
# AES-OCB on x86-64: the entry and the exit (`entry`, `restore`)

Untrusted: everything here is checked by Lean. `entry` reads `W` from the
stack, saves our caller's registers at `W + savO`, keeps the arguments in
`W`, the address of the tag at `W + tgO`, computes `L_$` and `L_0` from
`L_*` and zeroes the checksum (`entry_ok`); `restore` reads the registers
back (`restore_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem ctxLstar lDollar lAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append in_off add_ofNat_assoc)

/-- Our caller's registers, saved at `W + savO`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The parts of `W` that `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 32, 352⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- A stack argument kept in `W`. -/
theorem argSlot_ok {SP W : Addr} {s : State} {a d : Nat} {v : BitVec 64} (hsp : s.gpr .rsp = SP)
    (h15 : s.gpr .r15 = W) (hv : s.mem.readW (SP + BitVec.ofNat 64 a) 64 = v)
    (ra : InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 a) 8) (wd : InRegions s.wr (W + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [ld .rax .rsp a, st .r15 d .rax] s = some s' ∧
      s'.mem = s.mem.writeW (W + BitVec.ofNat 64 d) v ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by orun [hsp, h15, hv, ra, wd], ?_, fun r h => ?_, ?_, ?_⟩
  · simp only [mem_setReg]
  · simp only [gpr_setReg, h, ite_false]
  all_goals rfl

/-- What `entry` leaves. -/
structure EntryPost (K W SP : Addr) (R : Nat) (N A D : Addr) (nl al n tl : Nat) (T : Addr) (s s₁ : State) :
    Prop where
  env : Env K W SP s₁
  slots : Slots W R N A D nl n tl s₁.mem
  tg : s₁.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  alen : s₁.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al
  saved : Saved s₁.mem W s.gpr
  ld : blockAtMem s₁.mem (W + BitVec.ofNat 64 ldO) = lDollar (ctxLstar s.mem K)
  l0 : blockAtMem s₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0
  ck : blockAtMem s₁.mem (W + BitVec.ofNat 64 ckO) = 0
  frame : Frame [entryR W] s.mem s₁.mem
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} (L : Lay K W SP) {s : State} (P : Perm K W s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} {T : Addr} (hsp : s.gpr .rsp = SP)
    (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr))
    (hargsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    ∃ s₁, runBlock isa entry s = some s₁ ∧ EntryPost K W SP R N A D nl al n tl T s s₁ := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₁₆ := in_off (d := 8) (n := 8) hargs (by decide) (by decide)
  have a₂₄ := in_off (d := 16) (n := 8) hargs (by decide) (by decide)
  have a₃₂ := in_off (d := 24) (n := 8) hargs (by decide) (by decide)
  have a₄₀ := in_off (d := 32) (n := 8) hargs (by decide) (by decide)
  rw [add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [add_ofNat_assoc] at a₁₆ a₂₄ a₃₂ a₄₀
  have w₁ := P.wW (show 160 + 8 ≤ 2560 by decide)
  have w₂ := P.wW (show 168 + 8 ≤ 2560 by decide)
  have w₃ := P.wW (show 176 + 8 ≤ 2560 by decide)
  have w₄ := P.wW (show 184 + 8 ≤ 2560 by decide)
  have w₅ := P.wW (show 192 + 8 ≤ 2560 by decide)
  have w₆ := P.wW (show 200 + 8 ≤ 2560 by decide)
  have w₇ := P.wW (show 232 + 8 ≤ 2560 by decide)
  have w₈ := P.wW (show 288 + 8 ≤ 2560 by decide)
  have w₉ := P.wW (show 296 + 8 ≤ 2560 by decide)
  have w₁₀ := P.wW (show 240 + 8 ≤ 2560 by decide)
  have w₁₁ := P.wW (show 248 + 8 ≤ 2560 by decide)
  -- The registers saved, `W` and `K` in `r15` and `r14`, the arguments in registers kept.
  obtain ⟨s₁, run₁, hsp₁, h15₁, h14₁, rd₁, wr₁, f₁, sv₁, s232, s288, s296, s240, s248⟩ : ∃ s₁, runBlock isa
      ([.mov .rax (.mem (at_ .rsp 40))] ++ save .rax ++
        [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
          st .r15 aadO .r8, st .r15 alenO .r9]) s = some s₁ ∧
      s₁.gpr .rsp = SP ∧ s₁.gpr .r15 = W ∧ s₁.gpr .r14 = K ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      Frame [⟨W + BitVec.ofNat 64 160, 144⟩] s.mem s₁.mem ∧ Saved s₁.mem W s.gpr ∧
      s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R ∧ s₁.mem.readW (W + BitVec.ofNat 64 288) 64 = N ∧
      s₁.mem.readW (W + BitVec.ofNat 64 296) 64 = BitVec.ofNat 64 nl ∧
      s₁.mem.readW (W + BitVec.ofNat 64 240) 64 = A ∧
      s₁.mem.readW (W + BitVec.ofNat 64 248) 64 = BitVec.ofNat 64 al := by
    have cE : ∀ d, 160 ≤ d → d + 8 ≤ 304 → (⟨W + BitVec.ofNat 64 160, 144⟩ : Region).Contains
        (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
    refine ⟨_, by orun [save, saved, List.map_cons, List.map_nil, hW, hsp, a₄₀, w₁, w₂, w₃, w₄, w₅, w₆, w₇,
      w₈, w₉, w₁₀, w₁₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
        simp (disch := decide) only [savO, Nat.reduceAdd, mem_setReg, readW_writeW_off, Mem.readW_writeW_self64]
    all_goals simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
      ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9]
  -- The arguments on the stack.
  have dA : ∀ {a d k : Nat}, 8 ≤ a → a + 8 ≤ 48 → d + k ≤ 2560 →
      (⟨SP + BitVec.ofNat 64 a, 8⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ := fun {a d k} h₁ h₂ h₃ => by
    have e : SP + BitVec.ofNat 64 a = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 (a - 8) := by
      rw [add_ofNat_assoc, show 8 + (a - 8) = a by omega]
    rw [e]; exact (hargsW.sub_left (Offset.sub_base _ (by omega))).sub_right (Lay.wSub h₃)
  have kA : ∀ {a : Nat}, 8 ≤ a → a + 8 ≤ 48 →
      s₁.mem.readW (SP + BitVec.ofNat 64 a) 64 = s.mem.readW (SP + BitVec.ofNat 64 a) 64 := fun {a} h₁ h₂ =>
    f₁.readW (r := ⟨SP + BitVec.ofNat 64 a, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dA h₁ h₂ (by decide)) (by decide)
  have sW : ∀ {a d : Nat}, 8 ≤ a → a + 8 ≤ 48 → d + 8 ≤ 2560 → Mem.Sep (SP + BitVec.ofNat 64 a) (64 / 8)
      (W + BitVec.ofNat 64 d) (64 / 8) := fun h₁ h₂ h₃ =>
    (dA h₁ h₂ h₃).sep (Region.contains_self _ _) (Region.contains_self _ _)
  obtain ⟨s₂, run₂, m₂, g₂, rd₂, wr₂⟩ := argSlot_ok (s := s₁) (a := 8) (d := dataO) hsp₁ h15₁
    (by rw [kA (by decide) (by decide), hD]) (by rw [rd₁, wr₁]; exact a₈) (by rw [wr₁]; exact P.wW (by decide))
  obtain ⟨s₃, run₃, m₃, g₃, rd₃, wr₃⟩ := argSlot_ok (s := s₂) (a := 16) (d := lenO)
    (by rw [g₂ _ (by decide), hsp₁]) (by rw [g₂ _ (by decide), h15₁])
    (by rw [m₂, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide),
      kA (by decide) (by decide), hn])
    (by rw [rd₂, wr₂, rd₁, wr₁]; exact a₁₆) (by rw [wr₂, wr₁]; exact P.wW (by decide))
  obtain ⟨s₄, run₄, m₄, g₄, rd₄, wr₄⟩ := argSlot_ok (s := s₃) (a := 32) (d := tlO)
    (by rw [g₃ _ (by decide), g₂ _ (by decide), hsp₁]) (by rw [g₃ _ (by decide), g₂ _ (by decide), h15₁])
    (by rw [m₃, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₂,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), kA (by decide) (by decide), htl])
    (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact a₃₂) (by rw [wr₃, wr₂, wr₁]; exact P.wW (by decide))
  obtain ⟨s₄', run₄', m₄', g₄', rd₄', wr₄'⟩ := argSlot_ok (s := s₄) (a := 24) (d := tgO)
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), hsp₁])
    (by rw [g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h15₁])
    (by rw [m₄, Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₃,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), m₂,
      Mem.readW_writeW_sep (sW (by decide) (by decide) (by decide)) (by decide), kA (by decide) (by decide), hT])
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁]; exact a₂₄) (by rw [wr₄, wr₃, wr₂, wr₁]; exact P.wW (by decide))
  have E₄ : Env K W SP s₄' := ⟨by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h14₁],
    by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), h15₁],
    by rw [g₄' _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), hsp₁],
    P.of_eq (by rw [rd₄', rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄', wr₄, wr₃, wr₂, wr₁])⟩
  -- What the writes of the arguments keep.
  have k₄ : ∀ {d : Nat}, (d + 8 ≤ 208 ∨ 232 ≤ d ∧ d + 8 ≤ 304) → d + 8 ≤ 2560 →
      s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₄', readW_writeW_off _ (by simp only [tgO]; omega) (by omega) (by decide),
      m₄, readW_writeW_off _ (by simp only [tlO]; omega) (by omega) (by decide), m₃,
      readW_writeW_off _ (by simp only [lenO]; omega) (by omega) (by decide), m₂,
      readW_writeW_off _ (by simp only [dataO]; omega) (by omega) (by decide)]
  have fr₄ : Frame [⟨W + BitVec.ofNat 64 208, 104⟩] s₁.mem s₄'.mem := by
    rw [m₄', m₄, m₃, m₂]
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains W (d := 208) (n := 8) (e := 208)
      (k := 104) (by decide) (by decide) (by decide))).writeW (List.mem_singleton_self _) _
      (Offset.contains W (d := 216) (n := 8) (e := 208) (k := 104) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 224) (n := 8) (e := 208) (k := 104) (by decide) (by decide)
        (by decide))).writeW
      (List.mem_singleton_self _) _ (Offset.contains W (d := 304) (n := 8) (e := 208) (k := 104) (by decide) (by decide)
        (by decide))
  have f₁₄ : Frame [⟨W + BitVec.ofNat 64 160, 144⟩, ⟨W + BitVec.ofNat 64 208, 104⟩] s.mem s₄'.mem :=
    (f₁.mono (by simp)).trans (fr₄.mono (by simp))
  -- `L_$`, `L_0` and the checksum.
  have l₄ : blockAtMem s₄'.mem (K + BitVec.ofNat 64 240) = ctxLstar s.mem K := by
    rw [blockAtMem_frame f₁₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide)))]
    rfl
  obtain ⟨s₅, run₅, B₅⟩ := dbl_ok (s := s₄') (b := .r14) (a := 240) (d := ldO) E₄.r15 E₄.r14 (by decide)
    (E₄.perm.kR (by decide)) (E₄.perm.kR (by decide)) (E₄.perm.wW (by decide)) (E₄.perm.wW (by decide))
  have nE : ∀ r ∈ [Reg.r14, .r15, .rsp], r ∉ [Reg.rax, .rdx, .rcx, .r8] := by decide
  have E₅ : Env K W SP s₅ := E₄.keep (fun r hr => B₅.gpr r (nE r hr)) B₅.rd B₅.wr
  obtain ⟨s₆, run₆, B₆⟩ := dbl_ok (s := s₅) (b := .r15) (a := ldO) (d := l0O) E₅.r15 E₅.r15 (by decide)
    (E₅.perm.wR (by decide)) (E₅.perm.wR (by decide)) (E₅.perm.wW (by decide)) (E₅.perm.wW (by decide))
  have E₆ : Env K W SP s₆ := E₅.keep (fun r hr => B₆.gpr r (nE r hr)) B₆.rd B₆.wr
  obtain ⟨s₇, run₇, B₇⟩ := zero16_ok (s := s₆) (d := ckO) E₆.r15 (E₆.perm.wW (by decide)) (E₆.perm.wW (by decide))
  have E₇ : Env K W SP s₇ := E₆.keep (fun r hr => B₇.gpr r (by simp at hr ⊢; rcases hr with rfl | rfl | rfl <;> decide))
    B₇.rd B₇.wr
  have fr₇ : Frame [⟨W + BitVec.ofNat 64 32, 64⟩] s₄'.mem s₇.mem :=
    ((B₅.frame.sub fun r hr => ?_).trans (B₆.frame.sub fun r hr => ?_)).trans (B₇.frame.sub fun r hr => ?_)
  rotate_left
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩
  have k₇ : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ 2560 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    fr₇.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by omega)) h₂ (by decide)) (by decide)
  have k : ∀ {d : Nat}, 232 ≤ d → d + 8 ≤ 304 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [k₇ (by omega) (by omega), k₄ (.inr ⟨h₁, h₂⟩) (by omega)]
  have kd : ∀ {d : Nat}, 208 ≤ d → d + 8 ≤ 2560 →
      s₇.mem.readW (W + BitVec.ofNat 64 d) 64 = s₄'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    k₇ (by omega) (by omega)
  refine ⟨s₇, ?_, ⟨E₇, ⟨?_, ?_, ?_, by rw [k (by decide) (by decide), s232], by rw [k (by decide) (by decide), s240],
    by rw [k (by decide) (by decide), s288], by rw [k (by decide) (by decide), s296]⟩, ?_,
    by rw [show alenO = 248 from rfl, k (by decide) (by decide), s248], fun p hp => ?_, ?_, ?_, B₇.val, ?_,
    by rw [B₇.rd, B₆.rd, B₅.rd, rd₄', rd₄, rd₃, rd₂, rd₁], by rw [B₇.wr, B₆.wr, B₅.wr, wr₄', wr₄, wr₃, wr₂, wr₁]⟩⟩
  · rw [show entry = ([.mov .rax (.mem (at_ .rsp 40))] ++ save .rax ++
        [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
          st .r15 aadO .r8, st .r15 alenO .r9]) ++ [ld .rax .rsp 8, st .r15 dataO .rax] ++
        [ld .rax .rsp 16, st .r15 lenO .rax] ++ [ld .rax .rsp 32, st .r15 tlO .rax] ++
        [ld .rax .rsp 24, st .r15 tgO .rax] ++ dbl .r14 240 ldO ++
        dbl .r15 ldO l0O ++ zero16 ckO by
      simp only [entry, lsetup, List.append_assoc, List.cons_append, List.nil_append],
      runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append, runBlock_append,
      runBlock_append, run₁, Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, run₄,
      Option.bind_some, run₄', Option.bind_some, run₅, Option.bind_some, run₆, Option.bind_some, run₇]
  · rw [kd (by decide) (by decide), m₄', readW_writeW_off _ (by decide) (by decide) (by decide), m₄,
      readW_writeW_off _ (by decide) (by decide) (by decide), m₃,
      readW_writeW_off _ (by decide) (by decide) (by decide), m₂]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄', readW_writeW_off _ (by decide) (by decide) (by decide), m₄,
      readW_writeW_off _ (by decide) (by decide) (by decide), m₃]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄', readW_writeW_off _ (by decide) (by decide) (by decide), m₄]
    exact Mem.readW_writeW_self64 ..
  · rw [kd (by decide) (by decide), m₄']
    exact Mem.readW_writeW_self64 ..
  · have hp' := hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [← sv₁ p hp]
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₇ (by decide) (by decide), k₄ (.inl (by decide)) (by decide)]
  · rw [blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      blockAtMem_frame B₆.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide)),
      B₅.val, l₄]
    rfl
  · rw [blockAtMem_frame B₇.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
      B₆.val, B₅.val, l₄]
    rfl
  · refine (((f₁₄.mono (rs' := [⟨W + BitVec.ofNat 64 160, 144⟩, ⟨W + BitVec.ofNat 64 208, 104⟩,
      ⟨W + BitVec.ofNat 64 32, 64⟩]) (by simp)).trans (fr₇.mono (by simp)))).sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨_, List.mem_singleton_self _, Offset.sub W (by decide) (by decide)⟩

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {g : Reg → BitVec 64} (hs : Saved s.mem W g) :
    ∃ s', runBlock isa restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 160 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 168 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 176 + 8 ≤ 2560 by decide)
  have r₄ := E.perm.wR (show 184 + 8 ≤ 2560 by decide)
  have r₅ := E.perm.wR (show 192 + 8 ≤ 2560 by decide)
  have r₆ := E.perm.wR (show 200 + 8 ≤ 2560 by decide)
  have v₁ := hs (.rbx, 160) (by decide)
  have v₂ := hs (.rbp, 168) (by decide)
  have v₃ := hs (.r12, 176) (by decide)
  have v₄ := hs (.r13, 184) (by decide)
  have v₅ := hs (.r14, 192) (by decide)
  have v₆ := hs (.r15, 200) (by decide)
  refine ⟨_, by orun [restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesOcb.X86_64
