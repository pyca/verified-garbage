module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.CT
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ContractPost
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
public import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64

/-!
# ChaCha20-Poly1305 on x86-64: `open` after the tag

Untrusted: everything here is checked by Lean. `openTail`, which both `open`
and the stitched `openStitched` end with: from the state their bodies leave
(`TailIn`), the tags compared without a branch, the data zeroed if they
differ (`zeroData`), and the registers restored; then `open` from `openBody`
and `openTail`. Constant time: `openBody` by its own proof (`body_rel`),
then the tail from the public data that the correctness proof gives both
runs, the branch being on whether the tag is right, which the contract lets
`open` leak (`openX86_64.pub`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64
open VG.Spec.Poly1305 (Repr bytesAt mac)
open VG.Spec.ChaCha20Poly1305 (macData)

/-! ## The steps -/

set_option simprocs false in
theorem cmp32_ok (s : State) : WP isa (.block [.alu32 .cmp .rax (.imm 0)]) s fun s' =>
    s'.zf = some ((s.gpr .rax).setWidth 32 == 0) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    execAlu32, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by rw [show (BitVec.setWidth 32 (s.gpr .rax) - 0 : BitVec 32) = BitVec.setWidth 32 (s.gpr .rax) from
    BitVec.sub_zero _], trivial, trivial, trivial, trivial, rfl⟩

theorem zeroArgs_ok (s : State) :
    WP isa (.block [.mov .rdx (.reg .r14), .mov .rcx (.reg .r13), .alu .cmp .rcx (.imm 0)]) s fun s' =>
      s'.gpr .rdx = s.gpr .r14 ∧ s'.gpr .rcx = s.gpr .r13 ∧ s'.zf = some (s.gpr .r13 == 0) ∧
      (∀ q, q ≠ .rdx → q ≠ .rcx → s'.gpr q = s.gpr q) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_arithFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ↓reduceIte,
    show BitVec.signExtend 64 (0 : BitVec 32) = 0 by decide]
  exact ⟨trivial, trivial, by rw [show (s.gpr .r13 - 0 : BitVec 64) = s.gpr .r13 from BitVec.sub_zero _],
    fun q a b => by simp [a, b], trivial, trivial, trivial, rfl⟩

theorem zeroStep_run {s : State} {a : Addr} (hd : s.gpr .rdx = a) (hw : InRegions s.wr a 1) :
    WP isa (.block [.store8 { base := .rdx } .rax, .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]) s
      fun s' => s'.mem = s.mem.writeW a ((s.gpr .rax).setWidth 8) ∧ s'.gpr .rdx = a + 1 ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        (∀ q, q ≠ .rdx → q ≠ .rcx → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.mxcsr = s.mxcsr := by
  have he : s.ea { base := .rdx } = a := by show s.gpr .rdx + BitVec.ofInt 64 0 = a; rw [hd]; exact BitVec.add_zero _
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, State.store8, he, hw, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.zf_arithFlags, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    Option.bind_some, Option.some.injEq, exists_eq_left', reduceCtorEq, ↓reduceIte,
    RegUpd.zf_setReg, RegUpd.mxcsr_setReg,
    show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide]
  exact ⟨trivial, by rw [hd], trivial, trivial, fun q a b => by simp [a, b], trivial, trivial, rfl⟩

/-! ## Zeroing the data -/

theorem ofNat64_sub_one {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem ofNat64_ne_zero {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  exact Nat.ne_of_gt h this

/-- What the zeroing keeps, from `s`: the invariant, `rdi` and `rax`, the
memory but the data, and `mxcsr`. -/
structure ZK (s₀ s u : State) : Prop where
  inv : Inv s₀ u
  rdi : u.gpr .rdi = s.gpr .rdi
  rax : u.gpr .rax = s.gpr .rax
  frame : Frame [dR s₀] s.mem u.mem
  mx : u.mxcsr = s.mxcsr

/-- A part that writes only `rdx`, `rcx` and the data keeps `ZK`. -/
theorem ZK.step {s₀ s u u' : State} (hp : APre false s₀) (h : ZK s₀ s u)
    (hg : ∀ q, q ≠ .rdx → q ≠ .rcx → u'.gpr q = u.gpr q) (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr)
    (hf : Frame [dR s₀] u.mem u'.mem) (hmx : u'.mxcsr = u.mxcsr) : ZK s₀ s u' :=
  ⟨h.inv.step (fun r hr => hg r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
      hrd hwr hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, fun _ h => h⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; rdisj),
    by rw [hg _ (by decide) (by decide), h.rdi], by rw [hg _ (by decide) (by decide), h.rax],
    h.frame.trans hf, by rw [hmx, h.mx]⟩

/-- `zeroData`, with the low byte of `rax` zero: zeros at `data`. -/
theorem zeroData_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s)
    (h0 : (s.gpr .rax).setWidth 8 = 0) :
    WP isa zeroData s fun s' => ZK s₀ s s' ∧ bytesAt s'.mem (dp s₀) (L s₀) = List.replicate (L s₀) 0 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have hfit := hp.wrap_d
  have k₀ : ZK s₀ s s := ⟨h, rfl, rfl, Frame.refl _ _, rfl⟩
  unfold zeroData
  refine WP.seq (WP.mono (zeroArgs_ok s) fun u₁ ⟨d₁, c₁, z₁, g₁, m₁, rd₁, wr₁, mx₁⟩ => ?_)
  have k₁ : ZK s₀ s u₁ := k₀.step hp g₁ rd₁ wr₁ (by rw [m₁]; exact Frame.refl _ _) mx₁
  rw [h.r14] at d₁
  rw [h.r13, show s₀.gpr .r9 = BitVec.ofNat 64 (L s₀) by simp] at c₁ z₁
  by_cases hz : L s₀ = 0
  · refine WP.ite true (by show u₁.zf = some true; rw [z₁, hz]; rfl)
      (fun _ => WP.block_nil ⟨k₁, ?_⟩) (by simp)
    rw [hz]; rfl
  · have hne := ofNat64_ne_zero (n := L s₀) (by omega) hL
    refine WP.ite false (by show u₁.zf = some false; rw [z₁, beq_false_of_ne hne]) (by simp) fun _ => ?_
    refine WP.loop (M := isa) (fun rem u => ∃ j, j < L s₀ ∧ rem = L s₀ - j ∧ ZK s₀ s u ∧
      u.gpr .rdx = dp s₀ + BitVec.ofNat 64 j ∧ u.gpr .rcx = BitVec.ofNat 64 (L s₀ - j) ∧
      Proof.Zeroize.Prefix u.mem (dp s₀) j) ?_ (L s₀) u₁
      ⟨0, by omega, by omega, k₁, by rw [d₁]; exact (BitVec.add_zero _).symm, by rw [c₁, Nat.sub_zero],
        fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    intro rem u ⟨j, hj, hr, hu, e1, e2, hpz⟩
    have hc : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 j) 1 :=
      Offset.contains_base _ (by omega) (by omega)
    refine WP.mono (zeroStep_run e1 ⟨dR s₀, by rw [hu.inv.wr]; exact hp.d_wr, hc⟩)
      fun u' ⟨m', d', c', z', g', rd', wr', mx'⟩ => ?_
    have k' : ZK s₀ s u' := hu.step hp g' rd' wr'
      (by rw [m']; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc) mx'
    have p' : Proof.Zeroize.Prefix u'.mem (dp s₀) (j + 1) := by
      rw [m', hu.rax, h0]
      exact Proof.Zeroize.prefix_writeW hpz (by omega)
    have hsub : BitVec.ofNat 64 (L s₀ - j) - 1 = BitVec.ofNat 64 (L s₀ - (j + 1)) := by
      rw [ofNat64_sub_one (by omega) (by omega), Nat.sub_sub]
    rw [e2, hsub] at c' z'
    have d'' : u'.gpr .rdx = dp s₀ + BitVec.ofNat 64 (j + 1) := by
      rw [d', BitVec.add_assoc, BitVec.ofNat_add]; rfl
    by_cases he : j + 1 = L s₀
    · left
      refine ⟨by show u'.zf.map (!·) = some false; rw [z', he, Nat.sub_self]; rfl, k', ?_⟩
      rw [he] at p'
      exact Proof.Zeroize.prefix_spec p'
    · right
      have hne := ofNat64_ne_zero (n := L s₀ - (j + 1)) (by omega) (by omega)
      refine ⟨by show u'.zf.map (!·) = some true; rw [z', beq_false_of_ne hne]; rfl,
        L s₀ - (j + 1), by omega, j + 1, by omega, rfl, k', d'', c', p'⟩

/-! ## The tail -/

theorem stk_arg (s₀ : State) : (stkR s₀).Disjoint (argR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 24) (d := 32) (n := 16) (k := 24) (by decide)
    (by decide)
  rw [show s₀.gpr .rsp - BitVec.ofNat 64 24 + BitVec.ofNat 64 32 = stackArgAddr s₀ 0 by
    rw [stackArgAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]; congr 1] at this
  exact this.symm

/-- `tagLoad`: the received tag's address into `r12`, from its stack slot,
which the body never writes. -/
theorem tagLoad_ok {s₀ : State} (hp : APre false s₀) {t : Addr} {s : State} (h : TailIn s₀ t s) :
    WP isa (.block tagLoad) s (TailIn s₀ (tp s₀)) := by
  have ea : off (s₀.gpr .rsp) 8 = stackArgAddr s₀ 0 := by rw [off_eq, stackArgAddr]
  have hc : (argR s₀).Contains (stackArgAddr s₀ 0) (64 / 8) := by
    have := Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 8) (k := 16) (by decide) (by decide)
    rwa [BitVec.add_zero] at this
  have hin : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 8) 8 := by
    rw [h.inv.rsp, ea, h.inv.rd]
    exact ⟨argR s₀, by simp [hp.g_rd], hc⟩
  have hv : s.mem.readW (off (s.gpr .rsp) 8) 64 = tp s₀ := by
    rw [h.inv.rsp, ea, h.inv.frame.readW hc (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.c_g.sub_left (sub_ctx s₀ (by lit_omega))).symm
      · exact hp.d_g.symm
      · exact (stk_arg s₀).symm) (by decide)]
    rfl
  apply WP.of_runBlock
  simp only [tagLoad, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_at, hin,
    ite_true, Option.map_some, hv, Option.some.injEq, exists_eq_left']
  have g : ∀ r, r ≠ .r12 → (s.setReg .r12 (tp s₀)).gpr r = s.gpr r := fun r hr =>
    RegUpd.gpr_setReg_of_ne _ _ hr
  exact ⟨⟨by rw [g _ (by decide), h.inv.r15], by rw [g _ (by decide), h.inv.r14],
      by rw [g _ (by decide), h.inv.r13], RegUpd.gpr_setReg_self _ _ _, by rw [g _ (by decide), h.inv.rsp],
      h.inv.rd, h.inv.wr, h.inv.saved, h.inv.frame⟩,
    by rw [g _ (by decide), h.rcx], by rw [g _ (by decide), h.rdi], h.tag, h.pt, h.mx⟩

/-- The tags compared, and `ZF` whether they differ: `eax` is 1 if the tag
is right. -/
theorem cmpTail_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : TailIn s₀ (tp s₀) s) :
    WP isa (.block (compare ++ ([.alu32 .cmp .rax (.imm 0)] : List Instr))) s fun s' => Inv s₀ s' ∧
      (s'.gpr .rax).setWidth 32 = (if mac (otk s₀) (macData (A s₀) (C s₀)) = T0 s₀ then 1 else 0) ∧
      s'.zf = some ((s'.gpr .rax).setWidth 32 == 0) ∧ s'.gpr .rdi = off (cx s₀) 448 ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr := by
  have T0 : bytesAt s.mem (tp s₀) 16 = T0 s₀ := bytesAt_frame h.inv.frame (by rdisj_all) (by lit_omega)
  refine WP.block_append (WP.mono_mx (by decide) (compare_ok hp h.rcx h.inv.r12 h.inv.rd h.inv.wr)
    fun s₁ ⟨rax₁, g₁, m₁, rd₁, wr₁⟩ mx₁ => WP.mono (cmp32_ok s₁) fun s₂ ⟨z₂, g₂, m₂, rd₂, wr₂, mx₂⟩ => ?_)
  have g : ∀ q, q ≠ .rax → q ≠ .rdx → s₂.gpr q = s.gpr q := fun q a b => by rw [g₂, g₁ q a b]
  refine ⟨h.inv.step (fun r hr => g r (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
      (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (rs := []) (by rw [m₂, m₁]; exact Frame.refl _ _)
      (fun _ h => by simp at h) (fun _ h => by simp at h),
    by rw [g₂, rax₁, h.tag, T0], by rw [z₂, g₂], by rw [g _ (by decide) (by decide), h.rdi], by rw [m₂, m₁],
    by rw [mx₂, mx₁]⟩

theorem low8 {x : BitVec 64} (h : x.setWidth 32 = 0) : x.setWidth 8 = 0 := by
  rw [show x.setWidth 8 = (x.setWidth 32).setWidth 8 by rw [BitVec.setWidth_setWidth_of_le _ (by decide)], h]
  rfl

/-- What `open`'s body and tail give: `openX86_64.post` with the ciphertext
read from `sp` (`C`) and the plaintext written to `dp`. -/
def openSPost (s₀ s' : State) : Prop :=
  match Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (C s₀) (T0 s₀) with
  | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (dp s₀) (L s₀) = pt
  | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (dp s₀) (L s₀) = List.replicate (L s₀) 0

/-- What `open`'s body may leak: whether the message is authenticated. -/
def openSLeak (s₀ : State) : List Nat :=
  [if (Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (C s₀) (T0 s₀)).isSome then 1 else 0]

theorem tailT_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : TailIn s₀ (tp s₀) s) :
    WP isa (.seq (.block (compare ++ ([.alu32 .cmp .rax (.imm 0)] : List Instr)))
      (.seq (.ite .e zeroData (.block [])) (.block restore))) s fun s' =>
      abiPreserved s₀ s' ∧ openSPost s₀ s' := by
  have ret : ∀ {m : Mem}, Frame [dR s₀] s.mem m →
      m.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := fun hf => by
    have c : (retR s₀).Contains (s₀.gpr .rsp) (64 / 8) := Region.contains_self _ _
    rw [hf.readW c (by rdisj_all) (by lit_omega), h.inv.frame.readW c (by rdisj_all) (by lit_omega)]
  refine WP.seq (WP.mono (cmpTail_ok hp h) fun s₂ ⟨i₂, rax₂, z₂, rdi₂, m₂, mx₂⟩ => ?_)
  refine WP.seq ?_
  by_cases hc : mac (otk s₀) (macData (A s₀) (C s₀)) = T0 s₀
  · simp only [hc, ↓reduceIte] at rax₂
    refine WP.ite false (by show s₂.zf = some false; rw [z₂, rax₂]; rfl) (by simp) fun _ => WP.block_nil ?_
    refine WP.mono_mx (by decide) (restore_ok hp rdi₂ i₂.saved i₂.rsp i₂.rd i₂.wr)
      fun s₃ ⟨cs₃, rax₃, m₃⟩ mx₃ => ⟨⟨cs₃, by rw [m₃, m₂]; exact ret (Frame.refl _ _),
        by rw [mx₃, mx₂, h.mx]⟩, ?_⟩
    unfold openSPost
    split
    next pt hpt =>
      obtain ⟨-, rfl⟩ := decrypt_eq_some hpt
      exact ⟨by rw [rax₃, rax₂], by rw [m₃, m₂, h.pt]⟩
    next hn => exact absurd hc (decrypt_eq_none hn)
  · simp only [hc, ↓reduceIte] at rax₂
    refine WP.ite true (by show s₂.zf = some true; rw [z₂, rax₂]; rfl) (fun _ => ?_) (by simp)
    refine WP.mono (zeroData_ok hp i₂ (low8 rax₂)) fun s₃ ⟨k₃, z₃⟩ => ?_
    refine WP.mono_mx (by decide) (restore_ok hp (by rw [k₃.rdi, rdi₂]) k₃.inv.saved k₃.inv.rsp k₃.inv.rd
      k₃.inv.wr) fun s₄ ⟨cs₄, rax₄, m₄⟩ mx₄ => ⟨⟨cs₄, by rw [m₄]; exact ret (by rw [← m₂]; exact k₃.frame),
        by rw [mx₄, k₃.mx, mx₂, h.mx]⟩, ?_⟩
    unfold openSPost
    split
    next pt hpt => exact absurd (decrypt_eq_some hpt).1 hc
    next hn => exact ⟨by rw [rax₄, k₃.rax, rax₂], by rw [m₄, z₃]⟩

theorem tail_ok {s₀ : State} (hp : APre false s₀) {t : Addr} {s : State} (h : TailIn s₀ t s) :
    WP isa openTail s fun s' => abiPreserved s₀ s' ∧ openSPost s₀ s' :=
  WP.seq (WP.mono (tagLoad_ok hp h) fun _ h => tailT_ok hp h)

/-- `APre` of a state that may read more. -/
theorem APre.of_more {e : Bool} {u : State} {rd wr more : List Region} (h : preX86_64 e (u.withRegions rd wr)) :
    APre e (u.withRegions (rd ++ more) wr) := by
  have h' := APre.of _ h
  obtain ⟨m', hm'⟩ := h'.rd
  have hrd : rd = (if e then [kR u, nR u, aR u, argR u] else [kR u, nR u, aR u, tR u, argR u]) ++ m' := hm'
  exact { h' with rd := ⟨m' ++ more, by simp only [State.withRegions_rd, hrd, List.append_assoc]; rfl⟩ }

/-- What the code `open` and `open_to` share (`openShared`, and the stitched
`Stitch.openStitchedShared`) starts from: `open`'s precondition, with the
ciphertext at `r11` (`sp`), which is the data or apart from it. -/
def SPreO (s₀ : State) : Prop := APre false s₀ ∧ SrcIO s₀ (sp s₀)

theorem shared_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : SPreO s₀) :
    WP isa (openShared v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ openSPost s₀ s' :=
  WP.seq (WP.mono (body_ok v hp.1 hp.2) fun _ h => tail_ok hp.1 h)

/-- The state after `srcIn`: the ciphertext's address, the data's, in `r11`. -/
abbrev inS (s₀ : State) : State := s₀.setReg .r11 (s₀.gpr .r8)

theorem srcIn_ok (s₀ : State) : WP isa (.block srcIn) s₀ fun s => s = inS s₀ := by
  apply WP.of_runBlock
  simp only [srcIn, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left']

theorem inS_pre {s₀ : State} (hp : APre false s₀) : APre false (inS s₀) := hp.setR11 _

theorem open_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre false s₀) :
    WP isa («open» v.callee v.poly) s₀ fun s' => abiPreserved s₀ s' ∧ openX86_64.post s₀ s' := by
  refine WP.seq (WP.mono_mx (by decide) (srcIn_ok s₀) fun s₁ e₁ mx₁ => ?_)
  subst e₁
  refine WP.mono (shared_correct v ⟨inS_pre hp, srcIO_dp (inS_pre hp)⟩)
    fun s' ⟨ab, hpost⟩ => ⟨⟨fun r hr => ?_, ab.2.1, ab.2.2⟩, hpost⟩
  rw [ab.1 r hr]
  exact RegUpd.gpr_setReg_of_ne _ _ (by
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-! ## Constant time -/

/-- Whether the message is authenticated, in the state on entry to `open`'s
body. -/
def okS (s₀ : State) : Bool :=
  (Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (C s₀) (T0 s₀)).isSome

theorem ok_iff (s₀ : State) :
    okS s₀ = true ↔ mac (otk s₀) (macData (A s₀) (C s₀)) = T0 s₀ := by
  unfold okS
  constructor
  · intro h
    obtain ⟨pt, hpt⟩ := Option.isSome_iff_exists.mp h
    exact (decrypt_eq_some hpt).1
  · intro h
    cases hd : Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (C s₀) (T0 s₀) with
    | none => exact absurd h (decrypt_eq_none hd)
    | some _ => rfl

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The result in two runs whose leaks agree. -/
theorem bit_eq {s₁ s₂ : State} (h : openSLeak s₁ = openSLeak s₂) :
    (if mac (otk s₁) (macData (A s₁) (C s₁)) = T0 s₁ then (1 : BitVec 32) else 0) =
      if mac (otk s₂) (macData (A s₂) (C s₂)) = T0 s₂ then 1 else 0 := by
  have e : okS s₁ = okS s₂ := leak_bool h
  by_cases h₁ : okS s₁ = true
  · have h₂ : okS s₂ = true := e ▸ h₁
    simp only [(ok_iff s₁).mp h₁, (ok_iff s₂).mp h₂, ↓reduceIte]
  · have h₂ : ¬okS s₂ = true := e ▸ h₁
    simp only [show ¬mac (otk s₁) (macData (A s₁) (C s₁)) = T0 s₁ from fun h' => h₁ ((ok_iff s₁).mpr h'),
      show ¬mac (otk s₂) (macData (A s₂) (C s₂)) = T0 s₂ from fun h' => h₂ ((ok_iff s₂).mpr h'), ↓reduceIte]

/-- An empty block, in two runs: the same (empty) trace, and the states
unchanged. -/
theorem skip_rel {P Q : State → State → Prop} (h : ∀ x y, P x y → Q x y) : RelCT isa P (.block []) Q := by
  intro _ _ _ _ _ _ hp x₁ x₂
  cases x₁ with
  | block h₁ =>
    cases x₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      rw [← h₁.1, ← h₂.1]
      exact ⟨h₁.2.symm.trans h₂.2, h _ _ hp⟩

/-- Code the taint analysis proves constant time from the registers `rs`. -/
theorem taintRel {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun x y hp => Taint.agree_ofRegs (hr x y hp)) h

/-- What `cmpTail_ok` gives. -/
structure CmpT (s₀ s : State) : Prop where
  inv : Inv s₀ s
  rax : (s.gpr .rax).setWidth 32 = (if mac (otk s₀) (macData (A s₀) (C s₀)) = T0 s₀ then 1 else 0)
  zf : s.zf = some ((s.gpr .rax).setWidth 32 == 0)
  rdi : s.gpr .rdi = off (cx s₀) 448

theorem zero_of_e {s₀ x : State} (h : CmpT s₀ x) (he : isa.eval .e x = some true) :
    (x.gpr .rax).setWidth 32 = 0 := by
  have : x.zf = some true := he
  rw [h.zf] at this
  exact beq_iff_eq.mp (Option.some.inj this)

section
variable {s₀ s₀' : State} (hp : APre false s₀) (hp' : APre false s₀') (hq : pubX86_64 s₀ s₀')
  (hl : openSLeak s₀ = openSLeak s₀')
include hp hp' hq hl

/-- `openTail`, in two runs from the states `body_ok` describes. -/
theorem tail_rel {t t' : Addr} :
    RelCT isa (fun x y => TailIn s₀ t x ∧ TailIn s₀' t' y) openTail fun _ _ => True := by
  obtain ⟨-, -, -, -, p5, p6, p7, p8, p9⟩ := id hq
  have ecx : cx s₀ = cx s₀' := by simp only [cx, p9]
  have edp : dp s₀ = dp s₀' := by simp only [dp, p5]
  have etp : tp s₀ = tp s₀' := by simp only [tp, p8]
  have he : ∀ {x y : State}, CmpT s₀ x → CmpT s₀' y → isa.eval .e x = some true → isa.eval .e y = some true :=
    fun {x y} hx hy h => by
      show y.zf = some true
      rw [hy.zf, hy.rax, ← bit_eq hl, ← hx.rax, ← hx.zf]; exact h
  unfold openTail
  refine RelCT.seq (R := fun x y => TailIn s₀ (tp s₀) x ∧ TailIn s₀' (tp s₀') y)
    (RelCT.mono ((taintRel [.rsp] (fun x y h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; rw [h.1.inv.rsp, h.2.inv.rsp, p7]) (by taint_decide)).wp fun x y h =>
      ⟨tagLoad_ok hp h.1, tagLoad_ok hp' h.2⟩) (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine RelCT.seq (R := fun x y => CmpT s₀ x ∧ CmpT s₀' y)
    (RelCT.mono ((taintRel [.rcx, .r12] (fun x y h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.rcx, h.2.rcx, ecx]
        · rw [h.1.inv.r12, h.2.inv.r12, etp]) (by taint_decide)).wp fun x y h =>
      ⟨WP.mono (cmpTail_ok hp h.1) fun _ h' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩,
       WP.mono (cmpTail_ok hp' h.2) fun _ h' => ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1⟩⟩)
      (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine RelCT.seq (R := fun (x y : State) => (Inv s₀ x ∧ x.gpr .rdi = off (cx s₀) 448) ∧
      (Inv s₀' y ∧ y.gpr .rdi = off (cx s₀') 448))
    (RelCT.ite (fun x y h => by
        show x.zf = y.zf; rw [h.1.zf, h.2.zf, h.1.rax, h.2.rax, bit_eq hl])
      (RelCT.mono ((taintRel [.r13, .r14] (fun x y h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.1.inv.r13, h.1.2.inv.r13, p6]
          · rw [h.1.1.inv.r14, h.1.2.inv.r14, edp]) (by taint_decide)).wp fun x y h =>
        ⟨WP.mono (zeroData_ok hp h.1.1.inv (low8 (zero_of_e h.1.1 h.2))) fun _ h' =>
            ⟨h'.1.inv, by rw [h'.1.rdi, h.1.1.rdi]⟩,
         WP.mono (zeroData_ok hp' h.1.2.inv (low8 (zero_of_e h.1.2 (he h.1.1 h.1.2 h.2)))) fun _ h' =>
            ⟨h'.1.inv, by rw [h'.1.rdi, h.1.2.rdi]⟩⟩) (fun _ _ h => h) fun _ _ h => h.2)
      (skip_rel fun _ _ h => ⟨⟨h.1.1.inv, h.1.1.rdi⟩, ⟨h.1.2.inv, h.1.2.rdi⟩⟩)) ?_
  exact taintRel [.rdi, .rsp] (fun x y h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.1.2, h.2.2, ecx]
    · rw [h.1.1.rsp, h.2.1.rsp, p7]) (by taint_decide)

end

/-- The public data of the shared code's entry: `open`'s, the ciphertext's
address, and whether the tag is right (what `open` may leak). -/
def sharedPub (s₁ s₂ : State) : Prop := pubX86_64 s₁ s₂ ∧ sp s₁ = sp s₂ ∧ openSLeak s₁ = openSLeak s₂

/-- The contract of the shared code, as `open_to` runs it inline. -/
def sharedK : Contract isa where
  pre := SPreO
  post := openSPost
  pub := sharedPub

theorem shared_rel (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State} (hp : SPreO s₀) (hp' : SPreO s₀')
    (hq : sharedPub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (openShared v.callee v.poly) fun _ _ => True :=
  RelCT.seq (R := fun x y => TailIn s₀ (sp s₀) x ∧ TailIn s₀' (sp s₀') y)
    (RelCT.mono ((body_rel v hp.1 hp'.1 hq.1 hq.2.1 hp.2 hp'.2).wp fun x y ⟨ex, ey⟩ => by
      subst ex; subst ey; exact ⟨body_ok v hp.1 hp.2, body_ok v hp'.1 hp'.2⟩) (fun _ _ h => h) fun _ _ h => h.2)
    (tail_rel hp.1 hp'.1 hq.1 hq.2.2)

theorem shared_ok (v : Proof.ChaCha20.X86_64.XorImpl) (s : State) (hs : sharedK.pre s) :
    ∃ t s', Exec isa (openShared v.callee v.poly) s t s' ∧ abiPreserved s s' ∧ sharedK.post s s' :=
  let ⟨t, s', e, a, p⟩ := shared_correct v hs; ⟨t, s', e, a, p⟩

theorem shared_ct (v : Proof.ChaCha20.X86_64.XorImpl) :
    ConstantTime isa sharedK.pre sharedK.pub (openShared v.callee v.poly) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (shared_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem open_rel (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ s₀' : State} (h₀ : preX86_64 false s₀)
    (h₀' : preX86_64 false s₀') (hq : pubX86_64 s₀ s₀') (hl : openLeakX86_64 s₀ = openLeakX86_64 s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («open» v.callee v.poly) fun _ _ => True := by
  have hp := inS_pre (APre.of _ h₀)
  have hp' := inS_pre (APre.of _ h₀')
  have hq' : pubX86_64 (inS s₀) (inS s₀') := hq
  have hs : sp (inS s₀) = sp (inS s₀') := hq.2.2.2.2.1
  refine RelCT.seq (R := fun x y => x = inS s₀ ∧ y = inS s₀')
    (RelCT.mono ((taintRel [] (fun _ _ _ r hr => by simp at hr) (by taint_decide)).wp fun x y h =>
      ⟨by rw [h.1]; exact srcIn_ok s₀, by rw [h.2]; exact srcIn_ok s₀'⟩) (fun _ _ h => h) fun _ _ h => h.2) ?_
  exact shared_rel v ⟨hp, srcIO_dp hp⟩ ⟨hp', srcIO_dp hp'⟩ ⟨hq', hs, hl⟩

end VG.Proof.ChaCha20Poly1305.X86_64
