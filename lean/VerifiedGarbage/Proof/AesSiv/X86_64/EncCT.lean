import VerifiedGarbage.Proof.AesSiv.X86_64.Enc
import VerifiedGarbage.Proof.AesSiv.X86_64.CryptCT

/-!
# AES-SIV on x86-64: `encrypt` and `decrypt` are constant time

Two runs with the same public arguments and the same descriptors (`EPub`)
leak the same trace. The taint analysis proves the straight-line pieces from
the registers that are public, with what correctness says about the values
they load: the working space's address from the stack (`argLoad_wp`), and in
each iteration the next descriptor's address from its slot and the
component's address and length from the descriptor (`adLoad_wp`,
`adDesc_wp`), the same in both runs since the descriptors are. The calls are
related by their callees' contracts (`fin_rel`, `cmacOf_rel`), and the end by
`sealTail_rel` and `openTail_rel`.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesSiv.X86_64
open VG.Impl.CmacAes.X86_64 (at_)
open VG.Proof.CmacAes.X86_64 (offset_nat)
open VG.Proof.CmacAes.Stream.X86_64 (FArgs fin_rel)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

variable {s₀ s₀' : State} {C A P W D : Addr} {R N L : Nat}

/-- What two runs agree on besides the arguments `EPre` names: the stack
pointer and the descriptors. -/
structure EPub (s₀ s₀' : State) (A : Addr) (N : Nat) : Prop where
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp
  desc : ∀ j < N * 16, s₀.mem (A + BitVec.ofNat 64 j) = s₀'.mem (A + BitVec.ofNat 64 j)

/-- The same descriptors list the same components. -/
theorem EPub.comp_eq (hq : EPub s₀ s₀' A N) {i : Nat} (hi : i < N) : comp s₀.mem A i = comp s₀'.mem A i := by
  have r {d : Nat} (hd : d + 8 ≤ N * 16) : s₀.mem.readW (A + BitVec.ofNat 64 d) 64 =
      s₀'.mem.readW (A + BitVec.ofNat 64 d) 64 := by
    have e := Mem.read_congr (m := s₀.mem) (m' := s₀'.mem) (a := A + BitVec.ofNat 64 d) (n := 64 / 8)
      fun j hj => by rw [Offset.add_add]; exact hq.desc (d + j) (by omega)
    simp only [Mem.readW, e]
  unfold comp
  rw [r (d := 16 * i) (by omega), r (d := 16 * i + 8) (by omega)]

/-- The working space's address, from the stack. -/
theorem argLoad_wp (h : EPre s₀ C A P W D R N L) :
    WP isa (.block [.mov .rax (.mem (at_ .rsp 8))]) s₀ fun s =>
      s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r :=
  WP.of_runBlock ⟨s₀.setReg .rax W, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, at_, exec, readSrc, State.load64, State.ea, offset_nat,
      Option.map_some, h.argIn, ite_true, h.arg], gpr_setReg_self _ _ _, fun r hr => gpr_setReg_of_ne _ _ hr⟩

/-- The arguments in both runs. -/
theorem args_agree (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L) (q1 : s₀.gpr .rsp = s₀'.gpr .rsp)
    {a b : State} (ha : a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r)
    (hb : b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r) :
    taint.Agree (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.1, hb.1]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rdi, h'.rdi]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rsi, h'.rsi]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rdx, h'.rdx]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.rcx, h'.rcx]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.r8, h'.r8]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), h.r9, h'.r9]
  · rw [ha.2 _ (by decide), hb.2 _ (by decide), q1]

/-- The state before the components, in both runs. -/
abbrev AA (s₀ s₀' : State) (C A P W D : Addr) (R N L i : Nat) (a b : State) : Prop :=
  AInv s₀ C A P W D R N L i a ∧ AInv s₀' C A P W D R N L i b

/-- The registers the taint analysis needs public in the loop. -/
theorem ainv_agree (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) {i : Nat} {a b : State} (hab : AA s₀ s₀' C A P W D R N L i a b) :
    taint.Agree (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp]) a b := by
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hab.1.rbx, hab.2.rbx]
  · rw [hab.1.rbp, hab.2.rbp]
  · rw [hab.1.r12, hab.2.r12]
  · rw [hab.1.r15, hab.2.r15]
  · rw [hab.1.rsp, hab.2.rsp, q1]

/-- The save and S2V's first state. -/
theorem start_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    (q1 : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block (encPre ++ startPre)) (callFinalize v.callee v.suffix))
      (AA s₀ s₀' C A P W D R N L 0) := by
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block [.mov .rax (.mem (at_ .rsp 8))]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (encPre.drop 1 ++ startPre)) hc).isSome = true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h.rdi, h'.rdi]
    · rw [h.rsi, h'.rsi]
    · rw [h.rdx, h'.rdx]
    · rw [h.rcx, h'.rcx]
    · rw [h.r8, h'.r8]
    · rw [h.r9, h'.r9]
    · exact q1) hA).wp
    (F₁ := fun (s : State) => s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r)
    (F₂ := fun (s : State) => s.gpr .rax = W ∧ ∀ r, r ≠ .rax → s.gpr r = s₀'.gpr r) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨argLoad_wp h, argLoad_wp h'⟩
  have b := RelCT.taint (A := taint) (P := fun (a b : State) => (a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r) ∧
      b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r) _ (fun a b hab => args_agree h h' q1 hab.1 hab.2) hB
  have blk := (RelCT.block_append (M := isa) (l₁ := ([.mov .rax (.mem (at_ .rsp 8))] : List Instr)) (l₂ := encPre.drop 1 ++ startPre)
      ((a.mono (fun _ _ p => p) fun _ _ p => p.2).seq b)).wp
    (F₁ := fun (s : State) => FArgs s C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧
      s.gpr .rsp = s₀.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) s (AInv s₀ C A P W D R N L 0))
    (F₂ := fun (s : State) => FArgs s C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧
      s.gpr .rsp = s₀'.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) s (AInv s₀' C A P W D R N L 0))
    fun a b hab => by obtain ⟨rfl, rfl⟩ := hab; exact ⟨start_wp v h, start_wp v h'⟩
  have f := (fin_rel v ("vg_cmac_aes_finalize" ++ v.suffix)
    (P := fun a b => (FArgs a C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧
      a.gpr .rsp = s₀.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) a (AInv s₀ C A P W D R N L 0)) ∧
      FArgs b C D (W + BitVec.ofNat 64 16) (W + BitVec.ofNat 64 256) 16 R ∧
      b.gpr .rsp = s₀'.gpr .rsp ∧ WP isa (callFinalize v.callee v.suffix) b (AInv s₀' C A P W D R N L 0))
    fun a b hab => ⟨_, _, _, _, _, _, hab.1.1, hab.2.1, by rw [hab.1.2.1, hab.2.2.1, q1]⟩).wp
    (F₁ := AInv s₀ C A P W D R N L 0) (F₂ := AInv s₀' C A P W D R N L 0)
    fun a b hab => ⟨by exact hab.1.2.2, by exact hab.2.2.2⟩
  exact (blk.mono (fun _ _ p => p) fun _ _ p => p.2).seq (f.mono (fun _ _ p => p) fun _ _ p => p.2)

/-- One component in both runs. -/
theorem adBody_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) {i : Nat} (hiN : i < N) :
    RelCT isa (AA s₀ s₀' C A P W D R N L i)
      (.seq (.block adNext) (.seq (cmacOf v.callee v.suffix stOff) (.block adStep)))
      fun a b => (AInv s₀ C A P W D R N L (i + 1) a ∧ a.zf = some (decide (i + 1 = N))) ∧
        AInv s₀' C A P W D R N L (i + 1) b ∧ b.zf = some (decide (i + 1 = N)) := by
  have hQ := h.comps _ (comp_mem s₀.mem A hiN)
  have hQ' := h'.comps _ (comp_mem s₀'.mem A hiN)
  have ec := hq.comp_eq hiN
  rw [← ec] at hQ'
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .rax (.mem (at_ .r15 adsOff))]) hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .r13 (.mem (at_ .rax 0)), .mov .r14 (.mem (at_ .rax 8))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block adStep) hc).isSome = true := ⟨_, by taint_decide⟩
  have p₁ := (RelCT.taint (A := taint) (P := AA s₀ s₀' C A P W D R N L i) _
    (fun a b hab => ainv_agree hq.rsp hab) hA).wp
    (F₁ := fun (s : State) => AInv s₀ C A P W D R N L i s ∧ s.gpr .rax = A + BitVec.ofNat 64 (16 * i))
    (F₂ := fun (s : State) => AInv s₀' C A P W D R N L i s ∧ s.gpr .rax = A + BitVec.ofNat 64 (16 * i))
    fun a b hab => ⟨WP.mono (adLoad_wp h hab.1) fun _ p => ⟨p.1, p.2.1⟩,
      WP.mono (adLoad_wp h' hab.2) fun _ p => ⟨p.1, p.2.1⟩⟩
  have p₂ := (RelCT.taint (A := taint)
    (P := fun (a b : State) => (AInv s₀ C A P W D R N L i a ∧ a.gpr .rax = A + BitVec.ofNat 64 (16 * i)) ∧
      AInv s₀' C A P W D R N L i b ∧ b.gpr .rax = A + BitVec.ofNat 64 (16 * i)) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hab.1.2, hab.2.2]
      · rw [hab.1.1.rbx, hab.2.1.rbx]
      · rw [hab.1.1.rbp, hab.2.1.rbp]
      · rw [hab.1.1.r12, hab.2.1.r12]
      · rw [hab.1.1.r15, hab.2.1.r15]
      · rw [hab.1.1.rsp, hab.2.1.rsp, hq.rsp]) hB).wp
    (F₁ := Regs s₀ C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len)
    (F₂ := Regs s₀' C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len)
    fun a b hab => ⟨WP.mono (adDesc_wp h hiN hab.1.1 hab.1.2) fun _ p => p.1,
      WP.mono (adDesc_wp h' hiN hab.2.1 hab.2.2) fun _ p => by rw [ec]; exact p.1⟩
  have p₄ := RelCT.taint (A := taint)
    (P := RR s₀ s₀' C D (comp s₀.mem A i).base W R (comp s₀.mem A i).len) _
    (fun a b hab => regs_agree hq.rsp hab.1 hab.2) hC
  have body := (RelCT.block_append (M := isa) ((p₁.mono (fun _ _ p => p) fun _ _ p => p.2).seq
    (p₂.mono (fun _ _ p => p) fun _ _ p => p.2))).seq ((cmacOf_rel v hQ hQ' hq.rsp).seq p₄)
  refine (body.wp (F₁ := fun (s : State) => AInv s₀ C A P W D R N L (i + 1) s ∧ s.zf = some (decide (i + 1 = N)))
    (F₂ := fun (s : State) => AInv s₀' C A P W D R N L (i + 1) s ∧ s.zf = some (decide (i + 1 = N)))
    fun a b hab => ⟨by exact adBody_wp v h hiN hab.1, by exact adBody_wp v h' hiN hab.2⟩).mono
    (fun _ _ p => p) fun _ _ p => p.2

/-- S2V over the components in both runs. -/
theorem ads_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (AA s₀ s₀' C A P W D R N L 0) (s2vAds v.callee v.suffix) (AA s₀ s₀' C A P W D R N L N) := by
  obtain ⟨_, hH⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r15, .rsp])
      (.block [.mov .rax (.mem (at_ .r15 leftOff)), .alu .test .rax (.reg .rax)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have hd := (RelCT.taint (A := taint) (P := AA s₀ s₀' C A P W D R N L 0) _
    (fun a b hab => ainv_agree hq.rsp hab) hH).wp
    (F₁ := fun (s : State) => AInv s₀ C A P W D R N L 0 s ∧ s.zf = some (decide (N = 0)))
    (F₂ := fun (s : State) => AInv s₀' C A P W D R N L 0 s ∧ s.zf = some (decide (N = 0)))
    fun a b hab => ⟨adsHead_wp h hab.1, adsHead_wp h' hab.2⟩
  refine (hd.mono (fun _ _ p => p) fun _ _ p => p.2).seq (RelCT.ite (fun a b hab => by
    show a.zf = b.zf; rw [hab.1.2, hab.2.2]) ?_ ?_)
  · refine RelCT.block_nil fun a b hab => ?_
    have e := hab.2
    rw [show isa.eval .e a = a.zf from rfl, hab.1.1.2] at e
    have hN0 : N = 0 := by simpa using e
    rw [hN0] at hab ⊢
    exact ⟨hab.1.1.1, hab.1.2.1⟩
  by_cases hN0 : N = 0
  · exact RelCT.of_false fun a b hab => by
      have e := hab.2; rw [show isa.eval .e a = a.zf from rfl, hab.1.1.2] at e; simp [hN0] at e
  refine (RelCT.loop (M := isa) (c := .ne)
    (fun (n : Nat) (a b : State) => ∃ i, n = N - i ∧ i < N ∧ AA s₀ s₀' C A P W D R N L i a b) (fun n => ?_)
    (N - 0)).mono (fun a b hab => ⟨0, rfl, Nat.pos_of_ne_zero hN0, hab.1.1.1, hab.1.2.1⟩) fun _ _ p => p
  refine RelCT.exists_ fun i => ?_
  by_cases hc : n = N - i ∧ i < N
  swap
  · exact RelCT.of_false fun _ _ p => hc ⟨p.1, p.2.1⟩
  obtain ⟨rfl, hiN⟩ := hc
  refine (adBody_rel v h h' hq hiN).mono (fun _ _ p => p.2.2) fun a b p => ?_
  obtain ⟨⟨ha, za⟩, hb, zb⟩ := p
  refine ⟨by simp [eval, za, zb], fun e => ?_, fun e => ?_⟩
  · have he : i + 1 = N := by simpa [eval, za] using e
    subst he; exact ⟨ha, hb⟩
  · have he : i + 1 ≠ N := by simpa [eval, za] using e
    exact ⟨N - (i + 1), by omega, i + 1, rfl, by omega, ha, hb⟩

/-- S2V of the associated data in both runs. -/
theorem encS2v_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encS2v v.callee v.suffix)
      fun a b => SDone s₀ C A P W D R N L a ∧ SDone s₀' C A P W D R N L b := by
  obtain ⟨_, hE⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [.mov .r13 (.mem (at_ .r15 dataOff)), .mov .r14 (.mem (at_ .r15 lenOff))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have e := (RelCT.taint (A := taint) (P := AA s₀ s₀' C A P W D R N L N) _
    (fun a b hab => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hab.1.r15, hab.2.r15]) hE).wp
    (F₁ := SDone s₀ C A P W D R N L) (F₂ := SDone s₀' C A P W D R N L)
    fun a b hab => ⟨adsEnd_wp h hab.1, adsEnd_wp h' hab.2⟩
  exact RelCT.assoc ((start_rel v h h' hq.rsp).seq ((ads_rel v h h' hq).seq
    (e.mono (fun _ _ p => p) fun _ _ p => p.2)))

theorem encrypt_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encrypt v.callee v.suffix) fun _ _ => True :=
  (encS2v_rel v h h' hq).seq ((sealTail_rel v h.env h'.env hq.rsp h.cp h.pw h'.pw).mono
    (fun _ _ p => ⟨p.1.spre, p.2.spre⟩) fun _ _ p => p)

theorem decrypt_rel (v : Ctr32Impl) (h : EPre s₀ C A P W D R N L) (h' : EPre s₀' C A P W D R N L)
    (hq : EPub s₀ s₀' A N) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decrypt v.callee v.suffix) fun _ _ => True :=
  (encS2v_rel v h h' hq).seq ((openTail_rel v h.env h'.env hq.rsp h.cp h.pw h'.pw).mono
    (fun _ _ p => ⟨p.1.spre, p.2.spre⟩) fun _ _ p => p)

end VG.Proof.AesSiv.X86_64
