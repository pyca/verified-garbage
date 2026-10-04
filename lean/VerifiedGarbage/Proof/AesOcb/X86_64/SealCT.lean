import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
import VerifiedGarbage.Proof.AesOcb.X86_64.NonceCT
import VerifiedGarbage.Proof.AesOcb.X86_64.HashCT
import VerifiedGarbage.Proof.AesOcb.X86_64.BodyCT

/-!
# AES-OCB on x86-64: `vg_aes_ocb_seal` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments are related piece by piece: the entry by the taint analysis from
the public registers, once the first instruction has loaded `W` (`entry_rel`),
then `Offset_0`, `HASH`, the data, the tag and `restore` (`nonce_rel`,
`hash_rel`, `bodySeal_rel`, `tag_rel`), each run satisfying what correctness
says between them (`RelCT.wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame in_off add_ofNat_assoc)

/-- A run after `Offset_0`: what `HASH` needs. -/
structure NRun (K W SP N A D : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
  C : HCtx K W SP D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al) s
  one : One K W SP R N A D nl n tl s
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (bytesAt s₀.mem A al).length
  l0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s₀.mem K) 0

/-- `Offset_0`, after `entry`. -/
theorem nonce_nrun (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat}
    (Ar : Args s K W SP N A D R nl al n tl) {s₁ : State} (P₁ : EntryPost K W SP R N A D nl al n tl s s₁) :
    WP isa (nonce (callees v)) s₁ (NRun K W SP N A D R nl al n tl s) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have eK : ctxCiph s₁.mem K R = ctxCiph s.mem K R := by
    unfold ctxCiph
    rw [bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))) (by omega)]
  have eL : ctxLstar s₁.mem K = ctxLstar s.mem K := blockAtMem_frame P₁.frame (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (L.k_w.sub_left (Lay.kSub (by decide))).sub_right (Lay.wSub (by decide)))
  have eB : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → bytesAt s₁.mem P k = bytesAt s.mem P k := fun hP =>
    bytesAt_frame P₁.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
      (by have := hP.lt; omega)
  refine WP.mono (nonce_ok v L P₁.env Ar.rounds P₁.slots.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k Ar.data.w) fun s₂ P₂ => ?_
  have F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := nonceR_mut P₂.frame
  have S₂ := Slots.of_mut L Ar.data.w F₂ P₁.slots
  have c₂ : ctxCiph s₂.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₂ Ar.rounds).trans eK
  have l₂ : ctxLstar s₂.mem K = ctxLstar s.mem K := (lstar_mut L Ar.data.k F₂).trans eL
  have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := (buf_mut Ar.aad Ar.ad F₂).trans (eB Ar.aad)
  exact
    { C := { lay := L, rounds := Ar.rounds, ciph := c₂, lstar := l₂
             buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
             aad := by rw [length_bytesAt, a₂]
             ad := by rw [length_bytesAt]; exact Ar.ad
             kd := Ar.data.k, dw := Ar.data.w, rnd := S₂.rounds
             short := by rw [length_bytesAt]; exact Ar.aad.lt }
      one := ⟨P₂.env, S₂, P₂.wr.trans (P₁.wr.trans Ar.wr)⟩
      alen := by rw [P₂.alen, P₁.alen, length_bytesAt]
      l0 := by rw [P₂.keep (by decide) (by decide), P₁.l0] }

/-- Two runs of the same public arguments: `seal`'s and `open`'s inputs. -/
structure Two (s₀ s₀' : State) (K W SP N A D : Addr) (R nl al n tl : Nat) : Prop where
  ar : Args s₀ K W SP N A D R nl al n tl
  ar' : Args s₀' K W SP N A D R nl al n tl
  sp : s₀.gpr .rsp = SP
  sp' : s₀'.gpr .rsp = SP
  dd : s₀.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  dd' : s₀'.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  nn : s₀.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n
  nn' : s₀'.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n
  ww : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = W
  ww' : s₀'.mem.readW (SP + BitVec.ofNat 64 24) 64 = W
  tt : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl
  tt' : s₀'.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl
  di : s₀.gpr .rdi = K
  di' : s₀'.gpr .rdi = K
  si : s₀.gpr .rsi = BitVec.ofNat 64 R
  si' : s₀'.gpr .rsi = BitVec.ofNat 64 R
  dx : s₀.gpr .rdx = N
  dx' : s₀'.gpr .rdx = N
  cx : s₀.gpr .rcx = BitVec.ofNat 64 nl
  cx' : s₀'.gpr .rcx = BitVec.ofNat 64 nl
  r8 : s₀.gpr .r8 = A
  r8' : s₀'.gpr .r8 = A
  r9 : s₀.gpr .r9 = BitVec.ofNat 64 al
  r9' : s₀'.gpr .r9 = BitVec.ofNat 64 al

section
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} (T : Two s₀ s₀' K W SP N A D R nl al n tl)
include T

/-- What `entry` leaves, in each run. -/
theorem Two.entry₁ : WP isa (.block entry) s₀ (EntryPost K W SP R N A D nl al n tl s₀) := by
  obtain ⟨s₁, run₁, P₁⟩ := entry_ok T.ar.lay T.ar.perm T.sp T.ar.args T.ar.argsW T.dd T.nn T.ww T.tt T.di T.si T.dx
    T.cx T.r8 T.r9
  exact WP.of_runBlock ⟨s₁, run₁, P₁⟩

theorem Two.entry₂ : WP isa (.block entry) s₀' (EntryPost K W SP R N A D nl al n tl s₀') := by
  obtain ⟨s₁, run₁, P₁⟩ := entry_ok T.ar'.lay T.ar'.perm T.sp' T.ar'.args T.ar'.argsW T.dd' T.nn' T.ww' T.tt' T.di'
    T.si' T.dx' T.cx' T.r8' T.r9'
  exact WP.of_runBlock ⟨s₁, run₁, P₁⟩

/-- `entry` in two runs: the first instruction loads `W` from the stack, the
rest passes the taint analysis from the public registers. -/
theorem entry_rel : RelCT isa (fun a b => a = s₀ ∧ b = s₀') (.block entry) fun _ _ => True := by
  have a₂₄ := in_off (d := 16) (n := 8) T.ar.args (by decide) (by decide)
  have a₂₄' := in_off (d := 16) (n := 8) T.ar'.args (by decide) (by decide)
  rw [add_ofNat_assoc] at a₂₄ a₂₄'
  have first : ∀ {s : State}, s.gpr .rsp = SP → s.mem.readW (SP + BitVec.ofNat 64 24) 64 = W →
      InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 (8 + 16)) 8 →
      WP isa (.block [.mov .rax (.mem (at_ .rsp 24))]) s fun t =>
        t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s.gpr r := fun hsp hW ha =>
    WP.of_runBlock ⟨_, by orun [hsp, hW, ha], by simp only [gpr_setReg, ite_true],
      fun r h => by simp only [gpr_setReg, h, ite_false]⟩
  have e : entry = [.mov .rax (.mem (at_ .rsp 24))] ++ (save .rax ++
      [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
       st .r15 aadO .r8, st .r15 alenO .r9,
       ld .rax .rsp 8, st .r15 dataO .rax, ld .rax .rsp 16, st .r15 lenO .rax, ld .rax .rsp 32,
       st .r15 tlO .rax] ++ lsetup ++ zero16 ckO) := by
    simp only [entry, List.append_assoc]
  rw [e]
  refine RelCT.block_append ?_
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 24))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [T.sp, T.sp']) hA).wp
    (F₁ := fun (t : State) => t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s₀.gpr r)
    (F₂ := fun (t : State) => t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s₀'.gpr r) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨first T.sp T.ww a₂₄, first T.sp' T.ww' a₂₄'⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save .rax ++ [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
       st .r15 aadO .r8, st .r15 alenO .r9,
       ld .rax .rsp 8, st .r15 dataO .rax, ld .rax .rsp 16, st .r15 lenO .rax, ld .rax .rsp 32,
       st .r15 tlO .rax] ++ lsetup ++ zero16 ckO)) hc).isSome = true := ⟨_, by taint_decide⟩
  have b := RelCT.taint (A := taint) (P := fun (a b : State) => True ∧
      (a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r) ∧ (b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r))
    _ (fun a b ⟨_, ha, hb⟩ => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ha.1, hb.1]
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), T.di, T.di']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), T.si, T.si']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), T.dx, T.dx']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), T.cx, T.cx']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), T.r8, T.r8']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), T.r9, T.r9']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), T.sp, T.sp']) hB
  exact RelCT.seq a b


/-- `entry`, `Offset_0` and `HASH` in two runs. -/
theorem pre_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (.seq (.block entry) (.seq (nonce (callees v)) (hash (callees v))))
      fun _ _ => True := by
  have L := T.ar.lay
  have hDW := T.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt T.ar.data.lt
  have e := (entry_rel T).wp (F₁ := EntryPost K W SP R N A D nl al n tl s₀)
    (F₂ := EntryPost K W SP R N A D nl al n tl s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨T.entry₁, T.entry₂⟩
  have nn := (nonce_rel v L T.ar.rounds hDW hn T.ar.n1 T.ar.n15 (by have := T.ar.t16; omega)
    (P := fun a b => True ∧ EntryPost K W SP R N A D nl al n tl s₀ a ∧ EntryPost K W SP R N A D nl al n tl s₀' b)
    fun a b h => ⟨⟨h.2.1.env, h.2.1.slots, h.2.1.wr.trans T.ar.wr⟩, ⟨h.2.2.env, h.2.2.slots, h.2.2.wr.trans T.ar'.wr⟩,
      T.ar.nonce.of_eq h.2.1.rd h.2.1.wr, T.ar'.nonce.of_eq h.2.2.rd h.2.2.wr⟩).wp
    (F₁ := NRun K W SP N A D R nl al n tl s₀) (F₂ := NRun K W SP N A D R nl al n tl s₀')
    fun a b h => ⟨nonce_nrun v T.ar h.2.1, nonce_nrun v T.ar' h.2.2⟩
  have hh := rel_of_pt (P := fun a b => True ∧ NRun K W SP N A D R nl al n tl s₀ a ∧
      NRun K W SP N A D R nl al n tl s₀' b) (Q := fun _ _ => True) (c := hash (callees v)) fun a b h =>
    hash_rel v h.2.1.C h.2.2.C h.2.1.one h.2.2.one (by simp only [length_bytesAt]) hn h.2.1.alen h.2.2.alen
      h.2.1.l0 h.2.2.l0
  exact RelCT.seq e (RelCT.seq nn hh)

omit T in
/-- What `pre_wp'` leaves is what `body` needs. -/
theorem brun_of {s : State} {s' : State} (Ar : Args s K W SP N A D R nl al n tl)
    (P : Pre K W SP N A D R nl al n tl s s') : BRun K W SP R N A D nl n tl s' :=
  ⟨⟨P.env, P.slots, P.wr.trans Ar.wr⟩, Ar.data.of_eq P.rd P.wr, ⟨_, P.l0⟩, P.ofs.trans P.o0.symm⟩

/-- The tag keeps the public arguments. -/
theorem tag_one (v : BlocksImpl) {d : Nat} (hd : d = tagO ∨ d = t2O) {s : State}
    (o : One K W SP R N A D nl n tl s) : WP isa (tag (callees v) d) s (One K W SP R N A D nl n tl) :=
  WP.mono (tag_ok v T.ar.lay o.env T.ar.rounds o.sl.rounds hd) fun t P =>
    o.step T.ar.lay T.ar.data.w P.env P.wr (tagR_mut (by rcases hd with rfl | rfl <;> decide) P.frame)

/-- `vg_aes_ocb_seal` in two runs. -/
theorem seal_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («seal» (callees v)) fun _ _ => True := by
  have L := T.ar.lay
  have hDW := T.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt T.ar.data.lt
  have pre := (pre_rel T v).wp (F₁ := Pre K W SP N A D R nl al n tl s₀) (F₂ := Pre K W SP N A D R nl al n tl s₀')
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pre_wp' v T.ar T.sp T.dd T.nn T.ww T.tt T.di T.si T.dx T.cx T.r8 T.r9,
        pre_wp' v T.ar' T.sp' T.dd' T.nn' T.ww' T.tt' T.di' T.si' T.dx' T.cx' T.r8' T.r9'⟩
  have body1 : ∀ {σ s : State}, Args σ K W SP N A D R nl al n tl → Pre K W SP N A D R nl al n tl σ s →
      WP isa (body (callees v) true) s (One K W SP R N A D nl n tl) := fun Ar P =>
    WP.mono (bodySeal_ok v L P.env Ar.rounds P.slots.rounds (Ar.data.of_eq P.rd P.wr) P.slots.data P.slots.len P.ofs
      P.o0 P.ck (by rw [P.l0, P.lstar])) fun t B =>
      (brun_of Ar P).1.step L hDW B.env B.wr (bodyR_mut B.frame)
  have bb := (bodySeal_rel v L T.ar.rounds hDW T.ar.data.lt
    (P := fun a b => True ∧ Pre K W SP N A D R nl al n tl s₀ a ∧ Pre K W SP N A D R nl al n tl s₀' b)
    fun a b h => ⟨brun_of T.ar h.2.1, brun_of T.ar' h.2.2⟩).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨body1 T.ar h.2.1, body1 T.ar' h.2.2⟩
  have tt := (tag_rel v L T.ar.rounds hDW hn (d := tagO) (.inl rfl)
    (P := fun a b => True ∧ One K W SP R N A D nl n tl a ∧ One K W SP R N A D nl n tl b) fun _ _ h => h.2).wp
    (F₁ := One K W SP R N A D nl n tl) (F₂ := One K W SP R N A D nl n tl)
    fun a b h => ⟨tag_one T v (.inl rfl) h.2.1, tag_one T v (.inl rfl) h.2.2⟩
  have rs := rel_taintC [] [] hDW hn (fun a b (h : True ∧ One K W SP R N A D nl n tl a ∧
    One K W SP R N A D nl n tl b) => Both.of h.2.1 h.2.2) (c := .block restore) ⟨_, by taint_decide⟩
  unfold «seal»
  exact Proof.AesCcm.X86_64.rel_assoc3 (RelCT.seq pre (RelCT.seq bb (RelCT.seq tt rs)))

end

/-- Two runs of `seal` or `open` with the same public arguments. -/
theorem Two.of {s₁ s₂ : State} (h₁ : onePre s₁) (h₂ : onePre s₂) (hq : onePub s₁ s₂) :
    Two s₁ s₂ (s₁.gpr .rdi) (arg s₁ 2) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
  have a0 := q8 0 (by decide)
  have a1 := q8 1 (by decide)
  have a2 := q8 2 (by decide)
  have a3 := q8 3 (by decide)
  have ar' := args_of h₂
  rw [← a0, ← a1, ← a2, ← a3, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7] at ar'
  exact
  { ar := args_of h₁, ar' := ar', sp := rfl, sp' := q7.symm
    dd := rfl, dd' := by rw [q7]; exact a0.symm
    nn := (ofNat_toNat64 _).symm, nn' := by rw [q7, a1]; exact (ofNat_toNat64 _).symm
    ww := rfl, ww' := by rw [q7]; exact a2.symm
    tt := (ofNat_toNat64 _).symm, tt' := by rw [q7, a3]; exact (ofNat_toNat64 _).symm
    di := rfl, di' := q1.symm
    si := (ofNat_toNat64 _).symm, si' := by rw [← q2]; exact (ofNat_toNat64 _).symm
    dx := rfl, dx' := q3.symm
    cx := (ofNat_toNat64 _).symm, cx' := by rw [← q4]; exact (ofNat_toNat64 _).symm
    r8 := rfl, r8' := q5.symm
    r9 := (ofNat_toNat64 _).symm, r9' := by rw [← q6]; exact (ofNat_toNat64 _).symm }

/-- `vg_aes_ocb_seal` is constant time. -/
theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» (callees v)) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (seal_rel (Two.of h₁ h₂ hq) v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64
