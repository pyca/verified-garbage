import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
import VerifiedGarbage.Proof.AesOcb.X86_64.NonceCT
import VerifiedGarbage.Proof.AesOcb.X86_64.HashCT
import VerifiedGarbage.Proof.AesOcb.X86_64.BodyCT

/-!
# AES-OCB on x86-64: `vg_aes_ocb_seal` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments are related piece by piece: the entry by the taint analysis from
the public registers, once the first instruction has loaded `W` (`entry_rel`),
then the table of `L_j` by the taint analysis from the public slots and the
length of the associated data, then `Offset_0`, `HASH`, the data and the tag
(`nonce_rel`, `hash_rel`, `bodySeal_rel`, `tag_rel`; `front_rel`), each run
satisfying what correctness says between them (`RelCT.wp`).

The taint analysis knows `W` as the second writable region, as it is for
`open`; `seal` may write `tag` too, before `W`, but its `front` does not, and
runs the same from its states with `tag` only readable (`rel_narrow`). The
copy of the tag and `restore` are related by the taint analysis from the
registers that correctness says agree (`sealTail_rel`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ctxCiph ctxLstar)
open VG.Proof.Aes.X86_64 (BlocksImpl)
open VG.Proof.AesCcm.X86_64 (runBlock_append length_bytesAt bytesAt_frame in_off add_ofNat_assoc)

/-- A run after `entry` and `table`: what `Offset_0` needs, and the table. -/
structure TRun (K W SP N A D : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
  env : Env K W SP s
  slots : Slots W R N A D nl n tl s.mem
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al
  tbl : Tbl W (ctxLstar s₀.mem K) ((n ||| al) / 16) s.mem
  frame : Frame (entryR W :: mutR W SP D n) s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The table, after `entry`. -/
theorem table_trun {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W SP N A D R nl al n tl T) {s₁ : State} (P₁ : EntryPost K W SP R N A D nl al n tl T s s₁) :
    WP isa table s₁ (TRun K W SP N A D R nl al n tl s) := by
  have L := Ar.lay
  refine WP.mono (table_ok P₁.env Ar.data.lt Ar.aad.lt P₁.slots.len P₁.alen P₁.l0) fun s₂ Q => ?_
  exact
    { env := Q.env
      slots := Slots.of_mut L Ar.data.w (wT_mut Q.frame) P₁.slots
      alen := by
        rw [Q.frame.readW (r := ⟨W + BitVec.ofNat 64 alenO, 8⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (L.wT_w (by decide)).symm) (by decide), P₁.alen]
      tbl := Q.tbl
      frame := (P₁.frame.sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩).trans
        ((wT_mut Q.frame).sub fun r hr => ⟨r, List.mem_cons_of_mem _ hr, fun _ h => h⟩)
      rd := Q.rd.trans P₁.rd
      wr := Q.wr.trans P₁.wr }

/-- A run after `Offset_0`: what `HASH` needs. -/
structure NRun (K W SP N A D : Addr) (R nl al n tl : Nat) (s₀ s : State) : Prop where
  C : HCtx K W SP D n R (ctxCiph s₀.mem K R) (ctxLstar s₀.mem K) A (bytesAt s₀.mem A al) s
  one : One K W SP R N A D nl n tl s
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 (bytesAt s₀.mem A al).length

/-- `Offset_0`, after `entry` and `table`. -/
theorem nonce_nrun (v : BlocksImpl) {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W SP N A D R nl al n tl T) (hw : s.wr = [⟨D, n⟩, ⟨W, 3584⟩]) {s₁ : State}
    (P₁ : TRun K W SP N A D R nl al n tl s s₁) :
    WP isa (nonce (callees v)) s₁ (NRun K W SP N A D R nl al n tl s) := by
  have L := Ar.lay
  have hRb : 16 * (R + 1) ≤ 256 := by rcases Ar.rounds with h | h | h <;> subst h <;> decide
  have dK : ∀ r ∈ entryR W :: mutR W SP D n, (⟨K, 256⟩ : Region).Disjoint r := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact L.k_w.sub_right (Lay.wSub (by decide))
    · exact k_mut L Ar.data.k r hr
  have eK : ctxCiph s₁.mem K R = ctxCiph s.mem K R := by
    unfold ctxCiph
    rw [bytesAt_frame P₁.frame (fun r hr => (dK r hr).sub_left (Region.sub_prefix hRb)) (by omega)]
  have eL : ctxLstar s₁.mem K = ctxLstar s.mem K :=
    blockAtMem_frame P₁.frame fun r hr => (dK r hr).sub_left (Lay.kSub (by decide))
  have eB : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → (⟨P, k⟩ : Region).Disjoint ⟨D, n⟩ →
      bytesAt s₁.mem P k = bytesAt s.mem P k := fun hP hPD =>
    bytesAt_frame P₁.frame (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hP.w.sub_right (Lay.wSub (by decide))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hP.w.sub_right (Region.sub_prefix (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.w.sub_right (Lay.wSub (by decide))
        · exact hP.stk.symm
        · exact hPD
        · exact hP.w.sub_right (Lay.wSub (by decide))) (by have := hP.lt; omega)
  refine WP.mono (nonce_ok v L P₁.env Ar.rounds P₁.slots.rounds P₁.slots.nonce P₁.slots.nlen P₁.slots.tl
    Ar.n1 Ar.n15 (by have := Ar.t16; omega) (Ar.nonce.of_eq P₁.rd P₁.wr) Ar.data.k Ar.data.w) fun s₂ P₂ => ?_
  have F₂ : Frame (mutR W SP D n) s₁.mem s₂.mem := nonceR_mut P₂.frame
  have S₂ := Slots.of_mut L Ar.data.w F₂ P₁.slots
  have c₂ : ctxCiph s₂.mem K R = ctxCiph s.mem K R := (ctxCiph_mut L Ar.data.k F₂ Ar.rounds).trans eK
  have l₂ : ctxLstar s₂.mem K = ctxLstar s.mem K := (lstar_mut L Ar.data.k F₂).trans eL
  have a₂ : bytesAt s₂.mem A al = bytesAt s.mem A al := (buf_mut Ar.aad Ar.ad F₂).trans (eB Ar.aad Ar.ad)
  exact
    { C := { lay := L, rounds := Ar.rounds, ciph := c₂, lstar := l₂
             buf := by rw [length_bytesAt]; exact Ar.aad.of_eq (P₂.rd.trans P₁.rd) (P₂.wr.trans P₁.wr)
             aad := by rw [length_bytesAt, a₂]
             ad := by rw [length_bytesAt]; exact Ar.ad
             kd := Ar.data.k, dw := Ar.data.w, rnd := S₂.rounds
             short := by rw [length_bytesAt]; exact Ar.aad.lt
             tbl := by
               rw [length_bytesAt]
               exact ⟨_, P₁.tbl.frame P₂.frame (wT_nonceR L), Nat.div_le_div_right Nat.right_le_or⟩ }
      one := ⟨P₂.env, S₂, P₂.wr.trans (P₁.wr.trans hw)⟩
      alen := by rw [P₂.alen, P₁.alen, length_bytesAt] }

/-- Two runs of the same public arguments: `seal`'s and `open`'s inputs. -/
structure Two (s₀ s₀' : State) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) : Prop where
  ar : Args s₀ K W SP N A D R nl al n tl T
  ar' : Args s₀' K W SP N A D R nl al n tl T
  sp : s₀.gpr .rsp = SP
  sp' : s₀'.gpr .rsp = SP
  dd : s₀.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  dd' : s₀'.mem.readW (SP + BitVec.ofNat 64 8) 64 = D
  nn : s₀.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n
  nn' : s₀'.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n
  tg : s₀.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  tg' : s₀'.mem.readW (SP + BitVec.ofNat 64 24) 64 = T
  tt : s₀.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl
  tt' : s₀'.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl
  ww : s₀.mem.readW (SP + BitVec.ofNat 64 40) 64 = W
  ww' : s₀'.mem.readW (SP + BitVec.ofNat 64 40) 64 = W
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
variable {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
  (Tw : Two s₀ s₀' K W SP N A D R nl al n tl T)
include Tw

/-- What `entry` leaves, in each run. -/
theorem Two.entry₁ : WP isa (.block entry) s₀ (EntryPost K W SP R N A D nl al n tl T s₀) := by
  obtain ⟨s₁, run₁, P₁⟩ := entry_ok Tw.ar.lay Tw.ar.perm Tw.sp Tw.ar.args Tw.ar.argsW Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww
    Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9
  exact WP.of_runBlock ⟨s₁, run₁, P₁⟩

theorem Two.entry₂ : WP isa (.block entry) s₀' (EntryPost K W SP R N A D nl al n tl T s₀') := by
  obtain ⟨s₁, run₁, P₁⟩ := entry_ok Tw.ar'.lay Tw.ar'.perm Tw.sp' Tw.ar'.args Tw.ar'.argsW Tw.dd' Tw.nn' Tw.tg'
    Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'
  exact WP.of_runBlock ⟨s₁, run₁, P₁⟩

/-- `entry` in two runs: the first instruction loads `W` from the stack, the
rest passes the taint analysis from the public registers. -/
theorem entry_rel : RelCT isa (fun a b => a = s₀ ∧ b = s₀') (.block entry) fun _ _ => True := by
  have a₄₀ := in_off (d := 32) (n := 8) Tw.ar.args (by decide) (by decide)
  have a₄₀' := in_off (d := 32) (n := 8) Tw.ar'.args (by decide) (by decide)
  rw [add_ofNat_assoc] at a₄₀ a₄₀'
  have first : ∀ {s : State}, s.gpr .rsp = SP → s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W →
      InRegions (s.rd ++ s.wr) (SP + BitVec.ofNat 64 (8 + 32)) 8 →
      WP isa (.block [.mov .rax (.mem (at_ .rsp 40))]) s fun t =>
        t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s.gpr r := fun hsp hW ha =>
    WP.of_runBlock ⟨_, by orun [hsp, hW, ha], by simp only [gpr_setReg, ite_true],
      fun r h => by simp only [gpr_setReg, h, ite_false]⟩
  have e : entry = [.mov .rax (.mem (at_ .rsp 40))] ++ (save .rax ++
      [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
       st .r15 aadO .r8, st .r15 alenO .r9,
       ld .rax .rsp 8, st .r15 dataO .rax, ld .rax .rsp 16, st .r15 lenO .rax, ld .rax .rsp 32,
       st .r15 tlO .rax, ld .rax .rsp 24, st .r15 tgO .rax] ++ lsetup ++ zero16 ckO) := by
    simp only [entry, List.append_assoc]
  rw [e]
  refine RelCT.block_append ?_
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem (at_ .rsp 40))]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _ (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [Tw.sp, Tw.sp']) hA).wp
    (F₁ := fun (t : State) => t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s₀.gpr r)
    (F₂ := fun (t : State) => t.gpr .rax = W ∧ ∀ r, r ≠ .rax → t.gpr r = s₀'.gpr r) fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab; exact ⟨first Tw.sp Tw.ww a₄₀, first Tw.sp' Tw.ww' a₄₀'⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save .rax ++ [mvr .r15 .rax, mvr .r14 .rdi, st .r15 rndO .rsi, st .r15 nO .rdx, st .r15 nlO .rcx,
       st .r15 aadO .r8, st .r15 alenO .r9,
       ld .rax .rsp 8, st .r15 dataO .rax, ld .rax .rsp 16, st .r15 lenO .rax, ld .rax .rsp 32,
       st .r15 tlO .rax, ld .rax .rsp 24, st .r15 tgO .rax] ++ lsetup ++ zero16 ckO)) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have b := RelCT.taint (A := taint) (P := fun (a b : State) => True ∧
      (a.gpr .rax = W ∧ ∀ r, r ≠ .rax → a.gpr r = s₀.gpr r) ∧ (b.gpr .rax = W ∧ ∀ r, r ≠ .rax → b.gpr r = s₀'.gpr r))
    _ (fun a b ⟨_, ha, hb⟩ => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [ha.1, hb.1]
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.di, Tw.di']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.si, Tw.si']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.dx, Tw.dx']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.cx, Tw.cx']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.r8, Tw.r8']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.r9, Tw.r9']
      · rw [ha.2 _ (by decide), hb.2 _ (by decide), Tw.sp, Tw.sp']) hB
  exact RelCT.seq a b

variable (hw : s₀.wr = [⟨D, n⟩, ⟨W, 3584⟩]) (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 3584⟩])
include hw hw'

/-- `entry`, the table, `Offset_0` and `HASH` in two runs. -/
theorem pre_rel (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block entry) (.seq table (.seq (nonce (callees v)) (hash (callees v))))) fun _ _ => True := by
  have L := Tw.ar.lay
  have hDW := Tw.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt Tw.ar.data.lt
  have e := (entry_rel Tw).wp (F₁ := EntryPost K W SP R N A D nl al n tl T s₀)
    (F₂ := EntryPost K W SP R N A D nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨Tw.entry₁, Tw.entry₂⟩
  have tb := (rel_taintC [] [alenO] hDW hn (P := fun a b => True ∧ EntryPost K W SP R N A D nl al n tl T s₀ a ∧
      EntryPost K W SP R N A D nl al n tl T s₀' b)
    (fun a b h => ⟨h.2.1.env, h.2.2.env, h.2.1.slots, h.2.2.slots, h.2.1.wr.trans hw, h.2.2.wr.trans hw',
      fun _ h => (nomatch h), fun d hd => by
        simp only [List.mem_singleton] at hd; subst hd
        exact ⟨by decide, by rw [h.2.1.alen, h.2.2.alen]⟩⟩)
    (c := table) ⟨_, by taint_decide⟩).wp
    (F₁ := TRun K W SP N A D R nl al n tl s₀) (F₂ := TRun K W SP N A D R nl al n tl s₀')
    fun a b h => ⟨table_trun Tw.ar h.2.1, table_trun Tw.ar' h.2.2⟩
  have nn := (nonce_rel v L Tw.ar.rounds hDW hn Tw.ar.n1 Tw.ar.n15 (by have := Tw.ar.t16; omega)
    (P := fun a b => True ∧ TRun K W SP N A D R nl al n tl s₀ a ∧ TRun K W SP N A D R nl al n tl s₀' b)
    fun a b h => ⟨⟨h.2.1.env, h.2.1.slots, h.2.1.wr.trans hw⟩, ⟨h.2.2.env, h.2.2.slots, h.2.2.wr.trans hw'⟩,
      Tw.ar.nonce.of_eq h.2.1.rd h.2.1.wr, Tw.ar'.nonce.of_eq h.2.2.rd h.2.2.wr⟩).wp
    (F₁ := NRun K W SP N A D R nl al n tl s₀) (F₂ := NRun K W SP N A D R nl al n tl s₀')
    fun a b h => ⟨nonce_nrun v Tw.ar hw h.2.1, nonce_nrun v Tw.ar' hw' h.2.2⟩
  have hh := rel_of_pt (P := fun a b => True ∧ NRun K W SP N A D R nl al n tl s₀ a ∧
      NRun K W SP N A D R nl al n tl s₀' b) (Q := fun _ _ => True) (c := hash (callees v)) fun a b h =>
    hash_rel v h.2.1.C h.2.2.C h.2.1.one h.2.2.one (by simp only [length_bytesAt]) hn h.2.1.alen h.2.2.alen
  exact RelCT.seq e (RelCT.seq tb (RelCT.seq nn hh))

end

/-- A run with the public arguments and the address of the tag at `W + tgO`,
which it may read. -/
def OneT (K W SP : Addr) (R : Nat) (N A D : Addr) (nl n tl : Nat) (T : Addr) (s : State) : Prop :=
  One K W SP R N A D nl n tl s ∧ s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T ∧
    Covers [⟨T, tl⟩] (s.rd ++ s.wr)

/-- What `pre_wp'` leaves is what `body` needs. -/
theorem brun_of {s : State} {s' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W SP N A D R nl al n tl T) (hw : s.wr = [⟨D, n⟩, ⟨W, 3584⟩])
    (P : Pre K W SP N A D R nl al n tl T s s') : BRun K W SP R N A D nl n tl s' :=
  ⟨⟨P.env, P.slots, P.wr.trans hw⟩, Ar.data.of_eq P.rd P.wr, ⟨_, P.tbl⟩, P.ofs.trans P.o0.symm⟩

/-- `body` keeps the public arguments and the address of the tag. -/
theorem body_oneT (v : BlocksImpl) (enc : Bool) {σ s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args σ K W SP N A D R nl al n tl T) (hw : σ.wr = [⟨D, n⟩, ⟨W, 3584⟩])
    (P : Pre K W SP N A D R nl al n tl T σ s) :
    WP isa (body (callees v) enc) s (OneT K W SP R N A D nl n tl T) := by
  have L := Ar.lay
  have k : ∀ {t : State}, Env K W SP t → t.rd = s.rd → t.wr = s.wr → Frame (bodyR W SP D n) s.mem t.mem →
      OneT K W SP R N A D nl n tl T t := fun E hr' hw' f =>
    ⟨(brun_of Ar hw P).1.step L Ar.data.w E hw' (bodyR_mut f),
      by rw [kept_read L Ar.data.w (bodyR_mut f) (d := tgO) (by decide), P.tg],
      by rw [hr', hw', P.rd, P.wr]; exact Ar.tag.rd⟩
  cases enc
  · exact WP.mono (bodyOpen_ok v L P.env Ar.rounds P.slots.rounds (Ar.data.of_eq P.rd P.wr) P.slots.data
      P.slots.len P.ofs P.o0 P.ck (by rw [P.lstar]; exact P.tbl)) fun t B => k B.env B.rd B.wr B.frame
  · exact WP.mono (bodySeal_ok v L P.env Ar.rounds P.slots.rounds (Ar.data.of_eq P.rd P.wr) P.slots.data
      P.slots.len P.ofs P.o0 P.ck (by rw [P.lstar]; exact P.tbl)) fun t B => k B.env B.rd B.wr B.frame

/-- The tag keeps the public arguments and the address of the tag. -/
theorem tag_oneT (v : BlocksImpl) {K W SP : Addr} (L : Lay K W SP) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {N A D : Addr} {nl n tl : Nat} {T : Addr} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 3584⟩)
    {d : Nat} (hd : d = tagO ∨ d = t2O) {s : State}
    (o : OneT K W SP R N A D nl n tl T s) : WP isa (tag (callees v) d) s (OneT K W SP R N A D nl n tl T) :=
  WP.mono (tag_ok v L o.1.env hR o.1.sl.rounds hd) fun t P =>
    have f := tagR_mut (D := D) (n := n) (by rcases hd with rfl | rfl <;> decide) P.frame
    ⟨o.1.step L hDW P.env P.wr f, by rw [kept_read L hDW f (d := tgO) (by decide), o.2.1],
      by rw [P.rd, P.wr]; exact o.2.2⟩

/-- `front` in two runs from states whose writable regions are the data and
`W`. -/
theorem front_rel {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : Two s₀ s₀' K W SP N A D R nl al n tl T) (hw : s₀.wr = [⟨D, n⟩, ⟨W, 3584⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨W, 3584⟩]) (v : BlocksImpl) (enc : Bool) {d : Nat} (hd : d = tagO ∨ d = t2O) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (front (callees v) enc d) fun a b =>
      True ∧ OneT K W SP R N A D nl n tl T a ∧ OneT K W SP R N A D nl n tl T b := by
  have L := Tw.ar.lay
  have hDW := Tw.ar.data.w
  have hn : n ≤ 2 ^ 64 := Nat.le_of_lt Tw.ar.data.lt
  have pre := (pre_rel Tw hw hw' v).wp (F₁ := Pre K W SP N A D R nl al n tl T s₀)
    (F₂ := Pre K W SP N A D R nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨pre_wp' v Tw.ar Tw.sp Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9,
        pre_wp' v Tw.ar' Tw.sp' Tw.dd' Tw.nn' Tw.tg' Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'⟩
  have bb : RelCT isa (fun a b => True ∧ Pre K W SP N A D R nl al n tl T s₀ a ∧ Pre K W SP N A D R nl al n tl T s₀' b)
      (body (callees v) enc) fun _ _ => True := by
    cases enc
    · exact bodyOpen_rel v L Tw.ar.rounds hDW Tw.ar.data.lt fun a b h => ⟨brun_of Tw.ar hw h.2.1, brun_of Tw.ar' hw' h.2.2⟩
    · exact bodySeal_rel v L Tw.ar.rounds hDW Tw.ar.data.lt fun a b h => ⟨brun_of Tw.ar hw h.2.1, brun_of Tw.ar' hw' h.2.2⟩
  have bb' := bb.wp (F₁ := OneT K W SP R N A D nl n tl T) (F₂ := OneT K W SP R N A D nl n tl T)
    fun a b h => ⟨body_oneT v enc Tw.ar hw h.2.1, body_oneT v enc Tw.ar' hw' h.2.2⟩
  have tt := (tag_rel v L Tw.ar.rounds hDW hn (d := d) hd
    (P := fun a b => True ∧ OneT K W SP R N A D nl n tl T a ∧ OneT K W SP R N A D nl n tl T b)
    fun _ _ h => ⟨h.2.1.1, h.2.2.1⟩).wp
    (F₁ := OneT K W SP R N A D nl n tl T) (F₂ := OneT K W SP R N A D nl n tl T)
    fun a b h => ⟨tag_oneT v L Tw.ar.rounds hDW hd h.2.1, tag_oneT v L Tw.ar.rounds hDW hd h.2.2⟩
  unfold front
  exact Proof.AesCcm.X86_64.rel_assoc4 (RelCT.seq pre (RelCT.seq bb' tt))

/-! ## Moving the tag to the regions read only -/

/-- Two runs, as the runs from their states with the writable regions `ex`
moved to those they read only, and only the writable regions `w` left: the
code runs the same from both (`Exec.widen`, `Exec.det`). -/
theorem rel_narrow {P Q : State → State → Prop} {c : Prog isa} (ex w : List Region)
    (h : RelCT isa (fun σ₁ σ₂ => ∃ s₁ s₂, P s₁ s₂ ∧ σ₁ = s₁.withRegions (s₁.rd ++ ex) w ∧
      σ₂ = s₂.withRegions (s₂.rd ++ ex) w) c Q)
    (hP : ∀ s₁ s₂, P s₁ s₂ → (Covers (ex ++ w) s₁.wr ∧ Covers w s₁.wr ∧
        ∃ t s', Exec isa c (s₁.withRegions (s₁.rd ++ ex) w) t s') ∧
      (Covers (ex ++ w) s₂.wr ∧ Covers w s₂.wr ∧ ∃ t s', Exec isa c (s₂.withRegions (s₂.rd ++ ex) w) t s')) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨⟨c₁, w₁, u₁, σ₁', n₁⟩, ⟨c₂, w₂, u₂, σ₂', n₂⟩⟩ := hP _ _ hp
  have widen : ∀ {s σ' : State} {u : List Leak}, Covers (ex ++ w) s.wr → Covers w s.wr →
      Exec isa c (s.withRegions (s.rd ++ ex) w) u σ' → Exec isa c s u (σ'.withRegions s.rd s.wr) :=
    fun {s σ' u} hc hw n => by
    have m := Exec.widen n (rd := s.rd) (wr := s.wr)
      (by simp only [State.withRegions_rd, State.withRegions_wr, List.append_assoc]
          exact Covers.append (Covers.refl _) hc)
      (by simpa only [State.withRegions_wr] using hw)
    rwa [State.withRegions_withRegions, State.withRegions_self] at m
  obtain ⟨rfl, -⟩ := Exec.det e₁ (widen c₁ w₁ n₁)
  obtain ⟨rfl, -⟩ := Exec.det e₂ (widen c₂ w₂ n₂)
  exact ⟨(h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ n₁ n₂).1, trivial⟩

/-- `s` with the tag `⟨T, tl⟩` read only, and the data and `W` its writable
regions. -/
abbrev narrowT (D : Addr) (n : Nat) (T : Addr) (tl : Nat) (W : Addr) (s : State) : State :=
  s.withRegions (s.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 3584⟩]

theorem covers_narrowT (rd : List Region) (d t w : Region) :
    Covers (rd ++ [d, t, w]) ((rd ++ [t]) ++ [d, w]) :=
  Covers.of_mem fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h | h <;> simp [h]

/-- The arguments, in the state with the tag read only. -/
theorem Args.narrow {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : Args s K W SP N A D R nl al n tl T) (hw : s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩]) :
    Args (narrowT D n T tl W s) K W SP N A D R nl al n tl T := by
  have c : Covers (s.rd ++ s.wr) ((narrowT D n T tl W s).rd ++ (narrowT D n T tl W s).wr) := by
    rw [hw]; exact covers_narrowT _ _ _ _
  have b : ∀ {P : Addr} {k : Nat}, Buf W SP s P k → Buf W SP (narrowT D n T tl W s) P k := fun h =>
    ⟨h.rd.trans c, h.lt, h.wrap, h.w, h.stk⟩
  have w : Covers [⟨W, 3584⟩] (narrowT D n T tl W s).wr := Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  have d : Covers [⟨D, n⟩] (narrowT D n T tl W s).wr := Covers.of_mem fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp
  exact {
    lay := Ar.lay, perm := ⟨Ar.perm.k.trans c, w⟩
    rounds := Ar.rounds, nonce := b Ar.nonce, aad := b Ar.aad
    data := ⟨b Ar.data.toBuf, d, Ar.data.k⟩, tag := b Ar.tag
    nd := Ar.nd, ad := Ar.ad, td := Ar.td, n1 := Ar.n1, n15 := Ar.n15, t1 := Ar.t1, t16 := Ar.t16
    retW := Ar.retW, retD := Ar.retD, retT := Ar.retT, args := Ar.args.trans c, argsW := Ar.argsW }

/-- Two runs, from the states with the tag read only. -/
theorem Two.narrow {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : Two s₀ s₀' K W SP N A D R nl al n tl T) (hw : s₀.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩]) :
    Two (narrowT D n T tl W s₀) (narrowT D n T tl W s₀') K W SP N A D R nl al n tl T :=
  { Tw with ar := Tw.ar.narrow hw, ar' := Tw.ar'.narrow hw' }

/-! ## The copy of the tag and the exit -/

/-- What the copy of the tag needs of a run: the environment, the tag
length in its slot and the address of the tag at `W + tgO`. -/
def SealOut (K W SP T : Addr) (tl : Nat) (s : State) : Prop :=
  Env K W SP s ∧ s.mem.readW (W + BitVec.ofNat 64 tlO) 64 = BitVec.ofNat 64 tl ∧
    s.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T

/-- The copy of the tag and the exit, in two runs with the same `W`, tag
length and tag. -/
theorem sealTail_rel {K W SP T : Addr} {tl : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → SealOut K W SP T tl s₁ ∧ SealOut K W SP T tl s₂) :
    RelCT isa P (.seq tagOut (.block restore)) fun _ _ => True := by
  let F : State → Prop := fun s => s.gpr .rbx = W ∧ s.gpr .rsi = T ∧ s.gpr .r12 = BitVec.ofNat 64 tl ∧
    s.gpr .rcx = BitVec.ofNat 64 0 ∧ s.gpr .r15 = W
  have args : ∀ {s : State}, SealOut K W SP T tl s →
      WP isa (.block [mvr .rbx .r15, ld .rsi .r15 tgO, ld .r12 .r15 tlO, .mov .rcx (.imm 0)]) s F :=
    fun ⟨E, htl, htg⟩ => by
      obtain ⟨s', run, h1, h2, h3, h4, g, -⟩ := tagOutArgs_ok E htg htl
      exact WP.of_runBlock ⟨s', run, h1, h2, h3, h4, by rw [g _ (by decide) (by decide) (by decide) (by decide), E.r15]⟩
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.r15])
      (.block [mvr .rbx .r15, ld .rsi .r15 tgO, ld .r12 .r15 tlO, .mov .rcx (.imm 0)]) hc).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := P) _ (fun a b h => by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; rw [(hP a b h).1.1.r15, (hP a b h).2.1.r15]) hA).wp
    (F₁ := F) (F₂ := F) fun a b h => ⟨args (hP a b h).1, args (hP a b h).2⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.rbx, .rsi, .r12, .rcx, .r15])
      (.seq copyLoop (.block restore)) hc).isSome = true := ⟨_, by taint_decide⟩
  have b := RelCT.taint (A := taint) (P := fun a b => True ∧ F a ∧ F b) _ (fun a b ⟨_, ha, hb⟩ => by
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [ha.1, hb.1]
    · rw [ha.2.1, hb.2.1]
    · rw [ha.2.2.1, hb.2.2.1]
    · rw [ha.2.2.2.1, hb.2.2.2.1]
    · rw [ha.2.2.2.2, hb.2.2.2.2]) hB
  unfold tagOut
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with | seq e₁ c₁ => cases e₁ with | seq a₁ b₁ =>
  cases e₂ with | seq e₂ c₂ => cases e₂ with | seq a₂ b₂ =>
  obtain ⟨ht, hq⟩ := RelCT.seq a b _ _ _ _ _ _ hp (.seq a₁ (.seq b₁ c₁)) (.seq a₂ (.seq b₂ c₂))
  simp only [List.append_assoc] at ht ⊢
  exact ⟨ht, hq⟩

/-- `vg_aes_ocb_seal` in two runs. -/
theorem seal_rel {s₀ s₀' : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Tw : Two s₀ s₀' K W SP N A D R nl al n tl T) (hw : s₀.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩])
    (hw' : s₀'.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩]) (v : BlocksImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') («seal» (callees v)) fun _ _ => True := by
  have Tn := Tw.narrow hw hw'
  have inner := (front_rel Tn rfl rfl v true (.inl rfl)).mono (P' := fun σ₁ σ₂ => ∃ s₁ s₂,
      (s₁ = s₀ ∧ s₂ = s₀') ∧ σ₁ = s₁.withRegions (s₁.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 3584⟩] ∧
        σ₂ = s₂.withRegions (s₂.rd ++ [⟨T, tl⟩]) [⟨D, n⟩, ⟨W, 3584⟩])
    (fun _ _ ⟨_, _, ⟨rfl, rfl⟩, e₁, e₂⟩ => ⟨e₁, e₂⟩) fun _ _ h => h
  have cw : ∀ {s : State}, s.wr = [⟨D, n⟩, ⟨T, tl⟩, ⟨W, 3584⟩] →
      Covers ([⟨T, tl⟩] ++ [⟨D, n⟩, ⟨W, 3584⟩]) s.wr ∧ Covers [⟨D, n⟩, ⟨W, 3584⟩] s.wr := fun h => by
    rw [h]
    refine ⟨Covers.of_mem fun r hr => ?_, Covers.of_mem fun r hr => ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp
  have fr := (rel_narrow [⟨T, tl⟩] [⟨D, n⟩, ⟨W, 3584⟩] inner fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨_, _, e₁, -⟩ := sealFront_wp' v Tn.ar Tn.sp Tn.dd Tn.nn Tn.tg Tn.tt Tn.ww Tn.di Tn.si Tn.dx Tn.cx
        Tn.r8 Tn.r9
      obtain ⟨_, _, e₂, -⟩ := sealFront_wp' v Tn.ar' Tn.sp' Tn.dd' Tn.nn' Tn.tg' Tn.tt' Tn.ww' Tn.di' Tn.si' Tn.dx'
        Tn.cx' Tn.r8' Tn.r9'
      exact ⟨⟨(cw hw).1, (cw hw).2, _, _, e₁⟩, ⟨(cw hw').1, (cw hw').2, _, _, e₂⟩⟩).wp
    (F₁ := SFront K W SP N A D R nl al n tl T s₀) (F₂ := SFront K W SP N A D R nl al n tl T s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨sealFront_wp' v Tw.ar Tw.sp Tw.dd Tw.nn Tw.tg Tw.tt Tw.ww Tw.di Tw.si Tw.dx Tw.cx Tw.r8 Tw.r9,
        sealFront_wp' v Tw.ar' Tw.sp' Tw.dd' Tw.nn' Tw.tg' Tw.tt' Tw.ww' Tw.di' Tw.si' Tw.dx' Tw.cx' Tw.r8' Tw.r9'⟩
  exact RelCT.seq fr (sealTail_rel fun a b h => ⟨⟨h.2.1.env, h.2.1.slots.tl, h.2.1.tg⟩,
    ⟨h.2.2.env, h.2.2.slots.tl, h.2.2.tg⟩⟩)

/-- Two runs of `seal` or `open` with the same public arguments. -/
theorem Two.of {s₁ s₂ : State} (hq : onePub s₁ s₂)
    (ar₁ : Args s₁ (s₁.gpr .rdi) (arg s₁ 4) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 2))
    (ar₂ : Args s₂ (s₂.gpr .rdi) (arg s₂ 4) (s₂.gpr .rsp) (s₂.gpr .rdx) (s₂.gpr .r8) (arg s₂ 0) (s₂.gpr .rsi).toNat
      (s₂.gpr .rcx).toNat (s₂.gpr .r9).toNat (arg s₂ 1).toNat (arg s₂ 3).toNat (arg s₂ 2)) :
    Two s₁ s₂ (s₁.gpr .rdi) (arg s₁ 4) (s₁.gpr .rsp) (s₁.gpr .rdx) (s₁.gpr .r8) (arg s₁ 0) (s₁.gpr .rsi).toNat
      (s₁.gpr .rcx).toNat (s₁.gpr .r9).toNat (arg s₁ 1).toNat (arg s₁ 3).toNat (arg s₁ 2) := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
  have a0 := q8 0 (by decide)
  have a1 := q8 1 (by decide)
  have a2 := q8 2 (by decide)
  have a3 := q8 3 (by decide)
  have a4 := q8 4 (by decide)
  have ar' := ar₂
  rw [← a0, ← a1, ← a2, ← a3, ← a4, ← q1, ← q2, ← q3, ← q4, ← q5, ← q6, ← q7] at ar'
  exact
  { ar := ar₁, ar' := ar', sp := rfl, sp' := q7.symm
    dd := rfl, dd' := by rw [q7]; exact a0.symm
    nn := (ofNat_toNat64 _).symm, nn' := by rw [q7, a1]; exact (ofNat_toNat64 _).symm
    tg := rfl, tg' := by rw [q7]; exact a2.symm
    tt := (ofNat_toNat64 _).symm, tt' := by rw [q7, a3]; exact (ofNat_toNat64 _).symm
    ww := rfl, ww' := by rw [q7]; exact a4.symm
    di := rfl, di' := q1.symm
    si := (ofNat_toNat64 _).symm, si' := by rw [← q2]; exact (ofNat_toNat64 _).symm
    dx := rfl, dx' := q3.symm
    cx := (ofNat_toNat64 _).symm, cx' := by rw [← q4]; exact (ofNat_toNat64 _).symm
    r8 := rfl, r8' := q5.symm
    r9 := (ofNat_toNat64 _).symm, r9' := by rw [← q6]; exact (ofNat_toNat64 _).symm }

/-- `vg_aes_ocb_seal` is constant time. -/
theorem seal_ct (v : BlocksImpl) : ConstantTime isa sealX86_64.pre sealX86_64.pub («seal» (callees v)) :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hq e₁ e₂ => by
    have T := Two.of hq (sealArgs_of h₁) (sealArgs_of h₂)
    obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ := hq
    have hw₂ : s₂.wr = [⟨arg s₁ 0, (arg s₁ 1).toNat⟩, ⟨arg s₁ 2, (arg s₁ 3).toNat⟩, ⟨arg s₁ 4, 3584⟩] := by
      rw [h₂.2.1, q8 0 (by decide), q8 1 (by decide), q8 2 (by decide), q8 3 (by decide), q8 4 (by decide)]
    exact (seal_rel T h₁.2.1 hw₂ v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesOcb.X86_64
