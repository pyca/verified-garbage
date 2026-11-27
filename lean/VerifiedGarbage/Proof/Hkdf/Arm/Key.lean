module

public import VerifiedGarbage.Proof.HmacTable.Arm
public import VerifiedGarbage.Impl.Hkdf.Arm
public import VerifiedGarbage.Spec.Hkdf.Table
public import VerifiedGarbage.Proof.Framework.Arm.Steps
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Proof.Framework.ICall
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.CallWipeStack
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Hkdf.Arm

/-!
# HKDF on 32-bit ARM: `vg_hkdf_key`, correct and constant time

The contract the proof is written against (`keyR`), for the table `hmac` of
one hash function `w` (`HVar`), whose functions an indirect call of `f`'s
reaches: `key(prk, prk_len, key, hmac)` makes the 384 bytes at `key` hold
HMAC's states keyed with `PRK` (`Spec.Hkdf.Keyed`, with `w`'s streaming
states). The frame (`kFr` bytes: the working space, then our return
address) allocated, `keyArgs` saves our return address and moves `init`'s
arguments into place and its address into `lr` (`args_ok`); HMAC's `init`
for a key of any length, through the table, in the frame of its stack
argument, writes the states (`any_frame`); `keyEpi` restores our return
address, and the frame's release leaves the states as they are
(`key_correct`).

What every function of HKDF uses is here too: where the stack is
(`StackAt`: `fr + 32` bytes below the stack pointer on entry, from `B` up,
the 32 bytes the calls use, then the frame), the sizes the frames hold
(`HOk`), the indirect call of a table's function (`tcall_ok`, `tcall_rel`),
and the relational form of a block of code whose addresses the taint
analysis checks, from the frame's base (`rel_blk`).
-/

@[expose] public section

namespace VG.Proof.Hkdf.Arm

open VG VG.Arm VG.Arm.Steps
open VG.Impl.Hkdf.Arm
open VG.Impl.Ecdsa.Rfc6979.Arm (Fns)
open VG.Proof.HmacTable.Arm (HVar TabOK TabMem tA AnyArgs any_frame any_rel)
open VG.Arm.FrameStack (armStack addr_sub' sub_toNat')

/-- What the functions need of a hash function's sizes: its streaming states
fit their 192 bytes, and the working space of its functions the frames'. -/
structure HOk (w : HVar) : Prop where
  hS : w.F.H.S ≤ 192
  hA : (w.F.W + w.F.H.S) * 8 ≤ work
  hW : w.ok.Wf * 8 ≤ 1872
  hWb : w.ok.hH.Wb ≤ 1872
  /-- The digests have `D` bytes. -/
  macLen : ∀ x, (w.ok.hH.SH.H.hash x).length = w.F.H.D

/-- `K₀` has a block's bytes. -/
theorem blockKey_len {w : HVar} (hw : HOk w) (k : List Byte) :
    (Spec.Hmac.blockKey w.ok.hH.SH.H k).length = w.F.H.B := by
  have hB := w.ok.hH.hB; have hDB := w.ok.hDB
  simp only [Spec.Hmac.blockKey, hB, List.length_append, List.length_replicate]
  split
  · rw [hw.macLen]; omega_using [hDB]
  · omega_arith

theorem append_zero {k : Nat} (hk : k < 2 ^ 32) : (0 : BitVec 32) ++ BitVec.ofNat 32 k = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  omega_arith

/-- The representation of a streaming state depends only on its bytes. -/
theorem reprOK (w : HVar) : Proof.Pbkdf2.Whole.Arm.ReprOK w.ok.hH.SH := fun m m' p q msg hb =>
  w.ok.hH.repr m m' p q msg (fun i hi => hb i (by rw [w.ok.hH.hS]; exact hi))

theorem stateBytes_eq (w : HVar) : w.ok.hH.SH.stateBytes = w.F.H.S := w.ok.hH.hS

/-! ## The stack -/

/-- Where the stack is, for a frame of `fr` bytes and the stack pointer `sp`
on entry: `B` its lowest byte, `fr + 32` bytes below `sp`, then the 32
bytes the calls use, then the frame, from its base `sp - fr`. -/
structure StackAt (sp : BitVec 32) (fr : Nat) (B : Addr) : Prop where
  fb : State.addr (sp - BitVec.ofNat 32 fr) = B + BitVec.ofNat 64 32
  fbN : (sp - BitVec.ofNat 32 fr).toNat + fr = sp.toNat
  bN : B.toNat + (fr + 32) = sp.toNat

/-- The stack's lowest byte, `fr + 32` bytes below the stack pointer. -/
abbrev base (sp : BitVec 32) (fr : Nat) : Addr := State.addr sp - BitVec.ofNat 64 (fr + 32)

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (by decide))

theorem stackAt {sp : BitVec 32} {fr : Nat} (h : fr + 32 ≤ sp.toNat) : StackAt sp fr (base sp fr) := by
  have hl := sp.isLt
  have h1 : fr ≤ sp.toNat := Nat.le_trans (Nat.le_add_right _ _) h
  have h2 : fr ≤ fr + 32 := Nat.le_add_right _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [addr_sub' h1, Offset.sub_ofNat_eq (State.addr sp) h2, Nat.add_sub_cancel_left]
  · rw [sub_toNat' h1]; exact Nat.sub_add_cancel h1
  · simp only [base]
    rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat, toNat_addr, Nat.mod_eq_of_lt (by omega_using [hl, h])]; exact h),
      BitVec.toNat_ofNat, toNat_addr, Nat.mod_eq_of_lt (by omega_using [hl, h])]
    omega_using [h]

namespace StackAt
variable {sp : BitVec 32} {fr : Nat} {B : Addr} (h : StackAt sp fr B)
include h

/-- An offset into the frame. -/
theorem fo {o : Nat} (ho : o ≤ fr) :
    State.addr (sp - BitVec.ofNat 32 fr + BitVec.ofNat 32 o) = B + BitVec.ofNat 64 (32 + o) := by
  have h1 := h.fbN; have h2 := sp.isLt
  rw [VG.Arm.addr_add (by omega_using [ho, h1, h2]), h.fb, Offset.add_add]

/-- An offset into the frame, as a number. -/
theorem foN {o : Nat} (ho : o ≤ fr) : (sp - BitVec.ofNat 32 fr + BitVec.ofNat 32 o).toNat =
    (sp - BitVec.ofNat 32 fr).toNat + o := by
  have h1 := h.fbN; have h2 := sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho, h1, h2]),
    Nat.mod_eq_of_lt (by omega_using [ho, h1, h2])]

/-- An offset of `B`, as a number. -/
theorem bo {o : Nat} (ho : o ≤ fr + 32) : (B + BitVec.ofNat 64 o).toNat = B.toNat + o := by
  have h1 := h.bN; have h2 := sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho, h1, h2]),
    Nat.mod_eq_of_lt (by omega_using [ho, h1, h2])]

omit h in
/-- A part of the stack. -/
theorem sub {o n : Nat} (hn : o + n ≤ fr + 32) : Region.Sub ⟨B + BitVec.ofNat 64 o, n⟩ ⟨B, fr + 32⟩ :=
  Offset.sub_base _ hn

/-- Two parts of the stack apart. -/
theorem disj {o n o' n' : Nat} (h₁ : o + n ≤ o' ∨ o' + n' ≤ o) (h₂ : o + n ≤ fr + 32) (h₃ : o' + n' ≤ fr + 32) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 o, n⟩ ⟨B + BitVec.ofNat 64 o', n'⟩ := by
  have h1 := h.bN; have h2 := sp.isLt
  exact Offset.disjoint _ h₁ (by omega_using [h₂, h1, h2]) (by omega_using [h₃, h1, h2])

/-- The 32 bytes below the frame, as `initAny`'s contract states them. -/
theorem below32 : State.addr (sp - BitVec.ofNat 32 fr) - BitVec.ofNat 64 32 = B := by
  rw [h.fb, BitVec.add_sub_cancel]

/-- The 24 bytes below the frame, where the calls' frames go. -/
theorem stk24 : State.addr (sp - BitVec.ofNat 32 fr) - 24 = B + BitVec.ofNat 64 8 := by
  rw [h.fb, show (24 : Addr) = BitVec.ofNat 64 24 from rfl, Offset.add_ofNat_sub _ (by decide)]

/-- The 16 bytes below the frame, which `update` uses. -/
theorem stk16 : State.addr (sp - BitVec.ofNat 32 fr) - 16 = B + BitVec.ofNat 64 16 := by
  rw [h.fb, show (16 : Addr) = BitVec.ofNat 64 16 from rfl, Offset.add_ofNat_sub _ (by decide)]

end StackAt

/-! ## The indirect call of a table's function -/

theorem push_gpr {rs : List Reg} {s u : State} (h : isa.push (.push rs) s = some u) :
    u.gpr = s.gpr ∧ u.syms = s.syms := by
  simp only [isa, push] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

/-- The table's function `j`, at `n` in `s`, among `ts`, which an indirect
call reaches. -/
structure TabFn (s : State) (t : Reg) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) :
    Prop where
  hj : 4 * j < 4096
  rd : InRegions (s.rd ++ s.wr) (State.addr (s.gpr t + BitVec.ofNat 32 (4 * j))) 4
  word : s.mem.readW (State.addr (s.gpr t + BitVec.ofNat 32 (4 * j))) 32 = s.syms n
  find : ts.find? (fun q => (s.syms q.1).setWidth 64 == (s.syms n).setWidth 64) = some (n, c)

/-- The call of the table's function `j`: its address into `lr`, then the
frame of its call. -/
theorem tcall_ok {s : State} {t : Reg} {j : Nat} {n : String} {c : Prog isa} {ts : List (String × Prog isa)}
    {rs : List Reg} {r : Reg} {k : Nat} {Q : State → Prop} (hf : TabFn s t j n c ts)
    (hk : ∀ u, Upd s u .lr (s.syms n) → WP isa (.frame (.push rs) (.call n c) (.pop r k)) u Q) :
    WP isa (tcall t j ts rs r k) s Q := by
  unfold tcall
  refine WP.seq (wp_ldr hf.hj rfl hf.rd fun u hu => WP.block_nil ?_)
  rw [hf.word] at hu
  refine WP.frame_icalls_of_call (fun s₁ hp => ?_) (hk u hu)
  obtain ⟨g₁, y₁⟩ := push_gpr hp
  refine ⟨_, rfl, ?_⟩
  show (ts.find? fun p => (s₁.syms p.1).setWidth 64 == (s₁.gpr .lr).setWidth 64) = some (n, c)
  rw [g₁, y₁, hu.gpr, hu.syms]
  exact hf.find

/-! ## Two runs -/

/-- The taint whose public registers are `rs`. -/
def τr (rs : List Reg) : VG.Arm.Taint.T := { regs := RegSet.ofList rs, flags := false }

theorem agree_regs {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.Arm.Taint.Agree (τr rs) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp h := absurd h (Nat.lt_irrefl 0)
  argMem _ h := absurd h (Nat.not_lt_zero _)

/-- Code whose addresses the taint analysis checks from the registers `rs`. -/
abbrev Ck (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.Arm.taint (τr rs) c hc).isSome = true

/-- Code the taint analysis checks from the registers `rs`, which agree. -/
theorem rel_ck {P : State → State → Prop} {c : Prog isa} {rs : List Reg} (hc : Ck rs c)
    (h : ∀ s₁ s₂, P s₁ s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : RelCT isa P c fun _ _ => True :=
  let ⟨_, hc⟩ := hc
  RelCT.taint (A := VG.Arm.taint) (τr rs) (fun _ _ hp => agree_regs (h _ _ hp)) hc

/-- An instruction that accesses the same addresses in two runs, then a block. -/
theorem block_cons_rel {i : Instr} {is : List Instr} {P R Q : State → State → Prop}
    (hi : ∀ a b a' b', P a b → exec i a = some a' → exec i b = some b' →
      addrs i a = addrs i b ∧ R a' b')
    (ht : RelCT isa R (.block is) Q) : RelCT isa P (.block (i :: is)) Q := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      cases ha : exec i a with
      | none => simp only [execBlock, ha, reduceCtorEq] at ea
      | some u =>
        cases hb : exec i b with
        | none => simp only [execBlock, hb, reduceCtorEq] at eb
        | some v =>
          simp only [execBlock, ha, hb, Option.map_eq_some_iff,
            Prod.exists, Prod.mk.injEq] at ea eb
          obtain ⟨u', tr, eu, rfl, rfl⟩ := ea
          obtain ⟨v', ts, ev, rfl, rfl⟩ := eb
          obtain ⟨he, hr⟩ := hi a b u v hp ha hb
          obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ hr (.block eu) (.block ev)
          exact ⟨by rw [he], hq⟩

/-- A block that starts by putting the frame's base in `r12`, whose rest the
taint analysis checks from `r12` and the registers `rs`: in two runs with
the same stack pointer and `rs`, it leaks the same. -/
theorem rel_blk {P : State → State → Prop} {is : List Instr} {rs : List Reg} (hc : Ck (.r12 :: rs) (.block is))
    (h : ∀ s₁ s₂, P s₁ s₂ → s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    RelCT isa P (.block (.addSp .r12 0 :: is)) fun _ _ => True := by
  refine block_cons_rel (R := fun a b => ∀ r ∈ .r12 :: rs, a.gpr r = b.gpr r) (fun a b a' b' hp ea eb => ?_)
    (rel_ck hc fun _ _ h => h)
  obtain ⟨hsp, hr⟩ := h a b hp
  simp only [exec, show (0 : Nat) < 256 from by decide, ↓reduceIte, Option.some.injEq] at ea eb
  subst ea eb
  refine ⟨rfl, fun r hr' => ?_⟩
  rcases List.mem_cons.mp hr' with rfl | hr'
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, hsp]
  · by_cases e : r = .r12
    · subst e; rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, hsp]
    · rw [RegUpd.gpr_setReg_of_ne _ _ e, RegUpd.gpr_setReg_of_ne _ _ e, hr r hr']

/-- Two runs of the call of the table's function `j`, which reaches the same
function in both, from the same stack pointer. -/
theorem tcall_rel {P : State → State → Prop} {t : Reg} {j : Nat} {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} {rs : List Reg} {r : Reg} {k : Nat}
    (hP : ∀ s₁ s₂, P s₁ s₂ → TabFn s₁ t j n c ts ∧ TabFn s₂ t j n c ts ∧ s₁.gpr t = s₂.gpr t ∧
      s₁.syms n = s₂.syms n ∧ s₁.sp = s₂.sp)
    (hcall : RelCT isa (fun u₁ u₂ => ∃ s₁ s₂, P s₁ s₂ ∧ Upd s₁ u₁ .lr (s₁.syms n) ∧ Upd s₂ u₂ .lr (s₂.syms n))
      (.frame (.push rs) (.call n c) (.pop r k)) fun _ _ => True) :
    RelCT isa P (tcall t j ts rs r k) fun _ _ => True := by
  unfold tcall
  refine RelCT.seq (R := fun u₁ u₂ => ∃ s₁ s₂, P s₁ s₂ ∧ Upd s₁ u₁ .lr (s₁.syms n) ∧ Upd s₂ u₂ .lr (s₂.syms n))
    (block_cons_rel (fun a b a' b' hp ea eb => ?_) (RelCT.block_nil fun _ _ h => h)) ?_
  · obtain ⟨f₁, f₂, ht, -⟩ := hP a b hp
    refine ⟨by simp only [addrs, ht], a, b, hp, ?_, ?_⟩
    · rw [exec_ldr f₁.hj f₁.rd, Option.some.injEq] at ea; subst ea
      have u := Upd.setReg a .lr (a.mem.readW (State.addr (a.gpr t + BitVec.ofNat 32 (4 * j))) 32)
      exact ⟨u.gpr.trans f₁.word, u.other, u.sp, u.mem, u.rd, u.wr, u.syms, u.z, u.c⟩
    · rw [exec_ldr f₂.hj f₂.rd, Option.some.injEq] at eb; subst eb
      have u := Upd.setReg b .lr (b.mem.readW (State.addr (b.gpr t + BitVec.ofNat 32 (4 * j))) 32)
      exact ⟨u.gpr.trans f₂.word, u.other, u.sp, u.mem, u.rd, u.wr, u.syms, u.z, u.c⟩
  · cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨a, _, hp, _⟩ => by have := (hP _ _ hp).1.find; simp at this
    | cons q ts =>
      refine RelCT.frame_icalls_of_call hcall fun u₁ u₂ ⟨a, b, hp, v₁, v₂⟩ => ⟨?_, fun x₁ x₂ hx₁ hx₂ => ?_⟩
      · obtain ⟨-, -, -, -, hsp⟩ := hP a b hp
        show addrs (.push rs) u₁ = addrs (.push rs) u₂
        simp only [addrs, v₁.sp, v₂.sp, hsp]
      · obtain ⟨f₁, f₂, -, hn, -⟩ := hP a b hp
        obtain ⟨g₁, y₁⟩ := push_gpr hx₁
        obtain ⟨g₂, y₂⟩ := push_gpr hx₂
        refine ⟨(a.syms n).setWidth 64, by show some ((x₁.gpr .lr).setWidth 64) = _; rw [g₁, v₁.gpr],
          by show some ((x₂.gpr .lr).setWidth 64) = _; rw [g₂, v₂.gpr, hn], ?_, ?_, rfl⟩
        · show (q :: ts).find? (fun p => (x₁.syms p.1).setWidth 64 == (a.syms n).setWidth 64) = _
          rw [y₁, v₁.syms]; exact f₁.find
        · show (q :: ts).find? (fun p => (x₂.syms p.1).setWidth 64 == (a.syms n).setWidth 64) = _
          rw [y₂, v₂.syms, hn]; exact f₂.find

/-! ## `vg_hkdf_key` -/

/-- The stack `vg_hkdf_key` uses: its frame, and the 32 bytes below it that
the call of `init` uses. -/
def kStack : Nat := kFr + 32

theorem kFr_eq : kFr = 3424 := rfl
theorem kStack_eq : kStack = 3456 := rfl
theorem kLr_eq : kLr = 3408 := rfl
theorem work_eq : work = 3408 := rfl

/-- `key(prk, prk_len, key, hmac)`, with `N` bytes of stack, for the table
`hmac` of `w`, whose functions an indirect call of `f`'s reaches, with the
addresses of the functions `ns` public. -/
def keyR (w : HVar) (f : Fns) (ns : List String) (N : Nat) : Contract isa where
  pre s :=
    let prk : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let key : Region := ⟨State.addr (s.gpr .r2), 384⟩
    let tab : Region := ⟨State.addr (s.gpr .r3), 24⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 N, N⟩
    N ≤ s.sp.toNat ∧ s.rd = [prk, tab] ∧ s.wr = [key] ∧ prk.Disjoint key ∧ key.Disjoint tab ∧
      stk.Disjoint prk ∧ stk.Disjoint key ∧ stk.Disjoint tab ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 24 ≤ 2 ^ 32 ∧ TabMem w.F s.syms (s.gpr .r3) s.mem ∧ TabOK w.F f s.syms
  post s s' := Spec.Hkdf.Keyed w.ok.hH.SH s'.mem (State.addr (s.gpr .r2))
    (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ n ∈ ns, s₁.syms n = s₂.syms n

/-- A region contains its first bytes. -/
theorem contains_pre {r : Region} {a : Addr} {n : Nat} (ha : a = r.base) (hn : n ≤ r.len) : r.Contains a n := by
  subst ha; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hn

/-- Reads registers through register writes (`Upd`), deciding which register
each writes. -/
macro "upd_simp" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  (set_option linter.unusedSimpArgs false in simp (disch := decide) only [$ls,*]))

/-- The facts of `keyR`'s precondition, by name, with the stack's regions
from its lowest byte `B`. -/
structure KP (w : HVar) (f : Fns) (s : State) : Prop where
  st : StackAt s.sp kFr (base s.sp kFr)
  sp : kStack ≤ s.sp.toNat
  rd : s.rd = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, ⟨State.addr (s.gpr .r3), 24⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r2), 384⟩]
  p_k : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩ ⟨State.addr (s.gpr .r2), 384⟩
  k_t : Region.Disjoint ⟨State.addr (s.gpr .r2), 384⟩ ⟨State.addr (s.gpr .r3), 24⟩
  s_p : Region.Disjoint ⟨base s.sp kFr, kStack⟩ ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
  s_k : Region.Disjoint ⟨base s.sp kFr, kStack⟩ ⟨State.addr (s.gpr .r2), 384⟩
  s_t : Region.Disjoint ⟨base s.sp kFr, kStack⟩ ⟨State.addr (s.gpr .r3), 24⟩
  np : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  nk : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32
  nt : (s.gpr .r3).toNat + 24 ≤ 2 ^ 32
  tm : TabMem w.F s.syms (s.gpr .r3) s.mem
  tok : TabOK w.F f s.syms

theorem kp_of {w : HVar} {f : Fns} {ns : List String} {s : State} (hp : (keyR w f ns kStack).pre s) : KP w f s :=
  let ⟨hsp, hrd, hwr, pk, kt, sp, sk, st, np, nk, nt, tm, tok⟩ := hp
  ⟨stackAt hsp, hsp, hrd, hwr, pk, kt, sp, sk, st, np, nk, nt, tm, tok⟩

/-- The frame's base. -/
abbrev fbk (s : State) : BitVec 32 := s.sp - BitVec.ofNat 32 kFr

/-- Our return address's slot. -/
abbrev lrA (s : State) : Addr := base s.sp kFr + BitVec.ofNat 64 (32 + kLr)

/-- What `keyArgs` leaves: our return address saved, `init`'s arguments, and
its address in `lr`. -/
structure KA (w : HVar) (s t : State) : Prop where
  r0 : t.gpr .r0 = s.gpr .r2
  r1 : t.gpr .r1 = s.gpr .r2 + BitVec.ofNat 32 192
  r2 : t.gpr .r2 = s.gpr .r0
  r3 : t.gpr .r3 = s.gpr .r1
  r12 : t.gpr .r12 = fbk s
  lr : t.gpr .lr = s.syms w.F.hiAnyN
  cs : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r
  sp : t.sp = fbk s
  mem : t.mem = s.mem.writeW (lrA s) (s.gpr .lr)
  rd : t.rd = s.rd
  wr : t.wr = ⟨State.addr (fbk s), kFr⟩ :: s.wr
  syms : t.syms = s.syms

section
variable {w : HVar} {f : Fns} {s : State} (hp : KP w f s)
include hp

/-- The frame is apart from the arguments' buffers. -/
theorem kfr_sub {o n : Nat} (h : o + n ≤ kFr) :
    Region.Sub ⟨State.addr (fbk s) + BitVec.ofNat 64 o, n⟩ ⟨base s.sp kFr, kStack⟩ := by
  rw [hp.st.fb, Offset.add_add]; exact Offset.sub_base _ (by simp only [kStack]; omega_using [h])

theorem args_ok : WP isa (.block keyArgs) (allocated kFr s) (KA w s) := by
  have hS := hp.st
  unfold keyArgs
  refine wp_addSp (by decide) fun t₁ u₁ => ?_
  have h12 : t₁.gpr .r12 = fbk s := by rw [u₁.gpr, BitVec.add_zero]; rfl
  refine wp_str (a := lrA s) (by decide) (by rw [h12]; exact hS.fo (by decide))
    ⟨_, by rw [u₁.wr]; exact List.mem_cons_self .., by
      rw [hS.fb]; exact Offset.contains _ (by decide) (by decide) (by
        have := hS.bN; have := s.sp.isLt; simp only [kFr] at *; omega_using [this])⟩ fun t₂ u₂ => ?_
  have hr3 : t₂.gpr .r3 = s.gpr .r3 := by rw [u₂.gpr, u₁.other _ (by decide)]; rfl
  refine wp_ldr (a := tA (s.gpr .r3) 0) (by decide) (by rw [hr3])
    ⟨⟨State.addr (s.gpr .r3), 24⟩, List.mem_append_left _ (by rw [u₂.rd, u₁.rd]; show _ ∈ s.rd; rw [hp.rd]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      contains_pre (by rw [tA, BitVec.add_zero]) (show 4 ≤ 24 by decide)⟩ fun t₃ u₃ => ?_
  refine wp_movr fun t₄ u₄ => wp_movr fun t₅ u₅ => wp_movr fun t₆ u₆ => wp_movr fun t₇ u₇ =>
    wp_addi (by decide) fun t₈ u₈ => WP.block_nil ?_
  have hm : t₂.mem = s.mem.writeW (lrA s) (s.gpr .lr) := by rw [u₂.mem, u₁.mem, u₁.other _ (by decide)]; rfl
  have hd : Region.Disjoint ⟨State.addr (s.gpr .r3), 24⟩ ⟨lrA s, 4⟩ :=
    (hp.s_t.sub_left (Offset.sub_base _ (by decide))).symm
  have htab : t₂.mem.readW (tA (s.gpr .r3) 0) 32 = s.syms w.F.hiAnyN := by
    rw [hm, Mem.readW_writeW_sep (Region.Disjoint.sep hd (contains_pre (by rw [tA, BitVec.add_zero]) (show 4 ≤ 24 by decide))
      (Region.contains_self _ _)) (by decide)]
    exact hp.tm.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr hl => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · upd_simp [u₈.other, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]; rfl
  · upd_simp [u₈.gpr, u₇.other, u₆.gpr, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]; rfl
  · upd_simp [u₈.other, u₇.gpr, u₆.other, u₅.gpr, u₄.other, u₃.other, u₂.gpr, u₁.other]; rfl
  · upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.gpr, u₃.other, u₂.gpr, u₁.other]; rfl
  · upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, h12]
  · upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.gpr]; exact htab
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hl
      | (upd_simp [u₈.other, u₇.other, u₆.other, u₅.other, u₄.other, u₃.other, u₂.gpr, u₁.other]; rfl)
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]; rfl
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; rfl
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rfl
  · rw [u₈.syms, u₇.syms, u₆.syms, u₅.syms, u₄.syms, u₃.syms, u₂.syms, u₁.syms]; rfl

/-- The frame's first `n` bytes, among the stack's. -/
theorem kfb_sub {n : Nat} (h : n ≤ kFr) : Region.Sub ⟨State.addr (fbk s), n⟩ ⟨base s.sp kFr, kStack⟩ := by
  rw [hp.st.fb]; exact Offset.sub_base _ (by simp only [kStack]; omega_using [h])

omit hp in
/-- The 32 bytes below the frame, among the stack's. -/
theorem kb32_sub : Region.Sub ⟨base s.sp kFr, 32⟩ ⟨base s.sp kFr, kStack⟩ := Region.sub_prefix (by decide)

theorem key192 : State.addr (s.gpr .r2 + BitVec.ofNat 32 192) = State.addr (s.gpr .r2) + BitVec.ofNat 64 192 := by
  have := hp.nk; exact VG.Arm.addr_add (by omega_using [this])

theorem key192N : (s.gpr .r2 + BitVec.ofNat 32 192).toNat = (s.gpr .r2).toNat + 192 := by
  have := hp.nk
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 192) (by decide),
    Nat.mod_eq_of_lt (by omega_using [this])]

/-- `init`'s arguments, from what `keyArgs` leaves. -/
theorem any_args (hw : HOk w) {t : State} (ka : KA w s t) :
    AnyArgs w.ok.hH.SH (w.F.W + w.F.H.S) t (s.gpr .r2) (s.gpr .r2 + BitVec.ofNat 32 192) (s.gpr .r0) (fbk s)
      (s.gpr .r1).toNat := by
  have hS := hp.st
  have hS1 := hw.hS; have hA := hw.hA; have hwk := work_eq
  have hsb := stateBytes_eq w
  have nk := hp.nk; have hsp := hp.sp; have hlt := s.sp.isLt
  have hfN : (fbk s).toNat + kFr = s.sp.toNat := hS.fbN
  have hks : kStack = kFr + 32 := rfl
  have hkf := kFr_eq
  have iS : Region.Sub ⟨State.addr (s.gpr .r2), w.ok.hH.SH.stateBytes⟩ ⟨State.addr (s.gpr .r2), 384⟩ :=
    Region.sub_prefix (by omega_using [hS1, hsb])
  have oS : Region.Sub ⟨State.addr (s.gpr .r2 + BitVec.ofNat 32 192), w.ok.hH.SH.stateBytes⟩
      ⟨State.addr (s.gpr .r2), 384⟩ := by
    rw [key192 hp]; exact Offset.sub_base _ (by omega_using [hS1, hsb])
  have sS : Region.Sub ⟨State.addr (fbk s), (w.F.W + w.F.H.S) * 8⟩ ⟨base s.sp kFr, kStack⟩ :=
    kfb_sub hp (by omega_using [hA, hwk, hkf])
  have hb : (⟨State.addr t.sp - BitVec.ofNat 64 32, 32⟩ : Region) = ⟨base s.sp kFr, 32⟩ := by
    rw [ka.sp, hS.below32]
  exact
    { r0 := ka.r0, r1 := ka.r1, r2 := ka.r2, r12 := ka.r12
      r3 := by rw [ka.r3, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      kl32 := (s.gpr .r1).isLt
      sp := by rw [ka.sp, sub_toNat' (by omega_using [hsp, hks])]; omega_using [hsp, hks]
      cr := VG.Covers.left (by
        rw [ka.rd, hp.rd]; exact VG.Covers.of_mem fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self ..)
      cw := by
        rw [ka.wr, hp.wr]
        refine VG.Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), 0, (BitVec.add_zero _).symm,
            by dsimp only; omega_using [hS1, hsb]⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), 192, key192 hp,
            by dsimp only; omega_using [hS1, hsb]⟩
        · exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm,
            by dsimp only; omega_using [hA, hwk, hkf]⟩
      i_o := by rw [key192 hp]; exact Offset.base_disjoint _ (by omega_using [hS1, hsb]) (by
        have := (State.addr (s.gpr .r2)).isLt; rw [toNat_addr] at *; omega_using [hS1, hsb, nk])
      i_k := hp.p_k.symm.sub_left iS
      i_s := (hp.s_k.symm.sub_left iS).sub_right sS
      o_k := hp.p_k.symm.sub_left oS
      o_s := (hp.s_k.symm.sub_left oS).sub_right sS
      k_s := hp.s_p.symm.sub_right sS
      b_i := by rw [hb]; exact (hp.s_k.sub_left kb32_sub).sub_right iS
      b_o := by rw [hb]; exact (hp.s_k.sub_left kb32_sub).sub_right oS
      b_k := by rw [hb]; exact hp.s_p.sub_left kb32_sub
      b_s := by
        rw [hb, hS.fb]; exact Offset.base_disjoint _ (by decide) (by
          have := hS.bN; omega_using [this, hA, hwk, hkf, hlt])
      ni := by omega_using [hS1, hsb, nk]
      no := by rw [key192N hp]; omega_using [hS1, hsb, nk]
      nk := hp.np
      nsc := by omega_using [hA, hwk, hkf, hfN, hlt] }

end

/-- The bytes of a region apart from `rs` are kept. -/
theorem bytes_keep {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A state at `p` represents the same message in memory that agrees with it
there. -/
theorem repr_keep (w : HVar) {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr} {msg : List Byte}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, w.F.H.S⟩ r) (hr : w.ok.hH.SH.Repr m p msg) : w.ok.hH.SH.Repr m' p msg :=
  w.ok.hH.repr m m' p p msg (fun i hi => hf.bytes (R := ⟨p, w.F.H.S⟩) hd
    (by have := w.ok.hH.hSB; show w.F.H.S ≤ 2 ^ 64; omega_using [this]) hi) hr

section
variable {w : HVar} {f : Fns} {s : State} (hp : KP w f s)
include hp

/-- `vg_hkdf_key`: the frame, the arguments, HMAC's `init` through the
table, and our return address restored. -/
theorem key_correct (hw : HOk w) :
    WP isa (key f) s fun s' => abiPreserved s s' ∧ Spec.Hkdf.Keyed w.ok.hH.SH s'.mem (State.addr (s.gpr .r2))
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) := by
  have hS := hp.st
  have hS1 := hw.hS; have hA := hw.hA; have hwk := work_eq; have hkf := kFr_eq
  have hsb := stateBytes_eq w
  have hsp := hp.sp; have hlt := s.sp.isLt; have hkl := kLr_eq
  have hks : kStack = kFr + 32 := rfl
  unfold key
  refine WP.alloc (by decide) (by omega_using [hsp, hks]) ?_
  unfold keyMain
  refine WP.seq (WP.mono (args_ok hp) fun t ka => ?_)
  refine WP.seq (WP.frame_icalls_of_call (fun s₁ hp₁ => ?_)
    (any_frame (n := w.F.hiAnyN) (reprOK w) (by rw [hsb]; have := w.ok.hH.hSB; omega_using [this]) w.any
      w.scrub.1.1 (any_args hp hw ka) fun s' ha hi ho => ?_))
  · obtain ⟨g₁, y₁⟩ := push_gpr hp₁
    refine ⟨_, rfl, ?_⟩
    show (f.init.find? fun p => (s₁.syms p.1).setWidth 64 == (s₁.gpr .lr).setWidth 64) = some _
    rw [g₁, y₁, ka.lr, ka.syms]
    exact hp.tok.i
  -- The return address's slot, apart from what the call writes.
  have hlrd : ∀ r ∈ Proof.Pbkdf2.Whole.Arm.HiArgs.wr w.ok.hH.SH (w.F.W + w.F.H.S) (s.gpr .r2)
      (s.gpr .r2 + BitVec.ofNat 32 192) (fbk s) ++ [Proof.Pbkdf2.Whole.Arm.stk t],
      Region.Disjoint ⟨lrA s, 4⟩ r := by
    have sl : Region.Sub ⟨lrA s, 4⟩ ⟨base s.sp kFr, kStack⟩ := Offset.sub_base _ (by decide)
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hp.s_k.sub_left sl).sub_right (Region.sub_prefix (by omega_using [hS1, hsb]))
    · exact (hp.s_k.sub_left sl).sub_right (by
        rw [key192 hp]; exact Offset.sub_base _ (by omega_using [hS1, hsb]))
    · rw [hS.fb]; exact hS.disj (.inr (by omega_using [hA, hwk, hkl])) (by decide) (by omega_using [hA, hwk, hkf])
    · show Region.Disjoint _ ⟨State.addr t.sp - 24, 24⟩
      rw [ka.sp, hS.stk24]; exact hS.disj (.inr (by decide)) (by decide) (by decide)
  have hret : s'.mem.readW (lrA s) 32 = s.gpr .lr := by
    rw [ha.frame.readW (r := ⟨lrA s, 4⟩) (Region.contains_self _ _) hlrd (by decide), ka.mem,
      Mem.readW_writeW_self32]
  have hsp' : s'.sp = fbk s := ha.sp.trans ka.sp
  refine wp_addSp (by decide) fun u₁ v₁ => ?_
  refine wp_ldr (a := lrA s) (by decide) (by rw [v₁.gpr, hsp', BitVec.add_zero]; exact hS.fo (by decide))
    ⟨_, List.mem_append_right _ (by rw [v₁.wr, ha.wr, ka.wr]; exact List.mem_cons_self ..), by
      rw [hS.fb]; exact Offset.contains _ (by decide) (by decide) (by
        have := hS.bN; omega_using [this, hlt])⟩ fun u₂ v₂ => WP.block_nil ?_
  intro m uk hm
  have hmk : Frame [⟨base s.sp kFr + BitVec.ofNat 64 32, kFr⟩] s'.mem m := by
    rw [← hS.fb, ← v₁.mem, ← v₂.mem]; exact hm
  have hkd : ∀ o, o + w.F.H.S ≤ 384 → ∀ r ∈ [(⟨base s.sp kFr + BitVec.ofNat 64 32, kFr⟩ : Region)],
      Region.Disjoint ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 o, w.F.H.S⟩ r := fun o ho r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.s_k.symm.sub_left (Offset.sub_base _ ho)).sub_right (Offset.sub_base _ (by decide))
  have hpk : Spec.Sha256.bytesAt t.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat := by
    rw [ka.mem]
    refine bytes_keep ((Frame.refl _ _).writeW (List.mem_singleton_self ⟨lrA s, 4⟩) _ (Region.contains_self _ _))
      (fun r hr => ?_) (by have := (s.gpr .r1).isLt; omega_using [this])
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.s_p.sub_left (Offset.sub_base _ (by decide))).symm
  rw [hpk] at hi ho
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · show u₂.gpr r = s.gpr r
    by_cases hl : r = .lr
    · subst hl; rw [v₂.gpr, v₁.mem, hret]
    · rw [v₂.other _ (Ne.symm (Ne.symm hl)), v₁.other _ (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        ha.cs r hr hl, ka.cs r hr hl]
  · show u₂.sp + BitVec.ofNat 32 kFr = s.sp
    rw [v₂.sp, v₁.sp, hsp', BitVec.sub_add_cancel]
  · have := hkd 0 (by omega_using [hS1]) 
    rw [BitVec.add_zero] at this
    exact repr_keep w hmk this hi
  · exact repr_keep w hmk (hkd 192 (by omega_using [hS1])) (by rw [← key192 hp]; exact ho)

end

/-! ## Constant time -/

/-- Code leaves the stack pointer as it found it. -/
theorem rel_sp {P Q : State → State → Prop} {c : Prog isa} (h : RelCT isa P c Q) :
    RelCT isa P c fun a b => Q a b ∧ ∃ x y, P x y ∧ a.sp = x.sp ∧ b.sp = y.sp := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp e₁ e₂
  exact ⟨ht, hq, s₁, s₂, hp, Exec.sp e₁, Exec.sp e₂⟩

/-- Leaking the same, and the single-run facts of both runs. -/
theorem rel_both {P₁ P₂ G₁ G₂ : State → Prop} {c : Prog isa}
    (h : RelCT isa (fun a b => P₁ a ∧ P₂ b) c fun _ _ => True)
    (hw : ∀ a, P₁ a → WP isa c a G₁) (hw' : ∀ b, P₂ b → WP isa c b G₂) :
    RelCT isa (fun a b => P₁ a ∧ P₂ b) c fun a b => G₁ a ∧ G₂ b :=
  (h.wp fun a b hp => ⟨hw a hp.1, hw' b hp.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem keyArgs_ck : Ck [.r12, .r0, .r1, .r2, .r3] (.block keyArgs.tail) := ⟨_, by taint_decide⟩
theorem keyEpi_ck : Ck [.r12] (.block keyEpi.tail) := ⟨_, by taint_decide⟩

section
variable {w : HVar} {f : Fns} {ns : List String}

/-- `vg_hkdf_key` is constant time: two runs whose public data agree leak the
same trace. -/
theorem key_ct (hw : HOk w) (hns : w.F.hiAnyN ∈ ns) :
    ConstantTime isa (keyR w f ns kStack).pre (keyR w f ns kStack).pub (key f) := by
  refine RelCT.constantTime (Q := fun _ _ => True) fun e e' t₁ t₂ a b ⟨h, h', hpub⟩ e₁ e₂ => ?_
  obtain ⟨qsp, q0, q1, q2, q3, qn⟩ := hpub
  have hp := kp_of h
  have hp' := kp_of h'
  have hfb : fbk e' = fbk e := by simp only [fbk, qsp]
  revert e₁ e₂
  generalize hP : (fun x y : State => x = e ∧ y = e') = Q
  suffices hr : RelCT isa Q (key f) fun _ _ => True by
    intro e₁ e₂; exact hr _ _ _ _ _ _ (hP ▸ ⟨rfl, rfl⟩) e₁ e₂
  subst hP
  unfold key keyMain
  refine RelCT.allocFrame ?_
  have r1 : RelCT isa (fun x y => ∃ s₁ s₂, (s₁ = e ∧ s₂ = e') ∧ x = allocated kFr s₁ ∧ y = allocated kFr s₂)
      (.block keyArgs) fun x y => KA w e x ∧ KA w e' y := by
    have hb := rel_blk (P := fun x y => ∃ s₁ s₂, (s₁ = e ∧ s₂ = e') ∧ x = allocated kFr s₁ ∧ y = allocated kFr s₂)
      keyArgs_ck fun x y ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ => by
        subst e₁ e₂ hx hy
        refine ⟨by simp only [allocated, qsp], fun r hr => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [q0, q1, q2, q3]
    refine (hb.wp fun x y ⟨s₁, s₂, ⟨e₁, e₂⟩, hx, hy⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    subst e₁ e₂ hx hy
    exact ⟨args_ok hp, args_ok hp'⟩
  refine r1.seq (RelCT.seq (rel_sp (Q := fun _ _ => True) ?_) ?_)
  · have hcall : RelCT isa (fun x y => KA w e x ∧ KA w e' y)
        (.frame (.push [.r12, .lr]) (.call w.F.hiAnyN w.F.hmacInitAny) (.pop .r12 8)) fun _ _ => True :=
      any_rel w.any (sp := fbk e) fun x y ⟨ka, ka'⟩ => ⟨any_args hp hw ka, by
          have := any_args hp' hw ka'; rwa [← q0, ← q1, ← q2, hfb] at this,
        ka.sp, by rw [ka'.sp, hfb]⟩
    have hi := hp.tok.i
    have hi' := hp'.tok.i
    cases hf : f.init with
    | nil => rw [hf] at hi; cases hi
    | cons q ts =>
      rw [hf] at hi hi'
      refine RelCT.frame_icalls_of_call hcall fun x y ⟨ka, ka'⟩ => ⟨?_, fun u₁ u₂ hp₁ hp₂ => ?_⟩
      · show addrs (.push [.r12, .lr]) x = addrs (.push [.r12, .lr]) y
        simp only [addrs, ka.sp, ka'.sp, hfb]
      · obtain ⟨g₁, y₁⟩ := push_gpr hp₁
        obtain ⟨g₂, y₂⟩ := push_gpr hp₂
        have hn := qn _ hns
        refine ⟨(e.syms w.F.hiAnyN).setWidth 64, by show some ((u₁.gpr .lr).setWidth 64) = _; rw [g₁, ka.lr],
          by show some ((u₂.gpr .lr).setWidth 64) = _; rw [g₂, ka'.lr, hn], ?_, ?_, rfl⟩
        · show (q :: ts).find? (fun p => (u₁.syms p.1).setWidth 64 == (e.syms w.F.hiAnyN).setWidth 64) = _
          rw [y₁, ka.syms]; exact hi
        · show (q :: ts).find? (fun p => (u₂.syms p.1).setWidth 64 == (e.syms w.F.hiAnyN).setWidth 64) = _
          rw [y₂, ka'.syms, hn]; exact hi'
  · refine rel_blk keyEpi_ck fun x y hxy => ?_
    obtain ⟨-, x₀, y₀, ⟨ka, ka'⟩, hx, hy⟩ := hxy
    exact ⟨by rw [hx, hy, ka.sp, ka'.sp, hfb], fun _ h => absurd h List.not_mem_nil⟩

end

end VG.Proof.Hkdf.Arm
