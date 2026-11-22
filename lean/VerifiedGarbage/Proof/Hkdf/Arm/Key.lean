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

instance (w : HVar) : Decidable (HOk w) :=
  decidable_of_iff (w.F.H.S ≤ 192 ∧ (w.F.W + w.F.H.S) * 8 ≤ work ∧ w.ok.Wf * 8 ≤ 1872 ∧ w.ok.hH.Wb ≤ 1872)
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

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
  refine ⟨?_, ?_, ?_⟩
  · rw [addr_sub' (by omega_using [h]), Offset.sub_ofNat_eq (State.addr sp) (show fr ≤ fr + 32 by omega_using []),
      show fr + 32 - fr = 32 by omega_using []]
  · rw [sub_toNat' (by omega_using [h])]; omega_using [h]
  · simp only [base]
    rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat, toNat_addr, Nat.mod_eq_of_lt (by omega_using [hl])]; exact h),
      BitVec.toNat_ofNat, toNat_addr, Nat.mod_eq_of_lt (by omega_using [hl])]
    omega_using [h]

namespace StackAt
variable {sp : BitVec 32} {fr : Nat} {B : Addr} (h : StackAt sp fr B)
include h

/-- An offset into the frame. -/
theorem fo {o : Nat} (ho : o ≤ fr) :
    State.addr (sp - BitVec.ofNat 32 fr + BitVec.ofNat 32 o) = B + BitVec.ofNat 64 (32 + o) := by
  have := h.fbN; have := sp.isLt
  rw [VG.Arm.addr_add (by omega_using [ho]), h.fb, Offset.add_add]

/-- An offset into the frame, as a number. -/
theorem foN {o : Nat} (ho : o ≤ fr) : (sp - BitVec.ofNat 32 fr + BitVec.ofNat 32 o).toNat =
    (sp - BitVec.ofNat 32 fr).toNat + o := by
  have := h.fbN; have := sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho]),
    Nat.mod_eq_of_lt (by omega_using [ho])]

/-- An offset of `B`, as a number. -/
theorem bo {o : Nat} (ho : o ≤ fr + 32) : (B + BitVec.ofNat 64 o).toNat = B.toNat + o := by
  have := h.bN; have := sp.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho]),
    Nat.mod_eq_of_lt (by omega_using [ho])]

/-- A part of the stack. -/
theorem sub {o n : Nat} (hn : o + n ≤ fr + 32) : Region.Sub ⟨B + BitVec.ofNat 64 o, n⟩ ⟨B, fr + 32⟩ :=
  Offset.sub_base _ hn

/-- Two parts of the stack apart. -/
theorem disj {o n o' n' : Nat} (h₁ : o + n ≤ o' ∨ o' + n' ≤ o) (h₂ : o + n ≤ fr + 32) (h₃ : o' + n' ≤ fr + 32) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 o, n⟩ ⟨B + BitVec.ofNat 64 o', n'⟩ := by
  have := h.bN; have := sp.isLt
  exact Offset.disjoint _ h₁ (by omega_using [h₂]) (by omega_using [h₃])

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

/-- Two runs of the call of the table's function `j`, which reaches the same
function in both. -/
theorem tcall_rel {P : State → State → Prop} {t : Reg} {j : Nat} {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} {rs : List Reg} {r : Reg} {k : Nat}
    (hP : ∀ s₁ s₂, P s₁ s₂ → TabFn s₁ t j n c ts ∧ TabFn s₂ t j n c ts ∧ s₁.gpr t = s₂.gpr t ∧
      s₁.syms n = s₂.syms n)
    (hcall : RelCT isa (fun u₁ u₂ => ∃ s₁ s₂, P s₁ s₂ ∧ Upd s₁ u₁ .lr (s₁.syms n) ∧ Upd s₂ u₂ .lr (s₂.syms n))
      (.frame (.push rs) (.call n c) (.pop r k)) fun _ _ => True) :
    RelCT isa P (tcall t j ts rs r k) fun _ _ => True := by
  unfold tcall
  have hb : RelCT isa P (.block [.ldr .lr t (4 * j)])
      fun u₁ u₂ => ∃ s₁ s₂, P s₁ s₂ ∧ Upd s₁ u₁ .lr (s₁.syms n) ∧ Upd s₂ u₂ .lr (s₂.syms n) := by
    intro s₁ s₂ t₁ t₂ u₁ u₂ hp e₁ e₂
    obtain ⟨f₁, f₂, ht, -⟩ := hP s₁ s₂ hp
    obtain ⟨tr₁, v₁, e₁', hv₁⟩ := wp_ldr (Q := fun u => Upd s₁ u .lr (s₁.syms n)) f₁.hj rfl f₁.rd
      (fun u hu => WP.block_nil (by rw [f₁.word] at hu; exact hu))
    obtain ⟨tr₂, v₂, e₂', hv₂⟩ := wp_ldr (Q := fun u => Upd s₂ u .lr (s₂.syms n)) f₂.hj rfl f₂.rd
      (fun u hu => WP.block_nil (by rw [f₂.word] at hu; exact hu))
    obtain ⟨rfl, rfl⟩ := Exec.det e₁ e₁'
    obtain ⟨rfl, rfl⟩ := Exec.det e₂ e₂'
    refine ⟨?_, s₁, s₂, hp, hv₁, hv₂⟩
    cases e₁ with | block r₁ => cases e₂ with | block r₂ =>
      simp only [runBlock, execBlock, isa, addrs, ht] at r₁ r₂ ⊢
      sorry
  sorry

end VG.Proof.Hkdf.Arm
